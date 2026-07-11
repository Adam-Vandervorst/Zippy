import numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm

rows=[]; labels=[]; 
with open("/tmp/prog_matrix.tsv") as f:
    cols = f.readline().rstrip("\n").split("\t")[1:]
    for line in f:
        parts=line.rstrip("\n").split("\t")
        labels.append(parts[0]); rows.append([int(x) for x in parts[1:]])
M=np.array(rows, dtype=float)
disp=np.where(M>0, M, np.nan)   # zeros blank

fig,ax=plt.subplots(figsize=(13, 13))
cmap=plt.cm.viridis.copy(); cmap.set_bad("#f2f2f2")
im=ax.imshow(disp, aspect="auto", cmap=cmap, norm=LogNorm(vmin=max(1,np.nanmin(disp)), vmax=np.nanmax(disp)))
ax.set_xticks(range(len(cols))); ax.set_xticklabels(cols, rotation=55, ha="right", fontsize=9)
ax.set_yticks(range(len(labels))); ax.set_yticklabels(labels, fontsize=9, family="monospace")
ax.set_xlabel("child term type  X", fontsize=11); ax.set_ylabel("parent type . position   (Y . p)", fontsize=11)
ax.set_title("1,000,000 fuzzed MORKL programs (depth 6, ≥12 nodes)\n\"type X occurs at position p inside type Y\" — counts (log color)", fontsize=12)

def ab(v):
    v=int(v)
    if v>=1e6: return f"{v/1e6:.1f}M"
    if v>=1e3: return f"{v/1e3:.0f}k"
    return str(v)
for i in range(M.shape[0]):
    for j in range(M.shape[1]):
        if M[i,j]>0:
            # contrast: light text on dark cells
            frac=(np.log10(M[i,j])-np.log10(np.nanmin(disp)))/(np.log10(np.nanmax(disp))-np.log10(np.nanmin(disp))+1e-9)
            ax.text(j,i,ab(M[i,j]),ha="center",va="center",fontsize=6.5,color=("white" if frac<0.6 else "black"))
ax.set_xticks(np.arange(-.5,len(cols),1),minor=True); ax.set_yticks(np.arange(-.5,len(labels),1),minor=True)
ax.grid(which="minor",color="white",linewidth=.6); ax.tick_params(which="minor",length=0)
fig.colorbar(im,ax=ax,fraction=0.025,pad=0.02,label="count")
fig.tight_layout()
fig.savefig("/tmp/prog_matrix.png", dpi=130, bbox_inches="tight")
print("rows",M.shape[0],"cols",M.shape[1],"total edges",int(M.sum()),"wrote /tmp/prog_matrix.png")
