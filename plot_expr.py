import numpy as np, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm
d = np.genfromtxt("/tmp/expressivity.csv", delimiter=",", names=True)
uo=d["uniqueOut"]; ent=d["entropy"]; nE=d["nEmpty"]; nId=d["nIdentity"]; sx=d["sensX"]; sp=d["sensP"]; nodes=d["nodes"]; sz=d["avgSize"]
N=len(uo)
fig,ax=plt.subplots(2,3,figsize=(18,10))
fig.suptitle(f"Expressivity of {N:,} fuzzed MORKL programs on a fixed bank of 100 (trie, path) inputs",fontsize=14,y=0.98)

# A: histogram of unique outputs
a=ax[0,0]; a.hist(uo,bins=np.arange(1,102)-0.5,color="#3b6db5"); a.set_yscale("log")
a.set_xlabel("# distinct outputs over 100 inputs"); a.set_ylabel("# programs (log)"); a.set_title("(A) output variety  — median=%d, mean=%.1f"%(int(np.median(uo)),uo.mean()))
a.axvline(1,color="crimson",ls=":",lw=1)

# B: interestingness classes
emptyConst=int(np.sum((uo==1)&(nE==100))); neConst=int(np.sum((uo==1)&(nE<100)))
low=int(np.sum((uo>=2)&(uo<=5))); mid=int(np.sum((uo>=6)&(uo<=50))); high=int(np.sum((uo>=51)&(uo<=99))); bij=int(np.sum(uo==100))
cls=[emptyConst,neConst,low,mid,high,bij]; lbl=["const ∅\n(always empty)","const ≠∅","low\n2–5","mid\n6–50","high\n51–99","bijective\n=100"]
col=["#bbbbbb","#888888","#c6dbef","#6baed6","#3182bd","#08519c"]
b=ax[0,1]; bars=b.bar(range(6),cls,color=col); b.set_yscale("log"); b.set_xticks(range(6)); b.set_xticklabels(lbl,fontsize=9)
for r,c in zip(bars,cls): b.text(r.get_x()+r.get_width()/2,c,f"{100*c/N:.1f}%",ha="center",va="bottom",fontsize=9)
b.set_title("(B) interestingness classes"); b.set_ylabel("# programs (log)")

# C: entropy distribution
c=ax[0,2]; c.hist(ent,bins=60,color="#2a9d8f"); c.set_yscale("log"); c.set_xlabel("output entropy (bits, max=log2 100≈6.64)"); c.set_ylabel("# programs (log)")
c.set_title("(C) output entropy — variety weighted by balance")

# D: sensitivity to x vs p
e=ax[1,0]; h=e.hist2d(np.clip(sx,1,100),np.clip(sp,1,100),bins=[np.arange(1,52),np.arange(1,52)],norm=LogNorm(),cmap="magma")
e.set_xlabel("distinct outputs when only x (trie) varies"); e.set_ylabel("when only p (path) varies"); e.set_title("(D) responsiveness: space input vs path input")
fig.colorbar(h[3],ax=e,fraction=0.046,pad=0.04,label="# programs")
dependsX=100*np.mean(sx>1); dependsP=100*np.mean(sp>1); both=100*np.mean((sx>1)&(sp>1)); neither=100*np.mean((sx==1)&(sp==1))
e.text(0.98,0.97,f"depends on x: {dependsX:.0f}%\ndepends on p: {dependsP:.0f}%\nboth: {both:.0f}%\nneither: {neither:.0f}%",
       transform=e.transAxes,ha="right",va="top",fontsize=9,color="white",bbox=dict(fc="black",alpha=.5))

# E: unique outputs vs program size
f=ax[1,1]; h2=f.hist2d(nodes,uo,bins=[np.arange(12,nodes.max()+2,2),np.arange(1,102,3)],norm=LogNorm(),cmap="viridis")
f.set_xlabel("program size (# nodes)"); f.set_ylabel("# distinct outputs"); f.set_title("(E) expressivity vs program size")
fig.colorbar(h2[3],ax=f,fraction=0.046,pad=0.04,label="# programs")

# F: identity-likeness + summary text
g=ax[1,2]; g.axis("off")
anyId=100*np.mean(nId>0); mostlyId=100*np.mean(nId>=90); alwaysEmpty=100*np.mean(nE==100); someEmpty=100*np.mean(nE>0)
txt=("SUMMARY (N=%d programs, 100 inputs each)\n\n"
     "distinct outputs:  median %d,  mean %.1f,  max %d\n\n"
     "constant (1 output):        %.1f%%\n"
     "   – of which always ∅:     %.1f%%\n"
     "low variety (≤5):           %.1f%%\n"
     "mid (6–50):                 %.1f%%\n"
     "high (51–99):               %.1f%%\n"
     "bijective (=100):           %.1f%%\n\n"
     "responds to space x:        %.1f%%\n"
     "responds to path p:         %.1f%%\n"
     "responds to both:           %.1f%%\n"
     "responds to neither:        %.1f%%\n\n"
     "≥1 identity output (out=x):  %.1f%%\n"
     "some empty output:          %.1f%%\n"
     "mean output |size|:         %.2f"
     )%(N,int(np.median(uo)),uo.mean(),int(uo.max()),
        100*np.mean(uo==1),100*np.mean((uo==1)&(nE==100)),
        100*np.mean(uo<=5),100*np.mean((uo>=6)&(uo<=50)),100*np.mean((uo>=51)&(uo<=99)),100*np.mean(uo==100),
        dependsX,dependsP,both,neither,anyId,someEmpty,sz.mean())
g.text(0.0,1.0,txt,va="top",ha="left",fontsize=11,family="monospace")
fig.tight_layout(rect=[0,0,1,0.96]); fig.savefig("/tmp/expressivity.png",dpi=120,bbox_inches="tight")
print("wrote /tmp/expressivity.png")
