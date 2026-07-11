import numpy as np, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm
d=np.genfromtxt("/tmp/expressivity.csv",delimiter=",",names=True)
uo=d["uniqueOut"];ent=d["entropy"];nE=d["nEmpty"];ns=d["nSpace"].astype(int);npp=d["nPath"].astype(int)
rs=d["respSpace"].astype(int);rp=d["respPath"].astype(int);rf=d["respFrac"];sz=d["avgSize"];nodes=d["nodes"]
N=len(uo); nArgs=ns+npp; rArgs=rs+rp
fig,ax=plt.subplots(2,3,figsize=(18,10))
fig.suptitle(f"{N:,} fuzzed MORKL programs with variable args (space 1–3, path 0–2), 100 inputs each",fontsize=14,y=0.99)

# A unique outputs
a=ax[0,0]; a.hist(uo,bins=np.arange(1,102)-0.5,color="#3b6db5"); a.set_yscale("log")
a.set_xlabel("# distinct outputs / 100 inputs"); a.set_ylabel("# programs (log)")
a.set_title("(A) output variety — median %d, mean %.1f"%(int(np.median(uo)),uo.mean())); a.axvline(1,color="crimson",ls=":")

# B arg-count distribution (ns x np)
b=ax[0,1]; M=np.zeros((4,3))  # ns 1..3 rows(use 0..3), np 0..2 cols
for i in range(1,4):
  for j in range(0,3): M[i,j]=np.sum((ns==i)&(npp==j))
im=b.imshow(M[1:4,:],origin="lower",cmap="Blues",aspect="auto")
b.set_xticks(range(3));b.set_xticklabels(range(3));b.set_yticks(range(3));b.set_yticklabels(range(1,4))
b.set_xlabel("# path args");b.set_ylabel("# space args");b.set_title("(B) argument-count mix")
for i in range(3):
  for j in range(3): b.text(j,i,f"{100*M[i+1,j]/N:.1f}%",ha="center",va="center",fontsize=10,color="black")

# C responsiveness parameter respFrac
c=ax[0,2]; c.hist(rf,bins=np.linspace(0,1,21),color="#2a9d8f"); c.set_yscale("log")
c.set_xlabel("responsiveness = responded args / total args"); c.set_ylabel("# programs (log)")
c.set_title("(C) responsiveness parameter — mean %.2f"%rf.mean())

# D responded args: space vs path (rate per arg present)
e=ax[1,0]
# per-arg responsiveness rate: total responded / total present, for space and path
spaceRate=rs.sum()/ns.sum()*100; pathRate=rp.sum()/npp[npp>0].sum()*100 if npp.sum()>0 else 0
# distribution of #responded args
maxr=int(rArgs.max())
e.hist(rArgs,bins=np.arange(0,maxr+2)-0.5,color="#7048aa")
e.set_xlabel("# args the program responds to"); e.set_ylabel("# programs"); e.set_yscale("log")
e.set_title("(D) responded-arg count")
e.text(0.97,0.95,f"per space-arg responded: {spaceRate:.0f}%\nper path-arg responded: {pathRate:.0f}%\n"
       f"responds to 0 args: {100*np.mean(rArgs==0):.0f}%\n>=1: {100*np.mean(rArgs>=1):.0f}%\nall args: {100*np.mean(rArgs==nArgs):.0f}%",
       transform=e.transAxes,ha="right",va="top",fontsize=9,bbox=dict(fc="white",alpha=.8))

# E unique outputs vs responsiveness
f=ax[1,1]; h=f.hist2d(rf,uo,bins=[np.linspace(0,1,21),np.arange(1,102,3)],norm=LogNorm(),cmap="viridis")
f.set_xlabel("responsiveness (respFrac)"); f.set_ylabel("# distinct outputs"); f.set_title("(E) output variety vs responsiveness")
fig.colorbar(h[3],ax=f,fraction=0.046,pad=0.04,label="# programs")

# F summary
g=ax[1,2]; g.axis("off")
def m(x): return 100*np.mean(x)
# responsiveness-filtered view
resp=rArgs>=1
txt=("SUMMARY  (N=%d, 100 inputs each)\n\n"
     "args/program:   space mean %.2f, path mean %.2f\n"
     "distinct outputs: median %d, mean %.1f, max %d\n\n"
     "RESPONSIVENESS\n"
     "  responds to 0 args (inert):  %.1f%%\n"
     "  responds to >=1 arg:         %.1f%%\n"
     "  responds to ALL its args:    %.1f%%\n"
     "  mean respFrac:               %.2f\n"
     "  per space-arg responded:     %.0f%%\n"
     "  per path-arg responded:      %.0f%%\n\n"
     "OUTPUTS\n"
     "  constant (1 output):         %.1f%%\n"
     "  some empty output:           %.1f%%\n"
     "  high variety (>50):          %.1f%%\n\n"
     "AMONG RESPONSIVE (>=1 arg):\n"
     "  median distinct outputs:     %d\n"
     "  high variety (>50):          %.1f%%\n"
     "  constant:                    %.1f%%"
     )%(N,ns.mean(),npp.mean(),int(np.median(uo)),uo.mean(),int(uo.max()),
        m(rArgs==0),m(rArgs>=1),m(rArgs==nArgs),rf.mean(),spaceRate,pathRate,
        m(uo==1),m(nE>0),m(uo>50),
        int(np.median(uo[resp])),m(uo[resp]>50),m(uo[resp]==1))
g.text(0,1,txt,va="top",ha="left",fontsize=10.5,family="monospace")
fig.tight_layout(rect=[0,0,1,0.96]); fig.savefig("/tmp/expressivity2.png",dpi=120,bbox_inches="tight")
print("OK")
