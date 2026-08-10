"""W61-WIDER step 11: is the three-channel functional LIVE at wave 60's binder point?

The Lean file proves the class-five row moves by `SqU6.gaTwoShiftChan` and by nothing else on
the achievable lattice.  Whether that gives an EXCLUSION one filtration step wider than wave
60's is then a question about the functional alone.  This file answers it with the cheap and
decisive part of the census: the pairwise commutators of the point's letters are achievable
`gamma_2`-dressings by definition, so if the functional is odd on one of them it is live.

Group law: `w59_force5/u6mat.py`, honest 6 x 6 matrices.  Nothing is read from Lean.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))
import u6mat as M

SIG = M.sigFiveMark
X = M.named(a=2, e=5)
U = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
V = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
Y = M.named(e=2, f=1, g=1, h=1, m=3, n=3)
IDX = {c: k for k, c in enumerate(M.COORDS)}
def co(z, c): return z[IDX[c]]
def channel(z, L):
    return (co(z,"m")*co(L,"e") + co(z,"i")*co(L,"j") + co(z,"l")*co(L,"f")) % 8
def fox(s,x,y): return tuple((10*x[k]-s[k]-8*y[k]) % 8 for k in range(15))

letters=[SIG,X,Y,U,V]; names=["sigma","x0","x1","U","V"]
base=[M.mul(SIG,X),X,Y,U,V]; BETA=[X,fox(SIG,X,Y),Y,V,U]

print("=" * 92)
print("== 1. the pairwise commutators of the point's letters: achievable gamma_2-dressings ==")
gens={}
for i,a in enumerate(letters):
    for j,b in enumerate(letters):
        if i<j:
            c=M.commP(a,b)
            if c!=M.ONE: gens["[%s,%s]"%(names[i],names[j])]=c
for k,z in sorted(gens.items()):
    print("   %-12s = %-46s  f,h,j = %d,%d,%d   i,l,m = %d,%d,%d"
          % (k, M.show(z), co(z,"f")%2, co(z,"h")%2, co(z,"j")%2,
             co(z,"i")%2, co(z,"l")%2, co(z,"m")%2))
print()
bad=[k for k,z in gens.items() if co(z,"f")%2 or co(z,"h")%2 or co(z,"j")%2]
print("   wave 60's stageN2 (f, h, j all even) holds for every one: %s" % (not bad))
print()

print("=" * 92)
print("== 2. the three-channel functional on these generators ==")
live=[]
for k,z in sorted(gens.items()):
    vals=[channel(z,BETA[i])%2 for i in range(5)]
    if any(vals): live.append((k,vals))
    print("   %-12s : channel parity per slot (sigma,x0,x1,U,V) = %s" % (k, vals))
print()
print("   the functional is LIVE on the achievable lattice: %s (%d of %d generators)"
      % (bool(live), len(live), len(gens)))
print()

print("=" * 92)
print("== 3. do any of these single-slot moves kill the dressed frame? ==")
kills=0
for k,z in sorted(gens.items()):
    for i in range(5):
        for e in range(1,8):
            zz=z
            for _ in range(e-1): zz=M.mul(zz,z)
            m=list(base); m[i]=M.mul(m[i],zz)
            if M.sqRelWord(m)==M.ONE:
                kills+=1
                print("   KILL: slot %s by %s^%d" % (names[i],k,e))
print("   total kills among the %d generators and their powers, five slots: %d"
      % (len(gens), kills))
