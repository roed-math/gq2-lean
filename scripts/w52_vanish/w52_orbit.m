/*  W52-VANISH -- torsor invariance of the containment: does the relator's defect land in
 *  im delta along ARBITRARY clearing orbits, not just the greedy one?
 *
 *      magma -b cls:=4 marks:="0,1;1,1" no:=20 seed:=7 out:=../../data/w52orbit_c4.txt w52_orbit.m
 *
 *  The sweeps always take the first stage-A survivor and the particular solution of each
 *  level's linear system.  The level-(j+1) defect class changes, as the level-j clearing
 *  moves inside its solution torsor x0 + ker delta_j, by second-order terms invisible to
 *  the level-j layer; if the containment were an accident of the greedy path, a random
 *  point of the torsor would strand the lift at the next level with positive probability
 *  (a random vector misses a codimension-6 image 63 times of 64).  So: per orbit, pick a
 *  random stage-A survivor of the 6 and, at every level, the particular solution plus a
 *  RANDOM element of the kernel; record whether the defect stays in im delta at every level.
 */
SetColumns(0); SetAutoColumns(false);
load "../w50_depth_sweep/c0.m";

CLS := StringToInteger(cls);
NO := StringToInteger(no);
SetSeed(StringToInteger(seed));
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

MARKS := [];
for chunk in Split(marks, ";") do
  ab := Split(chunk, ",");
  Append(~MARKS, [StringToInteger(ab[1]), StringToInteger(ab[2])]);
end for;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
Say(Sprintf("W52 orbit probe -- class %o, layers %o, %o random orbits per marking", CLS, dm, NO));
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
for w in [1..CLS] do
  assert NPCgens(P[w]) eq n - ofs[w];
  assert Q.(ofs[w]+1) in P[w];
  assert not (Q.(ofs[w]+1) in P[w+1]);
end for;
Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
CoordChecked := function(x, w)
  e := Eltseq(x);
  for k in [1..ofs[w]] do assert e[k] eq 0; end for;
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
IndepSubset := function(cands, w)
  A := Matrix([ Coord(x, w) : x in cands ]);
  E := EchelonForm(Transpose(A));
  piv := [];
  for i in [1..Nrows(E)] do
    d := Depth(E[i]);
    if d ne 0 then Append(~piv, d); end if;
  end for;
  return [ cands[j] : j in piv ];
end function;

gQ  := [Q.i : i in [1..5]];
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
pw := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  KB := [ IndepSubset([UQ, VQ, tbQ], 1) ];
  for w in [2..CLS-1] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..5] do Append(~cands, (x, gQ[i])); end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    Append(~KB, IndepSubset(cands, w));
  end for;
  for w in [1..CLS-1] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    assert (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]);
  end for;
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];

  /* the six stage-A survivors: forced core code times the GL2 handle torsor.  The forced
     code is fc on sigma and x0; the handle block (a3, a4) ranges over the images of (U, V)
     under GL2(F2), realized as codes: (U,V), (V,U), (U, UV), (UV, U), (V, UV), (UV, V) --
     here as multiplications of the two handle slots by elements of {1, U, V, UV}.  Stage A
     of W50 measured exactly 6 survivors of this shape; each is re-verified before use. */
  fc := 4*(s mod 2) + 2*(t mod 2);
  handleCodes := [ [1, 1], [7, 7], [1, 5], [3, 7], [7, 5], [3, 1] ];
    /* dress indices into dressQ (1-based): 1 = trivial, 3 = V, 5 = U, 7 = UV;
       the pairs realize the GL2(F2) images (U,V), (V,U), (U,UV), (UV,U), (V,UV), (UV,V)
       of the handle pair, as additive dressing codes mod squares */
  contain := 0; total := 0; orbfail := 0;
  for orb in [1..NO] do
    hc := handleCodes[Random(1, 6)];
    m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3],
           base[4]*dressQ[hc[1]], base[5]*dressQ[hc[2]] ];
    /* stage-A survivor check: relator dies at class 2, frame generates mod Frattini */
    r := Rel(m);
    if not (r in P[3]) then
      Say(Sprintf("  (t,s)=(%o,%o) orbit %o: chosen handle code is NOT a survivor -- skip", t, s, orb));
      orbfail +:= 1; continue;
    end if;
    M := Matrix(GF(2), 5, 5, [ [ GF(2)!e : e in Eltseq(x)[1..5] ] : x in m ]);
    assert Rank(M) eq 5;
    line := Sprintf("  (t,s)=(%o,%o) orbit %o hc=%o: ", t, s, orb, hc);
    ok_all := true;
    for j in [3..CLS] do
      if r in P[j+1] then line cat:= Sprintf("L%o(triv) ", j); continue; end if;
      reps := KB[j-1]; nb := #reps;
      rows := [];
      for i in [1..5] do for b in reps do
        mm := m; mm[i] := m[i]*b;
        Append(~rows, Coord(Rel(mm) * r^-1, j));
      end for; end for;
      A := Matrix(rows);
      tar := CoordChecked(r^-1, j);
      total +:= 1;
      okc, x0 := IsConsistent(A, tar);
      if not okc then
        line cat:= Sprintf("L%o NOT-IN-IMAGE ", j);
        ok_all := false; break;
      end if;
      contain +:= 1;
      /* random point of the solution torsor */
      NS := NullspaceMatrix(A);
      x := x0;
      for k in [1..Nrows(NS)] do
        if Random(0,1) eq 1 then x +:= NS[k]; end if;
      end for;
      assert x*A eq tar;
      for i in [1..5] do for l in [1..nb] do
        if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
      end for; end for;
      r := Rel(m);
      assert r in P[j+1];
      line cat:= Sprintf("L%o[in-im, random torsor point] ", j);
    end for;
    if ok_all then line cat:= (r eq Id(Q)) select "SOLVED" else "cleared"; end if;
    Say(line);
  end for;
  Say(Sprintf("  (t,s)=(%o,%o): containment %o of %o level events along %o random orbits (skips %o)",
      t, s, contain, total, NO, orbfail));
end for;
Say("DONE");
