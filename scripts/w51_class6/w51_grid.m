/*  W51 -- continuation of the class-5 marking grid, using the generating-set route.
 *
 *      magma -b lo:=0 hi:=200 out:=../../data/grid_c5_a.txt w51_grid.m
 *
 *  Parameters
 *      lo, hi   index range into the ordered list of uncleared (t,s) mod 32 markings
 *               that W50 had NOT already covered (the 72 banked ones are skipped)
 *      out      output file, one line per marking, flushed as it goes
 *
 *  The marking list is (t,s) in (Z/32)^2 minus (0,0), enumerated t-major, with the 72
 *  markings already recorded in scripts/w50_depth_sweep/results/res_c5.txt and
 *  res_c5tail.txt removed.  Splitting by index range lets several processes share the
 *  grid without coordinating.
 *
 *  Method is exactly w51_corank.m's: graded generating set for K, self-certified at every
 *  level, layer coordinates off the pc exponent vector.  Per marking we report the level-one
 *  dressing used, the rank/corank at L3, L4, L5, whether the relator's defect landed in the
 *  image, and the verdict.
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "../w50_depth_sweep/c0.m";

CLS := 5;
LO := StringToInteger(lo); HI := StringToInteger(hi);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

/* the 72 markings W50 already banked */
DONE := [ [0,1],[0,2],[0,3],[0,4],[0,5],[0,6],[0,7],[1,0],[1,1],[1,2],[1,3],[1,4],[1,5],[1,6],
  [1,7],[2,0],[2,1],[2,2],[2,3],[2,4],[2,5],[2,6],[2,7],[3,0],[3,1],[3,2],[3,3],[3,4],[3,5],
  [3,6],[3,7],[4,0],[4,1],[4,2],[4,3],[4,4],[4,5],[4,6],[4,7],[5,0],[5,1],[5,2],
  [0,8],[8,0],[8,8],[0,16],[16,0],[16,16],[1,8],[8,1],[1,16],[16,1],[3,8],[8,3],[2,16],
  [16,2],[4,8],[8,4],[12,20],[20,12],[9,15],[15,9],[5,11],[11,5],[31,31],[31,1],[1,31],
  [17,17],[24,8],[8,24],[28,4],[4,28] ];
DS := { x : x in DONE };

TODO := [];
for t in [0..31] do for s in [0..31] do
  if t eq 0 and s eq 0 then continue; end if;
  if [t,s] in DS then continue; end if;
  Append(~TODO, [t,s]);
end for; end for;
HI := Min(HI, #TODO);
Say(Sprintf("W51 class-5 grid continuation: %o uncleared markings remain after W50's 72; this run does indices %o..%o", #TODO, LO+1, HI));

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
G := quo< F | (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv) >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

tall := Cputime();
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
for w in [1..CLS] do assert NPCgens(P[w]) eq n - ofs[w]; end for;
Say(Sprintf("Q_5 : order 2^%o, layers %o  (%o s)", Ilog2(#Q), dm, Cputime(tall)));

Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
IndepSubset := function(cands, w)
  E := EchelonForm(Transpose(Matrix([ Coord(x, w) : x in cands ])));
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

/* the commutator part of the generating set is marking independent: build it once */
tc := Cputime();
COMM := [ [] : w in [1..CLS] ];
for w in [2..CLS-1] do
  cs := [];
  for x in LGEN[w-1] do for i in [1..5] do Append(~cs, (x, gQ[i])); end for; end for;
  COMM[w] := cs;
end for;
Say(Sprintf("marking-independent commutator lists [L_{w-1},L_1] built in %o s", Cputime(tc)));
Say("");
Say("  t   s | verdict    | L3 rank/target  L4 rank/target  L5 rank/target | coranks | defect in im | cert | secs");

nsolv := 0; ninf := 0;
for idx in [LO+1..HI] do
  t := TODO[idx][1]; s := TODO[idx][2];
  tm := Cputime();
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];

  KB := [ IndepSubset([UQ, VQ, tbQ], 1) ];
  for w in [2..CLS-1] do
    Append(~KB, IndepSubset(COMM[w] cat [ b^2 : b in KB[w-1] ], w));
  end for;
  cert := true;
  for w in [1..CLS-1] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    cert := cert and (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]);
  end for;

  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s mod 2) + 2*(t mod 2);
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
  r := Rel(m);
  rks := []; cok := []; hit := true; verdict := "solvable";
  for j in [3..CLS] do
    if r in P[j+1] then Append(~rks, Sprintf("L%o:--/%o", j, dm[j])); Append(~cok, -1); continue; end if;
    reps := KB[j-1];
    rows := [];
    for i in [1..5] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      Append(~rows, Coord(Rel(mm) * r^-1, j));
    end for; end for;
    A := Matrix(rows); RS := RowSpace(A); tar := Coord(r^-1, j);
    Append(~rks, Sprintf("L%o:%o/%o", j, Dimension(RS), dm[j]));
    Append(~cok, dm[j]-Dimension(RS));
    hit := hit and (tar in RS);
    ok, x := IsConsistent(A, tar);
    if not ok then verdict := "INFEASIBLE"; break; end if;
    nb := #reps;
    for i in [1..5] do for l in [1..nb] do
      if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
    end for; end for;
    r := Rel(m);
  end for;
  if verdict eq "solvable" then assert r eq Id(Q); nsolv +:= 1; else ninf +:= 1; end if;
  Say(Sprintf("%3o %3o | %-10o | %o | %o | %-12o | %-4o | %o",
      t, s, verdict, rks, cok, hit, cert, Cputime(tm)));
end for;
Say(Sprintf("RANGE %o..%o COMPLETE: %o solvable, %o infeasible, %o s total", LO+1, HI, nsolv, ninf, Cputime(tall)));
Say("DONE");
quit;
