/*  W50 -- the optional h = 2 spot-check.
 *
 *      magma -b cls:=3 out:=h2_c3.txt w50_h2.m
 *      magma -b cls:=4 out:=h2_c4.txt w50_h2.m
 *
 *  D_sq 2 on sigma, x0, x1, u1, v1, u2, v2 (sqRank 2 = 7), relator
 *      sqWord(sigma,x0,x1) * [u1,v1] * [u2,v2].
 *  nu' = nuSel 2 j t s  puts (t,s) on handle j and 0 on the other, so the other handle is
 *  already cleared; SqClearingStep asks for handle j to be cleared with the other handle's
 *  rows left where they are -- automatic, since every dressing is nu'-trivial
 *  (nu_sqArbFrame_handleU_ne).  So the conditions are again exactly
 *      a_i in K = ker lam cap ker nu' ,  R(m) = 1 ,  SqModTwoIndep(m).
 *
 *  K/(K cap P_2) is now 5-dimensional -- basis U, V, tbar, u', v' (the other handle's two
 *  letters are lam- and nu'-trivial) -- so 32 codes per slot and 32^7 = 3.4e10 level-one
 *  tuples.  Exhaustive enumeration is out; the search below uses the h = 1 structure
 *  (sigma and x0 carry the forced dressing U^-s V^t, x1 undressed) and enumerates the two
 *  handle blocks, then falls back to random sampling.
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "c0.m";
CLS := StringToInteger(cls);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); end procedure;

F<fs,fx0,fx1,fu1,fv1,fu2,fv2> := FreeGroup(7);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu1,fv1) * (fu2,fv2);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]) * (m[6],m[7]);
end function;
Coord := function(q,x) return Vector(GF(2),[GF(2)!e : e in Eltseq(q(x))]); end function;

tt := Cputime();
Q, phi := pQuotient(G, 2, CLS);
P  := pCentralSeries(Q, 2);
gQ := [phi(G.i) : i in [1..7]];
DQ := DerivedSubgroup(Q);
wQ := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ:= (gQ[2]^2)^-1 * gQ[3];
Say(Sprintf("W50 h=2 spot-check -- class %o", CLS));
Say(Sprintf("relator: %o", RELW));
Say(Sprintf("Q : order 2^%o, layers %o, Q^ab %o  (%o s)", Ilog2(#Q),
   [Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1]], AbelianQuotientInvariants(Q), Cputime(tt)));
assert Rel(gQ) eq Id(Q);
Say("cross-check: Rel(standard generators) = 1 in Q .. OK");

LayerBasis := function(K, Pj, Pj1)
  V, q := quo< Pj | Pj1 >;
  gens := [ x : x in PCGenerators(K meet Pj) ];
  A := Matrix(GF(2), [ [ GF(2)!e : e in Eltseq(q(x)) ] : x in gens ]);
  E, T := EchelonForm(A);
  reps := [];
  for k in [1..Rank(A)] do
    y := Id(Q);
    for l in [1..#gens] do if T[k][l] ne 0 then y := y * gens[l]; end if; end for;
    Append(~reps, y);
  end for;
  return reps, NPCgens(V);
end function;

MOD := 2^CLS;
if assigned tmax then MOD := Min(MOD, StringToInteger(tmax)); end if;
Say(Sprintf("markings: (t,s) in [0..%o]^2, both handles", MOD-1));
Say("");
Say("  j   t   s | lvl1 tries | verdict    | delta ranks");
Say("------------+------------+------------+-------------------------------");

nsolv := 0; ninf := 0; infeas := [];
for j in [0..1] do
 iu := 4 + 2*j; iv := 5 + 2*j;          // 1-based slot indices of handle j
 ou := 4 + 2*(1-j); ov := 5 + 2*(1-j);  // the other handle
 for t in [0..MOD-1] do
  for s in [0..MOD-1] do
   if t eq 0 and s eq 0 then continue; end if;
   UQ := (wQ^t)^-1 * gQ[iu];  VQ := gQ[iv] * (wQ^s)^-1;
   base := gQ; base[iu] := UQ; base[iv] := VQ;
   K := sub< Q | UQ, VQ, tbQ, gQ[ou], gQ[ov], DQ >;
   assert Index(Q, K) eq 4^CLS;

   // level-one alphabet: 32 codes per slot over the basis U, V, tbar, u', v'
   KB := [UQ, VQ, tbQ, gQ[ou], gQ[ov]];
   dr := function(code)
     y := Id(Q);
     for l in [1..5] do if ((code div 2^(l-1)) mod 2) ne 0 then y := y * KB[l]; end if; end for;
     return y;
   end function;
   fc := (s mod 2) + 2*(t mod 2);       // U^-s V^t mod squares, in the KB coding

   // candidate level-one tuples: the h=1 structure on the core, both handle blocks free
   cands := [];
   for hb in [0..1023] do
     c := [fc, fc, 0, 0, 0, 0, 0];
     c[iu] := hb mod 32; c[iv] := (hb div 32) mod 32;
     Append(~cands, c);
   end for;
   // and a random tail over all seven slots
   for k in [1..3000] do
     Append(~cands, [Random(0,31) : l in [1..7]]);
   end for;

   W1b, qq1 := quo< Q | P[2] >;
   surv := [];
   for c in cands do
     m := [ base[l] * dr(c[l]) : l in [1..7] ];
     if not (Rel(m) in P[3]) then continue; end if;
     if Rank(Matrix(GF(2),7,7,[Coord(qq1,m[l])[k] : k in [1..7], l in [1..7]])) ne 7 then
       continue; end if;
     Append(~surv, c);
     if #surv ge 8 then break; end if;
   end for;

   LB := [];
   for jj in [3..CLS] do LB[jj] := LayerBasis(K, P[jj-1], P[jj]); end for;

   verdict := "INFEASIBLE"; info := "";
   for c in surv do
     m := [ base[l] * dr(c[l]) : l in [1..7] ];
     r := Rel(m); good := true; inf2 := "";
     for jj in [3..CLS] do
       if r eq Id(Q) then break; end if;
       if r in P[jj+1] then continue; end if;
       reps := LB[jj];
       Vt, qtar := quo< P[jj] | P[jj+1] >;
       rows := [];
       for l in [1..7] do for b in reps do
         mm := m; mm[l] := m[l]*b;
         Append(~rows, Coord(qtar, Rel(mm) * r^-1));
       end for; end for;
       A := Matrix(rows);
       ok, x := IsConsistent(A, Coord(qtar, r^-1));
       inf2 cat:= Sprintf(" [L%o:%o/%o]", jj, Rank(A), NPCgens(Vt));
       if not ok then good := false; break; end if;
       nb := #reps;
       for l in [1..7] do for k in [1..nb] do
         if x[(l-1)*nb + k] ne 0 then m[l] := m[l] * reps[k]; end if;
       end for; end for;
       r := Rel(m);
     end for;
     if good and r eq Id(Q) then
       assert Rank(Matrix(GF(2),7,7,[Coord(qq1,m[l])[k] : k in [1..7], l in [1..7]])) eq 7;
       for l in [1..7] do assert (base[l]^-1 * m[l]) in K; end for;
       verdict := "solvable"; info := inf2; break;
     end if;
   end for;
   if verdict eq "solvable" then nsolv +:= 1; else ninf +:= 1; Append(~infeas,[j,t,s]); end if;
   Say(Sprintf("%3o %3o %3o | %10o | %-10o |%o", j, t, s, #surv, verdict, info));
  end for;
 end for;
end for;

Say("");
Say(Sprintf("SUMMARY h=2 class %o : solvable %o, INFEASIBLE %o", CLS, nsolv, ninf));
if #infeas gt 0 then Say(Sprintf("INFEASIBLE (j,t,s): %o", infeas)); end if;
Say("DONE");
quit;
