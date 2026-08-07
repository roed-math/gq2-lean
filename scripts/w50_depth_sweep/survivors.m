/*  W50 -- structure of the level-one survivor set (the class-two balance gate),
 *  and the calibration reproductions:
 *    (i)  the forced x0-slot dressing  a1 = U^-s V^t   (GradedTwo S6)
 *    (ii) the W48 "0/60" run: the forced-alone dressing over Z/8 at class 3
 *    (iii) the restricted U/V-word family vs the arbitrary family
 *
 *  magma -b out:=surv.txt survivors.m
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "c0.m";
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); end procedure;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;
Coord := function(q,x) return Vector(GF(2),[GF(2)!e : e in Eltseq(q(x))]); end function;

Q2, phi2 := pQuotient(G, 2, 2);
P2s := pCentralSeries(Q2, 2);
g2  := [phi2(G.i) : i in [1..5]];
w2  := g2[1] * (g2[2]^(C0 mod 16))^-1;
tb2 := (g2[2]^2)^-1 * g2[3];
W1, q1 := quo< Q2 | P2s[2] >;

names := ["1", "t", "V", "Vt", "U", "Ut", "UV", "UVt"];

Say("=== level-one survivor sets of the class-two balance gate (Q_2, order 2^19) ===");
Say("code a  <->  dressing  U^(a div 4) V^((a div 2) mod 2) tbar^(a mod 2)");
Say("slots in order (sigma, x0, x1, u, v)");
Say("");
for t in [0..3] do for s in [0..3] do
  U2 := (w2^t)^-1 * g2[4];  V2 := g2[5] * (w2^s)^-1;
  base2 := [g2[1], g2[2], g2[3], U2, V2];
  dr := [ U2^(a div 4) * V2^((a div 2) mod 2) * tb2^(a mod 2) : a in [0..7] ];
  surv := []; survI := [];
  for code in [0..8^5-1] do
    e := [ (code div 8^(i-1)) mod 8 : i in [1..5] ];
    m := [ base2[i] * dr[e[i]+1] : i in [1..5] ];
    if Rel(m) ne Id(Q2) then continue; end if;
    Append(~surv, e);
    M := Matrix(GF(2),5,5,[Coord(q1,m[i])[k] : k in [1..5], i in [1..5]]);
    if Rank(M) eq 5 then Append(~survI, e); end if;
  end for;
  // the forced x0-slot value  U^-s V^t  reduced mod squares
  forced := 4*(s mod 2) + 2*(t mod 2);
  x0codes := { e[2] : e in survI };
  Say(Sprintf("(t,s)=(%o,%o) mod 4 : relator-killing %o, +indep %o ; x0-slot codes %o ; forced U^-s V^t = %o (%o)",
      t, s, #surv, #survI, x0codes, forced, names[forced+1]));
  for e in survI do
    Say(Sprintf("      %o   =  (%o, %o, %o, %o, %o)", e,
        names[e[1]+1], names[e[2]+1], names[e[3]+1], names[e[4]+1], names[e[5]+1]));
  end for;
  // affine-coset test: is survI a coset of a subgroup of F_2^15 ?
  vecs := [ Vector(GF(2), &cat[ [GF(2)!((e[i] div 4) mod 2), GF(2)!((e[i] div 2) mod 2),
                                GF(2)!(e[i] mod 2)] : i in [1..5] ]) : e in survI ];
  if #vecs gt 0 then
    d := [ v - vecs[1] : v in vecs ];
    S := sub< VectorSpace(GF(2),15) | d >;
    Say(Sprintf("      differences span a %o-dim space; coset? %o (|space| %o vs #surv %o)",
        Dimension(S), #d eq #S, #S, #survI));
  end if;
end for; end for;

Say("");
Say("=== calibration (ii): the W48 forced-alone dressing a1 = U^-s V^t at class 3, (t,s) mod 8 ===");
Q3, phi3 := pQuotient(G, 2, 3);
g3 := [phi3(G.i) : i in [1..5]];
w3 := g3[1] * (g3[2]^(C0 mod 32))^-1;
P3s := pCentralSeries(Q3,2);
nfail2 := 0; nfail3 := 0; ntot := 0;
for t in [0..7] do for s in [0..7] do
  if t eq 0 and s eq 0 then continue; end if;
  U3 := (w3^t)^-1 * g3[4]; V3 := g3[5] * (w3^s)^-1;
  m := [g3[1], g3[2]*(U3^(-s))*(V3^t), g3[3], U3, V3];
  r := Rel(m);
  ntot +:= 1;
  if not (r in P3s[3]) then nfail2 +:= 1; end if;    // class-two defect survives
  if r ne Id(Q3) then nfail3 +:= 1; end if;          // class-three defect survives
end for; end for;
Say(Sprintf("forced-alone dressing, %o uncleared markings mod 8:", ntot));
Say(Sprintf("   class-two failures  : %o / %o", nfail2, ntot));
Say(Sprintf("   class-three failures: %o / %o", nfail3, ntot));
Say("DONE");
quit;
