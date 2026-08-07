// W50: sizes of the class-c pro-2 quotients of D_sq 1, incremental output.
SetColumns(0); SetAutoColumns(false);
OUT := "sizes.out";
System("rm -f sizes.out");

F<s,x0,x1,u,v> := FreeGroup(5);
R := (x0^s)^-1 * (x0^3)^-1 * x1^2 * (x1, x1^s) * (u,v);
PrintFile(OUT, Sprintf("relator: %o", R));

G := quo< F | R >;
A := AbelianQuotientInvariants(G);
PrintFile(OUT, Sprintf("G^ab invariants: %o   (want [2] + Z^4)", A));

CMAX := StringToInteger(cmax);
for c in [1..CMAX] do
  t0 := Cputime();
  Q, phi := pQuotient(G, 2, c);
  P := pCentralSeries(Q, 2);
  rk := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
  PrintFile(OUT, Sprintf("class %o : order 2^%o  time %o s  layer ranks %o  Q^ab %o",
      c, Ilog2(#Q), Cputime(t0), rk, AbelianQuotientInvariants(Q)));
end for;
PrintFile(OUT, "DONE");
quit;
