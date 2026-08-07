SetColumns(0); SetAutoColumns(false);
OUT:="c6size.out"; System("rm -f c6size.out");
F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
G := quo< F | (fx0^fs)^-1*(fx0^3)^-1*fx1^2*(fx1,fx1^fs)*(fu,fv) >;
t0:=Cputime(); Q:=pQuotient(G,2,6); P:=pCentralSeries(Q,2);
PrintFile(OUT, Sprintf("h=1 class 6: 2^%o, layers %o, %o s", Ilog2(#Q),
   [Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1]], Cputime(t0)));
quit;
