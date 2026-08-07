/*  W51 -- class-6 build probe for D_sq 1.
 *
 *      magma -b out:=../../data/c6build.txt c6build.m
 *
 *  W50 (c6size.m) ran a bare pQuotient(G,2,6) and had not finished after ~50 min / ~700 MB.
 *  This probe instead walks the tower with pQuotientProcess/NextClass so that
 *    (a) every intermediate class is timed and reported the moment it exists, and
 *    (b) if class 6 does not finish we still know exactly where the wall is.
 *  Output is flushed line by line, so a kill -9 still leaves the measurement behind.
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); end procedure;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;

Say("W51 class-6 build probe (pQuotientProcess / NextClass)");
Say(Sprintf("relator: %o", RELW));
Say("");

tall := Cputime();
t0 := Cputime();
PR := pQuotientProcess(G, 2, 1);
Say(Sprintf("class 1 process built, %o s", Cputime(t0)));

for c in [2..6] do
  t0 := Cputime();
  NextClass(~PR);
  dt := Cputime(t0);
  Q := ExtractGroup(PR);
  P := pCentralSeries(Q, 2);
  rk := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
  Say(Sprintf("class %o : order 2^%o  layers %o  step %o s  cumulative %o s  mem %o MB",
      c, Ilog2(#Q), rk, dt, Cputime(tall), GetMemoryUsage() div (1024*1024)));
end for;
Say("DONE");
quit;
