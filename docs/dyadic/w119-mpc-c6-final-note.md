# W119: checked completion of the concrete Mpc class-six step

The explicit class-six marked correction is now proved inside Lean.  A guarded Jacobi rule is
derived from Hall-Witt and the depth-six deletion law.  The final module then checks 65 explicit
relation rows and assembles them semantically by permuting central depth-five factors and
cancelling duplicate pairs.

No external computation is trusted.  The generator emits ordinary terms of the checked
derivation language; the Boolean checks reduce in the kernel, and `Deriv.sound` supplies each
group equality.  The final path proves:

- the 65-factor endpoint evaluates to one;
- the reflected certificate word evaluates to one;
- `MpcMkC6CertificateKill`;
- `MpcMkFullSupply 4 mpcFvW5`.

All final semantic declarations use exactly the standard three axioms.  The remaining M6 work is
the uniform successor reflection theorem, not the concrete class-six base.
