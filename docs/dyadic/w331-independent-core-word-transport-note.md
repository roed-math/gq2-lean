# W331: independent corrected core and word transport

W331 removes two unnecessary couplings from the general flexible route.

`WordCertificateRN.transportWordEquiv` changes the candidate word by precomposing the existing
pro-2 map with an equivalence of corrected candidate groups.  Kernel and surjectivity follow
from the equivalence, so no new `CorePresentation` is needed.  The tame commuting square is the
only boundary equation.

`WordCertificateRN.transportCoreWord` composes this with W330, allowing the marked core and the
source word to move independently.  `GenAsmFlexibleRowResidualRN.ofCoreWordTransport` and the
final compatible assembler then consume those two equivalences directly.

This is a structural general-case reduction.  It leaves no analytic reproof when a suitable
normal form is isomorphic to a certified reference pair.  It does not claim that every field
marking belongs to the reference marking's automorphism orbit; mobile-pivot normal forms may
still require a certificate constructed directly at their adapted marking.

The three transport declarations print exactly the standard trust base.  The final field
equivalence inherits only the established general-assembly arithmetic axioms.
