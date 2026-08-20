# W336: Nielsen transport of core presentations

W336 proves that the changed-word route preserves the complete pro-2 presentation,
not merely its visible generator rows.

For an inverse syntactic Nielsen pair fixing the tame letter,
`CorePresentation.ofNielsen` substitutes the inverse transformation into the word and
the forward transformation into the marking.  It proves the transformed relation,
universal lift, computation law, and homomorphism uniqueness.  Cancellation is checked
at arbitrary profinite markings through the free profinite universal property.

`CorePresentation.mapEquiv` independently transports the presented target group through
a continuous equivalence.  The combined constructor
`FlexibleCoreLeavesRN.ofNielsenEquiv` therefore reduces an adapted field-core
presentation to exactly the normalized sigma and wild rows of the transformed marking.

All declarations have the standard trust base and are uniform in the alphabet rank and
the presentation word.  The remaining even-M construction is now sharply algebraic:
from the mobile exact pivot, choose a tau-fixing Nielsen composite whose transformed
field marking has the standard unramified rows.  W334 then supplies the analytic
certificate and final field equivalence automatically.
