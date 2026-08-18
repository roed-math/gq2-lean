# W268 — the one-handle class-seven relative target

The compact part of the explicit W6-to-W7 correction is now unconditional.  The checked
class-six certificate identifies the exact compact W6 marking, and the uniform marked
successor theorem supplies a legal compact class-seven correction at that named point.

All four compact correction factors lift through handle-forgetting.  The three ordinary
slots use depth-preserving, character-neutral lifts.  The pivot slot requires an additional
argument: after choosing a depth-five lift, divisible handle powers clear both handle rows
without changing its depth or compact image.  The compact derived condition then proves that
the corrected lift is invisible to every continuous `Z_2`-character.

The resulting `OneHandleC7RelativeLift` is a legal direct correction packet except for the
final vanishing equation.  Its modified relator remains in the one-handle depth-six central
layer and maps into compact `lambda_7`; therefore its class-seven residual lies in the
intersection of that central layer with the kernel of handle-forgetting.  The theorem
`oneHandleW6Correctable_iff_relativeResidual` proves that W6 is correctable exactly when some
such relative lift has trivial residual.

The finite correction layer sharpens this once more.  Four finite correction coordinates
are required to vanish exactly under handle-forgetting; the pivot coordinate also retains the
universal row condition.  Their direct stage shift must hit the inverse relative residual.
`oneHandleW6Correctable_iff_exists_relativeCorrectable` proves that this affine relative
range equation is equivalent to W6 correctability, not merely sufficient for it.
The map `oneHandleW6RelativeShiftHom` corestricts the stage shift to the relative central
layer, and `relativeCorrectable_iff_target_mem_range` presents the last condition as literal
membership of the inverse residual in its finite range.

This is a strict reduction, not the class-seven correction itself.  A full six-generator
class-seven p-quotient was experimentally too large to be a useful proof-search object, so
the next task is the much smaller four-coordinate relative range calculation isolated here.  No
all-stage successor supply or arbitrary-handle `MpcPivShiftH` is asserted.
