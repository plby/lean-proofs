import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyLocalizedBoundary
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyFlowLocalized

/-!
# The original elliptic gauge correction as a supported smooth cap isotopy

The boundary action is the literal translation by the full difference
between the native real logarithmic gauge and its linear counterpart.
It descends on the original affine mapping torus, has the exact
negative-time inverse, fixes the base circle, and commutes with the
unchanged delta-circle action.

`GaugeIsotopy.nativeLocalizedCollarDiffeomorph` extends this action to the
original small elliptic cap, in its original inherited real smooth
atlas.  Joint smoothness is proved through the genuine complex-vector
coverings.  Explicit inner and outer cutoffs place every moved point in
an annular collar strictly inside the original small piece.  The inverse,
base preservation, and commutation with the original complex vertical
flow are retained point for point.

`GaugeIsotopy.nativeLocalizedCollar_regular_one` is the exact equality
between the original attaching map after this cap diffeomorphism and the
original linear-gauge boundary map.  It is not an equality obtained from
homology or a chosen splitting.  No assertion about a global coinvariant
coordinate, a cusp extension, a Jacobian product, or smooth sphere
recognition is made here.
-/
