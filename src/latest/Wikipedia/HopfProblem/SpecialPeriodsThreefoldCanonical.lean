import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticFullPatch
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspBiholomorph
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackDiffeomorphBundle

/-!
# The native canonical bundle of the actual compact threefold

`SpecialPeriods.Threefold.Canonical.bundle` is the holomorphic inverse-Jacobian
bundle of the actual glued tangent atlas.  Its fibres are continuously
complex-linearly identified with all alternating three-covectors on the
actual tangent spaces.  Its nowhere-zero holomorphic local frames and all
their transition factors come from the actual chart derivatives.

The full open restrictions are compared with the native local canonical
bundles by biholomorphisms of the original bundle total spaces:

* `Canonical.Regular.bundleBiholomorph` uses the earlier actual regular
  period-family canonical bundle.
* `Canonical.Cusp.nativePatchTotalBiholomorph` uses the original native
  cusp canonical bundle, including its signed volume normalization and
  its native three-coordinate model.
* `Canonical.Elliptic.bundleBiholomorph` uses the ambient canonical bundle
  of each actual small elliptic filling.
* `Canonical.Elliptic.fullBundlePatchBiholomorph` compares the original
  full-filling ambient canonical bundle on the exact parametrization
  source with the entire corresponding global restriction.

All comparisons preserve the actual base maps and use inverse differential
pullback on fibres, with explicit intrinsic pullback and gluing laws.  Both
directions are holomorphic for the original atlases.  The elliptic ambient
threefold canonical bundle is distinct from the canonical bundle of its
central surface.  No global divisor formula or triviality of the global
canonical bundle is asserted here.
-/
