import Wikipedia.NoExoticSixSphere.ClopenStabilizedFraming
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.NativeBoundarySumHomology
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# Connectivity of actual framed component images and their sphere complements

The restriction of the original diffeomorphism transports simple
connectivity and actual second homology to its native image component.
Second Hurewicz then gives vanishing second homotopy at every image point.
A two-connected clopen component and a six-sphere complement imply zero
second homology of the whole boundary, without making it connected.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.StabilizedFramedDiffeomorph

open GLOrthonormalization

variable {n : ℕ} {M M' : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [TopologicalSpace M'] [ChartedSpace (Vector n) M']
  {e : EuclideanEmbedding n M} {e' : EuclideanEmbedding n M'}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel}
  (F : StabilizedFramedDiffeomorph e a e' a') (U : TopologicalSpace.Opens M)

theorem clopenImage_simplyConnected [SimplyConnectedSpace U] :
    SimplyConnectedSpace (F.clopenImage U) :=
  (openPreimageDiffeomorph F.diffeomorph.symm U).toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem clopenImage_secondHomology_subsingleton [Subsingleton (SingularHomology U 2)] :
    Subsingleton (SingularHomology (F.clopenImage U) 2) :=
  (homeomorphHomologyEquiv
    (openPreimageDiffeomorph F.diffeomorph.symm U).toHomeomorph 2).injective.subsingleton

variable [SimplyConnectedSpace U] (u : U) [Subsingleton (π_ 2 U u)]

include u in
theorem clopenImage_piTwo_subsingleton (v : F.clopenImage U) :
    Subsingleton (π_ 2 (F.clopenImage U) v) := by
  let := F.clopenImage_simplyConnected U
  let := TwoConnectedCoefficients.secondHomology_subsingleton u
  let := F.clopenImage_secondHomology_subsingleton U
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv v).injective.subsingleton

end NoExoticSixSphere.StabilizedFramedDiffeomorph

namespace NoExoticSixSphere.NativeBoundarySum

variable {Z : Type} [TopologicalSpace Z] (U : TopologicalSpace.Opens Z)
  (hU : IsClosed (U : Set Z)) [SimplyConnectedSpace U] (u : U)
  [Subsingleton (π_ 2 U u)]

include hU u in
theorem secondHomology_subsingleton_of_compl_sixSphere
    (hX : ↥((U : Set Z)ᶜ) ≃ₜ Sphere 6) : Subsingleton (SingularHomology Z 2) := by
  let := TwoConnectedCoefficients.secondHomology_subsingleton u
  let : Subsingleton (SingularHomology ↥((U : Set Z)ᶜ) 2) :=
    subsingleton_singularHomology_of_homeomorph_sphere (by decide) (by decide) (by decide) hX
  exact target_secondHomology_subsingleton (clopenComplementHomeomorph U hU)

end NoExoticSixSphere.NativeBoundarySum
