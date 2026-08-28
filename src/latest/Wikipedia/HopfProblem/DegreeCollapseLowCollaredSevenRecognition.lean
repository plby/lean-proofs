import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPromotion
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarNegativeConnectivity

/-!

# Native smooth sphere recognition without an initial H2-vanishing input

For a supplied framed collared state with simply connected halves and
spherical boundary, actual positive surgeries clear H2 on both sides.
The collar cover constructs the ambient hypotheses and the existing
middle-dimensional surgery and disk-recognition theorem then applies.
Every comparison retains the original zero-boundary smooth atlas.
The supplied filling and its simple connectivity are still required.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B]

theorem nonempty_zero_sphere_diffeomorph (S : LowCollaredSevenState B)
    (eBoundary : B ≃ₜ Sphere 6)
    [SimplyConnectedSpace S.PositiveHalf] [SimplyConnectedSpace S.NegativeHalf] :
    letI := S.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  have hB (j : ℕ) (hj : j ≠ 0) (h6 : j ≠ 6) : Subsingleton (SingularHomology B j) := by
    let : Subsingleton (SingularHomology (Sphere 6) j) :=
      SphereHomology.unitSphere_homology_subsingleton 5 j hj h6
    exact (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv j).injective.subsingleton
  let := hB 1 (by decide) (by decide)
  let := hB 2 (by decide) (by decide)
  obtain ⟨U, V, hSU, hUV, hVP, hVN, hVP2, hVN2⟩ := S.exists_h2_zero_both_halves
  let := hVP
  let := hVN
  let := hVP2
  let := hVN2
  let := S.zeroAtlas
  let := V.zeroAtlas
  let := V.toCollaredSevenState.zeroAtlas
  obtain ⟨D⟩ := zero_diffeomorphic_after_reversed_path hSU hUV
  obtain ⟨F⟩ := V.toCollaredSevenState.nonempty_zero_sphere_diffeomorph eBoundary
  exact ⟨D.trans (V.promotionZeroDiffeomorph.trans F)⟩

theorem nonempty_zero_sphere_diffeomorph_of_ambient_simpleConnectivity
    (S : LowCollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [SimplyConnectedSpace S.Space] [SimplyConnectedSpace S.PositiveHalf] :
    letI := S.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space
  let : SimplyConnectedSpace S.NegativeHalf := S.collar.negativeHalf_simplyConnected
  exact S.nonempty_zero_sphere_diffeomorph eBoundary

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
