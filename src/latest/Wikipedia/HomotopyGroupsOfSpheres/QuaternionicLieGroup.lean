import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSmoothness

/-! # Lie-group operations in the original symplectic operator model -/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization Smoothness

theorem contMDiff_multiplication (n : ℕ) :
    ContMDiff (𝓘(ℝ, SkewSpace n).prod 𝓘(ℝ, SkewSpace n)) 𝓘(ℝ, SkewSpace n) ∞
      (fun z : symplecticSubgroup n × symplecticSubgroup n => z.1 * z.2) := by
  apply contMDiff_iff_operator.mpr
  have h₁ : ContMDiff (𝓘(ℝ, SkewSpace n).prod 𝓘(ℝ, SkewSpace n))
      𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun z : symplecticSubgroup n × symplecticSubgroup n => z.1.val.val.val) :=
    (contMDiff_operator (n := n)).comp contMDiff_fst
  have h₂ : ContMDiff (𝓘(ℝ, SkewSpace n).prod 𝓘(ℝ, SkewSpace n))
      𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun z : symplecticSubgroup n × symplecticSubgroup n => z.2.val.val.val) :=
    (contMDiff_operator (n := n)).comp contMDiff_snd
  exact h₁.clm_comp h₂

theorem contMDiff_inversion (n : ℕ) :
    ContMDiff 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n) ∞
      (fun a : symplecticSubgroup n => a⁻¹) := by
  apply contMDiff_iff_operator.mpr
  intro a
  have hi : ContMDiffAt
      𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))
      𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      ContinuousLinearMap.inverse a.val.val.val :=
    a.val.val.property.contDiffAt_map_inverse.contMDiffAt
  have hs := hi.comp a contMDiff_operator.contMDiffAt
  convert hs using 1
  funext b
  exact NoExoticSixSphere.OrthogonalPaths.inverse_operator b.val

instance lieGroup (n : ℕ) : LieGroup 𝓘(ℝ, SkewSpace n) ∞ (symplecticSubgroup n) where
  contMDiff_mul := contMDiff_multiplication n
  contMDiff_inv := contMDiff_inversion n

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
