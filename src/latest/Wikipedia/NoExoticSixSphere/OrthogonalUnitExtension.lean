import Wikipedia.NoExoticSixSphere.SphereNormalization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Orthogonally adjoining a unit column using an actual L2 source model -/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalUnitExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def operator (B : E →L[ℝ] F) (ν : F) : WithLp 2 (E × ℝ) →L[ℝ] F :=
  B.comp ((ContinuousLinearMap.fst ℝ E ℝ).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap) +
      ((ContinuousLinearMap.snd ℝ E ℝ).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap).smulRight ν

theorem operator_apply (B : E →L[ℝ] F) (ν : F) (v : WithLp 2 (E × ℝ)) :
    operator B ν v = B v.fst + v.snd • ν := rfl

theorem inner_operator (B : E →L[ℝ] F) (hB : ∀ v, ‖B v‖ = ‖v‖)
    (ν : F) (hν : ‖ν‖ = 1) (ho : ∀ v, inner ℝ ν (B v) = 0)
    (u v : WithLp 2 (E × ℝ)) :
    inner ℝ (operator B ν u) (operator B ν v) = inner ℝ u v := by
  let L : E →ₗᵢ[ℝ] F := { toLinearMap := B.toLinearMap, norm_map' := hB }
  have hinner : inner ℝ (B u.fst) (B v.fst) = inner ℝ u.fst v.fst :=
    L.inner_map_map _ _
  have ho' (w : E) : inner ℝ (B w) ν = 0 := (real_inner_comm _ _).trans (ho w)
  rw [operator_apply, operator_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ho, ho', mul_zero, add_zero, zero_add, hinner, real_inner_self_eq_norm_sq, hν,
    one_pow, mul_one, WithLp.prod_inner_apply, Real.inner_apply]
  change inner ℝ u.fst v.fst + v.snd * u.snd = inner ℝ u.fst v.fst + u.snd * v.snd
  ring

theorem norm_operator (B : E →L[ℝ] F) (hB : ∀ v, ‖B v‖ = ‖v‖)
    (ν : F) (hν : ‖ν‖ = 1) (ho : ∀ v, inner ℝ ν (B v) = 0)
    (v : WithLp 2 (E × ℝ)) : ‖operator B ν v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_operator B hB ν hν ho v v

variable {K H X : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [TopologicalSpace H] {I : ModelWithCorners ℝ K H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiff_operator {B : X → E →L[ℝ] F} {ν : X → F}
    (hB : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ B) (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (E × ℝ) →L[ℝ] F) ∞ (fun x ↦ operator (B x) (ν x)) := by
  unfold operator
  apply (hB.clm_comp contMDiff_const).add
  exact (ContinuousLinearMap.smulRightL ℝ (WithLp 2 (E × ℝ)) F _).contDiff.contMDiff.comp hν

end NoExoticSixSphere.OrthogonalUnitExtension
