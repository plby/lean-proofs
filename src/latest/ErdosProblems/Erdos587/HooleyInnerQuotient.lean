import ErdosProblems.Erdos587.HooleyShortKernel
import ErdosProblems.Erdos587.HooleyZonotopeMap

/-! # An inner proper quotient certificate, with quantitative shrinkage -/

namespace Erdos587.GeneralizedAP

structure DeltaInnerQuotient (X : ConvexProgression) where
  progression : ConvexProgression
  projection : (Fin X.rank → ℤ) →ₗ[ℤ] (Fin progression.rank → ℤ)
  surjective : Function.Surjective projection
  rank_le : progression.rank ≤ X.rank
  factor : ℝ
  factor_pos : 0 < factor
  factor_lower : (1 : ℝ) / 4 ^ (X.rank + 1) ≤ factor
  factor_le_one : factor ≤ 1
  base_eq : progression.base = X.base
  eval_projection : ∀ v, progression.eval (projection v) = X.eval v
  body_eq : progression.body = bodyDilate factor (intLinearMapRealExtension projection '' X.body)
  carrier_subset : progression.carrier ⊆ X.carrier
  proper : progression.SProper 1
  rounding : ∀ x : Fin progression.rank → ℝ, ∃ v : Fin progression.rank → ℤ,
    x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) progression.body

theorem delta_innerQuotient_of_no_short_kernel (X : ConvexProgression) {d : ℕ}
    (p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ)) (hp : Function.Surjective p)
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body)
    (hkernel : ∀ v : Fin X.rank → ℤ, X.eval v = 0 →
      intCastVec v ∈ bodyDilate (1 / 2 : ℝ) X.body → v = 0) :
    Nonempty (DeltaInnerQuotient X) := by
  have hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) (bodyDilate (1 / 4 : ℝ) X.body) := by
    apply delta_rounding_of_projected_cube p hp
    intro e he
    rw [delta_bodyDilate_mul]
    exact delta_bodyDilate_mono X.body_zero X.body_convex (by positivity)
      (delta_small_cube_scale_le_quarter X.rank) (hcube e he)
  let Y := deltaDilatedConvexProgression X (1 / 4) (by norm_num) hround
  refine ⟨{
    progression := Y
    projection := LinearMap.id
    surjective := Function.surjective_id
    rank_le := le_refl _
    factor := 1 / 4
    factor_pos := by norm_num
    factor_lower := ?_
    factor_le_one := by norm_num
    base_eq := rfl
    eval_projection := fun _ => rfl
    body_eq := ?_
    carrier_subset := deltaDilatedConvexProgression_carrier_subset X (1 / 4)
      (by norm_num) (by norm_num) hround
    proper := ?_
    rounding := hround
  }⟩
  · have hp : (1 : ℝ) ≤ 4 ^ X.rank := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ X.rank * 4)).mpr
    nlinarith
  · change bodyDilate (1 / 4 : ℝ) X.body = bodyDilate (1 / 4 : ℝ)
      (intLinearMapRealExtension (LinearMap.id : (Fin X.rank → ℤ) →ₗ[ℤ] _) '' X.body)
    rw [delta_intLinearMapRealExtension_id]
    change bodyDilate (1 / 4 : ℝ) X.body = bodyDilate (1 / 4 : ℝ) (id '' X.body)
    rw [Set.image_id]
  · dsimp only [Y, deltaDilatedConvexProgression, deltaConvexProgression,
      ConvexProgression.SProper]
    norm_num only [Nat.cast_one]
    rw [delta_bodyDilate_one]
    simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using
      delta_injOn_half_body_of_no_short_kernel X (1 / 2) hkernel

theorem delta_innerQuotient_half_comp (X : ConvexProgression) {n : ℕ}
    (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a))) (hn : n + 1 = X.rank)
    (hround) (hu : intCastVec u ∈ bodyDilate (1 / 2 : ℝ) X.body) (heval : X.eval u = 0)
    (D : DeltaInnerQuotient (deltaShrunkenQuotient X u a hua b (1 / 2)
      (by norm_num) hround)) : Nonempty (DeltaInnerQuotient X) := by
  let q := primitiveQuotientProjection u a hua b
  let Y := deltaShrunkenQuotient X u a hua b (1 / 2) (by norm_num) hround
  let w : (Fin n → ℤ) →ₗ[ℤ] (Fin D.progression.rank → ℤ) := D.projection
  have hbodyY : Y.body = bodyDilate (1 / 2 : ℝ) (intLinearMapRealExtension q '' X.body) := by
    change bodyDilate (1 - (1 / 2 : ℝ)) _ = _
    norm_num
    rfl
  refine ⟨{
    progression := D.progression
    projection := D.projection.comp q
    surjective := D.surjective.comp (primitiveQuotientProjection_surjective u a hua b)
    rank_le := D.rank_le.trans (by change n ≤ X.rank; omega)
    factor := D.factor * (1 / 2)
    factor_pos := mul_pos D.factor_pos (by norm_num)
    factor_lower := ?_
    factor_le_one := by nlinarith [D.factor_le_one]
    base_eq := D.base_eq
    eval_projection := ?_
    body_eq := ?_
    carrier_subset := D.carrier_subset.trans
      (deltaShrunkenQuotient_carrier_subset X u a hua b hn (1 / 2)
        (by norm_num) (by norm_num) hround hu heval)
    proper := D.proper
    rounding := D.rounding
  }⟩
  · have hlow : (1 : ℝ) / 4 ^ (n + 1) ≤ D.factor := D.factor_lower
    rw [← hn, show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
    have hp : (0 : ℝ) < 4 ^ (n + 1) := by positivity
    have hquarter : (1 : ℝ) / (4 ^ (n + 1) * 4) ≤ (1 / 4 ^ (n + 1)) * (1 / 2) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ (n + 1) * 4)).mpr
      field_simp
      norm_num
    exact hquarter.trans (mul_le_mul_of_nonneg_right hlow (by norm_num))
  · intro v
    exact (D.eval_projection (q v)).trans
      (primitiveQuotientEval_projection X.eval u a hua heval b v)
  · rw [D.body_eq]
    change bodyDilate D.factor (intLinearMapRealExtension D.projection '' Y.body) = _
    rw [hbodyY]
    change bodyDilate D.factor (intLinearMapRealExtension w ''
      bodyDilate (1 / 2 : ℝ) (intLinearMapRealExtension q '' X.body)) =
        bodyDilate (D.factor * (1 / 2)) (intLinearMapRealExtension (w.comp q) '' X.body)
    rw [← delta_bodyDilate_image, delta_bodyDilate_mul, Set.image_image,
      delta_intLinearMapRealExtension_comp]
    rfl

end Erdos587.GeneralizedAP
