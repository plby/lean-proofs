import ErdosProblems.Erdos587.HooleyInnerQuotient

/-! # Finite inner rank reduction without losing the lattice rounding cell -/

namespace Erdos587.GeneralizedAP

lemma delta_half_quotient_small_cube (X : ConvexProgression) {d n : ℕ}
    (p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ))
    (q : (Fin X.rank → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hn : n + 1 = X.rank)
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body) :
    ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension (q.comp p) e ∈ bodyDilate (1 / 4 ^ (n + 2))
        (bodyDilate (1 / 2 : ℝ) (intLinearMapRealExtension q '' X.body)) := by
  intro e he
  rw [delta_intLinearMapRealExtension_comp, LinearMap.comp_apply,
    delta_bodyDilate_mul, delta_bodyDilate_image]
  refine ⟨intLinearMapRealExtension p e, ?_, rfl⟩
  apply delta_bodyDilate_mono X.body_zero X.body_convex (by positivity) _ (hcube e he)
  rw [← hn]
  exact delta_small_cube_scale_half_step n

lemma delta_half_quotient_rounding (X : ConvexProgression) {d n : ℕ}
    (p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ)) (hp : Function.Surjective p)
    (q : (Fin X.rank → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hq : Function.Surjective q)
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body) :
    ∀ x : Fin n → ℝ, ∃ v : Fin n → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ)
        (bodyDilate (1 / 2 : ℝ) (intLinearMapRealExtension q '' X.body)) := by
  apply delta_rounding_of_projected_cube (q.comp p) (hq.comp hp)
  intro e he
  rw [delta_intLinearMapRealExtension_comp, LinearMap.comp_apply,
    delta_bodyDilate_mul, delta_bodyDilate_image]
  refine ⟨intLinearMapRealExtension p e, ?_, rfl⟩
  apply delta_bodyDilate_mono X.body_zero X.body_convex (by positivity) _ (hcube e he)
  exact (delta_small_cube_scale_le_quarter X.rank).trans (by norm_num)

theorem delta_exists_inner_proper_quotient (X : ConvexProgression) {d : ℕ}
    (p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ)) (hp : Function.Surjective p)
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body) :
    Nonempty (DeltaInnerQuotient X) := by
  classical
  suffices hmain : ∀ r : ℕ, ∀ X : ConvexProgression, X.rank = r → ∀ d : ℕ,
      ∀ p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ), Function.Surjective p →
      (∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
        intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body) →
      Nonempty (DeltaInnerQuotient X) by
    exact hmain X.rank X rfl d p hp hcube
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro X hX d p hp hcube
    by_cases hkernel : ∀ v : Fin X.rank → ℤ, X.eval v = 0 →
        intCastVec v ∈ bodyDilate (1 / 2 : ℝ) X.body → v = 0
    · exact delta_innerQuotient_of_no_short_kernel X p hp hcube hkernel
    · push Not at hkernel
      obtain ⟨e, heval, heB, he⟩ := hkernel
      obtain ⟨u, _hu, hueval, huprim, huB⟩ :=
        delta_exists_primitive_short_kernel X e he heval heB
      obtain ⟨n, a, b, hua, hn⟩ := exists_primitiveQuotientData u huprim
      let q := primitiveQuotientProjection u a hua b
      have hq : Function.Surjective q := primitiveQuotientProjection_surjective u a hua b
      have hround := delta_half_quotient_rounding X p hp q hq hcube
      have hround' : ∀ x : Fin n → ℝ, ∃ v : Fin n → ℤ,
          x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ)
            (bodyDilate (1 - (1 / 2 : ℝ)) (intLinearMapRealExtension q '' X.body)) := by
        simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] using hround
      let Y := deltaShrunkenQuotient X u a hua b (1 / 2) (by norm_num) hround'
      have hcubeY : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
          intLinearMapRealExtension (q.comp p) e ∈ bodyDilate (1 / 4 ^ (Y.rank + 2))
            Y.body := by
        change ∀ e : Fin d → ℝ, _ → _ ∈ bodyDilate (1 / 4 ^ (n + 2))
          (bodyDilate (1 - (1 / 2 : ℝ)) (intLinearMapRealExtension q '' X.body))
        simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] using
          delta_half_quotient_small_cube X p q hn hcube
      have hnlt : n < r := by omega
      obtain ⟨D⟩ := ih n hnlt Y rfl d (q.comp p) (hq.comp hp) hcubeY
      exact delta_innerQuotient_half_comp X u a hua b hn hround' huB hueval D

end Erdos587.GeneralizedAP
