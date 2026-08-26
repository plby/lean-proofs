import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Concentrating a weighted finite moment into one summand -/

namespace Erdos421

theorem norm_sum_natPower_le {X : Type*} (S : Finset X) (f : X → ℂ) {m : ℕ} (hm : 0 < m) :
    ‖∑ x ∈ S, f x‖ ^ m ≤ (S.card : ℝ) ^ (m - 1) * ∑ x ∈ S, ‖f x‖ ^ m := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S
    (f := fun x ↦ ‖f x‖) (p := (m : ℝ)) (by exact_mod_cast hm) (fun x _ ↦ norm_nonneg _)
  have he : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  have hpow : (∑ x ∈ S, ‖f x‖) ^ m ≤
      (S.card : ℝ) ^ (m - 1) * ∑ x ∈ S, ‖f x‖ ^ m := by
    simpa only [he, Real.rpow_natCast] using h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) m).trans hpow

theorem weighted_norm_sum_natPower_le {X C : Type*} (S : Finset X) (T : Finset C)
    (w : X → ℝ) (g : C → X → ℂ) (hw : ∀ x ∈ S, 0 ≤ w x) {m : ℕ} (hm : 0 < m) :
    (∑ x ∈ S, w x * ‖∑ c ∈ T, g c x‖ ^ m) ≤
      (T.card : ℝ) ^ (m - 1) * ∑ c ∈ T, ∑ x ∈ S, w x * ‖g c x‖ ^ m := by
  calc
    _ ≤ ∑ x ∈ S, w x * ((T.card : ℝ) ^ (m - 1) * ∑ c ∈ T, ‖g c x‖ ^ m) :=
      Finset.sum_le_sum (fun x hx ↦ mul_le_mul_of_nonneg_left
        (norm_sum_natPower_le T (fun c ↦ g c x) hm) (hw x hx))
    _ = (T.card : ℝ) ^ (m - 1) * ∑ x ∈ S, ∑ c ∈ T, w x * ‖g c x‖ ^ m := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [Finset.sum_comm]

theorem exists_weighted_norm_sum_concentration {X C : Type*} (S : Finset X) (T : Finset C)
    (hT : T.Nonempty) (w : X → ℝ) (g : C → X → ℂ) (hw : ∀ x ∈ S, 0 ≤ w x)
    {m : ℕ} (hm : 0 < m) :
    ∃ c ∈ T, (∑ x ∈ S, w x * ‖∑ b ∈ T, g b x‖ ^ m) ≤
      (T.card : ℝ) ^ m * ∑ x ∈ S, w x * ‖g c x‖ ^ m := by
  obtain ⟨c, hc, hmax⟩ := T.exists_max_image (fun c ↦ ∑ x ∈ S, w x * ‖g c x‖ ^ m) hT
  refine ⟨c, hc, ?_⟩
  calc
    _ ≤ (T.card : ℝ) ^ (m - 1) * ∑ b ∈ T, ∑ x ∈ S, w x * ‖g b x‖ ^ m :=
      weighted_norm_sum_natPower_le S T w g hw hm
    _ ≤ (T.card : ℝ) ^ (m - 1) * ∑ _b ∈ T, ∑ x ∈ S, w x * ‖g c x‖ ^ m :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmax) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (T.card : ℝ) ^ m * ∑ x ∈ S, w x * ‖g c x‖ ^ m := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]

end Erdos421
