import ErdosProblems.Erdos1141.BurgessMoments
import ErdosProblems.Erdos1141.RepeatedTuples

/-!
# The complete prime-field Burgess moment estimate for every order
-/

namespace Pollack17.Burgess

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem qchar_le_one (z : ZMod p) : qchar z ≤ 1 := by
  rcases quadraticChar_isQuadratic (ZMod p) z with h | h | h <;> norm_num [qchar, h]

theorem shiftSum_even_moment_le (V : Finset (ZMod p)) (r : ℕ) :
    (∑ x : ZMod p, shiftSum V x ^ (2 * r)) ≤
      (V.card : ℝ) ^ r * (r : ℝ) ^ (2 * r) * p +
        (V.card : ℝ) ^ (2 * r) * (Stepanov.simpleRootConstant (2 * r) : ℝ) * Real.sqrt p := by
  classical
  let T := Fin (2 * r) → V
  let corr : T → ℝ := fun v => ∑ x : ZMod p,
    qchar (∏ i : Fin (2 * r), (x + (v i : ZMod p)))
  let C : ℝ := (Stepanov.simpleRootConstant (2 * r) : ℝ) * Real.sqrt p
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hpoint (v : T) : corr v ≤ (if RepeatedTuple v then (p : ℝ) else 0) + C := by
    by_cases hv : RepeatedTuple v
    · rw [if_pos hv]
      have htrivial : corr v ≤ p := by
        exact (Finset.sum_le_sum (fun x _ => qchar_le_one _)).trans_eq (by simp)
      exact htrivial.trans (le_add_of_nonneg_right hC)
    · rw [if_neg hv, zero_add]
      have hsingle : ∃ i : Fin (2 * r), ∀ j : Fin (2 * r), j ≠ i → v j ≠ v i := by
        simpa only [RepeatedTuple, not_forall, not_exists, not_and] using hv
      obtain ⟨i, hi⟩ := hsingle
      have hbound := correlation_le_of_singleton (fun j => (v j : ZMod p))
        ⟨i, fun j hji hval => hi j hji (Subtype.ext hval)⟩
      exact (le_abs_self (corr v)).trans hbound
  have hbad : ((repeatedTuples V (2 * r)).card : ℝ) ≤
      (V.card : ℝ) ^ r * (r : ℝ) ^ (2 * r) := by
    have hnat : (repeatedTuples V (2 * r)).card ≤ V.card ^ r * r ^ (2 * r) := by
      simpa using repeatedTuples_card_le V r
    exact_mod_cast hnat
  have hbadSum : (∑ v : T, if RepeatedTuple v then (p : ℝ) else 0) =
      ((repeatedTuples V (2 * r)).card : ℝ) * p := by
    rw [← Finset.sum_filter]
    simp [repeatedTuples, T]
  calc
    (∑ x : ZMod p, shiftSum V x ^ (2 * r)) = ∑ v : T, corr v :=
      shiftSum_moment_expansion V (2 * r)
    _ ≤ ∑ v : T, ((if RepeatedTuple v then (p : ℝ) else 0) + C) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = ((repeatedTuples V (2 * r)).card : ℝ) * p + (V.card : ℝ) ^ (2 * r) * C := by
      rw [Finset.sum_add_distrib, hbadSum]
      simp [T]
    _ ≤ ((V.card : ℝ) ^ r * (r : ℝ) ^ (2 * r)) * p + (V.card : ℝ) ^ (2 * r) * C :=
      add_le_add (mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg p)) le_rfl
    _ = _ := by dsimp [C]; ring

end Pollack17.Burgess
