import ErdosProblems.Erdos1141.ReciprocalIntervals
import ErdosProblems.Erdos1141.SiegelLowerBound

/-!
# Approximating the real L-value by a reciprocal prefix
-/

namespace Pollack17

open Filter
open scoped BigOperators
open BoundedGaps.Maynard

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ i ∈ Finset.range n, f (1 + i) := by
  have heq : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext i; simp
  rw [heq, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

theorem sum_range_succ_eq_zero_add_Icc (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) = f 0 + ∑ i ∈ Finset.Icc 1 n, f i := by
  rw [sum_Icc_one_eq_sum_range, Finset.sum_range_succ']
  simp only [add_comm]

theorem eventually_quadratic_prefix_bound {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        ∀ n : ℕ, (m : ℝ) ^ d ≤ n →
          |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) := by
  obtain ⟨σ, hσ, h⟩ := Burgess.eventually_quadratic_burgess hd
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h] with m hm
  intro χ hχ hχ1 n hn
  rw [sum_Icc_one_eq_sum_range]
  exact hm χ hχ hχ1 1 n hn

theorem reciprocal_prefix_re {m : ℕ} (χ : DirichletCharacter ℂ m) (y : ℕ) :
    (∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ)).re =
      ∑ i ∈ Finset.Icc 1 y, (χ (i : ℕ)).re / (i : ℝ) := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.div_natCast_re]

theorem abs_reciprocal_prefix_sub_LFunction_re_le {m : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ1 : χ ≠ 1)
    {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ i ∈ Finset.Icc 1 x, (χ (i : ℕ)).re / (i : ℝ)) -
        (DirichletCharacter.LFunction χ (1 : ℂ)).re| ≤
      b * (3 + Real.log (y : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
  let P : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re / (i : ℝ)
  have hzero : (χ ((0 : ℕ) : ZMod m)).re = 0 := by
    rw [Nat.cast_zero, χ.map_zero' (by omega), Complex.zero_re]
  have hfinite := abs_reciprocal_interval_le (fun i => (χ (i : ℕ)).re) hx hxy hb
    (fun n hn hny => by
      rw [sum_range_succ_eq_zero_add_Icc, hzero, zero_add]
      exact hprefix n hn hny)
  have hdiff : P y - P x = ∑ i ∈ Finset.Ioc x y, (χ (i : ℕ)).re / (i : ℝ) := by
    dsimp only [P]
    rw [show Finset.Icc 1 y = Finset.Ioc 0 y by ext i; simp; omega,
      show Finset.Icc 1 x = Finset.Ioc 0 x by ext i; simp; omega,
      ← Finset.sum_Ioc_consecutive (fun i => (χ (i : ℕ)).re / (i : ℝ)) (Nat.zero_le x) hxy]
    ring
  have htail := (Complex.abs_re_le_norm (DirichletCharacter.LFunction χ (1 : ℂ) -
      ∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ))).trans
    (norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le hm χ hχ1 y (hx.trans_le hxy))
  rw [Complex.sub_re, reciprocal_prefix_re] at htail
  change |P x - (DirichletCharacter.LFunction χ 1).re| ≤ _
  have htri := abs_sub_le (P x) (P y) (DirichletCharacter.LFunction χ 1).re
  rw [abs_sub_comm (P x) (P y), hdiff] at htri
  have htail' : |P y - (DirichletCharacter.LFunction χ 1).re| ≤
      4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
    rw [abs_sub_comm]
    exact htail
  exact htri.trans (add_le_add hfinite htail')

end Pollack17
