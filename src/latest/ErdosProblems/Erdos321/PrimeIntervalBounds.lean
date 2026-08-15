import ErdosProblems.Erdos321.PNTError

namespace Erdos321

open Chebyshev Finset Nat Real

/-- Primes in the half-open integer interval `(a,b]`. -/
def primeInterval (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter Nat.Prime

/-- Its logarithmic prime weight is exactly a Chebyshev-θ difference. -/
theorem sum_log_primeInterval (a b : ℕ) (hab : a ≤ b) :
    (∑ p ∈ primeInterval a b, Real.log p) = θ b - θ a := by
  have hsub : primesLE a ⊆ primesLE b := by
    intro p hp
    have hpData := mem_primesLE.mp hp
    exact mem_primesLE.mpr ⟨hpData.1.trans hab, hpData.2⟩
  have hdiff : primesLE b \ primesLE a = primeInterval a b := by
    ext p
    simp only [Finset.mem_sdiff, mem_primesLE, primeInterval,
      Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hp⟩, hnot⟩
      exact ⟨⟨by
        by_contra hpa
        exact hnot ⟨le_of_not_gt hpa, hp⟩, hpb⟩, hp⟩
    · rintro ⟨⟨hap, hpb⟩, hp⟩
      exact ⟨⟨hpb, hp⟩, fun hpa => (not_le_of_gt hap) hpa.1⟩
  rw [← hdiff, Finset.sum_sdiff_eq_sub hsub,
    ← theta_eq_sum_primesLE_log, ← theta_eq_sum_primesLE_log]

/-- Cardinality and logarithmic weight sandwich for a prime interval. -/
theorem card_primeInterval_log_sandwich
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (primeInterval a b).card * Real.log a ≤ θ b - θ a ∧
      θ b - θ a ≤ (primeInterval a b).card * Real.log b := by
  have hsum := sum_log_primeInterval a b hab
  constructor
  · rw [← hsum]
    calc
      (primeInterval a b).card * Real.log a =
          ∑ _p ∈ primeInterval a b, Real.log a := by simp
      _ ≤ ∑ p ∈ primeInterval a b, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpBounds := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1)
        exact Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; exact_mod_cast
            (lt_of_lt_of_le Nat.zero_lt_one ha))
          (by simp only [Set.mem_Ioi]; exact_mod_cast
            (Finset.mem_filter.mp hp).2.pos)
          (by exact_mod_cast hpBounds.1.le)
  · rw [← hsum]
    calc
      (∑ p ∈ primeInterval a b, Real.log p) ≤
          ∑ _p ∈ primeInterval a b, Real.log b := by
        apply Finset.sum_le_sum
        intro p hp
        have hpBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
        exact Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; exact_mod_cast
            (Finset.mem_filter.mp hp).2.pos)
          (by simp only [Set.mem_Ioi]; exact_mod_cast
            (lt_of_lt_of_le Nat.zero_lt_one (ha.trans hab)))
          (by exact_mod_cast hpBounds.2)
      _ = (primeInterval a b).card * Real.log b := by simp

/-- Uniform two-sided prime interval estimate derived from F-036.  The error
constant is absolute and the statement is valid simultaneously for every
integer interval above `2`. -/
theorem exists_primeInterval_theta_bounds :
    ∃ C ≥ 0, ∀ {a b : ℕ}, 2 ≤ a → a ≤ b →
      (primeInterval a b).card * Real.log a ≤
        (b - a) + C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2 ∧
      (b - a) - (C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2) ≤
        (primeInterval a b).card * Real.log b := by
  obtain ⟨C, hC, hθ⟩ := exists_theta_error_constant
  refine ⟨C, hC, ?_⟩
  intro a b ha hab
  have hb : (2 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hθa := hθ a haR
  have hθb := hθ b hb
  have hSand := card_primeInterval_log_sandwich (show 1 ≤ a by omega) hab
  have hErrA : 0 ≤ C * (a : ℝ) / Real.log a ^ 2 := by positivity
  have hErrB : 0 ≤ C * (b : ℝ) / Real.log b ^ 2 := by positivity
  have hUpperA : θ a ≥ (a : ℝ) - C * a / Real.log a ^ 2 := by
    have := (abs_le.mp hθa).1
    linarith
  have hUpperB : θ b ≤ (b : ℝ) + C * b / Real.log b ^ 2 := by
    have := (abs_le.mp hθb).2
    linarith
  have hLowerA : θ a ≤ (a : ℝ) + C * a / Real.log a ^ 2 := by
    have := (abs_le.mp hθa).2
    linarith
  have hLowerB : θ b ≥ (b : ℝ) - C * b / Real.log b ^ 2 := by
    have := (abs_le.mp hθb).1
    linarith
  constructor
  · calc
      (primeInterval a b).card * Real.log a ≤ θ b - θ a := hSand.1
      _ ≤ (b - a) + C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2 := by
        linarith
  · calc
      (b - a) - (C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2) ≤
          θ b - θ a := by
        linarith
      _ ≤ (primeInterval a b).card * Real.log b := hSand.2

end Erdos321
