import ErdosProblems.Erdos448.HalberstamComplete448

/-!
# A finite global Shiu mean-value bound

This is the `q = 1` mean-value estimate used in source Lemma 2.4 of the
Granville--Soundararajan argument.  The first prime coefficient is retained
exactly, while all higher prime powers are put into the summable quadratic
Euler tail.  This is the form needed after shifting the high-prime factor by
`eta = 1 / log y`.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRShiu

noncomputable section

/-- The Euler exponent in the global (`q = 1`) Shiu estimate. -/
def globalEulerExponent (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow,
    (h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))

theorem globalEulerExponent_nonneg
    {h : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ h n) (N : ℕ) :
    0 ≤ globalEulerExponent h N := by
  unfold globalEulerExponent
  refine Finset.sum_nonneg fun p hp ↦ add_nonneg
    (div_nonneg (hnonneg p) (Nat.cast_nonneg p)) ?_
  have hpPrime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  positivity

/-- Keeping the prime term separate turns the remaining local Euler factor
into a genuinely quadratic tail. -/
theorem localFactor_le
    {h : ℕ → ℝ}
    (h1 : h 1 = 1)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      1 + h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  let term : ℕ → ℝ := fun j ↦ h (p ^ j) / ((p ^ j : ℕ) : ℝ)
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := inv_nonneg.mpr hpR.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (lt_of_lt_of_le one_lt_two hpTwo)
  have htailBound (j : ℕ) : term (j + 2) ≤ r ^ (j + 2) := by
    have hden : (0 : ℝ) < ((p ^ (j + 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos hp.pos
    have hnum : h (p ^ (j + 2)) ≤ 1 := by
      simpa only [show j + 2 = (j + 1) + 1 by omega] using hpow p hp (j + 1)
    calc
      term (j + 2) = h (p ^ (j + 2)) /
          ((p ^ (j + 2) : ℕ) : ℝ) := rfl
      _ ≤ 1 / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = r ^ (j + 2) := by
        rw [Nat.cast_pow]
        simp only [r, one_div, inv_pow]
  have hmajorSummable : Summable (fun j : ℕ ↦ r ^ (j + 2)) := by
    have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hs
  have htailNonneg (j : ℕ) : 0 ≤ term (j + 2) :=
    div_nonneg (hnonneg _) (Nat.cast_nonneg _)
  have htailSummable : Summable (fun j : ℕ ↦ term (j + 2)) :=
    Summable.of_nonneg_of_le htailNonneg htailBound hmajorSummable
  have htermSummable : Summable term := (summable_nat_add_iff 2).1 htailSummable
  have hshiftSummable : Summable (fun j : ℕ ↦ term (j + 1)) :=
    (summable_nat_add_iff 1).2 htermSummable
  have htailTsum :
      (∑' j : ℕ, term (j + 2)) ≤ ∑' j : ℕ, r ^ (j + 2) :=
    htailSummable.tsum_le_tsum htailBound hmajorSummable
  have hmajorTsum :
      (∑' j : ℕ, r ^ (j + 2)) = r ^ 2 / (1 - r) := by
    have hs := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)).tsum_eq
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc,
      div_eq_mul_inv] using hs
  have hzero : term 0 = 1 := by simp [term, h1]
  have honeTerm : term 1 = h p / (p : ℝ) := by simp [term]
  rw [show (∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      ∑' j : ℕ, term j by rfl]
  rw [htermSummable.tsum_eq_zero_add, hzero,
    hshiftSummable.tsum_eq_zero_add, honeTerm]
  have htailFinal :
      (∑' j : ℕ, term (j + 2)) ≤
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      (∑' j : ℕ, term (j + 2)) ≤
          ∑' j : ℕ, r ^ (j + 2) := htailTsum
      _ = r ^ 2 / (1 - r) := hmajorTsum
      _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        dsimp [r]
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hpR
        have hp1 : (p : ℝ) - 1 ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le one_lt_two hpTwo))
        field_simp [hp0, hp1]
  linarith

/-- The finite HR Euler product is bounded by the exponential of the exact
prime mass plus a quadratic tail. -/
theorem eulerProduct_le_exp
    {h : ℕ → ℝ}
    (h1 : h 1 = 1)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp (globalEulerExponent h N) := by
  let E : ℕ → ℝ := fun p ↦
    h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ (N + 1).primesBelow, (1 + E p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun j ↦
          div_nonneg (hnonneg _) (Nat.cast_nonneg _)
      · intro p hp
        have hlocal := localFactor_le h1 hnonneg hpow
          (Nat.prime_of_mem_primesBelow hp)
        simpa [E, add_assoc] using hlocal
    _ ≤ Real.exp (∑ p ∈ (N + 1).primesBelow, E p) := by
      apply Real.prod_one_add_le_exp_sum
      intro p
      dsimp [E]
      by_cases hp0 : p = 0
      · subst p
        simp
      by_cases hp1 : p = 1
      · subst p
        simpa using hnonneg 1
      have hp2 : 2 ≤ p := by omega
      have hp1R : (1 : ℝ) < p := by exact_mod_cast
        (lt_of_lt_of_le Nat.one_lt_two hp2)
      exact add_nonneg (div_nonneg (hnonneg p) (Nat.cast_nonneg p)) (by positivity)
    _ = Real.exp (globalEulerExponent h N) := by rfl

/-- Fully explicit, axiom-free `q = 1` Shiu estimate.  Unlike the crude
prime-power HR bound, its exponent retains the shifted first-prime mass and
therefore supplies the `log y / log X` saving in source Lemma 2.4. -/
theorem partialSum_le_exp
    {h : ℕ → ℝ}
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum h N ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp (globalEulerExponent h N) := by
  have hbase := HalberstamComplete448.halberstam_richert_explicit
    h h0 h1 hmul hnonneg 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hpow) N hN
  have heuler := eulerProduct_le_exp h1 hnonneg hpow N
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hfactor : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num)) zero_le_one)
        (Nat.cast_nonneg _)) hlog.le
  exact hbase.trans (mul_le_mul_of_nonneg_left heuler hfactor)

end

end Erdos67.MRShiu

#print axioms Erdos67.MRShiu.partialSum_le_exp
