/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.SingularProductExpansion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Averaging the singular factor along differences of powers of two

For an odd modulus, divisibility of `2^(ℓ+h) - 2^ℓ` depends only on the
gap `h` and occurs once per multiplicative-order period.  This turns a
finite singular-factor average into a finite partial sum of Romanoff's
convergent series.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos851

/-- The modulus tail of Romanoff's series.  This is independent of the
finite upper endpoint in the local Euler product. -/
noncomputable def romanoffTail (z : ℕ) : ℝ :=
  ∑' q : ℕ, if z < q then romanoffTerm q else 0

theorem romanoffTail_nonneg (z : ℕ) : 0 ≤ romanoffTail z := by
  unfold romanoffTail
  exact tsum_nonneg fun q ↦ by
    split_ifs
    · exact romanoffTerm_nonneg q
    · exact le_rfl

/-- Every modulus is eventually absent from the ordinary magnitude tail;
dominated convergence applies because Romanoff's series is summable. -/
theorem romanoffTail_tendsto_zero :
    Tendsto romanoffTail atTop (nhds 0) := by
  have hpoint (q : ℕ) :
      Tendsto (fun z : ℕ ↦ if z < q then romanoffTerm q else 0)
        atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop q] with z hz
    rw [if_neg (not_lt_of_ge hz)]
  have hbound : ∀ᶠ z : ℕ in atTop, ∀ q,
      ‖(if z < q then romanoffTerm q else 0)‖ ≤ romanoffTerm q := by
    filter_upwards [] with z q
    split_ifs
    · simp [abs_of_nonneg (romanoffTerm_nonneg q)]
    · simpa using romanoffTerm_nonneg q
  have ht := tendsto_tsum_of_dominated_convergence
    summable_romanoffTerm hpoint hbound
  change Tendsto
    (fun z : ℕ ↦ ∑' q : ℕ, if z < q then romanoffTerm q else 0)
    atTop (nhds 0)
  simpa only [tsum_zero] using ht

@[simp] theorem romanoffTerm_one : romanoffTerm 1 = 1 := by
  have hmod : IsRomanoffModulus 1 := ⟨squarefree_one, odd_one⟩
  rw [romanoffTerm_eq_inv_mul hmod, twoOrder, Subsingleton.orderOf_eq]
  norm_num

/-- A finite set consisting only of `1` and moduli above `z` has total
Romanoff mass at most `1 + romanoffTail z`. -/
theorem sum_romanoffTerm_le_one_add_tail
    (Q : Finset ℕ) (z : ℕ) (hQ : ∀ q ∈ Q, q = 1 ∨ z < q) :
    ∑ q ∈ Q, romanoffTerm q ≤ 1 + romanoffTail z := by
  classical
  let T := Q.erase 1
  have hsplit :
      ∑ q ∈ Q, romanoffTerm q =
        (if 1 ∈ Q then romanoffTerm 1 else 0) +
          ∑ q ∈ T, romanoffTerm q := by
    by_cases h1 : 1 ∈ Q
    · rw [if_pos h1, ← Finset.sum_erase_add _ _ h1]
      simp [T, add_comm]
    · rw [if_neg h1]
      simp [T, h1]
  have hTlarge : ∀ q ∈ T, z < q := by
    intro q hq
    have hqQ := Finset.mem_of_mem_erase hq
    have hq1 : q ≠ 1 := (Finset.mem_erase.mp hq).1
    exact (hQ q hqQ).resolve_left hq1
  have htailSummable : Summable (fun q : ℕ ↦
      if z < q then romanoffTerm q else 0) := by
    exact Summable.of_nonneg_of_le
      (fun q ↦ by
        split_ifs
        · exact romanoffTerm_nonneg q
        · exact le_rfl)
      (fun q ↦ by split_ifs <;> simp [romanoffTerm_nonneg])
      summable_romanoffTerm
  calc
    ∑ q ∈ Q, romanoffTerm q =
        (if 1 ∈ Q then romanoffTerm 1 else 0) +
          ∑ q ∈ T, romanoffTerm q := hsplit
    _ ≤ 1 + ∑ q ∈ T, romanoffTerm q := by
      gcongr
      split_ifs <;> simp
    _ = 1 + ∑ q ∈ T, (if z < q then romanoffTerm q else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (hTlarge q hq)]
    _ ≤ 1 + ∑' q : ℕ, (if z < q then romanoffTerm q else 0) := by
      gcongr
      exact htailSummable.sum_le_tsum T (fun q hq ↦ by
        split_ifs
        · exact romanoffTerm_nonneg q
        · exact le_rfl)
    _ = 1 + romanoffTail z := rfl

/-- Divisibility of a difference of two powers of two is controlled exactly
by the multiplicative order.  The common lower power can be cancelled
because the modulus is odd. -/
theorem dvd_two_pow_add_sub_two_pow_iff_twoOrder_dvd
    {q ℓ h : ℕ} (hq : Odd q) :
    q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ ↔ twoOrder q ∣ h := by
  have hfactor : 2 ^ (ℓ + h) - 2 ^ ℓ = 2 ^ ℓ * (2 ^ h - 1) := by
    rw [pow_add, Nat.mul_sub_left_distrib, mul_one]
  have hcop : q.Coprime (2 ^ ℓ) := by
    exact Nat.Coprime.pow_right ℓ (Nat.coprime_two_right.mpr hq)
  rw [hfactor, hcop.dvd_mul_left]
  exact twoOrder_dvd_iff_dvd_two_pow_sub_one.symm

/-- Averaged singular-factor estimate for the differences
`2^(ℓ+h) - 2^ℓ`.  Each modulus occurs once per multiplicative-order
period, and the resulting majorant is precisely Romanoff's series. -/
theorem average_powDifference_singularSum_le
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Odd q) (ℓ H : ℕ) :
    (∑ h ∈ Finset.Ioc 0 H,
        ∑ q ∈ Q with q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ, romanoffCoeff q) ≤
      (H : ℝ) * ∑ q ∈ Q, romanoffTerm q := by
  classical
  have hcard (q : ℕ) (hq : q ∈ Q) :
      ((Finset.Ioc 0 H).filter
          (fun h ↦ q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ)).card =
        H / twoOrder q := by
    have hfilter :
        (Finset.Ioc 0 H).filter
            (fun h ↦ q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ) =
          (Finset.Ioc 0 H).filter (fun h ↦ twoOrder q ∣ h) := by
      ext h
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ ↦
        dvd_two_pow_add_sub_two_pow_iff_twoOrder_dvd (hQ q hq)
    rw [hfilter]
    exact Nat.Ioc_filter_dvd_card_eq_div H (twoOrder q)
  calc
    (∑ h ∈ Finset.Ioc 0 H,
        ∑ q ∈ Q with q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ, romanoffCoeff q) =
        ∑ q ∈ Q, romanoffCoeff q *
          (((Finset.Ioc 0 H).filter
            (fun h ↦ q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ)).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ q ∈ Q, romanoffCoeff q * ((H / twoOrder q : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hcard q hq]
    _ ≤ ∑ q ∈ Q,
        (H : ℝ) * (romanoffCoeff q / (twoOrder q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        romanoffCoeff q * ((H / twoOrder q : ℕ) : ℝ) ≤
            romanoffCoeff q * ((H : ℝ) / (twoOrder q : ℝ)) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le (romanoffCoeff_nonneg q)
        _ = (H : ℝ) * (romanoffCoeff q / (twoOrder q : ℝ)) := by ring
    _ = (H : ℝ) * ∑ q ∈ Q, romanoffTerm q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- Reindex the powers above a fixed lower exponent by their positive gap. -/
private theorem upperSlice_eq_gapSum (z y ℓ J : ℕ) :
    (∑ k ∈ Finset.range J with ℓ < k,
        singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) =
      ∑ h ∈ Finset.Ioc 0 (J - 1 - ℓ),
        singularFactor (2 ^ (ℓ + h) - 2 ^ ℓ) z y := by
  classical
  apply Finset.sum_bij (fun k _ ↦ k - ℓ)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ioc]
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
    omega
  · intro h hh
    simp only [Finset.mem_Ioc] at hh
    refine ⟨ℓ + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have hpows : 2 ^ ℓ ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) hk.2.le
    rw [Nat.dist_eq_sub_of_le_right hpows]
    rw [Nat.add_sub_of_le hk.2.le]

/-- The ordered off-diagonal sum is twice the sum over pairs whose first
exponent is the larger one. -/
private theorem orderedOffDiagonal_eq_two_upper (z y J : ℕ) :
    (∑ k ∈ Finset.range J,
        ∑ ℓ ∈ Finset.range J with k ≠ ℓ,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) =
      2 * (∑ ℓ ∈ Finset.range J,
        ∑ k ∈ Finset.range J with ℓ < k,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) := by
  classical
  let F : ℕ → ℕ → ℝ := fun k ℓ ↦
    singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y
  have hsplit (k ℓ : ℕ) :
      (if k ≠ ℓ then F k ℓ else 0) =
        (if ℓ < k then F k ℓ else 0) +
          (if k < ℓ then F k ℓ else 0) := by
    by_cases h₁ : ℓ < k <;> by_cases h₂ : k < ℓ <;>
      simp [h₁, h₂] <;> omega
  have hsymm (k ℓ : ℕ) : F k ℓ = F ℓ k := by
    simp only [F, Nat.dist_comm]
  change
    (∑ k ∈ Finset.range J, ∑ ℓ ∈ Finset.range J with k ≠ ℓ, F k ℓ) =
      2 * (∑ ℓ ∈ Finset.range J, ∑ k ∈ Finset.range J with ℓ < k, F k ℓ)
  simp_rw [Finset.sum_filter, hsplit, Finset.sum_add_distrib]
  have hfirst :
      (∑ k ∈ Finset.range J, ∑ ℓ ∈ Finset.range J,
          if ℓ < k then F k ℓ else 0) =
        ∑ ℓ ∈ Finset.range J, ∑ k ∈ Finset.range J,
          if ℓ < k then F k ℓ else 0 := by
    rw [Finset.sum_comm]
  rw [hfirst]
  have hsecond :
      (∑ k ∈ Finset.range J, ∑ ℓ ∈ Finset.range J,
          if k < ℓ then F k ℓ else 0) =
        ∑ ℓ ∈ Finset.range J, ∑ k ∈ Finset.range J,
          if ℓ < k then F k ℓ else 0 := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : ℓ < k
    · simp [h, hsymm]
    · simp [h]
  rw [hsecond]
  ring

/-- Exact finite local-product estimate used in the second moment.  The
bound is uniform in the upper sieve endpoint `y`; all dependence on the
lower endpoint is through the convergent Romanoff tail. -/
theorem orderedOffDiagonal_singularFactor_le (z y J : ℕ) (hz : 2 ≤ z) :
    (∑ k ∈ Finset.range J,
        ∑ ℓ ∈ Finset.range J with k ≠ ℓ,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) ≤
      (J : ℝ) ^ 2 * (1 + romanoffTail z) := by
  classical
  let Q := singularPrimeProducts z y
  let R : ℝ := ∑ q ∈ Q, romanoffTerm q
  let S : ℕ := ∑ ℓ ∈ Finset.range J, (J - 1 - ℓ)
  have hQodd : ∀ q ∈ Q, Odd q := by
    intro q hq
    exact odd_of_mem_singularPrimeProducts hz hq
  have hRnonneg : 0 ≤ R := by
    exact Finset.sum_nonneg fun q _ ↦ romanoffTerm_nonneg q
  have hRtail : R ≤ 1 + romanoffTail z := by
    apply sum_romanoffTerm_le_one_add_tail Q z
    intro q hq
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · exact Or.inr (z_lt_of_mem_singularPrimeProducts_of_ne_one hq hq1)
  have hslice (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range J) :
      (∑ k ∈ Finset.range J with ℓ < k,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) ≤
        ((J - 1 - ℓ : ℕ) : ℝ) * R := by
    rw [upperSlice_eq_gapSum]
    calc
      (∑ h ∈ Finset.Ioc 0 (J - 1 - ℓ),
          singularFactor (2 ^ (ℓ + h) - 2 ^ ℓ) z y) =
          ∑ h ∈ Finset.Ioc 0 (J - 1 - ℓ),
            ∑ q ∈ Q with q ∣ 2 ^ (ℓ + h) - 2 ^ ℓ,
              romanoffCoeff q := by
        apply Finset.sum_congr rfl
        intro h hh
        exact singularFactor_eq_sum_romanoffCoeff
          (2 ^ (ℓ + h) - 2 ^ ℓ) z y hz
      _ ≤ ((J - 1 - ℓ : ℕ) : ℝ) * R :=
        average_powDifference_singularSum_le Q hQodd ℓ (J - 1 - ℓ)
  have hupper :
      (∑ ℓ ∈ Finset.range J,
        ∑ k ∈ Finset.range J with ℓ < k,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) ≤
        (S : ℝ) * R := by
    calc
      (∑ ℓ ∈ Finset.range J,
        ∑ k ∈ Finset.range J with ℓ < k,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) ≤
          ∑ ℓ ∈ Finset.range J,
            ((J - 1 - ℓ : ℕ) : ℝ) * R := by
        exact Finset.sum_le_sum fun ℓ hℓ ↦ hslice ℓ hℓ
      _ = (S : ℝ) * R := by
        rw [← Finset.sum_mul, ← Nat.cast_sum]
  have hStwo : S * 2 = J * (J - 1) := by
    calc
      S * 2 = (∑ ℓ ∈ Finset.range J, ℓ) * 2 := by
        congr 1
        exact Finset.sum_range_reflect (fun ℓ : ℕ ↦ ℓ) J
      _ = J * (J - 1) := Finset.sum_range_id_mul_two J
  rw [orderedOffDiagonal_eq_two_upper]
  calc
    2 * (∑ ℓ ∈ Finset.range J,
        ∑ k ∈ Finset.range J with ℓ < k,
          singularFactor (Nat.dist (2 ^ k) (2 ^ ℓ)) z y) ≤
        2 * ((S : ℝ) * R) :=
      mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = ((J * (J - 1) : ℕ) : ℝ) * R := by
      have hStwoR : (S : ℝ) * 2 = ((J * (J - 1) : ℕ) : ℝ) := by
        exact_mod_cast hStwo
      rw [show 2 * ((S : ℝ) * R) = ((S : ℝ) * 2) * R by ring,
        hStwoR]
    _ ≤ (J : ℝ) ^ 2 * R := by
      apply mul_le_mul_of_nonneg_right _ hRnonneg
      rw [pow_two, Nat.cast_mul]
      exact_mod_cast Nat.mul_le_mul_left J (Nat.sub_le J 1)
    _ ≤ (J : ℝ) ^ 2 * (1 + romanoffTail z) := by
      exact mul_le_mul_of_nonneg_left hRtail (sq_nonneg (J : ℝ))

end Erdos851
