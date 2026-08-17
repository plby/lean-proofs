import ErdosProblems.Erdos877.Core
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Counting small fingerprints for Erdős Problem 877

The container argument uses fingerprints whose cardinality is at most
`72 * p * n`, with `p = 1 / (72 * R * K)`, `R = 2^K`, and `K = 40`.
This file records a generic weighted-binomial count and a deliberately coarse
but fully explicit specialization showing that all such fingerprints contribute
at most `2 ^ (n / 2^32)` choices.
-/

open scoped BigOperators
open Filter

namespace Erdos877

/-- The fixed depth used in the explicit fingerprint estimate. -/
def fingerprintK : ℕ := 40

/-- The scale `R = 2^K` used in the explicit fingerprint estimate. -/
def fingerprintR : ℕ := 2 ^ fingerprintK

/-- The denominator `R * K` of the fingerprint cardinality cutoff. -/
def fingerprintDenom : ℕ := fingerprintR * fingerprintK

/-- The container parameter `p = 1 / (72 * R * K)`. -/
noncomputable def fingerprintP : ℝ :=
  1 / (72 * (fingerprintR : ℝ) * fingerprintK)

/-- Subsets of `L` whose cardinality is at most `r`. -/
def smallSubsets {α : Type*} [DecidableEq α] (L : Finset α) (r : ℕ) :
    Finset (Finset α) :=
  L.powerset.filter fun S => S.card ≤ r

@[simp] theorem mem_smallSubsets {α : Type*} [DecidableEq α]
    {L S : Finset α} {r : ℕ} :
    S ∈ smallSubsets L r ↔ S ⊆ L ∧ S.card ≤ r := by
  simp [smallSubsets]

/-- Generic weighted-binomial estimate for subsets of a finite type with
cardinality at most `r`. -/
theorem card_smallSubsets_mul_pow_le {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (smallSubsets (Finset.univ : Finset α) r).card * x ^ r ≤
      (1 + x) ^ Fintype.card α := by
  let F := smallSubsets (Finset.univ : Finset α) r
  calc
    (F.card : ℝ) * x ^ r = ∑ _S ∈ F, x ^ r := by simp
    _ ≤ ∑ S ∈ F, x ^ S.card := by
      apply Finset.sum_le_sum
      intro S hS
      exact pow_le_pow_of_le_one hx0 hx1 (mem_smallSubsets.mp hS).2
    _ ≤ ∑ S ∈ (Finset.univ : Finset α).powerset, x ^ S.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro S hS hSF
        positivity
    _ = (1 + x) ^ Fintype.card α := by
      simpa [add_comm] using
        (Finset.sum_pow_mul_eq_add_pow x 1 (Finset.univ : Finset α))

/-- The family of all fingerprints on `Fin n` satisfying the real cutoff from
the container construction. -/
noncomputable def realCutoffFingerprints (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter fun S =>
    (S.card : ℝ) ≤ 72 * fingerprintP * n

@[simp] theorem mem_realCutoffFingerprints {n : ℕ} {S : Finset (Fin n)} :
    S ∈ realCutoffFingerprints n ↔ (S.card : ℝ) ≤ 72 * fingerprintP * n := by
  classical
  simp [realCutoffFingerprints]

/-- The displayed real cutoff is exactly strong enough to imply the natural
cutoff `card ≤ n / (R*K)`. -/
theorem card_le_div_fingerprintDenom {n : ℕ} {S : Finset (Fin n)}
    (hS : (S.card : ℝ) ≤ 72 * fingerprintP * n) :
    S.card ≤ n / fingerprintDenom := by
  have hcutoff : 72 * fingerprintP * (n : ℝ) =
      (n : ℝ) / fingerprintDenom := by
    simp [fingerprintP, fingerprintDenom, fingerprintR, fingerprintK]
    ring
  rw [hcutoff] at hS
  have hDpos : (0 : ℝ) < fingerprintDenom := by
    norm_num [fingerprintDenom, fingerprintR, fingerprintK]
  have hmul : (S.card : ℝ) * fingerprintDenom ≤ n :=
    (le_div_iff₀ hDpos).mp hS
  apply (Nat.le_div_iff_mul_le (by
    norm_num [fingerprintDenom, fingerprintR, fingerprintK] : 0 < fingerprintDenom)).2
  exact_mod_cast hmul

private theorem one_add_inv_two_pow_pow_le (n : ℕ) :
    (1 + (1 / (2 : ℝ) ^ 64)) ^ n ≤
      (2 : ℝ) ^ (2 * (n / 2 ^ 40 + 1)) := by
  let q := n / 2 ^ 40
  have hmod : n % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (by positivity)
  have hdecomp : n % 2 ^ 40 + 2 ^ 40 * (n / 2 ^ 40) = n :=
    Nat.mod_add_div n (2 ^ 40)
  have hnqNat : n ≤ 2 ^ 40 * (q + 1) := by
    dsimp [q]
    omega
  have hnqReal : (n : ℝ) * (1 / (2 : ℝ) ^ 64) ≤ (q : ℝ) + 1 := by
    have hcast : (n : ℝ) ≤ (2 ^ 40 : ℕ) * (q + 1) := by
      exact_mod_cast hnqNat
    norm_num at hcast ⊢
    linarith
  have hbase : 1 + (1 / (2 : ℝ) ^ 64) ≤ Real.exp (1 / (2 : ℝ) ^ 64) := by
    nlinarith [Real.add_one_le_exp (1 / (2 : ℝ) ^ 64)]
  calc
    (1 + (1 / (2 : ℝ) ^ 64)) ^ n ≤
        Real.exp (1 / (2 : ℝ) ^ 64) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = Real.exp ((n : ℝ) * (1 / (2 : ℝ) ^ 64)) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (q + 1) := Real.exp_le_exp.mpr hnqReal
    _ = Real.exp 1 ^ (q + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    _ ≤ (4 : ℝ) ^ (q + 1) :=
      pow_le_pow_left₀ (by positivity)
        (Real.exp_one_lt_three.le.trans (by norm_num)) _
    _ = (2 : ℝ) ^ (2 * (n / 2 ^ 40 + 1)) := by
      dsimp [q]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact (pow_mul (2 : ℝ) 2 (n / 2 ^ 40 + 1)).symm

/-- The lower Boolean-lattice layer at the fingerprint denominator has at most
`2 ^ (n / 2^32)` elements.  The estimate holds for every `n`, hence in
particular eventually. -/
theorem card_subsetsUpTo_div_fingerprintDenom_le (n : ℕ) :
    (smallSubsets (Finset.univ : Finset (Fin n)) (n / fingerprintDenom)).card ≤
      2 ^ (n / 2 ^ 32) := by
  classical
  let r := n / fingerprintDenom
  let q := n / 2 ^ 40
  by_cases hn : fingerprintDenom ≤ n
  · have hweighted := card_smallSubsets_mul_pow_le (α := Fin n) r
      (x := (1 / (2 : ℝ) ^ 64)) (by positivity) (by norm_num)
    have hweighted' :
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) *
            (1 / (2 : ℝ) ^ 64) ^ r ≤
          (1 + (1 / (2 : ℝ) ^ 64)) ^ n := by
      simpa using hweighted
    have hxpos : 0 < (1 / (2 : ℝ) ^ 64) ^ r := by positivity
    have hcancel :
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) ≤
          ((2 : ℝ) ^ 64) ^ r * (1 + (1 / (2 : ℝ) ^ 64)) ^ n := by
      have hdiv := (le_div_iff₀ hxpos).2 hweighted'
      calc
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) ≤
            (1 + (1 / (2 : ℝ) ^ 64)) ^ n /
              (1 / (2 : ℝ) ^ 64) ^ r := hdiv
        _ = ((2 : ℝ) ^ 64) ^ r * (1 + (1 / (2 : ℝ) ^ 64)) ^ n := by
          field_simp
          rw [← mul_pow]
          norm_num
    have hsmall := one_add_inv_two_pow_pow_le n
    have hreal :
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) ≤
          (2 : ℝ) ^ (64 * r + 2 * (q + 1)) := by
      calc
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) ≤
            ((2 : ℝ) ^ 64) ^ r * (1 + (1 / (2 : ℝ) ^ 64)) ^ n := hcancel
        _ ≤ ((2 : ℝ) ^ 64) ^ r * (2 : ℝ) ^ (2 * (n / 2 ^ 40 + 1)) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = (2 : ℝ) ^ (64 * r + 2 * (q + 1)) := by
          dsimp [q]
          rw [← pow_mul, ← pow_add]
    have hrq : r ≤ q := by
      have hMD : 2 ^ 40 ≤ fingerprintDenom := by
        norm_num [fingerprintDenom, fingerprintR, fingerprintK]
      have hrD : r * fingerprintDenom ≤ n := by
        simpa [r] using Nat.div_mul_le_self n fingerprintDenom
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ 40)).2
      exact (Nat.mul_le_mul_left r hMD).trans hrD
    have hq40 : 40 ≤ q := by
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ 40)).2
      simpa [q, fingerprintDenom, fingerprintR, fingerprintK, mul_comm] using hn
    have hqTarget : 256 * q ≤ n / 2 ^ 32 := by
      have hqeq : q = (n / 2 ^ 32) / 256 := by
        dsimp [q]
        symm
        rw [Nat.div_div_eq_div_mul]
      rw [hqeq, mul_comm]
      exact Nat.div_mul_le_self (n / 2 ^ 32) 256
    have hexponent : 64 * r + 2 * (q + 1) ≤ n / 2 ^ 32 := by
      have : 64 * r + 2 * (q + 1) ≤ 256 * q := by omega
      exact this.trans hqTarget
    have hreal' :
        ((smallSubsets (Finset.univ : Finset (Fin n)) r).card : ℝ) ≤
          (2 : ℝ) ^ (n / 2 ^ 32) :=
      hreal.trans (pow_le_pow_right₀ (by norm_num) hexponent)
    exact_mod_cast hreal'
  · have hnlt : n < fingerprintDenom := Nat.lt_of_not_ge hn
    have hr0 : n / fingerprintDenom = 0 := Nat.div_eq_of_lt hnlt
    have hfamily : smallSubsets (Finset.univ : Finset (Fin n)) 0 = {∅} := by
      ext S
      simp [smallSubsets]
    rw [hr0, hfamily]
    exact Nat.one_le_two_pow

/-- The real-cutoff fingerprint family is contained in the preceding lower
layer, and therefore satisfies the same explicit estimate. -/
theorem card_realCutoffFingerprints_le (n : ℕ) :
    (realCutoffFingerprints n).card ≤ 2 ^ (n / 2 ^ 32) := by
  classical
  calc
    (realCutoffFingerprints n).card ≤
        (smallSubsets (Finset.univ : Finset (Fin n)) (n / fingerprintDenom)).card := by
      apply Finset.card_le_card
      intro S hS
      rw [mem_smallSubsets]
      exact ⟨Finset.subset_univ _, card_le_div_fingerprintDenom
        (mem_realCutoffFingerprints.mp hS)⟩
    _ ≤ 2 ^ (n / 2 ^ 32) := card_subsetsUpTo_div_fingerprintDenom_le n

/-- Eventual form used directly by enumeration arguments. -/
theorem eventually_card_realCutoffFingerprints_le :
    ∀ᶠ n : ℕ in atTop,
      (realCutoffFingerprints n).card ≤ 2 ^ (n / 2 ^ 32) :=
  Eventually.of_forall card_realCutoffFingerprints_le

end Erdos877
