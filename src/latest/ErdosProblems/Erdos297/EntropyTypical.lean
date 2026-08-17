/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Product Bernoulli weights and typical-set counting

This file contains the finite probability calculation used in the lower-bound
argument for Erdős Problem 297.  It deliberately uses only finite sums.  Thus
there is no measurability overhead when the sample space is the powerset of a
finite set of denominators.

The central facts are:

* product Bernoulli weights on `I.powerset` have total mass one;
* an additive statistic has the usual mean and variance;
* Chebyshev bounds its exceptional mass;
* an event of positive mass on which every atom has information at least
  `H - d` contains at least `mass * exp (H - d)` atoms.
-/

open Finset
open scoped BigOperators

namespace Erdos297
namespace EntropyTypical

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Product Bernoulli mass of a subset `A` of the finite coordinate set `I`. -/
def bernoulliWeight (I : Finset ι) (p : ι → ℝ) (A : Finset ι) : ℝ :=
  ∏ i ∈ I, if i ∈ A then p i else 1 - p i

/-- Mass assigned by the product Bernoulli law to a finite family of subsets. -/
def bernoulliMass (I : Finset ι) (p : ι → ℝ) (E : Finset (Finset ι)) : ℝ :=
  ∑ A ∈ E.filter (· ⊆ I), bernoulliWeight I p A

/-- An additive statistic on a subset. -/
def subsetLinear (I : Finset ι) (x : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ I, if i ∈ A then x i else 0

/-- Mean of `subsetLinear I x` under the Bernoulli product law. -/
def bernoulliMean (I : Finset ι) (p x : ι → ℝ) : ℝ :=
  ∑ i ∈ I, p i * x i

/-- Variance of `subsetLinear I x` under the Bernoulli product law. -/
def bernoulliVariance (I : Finset ι) (p x : ι → ℝ) : ℝ :=
  ∑ i ∈ I, p i * (1 - p i) * (x i) ^ 2

private lemma sum_powerset_insert {I : Finset ι} {a : ι} (ha : a ∉ I)
    (f : Finset ι → ℝ) :
    (∑ A ∈ (insert a I).powerset, f A) =
      (∑ A ∈ I.powerset, f A) + ∑ A ∈ I.powerset, f (insert a A) := by
  rw [powerset_insert, sum_union]
  · rw [sum_image]
    intro A hA B hB hAB
    have haA : a ∉ A := fun hmem ↦ ha (mem_powerset.mp hA hmem)
    have haB : a ∉ B := fun hmem ↦ ha (mem_powerset.mp hB hmem)
    simpa [erase_insert haA, erase_insert haB] using
      congrArg (fun S : Finset ι ↦ S.erase a) hAB
  · rw [disjoint_left]
    intro A hAI hAimage
    have hAa : a ∉ A := fun hmem ↦ ha (mem_powerset.mp hAI hmem)
    rcases mem_image.mp hAimage with ⟨B, hBI, hBA⟩
    have : a ∈ A := by
      rw [← hBA]
      exact mem_insert_self _ _
    exact hAa this

private lemma bernoulliWeight_insert_not_mem {I A : Finset ι} {a : ι}
    (haI : a ∉ I) (hAI : A ⊆ I) (p : ι → ℝ) :
    bernoulliWeight (insert a I) p A =
      (1 - p a) * bernoulliWeight I p A := by
  have haA : a ∉ A := fun ha ↦ haI (hAI ha)
  simp [bernoulliWeight, haI, haA]

private lemma bernoulliWeight_insert_mem {I A : Finset ι} {a : ι}
    (haI : a ∉ I) (hAI : A ⊆ I) (p : ι → ℝ) :
    bernoulliWeight (insert a I) p (insert a A) =
      p a * bernoulliWeight I p A := by
  have haA : a ∉ A := fun ha ↦ haI (hAI ha)
  rw [bernoulliWeight, bernoulliWeight, prod_insert haI]
  rw [if_pos (mem_insert_self a A)]
  congr 1
  apply prod_congr rfl
  intro i hi
  have hia : i ≠ a := fun h ↦ haI (h ▸ hi)
  simp [hia]

private lemma subsetLinear_insert_not_mem {I A : Finset ι} {a : ι}
    (haI : a ∉ I) (hAI : A ⊆ I) (x : ι → ℝ) :
    subsetLinear (insert a I) x A = subsetLinear I x A := by
  have haA : a ∉ A := fun ha ↦ haI (hAI ha)
  simp [subsetLinear, haA]

private lemma subsetLinear_insert_mem {I A : Finset ι} {a : ι}
    (haI : a ∉ I) (hAI : A ⊆ I) (x : ι → ℝ) :
      subsetLinear (insert a I) x (insert a A) = x a + subsetLinear I x A := by
  have haA : a ∉ A := fun ha ↦ haI (hAI ha)
  rw [subsetLinear, subsetLinear, sum_insert haI]
  rw [if_pos (mem_insert_self a A)]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hia : i ≠ a := fun h ↦ haI (h ▸ hi)
  simp [hia]

@[simp] theorem sum_bernoulliWeight_powerset (I : Finset ι) (p : ι → ℝ) :
    (∑ A ∈ I.powerset, bernoulliWeight I p A) = 1 := by
  induction I using Finset.induction_on with
  | empty => simp [bernoulliWeight]
  | @insert a I ha ih =>
      rw [sum_powerset_insert ha]
      have hleft : (∑ A ∈ I.powerset, bernoulliWeight (insert a I) p A) =
          ∑ A ∈ I.powerset, (1 - p a) * bernoulliWeight I p A := by
        apply sum_congr rfl
        intro A hA
        exact bernoulliWeight_insert_not_mem ha (mem_powerset.mp hA) p
      have hright : (∑ A ∈ I.powerset,
          bernoulliWeight (insert a I) p (insert a A)) =
          ∑ A ∈ I.powerset, p a * bernoulliWeight I p A := by
        apply sum_congr rfl
        intro A hA
        exact bernoulliWeight_insert_mem ha (mem_powerset.mp hA) p
      rw [hleft, hright]
      rw [← mul_sum, ← mul_sum, ih]
      ring

theorem bernoulliWeight_nonneg (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) (A : Finset ι) :
    0 ≤ bernoulliWeight I p A := by
  apply prod_nonneg
  intro i hi
  split_ifs
  · exact hp0 i hi
  · exact sub_nonneg.mpr (hp1 i hi)

theorem sum_bernoulliWeight_mul_subsetLinear (I : Finset ι) (p x : ι → ℝ) :
    (∑ A ∈ I.powerset,
      bernoulliWeight I p A * subsetLinear I x A) = bernoulliMean I p x := by
  induction I using Finset.induction_on with
  | empty => simp [bernoulliMean, bernoulliWeight, subsetLinear]
  | @insert a I ha ih =>
      rw [sum_powerset_insert ha]
      have hleft : (∑ A ∈ I.powerset,
          bernoulliWeight (insert a I) p A * subsetLinear (insert a I) x A) =
          ∑ A ∈ I.powerset,
            ((1 - p a) * bernoulliWeight I p A) * subsetLinear I x A := by
        apply sum_congr rfl
        intro A hA
        rw [bernoulliWeight_insert_not_mem ha (mem_powerset.mp hA) p,
          subsetLinear_insert_not_mem ha (mem_powerset.mp hA) x]
      have hright : (∑ A ∈ I.powerset,
          bernoulliWeight (insert a I) p (insert a A) *
            subsetLinear (insert a I) x (insert a A)) =
          ∑ A ∈ I.powerset,
            (p a * bernoulliWeight I p A) * (x a + subsetLinear I x A) := by
        apply sum_congr rfl
        intro A hA
        rw [bernoulliWeight_insert_mem ha (mem_powerset.mp hA) p,
          subsetLinear_insert_mem ha (mem_powerset.mp hA) x]
      rw [hleft, hright]
      simp_rw [mul_add]
      rw [sum_add_distrib]
      simp_rw [mul_assoc]
      rw [← mul_sum, ← mul_sum, ← mul_sum, ih]
      have hconst : (∑ A ∈ I.powerset, bernoulliWeight I p A * x a) = x a := by
        calc
          (∑ A ∈ I.powerset, bernoulliWeight I p A * x a) =
              x a * ∑ A ∈ I.powerset, bernoulliWeight I p A := by
                rw [mul_sum]
                apply sum_congr rfl
                intro A hA
                ring
          _ = x a := by rw [sum_bernoulliWeight_powerset, mul_one]
      rw [hconst]
      simp [bernoulliMean, ha]
      ring

/-- Exact second centered moment of an additive Bernoulli statistic. -/
theorem sum_bernoulliWeight_mul_centered_sq (I : Finset ι) (p x : ι → ℝ) :
    (∑ A ∈ I.powerset,
      bernoulliWeight I p A *
        (subsetLinear I x A - bernoulliMean I p x) ^ 2) =
      bernoulliVariance I p x := by
  induction I using Finset.induction_on with
  | empty => simp [bernoulliMean, bernoulliVariance, bernoulliWeight, subsetLinear]
  | @insert a I ha ih =>
      rw [sum_powerset_insert ha]
      have hleft : (∑ A ∈ I.powerset,
          bernoulliWeight (insert a I) p A *
            (subsetLinear (insert a I) x A - bernoulliMean (insert a I) p x) ^ 2) =
          ∑ A ∈ I.powerset,
            ((1 - p a) * bernoulliWeight I p A) *
              (subsetLinear I x A - bernoulliMean (insert a I) p x) ^ 2 := by
        apply sum_congr rfl
        intro A hA
        rw [bernoulliWeight_insert_not_mem ha (mem_powerset.mp hA) p,
          subsetLinear_insert_not_mem ha (mem_powerset.mp hA) x]
      have hright : (∑ A ∈ I.powerset,
          bernoulliWeight (insert a I) p (insert a A) *
            (subsetLinear (insert a I) x (insert a A) -
              bernoulliMean (insert a I) p x) ^ 2) =
          ∑ A ∈ I.powerset,
            (p a * bernoulliWeight I p A) *
              (x a + subsetLinear I x A - bernoulliMean (insert a I) p x) ^ 2 := by
        apply sum_congr rfl
        intro A hA
        rw [bernoulliWeight_insert_mem ha (mem_powerset.mp hA) p,
          subsetLinear_insert_mem ha (mem_powerset.mp hA) x]
      rw [hleft, hright]
      simp_rw [bernoulliMean, sum_insert ha]
      have hpoint : ∀ A ∈ I.powerset,
          (1 - p a) * bernoulliWeight I p A *
                (subsetLinear I x A - (p a * x a + ∑ i ∈ I, p i * x i)) ^ 2 +
              p a * bernoulliWeight I p A *
                (x a + subsetLinear I x A -
                  (p a * x a + ∑ i ∈ I, p i * x i)) ^ 2 =
            bernoulliWeight I p A *
              (subsetLinear I x A - ∑ i ∈ I, p i * x i) ^ 2 +
            p a * (1 - p a) * (x a) ^ 2 * bernoulliWeight I p A := by
        intro A hA
        ring
      rw [← sum_add_distrib]
      rw [sum_congr rfl hpoint]
      rw [sum_add_distrib]
      change
        (∑ A ∈ I.powerset,
          bernoulliWeight I p A *
            (subsetLinear I x A - bernoulliMean I p x) ^ 2) +
          (∑ A ∈ I.powerset,
            p a * (1 - p a) * (x a) ^ 2 * bernoulliWeight I p A) =
        bernoulliVariance (insert a I) p x
      rw [ih]
      rw [← mul_sum, sum_bernoulliWeight_powerset]
      simp [bernoulliVariance, ha]
      ring

/-- Chebyshev's inequality for an explicitly weighted finite sample space. -/
theorem finite_weighted_chebyshev {α : Type*} [DecidableEq α]
    (Ω : Finset α) (w X : α → ℝ) (μ V t : ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z)
    (hsecond : (∑ z ∈ Ω, w z * (X z - μ) ^ 2) ≤ V)
    (ht : 0 < t) :
    (∑ z ∈ Ω.filter (fun z ↦ t ≤ |X z - μ|), w z) ≤ V / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  calc
    (∑ z ∈ Ω.filter (fun z ↦ t ≤ |X z - μ|), w z)
        ≤ ∑ z ∈ Ω.filter (fun z ↦ t ≤ |X z - μ|),
            (w z * (X z - μ) ^ 2) / t ^ 2 := by
          apply sum_le_sum
          intro z hz
          have hzlarge : t ≤ |X z - μ| := (mem_filter.mp hz).2
          have hsquare : t ^ 2 ≤ (X z - μ) ^ 2 := by
            nlinarith [sq_abs (X z - μ)]
          exact (le_div_iff₀ ht2).2 (by
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left hsquare (hw z (mem_filter.mp hz).1))
    _ = (∑ z ∈ Ω.filter (fun z ↦ t ≤ |X z - μ|),
            w z * (X z - μ) ^ 2) / t ^ 2 := by rw [sum_div]
    _ ≤ (∑ z ∈ Ω, w z * (X z - μ) ^ 2) / t ^ 2 := by
          apply div_le_div_of_nonneg_right _ ht2.le
          apply sum_le_sum_of_subset_of_nonneg
          · exact filter_subset _ _
          · intro z hzΩ hznot
            exact mul_nonneg (hw z hzΩ) (sq_nonneg _)
    _ ≤ V / t ^ 2 := div_le_div_of_nonneg_right hsecond ht2.le

/-- Chebyshev concentration for an additive statistic under a finite product
Bernoulli law. -/
theorem bernoulli_subsetLinear_tail_le (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    (∑ A ∈ I.powerset.filter (fun A ↦
        t ≤ |subsetLinear I x A - bernoulliMean I p x|),
      bernoulliWeight I p A) ≤ bernoulliVariance I p x / t ^ 2 := by
  apply finite_weighted_chebyshev I.powerset
    (bernoulliWeight I p) (subsetLinear I x)
    (bernoulliMean I p x) (bernoulliVariance I p x) t
  · intro A hA
    exact bernoulliWeight_nonneg I p hp0 hp1 A
  · exact (sum_bernoulliWeight_mul_centered_sq I p x).le
  · exact ht

/-- Negative log-likelihood (information) of a subset under the product law. -/
def bernoulliInformation (I : Finset ι) (p : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ I, if i ∈ A then -Real.log (p i) else -Real.log (1 - p i)

/-- Shannon entropy of the finite product Bernoulli law (natural logarithms). -/
def bernoulliEntropy (I : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ I, -(p i * Real.log (p i) + (1 - p i) * Real.log (1 - p i))

/-- Variance of the information, written using the log-odds increment. -/
def informationVariance (I : Finset ι) (p : ι → ℝ) : ℝ :=
  bernoulliVariance I p (fun i ↦ Real.log (1 - p i) - Real.log (p i))

theorem bernoulliInformation_eq (I : Finset ι) (p : ι → ℝ) (A : Finset ι) :
    bernoulliInformation I p A =
      (∑ i ∈ I, -Real.log (1 - p i)) +
        subsetLinear I (fun i ↦ Real.log (1 - p i) - Real.log (p i)) A := by
  simp_rw [bernoulliInformation, subsetLinear, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem bernoulliEntropy_eq_informationMean (I : Finset ι) (p : ι → ℝ) :
    bernoulliEntropy I p =
      (∑ i ∈ I, -Real.log (1 - p i)) +
        bernoulliMean I p (fun i ↦ Real.log (1 - p i) - Real.log (p i)) := by
  simp_rw [bernoulliEntropy, bernoulliMean, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  ring

/-- Chebyshev concentration of information around entropy.  The right-hand
side is the exact information variance, so later estimates may insert whatever
uniform bounds on the logistic probabilities are most convenient. -/
theorem bernoulliInformation_tail_le (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    (∑ A ∈ I.powerset.filter (fun A ↦
        t ≤ |bernoulliInformation I p A - bernoulliEntropy I p|),
      bernoulliWeight I p A) ≤ informationVariance I p / t ^ 2 := by
  simpa [bernoulliInformation_eq, bernoulliEntropy_eq_informationMean,
    informationVariance, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using bernoulli_subsetLinear_tail_le I p
      (fun i ↦ Real.log (1 - p i) - Real.log (p i)) hp0 hp1 ht

/-- A coarse but convenient information-variance bound.  For logistic weights
the log-odds on the right are explicit (equal, up to sign, to the logistic
parameter divided by the coordinate), so this estimate is immediately
applicable. -/
theorem informationVariance_le_card_mul_sq (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hodds : ∀ i ∈ I,
      |Real.log (1 - p i) - Real.log (p i)| ≤ L) :
    informationVariance I p ≤ (I.card : ℝ) * L ^ 2 := by
  rw [informationVariance, bernoulliVariance]
  calc
    (∑ i ∈ I,
        p i * (1 - p i) *
          (Real.log (1 - p i) - Real.log (p i)) ^ 2) ≤
        ∑ _i ∈ I, L ^ 2 := by
      apply sum_le_sum
      intro i hi
      have hpnonneg := hp0 i hi
      have hqnonneg : 0 ≤ 1 - p i := sub_nonneg.mpr (hp1 i hi)
      have hpq : p i * (1 - p i) ≤ 1 := by
        nlinarith [mul_nonneg hpnonneg hqnonneg]
      have hsquare :
          (Real.log (1 - p i) - Real.log (p i)) ^ 2 ≤ L ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hL] using hodds i hi
      calc
        p i * (1 - p i) *
              (Real.log (1 - p i) - Real.log (p i)) ^ 2 ≤
            1 * (Real.log (1 - p i) - Real.log (p i)) ^ 2 := by
              exact mul_le_mul_of_nonneg_right hpq (sq_nonneg _)
        _ ≤ L ^ 2 := by simpa using hsquare
    _ = (I.card : ℝ) * L ^ 2 := by simp

/-- Concrete Chebyshev bound obtained from a uniform log-odds estimate. -/
theorem bernoulliInformation_tail_le_card_mul_sq (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {L t : ℝ} (hL : 0 ≤ L) (ht : 0 < t)
    (hodds : ∀ i ∈ I,
      |Real.log (1 - p i) - Real.log (p i)| ≤ L) :
    (∑ A ∈ I.powerset.filter (fun A ↦
        t ≤ |bernoulliInformation I p A - bernoulliEntropy I p|),
      bernoulliWeight I p A) ≤ (I.card : ℝ) * L ^ 2 / t ^ 2 := by
  exact (bernoulliInformation_tail_le I p hp0 hp1 ht).trans
    (div_le_div_of_nonneg_right
      (informationVariance_le_card_mul_sq I p hp0 hp1 hL hodds)
      (sq_nonneg t))

theorem bernoulliWeight_eq_exp_neg_information (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 < p i) (hp1 : ∀ i ∈ I, p i < 1)
    (A : Finset ι) :
    bernoulliWeight I p A = Real.exp (-bernoulliInformation I p A) := by
  rw [bernoulliWeight, bernoulliInformation, ← Finset.sum_neg_distrib,
    Real.exp_sum]
  apply prod_congr rfl
  intro i hi
  split_ifs
  · rw [neg_neg, Real.exp_log (hp0 i hi)]
  · rw [neg_neg, Real.exp_log (sub_pos.mpr (hp1 i hi))]

/-- A lower information bound gives a uniform upper bound for atom masses. -/
theorem bernoulliWeight_le_exp_of_information_ge (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 < p i) (hp1 : ∀ i ∈ I, p i < 1)
    {A : Finset ι} {H d : ℝ} (hinfo : H - d ≤ bernoulliInformation I p A) :
    bernoulliWeight I p A ≤ Real.exp (-H + d) := by
  rw [bernoulliWeight_eq_exp_neg_information I p hp0 hp1 A]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Finite mass-to-cardinality conversion: if each atom has mass at most `B`,
an event carrying mass at least `m` has at least `m / B` atoms. -/
theorem event_card_ge_mass_div_atomBound {α : Type*} [DecidableEq α]
    (E : Finset α) (w : α → ℝ) {m B : ℝ}
    (hmass : m ≤ ∑ z ∈ E, w z) (hbound : ∀ z ∈ E, w z ≤ B)
    (hB : 0 < B) :
    m / B ≤ (E.card : ℝ) := by
  have hsum : (∑ z ∈ E, w z) ≤ (E.card : ℝ) * B := by
    calc
      (∑ z ∈ E, w z) ≤ ∑ _z ∈ E, B := sum_le_sum hbound
      _ = (E.card : ℝ) * B := by simp
  exact (div_le_iff₀ hB).2 (hmass.trans hsum)

/-- The typical-set counting lower bound in its form used by the Erdős 297
lower-bound argument.  `E` may already include an exact reciprocal-sum event;
only its positive product mass and its information lower bound matter here. -/
theorem typical_event_card_lower_bound (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 < p i) (hp1 : ∀ i ∈ I, p i < 1)
    (E : Finset (Finset ι)) {m H d : ℝ}
    (hmass : m ≤ ∑ A ∈ E, bernoulliWeight I p A)
    (hinfo : ∀ A ∈ E, H - d ≤ bernoulliInformation I p A) :
    m * Real.exp (H - d) ≤ (E.card : ℝ) := by
  have hB : 0 < Real.exp (-H + d) := Real.exp_pos _
  have hcard := event_card_ge_mass_div_atomBound E (bernoulliWeight I p)
    hmass (fun A hAE ↦ bernoulliWeight_le_exp_of_information_ge I p hp0 hp1
      (hinfo A hAE)) hB
  have hinv : (Real.exp (-H + d))⁻¹ = Real.exp (H - d) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  simpa [div_eq_mul_inv, hinv] using hcard

end

end EntropyTypical
end Erdos297

#print axioms Erdos297.EntropyTypical.sum_bernoulliWeight_mul_centered_sq
#print axioms Erdos297.EntropyTypical.bernoulliInformation_tail_le
#print axioms Erdos297.EntropyTypical.typical_event_card_lower_bound
