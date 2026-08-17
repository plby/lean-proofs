/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.FiniteSecondMoment
import Mathlib

/-!
# A finite second-moment schema for the Alon--Bohman--Huang argument

This file contains no graph-specific estimate.  It packages the common final
step of an ABH-style argument.  A witness is carried by a `k n`-element subset
of the vertices of a labelled graph on `Fin n`.  Ordered pairs of witnesses are
split according to the size of their intersection into

* disjoint pairs;
* moderately overlapping pairs (`0 < |A ∩ B| ≤ cutoff n`); and
* largely overlapping pairs (`cutoff n < |A ∩ B|`).

If the three contributions to the second moment, after division by the square
of the mean, are at most `1`, `moderateError n`, and `largeError n`, and both
error terms tend to zero, then a witness exists with probability tending to
one.  A deterministic implication from existence of a witness to a target
graph property then gives the same conclusion for the target property.

All probabilities below are exact normalized cardinalities on the finite set
of labelled simple graphs.  Thus the theorem can be used without any
measurability infrastructure.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos807
namespace ABHSchema

/-! ## Finite uniform probability and moments -/

/-- Exact probability of an event on a finite nonempty uniform sample space. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

/-- Expectation of a natural-valued variable on a finite uniform sample space. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω]
    (X : Ω → ℕ) : ℝ :=
  (∑ ω, (X ω : ℝ)) / Fintype.card Ω

/-- Second moment of a natural-valued variable on a finite uniform sample space. -/
noncomputable def uniformSecondMoment {Ω : Type*} [Fintype Ω]
    (X : Ω → ℕ) : ℝ :=
  (∑ ω, (X ω : ℝ) ^ 2) / Fintype.card Ω

section Uniform

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma uniform_card_pos : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

theorem uniformProbability_nonneg (P : Ω → Prop) :
    0 ≤ uniformProbability P := by
  classical
  exact div_nonneg (Nat.cast_nonneg _) uniform_card_pos.le

theorem uniformProbability_le_one (P : Ω → Prop) :
    uniformProbability P ≤ 1 := by
  classical
  rw [uniformProbability, div_le_one uniform_card_pos]
  exact_mod_cast Finset.card_filter_le (s := Finset.univ) P

theorem uniformProbability_mono {P Q : Ω → Prop}
    (h : ∀ ω, P ω → Q ω) :
    uniformProbability P ≤ uniformProbability Q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ uniform_card_pos.le
  exact_mod_cast Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω)

/-- The support form of Cauchy--Schwarz, normalized by the cardinality of the
sample space.  This is the finite Paley--Zygmund inequality at zero. -/
theorem uniformMean_sq_le_probability_pos_mul_secondMoment (X : Ω → ℕ) :
    uniformMean X ^ 2 ≤
      uniformProbability (fun ω ↦ 0 < X ω) * uniformSecondMoment X := by
  classical
  have hcs := Erdos851.sq_sum_natCast_le_card_pos_mul_sum_sq
    (Finset.univ : Finset Ω) X
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt uniform_card_pos
  have hmean : uniformMean X ^ 2 =
      (∑ ω, (X ω : ℝ)) ^ 2 / (Fintype.card Ω : ℝ) ^ 2 := by
    rw [uniformMean]
    ring
  have hrhs :
      uniformProbability (fun ω ↦ 0 < X ω) * uniformSecondMoment X =
        (((Finset.univ.filter fun ω ↦ 0 < X ω).card : ℝ) *
          ∑ ω, (X ω : ℝ) ^ 2) / (Fintype.card Ω : ℝ) ^ 2 := by
    rw [uniformProbability, uniformSecondMoment]
    rw [Finset.filter_congr_decidable]
    field_simp [hcard]
  rw [hmean, hrhs,
    div_le_div_iff_of_pos_right (sq_pos_of_pos uniform_card_pos)]
  simpa using hcs

/-- If the second moment is at most `(1 + error)` times the square of the
mean, the reciprocal factor is a lower bound for the probability of positive
support. -/
theorem inv_one_add_le_uniformProbability_pos (X : Ω → ℕ) {error : ℝ}
    (hmean : 0 < uniformMean X) (hcoef : 0 < 1 + error)
    (hsecond : uniformSecondMoment X ≤ (1 + error) * uniformMean X ^ 2) :
    (1 + error)⁻¹ ≤ uniformProbability (fun ω ↦ 0 < X ω) := by
  let p := uniformProbability (fun ω ↦ 0 < X ω)
  let μ := uniformMean X
  have hp : 0 ≤ p := uniformProbability_nonneg _
  have hpaley : μ ^ 2 ≤ p * uniformSecondMoment X :=
    uniformMean_sq_le_probability_pos_mul_secondMoment X
  have hupper : p * uniformSecondMoment X ≤ p * ((1 + error) * μ ^ 2) :=
    mul_le_mul_of_nonneg_left hsecond hp
  have hchain : μ ^ 2 ≤ (p * (1 + error)) * μ ^ 2 := by
    calc
      μ ^ 2 ≤ p * uniformSecondMoment X := hpaley
      _ ≤ p * ((1 + error) * μ ^ 2) := hupper
      _ = (p * (1 + error)) * μ ^ 2 := by ring
  have hmusq : 0 < μ ^ 2 := sq_pos_of_pos hmean
  have hone : 1 ≤ p * (1 + error) := by
    apply (mul_le_mul_iff_of_pos_right hmusq).mp
    simpa using hchain
  rw [inv_le_iff_one_le_mul₀ hcoef]
  simpa [mul_comm] using hone

end Uniform

/-! ## Counts of subset witnesses and their overlap decomposition -/

/-- Number of successful indices from an arbitrary finite candidate family.
This is the version used when witnesses have stable labelled roles, for
example when the index type is a space of slot assignments. -/
noncomputable def indexedWitnessCount {I : ℕ → Type*}
    (Candidates : ∀ n, Finset (I n))
    (Witness : ∀ n, I n → SimpleGraph (Fin n) → Prop)
    (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Candidates n).filter fun i ↦ Witness n i G).card

/-- The family of all `k`-subsets of the labelled vertex set. -/
def candidateSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard k

/-- The number of `k`-sets which satisfy the witness predicate in `G`. -/
noncomputable def witnessCount (k : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((candidateSets n (k n)).filter fun A ↦ Witness n A G).card

/-- Ordered pairs of witnesses in a fixed host graph. -/
noncomputable def witnessPairs (k : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) := by
  classical
  let good := (candidateSets n (k n)).filter fun A ↦ Witness n A G
  exact good ×ˢ good

/-- Number of ordered witness pairs whose intersection size satisfies `R`. -/
noncomputable def overlapPairCount (k : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (R : ℕ → Prop) (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((witnessPairs k Witness n G).filter fun AB ↦
    R (AB.1 ∩ AB.2).card).card

/-- Every natural-valued statistic on a finite set lies in exactly one of the
three ranges `= 0`, `0 < · ≤ c`, and `c < ·`. -/
theorem card_eq_filter_zero_add_filter_moderate_add_filter_large
    {α : Type*} (S : Finset α) (z : α → ℕ) (c : ℕ) :
    S.card =
      (S.filter fun a ↦ z a = 0).card +
      (S.filter fun a ↦ 0 < z a ∧ z a ≤ c).card +
      (S.filter fun a ↦ c < z a).card := by
  classical
  calc
    S.card = ∑ _a ∈ S, (1 : ℕ) := Finset.card_eq_sum_ones S
    _ = ∑ a ∈ S, ((if z a = 0 then (1 : ℕ) else 0) +
          (if 0 < z a ∧ z a ≤ c then (1 : ℕ) else 0) +
          (if c < z a then (1 : ℕ) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hz : z a = 0
      · simp [hz]
      · have hpos : 0 < z a := Nat.pos_of_ne_zero hz
        by_cases hc : z a ≤ c
        · simp [hz, hpos, hc]
        · have hlarge : c < z a := Nat.lt_of_not_ge hc
          simp [hz, hpos, hc, hlarge]
    _ = (S.filter fun a ↦ z a = 0).card +
        (S.filter fun a ↦ 0 < z a ∧ z a ≤ c).card +
        (S.filter fun a ↦ c < z a).card := by
      simp [Finset.sum_add_distrib]

/-- Exact trichotomy of ordered witness pairs by intersection size. -/
theorem witnessCount_sq_eq_overlap_trichotomy (k cutoff : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    witnessCount k Witness n G ^ 2 =
      overlapPairCount k Witness (fun r ↦ r = 0) n G +
      overlapPairCount k Witness (fun r ↦ 0 < r ∧ r ≤ cutoff n) n G +
      overlapPairCount k Witness (fun r ↦ cutoff n < r) n G := by
  classical
  let S := witnessPairs k Witness n G
  let z : (Finset (Fin n) × Finset (Fin n)) → ℕ :=
    fun AB ↦ (AB.1 ∩ AB.2).card
  have hpairs : S.card = witnessCount k Witness n G ^ 2 := by
    simp [S, witnessPairs, witnessCount, pow_two]
  rw [← hpairs]
  simpa [S, z, overlapPairCount] using
    card_eq_filter_zero_add_filter_moderate_add_filter_large S z (cutoff n)

/-- Normalized contribution of one intersection range to the second moment. -/
noncomputable def overlapContribution (k : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (R : ℕ → Prop) (n : ℕ) : ℝ :=
  uniformMean (overlapPairCount k Witness R n)

/-- The second moment is exactly the sum of the disjoint, moderate-overlap,
and large-overlap contributions. -/
theorem uniformSecondMoment_witnessCount_eq_overlap_trichotomy
    (k cutoff : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (n : ℕ) :
    uniformSecondMoment (witnessCount k Witness n) =
      overlapContribution k Witness (fun r ↦ r = 0) n +
      overlapContribution k Witness (fun r ↦ 0 < r ∧ r ≤ cutoff n) n +
      overlapContribution k Witness (fun r ↦ cutoff n < r) n := by
  classical
  unfold uniformSecondMoment overlapContribution uniformMean
  rw [← add_div, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G _
  exact_mod_cast witnessCount_sq_eq_overlap_trichotomy k cutoff Witness n G

/-! ## Asymptotic schema -/

/-- A sequence of properties of labelled graphs holds with high probability
in the finite uniform model. -/
def HoldsWithHighProbability
    (Target : ∀ n, SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n ↦ uniformProbability (Target n)) atTop (𝓝 1)

/-- Finite-index-set form of the second-moment schema.  The candidate type and
finite candidate family may vary with `n`; no subset or overlap structure is
assumed.  Consequently this theorem applies directly to labelled slot choices
such as functions `Fin (k n) → Fin (q n)`.

The relative second-moment estimate is stated without concealment: it is the
analytic/combinatorial input which applications must establish. -/
theorem holdsWithHighProbability_of_indexed_secondMoment
    {I : ℕ → Type*} (Candidates : ∀ n, Finset (I n))
    (Witness : ∀ n, I n → SimpleGraph (Fin n) → Prop)
    (Target : ∀ n, SimpleGraph (Fin n) → Prop)
    (lowerMean relativeError : ℕ → ℝ)
    (hlowerPositive : ∀ᶠ n in atTop, 0 < lowerMean n)
    (hlower : ∀ᶠ n in atTop,
      lowerMean n ≤ uniformMean (indexedWitnessCount Candidates Witness n))
    (hsecond : ∀ᶠ n in atTop,
      uniformSecondMoment (indexedWitnessCount Candidates Witness n) ≤
        (1 + relativeError n) *
          uniformMean (indexedWitnessCount Candidates Witness n) ^ 2)
    (herrorZero : Tendsto relativeError atTop (𝓝 0))
    (hdeterministic : ∀ n G,
      0 < indexedWitnessCount Candidates Witness n G → Target n G) :
    HoldsWithHighProbability Target := by
  have hlowerLimit : Tendsto (fun n ↦ (1 + relativeError n)⁻¹)
      atTop (𝓝 1) := by
    have hden : Tendsto (fun n ↦ 1 + relativeError n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add herrorZero
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcoefPositive : ∀ᶠ n in atTop, 0 < 1 + relativeError n := by
    have hgt : ∀ᶠ n in atTop, (-1 : ℝ) < relativeError n :=
      (tendsto_order.1 herrorZero).1 (-1) (by norm_num)
    exact hgt.mono fun n hn ↦ by linarith
  have hlowerTarget : ∀ᶠ n in atTop,
      (1 + relativeError n)⁻¹ ≤ uniformProbability (Target n) := by
    filter_upwards [hlowerPositive, hlower, hsecond, hcoefPositive] with
      n hlowPos hlow hsecondN hcoef
    let X := indexedWitnessCount Candidates Witness n
    have hmean : 0 < uniformMean X := hlowPos.trans_le hlow
    have hpos : (1 + relativeError n)⁻¹ ≤
        uniformProbability (fun G ↦ 0 < X G) :=
      inv_one_add_le_uniformProbability_pos X hmean hcoef hsecondN
    exact hpos.trans (uniformProbability_mono fun G hG ↦
      hdeterministic n G hG)
  unfold HoldsWithHighProbability
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLimit
    tendsto_const_nhds hlowerTarget
    (Eventually.of_forall fun n ↦ uniformProbability_le_one (Target n))

/-- Generic ABH second-moment schema.

The assumptions are intentionally stated in the form produced by the actual
counting argument: a positive lower bound for the first moment, followed by
separate normalized estimates for disjoint, moderate-overlap, and
large-overlap ordered pairs. -/
theorem holdsWithHighProbability_of_overlap_bounds
    (k cutoff : ℕ → ℕ)
    (Witness : ∀ n, Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (Target : ∀ n, SimpleGraph (Fin n) → Prop)
    (lowerMean moderateError largeError : ℕ → ℝ)
    (hlowerPositive : ∀ᶠ n in atTop, 0 < lowerMean n)
    (hlower : ∀ᶠ n in atTop,
      lowerMean n ≤ uniformMean (witnessCount k Witness n))
    (hdisjoint : ∀ᶠ n in atTop,
      overlapContribution k Witness (fun r ↦ r = 0) n /
          uniformMean (witnessCount k Witness n) ^ 2 ≤ 1)
    (hmoderate : ∀ᶠ n in atTop,
      overlapContribution k Witness
          (fun r ↦ 0 < r ∧ r ≤ cutoff n) n /
          uniformMean (witnessCount k Witness n) ^ 2 ≤ moderateError n)
    (hlarge : ∀ᶠ n in atTop,
      overlapContribution k Witness (fun r ↦ cutoff n < r) n /
          uniformMean (witnessCount k Witness n) ^ 2 ≤ largeError n)
    (hmoderateZero : Tendsto moderateError atTop (𝓝 0))
    (hlargeZero : Tendsto largeError atTop (𝓝 0))
    (hdeterministic : ∀ n G, 0 < witnessCount k Witness n G → Target n G) :
    HoldsWithHighProbability Target := by
  have herrorZero :
      Tendsto (fun n ↦ moderateError n + largeError n) atTop (𝓝 0) := by
    simpa using hmoderateZero.add hlargeZero
  have hlowerLimit :
      Tendsto (fun n ↦ (1 + (moderateError n + largeError n))⁻¹)
        atTop (𝓝 1) := by
    have hden : Tendsto (fun n ↦ 1 + (moderateError n + largeError n))
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add herrorZero
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcoefPositive : ∀ᶠ n in atTop,
      0 < 1 + (moderateError n + largeError n) := by
    have hgt : ∀ᶠ n in atTop,
        (-1 : ℝ) < moderateError n + largeError n :=
      (tendsto_order.1 herrorZero).1 (-1) (by norm_num)
    exact hgt.mono fun n hn ↦ by linarith
  have hlowerTarget : ∀ᶠ n in atTop,
      (1 + (moderateError n + largeError n))⁻¹ ≤
        uniformProbability (Target n) := by
    filter_upwards [hlowerPositive, hlower, hdisjoint, hmoderate, hlarge,
      hcoefPositive] with n hlowPos hlow hd hm hl hc
    let X := witnessCount k Witness n
    let μ := uniformMean X
    have hμ : 0 < μ := hlowPos.trans_le hlow
    have hμSq : 0 < μ ^ 2 := sq_pos_of_pos hμ
    have hd' : overlapContribution k Witness (fun r ↦ r = 0) n ≤ μ ^ 2 := by
      rw [div_le_one hμSq] at hd
      exact hd
    have hm' : overlapContribution k Witness
        (fun r ↦ 0 < r ∧ r ≤ cutoff n) n ≤ moderateError n * μ ^ 2 := by
      exact (div_le_iff₀ hμSq).mp hm
    have hl' : overlapContribution k Witness (fun r ↦ cutoff n < r) n ≤
        largeError n * μ ^ 2 := by
      exact (div_le_iff₀ hμSq).mp hl
    have hsecond : uniformSecondMoment X ≤
        (1 + (moderateError n + largeError n)) * μ ^ 2 := by
      rw [uniformSecondMoment_witnessCount_eq_overlap_trichotomy
        k cutoff Witness n]
      nlinarith
    have hpos : (1 + (moderateError n + largeError n))⁻¹ ≤
        uniformProbability (fun G ↦ 0 < X G) :=
      inv_one_add_le_uniformProbability_pos X hμ hc hsecond
    exact hpos.trans (uniformProbability_mono fun G hG ↦
      hdeterministic n G hG)
  unfold HoldsWithHighProbability
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLimit
    tendsto_const_nhds hlowerTarget
    (Eventually.of_forall fun n ↦ uniformProbability_le_one (Target n))

end ABHSchema
end Erdos807
