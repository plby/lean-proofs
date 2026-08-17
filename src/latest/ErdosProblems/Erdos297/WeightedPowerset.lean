/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 297: weighted finite powersets

This file records the finite algebra used by both the exponential-moment
upper bound and the tilted Bernoulli measure in the lower bound.  The basic
identity is the expansion

`∏ i ∈ X, (a i + b i)`

as a sum over all subsets of `X`.  We then specialize it to inhomogeneous
Bernoulli weights, identify their logarithms, and give the elementary step
which turns a lower bound for the mass of a family and an upper bound for the
mass of every atom into a lower bound for the family's cardinality.
-/

open Finset
open scoped BigOperators

namespace Erdos297

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The two-weight powerset identity -/

/-- The weight of a subset obtained by using `a i` on the subset and `b i`
on its complement inside `X`. -/
def subsetWeight {R : Type*} [CommMonoid R] {ι : Type*}
    (X : Finset ι) (a b : ι → R) (S : Finset ι) : R :=
  (∏ i ∈ S, a i) * ∏ i ∈ X \ S, b i

/-- Expansion of a product of sums as a sum over the powerset. -/
theorem sum_subsetWeight {R : Type*} [CommSemiring R] {ι : Type*}
    (X : Finset ι) (a b : ι → R) :
    (∑ S ∈ X.powerset, subsetWeight X a b S) =
      ∏ i ∈ X, (a i + b i) := by
  simpa only [subsetWeight] using (Finset.prod_add a b X).symm

/-- Real-valued form of `sum_subsetWeight`. -/
theorem sum_subsetWeight_real {ι : Type*} (X : Finset ι) (a b : ι → ℝ) :
    (∑ S ∈ X.powerset, subsetWeight X a b S) =
      ∏ i ∈ X, (a i + b i) :=
  sum_subsetWeight X a b

/-- Complex-valued form of `sum_subsetWeight`, used after inserting additive
characters in the Fourier argument. -/
theorem sum_subsetWeight_complex {ι : Type*} (X : Finset ι) (a b : ι → ℂ) :
    (∑ S ∈ X.powerset, subsetWeight X a b S) =
      ∏ i ∈ X, (a i + b i) :=
  sum_subsetWeight X a b

/-! ## Inhomogeneous Bernoulli weights -/

/-- Product Bernoulli mass of `S`, regarded as a subset of `X`, with an
individual inclusion probability `p i` at each coordinate. -/
def bernoulliWeight {ι : Type*} (X : Finset ι) (p : ι → ℝ)
    (S : Finset ι) : ℝ :=
  subsetWeight X p (fun i ↦ 1 - p i) S

/-- The inhomogeneous Bernoulli masses sum to one.  The identity is algebraic
and therefore requires no bounds on the values of `p`. -/
theorem sum_bernoulliWeight_eq_one {ι : Type*} (X : Finset ι) (p : ι → ℝ) :
    (∑ S ∈ X.powerset, bernoulliWeight X p S) = 1 := by
  change (∑ S ∈ X.powerset, subsetWeight X p (fun i ↦ 1 - p i) S) = 1
  rw [sum_subsetWeight]
  simp

/-- A Bernoulli atom is nonnegative when all probabilities on the ambient
set lie in `[0,1]`. -/
theorem bernoulliWeight_nonneg {ι : Type*} {X S : Finset ι} {p : ι → ℝ}
    (hSX : S ⊆ X) (hp0 : ∀ i ∈ X, 0 ≤ p i)
    (hp1 : ∀ i ∈ X, p i ≤ 1) :
    0 ≤ bernoulliWeight X p S := by
  rw [bernoulliWeight, subsetWeight]
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi ↦ hp0 i (hSX hi)
  · exact Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp1 i (Finset.mem_sdiff.mp hi).1)

/-- A Bernoulli atom is positive when all probabilities on the ambient set
lie strictly between zero and one. -/
theorem bernoulliWeight_pos {ι : Type*} {X S : Finset ι} {p : ι → ℝ}
    (hSX : S ⊆ X) (hp0 : ∀ i ∈ X, 0 < p i)
    (hp1 : ∀ i ∈ X, p i < 1) :
    0 < bernoulliWeight X p S := by
  rw [bernoulliWeight, subsetWeight]
  apply mul_pos
  · exact Finset.prod_pos fun i hi ↦ hp0 i (hSX hi)
  · exact Finset.prod_pos fun i hi ↦ sub_pos.mpr (hp1 i (Finset.mem_sdiff.mp hi).1)

/-- Log-likelihood of a Bernoulli atom. -/
def bernoulliLogLikelihood {ι : Type*} (X : Finset ι) (p : ι → ℝ)
    (S : Finset ι) : ℝ :=
  (∑ i ∈ S, Real.log (p i)) +
    ∑ i ∈ X \ S, Real.log (1 - p i)

/-- A positive Bernoulli atom is the exponential of its log-likelihood. -/
theorem bernoulliWeight_eq_exp_logLikelihood {ι : Type*}
    {X S : Finset ι} {p : ι → ℝ}
    (hSX : S ⊆ X) (hp0 : ∀ i ∈ X, 0 < p i)
    (hp1 : ∀ i ∈ X, p i < 1) :
    bernoulliWeight X p S = Real.exp (bernoulliLogLikelihood X p S) := by
  rw [bernoulliWeight, subsetWeight, bernoulliLogLikelihood, Real.exp_add,
    Real.exp_sum, Real.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact (Real.exp_log (hp0 i (hSX hi))).symm
  · apply Finset.prod_congr rfl
    intro i hi
    exact (Real.exp_log (sub_pos.mpr (hp1 i (Finset.mem_sdiff.mp hi).1))).symm

/-- Taking logarithms recovers the finite log-likelihood exactly. -/
theorem log_bernoulliWeight {ι : Type*} {X S : Finset ι} {p : ι → ℝ}
    (hSX : S ⊆ X) (hp0 : ∀ i ∈ X, 0 < p i)
    (hp1 : ∀ i ∈ X, p i < 1) :
    Real.log (bernoulliWeight X p S) = bernoulliLogLikelihood X p S := by
  rw [bernoulliWeight_eq_exp_logLikelihood hSX hp0 hp1, Real.log_exp]

/-- The negative log-mass is the sum of the coordinatewise negative
log-likelihoods. -/
theorem neg_log_bernoulliWeight {ι : Type*} {X S : Finset ι} {p : ι → ℝ}
    (hSX : S ⊆ X) (hp0 : ∀ i ∈ X, 0 < p i)
    (hp1 : ∀ i ∈ X, p i < 1) :
    -Real.log (bernoulliWeight X p S) =
      (∑ i ∈ S, -Real.log (p i)) +
        ∑ i ∈ X \ S, -Real.log (1 - p i) := by
  rw [log_bernoulliWeight hSX hp0 hp1, bernoulliLogLikelihood]
  simp only [Finset.sum_neg_distrib]
  ring

/-! ## Logistic tilting -/

/-- The logistic inclusion probability with energy `t`. -/
def tiltedProbability (t : ℝ) : ℝ :=
  Real.exp (-t) / (1 + Real.exp (-t))

theorem tiltedProbability_pos (t : ℝ) : 0 < tiltedProbability t := by
  rw [tiltedProbability]
  positivity

theorem tiltedProbability_lt_one (t : ℝ) : tiltedProbability t < 1 := by
  rw [tiltedProbability, div_lt_one]
  · linarith [Real.exp_pos (-t)]
  · positivity

/-- The exclusion probability for a logistic tilt has the same partition
function denominator. -/
theorem one_sub_tiltedProbability (t : ℝ) :
    1 - tiltedProbability t = 1 / (1 + Real.exp (-t)) := by
  rw [tiltedProbability]
  field_simp
  ring

theorem log_tiltedProbability (t : ℝ) :
    Real.log (tiltedProbability t) =
      -t - Real.log (1 + Real.exp (-t)) := by
  rw [tiltedProbability,
    Real.log_div (Real.exp_ne_zero _) (by positivity : 1 + Real.exp (-t) ≠ 0),
    Real.log_exp]

theorem log_one_sub_tiltedProbability (t : ℝ) :
    Real.log (1 - tiltedProbability t) =
      -Real.log (1 + Real.exp (-t)) := by
  rw [one_sub_tiltedProbability,
    Real.log_div one_ne_zero (by positivity : 1 + Real.exp (-t) ≠ 0)]
  simp

/-- Under logistic tilting the log-mass is the selected energy with a minus
sign, minus the log partition function over the whole ambient set. -/
theorem log_bernoulliWeight_tilted {ι : Type*} {X S : Finset ι}
    (t : ι → ℝ) (hSX : S ⊆ X) :
    Real.log (bernoulliWeight X (fun i ↦ tiltedProbability (t i)) S) =
      -(∑ i ∈ S, t i) -
        ∑ i ∈ X, Real.log (1 + Real.exp (-t i)) := by
  rw [log_bernoulliWeight hSX
      (fun i _ ↦ tiltedProbability_pos (t i))
      (fun i _ ↦ tiltedProbability_lt_one (t i)),
    bernoulliLogLikelihood]
  simp_rw [log_tiltedProbability, log_one_sub_tiltedProbability,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hpartition := Finset.sum_sdiff
    (f := fun i ↦ Real.log (1 + Real.exp (-t i))) hSX
  linarith

/-! ## Extracting cardinality from atom bounds -/

/-- If every atom in a finite family has weight at most `M`, its total weight
is at most `card * M`.  No sign assumptions are needed. -/
theorem sum_le_card_mul_of_atom_le {ι : Type*}
    (F : Finset (Finset ι)) (w : Finset ι → ℝ) (M : ℝ)
    (hatom : ∀ S ∈ F, w S ≤ M) :
    (∑ S ∈ F, w S) ≤ (F.card : ℝ) * M := by
  calc
    (∑ S ∈ F, w S) ≤ ∑ _S ∈ F, M := Finset.sum_le_sum hatom
    _ = (F.card : ℝ) * M := by simp

/-- A lower mass bound and a per-atom upper bound give the corresponding
cardinality inequality without division. -/
theorem mass_le_card_mul_of_atom_le {ι : Type*}
    (F : Finset (Finset ι)) (w : Finset ι → ℝ) (q M : ℝ)
    (hmass : q ≤ ∑ S ∈ F, w S)
    (hatom : ∀ S ∈ F, w S ≤ M) :
    q ≤ (F.card : ℝ) * M :=
  hmass.trans (sum_le_card_mul_of_atom_le F w M hatom)

/-- Division form of the elementary cardinality extraction step. -/
theorem div_atomBound_le_card {ι : Type*}
    (F : Finset (Finset ι)) (w : Finset ι → ℝ) (q M : ℝ)
    (hM : 0 < M) (hmass : q ≤ ∑ S ∈ F, w S)
    (hatom : ∀ S ∈ F, w S ≤ M) :
    q / M ≤ (F.card : ℝ) := by
  rw [div_le_iff₀ hM]
  simpa [mul_comm] using mass_le_card_mul_of_atom_le F w q M hmass hatom

/-- Exponential form used in the lower-bound argument: if every atom has
mass at most `exp (-L)`, then a family of mass at least `q` has cardinality at
least `q * exp L`. -/
theorem mass_mul_exp_le_card_of_atom_le_exp_neg {ι : Type*}
    (F : Finset (Finset ι)) (w : Finset ι → ℝ) (q L : ℝ)
    (hmass : q ≤ ∑ S ∈ F, w S)
    (hatom : ∀ S ∈ F, w S ≤ Real.exp (-L)) :
    q * Real.exp L ≤ (F.card : ℝ) := by
  simpa [Real.exp_neg, div_inv_eq_mul] using
    div_atomBound_le_card F w q (Real.exp (-L)) (Real.exp_pos _)
      hmass hatom

end

end Erdos297

#print axioms Erdos297.sum_subsetWeight
#print axioms Erdos297.sum_bernoulliWeight_eq_one
#print axioms Erdos297.log_bernoulliWeight_tilted
#print axioms Erdos297.mass_mul_exp_le_card_of_atom_le_exp_neg
