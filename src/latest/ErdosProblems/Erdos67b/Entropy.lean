import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite Shannon entropy

This file provides the finite information-theoretic objects needed in the entropy-decrement
part of the logarithmically averaged Elliott argument.  A finite probability vector is Mathlib's
closed standard simplex.  All entropies use natural logarithms.
-/

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory

namespace Erdos67b
namespace FiniteEntropy

noncomputable section

/-- A probability vector on a finite type. -/
abbrev FinProb (α : Type*) [Fintype α] := stdSimplex ℝ α

variable {α β γ δ Ω : Type*}
variable [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype Ω]

/-- Shannon entropy (with natural logarithms) of a finite probability vector. -/
def entropy (p : FinProb α) : ℝ :=
  ∑ a, Real.negMulLog (p a)

/-- The law of a finite random variable. -/
def law (p : FinProb Ω) (X : Ω → α) : FinProb α :=
  stdSimplex.map X p

/-- Entropy of a finite random variable. -/
def rvEntropy (p : FinProb Ω) (X : Ω → α) : ℝ :=
  entropy (law p X)

/-- Joint law of two finite random variables. -/
def jointLaw (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) : FinProb (α × β) :=
  law p fun ω ↦ (X ω, Y ω)

/-- First marginal of a finite joint law. -/
def fstMarginal (p : FinProb (α × β)) : FinProb α :=
  stdSimplex.map Prod.fst p

/-- Second marginal of a finite joint law. -/
def sndMarginal (p : FinProb (α × β)) : FinProb β :=
  stdSimplex.map Prod.snd p

/-- Product of two finite probability vectors. -/
def product (p : FinProb α) (q : FinProb β) : FinProb (α × β) :=
  ⟨fun z ↦ p z.1 * q z.2, by
    constructor
    · intro z
      exact mul_nonneg (stdSimplex.zero_le p z.1) (stdSimplex.zero_le q z.2)
    · rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
      exact stdSimplex.sum_eq_one p⟩

/-- Conditional entropy of the first coordinate given the second. -/
def condEntropy (p : FinProb (α × β)) : ℝ :=
  entropy p - entropy (sndMarginal p)

/-- Mutual information, in its entropy form. -/
def mutualInfo (p : FinProb (α × β)) : ℝ :=
  entropy (fstMarginal p) + entropy (sndMarginal p) - entropy p

/-- Conditional entropy of finite random variables `X` given `Y`. -/
def rvCondEntropy (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  condEntropy (jointLaw p X Y)

/-- Mutual information of two finite random variables. -/
def rvMutualInfo (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  mutualInfo (jointLaw p X Y)

/-- The corrected pointwise KL term.  The correction `-x+y` is convenient for finite
measures and makes nonnegativity pointwise. -/
def correctedKLTerm (x y : ℝ) : ℝ :=
  x * Real.log (x / y) - x + y

/-- KL divergence of a joint law from the product of its marginals, written as a finite sum. -/
def jointProductKL (p : FinProb (α × β)) : ℝ :=
  ∑ z, correctedKLTerm (p z) (fstMarginal p z.1 * sndMarginal p z.2)

/-- Total-variation (`L¹`) distance, without the conventional factor `1/2`. -/
def l1Dist (p q : FinProb α) : ℝ :=
  ∑ a, |p a - q a|

/-- Nonnegative-real coordinates of a finite probability vector. -/
def nnWeight (p : FinProb α) (a : α) : ℝ≥0 :=
  ⟨p a, stdSimplex.zero_le p a⟩

/-- Convert a real finite probability vector to Mathlib's probability mass function. -/
def toPMF (p : FinProb α) : PMF α :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ stdSimplex.zero_le p a),
      stdSimplex.sum_eq_one]
    simp)

/-- KL divergence between two finite probability vectors, using their discrete measures. -/
def klDivergence [MeasurableSpace α] (p q : FinProb α) : ℝ≥0∞ :=
  InformationTheory.klDiv (toPMF p).toMeasure (toPMF q).toMeasure

/-- KL divergence after applying the same finite random variable to both input laws. -/
def processedKLDivergence [MeasurableSpace α] [MeasurableSpace β]
    (p q : FinProb α) (X : α → β) : ℝ≥0∞ :=
  InformationTheory.klDiv ((toPMF p).map X).toMeasure ((toPMF q).map X).toMeasure

theorem klDivergence_nonneg [MeasurableSpace α] (p q : FinProb α) :
    0 ≤ klDivergence p q :=
  bot_le

omit [Fintype β] in
/-- Finite data-processing inequality, obtained directly from Mathlib's measure-theoretic
data-processing theorem. -/
theorem processedKLDivergence_le [MeasurableSpace α] [MeasurableSpace β]
    (p q : FinProb α) (X : α → β) (hX : Measurable X) :
    processedKLDivergence p q X ≤ klDivergence p q := by
  rw [processedKLDivergence, klDivergence,
    ← PMF.toMeasure_map X (toPMF p) hX, ← PMF.toMeasure_map X (toPMF q) hX]
  exact InformationTheory.klDiv_map_le _ _ hX

@[simp]
theorem entropy_apply (p : FinProb α) :
    entropy p = ∑ a, Real.negMulLog (p a) := rfl

theorem prob_nonneg (p : FinProb α) (a : α) : 0 ≤ p a :=
  stdSimplex.zero_le p a

theorem prob_le_one (p : FinProb α) (a : α) : p a ≤ 1 :=
  stdSimplex.le_one p a

@[simp]
theorem fstMarginal_apply (p : FinProb (α × β)) (a : α) :
    fstMarginal p a = ∑ b, p (a, b) := by
  classical
  simp only [fstMarginal, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

@[simp]
theorem sndMarginal_apply (p : FinProb (α × β)) (b : β) :
    sndMarginal p b = ∑ a, p (a, b) := by
  classical
  simp only [sndMarginal, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · simp
  · intro y _ hyb
    simp [hyb]
  · simp

@[simp]
theorem fstMarginal_jointLaw (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    fstMarginal (jointLaw p X Y) = law p X := by
  rw [fstMarginal, jointLaw, law, stdSimplex.map_comp_apply]
  congr 1

@[simp]
theorem sndMarginal_jointLaw (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    sndMarginal (jointLaw p X Y) = law p Y := by
  rw [sndMarginal, jointLaw, law, stdSimplex.map_comp_apply]
  congr 1

@[simp]
theorem fstMarginal_product (p : FinProb α) (q : FinProb β) :
    fstMarginal (product p q) = p := by
  apply stdSimplex.ext
  funext a
  rw [fstMarginal_apply]
  change (∑ b, p a * q b) = p a
  rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]

@[simp]
theorem sndMarginal_product (p : FinProb α) (q : FinProb β) :
    sndMarginal (product p q) = q := by
  apply stdSimplex.ext
  funext b
  rw [sndMarginal_apply]
  change (∑ a, p a * q b) = q b
  rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

theorem joint_le_fstMarginal (p : FinProb (α × β)) (a : α) (b : β) :
    p (a, b) ≤ fstMarginal p a := by
  rw [fstMarginal_apply]
  exact Finset.single_le_sum (fun b _ ↦ prob_nonneg p (a, b)) (Finset.mem_univ b)

theorem joint_le_sndMarginal (p : FinProb (α × β)) (a : α) (b : β) :
    p (a, b) ≤ sndMarginal p b := by
  rw [sndMarginal_apply]
  exact Finset.single_le_sum (fun a _ ↦ prob_nonneg p (a, b)) (Finset.mem_univ a)

/-- Pointwise Gibbs inequality for the corrected KL integrand.  The last hypothesis is the
absolute-continuity condition needed only when `x` is positive. -/
theorem correctedKLTerm_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x → 0 < y) : 0 ≤ correctedKLTerm x y := by
  by_cases hx0 : x = 0
  · subst x
    simpa [correctedKLTerm] using hy
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := hxy hxpos
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy)
  have hmul := mul_le_mul_of_nonneg_left h hy
  field_simp [ne_of_gt hypos] at hmul
  unfold correctedKLTerm
  linarith

theorem jointProductKL_nonneg (p : FinProb (α × β)) :
    0 ≤ jointProductKL p := by
  apply Finset.sum_nonneg
  rintro ⟨a, b⟩ _
  apply correctedKLTerm_nonneg
  · exact prob_nonneg p (a, b)
  · exact mul_nonneg (prob_nonneg (fstMarginal p) a) (prob_nonneg (sndMarginal p) b)
  · intro hp
    exact mul_pos (hp.trans_le (joint_le_fstMarginal p a b))
      (hp.trans_le (joint_le_sndMarginal p a b))

theorem joint_log_ratio_eq (p : FinProb (α × β)) (a : α) (b : β) :
    p (a, b) * Real.log (p (a, b) / (fstMarginal p a * sndMarginal p b)) =
      p (a, b) * Real.log (p (a, b)) -
        p (a, b) * Real.log (fstMarginal p a) -
          p (a, b) * Real.log (sndMarginal p b) := by
  by_cases hp : p (a, b) = 0
  · simp [hp]
  have hpa : fstMarginal p a ≠ 0 :=
    ne_of_gt ((lt_of_le_of_ne (prob_nonneg p (a, b)) (Ne.symm hp)).trans_le
      (joint_le_fstMarginal p a b))
  have hpb : sndMarginal p b ≠ 0 :=
    ne_of_gt ((lt_of_le_of_ne (prob_nonneg p (a, b)) (Ne.symm hp)).trans_le
      (joint_le_sndMarginal p a b))
  rw [Real.log_div hp (mul_ne_zero hpa hpb), Real.log_mul hpa hpb]
  ring

theorem sum_joint_mul_log_fst (p : FinProb (α × β)) :
    (∑ z, p z * Real.log (fstMarginal p z.1)) =
      ∑ a, fstMarginal p a * Real.log (fstMarginal p a) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, p (a, b) * Real.log (fstMarginal p a)) =
    fstMarginal p a * Real.log (fstMarginal p a)
  rw [← Finset.sum_mul, ← fstMarginal_apply]

theorem sum_joint_mul_log_snd (p : FinProb (α × β)) :
    (∑ z, p z * Real.log (sndMarginal p z.2)) =
      ∑ b, sndMarginal p b * Real.log (sndMarginal p b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ a, p (a, b) * Real.log (sndMarginal p b)) =
    sndMarginal p b * Real.log (sndMarginal p b)
  rw [← Finset.sum_mul, ← sndMarginal_apply]

theorem sum_marginal_product (p : FinProb (α × β)) :
    (∑ z : α × β, fstMarginal p z.1 * sndMarginal p z.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
  exact stdSimplex.sum_eq_one (fstMarginal p)

theorem sum_neg_eq_neg_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, -f i) = -(∑ i, f i) := by
  exact Finset.sum_neg_distrib f

theorem joint_log_ratio_eq' (p : FinProb (α × β)) (z : α × β) :
    p z * Real.log (p z / (fstMarginal p z.1 * sndMarginal p z.2)) =
      p z * Real.log (p z) - p z * Real.log (fstMarginal p z.1) -
        p z * Real.log (sndMarginal p z.2) := by
  simpa only using joint_log_ratio_eq p z.1 z.2

/-- The entropy formula for mutual information is exactly the finite KL divergence from the
joint law to the product of its marginals. -/
theorem mutualInfo_eq_jointProductKL (p : FinProb (α × β)) :
    mutualInfo p = jointProductKL p := by
  rw [jointProductKL]
  simp_rw [correctedKLTerm, joint_log_ratio_eq']
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_joint_mul_log_fst, sum_joint_mul_log_snd, stdSimplex.sum_eq_one,
    sum_marginal_product]
  simp only [mutualInfo, entropy, Real.negMulLog]
  simp_rw [neg_mul]
  rw [sum_neg_eq_neg_sum, sum_neg_eq_neg_sum, sum_neg_eq_neg_sum]
  ring

theorem mutualInfo_nonneg (p : FinProb (α × β)) :
    0 ≤ mutualInfo p := by
  rw [mutualInfo_eq_jointProductKL]
  exact jointProductKL_nonneg p

theorem entropy_le_add_marginals (p : FinProb (α × β)) :
    entropy p ≤ entropy (fstMarginal p) + entropy (sndMarginal p) := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

theorem entropy_nonneg (p : FinProb α) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (prob_nonneg p a) (prob_le_one p a)

theorem entropy_product (p : FinProb α) (q : FinProb β) :
    entropy (product p q) = entropy p + entropy q := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, Real.negMulLog (p a * q b)) = _
  simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, stdSimplex.sum_eq_one, one_mul]
  rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

@[simp]
theorem condEntropy_product (p : FinProb α) (q : FinProb β) :
    condEntropy (product p q) = entropy p := by
  rw [condEntropy, entropy_product, sndMarginal_product]
  ring

@[simp]
theorem mutualInfo_product (p : FinProb α) (q : FinProb β) :
    mutualInfo (product p q) = 0 := by
  rw [mutualInfo, fstMarginal_product, sndMarginal_product, entropy_product]
  ring

theorem entropy_le_card_sub_one (p : FinProb α) :
    entropy p ≤ (Fintype.card α : ℝ) - 1 := by
  calc
    entropy p ≤ ∑ a, (1 - p a) := by
      apply Finset.sum_le_sum
      intro a _
      exact Real.negMulLog_le_one_sub_self (prob_nonneg p a)
    _ = (Fintype.card α : ℝ) - 1 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, stdSimplex.sum_eq_one]
      simp

/-- `-x log x` is subadditive on nonnegative reals. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hy0 : y = 0
  · subst y
    simp
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hsumpos : 0 < x + y := add_pos hxpos hypos
  have hlogx : Real.log x ≤ Real.log (x + y) :=
    Real.strictMonoOn_log.monotoneOn hxpos hsumpos (le_add_of_nonneg_right hy)
  have hlogy : Real.log y ≤ Real.log (x + y) :=
    Real.strictMonoOn_log.monotoneOn hypos hsumpos (le_add_of_nonneg_left hx)
  have hxterm : 0 ≤ x * (Real.log (x + y) - Real.log x) :=
    mul_nonneg hx (sub_nonneg.mpr hlogx)
  have hyterm : 0 ≤ y * (Real.log (x + y) - Real.log y) :=
    mul_nonneg hy (sub_nonneg.mpr hlogy)
  rw [Real.negMulLog, Real.negMulLog, Real.negMulLog]
  nlinarith

/-- Finite form of subadditivity of `-x log x`. -/
theorem negMulLog_sum_le_sum {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.negMulLog (∑ i ∈ s, w i) ≤ ∑ i ∈ s, Real.negMulLog (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (negMulLog_add_le (hw a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg fun i hi ↦ hw i (Finset.mem_insert_of_mem hi))).trans
        (add_le_add_right (ih fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) _)

/-- Coarse graining a finite law cannot increase Shannon entropy. -/
theorem entropy_map_le (f : α → β) (p : FinProb α) :
    entropy (stdSimplex.map f p) ≤ entropy p := by
  classical
  simp only [entropy, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  calc
    ∑ y, Real.negMulLog (∑ x ∈ Finset.univ with f x = y, p x) ≤
        ∑ y, ∑ x ∈ Finset.univ with f x = y, Real.negMulLog (p x) := by
      apply Finset.sum_le_sum
      intro y _
      apply negMulLog_sum_le_sum
      intro x hx
      exact prob_nonneg p x
    _ = ∑ x, Real.negMulLog (p x) := by
      simpa only [Finset.sum_filter] using
        (Finset.sum_fiberwise Finset.univ f fun x ↦ Real.negMulLog (p x))

theorem entropy_law_le (p : FinProb Ω) (X : Ω → α) :
    entropy (law p X) ≤ entropy p :=
  entropy_map_le X p

/-- Deterministic data processing for the entropy of a finite random variable. -/
theorem rvEntropy_comp_le (p : FinProb Ω) (X : Ω → α) (g : α → β) :
    rvEntropy p (g ∘ X) ≤ rvEntropy p X := by
  rw [rvEntropy, rvEntropy, law, law, ← stdSimplex.map_comp_apply]
  exact entropy_map_le g (stdSimplex.map X p)

theorem condEntropy_nonneg (p : FinProb (α × β)) :
    0 ≤ condEntropy p := by
  exact sub_nonneg.mpr (entropy_map_le Prod.snd p)

/-- Chain rule for a pair, with conditional entropy defined from the joint law. -/
theorem entropy_chain_rule (p : FinProb (α × β)) :
    entropy p = entropy (sndMarginal p) + condEntropy p := by
  simp [condEntropy]

/-- Chain rule for two finite random variables. -/
theorem rvEntropy_chain_rule (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvEntropy p (fun ω ↦ (X ω, Y ω)) = rvEntropy p Y + rvCondEntropy p X Y := by
  change entropy (jointLaw p X Y) = entropy (law p Y) + condEntropy (jointLaw p X Y)
  rw [← sndMarginal_jointLaw p X Y]
  exact entropy_chain_rule (jointLaw p X Y)

theorem mutualInfo_eq_entropy_fst_sub_condEntropy (p : FinProb (α × β)) :
    mutualInfo p = entropy (fstMarginal p) - condEntropy p := by
  simp [mutualInfo, condEntropy]
  ring

theorem mutualInfo_le_entropy_fst (p : FinProb (α × β)) :
    mutualInfo p ≤ entropy (fstMarginal p) := by
  rw [mutualInfo_eq_entropy_fst_sub_condEntropy]
  exact sub_le_self _ (condEntropy_nonneg p)

theorem condEntropy_le_entropy_fst (p : FinProb (α × β)) :
    condEntropy p ≤ entropy (fstMarginal p) := by
  rw [← sub_nonneg]
  simpa [mutualInfo_eq_entropy_fst_sub_condEntropy] using mutualInfo_nonneg p

theorem mutualInfo_le_entropy_snd (p : FinProb (α × β)) :
    mutualInfo p ≤ entropy (sndMarginal p) := by
  have h : 0 ≤ entropy p - entropy (fstMarginal p) :=
    sub_nonneg.mpr (entropy_map_le Prod.fst p)
  unfold mutualInfo
  linarith

theorem mutualInfo_le_min_entropy (p : FinProb (α × β)) :
    mutualInfo p ≤ min (entropy (fstMarginal p)) (entropy (sndMarginal p)) := by
  exact le_min (mutualInfo_le_entropy_fst p) (mutualInfo_le_entropy_snd p)

theorem rvMutualInfo_nonneg (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ rvMutualInfo p X Y :=
  mutualInfo_nonneg (jointLaw p X Y)

theorem rvMutualInfo_le_entropy_left (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvMutualInfo p X Y ≤ rvEntropy p X := by
  simpa [rvMutualInfo, rvEntropy] using
    mutualInfo_le_entropy_fst (jointLaw p X Y)

theorem rvMutualInfo_le_entropy_right (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvMutualInfo p X Y ≤ rvEntropy p Y := by
  simpa [rvMutualInfo, rvEntropy] using
    mutualInfo_le_entropy_snd (jointLaw p X Y)

theorem l1Dist_nonneg (p q : FinProb α) : 0 ≤ l1Dist p q := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp]
theorem l1Dist_self (p : FinProb α) : l1Dist p p = 0 := by
  simp [l1Dist]

theorem l1Dist_symm (p q : FinProb α) : l1Dist p q = l1Dist q p := by
  apply Finset.sum_congr rfl
  intro a _
  rw [abs_sub_comm]

/-- A coordinatewise continuity bound.  This is the finite sum form from which explicit
Fannes estimates are obtained once a scalar modulus for `negMulLog` is chosen. -/
theorem entropy_sub_abs_le_sum_abs (p q : FinProb α) :
    |entropy p - entropy q| ≤
      ∑ a, |Real.negMulLog (p a) - Real.negMulLog (q a)| := by
  simpa only [entropy, ← Finset.sum_sub_distrib] using
    (Finset.abs_sum_le_sum_abs
      (fun a : α ↦ Real.negMulLog (p a) - Real.negMulLog (q a)) Finset.univ)

/-- Entropy is continuous on the finite probability simplex. -/
theorem continuous_entropy : Continuous (entropy : FinProb α → ℝ) := by
  unfold entropy
  apply continuous_finsetSum
  intro a _
  exact Real.continuous_negMulLog.comp ((continuous_apply a).comp continuous_subtype_val)

theorem continuous_condEntropy :
    Continuous (condEntropy : FinProb (α × β) → ℝ) := by
  unfold condEntropy sndMarginal
  exact continuous_entropy.sub
    (continuous_entropy.comp (stdSimplex.continuous_map Prod.snd))

theorem continuous_mutualInfo :
    Continuous (mutualInfo : FinProb (α × β) → ℝ) := by
  unfold mutualInfo fstMarginal sndMarginal
  exact (continuous_entropy.comp (stdSimplex.continuous_map Prod.fst)).add
    (continuous_entropy.comp (stdSimplex.continuous_map Prod.snd)) |>.sub continuous_entropy

/-- Uniform finite Fannes-style continuity: on a fixed finite alphabet, sufficiently small
`L¹` distance forces an arbitrarily small entropy difference. -/
theorem exists_delta_entropy_sub_abs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : FinProb α,
      l1Dist p q < δ → |entropy p - entropy q| < ε := by
  have hu : UniformContinuous (entropy : FinProb α → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous continuous_entropy
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.1 hu) ε hε
  refine ⟨δ, hδ, fun p q hpq ↦ hmod ?_⟩
  have hdist : dist p q ≤ l1Dist p q := by
    change dist (p : α → ℝ) (q : α → ℝ) ≤ l1Dist p q
    rw [dist_pi_le_iff (l1Dist_nonneg p q)]
    intro a
    rw [Real.dist_eq]
    exact Finset.single_le_sum
      (fun b (_ : b ∈ (Finset.univ : Finset α)) ↦ abs_nonneg (p b - q b))
      (Finset.mem_univ a)
  exact hdist.trans_lt hpq

/-- Uniform finite continuity estimate for mutual information on fixed alphabets. -/
theorem exists_delta_mutualInfo_sub_abs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : FinProb (α × β),
      l1Dist p q < δ → |mutualInfo p - mutualInfo q| < ε := by
  have hu : UniformContinuous (mutualInfo : FinProb (α × β) → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous continuous_mutualInfo
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.1 hu) ε hε
  refine ⟨δ, hδ, fun p q hpq ↦ hmod ?_⟩
  have hdist : dist p q ≤ l1Dist p q := by
    change dist (p : (α × β) → ℝ) (q : (α × β) → ℝ) ≤ l1Dist p q
    rw [dist_pi_le_iff (l1Dist_nonneg p q)]
    intro z
    rw [Real.dist_eq]
    exact Finset.single_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (α × β))) ↦ abs_nonneg (p w - q w))
      (Finset.mem_univ z)
  exact hdist.trans_lt hpq

end

end FiniteEntropy
end Erdos67b
