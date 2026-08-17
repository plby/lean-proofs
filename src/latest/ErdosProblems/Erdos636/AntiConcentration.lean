/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos636.PairEmbeddingAdapter
import ErdosProblems.Erdos636.External.Erdos88.Esseen
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Balanced fixed-slice anti-concentration

This file packages the analytic input used in the proof of Erdős problem 636.
A bounded integer coefficient population with linear centered variance first
produces linearly many disjoint unequal pairs, by `Pairing`.  The adapter in
`PairEmbeddingAdapter` turns that matching into the pair embedding expected by
the fixed-slice Fourier estimate.  Esseen's inequality then gives an explicit
point-mass bound of order `1 / sqrt |I|`.

The file deliberately does not import `ErdosProblems.Erdos636`: the main
problem file may therefore import this package without an import cycle.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace Erdos636.AntiConcentration

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos88.Fourier

universe u v

/-- Push-forward to `ℝ` of uniform counting measure on a nonempty finite
sample space. -/
noncomputable def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : Measure ℝ :=
  ((PMF.uniformOfFintype Ω).map X).toMeasure

noncomputable instance uniformLaw.instIsProbabilityMeasure
    (Ω : Type*) [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    IsProbabilityMeasure (uniformLaw Ω X) := by
  unfold uniformLaw
  infer_instance

lemma charFun_uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) :
    charFun (uniformLaw Ω X) t = finCharFun Ω X t := by
  letI : MeasurableSpace Ω := ⊤
  letI : MeasurableSingletonClass Ω := ⟨fun _ ↦ MeasurableSet.of_discrete⟩
  rw [uniformLaw, ← PMF.toMeasure_map (p := PMF.uniformOfFintype Ω) (f := X)
    (measurable_of_finite X), charFun_apply_real, integral_map]
  · rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      finCharFun, finExpectation]
    simp only [smul_eq_mul, div_eq_mul_inv]
    rw [mul_comm (∑ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Complex.real_smul, mul_comm]
    push_cast
    ring
  · fun_prop
  · fun_prop

lemma uniformLaw_real_apply (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (uniformLaw Ω X).real s =
      ((Finset.univ.filter fun ω ↦ X ω ∈ s).card : ℝ) / Fintype.card Ω := by
  letI : MeasurableSpace Ω := ⊤
  letI : MeasurableSingletonClass Ω := ⟨fun _ ↦ MeasurableSet.of_discrete⟩
  rw [uniformLaw, ← PMF.toMeasure_map (p := PMF.uniformOfFintype Ω) (f := X)
    (measurable_of_finite X), Measure.real, Measure.map_apply
      (measurable_of_finite X) hs]
  rw [PMF.toMeasure_uniformOfFintype_apply (s := X ⁻¹' s)
    (measurableSet_preimage (measurable_of_finite X) hs)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 1
  exact_mod_cast Fintype.card_subtype (fun ω : Ω ↦ X ω ∈ s)

/-- Every point event is contained in a positive-radius small ball under the
uniform push-forward law. -/
lemma finProbability_eq_le_smallBall (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    finProbability Ω (fun ω ↦ X ω = x) ≤
      Erdos88.Esseen.smallBall (uniformLaw Ω X) eps x := by
  rw [finProbability, Erdos88.Esseen.smallBall,
    uniformLaw_real_apply Ω X _ measurableSet_Icc]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      constructor <;> rw [hω] <;> linarith)
  · positivity

/-- The real linear statistic on a Boolean slice. -/
noncomputable def sliceLinear {I : Type*} [Fintype I] [DecidableEq I]
    (s : ℕ) (a : I → ℝ) (x : BoolSlice I s) : ℝ :=
  ∑ i, a i * if x.1 i then 1 else 0

lemma charFun_uniformLaw_sliceLinear {I : Type*} [Fintype I] [DecidableEq I]
    (s : ℕ) [Nonempty (BoolSlice I s)] (a : I → ℝ) (t : ℝ) :
    charFun (uniformLaw (BoolSlice I s) (sliceLinear s a)) t =
      sliceCharFun s a t := by
  exact charFun_uniformLaw _ _ _

/-- Restricting a nonnegative Gaussian to a symmetric finite interval can
only decrease its integral. -/
lemma intervalIntegral_exp_neg_mul_sq_le {b L : ℝ} (hb : 0 < b)
    (hL : 0 ≤ L) :
    (∫ t : ℝ in -L..L, Real.exp (-b * t ^ 2)) ≤ Real.sqrt (Real.pi / b) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc
    (∫ t : ℝ in Set.Ioc (-L) L, Real.exp (-b * t ^ 2)) ≤
        ∫ t : ℝ, Real.exp (-b * t ^ 2) :=
      MeasureTheory.setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
        (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / b) := integral_gaussian b

/-- Bounded gaps on disjoint pairs force Gaussian decay of the slice
characteristic function on a low-frequency interval. -/
lemma norm_sliceCharFun_le_gaussian_of_pairs
    {K : Type v} {I : Type u} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (c B t : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hdiffLower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hdiffUpper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (ht : |t| ≤ 1 / (4 * B)) :
    ‖sliceCharFun s a t‖ ≤
      Real.exp 1 * Real.exp (-(c ^ 3 / 256) * Fintype.card K *
        (|t| / (2 * Real.pi)) ^ 2) := by
  let delta : ℝ := |t| / (2 * Real.pi)
  let q : K → ℝ := fun k ↦
    t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfourB : 0 < 4 * B := mul_pos (by norm_num) hB0
  have hquarter : 1 / (4 * B) ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have htquarter : |t| ≤ (1 / 4 : ℝ) := ht.trans hquarter
  apply norm_sliceCharFun_le_balanced p s a t delta c q
  · exact hc0
  · exact hc1
  · exact hsel
  · exact hunsel
  · exact div_nonneg (abs_nonneg t) htwoPi.le
  · apply (div_le_iff₀ htwoPi).2
    nlinarith [Real.pi_gt_three]
  · intro k
    refine ⟨?_, 0, ?_⟩
    · dsimp only [q]
      rw [abs_div, abs_mul, abs_of_pos htwoPi]
      apply (div_le_iff₀ htwoPi).2
      have hmul :
          |t| * |a (p (k, false)) - a (p (k, true))| ≤
            (1 / (4 * B)) * B :=
        mul_le_mul ht (hdiffUpper k) (abs_nonneg _) (by positivity)
      have hmul' :
          |t| * |a (p (k, false)) - a (p (k, true))| ≤ 1 / 4 := by
        convert hmul using 1 <;> field_simp [ne_of_gt hB0]
      nlinarith [Real.pi_gt_three]
    · dsimp only [q]
      push_cast
      ring
  · intro k
    dsimp only [delta, q]
    rw [abs_div, abs_mul, abs_of_pos htwoPi]
    apply div_le_div_of_nonneg_right _ htwoPi.le
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hdiffLower k) (abs_nonneg t)

/-- Esseen's inequality turns the Gaussian characteristic-function estimate
into an explicit fixed-slice point-mass bound. -/
lemma slice_point_probability_le_of_pairs
    {K : Type v} {I : Type u} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (c B : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hdiffLower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hdiffUpper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (hK : 0 < Fintype.card K) (x : ℝ) :
    finProbability (BoolSlice I s) (fun ω ↦ sliceLinear s a ω = x) ≤
      16 * B * Real.exp 1 *
        Real.sqrt (Real.pi /
          ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2))) := by
  let rate : ℝ := (c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have heps : 0 < 8 * B := mul_pos (by norm_num) hB0
  have hrate : 0 < rate := by
    dsimp only [rate]
    positivity
  have hcharIntegral :
      (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          ‖charFun (uniformLaw (BoolSlice I s) (sliceLinear s a)) t‖) ≤
        ∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp 1 * Real.exp (-rate * t ^ 2) := by
    apply intervalIntegral.integral_mono_on
      (neg_le_self (by positivity))
      ((continuous_norm.comp continuous_charFun).intervalIntegrable _ _)
      ((continuous_const.mul
        (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)
    intro t htIcc
    have ht' : |t| ≤ 1 / (4 * B) := by
      calc
        |t| ≤ 2 / (8 * B) := (abs_le).2 htIcc
        _ = 1 / (4 * B) := by field_simp [ne_of_gt hB0] <;> ring
    change ‖charFun (uniformLaw (BoolSlice I s) (sliceLinear s a)) t‖ ≤
        Real.exp 1 * Real.exp (-rate * t ^ 2)
    rw [charFun_uniformLaw_sliceLinear]
    calc
      ‖sliceCharFun s a t‖ ≤
          Real.exp 1 * Real.exp (-(c ^ 3 / 256) * Fintype.card K *
            (|t| / (2 * Real.pi)) ^ 2) :=
        norm_sliceCharFun_le_gaussian_of_pairs p s a c B t hc0 hc1
          hsel hunsel hB hdiffLower hdiffUpper ht'
      _ = Real.exp 1 * Real.exp (-rate * t ^ 2) := by
        congr 2
        dsimp only [rate]
        rw [div_pow, sq_abs]
        ring
  calc
    finProbability (BoolSlice I s) (fun ω ↦ sliceLinear s a ω = x) ≤
        Erdos88.Esseen.smallBall
          (uniformLaw (BoolSlice I s) (sliceLinear s a)) (8 * B) x :=
      finProbability_eq_le_smallBall _ _ _ heps x
    _ ≤ 2 * (8 * B) *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          ‖charFun (uniformLaw (BoolSlice I s) (sliceLinear s a)) t‖) :=
      Erdos88.Esseen.esseen_4_7 _ heps x
    _ ≤ 2 * (8 * B) *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp 1 * Real.exp (-rate * t ^ 2)) :=
      mul_le_mul_of_nonneg_left hcharIntegral (by positivity)
    _ = 16 * B * Real.exp 1 *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp (-rate * t ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ 16 * B * Real.exp 1 * Real.sqrt (Real.pi / rate) := by
      apply mul_le_mul_of_nonneg_left
        (intervalIntegral_exp_neg_mul_sq_le hrate (by positivity))
      positivity
    _ = 16 * B * Real.exp 1 *
        Real.sqrt (Real.pi /
          ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2))) := rfl

/-! ## Integer-population wrapper -/

/-- The explicit constant in the variance form of the fixed-slice
anti-concentration estimate.  Its parameters are respectively the slice
balance, the variance density, and the integer coefficient bound. -/
noncomputable def variancePointMassConstant (c eta : ℝ) (B : ℕ) : ℝ :=
  32 * (B : ℝ) * Real.exp 1 *
    Real.sqrt
      ((8 * Real.pi * (B : ℝ) ^ 2) /
        (eta * ((c ^ 3 / 256) / (4 * Real.pi ^ 2))))

lemma variancePointMassConstant_pos {c eta : ℝ} {B : ℕ}
    (hc : 0 < c) (heta : 0 < eta) (hB : 0 < B) :
    0 < variancePointMassConstant c eta B := by
  simp only [variancePointMassConstant]
  positivity

/-- Large `ℓ¹` mass and a small total sum force large variance about the
population mean.  This is the deterministic nondegeneracy step used before
the integer matching argument. -/
lemma centered_variance_ge_of_l1_of_small_sum
    {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (mu theta : ℝ)
    (htheta : 0 ≤ theta) (hI : 0 < Fintype.card I)
    (hmean : (Fintype.card I : ℝ) * mu = ∑ i, a i)
    (hl1 : theta * Fintype.card I ≤ ∑ i, |a i|)
    (hsmall : |∑ i, a i| < theta / 2 * Fintype.card I) :
    theta ^ 2 / 4 * Fintype.card I ≤
      ∑ i, (a i - mu) ^ 2 := by
  classical
  have hcardPos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hI
  have hmeanAbs : (Fintype.card I : ℝ) * |mu| = |∑ i, a i| := by
    have hcardAbs : |(Fintype.card I : ℝ)| = (Fintype.card I : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    calc
      (Fintype.card I : ℝ) * |mu| = |(Fintype.card I : ℝ) * mu| := by
        rw [abs_mul, hcardAbs]
      _ = |∑ i, a i| := congrArg abs hmean
  have htriangle :
      ∑ i, |a i| ≤
        (Fintype.card I : ℝ) * |mu| + ∑ i, |a i - mu| := by
    calc
      ∑ i, |a i| ≤ ∑ i, (|mu| + |a i - mu|) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |a i| = |mu + (a i - mu)| := by congr 1 <;> ring
          _ ≤ |mu| + |a i - mu| := abs_add_le _ _
      _ = (Fintype.card I : ℝ) * |mu| + ∑ i, |a i - mu| := by
        simp [Finset.sum_add_distrib]
  have hdiff : theta / 2 * Fintype.card I < ∑ i, |a i - mu| := by
    rw [hmeanAbs] at htriangle
    linarith
  have hcauchy :
      (∑ i, |a i - mu|) ^ 2 ≤
        (Fintype.card I : ℝ) * ∑ i, (a i - mu) ^ 2 := by
    simpa only [sq_abs, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset I)) (f := fun i ↦ |a i - mu|))
  have htargetSq :
      (theta / 2 * (Fintype.card I : ℝ)) ^ 2 ≤
        (Fintype.card I : ℝ) * ∑ i, (a i - mu) ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (by positivity)
        (Finset.sum_nonneg fun i _ ↦ abs_nonneg (a i - mu))).2 hdiff.le
    exact hsquare.trans hcauchy
  have hvarianceNonneg : 0 ≤ ∑ i, (a i - mu) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

/-- **Balanced fixed-slice anti-concentration for bounded integer
coefficients.**

If the population is centered at `mu`, has variance at least `eta * |I|`,
and the slice selects and omits at least a `c` proportion of the population,
then every point mass is at most an explicit constant times `1 / sqrt |I|`.
The proof is the complete matching → pair embedding → Fourier → Esseen
pipeline; no probabilistic hypothesis is hidden in the statement. -/
theorem slice_point_probability_le_of_integer_variance
    {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (mu c eta : ℝ) (B s : ℕ)
    [Nonempty (BoolSlice I s)]
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (heta : 0 < eta) (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ i, |a i| ≤ (B : ℤ))
    (hcentered : ∑ i, ((a i : ℝ) - mu) = 0)
    (hvariance : eta * (Fintype.card I : ℝ) ≤
      ∑ i, ((a i : ℝ) - mu) ^ 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (x : ℝ) :
    finProbability (BoolSlice I s)
        (fun omega ↦ sliceLinear s (fun i ↦ (a i : ℝ)) omega = x) ≤
      variancePointMassConstant c eta B /
        Real.sqrt (Fintype.card I : ℝ) := by
  classical
  obtain ⟨M, hM, hgap, hMcard⟩ :=
    Pairing.exists_many_disjoint_coefficient_pairs
      (Finset.univ : Finset I) a B eta mu
      (by simpa using hbounded)
      (by simpa using hcentered)
      (by simpa using hvariance)
  let p : PairEmbedding (PairEmbeddingAdapter.MatchingIndex M) I :=
    PairEmbeddingAdapter.pairEmbeddingOfEdgeMatching
      (Pairing.coefficientGraph (Finset.univ : Finset I) a) M hM
  have hgapReal :=
    PairEmbeddingAdapter.coefficient_gap_real_of_edgeMatching
      (Pairing.coefficientGraph (Finset.univ : Finset I) a) M hM a
      (1 : ℤ) (2 * (B : ℤ)) hgap
  have hgapLower : ∀ k : PairEmbeddingAdapter.MatchingIndex M,
      1 ≤ |(a (p (k, false)) : ℝ) - (a (p (k, true)) : ℝ)| := by
    intro k
    simpa [p] using (hgapReal k).1
  have hgapUpper : ∀ k : PairEmbeddingAdapter.MatchingIndex M,
      |(a (p (k, false)) : ℝ) - (a (p (k, true)) : ℝ)| ≤
        2 * (B : ℝ) := by
    intro k
    simpa only [p, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat,
      Int.cast_natCast] using (hgapReal k).2
  have hNpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hI
  have hMposReal : 0 < (M.card : ℝ) := by
    have hleft : 0 < eta * (Fintype.card I : ℝ) := mul_pos heta hNpos
    have hright : 0 < 8 * (B : ℝ) ^ 2 * (M.card : ℝ) :=
      hleft.trans_le (by simpa using hMcard)
    by_contra hnot
    have hzero : (M.card : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg M.card)
    rw [hzero, mul_zero] at hright
    exact (lt_irrefl 0) hright
  have hMpos : 0 < Fintype.card (PairEmbeddingAdapter.MatchingIndex M) := by
    rw [PairEmbeddingAdapter.card_matchingIndex]
    exact_mod_cast hMposReal
  have htwoB : (1 : ℝ) ≤ 2 * (B : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * B by omega)
  have hpoint := slice_point_probability_le_of_pairs
    p s (fun i ↦ (a i : ℝ)) c (2 * (B : ℝ)) hc0 hc1 hsel hunsel
    htwoB hgapLower hgapUpper hMpos x
  have hA : 0 < (c ^ 3 / 256) / (4 * Real.pi ^ 2) := by positivity
  have hmatch : eta * (Fintype.card I : ℝ) ≤
      8 * (B : ℝ) ^ 2 * (M.card : ℝ) := by simpa using hMcard
  have hinvM : 1 / (M.card : ℝ) ≤
      (8 * (B : ℝ) ^ 2) /
        (eta * (Fintype.card I : ℝ)) := by
    apply (div_le_div_iff₀ hMposReal (mul_pos heta hNpos)).2
    simpa only [one_mul] using hmatch
  have hsqrt :
      Real.sqrt
          (Real.pi /
            ((c ^ 3 / 256) * (M.card : ℝ) / (4 * Real.pi ^ 2))) ≤
        Real.sqrt
          (((8 * Real.pi * (B : ℝ) ^ 2) /
              (eta * ((c ^ 3 / 256) / (4 * Real.pi ^ 2)))) /
            (Fintype.card I : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hpiA : 0 ≤ Real.pi / ((c ^ 3 / 256) / (4 * Real.pi ^ 2)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hinvM hpiA
    calc
      Real.pi /
            ((c ^ 3 / 256) * (M.card : ℝ) / (4 * Real.pi ^ 2)) =
          (Real.pi / ((c ^ 3 / 256) / (4 * Real.pi ^ 2))) *
            (1 / (M.card : ℝ)) := by
        field_simp [ne_of_gt hA, ne_of_gt hMposReal, ne_of_gt Real.pi_pos]
        <;> ring
      _ ≤ (Real.pi / ((c ^ 3 / 256) / (4 * Real.pi ^ 2))) *
            ((8 * (B : ℝ) ^ 2) /
              (eta * (Fintype.card I : ℝ))) := hmul
      _ = ((8 * Real.pi * (B : ℝ) ^ 2) /
              (eta * ((c ^ 3 / 256) / (4 * Real.pi ^ 2)))) /
            (Fintype.card I : ℝ) := by
        field_simp [ne_of_gt hA, ne_of_gt heta, ne_of_gt hNpos,
          ne_of_gt Real.pi_pos]
        <;> ring
  calc
    finProbability (BoolSlice I s)
        (fun omega ↦ sliceLinear s (fun i ↦ (a i : ℝ)) omega = x) ≤
        16 * (2 * (B : ℝ)) * Real.exp 1 *
          Real.sqrt
            (Real.pi /
              ((c ^ 3 / 256) *
                Fintype.card (PairEmbeddingAdapter.MatchingIndex M) /
                  (4 * Real.pi ^ 2))) := hpoint
    _ = 32 * (B : ℝ) * Real.exp 1 *
          Real.sqrt
            (Real.pi /
              ((c ^ 3 / 256) * (M.card : ℝ) /
                (4 * Real.pi ^ 2))) := by
      rw [PairEmbeddingAdapter.card_matchingIndex]
      ring
    _ ≤ 32 * (B : ℝ) * Real.exp 1 *
          Real.sqrt
            (((8 * Real.pi * (B : ℝ) ^ 2) /
                (eta * ((c ^ 3 / 256) / (4 * Real.pi ^ 2)))) /
              (Fintype.card I : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = variancePointMassConstant c eta B /
          Real.sqrt (Fintype.card I : ℝ) := by
      rw [Real.sqrt_div (by positivity)]
      simp only [variancePointMassConstant]
      ring

/-- Small-total-sum form of balanced fixed-slice anti-concentration.

The hypotheses `hl1` and `hsmall` are often the convenient graph-theoretic
output: the coefficients have linear absolute mass, but their signed sum is
too small to account for it.  The preceding deterministic lemma converts
these hypotheses into variance density `theta²/4`, after which
`slice_point_probability_le_of_integer_variance` applies. -/
theorem slice_point_probability_le_of_integer_l1_small_sum
    {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (mu c theta : ℝ) (B s : ℕ)
    [Nonempty (BoolSlice I s)]
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (htheta : 0 < theta) (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ i, |a i| ≤ (B : ℤ))
    (hmean : (Fintype.card I : ℝ) * mu = ∑ i, (a i : ℝ))
    (hl1 : theta * Fintype.card I ≤ ∑ i, |(a i : ℝ)|)
    (hsmall : |∑ i, (a i : ℝ)| < theta / 2 * Fintype.card I)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (x : ℝ) :
    finProbability (BoolSlice I s)
        (fun omega ↦ sliceLinear s (fun i ↦ (a i : ℝ)) omega = x) ≤
      variancePointMassConstant c (theta ^ 2 / 4) B /
        Real.sqrt (Fintype.card I : ℝ) := by
  have hcentered : ∑ i, ((a i : ℝ) - mu) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hvariance : theta ^ 2 / 4 * Fintype.card I ≤
      ∑ i, ((a i : ℝ) - mu) ^ 2 :=
    centered_variance_ge_of_l1_of_small_sum
      (fun i ↦ (a i : ℝ)) mu theta htheta.le hI hmean hl1 hsmall
  exact slice_point_probability_le_of_integer_variance
    a mu c (theta ^ 2 / 4) B s hc0 hc1 (by positivity) hB hI hbounded
    hcentered hvariance hsel hunsel x

end

end Erdos636.AntiConcentration
