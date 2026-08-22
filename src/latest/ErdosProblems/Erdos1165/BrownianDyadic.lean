/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.BrownianReflection
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian tails for dyadic Brownian increments

This file supplies the quantitative finite-dimensional input for a dyadic
chaining proof of Brownian strip survival.  In particular, every Brownian
increment is proved sub-Gaussian with its exact variance, and explicit one-
and two-sided tail estimates are derived without an additional stochastic
analysis assumption.

The statements deliberately use `Measure.real`: this is the convenient form
for finite union bounds in a probability space.
-/

open scoped ENNReal NNReal

namespace Erdos1165.BrownianDyadic

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {P : Measure Omega} {B : ℝ≥0 → Omega → ℝ}

/-! ## Exact sub-Gaussian laws -/

/-- A centred real Gaussian is sub-Gaussian with its exact variance. -/
theorem hasSubgaussianMGF_id_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- Transport the exact Gaussian sub-Gaussian estimate through a law. -/
theorem HasLaw.hasSubgaussianMGF_of_gaussianReal_zero
    {X : Omega → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    HasSubgaussianMGF X v P := by
  have hG := hasSubgaussianMGF_id_gaussianReal v
  rw [← hX.map_eq] at hG
  simpa only [id_eq, Function.id_comp] using
    HasSubgaussianMGF.of_map hX.aemeasurable hG

/-- A Brownian evaluation is sub-Gaussian with parameter equal to time. -/
theorem IsPreBrownianReal.hasSubgaussianMGF_eval
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasSubgaussianMGF (B t) t P :=
  HasLaw.hasSubgaussianMGF_of_gaussianReal_zero (hB.hasLaw_eval t)

/-- A Brownian increment is sub-Gaussian with parameter equal to the distance
between its two time arguments. -/
theorem IsPreBrownianReal.hasSubgaussianMGF_sub
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    HasSubgaussianMGF (B s - B t) (nndist (s : ℝ) (t : ℝ)) P :=
  HasLaw.hasSubgaussianMGF_of_gaussianReal_zero (hB.hasLaw_sub s t)

/-! ## Tail bounds -/

/-- Exact-variance Chernoff bound for the upper tail of a Brownian
increment. -/
theorem IsPreBrownianReal.measureReal_sub_ge_le
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P.real {omega | a ≤ B s omega - B t omega} ≤
      Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) :=
  (IsPreBrownianReal.hasSubgaussianMGF_sub hB s t).measure_ge_le ha

/-- The matching lower-tail estimate. -/
theorem IsPreBrownianReal.measureReal_sub_le_neg_le
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P.real {omega | B s omega - B t omega ≤ -a} ≤
      Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) := by
  have h := (IsPreBrownianReal.hasSubgaussianMGF_sub hB s t).neg.measure_ge_le ha
  change P.real {omega | a ≤ -(B s omega - B t omega)} ≤ _ at h
  have hevent :
      {omega | a ≤ -(B s omega - B t omega)} =
        {omega | B s omega - B t omega ≤ -a} := by
    ext omega
    constructor
    · intro homega
      change a ≤ -(B s omega - B t omega) at homega
      change B s omega - B t omega ≤ -a
      linarith
    · intro homega
      change B s omega - B t omega ≤ -a at homega
      change a ≤ -(B s omega - B t omega)
      linarith
  rw [hevent] at h
  simpa only [Pi.neg_apply, neg_sq] using h

/-- Two-sided exact-variance tail bound for a Brownian increment. -/
theorem IsPreBrownianReal.measureReal_abs_sub_ge_le
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P.real {omega | a ≤ |B s omega - B t omega|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let U : Set Omega := {omega | a ≤ B s omega - B t omega}
  let L : Set Omega := {omega | B s omega - B t omega ≤ -a}
  have hsubset : {omega | a ≤ |B s omega - B t omega|} ⊆ U ∪ L := by
    intro omega homega
    change a ≤ |B s omega - B t omega| at homega
    change a ≤ B s omega - B t omega ∨ B s omega - B t omega ≤ -a
    rcases (le_abs.mp homega) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  calc
    P.real {omega | a ≤ |B s omega - B t omega|}
        ≤ P.real (U ∪ L) := measureReal_mono hsubset
    _ ≤ P.real U + P.real L := measureReal_union_le _ _
    _ ≤ Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) +
          Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) := by
      gcongr
      · exact IsPreBrownianReal.measureReal_sub_ge_le hB s t ha
      · exact IsPreBrownianReal.measureReal_sub_le_neg_le hB s t ha
    _ = 2 * Real.exp (-a ^ 2 / (2 * (nndist (s : ℝ) (t : ℝ) : ℝ))) := by ring

/-! ## Finite dyadic levels -/

/-- The `j`th point of the level-`k` dyadic grid in `[0,T]`. -/
def dyadicTime (T : ℝ≥0) (k j : ℕ) : ℝ≥0 :=
  T * (j : ℝ≥0) / (2 ^ k : ℝ≥0)

@[simp] lemma dyadicTime_zero (T : ℝ≥0) (k : ℕ) :
    dyadicTime T k 0 = 0 := by
  simp [dyadicTime]

lemma dyadicTime_mono_index (T : ℝ≥0) (k : ℕ) :
    Monotone (dyadicTime T k) := by
  intro i j hij
  unfold dyadicTime
  gcongr

/-- Consecutive grid points are separated by exactly `T / 2^k`. -/
lemma nndist_dyadicTime_succ (T : ℝ≥0) (k j : ℕ) :
    nndist ((dyadicTime T k (j + 1) : ℝ)) ((dyadicTime T k j : ℝ)) =
      T / (2 ^ k : ℝ≥0) := by
  apply NNReal.eq
  rw [Real.nndist_eq]
  simp only [Real.coe_nnabs, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    dyadicTime, NNReal.coe_mul]
  rw [abs_of_nonneg]
  · push_cast
    ring
  · apply sub_nonneg.mpr
    change (dyadicTime T k j : ℝ) ≤ (dyadicTime T k (j + 1) : ℝ)
    exact_mod_cast dyadicTime_mono_index T k (Nat.le_succ j)

/-- Failure of the increment cutoff at one finite dyadic level. -/
def dyadicBadAt (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0)
    (a : ℝ) (k : ℕ) : Set Omega :=
  ⋃ j ∈ Finset.range (2 ^ k),
    {omega | a ≤
      |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega|}

lemma IsPreBrownianReal.nullMeasurableSet_dyadicBadAt
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (a : ℝ) (k : ℕ) :
    NullMeasurableSet (dyadicBadAt B T a k) P := by
  unfold dyadicBadAt
  apply NullMeasurableSet.iUnion
  intro j
  apply NullMeasurableSet.iUnion
  intro _hj
  have hmeas : AEMeasurable
      (fun omega ↦
        |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega|) P :=
    ((hB.aemeasurable _).sub (hB.aemeasurable _)).abs
  exact hmeas.nullMeasurableSet_preimage measurableSet_Ici

/-- A finite dyadic level has the expected union bound: number of edges
times the exact Gaussian two-sided tail of one edge. -/
theorem IsPreBrownianReal.measureReal_dyadicBadAt_le
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    P.real (dyadicBadAt B T a k) ≤
      (2 ^ k : ℝ) *
        (2 * Real.exp (-a ^ 2 / (2 * (T / (2 ^ k : ℝ≥0) : ℝ)))) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold dyadicBadAt
  calc
    P.real (⋃ j ∈ Finset.range (2 ^ k),
        {omega | a ≤
          |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega|})
        ≤ ∑ j ∈ Finset.range (2 ^ k),
          P.real {omega | a ≤
            |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (2 ^ k),
          2 * Real.exp (-a ^ 2 / (2 * (T / (2 ^ k : ℝ≥0) : ℝ))) := by
      gcongr with j hj
      have htail := IsPreBrownianReal.measureReal_abs_sub_ge_le hB
        (dyadicTime T k (j + 1)) (dyadicTime T k j) ha
      rw [nndist_dyadicTime_succ] at htail
      norm_cast at htail ⊢
    _ = (2 ^ k : ℝ) *
          (2 * Real.exp (-a ^ 2 / (2 * (T / (2 ^ k : ℝ≥0) : ℝ)))) := by
      simp

/-- Failure of at least one cutoff in a prescribed sequence of dyadic
levels. -/
def dyadicBad (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0)
    (a : ℕ → ℝ) : Set Omega :=
  ⋃ k : ℕ, dyadicBadAt B T (a k) k

lemma IsPreBrownianReal.nullMeasurableSet_dyadicBad
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (a : ℕ → ℝ) :
    NullMeasurableSet (dyadicBad B T a) P := by
  unfold dyadicBad
  exact NullMeasurableSet.iUnion fun k ↦
    IsPreBrownianReal.nullMeasurableSet_dyadicBadAt hB T (a k) k

/-- Countable union bound for all dyadic levels.  This is stated in
`ENNReal`, so no interchange of `toReal` with an infinite sum is needed. -/
theorem IsPreBrownianReal.measure_dyadicBad_le_tsum
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) :
    P (dyadicBad B T a) ≤
      ∑' k : ℕ, ENNReal.ofReal
        ((2 ^ k : ℝ) *
          (2 * Real.exp (-(a k) ^ 2 /
            (2 * (T / (2 ^ k : ℝ≥0) : ℝ))))) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold dyadicBad
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k ↦ ?_)
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal
    (IsPreBrownianReal.measureReal_dyadicBadAt_le hB T (ha k) k)

/-- If the explicit Gaussian union-bound series is less than one, the event
that every dyadic increment meets its cutoff has positive probability. -/
theorem IsPreBrownianReal.measure_compl_dyadicBad_pos
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k)
    (hsum :
      (∑' k : ℕ, ENNReal.ofReal
        ((2 ^ k : ℝ) *
          (2 * Real.exp (-(a k) ^ 2 /
            (2 * (T / (2 ^ k : ℝ≥0) : ℝ)))))) < 1) :
    0 < P (dyadicBad B T a)ᶜ := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbad : P (dyadicBad B T a) < 1 :=
    (IsPreBrownianReal.measure_dyadicBad_le_tsum hB T ha).trans_lt hsum
  rw [measure_compl₀
    (IsPreBrownianReal.nullMeasurableSet_dyadicBad hB T a)
    (measure_ne_top P _), measure_univ]
  exact tsub_pos_iff_lt.mpr hbad

/-! ## An explicit diffusive choice of cutoffs -/

/-- Geometrically decreasing chaining budget.  Its infinite sum is `r / 2`. -/
def geometricCutoff (r : ℝ≥0) (k : ℕ) : ℝ :=
  (r : ℝ) / 8 * ((3 : ℝ) / 4) ^ k

/-- A fixed short diffusive horizon for the explicit chaining estimate. -/
def dyadicHorizon (r : ℝ≥0) : ℝ≥0 :=
  r ^ 2 / 2048

lemma geometricCutoff_nonneg (r : ℝ≥0) (k : ℕ) :
    0 ≤ geometricCutoff r k := by
  unfold geometricCutoff
  positivity

lemma summable_geometricCutoff (r : ℝ≥0) :
    Summable (geometricCutoff r) := by
  unfold geometricCutoff
  exact (summable_geometric_of_norm_lt_one
    (by norm_num : ‖(3 / 4 : ℝ)‖ < 1)).mul_left _

lemma tsum_geometricCutoff (r : ℝ≥0) :
    ∑' k : ℕ, geometricCutoff r k = (r : ℝ) / 2 := by
  unfold geometricCutoff
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · ring
  · norm_num

/-- At the explicit horizon `r^2/2048`, the level-`k` Chernoff
exponent is exactly `16*(9/8)^k`. -/
lemma geometricCutoff_exponent {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    -(geometricCutoff r k) ^ 2 /
        (2 * (dyadicHorizon r / (2 ^ k : ℝ≥0) : ℝ)) =
      -(16 * ((9 : ℝ) / 8) ^ k) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hp : (2 : ℝ) ^ k * 3 ^ (k * 2) =
      ((9 : ℝ) / 8) ^ k * 4 ^ (k * 2) := by
    calc
      (2 : ℝ) ^ k * 3 ^ (k * 2)
          = (2 : ℝ) ^ k * (3 ^ 2) ^ k := by
            rw [mul_comm k 2, pow_mul]
      _ = (18 : ℝ) ^ k := by norm_num [← mul_pow]
      _ = ((9 : ℝ) / 8) ^ k * 4 ^ (k * 2) := by
        rw [mul_comm k 2, pow_mul]
        norm_num [← mul_pow]
  simp only [geometricCutoff, dyadicHorizon, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat]
  rw [div_pow]
  field_simp
  calc
    -(((3 : ℝ) ^ k) ^ 2 * 2048 * 2 ^ k)
        = -(2048 * ((2 : ℝ) ^ k * 3 ^ (k * 2))) := by
          rw [pow_mul]
          ring
    _ = -(2048 * (((9 : ℝ) / 8) ^ k * 4 ^ (k * 2))) := by rw [hp]
    _ = -((8 : ℝ) ^ 2 * (4 ^ k) ^ 2 * 2 * 16 * ((9 : ℝ) / 8) ^ k) := by
      rw [pow_mul]
      norm_num
      ring

/-- Explicit specialized finite-level estimate. -/
theorem IsPreBrownianReal.measureReal_dyadicBadAt_geometric_le
    (hB : IsPreBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    P.real (dyadicBadAt B (dyadicHorizon r) (geometricCutoff r k) k) ≤
      (2 ^ k : ℝ) *
        (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k))) := by
  simpa only [geometricCutoff_exponent hr] using
    IsPreBrownianReal.measureReal_dyadicBadAt_le hB (dyadicHorizon r)
      (geometricCutoff_nonneg r k) k

lemma one_add_nat_div_eight_le_nine_eighth_pow (k : ℕ) :
    1 + (k : ℝ) / 8 ≤ ((9 : ℝ) / 8) ^ k := by
  have h := one_add_mul_le_pow (a := (1 / 8 : ℝ)) (by norm_num) k
  calc
    1 + (k : ℝ) / 8 = 1 + (k : ℝ) * (1 / 8) := by ring
    _ ≤ (1 + (1 / 8 : ℝ)) ^ k := h
    _ = ((9 : ℝ) / 8) ^ k := by norm_num

/-- The exact level bound is dominated by a genuinely geometric sequence. -/
lemma geometric_level_bound_le (k : ℕ) :
    (2 ^ k : ℝ) *
        (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k))) ≤
      2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k := by
  have hpow := one_add_nat_div_eight_le_nine_eighth_pow k
  have hexp : Real.exp (-(16 * ((9 : ℝ) / 8) ^ k)) ≤
      Real.exp (-16 + (k : ℝ) * (-2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (2 ^ k : ℝ) *
          (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k)))
        ≤ (2 ^ k : ℝ) *
          (2 * Real.exp (-16 + (k : ℝ) * (-2))) := by gcongr
    _ = 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k := by
      rw [Real.exp_add, Real.exp_nat_mul]
      ring

lemma two_mul_exp_neg_two_le_two_thirds :
    2 * Real.exp (-2) ≤ (2 : ℝ) / 3 := by
  have hexp : (3 : ℝ) ≤ Real.exp 2 := by
    nlinarith [Real.add_one_le_exp 2]
  rw [Real.exp_neg]
  have hinv : (Real.exp 2)⁻¹ ≤ (3 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hexp
  nlinarith

lemma two_mul_exp_neg_sixteen_le_two_seventeenths :
    2 * Real.exp (-16) ≤ (2 : ℝ) / 17 := by
  have hexp : (17 : ℝ) ≤ Real.exp 16 := by
    nlinarith [Real.add_one_le_exp 16]
  rw [Real.exp_neg]
  have hinv : (Real.exp 16)⁻¹ ≤ (17 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hexp
  nlinarith

/-- The geometric majorant of the failure probabilities has total mass
strictly less than one. -/
lemma tsum_geometric_level_majorant_lt_one :
    (∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) < 1 := by
  have hq_nonneg : 0 ≤ 2 * Real.exp (-2) := by positivity
  have hq_lt : ‖2 * Real.exp (-2)‖ < 1 := by
    rw [Real.norm_of_nonneg hq_nonneg]
    exact (two_mul_exp_neg_two_le_two_thirds.trans_lt (by norm_num))
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_lt]
  rw [inv_eq_one_div, mul_one_div]
  apply (div_lt_one (by
    nlinarith [two_mul_exp_neg_two_le_two_thirds])).mpr
  nlinarith [two_mul_exp_neg_two_le_two_thirds,
    two_mul_exp_neg_sixteen_le_two_seventeenths]

/-- In fact, the geometric failure majorant is less than one half.  The
elementary estimates above give the sharper rational upper bound `6/17`. -/
lemma tsum_geometric_level_majorant_lt_half :
    (∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) <
      (1 : ℝ) / 2 := by
  have hq_nonneg : 0 ≤ 2 * Real.exp (-2) := by positivity
  have hq_lt : ‖2 * Real.exp (-2)‖ < 1 := by
    rw [Real.norm_of_nonneg hq_nonneg]
    exact (two_mul_exp_neg_two_le_two_thirds.trans_lt (by norm_num))
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_lt]
  rw [inv_eq_one_div, mul_one_div]
  have hden : 0 < 1 - 2 * Real.exp (-2) := by
    nlinarith [two_mul_exp_neg_two_le_two_thirds]
  rw [div_lt_iff₀ hden]
  nlinarith [two_mul_exp_neg_two_le_two_thirds,
    two_mul_exp_neg_sixteen_le_two_seventeenths]

lemma summable_geometric_level_majorant :
    Summable (fun k : ℕ ↦
      2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
  have hq : ‖2 * Real.exp (-2)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.exp (-2))]
    exact two_mul_exp_neg_two_le_two_thirds.trans_lt (by norm_num)
  have hgeom : Summable (fun k : ℕ ↦ (2 * Real.exp (-2)) ^ k) :=
    summable_geometric_of_norm_lt_one hq
  exact hgeom.mul_left _

lemma tsum_ofReal_geometric_failure_lt_one :
    (∑' k : ℕ, ENNReal.ofReal
      ((2 ^ k : ℝ) *
        (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k))))) < 1 := by
  calc
    (∑' k : ℕ, ENNReal.ofReal
        ((2 ^ k : ℝ) *
          (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k)))))
        ≤ ∑' k : ℕ, ENNReal.ofReal
          (2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
            apply ENNReal.tsum_le_tsum
            intro k
            exact ENNReal.ofReal_le_ofReal (geometric_level_bound_le k)
    _ = ENNReal.ofReal
          (∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun _ ↦ by positivity) summable_geometric_level_majorant
    _ < 1 := by
      rw [ENNReal.ofReal_lt_one]
      exact tsum_geometric_level_majorant_lt_one

lemma tsum_ofReal_geometric_failure_lt_half :
    (∑' k : ℕ, ENNReal.ofReal
      ((2 ^ k : ℝ) *
        (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k))))) <
      (1 : ℝ≥0∞) / 2 := by
  calc
    (∑' k : ℕ, ENNReal.ofReal
        ((2 ^ k : ℝ) *
          (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k)))))
        ≤ ∑' k : ℕ, ENNReal.ofReal
          (2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
            apply ENNReal.tsum_le_tsum
            intro k
            exact ENNReal.ofReal_le_ofReal (geometric_level_bound_le k)
    _ = ENNReal.ofReal
          (∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun _ ↦ by positivity) summable_geometric_level_majorant
    _ < (1 : ℝ≥0∞) / 2 := by
      have hnonneg : 0 ≤
          ∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k :=
        tsum_nonneg fun _ ↦ by positivity
      rw [ENNReal.ofReal_lt_iff_lt_toReal hnonneg (by finiteness)]
      simpa using tsum_geometric_level_majorant_lt_half

/-- The explicit Gaussian calculation already gives positive probability
that every dyadic increment satisfies the geometric cutoff. -/
theorem IsPreBrownianReal.measure_compl_dyadicBad_geometric_pos
    (hB : IsPreBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (dyadicBad B (dyadicHorizon r) (geometricCutoff r))ᶜ := by
  refine IsPreBrownianReal.measure_compl_dyadicBad_pos hB (dyadicHorizon r)
    (a := geometricCutoff r) (fun k ↦ geometricCutoff_nonneg r k) ?_
  simpa only [geometricCutoff_exponent hr] using
    tsum_ofReal_geometric_failure_lt_one

/-- The explicit union bound loses less than half the probability mass. -/
theorem IsPreBrownianReal.measure_dyadicBad_geometric_lt_half
    (hB : IsPreBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    P (dyadicBad B (dyadicHorizon r) (geometricCutoff r)) <
      (1 : ℝ≥0∞) / 2 := by
  exact (IsPreBrownianReal.measure_dyadicBad_le_tsum hB
    (dyadicHorizon r) (geometricCutoff_nonneg r)).trans_lt (by
      simpa only [geometricCutoff_exponent hr] using
        tsum_ofReal_geometric_failure_lt_half)

/-! ## Deterministic chaining on the dyadic tree -/

lemma dyadicTime_even (T : ℝ≥0) (k j : ℕ) :
    dyadicTime T (k + 1) (2 * j) = dyadicTime T k j := by
  apply NNReal.eq
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

lemma dyadicTime_top (T : ℝ≥0) (k : ℕ) :
    dyadicTime T k (2 ^ k) = T := by
  simp [dyadicTime]

/-- Outside `dyadicBad`, every edge of every grid satisfies its prescribed
strict cutoff. -/
lemma dyadic_edge_lt_of_mem_compl_dyadicBad
    {omega : Omega} {T : ℝ≥0} {a : ℕ → ℝ}
    (homega : omega ∈ (dyadicBad B T a)ᶜ) {k j : ℕ} (hj : j < 2 ^ k) :
    |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega| < a k := by
  by_contra hnot
  have hge : a k ≤
      |B (dyadicTime T k (j + 1)) omega - B (dyadicTime T k j) omega| :=
    le_of_not_gt hnot
  apply homega
  unfold dyadicBad dyadicBadAt
  exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨j,
    mem_iUnion.2 ⟨Finset.mem_range.2 hj, hge⟩⟩⟩

/-- Chaining bound at every finite dyadic endpoint.  The proof follows the
binary tree: an even endpoint is inherited from the previous level, while
an odd endpoint is one new fine-grid edge from an inherited endpoint. -/
lemma abs_dyadic_endpoint_le_sum
    {f : ℝ≥0 → ℝ} {T : ℝ≥0} {a : ℕ → ℝ}
    (hzero : f 0 = 0)
    (hedge : ∀ k j, j < 2 ^ k →
      |f (dyadicTime T k (j + 1)) - f (dyadicTime T k j)| < a k) :
    ∀ k j, j ≤ 2 ^ k →
      |f (dyadicTime T k j)| ≤ ∑ i ∈ Finset.range (k + 1), a i := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · have ha0 : 0 ≤ a 0 :=
          (abs_nonneg _).trans (hedge 0 0 (by norm_num)).le
        simp [dyadicTime, hzero, ha0]
      · have h := (hedge 0 0 (by norm_num)).le
        simpa [dyadicTime, hzero] using h
  | succ k ih =>
      intro j hj
      rcases Nat.even_or_odd' j with ⟨q, rfl | rfl⟩
      · rw [dyadicTime_even]
        exact (ih q (by
          rw [pow_succ] at hj
          omega)).trans (by
            have ha : 0 ≤ a (k + 1) :=
              (abs_nonneg _).trans (hedge (k + 1) 0 (by positivity)).le
            simp only [Finset.sum_range_succ]
            exact le_add_of_nonneg_right ha)
      · have hq : q ≤ 2 ^ k := by
          rw [pow_succ] at hj
          omega
        have hqedge : 2 * q < 2 ^ (k + 1) := by
          rw [pow_succ]
          omega
        have htri :
            |f (dyadicTime T (k + 1) (2 * q + 1))| ≤
              |f (dyadicTime T (k + 1) (2 * q + 1)) -
                f (dyadicTime T (k + 1) (2 * q))| +
              |f (dyadicTime T (k + 1) (2 * q))| := by
          calc
            |f (dyadicTime T (k + 1) (2 * q + 1))|
                = |(f (dyadicTime T (k + 1) (2 * q + 1)) -
                    f (dyadicTime T (k + 1) (2 * q))) +
                    f (dyadicTime T (k + 1) (2 * q))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        calc
          |f (dyadicTime T (k + 1) (2 * q + 1))|
              ≤ |f (dyadicTime T (k + 1) (2 * q + 1)) -
                  f (dyadicTime T (k + 1) (2 * q))| +
                |f (dyadicTime T (k + 1) (2 * q))| := htri
          _ ≤ a (k + 1) + ∑ i ∈ Finset.range (k + 1), a i := by
            gcongr
            · exact (by
                simpa only [Nat.add_eq, Nat.reduceAdd] using
                  (hedge (k + 1) (2 * q) hqedge).le)
            · rw [dyadicTime_even]
              exact ih q hq
          _ = ∑ i ∈ Finset.range (k + 1 + 1), a i := by
            simp only [Finset.sum_range_succ]
            ring

/-- The left dyadic-grid index immediately below `t`. -/
def dyadicIndex (T t : ℝ≥0) (k : ℕ) : ℕ :=
  ⌊((t : ℝ) / (T : ℝ)) * (2 : ℝ) ^ k⌋₊

/-- The corresponding left dyadic approximation to `t`. -/
def dyadicApprox (T t : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  dyadicTime T k (dyadicIndex T t k)

lemma dyadicIndex_le_pow {T t : ℝ≥0} (hT : 0 < T) (ht : t ≤ T) (k : ℕ) :
    dyadicIndex T t k ≤ 2 ^ k := by
  unfold dyadicIndex
  rw [← Nat.floor_natCast (R := ℝ) (2 ^ k)]
  apply Nat.floor_mono
  have hratio : (t : ℝ) / (T : ℝ) ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hT)).mpr
    exact_mod_cast ht
  calc
    (t : ℝ) / (T : ℝ) * (2 : ℝ) ^ k
        ≤ 1 * (2 : ℝ) ^ k := by gcongr
    _ = (2 ^ k : ℕ) := by norm_num

/-- The dyadic left approximations converge to their target time. -/
lemma tendsto_dyadicApprox {T t : ℝ≥0} (hT : 0 < T) :
    Tendsto (dyadicApprox T t) atTop (nhds t) := by
  rw [← NNReal.tendsto_coe]
  have hratio_nonneg : 0 ≤ (t : ℝ) / (T : ℝ) := by positivity
  have hpow : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hfloor :=
    (tendsto_nat_floor_mul_div_atTop hratio_nonneg).comp hpow
  have hconst : Tendsto (fun _ : ℕ ↦ (T : ℝ)) atTop (nhds (T : ℝ)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hfloor
  convert hmul using 1
  · ext k
    simp only [dyadicApprox, dyadicTime, dyadicIndex, NNReal.coe_div,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, Function.comp_apply]
    norm_num
    rw [mul_div_assoc]
  · field_simp

/-- A continuous function whose increments obey every dyadic cutoff is
bounded on the whole interval by the sum of those cutoffs. -/
lemma abs_le_tsum_of_continuous_of_dyadic_edges
    {f : ℝ≥0 → ℝ} {T : ℝ≥0} {a : ℕ → ℝ}
    (hT : 0 < T) (hcont : Continuous f) (hzero : f 0 = 0)
    (ha : ∀ k, 0 ≤ a k) (hsum : Summable a)
    (hedge : ∀ k j, j < 2 ^ k →
      |f (dyadicTime T k (j + 1)) - f (dyadicTime T k j)| < a k)
    {t : ℝ≥0} (ht : t ≤ T) :
    |f t| ≤ ∑' k : ℕ, a k := by
  have hvalues : Tendsto
      (fun k : ℕ ↦ |f (dyadicApprox T t k)|) atTop (nhds |f t|) :=
    (continuous_abs.tendsto (f t)).comp
      ((hcont.tendsto t).comp (tendsto_dyadicApprox hT))
  apply le_of_tendsto' hvalues
  intro k
  exact (abs_dyadic_endpoint_le_sum hzero hedge k (dyadicIndex T t k)
    (dyadicIndex_le_pow hT ht k)).trans
      (hsum.sum_le_tsum (Finset.range (k + 1)) (fun i _hi ↦ ha i))

/-- Pathwise conclusion of the explicit chaining construction: a continuous
path outside the dyadic failure event stays in the open strip of radius
`r` through time `r²/2048`. -/
lemma mem_rawStripEvent_of_continuous_of_mem_compl_dyadicBad
    {omega : Omega} {r : ℝ≥0} (hr : 0 < r)
    (hcont : Continuous (B · omega)) (hzero : B 0 omega = 0)
    (homega : omega ∈
      (dyadicBad B (dyadicHorizon r) (geometricCutoff r))ᶜ) :
    omega ∈ BrownianReflection.rawStripEvent B (dyadicHorizon r) (r : ℝ) := by
  intro t ht
  have hT : 0 < dyadicHorizon r := by
    unfold dyadicHorizon
    positivity
  have hbound : |B t omega| ≤ ∑' k : ℕ, geometricCutoff r k :=
    abs_le_tsum_of_continuous_of_dyadic_edges hT hcont hzero
      (geometricCutoff_nonneg r) (summable_geometricCutoff r)
      (fun k j hj ↦ dyadic_edge_lt_of_mem_compl_dyadicBad homega hj) ht
  rw [tsum_geometricCutoff] at hbound
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  linarith

/-- **Explicit Brownian short-time strip survival.**  At the deterministic
diffusive horizon `r²/2048`, the probability that a real Brownian motion
stays in the literal open strip `(-r,r)` is strictly positive. -/
theorem IsBrownianReal.measure_rawStripEvent_dyadicHorizon_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (BrownianReflection.rawStripEvent B (dyadicHorizon r) (r : ℝ)) := by
  let G : Set Omega :=
    (dyadicBad B (dyadicHorizon r) (geometricCutoff r))ᶜ
  have hGpos : 0 < P G := by
    simpa only [G] using
      IsPreBrownianReal.measure_compl_dyadicBad_geometric_pos
        hB.toIsPreBrownianReal hr
  have hsub : ∀ᵐ omega ∂P, omega ∈ G →
      omega ∈ BrownianReflection.rawStripEvent B
        (dyadicHorizon r) (r : ℝ) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero]
      with omega hcont hzero
    intro homega
    exact mem_rawStripEvent_of_continuous_of_mem_compl_dyadicBad
      hr hcont hzero homega
  exact hGpos.trans_le (measure_mono_ae hsub)

/-- Literal form of the preceding theorem, displaying the horizon rather
than the abbreviation used in the chaining proof. -/
theorem IsBrownianReal.measure_rawStripEvent_sq_div_2048_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (BrownianReflection.rawStripEvent B (r ^ 2 / 2048) (r : ℝ)) := by
  simpa only [dyadicHorizon] using
    IsBrownianReal.measure_rawStripEvent_dyadicHorizon_pos hB hr

/-- Measurable-envelope form of the explicit strip-survival estimate. -/
theorem IsBrownianReal.measure_stripEvent_sq_div_2048_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (BrownianReflection.stripEvent P B (r ^ 2 / 2048) (r : ℝ)) := by
  simpa only [BrownianReflection.stripEvent, measure_toMeasurable] using
    IsBrownianReal.measure_rawStripEvent_sq_div_2048_pos hB hr

end

end Erdos1165.BrownianDyadic
