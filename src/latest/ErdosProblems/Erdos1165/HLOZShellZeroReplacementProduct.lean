/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HeterogeneousProductTail
import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# The shell-zero replacement product

HLOZ control the initial shell by comparing a configuration in which every
selected coordinate lies in `I₁` with configurations in which some of those
coordinates have been replaced by values in the artificial window `I₀`.
The number of selected coordinates is genuinely random.

This file proves the finite algebra needed for that comparison.  After
conditioning on the exact `I₀ ∪ I₁` support size `total`, the source event
requires all `total` selected coordinates to lie in `I₁`.  The heterogeneous
moment estimate therefore uses cut `total`, producing

`((1 + C/(1+C))/2)^total`.

Since `total` is at least the shell-zero cut, this is bounded by the same
base to the cut.  Exact pair totals then sum without a factor equal to the
number of possible totals.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZShellZeroReplacementProduct

open Erdos1165.HeterogeneousProductTail
open Erdos1165.HLOZProposition48Candidates

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-- Bounded source configurations with at least `cut` selected coordinates,
all of which lie in the upper (`I₁`) window.  The redundant-looking
inequality `total ≤ upperCount` is the exact form used by the fixed-total
upper-tail theorem. -/
def boundedAllUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) (ell : ∀ c, State c) : Prop :=
  let total := (pairSupport upper lower ell).card
  total < bound + 1 ∧ cut ≤ total ∧ total ≤ upperCount upper ell

instance instDecidablePredBoundedAllUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) : DecidablePred (boundedAllUpperTail upper lower cut bound) :=
  fun ell ↦ by
    unfold boundedAllUpperTail
    infer_instance

/-- Partition the all-upper source by the actual selected support size. -/
theorem sum_boundedAllUpperTail_eq_sum_fixedTotal
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ) :
    (∑ ell : ∀ c, State c,
        if boundedAllUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) =
      ∑ total ∈ Finset.range (bound + 1),
        if cut ≤ total then
          ∑ ell : ∀ c, State c,
            if fixedTotalUpperTail upper lower total total ell then
              productPointMass weight ell else 0
        else 0 := by
  classical
  have hreorder :
      (∑ total ∈ Finset.range (bound + 1),
        if cut ≤ total then
          ∑ ell : ∀ c, State c,
            if fixedTotalUpperTail upper lower total total ell then
              productPointMass weight ell else 0
        else 0) =
      ∑ total ∈ Finset.range (bound + 1),
        ∑ ell : ∀ c, State c,
          if cut ≤ total then
            if fixedTotalUpperTail upper lower total total ell then
              productPointMass weight ell else 0
          else 0 := by
    apply Finset.sum_congr rfl
    intro total _
    by_cases hcut : cut ≤ total <;> simp [hcut]
  rw [hreorder]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _
  let actual := (pairSupport upper lower ell).card
  by_cases hbound : actual < bound + 1
  · have hmem : actual ∈ Finset.range (bound + 1) :=
      Finset.mem_range.mpr hbound
    rw [Finset.sum_eq_single actual]
    · by_cases hcut : cut ≤ actual <;>
        by_cases hall : actual ≤ upperCount upper ell <;>
          simp [actual, boundedAllUpperTail, fixedTotalUpperTail,
            hbound, hcut, hall]
    · intro total _ hne
      have hcard : actual ≠ total := Ne.symm hne
      by_cases hcutTotal : cut ≤ total
      · simp [hcutTotal, fixedTotalUpperTail, actual, hcard]
      · simp [hcutTotal]
    · exact fun hnot ↦ (hnot hmem).elim
  · have hout : actual ∉ Finset.range (bound + 1) := by
      simpa using hbound
    rw [Finset.sum_eq_zero]
    · simp [boundedAllUpperTail, actual, hbound]
    · intro total htotal
      have hne : actual ≠ total := by
        intro heq
        apply hout
        simpa [heq] using htotal
      by_cases hcutTotal : cut ≤ total
      · simp [hcutTotal, fixedTotalUpperTail, actual, hne]
      · simp [hcutTotal]

/-- The replacement moment base. -/
def replacementBase (C : ℝ) : ℝ :=
  (1 + C / (1 + C)) / 2

lemma replacementBase_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ replacementBase C := by
  unfold replacementBase
  have hden : 0 ≤ 1 + C := by linarith
  have hfrac : 0 ≤ C / (1 + C) := div_nonneg hC hden
  positivity

lemma replacementBase_le_one {C : ℝ} (hC : 0 ≤ C) :
    replacementBase C ≤ 1 := by
  unfold replacementBase
  have hden : 0 < 1 + C := by linarith
  have hfrac : C / (1 + C) ≤ 1 :=
    (div_le_one₀ hden).2 (by linarith)
  linarith

lemma momentQuotient_eq_replacementBase_pow (C : ℝ) (total : ℕ) :
    (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ total =
      replacementBase C ^ total := by
  rw [← div_pow]
  rfl

/-- Sharp heterogeneous all-upper product bound.  No homogeneous-binomial
shortcut is used: every exact selected total keeps its exact product mass,
and those masses are summed only after the fixed-total estimate. -/
theorem boundedAllUpperTail_product_bound
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬(upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    (∑ ell : ∀ c, State c,
        if boundedAllUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) ≤
      replacementBase C ^ cut := by
  rw [sum_boundedAllUpperTail_eq_sum_fixedTotal]
  calc
    (∑ total ∈ Finset.range (bound + 1),
      if cut ≤ total then
        ∑ ell : ∀ c, State c,
          if fixedTotalUpperTail upper lower total total ell then
            productPointMass weight ell else 0
      else 0) ≤
        ∑ total ∈ Finset.range (bound + 1),
          exactPairTotalMass weight upper lower total *
            (if cut ≤ total then replacementBase C ^ total else 0) := by
      apply Finset.sum_le_sum
      intro total _
      by_cases hcut : cut ≤ total
      · rw [if_pos hcut, if_pos hcut]
        rw [← momentQuotient_eq_replacementBase_pow]
        simpa only [mul_div_assoc] using
          (fixedTotalUpperTail_product_bound weight upper lower hweight
            hdisjoint hC hratio total total)
      · simp [hcut]
    _ ≤ replacementBase C ^ cut := by
      apply sum_exactPairTotalMass_mul_cost_le weight upper lower
        hweight hnorm bound
        (fun total ↦ if cut ≤ total then replacementBase C ^ total else 0)
      · exact pow_nonneg (replacementBase_nonneg hC) cut
      · intro total _
        by_cases hcut : cut ≤ total
        · rw [if_pos hcut]
          exact pow_le_pow_of_le_one (replacementBase_nonneg hC)
            (replacementBase_le_one hC) hcut
        · simp [hcut, pow_nonneg (replacementBase_nonneg hC) cut]

/-- At the canonical ratio `C ≤ 4/3`, the replacement base is at most
`11/14`, already strictly below one. -/
lemma replacementBase_le_elevenFourteenths
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 4 / 3) :
    replacementBase C ≤ (11 / 14 : ℝ) := by
  unfold replacementBase
  have hden : 0 < 1 + C := by linarith
  have hfrac : C / (1 + C) ≤ (4 / 7 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

theorem boundedAllUpperTail_product_bound_four_thirds
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (cut bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬(upper c v ∧ lower c v))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 4 / 3)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    (∑ ell : ∀ c, State c,
        if boundedAllUpperTail upper lower cut bound ell then
          productPointMass weight ell else 0) ≤
      (11 / 14 : ℝ) ^ cut := by
  refine (boundedAllUpperTail_product_bound weight upper lower cut bound
    hweight hnorm hdisjoint hC0 hratio).trans ?_
  exact pow_le_pow_left₀ (replacementBase_nonneg hC0)
    (replacementBase_le_elevenFourteenths hC0 hC) cut

/-! ## Global disjoint replacement summation -/

/-- Abstract path-level seam for HLOZ's `B_η` construction.  The checked
finite algebra above supplies the factor `q`.  A concrete instantiation must
still construct each replacement event, prove the atomwise source-to-
replacement comparison, and prove that the replacement events are pairwise
disjoint.  Those pathwise facts are deliberately not hidden in the finite
product theorem. -/
structure GlobalDisjointReplacementCertificate
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞) where
  sourceAtom : Index → Set Omega
  replacement : Index → Set Omega
  source_subset : source ⊆ ⋃ z, sourceAtom z
  atom_le : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z)
  measurable_replacement : ∀ z, MeasurableSet (replacement z)
  disjoint_replacement : Pairwise fun z w ↦
    Disjoint (replacement z) (replacement w)

/-- Exact per-atom product identity used to construct `atom_le`.  The source
and replacement products retain the same external stopped-trace factor; the
finite `I₀/I₁` theorem compares only their coordinate masses. -/
structure ReplacementAtomProductCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (source replacement : Set Omega) (q : ℝ) where
  sourceProductMass : ℝ
  replacementProductMass : ℝ
  commonExternalFactor : ℝ
  source_eq : mu.real source =
    sourceProductMass * commonExternalFactor
  replacement_eq : mu.real replacement =
    replacementProductMass * commonExternalFactor
  product_bound : sourceProductMass ≤ q * replacementProductMass
  q_nonneg : 0 ≤ q
  replacementProductMass_nonneg : 0 ≤ replacementProductMass
  commonExternalFactor_nonneg : 0 ≤ commonExternalFactor

theorem measure_le_of_replacementAtomProductCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (source replacement : Set Omega) (q : ℝ)
    (cert : ReplacementAtomProductCertificate
      mu source replacement q) :
    mu source ≤ ENNReal.ofReal q * mu replacement := by
  have hreal : mu.real source ≤ q * mu.real replacement := by
    rw [cert.source_eq, cert.replacement_eq]
    calc
      cert.sourceProductMass * cert.commonExternalFactor ≤
          (q * cert.replacementProductMass) * cert.commonExternalFactor :=
        mul_le_mul_of_nonneg_right cert.product_bound
          cert.commonExternalFactor_nonneg
      _ = q * (cert.replacementProductMass * cert.commonExternalFactor) := by
        ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top mu source),
    ← ENNReal.ofReal_toReal (measure_ne_top mu replacement),
    ← ENNReal.ofReal_mul cert.q_nonneg]
  exact ENNReal.ofReal_mono hreal

/-- Assemble the global certificate from exact per-atom product identities.
Consequently the concrete HLOZ layer need not state `atom_le` separately. -/
def globalDisjointReplacementCertificateOfAtomProducts
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (source : Set Omega) (sourceAtom replacement : Index → Set Omega)
    (q : ℝ)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (hdisjoint : Pairwise fun z w ↦ Disjoint (replacement z) (replacement w))
    (atom : ∀ z, ReplacementAtomProductCertificate
      mu (sourceAtom z) (replacement z) q) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source (ENNReal.ofReal q) where
  sourceAtom := sourceAtom
  replacement := replacement
  source_subset := hsource
  atom_le := fun z ↦ measure_le_of_replacementAtomProductCertificate
    mu (sourceAtom z) (replacement z) q (atom z)
  measurable_replacement := hmeasurable
  disjoint_replacement := hdisjoint

/-- Global disjoint summation keeps exactly one copy of the finite product
factor. -/
theorem measure_le_mul_univ_of_globalDisjointReplacementCertificate
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞)
    (cert : GlobalDisjointReplacementCertificate
      (Index := Index) mu source q) :
    mu source ≤ q * mu Set.univ := by
  calc
    mu source ≤ mu (⋃ z, cert.sourceAtom z) := measure_mono cert.source_subset
    _ ≤ ∑' z, mu (cert.sourceAtom z) := measure_iUnion_le _
    _ ≤ ∑' z, q * mu (cert.replacement z) :=
      ENNReal.tsum_le_tsum cert.atom_le
    _ = q * ∑' z, mu (cert.replacement z) := ENNReal.tsum_mul_left
    _ = q * mu (⋃ z, cert.replacement z) := by
      rw [measure_iUnion cert.disjoint_replacement cert.measurable_replacement]
    _ ≤ q * mu Set.univ := by
      apply mul_le_mul_of_nonneg_left
      · exact measure_mono
          (Set.subset_univ (⋃ z : Index, cert.replacement z))
      · exact bot_le

/-- Probability-measure form used by the shell-zero screen. -/
theorem measure_le_of_globalDisjointReplacementCertificate
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (q : ℝ≥0∞)
    (cert : GlobalDisjointReplacementCertificate
      (Index := Index) mu source q) :
    mu source ≤ q := by
  simpa using
    measure_le_mul_univ_of_globalDisjointReplacementCertificate
      mu source q cert

/-- The exact coefficient delivered by the finite `I₀/I₁` comparison at the
canonical local-ratio bound. -/
noncomputable def allUpperReplacementCost (cut : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((11 / 14 : ℝ) ^ cut)

theorem measure_le_allUpperReplacementCost
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (cut : ℕ)
    (cert : GlobalDisjointReplacementCertificate
      (Index := Index) mu source (allUpperReplacementCost cut)) :
    mu source ≤ allUpperReplacementCost cut :=
  measure_le_of_globalDisjointReplacementCertificate
    mu source (allUpperReplacementCost cut) cert

/-! ## Automatic HLOZ rate and summability -/

/-- Exact exponential rate of the canonical replacement base. -/
noncomputable def shellZeroReplacementRate : ℝ :=
  -Real.log (11 / 14 : ℝ)

lemma shellZeroReplacementRate_pos : 0 < shellZeroReplacementRate := by
  unfold shellZeroReplacementRate
  exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))

lemma elevenFourteenths_pow_eq_exp (n : ℕ) :
    (11 / 14 : ℝ) ^ n =
      Real.exp (-shellZeroReplacementRate * (n : ℝ)) := by
  have hpos : (0 : ℝ) < 11 / 14 := by norm_num
  rw [show (11 / 14 : ℝ) = Real.exp (Real.log (11 / 14 : ℝ)) by
    rw [Real.exp_log hpos]]
  rw [← Real.exp_nat_mul]
  congr 1
  unfold shellZeroReplacementRate
  ring

/-- Real form of the shell-zero coefficient at the HLOZ initial budget. -/
noncomputable def shellZeroReplacementRealCost (m : ℕ) : ℝ :=
  (11 / 14 : ℝ) ^ (initialBudget48 m + 1)

lemma shellZeroReplacementRealCost_nonneg (m : ℕ) :
    0 ≤ shellZeroReplacementRealCost m := by
  unfold shellZeroReplacementRealCost
  positivity

/-- The integer initial budget pays one full squared-logarithmic exponent. -/
theorem shellZeroReplacementRealCost_le_exp_neg_log_sq (m : ℕ) :
    shellZeroReplacementRealCost m ≤
      Real.exp
        (-shellZeroReplacementRate * Real.log (m : ℝ) ^ 2) := by
  rw [shellZeroReplacementRealCost,
    elevenFourteenths_pow_eq_exp]
  rw [Real.exp_le_exp]
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) :=
    Nat.le_ceil (Real.log (m : ℝ) ^ 2)
  have hbudget : Real.log (m : ℝ) ^ 2 ≤
      ((initialBudget48 m + 1 : ℕ) : ℝ) := by
    unfold initialBudget48
    push_cast
    linarith
  nlinarith [shellZeroReplacementRate_pos]

theorem summable_shellZeroReplacementRealCost :
    Summable shellZeroReplacementRealCost := by
  let r := shellZeroReplacementRate
  have hr : 0 < r := shellZeroReplacementRate_pos
  have hlog : Filter.Tendsto
      (fun m : ℕ ↦ Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have htarget : Summable
      (fun m : ℕ ↦ Real.exp (-r * Real.log (m : ℝ) ^ 2)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hlarge : ∀ᶠ m : ℕ in Filter.cofinite,
        2 / r ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (Filter.eventually_ge_atTop (2 / r))
    have hmpos : ∀ᶠ m : ℕ in Filter.cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using
        (Filter.eventually_gt_atTop 0)
    filter_upwards [hlarge, hmpos] with m hlogm hmpos
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -r * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hrMul : 2 ≤ r * Real.log (m : ℝ) := by
        calc
          2 = r * (2 / r) := by field_simp
          _ ≤ r * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hr.le
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
    exact Real.exp_le_exp.mpr hexponent
  apply Summable.of_nonneg_of_le
    (fun m ↦ shellZeroReplacementRealCost_nonneg m)
    (fun m ↦ shellZeroReplacementRealCost_le_exp_neg_log_sq m)
    htarget

/-- ENNReal coefficient form used directly by the global replacement
certificate. -/
noncomputable def shellZeroReplacementCost (m : ℕ) : ℝ≥0∞ :=
  allUpperReplacementCost (initialBudget48 m + 1)

theorem shellZeroReplacementCost_le_exp_neg_log_sq (m : ℕ) :
    shellZeroReplacementCost m ≤
      ENNReal.ofReal
        (Real.exp
          (-shellZeroReplacementRate * Real.log (m : ℝ) ^ 2)) := by
  apply ENNReal.ofReal_mono
  exact shellZeroReplacementRealCost_le_exp_neg_log_sq m

theorem tsum_shellZeroReplacementCost_ne_top :
    ∑' m, shellZeroReplacementCost m ≠ ∞ := by
  let f : ℕ → NNReal := fun m ↦
    ⟨shellZeroReplacementRealCost m,
      shellZeroReplacementRealCost_nonneg m⟩
  have hf : Summable (fun m : ℕ ↦ ((f m : NNReal) : ℝ)) := by
    change Summable shellZeroReplacementRealCost
    exact summable_shellZeroReplacementRealCost
  have hsum : ∑' m, ((f m : NNReal) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hf
  have hcoe : ∀ m, ((f m : NNReal) : ℝ≥0∞) =
      shellZeroReplacementCost m := by
    intro m
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← tsum_congr hcoe]
  exact hsum

end

end Erdos1165.HLOZShellZeroReplacementProduct
