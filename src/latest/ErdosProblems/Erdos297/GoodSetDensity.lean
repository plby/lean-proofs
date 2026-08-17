/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos297.SmoothDensity
import ErdosProblems.Erdos297.FactorDensity
import ErdosProblems.Erdos297.GoodFactorization

/-!
# Density of the concrete good set for Erdős Problem 297

This file joins the three density estimates used in the Liu--Sawhney lower
bound.  The set `sourceGoodDenominators N` consists of the denominators in
`[M,N]` which are prime-power smooth at `S` and obey both factorization
cutoffs.  Its complement in the full denominator interval `[1,N]` has size
`o(N)`.  In particular, the good set eventually contains at least `89N/100`
elements (and hence at least `N^0.95` elements).
-/

namespace Erdos297.GoodSetDensity

open Filter Finset Real Asymptotics
open scoped ArithmeticFunction.Omega Topology

noncomputable section

open Erdos297
open Erdos297.GoodFactorization

attribute [local instance] Classical.propDecidable

/-- The concrete good denominator set used in the source lower bound. -/
def sourceGoodDenominators (N : ℕ) : Finset ℕ :=
  goodDenominators N (M N) (S N)

/-- The denominators in `[1,N]` deleted when passing to the source good set. -/
def deletedSourceDenominators (N : ℕ) : Finset ℕ :=
  Icc 1 N \ sourceGoodDenominators N

/-- The `M` defined in `Parameters` is exactly the lower endpoint used in
`SmoothDensity`. -/
lemma lowerEndpoint_eq_M (N : ℕ) :
    SmoothDensity.liuDenominatorLowerEndpoint N = M N := by
  rfl

/-- The `S` defined in `Parameters` is exactly the smoothness cutoff used in
`SmoothDensity`. -/
lemma primePowerCutoff_eq_S (N : ℕ) :
    SmoothDensity.liuPrimePowerCutoff N = S N := by
  rfl

@[simp] lemma sourceGoodDenominators_eq (N : ℕ) :
    sourceGoodDenominators N = goodDenominators N (M N) (S N) := rfl

@[simp] lemma deletedSourceDenominators_eq (N : ℕ) :
    deletedSourceDenominators N =
      Icc 1 N \ goodDenominators N (M N) (S N) := rfl

lemma sourceGoodDenominators_subset_Icc (N : ℕ) :
    sourceGoodDenominators N ⊆ Icc (M N) N :=
  goodDenominators_subset_Icc N (M N) (S N)

lemma sourceGoodDenominators_subset_denominators {N : ℕ} (hM : 1 ≤ M N) :
    sourceGoodDenominators N ⊆ Icc 1 N := by
  exact (sourceGoodDenominators_subset_Icc N).trans (Icc_subset_Icc_left hM)

lemma sourceGoodDenominator_pos {N n : ℕ} (hM : 1 ≤ M N)
    (hn : n ∈ sourceGoodDenominators N) : 0 < n :=
  goodDenominator_pos hM hn

/-- The initial segment excluded by the lower endpoint has negligible size. -/
theorem natM_isLittleO :
    (fun N : ℕ ↦ (M N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hlarge := tendsto_logLogLogScale.eventually_ge_atTop (ε⁻¹ ^ 2)
  filter_upwards [hlarge, eventually_pos_scales] with N hLLL hpos
  rcases hpos with ⟨hNpos, hL, hLL, hLLLpos⟩
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)]
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) := Real.sqrt_pos.2 hLLLpos
  have heinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hsqrt : ε⁻¹ ≤ Real.sqrt (logLogLogScale N) := by
    rw [← Real.sqrt_sq heinv.le]
    exact Real.sqrt_le_sqrt hLLL
  have hMnonneg : 0 ≤ MReal N :=
    div_nonneg hNpos.le (Real.sqrt_nonneg _)
  calc
    (M N : ℝ) ≤ MReal N := Nat.floor_le hMnonneg
    _ = (N : ℝ) / Real.sqrt (logLogLogScale N) := rfl
    _ ≤ ε * (N : ℝ) := by
      rw [div_le_iff₀ hsqrtpos]
      have hmul : ε * ε⁻¹ ≤
          ε * Real.sqrt (logLogLogScale N) :=
        mul_le_mul_of_nonneg_left hsqrt hε.le
      rw [mul_inv_cancel₀ hε.ne'] at hmul
      nlinarith [mul_le_mul_of_nonneg_left hmul hNpos.le]

/-- Every deleted denominator is either below `M`, nonsmooth, or violates one
of the two factorization cutoffs. -/
lemma deletedSourceDenominators_subset_exceptions (N : ℕ) :
    deletedSourceDenominators N ⊆
      Ico 1 (M N) ∪ SmoothDensity.nonsmoothNumbersUpTo N ∪
        FactorDensity.exponentExceptional N ∪
          FactorDensity.factorExceptional N := by
  intro n hn
  rcases mem_sdiff.mp hn with ⟨hnIcc, hnGood⟩
  by_cases hnM : M N ≤ n
  · have hnot : ¬ (Erdos285.PrimePowers.PrimePowerSmooth (S N) n ∧
        maxPrimeExponent n ≤ exponentBound N ∧ Ω n ≤ factorBound N) := by
      intro h
      exact hnGood (mem_goodDenominators.mpr
        ⟨hnM, (mem_Icc.mp hnIcc).2, h.1, h.2.1, h.2.2⟩)
    rcases not_and_or.mp hnot with hsmooth | hrest
    · simp only [mem_union]
      exact Or.inl (Or.inl (Or.inr (by
        simp only [SmoothDensity.nonsmoothNumbersUpTo, mem_filter]
        refine ⟨hnIcc, ?_⟩
        change ¬ Erdos285.PrimePowers.PrimePowerSmooth
          (SmoothDensity.liuPrimePowerCutoff N) n
        rw [primePowerCutoff_eq_S]
        exact hsmooth)))
    · rcases not_and_or.mp hrest with hexp | hfactor
      · simp only [mem_union]
        exact Or.inl (Or.inr (by
          simp only [FactorDensity.exponentExceptional, mem_filter]
          exact ⟨hnIcc, Nat.lt_of_not_ge hexp⟩))
      · simp only [mem_union]
        exact Or.inr (by
          simp only [FactorDensity.factorExceptional, mem_filter]
          exact ⟨hnIcc, Nat.lt_of_not_ge hfactor⟩)
  · simp only [mem_union]
    exact Or.inl (Or.inl (Or.inl
      (mem_Ico.mpr ⟨(mem_Icc.mp hnIcc).1, Nat.lt_of_not_ge hnM⟩)))

/-- The exact complement of the concrete good set in `[1,N]` has cardinality
`o(N)`. -/
theorem deletedSourceDenominators_card_isLittleO :
    (fun N : ℕ ↦ ((deletedSourceDenominators N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  have hM := (Asymptotics.isLittleO_iff.mp natM_isLittleO) hε4
  have hsmooth := (Asymptotics.isLittleO_iff.mp
    SmoothDensity.nonsmoothNumbersUpTo_card_isLittleO) hε4
  have hexp := (Asymptotics.isLittleO_iff.mp
    FactorDensity.exponentExceptional_isLittleO) hε4
  have hfactor := (Asymptotics.isLittleO_iff.mp
    FactorDensity.factorExceptional_isLittleO) hε4
  filter_upwards [hM, hsmooth, hexp, hfactor] with N hMN hsmoothN hexpN hfactorN
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)] at hMN hsmoothN hexpN hfactorN ⊢
  have hcardNat : (deletedSourceDenominators N).card ≤
      (Ico 1 (M N)).card +
        (SmoothDensity.nonsmoothNumbersUpTo N).card +
        (FactorDensity.exponentExceptional N).card +
        (FactorDensity.factorExceptional N).card := by
    have hsub := Finset.card_le_card (deletedSourceDenominators_subset_exceptions N)
    have h₁ := Finset.card_union_le (Ico 1 (M N))
      (SmoothDensity.nonsmoothNumbersUpTo N)
    have h₂ := Finset.card_union_le
      (Ico 1 (M N) ∪ SmoothDensity.nonsmoothNumbersUpTo N)
      (FactorDensity.exponentExceptional N)
    have h₃ := Finset.card_union_le
      (Ico 1 (M N) ∪ SmoothDensity.nonsmoothNumbersUpTo N ∪
        FactorDensity.exponentExceptional N)
      (FactorDensity.factorExceptional N)
    omega
  have hinitial : ((Ico 1 (M N)).card : ℝ) ≤ (M N : ℝ) := by
    have hinitialNat : (Ico 1 (M N)).card ≤ M N := by
      simpa using Finset.card_le_card
        (show Ico 1 (M N) ⊆ range (M N) by
          intro n hn
          exact mem_range.mpr (mem_Ico.mp hn).2)
    exact_mod_cast hinitialNat
  have hcard : ((deletedSourceDenominators N).card : ℝ) ≤
      (M N : ℝ) +
        (SmoothDensity.nonsmoothNumbersUpTo N).card +
        (FactorDensity.exponentExceptional N).card +
        (FactorDensity.factorExceptional N).card := by
    have hcardCast : ((deletedSourceDenominators N).card : ℝ) ≤
        ((Ico 1 (M N)).card : ℝ) +
          (SmoothDensity.nonsmoothNumbersUpTo N).card +
          (FactorDensity.exponentExceptional N).card +
          (FactorDensity.factorExceptional N).card := by
      exact_mod_cast hcardNat
    linarith
  calc
    ((deletedSourceDenominators N).card : ℝ) ≤
        (M N : ℝ) +
          (SmoothDensity.nonsmoothNumbersUpTo N).card +
          (FactorDensity.exponentExceptional N).card +
          (FactorDensity.factorExceptional N).card := hcard
    _ ≤ (ε / 4) * (N : ℝ) + (ε / 4) * (N : ℝ) +
        (ε / 4) * (N : ℝ) + (ε / 4) * (N : ℝ) := by linarith
    _ = ε * (N : ℝ) := by ring

/-- The complement estimate, exposed directly with the source's
`goodDenominators` expression. -/
theorem goodDenominators_complement_card_isLittleO :
    (fun N : ℕ ↦
      (((Icc 1 N \ goodDenominators N (M N) (S N)).card : ℕ) : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [deletedSourceDenominators, sourceGoodDenominators] using
    deletedSourceDenominators_card_isLittleO

/-- Eventually the concrete good set is a subset of the available
denominators `[1,N]`. -/
theorem eventually_sourceGoodDenominators_subset_denominators :
    ∀ᶠ N : ℕ in atTop, sourceGoodDenominators N ⊆ Icc 1 N := by
  filter_upwards [FactorDensity.tendsto_nat_M_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))]
    with N hM
  exact sourceGoodDenominators_subset_denominators (by exact_mod_cast hM)

/-- Every member of the concrete source good set is eventually positive. -/
theorem eventually_sourceGoodDenominators_pos :
    ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ sourceGoodDenominators N, 0 < n := by
  filter_upwards [FactorDensity.tendsto_nat_M_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with N hM n hn
  exact sourceGoodDenominator_pos (by exact_mod_cast hM) hn

/-- The source good set eventually contains at least `89N/100` elements. -/
theorem eventually_sourceGoodDenominators_card_ge :
    ∀ᶠ N : ℕ in atTop,
      ((89 : ℝ) / 100) * N ≤ (sourceGoodDenominators N).card := by
  have hsmall := (Asymptotics.isLittleO_iff.mp
    deletedSourceDenominators_card_isLittleO)
      (show (0 : ℝ) < 11 / 100 by norm_num)
  filter_upwards [hsmall, eventually_sourceGoodDenominators_subset_denominators]
      with N hdeleted hsub
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)] at hdeleted
  have hcover : Icc 1 N ⊆
      sourceGoodDenominators N ∪ deletedSourceDenominators N := by
    intro n hn
    by_cases hgood : n ∈ sourceGoodDenominators N
    · exact mem_union_left _ hgood
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hn, hgood⟩)
  have hcardNat : (Icc 1 N).card ≤
      (sourceGoodDenominators N).card + (deletedSourceDenominators N).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hcard : (N : ℝ) ≤
      (sourceGoodDenominators N).card + (deletedSourceDenominators N).card := by
    simpa using (show ((Icc 1 N).card : ℝ) ≤
      (sourceGoodDenominators N).card + (deletedSourceDenominators N).card by
        exact_mod_cast hcardNat)
  linarith

/-- The `89%` estimate in the unrepackaged source notation. -/
theorem eventually_goodDenominators_card_ge :
    ∀ᶠ N : ℕ in atTop,
      ((89 : ℝ) / 100) * N ≤
        ((goodDenominators N (M N) (S N)).card : ℝ) := by
  simpa only [sourceGoodDenominators] using
    eventually_sourceGoodDenominators_card_ge

/-- A slightly stronger, source-convenient cardinal bound: eventually the
good set has at least `N^0.9999` elements. -/
theorem eventually_almostOnePower_le_sourceGoodDenominators_card :
    ∀ᶠ N : ℕ in atTop,
      almostOnePower N ≤ ((sourceGoodDenominators N).card : ℝ) := by
  filter_upwards [eventually_sourceGoodDenominators_card_ge,
    eventually_almostOnePower_le_natS, eventually_nat_scale_chain] with N hcard hS hchain
  calc
    almostOnePower N ≤ (S N : ℝ) := hS
    _ ≤ (M N : ℝ) := hchain.1.trans hchain.2.1
    _ ≤ (N : ℝ) / 10 := hchain.2.2
    _ ≤ ((89 : ℝ) / 100) * N := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    _ ≤ (sourceGoodDenominators N).card := hcard

/-- In particular, the concrete good set eventually has at least `N^0.95`
elements, the convenient power-size hypothesis used in the local limit. -/
theorem eventually_nineteenTwentiethPower_le_sourceGoodDenominators_card :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((19 : ℝ) / 20) ≤
        ((sourceGoodDenominators N).card : ℝ) := by
  filter_upwards [eventually_almostOnePower_le_sourceGoodDenominators_card,
    eventually_ge_atTop (1 : ℕ)] with N hcard hN
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (by norm_num : (19 : ℝ) / 20 ≤ (9999 : ℝ) / 10000)).trans hcard

/-- The `N^0.95` estimate in the unrepackaged source notation. -/
theorem eventually_nineteenTwentiethPower_le_goodDenominators_card :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((19 : ℝ) / 20) ≤
        ((goodDenominators N (M N) (S N)).card : ℝ) := by
  simpa only [sourceGoodDenominators] using
    eventually_nineteenTwentiethPower_le_sourceGoodDenominators_card

/-- The lower endpoint itself also satisfies the `N^0.95` range condition
eventually. -/
theorem eventually_nineteenTwentiethPower_le_M :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((19 : ℝ) / 20) ≤ (M N : ℝ) := by
  filter_upwards [eventually_almostOnePower_le_natS,
    eventually_nat_scale_chain, eventually_ge_atTop (1 : ℕ)] with N hS hchain hN
  calc
    (N : ℝ) ^ ((19 : ℝ) / 20) ≤
        (N : ℝ) ^ ((9999 : ℝ) / 10000) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
    _ = almostOnePower N := by rfl
    _ ≤ (S N : ℝ) := hS
    _ ≤ (M N : ℝ) := hchain.1.trans hchain.2.1

end

end Erdos297.GoodSetDensity

#print axioms Erdos297.GoodSetDensity.goodDenominators_complement_card_isLittleO
#print axioms Erdos297.GoodSetDensity.eventually_nineteenTwentiethPower_le_goodDenominators_card
