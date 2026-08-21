import ErdosProblems.Erdos239.External.Erdos67.MRGSA10ToA9Central
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TwoBlockAtypicalLargeScalar
import ErdosProblems.Erdos239.External.Erdos67.MRTTypicalReduction

/-!
# Removing the canonical two-block restriction from an A.10 prefix bound

The A.10 reconstruction controls the coefficient restricted to integers
having a prime factor in each selected block.  This file returns to the
ordinary sharp prefix by charging the omitted summands once to the genuine
MRT atypical set.  The loss is its density, with no block-count factor.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- On positive integers up to `N`, the finite-Halász coefficient for the
MRT two-block predicates is exactly restriction to the MRT typical set. -/
theorem finiteHalaszTypicalCoefficient_twoBlock_eq_ite_mem_typical
    {f : ℕ → ℂ} {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    finiteHalaszTypicalCoefficient f
        (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) n =
      if n ∈ typicalFactorizationSet {I₁, I₂} N then f n else 0 := by
  have htyp :
      (HasPrimeFactor
          (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) n ∧
        HasPrimeFactor
          (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ ¬mrTwoBlockFirst I₁ p) n) ↔
        HasTypicalFactorization {I₁, I₂} n := by
    rw [hasPrimeFactor_not_outside_and_first_iff I₁ I₂ hn,
      hasPrimeFactor_not_outside_and_not_first_iff hdisj hn]
    constructor
    · rintro ⟨h₁, h₂⟩ I hI
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI
      rcases hI with rfl | rfl
      · exact h₁
      · exact h₂
    · intro h
      exact ⟨h I₁ (by simp), h I₂ (by simp)⟩
  unfold finiteHalaszTypicalCoefficient
  by_cases h : HasTypicalFactorization {I₁, I₂} n
  · have h' := htyp.mpr h
    simp [h', mem_typicalFactorizationSet, hn.ne', hnN, h]
  · have h' : ¬(HasPrimeFactor
          (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) n ∧
        HasPrimeFactor
          (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ ¬mrTwoBlockFirst I₁ p) n) :=
      fun hh ↦ h (htyp.mp hh)
    simp [h', mem_typicalFactorizationSet, hnN, h]

/-- Removing the two-block restriction from one positive prefix costs at
most the cardinality of the corresponding atypical set. -/
theorem norm_positivePrefixSum_sub_finiteHalaszTypicalCoefficient_twoBlock_le
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    (N : ℕ) :
    ‖positivePrefixSum f N -
        positivePrefixSum
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ ≤
      (atypicalFactorizationSet {I₁, I₂} N).card := by
  classical
  have hsum (a : ℕ → ℂ) :
      positivePrefixSum a N = ∑ n ∈ Finset.Ioc 0 N, a n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  rw [hsum, hsum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Ioc 0 N,
        (f n - finiteHalaszTypicalCoefficient f
          (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) n)‖ ≤
        ∑ n ∈ Finset.Ioc 0 N,
          ‖f n - finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 N,
          if n ∈ atypicalFactorizationSet {I₁, I₂} N then (1 : ℝ)
          else 0 := by
      apply Finset.sum_le_sum
      intro n hnmem
      have hn : 0 < n := (Finset.mem_Ioc.mp hnmem).1
      have hnN : n ≤ N := (Finset.mem_Ioc.mp hnmem).2
      rw [finiteHalaszTypicalCoefficient_twoBlock_eq_ite_mem_typical
        hdisj hn hnN]
      have hatyp := mem_atypicalFactorizationSet_iff_not_mem_typical_of_bounds
        (blocks := {I₁, I₂}) hn hnN
      by_cases htyp : n ∈ typicalFactorizationSet {I₁, I₂} N
      · simp [htyp, hatyp]
      · simp [htyp, hatyp.mpr htyp, hbound n hn]
    _ = (atypicalFactorizationSet {I₁, I₂} N).card := by
      have hfilter :
          (Finset.Ioc 0 N).filter
              (fun n ↦ n ∈ atypicalFactorizationSet {I₁, I₂} N) =
            atypicalFactorizationSet {I₁, I₂} N := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · exact fun h ↦ h.2
        · intro h
          have hrange := (mem_atypicalFactorizationSet.mp h)
          exact ⟨⟨by omega, hrange.2.1⟩, h⟩
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp

/-- Density form of prefix unrestriction. -/
theorem norm_positivePrefixMean_sub_finiteHalaszTypicalCoefficient_twoBlock_le
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {N : ℕ} (hN : 0 < N) {rho : ℝ}
    (hbad : ((atypicalFactorizationSet {I₁, I₂} N).card : ℝ) ≤
      rho * N) :
    ‖positivePrefixMean f N -
        positivePrefixMean
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ ≤ rho := by
  have hsum :=
    norm_positivePrefixSum_sub_finiteHalaszTypicalCoefficient_twoBlock_le
      hbound hdisj N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold positivePrefixMean
  rw [← sub_div, norm_div, Complex.norm_natCast]
  calc
    ‖positivePrefixSum f N -
        positivePrefixSum
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ / N ≤
        ((atypicalFactorizationSet {I₁, I₂} N).card : ℝ) / N :=
      div_le_div_of_nonneg_right hsum hNR.le
    _ ≤ rho := (div_le_iff₀ hNR).2 hbad

/-- Source-facing adapter: an A.10 bound for the whole reconstructed
two-block coefficient plus the canonical atypical density gives an ordinary
sharp-prefix bound for `f`. -/
theorem norm_positivePrefixMean_le_reconstructed_add_atypicalDensity
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {y N : ℕ} (hN : 0 < N)
    (hQ₂ : ∀ p, (¬mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬mrTwoBlockOutside I₁ I₂ p ∧ ¬mrTwoBlockFirst I₁ p) → p ≤ y)
    {E rho : ℝ}
    (hreconstructed :
      ‖positivePrefixMean
          (gsA10TwoBlockReconstructedCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y) N‖ ≤ E)
    (hbad : ((atypicalFactorizationSet {I₁, I₂} N).card : ℝ) ≤
      rho * N) :
    ‖positivePrefixMean f N‖ ≤ E + rho := by
  have hrec :
      positivePrefixMean
          (gsA10TwoBlockReconstructedCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y) N =
        positivePrefixMean
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N := by
    have hsum (a : ℕ → ℂ) :
        positivePrefixSum a N = ∑ n ∈ Finset.Ioc 0 N, a n := by
      have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
      simpa [positivePrefixSum] using h.symm
    unfold positivePrefixMean
    congr 1
    rw [hsum, hsum]
    apply Finset.sum_congr rfl
    intro n hnmem
    exact gsA10TwoBlockReconstructedCoefficient_eq_typical
      hmul (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y
        hQ₂ hQ₃ (Finset.mem_Ioc.mp hnmem).1
  have htyp :
      ‖positivePrefixMean
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ ≤ E := by
    rw [← hrec]
    exact hreconstructed
  have hdiff :=
    norm_positivePrefixMean_sub_finiteHalaszTypicalCoefficient_twoBlock_le
      hbound hdisj hN hbad
  calc
    ‖positivePrefixMean f N‖ =
        ‖positivePrefixMean
            (finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N +
          (positivePrefixMean f N -
            positivePrefixMean
              (finiteHalaszTypicalCoefficient f
                (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N)‖ := by
      congr 1
      ring
    _ ≤ ‖positivePrefixMean
          (finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ +
        ‖positivePrefixMean f N -
          positivePrefixMean
            (finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) N‖ :=
      norm_add_le _ _
    _ ≤ E + rho := add_le_add htyp hdiff

/-- Canonical-large specialization of the source-facing unrestriction
adapter.  Both selected prime blocks lie below `2^(K^2)`, so callers only
need to supply the reconstructed-prefix estimate and the genuine atypical
density. -/
theorem norm_positivePrefixMean_le_gsA10CanonicalLarge_reconstructed_add_atypicalDensity
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K) {N : ℕ} (hN : 0 < N)
    {E rho : ℝ}
    (hreconstructed :
      ‖positivePrefixMean
          (gsA10TwoBlockReconstructedCoefficient f
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            (2 ^ (K ^ 2))) N‖ ≤ E)
    (hbad : ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} N).card : ℝ) ≤ rho * N) :
    ‖positivePrefixMean f N‖ ≤ E + rho := by
  obtain ⟨hupper₁, hupper₂⟩ :=
    Erdos67.gsA10CanonicalLargeBlock_uppers_le hK
  apply norm_positivePrefixMean_le_reconstructed_add_atypicalDensity
    hmul hbound (Erdos67.disjoint_primesInBlock_gsA10CanonicalLarge hK)
    hN
  · intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans hupper₁
  · intro p hp
    have hpI₂ : p ∈ primesInBlock
        (gsA10CanonicalLargeSecondBlock K) := by
      by_contra hpI₂
      apply hp.1
      exact ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans hupper₂
  · exact hreconstructed
  · exact hbad

/-- The canonical two-block exceptional set is uniformly negligible on
every prefix in `[X,3X]` at the weak exponent used by the real-prefix
stability argument.  This is the unconditional combinatorial half of the
A.10-to-ordinary-prefix passage. -/
theorem exists_eventually_uniform_gsA10Canonical_atypicalDensity_le_one_thousandth :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ᶠ X : ℕ in Filter.atTop, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalFirstBlock K,
              gsA10CanonicalSecondBlock K} Z).card : ℝ) ≤
          C * (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) * Z := by
  obtain ⟨C, hC, S, hS, hbad⟩ :=
    Erdos67.exists_gsA10Canonical_scheduled_atypicalFactorizationSet_le_realLog_half
  refine ⟨C, hC, S, hS, ?_⟩
  refine Filter.eventually_atTop.2 ⟨max (2 ^ (16 * S)) 3, ?_⟩
  intro X hX
  intro Z hXZ _
  dsimp only
  have hcut : 2 ^ (16 * S) ≤ Z :=
    (le_max_left _ _).trans hX |>.trans hXZ
  have hbase := hbad Z hcut
  dsimp only at hbase
  have hXthree : 3 ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogX : 1 ≤ Real.log (X : ℝ) := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hXthree)
    exact Real.exp_le_exp.mp (hexp.le.trans_eq
      (Real.exp_log hXpos).symm)
  have hlogMono : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hXpos hZpos (by exact_mod_cast hXZ)
  have hhalfMono :
      (Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hlogX)
      hlogMono (by norm_num)
  have hexponent :
      (Real.log (X : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hlogX
    norm_num
  exact hbase.trans (by
    gcongr
    exact hhalfMono.trans hexponent)

/-- Uniform weak-exponent density for the repaired canonical blocks whose
first block begins above the fixed small-prime cutoff. -/
theorem exists_eventually_uniform_gsA10CanonicalLarge_atypicalDensity_le_one_thousandth :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ᶠ X : ℕ in Filter.atTop, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) * Z := by
  obtain ⟨C, hC, S, hS, hbad⟩ :=
    Erdos67.exists_gsA10CanonicalLarge_scheduled_atypicalFactorizationSet_le_realLog_half
  refine ⟨C, hC, S, hS, ?_⟩
  refine Filter.eventually_atTop.2 ⟨max (2 ^ (100 * S)) 3, ?_⟩
  intro X hX Z hXZ _
  dsimp only
  have hcut : 2 ^ (100 * S) ≤ Z :=
    (le_max_left _ _).trans hX |>.trans hXZ
  have hbase := hbad Z hcut
  dsimp only at hbase
  have hXthree : 3 ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogX : 1 ≤ Real.log (X : ℝ) := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hXthree)
    exact Real.exp_le_exp.mp (hexp.le.trans_eq
      (Real.exp_log hXpos).symm)
  have hlogMono : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hXpos hZpos (by exact_mod_cast hXZ)
  have hhalfMono :
      (Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hlogX)
      hlogMono (by norm_num)
  have hexponent :
      (Real.log (X : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hlogX
    norm_num
  exact hbase.trans (by
    gcongr
    exact hhalfMono.trans hexponent)

/-- The repaired canonical density at the exponent used after the fixed
one-unit nonpretentiousness loss. -/
theorem exists_eventually_uniform_gsA10CanonicalLarge_atypicalDensity_le_two_thousandth :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ᶠ X : ℕ in Filter.atTop, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        let K := gsA10CanonicalBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (Real.log (X : ℝ)) ^ (-1 / 2000 : ℝ) * Z := by
  obtain ⟨C, hC, S, hS, hbad⟩ :=
    exists_eventually_uniform_gsA10CanonicalLarge_atypicalDensity_le_one_thousandth
  refine ⟨C, hC, S, hS, ?_⟩
  filter_upwards [hbad, Filter.eventually_ge_atTop 3] with X hbadX hX
  intro Z hXZ hZX
  dsimp only
  have hlog : 1 ≤ Real.log (X : ℝ) := by
    have hXpos : (0 : ℝ) < X := by positivity
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    exact Real.exp_le_exp.mp (hexp.le.trans_eq
      (Real.exp_log hXpos).symm)
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock
            (gsA10CanonicalBlockExponent S Z),
          gsA10CanonicalLargeSecondBlock
            (gsA10CanonicalBlockExponent S Z)} Z).card : ℝ) ≤
        C * (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) * Z :=
      hbadX Z hXZ hZX
    _ ≤ C * (Real.log (X : ℝ)) ^ (-1 / 2000 : ℝ) * Z := by
      have hrpow :
          (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) ≤
            (Real.log (X : ℝ)) ^ (-1 / 2000 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        norm_num
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow hC.le) (by positivity)

end

end Erdos67.MRHalaszBands
