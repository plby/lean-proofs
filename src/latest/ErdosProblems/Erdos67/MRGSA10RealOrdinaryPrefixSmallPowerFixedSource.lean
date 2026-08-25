import ErdosProblems.Erdos67.MRGSA10SourceContourSmallPowerBaseIntegrated
import ErdosProblems.Erdos67.MRGSA10RealOrdinaryPrefixFixedSource
import ErdosProblems.Erdos67.MRGSA10SmallPowerNoncontourScalar
import ErdosProblems.Erdos67.MRRealPrefixMovingCutoff

/-!
# Real ordinary prefixes from the small-power fixed source contour

This closes the fixed-source contour, projection, Shiu secondary, and
canonical two-block unrestriction at every prefix in `[X,3X]`.  Complete
multiplicativity is retained explicitly because the current global-secondary
identity uses it.
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67.MRHalaszBands

noncomputable section

theorem eventually_smallPower_contour_structure (Nrow : ℕ) :
    ∀ᶠ Z : ℕ in atTop,
      let K := Erdos67.gsA10SmallPowerBlockExponent Z
      let y := 2 ^ (K ^ 2)
      Nrow ≤ y ∧ 2 ≤ Z / y ∧
        Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ) := by
  filter_upwards
      [Erdos67.eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent,
       Erdos67.tendsto_natLog_two_rpow_one_thousandth_atTop.eventually
        (eventually_ge_atTop (2 * Nrow : ℝ)),
       Erdos67.eventually_five_le_gsA10SmallPowerBlockExponent,
       Erdos67.eventually_four_mul_smallPowerBlockExponent_sq_le_log 1,
       Erdos67.eventually_log_pow_six_le_gsA10SmallPowerBlockCutoff]
      with Z hfloor hlarge hK hExp hlogSix
  dsimp only
  let K := Erdos67.gsA10SmallPowerBlockExponent Z
  let y := 2 ^ (K ^ 2)
  let L := Nat.log 2 Z
  have hK' : 5 ≤ K := by simpa only [K] using hK
  have hNrowK : Nrow ≤ K := by
    have hreal : (Nrow : ℝ) ≤ K := by
      have hf := hfloor
      have hl := hlarge
      dsimp only [K] at hf ⊢
      nlinarith
    exact_mod_cast hreal
  have hKy : K ≤ y := by
    have hself : K < 2 ^ K := Nat.lt_two_pow_self
    have hpow : 2 ^ K ≤ 2 ^ (K ^ 2) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    exact hself.le.trans hpow
  have hNrowy : Nrow ≤ y := hNrowK.trans hKy
  have hKsqLog : 4 * K ^ 2 ≤ L := by
    simpa only [K, L] using hExp
  have hExp' : K ^ 2 + 1 ≤ L := by
    have hKsq : 1 ≤ K ^ 2 := by nlinarith
    omega
  have hZne : Z ≠ 0 := by
    intro hzero
    subst Z
    norm_num at hExp'
  have htwoy : 2 * y ≤ Z := by
    calc
      2 * y = 2 ^ (K ^ 2 + 1) := by
        dsimp only [y]
        rw [pow_succ]
        ring
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hExp'
      _ ≤ Z := by
        dsimp only [L]
        exact Nat.pow_log_le_self 2 hZne
  have hypos : 0 < y := by positivity
  have hquot : 2 ≤ Z / y :=
    (Nat.le_div_iff_mul_le hypos).2 htwoy
  exact ⟨hNrowy, hquot, by simpa only [y, K] using hlogSix⟩

/-- The source A.10 route gives the ordinary-prefix estimate required in
the Archimedean-nonpretentious branch, uniformly over `[X,3X]`. -/
theorem exists_eventually_norm_positivePrefixMean_real_halasz_smallPower_fixedSource :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ)
        (hmul : IsMultiplicativeOnPositiveNat f),
        IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        MRArchimedeanNonpretentious f
          (Erdos67.realPrefixMovingThreshold X) (3 * X) →
        ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z‖ ≤
            C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨Cbeta, Nrow, hCbeta, hcontour⟩ :=
    exists_norm_gsA10TwoBlockSourcePerronIntegrated_div_le_smallPower_base_sub_one
  obtain ⟨Cbad, hCbad, Sblock, hSblock, hbadEvent⟩ :=
    Erdos67.exists_eventually_gsA10SmallPower_atypicalFactorizationSet_le_realLog
  let Ccont : ℝ := 2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta
  let C : ℝ := Ccont + gsA10SmallPowerNoncontourConstant + Cbad
  have hCcont : 0 ≤ Ccont := by
    dsimp only [Ccont]
    exact mul_nonneg (by norm_num)
      (gsA10SmallPowerSourceContourBaseSubOneConstant_nonneg hCbeta)
  have hC : 0 < C := by
    dsimp only [C]
    have hnon := gsA10SmallPowerNoncontourConstant_nonneg
    positivity
  refine ⟨C, hC, ?_⟩
  obtain ⟨Zbad, hbad⟩ := eventually_atTop.1 hbadEvent
  obtain ⟨Zstruct, hstruct⟩ := eventually_atTop.1
    Erdos67.eventually_gsA10SmallPowerBlock_structural
  obtain ⟨Zcontour, hcontourStruct⟩ := eventually_atTop.1
    (eventually_smallPower_contour_structure Nrow)
  obtain ⟨Zscalar, hscalar⟩ := eventually_atTop.1
    eventually_jointSource_add_shiu_smallPowerBlock_le
  filter_upwards
      [Erdos67.eventually_realPrefixMovingThreshold_sub_one_archimedean_at_prefix,
       Erdos67.eventually_one_le_realPrefixMovingThreshold,
       eventually_ge_atTop
        (max 4 (max Zbad (max Zstruct (max Zcontour Zscalar))))]
      with X htransfer hthreshold hXlarge
  intro f hmul hcomp hreal hbound harch Z hXZ hZX
  let K : ℕ := Erdos67.gsA10SmallPowerBlockExponent Z
  let y : ℕ := 2 ^ (K ^ 2)
  have hZlarge : max Zbad (max Zstruct (max Zcontour Zscalar)) ≤ Z :=
    (le_max_right 4 _).trans hXlarge |>.trans hXZ
  have hZbad : Zbad ≤ Z := (le_max_left _ _).trans hZlarge
  have hZstruct : Zstruct ≤ Z :=
    (le_max_left Zstruct (max Zcontour Zscalar)).trans
      (le_max_right Zbad _) |>.trans hZlarge
  have hZcontour : Zcontour ≤ Z :=
    (le_max_left Zcontour Zscalar).trans
      (le_max_right Zstruct _) |>.trans (le_max_right Zbad _) |>.trans hZlarge
  have hZscalar : Zscalar ≤ Z :=
    (le_max_right Zcontour Zscalar).trans
      (le_max_right Zstruct _) |>.trans (le_max_right Zbad _) |>.trans hZlarge
  have hs := hstruct Z hZstruct
  dsimp only at hs
  have hc := hcontourStruct Z hZcontour
  dsimp only at hc
  have hK : 5 ≤ K := by simpa only [K] using hs.1
  have hy : 23 ≤ y := by simpa only [y, K] using hs.2.1
  have hyZ : y ≤ Z := by simpa only [y, K] using hs.2.2.1
  have hlogZ : 1 ≤ Real.log (Z : ℝ) := hs.2.2.2.1
  have hlogy : 6 ≤ Real.log (y : ℝ) := by
    simpa only [y, K] using hs.2.2.2.2.1
  have hlogSq : Real.log (Z : ℝ) ^ 2 ≤ Z := hs.2.2.2.2.2.1
  have hprime : Erdos67.PrimeEstimates.primeReciprocals Z ≤
      Real.log (Z : ℝ) := hs.2.2.2.2.2.2.1
  have hlogFour : Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) := by
    simpa only [y, K] using hs.2.2.2.2.2.2.2
  have hNrowy : Nrow ≤ y := by simpa only [y, K] using hc.1
  have hquot : 2 ≤ Z / y := by simpa only [y, K] using hc.2.1
  have hlogSix : Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ) := by
    simpa only [y, K] using hc.2.2
  have hsmall : ∀ p ∈ gsA9SmallPrimeFinset,
      mrTwoBlockOutside (Erdos67.gsA10CanonicalLargeFirstBlock K)
        (Erdos67.gsA10CanonicalLargeSecondBlock K) p := by
    intro p hp
    have hpRaw : p < 23 ∧ p.Prime := by
      simpa only [gsA9SmallPrimeFinset, Finset.mem_filter,
        Finset.mem_range] using hp
    exact Erdos67.mrTwoBlockOutside_gsA10CanonicalLarge_of_le_twentyThree
      hK hpRaw.2 hpRaw.1.le
  have harchZ := htransfer f hbound harch Z hXZ hZX
  have hcontourZ := hcontour hmul (fun n _hn ↦ hbound n)
    (mrTwoBlockOutside (Erdos67.gsA10CanonicalLargeFirstBlock K)
      (Erdos67.gsA10CanonicalLargeSecondBlock K))
    (mrTwoBlockFirst (Erdos67.gsA10CanonicalLargeFirstBlock K))
    hsmall hNrowy (show 3 ≤ X by omega) hXZ hZX hy hyZ
    (show 4 ≤ Z by omega) hquot hlogy hlogZ hlogSq hprime hlogFour
    hlogSix hthreshold harchZ
  have hdisj := Erdos67.disjoint_primesInBlock_gsA10CanonicalLarge hK
  obtain ⟨hI₁y, hI₂y⟩ := Erdos67.gsA10CanonicalLargeBlock_uppers_le hK
  have hQ₂ : ∀ p, (¬ mrTwoBlockOutside
        (Erdos67.gsA10CanonicalLargeFirstBlock K)
        (Erdos67.gsA10CanonicalLargeSecondBlock K) p ∧
      mrTwoBlockFirst (Erdos67.gsA10CanonicalLargeFirstBlock K) p) → p ≤ y := by
    intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans (by simpa only [y] using hI₁y)
  have hQ₃ : ∀ p, (¬ mrTwoBlockOutside
        (Erdos67.gsA10CanonicalLargeFirstBlock K)
        (Erdos67.gsA10CanonicalLargeSecondBlock K) p ∧
      ¬ mrTwoBlockFirst (Erdos67.gsA10CanonicalLargeFirstBlock K) p) → p ≤ y := by
    intro p hp
    have hpI₂ : p ∈ primesInBlock
        (Erdos67.gsA10CanonicalLargeSecondBlock K) := by
      by_contra hpI₂
      exact hp.1 ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans (by simpa only [y] using hI₂y)
  have hbadZ : ((atypicalFactorizationSet
      {Erdos67.gsA10CanonicalLargeFirstBlock K,
        Erdos67.gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
      (Cbad * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ))) * Z := by
    simpa only [K] using hbad Z hZbad
  have hprefix := norm_positivePrefixMean_twoBlock_le_sourceContour_add_jointSource
    hmul hcomp (fun n hn ↦ hbound n) hdisj hy hyZ (show 2 ≤ Z by omega)
    hlogZ hlogy hprime hlogFour hQ₂ hQ₃ hcontourZ hbadZ
  have hnon := hscalar Z hZscalar
  dsimp only at hnon
  have hprefixZ : ‖positivePrefixMean f Z‖ ≤
      C * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    dsimp only [C, Ccont]
    calc
      ‖positivePrefixMean f Z‖ ≤
          2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
              (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) +
            gsA10JointMovingProjectionSourceBudget y Z +
            gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
              Real.log (Z : ℝ) +
            Cbad * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
        simpa only [K, y] using hprefix
      _ ≤
          (2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta +
              gsA10SmallPowerNoncontourConstant + Cbad) *
            (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
        have hnon' : gsA10JointMovingProjectionSourceBudget y Z +
            gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
              Real.log (Z : ℝ) ≤
            gsA10SmallPowerNoncontourConstant *
              (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
          simpa only [y, K] using hnon
        linarith
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hlogX : 1 ≤ Real.log (X : ℝ) := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ X by omega))
    exact Real.exp_le_exp.mp (hexp.le.trans_eq (Real.exp_log hXpos).symm)
  have hlogMono : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hXpos hZpos (by exact_mod_cast hXZ)
  have hrpow : (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) ≤
      (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hlogX) hlogMono (by norm_num)
  exact hprefixZ.trans
    (mul_le_mul_of_nonneg_left hrpow (by simpa only [C] using hC.le))

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_eventually_norm_positivePrefixMean_real_halasz_smallPower_fixedSource
