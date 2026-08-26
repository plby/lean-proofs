import ErdosProblems.Erdos67b.MRGSA10RealOrdinaryPrefixFixedSourceLocalDistance
import ErdosProblems.Erdos67b.MRGSA10RealOrdinaryPrefixSmallPowerFixedSource
import ErdosProblems.Erdos67b.MRRealCentralWindowDistance

/-!
# Ordinary real prefixes in the retained large-zero-distance branch
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- A retained large distance at the zero twist makes every ordinary prefix
small.  This is stronger than the far-minimizer branch needed by the real
dichotomy: the remote minimizer is not used after central-window separation.
-/
theorem exists_eventually_norm_positivePrefixMean_real_largeZero_smallPower_fixedSource :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ)
        (hmul : IsMultiplicativeOnPositiveNat f),
        IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
          pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
        ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z‖ ≤
            C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨Cbeta, Nrow, hCbeta, hprefixFinite⟩ :=
    exists_norm_positivePrefixMean_twoBlock_le_smallPower_base_sub_one_of_localDistance
  obtain ⟨Cbad, hCbad, Sblock, hSblock, hbadEvent⟩ :=
    Erdos67b.exists_eventually_gsA10SmallPower_atypicalFactorizationSet_le_realLog
  let Ccont : ℝ := 2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta
  let C : ℝ := Ccont + gsA10SmallPowerNoncontourConstant + Cbad
  have hC : 0 < C := by
    dsimp only [C, Ccont]
    have hcont :=
      gsA10SmallPowerSourceContourBaseSubOneConstant_nonneg hCbeta
    have hnon := gsA10SmallPowerNoncontourConstant_nonneg
    positivity
  refine ⟨C, hC, ?_⟩
  obtain ⟨Zbad, hbad⟩ := eventually_atTop.1 hbadEvent
  obtain ⟨Zstruct, hstruct⟩ := eventually_atTop.1
    Erdos67b.eventually_gsA10SmallPowerBlock_structural
  obtain ⟨Zcontour, hcontourStruct⟩ := eventually_atTop.1
    (eventually_smallPower_contour_structure Nrow)
  obtain ⟨Zscalar, hscalar⟩ := eventually_atTop.1
    eventually_jointSource_add_shiu_smallPowerBlock_le
  filter_upwards
      [Erdos67b.eventually_real_centralWindow_at_prefix_of_large_zero_three_mul,
       Erdos67b.eventually_one_le_realPrefixMovingThreshold,
       eventually_ge_atTop
        (max 4 (max Zbad (max Zstruct (max Zcontour Zscalar))))]
      with X hcentral hthreshold hXlarge
  intro f hmul hcomp hreal hbound hzero Z hXZ hZX
  let K : ℕ := Erdos67b.gsA10SmallPowerBlockExponent Z
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
  have hprime : Erdos67b.PrimeEstimates.primeReciprocals Z ≤
      Real.log (Z : ℝ) := hs.2.2.2.2.2.2.1
  have hlogFour : Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) := by
    simpa only [y, K] using hs.2.2.2.2.2.2.2
  have hNrowy : Nrow ≤ y := by simpa only [y, K] using hc.1
  have hquot : 2 ≤ Z / y := by simpa only [y, K] using hc.2.1
  have hlogSix : Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ) := by
    simpa only [y, K] using hc.2.2
  have hsmall : ∀ p ∈ gsA9SmallPrimeFinset,
      mrTwoBlockOutside (Erdos67b.gsA10CanonicalLargeFirstBlock K)
        (Erdos67b.gsA10CanonicalLargeSecondBlock K) p := by
    intro p hp
    have hpRaw : p < 23 ∧ p.Prime := by
      simpa only [gsA9SmallPrimeFinset, Finset.mem_filter,
        Finset.mem_range] using hp
    exact Erdos67b.mrTwoBlockOutside_gsA10CanonicalLarge_of_le_twentyThree
      hK hpRaw.2 hpRaw.1.le
  have hcentralZ : ∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
      (Erdos67b.realPrefixMovingThreshold X : ℝ) ≤
        pretentiousDistSq f (archimedeanTwist u) Z :=
    hcentral f hreal hbound hzero Z hXZ hZX
  have hdist : ∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
      (((Erdos67b.realPrefixMovingThreshold X - 1 : ℕ) : ℝ)) ≤
        pretentiousDistSq f (archimedeanTwist u) Z := by
    intro u hu
    have hsub : (((Erdos67b.realPrefixMovingThreshold X - 1 : ℕ) : ℝ)) ≤
        (Erdos67b.realPrefixMovingThreshold X : ℝ) := by
      exact_mod_cast Nat.sub_le (Erdos67b.realPrefixMovingThreshold X) 1
    exact hsub.trans (hcentralZ u hu)
  have hdisj := Erdos67b.disjoint_primesInBlock_gsA10CanonicalLarge hK
  obtain ⟨hI₁y, hI₂y⟩ := Erdos67b.gsA10CanonicalLargeBlock_uppers_le hK
  have hQ₂ : ∀ p, (¬ mrTwoBlockOutside
        (Erdos67b.gsA10CanonicalLargeFirstBlock K)
        (Erdos67b.gsA10CanonicalLargeSecondBlock K) p ∧
      mrTwoBlockFirst (Erdos67b.gsA10CanonicalLargeFirstBlock K) p) → p ≤ y := by
    intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans (by simpa only [y] using hI₁y)
  have hQ₃ : ∀ p, (¬ mrTwoBlockOutside
        (Erdos67b.gsA10CanonicalLargeFirstBlock K)
        (Erdos67b.gsA10CanonicalLargeSecondBlock K) p ∧
      ¬ mrTwoBlockFirst (Erdos67b.gsA10CanonicalLargeFirstBlock K) p) → p ≤ y := by
    intro p hp
    have hpI₂ : p ∈ primesInBlock
        (Erdos67b.gsA10CanonicalLargeSecondBlock K) := by
      by_contra hpI₂
      exact hp.1 ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans (by simpa only [y] using hI₂y)
  have hbadZ : ((atypicalFactorizationSet
      {Erdos67b.gsA10CanonicalLargeFirstBlock K,
        Erdos67b.gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
      (Cbad * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ))) * Z := by
    simpa only [K] using hbad Z hZbad
  have hprefix := hprefixFinite hmul hcomp (fun n _hn ↦ hbound n)
    hdisj hsmall hNrowy (show 3 ≤ X by omega) hXZ hZX hy hyZ
    (show 4 ≤ Z by omega) hquot hlogy hlogZ hlogSq hprime hlogFour
    hlogSix hthreshold hdist hQ₂ hQ₃ hbadZ
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

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.exists_eventually_norm_positivePrefixMean_real_largeZero_smallPower_fixedSource
