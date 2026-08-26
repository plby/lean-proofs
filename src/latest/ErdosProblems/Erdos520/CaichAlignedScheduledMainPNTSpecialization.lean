import ErdosProblems.Erdos520.CaichAlignedScheduledMainPNT
import ErdosProblems.Erdos520.CaichAlignedScheduledCleanup
import ErdosProblems.Erdos520.CaichBrunTitchmarsh

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Short-prime discharge of the selected aligned main geometry

The theorem below is the exact specialization consumed by
`CaichAlignedScheduledCleanup`: coefficient `9` for every short window and
the honest scaling constant `1200 K` for the literal near family.
-/

/-- The selected geometry needs only the displayed uniform reciprocal-prime
estimate.  This factoring keeps the geometry independent of whether that
estimate is supplied by effective PNT or by the verified Brun--Titchmarsh
sieve. -/
theorem eventually_selectedAlignedHarperMainGeometry_of_shortWindow
    (hprimeInput : ∀ A : ℕ,
      ∀ᶠ y : ℕ in atTop, ∀ {x X a b : ℕ} {z : ℝ},
        0 < z → 2 ≤ X →
        y ≤ caichLambdaLowerCutoff x X z →
        (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
        2 * X ≤ caichLambdaLowerCutoff x X z →
        caichShortWindowReciprocalMass (X : ℝ) x a b z ≤
          3 / ((X : ℝ) * Real.log (y : ℝ)))
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop,
      SelectedAlignedHarperMainGeometryAtScale
        hK hHarper q m 9 ((1200 * K : ℕ) : ℝ) ell := by
  classical
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  let A := caichAlignedEffectivePNTExponent q K
  have hprimeEvent := hprimeInput A
  rw [eventually_atTop] at hprimeEvent
  obtain ⟨Y, hprimeY⟩ := hprimeEvent
  have hbaseline := eventually_le_caichAlignedPNTBaseline Y (by omega : 1 ≤ K)
  have hfour :=
    eventually_four_mul_caichWSmoothingParameterNat_le_alignedInitial
      q m (by omega : 1 ≤ K)
  filter_upwards [eventually_ge_atTop w.clamp, hbaseline, hfour] with
    ell hclamp hbaselineEll hfourEll
  intro i hi
  have hell : 5 ≤ ell := w.five_le_clamp.trans hclamp
  have hxUpper : alignedRootExpTestPoint m i ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    rw [if_neg (by omega : ¬ell < 5)] at hi
    exact (Finset.mem_filter.mp hi).2.2
  have hxpos : 0 < alignedRootExpTestPoint m i :=
    Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  have hX := two_le_caichWSmoothingParameterNat_alignedTest
    (r := q) (by omega : 1 ≤ K) hi
  constructor
  · -- The effective-PNT short-window predicate.
    unfold SelectedAlignedHarperShortWindowBound
    intro j hj hnear z hz
    have hscaleEq : clampedAlignedScale w.clamp ell = ell :=
      clampedAlignedScale_eq_of_ge hclamp
    have hjN : j < caichAlignedFirstReachingBlock K ell
        (alignedRootExpTestPoint m i) := by
      simpa only [selectedAlignedHarperBlockCount, w, hscaleEq]
        using! Finset.mem_range.mp hj
    have hactive : alignedThinEndpoint K ell j <
        alignedRootExpTestPoint m i :=
      alignedThinEndpoint_lt_of_lt_firstReachingBlock
        (by omega) hxUpper hjN
    have hnearRatio :
        Real.log (alignedRootExpTestPoint m i : ℝ) /
            Real.log (alignedThinEndpoint K ell j : ℝ) ≤
          (ell : ℝ) ^ (100 * K) := by
      simpa only [selectedAlignedHarperNear, caichAlignedNearRatio,
        w, hscaleEq] using! hnear
    have hlogLeft : 0 < Real.log (alignedThinEndpoint K ell j : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < alignedThinEndpoint K ell j by
        exact Nat.one_lt_two.trans_le (two_le_alignedThinEndpoint K ell j)))
    have hnearProduct : Real.log (alignedRootExpTestPoint m i : ℝ) ≤
        (ell : ℝ) ^ (100 * K) *
          Real.log (alignedThinEndpoint K ell j : ℝ) :=
      (div_le_iff₀ hlogLeft).mp hnearRatio
    have hfourJ : 4 * caichWSmoothingParameterNat q
        (alignedRootExpTestPoint m i) ≤ alignedThinEndpoint K ell j :=
      (hfourEll i hi).trans
        (alignedThinEndpoint_mono K ell (Nat.zero_le j))
    have hpoly := caichAlignedNear_smoothing_polylog
      (r := q) (by omega : 1 ≤ K) hell hactive hnearProduct
    have hprime : ∀ {x' X' a b : ℕ} {z' : ℝ},
        0 < z' → 2 ≤ X' →
        caichAlignedPNTBaseline K ell j ≤
          caichLambdaLowerCutoff x' X' z' →
        (X' : ℝ) ≤
          Real.log (caichAlignedPNTBaseline K ell j : ℝ) ^ A →
        2 * X' ≤ caichLambdaLowerCutoff x' X' z' →
        caichShortWindowReciprocalMass (X' : ℝ) x' a b z' ≤
          3 / ((X' : ℝ) *
            Real.log (caichAlignedPNTBaseline K ell j : ℝ)) := by
      exact hprimeY _ (hbaselineEll j)
    have hshort := caichAlignedShortWindow_le_of_PNTBaseline
      (K := K) (L := ell) (j := j)
      (x := alignedRootExpTestPoint m i)
      (X := caichWSmoothingParameterNat q (alignedRootExpTestPoint m i))
      (A := A) (by omega : 1 ≤ K) (by omega) hxpos hX hfourJ hpoly hprime
      z
    have hz' : z ∈ Ioc
        ((alignedRootExpTestPoint m i : ℝ) /
          (alignedThinEndpoint K ell (j + 1) : ℝ))
        ((alignedRootExpTestPoint m i : ℝ) /
          (alignedThinEndpoint K ell j : ℝ)) := by
      simpa only [selectedAlignedHarperEndpoint, w, hscaleEq] using! hz
    simpa only [selectedAlignedHarperEndpoint, w, hscaleEq,
      caichWSmoothingParameterNatCast, A] using! hshort hz'
  · -- The literal near-cardinality budget.
    unfold SelectedAlignedHarperNearBudget selectedAlignedHarperNearBlocks
    let N := caichAlignedFirstReachingBlock K ell
      (alignedRootExpTestPoint m i)
    let sNear : Finset ℕ := (Finset.range N).filter
      (caichAlignedNearRatio K ell (alignedRootExpTestPoint m i))
    let sProduct : Finset ℕ := (Finset.range N).filter fun j ↦
      alignedThinEndpoint K ell j < alignedRootExpTestPoint m i ∧
        Real.log (alignedRootExpTestPoint m i : ℝ) ≤
          (ell : ℝ) ^ (100 * K) *
            Real.log (alignedThinEndpoint K ell j : ℝ)
    have hscaleEq : clampedAlignedScale w.clamp ell = ell :=
      clampedAlignedScale_eq_of_ge hclamp
    have hnearRewrite :
        (Finset.range
          (selectedAlignedHarperBlockCount hK hHarper m ell i)).filter
            (selectedAlignedHarperNear hK hHarper m ell i) = sNear := by
      apply Finset.ext
      intro j
      simp only [Finset.mem_filter, selectedAlignedHarperBlockCount,
        selectedAlignedHarperNear, w, hscaleEq, N, sNear]
    rw [hnearRewrite]
    have hsubset : sNear ⊆ sProduct := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjN : j < N := Finset.mem_range.mp hj'.1
      have hactive : alignedThinEndpoint K ell j <
          alignedRootExpTestPoint m i := by
        exact alignedThinEndpoint_lt_of_lt_firstReachingBlock
          (by omega) hxUpper (by simpa only [N] using! hjN)
      have hlogLeft : 0 < Real.log (alignedThinEndpoint K ell j : ℝ) :=
        Real.log_pos (by exact_mod_cast
          (show 1 < alignedThinEndpoint K ell j by
            exact Nat.one_lt_two.trans_le
              (two_le_alignedThinEndpoint K ell j)))
      have hproduct : Real.log (alignedRootExpTestPoint m i : ℝ) ≤
          (ell : ℝ) ^ (100 * K) *
            Real.log (alignedThinEndpoint K ell j : ℝ) :=
        (div_le_iff₀ hlogLeft).mp hj'.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hjN, hactive, hproduct⟩
    have hcard : (sNear.card : ℝ) ≤ sProduct.card := by
      exact_mod_cast Finset.card_le_card hsubset
    have hbase := card_alignedNear_mul_nine_le
      (K := K) (ell := ell) (x := alignedRootExpTestPoint m i) (N := N)
      (by omega : 1 ≤ K) hell
    have hbase' : (sProduct.card : ℝ) * 9 ≤
        ((1200 * K : ℕ) : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) := by
      simpa only [sProduct] using! hbase
    have hmul : (sNear.card : ℝ) * 9 ≤ (sProduct.card : ℝ) * 9 :=
      mul_le_mul_of_nonneg_right hcard (by norm_num)
    unfold caichAuxiliaryLogFactor
    norm_num [Nat.cast_mul]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using! hmul.trans hbase'

/-- Backwards-compatible specialization using the effective-PNT interface. -/
theorem eventually_selectedAlignedHarperMainGeometry_of_effectivePNT
    (hPNT : EffectivePrimeCountingStatement)
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop,
      SelectedAlignedHarperMainGeometryAtScale
        hK hHarper q m 9 ((1200 * K : ℕ) : ℝ) ell := by
  apply eventually_selectedAlignedHarperMainGeometry_of_shortWindow
    (fun A ↦
      eventually_caichShortWindowReciprocalMass_le_of_effectiveStatement hPNT A)
    hK hHarper q m

/-- Premise-free selected geometry from the verified Brun--Titchmarsh
sieve. -/
theorem eventually_selectedAlignedHarperMainGeometry_unconditional
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop,
      SelectedAlignedHarperMainGeometryAtScale
        hK hHarper q m 9 ((1200 * K : ℕ) : ℝ) ell := by
  apply eventually_selectedAlignedHarperMainGeometry_of_shortWindow
    (fun A ↦ eventually_caichShortWindowReciprocalMass_le_unconditional A)
    hK hHarper q m

end Problem520
end Erdos
