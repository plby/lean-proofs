import ErdosProblems.Erdos6.GenericOuterCollision
import Util.MaynardBFT.CandidateTransport

/-!
# A continuous good-region cutoff for the large candidate

The cutoff is one when the off-coordinate logarithmic mass is at most `6/7`
and vanishes once it reaches `7/8`.  Thus it is compatible with the continuous
outer-moment theorem and leaves a uniform positive interval in the missing
coordinate.
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def largeOuterCutoff (s : ℝ) : ℝ := min 1 (max 0 (49 - 56 * s))

def largeOuterContinuousDensity {ι : Type*} [Fintype ι]
    (t : ι → ℝ) : ℝ :=
  ∏ i, largeContinuousG (largeK * t i) ^ 2

def largeOuterIntegrand {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  largeOuterCutoff (largeCoordinateSum t) * largeOuterContinuousDensity t

def largeOuterSquaredIntegrand {ι : Type*} [Fintype ι]
    (t : ι → ℝ) : ℝ :=
  largeOuterCutoff (largeCoordinateSum t) ^ 2 *
    largeOuterContinuousDensity t

def largeInnerGoodRegion (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  BoundedGaps.Maynard.maynardCubeOf ι ∩
    {t | largeCoordinateSum t ≤ (6 : ℝ) / 7}

theorem continuous_largeOuterCutoff : Continuous largeOuterCutoff := by
  unfold largeOuterCutoff
  fun_prop

theorem continuous_largeOuterContinuousDensity
    (ι : Type*) [Fintype ι] :
    Continuous (largeOuterContinuousDensity : (ι → ℝ) → ℝ) := by
  unfold largeOuterContinuousDensity
  apply continuous_finsetProd
  intro i hi
  exact (continuous_largeContinuousG.comp
    (continuous_const.mul (continuous_apply i))).pow 2

theorem continuous_largeOuterIntegrand
    (ι : Type*) [Fintype ι] :
    Continuous (largeOuterIntegrand : (ι → ℝ) → ℝ) := by
  unfold largeOuterIntegrand
  exact (continuous_largeOuterCutoff.comp
    (by
      change Continuous (fun t : ι → ℝ => ∑ i : ι, t i)
      fun_prop)).mul
    (continuous_largeOuterContinuousDensity ι)

theorem continuous_largeOuterSquaredIntegrand
    (ι : Type*) [Fintype ι] :
    Continuous (largeOuterSquaredIntegrand : (ι → ℝ) → ℝ) := by
  unfold largeOuterSquaredIntegrand
  exact ((continuous_largeOuterCutoff.comp
    (by
      change Continuous (fun t : ι → ℝ => ∑ i : ι, t i)
      fun_prop)).pow 2).mul
    (continuous_largeOuterContinuousDensity ι)

theorem largeOuterCutoff_nonneg (s : ℝ) : 0 ≤ largeOuterCutoff s := by
  unfold largeOuterCutoff
  exact le_min (by norm_num) (le_max_left _ _)

theorem largeOuterCutoff_le_one (s : ℝ) : largeOuterCutoff s ≤ 1 := by
  unfold largeOuterCutoff
  exact min_le_left _ _

theorem largeOuterCutoff_eq_one {s : ℝ} (hs : s ≤ (6 : ℝ) / 7) :
    largeOuterCutoff s = 1 := by
  unfold largeOuterCutoff
  have h : 1 ≤ 49 - 56 * s := by linarith
  rw [max_eq_right ((by norm_num : (0 : ℝ) ≤ 1).trans h), min_eq_left h]

theorem largeOuterCutoff_eq_zero {s : ℝ} (hs : (7 : ℝ) / 8 ≤ s) :
    largeOuterCutoff s = 0 := by
  unfold largeOuterCutoff
  have h : 49 - 56 * s ≤ 0 := by linarith
  rw [max_eq_left h]
  norm_num

theorem largeOuterIntegrand_bounds
    {H : Finset ℕ} (t : H → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    0 ≤ largeOuterIntegrand t ∧ largeOuterIntegrand t ≤ 1 := by
  have hd0 : 0 ≤ largeOuterContinuousDensity t := by
    unfold largeOuterContinuousDensity
    exact Finset.prod_nonneg fun i hi => sq_nonneg _
  have hcut0 := largeOuterCutoff_nonneg (largeCoordinateSum t)
  have hcut1 := largeOuterCutoff_le_one (largeCoordinateSum t)
  have hd1 : largeOuterContinuousDensity t ≤ 1 := by
    unfold largeOuterContinuousDensity
    calc
      ∏ i : H, largeContinuousG (largeK * t i) ^ 2 ≤
          ∏ _i : H, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sq_nonneg _
        · intro i hi
          have hx : 0 ≤ largeK * t i :=
            mul_nonneg (by positivity) (ht.1 i (Set.mem_univ i)).1
          rw [largeContinuousG_eq_largeG hx]
          exact pow_le_one₀ (largeG_nonneg hx) (largeG_le_one hx)
      _ = 1 := Finset.prod_const_one
  constructor
  · exact mul_nonneg hcut0 hd0
  · exact (mul_le_mul hcut1 hd1 hd0 (by norm_num)).trans_eq (by ring)

theorem largeInnerGoodRegion_measurable
    (ι : Type*) [Fintype ι] :
    MeasurableSet (largeInnerGoodRegion ι) := by
  unfold largeInnerGoodRegion
  exact (MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Icc)).inter
      (measurableSet_Iic.preimage (measurable_largeCoordinateSum ι))

theorem badInnerRegion_productDensity_integral_le
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι,
      largeProductDensity t) ≤
      ((7 : ℝ) / 6) * (Fintype.card ι : ℝ) *
        largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
  have hleft : IntegrableOn
      (largeProductDensity : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι) :=
    (productDensity_integrableOn_cube ι).mono_set Set.diff_subset
  have hright : IntegrableOn (fun t : ι → ℝ =>
      ((7 : ℝ) / 6) *
        (largeCoordinateSum t * largeProductDensity t))
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι) :=
    by
      have hfull : IntegrableOn (fun t : ι → ℝ =>
          ((7 : ℝ) / 6) *
            (largeCoordinateSum t * largeProductDensity t))
          (BoundedGaps.Maynard.maynardCubeOf ι) :=
        (coordinateSum_mul_productDensity_integrableOn_cube ι).const_mul
          ((7 : ℝ) / 6)
      exact hfull.mono_set Set.diff_subset
  have hmeas : MeasurableSet
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι) :=
    (MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc)).diff
        (largeInnerGoodRegion_measurable ι)
  calc
    (∫ t : ι → ℝ in
        BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι,
        largeProductDensity t) ≤
        ∫ t : ι → ℝ in
          BoundedGaps.Maynard.maynardCubeOf ι \ largeInnerGoodRegion ι,
          ((7 : ℝ) / 6) *
            (largeCoordinateSum t * largeProductDensity t) := by
      apply setIntegral_mono_on hleft hright hmeas
      intro t ht
      have hsum : (6 : ℝ) / 7 < largeCoordinateSum t := by
        by_contra hnot
        exact ht.2 ⟨ht.1, le_of_not_gt hnot⟩
      nlinarith [largeProductDensity_nonneg t]
    _ ≤ ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          ((7 : ℝ) / 6) *
            (largeCoordinateSum t * largeProductDensity t) := by
      apply setIntegral_mono_set
        ((coordinateSum_mul_productDensity_integrableOn_cube ι).const_mul
          ((7 : ℝ) / 6))
      · exact (ae_restrict_mem (MeasurableSet.pi Set.countable_univ
          (fun _ _ => measurableSet_Icc))).mono (fun t ht =>
            mul_nonneg (by norm_num)
              (mul_nonneg (by
                unfold largeCoordinateSum
                exact Finset.sum_nonneg fun i hi =>
                  (ht i (Set.mem_univ i)).1)
                (largeProductDensity_nonneg t)))
      · exact Filter.Eventually.of_forall fun t ht => Set.diff_subset ht
    _ = ((7 : ℝ) / 6) * (Fintype.card ι : ℝ) *
        largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
      rw [integral_const_mul,
        integral_coordinateSum_mul_productDensity_cube]
      ring

theorem weighted_bad_inner_bound_lt_seven_eighths
    {K : ℕ} (hK2 : 2 ≤ K) {a b : ℝ} (ha : 0 < a)
    (hb : b < (3 / (4 * (K : ℝ))) * a) :
    ((7 : ℝ) / 6) * ((K - 1 : ℕ) : ℝ) * b *
        a ^ (K - 1 - 1) <
      ((7 : ℝ) / 8) * a ^ (K - 1) := by
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hK1 : 1 ≤ K := by omega
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]
    norm_num
  have hratio : ((K - 1 : ℕ) : ℝ) *
      (3 / (4 * (K : ℝ))) < (3 : ℝ) / 4 := by
    rw [hcast]
    have hden : 0 < (4 : ℝ) * (K : ℝ) := mul_pos (by norm_num) hK
    rw [show ((K : ℝ) - 1) * (3 / (4 * (K : ℝ))) =
      (((K : ℝ) - 1) * 3) / (4 * (K : ℝ)) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hfactor : 0 < ((7 : ℝ) / 6) *
      ((K - 1 : ℕ) : ℝ) * a ^ (K - 2) := by
    have : 0 < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hmoment := mul_lt_mul_of_pos_left hb hfactor
  have hpoweq : a ^ (K - 2) * a = a ^ (K - 1) := by
    have hexp : K - 1 = (K - 2) + 1 := by omega
    rw [hexp, pow_succ]
  have hratio_mul := mul_lt_mul_of_pos_right hratio
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 6)
      (pow_pos ha (K - 1)))
  have hexp : K - 1 - 1 = K - 2 := by omega
  rw [hexp]
  calc
    ((7 : ℝ) / 6) * ((K - 1 : ℕ) : ℝ) * b * a ^ (K - 2) =
        (((7 : ℝ) / 6) * ((K - 1 : ℕ) : ℝ) *
          a ^ (K - 2)) * b := by ring
    _ < (((7 : ℝ) / 6) * ((K - 1 : ℕ) : ℝ) *
          a ^ (K - 2)) * ((3 / (4 * (K : ℝ))) * a) := hmoment
    _ = (((K - 1 : ℕ) : ℝ) * (3 / (4 * (K : ℝ)))) *
          (((7 : ℝ) / 6) * a ^ (K - 1)) := by
      rw [← hpoweq]
      ring
    _ < ((3 : ℝ) / 4) *
          (((7 : ℝ) / 6) * a ^ (K - 1)) := hratio_mul
    _ = ((7 : ℝ) / 8) * a ^ (K - 1) := by ring

theorem innerGood_productDensity_integral_gt_one_eighth
    (ι : Type*) [Fintype ι]
    (hcard : Fintype.card ι = largeK - 1) :
    (∫ t : ι → ℝ in largeInnerGoodRegion ι,
      largeProductDensity t) >
      ((1 : ℝ) / 8) * largeBaseMass ^ (largeK - 1) := by
  have hbad := badInnerRegion_productDensity_integral_le ι
  rw [hcard] at hbad
  have hbad' := hbad.trans_lt
    (weighted_bad_inner_bound_lt_seven_eighths largeK_ge_two
      largeBaseMass_pos largeFirstMoment_lt_three_quarters)
  have hsubset : largeInnerGoodRegion ι ⊆
      BoundedGaps.Maynard.maynardCubeOf ι := fun t ht => ht.1
  have hsplit := setIntegral_sdiff (largeInnerGoodRegion_measurable ι)
    (productDensity_integrableOn_cube ι) hsubset
  have htotal := integral_product_largeSquareDensity_cube ι
  change (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
    largeProductDensity t) = _ at htotal
  rw [hcard] at htotal
  rw [htotal] at hsplit
  linarith

theorem largeOuterContinuousDensity_eq_productDensity_of_mem_cube
    {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    largeOuterContinuousDensity t = largeProductDensity t := by
  unfold largeOuterContinuousDensity largeProductDensity largeSquareDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [largeContinuousG_eq_largeG
    (mul_nonneg (by positivity) (ht i (Set.mem_univ i)).1)]

theorem largeOuterIntegrand_eq_productDensity_of_mem_innerGood
    {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ largeInnerGoodRegion ι) :
    largeOuterIntegrand t = largeProductDensity t := by
  unfold largeOuterIntegrand
  rw [largeOuterCutoff_eq_one ht.2,
    largeOuterContinuousDensity_eq_productDensity_of_mem_cube ht.1,
    one_mul]

theorem largeOuterSquaredIntegrand_eq_productDensity_of_mem_innerGood
    {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ largeInnerGoodRegion ι) :
    largeOuterSquaredIntegrand t = largeProductDensity t := by
  unfold largeOuterSquaredIntegrand
  rw [largeOuterCutoff_eq_one ht.2,
    largeOuterContinuousDensity_eq_productDensity_of_mem_cube ht.1]
  norm_num

theorem largeInnerGoodRegion_subset_finiteSimplex
    (H : Finset ℕ) :
    largeInnerGoodRegion H ⊆ BoundedGaps.Maynard.finiteSimplexOf H := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  exact ht.2.trans (by norm_num)

theorem integral_largeOuterIntegrand_finiteSimplex_gt_one_eighth
    (H : Finset ℕ) (hcard : Fintype.card H = largeK - 1) :
    (∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
      largeOuterIntegrand t) >
      ((1 : ℝ) / 8) * largeBaseMass ^ (largeK - 1) := by
  have hgood := innerGood_productDensity_integral_gt_one_eighth H hcard
  have heq :
      (∫ t : H → ℝ in largeInnerGoodRegion H,
        largeOuterIntegrand t) =
      ∫ t : H → ℝ in largeInnerGoodRegion H,
        largeProductDensity t := by
    apply setIntegral_congr_fun (largeInnerGoodRegion_measurable H)
    intro t ht
    exact largeOuterIntegrand_eq_productDensity_of_mem_innerGood ht
  have hint : IntegrableOn
      (largeOuterIntegrand : (H → ℝ) → ℝ)
      (BoundedGaps.Maynard.finiteSimplexOf H) :=
    (continuous_largeOuterIntegrand H).continuousOn.integrableOn_compact
      (BoundedGaps.Maynard.isCompact_finiteSimplexOf H)
  have hmono :
      (∫ t : H → ℝ in largeInnerGoodRegion H,
        largeOuterIntegrand t) ≤
      ∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
        largeOuterIntegrand t := by
    apply setIntegral_mono_set hint
    · exact (ae_restrict_mem
        (BoundedGaps.Maynard.isCompact_finiteSimplexOf H).measurableSet).mono
          (fun t ht => (largeOuterIntegrand_bounds t ht).1)
    · exact Filter.Eventually.of_forall fun t ht =>
        largeInnerGoodRegion_subset_finiteSimplex H ht
  rw [heq] at hmono
  exact hgood.trans_le hmono

theorem largeOuterSquaredIntegrand_bounds
    {H : Finset ℕ} (t : H → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    0 ≤ largeOuterSquaredIntegrand t ∧
      largeOuterSquaredIntegrand t ≤ 1 := by
  have hc0 := largeOuterCutoff_nonneg (largeCoordinateSum t)
  have hc1 := largeOuterCutoff_le_one (largeCoordinateSum t)
  have hd0 : 0 ≤ largeOuterContinuousDensity t := by
    unfold largeOuterContinuousDensity
    exact Finset.prod_nonneg fun i hi => sq_nonneg _
  have hd1 : largeOuterContinuousDensity t ≤ 1 := by
    unfold largeOuterContinuousDensity
    calc
      ∏ i : H, largeContinuousG (largeK * t i) ^ 2 ≤
          ∏ _i : H, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sq_nonneg _
        · intro i hi
          have hx : 0 ≤ largeK * t i :=
            mul_nonneg (by positivity) (ht.1 i (Set.mem_univ i)).1
          rw [largeContinuousG_eq_largeG hx]
          exact pow_le_one₀ (largeG_nonneg hx) (largeG_le_one hx)
      _ = 1 := Finset.prod_const_one
  unfold largeOuterSquaredIntegrand
  constructor
  · positivity
  · have hcSq : largeOuterCutoff (largeCoordinateSum t) ^ 2 ≤ 1 :=
      pow_le_one₀ hc0 hc1
    nlinarith [sq_nonneg (largeOuterCutoff (largeCoordinateSum t))]

theorem integral_largeOuterSquaredIntegrand_finiteSimplex_gt_one_eighth
    (H : Finset ℕ) (hcard : Fintype.card H = largeK - 1) :
    (∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
      largeOuterSquaredIntegrand t) >
      ((1 : ℝ) / 8) * largeBaseMass ^ (largeK - 1) := by
  have hgood := innerGood_productDensity_integral_gt_one_eighth H hcard
  have heq :
      (∫ t : H → ℝ in largeInnerGoodRegion H,
        largeOuterSquaredIntegrand t) =
      ∫ t : H → ℝ in largeInnerGoodRegion H,
        largeProductDensity t := by
    apply setIntegral_congr_fun (largeInnerGoodRegion_measurable H)
    intro t ht
    exact largeOuterSquaredIntegrand_eq_productDensity_of_mem_innerGood ht
  have hint : IntegrableOn
      (largeOuterSquaredIntegrand : (H → ℝ) → ℝ)
      (BoundedGaps.Maynard.finiteSimplexOf H) :=
    (continuous_largeOuterSquaredIntegrand H).continuousOn.integrableOn_compact
      (BoundedGaps.Maynard.isCompact_finiteSimplexOf H)
  have hmono :
      (∫ t : H → ℝ in largeInnerGoodRegion H,
        largeOuterSquaredIntegrand t) ≤
      ∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
        largeOuterSquaredIntegrand t := by
    apply setIntegral_mono_set hint
    · exact (ae_restrict_mem
        (BoundedGaps.Maynard.isCompact_finiteSimplexOf H).measurableSet).mono
          (fun t ht => (largeOuterSquaredIntegrand_bounds t ht).1)
    · exact Filter.Eventually.of_forall fun t ht =>
        largeInnerGoodRegion_subset_finiteSimplex H ht
  rw [heq] at hmono
  exact hgood.trans_le hmono

def largeOffFace (m : largePowerTuple) : Finset ℕ :=
  largePowerTuple.erase m.1

theorem largeOffFace_card (m : largePowerTuple) :
    (largeOffFace m).card = largeK - 1 := by
  unfold largeOffFace
  rw [Finset.card_erase_of_mem m.2, largePowerTuple_card]

theorem fintype_card_largeOffFace (m : largePowerTuple) :
    Fintype.card (largeOffFace m) = largeK - 1 := by
  simpa using largeOffFace_card m

theorem tendsto_normalizedLargeOffFaceOuterMoment
    (m : largePowerTuple) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterWeightedMoment (largeOffFace m) alpha
        largeOuterIntegrand N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterIntegrand t)) := by
  have hcardPos : 0 < (largeOffFace m).card := by
    rw [largeOffFace_card]
    have := largeK_ge_two
    omega
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcardPos
  let h0 : largeOffFace m := ⟨h, hh⟩
  exact tendsto_normalizedTupleOuterWeightedMoment h0 halpha
    (continuous_largeOuterIntegrand (largeOffFace m))
    (fun t ht => largeOuterIntegrand_bounds t ht)

theorem largeOffFaceOuterMoment_limit_gt
    (m : largePowerTuple) :
    ((1 : ℝ) / 8) * largeBaseMass ^ (largeK - 1) <
      ∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterIntegrand t := by
  exact integral_largeOuterIntegrand_finiteSimplex_gt_one_eighth
    (largeOffFace m) (fintype_card_largeOffFace m)

theorem tendsto_normalizedLargeOffFaceSquaredOuterMoment
    (m : largePowerTuple) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterWeightedMoment (largeOffFace m) alpha
        largeOuterSquaredIntegrand N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterSquaredIntegrand t)) := by
  have hcardPos : 0 < (largeOffFace m).card := by
    rw [largeOffFace_card]
    have := largeK_ge_two
    omega
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcardPos
  let h0 : largeOffFace m := ⟨h, hh⟩
  exact tendsto_normalizedTupleOuterWeightedMoment h0 halpha
    (continuous_largeOuterSquaredIntegrand (largeOffFace m))
    (fun t ht => largeOuterSquaredIntegrand_bounds t ht)

theorem largeOffFaceSquaredOuterMoment_limit_gt
    (m : largePowerTuple) :
    ((1 : ℝ) / 8) * largeBaseMass ^ (largeK - 1) <
      ∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterSquaredIntegrand t := by
  exact integral_largeOuterSquaredIntegrand_finiteSimplex_gt_one_eighth
    (largeOffFace m) (fintype_card_largeOffFace m)

theorem tendsto_normalizedLargeOffFaceMaynardSquaredOuterMoment
    (m : largePowerTuple) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterMaynardWeightedMoment (largeOffFace m) alpha
        largeOuterSquaredIntegrand N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterSquaredIntegrand t)) := by
  have hcardPos : 0 < (largeOffFace m).card := by
    rw [largeOffFace_card]
    have := largeK_ge_two
    omega
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcardPos
  let h0 : largeOffFace m := ⟨h, hh⟩
  exact tendsto_normalizedTupleOuterMaynardWeightedMoment h0 halpha
    (continuous_largeOuterSquaredIntegrand (largeOffFace m))
    (fun t ht => largeOuterSquaredIntegrand_bounds t ht)

theorem largeOuterContinuousDensity_bounds
    {H : Finset ℕ} (t : H → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    0 ≤ largeOuterContinuousDensity t ∧
      largeOuterContinuousDensity t ≤ 1 := by
  have hsq := largeOuterSquaredIntegrand_bounds t ht
  constructor
  · unfold largeOuterContinuousDensity
    exact Finset.prod_nonneg fun i hi => sq_nonneg _
  · rw [largeOuterContinuousDensity_eq_productDensity_of_mem_cube ht.1]
    unfold largeProductDensity largeSquareDensity
    calc
      (∏ i : H, largeG (largeK * t i) ^ 2) ≤
          ∏ _i : H, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sq_nonneg _
        · intro i hi
          have hx : 0 ≤ largeK * t i :=
            mul_nonneg (by positivity) (ht.1 i (Set.mem_univ i)).1
          exact pow_le_one₀ (largeG_nonneg hx) (largeG_le_one hx)
      _ = 1 := Finset.prod_const_one

theorem tendsto_normalizedLargeOffFaceMaynardDensityMoment
    (m : largePowerTuple) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterMaynardWeightedMoment (largeOffFace m) alpha
        largeOuterContinuousDensity N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf (largeOffFace m),
        largeOuterContinuousDensity t)) := by
  have hcardPos : 0 < (largeOffFace m).card := by
    rw [largeOffFace_card]
    have := largeK_ge_two
    omega
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcardPos
  let h0 : largeOffFace m := ⟨h, hh⟩
  exact tendsto_normalizedTupleOuterMaynardWeightedMoment h0 halpha
    (continuous_largeOuterContinuousDensity (largeOffFace m))
    (fun t ht => largeOuterContinuousDensity_bounds t ht)

end

end MaynardBFT.Sieve
