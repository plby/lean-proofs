/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomGreedyDenseInputs
import ErdosProblems.Erdos186.CFP.CenteredIdentification

/-!
# The common Corollary 2.17 box for random greedy reserves

The proper bounding progression identifies the source with a coefficient
lattice only after its affine offset is normalized.  We therefore subtract
the coefficient vector of zero.  Evaluation by the GAP steps then sends the
centered coordinate of `z` exactly to `z`, so ordinary integer subset-sum
growth transfers without loss to coordinate subset sums.

The subset sums of at most `k` centered unit-box coordinates lie in the
centered coefficient box whose widths are those of the `2*k` dilation.  Its
volume is consequently the displayed volume of that dilation, which is the
quantity controlled by weak stability and the `HApproximation` estimates.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace Preprocessing

/-- The coefficient box centered at zero.  In coordinate `i` it is the
integer interval
`[-k * (width_i - 1), k * (width_i - 1)]`.
Its widths are therefore exactly those of the `2*k` dilation. -/
def centeredCoordinateAxisBox {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    AxisBox d where
  lower := fun i ↦ -((k * (P.widths i - 1) : ℕ) : ℤ)
  widths := (P.dilate (2 * k)).widths
  width_pos := (P.dilate (2 * k)).width_pos

/-- The centered coordinate box has precisely the displayed volume of the
`2*k` dilation. -/
@[simp]
theorem centeredCoordinateAxisBox_volume {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    (centeredCoordinateAxisBox P k).volume =
      (P.dilate (2 * k)).volume := by
  rfl

/-- The affine bounding-box coordinate, normalized to send zero to zero and
extended by zero away from the bounded source. -/
def centeredIdentification {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) : ℤ → LatticePoint d :=
  fun z ↦ if hz : z ∈ A then
    P.identificationMap hproper ⟨z, hz⟩ -
      P.identificationMap hproper ⟨0, hzero⟩
    else -P.identificationMap hproper ⟨0, hzero⟩

@[simp]
theorem centeredIdentification_apply {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) {z : ℤ} (hz : z ∈ A) :
    centeredIdentification P hproper hzero z =
      P.identificationMap hproper ⟨z, hz⟩ -
        P.identificationMap hproper ⟨0, hzero⟩ := by
  simp [centeredIdentification, hz]

@[simp]
theorem centeredIdentification_zero {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    centeredIdentification P hproper hzero 0 = 0 := by
  simp [centeredIdentification, hzero]

/-- On a canonical minimal box, the generic centered identification is the
centered family used by the source preprocessing and relative-index APIs. -/
theorem centeredIdentification_eq_centeredMinimalIdentificationFamily
    {A : Finset ℤ} {d : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ A) :
    centeredIdentification
        (BoundingBox.dBoundingBox A d (hproper.positive hd))
        (hproper.proper hd) hzero =
      Stability.centeredMinimalIdentificationFamily hproper d := by
  funext z
  by_cases hz : z ∈ A
  · rw [centeredIdentification_apply _ _ _ hz]
    simp only [Stability.centeredMinimalIdentificationFamily,
      Stability.minimalIdentificationFamily_apply hproper hd hz,
      Stability.minimalIdentificationFamily_apply hproper hd hzero]
  · rw [centeredIdentification]
    simp only [dif_neg hz,
      Stability.centeredMinimalIdentificationFamily]
    rw [Stability.minimalIdentificationFamily_apply hproper hd hzero]
    have hout : Stability.minimalIdentificationFamily hproper d z = 0 := by
      simp [Stability.minimalIdentificationFamily, hd, hz]
    rw [hout, zero_sub]

/-- Step evaluation removes the affine normalization and recovers the
original integer. -/
theorem stepEvaluation_centeredIdentification {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) {z : ℤ} (hz : z ∈ A) :
    stepEvaluation P.progression
        (centeredIdentification P hproper hzero z) = z := by
  rw [centeredIdentification_apply P hproper hzero hz, map_sub,
    stepEvaluation_identificationMap P hproper ⟨z, hz⟩,
    stepEvaluation_identificationMap P hproper ⟨0, hzero⟩]
  change (z - P.progression.offset 0) -
      (0 - P.progression.offset 0) = z
  omega

/-- Centering preserves injectivity on the bounded source. -/
theorem centeredIdentification_injectiveOn {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    Set.InjOn (centeredIdentification P hproper hzero) A := by
  intro x hx y hy hxy
  rw [centeredIdentification_apply P hproper hzero hx,
    centeredIdentification_apply P hproper hzero hy] at hxy
  have hraw : P.identificationMap hproper ⟨x, hx⟩ =
      P.identificationMap hproper ⟨y, hy⟩ := sub_left_injective hxy
  exact congrArg Subtype.val ((P.identificationMap_injective hproper) hraw)

/-- Every source subset-sum is the step-evaluation image of a centered
coordinate subset-sum. -/
theorem integerSubsetSums_subset_image_centeredCoordinateSubsetSums
    {A S : Finset ℤ} {d : ℕ} (hSA : S ⊆ A)
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    Greedy.subsetSums S ⊆
      (GAP.subsetSums
        (S.image (centeredIdentification P hproper hzero))).image
          (stepEvaluation P.progression) := by
  classical
  intro z hz
  obtain ⟨T, hTS, hsum⟩ :=
    SubsetSumGrowth.mem_weightedSubsetSums.mp
      (show z ∈ SubsetSumGrowth.weightedSubsetSums S id by
        simpa only [Greedy.subsetSums] using hz)
  let φ := centeredIdentification P hproper hzero
  let U := T.image φ
  have hU : U ⊆ S.image φ := Finset.image_mono φ hTS
  have hinj : Set.InjOn φ T :=
    (centeredIdentification_injectiveOn P hproper hzero).mono
      (fun x hx ↦ hSA (hTS hx))
  have hcoord : ∑ u ∈ U, u = ∑ x ∈ T, φ x := by
    exact Finset.sum_image hinj
  have hsumU : ∑ u ∈ U, u ∈ GAP.subsetSums (S.image φ) :=
    GAP.mem_subsetSums_iff.mpr ⟨U, hU, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨∑ u ∈ U, u, hsumU, ?_⟩
  rw [hcoord, map_sum]
  calc
    ∑ x ∈ T, stepEvaluation P.progression (φ x) =
        ∑ x ∈ T, x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact stepEvaluation_centeredIdentification P hproper hzero
        (hSA (hTS hx))
    _ = z := by simpa only [id_eq] using hsum

/-- In particular, centered coordinate subset sums are at least as numerous
as the ordinary integer subset sums. -/
theorem card_integerSubsetSums_le_centeredCoordinateSubsetSums
    {A S : Finset ℤ} {d : ℕ} (hSA : S ⊆ A)
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    (Greedy.subsetSums S).card ≤
      (GAP.subsetSums
        (S.image (centeredIdentification P hproper hzero))).card := by
  calc
    (Greedy.subsetSums S).card ≤
        ((GAP.subsetSums
          (S.image (centeredIdentification P hproper hzero))).image
            (stepEvaluation P.progression)).card :=
      Finset.card_le_card
        (integerSubsetSums_subset_image_centeredCoordinateSubsetSums
          hSA P hproper hzero)
    _ ≤ (GAP.subsetSums
          (S.image (centeredIdentification P hproper hzero))).card :=
      Finset.card_image_le

/-- A centered source coordinate has absolute value at most one less than
the corresponding coefficient width. -/
theorem abs_centeredIdentification_apply_le {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) {z : ℤ} (hz : z ∈ A) (i : Fin d) :
    |centeredIdentification P hproper hzero z i| ≤
      ((P.progression.widths i - 1 : ℕ) : ℤ) := by
  rw [centeredIdentification_apply P hproper hzero hz]
  simp only [Pi.sub_apply, P.identificationMap_apply]
  have hzlt := (P.progression.coordinateMap hproper
    ⟨BoundingBox.intPoint z, P.bounds ⟨z, hz⟩⟩ i).isLt
  have h0lt := (P.progression.coordinateMap hproper
    ⟨BoundingBox.intPoint 0, P.bounds ⟨0, hzero⟩⟩ i).isLt
  have hzle : (P.progression.coordinateMap hproper
      ⟨BoundingBox.intPoint z, P.bounds ⟨z, hz⟩⟩ i : ℕ) ≤
      P.progression.widths i - 1 := by omega
  have h0le : (P.progression.coordinateMap hproper
      ⟨BoundingBox.intPoint 0, P.bounds ⟨0, hzero⟩⟩ i : ℕ) ≤
      P.progression.widths i - 1 := by omega
  have hzle' :
      ((P.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint z, P.bounds ⟨z, hz⟩⟩ i : ℕ) : ℤ) ≤
        (P.progression.widths i - 1 : ℕ) := by
    exact_mod_cast hzle
  have h0le' :
      ((P.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint 0, P.bounds ⟨0, hzero⟩⟩ i : ℕ) : ℤ) ≤
        (P.progression.widths i - 1 : ℕ) := by
    exact_mod_cast h0le
  have hznonneg : 0 ≤
      ((P.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint z, P.bounds ⟨z, hz⟩⟩ i : ℕ) : ℤ) := by
    exact Int.ofNat_nonneg _
  have h0nonneg : 0 ≤
      ((P.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint 0, P.bounds ⟨0, hzero⟩⟩ i : ℕ) : ℤ) := by
    exact Int.ofNat_nonneg _
  rw [abs_le]
  constructor <;> omega

/-- Subset sums of at most `k` centered source coordinates lie in the common
centered coefficient box. -/
theorem centeredCoordinateSubsetSums_subset_centeredCoordinateAxisBox
    {A S : Finset ℤ} {d k : ℕ} (hSA : S ⊆ A) (hcard : S.card ≤ k)
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    GAP.subsetSums
        (S.image (centeredIdentification P hproper hzero)) ⊆
      (centeredCoordinateAxisBox P.progression k).carrier := by
  classical
  intro x hx
  rw [AxisBox.mem_carrier_iff]
  intro i
  obtain ⟨T, hT, hsum⟩ := GAP.mem_subsetSums_iff.mp hx
  let a := P.progression.widths i - 1
  have hterm : ∀ y ∈ T, |y i| ≤ (a : ℤ) := by
    intro y hy
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp (hT hy)
    exact abs_centeredIdentification_apply_le P hproper hzero
      (hSA hzS) i
  have hTcard : T.card ≤ k := by
    calc
      T.card ≤ (S.image (centeredIdentification P hproper hzero)).card :=
        Finset.card_le_card hT
      _ ≤ S.card := Finset.card_image_le
      _ ≤ k := hcard
  have habs : |x i| ≤ (k * a : ℕ) := by
    calc
      |x i| = |∑ y ∈ T, y i| := by
        rw [← hsum]
        simp only [Finset.sum_apply]
      _ ≤ ∑ y ∈ T, |y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ T, (a : ℤ) :=
        Finset.sum_le_sum fun y hy ↦ hterm y hy
      _ = (T.card : ℤ) * a := by simp
      _ ≤ (k : ℤ) * a := by
        exact_mod_cast Nat.mul_le_mul_right a hTcard
      _ = (k * a : ℕ) := by norm_num
  change -((k * a : ℕ) : ℤ) ≤ x i ∧
    x i < -((k * a : ℕ) : ℤ) +
      (((P.progression.dilate (2 * k)).widths i : ℕ) : ℤ)
  have habs' := (abs_le.mp habs)
  have hwidth : (P.progression.dilate (2 * k)).widths i =
      2 * (k * a) + 1 := by
    simp only [GAP.dilate_widths]
    dsimp only [a]
    ring
  rw [hwidth]
  constructor
  · exact habs'.1
  ·
    push_cast
    omega

/-! ## Fixed-reference volume control -/

/-- Weak stability relative to an arbitrary fixed reference family forces
the minimal box of every accessible approximable subset to retain more than
three quarters of the fixed reference volume. -/
theorem HApproximation.three_mul_fixedReference_volume_lt_four_mul_minimalBox
    {A B : Finset ℤ} {box : (r : ℕ) → GAP 1 r}
    {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableFor A box x D (n ^ 2))
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (V : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    3 * (box d).volume <
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume := by
  have hsteps : Stability.HasDifferencesAtMost
      (BoundingBox.dBoundingBox B d hd).progression (n ^ 2) :=
    HApproximation.minimalBox_hasDifferencesAtMost V hd hhn
      (fun z hz ↦ hA z (hBA hz)) hnumeric
  have hcontains : Stability.integerPoints B ⊆
      (BoundingBox.dBoundingBox B d hd).progression.carrier := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Stability.mem_integerPoints_iff.mp hz
    exact BoundingBox.dBoundingBox_mem_carrier B d hd ha
  by_contra hnot
  have hvolume :
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume ≤
        3 * (box d).volume := by
    omega
  exact (hstable.avoids hBA hloss V.zero_mem hd hdD
    (BoundingBox.dBoundingBox B d hd).progression hsteps hvolume) hcontains

/-- The `2*h` dilation of a fixed weak-stability reference box is controlled
by the ambient set's `h`-fold sumset. -/
theorem HApproximation.fixedReference_two_mul_dilate_volume_le_ambientCard
    {A : Finset ℤ} {box : (r : ℕ) → GAP 1 r}
    {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableFor A box x D (n ^ 2))
    (V : HDimension.HApproximation A h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    ((box d).dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d) *
        (GrowthLemmas.multifoldSumset h A).card := by
  let PA := (BoundingBox.dBoundingBox A d hd).progression
  have hretains : 3 * (box d).volume < 4 * PA.volume := by
    exact HApproximation.three_mul_fixedReference_volume_lt_four_mul_minimalBox
      hstable Finset.Subset.rfl (by omega) V hd hdD hhn hA hnumeric
  have hlower := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le V hd
  change (scaleNum * h) ^ d * PA.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h A).card at hlower
  have hh : 0 < h := V.scale_pos.trans_le V.scale_le
  have hbase : 2 * h + 1 ≤ 3 * h := by omega
  have hscale : h ^ d ≤ (scaleNum * h) ^ d := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h V.scaleNum_pos
  have hvol := (box d).volume_dilate_le (2 * h)
  have hthree : 3 * ((box d).dilate (2 * h)).volume <
      (4 * (6 * scaleDen) ^ d) *
        (GrowthLemmas.multifoldSumset h A).card := by
    calc
      3 * ((box d).dilate (2 * h)).volume ≤
          3 * ((2 * h + 1) ^ d * (box d).volume) :=
        Nat.mul_le_mul_left 3 hvol
      _ ≤ 3 * (3 * h) ^ d * (box d).volume := by
        have hp : (2 * h + 1) ^ d ≤ (3 * h) ^ d :=
          Nat.pow_le_pow_left hbase d
        nlinarith
      _ < 4 * (3 * h) ^ d * PA.volume := by
        have hm := Nat.mul_lt_mul_of_pos_right hretains
          (pow_pos (Nat.mul_pos (by omega : 0 < 3) hh) d)
        nlinarith
      _ ≤ 4 * 3 ^ d * (2 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h A).card := by
        have hhPA : h ^ d * PA.volume ≤
            (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h A).card :=
          (Nat.mul_le_mul_right PA.volume hscale).trans hlower
        have hm := Nat.mul_le_mul_left (4 * 3 ^ d) hhPA
        simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm
      _ = (4 * (6 * scaleDen) ^ d) *
          (GrowthLemmas.multifoldSumset h A).card := by
        have hsix : 3 ^ d * (2 * scaleDen) ^ d =
            (6 * scaleDen) ^ d := by
          rw [← mul_pow]
          congr 1
          ring
        calc
          4 * 3 ^ d * (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h A).card =
            4 * (3 ^ d * (2 * scaleDen) ^ d) *
              (GrowthLemmas.multifoldSumset h A).card := by ring
          _ = _ := by rw [hsix]
  omega

/-- Rank-flexible fixed-reference estimate.  Here the fixed boxes are the
minimal boxes of an outer source `W`; an inner stable set `A ⊆ W` may use
rank `d`, while the accessible set `B` may use a different rank `e`. -/
theorem HApproximation.fixedMinimalReference_two_mul_dilate_volume_le
    {W A B : Finset ℤ} {x D n h d e scaleNum scaleDen : ℕ}
    (hAW : A ⊆ W)
    (hstable : Stability.WeaklyStableFor A
      (Stability.minimalBoxFamily W) x D (n ^ 2))
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (VA : HDimension.HApproximation A h d scaleNum scaleDen)
    (VB : HDimension.HApproximation B h e scaleNum scaleDen)
    (hd : 0 < d) (he : 0 < e) (hdD : d ≤ D) (heD : e ≤ D)
    (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericA :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d)
    (hnumericB :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e) :
    (((BoundingBox.dBoundingBox W d hd).progression).dilate
        (2 * h)).volume ≤
      (16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
  have hambient :
      (((BoundingBox.dBoundingBox W d hd).progression).dilate
          (2 * h)).volume ≤
        (4 * (6 * scaleDen) ^ d) *
          (GrowthLemmas.multifoldSumset h A).card := by
    simpa only [Stability.minimalBoxFamily_eq_dBoundingBox W hd] using
      HApproximation.fixedReference_two_mul_dilate_volume_le_ambientCard
        hstable VA hd hdD hhn hA hnumericA
  have hcanonical : Stability.WeaklyStableMinimalFor A x D n :=
    Greedy.weaklyStableMinimalFor_of_fixed_minimalBox hAW hstable
  have hdensity :
      3 * (GrowthLemmas.multifoldSumset h A).card <
        4 * (4 * scaleDen) ^ e *
          (GrowthLemmas.multifoldSumset h B).card :=
    HApproximation.three_mul_card_reference_multifoldSumset_lt
      hcanonical hBA hloss VB he heD hhn hA hnumericB
  calc
    (((BoundingBox.dBoundingBox W d hd).progression).dilate
        (2 * h)).volume ≤
        (4 * (6 * scaleDen) ^ d) *
          (GrowthLemmas.multifoldSumset h A).card := hambient
    _ ≤ (4 * (6 * scaleDen) ^ d) *
        (4 * (4 * scaleDen) ^ e *
          (GrowthLemmas.multifoldSumset h B).card) := by
      gcongr
      exact (Nat.le_mul_of_pos_left _ (by omega : 0 < 3)).trans hdensity.le
    _ = (16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by ring

/-- The fixed common-box dilation is bounded by the actual positive dyadic
threshold of a stable source.  Accessible subsets may have a different
`HApproximation` rank; the displayed constant is uniform over ranks at most
`D`. -/
theorem HApproximation.fixedMinimalReference_dilate_volume_le_positiveDyadicThreshold
    {W S : Finset ℤ}
    {deletionBudget D n level d scaleNum scaleDen : ℕ}
    (hSW : insert 0 S ⊆ W) (hzeroS : 0 ∉ S)
    (hstable : Stability.WeaklyStableFor (insert 0 S)
      (Stability.minimalBoxFamily W) deletionBudget D (n ^ 2))
    (VA : HDimension.HApproximation
      (insert 0 S) (2 ^ level) d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hfoldn : 2 ^ level ≤ n)
    (hinterval : ∀ z ∈ insert 0 S, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericA :
      (2 * scaleDen) ^ d * (2 ^ level + 1) ^ (d - 1) <
        (scaleNum * 2 ^ level) ^ d)
    (haccessible : ∀ B : Finset ℤ, B ⊆ S →
      S.card ≤ B.card + deletionBudget →
      ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
        ∃ VB : HDimension.HApproximation
            (insert 0 B) (2 ^ level) e scaleNum scaleDen,
          (2 * scaleDen) ^ e * (2 ^ level + 1) ^ (e - 1) <
            (scaleNum * 2 ^ level) ^ e) :
    (((BoundingBox.dBoundingBox W d hd).progression).dilate
        (2 * 2 ^ level)).volume ≤
      (32 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) *
        Greedy.positiveDyadicThreshold S deletionBudget level := by
  obtain ⟨B, hBS, hBcard, hBmin⟩ :=
    Greedy.exists_largeSubset_card_multifold_eq_minimum
      S deletionBudget (2 ^ level)
  obtain ⟨e, he, heD, VB, hnumericB⟩ :=
    haccessible B hBS hBcard
  have hzeroB : 0 ∉ B := fun h ↦ hzeroS (hBS h)
  have hinsertBS : insert 0 B ⊆ insert 0 S :=
    Finset.insert_subset_insert 0 hBS
  have hinsertCard : (insert 0 S).card ≤
      (insert 0 B).card + deletionBudget := by
    rw [Finset.card_insert_of_notMem hzeroS,
      Finset.card_insert_of_notMem hzeroB]
    omega
  have hvolume :=
    HApproximation.fixedMinimalReference_two_mul_dilate_volume_le
      hSW hstable hinsertBS hinsertCard VA VB hd he hdD heD hfoldn
      hinterval hnumericA hnumericB
  have hpowSix : (6 * scaleDen) ^ d ≤ (6 * scaleDen) ^ D := by
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 6) VA.scaleDen_pos) hdD
  have hpowFour : (4 * scaleDen) ^ e ≤ (4 * scaleDen) ^ D := by
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 4) VB.scaleDen_pos) heD
  have hminimum :=
    Greedy.minimumMultifoldCardinality_le_two_mul_positiveDyadicThreshold
      S deletionBudget level
  calc
    (((BoundingBox.dBoundingBox W d hd).progression).dilate
        (2 * 2 ^ level)).volume ≤
        (16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
          (GrowthLemmas.multifoldSumset (2 ^ level) (insert 0 B)).card :=
      hvolume
    _ = (16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
          Greedy.minimumMultifoldCardinality S deletionBudget (2 ^ level) := by
      rw [hBmin]
    _ ≤ (16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) *
          Greedy.minimumMultifoldCardinality S deletionBudget (2 ^ level) := by
      gcongr
    _ ≤ (16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) *
          (2 * Greedy.positiveDyadicThreshold S deletionBudget level) := by
      gcongr
    _ = (32 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) *
          Greedy.positiveDyadicThreshold S deletionBudget level := by ring

end Preprocessing

namespace RandomPartition

/-- A genuine first crossing gives the full integer threshold in centered
bounding-box coordinates.  There is no loss from the coordinate passage. -/
theorem positiveDyadicThreshold_le_card_centeredGreedySubsetSums
    {W S : Finset ℤ} {d deletionBudget steps level : ℕ}
    (hSW : S ⊆ W)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hsteps : steps ≤ S.card)
    (hcross : Greedy.dyadicBinStart S deletionBudget steps level < steps) :
    Greedy.positiveDyadicThreshold S deletionBudget level ≤
      (GAP.subsetSums
        ((Greedy.selected S steps).image
          (Preprocessing.centeredIdentification P hproper hzero))).card := by
  calc
    Greedy.positiveDyadicThreshold S deletionBudget level ≤
        (Greedy.sums S
          (Greedy.dyadicBinStart S deletionBudget steps level)).card :=
      Greedy.threshold_le_at_firstCrossing_of_lt hcross
    _ ≤ (Greedy.sums S steps).card :=
      Greedy.card_sums_mono hcross.le hsteps
    _ ≤ (GAP.subsetSums
        ((Greedy.selected S steps).image
          (Preprocessing.centeredIdentification P hproper hzero))).card := by
      exact Preprocessing.card_integerSubsetSums_le_centeredCoordinateSubsetSums
        ((Greedy.selected_subset S steps).trans hSW) P hproper hzero

/-- The selected coordinate reserve is contained in every coordinate image
of a completed source reserve. -/
theorem coordinateGreedyReserve_subset_coordinateCompletedColorReserve
    {A : Finset ℤ} {d q steps : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (completion : Fin (q + 1) → Finset ℤ)
    (phi : ℤ → LatticePoint d) (i : Fin (q + 1)) :
    coordinateGreedyReserve A c steps phi i ⊆
      coordinateCompletedColorReserve A c steps completion phi i := by
  exact Finset.image_mono phi Finset.subset_union_left

/-- Exact common-box inputs for the completed random greedy reserves in
centered coordinates.  The geometric estimate enters only through the
displayed comparison between the common box volume and the actual dyadic
threshold; the first crossing and completion transport are discharged here. -/
theorem centeredCompletedReserves_denseBoxInputs_of_firstCrossing
    {W A : Finset ℤ} {d q deletionBudget steps level k cNum cDen : ℕ}
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hAW : A ⊆ W)
    (c : {a // a ∈ A} → Fin (q + 1))
    (completion : Fin (q + 1) → Finset ℤ)
    (hsteps : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) deletionBudget
        steps level < steps)
    (hcompletedCard : ∀ i,
      (completedColorSet A c steps completion i).card ≤ k)
    (hcompletedSubset : ∀ i,
      completedColorSet A c steps completion i ⊆ W)
    (hvolume : ∀ i,
      cNum * (Preprocessing.centeredCoordinateAxisBox P.progression k).volume ≤
        cDen * Greedy.positiveDyadicThreshold
          (integerColorClass A c i) deletionBudget level) :
    (∀ i, GAP.subsetSums
        (coordinateCompletedColorReserve A c steps completion
          (Preprocessing.centeredIdentification P hproper hzero) i) ⊆
      (Preprocessing.centeredCoordinateAxisBox P.progression k).carrier) ∧
    (∀ i, cNum *
        (Preprocessing.centeredCoordinateAxisBox P.progression k).volume ≤
      cDen * (GAP.subsetSums
        (coordinateCompletedColorReserve A c steps completion
          (Preprocessing.centeredIdentification P hproper hzero) i)).card) := by
  let phi := Preprocessing.centeredIdentification P hproper hzero
  let selected : Fin (q + 1) → Finset (LatticePoint d) :=
    coordinateGreedyReserve A c steps phi
  let completed : Fin (q + 1) → Finset (LatticePoint d) :=
    coordinateCompletedColorReserve A c steps completion phi
  apply denseBoxFamilyInputs_of_selected_subset_completed
    (Preprocessing.centeredCoordinateAxisBox P.progression k)
    selected completed
    (fun i ↦ Greedy.positiveDyadicThreshold
      (integerColorClass A c i) deletionBudget level)
  · intro i
    exact coordinateGreedyReserve_subset_coordinateCompletedColorReserve
      c completion phi i
  · intro i
    exact Preprocessing.centeredCoordinateSubsetSums_subset_centeredCoordinateAxisBox
      (hcompletedSubset i) (hcompletedCard i) P hproper hzero
  · intro i
    exact positiveDyadicThreshold_le_card_centeredGreedySubsetSums
      ((integerColorClass_subset A c i).trans hAW) P hproper hzero
      (hsteps i) (hcross i)
  · exact hvolume

end RandomPartition

end

end Erdos186.CFP
