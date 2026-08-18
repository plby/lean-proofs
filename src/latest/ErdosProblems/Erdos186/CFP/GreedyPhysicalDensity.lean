/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyPhysicalTarget
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density

/-!
# Physical greedy density at a rank-flexible dyadic scale

The random colors in the CFP argument need not have a common
`HApproximation` rank.  The source comparison is instead made before taking
coordinates.  A large subset of one color has an approximation of some rank
`e`; stability makes its rank-`e` bounding box comparable with the fixed
rank-`e` box of the global core.  Consequently its `h`-fold sumset controls
the global core's `H`-fold sumset whenever `H` is at most a fixed multiple of
`h`.

This is the rank-flexible physical-cardinality estimate needed before the
single final centered coordinate map is chosen.
-/

namespace Erdos186.CFP

noncomputable section

open GrowthLemmas

namespace Preprocessing

/-- A rank-`e` approximation of a large subset of a stable color controls a
larger-fold sumset of the entire reference core.  The approximation rank may
vary with the color; the displayed coefficient is uniform for `e ≤ D`.

The factor `M + 1` absorbs the endpoint in the displayed-volume estimate for
the `H`-dilation. -/
theorem HApproximation.card_global_multifoldSumset_le_rankFlexible_inner
    {W A B : Finset ℤ}
    {x D n h H M e scaleNum scaleDen : ℕ}
    (hAW : A ⊆ W)
    (hstable : Stability.WeaklyStableFor A
      (Stability.minimalBoxFamily W) x D (n ^ 2))
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (V : HDimension.HApproximation B h e scaleNum scaleDen)
    (he : 0 < e) (heD : e ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e)
    (hHM : H ≤ M * h) :
    (multifoldSumset H W).card ≤
      (4 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
        (multifoldSumset h B).card := by
  let PW := (BoundingBox.dBoundingBox W e he).progression
  let PB := (BoundingBox.dBoundingBox B e he).progression
  have hcontainsW : W ⊆ BiluFreiman.integerCarrier PW := by
    intro z hz
    apply BiluFreiman.mem_integerCarrier_iff.mpr
    change BoundingBox.intPoint z ∈ PW.carrier
    exact BoundingBox.dBoundingBox_mem_carrier W e he hz
  have hsumset : multifoldSumset H W ⊆
      BiluFreiman.integerCarrier (PW.dilate H) :=
    HDimension.multifoldSumset_subset_integerCarrier_dilate PW hcontainsW
  have hglobalUpper : (multifoldSumset H W).card ≤
      (H + 1) ^ e * PW.volume := by
    calc
      (multifoldSumset H W).card ≤
          (BiluFreiman.integerCarrier (PW.dilate H)).card :=
        Finset.card_le_card hsumset
      _ = (PW.dilate H).carrier.card :=
        BiluFreiman.card_integerCarrier _
      _ ≤ (PW.dilate H).volume := (PW.dilate H).card_carrier_le_volume
      _ ≤ (H + 1) ^ e * PW.volume := PW.volume_dilate_le H
  have hretains : 3 * PW.volume < 4 * PB.volume := by
    simpa only [PW, PB,
      Stability.minimalBoxFamily_eq_dBoundingBox W he] using
      HApproximation.three_mul_fixedReference_volume_lt_four_mul_minimalBox
        hstable hBA hloss V he heD hhn hA hnumeric
  have hPW : PW.volume ≤ 4 * PB.volume := by
    calc
      PW.volume ≤ 3 * PW.volume := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 4 * PB.volume := hretains.le
  have hlower := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le V he
  change (scaleNum * h) ^ e * PB.volume ≤
      (2 * scaleDen) ^ e * (multifoldSumset h B).card at hlower
  have hh : 0 < h := V.scale_pos.trans_le V.scale_le
  have hHbase : H + 1 ≤ (M + 1) * h := by
    nlinarith
  have hscale : h ^ e ≤ (scaleNum * h) ^ e := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h V.scaleNum_pos
  have hhPB : h ^ e * PB.volume ≤
      (2 * scaleDen) ^ e * (multifoldSumset h B).card :=
    (Nat.mul_le_mul_right PB.volume hscale).trans hlower
  have hMpow : (M + 1) ^ e ≤ (M + 1) ^ D := by
    exact Nat.pow_le_pow_right (by omega) heD
  have hdenpow : (2 * scaleDen) ^ e ≤ (2 * scaleDen) ^ D := by
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 2) V.scaleDen_pos) heD
  calc
    (multifoldSumset H W).card ≤ (H + 1) ^ e * PW.volume :=
      hglobalUpper
    _ ≤ ((M + 1) * h) ^ e * (4 * PB.volume) := by gcongr
    _ = 4 * (M + 1) ^ e * (h ^ e * PB.volume) := by
      rw [mul_pow]
      ring
    _ ≤ 4 * (M + 1) ^ e *
        ((2 * scaleDen) ^ e * (multifoldSumset h B).card) := by
      gcongr
    _ ≤ (4 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
        (multifoldSumset h B).card := by
      have hcoeff :
          4 * (M + 1) ^ e * (2 * scaleDen) ^ e ≤
            4 * (M + 1) ^ D * (2 * scaleDen) ^ D := by gcongr
      simpa only [mul_assoc] using
        Nat.mul_le_mul_right (multifoldSumset h B).card hcoeff

/-- Uniform threshold form of
`card_global_multifoldSumset_le_rankFlexible_inner`.  The minimizing subset
in `positiveDyadicThreshold` is supplied its own (possibly color-dependent)
approximation rank. -/
theorem HApproximation.card_global_multifoldSumset_le_positiveDyadicThreshold
    {W A : Finset ℤ}
    {x D n level H M scaleNum scaleDen : ℕ}
    (hAW : insert 0 A ⊆ W) (hzeroA : 0 ∉ A)
    (hstable : Stability.WeaklyStableFor (insert 0 A)
      (Stability.minimalBoxFamily W) x D (n ^ 2))
    (hfoldn : 2 ^ level ≤ n)
    (hinterval : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (n : ℤ))
    (haccessible : ∀ B : Finset ℤ, B ⊆ A →
      A.card ≤ B.card + x →
      ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
        ∃ V : HDimension.HApproximation
            (insert 0 B) (2 ^ level) e scaleNum scaleDen,
          (2 * scaleDen) ^ e * (2 ^ level + 1) ^ (e - 1) <
            (scaleNum * 2 ^ level) ^ e)
    (hHM : H ≤ M * 2 ^ level) :
    (multifoldSumset H W).card ≤
      (8 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
        Greedy.positiveDyadicThreshold A x level := by
  obtain ⟨B, hBA, hBcard, hBmin⟩ :=
    Greedy.exists_largeSubset_card_multifold_eq_minimum
      A x (2 ^ level)
  obtain ⟨e, he, heD, V, hnumeric⟩ := haccessible B hBA hBcard
  have hzeroB : 0 ∉ B := fun hz ↦ hzeroA (hBA hz)
  have hinsertBA : insert 0 B ⊆ insert 0 A :=
    Finset.insert_subset_insert 0 hBA
  have hinsertCard : (insert 0 A).card ≤
      (insert 0 B).card + x := by
    rw [Finset.card_insert_of_notMem hzeroA,
      Finset.card_insert_of_notMem hzeroB]
    omega
  have hglobal :=
    HApproximation.card_global_multifoldSumset_le_rankFlexible_inner
      hAW hstable hinsertBA hinsertCard V he heD hfoldn hinterval
      hnumeric hHM
  have hminimum :=
    Greedy.minimumMultifoldCardinality_le_two_mul_positiveDyadicThreshold
      A x level
  rw [hBmin] at hglobal
  calc
    (multifoldSumset H W).card ≤
        (4 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
          Greedy.minimumMultifoldCardinality A x (2 ^ level) := hglobal
    _ ≤ (4 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
        (2 * Greedy.positiveDyadicThreshold A x level) := by gcongr
    _ = (8 * (M + 1) ^ D * (2 * scaleDen) ^ D) *
        Greedy.positiveDyadicThreshold A x level := by ring

/-- The final global approximation converts a lower bound for one physical
target into density in the single centered coordinate box used by all
colors. -/
theorem HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget
    {W : Finset ℤ} {x D n H d scaleNum scaleDen coefficient target : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor W x D n)
    (V : HDimension.HApproximation W H d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hHn : H ≤ n)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (H + 1) ^ (d - 1) <
        (scaleNum * H) ^ d)
    (hphysical : (multifoldSumset H W).card ≤ coefficient * target) :
    (Preprocessing.centeredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d hd).progression H).volume ≤
      (4 * (6 * scaleDen) ^ D * coefficient) * target := by
  have hvolume := HApproximation.two_mul_dilate_volume_le_indexBound_mul_card
    hstable (B := W) Finset.Subset.rfl (by omega) V hd hdD hHn hinterval
      hnumeric
  have hpow : (6 * scaleDen) ^ d ≤ (6 * scaleDen) ^ D := by
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 6) V.scaleDen_pos) hdD
  rw [Preprocessing.centeredCoordinateAxisBox_volume]
  calc
    ((BoundingBox.dBoundingBox W d hd).progression.dilate (2 * H)).volume ≤
        (4 * (6 * scaleDen) ^ d) * (multifoldSumset H W).card := hvolume
    _ ≤ (4 * (6 * scaleDen) ^ D) * (coefficient * target) := by
      gcongr
    _ = (4 * (6 * scaleDen) ^ D * coefficient) * target := by ring

end Preprocessing

namespace Greedy

/-- The common physical target obtained by dividing an ambient cardinality
by a fixed positive comparison coefficient. -/
def physicalDensityTarget (ambientCard coefficient : ℕ) : ℕ :=
  ambientCard / coefficient

/-- Division preserves an upper threshold once the ambient quantity is
bounded by `coefficient * threshold`. -/
theorem physicalDensityTarget_le_of_le_mul
    {ambientCard coefficient threshold : ℕ}
    (hcoefficient : 0 < coefficient)
    (hambient : ambientCard ≤ coefficient * threshold) :
    physicalDensityTarget ambientCard coefficient ≤ threshold := by
  exact Nat.div_le_of_le_mul hambient

/-- Once the ambient cardinality is at least the fixed coefficient, division
loses at most a factor of two. -/
theorem ambientCard_le_two_mul_physicalDensityTarget
    {ambientCard coefficient : ℕ}
    (hcoefficient : 0 < coefficient)
    (hlarge : coefficient ≤ ambientCard) :
    ambientCard ≤
      2 * coefficient * physicalDensityTarget ambientCard coefficient := by
  have htargetPos : 0 < ambientCard / coefficient :=
    Nat.div_pos hlarge hcoefficient
  have hmod : ambientCard % coefficient < coefficient :=
    Nat.mod_lt ambientCard hcoefficient
  have hdecomp : ambientCard % coefficient +
      coefficient * (ambientCard / coefficient) = ambientCard := by
    exact Nat.mod_add_div ambientCard coefficient
  simp only [physicalDensityTarget]
  nlinarith

end Greedy

namespace RandomPartition

/-- All original color classes reach one common physical target, although
the approximation ranks used to prove this may vary with the color.  The
target is the global `H`-fold cardinality divided by the uniform comparison
coefficient. -/
theorem exists_common_physicalTargetRun_of_rankFlexible_threshold
    {W A : Finset ℤ}
    {q x D n H M cap scaleNum scaleDen : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (level : Fin (q + 1) → ℕ)
    (hzeroA : 0 ∉ A) (hAW : insert 0 A ⊆ W)
    (hcap : ∀ i, cap ≤ (integerColorClass A c i).card)
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) x cap (level i) < cap)
    (hstable : ∀ i, Stability.WeaklyStableFor
      (anchoredColorClass A c i) (Stability.minimalBoxFamily W)
        x D (n ^ 2))
    (hfoldn : ∀ i, 2 ^ level i ≤ n)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (haccessible : ∀ i, ∀ B : Finset ℤ,
      B ⊆ integerColorClass A c i →
      (integerColorClass A c i).card ≤ B.card + x →
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
        ∃ V : HDimension.HApproximation
            (insert 0 B) (2 ^ level i) e scaleNum scaleDen,
          (2 * scaleDen) ^ e * (2 ^ level i + 1) ^ (e - 1) <
            (scaleNum * 2 ^ level i) ^ e)
    (hscaleDen : 0 < scaleDen)
    (hHM : ∀ i, H ≤ M * 2 ^ level i)
    (hlarge :
      8 * (M + 1) ^ D * (2 * scaleDen) ^ D ≤
        (GrowthLemmas.multifoldSumset H W).card) :
    ∃ target : ℕ, ∃ run : ∀ i, Greedy.PhysicalTargetRun
        (integerColorClass A c i) cap target,
      (GrowthLemmas.multifoldSumset H W).card ≤
        2 * (8 * (M + 1) ^ D * (2 * scaleDen) ^ D) * target ∧
      target = Greedy.physicalDensityTarget
        (GrowthLemmas.multifoldSumset H W).card
        (8 * (M + 1) ^ D * (2 * scaleDen) ^ D) := by
  let coefficient := 8 * (M + 1) ^ D * (2 * scaleDen) ^ D
  let ambientCard := (GrowthLemmas.multifoldSumset H W).card
  let target := Greedy.physicalDensityTarget ambientCard coefficient
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) (pow_pos (by omega) D))
      (pow_pos (Nat.mul_pos (by omega) hscaleDen) D)
  have hrun : ∀ i, Greedy.PhysicalTargetRun
      (integerColorClass A c i) cap target := by
    intro i
    let S := integerColorClass A c i
    have hzeroS : 0 ∉ S := by
      intro hz
      exact hzeroA (integerColorClass_subset A c i hz)
    have hanchoredW : insert 0 S ⊆ W := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hAW (by simp)
      · exact hAW (Finset.mem_insert_of_mem
          (integerColorClass_subset A c i hz))
    have hthreshold :=
      Preprocessing.HApproximation.card_global_multifoldSumset_le_positiveDyadicThreshold
        hanchoredW hzeroS (hstable i) (hfoldn i)
        (fun z hz ↦ hinterval z (hanchoredW hz))
        (haccessible i) (hHM i)
    have htargetThreshold : target ≤
        Greedy.positiveDyadicThreshold S x (level i) := by
      apply Greedy.physicalDensityTarget_le_of_le_mul hcoefficient
      simpa only [ambientCard, coefficient] using hthreshold
    have hthresholdEnd : Greedy.positiveDyadicThreshold S x (level i) ≤
        (Greedy.sums S cap).card := by
      have hat : Greedy.positiveDyadicThreshold S x (level i) ≤
          (Greedy.sums S (Greedy.dyadicBinStart S x cap (level i))).card :=
        Greedy.threshold_le_at_firstCrossing_of_lt (hcross i)
      exact hat.trans (Greedy.card_sums_mono (hcross i).le (hcap i))
    exact Greedy.physicalTargetRun S cap target (hcap i)
      (htargetThreshold.trans hthresholdEnd)
  refine ⟨target, hrun, ?_, rfl⟩
  apply Greedy.ambientCard_le_two_mul_physicalDensityTarget hcoefficient
  simpa only [ambientCard, coefficient] using hlarge

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.HApproximation.card_global_multifoldSumset_le_rankFlexible_inner
