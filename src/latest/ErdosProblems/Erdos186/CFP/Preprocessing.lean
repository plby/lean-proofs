/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.BoundingBox
import ErdosProblems.Erdos186.CFP.Contraction
import ErdosProblems.Erdos186.CFP.DeletionEngine
import ErdosProblems.Erdos186.CFP.FiniteGroupCover
import ErdosProblems.Erdos186.CFP.HDimension
import ErdosProblems.Erdos186.CFP.Stability
import ErdosProblems.Erdos186.CFP.SubgroupPruning

/-!
# Stable-core preprocessing (CFP Lemmas 2.32 and 2.38)

This file formalizes the two finite termination arguments in the stability
preprocessing of Conlon--Fox--Pham.

* A failure of weak stability deletes only the prescribed number of points
  and contracts one minimal bounding-box volume by a factor at least `3 / 4`.
  The sum of the binary logarithms of the cubed volumes is therefore a
  strictly decreasing natural-valued potential.
* Once weak stability has been reached, a failure of robustness of the
  generated coordinate subgroups deletes only the robustness budget and
  strictly decreases the subgroup-chain rank.  This is the finite pruning
  process in CFP Lemma 2.32.

The quantitative inputs produced by CFP Lemmas 2.22 and 2.26 are represented
by their concrete `HApproximation` witnesses.  From them this file proves the
`n^2` difference bound, the weak-stability density estimate, the quotient
sumset and relative-index bounds, and finally the logarithmic subgroup-chain
bound.  The conclusions are proved by actual finite iteration; no stable
subset, accessible-index bound, or subgroup-rank certificate is assumed by
the approximation-form source lemmas.
-/

namespace Erdos186.CFP.Preprocessing

open scoped BigOperators Pointwise
open Erdos186.CFP

/-- Constant-summand notation for the generic iterated sumset. -/
abbrev constantIteratedSumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (X : Finset G) (k : ℕ) : Finset G :=
  Erdos186.CFP.iteratedSumset (fun _ ↦ X) k

/-! ## A coordinate-fibre bound for long GAP differences -/

/-- The part of a dilated integer GAP which lies in the interval `[0, h*n]`.
This is the finite set counted in CFP Lemma 2.29. -/
def dilateIntervalPart {d : ℕ} (P : GAP 1 d) (h n : ℕ) :
    Finset ℤ :=
  (BiluFreiman.integerCarrier (P.dilate h)).filter fun z ↦
    0 ≤ z ∧ z ≤ ((h * n : ℕ) : ℤ)

/-- A chosen coefficient representation; no properness is required. -/
noncomputable def chosenCoord {ambient rank : ℕ} (P : GAP ambient rank)
    (x : {x // x ∈ P.carrier}) : P.Coord :=
  Classical.choose (GAP.mem_carrier_iff.mp x.property)

@[simp]
theorem coordPoint_chosenCoord {ambient rank : ℕ} (P : GAP ambient rank)
    (x : {x // x ∈ P.carrier}) :
    P.coordPoint (chosenCoord P x) = x :=
  Classical.choose_spec (GAP.mem_carrier_iff.mp x.property)

/-- Forget one coefficient of a chosen representation of a point in the
interval part. -/
noncomputable def omitLongCoordinate {d : ℕ} (P : GAP 1 d)
    (h n : ℕ) (i : Fin d) :
    {z // z ∈ dilateIntervalPart P h n} →
      ((j : {j : Fin d // j ≠ i}) → Fin ((P.dilate h).widths j.1)) := by
  classical
  intro z j
  exact chosenCoord (P.dilate h)
    ⟨BoundingBox.intPoint z.1,
      BiluFreiman.mem_integerCarrier_iff.mp
        (Finset.mem_filter.mp z.2).1⟩ j.1

/-- If one displayed difference is longer than the containing interval,
projection away from that coefficient is injective.  This is the fibre
count at the heart of CFP Lemma 2.29. -/
theorem omitLongCoordinate_injective {d : ℕ} (P : GAP 1 d)
    (h n : ℕ) (i : Fin d)
    (hlong : ((h * n : ℕ) : ℤ) < |P.steps i 0|) :
    Function.Injective (omitLongCoordinate P h n i) := by
  classical
  intro x y hxy
  apply Subtype.ext
  let rx := chosenCoord (P.dilate h)
    ⟨BoundingBox.intPoint x.1,
      BiluFreiman.mem_integerCarrier_iff.mp
        (Finset.mem_filter.mp x.2).1⟩
  let ry := chosenCoord (P.dilate h)
    ⟨BoundingBox.intPoint y.1,
      BiluFreiman.mem_integerCarrier_iff.mp
        (Finset.mem_filter.mp y.2).1⟩
  have hother : ∀ j : Fin d, j ≠ i → rx j = ry j := by
    intro j hji
    exact congrFun hxy ⟨j, hji⟩
  by_contra hne
  have hi : rx i ≠ ry i := by
    intro heq
    apply hne
    have hcoords : rx = ry := by
      funext j
      by_cases hji : j = i
      · subst j
        exact heq
      · exact hother j hji
    have hxrepr := coordPoint_chosenCoord (P.dilate h)
      ⟨BoundingBox.intPoint x.1,
        BiluFreiman.mem_integerCarrier_iff.mp
          (Finset.mem_filter.mp x.2).1⟩
    have hyrepr := coordPoint_chosenCoord (P.dilate h)
      ⟨BoundingBox.intPoint y.1,
        BiluFreiman.mem_integerCarrier_iff.mp
          (Finset.mem_filter.mp y.2).1⟩
    apply BoundingBox.intPoint_injective
    calc
      BoundingBox.intPoint x.1 = (P.dilate h).coordPoint rx := hxrepr.symm
      _ = (P.dilate h).coordPoint ry := congrArg _ hcoords
      _ = BoundingBox.intPoint y.1 := hyrepr
  have hsum :
      (∑ j : Fin d,
          (((rx j : ℕ) : ℤ) - ((ry j : ℕ) : ℤ)) * P.steps j 0) =
        (((rx i : ℕ) : ℤ) - ((ry i : ℕ) : ℤ)) * P.steps i 0 := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      rw [hother j hji]
      simp
    · simp
  have hxrepr := congrFun (coordPoint_chosenCoord (P.dilate h)
    ⟨BoundingBox.intPoint x.1,
      BiluFreiman.mem_integerCarrier_iff.mp
        (Finset.mem_filter.mp x.2).1⟩) 0
  have hyrepr := congrFun (coordPoint_chosenCoord (P.dilate h)
    ⟨BoundingBox.intPoint y.1,
      BiluFreiman.mem_integerCarrier_iff.mp
        (Finset.mem_filter.mp y.2).1⟩) 0
  change (P.dilate h).coordPoint rx 0 = x.1 at hxrepr
  change (P.dilate h).coordPoint ry 0 = y.1 at hyrepr
  have hdiff :
      x.1 - y.1 =
        (((rx i : ℕ) : ℤ) - ((ry i : ℕ) : ℤ)) * P.steps i 0 := by
    calc
      x.1 - y.1 =
          ((P.dilate h).coordPoint rx) 0 -
            ((P.dilate h).coordPoint ry) 0 := by rw [hxrepr, hyrepr]
      _ = ∑ j : Fin d,
          ((((rx j : ℕ) : ℤ) - ((ry j : ℕ) : ℤ)) * P.steps j 0) := by
        simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps]
        rw [add_sub_add_left_eq_sub]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = _ := hsum
  have hcoeff :
      (1 : ℤ) ≤
        |(((rx i : ℕ) : ℤ) - ((ry i : ℕ) : ℤ))| := by
    have hne' : (((rx i : ℕ) : ℤ) - ((ry i : ℕ) : ℤ)) ≠ 0 := by
      intro hz
      apply hi
      apply Fin.ext
      exact_mod_cast (sub_eq_zero.mp hz)
    exact (Int.one_le_abs hne')
  have hstep_le : |P.steps i 0| ≤ |x.1 - y.1| := by
    rw [hdiff, abs_mul]
    nlinarith [abs_nonneg (P.steps i 0)]
  have hxint := (Finset.mem_filter.mp x.2).2
  have hyint := (Finset.mem_filter.mp y.2).2
  have hinterval : |x.1 - y.1| ≤ ((h * n : ℕ) : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  exact (not_lt_of_ge (hstep_le.trans hinterval)) hlong

/-- The interval slice has only degree-`d-1` many possible fibres when one
difference is longer than the interval. -/
theorem card_dilateIntervalPart_le {d : ℕ} (P : GAP 1 d)
    (h n : ℕ) (i : Fin d)
    (hlong : ((h * n : ℕ) : ℤ) < |P.steps i 0|) :
    (dilateIntervalPart P h n).card ≤
      (h + 1) ^ (d - 1) * P.volume := by
  classical
  have hinj := omitLongCoordinate_injective P h n i hlong
  have hcard := Fintype.card_le_of_injective
    (omitLongCoordinate P h n i) hinj
  have hdomain : Fintype.card {z // z ∈ dilateIntervalPart P h n} =
      (dilateIntervalPart P h n).card := by simp
  have hcodomain :
      Fintype.card
          ((j : {j : Fin d // j ≠ i}) → Fin ((P.dilate h).widths j.1)) =
        ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          (P.dilate h).widths j := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact (Finset.prod_subtype ((Finset.univ : Finset (Fin d)).erase i)
      (by simp) fun j ↦ (P.dilate h).widths j).symm
  rw [hdomain, hcodomain] at hcard
  calc
    (dilateIntervalPart P h n).card ≤
        ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          (P.dilate h).widths j := hcard
    _ ≤ ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          ((h + 1) * P.widths j) := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun j _ ↦ P.dilate_width_le h j)
    _ = (h + 1) ^ (d - 1) *
          (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
            P.widths j) := by
      rw [Finset.prod_mul_distrib]
      have hcardErase :
          ((Finset.univ : Finset (Fin d)).erase i).card = d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
      simp [hcardErase]
    _ ≤ (h + 1) ^ (d - 1) * P.volume := by
      gcongr
      rw [GAP.volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      exact Nat.le_mul_of_pos_right _ (P.width_pos i)

/-- An iterated sumset of nonnegative integers bounded by `n` lies in the
corresponding interval slice of every bounding GAP. -/
theorem multifoldSumset_subset_dilateIntervalPart {A : Finset ℤ}
    {d h n : ℕ} (P : GAP 1 d) (hP : BoundingBox.IsBoundingGAP A P)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z ≤ (n : ℤ)) :
    GrowthLemmas.multifoldSumset h A ⊆ dilateIntervalPart P h n := by
  intro x hx
  rw [dilateIntervalPart, Finset.mem_filter]
  constructor
  · have hcontains : A ⊆ BiluFreiman.integerCarrier P := by
      intro z hz
      exact BiluFreiman.mem_integerCarrier_iff.mpr (hP ⟨z, hz⟩)
    have hxcarrier := HDimension.multifoldSumset_subset_integerCarrier_dilate
      P hcontains hx
    exact hxcarrier
  · obtain ⟨f, hf, rfl⟩ := GrowthLemmas.mem_multifoldSumset_iff.mp hx
    have hnonneg : 0 ≤ ∑ j, f j :=
      Finset.sum_nonneg fun j _ ↦ (hA (f j) (hf j)).1
    have hupper : (∑ j, f j) ≤ ((h * n : ℕ) : ℤ) := by
      calc
        (∑ j, f j) ≤ ∑ _j : Fin h, (n : ℤ) :=
          Finset.sum_le_sum fun j _ ↦ (hA (f j) (hf j)).2
        _ = ((h * n : ℕ) : ℤ) := by simp
    exact ⟨hnonneg, hupper⟩

/-- Exact finite form of CFP Lemma 2.29.  The numerical hypothesis is the
explicit meaning of "`n` sufficiently large in terms of the fixed rank and
approximation constants": degree-`d` growth beats every degree-`d-1` fibre
bound. -/
theorem HApproximation.minimalBox_hasDifferencesAtMost
    {A : Finset ℤ} {h d scaleNum scaleDen n : ℕ}
    (W : HDimension.HApproximation A h d scaleNum scaleDen)
    (hd : 0 < d) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    Stability.HasDifferencesAtMost
      (BoundingBox.dBoundingBox A d hd).progression (n ^ 2) := by
  intro i
  let P := (BoundingBox.dBoundingBox A d hd).progression
  have hAweak : ∀ z ∈ A, 0 ≤ z ∧ z ≤ ((n - 1 : ℕ) : ℤ) := by
    intro z hz
    have hz' := hA z hz
    constructor
    · exact hz'.1
    · have hn : 0 < n := by
        have := W.zero_mem
        have := (hA 0 this).2
        omega
      omega
  by_contra hstep
  change ¬ |P.steps i 0| ≤ (n ^ 2 : ℤ) at hstep
  have hstep' : (n ^ 2 : ℤ) < |P.steps i 0| := by
    have hnonneg : 0 ≤ |P.steps i 0| := abs_nonneg _
    omega
  have hmul : h * (n - 1) ≤ n ^ 2 := by
    calc
      h * (n - 1) ≤ n * n := Nat.mul_le_mul hhn (Nat.sub_le n 1)
      _ = n ^ 2 := by ring
  have hlong : (((h * (n - 1) : ℕ) : ℤ)) < |P.steps i 0| :=
    (by exact_mod_cast hmul : ((h * (n - 1) : ℕ) : ℤ) ≤ (n ^ 2 : ℤ)).trans_lt hstep'
  have hsubset : GrowthLemmas.multifoldSumset h A ⊆
      dilateIntervalPart P h (n - 1) := by
    apply multifoldSumset_subset_dilateIntervalPart P
      (BoundingBox.dBoundingBox_bounds A d hd)
    exact hAweak
  have hupper : (GrowthLemmas.multifoldSumset h A).card ≤
      (h + 1) ^ (d - 1) * P.volume :=
    (Finset.card_le_card hsubset).trans
      (card_dilateIntervalPart_le P h (n - 1) i hlong)
  have hlower := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le W hd
  change (scaleNum * h) ^ d * P.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h A).card at hlower
  have hcombined : (scaleNum * h) ^ d * P.volume ≤
      ((2 * scaleDen) ^ d * (h + 1) ^ (d - 1)) * P.volume := by
    calc
      (scaleNum * h) ^ d * P.volume ≤
          (2 * scaleDen) ^ d *
            (GrowthLemmas.multifoldSumset h A).card := hlower
      _ ≤ (2 * scaleDen) ^ d *
          ((h + 1) ^ (d - 1) * P.volume) := by gcongr
      _ = ((2 * scaleDen) ^ d * (h + 1) ^ (d - 1)) * P.volume := by ring
  have hstrict :
      ((2 * scaleDen) ^ d * (h + 1) ^ (d - 1)) * P.volume <
        (scaleNum * h) ^ d * P.volume :=
    Nat.mul_lt_mul_of_pos_right hnumeric
      (BoundingBox.dBoundingBox_volume_pos A d hd)
  exact (not_lt_of_ge hcombined) hstrict

/-- CFP Corollary 2.30 with all thresholds explicit.  Weak stability and the
preceding difference bound force the minimal box of every accessible
`h`-approximable subset to retain more than three quarters of the reference
volume. -/
theorem HApproximation.three_mul_reference_volume_lt_four_mul_minimalBox
    {A B : Finset ℤ} {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (W : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    3 * (BoundingBox.dBoundingBox A d hd).progression.volume <
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume := by
  have hsteps : Stability.HasDifferencesAtMost
      (BoundingBox.dBoundingBox B d hd).progression (n ^ 2) :=
    HApproximation.minimalBox_hasDifferencesAtMost W hd hhn
      (fun z hz ↦ hA z (hBA hz)) hnumeric
  have hcontains : Stability.integerPoints B ⊆
      (BoundingBox.dBoundingBox B d hd).progression.carrier := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Stability.mem_integerPoints_iff.mp hz
    exact BoundingBox.dBoundingBox_mem_carrier B d hd ha
  by_contra hnot
  have hvolume :
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume ≤
        3 * (BoundingBox.dBoundingBox A d hd).progression.volume := by
    omega
  exact (hstable.avoids hBA hloss W.zero_mem hd hdD
    (BoundingBox.dBoundingBox B d hd).progression hsteps hvolume) hcontains

/-- CFP Lemma 2.31 in an explicit constant form.  An accessible subset of a
weakly stable set retains a fixed proportion of its `h`-fold sumset. -/
theorem HApproximation.three_mul_card_reference_multifoldSumset_lt
    {A B : Finset ℤ} {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (W : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    3 * (GrowthLemmas.multifoldSumset h A).card <
      4 * (4 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h B).card := by
  let PA := (BoundingBox.dBoundingBox A d hd).progression
  let PB := (BoundingBox.dBoundingBox B d hd).progression
  have hretains : 3 * PA.volume < 4 * PB.volume := by
    exact HApproximation.three_mul_reference_volume_lt_four_mul_minimalBox
      hstable hBA hloss W hd hdD hhn hA hnumeric
  have hcontainsA : A ⊆ BiluFreiman.integerCarrier PA := by
    intro z hz
    exact BiluFreiman.mem_integerCarrier_iff.mpr
      (BoundingBox.dBoundingBox_mem_carrier A d hd hz)
  have hsumA : GrowthLemmas.multifoldSumset h A ⊆
      BiluFreiman.integerCarrier (PA.dilate h) :=
    HDimension.multifoldSumset_subset_integerCarrier_dilate PA hcontainsA
  have hupperA : (GrowthLemmas.multifoldSumset h A).card ≤
      (h + 1) ^ d * PA.volume := by
    calc
      (GrowthLemmas.multifoldSumset h A).card ≤
          (BiluFreiman.integerCarrier (PA.dilate h)).card :=
        Finset.card_le_card hsumA
      _ = (PA.dilate h).carrier.card := BiluFreiman.card_integerCarrier _
      _ ≤ (PA.dilate h).volume := (PA.dilate h).card_carrier_le_volume
      _ ≤ (h + 1) ^ d * PA.volume := PA.volume_dilate_le h
  have hlowerB := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le W hd
  change (scaleNum * h) ^ d * PB.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h B).card at hlowerB
  have hh : 0 < h := W.scale_pos.trans_le W.scale_le
  have hbase : h + 1 ≤ 2 * h := by omega
  have hpowbase : (h + 1) ^ d ≤ (2 * h) ^ d :=
    Nat.pow_le_pow_left hbase d
  have hscale : h ^ d ≤ (scaleNum * h) ^ d := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h W.scaleNum_pos
  have hcross : 3 * h ^ d *
        (GrowthLemmas.multifoldSumset h A).card <
      4 * h ^ d * (4 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h B).card := by
    calc
      3 * h ^ d * (GrowthLemmas.multifoldSumset h A).card ≤
          3 * (scaleNum * h) ^ d *
            ((h + 1) ^ d * PA.volume) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 3 hscale) hupperA
      _ < 4 * (scaleNum * h) ^ d *
          ((h + 1) ^ d * PB.volume) := by
        have := Nat.mul_lt_mul_of_pos_left hretains
          (Nat.mul_pos (pow_pos (Nat.mul_pos W.scaleNum_pos hh) d)
            (pow_pos (by omega : 0 < h + 1) d))
        nlinarith
      _ ≤ 4 * (h + 1) ^ d * (2 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h B).card := by
        have := Nat.mul_le_mul_left (4 * (h + 1) ^ d) hlowerB
        nlinarith
      _ ≤ 4 * h ^ d * (4 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h B).card := by
        calc
          4 * (h + 1) ^ d * (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h B).card ≤
            4 * (2 * h) ^ d * (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h B).card := by gcongr
          _ = 4 * (2 ^ d * 2 ^ d) * h ^ d * scaleDen ^ d *
              (GrowthLemmas.multifoldSumset h B).card := by
            simp only [mul_pow]
            ring
          _ = 4 * h ^ d * (4 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h B).card := by
            have htwo : 2 ^ d * 2 ^ d = 4 ^ d := by
              rw [← mul_pow]
              norm_num
            rw [htwo, mul_pow]
            ring
  have hhpow : 0 < h ^ d := pow_pos hh d
  apply (Nat.mul_lt_mul_left hhpow).mp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross

/-- The expanded ambient coefficient box is bounded by a fixed multiple of
the accessible subset's `h`-fold sumset.  This is the numerical estimate used
in the quotient-coset packing proof of CFP Lemma 2.32. -/
theorem HApproximation.two_mul_dilate_volume_le_indexBound_mul_card
    {A B : Finset ℤ} {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (W : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d) :
    ((BoundingBox.dBoundingBox A d hd).progression.dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d) *
        (GrowthLemmas.multifoldSumset h B).card := by
  let PA := (BoundingBox.dBoundingBox A d hd).progression
  let PB := (BoundingBox.dBoundingBox B d hd).progression
  have hretains : 3 * PA.volume < 4 * PB.volume :=
    HApproximation.three_mul_reference_volume_lt_four_mul_minimalBox
      hstable hBA hloss W hd hdD hhn hA hnumeric
  have hlower := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le W hd
  change (scaleNum * h) ^ d * PB.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h B).card at hlower
  have hh : 0 < h := W.scale_pos.trans_le W.scale_le
  have hbase : 2 * h + 1 ≤ 3 * h := by omega
  have hscale : h ^ d ≤ (scaleNum * h) ^ d := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h W.scaleNum_pos
  have hvol := PA.volume_dilate_le (2 * h)
  have hthree : 3 * (PA.dilate (2 * h)).volume <
      (4 * (6 * scaleDen) ^ d) *
        (GrowthLemmas.multifoldSumset h B).card := by
    calc
      3 * (PA.dilate (2 * h)).volume ≤
          3 * ((2 * h + 1) ^ d * PA.volume) :=
        Nat.mul_le_mul_left 3 hvol
      _ ≤ 3 * (3 * h) ^ d * PA.volume := by
        have hp : (2 * h + 1) ^ d ≤ (3 * h) ^ d :=
          Nat.pow_le_pow_left hbase d
        nlinarith
      _ < 4 * (3 * h) ^ d * PB.volume := by
        have hm := Nat.mul_lt_mul_of_pos_right hretains
          (pow_pos (Nat.mul_pos (by omega : 0 < 3) hh) d)
        nlinarith
      _ ≤ 4 * 3 ^ d * (2 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h B).card := by
        have hhPB : h ^ d * PB.volume ≤
            (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h B).card :=
          (Nat.mul_le_mul_right PB.volume hscale).trans hlower
        have hm := Nat.mul_le_mul_left (4 * 3 ^ d) hhPB
        simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm
      _ = (4 * (6 * scaleDen) ^ d) *
          (GrowthLemmas.multifoldSumset h B).card := by
        have hsix : 3 ^ d * (2 * scaleDen) ^ d =
            (6 * scaleDen) ^ d := by
          rw [← mul_pow]
          congr 1
          ring
        calc
          4 * 3 ^ d * (2 * scaleDen) ^ d *
              (GrowthLemmas.multifoldSumset h B).card =
            4 * (3 ^ d * (2 * scaleDen) ^ d) *
              (GrowthLemmas.multifoldSumset h B).card := by ring
          _ = _ := by rw [hsix]
  change (PA.dilate (2 * h)).volume ≤
    (4 * (6 * scaleDen) ^ d) *
      (GrowthLemmas.multifoldSumset h B).card
  omega

/-- Rank-flexible version used in CFP Lemma 2.32: the ambient relevant rank
`d` and the accessible subset's own `h`-dimension `e` may differ. -/
theorem HApproximation.two_mul_dilate_volume_le_general_indexBound_mul_card
    {A B : Finset ℤ} {x D n h d e scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (WA : HDimension.HApproximation A h d scaleNum scaleDen)
    (WB : HDimension.HApproximation B h e scaleNum scaleDen)
    (hd : 0 < d) (he : 0 < e) (heD : e ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericB :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e) :
    ((BoundingBox.dBoundingBox A d hd).progression.dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
  let PA := (BoundingBox.dBoundingBox A d hd).progression
  have hdensity : 3 * (GrowthLemmas.multifoldSumset h A).card <
      4 * (4 * scaleDen) ^ e *
        (GrowthLemmas.multifoldSumset h B).card :=
    HApproximation.three_mul_card_reference_multifoldSumset_lt
      hstable hBA hloss WB he heD hhn hA hnumericB
  have hlowerA := HDimension.HApproximation.h_pow_mul_boundingBox_volume_le WA hd
  change (scaleNum * h) ^ d * PA.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h A).card at hlowerA
  have hh : 0 < h := WA.scale_pos.trans_le WA.scale_le
  have hbase : 2 * h + 1 ≤ 3 * h := by omega
  have hscale : h ^ d ≤ (scaleNum * h) ^ d := by
    apply Nat.pow_le_pow_left
    calc
      h = 1 * h := by simp
      _ ≤ scaleNum * h := Nat.mul_le_mul_right h WA.scaleNum_pos
  have hhvol : h ^ d * PA.volume ≤
      (2 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h A).card :=
    (Nat.mul_le_mul_right PA.volume hscale).trans hlowerA
  have hvolA : (PA.dilate (2 * h)).volume ≤
      (6 * scaleDen) ^ d *
        (GrowthLemmas.multifoldSumset h A).card := by
    calc
      (PA.dilate (2 * h)).volume ≤ (2 * h + 1) ^ d * PA.volume :=
        PA.volume_dilate_le (2 * h)
      _ ≤ (3 * h) ^ d * PA.volume := by gcongr
      _ ≤ 3 ^ d * (2 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h A).card := by
        have hm := Nat.mul_le_mul_left (3 ^ d) hhvol
        simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm
      _ = (6 * scaleDen) ^ d *
          (GrowthLemmas.multifoldSumset h A).card := by
        have hsix : 3 ^ d * (2 * scaleDen) ^ d =
            (6 * scaleDen) ^ d := by
          rw [← mul_pow]
          congr 1
          ring
        rw [hsix]
  have hthree : 3 * (PA.dilate (2 * h)).volume <
      (4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
    calc
      3 * (PA.dilate (2 * h)).volume ≤
          3 * ((6 * scaleDen) ^ d *
            (GrowthLemmas.multifoldSumset h A).card) :=
        Nat.mul_le_mul_left 3 hvolA
      _ < (6 * scaleDen) ^ d *
          (4 * (4 * scaleDen) ^ e *
            (GrowthLemmas.multifoldSumset h B).card) := by
        have hm := Nat.mul_lt_mul_of_pos_left hdensity
          (pow_pos (Nat.mul_pos (by omega : 0 < 6) WA.scaleDen_pos) d)
        nlinarith
      _ = (4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
          (GrowthLemmas.multifoldSumset h B).card := by ring
  change (PA.dilate (2 * h)).volume ≤ _
  omega

/-! ## Coordinate boxes and coordinate sumsets -/

/-- The nonnegative integer coefficient box of the `k`-dilation, embedded in
the ambient coordinate lattice. -/
noncomputable def coordinateBox {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    Finset (LatticePoint d) := by
  classical
  exact Finset.univ.image fun c : (P.dilate k).Coord ↦
    fun i ↦ ((c i : ℕ) : ℤ)

/-- The coefficient embedding is injective, so the coordinate box has the
displayed dilated volume. -/
theorem card_coordinateBox {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    (coordinateBox P k).card = (P.dilate k).volume := by
  classical
  unfold coordinateBox
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact P.volume_dilate k
  · intro a b hab
    funext i
    apply Fin.ext
    have hi := congrFun hab i
    change (((a i : ℕ) : ℤ)) = ((b i : ℕ) : ℤ) at hi
    exact_mod_cast hi

/-- Adding coefficient vectors adds their dilation scales. -/
theorem add_mem_coordinateBox {d : ℕ} (P : GAP 1 d)
    {a b : ℕ} {x y : LatticePoint d}
    (hx : x ∈ coordinateBox P a) (hy : y ∈ coordinateBox P b) :
    x + y ∈ coordinateBox P (a + b) := by
  classical
  unfold coordinateBox at hx hy ⊢
  obtain ⟨cx, _hcx, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨cy, _hcy, rfl⟩ := Finset.mem_image.mp hy
  let c : (P.dilate (a + b)).Coord := fun i ↦
    ⟨(cx i : ℕ) + (cy i : ℕ), by
      have hxlt := (cx i).isLt
      have hylt := (cy i).isLt
      simp only [GAP.dilate_widths] at hxlt hylt ⊢
      rw [Nat.add_mul]
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  funext i
  simp [c]

/-- Zero is in the zero-dilation coefficient box. -/
theorem zero_mem_coordinateBox {d : ℕ} (P : GAP 1 d) :
    (0 : LatticePoint d) ∈ coordinateBox P 0 := by
  classical
  unfold coordinateBox
  let c : (P.dilate 0).Coord := fun i ↦ ⟨0, by simp⟩
  exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, by
    funext i
    simp [c]⟩

/-- Zero belongs to every coefficient box. -/
theorem zero_mem_coordinateBox_scale {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    (0 : LatticePoint d) ∈ coordinateBox P k := by
  classical
  unfold coordinateBox
  let c : (P.dilate k).Coord := fun i ↦ ⟨0, (P.dilate k).width_pos i⟩
  exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, by
    funext i
    simp [c]⟩

/-- A constant iterated sumset whose generators lie in the unit coefficient
box lies in the corresponding dilated coefficient box. -/
theorem constantIteratedSumset_subset_coordinateBox {d : ℕ}
    (P : GAP 1 d) (X : Finset (LatticePoint d))
    (hX : X ⊆ coordinateBox P 1) :
    ∀ k, constantIteratedSumset X k ⊆ coordinateBox P k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa [constantIteratedSumset] using hx
      simpa [hx0] using zero_mem_coordinateBox P
  | succ k ih =>
      rw [show constantIteratedSumset X (k + 1) =
          constantIteratedSumset X k + X by
        exact Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X) k]
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ :=
        Erdos186.CFP.mem_pointwise_add_iff.mp hz
      simpa using add_mem_coordinateBox P (ih hx) (hX hy)

/-- Consequently every coordinate iterated sumset has the expected box
cardinality upper bound. -/
theorem card_constantIteratedSumset_le_coordinateBox {d : ℕ}
    (P : GAP 1 d) (X : Finset (LatticePoint d))
    (hX : X ⊆ coordinateBox P 1) (k : ℕ) :
    (constantIteratedSumset X k).card ≤ (P.dilate k).volume := by
  rw [← card_coordinateBox P k]
  exact Finset.card_le_card
    (constantIteratedSumset_subset_coordinateBox P X hX k)

/-- A proper bounding-box identification is a unit coefficient vector. -/
theorem identificationMap_mem_coordinateBox {A : Finset ℤ} {d : ℕ}
    (B : BoundingBox.BoundingGAP A d) (hproper : B.progression.Proper)
    (z : {z // z ∈ A}) :
    B.identificationMap hproper z ∈ coordinateBox B.progression 1 := by
  classical
  unfold coordinateBox
  let c : (B.progression.dilate 1).Coord := fun i ↦
    ⟨B.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint z, B.bounds z⟩ i, by
      have hi := (B.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint z, B.bounds z⟩ i).isLt
      simp only [GAP.dilate_widths]
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  funext i
  exact B.identificationMap_apply hproper z i

/-! ## The logarithmic bounding-box potential -/

/-- The sum of the contraction ranks of the positive-rank minimal bounding
boxes up to `maxRank`.  Cubing makes one `3 / 4` volume contraction force a
strict decrease of the binary logarithm. -/
noncomputable def boxPotential (A : Finset ℤ) (maxRank : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 maxRank,
    contractionRank (Stability.minimalBoxFamily A d).volume

/-- Minimal bounding-box volumes, and hence their contraction ranks, are
monotone under passage to a subset. -/
theorem boxPotential_mono {A B : Finset ℤ} (hBA : B ⊆ A) (maxRank : ℕ) :
    boxPotential B maxRank ≤ boxPotential A maxRank := by
  classical
  unfold boxPotential
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  apply contractionRank_mono
  simpa only [Stability.minimalBoxFamily_eq_dBoundingBox A hdpos,
    Stability.minimalBoxFamily_eq_dBoundingBox B hdpos] using
    BoundingBox.dBoundingBox_volume_mono d hdpos hBA

/-- If one positive-rank minimal bounding box contracts by `3 / 4`, while the
underlying set only shrinks, then the total box potential strictly drops. -/
theorem boxPotential_lt_of_contraction {A B : Finset ℤ} (hBA : B ⊆ A)
    {maxRank d : ℕ} (hd : 0 < d) (hdD : d ≤ maxRank)
    (hcontract :
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume ≤
        3 * (BoundingBox.dBoundingBox A d hd).progression.volume) :
    boxPotential B maxRank < boxPotential A maxRank := by
  classical
  unfold boxPotential
  apply Finset.sum_lt_sum
  · intro i hi
    have hipos : 0 < i := (Finset.mem_Icc.mp hi).1
    apply contractionRank_mono
    simpa only [Stability.minimalBoxFamily_eq_dBoundingBox A hipos,
      Stability.minimalBoxFamily_eq_dBoundingBox B hipos] using
      BoundingBox.dBoundingBox_volume_mono i hipos hBA
  · refine ⟨d, Finset.mem_Icc.mpr ⟨hd, hdD⟩, ?_⟩
    have hstrict := contractionRank_lt_of_four_mul_le_three_mul
      (BoundingBox.dBoundingBox_volume_pos B d hd)
      (BoundingBox.dBoundingBox_volume_pos A d hd) hcontract
    simpa only [Stability.minimalBoxFamily_eq_dBoundingBox A hd,
      Stability.minimalBoxFamily_eq_dBoundingBox B hd] using hstrict

/-- On a set contained in `[0,n)`, the box potential has the expected
`O(maxRank * log n)` bound. -/
theorem boxPotential_le {A : Finset ℤ} {n maxRank : ℕ}
    (hzero : 0 ∈ A) (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ)) :
    boxPotential A maxRank ≤
      maxRank * (3 * (Nat.log 2 n + 1)) := by
  classical
  unfold boxPotential
  calc
    ∑ d ∈ Finset.Icc 1 maxRank,
        contractionRank (Stability.minimalBoxFamily A d).volume
        ≤ ∑ _d ∈ Finset.Icc 1 maxRank,
            3 * (Nat.log 2 n + 1) := by
              apply Finset.sum_le_sum
              intro d hd
              have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
              apply contractionRank_le_three_mul_log_add_one
              rw [Stability.minimalBoxFamily_eq_dBoundingBox A hdpos]
              exact BoundingBox.dBoundingBox_volume_le_of_mem_Ico A d n
                hdpos hzero hA
    _ = (Finset.Icc 1 maxRank).card * (3 * (Nat.log 2 n + 1)) := by
      simp
    _ ≤ maxRank * (3 * (Nat.log 2 n + 1)) := by
      gcongr
      simp

/-! ## Step 1: pruning to weak stability -/

/-- The precise difference-bound certificate needed in CFP Step 1.

The paper obtains this for the dimensions which arise as `h`-dimensions from
Lemma 2.29.  We state it for every positive rank up to `maxRank`, which is the
finite range tested by `WeaklyStableMinimalFor`. -/
def BoxDifferenceCertificate (A : Finset ℤ) (maxRank n : ℕ) : Prop :=
  ∀ {B : Finset ℤ}, B ⊆ A → 0 ∈ B →
    ∀ {d : ℕ}, 0 < d → d ≤ maxRank →
      Stability.HasDifferencesAtMost (Stability.minimalBoxFamily B d) (n ^ 2)

/-- One failed weak-stability test supplies a bounded deletion which strictly
decreases the logarithmic box potential. -/
theorem weakStability_deletion_step {A : Finset ℤ}
    {budget maxRank n : ℕ} (hzero : 0 ∈ A)
    (hnot : ¬ Stability.WeaklyStableMinimalFor A budget maxRank n) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card + budget ∧
      boxPotential B maxRank < boxPotential A maxRank := by
  classical
  unfold Stability.WeaklyStableMinimalFor Stability.WeaklyStableFor at hnot
  have hfailure : ¬ (∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card + budget → 0 ∈ B →
      ∀ {d : ℕ}, 0 < d → d ≤ maxRank →
        ∀ P : GAP 1 d, Stability.HasDifferencesAtMost P (n ^ 2) →
          4 * P.volume ≤ 3 * (Stability.minimalBoxFamily A d).volume →
            ¬ Stability.integerPoints B ⊆ P.carrier) := by
    intro hall
    exact hnot ⟨hzero, hall⟩
  push Not at hfailure
  obtain ⟨B, hBA, hloss, hzeroB, d, hd, hdD, P, _hPsteps,
      hvolume, hBP⟩ := hfailure
  have hbounding : BoundingBox.IsBoundingGAP B P := by
    rintro ⟨z, hz⟩
    have hz' : Stability.integerPoint z ∈ Stability.integerPoints B := by
      exact Stability.integerPoint_mem_integerPoints_iff.mpr hz
    simpa [Stability.integerPoint, BoundingBox.intPoint] using hBP hz'
  have hminimal :
      (BoundingBox.dBoundingBox B d hd).progression.volume ≤ P.volume :=
    BoundingBox.dBoundingBox_minimal B d hd P hbounding
  have hcontract :
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume ≤
        3 * (BoundingBox.dBoundingBox A d hd).progression.volume := by
    calc
      4 * (BoundingBox.dBoundingBox B d hd).progression.volume ≤ 4 * P.volume := by
        gcongr
      _ ≤ 3 * (BoundingBox.dBoundingBox A d hd).progression.volume := by
        simpa only [Stability.minimalBoxFamily_eq_dBoundingBox A hd] using hvolume
  refine ⟨B, hBA, hzeroB, hloss,
    boxPotential_lt_of_contraction hBA hd hdD hcontract⟩

/-- CFP Lemma 2.37, Step 1, without resilience: repeated bounded deletions
terminate at a weakly stable subset.  The total loss is the one-step budget
times the initial logarithmic box potential. -/
theorem exists_weaklyStable_core {A : Finset ℤ}
    {budget maxRank n : ℕ} (hzero : 0 ∈ A) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      Stability.WeaklyStableMinimalFor B budget maxRank n ∧
      A.card ≤ B.card + budget * boxPotential A maxRank := by
  classical
  let Good : Finset ℤ → Prop :=
    fun B ↦ Stability.WeaklyStableMinimalFor B budget maxRank n
  let Inv : Finset ℤ → Prop := fun B ↦ B ⊆ A ∧ 0 ∈ B
  have hstep : ∀ B : Finset ℤ, Inv B → ¬ Good B →
      ∃ C : Finset ℤ, C ⊆ B ∧ Inv C ∧
        B.card ≤ C.card + budget ∧
        boxPotential C maxRank < boxPotential B maxRank := by
    intro B hInv hnot
    obtain ⟨C, hCB, hzeroC, hloss, hpot⟩ :=
      weakStability_deletion_step hInv.2 hnot
    exact ⟨C, hCB, ⟨hCB.trans hInv.1, hzeroC⟩, hloss, hpot⟩
  obtain ⟨B, hBA, hInvB, hGoodB, hloss⟩ :=
    exists_good_invariant_subset_of_decreasing_potential
      Inv Good (boxPotential · maxRank) budget hstep A
      ⟨Finset.Subset.rfl, hzero⟩
  exact ⟨B, hBA, hInvB.2, hGoodB, hloss⟩

/-! ## Step 2: subgroup-span pruning (CFP Lemma 2.32) -/

/-- Natural rank certificate for the subgroup-index argument of CFP Lemma
2.32.  Strict descent of at least one relevant generated subgroup strictly
decreases `rank`; `height` bounds the initial rank. -/
structure SpanRankCertificate (A : Finset ℤ) (relevant : Finset ℕ)
    (phi : (d : ℕ) → ℤ → LatticePoint d) (height : ℕ) where
  rank : (∀ d : {d // d ∈ relevant},
    AddSubgroup (LatticePoint d.1)) → ℕ
  drops : ∀ {B C : Finset ℤ}, B ⊆ A → C ⊆ B →
    (∃ d : {d // d ∈ relevant},
      Stability.generatedSubgroup (phi d.1) C ≠
        Stability.generatedSubgroup (phi d.1) B) →
    rank (fun d ↦ Stability.generatedSubgroup (phi d.1) C) <
      rank (fun d ↦ Stability.generatedSubgroup (phi d.1) B)
  initial_le : rank (fun d ↦ Stability.generatedSubgroup (phi d.1) A) ≤ height

/-- A completely finite rank for subgroup profiles.  It counts the subsets
of a fixed ambient set whose generated profile is coordinatewise below the
given profile. -/
noncomputable def subgroupProfileRank (ambient : Finset ℤ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d)
    (H : ∀ d : {d // d ∈ relevant}, AddSubgroup (LatticePoint d.1)) : ℕ :=
  by
    classical
    exact (ambient.powerset.filter fun B ↦ ∀ d : {d // d ∈ relevant},
      Stability.generatedSubgroup (phi d.1) B ≤ H d).card

/-- Strict descent of a generated-subgroup profile strictly decreases the
finite profile rank. -/
theorem subgroupProfileRank_strict {ambient B C : Finset ℤ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hBambient : B ⊆ ambient) (hCB : C ⊆ B)
    (hchange : ∃ d : {d // d ∈ relevant},
      Stability.generatedSubgroup (phi d.1) C ≠
        Stability.generatedSubgroup (phi d.1) B) :
    subgroupProfileRank ambient relevant phi
        (fun d ↦ Stability.generatedSubgroup (phi d.1) C) <
      subgroupProfileRank ambient relevant phi
        (fun d ↦ Stability.generatedSubgroup (phi d.1) B) := by
  classical
  unfold subgroupProfileRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro X hX
    simp only [Finset.mem_filter, Finset.mem_powerset] at hX ⊢
    refine ⟨hX.1, ?_⟩
    intro d
    exact (hX.2 d).trans (Stability.generatedSubgroup_mono hCB)
  · intro heq
    obtain ⟨d, hdne⟩ := hchange
    have hBmemRight : B ∈ ambient.powerset.filter (fun X ↦
        ∀ e : {e // e ∈ relevant},
          Stability.generatedSubgroup (phi e.1) X ≤
            Stability.generatedSubgroup (phi e.1) B) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hBambient, fun _ ↦ le_rfl⟩
    have hBmemLeft := heq ▸ hBmemRight
    simp only [Finset.mem_filter, Finset.mem_powerset] at hBmemLeft
    apply hdne
    exact le_antisymm (Stability.generatedSubgroup_mono hCB) (hBmemLeft.2 d)

/-- The finite profile rank is bounded by the number of subsets of its
ambient set. -/
theorem subgroupProfileRank_le (ambient : Finset ℤ) (relevant : Finset ℕ)
    (phi : (d : ℕ) → ℤ → LatticePoint d)
    (H : ∀ d : {d // d ∈ relevant}, AddSubgroup (LatticePoint d.1)) :
    subgroupProfileRank ambient relevant phi H ≤ 2 ^ ambient.card := by
  classical
  unfold subgroupProfileRank
  calc
    (ambient.powerset.filter fun B ↦ ∀ d : {d // d ∈ relevant},
      Stability.generatedSubgroup (phi d.1) B ≤ H d).card
        ≤ ambient.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ ambient.card := Finset.card_powerset ambient

/-- Every finite coordinate system has a canonical (coarse) span-rank
certificate of height `2^|A|`.  CFP's subgroup-index argument replaces this
height by a constant depending only on `beta`. -/
noncomputable def finiteSpanRankCertificate (A : Finset ℤ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) :
    SpanRankCertificate A relevant phi (2 ^ A.card) where
  rank := subgroupProfileRank A relevant phi
  drops := by
    intro B C hBA hCB hchange
    exact subgroupProfileRank_strict hBA hCB hchange
  initial_le := subgroupProfileRank_le A relevant phi _

/-- **CFP Lemma 2.32, finite pruning engine.**

Under the bounded subgroup-chain rank supplied by the CFP index estimate, a
set containing zero has a large subset whose generated coordinate subgroups
survive every further deletion of at most `robustBudget` points. -/
theorem span_pruning_lemma232 {A : Finset ℤ} {relevant : Finset ℕ}
    {phi : (d : ℕ) → ℤ → LatticePoint d}
    {robustBudget height : ℕ} (hzero : 0 ∈ A)
    (certificate : SpanRankCertificate A relevant phi height) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card + robustBudget * height ∧
      Stability.SpanRobust 0 B robustBudget relevant phi := by
  classical
  let Good : Finset ℤ → Prop := fun B ↦
    Stability.SpanRobust 0 B robustBudget relevant phi
  let Inv : Finset ℤ → Prop := fun B ↦ B ⊆ A ∧ 0 ∈ B
  let mu : Finset ℤ → ℕ := fun B ↦
    certificate.rank (fun d ↦ Stability.generatedSubgroup (phi d.1) B)
  have hstep : ∀ B : Finset ℤ, Inv B → ¬ Good B →
      ∃ C : Finset ℤ, C ⊆ B ∧ Inv C ∧
        B.card ≤ C.card + robustBudget ∧ mu C < mu B := by
    intro B hInv hnot
    unfold Good Stability.SpanRobust at hnot
    push Not at hnot
    obtain ⟨d, hd, C, hCB, hloss, hzeroC, hne⟩ := hnot
    refine ⟨C, hCB, ⟨hCB.trans hInv.1, hzeroC⟩, hloss, ?_⟩
    exact certificate.drops hInv.1 hCB ⟨⟨d, hd⟩, hne⟩
  obtain ⟨B, hBA, hInvB, hGoodB, hloss⟩ :=
    exists_good_invariant_subset_of_decreasing_potential
      Inv Good mu robustBudget hstep A ⟨Finset.Subset.rfl, hzero⟩
  refine ⟨B, hBA, hInvB.2, hloss.trans ?_, hGoodB⟩
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left robustBudget certificate.initial_le) _

/-- A fully unconditional finite version of the span-pruning lemma.  Its
height `2^|A|` is deliberately coarse; the analytic content of CFP Lemma 2.32
is precisely the replacement of this height by a constant depending only on
`beta`. -/
theorem span_pruning_finite {A : Finset ℤ} {relevant : Finset ℕ}
    {phi : (d : ℕ) → ℤ → LatticePoint d} {robustBudget : ℕ}
    (hzero : 0 ∈ A) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card + robustBudget * (2 ^ A.card) ∧
      Stability.SpanRobust 0 B robustBudget relevant phi := by
  exact span_pruning_lemma232 hzero
    (finiteSpanRankCertificate A relevant phi)

/-! ## Accessible subgroup-index descent

The coarse certificate above counts every subset of the ambient set.  In
Lemma 2.32 one has a much sharper input: every set which can occur during the
pruning (hence every set within the advertised deletion budget) generates a
subgroup of uniformly bounded finite index.  The next argument is formulated
with precisely that accessibility restriction.  This is important: arbitrary
subgroups of `ℤ^d` have chains of unbounded length, so a global bounded-rank
certificate would be false.
-/

/-- The sum of the binary logarithms of the relative subgroup indices of a
profile `H` inside the initial profile `top`.  A strict decrease of one
finite-index subgroup strictly increases this depth. -/
noncomputable def spanIndexDepth {relevant : Finset ℕ}
    (top H : ∀ d : {d // d ∈ relevant},
      AddSubgroup (LatticePoint d.1)) : ℕ :=
  ∑ d, Nat.log 2 ((H d).relIndex (top d))

/-- Relative-index depth is zero at the initial profile. -/
@[simp]
theorem spanIndexDepth_self {relevant : Finset ℕ}
    (top : ∀ d : {d // d ∈ relevant},
      AddSubgroup (LatticePoint d.1)) :
    spanIndexDepth top top = 0 := by
  classical
  simp [spanIndexDepth, AddSubgroup.relIndex_self]

/-- A strict finite-index subgroup step increases binary logarithmic index by
at least one. -/
theorem log_relIndex_lt_of_lt {G : Type*} [AddGroup G]
    {H K L : AddSubgroup G} (hHK : H ≤ K) (hKL : K ≤ L)
    (hstrict : H ≠ K) (hfinite : H.relIndex L ≠ 0) :
    Nat.log 2 (K.relIndex L) < Nat.log 2 (H.relIndex L) := by
  have hmul := AddSubgroup.relIndex_mul_relIndex H K L hHK hKL
  have hHKnz : H.relIndex K ≠ 0 := by
    intro hzero
    apply hfinite
    rw [← hmul, hzero, zero_mul]
  have hKLnz : K.relIndex L ≠ 0 := by
    intro hzero
    apply hfinite
    rw [← hmul, hzero, mul_zero]
  have hHKtwo : 2 ≤ H.relIndex K := by
    have hone : H.relIndex K ≠ 1 := by
      intro heq
      have hKH : K ≤ H := AddSubgroup.relIndex_eq_one.mp heq
      exact hstrict (le_antisymm hHK hKH)
    omega
  have hdouble : K.relIndex L * 2 ≤ H.relIndex L := by
    rw [← hmul]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (K.relIndex L) hHKtwo
  have hlogdouble :
      Nat.log 2 (K.relIndex L * 2) = Nat.log 2 (K.relIndex L) + 1 :=
    Nat.log_mul_base (by omega) hKLnz
  calc
    Nat.log 2 (K.relIndex L) < Nat.log 2 (K.relIndex L) + 1 :=
      Nat.lt_succ_self _
    _ = Nat.log 2 (K.relIndex L * 2) := hlogdouble.symm
    _ ≤ Nat.log 2 (H.relIndex L) := Nat.log_monotone hdouble

/-- If all coordinates have finite relative index in the initial profile and
at least one coordinate subgroup decreases strictly, total index depth
strictly increases. -/
theorem spanIndexDepth_lt {relevant : Finset ℕ}
    {top H K : ∀ d : {d // d ∈ relevant},
      AddSubgroup (LatticePoint d.1)}
    (hKH : ∀ d, K d ≤ H d) (hHtop : ∀ d, H d ≤ top d)
    (hfinite : ∀ d, (K d).relIndex (top d) ≠ 0)
    (hchange : ∃ d, K d ≠ H d) :
    spanIndexDepth top H < spanIndexDepth top K := by
  classical
  unfold spanIndexDepth
  apply Finset.sum_lt_sum
  · intro d _hd
    exact Nat.log_monotone
      (AddSubgroup.relIndex_le_of_le_left (hKH d) (hfinite d))
  · obtain ⟨d, hd⟩ := hchange
    exact ⟨d, Finset.mem_univ d,
      log_relIndex_lt_of_lt (hKH d) (hHtop d) hd (hfinite d)⟩

/-- A uniform bound on the coordinatewise relative indices bounds total
binary index depth. -/
theorem spanIndexDepth_le {relevant : Finset ℕ}
    {top H : ∀ d : {d // d ∈ relevant},
      AddSubgroup (LatticePoint d.1)} {indexBound : ℕ}
    (hbound : ∀ d, (H d).relIndex (top d) ≤ indexBound) :
    spanIndexDepth top H ≤ relevant.card * Nat.log 2 indexBound := by
  classical
  unfold spanIndexDepth
  calc
    (∑ d, Nat.log 2 ((H d).relIndex (top d))) ≤
        ∑ _d : {d // d ∈ relevant}, Nat.log 2 indexBound := by
      exact Finset.sum_le_sum fun d _ ↦ Nat.log_monotone (hbound d)
    _ = relevant.card * Nat.log 2 indexBound := by simp

/-! ### A finite quotient is forced by bounded sumset growth -/

/-- The image of a finite set in an additive quotient. -/
noncomputable def quotientImage {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (T : Finset G) : Finset (G ⧸ H) := by
  classical
  exact T.image (QuotientAddGroup.mk' H)

/-- Coset packing: distinct quotient classes represented by `T`, translated
by a finite subset `S` of the subgroup, inject into any set containing all
of the corresponding sums. -/
theorem card_quotient_image_mul_card_le {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (T S U : Finset G)
    (hS : ∀ s ∈ S, s ∈ H)
    (hadd : ∀ t ∈ T, ∀ s ∈ S, t + s ∈ U) :
    (quotientImage H T).card * S.card ≤ U.card := by
  classical
  let q : G →+ (G ⧸ H) := QuotientAddGroup.mk' H
  let R : Finset (G ⧸ H) := quotientImage H T
  let rep : R → G := fun r ↦
    Classical.choose (Finset.mem_image.mp r.property)
  have hrep_mem (r : R) : rep r ∈ T :=
    (Classical.choose_spec (Finset.mem_image.mp r.property)).1
  have hqrep (r : R) : q (rep r) = r.1 :=
    (Classical.choose_spec (Finset.mem_image.mp r.property)).2
  have hqzero {s : G} (hs : s ∈ H) : q s = 0 := by
    rw [show (0 : G ⧸ H) = q 0 by simp, QuotientAddGroup.mk'_eq_mk']
    exact ⟨-s, H.neg_mem hs, by simp⟩
  let pack : R × {s // s ∈ S} → {u // u ∈ U} := fun p ↦
    ⟨rep p.1 + p.2.1, hadd _ (hrep_mem p.1) _ p.2.2⟩
  have hpack : Function.Injective pack := by
    rintro ⟨r, s⟩ ⟨r', s'⟩ heq
    have heqval : rep r + s.1 = rep r' + s'.1 :=
      congrArg Subtype.val heq
    have hreq : r = r' := by
      apply Subtype.ext
      have hqeq := congrArg q heqval
      simpa [map_add, hqrep, hqzero (hS s.1 s.2),
        hqzero (hS s'.1 s'.2)] using hqeq
    subst r'
    have hseq : s = s' := by
      apply Subtype.ext
      exact add_left_cancel heqval
    subst s'
    rfl
  have hcard := Fintype.card_le_of_injective pack hpack
  rw [Fintype.card_prod] at hcard
  rw [Fintype.card_coe R, Fintype.card_coe S, Fintype.card_coe U] at hcard
  simpa [R, quotientImage, q] using hcard

/-- Constant iterated sumsets add by adding their numbers of summands. -/
theorem constantIteratedSumset_add {G : Type*} [AddCommMonoid G]
    [DecidableEq G] (X : Finset G) (a b : ℕ) :
    constantIteratedSumset X a + constantIteratedSumset X b =
      constantIteratedSumset X (a + b) := by
  induction b with
  | zero =>
      change constantIteratedSumset X a + 0 = _
      exact add_zero _
  | succ b ih =>
      rw [show constantIteratedSumset X (b + 1) =
          constantIteratedSumset X b + X by
        exact Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X) b]
      rw [← add_assoc, ih, Nat.add_succ]
      exact (Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X) (a + b)).symm

/-- Membership in a constant iterated sumset is a sum of an indexed family
of the prescribed length. -/
theorem mem_constantIteratedSumset_iff {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {X : Finset G} {k : ℕ} {x : G} :
    x ∈ constantIteratedSumset X k ↔
      ∃ f : Fin k → G, (∀ i, f i ∈ X) ∧ ∑ i, f i = x := by
  induction k generalizing x with
  | zero =>
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa [constantIteratedSumset] using hx
        exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
          by simpa using hx0.symm⟩
      · rintro ⟨f, hf, rfl⟩
        simp [constantIteratedSumset]
  | succ k ih =>
      rw [show constantIteratedSumset X (k + 1) =
          constantIteratedSumset X k + X by
        exact Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X) k]
      constructor
      · intro hx
        obtain ⟨y, hy, a, ha, hya⟩ :=
          Erdos186.CFP.mem_pointwise_add_iff.mp hx
        obtain ⟨f, hf, hfsum⟩ := ih.mp hy
        refine ⟨Fin.cons a f, ?_, ?_⟩
        · intro i
          refine Fin.cases ha (fun j ↦ hf j) i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, hfsum]
          exact (add_comm a y).trans hya
      · rintro ⟨f, hf, rfl⟩
        apply Erdos186.CFP.mem_pointwise_add_iff.mpr
        refine ⟨∑ i : Fin k, f i.succ, ?_, f 0, hf 0, ?_⟩
        · apply ih.mpr
          exact ⟨fun i ↦ f i.succ, fun i ↦ hf i.succ, rfl⟩
        · simp [Fin.sum_univ_succ, add_comm]

/-- Constant iterated sumsets are monotone in their generator set. -/
theorem constantIteratedSumset_mono_set {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {X Y : Finset G} (hXY : X ⊆ Y) (k : ℕ) :
    constantIteratedSumset X k ⊆ constantIteratedSumset Y k := by
  intro z hz
  obtain ⟨f, hf, rfl⟩ := mem_constantIteratedSumset_iff.mp hz
  exact mem_constantIteratedSumset_iff.mpr
    ⟨f, fun i ↦ hXY (hf i), rfl⟩

/-- Additive homomorphisms commute with constant iterated sumsets. -/
theorem image_constantIteratedSumset {G Q : Type*}
    [AddCommMonoid G] [AddCommMonoid Q] [DecidableEq G] [DecidableEq Q]
    (f : G →+ Q) (X : Finset G) (k : ℕ) :
    (constantIteratedSumset X k).image f =
      constantIteratedSumset (X.image f) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show constantIteratedSumset X (k + 1) =
          constantIteratedSumset X k + X by
        exact Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X) k]
      rw [show constantIteratedSumset (X.image f) (k + 1) =
          constantIteratedSumset (X.image f) k + X.image f by
        exact Erdos186.CFP.iteratedSumset_succ (fun _ ↦ X.image f) k]
      ext y
      constructor
      · intro hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨u, hu, v, hv, rfl⟩ :=
          Erdos186.CFP.mem_pointwise_add_iff.mp hz
        apply Erdos186.CFP.mem_pointwise_add_iff.mpr
        refine ⟨f u, ?_, f v, ?_, ?_⟩
        · rw [← ih]
          exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
        · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        · exact (map_add f u v).symm
      · intro hy
        obtain ⟨u, hu, v, hv, huv⟩ :=
          Erdos186.CFP.mem_pointwise_add_iff.mp hy
        rw [← ih] at hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        apply Finset.mem_image.mpr
        refine ⟨u' + v', ?_, ?_⟩
        · exact Erdos186.CFP.mem_pointwise_add_iff.mpr
            ⟨u', hu', v', hv', rfl⟩
        · simpa using huv

/-- If zero belongs to the summand, constant iterated sumsets are monotone in
the number of summands. -/
theorem constantIteratedSumset_mono {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {X : Finset G} (hzero : 0 ∈ X) {a b : ℕ} (hab : a ≤ b) :
    constantIteratedSumset X a ⊆ constantIteratedSumset X b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction c with
  | zero => simpa using (Finset.Subset.rfl :
      constantIteratedSumset X a ⊆ constantIteratedSumset X a)
  | succ c ih =>
      have ih' : constantIteratedSumset X a ⊆
          constantIteratedSumset X (a + c) :=
        ih (Nat.le_add_right a c)
      have hstep : constantIteratedSumset X (a + c) ⊆
          constantIteratedSumset X (a + c + 1) := by
        rw [show constantIteratedSumset X (a + c + 1) =
            constantIteratedSumset X (a + c) + X by
          exact Erdos186.CFP.iteratedSumset_succ _ _]
        intro x hx
        simpa using Finset.add_mem_add hx hzero
      intro x hx
      simpa [Nat.add_assoc] using hstep (ih' hx)

/-- In an arbitrary (possibly infinite) abelian group, a finite generating
set containing zero either grows at every addition or has already filled the
whole group.  Consequently, if its `h`-fold sumset has at most `K ≤ h`
elements, it has filled the group. -/
theorem mem_constantIteratedSumset_of_card_le {G : Type*} [AddCommGroup G]
    [DecidableEq G] (X : Finset G) (hzero : 0 ∈ X)
    (hgen : AddSubgroup.closure (X : Set G) = ⊤)
    {h K : ℕ} (hKh : K ≤ h)
    (hcard : (constantIteratedSumset X h).card ≤ K) :
    ∀ g : G, g ∈ constantIteratedSumset X h := by
  classical
  have hex : ∃ j < h,
      (constantIteratedSumset X (j + 1)).card =
        (constantIteratedSumset X j).card := by
    by_contra hnone
    push Not at hnone
    have hgrowth : ∀ j < h,
        (constantIteratedSumset X j).card <
          (constantIteratedSumset X (j + 1)).card := by
      intro j hj
      have hmono := Finset.card_le_card
        (constantIteratedSumset_mono hzero (Nat.le_succ j))
      exact lt_of_le_of_ne hmono (Ne.symm (hnone j hj))
    have hlower : ∀ j ≤ h, j + 1 ≤ (constantIteratedSumset X j).card := by
      intro j hj
      induction j with
      | zero => simp [constantIteratedSumset]
      | succ j ih =>
          have hjh : j < h := Nat.lt_of_succ_le hj
          have hij := ih (Nat.le_of_lt hjh)
          have hstep := hgrowth j hjh
          omega
    have := hlower h le_rfl
    omega
  obtain ⟨j, hjh, hcardeq⟩ := hex
  let S := constantIteratedSumset X j
  have hsum : S + X = S := by
    have hsubset : S ⊆ S + X := by
      intro s hs
      simpa using Finset.add_mem_add hs hzero
    symm
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [S, constantIteratedSumset,
      Erdos186.CFP.iteratedSumset_succ] using hcardeq.le
  have hXstab : (X : Set G) ⊆ Erdos186.CFP.addStabilizer S := by
    intro x hx
    apply AddAction.mem_stabilizer_finset'.mpr
    intro s hs
    have hsx : s + x ∈ S + X := Finset.add_mem_add hs hx
    rw [hsum] at hsx
    simpa [add_comm] using hsx
  have hstab : Erdos186.CFP.addStabilizer S = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen, AddSubgroup.closure_le]
    exact hXstab
  have hSnonempty : S.Nonempty := by
    have h0zero : (0 : G) ∈ constantIteratedSumset X 0 := by simp
    exact ⟨0, constantIteratedSumset_mono hzero (Nat.zero_le j) h0zero⟩
  obtain ⟨s, hs⟩ := hSnonempty
  intro g
  have htrans : g - s ∈ Erdos186.CFP.addStabilizer S := by
    rw [hstab]
    exact trivial
  have hgS := (Erdos186.CFP.mem_addStabilizer_iff.mp htrans s).2 hs
  have hSj : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono hzero (Nat.le_of_lt hjh)
  apply hSj
  simpa using hgS

/-- The `h`-fold sumset of a generating set in a subgroup quotient.  Packaging
the finset as a noncomputable definition keeps the classical quotient equality
instance out of theorem statements using its cardinality. -/
noncomputable def quotientGeneratorIteratedSumset {G : Type*}
    [AddCommGroup G] (H Gamma : AddSubgroup G) (X : Finset Gamma)
    (h : ℕ) : Finset (Gamma ⧸ H.addSubgroupOf Gamma) := by
  classical
  exact constantIteratedSumset
    (X.image (QuotientAddGroup.mk' (H.addSubgroupOf Gamma))) h

/-- Packing an `h`-fold quotient sumset against any subgroup-valued subset
of the same ambient `h`-fold sumset puts their product inside the `2h`-fold
ambient sumset. -/
theorem quotientGeneratorIteratedSumset_card_mul_le_twice {G : Type*}
    [AddCommGroup G] [DecidableEq G] {H Gamma : AddSubgroup G}
    (_hHGamma : H ≤ Gamma)
    (X : Finset Gamma) (S : Finset Gamma) (h : ℕ)
    (hSsub : S ⊆ constantIteratedSumset X h)
    (hSH : ∀ s ∈ S, (s.1 : G) ∈ H) :
    (quotientGeneratorIteratedSumset H Gamma X h).card * S.card ≤
      (constantIteratedSumset X (2 * h)).card := by
  classical
  let J := H.addSubgroupOf Gamma
  let T := constantIteratedSumset X h
  let U := constantIteratedSumset X (2 * h)
  have hSJ : ∀ s ∈ S, s ∈ J := by
    intro s hs
    exact hSH s hs
  have hadd : ∀ t ∈ T, ∀ s ∈ S, t + s ∈ U := by
    intro t ht s hs
    have hmem : t + s ∈ T + T :=
      Erdos186.CFP.mem_pointwise_add_iff.mpr
        ⟨t, ht, s, hSsub hs, rfl⟩
    rw [constantIteratedSumset_add X h h] at hmem
    simpa [U, two_mul] using hmem
  have hp := card_quotient_image_mul_card_le J T S U hSJ hadd
  change ((T.image (QuotientAddGroup.mk' J)).card * S.card ≤ U.card) at hp
  rw [image_constantIteratedSumset] at hp
  simpa [quotientGeneratorIteratedSumset, J, T, U] using hp

/-- A bounded iterated sumset in the quotient bounds relative subgroup
index.  Unlike the printed coordinate-projection sentence in CFP Lemma 2.32,
this statement is valid for arbitrary sublattices and does not choose a
preferred coordinate. -/
theorem relIndex_ne_zero_and_le_of_quotient_sumset {G : Type*}
    [AddCommGroup G] {H Gamma : AddSubgroup G}
    (X : Finset Gamma) (hzero : (0 : Gamma) ∈ X)
    (hgen : AddSubgroup.closure (X : Set Gamma) = ⊤)
    {h K : ℕ} (hKh : K ≤ h)
    (hcard : (quotientGeneratorIteratedSumset H Gamma X h).card ≤ K) :
    H.relIndex Gamma ≠ 0 ∧ H.relIndex Gamma ≤ K := by
  classical
  let J := H.addSubgroupOf Gamma
  let Q := Gamma ⧸ J
  let q : Gamma →+ Q := QuotientAddGroup.mk' J
  let Y : Finset Q := X.image q
  have hzeroY : (0 : Q) ∈ Y := by
    exact Finset.mem_image.mpr ⟨0, hzero, map_zero q⟩
  have hgenY : AddSubgroup.closure (Y : Set Q) = ⊤ := by
    rw [show (Y : Set Q) = q '' (X : Set Gamma) by
      simp [Y], ← AddMonoidHom.map_closure, hgen]
    exact AddSubgroup.map_top_of_surjective q
      (QuotientAddGroup.mk'_surjective J)
  have hall : ∀ y : Q, y ∈ constantIteratedSumset Y h :=
    mem_constantIteratedSumset_of_card_le Y hzeroY hgenY hKh (by
      simpa [quotientGeneratorIteratedSumset, J, Q, q, Y] using hcard)
  let S := constantIteratedSumset Y h
  let cover : S → Q := fun y ↦ y.1
  have hcover : Function.Surjective cover := by
    intro y
    exact ⟨⟨y, hall y⟩, rfl⟩
  let : Finite Q := Finite.of_surjective cover hcover
  let : Fintype Q := Fintype.ofFinite Q
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall hall
  have hrel : H.relIndex Gamma = Fintype.card Q := by
    change Nat.card Q = Fintype.card Q
    exact Nat.card_eq_fintype_card
  rw [hrel]
  have hQcard : Fintype.card Q = S.card := by rw [hSuniv, Finset.card_univ]
  constructor
  · rw [hQcard]
    exact Finset.card_ne_zero.mpr ⟨0,
      constantIteratedSumset_mono hzeroY (Nat.zero_le h) (by simp)⟩
  · rw [hQcard]
    simpa [quotientGeneratorIteratedSumset, S, Y, q, Q, J] using hcard

/-- The finite coordinate generators of a generated subgroup, with zero
adjoined so that iterated sumsets are monotone in the number of summands. -/
noncomputable def coordinateGeneratorFinset {α : Type*} [DecidableEq α]
    {d : ℕ} (φ : α → LatticePoint d) (A : Finset α) :
    Finset (Stability.generatedSubgroup φ A) := by
  classical
  exact insert 0 (A.attach.image fun a ↦
    ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩)

@[simp]
theorem zero_mem_coordinateGeneratorFinset {α : Type*} [DecidableEq α]
    {d : ℕ} (φ : α → LatticePoint d) (A : Finset α) :
    (0 : Stability.generatedSubgroup φ A) ∈ coordinateGeneratorFinset φ A := by
  classical
  simp [coordinateGeneratorFinset]

/-- The displayed coordinate generators generate the whole generated
subgroup, viewed as an abstract additive group. -/
theorem coordinateGeneratorFinset_generates {α : Type*} [DecidableEq α]
    {d : ℕ} (φ : α → LatticePoint d) (A : Finset α) :
    AddSubgroup.closure (coordinateGeneratorFinset φ A :
      Set (Stability.generatedSubgroup φ A)) = ⊤ := by
  classical
  apply top_unique
  intro x _hx
  have hx : (x : LatticePoint d) ∈
      AddSubgroup.closure (φ '' (A : Set α)) := x.property
  refine AddSubgroup.closure_induction (p := fun y hy ↦
      (⟨y, hy⟩ : Stability.generatedSubgroup φ A) ∈
        AddSubgroup.closure
          (coordinateGeneratorFinset φ A :
            Set (Stability.generatedSubgroup φ A))) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    rw [show coordinateGeneratorFinset φ A =
        insert 0 (A.attach.image fun a ↦
          ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩) by
      rfl]
    apply Finset.mem_insert.mpr
    right
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, by simp, rfl⟩
  · apply AddSubgroup.subset_closure
    rw [show coordinateGeneratorFinset φ A =
        insert 0 (A.attach.image fun a ↦
          ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩) by
      rfl]
    exact Finset.mem_insert_self
      (0 : Stability.generatedSubgroup φ A)
      (A.attach.image fun a ↦
        ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩)
  · intro y z hy hz hy' hz'
    exact AddSubgroup.add_mem _ hy' hz'
  · intro y hy hy'
    exact AddSubgroup.neg_mem _ hy'

/-- Concrete subgroup-index bridge for the coordinate subgroups used in
CFP Lemma 2.32.  Once the indicated quotient sumset cardinality is bounded,
finite index and the same bound follow with no rank-certificate assumption. -/
theorem generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    {α : Type*} [DecidableEq α] {d : ℕ}
    (φ : α → LatticePoint d) {A B : Finset α} (_hBA : B ⊆ A)
    {h K : ℕ} (hKh : K ≤ h)
    (hcard :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup φ B)
        (Stability.generatedSubgroup φ A)
        (coordinateGeneratorFinset φ A) h).card ≤ K) :
    (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≠ 0 ∧
      (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≤ K := by
  apply relIndex_ne_zero_and_le_of_quotient_sumset
    (X := coordinateGeneratorFinset φ A)
  · exact zero_mem_coordinateGeneratorFinset φ A
  · exact coordinateGeneratorFinset_generates φ A
  · exact hKh
  · exact hcard

/-- Generators coming from a subset, but regarded in the coordinate subgroup
generated by a fixed ambient set. -/
noncomputable def ambientSubsetGeneratorFinset {α : Type*} [DecidableEq α]
    {d : ℕ} (φ : α → LatticePoint d) (A B : Finset α) (hBA : B ⊆ A) :
    Finset (Stability.generatedSubgroup φ A) := by
  classical
  exact insert 0 (B.attach.image fun b ↦
    ⟨φ b.1, Stability.image_mem_generatedSubgroup (hBA b.2)⟩)

theorem ambientSubsetGeneratorFinset_subset {α : Type*} [DecidableEq α]
    {d : ℕ} (φ : α → LatticePoint d) {A B : Finset α} (hBA : B ⊆ A) :
    ambientSubsetGeneratorFinset φ A B hBA ⊆ coordinateGeneratorFinset φ A := by
  classical
  intro x hx
  rw [show ambientSubsetGeneratorFinset φ A B hBA =
      insert 0 (B.attach.image fun b ↦
        ⟨φ b.1, Stability.image_mem_generatedSubgroup (hBA b.2)⟩) by rfl]
    at hx
  rw [show coordinateGeneratorFinset φ A =
      insert 0 (A.attach.image fun a ↦
        ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩) by rfl]
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert_self
      (0 : Stability.generatedSubgroup φ A)
      (A.attach.image fun a ↦
        ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩)
  · obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_insert.mpr
    right
    exact Finset.mem_image.mpr ⟨⟨b.1, hBA b.2⟩, by simp, rfl⟩

/-- Every subset generator lies in the subgroup generated by that subset. -/
theorem ambientSubsetGeneratorFinset_mem_generatedSubgroup
    {α : Type*} [DecidableEq α] {d : ℕ}
    (φ : α → LatticePoint d) {A B : Finset α} (hBA : B ⊆ A)
    {x : Stability.generatedSubgroup φ A}
    (hx : x ∈ ambientSubsetGeneratorFinset φ A B hBA) :
    (x.1 : LatticePoint d) ∈ Stability.generatedSubgroup φ B := by
  classical
  rw [show ambientSubsetGeneratorFinset φ A B hBA =
      insert 0 (B.attach.image fun b ↦
        ⟨φ b.1, Stability.image_mem_generatedSubgroup (hBA b.2)⟩) by rfl]
    at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact AddSubgroup.zero_mem _
  · obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hx
    exact Stability.image_mem_generatedSubgroup b.2

/-- Therefore every iterated subset-coordinate sum lies in the subset's
generated subgroup. -/
theorem ambientSubsetIteratedSumset_mem_generatedSubgroup
    {α : Type*} [DecidableEq α] {d h : ℕ}
    (φ : α → LatticePoint d) {A B : Finset α} (hBA : B ⊆ A)
    {x : Stability.generatedSubgroup φ A}
    (hx : x ∈ constantIteratedSumset
      (ambientSubsetGeneratorFinset φ A B hBA) h) :
    (x.1 : LatticePoint d) ∈ Stability.generatedSubgroup φ B := by
  obtain ⟨f, hf, hsum⟩ := mem_constantIteratedSumset_iff.mp hx
  rw [← hsum]
  change (Stability.generatedSubgroup φ A).subtype (∑ i, f i) ∈
    Stability.generatedSubgroup φ B
  rw [map_sum]
  apply AddSubgroup.sum_mem
  intro i _hi
  exact ambientSubsetGeneratorFinset_mem_generatedSubgroup φ hBA (hf i)

/-- Linear evaluation by the GAP differences, omitting the affine offset. -/
def stepEvaluation {d : ℕ} (P : GAP 1 d) : LatticePoint d →+ ℤ where
  toFun c := ∑ i, c i * P.steps i 0
  map_zero' := by simp
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Evaluation of an identification coordinate recovers the represented
integer after subtracting the GAP offset. -/
theorem stepEvaluation_identificationMap {A : Finset ℤ} {d : ℕ}
    (B : BoundingBox.BoundingGAP A d) (hproper : B.progression.Proper)
    (z : {z // z ∈ A}) :
    stepEvaluation B.progression (B.identificationMap hproper z) =
      z.1 - B.progression.offset 0 := by
  have hz := congrFun (B.coordPoint_coordinateMap hproper z) 0
  change B.progression.offset 0 +
      ∑ i, ((B.progression.coordinateMap hproper
        ⟨BoundingBox.intPoint z, B.bounds z⟩ i : ℕ) : ℤ) *
          B.progression.steps i 0 = z.1 at hz
  change (∑ i, B.identificationMap hproper z i *
    B.progression.steps i 0) = _
  simp only [B.identificationMap_apply hproper z]
  omega

/-- Coordinate sums of an identified subset are at least as numerous as its
ordinary integer sums: affine evaluation sends them onto a translate of the
integer multifold sumset. -/
theorem card_multifoldSumset_le_ambientSubsetIteratedSumset
    {A B : Finset ℤ} {d h : ℕ} (hBA : B ⊆ A)
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (φ : ℤ → LatticePoint d)
    (hφ : ∀ z (hz : z ∈ A), φ z =
      P.identificationMap hproper ⟨z, hz⟩) :
    (GrowthLemmas.multifoldSumset h B).card ≤
      (constantIteratedSumset
        (ambientSubsetGeneratorFinset φ A B hBA) h).card := by
  classical
  let Gamma := Stability.generatedSubgroup φ A
  let X := ambientSubsetGeneratorFinset φ A B hBA
  let S := constantIteratedSumset X h
  let e : Gamma →+ ℤ := (stepEvaluation P.progression).comp Gamma.subtype
  let τ : ℤ → ℤ := fun z ↦ z - (h : ℤ) * P.progression.offset 0
  let F := GrowthLemmas.multifoldSumset h B
  let FT : Finset ℤ := F.image τ
  have hτ : Function.Injective τ := by
    intro x y hxy
    dsimp [τ] at hxy
    omega
  have hFTcard : FT.card = F.card := by
    dsimp [FT]
    exact Finset.card_image_of_injective F hτ
  have hFTsub : FT ⊆ S.image e := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, hsum⟩ := GrowthLemmas.mem_multifoldSumset_iff.mp hz
    let g : Fin h → Gamma := fun i ↦
      ⟨φ (f i), Stability.image_mem_generatedSubgroup (hBA (hf i))⟩
    have hg (i : Fin h) : g i ∈ X := by
      rw [show X = insert 0 (B.attach.image fun b ↦
          ⟨φ b.1, Stability.image_mem_generatedSubgroup (hBA b.2)⟩) by
        rfl]
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_image.mpr ⟨⟨f i, hf i⟩, by simp, rfl⟩
    have hgsum : (∑ i, g i) ∈ S := by
      apply mem_constantIteratedSumset_iff.mpr
      exact ⟨g, hg, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨∑ i, g i, hgsum, ?_⟩
    dsimp [e]
    have hcoeg : Gamma.subtype (∑ i, g i) =
        ∑ i, Gamma.subtype (g i) := by
      simpa using map_sum Gamma.subtype g (Finset.univ : Finset (Fin h))
    change stepEvaluation P.progression (Gamma.subtype (∑ i, g i)) = τ z
    rw [hcoeg]
    change stepEvaluation P.progression (∑ i, φ (f i)) = τ z
    rw [map_sum]
    have heval (i : Fin h) :
        stepEvaluation P.progression (φ (f i)) =
          f i - P.progression.offset 0 := by
      rw [hφ (f i) (hBA (hf i))]
      exact stepEvaluation_identificationMap P hproper
        ⟨f i, hBA (hf i)⟩
    simp_rw [heval]
    dsimp [τ]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  calc
    F.card = FT.card := hFTcard.symm
    _ ≤ (S.image e).card := Finset.card_le_card hFTsub
    _ ≤ S.card := Finset.card_image_le

/-- Iterated sums of the ambient coordinate generators fit in the displayed
coefficient dilation of the proper bounding box. -/
theorem card_coordinateGeneratorIteratedSumset_le_dilate_volume
    {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (φ : ℤ → LatticePoint d)
    (hφ : ∀ z (hz : z ∈ A), φ z =
      P.identificationMap hproper ⟨z, hz⟩) (k : ℕ) :
    (constantIteratedSumset (coordinateGeneratorFinset φ A) k).card ≤
      (P.progression.dilate k).volume := by
  classical
  let Gamma := Stability.generatedSubgroup φ A
  let X := coordinateGeneratorFinset φ A
  have hXbox : X.image Gamma.subtype ⊆ coordinateBox P.progression 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [show X = insert 0 (A.attach.image fun a ↦
        ⟨φ a.1, Stability.image_mem_generatedSubgroup a.2⟩) by rfl] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_mem_coordinateBox_scale P.progression 1
    · obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
      change φ a.1 ∈ coordinateBox P.progression 1
      rw [hφ a.1 a.2]
      exact identificationMap_mem_coordinateBox P hproper a
  have hbox := card_constantIteratedSumset_le_coordinateBox
    P.progression (X.image Gamma.subtype) hXbox k
  let S := constantIteratedSumset X k
  have hcardImage : S.card = (S.image Gamma.subtype).card := by
    symm
    exact Finset.card_image_of_injective S Gamma.subtype_injective
  calc
    (constantIteratedSumset (coordinateGeneratorFinset φ A) k).card =
        S.card := rfl
    _ = (S.image Gamma.subtype).card := hcardImage
    _ = (constantIteratedSumset (X.image Gamma.subtype) k).card := by
      rw [image_constantIteratedSumset]
    _ ≤ (P.progression.dilate k).volume := hbox

/-- The concrete quotient-sumset bound required by the finite-index bridge.
It combines coordinate coset packing, the lower bound supplied by the
accessible subset, and the expanded-box estimate above. -/
theorem HApproximation.quotientGeneratorIteratedSumset_card_le
    {A B : Finset ℤ} {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (W : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d)
    (P : BoundingBox.BoundingGAP A d)
    (hP : P = BoundingBox.dBoundingBox A d hd)
    (hproper : P.progression.Proper)
    (φ : ℤ → LatticePoint d)
    (hφ : ∀ z (hz : z ∈ A), φ z =
      P.identificationMap hproper ⟨z, hz⟩) :
    (quotientGeneratorIteratedSumset
      (Stability.generatedSubgroup φ B)
      (Stability.generatedSubgroup φ A)
      (coordinateGeneratorFinset φ A) h).card ≤
        4 * (6 * scaleDen) ^ d := by
  classical
  let X := coordinateGeneratorFinset φ A
  let XB := ambientSubsetGeneratorFinset φ A B hBA
  let S := constantIteratedSumset XB h
  have hSsub : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono_set
      (ambientSubsetGeneratorFinset_subset φ hBA) h
  have hSH : ∀ s ∈ S,
      (s.1 : LatticePoint d) ∈ Stability.generatedSubgroup φ B := by
    intro s hs
    exact ambientSubsetIteratedSumset_mem_generatedSubgroup φ hBA hs
  have hpack := quotientGeneratorIteratedSumset_card_mul_le_twice
    (Stability.generatedSubgroup_mono hBA) X S h hSsub hSH
  have hsumLower : (GrowthLemmas.multifoldSumset h B).card ≤ S.card := by
    exact card_multifoldSumset_le_ambientSubsetIteratedSumset
      hBA P hproper φ hφ
  have hambientUpper : (constantIteratedSumset X (2 * h)).card ≤
      (P.progression.dilate (2 * h)).volume :=
    card_coordinateGeneratorIteratedSumset_le_dilate_volume
      P hproper φ hφ (2 * h)
  have hvolume : (P.progression.dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d) *
        (GrowthLemmas.multifoldSumset h B).card := by
    subst P
    exact HApproximation.two_mul_dilate_volume_le_indexBound_mul_card
      hstable hBA hloss W hd hdD hhn hA hnumeric
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup φ B)
        (Stability.generatedSubgroup φ A) X h).card * S.card ≤
        (4 * (6 * scaleDen) ^ d) * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ (P.progression.dilate (2 * h)).volume := hambientUpper
      _ ≤ (4 * (6 * scaleDen) ^ d) *
          (GrowthLemmas.multifoldSumset h B).card := hvolume
      _ ≤ (4 * (6 * scaleDen) ^ d) * S.card := by gcongr
  have hSpos : 0 < S.card := by
    have hzeroB : 0 ∈ GrowthLemmas.multifoldSumset h B :=
      GrowthLemmas.zero_mem_multifoldSumset W.zero_mem h
    have : 0 < (GrowthLemmas.multifoldSumset h B).card :=
      Finset.card_pos.mpr ⟨0, hzeroB⟩
    omega
  dsimp [X] at hmul ⊢
  exact Nat.le_of_mul_le_mul_right hmul hSpos

/-- The quotient packing bound converted to the finite relative-index bound
used by the pruning depth. -/
theorem HApproximation.generatedSubgroup_relIndex_ne_zero_and_le
    {A B : Finset ℤ} {x D n h d scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (W : HDimension.HApproximation B h d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hhn : h ≤ n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d)
    (P : BoundingBox.BoundingGAP A d)
    (hP : P = BoundingBox.dBoundingBox A d hd)
    (hproper : P.progression.Proper)
    (φ : ℤ → LatticePoint d)
    (hφ : ∀ z (hz : z ∈ A), φ z =
      P.identificationMap hproper ⟨z, hz⟩)
    (hlarge : 4 * (6 * scaleDen) ^ d ≤ h) :
    (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≠ 0 ∧
      (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≤
        4 * (6 * scaleDen) ^ d := by
  apply generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    φ hBA hlarge
  exact HApproximation.quotientGeneratorIteratedSumset_card_le
    hstable hBA hloss W hd hdD hhn hA hnumeric P hP hproper φ hφ

/-- Rank-flexible, uniform-rank version of the complete Lemma 2.32 index
estimate.  The ambient box has relevant rank `d`; the accessible subset may
use its own certified rank `e`. -/
theorem HApproximation.generatedSubgroup_relIndex_general_ne_zero_and_le
    {A B : Finset ℤ} {x D n h d e scaleNum scaleDen : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (WA : HDimension.HApproximation A h d scaleNum scaleDen)
    (WB : HDimension.HApproximation B h e scaleNum scaleDen)
    (hd : 0 < d) (he : 0 < e) (hdD : d ≤ D) (heD : e ≤ D)
    (hhn : h ≤ n) (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericB :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e)
    (P : BoundingBox.BoundingGAP A d)
    (hP : P = BoundingBox.dBoundingBox A d hd)
    (hproper : P.progression.Proper)
    (φ : ℤ → LatticePoint d)
    (hφ : ∀ z (hz : z ∈ A), φ z =
      P.identificationMap hproper ⟨z, hz⟩)
    (hlarge : 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ h) :
    (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≠ 0 ∧
      (Stability.generatedSubgroup φ B).relIndex
          (Stability.generatedSubgroup φ A) ≤
        4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D := by
  classical
  let X := coordinateGeneratorFinset φ A
  let XB := ambientSubsetGeneratorFinset φ A B hBA
  let S := constantIteratedSumset XB h
  have hSsub : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono_set
      (ambientSubsetGeneratorFinset_subset φ hBA) h
  have hSH : ∀ s ∈ S,
      (s.1 : LatticePoint d) ∈ Stability.generatedSubgroup φ B := by
    intro s hs
    exact ambientSubsetIteratedSumset_mem_generatedSubgroup φ hBA hs
  have hpack := quotientGeneratorIteratedSumset_card_mul_le_twice
    (Stability.generatedSubgroup_mono hBA) X S h hSsub hSH
  have hsumLower : (GrowthLemmas.multifoldSumset h B).card ≤ S.card :=
    card_multifoldSumset_le_ambientSubsetIteratedSumset
      hBA P hproper φ hφ
  have hambientUpper : (constantIteratedSumset X (2 * h)).card ≤
      (P.progression.dilate (2 * h)).volume :=
    card_coordinateGeneratorIteratedSumset_le_dilate_volume
      P hproper φ hφ (2 * h)
  have hvolume : (P.progression.dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
    subst P
    exact HApproximation.two_mul_dilate_volume_le_general_indexBound_mul_card
      hstable hBA hloss WA WB hd he heD hhn hA hnumericB
  let Kde := 4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e
  let KD := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hKde : Kde ≤ KD := by
    dsimp [Kde, KD]
    have h6pos : 1 ≤ 6 * scaleDen := by
      have := WA.scaleDen_pos
      omega
    have h4pos : 1 ≤ 4 * scaleDen := by
      have := WA.scaleDen_pos
      omega
    have hp6 : (6 * scaleDen) ^ d ≤ (6 * scaleDen) ^ D :=
      pow_le_pow_right' h6pos hdD
    have hp4 : (4 * scaleDen) ^ e ≤ (4 * scaleDen) ^ D :=
      pow_le_pow_right' h4pos heD
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp6) hp4
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup φ B)
        (Stability.generatedSubgroup φ A) X h).card * S.card ≤
        KD * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ (P.progression.dilate (2 * h)).volume := hambientUpper
      _ ≤ Kde * (GrowthLemmas.multifoldSumset h B).card := hvolume
      _ ≤ Kde * S.card := by gcongr
      _ ≤ KD * S.card := Nat.mul_le_mul_right S.card hKde
  have hSpos : 0 < S.card := by
    have hzeroB : 0 ∈ GrowthLemmas.multifoldSumset h B :=
      GrowthLemmas.zero_mem_multifoldSumset WB.zero_mem h
    have : 0 < (GrowthLemmas.multifoldSumset h B).card :=
      Finset.card_pos.mpr ⟨0, hzeroB⟩
    omega
  have hcard :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup φ B)
        (Stability.generatedSubgroup φ A)
        (coordinateGeneratorFinset φ A) h).card ≤ KD := by
    dsimp [X] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hSpos
  apply generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    φ hBA (by simpa [KD] using hlarge)
  simpa [KD] using hcard

/-- Finite-index control on every subset reachable within `deletionCap`.
This is the exact output of the sumset-density/index estimate in the proof of
CFP Lemma 2.32. -/
structure AccessibleSpanIndexBound (A : Finset ℤ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d)
    (deletionCap indexBound : ℕ) : Prop where
  finite : ∀ {B : Finset ℤ}, B ⊆ A →
    A.card ≤ B.card + deletionCap → 0 ∈ B →
    ∀ d : {d // d ∈ relevant},
      (Stability.generatedSubgroup (phi d.1) B).relIndex
        (Stability.generatedSubgroup (phi d.1) A) ≠ 0
  index_le : ∀ {B : Finset ℤ}, B ⊆ A →
    A.card ≤ B.card + deletionCap → 0 ∈ B →
    ∀ d : {d // d ∈ relevant},
      (Stability.generatedSubgroup (phi d.1) B).relIndex
        (Stability.generatedSubgroup (phi d.1) A) ≤ indexBound

/-- A family of positive relevant ranks bounded by `D` has at most `D`
members.  This converts the profile-height bound into one depending only on
the uniform rank bound, as in CFP Lemma 2.32. -/
theorem relevant_card_le_rankBound {relevant : Finset ℕ} {D : ℕ}
    (hpositive : ∀ {d}, d ∈ relevant → 0 < d)
    (hupper : ∀ d : {d // d ∈ relevant}, d.1 ≤ D) :
    relevant.card ≤ D := by
  have hsub : relevant ⊆ Finset.Icc 1 D := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨hpositive hd, hupper ⟨d, hd⟩⟩
  calc
    relevant.card ≤ (Finset.Icc 1 D).card := Finset.card_le_card hsub
    _ = D := by simp [Nat.card_Icc]

/-- The quotient-packing argument supplies the accessible index bound directly
from the actual `h`-approximations of the ambient set and its accessible
subsets.  In particular, the hypothesis here is additive-combinatorial data,
not a subgroup-rank or pruning certificate.

The ambient relevant rank is `d`; an accessible subset may use a different
rank `e ≤ D`.  This rank-flexible form is what is needed in CFP Lemma 2.32. -/
theorem accessibleSpanIndexBound_of_hApproximations
    {A : Finset ℤ} {x D n scaleNum scaleDen deletionCap : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hAt : {d // d ∈ relevant} → ℕ)
    (hambient : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation A (hAt d) d.1 scaleNum scaleDen)
    (hrank_le : ∀ d : {d // d ∈ relevant}, d.1 ≤ D)
    (hh_le : ∀ d : {d // d ∈ relevant}, hAt d ≤ n)
    (hlarge : ∀ d : {d // d ∈ relevant},
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ hAt d)
    (haccessible : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card + deletionCap → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e)
    (hcap : deletionCap ≤ x) :
    AccessibleSpanIndexBound A relevant
      (Stability.minimalIdentificationFamily hproper) deletionCap
      (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) := by
  classical
  let K := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have bound {B : Finset ℤ} (hBA : B ⊆ A)
      (hloss : A.card ≤ B.card + deletionCap) (hzero : 0 ∈ B)
      (d : {d // d ∈ relevant}) :
      (Stability.generatedSubgroup
            (Stability.minimalIdentificationFamily hproper d.1) B).relIndex
          (Stability.generatedSubgroup
            (Stability.minimalIdentificationFamily hproper d.1) A) ≠ 0 ∧
        (Stability.generatedSubgroup
            (Stability.minimalIdentificationFamily hproper d.1) B).relIndex
          (Stability.generatedSubgroup
            (Stability.minimalIdentificationFamily hproper d.1) A) ≤ K := by
    obtain ⟨e, he, heD, W, hnumeric⟩ :=
      haccessible hBA hloss hzero d
    have hlossx : A.card ≤ B.card + x :=
      hloss.trans (Nat.add_le_add_left hcap B.card)
    have hresult :=
      HApproximation.generatedSubgroup_relIndex_general_ne_zero_and_le
        hstable hBA hlossx (hambient d) W
        (hproper.positive d.property) he (hrank_le d) heD
        (hh_le d) hA hnumeric
        (BoundingBox.dBoundingBox A d.1 (hproper.positive d.property)) rfl
        (hproper.proper d.property)
        (Stability.minimalIdentificationFamily hproper d.1)
        (fun z hz ↦ Stability.minimalIdentificationFamily_apply
          hproper d.property hz)
        (hlarge d)
    simpa [K] using hresult
  refine ⟨?_, ?_⟩
  · intro B hBA hloss hzero d
    exact (bound hBA hloss hzero d).1
  · intro B hBA hloss hzero d
    simpa [K] using (bound hBA hloss hzero d).2

/-- Data supplied by a failed span-robustness test. -/
structure SpanPruneWitness (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) where
  carrier : Finset ℤ
  subset : carrier ⊆ A
  loss : A.card ≤ carrier.card + budget
  zero_mem : 0 ∈ carrier
  changes : ∃ d : {d // d ∈ relevant},
    Stability.generatedSubgroup (phi d.1) carrier ≠
      Stability.generatedSubgroup (phi d.1) A

/-- A failed span-robustness test produces a pruning witness. -/
theorem nonempty_spanPruneWitnessOfNot {A : Finset ℤ} {budget : ℕ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hnot : ¬ Stability.SpanRobust 0 A budget relevant phi) :
    Nonempty (SpanPruneWitness A budget relevant phi) := by
  classical
  unfold Stability.SpanRobust at hnot
  push Not at hnot
  obtain ⟨d, hd, B, hBA, hcard, hzero, hne⟩ := hnot
  exact ⟨⟨B, hBA, hcard, hzero, ⟨⟨d, hd⟩, hne⟩⟩⟩

/-- A chosen pruning witness for a failed robustness test. -/
noncomputable def spanPruneWitnessOfNot {A : Finset ℤ} {budget : ℕ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hnot : ¬ Stability.SpanRobust 0 A budget relevant phi) :
    SpanPruneWitness A budget relevant phi :=
  Classical.choice (nonempty_spanPruneWitnessOfNot hnot)

/-- One step selected whenever span robustness fails. -/
noncomputable def spanPruneNext (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) :
    Finset ℤ := by
  classical
  by_cases h : Stability.SpanRobust 0 A budget relevant phi
  · exact A
  · exact (spanPruneWitnessOfNot h).carrier

/-- The chosen step is a subset of the current set. -/
theorem spanPruneNext_subset (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) :
    spanPruneNext A budget relevant phi ⊆ A := by
  classical
  unfold spanPruneNext
  split_ifs with h
  · exact Finset.Subset.rfl
  · exact (spanPruneWitnessOfNot h).subset

/-- A failed robustness test makes the chosen step small-loss, anchored, and
strictly changes one relevant generated subgroup. -/
theorem spanPruneNext_spec {A : Finset ℤ} {budget : ℕ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hnot : ¬ Stability.SpanRobust 0 A budget relevant phi) :
    A.card ≤ (spanPruneNext A budget relevant phi).card + budget ∧
      0 ∈ spanPruneNext A budget relevant phi ∧
      ∃ d : {d // d ∈ relevant},
        Stability.generatedSubgroup (phi d.1)
            (spanPruneNext A budget relevant phi) ≠
          Stability.generatedSubgroup (phi d.1) A := by
  classical
  unfold spanPruneNext
  simp only [hnot, ↓reduceDIte]
  exact ⟨(spanPruneWitnessOfNot hnot).loss,
    (spanPruneWitnessOfNot hnot).zero_mem,
    (spanPruneWitnessOfNot hnot).changes⟩

/-- Iteration of the canonical failed-robustness deletion. -/
noncomputable def spanPruneIterate (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) :
    ℕ → Finset ℤ
  | 0 => A
  | i + 1 => spanPruneNext (spanPruneIterate A budget relevant phi i)
      budget relevant phi

theorem spanPruneIterate_subset_succ (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) (i : ℕ) :
    spanPruneIterate A budget relevant phi (i + 1) ⊆
      spanPruneIterate A budget relevant phi i := by
  exact spanPruneNext_subset _ _ _ _

theorem spanPruneIterate_subset (A : Finset ℤ) (budget : ℕ)
    (relevant : Finset ℕ) (phi : (d : ℕ) → ℤ → LatticePoint d) (i : ℕ) :
    spanPruneIterate A budget relevant phi i ⊆ A := by
  induction i with
  | zero => exact Finset.Subset.rfl
  | succ i ih => exact (spanPruneIterate_subset_succ A budget relevant phi i).trans ih

/-- As long as no earlier iterate is robust, the cumulative cardinality loss
after `i` steps is at most `i * budget`, and zero is retained. -/
theorem spanPruneIterate_loss_anchor {A : Finset ℤ} {budget : ℕ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hzero : 0 ∈ A) {i : ℕ}
    (hbad : ∀ j < i,
      ¬ Stability.SpanRobust 0
        (spanPruneIterate A budget relevant phi j) budget relevant phi) :
    A.card ≤ (spanPruneIterate A budget relevant phi i).card + i * budget ∧
      0 ∈ spanPruneIterate A budget relevant phi i := by
  induction i with
  | zero =>
      change A.card ≤ A.card + 0 * budget ∧ 0 ∈ A
      simp [hzero]
  | succ i ih =>
      have hprev := ih (fun j hj ↦ hbad j (hj.trans (Nat.lt_succ_self i)))
      have hstep := spanPruneNext_spec (hbad i (Nat.lt_succ_self i))
      change A.card ≤
          (spanPruneNext (spanPruneIterate A budget relevant phi i)
            budget relevant phi).card + (i + 1) * budget ∧ _
      constructor
      · calc
          A.card ≤ (spanPruneIterate A budget relevant phi i).card +
              i * budget := hprev.1
          _ ≤ ((spanPruneNext (spanPruneIterate A budget relevant phi i)
                budget relevant phi).card + budget) + i * budget := by
              exact Nat.add_le_add_right hstep.1 (i * budget)
          _ = (spanPruneNext (spanPruneIterate A budget relevant phi i)
                budget relevant phi).card + (i + 1) * budget := by ring
      · exact hstep.2.1

/-- If the first `i` iterates all fail robustness and remain in the accessible
range, their subgroup-index depth increases by at least `i`. -/
theorem spanPruneIterate_depth_growth {A : Finset ℤ} {budget cap : ℕ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hzero : 0 ∈ A)
    (hfinite : ∀ {B : Finset ℤ}, B ⊆ A → A.card ≤ B.card + cap →
      0 ∈ B → ∀ d : {d // d ∈ relevant},
        (Stability.generatedSubgroup (phi d.1) B).relIndex
          (Stability.generatedSubgroup (phi d.1) A) ≠ 0)
    {i : ℕ} (hiloss : i * budget ≤ cap)
    (hbad : ∀ j < i,
      ¬ Stability.SpanRobust 0
        (spanPruneIterate A budget relevant phi j) budget relevant phi) :
    i ≤ spanIndexDepth (relevant := relevant)
      (fun d ↦ Stability.generatedSubgroup (phi d.1) A)
      (fun d ↦ Stability.generatedSubgroup (phi d.1)
        (spanPruneIterate A budget relevant phi i)) := by
  classical
  induction i with
  | zero => simp
  | succ i ih =>
      have hbadPrev : ∀ j < i,
          ¬ Stability.SpanRobust 0
            (spanPruneIterate A budget relevant phi j) budget relevant phi :=
        fun j hj ↦ hbad j (hj.trans (Nat.lt_succ_self i))
      have hprevLoss := spanPruneIterate_loss_anchor hzero hbadPrev
      have hstep := spanPruneNext_spec (hbad i (Nat.lt_succ_self i))
      let B := spanPruneIterate A budget relevant phi i
      let C := spanPruneIterate A budget relevant phi (i + 1)
      have hCA : C ⊆ A := spanPruneIterate_subset A budget relevant phi (i + 1)
      have hzeroC : 0 ∈ C := by simpa [C, spanPruneIterate] using hstep.2.1
      have hlossC : A.card ≤ C.card + cap := by
        have htot : A.card ≤ C.card + (i + 1) * budget := by
          calc
            A.card ≤ B.card + i * budget := hprevLoss.1
            _ ≤ (C.card + budget) + i * budget := by
              exact Nat.add_le_add_right (by
                simpa [B, C, spanPruneIterate] using hstep.1) _
            _ = C.card + (i + 1) * budget := by ring
        exact htot.trans (Nat.add_le_add_left hiloss _)
      have hCB : C ⊆ B := by
        dsimp [B, C]
        exact spanPruneIterate_subset_succ A budget relevant phi i
      have hBA : B ⊆ A := spanPruneIterate_subset A budget relevant phi i
      have hdepth : spanIndexDepth (relevant := relevant)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) A)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) B) <
        spanIndexDepth (relevant := relevant)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) A)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) C) := by
        apply spanIndexDepth_lt
        · intro d
          exact Stability.generatedSubgroup_mono hCB
        · intro d
          exact Stability.generatedSubgroup_mono hBA
        · exact hfinite hCA hlossC hzeroC
        · simpa [B, C, spanPruneIterate] using hstep.2.2
      have hi := ih (Nat.le_trans (Nat.mul_le_mul_right budget (Nat.le_succ i)) hiloss)
        hbadPrev
      have hi' : i ≤ spanIndexDepth (relevant := relevant)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) A)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) B) := by
        simpa [B] using hi
      have hsucc : i + 1 ≤ spanIndexDepth (relevant := relevant)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) A)
          (fun d : {d // d ∈ relevant} ↦
            Stability.generatedSubgroup (phi d.1) C) := by
        omega
      simpa [C] using hsucc

/-- **CFP Lemma 2.32, subgroup-index form.**

Uniform finite-index control on all subsets reachable in `height + 1` pruning
steps forces the pruning to stop within `height` steps.  The proof performs
the deletions and rules out an overlong chain by logarithmic index growth. -/
theorem span_pruning_of_accessibleIndexBound {A : Finset ℤ}
    {relevant : Finset ℕ} {phi : (d : ℕ) → ℤ → LatticePoint d}
    {robustBudget indexBound : ℕ} (hzero : 0 ∈ A)
    (hindex : AccessibleSpanIndexBound A relevant phi
      (robustBudget *
        (relevant.card * Nat.log 2 indexBound + 1)) indexBound) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card +
        robustBudget * (relevant.card * Nat.log 2 indexBound) ∧
      Stability.SpanRobust 0 B robustBudget relevant phi := by
  classical
  let height := relevant.card * Nat.log 2 indexBound
  by_contra hnone
  push Not at hnone
  have hbad : ∀ i ≤ height,
      ¬ Stability.SpanRobust 0
        (spanPruneIterate A robustBudget relevant phi i)
          robustBudget relevant phi := by
    intro i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hgood
        have hpriorBad : ∀ j < i,
            ¬ Stability.SpanRobust 0
              (spanPruneIterate A robustBudget relevant phi j)
                robustBudget relevant phi := by
          intro j hj
          exact ih j hj (hj.le.trans hi)
        have hiloss := spanPruneIterate_loss_anchor hzero hpriorBad
        have hmul : i * robustBudget ≤ robustBudget * height := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right robustBudget hi
        have hcard : A.card ≤
            (spanPruneIterate A robustBudget relevant phi i).card +
              robustBudget * height :=
          hiloss.1.trans (Nat.add_le_add_left hmul _)
        exact hnone _
          (spanPruneIterate_subset A robustBudget relevant phi i)
          hiloss.2 (by simpa [height] using hcard) hgood
  have hbadLong : ∀ j < height + 1,
      ¬ Stability.SpanRobust 0
        (spanPruneIterate A robustBudget relevant phi j)
          robustBudget relevant phi := by
    intro j hj
    exact hbad j (by omega)
  have hdepth := spanPruneIterate_depth_growth
    (relevant := relevant) (phi := phi) hzero hindex.finite
    (i := height + 1) (by
      dsimp [height]
      simp [Nat.mul_comm]) hbadLong
  have hlastLoss := spanPruneIterate_loss_anchor hzero hbadLong
  have hlastSubset := spanPruneIterate_subset A robustBudget relevant phi (height + 1)
  have hupper := spanIndexDepth_le (relevant := relevant)
    (hindex.index_le hlastSubset (by
      dsimp [height] at hlastLoss ⊢
      simpa [Nat.mul_comm] using hlastLoss.1) hlastLoss.2)
  dsimp [height] at hdepth hupper
  omega

/-- **CFP Lemma 2.32, approximation form.**

Concrete `h`-approximations and weak stability imply the uniform finite-index
bound by quotient packing; the logarithmic-index iterator then produces a
span-robust core.  Unlike `span_pruning_lemma232`, this theorem has no
subgroup-rank certificate premise. -/
theorem span_pruning_lemma232_of_hApproximations
    {A : Finset ℤ} {x D n scaleNum scaleDen robustBudget : ℕ}
    (hzero : 0 ∈ A)
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hAt : {d // d ∈ relevant} → ℕ)
    (hambient : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation A (hAt d) d.1 scaleNum scaleDen)
    (hrank_le : ∀ d : {d // d ∈ relevant}, d.1 ≤ D)
    (hh_le : ∀ d : {d // d ∈ relevant}, hAt d ≤ n)
    (hlarge : ∀ d : {d // d ∈ relevant},
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ hAt d)
    (haccessible : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card +
        robustBudget *
          (D * Nat.log 2
            (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1) →
      0 ∈ B → ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e)
    (hcap : robustBudget *
      (D * Nat.log 2
        (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1) ≤ x) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card +
        robustBudget *
          (D * Nat.log 2
            (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D)) ∧
      Stability.SpanRobust 0 B robustBudget relevant
        (Stability.minimalIdentificationFamily hproper) := by
  let K := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hrelcard : relevant.card ≤ D :=
    relevant_card_le_rankBound hproper.positive hrank_le
  have hheight : relevant.card * Nat.log 2 K ≤ D * Nat.log 2 K :=
    Nat.mul_le_mul_right _ hrelcard
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card +
        robustBudget * (relevant.card * Nat.log 2 K + 1) →
      0 ∈ B → ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBA hcard hzeroB d
    apply haccessible hBA ?_ hzeroB d
    have hcapMono : robustBudget *
        (relevant.card * Nat.log 2 K + 1) ≤
          robustBudget * (D * Nat.log 2 K + 1) := by gcongr
    exact hcard.trans (Nat.add_le_add_left hcapMono B.card)
  have hindex : AccessibleSpanIndexBound A relevant
      (Stability.minimalIdentificationFamily hproper)
      (robustBudget * (relevant.card * Nat.log 2 K + 1)) K := by
    apply accessibleSpanIndexBound_of_hApproximations
      hstable hA hproper hAt hambient hrank_le hh_le hlarge haccessible'
    have hcapMono : robustBudget *
        (relevant.card * Nat.log 2 K + 1) ≤
          robustBudget * (D * Nat.log 2 K + 1) := by gcongr
    exact hcapMono.trans (by simpa [K] using hcap)
  obtain ⟨B, hBA, hzeroB, hcard, hrobust⟩ :=
    span_pruning_of_accessibleIndexBound hzero hindex
  refine ⟨B, hBA, hzeroB, ?_, hrobust⟩
  exact hcard.trans (Nat.add_le_add_left (Nat.mul_le_mul_left robustBudget hheight) _)

/-! ## Numerical form of the source loss estimate -/

/-- The explicit `100 * beta^2 * t` bookkeeping in CFP Lemma 2.38. -/
theorem preprocessing_loss_le_hundred_beta_sq {A : Finset ℤ}
    {n m beta t : ℕ} (hbeta : 1 ≤ beta) (hzero : 0 ∈ A)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hlog : Nat.log 2 n + 1 ≤ beta * (Nat.log 2 m + 1)) :
    (2 * (t / (Nat.log 2 m + 1))) * boxPotential A (beta + 1) +
        t / (Nat.log 2 m + 1) ≤ 100 * beta ^ 2 * t := by
  let ell := Nat.log 2 m + 1
  let q := t / ell
  have hlog' : Nat.log 2 n + 1 ≤ beta * ell := by simpa [ell] using hlog
  have hbox₀ := boxPotential_le (maxRank := beta + 1) hzero hA
  have hrank : beta + 1 ≤ 2 * beta := by omega
  have hbox : boxPotential A (beta + 1) ≤ 6 * beta ^ 2 * ell := by
    calc
      boxPotential A (beta + 1)
          ≤ (beta + 1) * (3 * (Nat.log 2 n + 1)) := hbox₀
      _ ≤ (2 * beta) * (3 * (beta * ell)) :=
        Nat.mul_le_mul hrank (Nat.mul_le_mul_left 3 hlog')
      _ = 6 * beta ^ 2 * ell := by ring
  have hqell : q * ell ≤ t := by
    exact Nat.div_mul_le_self t ell
  have hweak : (2 * q) * boxPotential A (beta + 1) ≤
      12 * beta ^ 2 * t := by
    calc
      (2 * q) * boxPotential A (beta + 1)
          ≤ (2 * q) * (6 * beta ^ 2 * ell) :=
            Nat.mul_le_mul_left (2 * q) hbox
      _ = 12 * beta ^ 2 * (q * ell) := by ring
      _ ≤ 12 * beta ^ 2 * t :=
        Nat.mul_le_mul_left (12 * beta ^ 2) hqell
  have hq : q ≤ beta ^ 2 * t := by
    calc
      q ≤ t := Nat.div_le_self _ _
      _ ≤ beta ^ 2 * t := by
        have hbsq : 1 ≤ beta ^ 2 := by nlinarith
        simpa using Nat.mul_le_mul hbsq (Nat.le_refl t)
  change (2 * q) * boxPotential A (beta + 1) + q ≤ _
  calc
    (2 * q) * boxPotential A (beta + 1) + q
        ≤ 12 * beta ^ 2 * t + beta ^ 2 * t := Nat.add_le_add hweak hq
    _ ≤ 100 * beta ^ 2 * t := by nlinarith

/-! ## Lemma 2.38 packaging -/

/-- Exact finite Steps 1 and 2 underlying CFP Lemma 2.38.

The output is strongly stable relative to the weak core's canonical boxes and
the fixed relevant coordinate maps used during subgroup pruning.  The
cardinality loss displays the two contributions separately: weak-stability
deletions and subgroup-span deletions. -/
theorem preprocessing_of_spanRankCertificate {A : Finset ℤ}
    {stableBudget maxRank n C0 spanHeight : ℕ}
    {relevant : Finset ℕ}
    {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (spanCertificate : ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
      Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
        SpanRankCertificate W relevant phi spanHeight)
    (hspanLoss : (stableBudget / C0) * spanHeight ≤ stableBudget) :
    ∃ W B : Finset ℤ, B ⊆ W ∧ W ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card +
        (2 * stableBudget) * boxPotential A maxRank + stableBudget ∧
      Stability.StronglyStableFor B (Stability.minimalBoxFamily W) stableBudget maxRank
        (n ^ 2) relevant phi C0 := by
  classical
  obtain ⟨W, hWA, hzeroW, hweakW, hlossW⟩ :=
    exists_weaklyStable_core hzero
  let cert := spanCertificate hWA hzeroW hweakW
  obtain ⟨B, hBW, hzeroB, hlossB, hspanB⟩ :=
    span_pruning_lemma232 hzeroW cert
  have hweakB : Stability.WeaklyStableFor B (Stability.minimalBoxFamily W)
      stableBudget maxRank (n ^ 2) := by
    apply Stability.WeaklyStableFor.delete hweakW hBW hzeroB hlossB
    exact (Nat.add_le_add_right hspanLoss stableBudget).trans_eq (by omega)
  refine ⟨W, B, hBW, hWA, hzeroB, ?_, ⟨hweakB, hC0, hspanB⟩⟩
  omega

/-- A convenient cardinal-only corollary with a single advertised loss
budget, such as the source's `100 * beta^2 * t`. -/
theorem preprocessing_of_spanRankCertificate_with_loss {A : Finset ℤ}
    {stableBudget maxRank n C0 spanHeight totalLoss : ℕ}
    {relevant : Finset ℕ}
    {phi : (d : ℕ) → ℤ → LatticePoint d}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (spanCertificate : ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
      Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
        SpanRankCertificate W relevant phi spanHeight)
    (hspanLoss : (stableBudget / C0) * spanHeight ≤ stableBudget)
    (hloss : (2 * stableBudget) * boxPotential A maxRank + stableBudget ≤
      totalLoss) :
    ∃ W B : Finset ℤ, B ⊆ W ∧ W ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card + totalLoss ∧
      Stability.StronglyStableFor B (Stability.minimalBoxFamily W) stableBudget maxRank
        (n ^ 2) relevant phi C0 := by
  obtain ⟨W, B, hBW, hWA, hzeroB, hcard, hstable⟩ :=
    preprocessing_of_spanRankCertificate hzero hC0 spanCertificate hspanLoss
  refine ⟨W, B, hBW, hWA, hzeroB, ?_, hstable⟩
  omega

/-- **CFP Lemma 2.38, approximation form.**

Starting from `A`, Step 1 performs the weak-stability deletions.  The only
source-level input to Step 2 is the family of actual `h`-approximations (and
their explicit large-`h` inequalities) supplied by CFP Lemmas 2.22 and 2.26
for the weak core and every accessible subset.  Quotient packing constructs
the finite-index bound internally, and the logarithmic-index iterator then
constructs the strongly stable core.  In particular, this theorem has no
`SpanRankCertificate`, accessible-index, or robustness premise. -/
theorem preprocessing_lemma238 {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
      Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
      ∃ (relevant : Finset ℕ)
        (hproper : Stability.RelevantBoxesProper W relevant)
        (hAt : {d // d ∈ relevant} → ℕ),
        (∀ d : {d // d ∈ relevant},
          Nonempty
            (HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen)) ∧
        (∀ d : {d // d ∈ relevant}, d.1 ≤ maxRank) ∧
        (∀ d : {d // d ∈ relevant}, hAt d ≤ n) ∧
        (∀ d : {d // d ∈ relevant},
          4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank ≤ hAt d) ∧
        (∀ {B : Finset ℤ}, B ⊆ W →
          W.card ≤ B.card +
            (stableBudget / C0) *
              (maxRank * Nat.log 2
                (4 * (6 * scaleDen) ^ maxRank *
                  (4 * scaleDen) ^ maxRank) + 1) →
          0 ∈ B → ∀ d : {d // d ∈ relevant},
            ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
              ∃ V : HDimension.HApproximation B (hAt d) e
                  scaleNum scaleDen,
                (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
                  (scaleNum * hAt d) ^ e) ∧
        (stableBudget / C0) *
          (maxRank * Nat.log 2
            (4 * (6 * scaleDen) ^ maxRank *
              (4 * scaleDen) ^ maxRank)) ≤ stableBudget) :
    ∃ W B : Finset ℤ, ∃ relevant : Finset ℕ,
      ∃ hproper : Stability.RelevantBoxesProper W relevant,
        B ⊆ W ∧ W ⊆ A ∧ 0 ∈ B ∧
        A.card ≤ B.card +
          (2 * stableBudget) * boxPotential A maxRank + stableBudget ∧
        Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
          stableBudget maxRank (n ^ 2) relevant
          (Stability.minimalIdentificationFamily hproper) C0 := by
  classical
  obtain ⟨W, hWA, hzeroW, hweakW, hlossW⟩ :=
    exists_weaklyStable_core hzero
  obtain ⟨relevant, hproper, hAt, hambient, hrank_le, hh_le,
      hlarge, haccessible, hspanLoss⟩ := happrox hWA hzeroW hweakW
  let hambient' : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen :=
    fun d ↦ Classical.choice (hambient d)
  let K := 4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank
  let height := maxRank * Nat.log 2 K
  let robustBudget := stableBudget / C0
  have hrobust_le : robustBudget ≤ stableBudget := by
    exact Nat.div_le_self _ _
  have hcap : robustBudget * (height + 1) ≤ 2 * stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa [robustBudget, height, K] using hspanLoss
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ W →
      W.card ≤ B.card + robustBudget * (height + 1) → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
          ∃ V : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBW hcard hzeroB d
    apply haccessible hBW (B := B) ?_ hzeroB d
    simpa [robustBudget, height, K] using hcard
  obtain ⟨B, hBW, hzeroB, hlossB, hspanB⟩ :=
    span_pruning_lemma232_of_hApproximations
      hzeroW hweakW (fun z hz ↦ hA z (hWA hz)) hproper hAt
      hambient' hrank_le hh_le hlarge haccessible' hcap
  have hweakB : Stability.WeaklyStableFor B (Stability.minimalBoxFamily W)
      stableBudget maxRank (n ^ 2) := by
    apply Stability.WeaklyStableFor.delete hweakW hBW hzeroB hlossB
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa [robustBudget, height, K] using hspanLoss
    exact (Nat.add_le_add_right hspanLoss' stableBudget).trans_eq (by omega)
  refine ⟨W, B, relevant, hproper, hBW, hWA, hzeroB, ?_,
    ⟨hweakB, hC0, ?_⟩⟩
  · have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa [robustBudget, height, K] using hspanLoss
    have hlossB' : W.card ≤ B.card + stableBudget :=
      hlossB.trans (Nat.add_le_add_left hspanLoss' B.card)
    omega
  · intro d hd B' hB'B hcard hzeroB'
    exact hspanB hd hB'B (by simpa [robustBudget] using hcard) hzeroB'

end Erdos186.CFP.Preprocessing
