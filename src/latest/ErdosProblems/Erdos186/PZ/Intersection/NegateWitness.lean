/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.PZ.Intersection.Irreducibility

/-!
# Negating a CFP witness

The second side of the Pham--Zakharov intersection argument is naturally
written with deviations `a - x`, whereas the coordinate reduction and its
CFP selector use the forward deviations `x - a`.  This file proves that an
enhanced CFP witness transports across pointwise negation without changing
any of its numerical parameters.

We negate the GAP presentation itself: both its offset and all its steps are
negated, while the widths are unchanged.  Consequently evaluation, dilation,
properness, symmetry, homogeneity, coverage, and the volume data all commute
with negation.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

/-- Negate the offset and every displayed step of a GAP. -/
def negatedGAP {d r : ℕ} (P : GAP d r) : GAP d r where
  offset := -P.offset
  steps i := -P.steps i
  widths := P.widths
  width_pos := P.width_pos

namespace negatedGAP

variable {d r : ℕ} (P : GAP d r)

@[simp] theorem offset : (negatedGAP P).offset = -P.offset := rfl

@[simp] theorem steps (i : Fin r) : (negatedGAP P).steps i = -P.steps i := rfl

@[simp] theorem widths (i : Fin r) : (negatedGAP P).widths i = P.widths i := rfl

@[simp] theorem volume : (negatedGAP P).volume = P.volume := by
  rfl

@[simp] theorem coordPoint (n : P.Coord) :
    (negatedGAP P).coordPoint n = -P.coordPoint n := by
  funext j
  simp only [GAP.coordPoint, offset, steps, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib]
  ring

@[simp] theorem carrier :
    (negatedGAP P).carrier = P.carrier.image (fun x ↦ -x) := by
  classical
  ext x
  simp only [GAP.mem_carrier_iff, Finset.mem_image]
  constructor
  · rintro ⟨n, rfl⟩
    change P.Coord at n
    exact ⟨P.coordPoint n, ⟨n, rfl⟩, by rw [coordPoint]⟩
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    rw [coordPoint]

@[simp] theorem negated_negated : negatedGAP (negatedGAP P) = P := by
  cases P
  simp [negatedGAP]

@[simp] theorem dilate (k : ℕ) :
    (negatedGAP P).dilate k = negatedGAP (P.dilate k) := by
  cases P
  simp only [GAP.dilate, negatedGAP]
  congr
  funext j
  simp

theorem proper_iff : (negatedGAP P).Proper ↔ P.Proper := by
  constructor
  · intro h n m hnm
    apply h
    simpa only [coordPoint] using congrArg Neg.neg hnm
  · intro h n m hnm
    change P.Coord at n m
    apply h
    rw [coordPoint, coordPoint] at hnm
    exact neg_injective hnm

theorem homogeneous_iff : (negatedGAP P).Homogeneous ↔ P.Homogeneous := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    funext j
    have hj := congrFun hz j
    have h := congrArg Neg.neg hj
    simpa only [negatedGAP, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, neg_neg] using h
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    funext j
    have hj := congrFun hz j
    have h := congrArg Neg.neg hj
    simpa only [negatedGAP, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib] using h

theorem symmetric_iff : (negatedGAP P).Symmetric ↔ P.Symmetric := by
  constructor
  · rintro ⟨radii, hcentered⟩
    refine ⟨radii, ?_⟩
    constructor
    · exact hcentered.1
    · funext j
      have hj := congrFun hcentered.2 j
      have h := congrArg Neg.neg hj
      simpa only [negatedGAP, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, neg_neg] using h
  · rintro ⟨radii, hcentered⟩
    refine ⟨radii, ?_⟩
    constructor
    · exact hcentered.1
    · funext j
      have hj := congrFun hcentered.2 j
      have h := congrArg Neg.neg hj
      simpa only [negatedGAP, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, neg_neg] using h

theorem nondegenerate_iff :
    (negatedGAP P).Nondegenerate ↔ P.Nondegenerate := by
  rfl

end negatedGAP

/-- Negating every summand negates every subset sum, and produces all subset
sums of the negated set. -/
theorem subsetSums_image_neg {d : ℕ} (A : Finset (LatticePoint d)) :
    GAP.subsetSums (A.image (fun x ↦ -x)) =
      (GAP.subsetSums A).image (fun x ↦ -x) := by
  classical
  ext x
  simp only [GAP.mem_subsetSums_iff, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    let S := T.image (fun x ↦ -x)
    have hSA : S ⊆ A := by
      intro y hy
      obtain ⟨z, hzT, hzy⟩ := Finset.mem_image.mp hy
      have hzImage := hT hzT
      obtain ⟨a, haA, haz⟩ := Finset.mem_image.mp hzImage
      have hya : y = a := by
        rw [← hzy, ← haz]
        simp
      simpa [hya] using haA
    refine ⟨∑ y ∈ S, y, ⟨S, hSA, rfl⟩, ?_⟩
    dsimp [S]
    rw [Finset.sum_image]
    · rw [Finset.sum_neg_distrib, neg_neg]
    · intro a₁ _ a₂ _ h
      simpa using congrArg Neg.neg h
  · rintro ⟨y, ⟨S, hSA, rfl⟩, rfl⟩
    let T := S.image (fun x ↦ -x)
    have hT : T ⊆ A.image (fun x ↦ -x) :=
      Finset.image_mono (fun x ↦ -x) hSA
    refine ⟨T, hT, ?_⟩
    dsimp [T]
    rw [Finset.sum_image]
    · rw [Finset.sum_neg_distrib]
    · intro a₁ _ a₂ _ h
      simpa using congrArg Neg.neg h

/-- Translation and pointwise negation commute after negating the translation
vector. -/
theorem cfpTranslate_image_neg {d : ℕ} (t : LatticePoint d)
    (S : Finset (LatticePoint d)) :
    CFP.translate (-t) (S.image (fun x ↦ -x)) =
      (CFP.translate t S).image (fun x ↦ -x) := by
  classical
  ext x
  simp only [CFP.mem_translate_iff, Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨t + y, ⟨y, hy, rfl⟩, by abel⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨-y, ⟨y, hy, rfl⟩, by abel⟩

/-- Transport an enhanced CFP witness through pointwise negation.  All four
external numerical parameters, and the two fixed scale constants stored in
the witness, are unchanged. -/
def negateEnhancedCFPWitness {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    CFP.EnhancedCFPWitness (A.image (fun x ↦ -x)) s D k loss where
  toCFPWitness :=
    { core := W.core.image (fun x ↦ -x)
      reserved := W.reserved.image (fun x ↦ -x)
      rank := W.rank
      rank_le := W.rank_le
      progression := negatedGAP W.progression
      core_subset := Finset.image_mono (fun x ↦ -x) W.core_subset
      reserved_subset_core :=
        Finset.image_mono (fun x ↦ -x) W.reserved_subset_core
      core_large := by
        simpa only [Finset.card_image_of_injective _ neg_injective] using
          W.core_large
      reserved_small := by
        simpa only [Finset.card_image_of_injective _ neg_injective] using
          W.reserved_small
      core_zero_subset := by
        intro x hx
        rw [negatedGAP.carrier]
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_image.mpr ⟨0, W.core_zero_subset (by simp), by simp⟩
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image.mpr
            ⟨y, W.core_zero_subset (Finset.mem_insert_of_mem hy), rfl⟩
      homogeneous := (negatedGAP.homogeneous_iff W.progression).2 W.homogeneous
      translatePoint := -W.translatePoint
      covered := by
        rw [negatedGAP.dilate, negatedGAP.carrier,
          cfpTranslate_image_neg, subsetSums_image_neg]
        exact Finset.image_mono (fun x ↦ -x) W.covered
      dilate_proper := by
        rw [negatedGAP.dilate]
        exact (negatedGAP.proper_iff (W.progression.dilate k)).2 W.dilate_proper }
  k_pos := W.k_pos
  scaleNum := W.scaleNum
  scaleDen := W.scaleDen
  scaleNum_pos := W.scaleNum_pos
  scaleDen_pos := W.scaleDen_pos
  scale_lower := W.scale_lower
  scale_upper := W.scale_upper
  progression_proper :=
    (negatedGAP.proper_iff W.progression).2 W.progression_proper
  progression_symmetric :=
    (negatedGAP.symmetric_iff W.progression).2 W.progression_symmetric
  progression_nondegenerate :=
    (negatedGAP.nondegenerate_iff W.progression).2 W.progression_nondegenerate
  covered_translate_homogeneous := by
    obtain ⟨z, hz⟩ := W.covered_translate_homogeneous
    refine ⟨z, ?_⟩
    funext j
    have hj := congrFun hz j
    have h := congrArg Neg.neg hj
    simpa only [Pi.add_apply, Pi.neg_apply, GAP.dilate_offset,
      negatedGAP.offset, negatedGAP.steps, neg_add_rev, mul_neg,
      Finset.sum_neg_distrib, add_comm] using h

namespace negateEnhancedCFPWitness

variable {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)

@[simp] theorem core :
    (negateEnhancedCFPWitness W).core = W.core.image (fun x ↦ -x) := by
  change W.core.image (fun x ↦ -x) = _
  rfl

@[simp] theorem reserved :
    (negateEnhancedCFPWitness W).reserved = W.reserved.image (fun x ↦ -x) := by
  change W.reserved.image (fun x ↦ -x) = _
  rfl

@[simp] theorem progression :
    (negateEnhancedCFPWitness W).progression = negatedGAP W.progression := by
  change negatedGAP W.progression = _
  rfl

@[simp] theorem translatePoint :
    (negateEnhancedCFPWitness W).translatePoint = -W.translatePoint := by
  change -W.translatePoint = _
  rfl

@[simp] theorem rank : (negateEnhancedCFPWitness W).rank = W.rank := by
  change W.rank = W.rank
  rfl

@[simp] theorem scaleNum :
    (negateEnhancedCFPWitness W).scaleNum = W.scaleNum := by
  change W.scaleNum = W.scaleNum
  rfl

@[simp] theorem scaleDen :
    (negateEnhancedCFPWitness W).scaleDen = W.scaleDen := by
  change W.scaleDen = W.scaleDen
  rfl

end negateEnhancedCFPWitness

/-- The coordinate reduction's translated candidate is exactly the forward
deviation set used by the first intersection side. -/
theorem orientedTranslate_forward_eq_identifiedTranslate
    {d : ℕ} (a : LatticePoint d) (A : Finset (LatticePoint d)) :
    orientedTranslate .forward a A =
      Reduction.identifiedTranslate A a := by
  classical
  change A.image (fun y ↦ y - a) = PZ.translate (-a) A
  ext x
  simp only [PZ.translate, Finset.mem_image]
  constructor <;> rintro ⟨y, hy, rfl⟩
  · exact ⟨y, hy, by simp [sub_eq_add_neg]⟩
  · exact ⟨y, hy, by simp [sub_eq_add_neg]⟩

/-- Reverse deviations are the pointwise negatives of the forward,
coordinate-reduction deviations. -/
theorem orientedTranslate_reverse_eq_image_neg_identifiedTranslate
    {d : ℕ} (a : LatticePoint d) (A : Finset (LatticePoint d)) :
    orientedTranslate .reverse a A =
      (Reduction.identifiedTranslate A a).image (fun x ↦ -x) := by
  classical
  change A.image (fun y ↦ a - y) =
    (A.image (fun y ↦ y + -a)).image (fun y ↦ -y)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨y + -a, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    abel
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨y, hy, by abel⟩

/-- A witness selected for the canonical forward set `A-a` therefore gives
the witness required for the reverse side `a-A`. -/
def reverseEnhancedCFPWitnessOfIdentifiedTranslate
    {d s D k loss : ℕ} (a : LatticePoint d)
    (A : Finset (LatticePoint d))
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate A a)
      s D k loss) :
    CFP.EnhancedCFPWitness (orientedTranslate .reverse a A) s D k loss := by
  rw [orientedTranslate_reverse_eq_image_neg_identifiedTranslate]
  exact negateEnhancedCFPWitness W

end

end Erdos186.PZ.Intersection
