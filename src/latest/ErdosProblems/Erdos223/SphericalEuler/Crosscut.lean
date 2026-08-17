/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.JordanCurve

/-!
A checked set-level crosscut lemma in an *adapted open-cell chart*.

The open square is used instead of the open disk because its two sides after
removing the standard diameter are literally products of intervals.  It is a
standard open 2-cell, and can of course be replaced by a disk via a fixed
homeomorphism.
-/

namespace JordanCurve.Crosscut

open Set Topology

abbrev ModelPlane := ℝ × ℝ

def openCell : Set ModelPlane := Ioo (-1) 1 ×ˢ Ioo (-1) 1

def diameter : Set ModelPlane := {p | p.1 = 0}

def slitCell : Set ModelPlane := openCell \ diameter

def negativeSide : Set ModelPlane := Ioo (-1) 0 ×ˢ Ioo (-1) 1

def positiveSide : Set ModelPlane := Ioo 0 1 ×ˢ Ioo (-1) 1

private noncomputable def leftPoint : ModelPlane := (-1 / 2, 0)

private noncomputable def rightPoint : ModelPlane := (1 / 2, 0)

private lemma leftPoint_mem_negativeSide : leftPoint ∈ negativeSide := by
  norm_num [leftPoint, negativeSide]

private lemma rightPoint_mem_positiveSide : rightPoint ∈ positiveSide := by
  norm_num [rightPoint, positiveSide]

private lemma negativeSide_subset_slitCell : negativeSide ⊆ slitCell := by
  rintro ⟨x, y⟩ ⟨⟨hxneg, hxzero⟩, hy⟩
  exact ⟨⟨⟨hxneg, hxzero.trans_le zero_le_one⟩, hy⟩, by simpa [diameter] using ne_of_lt hxzero⟩

private lemma positiveSide_subset_slitCell : positiveSide ⊆ slitCell := by
  rintro ⟨x, y⟩ ⟨⟨hxzero, hxpos⟩, hy⟩
  exact ⟨⟨⟨neg_one_lt_zero.trans hxzero, hxpos⟩, hy⟩, by simpa [diameter] using ne_of_gt hxzero⟩

private lemma isPreconnected_negativeSide : IsPreconnected negativeSide := by
  exact isPreconnected_Ioo.prod isPreconnected_Ioo

private lemma isPreconnected_positiveSide : IsPreconnected positiveSide := by
  exact isPreconnected_Ioo.prod isPreconnected_Ioo

theorem isConnected_negativeSide : IsConnected negativeSide :=
  ⟨⟨leftPoint, leftPoint_mem_negativeSide⟩, isPreconnected_negativeSide⟩

theorem isConnected_positiveSide : IsConnected positiveSide :=
  ⟨⟨rightPoint, rightPoint_mem_positiveSide⟩, isPreconnected_positiveSide⟩

theorem slitCell_eq_negativeSide_union_positiveSide :
    slitCell = negativeSide ∪ positiveSide := by
  ext p
  constructor
  · intro hp
    have hp0 : p.1 ≠ 0 := hp.2
    rcases lt_or_gt_of_ne hp0 with hpneg | hppos
    · exact Or.inl ⟨⟨hp.1.1.1, hpneg⟩, hp.1.2⟩
    · exact Or.inr ⟨⟨hppos, hp.1.1.2⟩, hp.1.2⟩
  · rintro (hp | hp)
    · exact negativeSide_subset_slitCell hp
    · exact positiveSide_subset_slitCell hp

theorem disjoint_negativeSide_positiveSide :
    Disjoint negativeSide positiveSide := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hx hy
  exact (not_lt_of_ge (le_of_lt hx.1.2)) hy.1.1

/-- The negative component of the model slit cell is itself an open 2-cell. -/
noncomputable def negativeSideHomeomorphOpenCell : negativeSide ≃ₜ openCell where
  toFun p := ⟨(2 * p.1.1 + 1, p.1.2), by
    rcases p.2 with ⟨⟨hxneg, hxzero⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩⟩
  invFun p := ⟨((p.1.1 - 1) / 2, p.1.2), by
    rcases p.2 with ⟨⟨hxneg, hxpos⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      ring
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The positive component of the model slit cell is itself an open 2-cell. -/
noncomputable def positiveSideHomeomorphOpenCell : positiveSide ≃ₜ openCell where
  toFun p := ⟨(2 * p.1.1 - 1, p.1.2), by
    rcases p.2 with ⟨⟨hxzero, hxpos⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩⟩
  invFun p := ⟨((p.1.1 + 1) / 2, p.1.2), by
    rcases p.2 with ⟨⟨hxneg, hxpos⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      ring
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private lemma slitCell_fst_ne_zero {p : ModelPlane} (hp : p ∈ slitCell) : p.1 ≠ 0 := by
  exact hp.2

private lemma same_component_of_fst_neg {p q : ModelPlane}
    (hpS : p ∈ slitCell) (hqS : q ∈ slitCell)
    (hp : p.1 < 0) (hq : q.1 < 0) :
    connectedComponentIn slitCell p = connectedComponentIn slitCell q := by
  have hpN : p ∈ negativeSide := ⟨⟨hpS.1.1.1, hp⟩, hpS.1.2⟩
  have hqN : q ∈ negativeSide := ⟨⟨hqS.1.1.1, hq⟩, hqS.1.2⟩
  have hqcomp : q ∈ connectedComponentIn slitCell p :=
    isPreconnected_negativeSide.subset_connectedComponentIn hpN
      negativeSide_subset_slitCell hqN
  exact connectedComponentIn_eq hqcomp

private lemma same_component_of_fst_pos {p q : ModelPlane}
    (hpS : p ∈ slitCell) (hqS : q ∈ slitCell)
    (hp : 0 < p.1) (hq : 0 < q.1) :
    connectedComponentIn slitCell p = connectedComponentIn slitCell q := by
  have hpP : p ∈ positiveSide := ⟨⟨hp, hpS.1.1.2⟩, hpS.1.2⟩
  have hqP : q ∈ positiveSide := ⟨⟨hq, hqS.1.1.2⟩, hqS.1.2⟩
  have hqcomp : q ∈ connectedComponentIn slitCell p :=
    isPreconnected_positiveSide.subset_connectedComponentIn hpP
      positiveSide_subset_slitCell hqP
  exact connectedComponentIn_eq hqcomp

private lemma left_right_components_ne :
    connectedComponentIn slitCell leftPoint ≠ connectedComponentIn slitCell rightPoint := by
  intro heq
  have hlS : leftPoint ∈ slitCell :=
    negativeSide_subset_slitCell leftPoint_mem_negativeSide
  have hrS : rightPoint ∈ slitCell :=
    positiveSide_subset_slitCell rightPoint_mem_positiveSide
  have hrcomp : rightPoint ∈ connectedComponentIn slitCell leftPoint := by
    rw [heq]
    exact mem_connectedComponentIn hrS
  have hlcomp : leftPoint ∈ connectedComponentIn slitCell leftPoint :=
    mem_connectedComponentIn hlS
  have hzero : (0 : ℝ) ∈ Icc leftPoint.1 rightPoint.1 := by
    norm_num [leftPoint, rightPoint]
  obtain ⟨p, hpcomp, hpzero⟩ :=
    isPreconnected_connectedComponentIn.intermediate_value hlcomp hrcomp
      continuous_fst.continuousOn hzero
  have hpS : p ∈ slitCell := connectedComponentIn_subset slitCell leftPoint hpcomp
  exact slitCell_fst_ne_zero hpS hpzero

/-- Removing the standard diameter from the standard open 2-cell leaves exactly
two connected components. -/
theorem nat_card_connectedComponents_slitCell :
    Nat.card (ConnectedComponents slitCell) = 2 := by
  let l : slitCell := ⟨leftPoint,
    negativeSide_subset_slitCell leftPoint_mem_negativeSide⟩
  let r : slitCell := ⟨rightPoint,
    positiveSide_subset_slitCell rightPoint_mem_positiveSide⟩
  have hlr : ConnectedComponents.mk l ≠ ConnectedComponents.mk r :=
    (Counting.connectedComponents_subtype_eq_iff l.2 r.2).not.mpr
      left_right_components_ne
  refine Counting.nat_card_connectedComponents_eq_two l r hlr ?_
  intro z
  have hz0 : z.1.1 ≠ 0 := slitCell_fst_ne_zero z.2
  rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
  · left
    exact (Counting.connectedComponents_subtype_eq_iff z.2 l.2).mpr
      (same_component_of_fst_neg z.2 l.2 hzneg (by norm_num [l, leftPoint]))
  · right
    exact (Counting.connectedComponents_subtype_eq_iff z.2 r.2).mpr
      (same_component_of_fst_pos z.2 r.2 hzpos (by norm_num [r, rightPoint]))

/-- Restrict an adapted open-cell chart to the complements of the crosscut.

`hcut` is the only compatibility required: inside the old open face, membership
in the inserted arc is exactly membership of the chart image in the standard
diameter.  The endpoints of the crosscut lie on the boundary of `F`, hence are
not visible in this open-face statement. -/
def slitChartHomeomorph {X : Type*} [TopologicalSpace X]
    {F C : Set X} (chart : F ≃ₜ openCell)
    (hcut : ∀ x : F, x.1 ∈ C ↔ (chart x : ModelPlane) ∈ diameter) :
    (F \ C : Set X) ≃ₜ slitCell where
  toFun x := ⟨chart ⟨x.1, x.2.1⟩, by
    refine ⟨(chart ⟨x.1, x.2.1⟩).2, ?_⟩
    exact (hcut ⟨x.1, x.2.1⟩).not.mp x.2.2⟩
  invFun y := ⟨(chart.symm ⟨y.1, y.2.1⟩).1, by
    refine ⟨(chart.symm ⟨y.1, y.2.1⟩).2, ?_⟩
    intro hC
    have hd := (hcut (chart.symm ⟨y.1, y.2.1⟩)).mp hC
    exact y.2.2 (by simpa using hd)⟩
  left_inv x := by
    apply Subtype.ext
    change (chart.symm (chart ⟨x.1, x.2.1⟩)).1 = x.1
    exact congrArg Subtype.val (chart.symm_apply_apply ⟨x.1, x.2.1⟩)
  right_inv y := by
    apply Subtype.ext
    change (chart (chart.symm ⟨y.1, y.2.1⟩)).1 = y.1
    exact congrArg Subtype.val (chart.apply_symm_apply ⟨y.1, y.2.1⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hinc : Continuous (fun x : (F \ C : Set X) =>
        (⟨x.1, x.2.1⟩ : F)) :=
      continuous_subtype_val.subtype_mk fun x => x.2.1
    exact (chart.continuous.comp hinc).subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hinc : Continuous (fun y : slitCell =>
        (⟨y.1, y.2.1⟩ : openCell)) :=
      continuous_subtype_val.subtype_mk fun y => y.2.1
    exact (chart.symm.continuous.comp hinc).subtype_val

private theorem nat_card_connectedComponents_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) := by
  have hfib : ∀ y : Y, IsConnected (e ⁻¹' {y}) := by
    intro y
    have heq : e ⁻¹' {y} = {e.symm y} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        apply e.injective
        simpa using h
      · rintro rfl
        exact e.apply_symm_apply y
    rw [heq]
    exact isConnected_singleton
  exact Nat.card_congr
    ((e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hfib).toEquiv)

/-- **Adapted-chart crosscut theorem.**  If an open face is charted by the
standard open 2-cell in such a way that the interior of an inserted crosscut is
the standard diameter, then deleting that crosscut splits the face into exactly
two connected components. -/
theorem nat_card_connectedComponents_face_diff_crosscut
    {X : Type*} [TopologicalSpace X] {F C : Set X}
    (chart : F ≃ₜ openCell)
    (hcut : ∀ x : F, x.1 ∈ C ↔ (chart x : ModelPlane) ∈ diameter) :
    Nat.card (ConnectedComponents (F \ C : Set X)) = 2 := by
  rw [nat_card_connectedComponents_homeomorph (slitChartHomeomorph chart hcut)]
  exact nat_card_connectedComponents_slitCell

end JordanCurve.Crosscut
