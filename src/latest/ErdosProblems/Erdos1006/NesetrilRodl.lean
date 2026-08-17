/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle, Boris Alexeev
-/

import ErdosProblems.Erdos1006.Core
import ErdosProblems.Erdos1006.Counting
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic

namespace Erdos1006

open scoped Classical BigOperators

section FiniteUnionBound

variable {R I A : Type*} [Fintype R] [Fintype I] [Fintype A]
  [DecidableEq R] [DecidableEq I] [DecidableEq A]

private def badLabelings (good : R → I → A) (r : R) : Finset (I → A) :=
  Finset.univ.filter fun label ↦ ∀ i, label i ≠ good r i

private def avoidEquiv (good : R → I → A) (r : R) :
    {label : I → A // ∀ i, label i ≠ good r i} ≃
      ((i : I) → {a : A // a ≠ good r i}) where
  toFun label i := ⟨label.1 i, label.2 i⟩
  invFun label := ⟨fun i ↦ (label i).1, fun i ↦ (label i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card_ne (a : A) :
    Fintype.card {x : A // x ≠ a} = Fintype.card A - 1 := by
  rw [Fintype.card_subtype_compl (fun x : A ↦ x = a)]
  simp

private lemma card_badLabelings (good : R → I → A) (r : R) :
    (badLabelings good r).card = (Fintype.card A - 1) ^ Fintype.card I := by
  rw [← Fintype.card_coe]
  let e₁ : {label : I → A // label ∈ badLabelings good r} ≃
      {label : I → A // ∀ i, label i ≠ good r i} :=
    Equiv.subtypeEquivRight (by
      intro label
      simp only [badLabelings, Finset.mem_filter, Finset.mem_univ, true_and])
  rw [Fintype.card_congr e₁, Fintype.card_congr (avoidEquiv good r)]
  simp only [Fintype.card_pi, card_ne]
  rw [Finset.prod_const, Finset.card_univ]

/-- A finite union bound in the form used by the Nešetřil--Rödl pasting
argument.  There are too few labelings avoiding the prescribed label in
every coordinate for even one row to cover all labelings. -/
theorem exists_labeling_hits_every_row (good : R → I → A)
    (hcard : Fintype.card R * (Fintype.card A - 1) ^ Fintype.card I <
      Fintype.card A ^ Fintype.card I) :
    ∃ label : I → A, ∀ r : R, ∃ i : I, label i = good r i := by
  classical
  by_contra! hno
  let badUnion : Finset (I → A) :=
    Finset.univ.biUnion (badLabelings good)
  have hcover : (Finset.univ : Finset (I → A)) ⊆ badUnion := by
    intro label _
    obtain ⟨r, hr⟩ := hno label
    simp only [badUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨r, by simpa only [badLabelings, Finset.mem_filter,
      Finset.mem_univ, true_and] using hr⟩
  have hle₁ : Fintype.card (I → A) ≤ badUnion.card := by
    simpa using Finset.card_le_card hcover
  have hle₂ : badUnion.card ≤
      ∑ r : R, (badLabelings good r).card := by
    dsimp only [badUnion]
    exact Finset.card_biUnion_le
  have hsum : (∑ r : R, (badLabelings good r).card) =
      Fintype.card R * (Fintype.card A - 1) ^ Fintype.card I := by
    simp only [card_badLabelings, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul]
  have htotal : Fintype.card (I → A) =
      Fintype.card A ^ Fintype.card I := by
    simp
  omega

end FiniteUnionBound

section PastedCycles

/-- One chosen direction around the five-cycle. `fromRel` below adds the
reverse directions. -/
private def c5Step (a b : Fin 5) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
    (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 0)

private def c5Graph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel c5Step

variable {X I : Type*}

/-- Paste a permuted copy of `C₅` into every five-vertex carrier block. -/
private def pastedC5 (block : I → Fin 5 → X)
    (label : I → Equiv.Perm (Fin 5)) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y ↦
    ∃ i a b, c5Graph.Adj a b ∧
      x = block i (label i a) ∧ y = block i (label i b)

private lemma pastedC5_local_adj (block : I → Fin 5 → X)
    (hblock : ∀ i, Function.Injective (block i))
    (label : I → Equiv.Perm (Fin 5)) (i : I) {a b : Fin 5}
    (hab : c5Graph.Adj a b) :
    (pastedC5 block label).Adj (block i (label i a)) (block i (label i b)) := by
  refine ⟨?_, Or.inl ⟨i, a, b, hab, rfl, rfl⟩⟩
  exact (hblock i).ne ((label i).injective.ne (c5Graph.ne_of_adj hab))

private lemma c5_adj_01 : c5Graph.Adj (0 : Fin 5) 1 := by
  exact ⟨by decide, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩

private lemma c5_adj_12 : c5Graph.Adj (1 : Fin 5) 2 := by
  exact ⟨by decide, Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩

private lemma c5_adj_23 : c5Graph.Adj (2 : Fin 5) 3 := by
  exact ⟨by decide, Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

private lemma c5_adj_34 : c5Graph.Adj (3 : Fin 5) 4 := by
  exact ⟨by decide, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩

private lemma c5_adj_04 : c5Graph.Adj (0 : Fin 5) 4 := by
  exact ⟨by decide,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

private lemma c5Graph_no_triangle : ¬HasTriangle c5Graph := by
  rintro ⟨a, b, c, hab, hac, hbc, eab, ebc, eca⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [c5Graph, c5Step]

private lemma c5Graph_no_fourCycle : ¬HasFourCycle c5Graph := by
  rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, eab, ebc, ecd, eda⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [c5Graph, c5Step]

/-- If one pasted local cycle is increasing in an ambient strict order, it
is a `HasMonotoneCycle` in the exact interface of `Erdos1006.Core`. -/
private theorem hasMonotoneCycle_pastedC5_of_increasing
    (block : I → Fin 5 → X) (hblock : ∀ i, Function.Injective (block i))
    (label : I → Equiv.Perm (Fin 5)) (lt : X → X → Prop)
    (i : I)
    (hincr : ∀ a b : Fin 5, a < b →
      lt (block i (label i a)) (block i (label i b))) :
    HasMonotoneCycle (pastedC5 block label) 5 lt := by
  let v : Fin 5 → X := fun a ↦ block i (label i a)
  have h01 : (pastedC5 block label).Adj (v 0) (v 1) :=
    pastedC5_local_adj block hblock label i c5_adj_01
  have h12 : (pastedC5 block label).Adj (v 1) (v 2) :=
    pastedC5_local_adj block hblock label i c5_adj_12
  have h23 : (pastedC5 block label).Adj (v 2) (v 3) :=
    pastedC5_local_adj block hblock label i c5_adj_23
  have h34 : (pastedC5 block label).Adj (v 3) (v 4) :=
    pastedC5_local_adj block hblock label i c5_adj_34
  have h04 : (pastedC5 block label).Adj (v 0) (v 4) :=
    pastedC5_local_adj block hblock label i c5_adj_04
  have hv_inj : Function.Injective v := (hblock i).comp (label i).injective
  have e01 : eraseArc (forwardArcs (pastedC5 block label).Adj lt) (v 0) (v 4)
      (v 0) (v 1) := by
    exact ⟨⟨h01, hincr 0 1 (by decide)⟩,
      fun h ↦ by have := hv_inj h.2; omega⟩
  have e12 : eraseArc (forwardArcs (pastedC5 block label).Adj lt) (v 0) (v 4)
      (v 1) (v 2) := by
    exact ⟨⟨h12, hincr 1 2 (by decide)⟩,
      fun h ↦ by have := hv_inj h.1; omega⟩
  have e23 : eraseArc (forwardArcs (pastedC5 block label).Adj lt) (v 0) (v 4)
      (v 2) (v 3) := by
    exact ⟨⟨h23, hincr 2 3 (by decide)⟩,
      fun h ↦ by have := hv_inj h.1; omega⟩
  have e34 : eraseArc (forwardArcs (pastedC5 block label).Adj lt) (v 0) (v 4)
      (v 3) (v 4) := by
    exact ⟨⟨h34, hincr 3 4 (by decide)⟩,
      fun h ↦ by have := hv_inj h.1; omega⟩
  refine ⟨v 0, v 4, ⟨h04, hincr 0 4 (by decide)⟩, ?_⟩
  exact (((PathN.single e01).tail e12).tail e23).tail e34

/-- The five distinct vertices of a carrier block can be enumerated in
increasing order for any strict total order. -/
private theorem exists_increasing_perm (f : Fin 5 → X)
    (hf : Function.Injective f) (lt : X → X → Prop)
    (hlt : IsStrictTotalOrder X lt) :
    ∃ p : Equiv.Perm (Fin 5),
      ∀ a b : Fin 5, a < b → lt (f (p a)) (f (p b)) := by
  classical
  letI : IsStrictTotalOrder X lt := hlt
  letI : DecidableRel lt := Classical.decRel lt
  letI : LinearOrder X := linearOrderOfSTO lt
  let s : Finset X := Finset.univ.image f
  have hs : s.card = 5 := by
    rw [show s = Finset.univ.image f from rfl,
      Finset.card_image_of_injective _ hf]
    simp
  let blockEquiv : Fin 5 ≃ s :=
    (Equiv.ofInjective f hf).trans (Equiv.setCongr (by
      ext x
      simp [s]))
  let sortedEquiv : Fin 5 ≃ s := s.orderIsoOfFin hs
  let p : Equiv.Perm (Fin 5) := sortedEquiv.trans blockEquiv.symm
  refine ⟨p, fun a b hab ↦ ?_⟩
  have hp (j : Fin 5) : f (p j) = (sortedEquiv j).1 := by
    have heq : blockEquiv (p j) = sortedEquiv j := by
      simp [p]
    exact congrArg Subtype.val heq
  rw [hp a, hp b]
  exact (s.orderIsoOfFin hs).lt_iff_lt.mpr hab

/-- A ranking of a finite type by its canonical finite ordinal. -/
private abbrev Rank (X : Type*) [Fintype X] :=
  X ≃ Fin (Fintype.card X)

private def rankLt {X : Type*} [Fintype X] (r : Rank X) (x y : X) : Prop :=
  (r x).val < (r y).val

private lemma rankLt_isStrictTotalOrder {X : Type*} [Fintype X]
    (r : Rank X) : IsStrictTotalOrder X (rankLt r) where
  irrefl x := by simp [rankLt]
  trans x y z hxy hyz := by exact lt_trans hxy hyz
  trichotomous x y hnxy hnyx := by
    apply r.injective
    apply Fin.ext
    simp only [rankLt] at hnxy hnyx
    omega

private noncomputable def prescribedPerm {X I : Type*} [Fintype X]
    (block : I → Fin 5 → X) (hblock : ∀ i, Function.Injective (block i))
    (r : Rank X) (i : I) : Equiv.Perm (Fin 5) :=
  Classical.choose
    (exists_increasing_perm (block i) (hblock i) (rankLt r)
      (rankLt_isStrictTotalOrder r))

private lemma prescribedPerm_increasing {X I : Type*} [Fintype X]
    (block : I → Fin 5 → X) (hblock : ∀ i, Function.Injective (block i))
    (r : Rank X) (i : I) :
    ∀ a b : Fin 5, a < b →
      rankLt r (block i (prescribedPerm block hblock r i a))
        (block i (prescribedPerm block hblock r i b)) :=
  Classical.choose_spec
    (exists_increasing_perm (block i) (hblock i) (rankLt r)
      (rankLt_isStrictTotalOrder r))

private lemma exists_rank_extending_order {X : Type*} [Fintype X]
    (lt : X → X → Prop) (hlt : IsStrictTotalOrder X lt) :
    ∃ r : Rank X, ∀ {x y}, rankLt r x y ↔ lt x y := by
  classical
  letI : IsStrictTotalOrder X lt := hlt
  letI : DecidableRel lt := Classical.decRel lt
  letI : LinearOrder X := linearOrderOfSTO lt
  have hcard : (Finset.univ : Finset X).card = Fintype.card X := by simp
  let sorted : Fin (Fintype.card X) ≃o (Finset.univ : Finset X) :=
    Finset.univ.orderIsoOfFin hcard
  let r : Rank X :=
    { toFun := fun x ↦ sorted.symm ⟨x, Finset.mem_univ x⟩
      invFun := fun j ↦ (sorted j).1
      left_inv := fun x ↦ by
        simpa only using congrArg Subtype.val (sorted.apply_symm_apply ⟨x, Finset.mem_univ x⟩)
      right_inv := fun j ↦ by
        exact sorted.symm_apply_apply j }
  refine ⟨r, fun {x y} ↦ ?_⟩
  change ((sorted.symm ⟨x, Finset.mem_univ x⟩).val <
    (sorted.symm ⟨y, Finset.mem_univ y⟩).val) ↔ lt x y
  exact sorted.symm.lt_iff_lt

/-- The complete second stage of the specialized Nešetřil--Rödl
construction.  Given sufficiently many injective carrier blocks, a finite
union bound chooses the local `C₅` labels so every vertex order sees one
local cycle monotonically. -/
theorem exists_pastedC5_everyOrder {X I : Type*} [Fintype X] [Fintype I]
    [DecidableEq X] [DecidableEq I]
    (block : I → Fin 5 → X) (hblock : ∀ i, Function.Injective (block i))
    (hcard : Fintype.card (Rank X) * 119 ^ Fintype.card I <
      120 ^ Fintype.card I) :
    ∃ label : I → Equiv.Perm (Fin 5),
      EveryOrderHasMonotoneCycle (pastedC5 block label) 5 := by
  classical
  have hperm : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hlabels := exists_labeling_hits_every_row
    (prescribedPerm block hblock)
    (R := Rank X) (I := I) (A := Equiv.Perm (Fin 5)) (by
      simpa [hperm] using hcard)
  obtain ⟨label, hlabel⟩ := hlabels
  refine ⟨label, fun lt hlt ↦ ?_⟩
  obtain ⟨r, hr⟩ := exists_rank_extending_order lt hlt
  obtain ⟨i, hi⟩ := hlabel r
  apply hasMonotoneCycle_pastedC5_of_increasing block hblock label lt i
  intro a b hab
  have hinc := prescribedPerm_increasing block hblock r i a b hab
  rw [hi]
  exact hr.mp hinc

/-! ### Transferring short-cycle freeness from the carrier hypergraph -/

private abbrev InBlock (block : I → Fin 5 → X) (i : I) (x : X) : Prop :=
  Erdos1006NR5.InBlock block i x

private abbrev NoBergeTwo (block : I → Fin 5 → X) : Prop :=
  Erdos1006NR5.NoBergeTwo block

private abbrev NoBergeThree (block : I → Fin 5 → X) : Prop :=
  Erdos1006NR5.NoBergeThree block

private abbrev NoBergeFour (block : I → Fin 5 → X) : Prop :=
  Erdos1006NR5.NoBergeFour block

private lemma pastedC5_adj_iff_exists_local (block : I → Fin 5 → X)
    (hblock : ∀ i, Function.Injective (block i))
    (label : I → Equiv.Perm (Fin 5)) (x y : X) :
    (pastedC5 block label).Adj x y ↔
      ∃ i a b, c5Graph.Adj a b ∧
        x = block i (label i a) ∧ y = block i (label i b) := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · obtain ⟨i, a, b, hab, hy, hx⟩ := h
      exact ⟨i, b, a, c5Graph.adj_symm hab, hx, hy⟩
  · rintro ⟨i, a, b, hab, rfl, rfl⟩
    exact pastedC5_local_adj block hblock label i hab

private lemma pastedC5_no_triangle_of_noBerge (block : I → Fin 5 → X)
    (hblock : ∀ i, Function.Injective (block i))
    (hB2 : NoBergeTwo block) (hB3 : NoBergeThree block)
    (label : I → Equiv.Perm (Fin 5)) :
    ¬HasTriangle (pastedC5 block label) := by
  rintro ⟨x, y, z, hxy, hxz, hyz, exy, eyz, ezx⟩
  obtain ⟨i, ai, bi, eab, hxi, hyi⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label x y).mp exy
  obtain ⟨j, aj, bj, ebc, hyj, hzj⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label y z).mp eyz
  obtain ⟨k, ak, bk, eca, hzk, hxk⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label z x).mp ezx
  have i_x : InBlock block i x := ⟨label i ai, hxi⟩
  have i_y : InBlock block i y := ⟨label i bi, hyi⟩
  have j_y : InBlock block j y := ⟨label j aj, hyj⟩
  have j_z : InBlock block j z := ⟨label j bj, hzj⟩
  have k_z : InBlock block k z := ⟨label k ak, hzk⟩
  have k_x : InBlock block k x := ⟨label k bk, hxk⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have hbi_aj : bi = aj := (label i).injective ((hblock i)
        (hyi.symm.trans hyj))
      have hbj_ak : bj = ak := (label i).injective ((hblock i)
        (hzj.symm.trans hzk))
      have hbk_ai : bk = ai := (label i).injective ((hblock i)
        (hxk.symm.trans hxi))
      subst aj
      subst ak
      subst bk
      apply c5Graph_no_triangle
      exact ⟨ai, bi, bj, eab.ne, eca.ne.symm, ebc.ne,
        eab, ebc, eca⟩
    · exact hB2 hik hxz i_x j_z k_x k_z
  · by_cases hjk : j = k
    · subst k
      exact hB2 (fun h ↦ hij h.symm) hxy k_x j_y i_x i_y
    · by_cases hik : i = k
      · subst k
        exact hB2 hij hyz i_y k_z j_y j_z
      · exact hB3 hij hik hjk hxy hxz hyz
          i_x i_y j_y j_z k_z k_x

private lemma pastedC5_no_fourCycle_of_noBerge (block : I → Fin 5 → X)
    (hblock : ∀ i, Function.Injective (block i))
    (hB2 : NoBergeTwo block) (hB3 : NoBergeThree block)
    (hB4 : NoBergeFour block)
    (label : I → Equiv.Perm (Fin 5)) :
    ¬HasFourCycle (pastedC5 block label) := by
  rintro ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz,
    ewx, exy, eyz, ezw⟩
  obtain ⟨i, ai, bi, ei, hwi, hxi⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label w x).mp ewx
  obtain ⟨j, aj, bj, ej, hxj, hyj⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label x y).mp exy
  obtain ⟨k, ak, bk, ek, hyk, hzk⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label y z).mp eyz
  obtain ⟨l, al, bl, el, hzl, hwl⟩ :=
    (pastedC5_adj_iff_exists_local block hblock label z w).mp ezw
  have i_w : InBlock block i w := ⟨label i ai, hwi⟩
  have i_x : InBlock block i x := ⟨label i bi, hxi⟩
  have j_x : InBlock block j x := ⟨label j aj, hxj⟩
  have j_y : InBlock block j y := ⟨label j bj, hyj⟩
  have k_y : InBlock block k y := ⟨label k ak, hyk⟩
  have k_z : InBlock block k z := ⟨label k bk, hzk⟩
  have l_z : InBlock block l z := ⟨label l al, hzl⟩
  have l_w : InBlock block l w := ⟨label l bl, hwl⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        have hbi_aj : bi = aj := (label i).injective ((hblock i)
          (hxi.symm.trans hxj))
        have hbj_ak : bj = ak := (label i).injective ((hblock i)
          (hyj.symm.trans hyk))
        have hbk_al : bk = al := (label i).injective ((hblock i)
          (hzk.symm.trans hzl))
        have hbl_ai : bl = ai := (label i).injective ((hblock i)
          (hwl.symm.trans hwi))
        subst aj
        subst ak
        subst al
        subst bl
        have hai_bj : ai ≠ bj := by
          intro h
          apply hwy
          calc
            w = block i (label i ai) := hwi
            _ = block i (label i bj) := by rw [h]
            _ = y := hyj.symm
        have hbi_bk : bi ≠ bk := by
          intro h
          apply hxz
          calc
            x = block i (label i bi) := hxi
            _ = block i (label i bk) := by rw [h]
            _ = z := hzk.symm
        apply c5Graph_no_fourCycle
        exact ⟨ai, bi, bj, bk, ei.ne, hai_bj, el.ne.symm,
          ej.ne, hbi_bk, ek.ne, ei, ej, ek, el⟩
      · exact hB2 hil hwz i_w k_z l_w l_z
    · by_cases hil : i = l
      · subst l
        exact hB2 hik hyz j_y l_z k_y k_z
      · by_cases hkl : k = l
        · subst l
          exact hB2 hik hwy i_w j_y l_w k_y
        · exact hB3 hik hil hkl hwy hwz hyz
            i_w j_y k_y k_z l_z l_w
  · by_cases hik : i = k
    · subst k
      exact hB2 hij hxy i_x k_y j_x j_y
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          exact hB2 hij hxz i_x l_z j_x k_z
        · exact hB3 hjk (fun h ↦ hij h.symm) (fun h ↦ hik h.symm)
            hxy hxz hyz
            j_x j_y k_y k_z l_z i_x
      · by_cases hjk : j = k
        · subst k
          by_cases hjl : j = l
          · subst l
            exact hB2 hij hwx i_w i_x l_w j_x
          · exact hB3 hij hil hjl
              hwx hwz hxz i_w i_x j_x k_z l_z l_w
        · by_cases hjl : j = l
          · subst l
            exact hB2 (fun h ↦ hij h.symm) hwx l_w j_x i_w i_x
          · by_cases hkl : k = l
            · subst l
              exact hB3 hij hik hjk hwx hwy hxy
                i_w i_x j_x j_y k_y l_w
            · exact hB4 hij hik hil hjk hjl hkl
                hwx hwy hwz hxy hxz hyz
                i_w i_x j_x j_y k_y k_z l_z l_w

private theorem pastedC5_girthGreaterThanFour_of_noBerge
    (block : I → Fin 5 → X) (hblock : ∀ i, Function.Injective (block i))
    (hB2 : NoBergeTwo block) (hB3 : NoBergeThree block)
    (hB4 : NoBergeFour block) (label : I → Equiv.Perm (Fin 5)) :
    GirthGreaterThanFour (pastedC5 block label) :=
  ⟨pastedC5_no_triangle_of_noBerge block hblock hB2 hB3 label,
    pastedC5_no_fourCycle_of_noBerge block hblock hB2 hB3 hB4 label⟩

/-! ### Assembly of the explicit finite construction -/

private lemma permutation_block_gain : 2 * 119 ^ 128 < 120 ^ 128 := by
  norm_num

private lemma explicit_K_eq : Erdos1006NR5.K =
    128 * (Erdos1006NR5.N * 64) := by
  simp [Erdos1006NR5.K]
  ring

private lemma order_union_bound_general (n k : ℕ) (hn : n = 2 ^ 64)
    (hk : k = 128 * (n * 64)) : n ^ n * 119 ^ k < 120 ^ k := by
  have hnpos : 0 < n := by rw [hn]; positivity
  have hpow : (2 * 119 ^ 128) ^ (n * 64) < (120 ^ 128) ^ (n * 64) := by
    exact Nat.pow_lt_pow_left permutation_block_gain
      (Nat.ne_of_gt (Nat.mul_pos hnpos (by norm_num)))
  have hnpow : n ^ n = 2 ^ (n * 64) := by
    calc
      n ^ n = (2 ^ 64) ^ n := by rw [hn]
      _ = 2 ^ (64 * n) := by rw [pow_mul]
      _ = 2 ^ (n * 64) := by rw [mul_comm 64 n]
  have h119pow : 119 ^ k = (119 ^ 128) ^ (n * 64) := by
    rw [hk, pow_mul]
  have h120pow : 120 ^ k = (120 ^ 128) ^ (n * 64) := by
    rw [hk, pow_mul]
  calc
    n ^ n * 119 ^ k = 2 ^ (n * 64) * (119 ^ 128) ^ (n * 64) := by
      rw [hnpow, h119pow]
    _ = (2 * 119 ^ 128) ^ (n * 64) := by rw [mul_pow]
    _ < (120 ^ 128) ^ (n * 64) := hpow
    _ = 120 ^ k := h120pow.symm

private lemma explicit_order_union_bound :
    Erdos1006NR5.N ^ Erdos1006NR5.N * 119 ^ Erdos1006NR5.K <
      120 ^ Erdos1006NR5.K := by
  exact order_union_bound_general Erdos1006NR5.N Erdos1006NR5.K rfl explicit_K_eq

private lemma rank_order_union_bound :
    Fintype.card (Rank (Fin Erdos1006NR5.N)) * 119 ^ Erdos1006NR5.K <
      120 ^ Erdos1006NR5.K := by
  apply lt_of_le_of_lt _ explicit_order_union_bound
  exact Nat.mul_le_mul_right _ (by
    rw [show Fintype.card (Rank (Fin Erdos1006NR5.N)) =
        Erdos1006NR5.N.factorial by
      simpa [Rank] using
        Fintype.card_equiv (Equiv.refl (Fin Erdos1006NR5.N))]
    exact Nat.factorial_le_pow Erdos1006NR5.N)

/-- Keep the assembly polymorphic in the two cardinalities.  In particular,
the elaborator never tries to enumerate the enormous concrete type `Fin K`
when the specialized theorem below applies this result. -/
private theorem assemble_pastedC5 {n k : ℕ}
    (block : Fin k → Fin 5 → Fin n)
    (hblock : ∀ i, Function.Injective (block i))
    (hB2 : NoBergeTwo block) (hB3 : NoBergeThree block)
    (hB4 : NoBergeFour block)
    (hcard : Fintype.card (Rank (Fin n)) *
        119 ^ Fintype.card (Fin k) < 120 ^ Fintype.card (Fin k)) :
    ∃ G : SimpleGraph (Fin n),
      GirthGreaterThanFour G ∧ EveryOrderHasMonotoneCycle G 5 := by
  obtain ⟨label, hmono⟩ :=
    exists_pastedC5_everyOrder block hblock hcard
  exact ⟨pastedC5 block label,
    pastedC5_girthGreaterThanFour_of_noBerge block hblock hB2 hB3 hB4 label,
    hmono⟩

/-- The specialized finite Nešetřil--Rödl theorem needed for Problem 1006:
there is a graph without triangles or quadrilaterals in which every strict
total vertex order contains a monotone five-cycle. -/
theorem exists_girthGreaterThanFour_everyOrderHasMonotoneFiveCycle :
    ∃ G : SimpleGraph (Fin Erdos1006NR5.N),
      GirthGreaterThanFour G ∧ EveryOrderHasMonotoneCycle G 5 := by
  obtain ⟨block, hblock, hB2, hB3, hB4⟩ := Erdos1006NR5.exists_NR_carrier
  have hcard :
      Fintype.card (Rank (Fin Erdos1006NR5.N)) *
          119 ^ Fintype.card (Fin Erdos1006NR5.K) <
        120 ^ Fintype.card (Fin Erdos1006NR5.K) := by
    simpa only [Fintype.card_fin] using rank_order_union_bound
  exact assemble_pastedC5 block hblock hB2 hB3 hB4 hcard

end PastedCycles

end Erdos1006
