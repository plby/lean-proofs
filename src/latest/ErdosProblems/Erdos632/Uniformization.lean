/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos632.Basic
import ErdosProblems.Erdos632.Graph
import ErdosProblems.Erdos632.Negative
import ErdosProblems.Erdos632.Positive

/-!
# The Dvořák--Hu--Sereni uniformization

This file carries out the final, uniform-list step in the counterexample to
Erdős Problem 632.  The nonuniform core gadget is `G5`; its prescribed lists
have sizes four, six, or eight.  We attach one copy of it to a root `K₄` for
each possible partition of eight new colours into four labelled pairs.
-/

namespace Erdos632

open Finset

/-- A labelled partition of eight colours into four disjoint pairs. -/
def RootPairing :=
  {ψ : Fin 4 → Finset (Fin 8) //
    (∀ i, (ψ i).card = 2) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (ψ i) (ψ j)}

noncomputable instance : Fintype RootPairing := by
  classical
  apply Fintype.subtype
    (Finset.univ.filter fun ψ : Fin 4 → Finset (Fin 8) ↦
      (∀ i, (ψ i).card = 2) ∧
        ∀ ⦃i j⦄, i ≠ j → Disjoint (ψ i) (ψ j))
  intro ψ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
noncomputable instance : DecidableEq RootPairing := Classical.decEq RootPairing

/-- The eight new colours, numbered `9,...,16`. -/
def externalColor (c : Fin 8) : ℕ := c.1 + 9

lemma externalColor_injective : Function.Injective externalColor := by
  intro a b h
  apply Fin.ext
  exact Nat.add_right_cancel h

/-- The natural-number version of one pair in a root pairing. -/
def RootPairing.colors (ψ : RootPairing) (i : Fin 4) : Finset ℕ :=
  (ψ.1 i).image externalColor

@[simp] lemma RootPairing.card_colors (ψ : RootPairing) (i : Fin 4) :
    (ψ.colors i).card = 2 := by
  change ((ψ.1 i).image externalColor).card = 2
  rw [Finset.card_image_of_injective _ externalColor_injective]
  exact ψ.2.1 i

lemma RootPairing.disjoint_colors (ψ : RootPairing) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (ψ.colors i) (ψ.colors j) := by
  rw [Finset.disjoint_left]
  intro c hci hcj
  simp only [RootPairing.colors, Finset.mem_image] at hci hcj
  obtain ⟨a, ha, rfl⟩ := hci
  obtain ⟨b, hb, hab⟩ := hcj
  have : a = b := externalColor_injective hab.symm
  subst b
  exact (Finset.disjoint_left.1 (ψ.2.2 hij)) ha hb

/-- The common list on the four root vertices. -/
def externalPalette : Finset ℕ := Finset.univ.image externalColor

@[simp] lemma card_externalPalette : externalPalette.card = 8 := by
  rw [externalPalette, Finset.card_image_of_injective _ externalColor_injective]
  simp

lemma RootPairing.colors_subset_externalPalette (ψ : RootPairing) (i : Fin 4) :
    ψ.colors i ⊆ externalPalette := by
  intro c hc
  simp only [RootPairing.colors, externalPalette, Finset.mem_image] at hc ⊢
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨x, Finset.mem_univ _, rfl⟩

/-- Decode a finite set of external natural-number colours back into `Fin 8`. -/
def decodeExternal (A : Finset ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun x ↦ externalColor x ∈ A

lemma image_decodeExternal_eq {A : Finset ℕ} (hA : A ⊆ externalPalette) :
    (decodeExternal A).image externalColor = A := by
  ext c
  constructor
  · simp only [Finset.mem_image, decodeExternal, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hc
    obtain ⟨x, -, hxc⟩ := Finset.mem_image.1 (hA hc)
    exact Finset.mem_image.2 ⟨x, by simp [decodeExternal, hxc, hc], hxc⟩

lemma card_decodeExternal {A : Finset ℕ} (hA : A ⊆ externalPalette) :
    (decodeExternal A).card = A.card := by
  calc
    (decodeExternal A).card = ((decodeExternal A).image externalColor).card :=
      (Finset.card_image_of_injective _ externalColor_injective).symm
    _ = A.card := congrArg Finset.card (image_decodeExternal_eq hA)

/-- Package four disjoint external pairs as the corresponding copy index. -/
def decodeRootPairing (A : Fin 4 → Finset ℕ)
    (hcard : ∀ i, (A i).card = 2)
    (hsub : ∀ i, A i ⊆ externalPalette)
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (A i) (A j)) : RootPairing :=
  ⟨fun i ↦ decodeExternal (A i),
    ⟨fun i ↦ (card_decodeExternal (hsub i)).trans (hcard i), by
      intro i j hij
      rw [Finset.disjoint_left]
      intro x hxi hxj
      simp only [decodeExternal, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
      exact (Finset.disjoint_left.1 (hdisj hij)) hxi hxj⟩⟩

@[simp] lemma decodeRootPairing_colors (A : Fin 4 → Finset ℕ)
    (hcard : ∀ i, (A i).card = 2)
    (hsub : ∀ i, A i ⊆ externalPalette)
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (A i) (A j)) (i : Fin 4) :
    (decodeRootPairing A hcard hsub hdisj).colors i = A i :=
  image_decodeExternal_eq (hsub i)

/-! ## The final finite graph -/

/-- The initial root vertices adjacent to the copy of a given `G5` vertex. -/
def rootSet (v : G5Vertex) : Finset (Fin 4) :=
  Finset.univ.filter fun i ↦ i.1 < rootNeighborCount v

@[simp] lemma mem_rootSet {v : G5Vertex} {i : Fin 4} :
    i ∈ rootSet v ↔ i.1 < rootNeighborCount v := by
  simp [rootSet]

@[simp] lemma card_rootSet (v : G5Vertex) :
    (rootSet v).card = rootNeighborCount v := by
  revert v
  decide

/-- Four root vertices, together with one disjoint `G5` copy for every root pairing. -/
inductive FinalVertex
  | root (i : Fin 4)
  | copy (ψ : RootPairing) (v : G5Vertex)

open FinalVertex

private def finalVertexEquiv : (Fin 4 ⊕ RootPairing × G5Vertex) ≃ FinalVertex where
  toFun
    | .inl i => root i
    | .inr (ψ, v) => copy ψ v
  invFun
    | root i => .inl i
    | copy ψ v => .inr (ψ, v)
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance : Fintype FinalVertex :=
  Fintype.ofEquiv (Fin 4 ⊕ RootPairing × G5Vertex) finalVertexEquiv

noncomputable instance : DecidableEq FinalVertex := Classical.decEq FinalVertex

/-- Adjacency in the final DHS graph. -/
def finalAdj : FinalVertex → FinalVertex → Prop
  | root i, root j => i ≠ j
  | copy ψ v, copy χ w => ψ = χ ∧ g5Graph.Adj v w
  | root i, copy _ v => i ∈ rootSet v
  | copy _ v, root i => i ∈ rootSet v

/-- The explicit finite graph which is 4-choosable but not `(8,2)`-choosable. -/
def finalGraph : SimpleGraph FinalVertex where
  Adj := finalAdj
  symm.symm := by
    intro u v h
    cases u with
    | root i =>
        cases v with
        | root j => exact h.symm
        | copy ψ w => exact h
    | copy ψ w =>
        cases v with
        | root i => exact h
        | copy χ z => exact ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := by
    intro u h
    cases u with
    | root i => exact h rfl
    | copy ψ v => exact g5Graph.loopless.irrefl v h.2

@[simp] lemma finalGraph_adj_root_root {i j : Fin 4} :
    finalGraph.Adj (root i) (root j) ↔ i ≠ j := Iff.rfl

@[simp] lemma finalGraph_adj_copy_copy {ψ χ : RootPairing} {v w : G5Vertex} :
    finalGraph.Adj (copy ψ v) (copy χ w) ↔ ψ = χ ∧ g5Graph.Adj v w := Iff.rfl

@[simp] lemma finalGraph_adj_root_copy {i : Fin 4} {ψ : RootPairing} {v : G5Vertex} :
    finalGraph.Adj (root i) (copy ψ v) ↔ i ∈ rootSet v := Iff.rfl

@[simp] lemma finalGraph_adj_copy_root {i : Fin 4} {ψ : RootPairing} {v : G5Vertex} :
    finalGraph.Adj (copy ψ v) (root i) ↔ i ∈ rootSet v := Iff.rfl

/-! ## The bad uniform eight-list assignment -/

/-- The new root-pair colours appended at one core vertex. -/
def padding (ψ : RootPairing) (v : G5Vertex) : Finset ℕ :=
  (rootSet v).biUnion ψ.colors

lemma padding_subset_externalPalette (ψ : RootPairing) (v : G5Vertex) :
    padding ψ v ⊆ externalPalette := by
  intro c hc
  obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 hc
  exact ψ.colors_subset_externalPalette i hc

lemma padding_card (ψ : RootPairing) (v : G5Vertex) :
    (padding ψ v).card = 2 * rootNeighborCount v := by
  rw [padding, Finset.card_biUnion]
  · simp only [RootPairing.card_colors, Finset.sum_const, nsmul_eq_mul, card_rootSet]
    exact Nat.mul_comm _ _
  · intro i hi j hj hij
    exact ψ.disjoint_colors hij

lemma colors8_disjoint_externalPalette : Disjoint colors8 externalPalette := by
  decide

lemma L5_disjoint_padding (ψ : RootPairing) (v : G5Vertex) :
    Disjoint (L5 v) (padding ψ v) :=
  colors8_disjoint_externalPalette.mono (L5_subset_colors8 v)
    (padding_subset_externalPalette ψ v)

/-- The exact eight-list assignment which has no two-fold colouring. -/
def badList : FinalVertex → Finset ℕ
  | root _ => externalPalette
  | copy ψ v => L5 v ∪ padding ψ v

@[simp] lemma badList_card (u : FinalVertex) : (badList u).card = 8 := by
  cases u with
  | root i => exact card_externalPalette
  | copy ψ v =>
      rw [badList, Finset.card_union_of_disjoint (L5_disjoint_padding ψ v), padding_card]
      exact L5_card_add_two_mul_rootNeighborCount v

/-! ## Universal four-choosability -/

universe u

/-- The uniformization step for the positive half.  This theorem is stated
against the precise interface supplied by the positive `G5` theorem, so the
argument remains palette-polymorphic. -/
theorem finalGraph_four_choosable_of_g5
    (hG5 : ∀ {Color : Type u} [DecidableEq Color]
      (L : G5Vertex → Finset Color),
      (∀ v, (L v).card = halfSize v) → HasLColoring g5Graph L) :
    IsABChoosable.{0, u} finalGraph 4 1 := by
  intro Color _ L hL
  classical
  have hall : ∀ s : Finset (Fin 4),
      s.card ≤ (s.biUnion fun i ↦ L (root i)).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ 4 := by simpa using Finset.card_le_univ s
        _ = (L (root i)).card := (hL (root i)).symm
        _ ≤ (s.biUnion fun j ↦ L (root j)).card :=
          Finset.card_le_card
            (Finset.subset_biUnion_of_mem (fun j : Fin 4 ↦ L (root j)) hi)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun i : Fin 4 ↦ L (root i))).1 hall
  let residual (ψ : RootPairing) (v : G5Vertex) : Finset Color :=
    L (copy ψ v) \ (rootSet v).image f
  have residual_large (ψ : RootPairing) (v : G5Vertex) :
      halfSize v ≤ (residual ψ v).card := by
    change halfSize v ≤ (L (copy ψ v) \ (rootSet v).image f).card
    have hbound := card_sub_card_le_card_sdiff
      (L (copy ψ v)) ((rootSet v).image f)
    have himage : ((rootSet v).image f).card = rootNeighborCount v := by
      rw [Finset.card_image_of_injective _ hf_inj, card_rootSet]
    rw [hL (copy ψ v), himage] at hbound
    have hsum := halfSize_add_rootNeighborCount v
    omega
  have thin_exists (ψ : RootPairing) (v : G5Vertex) :
      ∃ A : Finset Color, A ⊆ residual ψ v ∧ A.card = halfSize v :=
    Finset.exists_subset_card_eq (residual_large ψ v)
  choose thin hthin_sub hthin_card using thin_exists
  have copy_colorable (ψ : RootPairing) :
      HasLColoring g5Graph (thin ψ) :=
    hG5 (thin ψ) (hthin_card ψ)
  choose c hc using copy_colorable
  let finalColor : FinalVertex → Color
    | root i => f i
    | copy ψ v => c ψ v
  have final_proper : ∀ ⦃u v⦄, finalGraph.Adj u v → finalColor u ≠ finalColor v := by
    intro u v huv
    cases u with
    | root i =>
        cases v with
        | root j =>
            exact hf_inj.ne huv
        | copy ψ w =>
            intro heq
            have hcThin : c ψ w ∈ thin ψ w := (hc ψ).2 w
            have hcResidual : c ψ w ∈ residual ψ w := hthin_sub ψ w hcThin
            have hnot : c ψ w ∉ (rootSet w).image f := (Finset.mem_sdiff.1 hcResidual).2
            apply hnot
            exact Finset.mem_image.2 ⟨i, huv, heq⟩
    | copy ψ w =>
        cases v with
        | root i =>
            intro heq
            have hcThin : c ψ w ∈ thin ψ w := (hc ψ).2 w
            have hcResidual : c ψ w ∈ residual ψ w := hthin_sub ψ w hcThin
            have hnot : c ψ w ∉ (rootSet w).image f := (Finset.mem_sdiff.1 hcResidual).2
            apply hnot
            exact Finset.mem_image.2 ⟨i, huv, heq.symm⟩
        | copy χ z =>
            rw [finalGraph_adj_copy_copy] at huv
            rcases huv with ⟨rfl, hwz⟩
            exact (hc ψ).1 hwz
  have final_mem (u : FinalVertex) : finalColor u ∈ L u := by
    cases u with
    | root i => exact hf_mem i
    | copy ψ v =>
        exact (Finset.mem_sdiff.1 (hthin_sub ψ v ((hc ψ).2 v))).1
  refine ⟨fun u ↦ {finalColor u}, ?_⟩
  exact (isLMulticoloring_singleton_iff finalGraph L finalColor).2
    ⟨final_proper, final_mem⟩

/-- The positive half of the final Dvořák--Hu--Sereni counterexample. -/
theorem finalGraph_four_choosable :
    IsABChoosable.{0, u} finalGraph 4 1 :=
  finalGraph_four_choosable_of_g5 fun L hL ↦
    g5_half_list_colorable L hL

/-! ## Failure of `(8,2)`-choosability -/

/-- A two-fold colouring of the explicit bad assignment would restrict, in
the copy indexed by its four root pairs, to an `(L5,2)`-colouring of `G5`. -/
theorem no_badList_two_coloring_of_g5
    (hG5 : ¬ ∃ phi : G5Vertex → Finset ℕ,
      IsLMulticoloring g5Graph L5 phi 2) :
    ¬ ∃ phi : FinalVertex → Finset ℕ,
      IsLMulticoloring finalGraph badList phi 2 := by
  rintro ⟨phi, hphi⟩
  let A : Fin 4 → Finset ℕ := fun i ↦ phi (root i)
  have hAcard (i : Fin 4) : (A i).card = 2 := (hphi.2 (root i)).2
  have hAsub (i : Fin 4) : A i ⊆ externalPalette :=
    (hphi.2 (root i)).1
  have hAdisj : ∀ ⦃i j : Fin 4⦄, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    exact hphi.1 (finalGraph_adj_root_root.2 hij)
  let ψ : RootPairing := decodeRootPairing A hAcard hAsub hAdisj
  apply hG5
  refine ⟨fun v ↦ phi (copy ψ v), ?_, ?_⟩
  · intro v w hvw
    exact hphi.1 (finalGraph_adj_copy_copy.2 ⟨rfl, hvw⟩)
  · intro v
    refine ⟨?_, (hphi.2 (copy ψ v)).2⟩
    intro c hc
    have hcBad : c ∈ L5 v ∪ padding ψ v := (hphi.2 (copy ψ v)).1 hc
    rcases Finset.mem_union.1 hcBad with hcCore | hcPad
    · exact hcCore
    · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.1 hcPad
      have hciA : c ∈ A i := by
        rw [← decodeRootPairing_colors A hAcard hAsub hAdisj i]
        exact hci
      have hdis : Disjoint (phi (root i)) (phi (copy ψ v)) :=
        hphi.1 (finalGraph_adj_root_copy.2 hi)
      exact (Finset.disjoint_left.1 hdis) hciA hc |>.elim

/-- The explicit assignment `badList` witnesses failure of `(8,2)`-choosability. -/
theorem finalGraph_not_eight_two_choosable_of_g5
    (hG5 : ¬ ∃ phi : G5Vertex → Finset ℕ,
      IsLMulticoloring g5Graph L5 phi 2) :
    ¬ IsABChoosable.{0, 0} finalGraph 8 2 := by
  intro h
  obtain ⟨phi, hphi⟩ := h ℕ badList badList_card
  exact no_badList_two_coloring_of_g5 hG5 ⟨phi, hphi⟩

/-- The negative half of the final Dvořák--Hu--Sereni counterexample. -/
theorem finalGraph_not_eight_two_choosable :
    ¬ IsABChoosable.{0, 0} finalGraph 8 2 :=
  finalGraph_not_eight_two_choosable_of_g5 g5_not_twoColorable

/-- The complete explicit counterexample used to resolve Erdős Problem 632. -/
theorem finalGraph_counterexample :
    IsABChoosable.{0, 0} finalGraph 4 1 ∧
      ¬ IsABChoosable.{0, 0} finalGraph 8 2 :=
  ⟨finalGraph_four_choosable, finalGraph_not_eight_two_choosable⟩

end Erdos632
