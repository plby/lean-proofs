/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos615

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos22

attribute [local instance] Classical.propDecidable

open Erdos615.Construction

/-! ## Two finite graph operations -/

/-- Add an independent set of `t` vertices and join it completely to the
`true` Boolean part of `G`. -/
def oneSidedExtension {W : Type*} (G : SimpleGraph (Bool × W)) (t : ℕ) :
    SimpleGraph ((Bool × W) ⊕ Fin t) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr _ => u.1 = true
    | .inr _, .inl v => v.1 = true
    | .inr _, .inr _ => False
  symm.symm
    | .inl _, .inl _ => G.adj_symm
    | .inl _, .inr _ | .inr _, .inl _ => id
    | .inr _, .inr _ => id
  loopless.irrefl
    | .inl u => G.loopless.irrefl u
    | .inr _ => id

@[simp] lemma oneSidedExtension_adj_inl_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Bool × W) :
    (oneSidedExtension G t).Adj (.inl u) (.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inl_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Bool × W) (v : Fin t) :
    (oneSidedExtension G t).Adj (.inl u) (.inr v) ↔ u.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inr_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Fin t) (v : Bool × W) :
    (oneSidedExtension G t).Adj (.inr u) (.inl v) ↔ v.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_not_adj_inr_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Fin t) :
    ¬(oneSidedExtension G t).Adj (.inr u) (.inr v) := id

/-- A uniform independent-fibre blowup. -/
def uniformBlowup {V : Type*} (G : SimpleGraph V) (q : ℕ) :
    SimpleGraph (V × Fin q) where
  Adj u v := G.Adj u.1 v.1
  symm.symm _ _ := G.adj_symm
  loopless.irrefl u := G.loopless.irrefl u.1

@[simp] lemma uniformBlowup_adj {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (u v : V × Fin q) :
    (uniformBlowup G q).Adj u v ↔ G.Adj u.1 v.1 := Iff.rfl

/-- Add `r` isolated vertices to a uniform blowup. -/
abbrev paddedBlowup {V : Type*} (G : SimpleGraph V) (q r : ℕ) :
    SimpleGraph ((V × Fin q) ⊕ Fin r) := uniformBlowup G q ⊕g ⊥

/-! ## Clique-freeness of the one-sided extension -/

lemma BEGraph_no_samePart_triangle {h : ℕ} {ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha4 : a < 1 / 4) (b : Bool)
    (u v w : CopyVertex h ρ hh hρ L)
    (huv : (BEGraph h ρ hh hρ L a).Adj (b, u) (b, v))
    (huw : (BEGraph h ρ hh hρ L a).Adj (b, u) (b, w))
    (hvw : (BEGraph h ρ hh hρ L a).Adj (b, v) (b, w)) : False := by
  have hfar (x y : CopyVertex h ρ hh hρ L)
      (hxy : (BEGraph h ρ hh hρ L a).Adj (b, x) (b, y)) :
      2 - a < dist (position h ρ hh hρ L x) (position h ρ hh hρ L y) := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (b, x) (b, y)).mp hxy
    simpa [edgeRel] using H.2
  exact no_unit_far_triangle
    (position_norm h ρ hh hρ L u)
    (position_norm h ρ hh hρ L v)
    (position_norm h ρ hh hρ L w) ha0 ha4
    (hfar u v huv) (hfar u w huw) (hfar v w hvw)

lemma oneSidedExtension_cliqueFree_four {W : Type*} [Nonempty W]
    (G : SimpleGraph (Bool × W)) (t : ℕ)
    (hG : G.CliqueFree 4)
    (htri : ∀ u v w : W,
      G.Adj (true, u) (true, v) →
      G.Adj (true, u) (true, w) →
      G.Adj (true, v) (true, w) → False) :
    (oneSidedExtension G t).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (oneSidedExtension G t).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  by_cases hnew : ∃ i u, f i = .inr u
  · rcases hnew with ⟨i, u, hi⟩
    have hold (j : Fin 4) (hji : j ≠ i) : ∃ w : W, f j = .inl (true, w) := by
      cases hj : f j with
      | inl x =>
          have hx : x.1 = true := by
            have H := hadj j i hji
            simpa [hj, hi] using H
          rcases x with ⟨b, w⟩
          cases b <;> simp_all
      | inr v =>
          exfalso
          have H := hadj j i hji
          simpa [hj, hi] using H
    fin_cases i
    · rcases hold 1 (by decide) with ⟨v, hv⟩
      rcases hold 2 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 1 2 (by decide))
        (by simpa [hv, hx] using hadj 1 3 (by decide))
        (by simpa [hw, hx] using hadj 2 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 2 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 2 (by decide))
        (by simpa [hv, hx] using hadj 0 3 (by decide))
        (by simpa [hw, hx] using hadj 2 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 1 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 1 (by decide))
        (by simpa [hv, hx] using hadj 0 3 (by decide))
        (by simpa [hw, hx] using hadj 1 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 1 (by decide) with ⟨w, hw⟩
      rcases hold 2 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 1 (by decide))
        (by simpa [hv, hx] using hadj 0 2 (by decide))
        (by simpa [hw, hx] using hadj 1 2 (by decide))
  · have hold (i : Fin 4) : ∃ x : Bool × W, f i = .inl x := by
      cases hi : f i with
      | inl x => exact ⟨x, rfl⟩
      | inr u => exact False.elim (hnew ⟨i, u, hi⟩)
    choose g hg using hold
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro H
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ G.loopless.irrefl (g i) (hij ▸ H))
          · intro hij
            have H := hadj i j ((SimpleGraph.top_adj i j).mp hij)
            simpa [hg i, hg j] using H }
    exact e.isContained.not_cliqueFree hG

/-! ## Independence-number bounds -/

private noncomputable def leftPart {A B : Type*} [Fintype A]
    (s : Finset (A ⊕ B)) : Finset A :=
  Finset.univ.filter fun a ↦ Sum.inl a ∈ s

private lemma card_le_leftPart_add {A B : Type*} [Fintype A] [Fintype B]
    (s : Finset (A ⊕ B)) :
    s.card ≤ (leftPart s).card + Fintype.card B := by
  classical
  let f : s → (leftPart s) ⊕ B
    | ⟨.inl a, ha⟩ => .inl ⟨a, by simp [leftPart, ha]⟩
    | ⟨.inr b, _⟩ => .inr b
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rcases x with a | b <;> rcases y with a' | b' <;>
      simp [f] at hxy ⊢
    · exact congrArg Subtype.val hxy
    · exact hxy
  have H := Fintype.card_le_of_injective f hf
  simpa using H

private lemma leftPart_independent {A B : Type*} [Fintype A]
    (H : SimpleGraph (A ⊕ B)) (G : SimpleGraph A)
    (hleft : ∀ a b, H.Adj (.inl a) (.inl b) ↔ G.Adj a b)
    (s : Finset (A ⊕ B)) (hs : H.IsIndepSet s) :
    G.IsIndepSet (leftPart s) := by
  classical
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  intro a ha b hb hab hadj
  have ha' : Sum.inl a ∈ s := (Finset.mem_filter.mp ha).2
  have hb' : Sum.inl b ∈ s := (Finset.mem_filter.mp hb).2
  exact hs ha' hb' (by simpa using hab) ((hleft a b).mpr hadj)

lemma indepNum_le_left_add {A B : Type*} [Fintype A] [Fintype B]
    (H : SimpleGraph (A ⊕ B)) (G : SimpleGraph A)
    (hleft : ∀ a b, H.Adj (.inl a) (.inl b) ↔ G.Adj a b) :
    H.indepNum ≤ G.indepNum + Fintype.card B := by
  classical
  rcases H.exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rw [← hs.card_eq]
  calc
    s.card ≤ (leftPart s).card + Fintype.card B := card_le_leftPart_add s
    _ ≤ G.indepNum + Fintype.card B :=
      Nat.add_le_add_right (leftPart_independent H G hleft s hs.isIndepSet).card_le_indepNum _

lemma oneSidedExtension_indepNum_le {W : Type*} [Fintype W]
    (G : SimpleGraph (Bool × W)) (t : ℕ) :
    (oneSidedExtension G t).indepNum ≤ G.indepNum + t := by
  simpa using indepNum_le_left_add (oneSidedExtension G t) G
    (fun _ _ ↦ oneSidedExtension_adj_inl_inl G t _ _)

lemma uniformBlowup_indepNum_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) :
    (uniformBlowup G q).indepNum ≤ q * G.indepNum := by
  classical
  rcases (uniformBlowup G q).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have himage : G.IsIndepSet (s.image Prod.fst) := by
    have hs' := hs.isIndepSet
    rw [SimpleGraph.isIndepSet_iff] at hs' ⊢
    intro a ha b hb hab hadj
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, hy, hfy⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hab hfy
    exact hs' hx hy hxy (by simpa [hfy] using hadj)
  have hfiber (b : V) (hb : b ∈ s.image Prod.fst) :
      {a ∈ s | a.1 = b}.card ≤ q := by
    have H := Finset.card_le_card_of_injOn (fun a : V × Fin q ↦ a.2)
      (s := {a ∈ s | a.1 = b}) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)
      (by
        intro x hx y hy hsecond
        have hxfirst := (Finset.mem_filter.mp hx).2
        have hyfirst := (Finset.mem_filter.mp hy).2
        exact Prod.ext (hxfirst.trans hyfirst.symm) hsecond)
    simpa using H
  rw [← hs.card_eq]
  calc
    s.card ≤ q * (s.image Prod.fst).card :=
      Finset.card_le_mul_card_image s q hfiber
    _ ≤ q * G.indepNum := Nat.mul_le_mul_left q himage.card_le_indepNum

lemma paddedBlowup_indepNum_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q r : ℕ) :
    (paddedBlowup G q r).indepNum ≤ q * G.indepNum + r := by
  calc
    (paddedBlowup G q r).indepNum ≤ (uniformBlowup G q).indepNum + r := by
      simpa [paddedBlowup] using indepNum_le_left_add
        (uniformBlowup G q ⊕g (⊥ : SimpleGraph (Fin r))) (uniformBlowup G q)
        (fun _ _ ↦ SimpleGraph.sum_adj_inl)
    _ ≤ q * G.indepNum + r :=
      Nat.add_le_add_right (uniformBlowup_indepNum_le G q) r

/-! ## Clique-freeness and edge counts of blowups -/

lemma uniformBlowup_cliqueFree_four {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (hG : G.CliqueFree 4) : (uniformBlowup G q).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (uniformBlowup G q).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  have hproj : Function.Injective (fun i : Fin 4 ↦ (f i).1) := by
    intro i j hij
    by_contra hne
    have H := hadj i j hne
    exact G.loopless.irrefl (f i).1 (by simpa [hij] using H)
  let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
    { toFun := fun i ↦ (f i).1
      inj' := hproj
      map_rel_iff' := by
        intro i j
        constructor
        · intro H
          exact (SimpleGraph.top_adj i j).mpr
            (fun hij ↦ G.loopless.irrefl (f i).1 (hij ▸ H))
        · intro hij
          exact hadj i j ((SimpleGraph.top_adj i j).mp hij) }
  exact e.isContained.not_cliqueFree hG

lemma sum_cliqueFree_four {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B)
    (hG : G.CliqueFree 4) (hH : H.CliqueFree 4) : (G ⊕g H).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) : (G ⊕g H).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  rcases h0 : f 0 with a | b
  · have hall (i : Fin 4) : ∃ a : A, f i = .inl a := by
      by_cases hi : i = 0
      · subst i; exact ⟨a, h0⟩
      · cases hfi : f i with
        | inl x => exact ⟨x, rfl⟩
        | inr y => exfalso; simpa [h0, hfi] using hadj 0 i (Ne.symm hi)
    choose g hg using hall
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro had
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ G.loopless.irrefl (g i) (hij ▸ had))
          · intro hij
            simpa [hg i, hg j] using hadj i j ((SimpleGraph.top_adj i j).mp hij) }
    exact e.isContained.not_cliqueFree hG
  · have hall (i : Fin 4) : ∃ b : B, f i = .inr b := by
      by_cases hi : i = 0
      · subst i; exact ⟨b, h0⟩
      · cases hfi : f i with
        | inl x => exfalso; simpa [h0, hfi] using hadj 0 i (Ne.symm hi)
        | inr y => exact ⟨y, rfl⟩
    choose g hg using hall
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g H :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro had
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ H.loopless.irrefl (g i) (hij ▸ had))
          · intro hij
            simpa [hg i, hg j] using hadj i j ((SimpleGraph.top_adj i j).mp hij) }
    exact e.isContained.not_cliqueFree hH

lemma bot_cliqueFree_four {V : Type*} : (⊥ : SimpleGraph V).CliqueFree 4 := by
  intro s hs
  have hcard := hs.card_eq
  have hle : s.card ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ s.card := by omega
    rcases Finset.one_lt_card.mp (by omega : 1 < s.card) with ⟨x, hx, y, hy, hxy⟩
    simpa using hs.isClique hx hy hxy
  omega

lemma paddedBlowup_cliqueFree_four {V : Type*} (G : SimpleGraph V) (q r : ℕ)
    (hG : G.CliqueFree 4) : (paddedBlowup G q r).CliqueFree 4 :=
  sum_cliqueFree_four _ _ (uniformBlowup_cliqueFree_four G q hG) bot_cliqueFree_four

private def uniformBlowupDartEquiv {V : Type*} (G : SimpleGraph V) (q : ℕ) :
    (uniformBlowup G q).Dart ≃ G.Dart × (Fin q × Fin q) where
  toFun d := (⟨(d.fst.1, d.snd.1), d.adj⟩, (d.fst.2, d.snd.2))
  invFun d := ⟨((d.1.fst, d.2.1), (d.1.snd, d.2.2)), d.1.adj⟩
  left_inv := by rintro ⟨⟨⟨v, i⟩, ⟨w, j⟩⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨⟨v, w⟩, h⟩, ⟨i, j⟩⟩; rfl

lemma uniformBlowup_edgeCard {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) :
    Nat.card (uniformBlowup G q).edgeSet = q ^ 2 * Nat.card G.edgeSet := by
  classical
  have hc := Fintype.card_congr (uniformBlowupDartEquiv G q)
  have hblow := (uniformBlowup G q).dart_card_eq_twice_card_edges
  have hbase := G.dart_card_eq_twice_card_edges
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  rw [hblow, hbase, (uniformBlowup G q).edgeFinset_card, G.edgeFinset_card,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hc
  apply Nat.mul_left_cancel (n := 2)
  · norm_num
  · calc
      2 * Nat.card (uniformBlowup G q).edgeSet =
          2 * Nat.card G.edgeSet * (q * q) := hc
      _ = 2 * (q ^ 2 * Nat.card G.edgeSet) := by rw [pow_two]; ac_rfl

lemma paddedBlowup_edgeCard {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q r : ℕ) :
    Nat.card (paddedBlowup G q r).edgeSet = q ^ 2 * Nat.card G.edgeSet := by
  classical
  calc
    Nat.card (paddedBlowup G q r).edgeSet =
        Nat.card (uniformBlowup G q).edgeSet +
          Nat.card (⊥ : SimpleGraph (Fin r)).edgeSet := by
      rw [Nat.card_congr (SimpleGraph.edgeSetSumEquiv
        (G := uniformBlowup G q) (H := (⊥ : SimpleGraph (Fin r)))), Nat.card_sum]
    _ = Nat.card (uniformBlowup G q).edgeSet := by simp
    _ = q ^ 2 * Nat.card G.edgeSet := uniformBlowup_edgeCard G q

private lemma sym2_map_inl_ne_cross {A B : Type*} (e : Sym2 A) (a : A) (b : B) :
    Sym2.map Sum.inl e ≠ s(Sum.inr b, Sum.inl a) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_pair_eq]
      intro H
      rw [Sym2.eq_iff] at H
      simp at H

lemma oneSidedExtension_edgeCard_lower {W : Type*} [Fintype W]
    (G : SimpleGraph (Bool × W)) (t : ℕ) :
    Nat.card G.edgeSet + t * Fintype.card W ≤
      Nat.card (oneSidedExtension G t).edgeSet := by
  classical
  let eOld : G ↪g oneSidedExtension G t :=
    { toFun := Sum.inl
      inj' := Sum.inl_injective
      map_rel_iff' := by simp }
  let F : G.edgeSet ⊕ (Fin t × W) → (oneSidedExtension G t).edgeSet
    | .inl e => eOld.mapEdgeSet e
    | .inr p => ⟨s(.inr p.1, .inl (true, p.2)), by simp⟩
  have hF : Function.Injective F := by
    rintro (e | p) (e' | p') heq
    · change eOld.mapEdgeSet e = eOld.mapEdgeSet e' at heq
      congr 1
      exact eOld.mapEdgeSet.injective heq
    · exfalso
      have H := congrArg Subtype.val heq
      simp only [F, SimpleGraph.Embedding.mapEdgeSet_apply] at H
      dsimp [SimpleGraph.Hom.mapEdgeSet, eOld] at H
      exact sym2_map_inl_ne_cross e.1 (true, p'.2) p'.1 H
    · exfalso
      have H := congrArg Subtype.val heq
      simp only [F, SimpleGraph.Embedding.mapEdgeSet_apply] at H
      dsimp [SimpleGraph.Hom.mapEdgeSet, eOld] at H
      exact sym2_map_inl_ne_cross e'.1 (true, p.2) p.1 H.symm
    · congr 1
      have H := congrArg Subtype.val heq
      change s(Sum.inr p.1, Sum.inl (true, p.2)) =
        s(Sum.inr p'.1, Sum.inl (true, p'.2)) at H
      rw [Sym2.eq_iff] at H
      simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
        Sum.inr.injEq, Sum.inr_ne_inl, false_and, Sum.inl_ne_inr, or_false] at H
      exact Prod.ext H.1 H.2.2
  have H := Nat.card_le_card_of_injective F hF
  simpa [Nat.card_sum, Nat.card_prod, Nat.card_fin] using H

/-! ## A strict-density seed from the finite Bollobás--Erdős graph -/

structure StrictSeed (ε : ℝ) where
  Vertex : Type
  fintypeVertex : Fintype Vertex
  graph : SimpleGraph Vertex
  card_pos : 0 < @Fintype.card Vertex fintypeVertex
  cliqueFree : graph.CliqueFree 4
  indep_small : 4 * (graph.indepNum : ℝ) <
    ε * (@Fintype.card Vertex fintypeVertex : ℕ)
  edge_strict : (@Fintype.card Vertex fintypeVertex) ^ 2 <
    8 * Nat.card graph.edgeSet

lemma eventually_seed_error_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.exp (-(K : ℝ)) + 1 / (K : ℝ) ^ 22 + 50 / (K : ℝ) < ε / 4 := by
  have hExp : Tendsto (fun K : ℕ ↦ Real.exp (-(K : ℝ))) atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using H
  have hInv22 : Tendsto (fun K : ℕ ↦ 1 / (K : ℝ) ^ 22) atTop (𝓝 0) := by
    have H : Tendsto (fun K : ℕ ↦ ((K : ℝ)⁻¹) ^ 22) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).pow 22
    simpa [div_eq_mul_inv, inv_pow] using H
  have hInv : Tendsto (fun K : ℕ ↦ 50 / (K : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 50
    simpa [Function.comp_def, div_eq_mul_inv] using H
  have H := (hExp.add hInv22).add hInv
  exact (tendsto_order.1 H).2 (ε / 4) (by nlinarith)

lemma exists_strictSeed (ε : ℝ) (hε : 0 < ε) : Nonempty (StrictSeed ε) := by
  obtain ⟨K, hK30, hKerr⟩ :=
    ((eventually_ge_atTop 30).and (eventually_seed_error_small ε hε)).exists
  have hKpos : 0 < K := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  let h : ℕ := K ^ 12
  have hh : 1 < h := by
    have Hpow : 2 ^ 12 ≤ K ^ 12 := Nat.pow_le_pow_left (by omega) 12
    norm_num [h] at Hpow ⊢
    omega
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  let a : ℝ := 1 / (K : ℝ) ^ 7
  let ρ : ℝ := a / 16
  have ha : 0 < a := by dsimp [a]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsqrt : Real.sqrt (h : ℝ) = (K : ℝ) ^ 6 := by
    rw [show (h : ℝ) = ((K : ℝ) ^ 6) ^ 2 by
      norm_num [h]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hβ : a + 2 * ρ = 9 / (8 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  have herror : 4 * (a + 2 * ρ) * Real.sqrt h = 9 / (2 * (K : ℝ)) := by
    rw [hβ, hsqrt]
    field_simp
    ring
  have hβ0 : 0 ≤ a + 2 * ρ := by positivity
  have hβ1 : a + 2 * ρ ≤ 1 := by
    rw [hβ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * K ^ 7)).2
    have hpowK : (K : ℝ) ≤ K ^ 7 := by
      calc
        (K : ℝ) = K * 1 := by ring
        _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
        _ = K ^ 7 := by ring
    have hK9 : (9 : ℝ) ≤ K := by exact_mod_cast (show 9 ≤ K by omega)
    nlinarith
  have hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2 := by
    rw [herror]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).2
    nlinarith [show (9 : ℝ) ≤ K by exact_mod_cast (show 9 ≤ K by omega)]
  have ha0 : 0 ≤ a := ha.le
  have ha2 : a ≤ 2 := by
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact (div_le_one (by positivity)).2 (one_le_pow₀ hKone)
    linarith
  have ha4 : a < 1 / 4 := by
    have hpow : (4 : ℝ) < K ^ 7 := by
      have hK4 : (4 : ℝ) < K := by exact_mod_cast (show 4 < K by omega)
      calc
        (4 : ℝ) < K := hK4
        _ ≤ K ^ 7 := by
          calc
            (K : ℝ) = K * 1 := by ring
            _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
            _ = K ^ 7 := by ring
    dsimp [a]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K ^ 7)]
    nlinarith
  have haMix : a < 2 * (Real.sqrt 2 - 1) := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt54 : (5 : ℝ) / 4 < Real.sqrt 2 := by nlinarith
    nlinarith [ha4]
  have hd1 : 1 ≤ 2 - a + 2 * ρ := by nlinarith [hρ.le]
  let B : ℕ := netCard h ρ hρ
  have hBpos : 0 < B := netCard_pos h ρ hh0 hρ
  let L : ℕ := (B + 1) * K ^ 22
  have hLpos : 0 < L := by dsimp [L]; positivity
  let M : ℕ := copyCard h ρ hh0 hρ L
  let W := CopyVertex h ρ hh0 hρ L
  let G : SimpleGraph (Bool × W) := BEGraph h ρ hh0 hρ L a
  have hMlower : L ≤ M := scale_le_copyCard h ρ hh0 hρ L
  have hMupper : M ≤ L + B := copyCard_le_scale_add h ρ hh0 hρ L
  have hedgeRaw : (L : ℝ) ^ 2 *
      (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤ Nat.card G.edgeSet := by
    simpa [G] using BEGraph_edgeCard_lower h ρ hh hρ L a hβ0 hβ1 hsmall
  have hfreeRaw : G.CliqueFree 4 := by
    simpa [G] using BEGraph_cliqueFree_four h ρ hh0 hρ L a ha0 ha4 haMix
  have hindRaw : (G.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B) := by
    simpa [G] using BEGraph_indepNum_bound h ρ hh0 hρ L a ha2 hd1
  have hK22 : (K : ℝ) ≤ K ^ 22 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 21 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
      _ = K ^ 22 := by ring
  have hBKleL : (B : ℝ) * K ≤ L := by
    calc
      (B : ℝ) * K ≤ B * K ^ 22 :=
        mul_le_mul_of_nonneg_left hK22 (Nat.cast_nonneg B)
      _ ≤ (B + 1) * K ^ 22 := by gcongr; norm_num
      _ = (L : ℕ) := by norm_cast
  have hBdiv : (B : ℝ) ≤ L / K := (le_div_iff₀ hKR).2 hBKleL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hMbound : (M : ℝ) ≤ L * (1 + 1 / K) := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    calc
      (M : ℝ) ≤ L + B := HM
      _ ≤ L + L / K := by gcongr
      _ = L * (1 + 1 / K) := by ring
  have hradiusBase : (2 - a + 2 * ρ) / 2 =
      1 - 7 / (16 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  let x : ℝ := 7 / (16 * (K : ℝ) ^ 7)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * K ^ 7)).2
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have honeSub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbaseExp : 1 - x ≤ Real.exp (-x) := by
    simpa [add_comm] using Real.add_one_le_exp (-x)
  have hpowExp : (1 - x) ^ h ≤ Real.exp (-x) ^ h :=
    pow_le_pow_left₀ honeSub hbaseExp h
  have hhcast : (h : ℝ) = (K : ℝ) ^ 12 := by norm_num [h]
  have hexponent : Real.exp (-x) ^ h = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    dsimp [x]
    rw [hhcast]
    field_simp
  have hKexp : (K : ℝ) ≤ 7 * K ^ 5 / 16 := by
    have hK4 : (16 : ℝ) ≤ 7 * K ^ 4 := by
      have hK4thirty : (30 : ℝ) ^ 4 ≤ K ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hK30) 4
      norm_num at hK4thirty ⊢
      nlinarith only [hK4thirty]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have Hmul := mul_le_mul_of_nonneg_left hK4 hKR.le
    nlinarith only [Hmul]
  have halphaExp : ((2 - a + 2 * ρ) / 2) ^ h ≤ Real.exp (-(K : ℝ)) := by
    rw [hradiusBase]
    change (1 - x) ^ h ≤ _
    calc
      (1 - x) ^ h ≤ Real.exp (-x) ^ h := hpowExp
      _ = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := hexponent
      _ ≤ Real.exp (-(K : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hKexp])
  have hBK22leL : (B : ℝ) * K ^ 22 ≤ L := by
    change (B : ℝ) * K ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    gcongr
    norm_num
  have hRound : (B : ℝ) / L ≤ 1 / K ^ 22 := by
    rw [div_le_div_iff₀ hLR (by positivity : (0 : ℝ) < K ^ 22)]
    simpa using hBK22leL
  let t : ℕ := 100 * (B + 1) * K ^ 21
  let H : SimpleGraph ((Bool × W) ⊕ Fin t) := oneSidedExtension G t
  let instW : Fintype W := inferInstance
  have hWcard : @Fintype.card W instW = M := by simp [instW, W, M, copyCard]
  have hMpos : 0 < M := hLpos.trans_le hMlower
  letI : Nonempty W := Fintype.card_pos_iff.mp (by simpa [hWcard] using hMpos)
  have hfreeH : H.CliqueFree 4 := by
    apply oneSidedExtension_cliqueFree_four G t hfreeRaw
    intro u v w
    exact BEGraph_no_samePart_triangle hh0 hρ L a ha0 ha4 true u v w
  have htEq : (t : ℝ) = 100 * (L : ℝ) / K := by
    dsimp [t, L]
    push_cast
    field_simp
  have hedgeRaw' : (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) ≤
      Nat.card G.edgeSet := by simpa [herror] using hedgeRaw
  have hedgeExtNat := oneSidedExtension_edgeCard_lower G t
  rw [hWcard] at hedgeExtNat
  have hedgeExt : (Nat.card G.edgeSet : ℝ) + (t : ℝ) * M ≤
      Nat.card H.edgeSet := by
    exact_mod_cast hedgeExtNat
  have hMlowerR : (L : ℝ) ≤ M := by exact_mod_cast hMlower
  have hedgeH : (L : ℝ) ^ 2 * (1 / 2 + 191 / (2 * K)) ≤
      Nat.card H.edgeSet := by
    have htpos : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have htmul : (100 * (L : ℝ) / K) * L ≤ (t : ℝ) * M := by
      rw [← htEq]
      exact mul_le_mul_of_nonneg_left hMlowerR htpos
    have hident : (100 * (L : ℝ) / K) * L = 100 * (L : ℝ) ^ 2 / K := by ring
    rw [hident] at htmul
    calc
      (L : ℝ) ^ 2 * (1 / 2 + 191 / (2 * K)) =
          (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) + 100 * (L : ℝ) ^ 2 / K := by
            field_simp
            ring
      _ ≤ (Nat.card G.edgeSet : ℝ) + (t : ℝ) * M := add_le_add hedgeRaw' htmul
      _ ≤ Nat.card H.edgeSet := hedgeExt
  let instH : Fintype ((Bool × W) ⊕ Fin t) := inferInstance
  have hcardH : @Fintype.card ((Bool × W) ⊕ Fin t) instH = 2 * M + t := by
    simp [instH, hWcard]
  have hcardHpos : 0 < @Fintype.card ((Bool × W) ⊕ Fin t) instH := by
    rw [hcardH]
    omega
  have hcardBound : ((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ≤
      2 * (L : ℝ) * (1 + 51 / K) := by
    rw [hcardH]
    push_cast
    rw [htEq]
    calc
      2 * (M : ℝ) + 100 * (L : ℝ) / K ≤
          2 * ((L : ℝ) * (1 + 1 / K)) + 100 * (L : ℝ) / K := by
            gcongr
      _ = 2 * (L : ℝ) * (1 + 51 / K) := by ring
  have hcardSq : (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 ≤
      (L : ℝ) ^ 2 * (1 / 2 + 51 / K + 2601 / (2 * K ^ 2)) := by
    have hcardNonneg : (0 : ℝ) ≤ (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) :=
      Nat.cast_nonneg _
    have hrightNonneg : (0 : ℝ) ≤ 2 * (L : ℝ) * (1 + 51 / K) := by positivity
    have hsq := pow_le_pow_left₀ hcardNonneg hcardBound 2
    calc
      (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 ≤
          (2 * (L : ℝ) * (1 + 51 / K)) ^ 2 / 8 := by gcongr
      _ = (L : ℝ) ^ 2 * (1 / 2 + 51 / K + 2601 / (2 * K ^ 2)) := by ring
  have hcoeff : (1 : ℝ) / 2 + 51 / K + 2601 / (2 * K ^ 2) <
      1 / 2 + 191 / (2 * K) := by
    field_simp [hKR.ne']
    nlinarith only [show (30 : ℝ) ≤ K by exact_mod_cast hK30]
  have hedgeStrictR :
      (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 <
        Nat.card H.edgeSet := by
    have hLsqPos : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos hLR
    exact lt_of_le_of_lt hcardSq <|
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hcoeff hLsqPos) hedgeH
  have hedgeStrictNat : (@Fintype.card ((Bool × W) ⊕ Fin t) instH) ^ 2 <
      8 * Nat.card H.edgeSet := by
    let m : ℕ := @Fintype.card ((Bool × W) ⊕ Fin t) instH
    let E : ℕ := Nat.card H.edgeSet
    have hreal : (m : ℝ) ^ 2 < 8 * (E : ℝ) := by
      have hbase : (m : ℝ) ^ 2 / 8 < (E : ℝ) := by
        simpa [m, E] using hedgeStrictR
      calc
        (m : ℝ) ^ 2 = 8 * ((m : ℝ) ^ 2 / 8) := by ring
        _ < 8 * (E : ℝ) := mul_lt_mul_of_pos_left hbase (by norm_num)
    have hnat : m ^ 2 < 8 * E := by exact_mod_cast hreal
    simpa [m, E] using hnat
  have hindHNat := oneSidedExtension_indepNum_le G t
  have hindH : (H.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * Real.exp (-(K : ℝ)) + B) + t := by
    have hindH' : (H.indepNum : ℝ) ≤ (G.indepNum : ℝ) + t := by
      exact_mod_cast hindHNat
    nlinarith only [hindH', hindRaw, halphaExp, hLR.le,
      mul_le_mul_of_nonneg_left halphaExp hLR.le]
  have hBbound : (B : ℝ) ≤ (L : ℝ) / K ^ 22 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < K ^ 22)).2
    simpa [mul_comm] using hBK22leL
  have hindError : (H.indepNum : ℝ) ≤ 2 * (L : ℝ) *
      (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) := by
    calc
      (H.indepNum : ℝ) ≤ 2 * ((L : ℝ) * Real.exp (-(K : ℝ)) + B) + t := hindH
      _ ≤ 2 * ((L : ℝ) * Real.exp (-(K : ℝ)) + L / K ^ 22) +
          100 * L / K := by
            rw [htEq]
            gcongr
      _ = 2 * (L : ℝ) *
          (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) := by ring
  have hcardLowerR : 2 * (L : ℝ) ≤
      (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) := by
    rw [hcardH]
    push_cast
    have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith only [hMlowerR, htR]
  have hindSmall : 4 * (H.indepNum : ℝ) <
      ε * (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) := by
    have hεnonneg := hε.le
    have herrorLt : 2 * (L : ℝ) *
        (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) < ε * (L : ℝ) / 2 := by
      have hscale : (0 : ℝ) < 2 * (L : ℝ) := by positivity
      have H := mul_lt_mul_of_pos_left hKerr hscale
      nlinarith only [H]
    have hright := mul_le_mul_of_nonneg_left hcardLowerR hεnonneg
    nlinarith only [hindError, herrorLt, hright]
  exact ⟨⟨_, instH, H, hcardHpos, hfreeH, hindSmall, hedgeStrictNat⟩⟩

/-! ## Strict seed implies witnesses at every sufficiently large order -/

lemma strict_surplus_absorbs_padding {m E q r : ℕ} (hm : 0 < m)
    (hseed : m ^ 2 < 8 * E) (hr : r < m) (hq : 3 * m ^ 2 ≤ q) :
    (q * m + r) ^ 2 ≤ 8 * (q ^ 2 * E) := by
  have hseed' : m ^ 2 + 1 ≤ 8 * E := by omega
  have hq1 : 1 ≤ q := by nlinarith [sq_pos_of_pos (show (0 : ℝ) < m by exact_mod_cast hm)]
  have hrle : r ≤ m := Nat.le_of_lt hr
  have htwo : 2 * q * m * r ≤ 2 * q * m * m := by gcongr
  have hrsq : r ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hrle 2
  have hmtoq : m ^ 2 ≤ q * m ^ 2 := by
    calc
      m ^ 2 = 1 * m ^ 2 := by simp
      _ ≤ q * m ^ 2 := Nat.mul_le_mul_right _ hq1
  have hqbig : 3 * q * m ^ 2 ≤ q ^ 2 := by
    have H := Nat.mul_le_mul_left q hq
    nlinarith only [H]
  have hroom : 2 * q * m * r + r ^ 2 ≤ q ^ 2 := by
    nlinarith only [htwo, hrsq, hmtoq, hqbig]
  have hscaled := Nat.mul_le_mul_left (q ^ 2) hseed'
  nlinarith only [hroom, hscaled]

lemma eventual_graphs (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  rcases exists_strictSeed ε hε with ⟨S⟩
  letI : Fintype S.Vertex := S.fintypeVertex
  let m : ℕ := Fintype.card S.Vertex
  have hm : 0 < m := S.card_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (m : ℝ) / ε)
  refine Filter.eventually_atTop.2 ⟨max (3 * m ^ 3) N, ?_⟩
  intro n hn
  have hnCube : 3 * m ^ 3 ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  let q : ℕ := n / m
  let r : ℕ := n % m
  have hr : r < m := Nat.mod_lt n hm
  have hq : 3 * m ^ 2 ≤ q := by
    apply (Nat.le_div_iff_mul_le hm).2
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnCube
  have hqpos : 0 < q := by
    have hleft : 0 < 3 * m ^ 2 := by positivity
    omega
  have hdecomp : q * m + r = n := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod n m
  let A := (S.Vertex × Fin q) ⊕ Fin r
  let P : SimpleGraph A := paddedBlowup S.graph q r
  let instA : Fintype A := inferInstance
  have hcardA : @Fintype.card A instA = n := by
    simp only [A, instA, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    change m * q + r = n
    simpa [Nat.mul_comm] using hdecomp
  let e : A ≃ Fin n := Fintype.equivFinOfCardEq hcardA
  let Gfin : SimpleGraph (Fin n) := P.map e.toEmbedding
  letI : DecidableRel Gfin.Adj := fun _ _ ↦ Classical.propDecidable _
  have hnpos : 0 < n := by
    rw [← hdecomp]
    positivity
  letI : Nonempty A := Fintype.card_pos_iff.mp (by simpa [hcardA] using hnpos)
  have hfreeP : P.CliqueFree 4 := paddedBlowup_cliqueFree_four S.graph q r S.cliqueFree
  have hfreeFin : Gfin.CliqueFree 4 := by
    simpa [Gfin] using
      (SimpleGraph.cliqueFree_map_iff (G := P) (f := e.toEmbedding)).2 hfreeP
  have hIndEq : Gfin.indepNum = P.indepNum := by
    simpa [Gfin] using Erdos615.indepNum_map_equiv P e
  have hIndNat : P.indepNum ≤ q * S.graph.indepNum + r :=
    paddedBlowup_indepNum_le S.graph q r
  have hIndCast : (P.indepNum : ℝ) ≤
      (q : ℝ) * S.graph.indepNum + r := by exact_mod_cast hIndNat
  have hseedScaled : 4 * (q : ℝ) * S.graph.indepNum <
      (q : ℝ) * ε * m := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have H := mul_lt_mul_of_pos_left S.indep_small hqR
    nlinarith only [H]
  have hmSmall : (m : ℝ) ≤ ε * n / 2 := by
    have hNcast : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have hmul : 2 * (m : ℝ) < (N : ℝ) * ε := by
      exact (div_lt_iff₀ hε).mp hN
    nlinarith only [hmul, hNcast, hε]
  have hrSmall : (r : ℝ) ≤ ε * n / 2 := by
    have hrR : (r : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt hr)
    exact hrR.trans hmSmall
  have hdecompR : (q : ℝ) * m + r = n := by exact_mod_cast hdecomp
  have hIndFin : (Gfin.indepNum : ℝ) ≤ ε * n := by
    rw [hIndEq]
    nlinarith only [hIndCast, hseedScaled, hrSmall, hdecompR, hε]
  have hEdgeP : Nat.card P.edgeSet = q ^ 2 * Nat.card S.graph.edgeSet :=
    paddedBlowup_edgeCard S.graph q r
  have hEdgeNat : n ^ 2 ≤ 8 * Nat.card P.edgeSet := by
    rw [hEdgeP, ← hdecomp]
    exact strict_surplus_absorbs_padding hm S.edge_strict hr hq
  have hEdgeEq : Gfin.edgeFinset.card = Nat.card P.edgeSet := by
    calc
      Gfin.edgeFinset.card = P.edgeFinset.card := by
        simpa [Gfin] using (SimpleGraph.Iso.map e P).card_edgeFinset_eq.symm
      _ = Fintype.card P.edgeSet := P.edgeFinset_card
      _ = Nat.card P.edgeSet := Nat.card_eq_fintype_card.symm
  have hEdgeFin : (n : ℝ) ^ 2 / 8 ≤ Gfin.edgeFinset.card := by
    rw [hEdgeEq]
    have H : (n : ℝ) ^ 2 ≤ 8 * (Nat.card P.edgeSet : ℝ) := by exact_mod_cast hEdgeNat
    nlinarith only [H]
  exact ⟨Gfin, hfreeFin, hIndFin, hEdgeFin⟩

theorem erdos_22 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  constructor
  · intro _ ε hε
    exact eventual_graphs ε hε
  · intro _
    trivial

#print axioms erdos_22

end Erdos22
