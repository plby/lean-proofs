/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos136.Definitions

namespace Erdos136

open Finset

section FiniteImage

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Two independent collisions in a six-element domain leave at most four
values.  We keep this elementary cardinal lemma separate from the graph
argument below. -/
private lemma card_image_le_four_of_two_collisions
    (s : Finset α) (f : α → β) (hs : #s = 6)
    {a b c d : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) (hbd : b ≠ d)
    (h₁ : f a = f b) (h₂ : f c = f d) : #(s.image f) ≤ 4 := by
  let t := (s.erase b).erase d
  have hsub : s.image f ⊆ t.image f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    by_cases hxb : x = b
    · subst x
      refine mem_image.mpr ⟨a, ?_, h₁⟩
      simp [t, ha, hab, had]
    by_cases hxd : x = d
    · subst x
      refine mem_image.mpr ⟨c, ?_, h₂⟩
      simp [t, hc, hcb, hcd]
    exact mem_image.mpr ⟨x, by simp [t, hx, hxb, hxd], rfl⟩
  calc
    #(s.image f) ≤ #(t.image f) := card_le_card hsub
    _ ≤ #t := card_image_le
    _ = 4 := by
      rw [show t = (s.erase b).erase d from rfl,
        card_erase_of_mem (by simp [hd, hbd.symm]), card_erase_of_mem hb, hs]

/-- Three occurrences of one value in a six-element domain also leave at
most four values. -/
private lemma card_image_le_four_of_three_equal
    (s : Finset α) (f : α → β) (hs : #s = 6)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : f a = f b) (h₂ : f a = f c) : #(s.image f) ≤ 4 := by
  let t := (s.erase b).erase c
  have hsub : s.image f ⊆ t.image f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    by_cases hxb : x = b
    · subst x
      refine mem_image.mpr ⟨a, ?_, h₁⟩
      simp [t, ha, hab, hac]
    by_cases hxc : x = c
    · subst x
      refine mem_image.mpr ⟨a, ?_, h₂⟩
      simp [t, ha, hab, hac]
    exact mem_image.mpr ⟨x, by simp [t, hx, hxb, hxc], rfl⟩
  calc
    #(s.image f) ≤ #(t.image f) := card_le_card hsub
    _ ≤ #t := card_image_le
    _ = 4 := by
      rw [show t = (s.erase b).erase c from rfl,
        card_erase_of_mem (by simp [hc, hbc.symm]), card_erase_of_mem hb, hs]

end FiniteImage

section LocalObstructions

variable {n k : ℕ} {C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)}

/-- In a valid colouring, three different edges of one embedded `K₄`
cannot have the same colour. -/
private lemma Is45Coloring.not_three_equal (hC : Is45Coloring C)
    (v : Fin 4 ↪ Fin n)
    (a b c : (⊤ : SimpleGraph (Fin 4)).edgeSet)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : C.pullback v a = C.pullback v b)
    (h₂ : C.pullback v a = C.pullback v c) : False := by
  have hlo : #(Finset.univ.image (C.pullback v)) ≤ 4 :=
    card_image_le_four_of_three_equal Finset.univ (C.pullback v) (by
      rw [SimpleGraph.edgeSet_univ_card,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      decide)
      (by simp) (by simp) (by simp) hab hac hbc h₁ h₂
  exact (not_le_of_gt (hC v)) hlo

/-- Nor can two different pairs of edges of one embedded `K₄` repeat
colours (the two repeated colours are allowed to coincide). -/
private lemma Is45Coloring.not_two_pairs (hC : Is45Coloring C)
    (v : Fin 4 ↪ Fin n)
    (a b c d : (⊤ : SimpleGraph (Fin 4)).edgeSet)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) (hbd : b ≠ d)
    (h₁ : C.pullback v a = C.pullback v b)
    (h₂ : C.pullback v c = C.pullback v d) : False := by
  have hlo : #(Finset.univ.image (C.pullback v)) ≤ 4 :=
    card_image_le_four_of_two_collisions Finset.univ (C.pullback v) (by
      rw [SimpleGraph.edgeSet_univ_card,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      decide)
      (by simp) (by simp) (by simp) (by simp) hab had hcb hcd hbd h₁ h₂
  exact (not_le_of_gt (hC v)) hlo

end LocalObstructions

section ConcreteObstructions

variable {n k : ℕ} {C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)}

private def topEdge {m : ℕ} (x y : Fin m) (h : x ≠ y) :
    (⊤ : SimpleGraph (Fin m)).edgeSet :=
  ⟨s(x, y), by simpa using h⟩

private lemma topEdge_comm {m : ℕ} (x y : Fin m) (h : x ≠ y) :
    topEdge x y h = topEdge y x h.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- Four pairwise distinct vertices, packaged as an embedding of `Fin 4`. -/
private def quadEmbedding (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Fin n where
  toFun := ![a, b, c, d]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma pullback_topEdge (D : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k))
    {m : ℕ} (f : Fin m ↪ Fin n) (i j : Fin m) (hij : i ≠ j) :
    (D.pullback f) (topEdge i j hij) =
      D (topEdge (f i) (f j) (f.injective.ne hij)) := by
  rfl

/-- A monochromatic three-edge star is forbidden on four vertices. -/
private lemma Is45Coloring.no_three_star (hC : Is45Coloring C)
    (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : C (topEdge x a hxa) = C (topEdge x b hxb))
    (h₂ : C (topEdge x a hxa) = C (topEdge x c hxc)) : False := by
  let v := quadEmbedding x a b c hxa hxb hxc hab hac hbc
  let e₁ := topEdge (0 : Fin 4) (1 : Fin 4) (by decide)
  let e₂ := topEdge (0 : Fin 4) (2 : Fin 4) (by decide)
  let e₃ := topEdge (0 : Fin 4) (3 : Fin 4) (by decide)
  have he₁ : C.pullback v e₁ = C (topEdge x a hxa) := by
    rw [show C.pullback v e₁ = C (topEdge (v 0) (v 1) (v.injective.ne (by decide))) by
      simpa [e₁] using (pullback_topEdge C v (0 : Fin 4) (1 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  have he₂ : C.pullback v e₂ = C (topEdge x b hxb) := by
    rw [show C.pullback v e₂ = C (topEdge (v 0) (v 2) (v.injective.ne (by decide))) by
      simpa [e₂] using (pullback_topEdge C v (0 : Fin 4) (2 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  have he₃ : C.pullback v e₃ = C (topEdge x c hxc) := by
    rw [show C.pullback v e₃ = C (topEdge (v 0) (v 3) (v.injective.ne (by decide))) by
      simpa [e₃] using (pullback_topEdge C v (0 : Fin 4) (3 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  apply hC.not_three_equal v e₁ e₂ e₃ (by decide) (by decide) (by decide)
  · rw [he₁, he₂]
    exact h₁
  · rw [he₁, he₃]
    exact h₂

/-- A monochromatic triangle is forbidden once a fourth vertex exists. -/
private lemma Is45Coloring.no_triangle (hC : Is45Coloring C)
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : C (topEdge a b hab) = C (topEdge a c hac))
    (h₂ : C (topEdge a b hab) = C (topEdge b c hbc)) : False := by
  let v := quadEmbedding a b c d hab hac had hbc hbd hcd
  let e₁ := topEdge (0 : Fin 4) (1 : Fin 4) (by decide)
  let e₂ := topEdge (0 : Fin 4) (2 : Fin 4) (by decide)
  let e₃ := topEdge (1 : Fin 4) (2 : Fin 4) (by decide)
  have he₁ : C.pullback v e₁ = C (topEdge a b hab) := by
    rw [show C.pullback v e₁ = C (topEdge (v 0) (v 1) (v.injective.ne (by decide))) by
      simpa [e₁] using (pullback_topEdge C v (0 : Fin 4) (1 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  have he₂ : C.pullback v e₂ = C (topEdge a c hac) := by
    rw [show C.pullback v e₂ = C (topEdge (v 0) (v 2) (v.injective.ne (by decide))) by
      simpa [e₂] using (pullback_topEdge C v (0 : Fin 4) (2 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  have he₃ : C.pullback v e₃ = C (topEdge b c hbc) := by
    rw [show C.pullback v e₃ = C (topEdge (v 1) (v 2) (v.injective.ne (by decide))) by
      simpa [e₃] using (pullback_topEdge C v (1 : Fin 4) (2 : Fin 4) (by decide))]
    apply congrArg C
    apply Subtype.ext
    rfl
  apply hC.not_three_equal v e₁ e₂ e₃ (by decide) (by decide) (by decide)
  · rw [he₁, he₂]
    exact h₁
  · rw [he₁, he₃]
    exact h₂

/-- A monochromatic path of length three is forbidden. -/
private lemma Is45Coloring.no_three_path (hC : Is45Coloring C)
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : C (topEdge a b hab) = C (topEdge b c hbc))
    (h₂ : C (topEdge a b hab) = C (topEdge c d hcd)) : False := by
  let v := quadEmbedding a b c d hab hac had hbc hbd hcd
  let e₁ := topEdge (0 : Fin 4) (1 : Fin 4) (by decide)
  let e₂ := topEdge (1 : Fin 4) (2 : Fin 4) (by decide)
  let e₃ := topEdge (2 : Fin 4) (3 : Fin 4) (by decide)
  have he₁ : C.pullback v e₁ = C (topEdge a b hab) := by
    rw [show C.pullback v e₁ = C (topEdge (v 0) (v 1) (v.injective.ne (by decide))) by
      simpa [e₁] using (pullback_topEdge C v (0 : Fin 4) (1 : Fin 4) (by decide))]
    apply congrArg C; apply Subtype.ext; rfl
  have he₂ : C.pullback v e₂ = C (topEdge b c hbc) := by
    rw [show C.pullback v e₂ = C (topEdge (v 1) (v 2) (v.injective.ne (by decide))) by
      simpa [e₂] using (pullback_topEdge C v (1 : Fin 4) (2 : Fin 4) (by decide))]
    apply congrArg C; apply Subtype.ext; rfl
  have he₃ : C.pullback v e₃ = C (topEdge c d hcd) := by
    rw [show C.pullback v e₃ = C (topEdge (v 2) (v 3) (v.injective.ne (by decide))) by
      simpa [e₃] using (pullback_topEdge C v (2 : Fin 4) (3 : Fin 4) (by decide))]
    apply congrArg C; apply Subtype.ext; rfl
  apply hC.not_three_equal v e₁ e₂ e₃ (by decide) (by decide) (by decide)
  · rw [he₁, he₂]; exact h₁
  · rw [he₁, he₃]; exact h₂

/-- The two repeated pairs used to prove that a closing chord is isolated. -/
private lemma Is45Coloring.no_wedge_and_chord_fan (hC : Is45Coloring C)
    (v a b x : Fin n) (hva : v ≠ a) (hvb : v ≠ b) (hvx : v ≠ x)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (h₁ : C (topEdge v a hva) = C (topEdge v b hvb))
    (h₂ : C (topEdge a b hab) = C (topEdge a x hax)) : False := by
  let q := quadEmbedding v a b x hva hvb hvx hab hax hbx
  let e₁ := topEdge (0 : Fin 4) (1 : Fin 4) (by decide)
  let e₂ := topEdge (0 : Fin 4) (2 : Fin 4) (by decide)
  let e₃ := topEdge (1 : Fin 4) (2 : Fin 4) (by decide)
  let e₄ := topEdge (1 : Fin 4) (3 : Fin 4) (by decide)
  have hmap (i j : Fin 4) (hij : i ≠ j) :
      C.pullback q (topEdge i j hij) = C (topEdge (q i) (q j) (q.injective.ne hij)) :=
    pullback_topEdge C q i j hij
  have hq₁ : C.pullback q e₁ = C (topEdge v a hva) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₂ : C.pullback q e₂ = C (topEdge v b hvb) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₃ : C.pullback q e₃ = C (topEdge a b hab) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₄ : C.pullback q e₄ = C (topEdge a x hax) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  apply hC.not_two_pairs q e₁ e₂ e₃ e₄ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  · rw [hq₁, hq₂]; exact h₁
  · rw [hq₃, hq₄]; exact h₂

/-- Two different monochromatic wedges cannot have the same two endpoints. -/
private lemma Is45Coloring.no_two_wedges_same_ends (hC : Is45Coloring C)
    (a b v w : Fin n) (hab : a ≠ b) (hav : a ≠ v) (haw : a ≠ w)
    (hbv : b ≠ v) (hbw : b ≠ w) (hvw : v ≠ w)
    (h₁ : C (topEdge a v hav) = C (topEdge b v hbv))
    (h₂ : C (topEdge a w haw) = C (topEdge b w hbw)) : False := by
  let q := quadEmbedding a b v w hab hav haw hbv hbw hvw
  let e₁ := topEdge (0 : Fin 4) (2 : Fin 4) (by decide)
  let e₂ := topEdge (1 : Fin 4) (2 : Fin 4) (by decide)
  let e₃ := topEdge (0 : Fin 4) (3 : Fin 4) (by decide)
  let e₄ := topEdge (1 : Fin 4) (3 : Fin 4) (by decide)
  have hmap (i j : Fin 4) (hij : i ≠ j) :
      C.pullback q (topEdge i j hij) = C (topEdge (q i) (q j) (q.injective.ne hij)) :=
    pullback_topEdge C q i j hij
  have hq₁ : C.pullback q e₁ = C (topEdge a v hav) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₂ : C.pullback q e₂ = C (topEdge b v hbv) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₃ : C.pullback q e₃ = C (topEdge a w haw) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  have hq₄ : C.pullback q e₄ = C (topEdge b w hbw) := by
    rw [hmap]; apply congrArg C; apply Subtype.ext; rfl
  apply hC.not_two_pairs q e₁ e₂ e₃ e₄ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  · rw [hq₁, hq₂]; exact h₁
  · rw [hq₃, hq₄]; exact h₂

end ConcreteObstructions

section ColourGraphs

variable {n k : ℕ} {C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)}

/-- Every vertex has degree at most two in any one colour graph. -/
private lemma Is45Coloring.labelGraph_degree_le_two (hC : Is45Coloring C)
    (q : Fin k) (x : Fin n) : (C.labelGraph q).degree x ≤ 2 := by
  by_contra hle
  have hthree : 3 ≤ (C.labelGraph q).degree x := by omega
  let f : Fin 3 ↪ (C.labelGraph q).neighborSet x :=
    (Function.Embedding.nonempty_of_card_le (by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hthree)).some
  let a : Fin n := (f 0).1
  let b : Fin n := (f 1).1
  let c : Fin n := (f 2).1
  have hxaG : (C.labelGraph q).Adj x a := (f 0).2
  have hxbG : (C.labelGraph q).Adj x b := (f 1).2
  have hxcG : (C.labelGraph q).Adj x c := (f 2).2
  have hxa : x ≠ a := hxaG.ne
  have hxb : x ≠ b := hxbG.ne
  have hxc : x ≠ c := hxcG.ne
  have hab : a ≠ b := by
    intro heq
    exact f.injective.ne (show (0 : Fin 3) ≠ 1 by decide) (Subtype.ext heq)
  have hac : a ≠ c := by
    intro heq
    exact f.injective.ne (show (0 : Fin 3) ≠ 2 by decide) (Subtype.ext heq)
  have hbc : b ≠ c := by
    intro heq
    exact f.injective.ne (show (1 : Fin 3) ≠ 2 by decide) (Subtype.ext heq)
  obtain ⟨_, hqa⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x a).mp hxaG
  obtain ⟨_, hqb⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x b).mp hxbG
  obtain ⟨_, hqc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x c).mp hxcG
  apply hC.no_three_star x a b c hxa hxb hxc hab hac hbc
  · exact hqa.trans hqb.symm
  · exact hqa.trans hqc.symm

/-- Centres at which one colour occurs on exactly two incident edges. -/
private abbrev DoubleCenter (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) :=
  {p : Fin k × Fin n // (C.labelGraph p.1).degree p.2 = 2}

namespace DoubleCenter

variable (h : DoubleCenter C)

private noncomputable def chosenEnds
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (h : DoubleCenter C) : Fin n × Fin n :=
  let hx : ∃ x y, x ≠ y ∧
      (C.labelGraph h.1.1).neighborFinset h.1.2 = {x, y} :=
    Finset.card_eq_two.mp h.2
  ⟨hx.choose, hx.choose_spec.choose⟩

private lemma chosenEnds_spec : (chosenEnds C h).1 ≠ (chosenEnds C h).2 ∧
    (C.labelGraph h.1.1).neighborFinset h.1.2 =
      {(chosenEnds C h).1, (chosenEnds C h).2} :=
  by
    let hx : ∃ x y, x ≠ y ∧
        (C.labelGraph h.1.1).neighborFinset h.1.2 = {x, y} :=
      Finset.card_eq_two.mp h.2
    simpa [chosenEnds, hx] using hx.choose_spec.choose_spec

private lemma left_ne_right : (chosenEnds C h).1 ≠ (chosenEnds C h).2 :=
  (chosenEnds_spec h).1

private lemma adj_left : (C.labelGraph h.1.1).Adj h.1.2 (chosenEnds C h).1 := by
  rw [← SimpleGraph.mem_neighborFinset]
  rw [(chosenEnds_spec h).2]
  simp

private lemma adj_right : (C.labelGraph h.1.1).Adj h.1.2 (chosenEnds C h).2 := by
  rw [← SimpleGraph.mem_neighborFinset]
  rw [(chosenEnds_spec h).2]
  simp

private lemma color_left :
    C (topEdge h.1.2 (chosenEnds C h).1 (adj_left h).ne) = h.1.1 := by
  obtain ⟨H, hH⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj _ _).mp (adj_left h)
  simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hH

private lemma color_right :
    C (topEdge h.1.2 (chosenEnds C h).2 (adj_right h).ne) = h.1.1 := by
  obtain ⟨H, hH⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj _ _).mp (adj_right h)
  simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hH

private lemma neighbor_eq_left_or_right {u : Fin n}
    (hu : (C.labelGraph h.1.1).Adj h.1.2 u) :
    u = (chosenEnds C h).1 ∨ u = (chosenEnds C h).2 := by
  have : u ∈ (C.labelGraph h.1.1).neighborFinset h.1.2 := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hu
  rw [(chosenEnds_spec h).2] at this
  simpa [eq_comm] using this

end DoubleCenter

/-- A degree-two vertex has, besides any specified neighbor, another one. -/
private lemma exists_other_neighbor {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {x y : Fin n}
    (hdeg : G.degree x = 2) (_hxy : G.Adj x y) :
    ∃ z, G.Adj x z ∧ z ≠ y := by
  have hcard : 1 < #(G.neighborFinset x) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  by_cases hay : a = y
  · exact ⟨b, by simpa using hb, by simpa [hay] using hab.symm⟩
  · exact ⟨a, by simpa using ha, hay⟩

private lemma exists_fourth_vertex (hn : 4 ≤ n) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : Fin n, a ≠ d ∧ b ≠ d ∧ c ≠ d := by
  by_contra hex
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d hd
    have hm : d = a ∨ d = b ∨ d = c := by
      by_contra hm
      simp only [not_or] at hm
      exact hex ⟨d, Ne.symm hm.1, Ne.symm hm.2.1, Ne.symm hm.2.2⟩
    rcases hm with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  have hcard := Finset.card_le_card hsub
  have hrhs : #({a, b, c} : Finset (Fin n)) = 3 := by simp [hab, hac, hbc]
  simp only [Finset.card_univ, Fintype.card_fin, hrhs] at hcard
  omega

/-- An edge in one colour graph cannot have degree two at both endpoints. -/
private lemma Is45Coloring.not_degree_two_at_both_ends (hC : Is45Coloring C)
    (hn : 4 ≤ n) (q : Fin k) {x y : Fin n}
    (hxy : (C.labelGraph q).Adj x y)
    (hx : (C.labelGraph q).degree x = 2)
    (hy : (C.labelGraph q).degree y = 2) : False := by
  obtain ⟨a, hxa, hay⟩ := exists_other_neighbor hx hxy
  obtain ⟨b, hyb, hbx⟩ := exists_other_neighbor hy hxy.symm
  have hxy_ne : x ≠ y := hxy.ne
  have hxa_ne : x ≠ a := hxa.ne
  have hyb_ne : y ≠ b := hyb.ne
  obtain ⟨_, hqxy⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hxy
  obtain ⟨_, hqxa⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x a).mp hxa
  obtain ⟨_, hqyb⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj y b).mp hyb
  by_cases hab : a = b
  · subst b
    obtain ⟨d, hxd, hyd, had⟩ := exists_fourth_vertex hn hxy_ne hxa_ne hay.symm
    apply hC.no_triangle x y a d hxy_ne hxa_ne hxd hay.symm hyd had
    · exact hqxy.trans hqxa.symm
    · exact hqxy.trans hqyb.symm
  · apply hC.no_three_path a x y b hxa_ne.symm hay hab hxy_ne hbx.symm hyb_ne
    · rw [topEdge_comm a x]
      simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hqxa.trans hqxy.symm
    · rw [topEdge_comm a x]
      simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hqxa.trans hqyb.symm

end ColourGraphs

section MateInjection

variable {n k : ℕ} {C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)}

private abbrev WedgeLeg (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) :=
  Σ h : DoubleCenter C, (C.labelGraph h.1.1).neighborSet h.1.2

private noncomputable def chordEdge (h : DoubleCenter C) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  topEdge (DoubleCenter.chosenEnds C h).1 (DoubleCenter.chosenEnds C h).2
    (DoubleCenter.left_ne_right h)

private def legEdge (z : WedgeLeg C) : (⊤ : SimpleGraph (Fin n)).edgeSet :=
  topEdge z.1.1.2 z.2.1
    (show z.1.1.2 ≠ z.2.1 from
      (show (C.labelGraph z.1.1.1).Adj z.1.1.2 z.2.1 from z.2.2).ne)

private lemma legEdge_color (z : WedgeLeg C) : C (legEdge z) = z.1.1.1 := by
  obtain ⟨H, hH⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj _ _).mp z.2.2
  simpa [legEdge, topEdge, SimpleGraph.EdgeLabeling.get] using hH

private lemma card_wedgeLeg : Fintype.card (WedgeLeg C) = 2 * Fintype.card (DoubleCenter C) := by
  rw [Fintype.card_sigma]
  simp_rw [SimpleGraph.card_neighborSet_eq_degree]
  calc
    ∑ h : DoubleCenter C, (C.labelGraph h.1.1).degree h.1.2 =
        ∑ _h : DoubleCenter C, 2 := by
      apply Finset.sum_congr rfl
      intro h _
      exact h.2
    _ = 2 * Fintype.card (DoubleCenter C) := by simp [mul_comm]

/-- The two legs, globally, map injectively to complete-graph edges.  The
only possible failure would make both endpoints degree two in one colour. -/
private lemma legEdge_injective (hC : Is45Coloring C) (hn : 4 ≤ n) :
    Function.Injective (legEdge : WedgeLeg C → (⊤ : SimpleGraph (Fin n)).edgeSet) := by
  intro z z' he
  have hs := congrArg Subtype.val he
  change s(z.1.1.2, z.2.1) = s(z'.1.1.2, z'.2.1) at hs
  rcases Sym2.eq_iff.mp hs with hdir | hswap
  · have hv : z.1.1.2 = z'.1.1.2 := hdir.1
    have hu : z.2.1 = z'.2.1 := hdir.2
    have hq : z.1.1.1 = z'.1.1.1 := by
      rw [← legEdge_color z, ← legEdge_color z', he]
    have hz : z.1 = z'.1 := by
      apply Subtype.ext
      exact Prod.ext hq hv
    rcases z with ⟨h, u⟩
    rcases z' with ⟨h', u'⟩
    dsimp at hz hu ⊢
    subst h'
    congr
    exact Subtype.ext hu
  · have hvu : z.1.1.2 = z'.2.1 := hswap.1
    have huv : z.2.1 = z'.1.1.2 := hswap.2
    have hq : z.1.1.1 = z'.1.1.1 := by
      rw [← legEdge_color z, ← legEdge_color z', he]
    exfalso
    have hadj : (C.labelGraph z.1.1.1).Adj z.1.1.2 z.2.1 := z.2.2
    apply hC.not_degree_two_at_both_ends hn z.1.1.1 hadj z.1.2
    have hdeg' : (C.labelGraph z'.1.1.1).degree z'.1.1.2 = 2 := z'.1.2
    have hp : (z.1.1.1, z.2.1) = (z'.1.1.1, z'.1.1.2) := Prod.ext hq huv
    exact (congrArg (fun p : Fin k × Fin n ↦ (C.labelGraph p.1).degree p.2) hp).trans hdeg'

/-- Distinct monochromatic wedges have distinct closing chords. -/
private lemma chordEdge_injective (hC : Is45Coloring C) :
    Function.Injective (chordEdge : DoubleCenter C → (⊤ : SimpleGraph (Fin n)).edgeSet) := by
  intro h g he
  let a := (DoubleCenter.chosenEnds C h).1
  let b := (DoubleCenter.chosenEnds C h).2
  let a' := (DoubleCenter.chosenEnds C g).1
  let b' := (DoubleCenter.chosenEnds C g).2
  let v := h.1.2
  let w := g.1.2
  have hs := congrArg Subtype.val he
  change s(a, b) = s(a', b') at hs
  rcases Sym2.eq_iff.mp hs with hdir | hswap
  · by_cases hvw : v = w
    · have hedge : topEdge v a (DoubleCenter.adj_left h).ne =
          topEdge w a' (DoubleCenter.adj_left g).ne := by
        apply Subtype.ext
        simp only [topEdge]
        rw [hvw, hdir.1]
      have hq : h.1.1 = g.1.1 :=
        (DoubleCenter.color_left h).symm.trans
          ((congrArg C hedge).trans (DoubleCenter.color_left g))
      apply Subtype.ext
      exact Prod.ext hq hvw
    · have hab : a ≠ b := DoubleCenter.left_ne_right h
      have hav : a ≠ v := (DoubleCenter.adj_left h).ne.symm
      have hbv : b ≠ v := (DoubleCenter.adj_right h).ne.symm
      have hwa : w ≠ a := by simpa [hdir.1] using (DoubleCenter.adj_left g).ne
      have hwb : w ≠ b := by simpa [hdir.2] using (DoubleCenter.adj_right g).ne
      have h₁ : C (topEdge a v hav) = C (topEdge b v hbv) := by
        rw [topEdge_comm a v, topEdge_comm b v]
        exact (DoubleCenter.color_left h).trans (DoubleCenter.color_right h).symm
      have hga : C (topEdge w a hwa) = g.1.1 := by
        simpa [hdir.1, topEdge] using DoubleCenter.color_left g
      have hgb : C (topEdge w b hwb) = g.1.1 := by
        simpa [hdir.2, topEdge] using DoubleCenter.color_right g
      have h₂ : C (topEdge a w hwa.symm) = C (topEdge b w hwb.symm) := by
        rw [topEdge_comm a w, topEdge_comm b w]
        exact hga.trans hgb.symm
      exact (hC.no_two_wedges_same_ends a b v w hab hav hwa.symm hbv hwb.symm hvw h₁ h₂).elim
  · by_cases hvw : v = w
    · have hedge : topEdge v a (DoubleCenter.adj_left h).ne =
          topEdge w b' (DoubleCenter.adj_right g).ne := by
        apply Subtype.ext
        simp only [topEdge]
        rw [hvw, hswap.1]
      have hq : h.1.1 = g.1.1 :=
        (DoubleCenter.color_left h).symm.trans
          ((congrArg C hedge).trans (DoubleCenter.color_right g))
      apply Subtype.ext
      exact Prod.ext hq hvw
    · have hab : a ≠ b := DoubleCenter.left_ne_right h
      have hav : a ≠ v := (DoubleCenter.adj_left h).ne.symm
      have hbv : b ≠ v := (DoubleCenter.adj_right h).ne.symm
      have hwa : w ≠ a := by simpa [hswap.1] using (DoubleCenter.adj_right g).ne
      have hwb : w ≠ b := by simpa [hswap.2] using (DoubleCenter.adj_left g).ne
      have h₁ : C (topEdge a v hav) = C (topEdge b v hbv) := by
        rw [topEdge_comm a v, topEdge_comm b v]
        exact (DoubleCenter.color_left h).trans (DoubleCenter.color_right h).symm
      have hga : C (topEdge w a hwa) = g.1.1 := by
        simpa [hswap.1, topEdge] using DoubleCenter.color_right g
      have hgb : C (topEdge w b hwb) = g.1.1 := by
        simpa [hswap.2, topEdge] using DoubleCenter.color_left g
      have h₂ : C (topEdge a w hwa.symm) = C (topEdge b w hwb.symm) := by
        rw [topEdge_comm a w, topEdge_comm b w]
        exact hga.trans hgb.symm
      exact (hC.no_two_wedges_same_ends a b v w hab hav hwa.symm hbv hwb.symm hvw h₁ h₂).elim

private lemma chordEdge_color_ne (hC : Is45Coloring C) (hn : 4 ≤ n)
    (h : DoubleCenter C) : C (chordEdge h) ≠ h.1.1 := by
  intro heq
  let a := (DoubleCenter.chosenEnds C h).1
  let b := (DoubleCenter.chosenEnds C h).2
  let v := h.1.2
  have hvab : v ≠ a := (DoubleCenter.adj_left h).ne
  have hvbb : v ≠ b := (DoubleCenter.adj_right h).ne
  have hab : a ≠ b := DoubleCenter.left_ne_right h
  obtain ⟨d, hvd, had, hbd⟩ := exists_fourth_vertex hn hvab hvbb hab
  apply hC.no_triangle v a b d hvab hvbb hvd hab had hbd
  · exact (DoubleCenter.color_left h).trans (DoubleCenter.color_right h).symm
  · exact (DoubleCenter.color_left h).trans heq.symm

/-- A closing chord is never one of the globally counted legs. -/
private lemma chordEdge_ne_legEdge (hC : Is45Coloring C) (hn : 4 ≤ n)
    (h : DoubleCenter C) (z : WedgeLeg C) : chordEdge h ≠ legEdge z := by
  intro he
  let a := (DoubleCenter.chosenEnds C h).1
  let b := (DoubleCenter.chosenEnds C h).2
  let v := h.1.2
  let w := z.1.1.2
  let u := z.2.1
  have hs := congrArg Subtype.val he
  change s(a, b) = s(w, u) at hs
  have hchord : C (chordEdge h) = z.1.1.1 :=
    (congrArg C he).trans (legEdge_color (C := C) z)
  have hwudeg : (C.labelGraph z.1.1.1).degree w = 2 := z.1.2
  have hadjwu : (C.labelGraph z.1.1.1).Adj w u := z.2.2
  rcases Sym2.eq_iff.mp hs with hdir | hswap
  · have hwa : w = a := hdir.1.symm
    have hub : u = b := hdir.2.symm
    obtain ⟨x, hwx, hxu⟩ := exists_other_neighbor hwudeg hadjwu
    have hax : a ≠ x := by simpa [hwa] using hwx.ne
    have hbx : b ≠ x := by simpa [hub] using hxu.symm
    have haxadj : (C.labelGraph z.1.1.1).Adj a x := by
      rw [← hwa]
      exact hwx
    have hcolax : C (topEdge a x hax) = z.1.1.1 := by
      obtain ⟨H, hH⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj a x).mp haxadj
      simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hH
    have hvx : v ≠ x := by
      intro hvx
      have hza : z.1.1.1 = h.1.1 := by
        rw [← hcolax, ← DoubleCenter.color_left h, topEdge_comm a x]
        subst x
        rfl
      have : C (chordEdge h) = h.1.1 := hchord.trans hza
      exact chordEdge_color_ne hC hn h this
    have h₁ : C (topEdge v a (DoubleCenter.adj_left h).ne) =
        C (topEdge v b (DoubleCenter.adj_right h).ne) :=
      (DoubleCenter.color_left h).trans (DoubleCenter.color_right h).symm
    have h₂ : C (topEdge a b (DoubleCenter.left_ne_right h)) = C (topEdge a x hax) := by
      change C (chordEdge h) = C (topEdge a x hax)
      exact hchord.trans hcolax.symm
    exact (hC.no_wedge_and_chord_fan v a b x
      (DoubleCenter.adj_left h).ne (DoubleCenter.adj_right h).ne hvx
      (DoubleCenter.left_ne_right h) hax hbx h₁ h₂).elim
  · have hwb : w = b := hswap.2.symm
    have hua : u = a := hswap.1.symm
    obtain ⟨x, hwx, hxu⟩ := exists_other_neighbor hwudeg hadjwu
    have hbx : b ≠ x := by simpa [hwb] using hwx.ne
    have hax : a ≠ x := by simpa [hua] using hxu.symm
    have hbxadj : (C.labelGraph z.1.1.1).Adj b x := by
      rw [← hwb]
      exact hwx
    have hcolbx : C (topEdge b x hbx) = z.1.1.1 := by
      obtain ⟨H, hH⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj b x).mp hbxadj
      simpa [topEdge, SimpleGraph.EdgeLabeling.get] using hH
    have hvx : v ≠ x := by
      intro hvx
      have hzb : z.1.1.1 = h.1.1 := by
        rw [← hcolbx, ← DoubleCenter.color_right h, topEdge_comm b x]
        subst x
        rfl
      have : C (chordEdge h) = h.1.1 := hchord.trans hzb
      exact chordEdge_color_ne hC hn h this
    have h₁ : C (topEdge v b (DoubleCenter.adj_right h).ne) =
        C (topEdge v a (DoubleCenter.adj_left h).ne) :=
      (DoubleCenter.color_right h).trans (DoubleCenter.color_left h).symm
    have h₂ : C (topEdge b a (DoubleCenter.left_ne_right h).symm) = C (topEdge b x hbx) := by
      rw [← topEdge_comm a b]
      change C (chordEdge h) = C (topEdge b x hbx)
      exact hchord.trans hcolbx.symm
    exact (hC.no_wedge_and_chord_fan v b a x
      (DoubleCenter.adj_right h).ne (DoubleCenter.adj_left h).ne hvx
      (DoubleCenter.left_ne_right h).symm hbx hax h₁ h₂).elim

private noncomputable def mateMap : Sum (DoubleCenter C) (WedgeLeg C) →
    (⊤ : SimpleGraph (Fin n)).edgeSet
  | Sum.inl h => chordEdge h
  | Sum.inr z => legEdge z

private lemma mateMap_injective (hC : Is45Coloring C) (hn : 4 ≤ n) :
    Function.Injective (mateMap : Sum (DoubleCenter C) (WedgeLeg C) →
      (⊤ : SimpleGraph (Fin n)).edgeSet) := by
  intro x y he
  cases x with
  | inl h =>
      cases y with
      | inl g => exact congrArg Sum.inl (chordEdge_injective hC he)
      | inr z => exact (chordEdge_ne_legEdge hC hn h z he).elim
  | inr z =>
      cases y with
      | inl h => exact (chordEdge_ne_legEdge hC hn h z he.symm).elim
      | inr z' => exact congrArg Sum.inr (legEdge_injective hC hn he)

/-- The mate injection: three complete-graph edges can be charged to every
degree-two colour centre. -/
private lemma three_mul_doubleCenter_le_edges (hC : Is45Coloring C) (hn : 4 ≤ n) :
    3 * Fintype.card (DoubleCenter C) ≤ n.choose 2 := by
  have hcard := Fintype.card_le_of_injective mateMap (mateMap_injective hC hn)
  rw [Fintype.card_sum, card_wedgeLeg,
    SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

end MateInjection

section Counting


variable {n k : ℕ} {C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)}

private def colorEdgeEquiv (q : Fin k) :
    (C.labelGraph q).edgeSet ≃ {e : (⊤ : SimpleGraph (Fin n)).edgeSet // C e = q} where
  toFun e := by
    have he : ∃ H : e.1 ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, C ⟨e.1, H⟩ = q := by
      simpa [SimpleGraph.EdgeLabeling.labelGraph] using e.2
    exact ⟨⟨e.1, he.choose⟩, he.choose_spec⟩
  invFun e := ⟨e.1.1, by
    have hnd : ¬e.1.1.IsDiag := by
      simpa [SimpleGraph.edgeSet_top] using e.1.2
    have hraw : (¬e.1.1.IsDiag ∧ C e.1 = q) ∧ ¬e.1.1.IsDiag :=
      ⟨⟨hnd, e.2⟩, hnd⟩
    simpa [SimpleGraph.EdgeLabeling.labelGraph] using hraw⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; rfl

private noncomputable def allColorEdgesEquiv :
    (Σ q : Fin k, {e : (⊤ : SimpleGraph (Fin n)).edgeSet // C e = q}) ≃
      (⊤ : SimpleGraph (Fin n)).edgeSet where
  toFun z := z.2.1
  invFun e := ⟨C e, e, rfl⟩
  left_inv z := by rcases z with ⟨q, e, he⟩; simp only; subst q; rfl
  right_inv e := rfl

private lemma sum_color_edges :
    ∑ q : Fin k, #(C.labelGraph q).edgeFinset = n.choose 2 := by
  classical
  have hcard := Fintype.card_congr (allColorEdgesEquiv (C := C))
  rw [Fintype.card_sigma] at hcard
  calc
    ∑ q : Fin k, #(C.labelGraph q).edgeFinset =
        ∑ q : Fin k, Fintype.card {e : (⊤ : SimpleGraph (Fin n)).edgeSet // C e = q} := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← SimpleGraph.card_edgeSet]
      exact Fintype.card_congr (colorEdgeEquiv q)
    _ = Fintype.card (⊤ : SimpleGraph (Fin n)).edgeSet := hcard
    _ = n.choose 2 := by
      rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

private def doubleCenterSigmaEquiv : DoubleCenter C ≃
    Σ q : Fin k, {v : Fin n // (C.labelGraph q).degree v = 2} where
  toFun h := ⟨h.1.1, h.1.2, h.2⟩
  invFun h := ⟨(h.1, h.2.1), h.2.2⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv h := by rcases h with ⟨q, v, hv⟩; rfl

private lemma card_doubleCenter_eq_sum : Fintype.card (DoubleCenter C) =
    ∑ q : Fin k, #{v : Fin n | (C.labelGraph q).degree v = 2} := by
  rw [Fintype.card_congr (doubleCenterSigmaEquiv (C := C)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fintype.card_subtype]

private lemma degree_indicator (hC : Is45Coloring C) (q : Fin k) (v : Fin n) :
    (C.labelGraph q).degree v =
      (if v ∈ (C.labelGraph q).support then 1 else 0) +
      (if (C.labelGraph q).degree v = 2 then 1 else 0) := by
  have hle := hC.labelGraph_degree_le_two q v
  by_cases hs : v ∈ (C.labelGraph q).support
  · have hp : 0 < (C.labelGraph q).degree v := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact ((SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mp hz) hs
    by_cases htwo : (C.labelGraph q).degree v = 2
    · simp [hs, htwo]
    · have hone : (C.labelGraph q).degree v = 1 := by omega
      simp [hs, hone]
  · have hz : (C.labelGraph q).degree v = 0 :=
      (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr hs
    simp [hs, hz]

private lemma support_plus_double_eq_twice_edges (hC : Is45Coloring C) (q : Fin k) :
    #((C.labelGraph q).support.toFinset) +
      #{v : Fin n | (C.labelGraph q).degree v = 2} =
      2 * #(C.labelGraph q).edgeFinset := by
  rw [← (C.labelGraph q).sum_degrees_eq_twice_card_edges]
  have hsum : (∑ v : Fin n, (C.labelGraph q).degree v) =
      ∑ v : Fin n,
        ((if v ∈ (C.labelGraph q).support then 1 else 0) +
          (if (C.labelGraph q).degree v = 2 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro v _
    exact degree_indicator hC q v
  rw [hsum]
  rw [Finset.sum_add_distrib]
  have hsupp : (∑ v : Fin n, if v ∈ (C.labelGraph q).support then 1 else 0) =
      #((C.labelGraph q).support.toFinset) := by
    classical
    have hb := Finset.sum_boole (R := ℕ)
      (fun v : Fin n ↦ v ∈ (C.labelGraph q).support) Finset.univ
    rw [hb]
    have hfin : {v ∈ (Finset.univ : Finset (Fin n)) |
        v ∈ (C.labelGraph q).support} = (C.labelGraph q).support.toFinset := by
      ext v
      simp
    exact congrArg Finset.card hfin
  have htwo : (∑ v : Fin n, if (C.labelGraph q).degree v = 2 then 1 else 0) =
      #{v : Fin n | (C.labelGraph q).degree v = 2} := by
    exact
      (Finset.sum_boole (R := ℕ) (fun v : Fin n ↦ (C.labelGraph q).degree v = 2)
        Finset.univ)
  rw [hsupp, htwo]

private lemma total_support_plus_double_eq (hC : Is45Coloring C) :
    (∑ q : Fin k, #((C.labelGraph q).support.toFinset)) +
      Fintype.card (DoubleCenter C) = 2 * n.choose 2 := by
  rw [card_doubleCenter_eq_sum, ← Finset.sum_add_distrib]
  simp_rw [support_plus_double_eq_twice_edges hC]
  rw [← Finset.mul_sum, sum_color_edges]

private lemma total_support_le :
    (∑ q : Fin k, #((C.labelGraph q).support.toFinset)) ≤ k * n := by
  calc
    (∑ q : Fin k, #((C.labelGraph q).support.toFinset)) ≤ ∑ _q : Fin k, n := by
      apply Finset.sum_le_sum
      intro q _
      calc
        #((C.labelGraph q).support.toFinset) ≤ #(Finset.univ : Finset (Fin n)) :=
          Finset.card_le_card (by simp)
        _ = n := by simp
    _ = k * n := by simp

end Counting

section LowerBound

variable {n k : ℕ}

/-- The elementary Erdős--Gyárfás lower bound for every admissible
colouring, in denominator-free natural-number form. -/
theorem is45Coloring_lower_bound (hn : 4 ≤ n)
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) (hC : Is45Coloring C) :
    5 * (n - 1) ≤ 6 * k := by
  let S := ∑ q : Fin k, #((C.labelGraph q).support.toFinset)
  let H := Fintype.card (DoubleCenter C)
  let E := n.choose 2
  have hcount : S + H = 2 * E := total_support_plus_double_eq hC
  have hsupport : S ≤ k * n := total_support_le
  have hmate : 3 * H ≤ E := three_mul_doubleCenter_le_edges hC hn
  have hfive : 5 * E ≤ 3 * (k * n) := by omega
  have hchoose : 2 * E = n * (n - 1) := by
    dsimp [E]
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  apply Nat.le_of_mul_le_mul_left (c := n) ?_ (by omega)
  calc
    n * (5 * (n - 1)) = 5 * (n * (n - 1)) := by ring
    _ = 2 * (5 * E) := by rw [← hchoose]; ring
    _ ≤ 2 * (3 * (k * n)) := Nat.mul_le_mul_left 2 hfive
    _ = n * (6 * k) := by ring

/-- Palette-size version of `is45Coloring_lower_bound`. -/
theorem colorable_lower_bound (hn : 4 ≤ n) (h : Colorable n k) :
    5 * (n - 1) ≤ 6 * k := by
  obtain ⟨C, hC⟩ := h
  exact is45Coloring_lower_bound hn C hC

/-- The exact minimum in Problem 136 satisfies the finite lower bound. -/
theorem erdos136Fun_lower_bound (hn : 4 ≤ n) :
    5 * (n - 1) ≤ 6 * erdos136Fun n :=
  colorable_lower_bound hn (erdos136Fun_spec n)

/-- The familiar real-number formulation
`(5/6)(n-1) ≤ f(n)`. -/
theorem erdos136Fun_lower_bound_real (hn : 4 ≤ n) :
    (5 / 6 : ℝ) * ((n : ℝ) - 1) ≤ (erdos136Fun n : ℝ) := by
  have hnat := erdos136Fun_lower_bound hn
  have hc : ((5 * (n - 1) : ℕ) : ℝ) ≤
      ((6 * erdos136Fun n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcast : (5 : ℝ) * ((n : ℝ) - 1) ≤
      6 * (erdos136Fun n : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using hc
  linarith

end LowerBound

end Erdos136

#print axioms Erdos136.erdos136Fun_lower_bound
#print axioms Erdos136.erdos136Fun_lower_bound_real
