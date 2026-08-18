/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.ConflictFreeMatching
import ErdosProblems.Erdos136.Completion

/-!
# The Joos--Mubayi partial construction for Erdős Problem 136

This file isolates the deterministic part of the Joos--Mubayi construction.
An auxiliary vertex is either an edge of `K_n` or a labelled vertex
`(v, i)`.  An auxiliary edge is the eight-element support attached to a
triangle block `(u; v, w; i, j)` and records the colouring

* `uv, uw` with the repeated colour `i`, and
* `vw` with the singleton colour `j`.

The explicit block decomposition is retained in `PartialGood`; this is the
closure invariant needed by the final completion argument.  The elementary
properties (P0)--(P2) are proved directly from disjoint auxiliary supports.
Properties (P3)--(P5) are the exact output predicates supplied by the
conflict-free matching and its tracked test functions.
-/

namespace Erdos136

open Finset

noncomputable section

/-- The auxiliary hypergraph has one vertex for every graph edge and one
vertex for every vertex/old-colour label.  Diagonal `Sym2` vertices are
harmless: no auxiliary edge contains one. -/
abbrev AuxVertex (n k : ℕ) := Sym2 (Fin n) ⊕ (Fin n × Fin k)

/-- A marked triangle carrying the colour pattern `i,i,j`.  Ordering the
two non-apex vertices removes the otherwise irrelevant swap symmetry and
makes a block recoverable from its auxiliary support. -/
structure TriangleBlock (n k : ℕ) where
  apex : Fin n
  left : Fin n
  right : Fin n
  apex_ne_left : apex ≠ left
  apex_ne_right : apex ≠ right
  left_lt_right : left < right
  repeated : Fin k
  singleton : Fin k
  colors_ne : repeated ≠ singleton
  deriving DecidableEq

namespace TriangleBlock

variable {n k : ℕ}

/-- The three graph edges in a triangle block. -/
def graphEdges (b : TriangleBlock n k) : Finset (Sym2 (Fin n)) :=
  {s(b.apex, b.left), s(b.apex, b.right), s(b.left, b.right)}

/-- The five positive labelled vertices of the Joos--Mubayi auxiliary edge. -/
def positiveLabels (b : TriangleBlock n k) : Finset (Fin n × Fin k) :=
  {(b.apex, b.repeated), (b.left, b.repeated), (b.right, b.repeated),
    (b.left, b.singleton), (b.right, b.singleton)}

/-- The complete eight-vertex support of a Joos--Mubayi auxiliary edge. -/
def auxSupport (b : TriangleBlock n k) : Finset (AuxVertex n k) :=
  b.graphEdges.image Sum.inl ∪ b.positiveLabels.image Sum.inr

/-- The binary edge `xy` is one of the three graph edges of `b`. -/
def Supports (b : TriangleBlock n k) (x y : Fin n) : Prop :=
  s(x, y) ∈ b.graphEdges

/-- The block `b` assigns colour `c` to the unordered edge `xy`. -/
def Paints (b : TriangleBlock n k) (x y : Fin n) (c : Fin k) : Prop :=
  ((s(x, y) = s(b.apex, b.left) ∨ s(x, y) = s(b.apex, b.right)) ∧
      c = b.repeated) ∨
    (s(x, y) = s(b.left, b.right) ∧ c = b.singleton)

theorem left_ne_right (b : TriangleBlock n k) : b.left ≠ b.right :=
  ne_of_lt b.left_lt_right

theorem vertices_pairwise (b : TriangleBlock n k) :
    b.apex ≠ b.left ∧ b.apex ≠ b.right ∧ b.left ≠ b.right :=
  ⟨b.apex_ne_left, b.apex_ne_right, b.left_ne_right⟩

@[simp] theorem graphEdges_card (b : TriangleBlock n k) : b.graphEdges.card = 3 := by
  simp [graphEdges, Sym2.eq_iff, b.apex_ne_left, b.apex_ne_right,
    b.left_ne_right]

@[simp] theorem positiveLabels_card (b : TriangleBlock n k) :
    b.positiveLabels.card = 5 := by
  simp [positiveLabels, b.apex_ne_left, b.apex_ne_right, b.left_ne_right,
    b.colors_ne]

@[simp] theorem auxSupport_card (b : TriangleBlock n k) :
    b.auxSupport.card = 8 := by
  classical
  rw [auxSupport, card_union_of_disjoint]
  · rw [card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective]
    simp
  · exact Finset.disjoint_left.2 (by simp)

theorem paints_symm (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : b.Paints y x c := by
  simpa only [Paints, Sym2.eq_swap (a := x) (b := y)] using h

theorem paints_supports (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : b.Supports x y := by
  rcases h with (⟨h, rfl⟩ | ⟨h, rfl⟩)
  · rcases h with h | h
    · exact (by simp only [Supports, graphEdges, mem_insert, mem_singleton]; aesop)
    · exact (by simp only [Supports, graphEdges, mem_insert, mem_singleton]; aesop)
  · exact (by simp only [Supports, graphEdges, mem_insert, mem_singleton]; aesop)

theorem paints_graph_mem (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : Sum.inl s(x, y) ∈ b.auxSupport := by
  classical
  apply mem_union_left
  exact mem_image.2 ⟨s(x, y), b.paints_supports h, rfl⟩

/-- Every endpoint of a painted edge is among the five positive labels. -/
theorem paints_positiveLabel_mem (b : TriangleBlock n k)
    {x y : Fin n} {c : Fin k} (h : b.Paints x y c) :
    (x, c) ∈ b.positiveLabels := by
  classical
  rcases h with (⟨he, rfl⟩ | ⟨he, rfl⟩)
  · rcases he with he | he <;> rw [Sym2.eq_iff] at he
    · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [positiveLabels]
    · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [positiveLabels]
  · rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [positiveLabels]

/-- Every endpoint of a painted edge contributes its vertex/colour label to
the auxiliary support. -/
theorem paints_label_mem (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : Sum.inr (x, c) ∈ b.auxSupport := by
  classical
  apply mem_union_right
  exact mem_image.2 ⟨(x, c), b.paints_positiveLabel_mem h, rfl⟩

theorem paints_other_label_mem (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : Sum.inr (y, c) ∈ b.auxSupport :=
  b.paints_label_mem (TriangleBlock.paints_symm b h)

theorem paints_ne (b : TriangleBlock n k) {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : x ≠ y := by
  intro hxy
  subst y
  rcases h with (⟨h, -⟩ | ⟨h, -⟩)
  · rcases h with h | h
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨hxa, hxl⟩ | ⟨hxl, hxa⟩
      · exact b.apex_ne_left (hxa.symm.trans hxl)
      · exact b.apex_ne_left (hxa.symm.trans hxl)
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨hxa, hxr⟩ | ⟨hxr, hxa⟩
      · exact b.apex_ne_right (hxa.symm.trans hxr)
      · exact b.apex_ne_right (hxa.symm.trans hxr)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨hxl, hxr⟩ | ⟨hxr, hxl⟩
    · exact b.left_ne_right (hxl.symm.trans hxr)
    · exact b.left_ne_right (hxl.symm.trans hxr)

theorem paint_unique (b : TriangleBlock n k) {x y : Fin n} {c d : Fin k}
    (hc : b.Paints x y c) (hd : b.Paints x y d) : c = d := by
  rcases hc with (⟨hc, rfl⟩ | ⟨hc, rfl⟩) <;>
    rcases hd with (⟨hd, rfl⟩ | ⟨hd, rfl⟩)
  · rfl
  · exfalso
    rcases hc with hc | hc
    · have he := hc.symm.trans hd
      simpa [Sym2.eq_iff, b.apex_ne_left, b.apex_ne_right] using he
    · have he := hc.symm.trans hd
      simpa [Sym2.eq_iff, b.apex_ne_left, b.apex_ne_right,
        b.left_ne_right] using he
  · exfalso
    rcases hd with hd | hd
    · have he := hd.symm.trans hc
      simpa [Sym2.eq_iff, b.apex_ne_left, b.apex_ne_right] using he
    · have he := hd.symm.trans hc
      simpa [Sym2.eq_iff, b.apex_ne_left, b.apex_ne_right,
        b.left_ne_right] using he
  · rfl

/-- In one block, an edge painted with the singleton colour is precisely
the opposite edge. -/
theorem singleton_edge {b : TriangleBlock n k} {x y : Fin n}
    (h : b.Paints x y b.singleton) : s(x, y) = s(b.left, b.right) := by
  rcases h with (⟨he, hc⟩ | ⟨he, -⟩)
  · exact (b.colors_ne hc.symm).elim
  · exact he

/-- The explicit closure invariant: two distinct incident edges painted the
same colour by one block are its repeated pair, so their closing edge is
painted with the singleton colour. -/
theorem closes_sameColor_path {b : TriangleBlock n k} {x y z : Fin n}
    {c : Fin k} (hxy : b.Paints x y c) (hxz : b.Paints x z c)
    (hyz : y ≠ z) : b.Paints y z b.singleton := by
  rcases hxy with (⟨hxy, hc⟩ | ⟨hxy, hc⟩) <;>
    rcases hxz with (⟨hxz, hc'⟩ | ⟨hxz, hc'⟩)
  · have hcc : c = b.repeated := hc
    subst c
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz <;>
      rw [Sym2.eq_iff] at hxy hxz <;>
      simp only [Paints] <;> aesop
  · exact (b.colors_ne (hc.symm.trans hc')).elim
  · exact (b.colors_ne (hc'.symm.trans hc)).elim
  · have he : s(x, y) = s(x, z) := hxy.trans hxz.symm
    exact (hyz (Sym2.congr_right.mp he)).elim

theorem paint_color_cases {b : TriangleBlock n k} {x y : Fin n} {c : Fin k}
    (h : b.Paints x y c) : c = b.repeated ∨ c = b.singleton := by
  rcases h with (⟨-, rfl⟩ | ⟨-, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem support_has_color {b : TriangleBlock n k} {x y : Fin n}
    (h : b.Supports x y) : ∃ c, b.Paints x y c := by
  simp only [Supports, graphEdges, mem_insert, mem_singleton] at h
  rcases h with h | h | h
  · exact ⟨b.repeated, Or.inl ⟨Or.inl h, rfl⟩⟩
  · exact ⟨b.repeated, Or.inl ⟨Or.inr h, rfl⟩⟩
  · exact ⟨b.singleton, Or.inr ⟨h, rfl⟩⟩

theorem closes_supported_path {b : TriangleBlock n k} {x y z : Fin n}
    (hxy : b.Supports x y) (hxz : b.Supports x z) (hyz : y ≠ z) :
    b.Supports y z := by
  simp only [Supports, graphEdges, mem_insert, mem_singleton] at hxy hxz ⊢
  rcases hxy with hxy | hxy | hxy <;>
    rcases hxz with hxz | hxz | hxz <;>
    rw [Sym2.eq_iff] at hxy hxz <;> aesop

/-- If two distinct incident edges of a block have different colours, the
closing edge has one of these two colours. -/
theorem closes_differentColor_path {b : TriangleBlock n k} {x y z : Fin n}
    {c d : Fin k} (hxy : b.Paints x y c) (hxz : b.Paints x z d)
    (hyz : y ≠ z) (hcd : c ≠ d) :
    ∃ q, (q = c ∨ q = d) ∧ b.Paints y z q := by
  obtain ⟨q, hq⟩ := b.support_has_color
    (b.closes_supported_path (b.paints_supports hxy) (b.paints_supports hxz) hyz)
  refine ⟨q, ?_, hq⟩
  rcases b.paint_color_cases hxy with hc | hc <;>
    rcases b.paint_color_cases hxz with hd | hd <;>
    rcases b.paint_color_cases hq with hq' | hq' <;> aesop

end TriangleBlock

/-- A retention pattern for the copied vertex-colour labels. -/
abbrev RetainedLabels (n k : ℕ) := Finset (Fin n × Fin k)

/-- Eligibility of a candidate auxiliary edge.  The five positive labels
are retained, while the apex in the singleton colour is not retained. -/
def Eligible {n k : ℕ} (R : RetainedLabels n k) (b : TriangleBlock n k) : Prop :=
  b.positiveLabels ⊆ R ∧ (b.apex, b.singleton) ∉ R

/-- The concrete 8-uniform auxiliary hypergraph. -/
def auxiliaryHypergraph {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) :
    Finset (Finset (AuxVertex n k)) :=
  by
    classical
    exact (candidates.filter (Eligible R)).image TriangleBlock.auxSupport

theorem auxiliaryHypergraph_uniform {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e : Finset (AuxVertex n k)} (he : e ∈ auxiliaryHypergraph candidates R) :
    e.card = 8 := by
  classical
  rw [auxiliaryHypergraph, mem_image] at he
  obtain ⟨b, -, rfl⟩ := he
  exact TriangleBlock.auxSupport_card b

/-- Choose the unique *selected representative* of an auxiliary hyperedge.
The support map need not be globally injective; choosing one preimage for
each hyperedge is enough, and distinct matching edges then choose blocks
with distinct supports. -/
def blockOfAuxEdge {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (e : Finset (AuxVertex n k))
    (he : e ∈ auxiliaryHypergraph candidates R) : TriangleBlock n k := by
  classical
  exact Classical.choose (Finset.mem_image.mp he)

theorem blockOfAuxEdge_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e : Finset (AuxVertex n k)) (he : e ∈ auxiliaryHypergraph candidates R) :
    blockOfAuxEdge candidates R e he ∈ candidates ∧
      Eligible R (blockOfAuxEdge candidates R e he) ∧
      (blockOfAuxEdge candidates R e he).auxSupport = e := by
  classical
  have hs := Classical.choose_spec (Finset.mem_image.mp he)
  exact ⟨(Finset.mem_filter.mp hs.1).1, (Finset.mem_filter.mp hs.1).2, hs.2⟩

theorem blockOfAuxEdge_eligible {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e : Finset (AuxVertex n k)) (he : e ∈ auxiliaryHypergraph candidates R) :
    Eligible R (blockOfAuxEdge candidates R e he) := by
  exact (blockOfAuxEdge_spec candidates R e he).2.1

theorem blockOfAuxEdge_support {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e : Finset (AuxVertex n k)) (he : e ∈ auxiliaryHypergraph candidates R) :
    (blockOfAuxEdge candidates R e he).auxSupport = e :=
  (blockOfAuxEdge_spec candidates R e he).2.2

/-- Recover one concrete triangle block for every edge of an abstract
auxiliary matching. -/
def blocksOfAuxFamily {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (M : Hypergraph (AuxVertex n k))
    (hM : M ⊆ auxiliaryHypergraph candidates R) : Finset (TriangleBlock n k) := by
  classical
  exact M.attach.image fun e =>
    blockOfAuxEdge candidates R e.1 (hM e.2)

theorem blocksOfAuxFamily_supports {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (M : Hypergraph (AuxVertex n k))
    (hM : M ⊆ auxiliaryHypergraph candidates R) :
    (blocksOfAuxFamily candidates R M hM).image TriangleBlock.auxSupport = M := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hb
    simpa [blockOfAuxEdge_support] using e'.2
  · intro he
    apply Finset.mem_image.2
    let e' : {e // e ∈ M} := ⟨e, he⟩
    refine ⟨blockOfAuxEdge candidates R e (hM he), ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨e', Finset.mem_attach _ e', rfl⟩
    · exact blockOfAuxEdge_support candidates R e (hM he)

/-- A selected family is an auxiliary matching if every selected block is
eligible and different blocks have disjoint eight-vertex supports. -/
def IsAuxMatching {n k : ℕ} (R : RetainedLabels n k)
    (M : Finset (TriangleBlock n k)) : Prop :=
  (∀ b ∈ M, Eligible R b) ∧
    (↑M : Set (TriangleBlock n k)).Pairwise
      fun b b' => Disjoint b.auxSupport b'.auxSupport

theorem blocksOfAuxFamily_isAuxMatching {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (M : Hypergraph (AuxVertex n k))
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) M) :
    IsAuxMatching R (blocksOfAuxFamily candidates R M hmatch.1) := by
  classical
  constructor
  · intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    exact blockOfAuxEdge_eligible candidates R e.1 (hmatch.1 e.2)
  · intro b hb b' hb' hbb'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hb'
    have hee' : e.1 ≠ e'.1 := by
      intro heq
      apply hbb'
      rcases e with ⟨e, heM⟩
      rcases e' with ⟨e', heM'⟩
      dsimp at heq ⊢
      subst e'
      rfl
    have hd := hmatch.2 e.2 e'.2 hee'
    simpa only [blockOfAuxEdge_support] using hd

/-- The selected blocks assign colour `c` to edge `xy`. -/
def HasPaint {n k : ℕ} (M : Finset (TriangleBlock n k))
    (x y : Fin n) (c : Fin k) : Prop :=
  ∃ b ∈ M, b.Paints x y c

theorem hasPaint_symm {n k : ℕ} {M : Finset (TriangleBlock n k)}
    {x y : Fin n} {c : Fin k} (h : HasPaint M x y c) : HasPaint M y x c := by
  obtain ⟨b, hb, hpaint⟩ := h
  exact ⟨b, hb, TriangleBlock.paints_symm b hpaint⟩

theorem hasPaint_unique {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {x y : Fin n} {c d : Fin k}
    (hc : HasPaint M x y c) (hd : HasPaint M x y d) : c = d := by
  obtain ⟨b, hb, hbc⟩ := hc
  obtain ⟨b', hb', hb'd⟩ := hd
  by_cases hbb' : b = b'
  · subst b'
    exact b.paint_unique hbc hb'd
  · have hdisj := hM.2 (by simpa using hb) (by simpa using hb') hbb'
    change Disjoint b.auxSupport b'.auxSupport at hdisj
    rw [Finset.disjoint_left] at hdisj
    exact False.elim <| (hdisj (b.paints_graph_mem hbc))
      (b'.paints_graph_mem hb'd)

/-- Two selected blocks which use the same colour at the same graph vertex
must be the same auxiliary edge.  This is the labelled-vertex mechanism
behind property (P1). -/
theorem blocks_eq_of_paints_at {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {b b' : TriangleBlock n k} (hb : b ∈ M) (hb' : b' ∈ M)
    {x y z : Fin n} {c : Fin k}
    (hpaint : b.Paints x y c) (hpaint' : b'.Paints x z c) : b = b' := by
  by_contra hne
  have hdisj := hM.2 (by simpa using hb) (by simpa using hb') hne
  change Disjoint b.auxSupport b'.auxSupport at hdisj
  rw [Finset.disjoint_left] at hdisj
  exact (hdisj (b.paints_label_mem hpaint)) (b'.paints_label_mem hpaint')

/-- The partial old colouring induced by an auxiliary matching. -/
def inducedColor {n k : ℕ} (M : Finset (TriangleBlock n k))
    (x y : Fin n) : Option (Fin k) :=
  by
    classical
    exact if h : Nonempty {c // HasPaint M x y c} then some h.some.1 else none

theorem inducedColor_eq_some_iff {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {x y : Fin n} {c : Fin k} :
    inducedColor M x y = some c ↔ HasPaint M x y c := by
  unfold inducedColor
  split_ifs with h
  · constructor
    · intro heq
      have hc : h.some.1 = c := Option.some.inj heq
      simpa [hc] using h.some.2
    · intro hc
      congr 1
      exact hasPaint_unique hM h.some.2 hc
  · constructor
    · simp
    · exact fun hc => (h ⟨⟨c, hc⟩⟩).elim

@[simp] theorem inducedColor_symm {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    (x y : Fin n) : inducedColor M x y = inducedColor M y x := by
  apply Option.ext
  intro c
  simp only [inducedColor_eq_some_iff hM]
  exact ⟨hasPaint_symm, hasPaint_symm⟩

@[simp] theorem inducedColor_self {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    (x : Fin n) : inducedColor M x x = none := by
  apply Option.eq_none_iff_forall_not_mem.2
  intro c hc
  have hp : HasPaint M x x c :=
    (inducedColor_eq_some_iff hM).1 (Option.mem_def.1 hc)
  obtain ⟨b, -, hpaint⟩ := hp
  exact TriangleBlock.paints_ne b hpaint rfl

/-! ## The explicit partial-colouring properties -/

/-- (P0): the old-coloured graph is exactly the edge-disjoint union of the
displayed triangle blocks, with their `i,i,j` patterns. -/
def BlockClosure {n k : ℕ} (blocks : Finset (TriangleBlock n k))
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ((↑blocks : Set (TriangleBlock n k)).Pairwise
      fun b b' => Disjoint b.graphEdges b'.graphEdges) ∧
    ∀ x y c, old x y = some c ↔ ∃ b ∈ blocks, b.Paints x y c

/-- (P1): whenever two old edges of the same colour meet, they belong to
one explicit triangle block.  Since a block uses its singleton colour only
once, this says precisely that every colour class is a disjoint union of
isolated edges and two-edge paths. -/
def ColorClassesAreEdgesOrPaths {n k : ℕ}
    (blocks : Finset (TriangleBlock n k))
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ∀ c x y z, old x y = some c → old x z = some c →
    ∃ b ∈ blocks, b.Paints x y c ∧ b.Paints x z c

/-- (P2): for every `i,i,j` block, the apex is isolated in colour `j` and
the opposite `j`-edge is an isolated component of its colour class. -/
def MateIsolated {n k : ℕ} (blocks : Finset (TriangleBlock n k))
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ∀ b ∈ blocks,
    (∀ x, old b.apex x ≠ some b.singleton) ∧
    (∀ x, old b.left x = some b.singleton →
      s(b.left, x) = s(b.left, b.right)) ∧
    (∀ x, old b.right x = some b.singleton →
      s(b.right, x) = s(b.left, b.right))

/-- Four vertices are pairwise distinct. -/
def FourDistinct {n : ℕ} (x₀ x₁ x₂ x₃ : Fin n) : Prop :=
  x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃

theorem TriangleBlock.repeated_of_sameColor_path {n k : ℕ}
    {b : TriangleBlock n k} {x y z : Fin n} {c : Fin k}
    (hxy : b.Paints x y c) (hxz : b.Paints x z c) (hyz : y ≠ z) :
    c = b.repeated := by
  rcases b.paint_color_cases hxy with hc | hc
  · exact hc
  · have h₁ := b.singleton_edge (hc ▸ hxy)
    have h₂ := b.singleton_edge (hc ▸ hxz)
    exact (hyz (Sym2.congr_right.mp (h₁.trans h₂.symm))).elim

theorem no_monochromatic_path_three {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {x₀ x₁ x₂ x₃ : Fin n} {c : Fin k}
    (hD : FourDistinct x₀ x₁ x₂ x₃)
    (h₀₁ : HasPaint M x₀ x₁ c) (h₁₂ : HasPaint M x₁ x₂ c)
    (h₂₃ : HasPaint M x₂ x₃ c) : False := by
  obtain ⟨b₀, hb₀, hp₀⟩ := h₀₁
  obtain ⟨b₁, hb₁, hp₁⟩ := h₁₂
  obtain ⟨b₂, hb₂, hp₂⟩ := h₂₃
  have h₀₁b := blocks_eq_of_paints_at hM hb₀ hb₁
    (TriangleBlock.paints_symm b₀ hp₀) hp₁
  subst b₁
  have h₁₂b := blocks_eq_of_paints_at hM hb₀ hb₂
    (TriangleBlock.paints_symm b₀ hp₁) hp₂
  subst b₂
  have hclose₀ := b₀.closes_sameColor_path
    (TriangleBlock.paints_symm b₀ hp₀) hp₁ hD.2.1
  have hclose₁ := b₀.closes_sameColor_path
    (TriangleBlock.paints_symm b₀ hp₁) hp₂ hD.2.2.2.2.1
  have he := (b₀.singleton_edge hclose₀).trans
    (b₀.singleton_edge hclose₁).symm
  rw [Sym2.eq_iff] at he
  unfold FourDistinct at hD
  rcases he with he | he <;> aesop

theorem TriangleBlock.no_disjoint_painted_edges {n k : ℕ}
    {b : TriangleBlock n k} {x₀ x₁ x₂ x₃ : Fin n} {c d : Fin k}
    (hD : FourDistinct x₀ x₁ x₂ x₃)
    (h₀₁ : b.Paints x₀ x₁ c) (h₂₃ : b.Paints x₂ x₃ d) : False := by
  have hs₀ := b.paints_supports h₀₁
  have hs₂ := b.paints_supports h₂₃
  simp only [Supports, graphEdges, mem_insert, mem_singleton] at hs₀ hs₂
  unfold FourDistinct at hD
  rcases hs₀ with hs₀ | hs₀ | hs₀ <;>
    rcases hs₂ with hs₂ | hs₂ | hs₂ <;>
    rw [Sym2.eq_iff] at hs₀ hs₂ <;> aesop

/-- In a putative two-coloured old four-cycle, adjacent colours cannot be
equal.  This is the non-alternating case eliminated by (P1), (P2), and the
explicit block closure. -/
theorem cycle_adjacent_colors_ne {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {x₀ x₁ x₂ x₃ : Fin n} {c₀ c₁ c₂ c₃ : Fin k}
    (hD : FourDistinct x₀ x₁ x₂ x₃)
    (h₀₁ : HasPaint M x₀ x₁ c₀) (h₁₂ : HasPaint M x₁ x₂ c₁)
    (h₂₃ : HasPaint M x₂ x₃ c₂) (h₃₀ : HasPaint M x₃ x₀ c₃)
    (hcard : ({c₀, c₁, c₂, c₃} : Finset (Fin k)).card < 3) : c₀ ≠ c₁ := by
  intro hc₀₁
  subst c₁
  have hc₂ : c₂ ≠ c₀ := by
    intro h
    subst c₂
    exact no_monochromatic_path_three hM hD h₀₁ h₁₂ h₂₃
  have hc₃ : c₃ ≠ c₀ := by
    intro h
    subst c₃
    have hD' : FourDistinct x₂ x₁ x₀ x₃ := by
      unfold FourDistinct at hD ⊢
      aesop
    exact no_monochromatic_path_three hM hD'
      (hasPaint_symm h₁₂) (hasPaint_symm h₀₁) (hasPaint_symm h₃₀)
  have hc₂₃ : c₂ = c₃ := by
    by_contra hne
    have hsub : ({c₀, c₂, c₃} : Finset (Fin k)) ⊆ {c₀, c₀, c₂, c₃} := by
      simp
    have hle := Finset.card_le_card hsub
    have hthree : ({c₀, c₂, c₃} : Finset (Fin k)).card = 3 := by
      have h0 : c₀ ∉ ({c₂, c₃} : Finset (Fin k)) := by
        simp [Ne.symm hc₂, Ne.symm hc₃]
      have h2 : c₂ ∉ ({c₃} : Finset (Fin k)) := by
        simpa using hne
      rw [card_insert_of_notMem h0, card_insert_of_notMem h2, card_singleton]
    omega
  subst c₃
  obtain ⟨b, hb, hp₀⟩ := h₀₁
  obtain ⟨b₁, hb₁, hp₁⟩ := h₁₂
  have hbb₁ := blocks_eq_of_paints_at hM hb hb₁
    (TriangleBlock.paints_symm b hp₀) hp₁
  subst b₁
  obtain ⟨b', hb', hp₂⟩ := h₂₃
  obtain ⟨b₃, hb₃, hp₃⟩ := h₃₀
  have hb'b₃ := blocks_eq_of_paints_at hM hb' hb₃
    (TriangleBlock.paints_symm b' hp₂) hp₃
  subst b₃
  have hclose := b.closes_sameColor_path
    (TriangleBlock.paints_symm b hp₀) hp₁ hD.2.1
  have hclose' := b'.closes_sameColor_path
    (TriangleBlock.paints_symm b' hp₂) hp₃ hD.2.1.symm
  have hsingle : b.singleton = b'.singleton :=
    hasPaint_unique hM ⟨b, hb, hclose⟩
      ⟨b', hb', TriangleBlock.paints_symm b' hclose'⟩
  have hblocks : b = b' := by
    apply blocks_eq_of_paints_at hM hb hb'
      (TriangleBlock.paints_symm b hclose)
    simpa [hsingle] using hclose'
  have hc₀rep := b.repeated_of_sameColor_path
    (TriangleBlock.paints_symm b hp₀) hp₁ hD.2.1
  have hc₂rep := b'.repeated_of_sameColor_path
    (TriangleBlock.paints_symm b' hp₂) hp₃ hD.2.1.symm
  subst b'
  exact hc₂ (hc₂rep.trans hc₀rep.symm)

/-- The four blocks witnessing an alternating old cycle are genuinely four
different auxiliary edges.  This lemma handles one adjacent pair; rotations
give all four adjacent inequalities. -/
theorem alternating_adjacent_blocks_ne {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {x₀ x₁ x₂ x₃ : Fin n} {c d : Fin k}
    (hD : FourDistinct x₀ x₁ x₂ x₃) (hcd : c ≠ d)
    {b₀ b₁ : TriangleBlock n k} (hb₀ : b₀ ∈ M) (hb₁ : b₁ ∈ M)
    (hp₀ : b₀.Paints x₀ x₁ c) (hp₁ : b₁.Paints x₁ x₂ d)
    (h₂₃ : HasPaint M x₂ x₃ c) (h₃₀ : HasPaint M x₃ x₀ d) : b₀ ≠ b₁ := by
  intro hblocks
  subst b₁
  obtain ⟨q, hq, hclose⟩ := b₀.closes_differentColor_path
    (TriangleBlock.paints_symm b₀ hp₀) hp₁ hD.2.1 hcd
  rcases hq with rfl | rfl
  · have hD' : FourDistinct x₁ x₀ x₂ x₃ := by
      unfold FourDistinct at hD ⊢
      aesop
    exact no_monochromatic_path_three hM hD'
      ⟨b₀, hb₀, TriangleBlock.paints_symm b₀ hp₀⟩
      ⟨b₀, hb₀, hclose⟩ h₂₃
  · have hD' : FourDistinct x₁ x₂ x₀ x₃ := by
      unfold FourDistinct at hD ⊢
      aesop
    exact no_monochromatic_path_three hM hD'
      ⟨b₀, hb₀, hp₁⟩
      ⟨b₀, hb₀, TriangleBlock.paints_symm b₀ hclose⟩
      (hasPaint_symm h₃₀)

theorem auxSupports_ne_of_blocks_ne {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M)
    {b b' : TriangleBlock n k} (hb : b ∈ M) (hb' : b' ∈ M)
    (hne : b ≠ b') : b.auxSupport ≠ b'.auxSupport := by
  intro heq
  have hd := hM.2 hb hb' hne
  change Disjoint b.auxSupport b'.auxSupport at hd
  rw [← heq] at hd
  have hempty : b.auxSupport = ∅ := disjoint_self.mp hd
  have hc := TriangleBlock.auxSupport_card b
  rw [hempty] at hc
  simp at hc

theorem opposite_eq_of_fourColor_card_lt_three {k : ℕ}
    {c₀ c₁ c₂ c₃ : Fin k} (h₀₁ : c₀ ≠ c₁) (h₁₂ : c₁ ≠ c₂)
    (hcard : ({c₀, c₁, c₂, c₃} : Finset (Fin k)).card < 3) : c₀ = c₂ := by
  by_contra h₀₂
  have hsub : ({c₀, c₁, c₂} : Finset (Fin k)) ⊆ {c₀, c₁, c₂, c₃} := by
    simp
  have hle := Finset.card_le_card hsub
  have hthree : ({c₀, c₁, c₂} : Finset (Fin k)).card = 3 := by
    have h0 : c₀ ∉ ({c₁, c₂} : Finset (Fin k)) := by
      simp [h₀₁, h₀₂]
    have h1 : c₁ ∉ ({c₂} : Finset (Fin k)) := by
      simpa using h₁₂
    rw [card_insert_of_notMem h0, card_insert_of_notMem h1, card_singleton]
  omega

/-- A four-member conflict is the set of auxiliary edges which would paint
an alternating two-coloured old four-cycle. -/
def IsAlternatingCycleConflict {n k : ℕ}
    (Q : Hypergraph (AuxVertex n k)) : Prop :=
  ∃ (x₀ x₁ x₂ x₃ : Fin n) (c d : Fin k)
      (b₀ b₁ b₂ b₃ : TriangleBlock n k),
    FourDistinct x₀ x₁ x₂ x₃ ∧ c ≠ d ∧
    b₀.Paints x₀ x₁ c ∧ b₁.Paints x₁ x₂ d ∧
    b₂.Paints x₂ x₃ c ∧ b₃.Paints x₃ x₀ d ∧
    Q = {b₀.auxSupport, b₁.auxSupport, b₂.auxSupport, b₃.auxSupport}

/-- The 4-uniform conflict system used by Joos--Mubayi. -/
def alternatingCycleConflicts {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    ConflictSystem (AuxVertex n k) := by
  classical
  exact (auxiliaryHypergraph candidates R).powersetCard 4 |>.filter
    IsAlternatingCycleConflict

theorem alternatingCycleConflicts_uniform {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {Q : Hypergraph (AuxVertex n k)}
    (hQ : Q ∈ alternatingCycleConflicts candidates R) : Q.card = 4 := by
  classical
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).2

theorem alternatingCycleConflicts_isConflictSystem {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    IsConflictSystem (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) := by
  classical
  intro Q hQ
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).1

/-- (P3): every completely old-coloured four-cycle has at least three old
colours. -/
def OldFourCyclesUseThree {n k : ℕ}
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ∀ x₀ x₁ x₂ x₃ c₀ c₁ c₂ c₃,
    FourDistinct x₀ x₁ x₂ x₃ →
    old x₀ x₁ = some c₀ → old x₁ x₂ = some c₁ →
    old x₂ x₃ = some c₂ → old x₃ x₀ = some c₃ →
    3 ≤ ({c₀, c₁, c₂, c₃} : Finset (Fin k)).card

theorem matching_oldFourCyclesUseThree {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (MH : Hypergraph (AuxVertex n k))
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    (hfree : ConflictFree (alternatingCycleConflicts candidates R) MH) :
    let BM := blocksOfAuxFamily candidates R MH hmatch.1
    OldFourCyclesUseThree (inducedColor BM) := by
  classical
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  have hBM : IsAuxMatching R BM :=
    blocksOfAuxFamily_isAuxMatching candidates R MH hmatch
  change OldFourCyclesUseThree (inducedColor BM)
  intro x₀ x₁ x₂ x₃ c₀ c₁ c₂ c₃ hD hold₀ hold₁ hold₂ hold₃
  have hp₀ : HasPaint BM x₀ x₁ c₀ := (inducedColor_eq_some_iff hBM).1 hold₀
  have hp₁ : HasPaint BM x₁ x₂ c₁ := (inducedColor_eq_some_iff hBM).1 hold₁
  have hp₂ : HasPaint BM x₂ x₃ c₂ := (inducedColor_eq_some_iff hBM).1 hold₂
  have hp₃ : HasPaint BM x₃ x₀ c₃ := (inducedColor_eq_some_iff hBM).1 hold₃
  by_contra hnot
  have hcard : ({c₀, c₁, c₂, c₃} : Finset (Fin k)).card < 3 :=
    Nat.lt_of_not_ge hnot
  have hn₀₁ : c₀ ≠ c₁ :=
    cycle_adjacent_colors_ne hBM hD hp₀ hp₁ hp₂ hp₃ hcard
  have hD₁ : FourDistinct x₁ x₂ x₃ x₀ := by
    unfold FourDistinct at hD ⊢
    aesop
  have hcard₁ : ({c₁, c₂, c₃, c₀} : Finset (Fin k)).card < 3 := by
    have heq : ({c₁, c₂, c₃, c₀} : Finset (Fin k)) = {c₀, c₁, c₂, c₃} := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [heq]
    exact hcard
  have hn₁₂ : c₁ ≠ c₂ :=
    cycle_adjacent_colors_ne hBM hD₁ hp₁ hp₂ hp₃ hp₀ hcard₁
  have hD₂ : FourDistinct x₂ x₃ x₀ x₁ := by
    unfold FourDistinct at hD ⊢
    aesop
  have hcard₂ : ({c₂, c₃, c₀, c₁} : Finset (Fin k)).card < 3 := by
    have heq : ({c₂, c₃, c₀, c₁} : Finset (Fin k)) = {c₀, c₁, c₂, c₃} := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [heq]
    exact hcard
  have hn₂₃ : c₂ ≠ c₃ :=
    cycle_adjacent_colors_ne hBM hD₂ hp₂ hp₃ hp₀ hp₁ hcard₂
  have hD₃ : FourDistinct x₃ x₀ x₁ x₂ := by
    unfold FourDistinct at hD ⊢
    aesop
  have hcard₃ : ({c₃, c₀, c₁, c₂} : Finset (Fin k)).card < 3 := by
    have heq : ({c₃, c₀, c₁, c₂} : Finset (Fin k)) = {c₀, c₁, c₂, c₃} := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [heq]
    exact hcard
  have hn₃₀ : c₃ ≠ c₀ :=
    cycle_adjacent_colors_ne hBM hD₃ hp₃ hp₀ hp₁ hp₂ hcard₃
  have hop₀₂ : c₀ = c₂ :=
    opposite_eq_of_fourColor_card_lt_three hn₀₁ hn₁₂ hcard
  have hop₁₃ : c₁ = c₃ :=
    opposite_eq_of_fourColor_card_lt_three hn₁₂ hn₂₃ hcard₁
  subst c₂
  subst c₃
  obtain ⟨b₀, hb₀, hpb₀⟩ := hp₀
  obtain ⟨b₁, hb₁, hpb₁⟩ := hp₁
  obtain ⟨b₂, hb₂, hpb₂⟩ := hp₂
  obtain ⟨b₃, hb₃, hpb₃⟩ := hp₃
  have hb₀₁ : b₀ ≠ b₁ := alternating_adjacent_blocks_ne hBM hD hn₀₁
    hb₀ hb₁ hpb₀ hpb₁ ⟨b₂, hb₂, hpb₂⟩ ⟨b₃, hb₃, hpb₃⟩
  have hb₁₂ : b₁ ≠ b₂ := alternating_adjacent_blocks_ne hBM hD₁ hn₀₁.symm
    hb₁ hb₂ hpb₁ hpb₂ ⟨b₃, hb₃, hpb₃⟩ ⟨b₀, hb₀, hpb₀⟩
  have hb₂₃ : b₂ ≠ b₃ := alternating_adjacent_blocks_ne hBM hD₂ hn₀₁
    hb₂ hb₃ hpb₂ hpb₃ ⟨b₀, hb₀, hpb₀⟩ ⟨b₁, hb₁, hpb₁⟩
  have hb₃₀ : b₃ ≠ b₀ := alternating_adjacent_blocks_ne hBM hD₃ hn₀₁.symm
    hb₃ hb₀ hpb₃ hpb₀ ⟨b₁, hb₁, hpb₁⟩ ⟨b₂, hb₂, hpb₂⟩
  have hb₀₂ : b₀ ≠ b₂ := by
    intro h
    subst b₂
    exact b₀.no_disjoint_painted_edges hD hpb₀ hpb₂
  have hb₁₃ : b₁ ≠ b₃ := by
    intro h
    subst b₃
    exact b₁.no_disjoint_painted_edges hD₁ hpb₁ hpb₃
  have hs₀₁ := auxSupports_ne_of_blocks_ne hBM hb₀ hb₁ hb₀₁
  have hs₀₂ := auxSupports_ne_of_blocks_ne hBM hb₀ hb₂ hb₀₂
  have hs₀₃ := auxSupports_ne_of_blocks_ne hBM hb₀ hb₃ hb₃₀.symm
  have hs₁₂ := auxSupports_ne_of_blocks_ne hBM hb₁ hb₂ hb₁₂
  have hs₁₃ := auxSupports_ne_of_blocks_ne hBM hb₁ hb₃ hb₁₃
  have hs₂₃ := auxSupports_ne_of_blocks_ne hBM hb₂ hb₃ hb₂₃
  have hsupp := blocksOfAuxFamily_supports candidates R MH hmatch.1
  have hs₀ : b₀.auxSupport ∈ MH := by
    rw [← hsupp]
    exact Finset.mem_image.2 ⟨b₀, hb₀, rfl⟩
  have hs₁ : b₁.auxSupport ∈ MH := by
    rw [← hsupp]
    exact Finset.mem_image.2 ⟨b₁, hb₁, rfl⟩
  have hs₂ : b₂.auxSupport ∈ MH := by
    rw [← hsupp]
    exact Finset.mem_image.2 ⟨b₂, hb₂, rfl⟩
  have hs₃ : b₃.auxSupport ∈ MH := by
    rw [← hsupp]
    exact Finset.mem_image.2 ⟨b₃, hb₃, rfl⟩
  let Q : Hypergraph (AuxVertex n k) :=
    {b₀.auxSupport, b₁.auxSupport, b₂.auxSupport, b₃.auxSupport}
  have hQcard : Q.card = 4 := by
    dsimp [Q]
    simp [hs₀₁, hs₀₂, hs₀₃, hs₁₂, hs₁₃, hs₂₃]
  have hQsub : Q ⊆ MH := by
    intro e he
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hs₀
    · exact hs₁
    · exact hs₂
    · exact hs₃
  have hQpow : Q ∈ (auxiliaryHypergraph candidates R).powersetCard 4 :=
    Finset.mem_powersetCard.2 ⟨hQsub.trans hmatch.1, hQcard⟩
  have hQalt : IsAlternatingCycleConflict Q :=
    ⟨x₀, x₁, x₂, x₃, c₀, c₁, b₀, b₁, b₂, b₃,
      hD, hn₀₁, hpb₀, hpb₁, hpb₂, hpb₃, rfl⟩
  have hQconf : Q ∈ alternatingCycleConflicts candidates R := by
    exact Finset.mem_filter.2 ⟨hQpow, hQalt⟩
  exact (hfree Q hQconf) hQsub

/-- The number of uncoloured neighbours of a vertex. -/
def leaveDegree {n k : ℕ} (old : Fin n → Fin n → Option (Fin k))
    (x : Fin n) : ℕ :=
  (Finset.univ.filter fun y => y ≠ x ∧ old x y = none).card

/-- (P4): the leave has maximum degree at most `B`. -/
def LeaveMaxDegree {n k : ℕ} (B : ℕ)
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ∀ x, leaveDegree old x ≤ B

/-- The canonical orientation of a leave edge which is an obstruction for
the ordered base edge `xy` in (P5).  Both possible cross orderings are
included. -/
def IsCrossObstruction {n k : ℕ} (old : Fin n → Fin n → Option (Fin k))
    (x y : Fin n) (p : Fin n × Fin n) : Prop :=
  p.1 < p.2 ∧ p.1 ≠ x ∧ p.1 ≠ y ∧ p.2 ≠ x ∧ p.2 ≠ y ∧
    old p.1 p.2 = none ∧
    ∃ c, (old x p.1 = some c ∧ old y p.2 = some c) ∨
      (old x p.2 = some c ∧ old y p.1 = some c)

/-- The finite set counted in (P5); the order condition counts each leave
edge exactly once. -/
def crossObstructions {n k : ℕ} (old : Fin n → Fin n → Option (Fin k))
    (x y : Fin n) : Finset (Fin n × Fin n) :=
  by
    classical
    exact Finset.univ.filter (IsCrossObstruction old x y)

/-- (P5): the tracked cross-leave obstruction count is uniformly small. -/
def CrossLeaveBound {n k : ℕ} (B : ℕ)
    (old : Fin n → Fin n → Option (Fin k)) : Prop :=
  ∀ x y, x ≠ y → (crossObstructions old x y).card ≤ B

/-- The complete output of the quantitative partial-colouring theorem.
The explicit block closure is deliberately a field, rather than an
existential consequence of (P1)--(P5). -/
structure PartialGood (n k B : ℕ) where
  old : Fin n → Fin n → Option (Fin k)
  blocks : Finset (TriangleBlock n k)
  symmetric : ∀ x y, old x y = old y x
  diagonal : ∀ x, old x x = none
  p0 : BlockClosure blocks old
  p1 : ColorClassesAreEdgesOrPaths blocks old
  p2 : MateIsolated blocks old
  p3 : OldFourCyclesUseThree old
  p4 : LeaveMaxDegree B old
  p5 : CrossLeaveBound B old

/-! ## Adapter to the deterministic completion module -/

/-- The block type exported to `Completion` contains exactly the selected
blocks, not all candidate triangles. -/
abbrev SelectedBlock {n k B : ℕ} (P : PartialGood n k B) :=
  {b : TriangleBlock n k // b ∈ P.blocks}

/-- Forget the construction-specific ordering proof and expose a selected
block through the completion module's generic block type. -/
def completionBlock {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) : Completion.TriangleBlock (Fin n) (Fin k) where
  apex := b.1.apex
  left := b.1.left
  right := b.1.right
  apex_ne_left := b.1.apex_ne_left
  apex_ne_right := b.1.apex_ne_right
  left_ne_right := b.1.left_ne_right
  pathColor := b.1.repeated
  mateColor := b.1.singleton
  colors_ne := b.1.colors_ne

/-- Regard the symmetric two-argument old colouring as an exact complete
graph edge labelling. -/
def completionOld {n k B : ℕ} (P : PartialGood n k B) :
    SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k)) :=
  fun e => Sym2.lift ⟨P.old, P.symmetric⟩ e.1

@[simp] theorem completionOld_topEdge {n k B : ℕ} (P : PartialGood n k B)
    (x y : Fin n) (hxy : x ≠ y) :
    completionOld P (Completion.topEdge x y hxy) = P.old x y := rfl

/-- Choose the selected block owning an old edge, when it has one. -/
def completionOwner {n k B : ℕ} (P : PartialGood n k B)
    (e : Completion.Edge (Fin n)) : Option (SelectedBlock P) := by
  classical
  exact if h : Nonempty {b : SelectedBlock P // e.1 ∈ b.val.graphEdges}
    then some h.some.1 else none

theorem completionBlock_supports_iff {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) (e : Completion.Edge (Fin n)) :
    (completionBlock P b).Supports e ↔ e.1 ∈ b.1.graphEdges := by
  simp only [Completion.TriangleBlock.Supports, completionBlock,
    TriangleBlock.graphEdges, Finset.mem_insert, Finset.mem_singleton]

theorem completionOwner_eq_some_iff {n k B : ℕ} (P : PartialGood n k B)
    (e : Completion.Edge (Fin n)) (b : SelectedBlock P) :
    completionOwner P e = some b ↔ e.1 ∈ b.1.graphEdges := by
  classical
  unfold completionOwner
  split_ifs with h
  · constructor
    · intro heq
      have hb : h.some.1 = b := Option.some.inj heq
      simpa [hb] using h.some.2
    · intro hb
      congr 1
      apply Subtype.ext
      by_contra hne
      have hd := P.p0.1 h.some.1.2 b.2 hne
      change Disjoint h.some.1.1.graphEdges b.1.graphEdges at hd
      rw [Finset.disjoint_left] at hd
      exact (hd h.some.2) hb
  · constructor
    · simp
    · intro hb
      exact (h ⟨⟨b, hb⟩⟩).elim

theorem completionOwner_iff_support {n k B : ℕ} (P : PartialGood n k B)
    (e : Completion.Edge (Fin n)) (b : SelectedBlock P) :
    completionOwner P e = some b ↔ (completionBlock P b).Supports e := by
  rw [completionOwner_eq_some_iff, completionBlock_supports_iff]

theorem completion_edgeColor_of_paints {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) {x y : Fin n} {c : Fin k} (hxy : x ≠ y)
    (hp : b.1.Paints x y c) :
    (completionBlock P b).edgeColor (Completion.topEdge x y hxy) = c := by
  rw [Completion.TriangleBlock.edgeColor]
  rcases hp with (⟨he, rfl⟩ | ⟨he, rfl⟩)
  · have hpos :
        (Completion.topEdge x y hxy).1 =
            s((completionBlock P b).apex, (completionBlock P b).left) ∨
          (Completion.topEdge x y hxy).1 =
            s((completionBlock P b).apex, (completionBlock P b).right) := by
      simpa [Completion.topEdge, completionBlock] using he
    rw [if_pos hpos]
    rfl
  · have hneg : ¬((Completion.topEdge x y hxy).1 =
            s((completionBlock P b).apex, (completionBlock P b).left) ∨
          (Completion.topEdge x y hxy).1 =
            s((completionBlock P b).apex, (completionBlock P b).right)) := by
      intro h
      simp only [Completion.topEdge, completionBlock] at h
      rcases h with h | h
      · have hbad := h.symm.trans he
        simpa [Sym2.eq_iff, b.1.apex_ne_left, b.1.apex_ne_right] using hbad
      · have hbad := h.symm.trans he
        simpa [Sym2.eq_iff, b.1.apex_ne_left, b.1.apex_ne_right,
          b.1.left_ne_right] using hbad
    rw [if_neg hneg]
    rfl

theorem completionOld_eq_owner {n k B : ℕ} (P : PartialGood n k B)
    (e : Completion.Edge (Fin n)) :
    completionOld P e = (completionOwner P e).map fun b =>
      (completionBlock P b).edgeColor e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by simpa using he
      change P.old x y = (completionOwner P ⟨s(x, y), he⟩).map fun b =>
        (completionBlock P b).edgeColor ⟨s(x, y), he⟩
      by_cases hpaint : ∃ c, HasPaint P.blocks x y c
      · obtain ⟨c, b, hb, hp⟩ := hpaint
        have hold : P.old x y = some c := (P.p0.2 x y c).2 ⟨b, hb, hp⟩
        let bs : SelectedBlock P := ⟨b, hb⟩
        have howner : completionOwner P ⟨s(x, y), he⟩ = some bs := by
          apply (completionOwner_eq_some_iff P ⟨s(x, y), he⟩ bs).2
          exact b.paints_supports hp
        rw [hold, howner]
        simp only [Option.map_some, Option.some.injEq]
        have hedge : Completion.topEdge x y hxy =
            (⟨s(x, y), he⟩ : Completion.Edge (Fin n)) := Subtype.ext rfl
        rw [← hedge]
        exact (completion_edgeColor_of_paints P bs hxy hp).symm
      · have hold : P.old x y = none := by
          apply Option.eq_none_iff_forall_not_mem.2
          intro c hc
          have hc' : P.old x y = some c := Option.mem_def.1 hc
          exact hpaint ⟨c, (P.p0.2 x y c).1 hc'⟩
        have howner : completionOwner P ⟨s(x, y), he⟩ = none := by
          apply Option.eq_none_iff_forall_not_mem.2
          intro b hbmem
          have hbEq : completionOwner P ⟨s(x, y), he⟩ = some b :=
            Option.mem_def.1 hbmem
          have hsupp : b.1.Supports x y :=
            (completionOwner_eq_some_iff P ⟨s(x, y), he⟩ b).1 hbEq
          obtain ⟨c, hp⟩ := b.1.support_has_color hsupp
          exact hpaint ⟨c, b.1, b.2, hp⟩
        rw [hold, howner]
        rfl

theorem completion_same_old_path_same_owner {n k B : ℕ}
    (P : PartialGood n k B) (x y z : Fin n)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (c : Fin k)
    (h₁ : completionOld P (Completion.topEdge x y hxy) = some c)
    (h₂ : completionOld P (Completion.topEdge y z hyz) = some c) :
    completionOwner P (Completion.topEdge x y hxy) =
      completionOwner P (Completion.topEdge y z hyz) := by
  have hyx : P.old y x = some c := (P.symmetric x y).symm.trans (by simpa using h₁)
  have hyz' : P.old y z = some c := by simpa using h₂
  have hp := P.p1 c y x z hyx hyz'
  obtain ⟨b, hb, hp₁, hp₂⟩ := hp
  let bs : SelectedBlock P := ⟨b, hb⟩
  have ho₁ : completionOwner P (Completion.topEdge x y hxy) = some bs := by
    apply (completionOwner_eq_some_iff P _ bs).2
    exact b.paints_supports (TriangleBlock.paints_symm b hp₁)
  have ho₂ : completionOwner P (Completion.topEdge y z hyz) = some bs := by
    apply (completionOwner_eq_some_iff P _ bs).2
    exact b.paints_supports hp₂
  rw [ho₁, ho₂]

theorem completion_mate_isolated_apex {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) (t : Fin n) (h : (completionBlock P b).apex ≠ t) :
    completionOld P (Completion.topEdge (completionBlock P b).apex t h) ≠
      some (completionBlock P b).mateColor := by
  exact (P.p2 b.1 b.2).1 t

theorem completion_mate_isolated_left {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) (t : Fin n) (h : (completionBlock P b).left ≠ t)
    (hcol : completionOld P (Completion.topEdge (completionBlock P b).left t h) =
      some (completionBlock P b).mateColor) : t = (completionBlock P b).right := by
  have he := (P.p2 b.1 b.2).2.1 t (by simpa [completionBlock] using hcol)
  exact Sym2.congr_right.mp he

theorem completion_mate_isolated_right {n k B : ℕ} (P : PartialGood n k B)
    (b : SelectedBlock P) (t : Fin n) (h : (completionBlock P b).right ≠ t)
    (hcol : completionOld P (Completion.topEdge (completionBlock P b).right t h) =
      some (completionBlock P b).mateColor) : t = (completionBlock P b).left := by
  have he := (P.p2 b.1 b.2).2.2 t (by simpa [completionBlock] using hcol)
  have he' : s(b.1.right, t) = s(b.1.right, b.1.left) :=
    he.trans (Sym2.eq_swap (a := b.1.left) (b := b.1.right))
  exact Sym2.congr_right.mp he'

/-- The block ownership/decomposition part of the completion interface. -/
def toCompletionDecomposition {n k B : ℕ} (P : PartialGood n k B) :
    Completion.TriangleBlockDecomposition (Fin n) (Fin k) (SelectedBlock P) where
  old := completionOld P
  block := completionBlock P
  owner := completionOwner P
  owner_iff_support := completionOwner_iff_support P
  old_eq_owner := completionOld_eq_owner P
  same_old_path_same_owner := completion_same_old_path_same_owner P
  mate_isolated_at_apex := completion_mate_isolated_apex P
  mate_isolated_at_left := completion_mate_isolated_left P
  mate_isolated_at_right := completion_mate_isolated_right P

/-! ### The two local multiplicity consequences -/

/-- Two labelled edges of `K₄` meet when they have a common endpoint. -/
def Edge4Meet (e f : Completion.Edge4) : Prop :=
  ∃ x : Fin 4, x ∈ e.1 ∧ x ∈ f.1

/-- Any three different edges on four vertices can be ordered as a
two-edge path together with a third edge meeting that path.  This is the
small, closed finite fact behind the old-colour multiplicity bound. -/
theorem edge4_three_edge_chain (e f g : Completion.Edge4)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (Edge4Meet e f ∧ (Edge4Meet g e ∨ Edge4Meet g f)) ∨
    (Edge4Meet e g ∧ (Edge4Meet f e ∨ Edge4Meet f g)) ∨
    (Edge4Meet f g ∧ (Edge4Meet e f ∨ Edge4Meet e g)) := by
  rcases Completion.edge4_cases e with h | h | h | h | h | h <;> subst e <;>
    rcases Completion.edge4_cases f with h | h | h | h | h | h <;> subst f <;>
    rcases Completion.edge4_cases g with h | h | h | h | h | h <;> subst g <;>
    simp_all [Edge4Meet, Completion.edge01, Completion.edge02, Completion.edge03,
      Completion.edge12, Completion.edge13, Completion.edge23, Completion.topEdge,
      Sym2.mem_iff]

theorem edge4_exists_other (e : Completion.Edge4) {x : Fin 4}
    (hx : x ∈ e.1) : ∃ y : Fin 4, x ≠ y ∧ e.1 = s(x, y) := by
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.1 hx
  refine ⟨y, ?_, hy⟩
  intro hxy
  subst y
  have he := e.2
  simpa [hy] using he

@[simp] theorem completion_pullOld_topEdge {n k B : ℕ}
    (P : PartialGood n k B) (v : Fin 4 ↪ Fin n)
    (x y : Fin 4) (hxy : x ≠ y) :
    Completion.pullOld (completionOld P) v (Completion.topEdge x y hxy) =
      P.old (v x) (v y) := by
  rfl

theorem old_of_pullOld_of_edge_eq {n k B : ℕ} (P : PartialGood n k B)
    (v : Fin 4 ↪ Fin n) (e : Completion.Edge4) {x y : Fin 4} {c : Fin k}
    (hxy : x ≠ y) (he : e.1 = s(x, y))
    (hc : Completion.pullOld (completionOld P) v e = some c) :
    P.old (v x) (v y) = some c := by
  have heq : e = Completion.topEdge x y hxy := Subtype.ext he
  rw [heq] at hc
  simpa using hc

theorem local_edges_ne_of_distinct_colors {n k B : ℕ} (P : PartialGood n k B)
    (v : Fin 4 ↪ Fin n) {c d : Fin k} (hcd : c ≠ d)
    {e f : Completion.Edge4}
    (he : Completion.pullOld (completionOld P) v e = some c)
    (hf : Completion.pullOld (completionOld P) v f = some d) : e ≠ f := by
  intro hef
  subst f
  exact hcd (Option.some.inj (he.symm.trans hf))

theorem PartialGood.blocks_eq_of_paints {n k B : ℕ}
    (P : PartialGood n k B) {b b' : TriangleBlock n k}
    (hb : b ∈ P.blocks) (hb' : b' ∈ P.blocks)
    {x y u v : Fin n} {c d : Fin k}
    (hp : b.Paints x y c) (hp' : b'.Paints u v d)
    (hedge : s(x, y) = s(u, v)) : b = b' := by
  by_contra hne
  have hd := P.p0.1 hb hb' hne
  change Disjoint b.graphEdges b'.graphEdges at hd
  rw [Finset.disjoint_left] at hd
  exact (hd (b.paints_supports hp) (hedge ▸ b'.paints_supports hp')).elim

theorem PartialGood.blocks_eq_of_supports {n k B : ℕ}
    (P : PartialGood n k B) {b b' : TriangleBlock n k}
    (hb : b ∈ P.blocks) (hb' : b' ∈ P.blocks)
    {e : Sym2 (Fin n)} (he : e ∈ b.graphEdges) (he' : e ∈ b'.graphEdges) :
    b = b' := by
  by_contra hne
  have hd := P.p0.1 hb hb' hne
  change Disjoint b.graphEdges b'.graphEdges at hd
  exact (Finset.disjoint_left.1 hd he he').elim

/-- One triangle block has only two edges of any fixed colour. -/
theorem TriangleBlock.not_three_distinct_sameColor {n k : ℕ}
    (b : TriangleBlock n k)
    {x₁ y₁ x₂ y₂ x₃ y₃ : Fin n} {c : Fin k}
    (h₁ : b.Paints x₁ y₁ c) (h₂ : b.Paints x₂ y₂ c)
    (h₃ : b.Paints x₃ y₃ c)
    (h₁₂ : s(x₁, y₁) ≠ s(x₂, y₂))
    (h₁₃ : s(x₁, y₁) ≠ s(x₃, y₃))
    (h₂₃ : s(x₂, y₂) ≠ s(x₃, y₃)) : False := by
  simp only [Paints] at h₁ h₂ h₃
  rcases h₁ with (⟨h₁, hc₁⟩ | ⟨h₁, hc₁⟩) <;>
    rcases h₂ with (⟨h₂, hc₂⟩ | ⟨h₂, hc₂⟩) <;>
    rcases h₃ with (⟨h₃, hc₃⟩ | ⟨h₃, hc₃⟩)
  · rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
      rcases h₃ with h₃ | h₃ <;> aesop
  · exact b.colors_ne (hc₁.symm.trans hc₃)
  · exact b.colors_ne (hc₁.symm.trans hc₂)
  · exact b.colors_ne (hc₁.symm.trans hc₂)
  · exact b.colors_ne (hc₂.symm.trans hc₁)
  · exact b.colors_ne (hc₂.symm.trans hc₁)
  · exact b.colors_ne (hc₃.symm.trans hc₁)
  · exact h₁₂ (h₁.trans h₂.symm)

theorem TriangleBlock.apex_eq_of_sameColor_path {n k : ℕ}
    (b : TriangleBlock n k) {x y z : Fin n} {c : Fin k}
    (hxy : b.Paints x y c) (hxz : b.Paints x z c) (hyz : y ≠ z) :
    x = b.apex := by
  rcases hxy with (⟨hxy, hc⟩ | ⟨hxy, hc⟩) <;>
    rcases hxz with (⟨hxz, hc'⟩ | ⟨hxz, hc'⟩)
  · rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz <;>
      rw [Sym2.eq_iff] at hxy hxz <;> aesop
  · exact (b.colors_ne (hc.symm.trans hc')).elim
  · exact (b.colors_ne (hc'.symm.trans hc)).elim
  · have he : s(x, y) = s(x, z) := hxy.trans hxz.symm
    exact (hyz (Sym2.congr_right.mp he)).elim

theorem TriangleBlock.not_four_distinct_supported {n k : ℕ}
    (b : TriangleBlock n k)
    {e₁ e₂ e₃ e₄ : Sym2 (Fin n)}
    (h₁ : e₁ ∈ b.graphEdges) (h₂ : e₂ ∈ b.graphEdges)
    (h₃ : e₃ ∈ b.graphEdges) (h₄ : e₄ ∈ b.graphEdges)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₁₄ : e₁ ≠ e₄)
    (h₂₃ : e₂ ≠ e₃) (h₂₄ : e₂ ≠ e₄) (h₃₄ : e₃ ≠ e₄) : False := by
  have hsub : ({e₁, e₂, e₃, e₄} : Finset (Sym2 (Fin n))) ⊆ b.graphEdges := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨h₁, h₂, h₃, h₄⟩
  have hcard := Finset.card_le_card hsub
  have hfour : ({e₁, e₂, e₃, e₄} : Finset (Sym2 (Fin n))).card = 4 := by
    simp [h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]
  rw [hfour, b.graphEdges_card] at hcard
  omega

theorem mapped_edge_ne_of_ne {n : ℕ} (v : Fin 4 ↪ Fin n)
    {e f : Completion.Edge4} {x y u z : Fin 4}
    (he : e.1 = s(x, y)) (hf : f.1 = s(u, z)) (hne : e ≠ f) :
    s(v x, v y) ≠ s(v u, v z) := by
  intro h
  apply hne
  apply Subtype.ext
  rw [he, hf]
  apply Sym2.map.injective v.injective
  simpa using h

/-- Three distinct local edges forming a connected three-edge graph cannot
all receive one old colour.  The first meeting pair belongs to one block;
the second meeting forces the third edge into that same block. -/
theorem partialGood_no_three_chain {n k B : ℕ} (P : PartialGood n k B)
    (v : Fin 4 ↪ Fin n) (c : Fin k)
    (e f g : Completion.Edge4)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hec : Completion.pullOld (completionOld P) v e = some c)
    (hfc : Completion.pullOld (completionOld P) v f = some c)
    (hgc : Completion.pullOld (completionOld P) v g = some c)
    (hefMeet : Edge4Meet e f)
    (hgMeet : Edge4Meet g e ∨ Edge4Meet g f) : False := by
  obtain ⟨x, hxe, hxf⟩ := hefMeet
  obtain ⟨y, hxy, hey⟩ := edge4_exists_other e hxe
  obtain ⟨z, hxz, hfz⟩ := edge4_exists_other f hxf
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact hef (Subtype.ext (hey.trans hfz.symm))
  have hec' : P.old (v x) (v y) = some c := by
    have heq : e = Completion.topEdge x y hxy := Subtype.ext hey
    rw [heq] at hec
    simpa using hec
  have hfc' : P.old (v x) (v z) = some c := by
    have heq : f = Completion.topEdge x z hxz := Subtype.ext hfz
    rw [heq] at hfc
    simpa using hfc
  obtain ⟨b, hb, hbe, hbf⟩ := P.p1 c (v x) (v y) (v z) hec' hfc'
  rcases hgMeet with hge | hgf
  · obtain ⟨q, hqg, hqe⟩ := hge
    obtain ⟨r, hqr, hgr⟩ := edge4_exists_other g hqg
    obtain ⟨t, hqt, het⟩ := edge4_exists_other e hqe
    have hrt : r ≠ t := by
      intro hrt
      subst t
      exact heg (Subtype.ext (het.trans hgr.symm))
    have hgc' : P.old (v q) (v r) = some c := by
      have heq : g = Completion.topEdge q r hqr := Subtype.ext hgr
      rw [heq] at hgc
      simpa using hgc
    have hec'' : P.old (v q) (v t) = some c := by
      have heq : e = Completion.topEdge q t hqt := Subtype.ext het
      rw [heq] at hec
      simpa using hec
    obtain ⟨b', hb', hbg, hbe'⟩ := P.p1 c (v q) (v r) (v t) hgc' hec''
    have hbb' : b = b' := P.blocks_eq_of_paints hb hb' hbe hbe'
      (by simpa only [Sym2.map_mk] using
        congrArg (Sym2.map v) (hey.symm.trans het))
    subst b'
    exact b.not_three_distinct_sameColor hbe hbf hbg
      (mapped_edge_ne_of_ne v hey hfz hef)
      (mapped_edge_ne_of_ne v hey hgr heg)
      (mapped_edge_ne_of_ne v hfz hgr hfg)
  · obtain ⟨q, hqg, hqf⟩ := hgf
    obtain ⟨r, hqr, hgr⟩ := edge4_exists_other g hqg
    obtain ⟨t, hqt, hft⟩ := edge4_exists_other f hqf
    have hrt : r ≠ t := by
      intro hrt
      subst t
      exact hfg (Subtype.ext (hft.trans hgr.symm))
    have hgc' : P.old (v q) (v r) = some c := by
      have heq : g = Completion.topEdge q r hqr := Subtype.ext hgr
      rw [heq] at hgc
      simpa using hgc
    have hfc'' : P.old (v q) (v t) = some c := by
      have heq : f = Completion.topEdge q t hqt := Subtype.ext hft
      rw [heq] at hfc
      simpa using hfc
    obtain ⟨b', hb', hbg, hbf'⟩ := P.p1 c (v q) (v r) (v t) hgc' hfc''
    have hbb' : b = b' := P.blocks_eq_of_paints hb hb' hbf hbf'
      (by simpa only [Sym2.map_mk] using
        congrArg (Sym2.map v) (hfz.symm.trans hft))
    subst b'
    exact b.not_three_distinct_sameColor hbe hbf hbg
      (mapped_edge_ne_of_ne v hey hfz hef)
      (mapped_edge_ne_of_ne v hey hgr heg)
      (mapped_edge_ne_of_ne v hfz hgr hfg)

theorem completion_oldAtMostTwoOnK4 {n k B : ℕ} (P : PartialGood n k B) :
    ∀ (v : Fin 4 ↪ Fin n) (c : Fin k),
      (Completion.fiber (Completion.pullOld (completionOld P) v) (some c)).card ≤ 2 := by
  intro v c
  apply Completion.card_fiber_le_two_of_no_three
  intro e f g hef heg hfg hec hfc hgc
  rcases edge4_three_edge_chain e f g hef heg hfg with h | h | h
  · exact partialGood_no_three_chain P v c e f g hef heg hfg hec hfc hgc h.1 h.2
  · exact partialGood_no_three_chain P v c e g f heg hef hfg.symm hec hgc hfc h.1 h.2
  · exact partialGood_no_three_chain P v c f g e hfg hef.symm heg.symm hfc hgc hec h.1 h.2

/-- Two three-element subsets of a four-element type share two different
vertices.  It is kept in this elementary membership form for the path--path
case below. -/
theorem fin4_triples_share_edge (x y z u w t : Fin 4)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (huw : u ≠ w) (hut : u ≠ t) (hwt : w ≠ t) :
    ∃ p q : Fin 4, p ≠ q ∧
      (p = x ∨ p = y ∨ p = z) ∧ (q = x ∨ q = y ∨ q = z) ∧
      (p = u ∨ p = w ∨ p = t) ∧ (q = u ∨ q = w ∨ q = t) := by
  revert x y z u w t
  decide

theorem TriangleBlock.supports_pair_of_triangle_vertices {n k : ℕ}
    (b : TriangleBlock n k) {x y z p q : Fin n} {c : Fin k}
    (hxy : b.Paints x y c) (hxz : b.Paints x z c) (hyz : y ≠ z)
    (hpq : p ≠ q)
    (hp : p = x ∨ p = y ∨ p = z) (hq : q = x ∨ q = y ∨ q = z) :
    s(p, q) ∈ b.graphEdges := by
  have h₁ : b.Supports x y := b.paints_supports hxy
  have h₂ : b.Supports x z := b.paints_supports hxz
  have h₃ : b.Supports y z := b.closes_supported_path h₁ h₂ hyz
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals try { exact (hpq rfl).elim }
  all_goals simp_all only [Supports, Sym2.eq_swap]

/-- A matching avoiding two incident edges consists of their closing chord
and the edge from the common endpoint to the fourth vertex. -/
theorem edge4_matching01_23_avoiding_path {x y z : Fin 4}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : (Completion.edge01 : Completion.Edge4).1 ≠ s(x, y))
    (h₂ : (Completion.edge01 : Completion.Edge4).1 ≠ s(x, z))
    (h₃ : (Completion.edge23 : Completion.Edge4).1 ≠ s(x, y))
    (h₄ : (Completion.edge23 : Completion.Edge4).1 ≠ s(x, z)) :
    ((Completion.edge01 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge23 : Completion.Edge4).1) ∨
      ((Completion.edge23 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge01 : Completion.Edge4).1) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [Completion.edge01, Completion.edge23, Completion.topEdge,
      Sym2.mem_iff, Sym2.eq_iff]

theorem edge4_matching02_13_avoiding_path {x y z : Fin 4}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : (Completion.edge02 : Completion.Edge4).1 ≠ s(x, y))
    (h₂ : (Completion.edge02 : Completion.Edge4).1 ≠ s(x, z))
    (h₃ : (Completion.edge13 : Completion.Edge4).1 ≠ s(x, y))
    (h₄ : (Completion.edge13 : Completion.Edge4).1 ≠ s(x, z)) :
    ((Completion.edge02 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge13 : Completion.Edge4).1) ∨
      ((Completion.edge13 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge02 : Completion.Edge4).1) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [Completion.edge02, Completion.edge13, Completion.topEdge,
      Sym2.mem_iff, Sym2.eq_iff]

theorem edge4_matching03_12_avoiding_path {x y z : Fin 4}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : (Completion.edge03 : Completion.Edge4).1 ≠ s(x, y))
    (h₂ : (Completion.edge03 : Completion.Edge4).1 ≠ s(x, z))
    (h₃ : (Completion.edge12 : Completion.Edge4).1 ≠ s(x, y))
    (h₄ : (Completion.edge12 : Completion.Edge4).1 ≠ s(x, z)) :
    ((Completion.edge03 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge12 : Completion.Edge4).1) ∨
      ((Completion.edge12 : Completion.Edge4).1 = s(y, z) ∧
        x ∈ (Completion.edge03 : Completion.Edge4).1) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [Completion.edge03, Completion.edge12, Completion.topEdge,
      Sym2.mem_iff, Sym2.eq_iff]

theorem edge4_matching_avoiding_path
    {e f g h : Completion.Edge4} {x y z : Fin 4}
    (he : e.1 = s(x, y)) (hf : f.1 = s(x, z))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hge : g ≠ e) (hgf : g ≠ f) (hhe : h ≠ e) (hhf : h ≠ f)
    (hgh : g ≠ h) (hm : Completion.IsMatchingPair g h) :
    (g.1 = s(y, z) ∧ x ∈ h.1) ∨ (h.1 = s(y, z) ∧ x ∈ g.1) := by
  have hge' : g.1 ≠ e.1 := fun h' => hge (Subtype.ext h')
  have hgf' : g.1 ≠ f.1 := fun h' => hgf (Subtype.ext h')
  have hhe' : h.1 ≠ e.1 := fun h' => hhe (Subtype.ext h')
  have hhf' : h.1 ≠ f.1 := fun h' => hhf (Subtype.ext h')
  have hgxy : g.1 ≠ s(x, y) := fun h' => hge' (h'.trans he.symm)
  have hgxz : g.1 ≠ s(x, z) := fun h' => hgf' (h'.trans hf.symm)
  have hhxy : h.1 ≠ s(x, y) := fun h' => hhe' (h'.trans he.symm)
  have hhxz : h.1 ≠ s(x, z) := fun h' => hhf' (h'.trans hf.symm)
  clear e f he hf hge hgf hhe hhf hge' hgf' hhe' hhf'
  rcases (Completion.matchingPair_cases hgh).1 hm with h' | h' | h' | h' | h' | h'
  · rcases h' with ⟨rfl, rfl⟩
    exact edge4_matching01_23_avoiding_path hxy hxz hyz hgxy hgxz hhxy hhxz
  · rcases h' with ⟨rfl, rfl⟩
    simpa [or_comm, and_comm] using
      edge4_matching01_23_avoiding_path hxy hxz hyz hhxy hhxz hgxy hgxz
  · rcases h' with ⟨rfl, rfl⟩
    exact edge4_matching02_13_avoiding_path hxy hxz hyz hgxy hgxz hhxy hhxz
  · rcases h' with ⟨rfl, rfl⟩
    simpa [or_comm, and_comm] using
      edge4_matching02_13_avoiding_path hxy hxz hyz hhxy hhxz hgxy hgxz
  · rcases h' with ⟨rfl, rfl⟩
    exact edge4_matching03_12_avoiding_path hxy hxz hyz hgxy hgxz hhxy hhxz
  · rcases h' with ⟨rfl, rfl⟩
    simpa [or_comm, and_comm] using
      edge4_matching03_12_avoiding_path hxy hxz hyz hhxy hhxz hgxy hgxz

theorem partialGood_path_matching_contra {n k B : ℕ} (P : PartialGood n k B)
    (v : Fin 4 ↪ Fin n) {c d : Fin k} (hcd : c ≠ d)
    (e f g h : Completion.Edge4)
    (hef : e ≠ f) (hgh : g ≠ h)
    (hnm : ¬ Completion.IsMatchingPair e f)
    (hm : Completion.IsMatchingPair g h)
    (hec : Completion.pullOld (completionOld P) v e = some c)
    (hfc : Completion.pullOld (completionOld P) v f = some c)
    (hgd : Completion.pullOld (completionOld P) v g = some d)
    (hhd : Completion.pullOld (completionOld P) v h = some d) : False := by
  have hmeet : Edge4Meet e f := by
    simpa only [Edge4Meet, Completion.IsMatchingPair, not_not] using hnm
  obtain ⟨x, hxe, hxf⟩ := hmeet
  obtain ⟨y, hxy, hey⟩ := edge4_exists_other e hxe
  obtain ⟨z, hxz, hfz⟩ := edge4_exists_other f hxf
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact hef (Subtype.ext (hey.trans hfz.symm))
  have hec' := old_of_pullOld_of_edge_eq P v e hxy hey hec
  have hfc' := old_of_pullOld_of_edge_eq P v f hxz hfz hfc
  obtain ⟨b, hb, hbe, hbf⟩ := P.p1 c (v x) (v y) (v z) hec' hfc'
  have hclose : b.Paints (v y) (v z) b.singleton :=
    b.closes_sameColor_path hbe hbf (v.injective.ne hyz)
  have holdClose : P.old (v y) (v z) = some b.singleton :=
    (P.p0.2 (v y) (v z) b.singleton).2 ⟨b, hb, hclose⟩
  have hcenter : v x = b.apex :=
    b.apex_eq_of_sameColor_path hbe hbf (v.injective.ne hyz)
  have hge : g ≠ e := (local_edges_ne_of_distinct_colors P v hcd hec hgd).symm
  have hgf : g ≠ f := (local_edges_ne_of_distinct_colors P v hcd hfc hgd).symm
  have hhe : h ≠ e := (local_edges_ne_of_distinct_colors P v hcd hec hhd).symm
  have hhf : h ≠ f := (local_edges_ne_of_distinct_colors P v hcd hfc hhd).symm
  rcases edge4_matching_avoiding_path hey hfz hxy hxz hyz
      hge hgf hhe hhf hgh hm with hcase | hcase
  · obtain ⟨hgchord, hxh⟩ := hcase
    have hgd' := old_of_pullOld_of_edge_eq P v g hyz hgchord hgd
    have hds : d = b.singleton := Option.some.inj (hgd'.symm.trans holdClose)
    obtain ⟨t, hxt, hht⟩ := edge4_exists_other h hxh
    have hhd' := old_of_pullOld_of_edge_eq P v h hxt hht hhd
    rw [hds, hcenter] at hhd'
    exact (P.p2 b hb).1 (v t) hhd'
  · obtain ⟨hhchord, hxg⟩ := hcase
    have hhd' := old_of_pullOld_of_edge_eq P v h hyz hhchord hhd
    have hds : d = b.singleton := Option.some.inj (hhd'.symm.trans holdClose)
    obtain ⟨t, hxt, hgt⟩ := edge4_exists_other g hxg
    have hgd' := old_of_pullOld_of_edge_eq P v g hxt hgt hgd
    rw [hds, hcenter] at hgd'
    exact (P.p2 b hb).1 (v t) hgd'

theorem partialGood_path_path_contra {n k B : ℕ} (P : PartialGood n k B)
    (v : Fin 4 ↪ Fin n) {c d : Fin k} (hcd : c ≠ d)
    (e f g h : Completion.Edge4)
    (hef : e ≠ f) (hgh : g ≠ h)
    (hnm₁ : ¬ Completion.IsMatchingPair e f)
    (hnm₂ : ¬ Completion.IsMatchingPair g h)
    (hec : Completion.pullOld (completionOld P) v e = some c)
    (hfc : Completion.pullOld (completionOld P) v f = some c)
    (hgd : Completion.pullOld (completionOld P) v g = some d)
    (hhd : Completion.pullOld (completionOld P) v h = some d) : False := by
  have hmeet₁ : Edge4Meet e f := by
    simpa only [Edge4Meet, Completion.IsMatchingPair, not_not] using hnm₁
  have hmeet₂ : Edge4Meet g h := by
    simpa only [Edge4Meet, Completion.IsMatchingPair, not_not] using hnm₂
  obtain ⟨x, hxe, hxf⟩ := hmeet₁
  obtain ⟨y, hxy, hey⟩ := edge4_exists_other e hxe
  obtain ⟨z, hxz, hfz⟩ := edge4_exists_other f hxf
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact hef (Subtype.ext (hey.trans hfz.symm))
  obtain ⟨u, hug, huh⟩ := hmeet₂
  obtain ⟨w, huw, hgw⟩ := edge4_exists_other g hug
  obtain ⟨t, hut, hht⟩ := edge4_exists_other h huh
  have hwt : w ≠ t := by
    intro hwt
    subst t
    exact hgh (Subtype.ext (hgw.trans hht.symm))
  have hec' := old_of_pullOld_of_edge_eq P v e hxy hey hec
  have hfc' := old_of_pullOld_of_edge_eq P v f hxz hfz hfc
  have hgd' := old_of_pullOld_of_edge_eq P v g huw hgw hgd
  have hhd' := old_of_pullOld_of_edge_eq P v h hut hht hhd
  obtain ⟨b, hb, hbe, hbf⟩ := P.p1 c (v x) (v y) (v z) hec' hfc'
  obtain ⟨b', hb', hbg, hbh⟩ := P.p1 d (v u) (v w) (v t) hgd' hhd'
  obtain ⟨p, q, hpq, hp₁, hq₁, hp₂, hq₂⟩ :=
    fin4_triples_share_edge x y z u w t hxy hxz hyz huw hut hwt
  have hp₁' : v p = v x ∨ v p = v y ∨ v p = v z := by
    rcases hp₁ with rfl | rfl | rfl <;> simp
  have hq₁' : v q = v x ∨ v q = v y ∨ v q = v z := by
    rcases hq₁ with rfl | rfl | rfl <;> simp
  have hp₂' : v p = v u ∨ v p = v w ∨ v p = v t := by
    rcases hp₂ with rfl | rfl | rfl <;> simp
  have hq₂' : v q = v u ∨ v q = v w ∨ v q = v t := by
    rcases hq₂ with rfl | rfl | rfl <;> simp
  have hs₁ : s(v p, v q) ∈ b.graphEdges :=
    b.supports_pair_of_triangle_vertices hbe hbf (v.injective.ne hyz)
      (v.injective.ne hpq) hp₁' hq₁'
  have hs₂ : s(v p, v q) ∈ b'.graphEdges :=
    b'.supports_pair_of_triangle_vertices hbg hbh (v.injective.ne hwt)
      (v.injective.ne hpq) hp₂' hq₂'
  have hbb' : b = b' := P.blocks_eq_of_supports hb hb' hs₁ hs₂
  subst b'
  have heg : e ≠ g := local_edges_ne_of_distinct_colors P v hcd hec hgd
  have heh : e ≠ h := local_edges_ne_of_distinct_colors P v hcd hec hhd
  have hfg : f ≠ g := local_edges_ne_of_distinct_colors P v hcd hfc hgd
  have hfh : f ≠ h := local_edges_ne_of_distinct_colors P v hcd hfc hhd
  exact b.not_four_distinct_supported
    (b.paints_supports hbe) (b.paints_supports hbf)
    (b.paints_supports hbg) (b.paints_supports hbh)
    (mapped_edge_ne_of_ne v hey hfz hef)
    (mapped_edge_ne_of_ne v hey hgw heg)
    (mapped_edge_ne_of_ne v hey hht heh)
    (mapped_edge_ne_of_ne v hfz hgw hfg)
    (mapped_edge_ne_of_ne v hfz hht hfh)
    (mapped_edge_ne_of_ne v hgw hht hgh)

theorem partialGood_local_twoColor_cycle_contra {n k B : ℕ}
    (P : PartialGood n k B) (v : Fin 4 ↪ Fin n) {c d : Fin k}
    (a b q r : Fin 4)
    (hD : FourDistinct a b q r)
    (hab : a ≠ b) (hbq : b ≠ q) (hqr : q ≠ r) (hra : r ≠ a)
    (h₁ : Completion.pullOld (completionOld P) v
      (Completion.topEdge a b hab) = some c)
    (h₂ : Completion.pullOld (completionOld P) v
      (Completion.topEdge b q hbq) = some d)
    (h₃ : Completion.pullOld (completionOld P) v
      (Completion.topEdge q r hqr) = some c)
    (h₄ : Completion.pullOld (completionOld P) v
      (Completion.topEdge r a hra) = some d) : False := by
  have hD' : FourDistinct (v a) (v b) (v q) (v r) := by
    unfold FourDistinct at hD ⊢
    aesop
  have h₁' : P.old (v a) (v b) = some c := by simpa using h₁
  have h₂' : P.old (v b) (v q) = some d := by simpa using h₂
  have h₃' : P.old (v q) (v r) = some c := by simpa using h₃
  have h₄' : P.old (v r) (v a) = some d := by simpa using h₄
  have hc := P.p3 (v a) (v b) (v q) (v r) c d c d hD' h₁' h₂' h₃' h₄'
  have hle : ({c, d, c, d} : Finset (Fin k)).card ≤ 2 := by
    simpa using (Finset.card_le_two (a := c) (b := d))
  omega

theorem edge4_matching_pairs_cycle
    (e f g h : Completion.Edge4)
    (hef : e ≠ f) (hgh : g ≠ h)
    (heg : e ≠ g) (heh : e ≠ h) (hfg : f ≠ g) (hfh : f ≠ h)
    (hm₁ : Completion.IsMatchingPair e f)
    (hm₂ : Completion.IsMatchingPair g h) :
    ∃ a b q r : Fin 4, FourDistinct a b q r ∧
      ((e.1 = s(a, b) ∧ f.1 = s(q, r)) ∨
        (f.1 = s(a, b) ∧ e.1 = s(q, r))) ∧
      ((g.1 = s(b, q) ∧ h.1 = s(r, a)) ∨
        (h.1 = s(b, q) ∧ g.1 = s(r, a))) := by
  rcases (Completion.matchingPair_cases hef).1 hm₁ with he | he | he | he | he | he <;>
    rcases he with ⟨rfl, rfl⟩ <;>
    rcases (Completion.matchingPair_cases hgh).1 hm₂ with hg | hg | hg | hg | hg | hg <;>
    rcases hg with ⟨rfl, rfl⟩
  all_goals try { exact (heg rfl).elim }
  all_goals try { exact (heh rfl).elim }
  all_goals try { exact (hfg rfl).elim }
  all_goals try { exact (hfh rfl).elim }
  all_goals simp only [FourDistinct]
  all_goals decide

theorem partialGood_matching_matching_contra {n k B : ℕ}
    (P : PartialGood n k B) (v : Fin 4 ↪ Fin n) {c d : Fin k}
    (hcd : c ≠ d) (e f g h : Completion.Edge4)
    (hef : e ≠ f) (hgh : g ≠ h)
    (hm₁ : Completion.IsMatchingPair e f)
    (hm₂ : Completion.IsMatchingPair g h)
    (hec : Completion.pullOld (completionOld P) v e = some c)
    (hfc : Completion.pullOld (completionOld P) v f = some c)
    (hgd : Completion.pullOld (completionOld P) v g = some d)
    (hhd : Completion.pullOld (completionOld P) v h = some d) : False := by
  have heg : e ≠ g := local_edges_ne_of_distinct_colors P v hcd hec hgd
  have heh : e ≠ h := local_edges_ne_of_distinct_colors P v hcd hec hhd
  have hfg : f ≠ g := local_edges_ne_of_distinct_colors P v hcd hfc hgd
  have hfh : f ≠ h := local_edges_ne_of_distinct_colors P v hcd hfc hhd
  obtain ⟨a, b, q, r, hD, hef', hgh'⟩ :=
    edge4_matching_pairs_cycle e f g h hef hgh heg heh hfg hfh hm₁ hm₂
  have hab : a ≠ b := hD.1
  have hbq : b ≠ q := hD.2.2.2.1
  have hqr : q ≠ r := hD.2.2.2.2.2
  have hra : r ≠ a := hD.2.2.1.symm
  rcases hef' with ⟨he, hf⟩ | ⟨hf, he⟩
  · rcases hgh' with ⟨hg, hh⟩ | ⟨hh, hg⟩
    · exact partialGood_local_twoColor_cycle_contra P v a b q r hD hab hbq hqr hra
        (by simpa [show e = Completion.topEdge a b hab from Subtype.ext he] using hec)
        (by simpa [show g = Completion.topEdge b q hbq from Subtype.ext hg] using hgd)
        (by simpa [show f = Completion.topEdge q r hqr from Subtype.ext hf] using hfc)
        (by simpa [show h = Completion.topEdge r a hra from Subtype.ext hh] using hhd)
    · exact partialGood_local_twoColor_cycle_contra P v a b q r hD hab hbq hqr hra
        (by simpa [show e = Completion.topEdge a b hab from Subtype.ext he] using hec)
        (by simpa [show h = Completion.topEdge b q hbq from Subtype.ext hh] using hhd)
        (by simpa [show f = Completion.topEdge q r hqr from Subtype.ext hf] using hfc)
        (by simpa [show g = Completion.topEdge r a hra from Subtype.ext hg] using hgd)
  · rcases hgh' with ⟨hg, hh⟩ | ⟨hh, hg⟩
    · exact partialGood_local_twoColor_cycle_contra P v a b q r hD hab hbq hqr hra
        (by simpa [show f = Completion.topEdge a b hab from Subtype.ext hf] using hfc)
        (by simpa [show g = Completion.topEdge b q hbq from Subtype.ext hg] using hgd)
        (by simpa [show e = Completion.topEdge q r hqr from Subtype.ext he] using hec)
        (by simpa [show h = Completion.topEdge r a hra from Subtype.ext hh] using hhd)
    · exact partialGood_local_twoColor_cycle_contra P v a b q r hD hab hbq hqr hra
        (by simpa [show f = Completion.topEdge a b hab from Subtype.ext hf] using hfc)
        (by simpa [show h = Completion.topEdge b q hbq from Subtype.ext hh] using hhd)
        (by simpa [show e = Completion.topEdge q r hqr from Subtype.ext he] using hec)
        (by simpa [show g = Completion.topEdge r a hra from Subtype.ext hg] using hgd)

theorem completion_oldRepeatUniqueOnK4 {n k B : ℕ} (P : PartialGood n k B) :
    ∀ (v : Fin 4 ↪ Fin n) (c d : Fin k),
      2 ≤ (Completion.fiber (Completion.pullOld (completionOld P) v) (some c)).card →
      2 ≤ (Completion.fiber (Completion.pullOld (completionOld P) v) (some d)).card →
      c = d := by
  intro v c d hc hd
  by_contra hcd
  obtain ⟨e, f, hef, hec, hfc⟩ :=
    (Completion.two_le_card_fiber_iff
      (Completion.pullOld (completionOld P) v) (some c)).1 hc
  obtain ⟨g, h, hgh, hgd, hhd⟩ :=
    (Completion.two_le_card_fiber_iff
      (Completion.pullOld (completionOld P) v) (some d)).1 hd
  by_cases hm₁ : Completion.IsMatchingPair e f
  · by_cases hm₂ : Completion.IsMatchingPair g h
    · exact partialGood_matching_matching_contra P v hcd e f g h hef hgh hm₁ hm₂
        hec hfc hgd hhd
    · exact partialGood_path_matching_contra P v (Ne.symm hcd) g h e f hgh hef hm₂ hm₁
        hgd hhd hec hfc
  · by_cases hm₂ : Completion.IsMatchingPair g h
    · exact partialGood_path_matching_contra P v hcd e f g h hef hgh hm₁ hm₂
        hec hfc hgd hhd
    · exact partialGood_path_path_contra P v hcd e f g h hef hgh hm₁ hm₂
        hec hfc hgd hhd

theorem completion_oldFourCycleUsesThree {n k B : ℕ} (P : PartialGood n k B) :
    ∀ (a b c d : Fin n)
      (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
      (hac : a ≠ c) (hbd : b ≠ d)
      (cab cbc ccd cda : Fin k),
      completionOld P (Completion.topEdge a b hab) = some cab →
      completionOld P (Completion.topEdge b c hbc) = some cbc →
      completionOld P (Completion.topEdge c d hcd) = some ccd →
      completionOld P (Completion.topEdge d a hda) = some cda →
      3 ≤ ({cab, cbc, ccd, cda} : Finset (Fin k)).card := by
  intro a b c d hab hbc hcd hda hac hbd cab cbc ccd cda h₁ h₂ h₃ h₄
  apply P.p3 a b c d cab cbc ccd cda
  · exact ⟨hab, hac, hda.symm, hbc, hbd, hcd⟩
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃
  · simpa using h₄

/-- Export a construction-specific partial colouring to the exact corrected
triangle-block interface used by deterministic leave completion.  All local
`K₄` multiplicity facts are derived above from P0--P3. -/
def toCompletionPartialGood {n k B : ℕ} (P : PartialGood n k B) :
    Completion.TriangleBlockPartialGood n (Fin k) (SelectedBlock P) where
  toTriangleBlockDecomposition := toCompletionDecomposition P
  oldAtMostTwoOnK4 := completion_oldAtMostTwoOnK4 P
  oldRepeatUniqueOnK4 := completion_oldRepeatUniqueOnK4 P
  oldFourCycleUsesThree := completion_oldFourCycleUsesThree P

theorem matching_blockClosure {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M) :
    BlockClosure M (inducedColor M) := by
  constructor
  · intro b hb b' hb' hne
    have hdisj := hM.2 hb hb' hne
    change Disjoint b.auxSupport b'.auxSupport at hdisj
    rw [Finset.disjoint_left] at hdisj ⊢
    intro e he he'
    exact (hdisj (mem_union_left _ (mem_image.2 ⟨e, he, rfl⟩)))
      (mem_union_left _ (mem_image.2 ⟨e, he', rfl⟩))
  · intro x y c
    exact inducedColor_eq_some_iff hM

theorem matching_colorClasses {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M) :
    ColorClassesAreEdgesOrPaths M (inducedColor M) := by
  intro c x y z hxy hxz
  obtain ⟨b, hb, hbxy⟩ := (inducedColor_eq_some_iff hM).1 hxy
  obtain ⟨b', hb', hb'xz⟩ := (inducedColor_eq_some_iff hM).1 hxz
  have hbb' := blocks_eq_of_paints_at hM hb hb' hbxy hb'xz
  subst b'
  exact ⟨b, hb, hbxy, hb'xz⟩

theorem matching_mateIsolated {n k : ℕ} {R : RetainedLabels n k}
    {M : Finset (TriangleBlock n k)} (hM : IsAuxMatching R M) :
    MateIsolated M (inducedColor M) := by
  intro b hb
  have hbEligible := hM.1 b hb
  refine ⟨?_, ?_, ?_⟩
  · intro x hcol
    obtain ⟨b', hb', hpaint'⟩ := (inducedColor_eq_some_iff hM).1 hcol
    have hin : (b.apex, b.singleton) ∈ R :=
      (hM.1 b' hb').1 (b'.paints_positiveLabel_mem hpaint')
    exact hbEligible.2 hin
  · intro x hcol
    obtain ⟨b', hb', hpaint'⟩ := (inducedColor_eq_some_iff hM).1 hcol
    have hbPaint : b.Paints b.left b.right b.singleton := Or.inr ⟨rfl, rfl⟩
    have hbb' := blocks_eq_of_paints_at hM hb hb' hbPaint hpaint'
    subst b'
    exact b.singleton_edge hpaint'
  · intro x hcol
    obtain ⟨b', hb', hpaint'⟩ := (inducedColor_eq_some_iff hM).1 hcol
    have hbPaint : b.Paints b.right b.left b.singleton :=
      (TriangleBlock.paints_symm b) (Or.inr ⟨rfl, rfl⟩)
    have hbb' := blocks_eq_of_paints_at hM hb hb' hbPaint hpaint'
    subst b'
    exact b.singleton_edge hpaint'

/-! ## Quantitative conflict-free-matching adapter -/

/-- The precise obligation for the `1`-, `2`-, and `3`-uniform test
functions in the Joos--Mubayi application.  It does not assume a matching
exists: it says that the numerical estimates delivered by the specialized
conflict-free matching theorem imply the concrete leave bounds (P4)--(P5).
This is the interface consumed by the concentration/counting layer. -/
def TestsControlLeave {n k : ℕ} (B : ℕ)
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {ι : Type} (d eta : ℝ) (j : ι → ℕ)
    (w : ι → TestWeight (AuxVertex n k)) : Prop :=
  ∀ MH, (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH) →
    SatisfiesTestEstimates (auxiliaryHypergraph candidates R) MH d
      (Real.rpow d (-(eta ^ 3))) j w →
    let BM := blocksOfAuxFamily candidates R MH hmatch.1
    LeaveMaxDegree B (inducedColor BM) ∧
      CrossLeaveBound B (inducedColor BM)

/-- Deterministic extraction of the concrete partial colouring from the
quantitative conclusion of the conflict-free matching theorem.  The matching
constructs P0--P3; the terminal tracked-test estimates supply P4--P5. -/
theorem partialGood_of_specializedCFMConclusion
    (n k B : ℕ) (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) {iota : Type} [Fintype iota]
    (d eta : ℝ) (j : iota → ℕ)
    (w : iota → TestWeight (AuxVertex n k))
    (hconclusion :
      SpecializedCFMConclusion (auxiliaryHypergraph candidates R)
        (alternatingCycleConflicts candidates R) d eta j w)
    (htests : TestsControlLeave B candidates R d eta j w) :
    Nonempty (PartialGood n k B) := by
  obtain ⟨MH, hmatch, hfree, -, hest⟩ := hconclusion
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  have hBM : IsAuxMatching R BM :=
    blocksOfAuxFamily_isAuxMatching candidates R MH hmatch
  have hleave : LeaveMaxDegree B (inducedColor BM) ∧
      CrossLeaveBound B (inducedColor BM) := htests MH hmatch hest
  exact ⟨{
    old := inducedColor BM
    blocks := BM
    symmetric := inducedColor_symm hBM
    diagonal := inducedColor_self hBM
    p0 := matching_blockClosure hBM
    p1 := matching_colorClasses hBM
    p2 := matching_mateIsolated hBM
    p3 := matching_oldFourCyclesUseThree candidates R MH hmatch hfree
    p4 := hleave.1
    p5 := hleave.2
  }⟩

/-- Quantitative partial colouring obtained from the exact specialized
conflict-free matching theorem.  The only existence input is
`SpecializedCFMTheorem`; `TestsControlLeave` is a deterministic implication
from its terminal test estimates to the explicitly counted P4/P5 sets.

The result retains the selected block family and proves P0--P3 rather than
postulating them. -/
theorem specialized_quantitative_partial_coloring {ell : ℕ}
    (hCFM : SpecializedCFMTheorem ell)
    (n k B : ℕ) (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) {ι : Type} [Fintype ι]
    (j : ι → ℕ) (w : ι → TestWeight (AuxVertex n k)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta < eta0 →
        ∃ d0 : ℝ, ∀ d : ℝ, d0 ≤ d →
          IsSpecializedCFMInstance (auxiliaryHypergraph candidates R)
            (alternatingCycleConflicts candidates R) d eta ell j w →
          TestsControlLeave B candidates R d eta j w →
          Nonempty (PartialGood n k B) := by
  rcases hCFM with ⟨eta0, heta0, hCFM⟩
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta heta0
  obtain ⟨d0, hd0⟩ := hCFM eta heta heta0
  refine ⟨d0, ?_⟩
  intro d hd hinst htests
  have hconclusion :
      SpecializedCFMConclusion (auxiliaryHypergraph candidates R)
        (alternatingCycleConflicts candidates R) d eta j w :=
    hd0 d hd (AuxVertex n k) ι (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) j w hinst
  exact partialGood_of_specializedCFMConclusion n k B candidates R d eta j w
    hconclusion htests

/-- The same quantitative construction, exported directly through the
deterministic completion interface.  The selected block type depends on the
constructed `PartialGood`, so it is packaged by a dependent existential. -/
theorem specialized_quantitative_completion_partial_coloring {ell : ℕ}
    (hCFM : SpecializedCFMTheorem ell)
    (n k B : ℕ) (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) {ι : Type} [Fintype ι]
    (j : ι → ℕ) (w : ι → TestWeight (AuxVertex n k)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta < eta0 →
        ∃ d0 : ℝ, ∀ d : ℝ, d0 ≤ d →
          IsSpecializedCFMInstance (auxiliaryHypergraph candidates R)
            (alternatingCycleConflicts candidates R) d eta ell j w →
          TestsControlLeave B candidates R d eta j w →
          ∃ P : PartialGood n k B,
            Nonempty
              (Completion.TriangleBlockPartialGood n (Fin k) (SelectedBlock P)) := by
  rcases specialized_quantitative_partial_coloring hCFM n k B candidates R j w with
    ⟨eta0, heta0, hmain⟩
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta heta0
  rcases hmain eta heta heta0 with ⟨d0, hd0⟩
  refine ⟨d0, ?_⟩
  intro d hd hinst htests
  obtain ⟨P⟩ := hd0 d hd hinst htests
  exact ⟨P, ⟨toCompletionPartialGood P⟩⟩

end

end Erdos136
