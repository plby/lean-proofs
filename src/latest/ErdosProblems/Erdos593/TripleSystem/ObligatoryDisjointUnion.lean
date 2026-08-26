import ErdosProblems.Erdos593.TripleSystem.DisjointUnion
import ErdosProblems.Erdos593.TripleSystem.Obligatory
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite deletion and disjoint-union closure for obligatory triple systems

This file starts the infinitary-facing positive theory.  Restriction to a
vertex set retains precisely those host hyperedges contained in that set.  A
proper colouring after deleting finitely many vertices extends by assigning a
private colour to every deleted vertex; consequently finite deletion preserves
uncountable chromatic cardinality.  This lets two finite obligatory systems be
embedded successively with disjoint images.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace TripleSystem

variable {V W X : Type u} {E D A : Type v}

section Restriction

variable (H : TripleSystem W D) (S : Set W)

/-- The edge indices retained by restriction to `S`: exactly the host edges
whose three vertices all lie in `S`. -/
abbrev RestrictedEdge := {d : D // H.edgeSet d ⊆ S}

/-- Restrict a triple system to a set of vertices, retaining precisely the
hyperedges wholly contained in that set. -/
def vertexRestriction : TripleSystem S (H.RestrictedEdge S) where
  Inc x d := H.Inc x.1 d.1
  edge_ncard := by
    intro d
    have himage :
        ((fun x : S => (x : W)) ''
            {x : S | H.Inc x.1 d.1}) = H.edgeSet d.1 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, d.2 hx⟩, hx, rfl⟩
    calc
      Set.ncard {x : S | H.Inc x.1 d.1} =
          Set.ncard ((fun x : S => (x : W)) ''
            {x : S | H.Inc x.1 d.1}) :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ = Set.ncard (H.edgeSet d.1) := congrArg Set.ncard himage
      _ = 3 := H.edgeSet_ncard d.1
  simple := by
    intro d₁ d₂ hedge
    apply Subtype.ext
    apply H.edgeSet_injective
    ext x
    constructor
    · intro hx
      have hxS : x ∈ S := d₁.2 hx
      have := Set.ext_iff.mp hedge ⟨x, hxS⟩
      exact this.mp hx
    · intro hx
      have hxS : x ∈ S := d₂.2 hx
      have := Set.ext_iff.mp hedge ⟨x, hxS⟩
      exact this.mpr hx

@[simp]
theorem vertexRestriction_inc (x : S) (d : H.RestrictedEdge S) :
    (H.vertexRestriction S).Inc x d ↔ H.Inc x.1 d.1 :=
  Iff.rfl

/-- The canonical non-induced embedding of a vertex restriction into its host.
It is in fact induced on the retained edge indices, but only the weaker project
embedding interface is needed. -/
def vertexRestrictionEmbedding : (H.vertexRestriction S).Embedding H where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge := Subtype.val
  map_edge := by
    intro d
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, d.2 hx⟩, hx, rfl⟩

/-- Delete `R` from the vertex set and retain exactly the edges avoiding `R`. -/
abbrev deleteVertices (R : Set W) :
    TripleSystem (Rᶜ : Set W) (H.RestrictedEdge (Rᶜ : Set W)) :=
  H.vertexRestriction (Rᶜ : Set W)

/-- The canonical embedding of a finite or infinite vertex deletion back into
the original host. -/
abbrev deleteVerticesEmbedding (R : Set W) :
    (H.deleteVertices R).Embedding H :=
  H.vertexRestrictionEmbedding (Rᶜ : Set W)

end Restriction

section ChromaticCardinal

variable (H : TripleSystem W D)

/-- Every edge contains another vertex distinct from any prescribed incident
vertex.  This elementary consequence of 3-uniformity is used when a deleted
vertex supplies one of the two colours witnessing properness. -/
theorem exists_other_incident (e : D) {x : W} (_hx : H.Inc x e) :
    ∃ y : W, H.Inc y e ∧ y ≠ x := by
  have hone : 1 < (H.edgeSet e).ncard := by
    rw [H.edgeSet_ncard]
    decide
  exact Set.exists_ne_of_one_lt_ncard hone x

/-- The set of cardinalities of proper colour types is nonempty. -/
private theorem coloringCardinals_nonempty :
    {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
      ∃ c : W → C, H.IsProperColoring c}.Nonempty := by
  refine ⟨#W, W, rfl, id, ?_⟩
  intro e
  have hne : (H.edgeSet e).ncard ≠ 0 := by
    rw [H.edgeSet_ncard]
    decide
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨y, hy, hyx⟩ := H.exists_other_incident e hx
  exact ⟨x, hx, y, hy, hyx.symm⟩

/-- The `sInf` defining the chromatic cardinal is attained by an actual colour
type and proper colouring. -/
theorem exists_properColoring_mk_eq_chromaticCardinal :
    ∃ C : Type u, #C = H.chromaticCardinal ∧
      ∃ c : W → C, H.IsProperColoring c := by
  unfold chromaticCardinal
  exact csInf_mem (H.coloringCardinals_nonempty)

/-- Exact usable characterization of the chromatic cardinal: it is at most
`#C` exactly when a proper `C`-colouring exists. -/
theorem chromaticCardinal_le_mk_iff {C : Type u} :
    H.chromaticCardinal ≤ #C ↔ ∃ c : W → C, H.IsProperColoring c := by
  constructor
  · intro hle
    obtain ⟨C₀, hC₀, c₀, hc₀⟩ :=
      H.exists_properColoring_mk_eq_chromaticCardinal
    have hcard : #C₀ ≤ #C := hC₀.trans_le hle
    obtain ⟨i⟩ : Nonempty (C₀ ↪ C) := by
      exact (Cardinal.lift_mk_le'.mp (by simpa using! hcard))
    exact ⟨fun x => i (c₀ x), fun e => by
      obtain ⟨x, hx, y, hy, hxy⟩ := hc₀ e
      exact ⟨x, hx, y, hy, i.injective.ne hxy⟩⟩
  · rintro ⟨c, hc⟩
    unfold chromaticCardinal
    exact csInf_le' ⟨C, rfl, c, hc⟩

/-- Extend a proper colouring from the deletion of `R` to the whole host by
giving every deleted vertex its own private colour. -/
theorem exists_properColoring_sum_deleted
    (R : Set W) {C : Type u} (c : (Rᶜ : Set W) → C)
    (hc : (H.deleteVertices R).IsProperColoring c) :
    ∃ c' : W → (C ⊕ R), H.IsProperColoring c' := by
  classical
  let c' : W → (C ⊕ R) := fun x =>
    if hx : x ∈ R then Sum.inr ⟨x, hx⟩ else Sum.inl (c ⟨x, hx⟩)
  refine ⟨c', ?_⟩
  intro e
  by_cases hhit : ∃ x : W, H.Inc x e ∧ x ∈ R
  · obtain ⟨x, hxe, hxR⟩ := hhit
    obtain ⟨y, hye, hyx⟩ := H.exists_other_incident e hxe
    refine ⟨x, hxe, y, hye, ?_⟩
    by_cases hyR : y ∈ R
    · rw [show c' x = Sum.inr ⟨x, hxR⟩ by simp [c', hxR],
          show c' y = Sum.inr ⟨y, hyR⟩ by simp [c', hyR]]
      intro heq
      exact hyx (congrArg (fun z : C ⊕ R => Sum.elim (fun _ => y) Subtype.val z) heq).symm
    · simp [c', hxR, hyR]
  · push Not at hhit
    let d : H.RestrictedEdge Rᶜ :=
      ⟨e, fun _ hx => hhit _ hx⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hc d
    refine ⟨x.1, hx, y.1, hy, ?_⟩
    have hxR : x.1 ∉ R := x.2
    have hyR : y.1 ∉ R := y.2
    rw [show c' x.1 = Sum.inl (c x) by simp [c', hxR],
        show c' y.1 = Sum.inl (c y) by simp [c', hyR]]
    exact Sum.inl_injective.ne hxy

/-- Deleting finitely many vertices from an uncountably chromatic host leaves
an uncountably chromatic restriction. -/
theorem aleph0_lt_chromaticCardinal_deleteVertices
    (R : Set W) (hR : R.Finite)
    (hH : ℵ₀ < H.chromaticCardinal) :
    ℵ₀ < (H.deleteVertices R).chromaticCardinal := by
  by_contra hnot
  have hdel : (H.deleteVertices R).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hnot
  obtain ⟨C, hC, c, hc⟩ :=
    (H.deleteVertices R).exists_properColoring_mk_eq_chromaticCardinal
  obtain ⟨c', hc'⟩ := H.exists_properColoring_sum_deleted R c hc
  have hHsum : H.chromaticCardinal ≤ #(C ⊕ R) :=
    (H.chromaticCardinal_le_mk_iff).2 ⟨c', hc'⟩
  have hCcount : #C ≤ ℵ₀ := hC.trans_le hdel
  letI : Fintype R := hR.fintype
  have hRcount : #R ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite R).le
  have hsum : #(C ⊕ R) ≤ ℵ₀ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_aleph0.2 ⟨hCcount, hRcount⟩
  exact hH.2 (hHsum.trans hsum)

end ChromaticCardinal

section DisjointEmbedding

variable {F : TripleSystem V E} {G : TripleSystem X A}
variable {H : TripleSystem W D}

/-- Embeddings with disjoint vertex images combine to an embedding of the
tagged disjoint union. -/
def Embedding.disjointUnionOfDisjoint
    (f : F.Embedding H) (g : G.Embedding H)
    (hdisj : ∀ x y, f.vertex x ≠ g.vertex y) :
    (F.disjointUnion G).Embedding H where
  vertex :=
    { toFun := Sum.elim f.vertex g.vertex
      inj' := by
        intro p q hpq
        cases p with
        | inl x =>
            cases q with
            | inl y => exact congrArg Sum.inl (f.vertex.injective hpq)
            | inr y => exact False.elim (hdisj x y hpq)
        | inr x =>
            cases q with
            | inl y => exact False.elim (hdisj y x hpq.symm)
            | inr y => exact congrArg Sum.inr (g.vertex.injective hpq) }
  edge := Sum.elim f.edge g.edge
  map_edge := by
    intro e
    cases e with
    | inl e =>
        rw [disjointUnion_edgeSet_inl]
        rw [Set.image_image]
        change f.vertex '' F.edgeSet e = H.edgeSet (f.edge e)
        exact f.map_edge e
    | inr d =>
        rw [disjointUnion_edgeSet_inr]
        rw [Set.image_image]
        change g.vertex '' G.edgeSet d = H.edgeSet (g.edge d)
        exact g.map_edge d

end DisjointEmbedding

section ObligatoryClosure

variable (F : TripleSystem V E) (G : TripleSystem X A)

/-- The class of finite obligatory triple systems is closed under tagged
disjoint union. -/
theorem IsObligatory.disjointUnion
    [Fintype V] [Fintype E] [Fintype X] [Fintype A]
    (hF : F.IsObligatory) (hG : G.IsObligatory) :
    (F.disjointUnion G).IsObligatory := by
  intro Y B _ H hH
  obtain ⟨f⟩ := hF Y B H hH
  let R : Set Y := Set.range f.vertex
  have hR : R.Finite := Set.finite_range f.vertex
  have hdelete : ℵ₀ < (H.deleteVertices R).chromaticCardinal :=
    H.aleph0_lt_chromaticCardinal_deleteVertices R hR hH
  obtain ⟨g₀⟩ := hG (Rᶜ : Set Y) (H.RestrictedEdge (Rᶜ : Set Y))
    (H.deleteVertices R) hdelete
  let g : G.Embedding H := g₀.trans (H.deleteVerticesEmbedding R)
  have hdisj : ∀ x y, f.vertex x ≠ g.vertex y := by
    intro x y heq
    have hy : (g.vertex y : Y) ∉ R := (g₀.vertex y).2
    exact hy ⟨x, heq⟩
  exact ⟨f.disjointUnionOfDisjoint g hdisj⟩

end ObligatoryClosure

end TripleSystem
end Erdos593
