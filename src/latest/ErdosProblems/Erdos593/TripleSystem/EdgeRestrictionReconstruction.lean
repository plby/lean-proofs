import ErdosProblems.Erdos593.TripleSystem.Constructive
import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reconstructing exact edge restrictions

This file identifies an edge restriction assembled from two edge-disjoint
pieces.  Disjoint vertex supports give a disjoint union, while a singleton
support intersection gives the canonical one-point amalgamation.  A finite
running-union theorem then packages repeated use of these identifications.
-/

namespace Erdos593

universe u v w

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- Edge support commutes with binary union of edge-index sets. -/
theorem edgeSupportSet_union (S T : Set E) :
    F.edgeSupportSet (S ∪ T) = F.edgeSupportSet S ∪ F.edgeSupportSet T := by
  ext x
  simp only [edgeSupportSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨e, heS | heT, hxe⟩
    · exact Or.inl ⟨e, heS, hxe⟩
    · exact Or.inr ⟨e, heT, hxe⟩
  · rintro (⟨e, heS, hxe⟩ | ⟨e, heT, hxe⟩)
    · exact ⟨e, Or.inl heS, hxe⟩
    · exact ⟨e, Or.inr heT, hxe⟩

/-- For edge-disjoint index sets, their tagged sum is canonically equivalent
to their union. -/
noncomputable def edgeUnionEquiv {S T : Set E} (hST : Disjoint S T) :
    S ⊕ T ≃ (S ∪ T : Set E) := by
  classical
  exact (Equiv.Set.union hST).symm

/-- For edge sets with disjoint supports, the tagged sum of the two support
types is canonically equivalent to the support of their union. -/
noncomputable def edgeSupportUnionEquiv {S T : Set E}
    (hST : Disjoint (F.edgeSupportSet S) (F.edgeSupportSet T)) :
    F.EdgeSupport S ⊕ F.EdgeSupport T ≃ F.EdgeSupport (S ∪ T) := by
  classical
  exact (Equiv.Set.union hST).symm |>.trans
    (Equiv.setCongr (F.edgeSupportSet_union S T).symm)

/-- If two source edge sets and their vertex supports are disjoint, the exact
restriction to their union is the disjoint union of the two exact
restrictions. -/
noncomputable def edgeRestrictionUnionIsoDisjointUnion {S T : Set E}
    (hEdges : Disjoint S T)
    (hSupports : Disjoint (F.edgeSupportSet S) (F.edgeSupportSet T)) :
    Iso ((F.edgeRestriction S).disjointUnion (F.edgeRestriction T))
      (F.edgeRestriction (S ∪ T)) where
  vertexEquiv := F.edgeSupportUnionEquiv hSupports
  edgeEquiv := edgeUnionEquiv hEdges
  map_inc_iff := by
    intro x e
    cases x with
    | inl x =>
        cases e with
        | inl e =>
            change F.Inc x.1 e.1 ↔ F.Inc _ _
            simp [edgeSupportUnionEquiv, edgeUnionEquiv]
        | inr e =>
            change False ↔ F.Inc _ _
            simp only [edgeSupportUnionEquiv, edgeUnionEquiv,
              Equiv.trans_apply, Equiv.Set.union_symm_apply_left,
              Equiv.Set.union_symm_apply_right, Equiv.setCongr_apply]
            exact (iff_false_intro fun hxe =>
              Set.disjoint_left.mp hSupports x.2 ⟨e.1, e.2, hxe⟩).symm
    | inr x =>
        cases e with
        | inl e =>
            change False ↔ F.Inc _ _
            simp only [edgeSupportUnionEquiv, edgeUnionEquiv,
              Equiv.trans_apply, Equiv.Set.union_symm_apply_left,
              Equiv.Set.union_symm_apply_right, Equiv.setCongr_apply]
            exact (iff_false_intro fun hxe =>
              Set.disjoint_left.mp hSupports ⟨e.1, e.2, hxe⟩ x.2).symm
        | inr e =>
            change F.Inc x.1 e.1 ↔ F.Inc _ _
            simp [edgeSupportUnionEquiv, edgeUnionEquiv]

/-- Include the support of the left edge set into the support of a union. -/
def edgeSupportUnionLeft (S T : Set E) :
    F.EdgeSupport S → F.EdgeSupport (S ∪ T) :=
  fun x => ⟨x.1, by
    change x.1 ∈ F.edgeSupportSet (S ∪ T)
    rw [F.edgeSupportSet_union S T]
    exact Or.inl x.2⟩

/-- Include the support of the right edge set into the support of a union. -/
def edgeSupportUnionRight (S T : Set E) :
    F.EdgeSupport T → F.EdgeSupport (S ∪ T) :=
  fun x => ⟨x.1, by
    change x.1 ∈ F.edgeSupportSet (S ∪ T)
    rw [F.edgeSupportSet_union S T]
    exact Or.inr x.2⟩

@[simp]
theorem edgeSupportUnionLeft_val (S T : Set E) (x : F.EdgeSupport S) :
    (F.edgeSupportUnionLeft S T x).1 = x.1 :=
  rfl

@[simp]
theorem edgeSupportUnionRight_val (S T : Set E) (x : F.EdgeSupport T) :
    (F.edgeSupportUnionRight S T x).1 = x.1 :=
  rfl

/-- The left copy of the unique point in a singleton support intersection. -/
def edgeSupportLeftRoot {S T : Set E} {r : V}
    (h : F.edgeSupportSet S ∩ F.edgeSupportSet T = {r}) :
    F.EdgeSupport S := by
  refine ⟨r, ?_⟩
  have hr : r ∈ F.edgeSupportSet S ∩ F.edgeSupportSet T := by
    rw [h]
    simp
  exact hr.1

/-- The right copy of the unique point in a singleton support intersection. -/
def edgeSupportRightRoot {S T : Set E} {r : V}
    (h : F.edgeSupportSet S ∩ F.edgeSupportSet T = {r}) :
    F.EdgeSupport T := by
  refine ⟨r, ?_⟩
  have hr : r ∈ F.edgeSupportSet S ∩ F.edgeSupportSet T := by
    rw [h]
    simp
  exact hr.2

@[simp]
theorem edgeSupportLeftRoot_val {S T : Set E} {r : V}
    (h : F.edgeSupportSet S ∩ F.edgeSupportSet T = {r}) :
    (F.edgeSupportLeftRoot h).1 = r :=
  rfl

@[simp]
theorem edgeSupportRightRoot_val {S T : Set E} {r : V}
    (h : F.edgeSupportSet S ∩ F.edgeSupportSet T = {r}) :
    (F.edgeSupportRightRoot h).1 = r :=
  rfl

/-- If two edge-disjoint restrictions meet in exactly one ambient point, the
exact restriction to their union is their canonical one-point amalgamation at
the two copies of that point. -/
noncomputable def edgeRestrictionUnionIsoOnePointAmalgamation
    {S T : Set E} (hEdges : Disjoint S T) {r : V}
    (hSupport : F.edgeSupportSet S ∩ F.edgeSupportSet T = {r}) :
    Iso
      (OnePointAmalgamation.amalgam
        (F.edgeRestriction S) (F.edgeRestriction T)
        (F.edgeSupportLeftRoot hSupport) (F.edgeSupportRightRoot hSupport))
      (F.edgeRestriction (S ∪ T)) := by
  let f₀ : F.EdgeSupport S → F.EdgeSupport (S ∪ T) :=
    F.edgeSupportUnionLeft S T
  let f₁ : F.EdgeSupport T → F.EdgeSupport (S ∪ T) :=
    F.edgeSupportUnionRight S T
  let eEquiv : S ⊕ T ≃ (S ∪ T : Set E) := edgeUnionEquiv hEdges
  apply OnePointAmalgamation.isoOfMaps
    (F.edgeRestriction S) (F.edgeRestriction T)
    (F.edgeRestriction (S ∪ T))
    (F.edgeSupportLeftRoot hSupport) (F.edgeSupportRightRoot hSupport)
    f₀ f₁ (edgeEquiv := eEquiv)
  · apply Subtype.ext
    rfl
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : F.EdgeSupport (S ∪ T) => z.1) hxy
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : F.EdgeSupport (S ∪ T) => z.1) hxy
  · intro x y
    constructor
    · intro hxy
      have hval : x.1 = y.1 := congrArg Subtype.val hxy
      have hxInter : x.1 ∈ F.edgeSupportSet S ∩ F.edgeSupportSet T :=
        ⟨x.2, hval ▸ y.2⟩
      have hxr : x.1 = r := by
        have : x.1 ∈ ({r} : Set V) := hSupport ▸ hxInter
        simpa using! this
      constructor
      · apply Subtype.ext
        exact hxr
      · apply Subtype.ext
        exact hval.symm.trans hxr
    · rintro ⟨rfl, rfl⟩
      apply Subtype.ext
      rfl
  · intro z
    have hz : z.1 ∈ F.edgeSupportSet S ∪ F.edgeSupportSet T :=
      (F.edgeSupportSet_union S T) ▸ z.2
    rcases hz with hzS | hzT
    · exact Or.inl ⟨⟨z.1, hzS⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨⟨z.1, hzT⟩, Subtype.ext rfl⟩
  · intro e
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      refine ⟨⟨z.1, ⟨e.1, e.2, hz⟩⟩, hz, ?_⟩
      apply Subtype.ext
      rfl
  · intro e
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      refine ⟨⟨z.1, ⟨e.1, e.2, hz⟩⟩, hz, ?_⟩
      apply Subtype.ext
      rfl

/-- The edgeless system on the (empty) support of the empty edge set is
isomorphic to the exact empty edge restriction. -/
noncomputable def edgelessIsoEdgeRestrictionEmpty
    (F : TripleSystem (V := V) (E := E)) :
    Iso (edgeless (F.EdgeSupport ∅)) (F.edgeRestriction ∅) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.equivOfIsEmpty _ _
  map_inc_iff := by
    intro x e
    exact isEmptyElim e

section ConstructibleReconstruction

variable {X I : Type w} (K : TripleSystem X I)

/-- Exact union of an ordered finite list of edge pieces.  The list is stored
newest piece first, so the tail is precisely the previously assembled union. -/
def edgePieceUnion : List (Set I) → Set I
  | [] => ∅
  | S :: pieces => edgePieceUnion pieces ∪ S

/-- Auditable running-intersection data for a finite reconstruction.  At each
step the new piece is edge-disjoint from the exact previous union, is itself
constructible, and its vertex support meets the previous support either in no
point or in exactly one named point. -/
def RunningEdgeAssembly : List (Set I) → Prop
  | [] => True
  | S :: pieces =>
      RunningEdgeAssembly pieces ∧
      Constructible (K.edgeRestriction S) ∧
      Disjoint (edgePieceUnion pieces) S ∧
      (Disjoint
          (K.edgeSupportSet (edgePieceUnion pieces))
          (K.edgeSupportSet S) ∨
        ∃ r : X,
          K.edgeSupportSet (edgePieceUnion pieces) ∩
            K.edgeSupportSet S = {r})

/-- The empty exact restriction belongs to the constructive class. -/
theorem edgeRestriction_empty_constructible :
    Constructible (K.edgeRestriction ∅) := by
  let : IsEmpty (K.EdgeSupport ∅) := ⟨by
    intro x
    rcases x.2 with ⟨e, he, hxe⟩
    exact he⟩
  let : Fintype (K.EdgeSupport ∅) := Fintype.ofFinite _
  exact Constructible.ofIso
    (Constructible.ofEdgeless (K.EdgeSupport ∅))
    (edgelessIsoEdgeRestrictionEmpty K)

/-- A finite running family of constructible exact pieces reconstructs the
exact restriction to their total edge union.  Both permitted gluing cases are
realized by the corresponding constructor, and the conclusion retains the
literal source edge set `edgePieceUnion pieces`. -/
theorem runningEdgeAssembly_constructible (pieces : List (Set I))
    (hpieces : K.RunningEdgeAssembly pieces) :
    Constructible (K.edgeRestriction (edgePieceUnion pieces)) := by
  induction pieces with
  | nil =>
      exact K.edgeRestriction_empty_constructible
  | cons S pieces ih =>
      rcases hpieces with ⟨hprevious, hS, hEdges, hSupports⟩
      have hPrev :
          Constructible (K.edgeRestriction (edgePieceUnion pieces)) :=
        ih hprevious
      rcases hSupports with hDisjoint | ⟨r, hRoot⟩
      · exact Constructible.ofIso
          (Constructible.disjointUnion hPrev hS)
          (K.edgeRestrictionUnionIsoDisjointUnion hEdges hDisjoint)
      · exact Constructible.ofIso
          (Constructible.amalgam hPrev hS
            (K.edgeSupportLeftRoot hRoot)
            (K.edgeSupportRightRoot hRoot))
          (K.edgeRestrictionUnionIsoOnePointAmalgamation hEdges hRoot)

end ConstructibleReconstruction

end TripleSystem
end Erdos593
