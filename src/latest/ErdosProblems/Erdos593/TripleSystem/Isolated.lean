import ErdosProblems.Erdos593.TripleSystem.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Isolated-point reduction

The isolated-point reduction keeps the edge-index type unchanged and restricts
the vertex type to points incident with at least one edge.  Since every point of
an edge is non-isolated, this restriction preserves every edge, its cardinality,
and simplicity.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A triple system has no isolated points when every point lies on an edge. -/
def HasNoIsolatedPoints : Prop :=
  ∀ x, ¬F.IsIsolated x

/-- Any point incident with an edge is non-isolated. -/
theorem not_isolated_of_inc {x : V} {e : E} (hxe : F.Inc x e) :
    ¬F.IsIsolated x := by
  intro hx
  exact hx e hxe

/-- Classically, being non-isolated is equivalent to lying on some edge. -/
theorem not_isolated_iff_exists_inc {x : V} :
    ¬F.IsIsolated x ↔ ∃ e, F.Inc x e := by
  classical
  simp [IsIsolated]

/-- The type of non-isolated points of `F`. -/
abbrev NonIsolatedPoint :=
  {x : V // ¬F.IsIsolated x}

/-- Delete all isolated points while retaining the original edge indices. -/
def isolatedReduction : TripleSystem F.NonIsolatedPoint E where
  Inc x e := F.Inc x.1 e
  edge_ncard := by
    intro e
    change Set.ncard {x : F.NonIsolatedPoint |
      (x : V) ∈ {y : V | F.Inc y e}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e} ⊆ {x : V | ¬F.IsIsolated x} := by
      intro x hx
      exact F.not_isolated_of_inc hx
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e
  simple := by
    intro e f hef
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxe⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mp hxe
    · intro hxf
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxf⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mpr hxf

@[simp]
theorem isolatedReduction_inc {x : F.NonIsolatedPoint} {e : E} :
    F.isolatedReduction.Inc x e ↔ F.Inc x.1 e :=
  Iff.rfl

/-- Each reduced edge still has exactly three points. -/
theorem isolatedReduction_edge_ncard (e : E) :
    Set.ncard {x : F.NonIsolatedPoint | F.isolatedReduction.Inc x e} = 3 :=
  F.isolatedReduction.edge_ncard e

/-- Distinct edge indices remain distinct after isolated points are deleted. -/
theorem isolatedReduction_simple :
    Function.Injective (fun e => {x | F.isolatedReduction.Inc x e}) :=
  F.isolatedReduction.simple

/-- Deleting isolated points preserves linearity. -/
theorem isolatedReduction_linear (hlinear : F.Linear) :
    F.isolatedReduction.Linear := by
  intro e f x y hef hxe hxf hye hyf
  apply Subtype.ext
  exact hlinear hef hxe hxf hye hyf

/-- The isolated-point reduction has no isolated points. -/
theorem isolatedReduction_hasNoIsolatedPoints :
    F.isolatedReduction.HasNoIsolatedPoints := by
  intro x hx
  exact x.property hx

end TripleSystem

end Erdos593
