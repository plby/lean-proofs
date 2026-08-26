import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberPartition

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite active-base indexing for sequence-lift fibres

This module reindexes canonical base fibres by the exact subtype of active base
nodes and gives the finite support bound induced by a finite embedded source.
It does not assert a fibre-cardinality sum or a global finite-trace
decomposition.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The subtype of exactly the active canonical base nodes of a selected family. -/
abbrev activeBaseNodeIndex (S : Set (Edge G)) : Type u :=
  {q : Node G // q ∈ activeBaseNodes S}

/-- A finite selected family has a finite active-base index subtype. -/
theorem finite_activeBaseNodeIndex {S : Set (Edge G)}
    (hS : S.Finite) :
    Finite (activeBaseNodeIndex S) :=
  (finite_activeBaseNodes_of_finite hS).to_subtype

/-- A chosen finite enumeration of the active-base index subtype of a finite
selected family. This is supplied explicitly rather than as a global instance. -/
@[reducible]
noncomputable def activeBaseNodeIndexFintype {S : Set (Edge G)}
    (hS : S.Finite) : Fintype (activeBaseNodeIndex S) := by
  letI : Finite (activeBaseNodeIndex S) := finite_activeBaseNodeIndex hS
  exact Fintype.ofFinite _

/-- Every active base-node index labels a nonempty canonical base fibre. -/
theorem baseFiber_nonempty_activeBaseNodeIndex
    (S : Set (Edge G)) (q : activeBaseNodeIndex S) :
    (baseFiber S q.1).Nonempty :=
  (baseFiber_nonempty_iff_mem_activeBaseNodes).2 q.2

/-- Canonical base fibres are pairwise disjoint when indexed by active base
nodes as a subtype. -/
theorem pairwiseDisjoint_baseFiber_activeBaseNodeIndex (S : Set (Edge G)) :
    Set.PairwiseDisjoint Set.univ
      (fun q : activeBaseNodeIndex S => baseFiber S q.1) := by
  intro q₁ _ q₂ _ hneq
  apply baseFiber_disjoint
  intro hq
  apply hneq
  exact Subtype.ext hq

/-- The active-base subtype reindexes the canonical base-fibre partition of a
selected family. -/
theorem iUnion_baseFiber_activeBaseNodeIndex (S : Set (Edge G)) :
    ⋃ q : activeBaseNodeIndex S, baseFiber S q.1 = S := by
  ext e
  constructor
  · intro he
    rcases Set.mem_iUnion.mp he with ⟨q, hq⟩
    exact hq.1
  · intro he
    refine Set.mem_iUnion.mpr ?_
    exact ⟨⟨baseNode e, ⟨e, he, rfl⟩⟩, ⟨he, rfl⟩⟩

/-- The canonical base-node index associated to a source edge of an embedding. -/
noncomputable def baseNodeIndexMap
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) :
    E → activeBaseNodeIndex f.edgeImage := fun i =>
  ⟨baseNode (f.edge i), ⟨f.edge i, ⟨i, rfl⟩, rfl⟩⟩

/-- Every active base-node index of an embedded source comes from a source edge. -/
theorem surjective_baseNodeIndexMap
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) :
    Function.Surjective (baseNodeIndexMap f) := by
  intro q
  rcases q.2 with ⟨e, ⟨i, rfl⟩, hq⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  simpa only [baseNodeIndexMap] using! hq

/-- The number of active canonical base nodes of a finite embedded source is at
most its number of source edges. -/
theorem activeBaseNodeIndex_natCard_le_edge_card
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) :
    Nat.card (activeBaseNodeIndex f.edgeImage) ≤ Fintype.card E := by
  calc
    Nat.card (activeBaseNodeIndex f.edgeImage) ≤ Nat.card E :=
      Nat.card_le_card_of_surjective _ (surjective_baseNodeIndexMap f)
    _ = Fintype.card E := Nat.card_eq_fintype_card

/-- The chosen finite active-base enumeration has cardinality at most the
number of source edges. -/
theorem activeBaseNodeIndex_card_le_edge_card
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) :
    @Fintype.card (activeBaseNodeIndex f.edgeImage)
      (activeBaseNodeIndexFintype (Set.finite_range f.edge)) ≤ Fintype.card E := by
  calc
    @Fintype.card (activeBaseNodeIndex f.edgeImage)
        (activeBaseNodeIndexFintype (Set.finite_range f.edge)) =
        Nat.card (activeBaseNodeIndex f.edgeImage) := Fintype.card_eq_nat_card
    _ ≤ Fintype.card E := activeBaseNodeIndex_natCard_le_edge_card f

end SequenceLift

end Erdos593
