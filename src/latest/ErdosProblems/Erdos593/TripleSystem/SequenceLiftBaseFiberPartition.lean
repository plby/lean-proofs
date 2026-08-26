import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical base-fibre support for sequence lifts

The canonical base-node map partitions any selected family of sequence-lift
edges into its base fibres.  This module records only the set-theoretic
partition and the finite support inherited from a finite selected family.  In
particular, it supplies neither a finite trace decomposition nor a cardinality
sum over the fibres.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Canonical base nodes which occur in a selected family of lift edges. -/
def activeBaseNodes (S : Set (Edge G)) : Set (Node G) :=
  baseNode '' S

@[simp]
theorem mem_activeBaseNodes {S : Set (Edge G)} {q : Node G} :
    q ∈ activeBaseNodes S ↔ ∃ e ∈ S, baseNode e = q :=
  Iff.rfl

/-- A canonical base fibre is nonempty exactly at an active base node. -/
theorem baseFiber_nonempty_iff_mem_activeBaseNodes
    {S : Set (Edge G)} {q : Node G} :
    (baseFiber S q).Nonempty ↔ q ∈ activeBaseNodes S := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, he.1, he.2⟩
  · rintro ⟨e, heS, heq⟩
    exact ⟨e, heS, heq⟩

/-- Distinct canonical base nodes have disjoint fibres. -/
theorem baseFiber_disjoint {S : Set (Edge G)} {q₁ q₂ : Node G}
    (hneq : q₁ ≠ q₂) :
    Disjoint (baseFiber S q₁) (baseFiber S q₂) := by
  refine Set.disjoint_left.2 ?_
  intro e he₁ he₂
  exact hneq (he₁.2.symm.trans he₂.2)

/-- The canonical base fibres form a pairwise-disjoint family. -/
theorem pairwiseDisjoint_baseFiber (S : Set (Edge G)) :
    Set.PairwiseDisjoint Set.univ (baseFiber S) := by
  intro q₁ _ q₂ _ hneq
  change Disjoint (baseFiber S q₁) (baseFiber S q₂)
  exact baseFiber_disjoint hneq

/-- The union of all canonical base fibres recovers the selected edge family. -/
theorem iUnion_baseFiber (S : Set (Edge G)) :
    ⋃ q : Node G, baseFiber S q = S := by
  ext e
  constructor
  · intro he
    rcases Set.mem_iUnion.mp he with ⟨q, hq⟩
    exact hq.1
  · intro he
    refine Set.mem_iUnion.mpr ?_
    exact ⟨baseNode e, ⟨he, rfl⟩⟩

/-- The active base nodes are sufficient to recover a selected edge family
from its canonical base fibres. -/
theorem iUnion_baseFiber_activeBaseNodes (S : Set (Edge G)) :
    ⋃ q ∈ activeBaseNodes S, baseFiber S q = S := by
  ext e
  constructor
  · intro he
    rcases Set.mem_iUnion.mp he with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨_, hfiber⟩
    exact hfiber.1
  · intro he
    refine Set.mem_iUnion.mpr ⟨baseNode e, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ⟨he, rfl⟩⟩
    exact ⟨e, he, rfl⟩

/-- A finite selected family has finite canonical base-node support. -/
theorem finite_activeBaseNodes_of_finite {S : Set (Edge G)}
    (hS : S.Finite) :
    (activeBaseNodes S).Finite := by
  exact hS.image baseNode

/-- A finite embedded source has finite canonical base-node support. -/
theorem finite_activeBaseNodes_edgeImage
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) :
    (activeBaseNodes f.edgeImage).Finite := by
  exact finite_activeBaseNodes_of_finite (Set.finite_range f.edge)

end SequenceLift

end Erdos593
