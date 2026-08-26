import ErdosProblems.Erdos593.TripleSystem.EdgeRestrictionReconstruction
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberObligatory
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupport
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Running assemblies of linear sequence-lift base fibres

The fibre-local constructibility theorem does not by itself permit a global
conclusion: distinct fibres can have interacting vertex supports.  This module
makes the missing finite gluing condition explicit.  A list is stored newest
first, and each new fibre must be edge-disjoint from the already assembled
tail and meet its total vertex support either in no point or in exactly one
point.  Under that condition, the general exact-restriction reconstruction API
assembles the local constructible pieces.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The geometric part of an auditable running assembly of base fibres.  The
list is newest first: the tail has already been assembled before the head is
attached.  The local constructibility requirement is supplied separately by
the linear, host-two-colourable fibre theorem. -/
def baseFiberAssemblyCompatible (S : Set (Edge G)) : List (Node G) → Prop
  | [] => True
  | q :: nodes =>
      baseFiberAssemblyCompatible S nodes ∧
      Disjoint
        (TripleSystem.edgePieceUnion (nodes.map (baseFiber S)))
        (baseFiber S q) ∧
      (Disjoint
          ((system G).edgeSupportSet
            (TripleSystem.edgePieceUnion (nodes.map (baseFiber S))))
          ((system G).edgeSupportSet (baseFiber S q)) ∨
        ∃ r : Point G,
          (system G).edgeSupportSet
              (TripleSystem.edgePieceUnion (nodes.map (baseFiber S))) ∩
            (system G).edgeSupportSet (baseFiber S q) = {r})

/-- Membership in a finite union of listed base fibres is exactly membership in
one fibre indexed by a node occurring in the list. -/
theorem mem_edgePieceUnion_baseFiberList
    (S : Set (Edge G)) (nodes : List (Node G)) {e : Edge G} :
    e ∈ TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) ↔
      ∃ q, q ∈ nodes ∧ e ∈ baseFiber S q := by
  induction nodes with
  | nil =>
      simp [TripleSystem.edgePieceUnion]
  | cons q nodes ih =>
      change
        (e ∈ TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) ∨
          e ∈ baseFiber S q) ↔ _
      constructor
      · rintro (he | he)
        · rcases ih.mp he with ⟨q', hq', heq'⟩
          exact ⟨q', List.mem_cons.mpr (Or.inr hq'), heq'⟩
        · exact ⟨q, List.mem_cons.mpr (Or.inl rfl), he⟩
      · rintro ⟨q', hq', he⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact Or.inr he
        · exact Or.inl (ih.mpr ⟨q', hq', he⟩)

/-- A listed family of base fibres covers exactly the edge set S as soon as it
contains the canonical base node of every edge of S. -/
theorem edgePieceUnion_baseFiber_eq_of_baseNode_mem
    {S : Set (Edge G)} (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes) :
    TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S := by
  ext e
  rw [mem_edgePieceUnion_baseFiberList]
  constructor
  · rintro ⟨q, hq, he⟩
    exact he.1
  · intro he
    exact ⟨baseNode e, hcover e he, ⟨he, rfl⟩⟩

/-- A finite selected edge set has a canonical finite list of its active base
nodes.  This list is an enumeration only; it does not assert any geometric
running order. -/
noncomputable def activeBaseNodeList
    (S : Set (Edge G)) (hS : S.Finite) : List (Node G) :=
  (@Finset.univ (activeBaseNodeIndex S) (activeBaseNodeIndexFintype hS)).toList.map
    Subtype.val

/-- The canonical finite active-base list covers the exact union of all
selected base fibres. -/
theorem edgePieceUnion_activeBaseNodeList
    {S : Set (Edge G)} (hS : S.Finite) :
    TripleSystem.edgePieceUnion
        ((activeBaseNodeList S hS).map (baseFiber S)) = S := by
  apply edgePieceUnion_baseFiber_eq_of_baseNode_mem (activeBaseNodeList S hS)
  intro e he
  let q : activeBaseNodeIndex S :=
    { val := baseNode e
      property := Exists.intro e (And.intro he rfl) }
  change List.Mem q.val
    ((@Finset.univ (activeBaseNodeIndex S)
      (activeBaseNodeIndexFintype hS)).toList.map Subtype.val)
  exact List.mem_map_of_mem
    (Finset.mem_toList.mpr
      (@Finset.mem_univ (activeBaseNodeIndex S)
        (activeBaseNodeIndexFintype hS) q))

/-- In a linear selected restriction, the canonical finite active-base
enumeration has singleton-or-empty pairwise support intersections.  This is
only pairwise geometry and does not by itself supply a running assembly
order. -/
theorem activeBaseNodeList_pairwise_support_inter_subsingleton_of_linear
    {S : Set (Edge G)} (hS : S.Finite)
    (hlin : ((system G).edgeRestriction S).Linear) :
    (activeBaseNodeList S hS).Pairwise
      (fun q u =>
        (((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S u))).Subsingleton) := by
  change
    ((@Finset.univ (activeBaseNodeIndex S)
      (activeBaseNodeIndexFintype hS)).toList.map Subtype.val).Pairwise _
  have hnodup :
      ((@Finset.univ (activeBaseNodeIndex S)
        (activeBaseNodeIndexFintype hS)).toList.map Subtype.val).Nodup :=
    (Finset.nodup_toList _).map Subtype.val_injective
  exact hnodup.pairwise_of_forall_ne (by
    intro q _ u _ hne
    exact baseFiber_support_inter_subsingleton_of_linear hlin hne)

/-- Finite linear base fibres over a two-colourable host form a generic
running edge assembly whenever their supports satisfy
`baseFiberAssemblyCompatible`. -/
theorem baseFiberAssemblyCompatible.runningEdgeAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) :
    ∀ nodes : List (Node G),
      baseFiberAssemblyCompatible S nodes →
        (system G).RunningEdgeAssembly (nodes.map (baseFiber S)) := by
  intro nodes hcompatible
  induction nodes with
  | nil =>
      simp [TripleSystem.RunningEdgeAssembly]
  | cons q nodes ih =>
      rcases hcompatible with ⟨htail, hEdges, hSupports⟩
      refine ⟨ih htail,
        baseFiber_constructible_of_linear_of_hostColorable hS q hlinear hG,
        ?_, ?_⟩
      · simpa [TripleSystem.edgePieceUnion] using! hEdges
      · simpa [TripleSystem.edgePieceUnion] using! hSupports

/-- A compatible finite list of linear base fibres covering an edge set makes
its exact sequence-lift restriction constructible.  The cover equality is
kept explicit so that this theorem does not claim an unsupported global fibre
partition. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_baseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hcompatible : baseFiberAssemblyCompatible S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) := by
  have hassembly :
      (system G).RunningEdgeAssembly (nodes.map (baseFiber S)) :=
    hcompatible.runningEdgeAssembly hS hlinear hG nodes
  have hconstructible :
      TripleSystem.Constructible
        ((system G).edgeRestriction
          (TripleSystem.edgePieceUnion (nodes.map (baseFiber S))) ) :=
    (system G).runningEdgeAssembly_constructible _ hassembly
  rw [hcover] at hconstructible
  exact hconstructible

/-- The exact cover premise in the compatible-assembly theorem follows from
the simpler requirement that the list contains every edge's canonical base
node. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_baseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hcompatible : baseFiberAssemblyCompatible S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_baseFiberAssembly
    hS hlinear hG nodes
    (edgePieceUnion_baseFiber_eq_of_baseNode_mem nodes hcover)
    hcompatible

/-- The canonical active-base enumeration removes the separate cover premise
from the compatible finite assembly theorem.  Its compatibility requirement
remains an explicit geometric obligation. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hcompatible : baseFiberAssemblyCompatible S (activeBaseNodeList S hS)) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_baseFiberAssembly
    hS hlinear hG (activeBaseNodeList S hS)
    (edgePieceUnion_activeBaseNodeList hS)
    hcompatible

/-- The preceding finite compatible assembly is obligatory, by the completed
classical positive-atom closure theorem for constructible triple systems. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_baseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hcompatible : baseFiberAssemblyCompatible S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  TripleSystem.Constructible.isObligatory
    (edgeRestriction_constructible_of_linear_of_hostColorable_of_baseFiberAssembly
      hS hlinear hG nodes hcover hcompatible)

/-- The canonical-base-node cover version of the compatible-assembly
obligatoriness theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_baseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hcompatible : baseFiberAssemblyCompatible S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  TripleSystem.Constructible.isObligatory
    (edgeRestriction_constructible_of_linear_of_hostColorable_of_baseNodeCover
      hS hlinear hG nodes hcover hcompatible)

/-- The canonical-active-base version of the compatible-assembly
obligatoriness theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_activeBaseNodeAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hcompatible : baseFiberAssemblyCompatible S (activeBaseNodeList S hS)) :
    ((system G).edgeRestriction S).IsObligatory :=
  TripleSystem.Constructible.isObligatory
    (edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeAssembly
      hS hlinear hG hcompatible)

end SequenceLift

end Erdos593
