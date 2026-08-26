import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberFactor
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseIncidence
import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.Isomorph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Private-vertex expansions of linear sequence-lift base fibres

This module identifies one chosen linear base fibre with the private-vertex
expansion of the graph selected by its canonical base letters.  The result is
strictly local in the selected edge set and the selected base node.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

private noncomputable def baseFiberExpansionEdgeEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.edgeSet ≃
      baseFiber S q :=
  baseFiberLetterSubgraphEdgeEquiv_of_linear q hlinear

private theorem baseFiberExpansionEdgeEquiv_baseLetter
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (j : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.edgeSet) :
    baseLetter ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) =
      (baseLetterSubgraphEdgeEquiv G (baseLetter '' baseFiber S q) j).1 := by
  let psi := baseFiberEquivBaseLetterImage_of_linear q hlinear
  let theta := baseLetterSubgraphEdgeEquiv G (baseLetter '' baseFiber S q)
  change baseLetter ((psi.symm (theta j)).1) = (theta j).1
  exact congrArg Subtype.val (psi.apply_symm_apply (theta j))

private theorem baseFiberExpansionEdgeEquiv_core_mem_iff
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (x : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts)
    (j : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.edgeSet) :
    x ∈ (j.1 : Sym2 (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts) ↔
      (x : V) ∈
        (baseLetter ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)).1 := by
  rw [baseFiberExpansionEdgeEquiv_baseLetter q hlinear j]
  change x ∈ j.1 ↔ (x : V) ∈
    Sym2.map (fun y : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts =>
      (y : V)) j.1
  constructor
  · intro hx
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    rcases Sym2.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hxy' : x = y := Subtype.ext hxy.symm
    simpa [hxy'] using! hy

private noncomputable def baseFiberExpansionPointEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    TripleSystem.PrivateVertexExpansion.Point
      (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe ≃
      (system G).EdgeSupport (baseFiber S q) := by
  classical
  let K := baseLetterSubgraph G (baseLetter '' baseFiber S q)
  let edgeEquiv : K.coe.edgeSet ≃ baseFiber S q :=
    baseFiberExpansionEdgeEquiv_of_linear q hlinear
  let f : TripleSystem.PrivateVertexExpansion.Point K.coe →
      (system G).EdgeSupport (baseFiber S q) := fun p =>
    match p with
    | .inl x =>
        ⟨(q, (x : V)), by
          rcases x.2 with ⟨a, ha, hx⟩
          rcases ha with ⟨e, he, hletter⟩
          refine ⟨e, he,
            (inc_iff_baseNode_baseLetter_or_baseApex G e (q, (x : V))).2 (Or.inl ?_)⟩
          constructor
          · exact he.2.symm
          · simpa [hletter] using! hx⟩
    | .inr j =>
        let e := edgeEquiv j
        ⟨baseApex e.1, ⟨e.1, e.2, inc_baseApex e.1⟩⟩
  exact Equiv.ofBijective f (by
    constructor
    · intro a b hab
      rcases a with x | j <;> rcases b with y | k
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun z => z.2) (congrArg Subtype.val hab)
      · exfalso
        have hnode := congrArg (fun z => z.1) (congrArg Subtype.val hab)
        change q = (baseApex (edgeEquiv k).1).1 at hnode
        exact baseApex_node_ne_baseNode (edgeEquiv k).1
          (hnode.symm.trans (edgeEquiv k).2.2.symm)
      · exfalso
        have hnode := congrArg (fun z => z.1) (congrArg Subtype.val hab)
        change (baseApex (edgeEquiv j).1).1 = q at hnode
        exact baseApex_node_ne_baseNode (edgeEquiv j).1
          (hnode.trans (edgeEquiv j).2.2.symm)
      · apply congrArg Sum.inr
        apply edgeEquiv.injective
        apply Subtype.ext
        apply baseApex_injOn_baseFiber_of_linear q hlinear (edgeEquiv j).2 (edgeEquiv k).2
        exact congrArg Subtype.val hab
    · intro p
      rcases p with ⟨p, hp⟩
      change (∃ e : Edge G, e ∈ baseFiber S q ∧ (system G).Inc p e) at hp
      rcases hp with ⟨e, he, hInc⟩
      rcases (inc_iff_baseNode_baseLetter_or_baseApex G e p).1 hInc with hcore | hapex
      · let x : K.verts := ⟨p.2, ⟨baseLetter e, ⟨e, he, rfl⟩, hcore.2⟩⟩
        refine ⟨.inl x, ?_⟩
        apply Subtype.ext
        exact Prod.ext (hcore.1.trans he.2).symm rfl
      · let j : K.coe.edgeSet := edgeEquiv.symm ⟨e, he⟩
        refine ⟨.inr j, ?_⟩
        apply Subtype.ext
        change baseApex (edgeEquiv j).1 = p
        rw [show edgeEquiv j = ⟨e, he⟩ by simp [j]]
        exact hapex.symm)

/-- If the selected sequence-lift edge restriction is linear, then its fibre
over `q` is isomorphic to the private-vertex expansion of the subgraph whose
edges are exactly the fibre's canonical base letters. -/
noncomputable def baseFiber_privateVertexExpansionIso_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    TripleSystem.Iso
      (TripleSystem.privateVertexExpansion
        (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe)
      ((system G).edgeRestriction (baseFiber S q)) where
  vertexEquiv := baseFiberExpansionPointEquiv_of_linear q hlinear
  edgeEquiv := baseFiberExpansionEdgeEquiv_of_linear q hlinear
  map_inc_iff := by
    intro p j
    rcases p with x | k
    · change x ∈ (j.1 : Sym2 (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts) ↔
        (system G).Inc (q, (x : V))
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
      constructor
      · intro hx
        apply (inc_iff_baseNode_baseLetter_or_baseApex G
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) (q, (x : V))).2
        exact Or.inl ⟨(baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2.2.symm,
          (baseFiberExpansionEdgeEquiv_core_mem_iff q hlinear x j).1 hx⟩
      · intro hInc
        rcases (inc_iff_baseNode_baseLetter_or_baseApex G
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) (q, (x : V))).1 hInc with
          hcore | hapex
        · exact (baseFiberExpansionEdgeEquiv_core_mem_iff q hlinear x j).2 hcore.2
        · exfalso
          have hnode := congrArg Prod.fst hapex
          exact baseApex_node_ne_baseNode
            ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
            (hnode.symm.trans
              (baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2.2.symm)
    · change k = j ↔
        (system G).Inc
          (baseApex ((baseFiberExpansionEdgeEquiv_of_linear q hlinear k).1))
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
      rw [baseApex_inc_iff_eq_of_linear q hlinear
        (baseFiberExpansionEdgeEquiv_of_linear q hlinear k).2
        (baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2]
      constructor
      · intro h
        simp [h]
      · intro h
        apply (baseFiberExpansionEdgeEquiv_of_linear q hlinear).injective
        apply Subtype.ext
        exact h

/-- Finite fibre-local wrapper for the selected base-letter subgraph: it
exhibits its exact vertex subtype with a `Fintype` instance, its canonical
non-induced factor into the host graph, and the private-vertex-expansion
isomorphism of the chosen base fibre. -/
theorem exists_fintype_baseFiberLetterSubgraphFactorExpansionIso_of_linear
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    Exists (fun _ : Fintype
      (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts =>
      And
        (Nonempty (Erdos593.SimpleGraph.NonInducedFactor
          (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe G))
        (Nonempty (TripleSystem.Iso
          (TripleSystem.privateVertexExpansion
            (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe)
          ((system G).edgeRestriction (baseFiber S q))))) := by
  classical
  letI : Finite (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts :=
    Set.finite_coe_iff.mpr <|
      baseLetterSubgraph_finite_verts G <|
        (hS.subset (baseFiber_subset S q)).image baseLetter
  letI : Fintype (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts :=
    Fintype.ofFinite _
  apply Exists.intro (inferInstance : Fintype
    (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts)
  exact And.intro
    (Nonempty.intro (baseFiberLetterSubgraphFactor S q))
    (Nonempty.intro (baseFiber_privateVertexExpansionIso_of_linear q hlinear))

end SequenceLift

end Erdos593
