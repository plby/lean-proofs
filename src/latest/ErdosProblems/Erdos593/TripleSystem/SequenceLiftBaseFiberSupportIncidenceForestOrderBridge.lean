import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceForestOrder
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceGraph
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportRunningOrder

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From incidence forests to coherent base-fibre orders

The generic bipartite incidence-forest ordering theorem removes a base fibre
only after pruning the point side to points shared by at least two remaining
fibres.  Here that order is transported to the sequence-lift base fibres.
Linearity upgrades the resulting statement that all shared points agree into
equality of the corresponding support intersections, which is exactly the
coherence hypothesis required by the running base-fibre assembly API.

The incidence-acyclicity hypothesis remains explicit.  In particular, this
module does not replace it by pairwise linearity or by acyclicity of the
stronger projected support-overlap graph.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Support points of a base fibre lie in the total support of the selected
family, so they can be used as vertices of the finite incidence graph. -/
theorem edgeSupportSet_baseFiber_subset
    (S : Set (Edge G)) (q : Node G) :
    (system G).edgeSupportSet (baseFiber S q) ⊆
      (system G).edgeSupportSet S := by
  rintro p ⟨e, he, hp⟩
  exact ⟨e, (baseFiber_subset S q) he, hp⟩

/-- Lift a support point of one base fibre to the active point-side carrier of
the incidence graph. -/
def activeBaseFiberSupportPointIndex_of_mem_baseFiberSupport
    {S : Set (Edge G)} {q : Node G} {p : Point G}
    (hp : p ∈ (system G).edgeSupportSet (baseFiber S q)) :
    activeBaseFiberSupportPointIndex S :=
  ⟨p, edgeSupportSet_baseFiber_subset S q hp⟩

@[simp]
theorem activeBaseFiberSupportPointIndex_of_mem_baseFiberSupport_val
    {S : Set (Edge G)} {q : Node G} {p : Point G}
    (hp : p ∈ (system G).edgeSupportSet (baseFiber S q)) :
    (activeBaseFiberSupportPointIndex_of_mem_baseFiberSupport hp).1 = p := rfl

/-- Under linearity, if the support intersections of a head fibre with two
distinct tail fibres both contain the same point, then those intersections
are equal. -/
theorem baseFiber_support_inter_eq_of_linear_of_ne_of_mem
    {S : Set (Edge G)} {q u v : Node G}
    (hlin : ((system G).edgeRestriction S).Linear)
    (hqu : q ≠ u) (hqv : q ≠ v)
    {p : Point G}
    (hpq : p ∈ (system G).edgeSupportSet (baseFiber S q))
    (hpu : p ∈ (system G).edgeSupportSet (baseFiber S u))
    (hpv : p ∈ (system G).edgeSupportSet (baseFiber S v)) :
    ((system G).edgeSupportSet (baseFiber S q) ∩
      (system G).edgeSupportSet (baseFiber S u)) =
      ((system G).edgeSupportSet (baseFiber S q) ∩
        (system G).edgeSupportSet (baseFiber S v)) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxp : x = p :=
      baseFiber_support_inter_subsingleton_of_linear hlin hqu hx ⟨hpq, hpu⟩
    subst x
    exact ⟨hpq, hpv⟩
  · intro x hx
    have hxp : x = p :=
      baseFiber_support_inter_subsingleton_of_linear hlin hqv hx ⟨hpq, hpv⟩
    subst x
    exact ⟨hpq, hpu⟩

/-- A generic dynamic incidence order of active base-fibre indices becomes a
coherent support-tail-overlap order of the corresponding base nodes. -/
theorem baseFiberSupportTailOverlapCoherent_of_bipartiteTailPointSubsingleton
    {S : Set (Edge G)} {qs : List (activeBaseNodeIndex S)}
    (hlin : ((system G).edgeRestriction S).Linear)
    (hnodup : qs.Nodup)
    (htail : SimpleGraph.bipartiteTailPointSubsingleton
      (fun (q : activeBaseNodeIndex S)
          (p : activeBaseFiberSupportPointIndex S) =>
        p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1)) qs) :
    baseFiberSupportTailOverlapCoherent S (qs.map Subtype.val) := by
  induction qs with
  | nil =>
      simp [baseFiberSupportTailOverlapCoherent]
  | cons q qs ih =>
      rw [List.nodup_cons] at hnodup
      rcases htail with ⟨htail, hpoints⟩
      change baseFiberSupportTailOverlapCoherent S (qs.map Subtype.val) ∧
        ∀ u ∈ qs.map Subtype.val, ∀ v ∈ qs.map Subtype.val,
          (((system G).edgeSupportSet (baseFiber S q.1) ∩
            (system G).edgeSupportSet (baseFiber S u)).Nonempty) →
          (((system G).edgeSupportSet (baseFiber S q.1) ∩
            (system G).edgeSupportSet (baseFiber S v)).Nonempty) →
          ((system G).edgeSupportSet (baseFiber S q.1) ∩
            (system G).edgeSupportSet (baseFiber S u)) =
            ((system G).edgeSupportSet (baseFiber S q.1) ∩
              (system G).edgeSupportSet (baseFiber S v))
      refine ⟨ih hnodup.2 htail, ?_⟩
      intro u hu v hv hqu hqv
      obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hu
      obtain ⟨v', hv', rfl⟩ := List.mem_map.1 hv
      rcases hqu with ⟨p, hpq, hpu⟩
      rcases hqv with ⟨p', hpq', hpv⟩
      let pI : activeBaseFiberSupportPointIndex S :=
        activeBaseFiberSupportPointIndex_of_mem_baseFiberSupport hpq
      let pI' : activeBaseFiberSupportPointIndex S :=
        activeBaseFiberSupportPointIndex_of_mem_baseFiberSupport hpq'
      have hpIeq : pI = pI' := hpoints pI pI'
        (by simpa [pI] using! hpq)
        (by simpa [pI'] using! hpq')
        ⟨u', hu', by simpa [pI] using! hpu⟩
        ⟨v', hv', by simpa [pI'] using! hpv⟩
      have hpp' : p = p' := by
        simpa [pI, pI'] using! congrArg Subtype.val hpIeq
      have hqu' : q.1 ≠ u'.1 := by
        intro hqeu
        apply hnodup.1
        have hqe : q = u' := Subtype.ext hqeu
        simpa [hqe] using! hu'
      have hqv' : q.1 ≠ v'.1 := by
        intro hqev
        apply hnodup.1
        have hqe : q = v' := Subtype.ext hqev
        simpa [hqe] using! hv'
      subst p'
      exact baseFiber_support_inter_eq_of_linear_of_ne_of_mem hlin hqu' hqv'
        hpq hpu hpv

/-- The sequence-lift incidence graph is the generic bipartite incidence graph
of base-fibre support membership. -/
theorem baseFiberSupportIncidenceGraph_eq_bipartiteIncidenceGraph
    (S : Set (Edge G)) :
    baseFiberSupportIncidenceGraph S =
      SimpleGraph.bipartiteIncidenceGraph
        (fun (q : activeBaseNodeIndex S)
            (p : activeBaseFiberSupportPointIndex S) =>
          p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1)) := by
  ext x y
  rcases x with q | p <;> rcases y with r | s <;>
    simp [baseFiberSupportIncidenceGraph, SimpleGraph.bipartiteIncidenceGraph,
      SimpleGraph.fromRel_adj]

/-- Acyclicity of the sequence-lift incidence graph is exactly acyclicity of
the corresponding generic bipartite incidence graph. -/
theorem baseFiberSupportIncidenceGraph_isAcyclic_iff
    (S : Set (Edge G)) :
    (baseFiberSupportIncidenceGraph S).IsAcyclic ↔
      (SimpleGraph.bipartiteIncidenceGraph
        (fun (q : activeBaseNodeIndex S)
            (p : activeBaseFiberSupportPointIndex S) =>
          p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1))).IsAcyclic := by
  rw [baseFiberSupportIncidenceGraph_eq_bipartiteIncidenceGraph]

/-- A finite linear selected family with acyclic bipartite base-fibre support
incidence graph admits a noduplicated base-node cover with coherent support
intersections along its tail order. -/
theorem exists_baseFiberSupportTailOverlapCoherent_order_of_incidenceAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlin : ((system G).edgeRestriction S).Linear)
    (hacyclic : (baseFiberSupportIncidenceGraph S).IsAcyclic) :
    ∃ nodes : List (Node G),
      nodes.Nodup ∧
        (∀ e, e ∈ S → baseNode e ∈ nodes) ∧
        baseFiberSupportTailOverlapCoherent S nodes := by
  classical
  let : Fintype (activeBaseNodeIndex S) := activeBaseNodeIndexFintype hS
  let : Fintype (activeBaseFiberSupportPointIndex S) :=
    activeBaseFiberSupportPointIndexFintype hS
  have hG :
      (SimpleGraph.bipartiteIncidenceGraph
        (fun (q : activeBaseNodeIndex S)
            (p : activeBaseFiberSupportPointIndex S) =>
          p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1))).IsAcyclic := by
    rw [← baseFiberSupportIncidenceGraph_eq_bipartiteIncidenceGraph]
    exact hacyclic
  obtain ⟨qs, hnodup, hqs, htail⟩ :=
    hG.exists_finset_bipartiteTailPointSubsingletonOrder
      (fun (q : activeBaseNodeIndex S)
          (p : activeBaseFiberSupportPointIndex S) =>
        p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1)) Finset.univ
  refine ⟨qs.map Subtype.val, hnodup.map Subtype.val_injective, ?_, ?_⟩
  · intro e he
    let q : activeBaseNodeIndex S := ⟨baseNode e, ⟨e, he, rfl⟩⟩
    have hqmemFinset : q ∈ qs.toFinset := by
      rw [hqs]
      exact Finset.mem_univ q
    have hqmem : q ∈ qs := List.mem_toFinset.mp hqmemFinset
    change q.1 ∈ qs.map Subtype.val
    exact List.mem_map_of_mem hqmem
  · exact baseFiberSupportTailOverlapCoherent_of_bipartiteTailPointSubsingleton
      hlin hnodup htail

/-- The incidence-forest order immediately provides the compatibility premise
for the existing recursive base-fibre assembly theorem. -/
theorem exists_baseFiberAssemblyCompatible_order_of_linear_of_incidenceAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlin : ((system G).edgeRestriction S).Linear)
    (hacyclic : (baseFiberSupportIncidenceGraph S).IsAcyclic) :
    ∃ nodes : List (Node G),
      nodes.Nodup ∧
        (∀ e, e ∈ S → baseNode e ∈ nodes) ∧
        baseFiberAssemblyCompatible S nodes := by
  obtain ⟨nodes, hnodup, hcover, hcoherent⟩ :=
    exists_baseFiberSupportTailOverlapCoherent_order_of_incidenceAcyclic
      hS hlin hacyclic
  exact ⟨nodes, hnodup, hcover,
    baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlin hnodup hcoherent⟩

end SequenceLift

end Erdos593
