import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportForestOrder

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dynamic leaf orders for bipartite incidence forests

For a finite set of left vertices in a bipartite forest, this module produces
an order in which each left vertex shares at most one right vertex with its
remaining tail.  The right-side carrier is pruned at every induction step to
points adjacent to at least two currently remaining left vertices.  This is
strictly weaker than requiring the projected left-overlap graph to be a
forest: many left vertices may share one common right vertex.

The sequence-lift-specific incidence graph is connected to this generic core
in a later module.
-/

namespace SimpleGraph

universe u v

variable {A : Type u} {P : Type v}

/-- The undirected bipartite graph induced by a left-to-right relation. -/
def bipartiteIncidenceGraph (r : A → P → Prop) : SimpleGraph (A ⊕ P) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl a, .inr p => r a p
    | _, _ => False

/-- The left-to-right adjacency predicate of `bipartiteIncidenceGraph`. -/
@[simp]
theorem bipartiteIncidenceGraph_adj_inl_inr_iff
    (r : A → P → Prop) (a : A) (p : P) :
    (bipartiteIncidenceGraph r).Adj (.inl a) (.inr p) ↔ r a p := by
  simp [bipartiteIncidenceGraph]

/-- The right-to-left adjacency predicate of `bipartiteIncidenceGraph`. -/
@[simp]
theorem bipartiteIncidenceGraph_adj_inr_inl_iff
    (r : A → P → Prop) (a : A) (p : P) :
    (bipartiteIncidenceGraph r).Adj (.inr p) (.inl a) ↔ r a p := by
  simp [bipartiteIncidenceGraph]

/-- Right vertices incident to at least two members of a finite left set. -/
def sharedRightPoints (r : A → P → Prop)
    [Fintype P] [DecidableEq P] [DecidableRel r]
    (t : Finset A) : Finset P :=
  Finset.univ.filter fun p => 2 ≤ (t.filter fun a => r a p).card

/-- The dynamically pruned incidence carrier: all current left vertices and
only right vertices shared by at least two of them. -/
def bipartitePruneVertices (r : A → P → Prop)
    [Fintype P] [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) : Finset (A ⊕ P) :=
  (t.image Sum.inl) ∪ ((sharedRightPoints r t).image Sum.inr)

@[simp]
theorem mem_sharedRightPoints
    (r : A → P → Prop) [Fintype P] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (p : P) :
    p ∈ sharedRightPoints r t ↔ 2 ≤ (t.filter fun a => r a p).card := by
  simp [sharedRightPoints]

@[simp]
theorem mem_bipartitePruneVertices_inl
    (r : A → P → Prop) [Fintype P]
    [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (a : A) :
    .inl a ∈ bipartitePruneVertices r t ↔ a ∈ t := by
  simp [bipartitePruneVertices]

@[simp]
theorem mem_bipartitePruneVertices_inr
    (r : A → P → Prop) [Fintype P]
    [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (p : P) :
    .inr p ∈ bipartitePruneVertices r t ↔ p ∈ sharedRightPoints r t := by
  simp [bipartitePruneVertices]

/-- A left-vertex order in which every head shares at most one right point
with a member of its remaining tail. -/
def bipartiteTailPointSubsingleton (r : A → P → Prop) : List A → Prop
  | [] => True
  | a :: tail =>
      bipartiteTailPointSubsingleton r tail ∧
        ∀ p p', r a p → r a p' →
          (∃ b ∈ tail, r b p) →
          (∃ c ∈ tail, r c p') → p = p'

/-- In a nonempty finite left set of a bipartite forest, some left vertex has
at most one neighbour in the dynamically pruned incidence graph.  A right
leaf is impossible because every retained right vertex has two left
neighbours. -/
theorem IsAcyclic.exists_bipartiteLeftVertex_adj_unique
    (r : A → P → Prop) [Fintype P] [DecidableEq A] [DecidableEq P]
    [DecidableRel r] (hG : (bipartiteIncidenceGraph r).IsAcyclic)
    {t : Finset A} (ht : t.Nonempty) :
    ∃ a ∈ t, ∀ ⦃z w : A ⊕ P⦄,
      z ∈ bipartitePruneVertices r t →
      w ∈ bipartitePruneVertices r t →
      (bipartiteIncidenceGraph r).Adj (.inl a) z →
      (bipartiteIncidenceGraph r).Adj (.inl a) w → z = w := by
  classical
  let s : Finset (A ⊕ P) := bipartitePruneVertices r t
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := ht
    exact ⟨.inl a, (mem_bipartitePruneVertices_inl r t a).mpr ha⟩
  let : Nonempty s := hs.to_subtype
  obtain ⟨q, hq⟩ :=
    SimpleGraph.IsAcyclic.exists_vertex_adj_unique
      (hG.induce (↑s : Set (A ⊕ P)))
  rcases q with ⟨q, hqmem⟩
  rcases q with a | p
  · have ha : a ∈ t := (mem_bipartitePruneVertices_inl r t a).mp hqmem
    refine ⟨a, ha, ?_⟩
    intro z w hz hw haz haw
    let qa : ↑(↑s : Set (A ⊕ P)) := ⟨.inl a, hqmem⟩
    let z' : ↑(↑s : Set (A ⊕ P)) := ⟨z, hz⟩
    let w' : ↑(↑s : Set (A ⊕ P)) := ⟨w, hw⟩
    have haz' :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa z' := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inl a) z
      exact haz
    have haw' :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa w' := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inl a) w
      exact haw
    have heq : z' = w' := hq haz' haw'
    simpa [z', w'] using! congrArg Subtype.val heq
  · have hp : p ∈ sharedRightPoints r t :=
      (mem_bipartitePruneVertices_inr r t p).mp hqmem
    have hcard : 2 ≤ (t.filter fun a => r a p).card :=
      (mem_sharedRightPoints r t p).mp hp
    have htwo : 1 < (t.filter fun a => r a p).card := by
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    rcases Finset.mem_filter.mp ha with ⟨ha, hap⟩
    rcases Finset.mem_filter.mp hb with ⟨hb, hbp⟩
    have hma : (.inl a : A ⊕ P) ∈ s :=
      (mem_bipartitePruneVertices_inl r t a).mpr ha
    have hmb : (.inl b : A ⊕ P) ∈ s :=
      (mem_bipartitePruneVertices_inl r t b).mpr hb
    let qa : ↑(↑s : Set (A ⊕ P)) := ⟨.inr p, hqmem⟩
    let za : ↑(↑s : Set (A ⊕ P)) := ⟨.inl a, hma⟩
    let zb : ↑(↑s : Set (A ⊕ P)) := ⟨.inl b, hmb⟩
    have hqza :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa za := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inr p) (.inl a)
      exact (bipartiteIncidenceGraph_adj_inr_inl_iff r a p).mpr hap
    have hqzb :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa zb := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inr p) (.inl b)
      exact (bipartiteIncidenceGraph_adj_inr_inl_iff r b p).mpr hbp
    have heq : za = zb := hq hqza hqzb
    have heq' : (.inl a : A ⊕ P) = .inl b := by
      simpa [za, zb] using! congrArg Subtype.val heq
    exact False.elim (hab (Sum.inl.inj heq'))

/-- Every finite set of left vertices in an acyclic bipartite incidence graph
has a noduplicated order with at most one shared right point at every head.
The point carrier is recomputed after each removal. -/
theorem IsAcyclic.exists_finset_bipartiteTailPointSubsingletonOrder
    (r : A → P → Prop) [Fintype P] [DecidableEq A] [DecidableEq P]
    [DecidableRel r] (hG : (bipartiteIncidenceGraph r).IsAcyclic)
    (t : Finset A) :
    ∃ l : List A,
      l.Nodup ∧ l.toFinset = t ∧ bipartiteTailPointSubsingleton r l := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
    by_cases ht : t.Nonempty
    · obtain ⟨a, ha, hleaf⟩ := hG.exists_bipartiteLeftVertex_adj_unique r ht
      obtain ⟨l, hlnd, hlt, hlcoh⟩ :=
        ih (t.erase a) (Finset.erase_ssubset ha)
      refine ⟨a :: l, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hlnd⟩
        intro hal
        have hae : a ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hal
        exact (Finset.mem_erase.mp hae).1 rfl
      · rw [List.toFinset_cons, hlt, Finset.insert_erase ha]
      · change bipartiteTailPointSubsingleton r l ∧
          ∀ p p', r a p → r a p' →
            (∃ b ∈ l, r b p) →
            (∃ c ∈ l, r c p') → p = p'
        refine ⟨hlcoh, ?_⟩
        intro p p' hap hap' hpt hp't
        rcases hpt with ⟨b, hb, hbp⟩
        rcases hp't with ⟨c, hc, hcp'⟩
        have hbe : b ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hb
        have hce : c ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hc
        have hbT : b ∈ t := (Finset.mem_erase.mp hbe).2
        have hcT : c ∈ t := (Finset.mem_erase.mp hce).2
        have hab : a ≠ b := by
          intro hab
          subst b
          exact (Finset.mem_erase.mp hbe).1 rfl
        have hac : a ≠ c := by
          intro hac
          subst c
          exact (Finset.mem_erase.mp hce).1 rfl
        have hpactive : (.inr p : A ⊕ P) ∈ bipartitePruneVertices r t := by
          rw [mem_bipartitePruneVertices_inr]
          rw [mem_sharedRightPoints]
          have hcard : 1 < (t.filter fun x => r x p).card :=
            Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hap⟩,
              b, Finset.mem_filter.mpr ⟨hbT, hbp⟩, hab⟩
          omega
        have hp'active : (.inr p' : A ⊕ P) ∈ bipartitePruneVertices r t := by
          rw [mem_bipartitePruneVertices_inr]
          rw [mem_sharedRightPoints]
          have hcard : 1 < (t.filter fun x => r x p').card :=
            Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hap'⟩,
              c, Finset.mem_filter.mpr ⟨hcT, hcp'⟩, hac⟩
          omega
        exact Sum.inr.inj (hleaf hpactive hp'active
          ((bipartiteIncidenceGraph_adj_inl_inr_iff r a p).mpr hap)
          ((bipartiteIncidenceGraph_adj_inl_inr_iff r a p').mpr hap'))
    · have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      exact ⟨[], by simp, by simp, trivial⟩

end SimpleGraph
