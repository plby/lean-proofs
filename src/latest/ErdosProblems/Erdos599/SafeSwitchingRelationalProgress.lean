/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalBalance

/-!
# Unused forward incidence in the safe-route recursion

These are positive progress lemmas for a finite balanced prefix. They do
not assume the false nonadjacent-link compatibility of the raw-run
compiler. The geometric source constructor must still produce the prefix
balance, contact-removal and first-contact invariants.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A backward-ending balanced prefix has not yet used its next forward
edge. This is the strict-progress invariant missing from the bare order
argument in the source. -/
theorem no_forward_outgoing_at_backward_exit
    {F R : Set (V × V)} {s a : V} (hsa : s ≠ a)
    (hbalance : edgeBalance F a - edgeBalance R a =
      propInt (a = s) - propInt (a = a))
    (hRout : HasOutgoing R a)
    (hin : HasIncoming F a → HasIncoming R a) :
    ¬HasOutgoing F a := by
  classical
  intro hFout
  have has : a ≠ s := Ne.symm hsa
  by_cases hFin : HasIncoming F a
  · have hRin := hin hFin
    simp [edgeBalance, propInt, hFout, hRout, hFin, hRin, has] at hbalance
  · by_cases hRin : HasIncoming R a <;>
      simp [edgeBalance, propInt, hFout, hRout, hFin, hRin, has] at hbalance

/-- Away from both ends of a balanced prefix, an initial of the inserted
edge relation is also a lower boundary of the removed relation. -/
theorem removed_lower_boundary_of_forward_lower_boundary
    {F R : Set (V × V)} {s a x : V}
    (hbalance : edgeBalance F x - edgeBalance R x =
      propInt (x = s) - propInt (x = a))
    (hxs : x ≠ s) (hxa : x ≠ a)
    (hFout : HasOutgoing F x) (hFin : ¬HasIncoming F x) :
    HasOutgoing R x ∧ ¬HasIncoming R x := by
  classical
  have hRbalance : edgeBalance R x = 1 := by
    have hFb : edgeBalance F x = 1 :=
      edgeBalance_eq_one_iff.mpr ⟨hFout, hFin⟩
    simp only [hFb, propInt, if_neg hxs, if_neg hxa] at hbalance
    omega
  exact edgeBalance_eq_one_iff.mp hRbalance

/-- Along an original-warp walk, entering the inserted relation from a
vertex with no inserted incoming edge passes through a lower boundary of
the inserted relation. The proof scans the finite walk, using uniqueness
of the original incoming edge at each step. -/
theorem walk_meets_forward_lower_boundary
    {W : Set Gamma.DPath} {F : Set (V × V)} (hW : Gamma.IsWarp W)
    (hF : F ⊆ familyEdges W) {a b : V} (p : Walk Gamma.graph a b)
    (hp : p.edgeSet ⊆ familyEdges W)
    (ha : ¬HasIncoming F a) (hb : HasIncoming F b) :
    ∃ x ∈ p.support, HasOutgoing F x ∧ ¬HasIncoming F x := by
  induction p with
  | nil => exact (ha hb).elim
  | @cons a c b hac p ih =>
      have hacW : (a, c) ∈ familyEdges W := hp (by simp [Walk.edgeSet])
      have hpW : p.edgeSet ⊆ familyEdges W := by
        intro e he
        exact hp (by simp [Walk.edgeSet, he])
      by_cases hacF : (a, c) ∈ F
      · exact ⟨a, by simp [Walk.support], ⟨c, hacF⟩, ha⟩
      · have hc : ¬HasIncoming F c := by
          rintro ⟨z, hz⟩
          have hza : z = a := (IsWarp.familyEdges_biUnique hW).1 (hF hz) hacW
          exact hacF (hza ▸ hz)
        obtain ⟨x, hx, hxo, hxi⟩ := ih hpW hc hb
        exact ⟨x, by simp [Walk.support, hx], hxo, hxi⟩

/-- If a nontrivial forward segment starts at an unused outgoing port but
ends at an already-used incoming port, it encounters an old forward lower
boundary strictly between its two endpoints. -/
theorem finitePath_meets_forward_lower_boundary_interior
    {W : Set Gamma.DPath} {F : Set (V × V)} (hW : Gamma.IsWarp W)
    (hF : F ⊆ familyEdges W) (p : FinitePath Gamma.graph)
    (hpne : p.start ≠ p.finish) (hp : p.edgeSet ⊆ familyEdges W)
    (hstart : ¬HasOutgoing F p.start) (hfinish : HasIncoming F p.finish) :
    ∃ x ∈ p.support, x ≠ p.start ∧ x ≠ p.finish ∧
      HasOutgoing F x ∧ ¬HasIncoming F x := by
  have hwalk : ∀ {a b : V} (q : Walk Gamma.graph a b),
      a ≠ b → q.edgeSet ⊆ familyEdges W → ¬HasOutgoing F a →
      HasIncoming F b →
      ∃ x ∈ q.support, x ≠ a ∧ x ≠ b ∧
        HasOutgoing F x ∧ ¬HasIncoming F x := by
    intro a b q hab hq ha hb
    cases q with
    | nil => exact (hab rfl).elim
    | @cons a c b hac q =>
        have hacW : (a, c) ∈ familyEdges W := hq (by simp [Walk.edgeSet])
        have hc : ¬HasIncoming F c := by
          rintro ⟨z, hz⟩
          have hza : z = a := (IsWarp.familyEdges_biUnique hW).1 (hF hz) hacW
          exact ha ⟨c, hza ▸ hz⟩
        have hqW : q.edgeSet ⊆ familyEdges W := by
          intro e he
          exact hq (by simp [Walk.edgeSet, he])
        obtain ⟨x, hx, hxo, hxi⟩ :=
          walk_meets_forward_lower_boundary hW hF q hqW hc hb
        refine ⟨x, by simp [Walk.support, hx], ?_, ?_, hxo, hxi⟩
        · intro hxa
          exact ha (hxa ▸ hxo)
        · intro hxb
          exact hxi (hxb ▸ hb)
  exact hwalk p.walk hpne hp hstart hfinish

/-- First-contact purity rules out return to an old incoming forward
contact, once lower boundaries are known to be genuine contact vertices.
The two endpoints themselves are allowed in the contact set. -/
theorem firstContact_has_no_old_forward_incoming
    {W : Set Gamma.DPath} {F : Set (V × V)} {C : Set V}
    (hW : Gamma.IsWarp W) (hF : F ⊆ familyEdges W)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hstart : ¬HasOutgoing F p.start)
    (hfirst : p.support ∩ C ⊆ {p.start, p.finish})
    (hlower : ∀ x ∈ p.support, x ≠ p.start → x ≠ p.finish →
      HasOutgoing F x → ¬HasIncoming F x → x ∈ C) :
    ¬HasIncoming F p.finish := by
  intro hfinish
  obtain ⟨x, hxp, hxs, hxt, hxo, hxi⟩ :=
    finitePath_meets_forward_lower_boundary_interior hW hF p hpne hp hstart hfinish
  have hx := hfirst ⟨hxp, hlower x hxp hxs hxt hxo hxi⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  exact hx.elim hxs hxt

/-- The open interior of a removed reference interval is recognized by
having both a removed incoming and a removed outgoing edge. This incidence
definition also includes old contact points between adjacent removed links. -/
def removedInterior (R : Set (V × V)) : Set V :=
  {x | HasIncoming R x ∧ HasOutgoing R x}

/-- Contact removal and initial purity discharge the incoming-incidence
premise at an actual backward exit on a finite reference warp. -/
theorem no_forward_outgoing_at_backward_exit_of_reference
    {Y : Set Gamma.DPath} {F R : Set (V × V)}
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hR : R ⊆ familyEdges Y)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hpure : ∀ {x y : V}, (x, y) ∈ F → y ∉ Gamma.initialSet Y)
    {s a : V} (hsa : s ≠ a)
    (hbalance : edgeBalance F a - edgeBalance R a =
      propInt (a = s) - propInt (a = a))
    (hRout : HasOutgoing R a) : ¬HasOutgoing F a := by
  apply no_forward_outgoing_at_backward_exit hsa hbalance hRout
  rintro ⟨x, hxF⟩
  have haY : a ∈ Gamma.vertexSet Y := by
    obtain ⟨b, hb⟩ := hRout
    exact (familyEdges_subset_vertexSet_prod Y (hR hb)).1
  have haIn : HasIncoming (familyEdges Y) a := by
    by_contra hnot
    apply hpure hxF
    rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin]
    exact ⟨haY, hnot⟩
  obtain ⟨b, hb⟩ := haIn
  exact ⟨b, hin hxF hb⟩

/-- With the exact finite-prefix balance, all the lower-boundary contact
hypotheses in `firstContact_has_no_old_forward_incoming` follow from the
reference geometry. In particular a first new contact cannot equal an old
upper contact, which already has an incoming forward edge. -/
theorem firstReferenceContact_has_no_old_forward_incoming_of_balance
    {W Y : Set Gamma.DPath} {F R : Set (V × V)}
    (hW : Gamma.IsWarp W) (hF : F ⊆ familyEdges W)
    (hR : R ⊆ familyEdges Y)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hstart : ¬HasOutgoing F p.start)
    {s : V} (hs : s ∉ p.support)
    (hbalance : ∀ x, edgeBalance F x - edgeBalance R x =
      propInt (x = s) - propInt (x = p.start))
    (hfirst : p.support ∩ (Gamma.vertexSet Y \ removedInterior R) ⊆
      {p.start, p.finish}) : ¬HasIncoming F p.finish := by
  apply firstContact_has_no_old_forward_incoming hW hF p hpne hp hstart hfirst
  intro x hxp hxs _hxt hxo hxi
  have hxu : x ≠ s := by
    intro heq
    exact hs (heq ▸ hxp)
  have hxR := removed_lower_boundary_of_forward_lower_boundary
    (hbalance x) hxu hxs hxo hxi
  obtain ⟨y, hy⟩ := hxR.1
  refine ⟨(familyEdges_subset_vertexSet_prod Y (hR hy)).1, ?_⟩
  exact fun h ↦ hxR.2 h.1

/-- Common terminal purity closes the source proof's contact-free-tail
case: a forward terminal cannot be hidden in a removed reference interior.
No such claim is made for arbitrary endpoint-impure warps. -/
theorem terminal_outside_reference_of_no_new_contact
    {W Y : Set Gamma.DPath} {R : Set (V × V)}
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hR : R ⊆ familyEdges Y)
    (hpure : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {t : V} (htW : t ∈ Gamma.terminalFrontier W)
    (hno : t ∉ Gamma.vertexSet Y \ removedInterior R) :
    t ∉ Gamma.vertexSet Y := by
  intro htY
  have htR : t ∈ removedInterior R := by
    by_contra hnot
    exact hno ⟨htY, hnot⟩
  have htTerm := hpure ⟨htW, htY⟩
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin] at htTerm
  obtain ⟨b, hb⟩ := htR.2
  exact htTerm.2 ⟨b, hR hb⟩

/-- An actual old forward edge on a finite original-warp walk has an old
forward lower boundary no later than its tail, unless the initial vertex
already has an old incoming edge. The returned lower boundary has an
outgoing edge on the walk itself. -/
theorem walk_meets_forward_lower_boundary_of_edge
    {W : Set Gamma.DPath} {F : Set (V × V)} (hW : Gamma.IsWarp W)
    (hF : F ⊆ familyEdges W) {a b : V} (p : Walk Gamma.graph a b)
    (hp : p.edgeSet ⊆ familyEdges W) (ha : ¬HasIncoming F a)
    (hmeet : (p.edgeSet ∩ F).Nonempty) :
    ∃ x ∈ p.support, HasOutgoing p.edgeSet x ∧
      HasOutgoing F x ∧ ¬HasIncoming F x := by
  induction p with
  | nil => simp [Walk.edgeSet] at hmeet
  | @cons a c b hac p ih =>
      have hacW : (a, c) ∈ familyEdges W := hp (by simp [Walk.edgeSet])
      have hpW : p.edgeSet ⊆ familyEdges W := by
        intro e he
        exact hp (by simp [Walk.edgeSet, he])
      by_cases hacF : (a, c) ∈ F
      · exact ⟨a, by simp [Walk.support],
          ⟨c, by simp [Walk.edgeSet]⟩, ⟨c, hacF⟩, ha⟩
      · have hc : ¬HasIncoming F c := by
          rintro ⟨z, hz⟩
          have hza : z = a := (IsWarp.familyEdges_biUnique hW).1 (hF hz) hacW
          exact hacF (hza ▸ hz)
        have hmeetTail : (p.edgeSet ∩ F).Nonempty := by
          obtain ⟨e, he, heF⟩ := hmeet
          simp only [Walk.edgeSet_cons] at he
          rcases he with he | he
          · exact (hacF (he ▸ heF)).elim
          · exact ⟨e, he, heF⟩
        obtain ⟨x, hx, ⟨y, hxy⟩, hxo, hxi⟩ := ih hpW hc hmeetTail
        exact ⟨x, by simp [Walk.support, hx],
          ⟨y, by simp [Walk.edgeSet, hxy]⟩, hxo, hxi⟩

/-- The entire newly scanned forward fragment is fresh, not just its
first edge. This is the constructor-facing same-colour freshness condition
for appending the fragment to an occurrence word. -/
theorem firstReferenceContact_forward_edges_fresh
    {W Y : Set Gamma.DPath} {F R : Set (V × V)}
    (hW : Gamma.IsWarp W) (hF : F ⊆ familyEdges W)
    (hR : R ⊆ familyEdges Y)
    (p : FinitePath Gamma.graph) (hp : p.edgeSet ⊆ familyEdges W)
    (hstart : ¬HasOutgoing F p.start)
    {s : V} (hs : s ∉ p.support)
    (hbalance : ∀ x, edgeBalance F x - edgeBalance R x =
      propInt (x = s) - propInt (x = p.start))
    (hfirst : p.support ∩ (Gamma.vertexSet Y \ removedInterior R) ⊆
      {p.start, p.finish}) : Disjoint p.edgeSet F := by
  apply Set.disjoint_left.2
  intro e hep heF
  have hwalk : ∃ x ∈ p.support, HasOutgoing p.edgeSet x ∧
      HasOutgoing F x ∧ ¬HasIncoming F x := by
    have hscan : ∀ {a b : V} (q : Walk Gamma.graph a b),
        q.edgeSet ⊆ familyEdges W → ¬HasOutgoing F a →
        (q.edgeSet ∩ F).Nonempty →
        ∃ x ∈ q.support, HasOutgoing q.edgeSet x ∧
          HasOutgoing F x ∧ ¬HasIncoming F x := by
      intro a b q hq ha hm
      cases q with
      | nil => simp [Walk.edgeSet] at hm
      | @cons a c b hac q =>
          have hacW : (a, c) ∈ familyEdges W := hq (by simp [Walk.edgeSet])
          have hacF : (a, c) ∉ F := fun h ↦ ha ⟨c, h⟩
          have hc : ¬HasIncoming F c := by
            rintro ⟨z, hz⟩
            have hza : z = a := (IsWarp.familyEdges_biUnique hW).1 (hF hz) hacW
            exact hacF (hza ▸ hz)
          have hqW : q.edgeSet ⊆ familyEdges W := by
            intro d hd
            exact hq (by simp [Walk.edgeSet, hd])
          have hmTail : (q.edgeSet ∩ F).Nonempty := by
            obtain ⟨d, hd, hdF⟩ := hm
            simp only [Walk.edgeSet_cons] at hd
            rcases hd with hd | hd
            · exact (hacF (hd ▸ hdF)).elim
            · exact ⟨d, hd, hdF⟩
          obtain ⟨x, hx, ⟨y, hxy⟩, hxo, hxi⟩ :=
            walk_meets_forward_lower_boundary_of_edge hW hF q hqW hc hmTail
          exact ⟨x, by simp [Walk.support, hx],
            ⟨y, by simp [Walk.edgeSet, hxy]⟩, hxo, hxi⟩
    exact hscan p.walk hp hstart ⟨e, hep, heF⟩
  obtain ⟨x, hxp, ⟨y, hxy⟩, hxo, hxi⟩ := hwalk
  have hxs : x ≠ s := fun h ↦ hs (h ▸ hxp)
  have hxa : x ≠ p.start := fun h ↦ hstart (h ▸ hxo)
  have hxb : x ≠ p.finish := by
    intro heq
    exact FinitePath.no_outgoing_edge_at_finish p y (heq ▸ hxy)
  have hxR := removed_lower_boundary_of_forward_lower_boundary
    (hbalance x) hxs hxa hxo hxi
  obtain ⟨z, hxz⟩ := hxR.1
  have hxContact : x ∈ Gamma.vertexSet Y \ removedInterior R :=
    ⟨(familyEdges_subset_vertexSet_prod Y (hR hxz)).1, fun h ↦ hxR.2 h.1⟩
  have hxEnds := hfirst ⟨hxp, hxContact⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxEnds
  exact hxEnds.elim hxa hxb

#print axioms no_forward_outgoing_at_backward_exit
#print axioms removed_lower_boundary_of_forward_lower_boundary
#print axioms finitePath_meets_forward_lower_boundary_interior
#print axioms firstContact_has_no_old_forward_incoming
#print axioms no_forward_outgoing_at_backward_exit_of_reference
#print axioms firstReferenceContact_has_no_old_forward_incoming_of_balance
#print axioms terminal_outside_reference_of_no_new_contact
#print axioms firstReferenceContact_forward_edges_fresh

end Erdos599.Alternating.SwitchingCore.RelationalInterval
