/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawForwardProvenance

/-!
# Raw auxiliary ports and companion-preserving local switching

The six arc classes determine the unique incoming port at every original
vertex and the unique non-proxy outgoing port. Simplicity of the auxiliary
path therefore gives degree bounds for its actual forward relation.
Every conflicting reference incidence is already a raw backward gadget;
no additional conflict cut is needed for a proxy-free route.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

/-- The ordinary or reversed-edge port used by a non-loop forward arrival. -/
def RawHeadPort (b : L.LV) (y : V) : Prop :=
  (b = .old y ∧ ¬ HasIncoming L.familyEdges y) ∨
    ∃ w, b = .edge w y ∧ (w, y) ∈ L.familyEdges

/-- The ordinary or reversed-edge port used by a non-proxy forward departure. -/
def RawTailPort (a : L.LV) (x : V) : Prop :=
  (a = .old x ∧ ¬ HasOutgoing L.familyEdges x) ∨
    ∃ w, a = .edge x w ∧ (x, w) ∈ L.familyEdges

/-- Self-loops contribute no boundary change and are not inserted into a
path family. All other deterministically decoded forward edges are kept. -/
def properSelectedConnectorEdges (p : FinitePath L.lambda.graph) : Set (V × V) :=
  {e | e ∈ L.selectedConnectorEdges p ∧ e.1 ≠ e.2}

/-- The full local raw switch, retaining all reference edges except the
actually visited backward gadgets. -/
def rawSwitchedEdges (p : FinitePath L.lambda.graph) : Set (V × V) :=
  (L.familyEdges \ L.representedEdges p) ∪ L.properSelectedConnectorEdges p

variable {L}

theorem RawHeadPort.unique {a b : L.LV} {x : V}
    (ha : L.RawHeadPort a x) (hb : L.RawHeadPort b x) : a = b := by
  rcases ha with ⟨rfl, hno⟩ | ⟨y, rfl, hy⟩
  · rcases hb with ⟨rfl, _⟩ | ⟨z, rfl, hz⟩
    · rfl
    · exact False.elim (hno ⟨z, hz⟩)
  · rcases hb with ⟨rfl, hno⟩ | ⟨z, rfl, hz⟩
    · exact False.elim (hno ⟨y, hy⟩)
    · exact congrArg (fun w ↦ LambdaVertex.edge w x)
        (L.raw_familyEdges_biUnique.1 hy hz)

theorem RawTailPort.unique {a b : L.LV} {x : V}
    (ha : L.RawTailPort a x) (hb : L.RawTailPort b x) : a = b := by
  rcases ha with ⟨rfl, hno⟩ | ⟨y, rfl, hy⟩
  · rcases hb with ⟨rfl, _⟩ | ⟨z, rfl, hz⟩
    · rfl
    · exact False.elim (hno ⟨z, hz⟩)
  · rcases hb with ⟨rfl, hno⟩ | ⟨z, rfl, hz⟩
    · exact False.elim (hno ⟨y, hy⟩)
    · exact congrArg (fun w ↦ LambdaVertex.edge x w)
        (L.raw_familyEdges_biUnique.2 hy hz)

/-- Every non-loop forward connector has the unique ordinary/reference
head port. There is no proxy exception at an arrival. -/
theorem HasBoundaryIncidence.forward_head_port
    (hL : L.HasBoundaryIncidence) {a b : L.LV} {x y : V}
    (hab : L.lambda.graph.Adj a b) (hc : L.ForwardConnector a b x y)
    (hne : x ≠ y) : L.RawHeadPort b y := by
  change L.LambdaAdj a b at hab
  rcases hab with hVV | hEV | hVE | hEE | hIV | hIE
  · obtain ⟨q, r, rfl, rfl, _hq, hr, _hqr⟩ := hVV
    have hry : r = y := by simpa using hc.2.1
    subst y
    exact Or.inl ⟨rfl, hL.noIncoming_oldForward hr⟩
  · obtain ⟨q, r, z, rfl, rfl, _hqr, hz⟩ := hEV
    have hqx : q = x := by simpa using hc.1
    have hzy : z = y := by simpa using hc.2.1
    subst x
    subst y
    rcases hz with hz | ⟨hz, _hqz⟩
    · exact False.elim (hne hz)
    · exact Or.inl ⟨rfl, hL.noIncoming_oldForward hz⟩
  · obtain ⟨q, r, z, rfl, rfl, hrz, _hq⟩ := hVE
    have hzy : z = y := by simpa using hc.2.1
    subst y
    exact Or.inr ⟨r, rfl, hrz⟩
  · obtain ⟨q, r, w, z, rfl, rfl, _hqr, hwz, _hqz⟩ := hEE
    have hzy : z = y := by simpa using hc.2.1
    subst y
    exact Or.inr ⟨w, rfl, hwz⟩
  · obtain ⟨i, z, rfl, rfl, hz, _hattach⟩ := hIV
    have hzy : z = y := by simpa using hc.2.1
    subst y
    exact Or.inl ⟨rfl, hL.noIncoming_oldForward hz⟩
  · obtain ⟨i, w, z, rfl, rfl, hwz, _hattach⟩ := hIE
    have hzy : z = y := by simpa using hc.2.1
    subst y
    exact Or.inr ⟨w, rfl, hwz⟩

/-- A non-loop forward connector uses the unique departure port, except
possibly when it is attached directly to a starting proxy. -/
theorem HasBoundaryIncidence.forward_tail_port_or_proxy
    (hL : L.HasBoundaryIncidence) {a b : L.LV} {x y : V}
    (hab : L.lambda.graph.Adj a b) (hc : L.ForwardConnector a b x y)
    (hne : x ≠ y) :
    L.RawTailPort a x ∨ ∃ i : I, a = .proxy i ∧ x ∈ (L.proxyPath i).support := by
  change L.LambdaAdj a b at hab
  rcases hab with hVV | hEV | hVE | hEE | hIV | hIE
  · obtain ⟨q, r, rfl, rfl, hq, _hr, _hqr⟩ := hVV
    have hqx : q = x := by simpa using hc.1
    subst x
    exact Or.inl (Or.inl ⟨rfl, hL.noOutgoing_oldForward hq⟩)
  · obtain ⟨q, r, z, rfl, rfl, hqr, _hz⟩ := hEV
    have hqx : q = x := by simpa using hc.1
    subst x
    exact Or.inl (Or.inr ⟨r, rfl, hqr⟩)
  · obtain ⟨q, r, z, rfl, rfl, _hrz, hq⟩ := hVE
    have hqx : q = x := by simpa using hc.1
    have hzy : z = y := by simpa using hc.2.1
    subst x
    subst y
    rcases hq with hq | ⟨hq, _hqz⟩
    · exact False.elim (hne hq)
    · exact Or.inl (Or.inl ⟨rfl, hL.noOutgoing_oldForward hq⟩)
  · obtain ⟨q, r, w, z, rfl, rfl, hqr, _hwz, _hqz⟩ := hEE
    have hqx : q = x := by simpa using hc.1
    subst x
    exact Or.inl (Or.inr ⟨r, rfl, hqr⟩)
  · obtain ⟨i, z, rfl, rfl, _hz, _hattach⟩ := hIV
    have hxi : x ∈ (L.proxyPath i).support := by simpa using hc.1
    exact Or.inr ⟨i, rfl, hxi⟩
  · obtain ⟨i, w, z, rfl, rfl, _hwz, _hattach⟩ := hIE
    have hxi : x ∈ (L.proxyPath i).support := by simpa using hc.1
    exact Or.inr ⟨i, rfl, hxi⟩

/-- A reference edge at the head port is represented by that exact gadget. -/
theorem RawHeadPort.eq_edge_of_reference {b : L.LV} {x y : V}
    (hb : L.RawHeadPort b y) (hxy : (x, y) ∈ L.familyEdges) :
    b = .edge x y := by
  rcases hb with ⟨_hb, hno⟩ | ⟨w, rfl, hwy⟩
  · exact False.elim (hno ⟨x, hxy⟩)
  · rw [L.raw_familyEdges_biUnique.1 hwy hxy]

/-- A reference edge at the tail port is represented by that exact gadget. -/
theorem RawTailPort.eq_edge_of_reference {a : L.LV} {x y : V}
    (ha : L.RawTailPort a x) (hxy : (x, y) ∈ L.familyEdges) :
    a = .edge x y := by
  rcases ha with ⟨_ha, hno⟩ | ⟨w, rfl, hxw⟩
  · exact False.elim (hno ⟨y, hxy⟩)
  · rw [L.raw_familyEdges_biUnique.2 hxw hxy]

/-- The actual raw forward relation always has indegree at most one. -/
theorem HasBoundaryIncidence.properSelectedConnectorEdges_leftUnique
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph) :
    Relator.LeftUnique (fun x y ↦ (x, y) ∈ L.properSelectedConnectorEdges p) := by
  intro x z y hxy hzy
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := hxy
  obtain ⟨⟨c, d, hcd, hchoice'⟩, hne'⟩ := hzy
  have hbd : b = d :=
    (hL.forward_head_port (x := x) (p.edgeSet_subset_adj hab)
      (L.chosenConnector?_eq_some hchoice) hne).unique
      (hL.forward_head_port (x := z) (p.edgeSet_subset_adj hcd)
        (L.chosenConnector?_eq_some hchoice') hne')
  subst d
  have hac : a = c := (Alternating.FinitePath.edgeSet_biUnique p).1 hab hcd
  subst c
  exact congrArg Prod.fst (Option.some.inj (hchoice.symm.trans hchoice'))

/-- With no proxy on the auxiliary route, departures are biunique too. -/
theorem HasBoundaryIncidence.properSelectedConnectorEdges_rightUnique_of_no_proxy
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hproxy : ∀ i : I, LambdaVertex.proxy i ∉ p.support) :
    Relator.RightUnique (fun x y ↦ (x, y) ∈ L.properSelectedConnectorEdges p) := by
  intro x y z hxy hxz
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := hxy
  obtain ⟨⟨c, d, hcd, hchoice'⟩, hne'⟩ := hxz
  have hport : L.RawTailPort a x := by
    rcases hL.forward_tail_port_or_proxy (p.edgeSet_subset_adj hab)
        (L.chosenConnector?_eq_some hchoice) hne with h | ⟨i, rfl, _⟩
    · exact h
    · exact False.elim (hproxy i (p.edgeSet_subset_support_prod hab).1)
  have hport' : L.RawTailPort c x := by
    rcases hL.forward_tail_port_or_proxy (p.edgeSet_subset_adj hcd)
        (L.chosenConnector?_eq_some hchoice') hne' with h | ⟨i, rfl, _⟩
    · exact h
    · exact False.elim (hproxy i (p.edgeSet_subset_support_prod hcd).1)
  have hac : a = c := hport.unique hport'
  subst c
  have hbd : b = d := (Alternating.FinitePath.edgeSet_biUnique p).2 hab hcd
  subst d
  exact congrArg Prod.snd (Option.some.inj (hchoice.symm.trans hchoice'))

/-- Every reference edge entering an inserted forward head is among the
raw backward gadgets, with no erasure or extra conflict deletion. -/
theorem HasBoundaryIncidence.incoming_reference_represented
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    {x y z : V} (hxy : (x, y) ∈ L.properSelectedConnectorEdges p)
    (hzy : (z, y) ∈ L.familyEdges) : (z, y) ∈ L.representedEdges p := by
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := hxy
  have hb := (hL.forward_head_port (p.edgeSet_subset_adj hab)
    (L.chosenConnector?_eq_some hchoice) hne).eq_edge_of_reference hzy
  refine ⟨?_, hzy⟩
  rw [← hb]
  exact (p.edgeSet_subset_support_prod hab).2

/-- The dual incidence removal holds on proxy-free routes. -/
theorem HasBoundaryIncidence.outgoing_reference_represented_of_no_proxy
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hproxy : ∀ i : I, LambdaVertex.proxy i ∉ p.support)
    {x y z : V} (hxy : (x, y) ∈ L.properSelectedConnectorEdges p)
    (hxz : (x, z) ∈ L.familyEdges) : (x, z) ∈ L.representedEdges p := by
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := hxy
  have hport : L.RawTailPort a x := by
    rcases hL.forward_tail_port_or_proxy (p.edgeSet_subset_adj hab)
        (L.chosenConnector?_eq_some hchoice) hne with h | ⟨i, rfl, _⟩
    · exact h
    · exact False.elim (hproxy i (p.edgeSet_subset_support_prod hab).1)
  have ha := hport.eq_edge_of_reference hxz
  refine ⟨?_, hxz⟩
  rw [← ha]
  exact (p.edgeSet_subset_support_prod hab).1

/-- The complete raw local switch is biunique. Every unused companion edge
is retained: only genuine backward gadgets are removed. -/
theorem HasBoundaryIncidence.rawSwitchedEdges_biUnique_of_no_proxy
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hproxy : ∀ i : I, LambdaVertex.proxy i ∉ p.support) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ L.rawSwitchedEdges p) := by
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact L.raw_familyEdges_biUnique.1 hxy.1 hzy.1
    · exact False.elim (hxy.2 (hL.incoming_reference_represented p hzy hxy.1))
    · exact False.elim (hzy.2 (hL.incoming_reference_represented p hxy hzy.1))
    · exact hL.properSelectedConnectorEdges_leftUnique p hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact L.raw_familyEdges_biUnique.2 hxy.1 hxz.1
    · exact False.elim (hxy.2
        (hL.outgoing_reference_represented_of_no_proxy p hproxy hxz hxy.1))
    · exact False.elim (hxz.2
        (hL.outgoing_reference_represented_of_no_proxy p hproxy hxy hxz.1))
    · exact hL.properSelectedConnectorEdges_rightUnique_of_no_proxy p hproxy hxy hxz

/-- A source-starting route from an ordinary finite source has no proxy. -/
theorem no_proxy_of_start_old (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {x : V} (hx : p.start = .old x) :
    ∀ i : I, LambdaVertex.proxy i ∉ p.support := by
  intro i hi
  have hstart := L.proxy_mem_support_eq_start p hs hi
  rw [hx] at hstart
  cases hstart

/-- Actual finite-source raw switches satisfy the degree condition without
any extra incidence-removal premise. -/
theorem HasBoundaryIncidence.rawSwitchedEdges_biUnique_of_start_old
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {x : V} (hx : p.start = .old x) :
    Relator.BiUnique (fun a b ↦ (a, b) ∈ L.rawSwitchedEdges p) :=
  hL.rawSwitchedEdges_biUnique_of_no_proxy p (no_proxy_of_start_old p hs hx)

end PopularAuxiliary.Input
end Erdos599

#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.properSelectedConnectorEdges_leftUnique
#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.rawSwitchedEdges_biUnique_of_start_old
