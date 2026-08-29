/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerStoppedMatchingRoutes

/-!
# Decoding auxiliary paths in a retained submatching

The decoding graph records port provenance in its adjacency. Its last
vertex is entered at the receiving port only. Internal backward pairs
are supplied by the retained matching, and ordinary forward steps remain
nonmatching because this matching is contained in the original one.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def matchingStep (M : V → V → Prop) : Port V → Port V → Prop
  | .inl x, .inr y => (G.graph.Adj x y ∨ x = y) ∧ ¬ M x y
  | .inr y, .inl x => M x y
  | _, _ => False

def routePortSet (T : Set L.Vertex) (last : L.Vertex) (departure : V) : Set (Port V)
  | .inl x => x = departure ∨ ∃ a ∈ T, a ≠ last ∧ L.sending a = some x
  | .inr y => ∃ a ∈ T, L.receiving a = some y

def matchingRouteGraph (T : Set L.Vertex) (last : L.Vertex) (departure : V)
    (M : V → V → Prop) : Digraph (Port V) where
  Adj p q := matchingStep (G := G) M p q ∧
    p ∈ L.routePortSet T last departure ∧ q ∈ L.routePortSet T last departure

theorem walk_decode_matching_from_receiving (T : Set L.Vertex) (departure : V)
    (M : V → V → Prop)
    (hM : ∀ {x y}, M x y → referenceMatching L.reference.paths x y)
    {a b : L.Vertex} (p : Walk L.web.graph a b) (hp : p.IsPath)
    (hT : ∀ z ∈ p.support, z ∈ T)
    (hInternal : ∀ a ∈ T, a ≠ b → ∀ x y,
      L.sending a = some x → L.receiving a = some y → M x y)
    {x y : V} (hx : L.receiving a = some x) (hy : L.receiving b = some y) :
    Nonempty (Walk (L.matchingRouteGraph T b departure M) (.inr x) (.inr y)) := by
  induction p generalizing x with
  | nil =>
      have hxy : x = y := Option.some.inj (hx.symm.trans hy)
      subst y
      exact ⟨.nil⟩
  | @cons a c b e p ih =>
      have hpath := List.nodup_cons.mp hp
      have haT : a ∈ T := hT a (List.mem_cons_self ..)
      have hcT : c ∈ T := hT c (List.mem_cons_of_mem a p.start_mem_support)
      have hab : a ≠ b := fun h ↦ hpath.1 (h.symm ▸ p.end_mem_support)
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨w, hw, hstep⟩ := hforward
        obtain ⟨tail⟩ := ih hpath.2
          (fun z hz ↦ hT z (List.mem_cons_of_mem a hz)) hInternal hz hy
        have hback : (L.matchingRouteGraph T b departure M).Adj (.inr x) (.inl w) :=
          ⟨hInternal a haT hab w x hw hx, ⟨a, haT, hx⟩, Or.inr ⟨a, haT, hab, hw⟩⟩
        have hnext : (L.matchingRouteGraph T b departure M).Adj (.inl w) (.inr z) :=
          ⟨⟨hstep.1, fun h ↦ hstep.2 (hM h)⟩,
            Or.inr ⟨a, haT, hab, hw⟩, ⟨c, hcT, hz⟩⟩
        exact ⟨.cons hback (.cons hnext tail)⟩
      · obtain ⟨i, ray, rfl, _, _⟩ := hproxy
        simp [receiving] at hx

/-- A finite record's initial sending port needs no initial backward step. -/
theorem walk_decode_matching_from_sending (T : Set L.Vertex) (M : V → V → Prop)
    (hM : ∀ {x y}, M x y → referenceMatching L.reference.paths x y)
    {a b : L.Vertex} (p : Walk L.web.graph a b) (hp : p.IsPath)
    (hT : ∀ z ∈ p.support, z ∈ T)
    (hInternal : ∀ a ∈ T, a ≠ b → ∀ x y,
      L.sending a = some x → L.receiving a = some y → M x y)
    (hne : a ≠ b) {x y : V}
    (hx : L.sending a = some x) (hy : L.receiving b = some y) :
    Nonempty (Walk (L.matchingRouteGraph T b x M) (.inl x) (.inr y)) := by
  cases p with
  | nil => exact (hne rfl).elim
  | @cons a c b e p =>
      have hcT : c ∈ T := hT c (List.mem_cons_of_mem a p.start_mem_support)
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨w, hw, hstep⟩ := hforward
        have hwx : w = x := Option.some.inj (hw.symm.trans hx)
        subst w
        obtain ⟨tail⟩ := L.walk_decode_matching_from_receiving T x M hM p
          (List.nodup_cons.mp hp).2
          (fun z hz ↦ hT z (List.mem_cons_of_mem a hz)) hInternal hz hy
        have hnext : (L.matchingRouteGraph T b x M).Adj (.inl x) (.inr z) :=
          ⟨⟨hstep.1, fun h ↦ hstep.2 (hM h)⟩, Or.inl rfl, ⟨c, hcT, hz⟩⟩
        exact ⟨.cons hnext tail⟩
      · obtain ⟨i, ray, rfl, hi, _⟩ := hproxy
        simp [sending, hi] at hx

/-- A ray's first original departure is nonmatching once its sending
port is freed; the rest uses the same retained-pair decoder. -/
theorem walk_decode_matching_from_ray (T : Set L.Vertex)
    (M : V → V → V → Prop)
    (hM : ∀ d {x y}, M d x y → referenceMatching L.reference.paths x y)
    (i : I) (ray : Ray G.graph) (hi : L.record i = .inr ray)
    {a b : L.Vertex} (p : Walk L.web.graph a b) (hp : p.IsPath)
    (hT : ∀ z ∈ p.support, z ∈ T) (ha : a = .source i)
    (hInternal : ∀ d, ∀ a ∈ T, a ≠ b → ∀ x y,
      L.sending a = some x → L.receiving a = some y → M d x y)
    (hFree : ∀ x ∈ ray.support, ∀ y, ¬ M x x y)
    {y : V} (hy : L.receiving b = some y) :
    ∃ x ∈ ray.support,
      Nonempty (Walk (L.matchingRouteGraph T b x (M x)) (.inl x) (.inr y)) := by
  cases p with
  | nil => simp [ha, receiving] at hy
  | @cons a c b e p =>
      have hcT : c ∈ T := hT c (List.mem_cons_of_mem a p.start_mem_support)
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨x, hx, _⟩ := hforward
        simp [ha, sending, hi] at hx
      · obtain ⟨j, s, haj, hjs, x, hx, hxz⟩ := hproxy
        have hij : i = j := Vertex.source.inj (ha.symm.trans haj)
        subst j
        have hsr : s = ray := Sum.inr.inj (hjs.symm.trans hi)
        subst s
        obtain ⟨tail⟩ := L.walk_decode_matching_from_receiving T x (M x) (hM x) p
          (List.nodup_cons.mp hp).2
          (fun z hz ↦ hT z (List.mem_cons_of_mem a hz)) (hInternal x) hz hy
        have hnext : (L.matchingRouteGraph T b x (M x)).Adj (.inl x) (.inr z) :=
          ⟨⟨Or.inl hxz, hFree x hx z⟩, Or.inl rfl, ⟨c, hcT, hz⟩⟩
        exact ⟨x, hx, ⟨.cons hnext tail⟩⟩

#print axioms walk_decode_matching_from_receiving
#print axioms walk_decode_matching_from_sending
#print axioms walk_decode_matching_from_ray

end Erdos599.GroundingAllMarkerAuxiliary.Input
