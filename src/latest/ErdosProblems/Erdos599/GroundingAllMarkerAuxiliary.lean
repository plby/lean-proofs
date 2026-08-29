/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerPorts
import ErdosProblems.Erdos599.Normalization

/-!
# The contracted auxiliary targeting all marker initials

Each reference edge, or identity strictly outside the reference warp, is
represented by one vertex. Finite record terminals retain their unmatched
sending port; marker initials retain their unmatched receiving port. Rays
have fresh sources with precisely the original-edge departure rule. Other
unmatched ports are omitted and loops are discarded.

Every auxiliary walk decodes to the uncontracted residual graph. The final
edge gadget is entered at its receiving port; its backward matching step
is performed only when continuing the walk. Ray sources are handled by
their first original edge, not by an invented terminal for the ray.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u v

variable {V : Type u} {I : Type v} {G : DWeb V}

/-- Concrete reference and record data. Marker initials need not belong
to essential reference components. -/
structure Input (G : DWeb V) (I : Type v) where
  reference : G.Warp
  record : I → G.DPath
  record_mem : ∀ i, record i ∈ reference.paths
  record_injective : Function.Injective record
  markers : Set V
  markers_initial : markers ⊆ G.initialSet reference.paths

namespace Input

variable (L : Input G I)

/-- The four disjoint sorts of retained contracted vertices. -/
inductive Vertex
  | source : I → Vertex
  | marker : L.markers → Vertex
  | edge : {e : V × V // e ∈ familyEdges L.reference.paths} → Vertex
  | off : {x : V // x ∉ G.vertexSet L.reference.paths} → Vertex

/-- A ray source has no sending port; its departures are defined separately. -/
def sending : L.Vertex → Option V
  | .source i => (L.record i).terminal?
  | .marker _ => none
  | .edge e => some e.1.1
  | .off x => some x.1

/-- Sources have no receiving port. A reference-edge gadget is entered at
the head, before any backward traversal of that reference edge. -/
def receiving : L.Vertex → Option V
  | .source _ => none
  | .marker y => some y.1
  | .edge e => some e.1.2
  | .off x => some x.1

/-- Each contracted matching vertex has its actual backward internal step. -/
theorem internal_step {a : L.Vertex} {x y : V}
    (hx : L.sending a = some x) (hy : L.receiving a = some y) :
    Step L.reference.paths (.inr y) (.inl x) := by
  cases a with
  | source i => simp [receiving] at hy
  | marker z => simp [sending] at hx
  | edge e =>
      have hxe : e.1.1 = x := Option.some.inj hx
      have hye : e.1.2 = y := Option.some.inj hy
      exact Or.inl (hxe ▸ hye ▸ e.2)
  | off z =>
      have hzx : z.1 = x := Option.some.inj hx
      have hzy : z.1 = y := Option.some.inj hy
      exact Or.inr ⟨hzx.symm.trans hzy, hzx ▸ z.2⟩

/-- An ordinary nonmatching port edge, or an original departure from a
ray proxy. Loop deletion is explicit. -/
def Adj (a b : L.Vertex) : Prop :=
  a ≠ b ∧ ∃ y, L.receiving b = some y ∧
    ((∃ x, L.sending a = some x ∧ Step L.reference.paths (.inl x) (.inr y)) ∨
      ∃ (i : I) (r : Ray G.graph), a = .source i ∧ L.record i = .inr r ∧
        ∃ x ∈ r.support, G.graph.Adj x y)

def web : DWeb L.Vertex where
  graph := ⟨L.Adj⟩
  source := Set.range Vertex.source
  target := Set.range Vertex.marker

/-- Auxiliary sources are exactly the record indices, without additional
vertices or copies arising from endpoints shared with other sorts. -/
noncomputable def sourceEquiv : I ≃ L.web.source :=
  Equiv.ofInjective Vertex.source (fun _ _ h ↦ Vertex.source.inj h)

noncomputable def targetEquiv : L.markers ≃ L.web.target :=
  Equiv.ofInjective Vertex.marker (fun _ _ h ↦ Vertex.marker.inj h)

@[simp]
theorem sourceEquiv_val (i : I) : (L.sourceEquiv i).1 = .source i := rfl

@[simp]
theorem targetEquiv_val (y : L.markers) : (L.targetEquiv y).1 = .marker y := rfl

theorem sourceEquiv_symm_val (x : L.web.source) :
    Vertex.source (L.sourceEquiv.symm x) = x.1 :=
  congrArg Subtype.val (L.sourceEquiv.apply_symm_apply x)

theorem targetEquiv_symm_val (x : L.web.target) :
    Vertex.marker (L.targetEquiv.symm x) = x.1 :=
  congrArg Subtype.val (L.targetEquiv.apply_symm_apply x)

theorem not_adj_self (a : L.Vertex) : ¬ L.web.graph.Adj a a :=
  fun h ↦ h.1 rfl

theorem not_adj_to_source (a : L.Vertex) (i : I) :
    ¬ L.web.graph.Adj a (.source i) := by
  rintro ⟨_, y, hy, _⟩
  simp [receiving] at hy

theorem not_adj_from_marker (y : L.markers) (a : L.Vertex) :
    ¬ L.web.graph.Adj (.marker y) a := by
  rintro ⟨_, z, _, ⟨x, hx, _⟩ | ⟨i, r, hi, _⟩⟩
  · simp [sending] at hx
  · cases hi

theorem web_isNormalized : L.web.IsNormalized := by
  intro a b hab
  constructor
  · rintro ⟨i, rfl⟩
    exact L.not_adj_to_source a i hab
  · rintro ⟨y, rfl⟩
    exact L.not_adj_from_marker y b hab

/-- A continuation from a receiving port includes each internal matching
step before its next nonmatching departure, but not after its last arrival. -/
theorem walk_decode_from_receiving {a b : L.Vertex}
    (p : Walk L.web.graph a b) {x y : V}
    (hx : L.receiving a = some x) (hy : L.receiving b = some y) :
    Relation.ReflTransGen (Step L.reference.paths) (.inr x) (.inr y) := by
  induction p generalizing x with
  | nil =>
      have hxy : x = y := Option.some.inj (hx.symm.trans hy)
      subst y
      exact .refl
  | @cons a c b e p ih =>
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨w, hw, hstep⟩ := hforward
        exact (Relation.ReflTransGen.single (L.internal_step hw hx)).trans
          ((Relation.ReflTransGen.single hstep).trans (ih hz hy))
      · obtain ⟨i, r, rfl, _, _⟩ := hproxy
        simp [receiving] at hx

/-- Nonempty auxiliary walks from a sending port decode without an
initial backward step. -/
theorem walk_decode_from_sending {a b : L.Vertex}
    (p : Walk L.web.graph a b) (hne : a ≠ b) {x y : V}
    (hx : L.sending a = some x) (hy : L.receiving b = some y) :
    Relation.ReflTransGen (Step L.reference.paths) (.inl x) (.inr y) := by
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ c _ e p =>
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨w, hw, hstep⟩ := hforward
        have hwx : w = x := Option.some.inj (hw.symm.trans hx)
        exact (Relation.ReflTransGen.single (hwx ▸ hstep)).trans
          (L.walk_decode_from_receiving p hz hy)
      · obtain ⟨i, r, rfl, hr, _⟩ := hproxy
        simp [sending, hr] at hx

theorem walk_decode_finite_record {i : I} (f : FinitePath G.graph)
    (hi : L.record i = .inl f) (y : L.markers)
    (p : Walk L.web.graph (.source i) (.marker y)) :
    Relation.ReflTransGen (Step L.reference.paths) (.inl f.finish) (.inr y.1) := by
  apply L.walk_decode_from_sending p (by intro h; cases h) ?_ rfl
  simp only [sending, hi, Path.terminal?]

/-- A ray-source walk starts with one actual original edge from its ray;
the remaining walk begins at the receiving port of that edge's head. -/
theorem walk_decode_ray_record {i : I} (r : Ray G.graph)
    (hi : L.record i = .inr r) (y : L.markers)
    (p : Walk L.web.graph (.source i) (.marker y)) :
    ∃ x ∈ r.support, ∃ z, G.graph.Adj x z ∧
      Relation.ReflTransGen (Step L.reference.paths) (.inr z) (.inr y.1) := by
  cases p with
  | @cons _ c _ e p =>
      obtain ⟨_, z, hz, hforward | hproxy⟩ := e
      · obtain ⟨x, hx, _⟩ := hforward
        simp [sending, hi] at hx
      · obtain ⟨j, s, hij, hjs, x, hx, hxz⟩ := hproxy
        have hij' : i = j := Vertex.source.inj hij
        subst j
        have hsr : s = r := Sum.inr.inj (hjs.symm.trans hi)
        subst s
        exact ⟨x, hx, z, hxz, L.walk_decode_from_receiving p hz rfl⟩

#print axioms web_isNormalized
#print axioms walk_decode_finite_record
#print axioms walk_decode_ray_record

end Input
end Erdos599.GroundingAllMarkerAuxiliary
