import ErdosProblems.Erdos73.SubdivisionHalfPaths
import ErdosProblems.Erdos73.TreeIncidenceIndependence

/-! Each incidence-graph edge has a unique original corridor and endpoint side. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph GraphSubdivisionModel

variable {W : Type*} [Fintype W] [LinearOrder W] {H : SimpleGraph W}
variable [LinearOrder (W ⊕ OrientedEdge H)]

theorem exists_incidence_edge_code (d : OrientedEdge (treeIncidenceGraph H)) :
    ∃ e : OrientedEdge H, ∃ side : Bool,
      s(d.lo, d.hi) = s(Sum.inl (halfEndpoint e side), Sum.inr e) := by
  rcases d with ⟨⟨x, y⟩, hlt, hadj⟩
  cases x with
  | inl w =>
    cases y with
    | inl z => exact hadj.elim
    | inr e =>
      change w = e.lo ∨ w = e.hi at hadj
      rcases hadj with rfl | rfl
      · refine ⟨e, false, ?_⟩
        simp only [OrientedEdge.lo, OrientedEdge.hi, halfEndpoint, Bool.false_eq_true, if_false]
      · refine ⟨e, true, ?_⟩
        simp only [OrientedEdge.lo, OrientedEdge.hi, halfEndpoint, if_pos rfl, ite_true]
  | inr e =>
    cases y with
    | inr f => exact hadj.elim
    | inl w =>
      change w = e.lo ∨ w = e.hi at hadj
      rcases hadj with rfl | rfl
      · refine ⟨e, false, ?_⟩
        simp only [OrientedEdge.lo, OrientedEdge.hi, halfEndpoint, Bool.false_eq_true, if_false]
        exact Sym2.eq_swap
      · refine ⟨e, true, ?_⟩
        simp only [OrientedEdge.lo, OrientedEdge.hi, halfEndpoint, if_pos rfl, ite_true]
        exact Sym2.eq_swap

structure IncidenceEdgeWitness (d : OrientedEdge (treeIncidenceGraph H)) where
  original : OrientedEdge H
  side : Bool
  edge_eq : s(d.lo, d.hi) = s(Sum.inl (halfEndpoint original side), Sum.inr original)

def incidenceEdgeWitness (d : OrientedEdge (treeIncidenceGraph H)) : IncidenceEdgeWitness d :=
  ⟨(exists_incidence_edge_code d).choose, (exists_incidence_edge_code d).choose_spec.choose,
    (exists_incidence_edge_code d).choose_spec.choose_spec⟩

namespace IncidenceEdgeWitness

variable {d f : OrientedEdge (treeIncidenceGraph H)}

theorem endpoints (D : IncidenceEdgeWitness d) :
    (d.lo = Sum.inl (halfEndpoint D.original D.side) ∧ d.hi = Sum.inr D.original) ∨
      (d.lo = Sum.inr D.original ∧ d.hi = Sum.inl (halfEndpoint D.original D.side)) :=
  Sym2.eq_iff.mp D.edge_eq

theorem branch_incident (D : IncidenceEdgeWitness d) :
    Sum.inl (halfEndpoint D.original D.side) = d.lo ∨
      Sum.inl (halfEndpoint D.original D.side) = d.hi :=
  D.endpoints.elim (fun hh => Or.inl hh.1.symm) (fun hh => Or.inr hh.2.symm)

theorem midpoint_incident (D : IncidenceEdgeWitness d) :
    Sum.inr D.original = d.lo ∨ Sum.inr D.original = d.hi :=
  D.endpoints.elim (fun hh => Or.inr hh.2.symm) (fun hh => Or.inl hh.1.symm)

theorem edge_eq_of_code (D : IncidenceEdgeWitness d) (F : IncidenceEdgeWitness f)
    (he : D.original = F.original) (hs : D.side = F.side) : d = f := by
  apply OrientedEdge.eq_of_sym2_eq
  rw [D.edge_eq, F.edge_eq, he, hs]

end IncidenceEdgeWitness
end
end Erdos73
