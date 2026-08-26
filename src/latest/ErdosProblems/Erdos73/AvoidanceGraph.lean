/- Vertex deletion implemented by isolation, for same-type routing induction. -/
import ErdosProblems.Erdos73.BoundaryPaths

namespace Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

def avoidanceGraph (G : _root_.SimpleGraph V) (D : Finset V) : _root_.SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ D ∧ y ∉ D
  symm := ⟨by rintro x y ⟨hxy, hx, hy⟩; exact ⟨hxy.symm, hy, hx⟩⟩
  loopless := ⟨by rintro x ⟨hxx, _⟩; exact hxx.ne rfl⟩

theorem avoidanceGraph_le (D : Finset V) : avoidanceGraph G D ≤ G := fun _ _ h => h.1

namespace GraphPath

theorem avoidanceGraph_disjoint {D : Finset V} (P : GraphPath (avoidanceGraph G D))
    (hs : P.source ∉ D) : Disjoint P.vertexSet D := by
  have hw {x y : V} (w : (avoidanceGraph G D).Walk x y) (hx : x ∉ D) :
      ∀ z ∈ w.support, z ∉ D := by
    induction w with
    | nil => simpa using hx
    | @cons x v y h w ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact ih h.2.2 z hz
  exact Finset.disjoint_left.mpr fun z hz hzD =>
    hw P.walk hs z (List.mem_toFinset.mp hz) hzD

theorem edges_mem_avoidanceGraph (P : GraphPath G) (D : Finset V)
    (hd : Disjoint P.vertexSet D) :
    ∀ e, e ∈ P.walk.edges → e ∈ (avoidanceGraph G D).edgeSet := by
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
    intro he
    have hxy : s(x, y) ∈ P.edgeSet := List.mem_toFinset.mpr he
    obtain ⟨hx, hy⟩ := P.endpoints_mem_vertexSet_of_edgeSet hxy
    exact ⟨P.walk.edges_subset_edgeSet he,
      fun h => Finset.disjoint_left.mp hd hx h,
      fun h => Finset.disjoint_left.mp hd hy h⟩

theorem IsBoundaryProper.transfer {P : GraphPath G} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) (H : _root_.SimpleGraph V)
    (he : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) : (P.transfer H he).IsBoundaryProper Z := by
  refine ⟨hP.source_mem, hP.target_mem, ?_, ?_⟩
  · intro x hx hxZ
    rw [GraphPath.transfer_vertexSet] at hx
    exact hP.internal_disjoint hx hxZ
  · simpa only [GraphPath.transfer, _root_.SimpleGraph.Walk.length_transfer] using hP.length_ne_one

end GraphPath

namespace PathPacking
variable {A B Z D : Finset V}

def toAvoidanceGraph (P : PathPacking G A B)
    (hd : ∀ r, Disjoint (P.path r).vertexSet D) :
    PathPacking (avoidanceGraph G D) A B :=
  P.transfer (avoidanceGraph G D) (fun r => (P.path r).edges_mem_avoidanceGraph D (hd r))

@[simp] theorem toAvoidanceGraph_card (P : PathPacking G A B)
    (hd : ∀ r, Disjoint (P.path r).vertexSet D) : (P.toAvoidanceGraph hd).card = P.card := rfl

theorem IsBoundaryProper.toAvoidanceGraph {P : PathPacking G A B}
    (hP : P.IsBoundaryProper Z) (hd : ∀ r, Disjoint (P.path r).vertexSet D) :
    (P.toAvoidanceGraph hd).IsBoundaryProper Z :=
  fun r => (hP r).transfer _ _

end PathPacking
end Erdos73Infrastructure.SimpleGraph
