import ErdosProblems.Erdos633b.InteriorSectorPartition
import ErdosProblems.Erdos633b.BoundaryStarAngles

/-! The actual incident tiles partition into vertex incidences and open-edge
incidences. An explicit equivalence permits exact finite angle sums. -/

namespace Erdos633b.Tiling

def EdgePiece {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :=
  {e : Fin n × Fin 3 // p ∈ (d.tile.move (d.place e.1)).openEdge e.2}

instance edgePieceFinite {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Finite (d.EdgePiece p) := by
  unfold EdgePiece
  infer_instance

noncomputable instance edgePieceFintype {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Fintype (d.EdgePiece p) := Fintype.ofFinite _

def vertexPieceIncident {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane)
    (e : d.VertexPiece p) : d.IncidentPiece p :=
  ⟨e.val.1, by
    rw [Triangle.support_move]
    exact ⟨d.tile.points e.val.2, d.tile.vertex_mem_support e.val.2, e.property⟩⟩

def edgePieceIncident {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane)
    (e : d.EdgePiece p) : d.IncidentPiece p :=
  ⟨e.val.1, ((d.tile.move (d.place e.val.1)).openEdge_subset_edge e.val.2 e.property).1⟩

theorem edgePiece_tile_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Function.Injective (fun e : d.EdgePiece p => e.val.1) := by
  intro e f hef
  change e.val.1 = f.val.1 at hef
  apply Subtype.ext
  refine Prod.ext hef ?_
  by_contra hne
  have hp := f.property
  rw [← hef] at hp
  exact Set.disjoint_left.mp ((d.tile.move (d.place e.val.1)).openEdge_disjoint hne) e.property hp

theorem vertexPieceIncident_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Function.Injective (d.vertexPieceIncident p) := by
  intro e f hef
  exact d.vertexPiece_tile_injective p (congrArg Subtype.val hef)

theorem edgePieceIncident_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Function.Injective (d.edgePieceIncident p) := by
  intro e f hef
  exact d.edgePiece_tile_injective p (congrArg Subtype.val hef)

theorem vertexPieceIncident_ne_edgePieceIncident {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : Plane) (e : d.VertexPiece p) (f : d.EdgePiece p) :
    d.vertexPieceIncident p e ≠ d.edgePieceIncident p f := by
  intro he
  have hef : e.val.1 = f.val.1 := congrArg Subtype.val he
  have hv : (d.tile.move (d.place f.val.1)).points e.val.2 = p := by
    change d.place f.val.1 (d.tile.points e.val.2) = p
    rw [← hef]
    exact e.property
  apply (d.tile.move (d.place f.val.1)).vertex_not_mem_openEdge f.val.2 e.val.2
  simpa only [hv] using f.property

def incidenceSumMap {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    d.VertexPiece p ⊕ d.EdgePiece p → d.IncidentPiece p :=
  Sum.elim (d.vertexPieceIncident p) (d.edgePieceIncident p)

theorem incidenceSumMap_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Function.Injective (d.incidenceSumMap p) := by
  intro x y h
  rcases x with e | e <;> rcases y with f | f
  · exact congrArg Sum.inl (d.vertexPieceIncident_injective p h)
  · exact False.elim (d.vertexPieceIncident_ne_edgePieceIncident p e f h)
  · exact False.elim (d.vertexPieceIncident_ne_edgePieceIncident p f e h.symm)
  · exact congrArg Sum.inr (d.edgePieceIncident_injective p h)

theorem incidenceSumMap_surjective {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    Function.Surjective (d.incidenceSumMap p) := by
  intro b
  rcases d.vertex_incident_piece_cases a j ha b.val b.property with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨Sum.inl ⟨(b.val, k), hk⟩, Subtype.ext rfl⟩
  · exact ⟨Sum.inr ⟨(b.val, k), hk⟩, Subtype.ext rfl⟩

noncomputable def incidenceSumEquiv {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    d.VertexPiece p ⊕ d.EdgePiece p ≃ d.IncidentPiece p :=
  Equiv.ofBijective (d.incidenceSumMap p)
    ⟨d.incidenceSumMap_injective p, d.incidenceSumMap_surjective a j ha⟩

end Erdos633b.Tiling
