import ErdosProblems.Erdos633b.EdgeDirectionSectors
import ErdosProblems.Erdos633b.InteriorVertexIncidence

/-! Actual incident sectors cover the whole circle at an interior point.
Their interiors are disjoint; their closed boundaries are finite. -/

namespace Erdos633b.Tiling

open MeasureTheory

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def IncidentPiece {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :=
  {a : Fin n // p ∈ (d.tile.move (d.place a)).support}

instance incidentPieceFinite {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Finite (d.IncidentPiece p) := by
  unfold IncidentPiece
  infer_instance

noncomputable instance incidentPieceFintype {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Fintype (d.IncidentPiece p) := Fintype.ofFinite _

theorem incident_sector_regular {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    (b : d.IncidentPiece p) :
    IsCompact (closedDirections o u p (d.tile.move (d.place b.val))) ∧
    (closedDirections o u p (d.tile.move (d.place b.val)) \
      interiorDirections o u p (d.tile.move (d.place b.val))).Finite := by
  rcases d.vertex_incident_piece_cases a j ha b.val b.property with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h := (d.tile.move (d.place b.val)).vertex_sector_properties o hu k
    rw [hk] at h
    exact ⟨h.1, h.2.1⟩
  · have h := (d.tile.move (d.place b.val)).openEdge_sector_properties o hu k hk
    exact ⟨h.1, h.2.1⟩

theorem incident_interior_directions_disjoint {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    {b c : d.IncidentPiece p} (hbc : b ≠ c) :
    Disjoint (interiorDirections o u p (d.tile.move (d.place b.val)))
      (interiorDirections o u p (d.tile.move (d.place c.val))) := by
  apply Set.disjoint_left.mpr
  rintro t ⟨q, hq, hqt⟩ ⟨r, hr, hrt⟩
  have hqp : q ≠ p := by
    rintro rfl
    exact d.vertex_not_mem_piece_interior a j ha b.val hq
  have hrp : r ≠ p := by
    rintro rfl
    exact d.vertex_not_mem_piece_interior a j ha c.val hr
  have hsame := direction_sameRay o hu hqp hrp (hqt.trans hrt.symm)
  obtain ⟨x, hxB, hxC⟩ := (d.tile.move (d.place b.val)).interiors_inter_of_sameRay
    (d.tile.move (d.place c.val)) b.property c.property hq hr hqp hrp hsame
  rw [Triangle.support_move] at hxB hxC
  exact Set.disjoint_left.mp (d.disjoint_interiors (fun he => hbc (Subtype.ext he))) hxB hxC

theorem incident_closed_directions_aedisjoint {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    {b c : d.IncidentPiece p} (hbc : b ≠ c) :
    AEDisjoint CircleArcMeasure.measure (closedDirections o u p (d.tile.move (d.place b.val)))
      (closedDirections o u p (d.tile.move (d.place c.val))) := by
  have hb := (d.incident_sector_regular o hu a j ha b).2
  have hc := (d.incident_sector_regular o hu a j ha c).2
  have hd := d.incident_interior_directions_disjoint o hu a j ha hbc
  have hfinite : (closedDirections o u p (d.tile.move (d.place b.val)) ∩
      closedDirections o u p (d.tile.move (d.place c.val))).Finite := by
    apply (hb.union hc).subset
    intro t ht
    by_cases hbint : t ∈ interiorDirections o u p (d.tile.move (d.place b.val))
    · exact Or.inr ⟨ht.2, fun hcint => Set.disjoint_left.mp hd hbint hcint⟩
    · exact Or.inl ⟨ht.1, hbint⟩
  exact hfinite.measure_zero CircleArcMeasure.measure

theorem incident_closed_directions_cover {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (hp : p ∈ interior T.support) :
    (⋃ b : d.IncidentPiece p, closedDirections o u p (d.tile.move (d.place b.val))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨q, hqp, hqt⟩ := exists_point_direction o hu p t
  obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius p
  obtain ⟨r, hr, _, hx⟩ := exists_small_radial p q (isOpen_interior.inter Metric.isOpen_ball)
    (show p ∈ interior T.support ∩ Metric.ball p ε from ⟨hp, Metric.mem_ball_self hε⟩)
  let x := AffineMap.homothety p r q
  have hxT : x ∈ T.support := interior_subset hx.1
  rw [← d.covers, Set.mem_iUnion] at hxT
  obtain ⟨b, hb⟩ := hxT
  have hpB : p ∈ (d.tile.move (d.place b)).support := by
    rw [Triangle.support_move]
    exact hlocal b x hx.2 hb
  refine Set.mem_iUnion.mpr ⟨⟨b, hpB⟩, x, ⟨?_, ?_⟩, ?_⟩
  · rwa [Triangle.support_move]
  · intro he
    change x = p at he
    have hz : r • (q - p) = 0 := by
      simpa only [x, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
        add_eq_right] using he
    exact hqp (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hr.ne'))
  · exact (direction_homothety o u p q hr).trans hqt

theorem sum_incident_sector_measures {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (hp : p ∈ interior T.support) (a : Fin n) (j : Fin 3)
    (ha : d.place a (d.tile.points j) = p) :
    (∑ b : d.IncidentPiece p,
      CircleArcMeasure.measure (closedDirections o u p (d.tile.move (d.place b.val)))) =
        ENNReal.ofReal (2 * Real.pi) := by
  have hd : Pairwise (fun b c : d.IncidentPiece p =>
      AEDisjoint CircleArcMeasure.measure (closedDirections o u p (d.tile.move (d.place b.val)))
        (closedDirections o u p (d.tile.move (d.place c.val)))) :=
    fun _ _ hbc => d.incident_closed_directions_aedisjoint o hu a j ha hbc
  have hm := measure_iUnion₀ hd (fun b =>
    (d.incident_sector_regular o hu a j ha b).1.isClosed.measurableSet.nullMeasurableSet)
  rw [d.incident_closed_directions_cover o hu hp, CircleArcMeasure.measure_univ, tsum_fintype] at hm
  exact hm.symm

end Erdos633b.Tiling
