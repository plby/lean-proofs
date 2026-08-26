import ErdosProblems.Erdos633b.TouchingEdgeOrientation
import ErdosProblems.Erdos633b.IncidentPieceTypes

/-! At a nonvertex point in an internal edge there are exactly two
open-edge incidences. The opposite tile is supplied by actual coverage. -/

namespace Erdos633b.Tiling

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem openEdge_not_mem_piece_interior {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (e : d.EdgePiece p) (b : Fin n) :
    p ∉ interior (d.tile.move (d.place b)).support := by
  intro hp
  by_cases hab : b = e.val.1
  · subst b
    have hpos := ((d.tile.move (d.place e.val.1)).mem_interior_support_iff_all_coords p).mp
      hp e.val.2
    rw [e.property.1] at hpos
    exact lt_irrefl _ hpos
  · obtain ⟨x, hxB, hxA⟩ := (d.tile.move (d.place b)).interiors_inter_of_mem_interior_and_support
      (d.tile.move (d.place e.val.1)) hp
      ((d.tile.move (d.place e.val.1)).openEdge_subset_edge e.val.2 e.property).1
    rw [Triangle.support_move] at hxB hxA
    exact Set.disjoint_left.mp (d.disjoint_interiors hab) hxB hxA

theorem edgePiece_positive_directions {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    {e f : d.EdgePiece p} (hef : e ≠ f) :
    (d.tile.move (d.place e.val.1)).positiveEdgeDirection o u e.val.2 =
      (d.tile.move (d.place f.val.1)).positiveEdgeDirection o u f.val.2 +
        (Real.pi : Real.Angle) := by
  apply Triangle.touching_positiveEdgeDirections _ _ o hu _ f.val.2 e.val.2
    e.property f.property
  simpa only [Triangle.support_move] using
    d.disjoint_interiors (fun h => hef (d.edgePiece_tile_injective p h))

theorem edgePiece_card_le_two {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Fintype.card (d.EdgePiece p) ≤ 2 := by
  by_contra hn
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp (lt_of_not_ge hn)
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  have h1 := d.edgePiece_positive_directions o hu hab
  have h2 := d.edgePiece_positive_directions o hu hac
  have h3 := d.edgePiece_positive_directions o hu hbc
  have he := add_right_cancel (h1.symm.trans h2)
  rw [he] at h3
  have hz : (0 : Real.Angle) = Real.pi :=
    add_left_cancel (by simpa only [add_zero] using h3)
  exact Real.Angle.pi_ne_zero hz.symm

theorem exists_other_edgePiece {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (hp : p ∈ interior T.support) (hv : p ∉ d.vertices)
    (e : d.EdgePiece p) : ∃ f : d.EdgePiece p, f ≠ e := by
  let S := d.tile.move (d.place e.val.1)
  let q := 2 • p - S.points e.val.2
  have hq : S.coord e.val.2 q = -1 := by
    have he : q = AffineMap.lineMap p (S.points e.val.2) (-1 : ℝ) := by
      simp only [q, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [he, S.coord_lineMap, S.coord_vertex, if_pos rfl, e.property.1]
    ring
  obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius p
  obtain ⟨r, hr, _, hx⟩ := exists_small_radial p q (isOpen_interior.inter Metric.isOpen_ball)
    (show p ∈ interior T.support ∩ Metric.ball p ε from ⟨hp, Metric.mem_ball_self hε⟩)
  let x := AffineMap.homothety p r q
  have hxS : S.coord e.val.2 x = -r := by
    rw [show x = AffineMap.lineMap p q r from AffineMap.homothety_eq_lineMap p r q,
      S.coord_lineMap, e.property.1, hq]
    ring
  have hxT : x ∈ T.support := interior_subset hx.1
  rw [← d.covers, Set.mem_iUnion] at hxT
  obtain ⟨b, hb⟩ := hxT
  have hba : b ≠ e.val.1 := by
    intro he
    have hnonneg := S.coord_nonneg (show x ∈ S.support by
      simpa only [S, Triangle.support_move, he] using hb) e.val.2
    rw [hxS] at hnonneg
    linarith
  have hpB : p ∈ (d.tile.move (d.place b)).support := by
    rw [Triangle.support_move]
    exact hlocal b x hx.2 hb
  obtain ⟨j, hj⟩ := (d.tile.move (d.place b)).openEdge_of_not_interior_nonvertex hpB
    (d.openEdge_not_mem_piece_interior e b) (fun j he => hv ⟨(b, j), he.symm⟩)
  refine ⟨⟨(b, j), hj⟩, ?_⟩
  intro he
  exact hba (congrArg (fun f : d.EdgePiece p => f.val.1) he)

theorem interior_edgePiece_card_eq_two {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (hp : p ∈ interior T.support) (hv : p ∉ d.vertices)
    (e : d.EdgePiece p) : Fintype.card (d.EdgePiece p) = 2 := by
  obtain ⟨f, hfe⟩ := d.exists_other_edgePiece hp hv e
  have hlt : 1 < Fintype.card (d.EdgePiece p) := Fintype.one_lt_card_iff.mpr ⟨f, e, hfe⟩
  exact le_antisymm (d.edgePiece_card_le_two p) (by omega)

end Erdos633b.Tiling
