import ErdosProblems.Erdos633b.CornerSection
import ErdosProblems.Erdos633b.SmallRadial

/-! The actual incident tiles at an outer corner project to an exact finite
partition of the opposite side, with pairwise disjoint open intervals. -/

namespace Erdos633b.Tiling

def CornerPiece {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :=
  {e : Fin n × Fin 3 // d.place e.1 (d.tile.points e.2) = T.points i}

instance {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) : Finite (d.CornerPiece i) := by
  unfold CornerPiece
  infer_instance

theorem cornerPiece_tile_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Function.Injective (fun e : d.CornerPiece i => e.val.1) := by
  intro e f h
  change e.val.1 = f.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply d.tile.independent.injective
  apply (d.place e.val.1).injective
  exact e.property.trans (by rw [h]; exact f.property.symm)

theorem corner_sections_cover {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    (⋃ e : d.CornerPiece i,
      T.cornerSection (d.tile.move (d.place e.val.1)) i e.val.2) = T.edge i := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hq
    apply T.cornerSection_subset_edge (d.tile.move (d.place e.val.1)) ?_ i e.val.2 e.property he
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  · intro q hq
    obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius (T.points i)
    obtain ⟨r, hr, hr1, hxball⟩ := exists_small_radial (T.points i) q Metric.isOpen_ball
      (Metric.mem_ball_self hε)
    have hxT := T.homothety_vertex_mem_support i hq.1 hr.le hr1.le
    rw [← d.covers, Set.mem_iUnion] at hxT
    obtain ⟨k, hk⟩ := hxT
    obtain ⟨j, hj⟩ := d.outer_vertex_of_mem_piece i k (hlocal k _ hxball hk)
    let S : Triangle := d.tile.move (d.place k)
    have hST : S.support ⊆ T.support := by
      rw [Triangle.support_move]
      exact d.piece_subset k
    have hxS : AffineMap.homothety (T.points i) r q ∈ S.support := by
      rwa [Triangle.support_move]
    have hO : S.points j = T.points i := hj
    have hcoord (l : Fin 3) (hl : l ≠ j) : 0 ≤ S.coord l q := by
      have h := S.coord_nonneg hxS l
      rw [T.coord_radial_shared S i j l hO hl] at h
      nlinarith
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(k, j), hj⟩, ?_⟩
    apply (T.mem_cornerSection_iff S hST i j hO q).mpr
    exact ⟨hq, hcoord (j + 1) ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j),
      hcoord (j + 2) ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j)⟩

theorem corner_sections_open_pairwise {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Pairwise fun e f : d.CornerPiece i =>
      Disjoint (T.openCornerSection (d.tile.move (d.place e.val.1)) i e.val.2)
        (T.openCornerSection (d.tile.move (d.place f.val.1)) i f.val.2) := by
  intro e f hef
  have hk : e.val.1 ≠ f.val.1 := (d.cornerPiece_tile_injective i).ne hef
  let S : Triangle := d.tile.move (d.place e.val.1)
  let R : Triangle := d.tile.move (d.place f.val.1)
  have hST : S.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  have hRT : R.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset f.val.1
  have hSO : S.points e.val.2 = T.points i := e.property
  have hRO : R.points f.val.2 = T.points i := f.property
  apply Set.disjoint_left.mpr
  intro q hqS hqR
  obtain ⟨_, hS1, hS2⟩ := (T.mem_openCornerSection_iff S hST i e.val.2 hSO q).mp hqS
  obtain ⟨_, hR1, hR2⟩ := (T.mem_openCornerSection_iff R hRT i f.val.2 hRO q).mp hqR
  let U : Set Plane := {x | 0 < S.coord e.val.2 x} ∩ {x | 0 < R.coord f.val.2 x}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (continuous_barycentric_coord S.affineBasis e.val.2)).inter
      (isOpen_lt continuous_const (continuous_barycentric_coord R.affineBasis f.val.2))
  have hO : T.points i ∈ U := by
    constructor
    · change 0 < S.coord e.val.2 (T.points i)
      calc
        0 < S.coord e.val.2 (S.points e.val.2) := by simp [Triangle.coord_vertex]
        _ = S.coord e.val.2 (T.points i) := congrArg (S.coord e.val.2) hSO
    · change 0 < R.coord f.val.2 (T.points i)
      calc
        0 < R.coord f.val.2 (R.points f.val.2) := by simp [Triangle.coord_vertex]
        _ = R.coord f.val.2 (T.points i) := congrArg (R.coord f.val.2) hRO
  obtain ⟨r, hr, _, hrad⟩ := exists_small_radial (T.points i) q hU hO
  have hxS := S.radial_mem_interior_of_noncentral_pos e.val.2 r hr q hS1 hS2
    (show 0 < S.coord e.val.2 (AffineMap.homothety (S.points e.val.2) r q) by
      rw [hSO]; exact hrad.1)
  have hxR := R.radial_mem_interior_of_noncentral_pos f.val.2 r hr q hR1 hR2
    (show 0 < R.coord f.val.2 (AffineMap.homothety (R.points f.val.2) r q) by
      rw [hRO]; exact hrad.2)
  rw [hSO] at hxS
  rw [hRO] at hxR
  rw [Triangle.support_move] at hxS hxR
  exact Set.disjoint_left.mp (d.disjoint_interiors hk) hxS hxR

end Erdos633b.Tiling
