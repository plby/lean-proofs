import ErdosProblems.Erdos633b.CornerAngles

/-! An outer angle no larger than any reference tile angle cannot split.
This follows from actual incidence and the proved finite corner angle sum. -/

namespace Erdos633b.Tiling

theorem cornerPiece_subsingleton_of_min {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (hmin : ∀ j, T.angle i ≤ d.tile.angle j) :
    Subsingleton (d.CornerPiece i) := by
  classical
  constructor
  intro e f
  by_contra hef
  have hle : d.tile.angle e.val.2 + d.tile.angle f.val.2 ≤
      ∑ k : d.CornerPiece i, d.tile.angle k.val.2 :=
    Finset.add_le_sum (fun k _ => (d.tile.angle_pos k.val.2).le)
      (Finset.mem_univ e) (Finset.mem_univ f) hef
  rw [← d.angle_eq_sum_cornerPieces i] at hle
  have he := hmin e.val.2
  have hf := hmin f.val.2
  have hp := T.angle_pos i
  linarith

theorem exists_unique_cornerPiece_of_min {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (hmin : ∀ j, T.angle i ≤ d.tile.angle j) :
    ∃! _e : d.CornerPiece i, True := by
  obtain ⟨k, j, hj⟩ := d.outer_vertex_is_tile_vertex i
  let e : d.CornerPiece i := ⟨(k, j), hj⟩
  exact ⟨e, trivial, fun f _ => (d.cornerPiece_subsingleton_of_min i hmin).elim f e⟩

theorem angle_cornerPiece_of_min {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (hmin : ∀ j, T.angle i ≤ d.tile.angle j) (e : d.CornerPiece i) :
    d.tile.angle e.val.2 = T.angle i := by
  classical
  have heq : (∑ f : d.CornerPiece i, d.tile.angle f.val.2) = d.tile.angle e.val.2 :=
    Finset.sum_eq_single e
      (fun f _ hfe => False.elim (hfe ((d.cornerPiece_subsingleton_of_min i hmin).elim f e)))
      (fun he => False.elim (he (Finset.mem_univ e)))
  exact heq.symm.trans (d.angle_eq_sum_cornerPieces i).symm

theorem cornerSection_eq_edge_of_min {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (hmin : ∀ j, T.angle i ≤ d.tile.angle j) (e : d.CornerPiece i) :
    T.cornerSection (d.tile.move (d.place e.val.1)) i e.val.2 = T.edge i := by
  calc
    _ = ⋃ f : d.CornerPiece i,
        T.cornerSection (d.tile.move (d.place f.val.1)) i f.val.2 := by
      apply Set.Subset.antisymm
      · intro q hq
        exact Set.mem_iUnion.mpr ⟨e, hq⟩
      · intro q hq
        obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hq
        rwa [(d.cornerPiece_subsingleton_of_min i hmin).elim f e] at hf
    _ = T.edge i := d.corner_sections_cover i

end Erdos633b.Tiling
