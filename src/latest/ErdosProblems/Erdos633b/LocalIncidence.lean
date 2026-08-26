import ErdosProblems.Erdos633b.BoundaryCoordinates

/-! A finite geometric tiling agrees locally with its incident tiles.
No assumptions about how edges meet are used. -/

namespace Erdos633b.Tiling

theorem piece_isClosed {T : Triangle} {n : ℕ} (d : Tiling T n) (k : Fin n) :
    IsClosed (d.place k '' d.tile.support) :=
  (d.tile.support_isCompact.image (d.place k).continuous).isClosed

/-- A sufficiently small ball about any point meets only tiles containing
that point. This also holds outside the outer support. -/
theorem exists_incidence_radius {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    ∃ ε > 0, ∀ k : Fin n, ∀ x ∈ Metric.ball p ε,
      x ∈ d.place k '' d.tile.support → p ∈ d.place k '' d.tile.support := by
  classical
  let U : Fin n → Set Plane := fun k =>
    if p ∈ d.place k '' d.tile.support then Set.univ else (d.place k '' d.tile.support)ᶜ
  have hU : IsOpen (⋂ k, U k) := by
    apply isOpen_iInter_of_finite
    intro k
    by_cases hk : p ∈ d.place k '' d.tile.support
    · simpa only [U, if_pos hk] using isOpen_univ (X := Plane)
    · simpa only [U, if_neg hk] using (d.piece_isClosed k).isOpen_compl
  have hp : p ∈ ⋂ k, U k := by
    apply Set.mem_iInter.mpr
    intro k
    by_cases hk : p ∈ d.place k '' d.tile.support
    · simp only [U, if_pos hk, Set.mem_univ]
    · simpa only [U, if_neg hk, Set.mem_compl_iff] using hk
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  refine ⟨ε, hε, ?_⟩
  intro k x hx htile
  by_contra hk
  have hmem := Set.mem_iInter.mp (hball hx) k
  exact (show x ∉ d.place k '' d.tile.support by
    simpa only [U, if_neg hk, Set.mem_compl_iff] using hmem) htile

theorem local_cover {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    ∃ ε > 0, T.support ∩ Metric.ball p ε =
      ⋃ k : {k : Fin n // p ∈ d.place k '' d.tile.support},
        (d.place k.val '' d.tile.support) ∩ Metric.ball p ε := by
  obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius p
  refine ⟨ε, hε, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    rw [← d.covers, Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨k, hlocal k x hball hk⟩, hk, hball⟩
  · intro hx
    obtain ⟨k, hk, hball⟩ := Set.mem_iUnion.mp hx
    exact ⟨d.piece_subset k.val hk, hball⟩

theorem local_corner_cover {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    ∃ ε > 0, ∀ x ∈ Metric.ball (T.points i) ε,
      x ∈ T.support ↔ ∃ k : Fin n, ∃ j : Fin 3,
        d.place k (d.tile.points j) = T.points i ∧
        x ∈ d.place k '' d.tile.support := by
  obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius (T.points i)
  refine ⟨ε, hε, ?_⟩
  intro x hball
  constructor
  · intro hx
    rw [← d.covers, Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨j, hj⟩ := d.outer_vertex_of_mem_piece i k (hlocal k x hball hk)
    exact ⟨k, j, hj, hk⟩
  · rintro ⟨k, j, _, hk⟩
    exact d.piece_subset k hk

end Erdos633b.Tiling
