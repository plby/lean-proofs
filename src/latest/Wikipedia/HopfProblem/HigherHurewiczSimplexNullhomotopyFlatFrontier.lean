import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyFlatHomeomorph
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyFlatGeometry

/-!
# The flat simplex frontier is the actual barycentric boundary

All coordinates, including the restored zeroth coordinate, are positive
exactly in the ambient interior. Thus the ambient frontier corresponds
to the literal vanishing-coordinate boundary of the standard simplex.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz

/-- The ambient interior is exactly strict positivity of every original
barycentric coordinate, in every dimension. -/
theorem simplexFlatHomeomorph_mem_interior_iff (n : ℕ) (s : Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ interior (flatSimplexSet n) ↔
      ∀ i, 0 < s i := by
  rw [interior_flatSimplexSet]
  change ((∀ i : Fin n, 0 < s i.succ) ∧ ∑ i : Fin n, s i.succ < 1) ↔ _
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨hpos, hsum⟩ i
    refine Fin.cases ?_ (fun j => hpos j) i
    linarith
  · intro hpos
    exact ⟨fun i => hpos i.succ, by linarith [hpos 0]⟩

/-- The ambient frontier of the flattened simplex is precisely the
existing union of barycentric faces. -/
theorem simplexFlatHomeomorph_mem_frontier_iff (n : ℕ) (s : Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ frontier (flatSimplexSet n) ↔
      s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  rw [frontier, (isClosed_flatSimplexSet n).closure_eq]
  change (_ ∧ _) ↔ ∃ i : Fin (n + 1), s i = 0
  rw [simplexFlatHomeomorph_mem_interior_iff]
  constructor
  · rintro ⟨_, hnot⟩
    classical
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, le_antisymm hi (stdSimplex.zero_le s i)⟩
  · rintro ⟨i, hi⟩
    refine ⟨(simplexFlatHomeomorph n s).property, ?_⟩
    intro hpos
    have := hpos i
    rw [hi] at this
    exact (lt_irrefl 0) this

/-- The inverse coordinate map also identifies the actual boundary. -/
theorem simplexFlatHomeomorph_symm_mem_boundary_iff (n : ℕ)
    (v : ↥(flatSimplexSet n)) :
    (simplexFlatHomeomorph n).symm v ∈
        SecondHurewicz.SimplyConnected.simplexBoundary n ↔
      v.val ∈ frontier (flatSimplexSet n) := by
  simpa only [Homeomorph.apply_symm_apply] using
    (simplexFlatHomeomorph_mem_frontier_iff n ((simplexFlatHomeomorph n).symm v)).symm

/-- The image of the full face-boundary is the actual ambient frontier,
viewed in the flattened simplex. -/
theorem simplexFlatHomeomorph_image_boundary (n : ℕ) :
    simplexFlatHomeomorph n '' SecondHurewicz.SimplyConnected.simplexBoundary n =
      {v : ↥(flatSimplexSet n) | v.val ∈ frontier (flatSimplexSet n)} := by
  ext v
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (simplexFlatHomeomorph_mem_frontier_iff n s).2 hs
  · intro hv
    exact ⟨(simplexFlatHomeomorph n).symm v,
      (simplexFlatHomeomorph_symm_mem_boundary_iff n v).2 hv,
      (simplexFlatHomeomorph n).apply_symm_apply v⟩

end Wikipedia.HopfProblem.HigherHurewicz
