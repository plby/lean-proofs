import Mathlib

/-!
# Orthogonal projections for the Lovett--Meka edge walk

At a step of the Lovett--Meka walk, two finite collections of linear
conditions have to remain fixed: coordinates which are already close to a
face of the cube, and discrepancy constraints which are already close to
their permitted boundary.  An increment is therefore chosen in the
orthogonal complement of the span of the corresponding normal vectors.

This file packages that finite-dimensional linear algebra.  The definitions
are independent of the probabilistic law used to sample an increment.  In
particular, the dimension estimates show that fewer than half as many active
constraints as ambient coordinates leave a subspace of dimension greater
than half the ambient dimension.
-/

namespace Erdos228.ProjectionWalk

open scoped BigOperators

noncomputable section

/-! ## A generic finite family of active normal vectors -/

variable {I K : Type*} [Fintype I]

/-- The Euclidean space in which the finite edge walk takes place. -/
abbrev WalkSpace (I : Type*) [Fintype I] := EuclideanSpace ℝ I

/-- The span of the normals of all currently active linear constraints. -/
def constraintSpan (w : K → WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  Submodule.span ℝ (Set.range w)

/-- The subspace of permitted increments: every vector in it is orthogonal
to every currently active normal. -/
def incrementSubspace (w : K → WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  (constraintSpan w)ᗮ

/-- Orthogonally project an arbitrary proposed increment onto the permitted
increment subspace. -/
def projectIncrement (w : K → WalkSpace I) :
    WalkSpace I →L[ℝ] WalkSpace I :=
  (incrementSubspace w).starProjection

theorem normal_mem_constraintSpan (w : K → WalkSpace I) (k : K) :
    w k ∈ constraintSpan w := by
  exact Submodule.subset_span (Set.mem_range_self k)

/-- Orthogonality to the span is equivalent to orthogonality to the finite
family of generators. -/
theorem mem_incrementSubspace_iff (w : K → WalkSpace I) (x : WalkSpace I) :
    x ∈ incrementSubspace w ↔ ∀ k, inner ℝ (w k) x = 0 := by
  constructor
  · intro hx k
    exact (Submodule.mem_orthogonal (constraintSpan w) x).1 hx
      (w k) (normal_mem_constraintSpan w k)
  · intro hx
    rw [incrementSubspace, Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact hx k
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]

theorem projectIncrement_mem (w : K → WalkSpace I) (x : WalkSpace I) :
    projectIncrement w x ∈ incrementSubspace w := by
  exact (incrementSubspace w).starProjection_apply_mem x

/-- A projected increment changes none of the active linear functionals. -/
theorem inner_normal_projectIncrement (w : K → WalkSpace I)
    (x : WalkSpace I) (k : K) :
    inner ℝ (w k) (projectIncrement w x) = 0 := by
  exact (mem_incrementSubspace_iff w _).1 (projectIncrement_mem w x) k

/-- Projection does nothing to an already admissible increment. -/
theorem projectIncrement_eq_self_iff (w : K → WalkSpace I) (x : WalkSpace I) :
    projectIncrement w x = x ↔ x ∈ incrementSubspace w := by
  exact Submodule.starProjection_eq_self_iff

/-- Orthogonal projection does not increase the Euclidean norm. -/
theorem norm_projectIncrement_le (w : K → WalkSpace I) (x : WalkSpace I) :
    ‖projectIncrement w x‖ ≤ ‖x‖ := by
  exact (incrementSubspace w).norm_starProjection_apply_le x

/-- The part removed by projection lies in the active-constraint span. -/
theorem sub_projectIncrement_mem_constraintSpan
    (w : K → WalkSpace I) (x : WalkSpace I) :
    x - projectIncrement w x ∈ constraintSpan w := by
  change x - (incrementSubspace w).starProjection x ∈ constraintSpan w
  have heq : (incrementSubspace w)ᗮ = constraintSpan w := by
    rw [incrementSubspace, Submodule.orthogonal_orthogonal]
  rw [← heq]
  exact (incrementSubspace w).sub_starProjection_mem_orthogonal x

/-- Projection gives an orthogonal decomposition into permitted and removed
components. -/
theorem inner_projectIncrement_sub_eq_zero
    (w : K → WalkSpace I) (x : WalkSpace I) :
    inner ℝ (projectIncrement w x) (x - projectIncrement w x) = 0 := by
  have hmem := projectIncrement_mem w x
  have hspan := sub_projectIncrement_mem_constraintSpan w x
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal (constraintSpan w) _).1 hmem _ hspan

/-- Pythagoras for the proposed increment and its projected/removed pieces. -/
theorem norm_sq_eq_projectIncrement_add_removed
    (w : K → WalkSpace I) (x : WalkSpace I) :
    ‖x‖ ^ 2 = ‖projectIncrement w x‖ ^ 2 +
      ‖x - projectIncrement w x‖ ^ 2 := by
  have h := (incrementSubspace w).norm_sq_eq_add_norm_sq_starProjection x
  simpa [projectIncrement, incrementSubspace] using h

/-! ## Dimension and codimension -/

variable [Fintype K]

/-- The span of `m` active normals has dimension at most `m`, without any
linear-independence assumption. -/
theorem finrank_constraintSpan_le_card (w : K → WalkSpace I) :
    Module.finrank ℝ (constraintSpan w) ≤ Fintype.card K := by
  exact finrank_range_le_card w

omit [Fintype K] in
/-- Rank-nullity for the active span and its orthogonal complement. -/
theorem finrank_constraintSpan_add_incrementSubspace (w : K → WalkSpace I) :
    Module.finrank ℝ (constraintSpan w) +
      Module.finrank ℝ (incrementSubspace w) = Fintype.card I := by
  calc
    Module.finrank ℝ (constraintSpan w) +
        Module.finrank ℝ (incrementSubspace w) =
        Module.finrank ℝ (WalkSpace I) := by
      exact Submodule.finrank_add_finrank_orthogonal (constraintSpan w)
    _ = Fintype.card I := finrank_euclideanSpace

omit [Fintype K] in
/-- Codimension of the permitted-increment subspace is exactly the rank of
the active normals. -/
theorem codim_incrementSubspace (w : K → WalkSpace I) :
    Fintype.card I - Module.finrank ℝ (incrementSubspace w) =
      Module.finrank ℝ (constraintSpan w) := by
  have h := finrank_constraintSpan_add_incrementSubspace w
  omega

/-- The number of active constraints bounds the codimension of the permitted
increment subspace. -/
theorem codim_incrementSubspace_le_card (w : K → WalkSpace I) :
    Fintype.card I - Module.finrank ℝ (incrementSubspace w) ≤ Fintype.card K := by
  rw [codim_incrementSubspace]
  exact finrank_constraintSpan_le_card w

/-- Equivalently, at least `d-m` dimensions remain when there are `m`
active normals in ambient dimension `d`. -/
theorem card_sub_card_le_finrank_incrementSubspace (w : K → WalkSpace I) :
    Fintype.card I - Fintype.card K ≤
      Module.finrank ℝ (incrementSubspace w) := by
  have hrank := finrank_constraintSpan_le_card w
  have hsum := finrank_constraintSpan_add_incrementSubspace w
  omega

/-- If the active family has fewer elements than the ambient dimension, the
permitted-increment subspace contains a nonzero direction. -/
theorem finrank_incrementSubspace_pos (w : K → WalkSpace I)
    (hcard : Fintype.card K < Fintype.card I) :
    0 < Module.finrank ℝ (incrementSubspace w) := by
  have hrank := finrank_constraintSpan_le_card w
  have hsum := finrank_constraintSpan_add_incrementSubspace w
  omega

theorem incrementSubspace_ne_bot (w : K → WalkSpace I)
    (hcard : Fintype.card K < Fintype.card I) :
    incrementSubspace w ≠ ⊥ := by
  apply Submodule.nontrivial_iff_ne_bot.mp
  exact Module.finrank_pos_iff.mp (finrank_incrementSubspace_pos w hcard)

/-- The form used in the edge walk: fewer than `d/2` active constraints
leave strictly more than `d/2` dimensions available.  Writing the hypothesis
as `2*m < d` avoids all ambiguity from natural-number division. -/
theorem two_mul_card_lt_two_mul_finrank_incrementSubspace
    (w : K → WalkSpace I)
    (hhalf : 2 * Fintype.card K < Fintype.card I) :
    Fintype.card I < 2 * Module.finrank ℝ (incrementSubspace w) := by
  have hrank := finrank_constraintSpan_le_card w
  have hsum := finrank_constraintSpan_add_incrementSubspace w
  omega

theorem half_card_lt_finrank_incrementSubspace
    (w : K → WalkSpace I)
    (hhalf : 2 * Fintype.card K < Fintype.card I) :
    Fintype.card I / 2 < Module.finrank ℝ (incrementSubspace w) := by
  have h := two_mul_card_lt_two_mul_finrank_incrementSubspace w hhalf
  omega

/-! ## Coordinate and discrepancy constraints used by the edge walk -/

variable {J : Type*} [DecidableEq I]

/-- The standard coordinate normal. -/
def coordinateNormal (i : I) : WalkSpace I :=
  EuclideanSpace.single i 1

@[simp]
theorem inner_coordinateNormal (i : I) (x : WalkSpace I) :
    inner ℝ (coordinateNormal i) x = x i := by
  rw [coordinateNormal, EuclideanSpace.inner_single_left]
  norm_num

/-- A single indexed family containing both frozen coordinate normals and
active discrepancy normals. -/
def tightNormalFamily (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Sum coordinates discrepancies → WalkSpace I
  | Sum.inl i => coordinateNormal i.1
  | Sum.inr j => v j.1

/-- The subspace of increments preserving both kinds of tight constraint. -/
def tightIncrementSubspace (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) : Submodule ℝ (WalkSpace I) :=
  incrementSubspace (tightNormalFamily v coordinates discrepancies)

/-- Orthogonal projection onto the simultaneous tight-constraint subspace. -/
def projectTightIncrement (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) : WalkSpace I →L[ℝ] WalkSpace I :=
  projectIncrement (tightNormalFamily v coordinates discrepancies)

theorem mem_tightIncrementSubspace_iff
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSpace I) :
    x ∈ tightIncrementSubspace v coordinates discrepancies ↔
      (∀ i ∈ coordinates, x i = 0) ∧
      (∀ j ∈ discrepancies, inner ℝ (v j) x = 0) := by
  rw [tightIncrementSubspace, mem_incrementSubspace_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [tightNormalFamily, inner_coordinateNormal] using
        h (Sum.inl ⟨i, hi⟩)
    · intro j hj
      simpa [tightNormalFamily] using h (Sum.inr ⟨j, hj⟩)
  · rintro ⟨hcoord, hdisc⟩ k
    cases k with
    | inl i =>
        simpa [tightNormalFamily, inner_coordinateNormal] using hcoord i.1 i.2
    | inr j =>
        simpa [tightNormalFamily] using hdisc j.1 j.2

theorem projectTightIncrement_mem
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSpace I) :
    projectTightIncrement v coordinates discrepancies x ∈
      tightIncrementSubspace v coordinates discrepancies := by
  exact projectIncrement_mem _ x

/-- Every frozen coordinate of a projected increment is zero. -/
theorem projectTightIncrement_apply_eq_zero
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSpace I)
    {i : I} (hi : i ∈ coordinates) :
    projectTightIncrement v coordinates discrepancies x i = 0 := by
  exact (mem_tightIncrementSubspace_iff v coordinates discrepancies _).1
    (projectTightIncrement_mem v coordinates discrepancies x) |>.1 i hi

/-- Every active discrepancy normal is orthogonal to a projected increment. -/
theorem inner_projectTightIncrement_eq_zero
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSpace I)
    {j : J} (hj : j ∈ discrepancies) :
    inner ℝ (v j) (projectTightIncrement v coordinates discrepancies x) = 0 := by
  exact (mem_tightIncrementSubspace_iff v coordinates discrepancies _).1
    (projectTightIncrement_mem v coordinates discrepancies x) |>.2 j hj

omit [Fintype I] [DecidableEq I] in
/-- The combined active family has one index per frozen coordinate and one
per tight discrepancy constraint. -/
theorem card_tightNormalFamily_index (coordinates : Finset I)
    (discrepancies : Finset J) :
    Fintype.card (Sum coordinates discrepancies) =
      coordinates.card + discrepancies.card := by
  simp

/-- The active span has dimension at most the total number of coordinate and
discrepancy constraints. -/
theorem finrank_tightConstraintSpan_le
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Module.finrank ℝ
        (constraintSpan (tightNormalFamily v coordinates discrepancies)) ≤
      coordinates.card + discrepancies.card := by
  simpa using finrank_constraintSpan_le_card
    (tightNormalFamily v coordinates discrepancies)

/-- At least `d-m` dimensions remain after imposing the two kinds of active
constraint. -/
theorem card_sub_tight_card_le_finrank
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Fintype.card I - (coordinates.card + discrepancies.card) ≤
      Module.finrank ℝ (tightIncrementSubspace v coordinates discrepancies) := by
  have h := card_sub_card_le_finrank_incrementSubspace
    (tightNormalFamily v coordinates discrepancies)
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at h
  exact h

/-- The exact half-dimensional statement for the simultaneous constraints. -/
theorem half_card_lt_finrank_tightIncrementSubspace
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J)
    (hhalf : 2 * (coordinates.card + discrepancies.card) < Fintype.card I) :
    Fintype.card I / 2 <
      Module.finrank ℝ (tightIncrementSubspace v coordinates discrepancies) := by
  have hcard :
      2 * Fintype.card (Sum coordinates discrepancies) < Fintype.card I := by
    simpa using hhalf
  exact half_card_lt_finrank_incrementSubspace
    (tightNormalFamily v coordinates discrepancies) hcard

/-- A weak-half version useful when the active count is allowed to equal
`floor (d/2)`. -/
theorem half_card_le_finrank_tightIncrementSubspace
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J)
    (hhalf : coordinates.card + discrepancies.card ≤ Fintype.card I / 2) :
    Fintype.card I / 2 ≤
      Module.finrank ℝ (tightIncrementSubspace v coordinates discrepancies) := by
  have h := card_sub_tight_card_le_finrank v coordinates discrepancies
  omega

end

end Erdos228.ProjectionWalk
