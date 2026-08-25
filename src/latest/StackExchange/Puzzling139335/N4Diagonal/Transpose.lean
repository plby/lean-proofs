import StackExchange.Puzzling139335.N4Diagonal.Transpose.Images

/-!
# Transposing the normalized diagonal model

Reflection in `x = y` preserves the lower half-square and commutes with the
anti-diagonal reflection. Exchanging the first and last corner types restores
the angular order. Every field below is transported from the actual model,
including its full corner neighborhoods, coverage, and disjoint interiors.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ReflectionSeparation ThreeCorners

noncomputable section

namespace Model

/-- Transpose all coordinates and exchange the first and last corner types. -/
def transpose (m : Model) : Model where
  P := diagonal '' m.P
  p := diagonal m.q
  q := diagonal m.p
  θ := Real.pi / 2 - m.β
  β := Real.pi / 2 - m.θ
  e := transposeIsometry m.f
  f := transposeIsometry m.e
  firstCorner := -m.lastCorner
  lastCorner := -m.firstCorner
  jordan := m.jordan.image_homeomorph diagonal.toHomeomorph
  triangle := by
    rintro _ ⟨x, hx, rfl⟩
    exact diagonal_mem_lowerTriangle.mpr (m.triangle hx)
  origin_mem := by
    simpa only [diagonal_zero] using mem_image_of_mem diagonal m.origin_mem
  origin_full := by
    simpa only [diagonal_zero] using m.origin_full.map diagonal
  p_mem := mem_image_of_mem diagonal m.q_mem
  q_mem := mem_image_of_mem diagonal m.p_mem
  p_ne_origin := by
    intro h
    apply m.q_ne_origin
    simpa only [diagonal_involutive, diagonal_zero] using congrArg diagonal h
  q_ne_origin := by
    intro h
    apply m.p_ne_origin
    simpa only [diagonal_involutive, diagonal_zero] using congrArg diagonal h
  p_ne_q := fun h => m.p_ne_q (diagonal.injective h).symm
  p_full := m.q_full.map diagonal
  q_full := m.p_full.map diagonal
  theta_bounds := by
    constructor
    · linarith [m.beta_bounds.2]
    · linarith [m.beta_nonneg]
  beta_bounds := by
    constructor
    · linarith [m.beta_bounds.1]
    · linarith [m.theta_bounds.1]
  first_support := by
    rintro _ ⟨x, hx, rfl⟩
    rw [inner_perpRay_diagonal_sub, inner_ray_diagonal_sub]
    exact ⟨neg_nonneg.mpr (m.last_support x hx).2, (m.last_support x hx).1⟩
  last_support := by
    rintro _ ⟨x, hx, rfl⟩
    rw [inner_ray_diagonal_sub, inner_perpRay_diagonal_sub]
    exact ⟨(m.first_support x hx).2, neg_nonpos.mpr (m.first_support x hx).1⟩
  first_subset := by
    rw [transposeIsometry_image]
    rintro _ ⟨x, hx, rfl⟩
    exact diagonal_mem_unitSquare.mpr (m.last_subset hx)
  last_subset := by
    rw [transposeIsometry_image]
    rintro _ ⟨x, hx, rfl⟩
    exact diagonal_mem_unitSquare.mpr (m.first_subset hx)
  first_corner := by
    rw [transposeIsometry_apply, diagonal_involutive, m.last_corner, diagonal_corner]
  last_corner := by
    rw [transposeIsometry_apply, diagonal_involutive, m.first_corner, diagonal_corner]
  corner_order := by
    rcases m.corner_order with ⟨hf, hl⟩ | ⟨hf, hl⟩
    · left
      rw [hf, hl]
      decide
    · right
      rw [hf, hl]
      decide
  origin_only_corner := by
    simpa only [neg_zero] using only_corner_diagonal_image m.origin_only_corner
  first_only_corner := by
    rw [transposeIsometry_image]
    exact only_corner_diagonal_image m.last_only_corner
  last_only_corner := by
    rw [transposeIsometry_image]
    exact only_corner_diagonal_image m.first_only_corner
  cover := by
    intro x hx
    have hx' := diagonal_mem_unitSquare.mpr hx
    rcases m.cover (diagonal x) hx' with hp | hq | he | hf
    · exact Or.inl (mem_diagonal_image_iff.mpr hp)
    · exact Or.inr (Or.inl (by
        rw [antiDiagonal_diagonal_image]
        exact mem_diagonal_image_iff.mpr hq))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [transposeIsometry_image]
        exact mem_diagonal_image_iff.mpr he)))
    · exact Or.inr (Or.inr (Or.inl (by
        rw [transposeIsometry_image]
        exact mem_diagonal_image_iff.mpr hf)))
  disjoint := by
    intro i j hij
    rw [pieces_transposed, pieces_transposed]
    exact RectangularHull.disjoint_interiors_image_homeomorph
      (m.disjoint ((Equiv.swap (1 : Fin 4) 3).injective.ne hij))
      diagonal.toHomeomorph

@[simp] theorem transpose_P (m : Model) : m.transpose.P = diagonal '' m.P := rfl

@[simp] theorem transpose_p (m : Model) : m.transpose.p = diagonal m.q := rfl

@[simp] theorem transpose_q (m : Model) : m.transpose.q = diagonal m.p := rfl

@[simp] theorem transpose_theta (m : Model) :
    m.transpose.θ = Real.pi / 2 - m.β := rfl

@[simp] theorem transpose_beta (m : Model) :
    m.transpose.β = Real.pi / 2 - m.θ := rfl

@[simp] theorem transpose_e (m : Model) : m.transpose.e = transposeIsometry m.f := rfl

@[simp] theorem transpose_f (m : Model) : m.transpose.f = transposeIsometry m.e := rfl

/-- The singleton corner assignment is unchanged after swapping the types. -/
@[simp] theorem transpose_firstCorner (m : Model) :
    m.transpose.firstCorner = m.firstCorner := by
  change -m.lastCorner = m.firstCorner
  rcases m.corner_order with ⟨hf, hl⟩ | ⟨hf, hl⟩ <;>
    rw [hf, hl] <;> decide

@[simp] theorem transpose_lastCorner (m : Model) :
    m.transpose.lastCorner = m.lastCorner := by
  change -m.firstCorner = m.lastCorner
  rcases m.corner_order with ⟨hf, hl⟩ | ⟨hf, hl⟩ <;>
    rw [hf, hl] <;> decide

theorem transpose_first_image (m : Model) :
    m.transpose.e '' m.transpose.P = diagonal '' (m.f '' m.P) :=
  transposeIsometry_image m.f m.P

theorem transpose_last_image (m : Model) :
    m.transpose.f '' m.transpose.P = diagonal '' (m.e '' m.P) :=
  transposeIsometry_image m.e m.P

theorem transpose_piece (m : Model) (i : Fin 4) :
    m.transpose.piece i = diagonal '' m.piece (Equiv.swap 1 3 i) :=
  pieces_transposed m.P m.e m.f i

theorem transpose_first_center_iff (m : Model) :
    squareCenter ∈ interior (m.transpose.e '' m.transpose.P) ↔
      squareCenter ∈ interior (m.f '' m.P) := by
  rw [transpose_first_image]
  simpa only [diagonal_center] using
    (mem_interior_image_affineIsometry diagonal (P := m.f '' m.P)
      (p := squareCenter))

theorem transpose_last_center_iff (m : Model) :
    squareCenter ∈ interior (m.transpose.f '' m.transpose.P) ↔
      squareCenter ∈ interior (m.e '' m.P) := by
  rw [transpose_last_image]
  simpa only [diagonal_center] using
    (mem_interior_image_affineIsometry diagonal (P := m.e '' m.P)
      (p := squareCenter))

/-- Transposition preserves the possible center owner among the two singleton
copies, without assuming any symmetry of the prototype or its placements. -/
theorem transpose_center_disjunction_iff (m : Model) :
    (squareCenter ∈ interior (m.transpose.e '' m.transpose.P) ∨
      squareCenter ∈ interior (m.transpose.f '' m.transpose.P)) ↔
    (squareCenter ∈ interior (m.e '' m.P) ∨
      squareCenter ∈ interior (m.f '' m.P)) := by
  rw [transpose_first_center_iff, transpose_last_center_iff]
  exact or_comm

end Model

end

end Puzzling139335.N4Diagonal
