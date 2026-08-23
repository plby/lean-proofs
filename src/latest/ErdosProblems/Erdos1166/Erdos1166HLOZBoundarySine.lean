import ErdosProblems.Erdos1166.Erdos1166HLOZDiscreteSine

namespace Erdos1166.KilledGreen

open scoped BigOperators

/-! # Boundary-face form of the square sine expansion

For a genuine first exit from the square, every contributing last-step
predecessor lies on one of the four faces.  This file records that geometry
and rewrites the source factor in the exact Green sine expansion as a normal
boundary sine times a tangential mode.  No absolute values are moved inside
the spectral sum, so the cancellation needed at corners is preserved. -/

/-- The coordinate of an admissible last-step predecessor is exactly on the
face crossed by its last step. -/
theorem exit_predecessor_coordinate
    {R : ℕ} {y : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R) :
    match p.1 with
    | 0 => (y - directionStep p).1 = (R : ℤ)
    | 1 => (y - directionStep p).1 = -(R : ℤ)
    | 2 => (y - directionStep p).2 = (R : ℤ)
    | _ => (y - directionStep p).2 = -(R : ℤ) := by
  unfold squareDisk at hy hp
  fin_cases p <;> simp [directionStep] at hy hp ⊢ <;> omega

/-- One coordinate of the Dirichlet sine basis. -/
noncomputable def squareSineCoordinate
    (R : ℕ) (k : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  Real.sin (squareSineAngle R k * (a : ℝ) +
    squareSineAngle R k * (R + 1 : ℝ))

/-- The normal sine factor of a mode at the boundary predecessor.  The signs
on the positive faces are the exact reflection signs, not estimates. -/
noncomputable def squareSinePredecessorFactor
    (R : ℕ) (p : Direction)
    (k l : Fin (2 * R + 1)) : ℝ :=
  match p.1 with
  | 0 => -((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k))
  | 1 => Real.sin (squareSineAngle R k)
  | 2 => -((-1 : ℝ) ^ ((l : ℕ) + 1) * Real.sin (squareSineAngle R l))
  | _ => Real.sin (squareSineAngle R l)

/-- The tangential factor of a mode at the boundary predecessor. -/
noncomputable def squareSinePredecessorTangential
    (R : ℕ) (p : Direction)
    (k l : Fin (2 * R + 1)) (z : Site) : ℝ :=
  match p.1 with
  | 0 | 1 => squareSineCoordinate R l z.2
  | _ => squareSineCoordinate R k z.1

theorem squareSineMode_right_face
    {R : ℕ} {z : Site} (hz : z.1 = (R : ℤ))
    (k l : Fin (2 * R + 1)) :
    squareSineMode R k l z =
      -((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) *
        squareSineCoordinate R l z.2 := by
  unfold squareSineMode planeSineMode squareSineCoordinate
  rw [hz]
  norm_num only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hphase :
      squareSineAngle R (k : Fin (2 * R + 1)) * (R : ℝ) +
          squareSineAngle R k * (R + 1 : ℝ) =
        (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi - squareSineAngle R k := by
    unfold squareSineAngle
    have hpos : (0 : ℝ) < (R + 1 : ℕ) := by positivity
    field_simp
    norm_num
    ring
  rw [hphase, Real.sin_nat_mul_pi_sub]

theorem squareSineMode_left_face
    {R : ℕ} {z : Site} (hz : z.1 = -(R : ℤ))
    (k l : Fin (2 * R + 1)) :
    squareSineMode R k l z =
      Real.sin (squareSineAngle R k) *
        squareSineCoordinate R l z.2 := by
  unfold squareSineMode planeSineMode squareSineCoordinate
  rw [hz]
  have hcast : ((-(R : ℤ) : ℤ) : ℝ) = -(R : ℝ) := by norm_num
  rw [hcast]
  have hphase :
      squareSineAngle R (k : Fin (2 * R + 1)) * (-(R : ℝ)) +
          squareSineAngle R k * (R + 1 : ℝ) = squareSineAngle R k := by
    ring
  rw [hphase]

theorem squareSineMode_top_face
    {R : ℕ} {z : Site} (hz : z.2 = (R : ℤ))
    (k l : Fin (2 * R + 1)) :
    squareSineMode R k l z =
      -((-1 : ℝ) ^ ((l : ℕ) + 1) * Real.sin (squareSineAngle R l)) *
        squareSineCoordinate R k z.1 := by
  unfold squareSineMode planeSineMode squareSineCoordinate
  rw [hz]
  norm_num only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hphase :
      squareSineAngle R (l : Fin (2 * R + 1)) * (R : ℝ) +
          squareSineAngle R l * (R + 1 : ℝ) =
        (((l : ℕ) + 1 : ℕ) : ℝ) * Real.pi - squareSineAngle R l := by
    unfold squareSineAngle
    have hpos : (0 : ℝ) < (R + 1 : ℕ) := by positivity
    field_simp
    norm_num
    ring
  rw [hphase, Real.sin_nat_mul_pi_sub]
  ring

theorem squareSineMode_bottom_face
    {R : ℕ} {z : Site} (hz : z.2 = -(R : ℤ))
    (k l : Fin (2 * R + 1)) :
    squareSineMode R k l z =
      Real.sin (squareSineAngle R l) *
        squareSineCoordinate R k z.1 := by
  unfold squareSineMode planeSineMode squareSineCoordinate
  rw [hz]
  have hcast : ((-(R : ℤ) : ℤ) : ℝ) = -(R : ℝ) := by norm_num
  rw [hcast]
  have hphase :
      squareSineAngle R (l : Fin (2 * R + 1)) * (-(R : ℝ)) +
          squareSineAngle R l * (R + 1 : ℝ) = squareSineAngle R l := by
    ring
  rw [hphase]
  ring

/-- Exact factorization of the source mode at an admissible predecessor. -/
theorem squareSineMode_exit_predecessor
    {R : ℕ} {y : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (k l : Fin (2 * R + 1)) :
    squareSineMode R k l (y - directionStep p) =
      squareSinePredecessorFactor R p k l *
        squareSinePredecessorTangential R p k l
          (y - directionStep p) := by
  have hface := exit_predecessor_coordinate p hy hp
  fin_cases p <;> simp only at hface ⊢
  · exact squareSineMode_right_face hface k l
  · exact squareSineMode_left_face hface k l
  · simpa [squareSinePredecessorFactor,
      squareSinePredecessorTangential, mul_comm] using
      squareSineMode_top_face hface k l
  · simpa [squareSinePredecessorFactor,
      squareSinePredecessorTangential, mul_comm] using
      squareSineMode_bottom_face hface k l

/-- Exact boundary-face version of the signed target-edge expansion. -/
theorem diskGreen_toReal_exit_predecessor_target_edge_sub_eq_boundary_sine_sum
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (e : Direction) (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R (y - directionStep p)
          (x + directionStep e)).toReal -
        (diskGreen R (y - directionStep p) x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          ((squareSinePredecessorFactor R p k l *
                squareSinePredecessorTangential R p k l
                  (y - directionStep p)) /
              squareSineEigenvalue R k l) *
            (squareSineMode R k l (x + directionStep e) -
              squareSineMode R k l x) := by
  rw [diskGreen_toReal_target_edge_sub_eq_signed_sine_sum hp e hx hxe]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineMode_exit_predecessor p hy hp]

/-- Exact boundary-face version of the positive reference denominator. -/
theorem diskGreen_toReal_exit_predecessor_eq_boundary_sine_sum
    {R : ℕ} {y referenceStart : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (href : referenceStart ∈ squareDisk R) :
    (diskGreen R (y - directionStep p) referenceStart).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          ((squareSinePredecessorFactor R p k l *
                squareSinePredecessorTangential R p k l
                  (y - directionStep p)) /
              squareSineEigenvalue R k l) *
            squareSineMode R k l referenceStart := by
  rw [diskGreen_toReal_eq_signed_sine_sum hp href]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineMode_exit_predecessor p hy hp]

/-! ## Normal-frequency resolvent regrouping

The following four profiles perform the normal-frequency summation first.
Thus each boundary Green column is represented by one signed tangential
sum.  This is the useful form for a corner estimate: taking absolute values
before this regrouping would destroy the tangential cancellation. -/

noncomputable def rightBoundaryNormalResolvent
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    (-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
      squareSineEigenvalue R k l) * squareSineCoordinate R k a

noncomputable def leftBoundaryNormalResolvent
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    (Real.sin (squareSineAngle R k) / squareSineEigenvalue R k l) *
      squareSineCoordinate R k a

noncomputable def topBoundaryNormalResolvent
    (R : ℕ) (k : Fin (2 * R + 1)) (b : ℤ) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    (-((-1 : ℝ) ^ ((l : ℕ) + 1) * Real.sin (squareSineAngle R l)) /
      squareSineEigenvalue R k l) * squareSineCoordinate R l b

noncomputable def bottomBoundaryNormalResolvent
    (R : ℕ) (k : Fin (2 * R + 1)) (b : ℤ) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    (Real.sin (squareSineAngle R l) / squareSineEigenvalue R k l) *
      squareSineCoordinate R l b

noncomputable def rightBoundaryColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
      rightBoundaryNormalResolvent R l x.1

noncomputable def leftBoundaryColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
      leftBoundaryNormalResolvent R l x.1

noncomputable def topBoundaryColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    squareSineCoordinate R k z.1 * squareSineCoordinate R k x.1 *
      topBoundaryNormalResolvent R k x.2

noncomputable def bottomBoundaryColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    squareSineCoordinate R k z.1 * squareSineCoordinate R k x.1 *
      bottomBoundaryNormalResolvent R k x.2

theorem diskGreen_toReal_right_face_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.1 = (R : ℤ))
    (hzmem : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        rightBoundaryColumnProfile R z x := by
  rw [diskGreen_toReal_eq_signed_sine_sum hzmem hx]
  unfold rightBoundaryColumnProfile
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  unfold rightBoundaryNormalResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [squareSineMode_right_face hz]
  unfold squareSineMode planeSineMode squareSineCoordinate
  ring

theorem diskGreen_toReal_left_face_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.1 = -(R : ℤ))
    (hzmem : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        leftBoundaryColumnProfile R z x := by
  rw [diskGreen_toReal_eq_signed_sine_sum hzmem hx]
  unfold leftBoundaryColumnProfile
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  unfold leftBoundaryNormalResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [squareSineMode_left_face hz]
  unfold squareSineMode planeSineMode squareSineCoordinate
  ring

theorem diskGreen_toReal_top_face_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.2 = (R : ℤ))
    (hzmem : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        topBoundaryColumnProfile R z x := by
  rw [diskGreen_toReal_eq_signed_sine_sum hzmem hx]
  unfold topBoundaryColumnProfile
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold topBoundaryNormalResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineMode_top_face hz]
  unfold squareSineMode planeSineMode squareSineCoordinate
  ring

theorem diskGreen_toReal_bottom_face_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.2 = -(R : ℤ))
    (hzmem : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        bottomBoundaryColumnProfile R z x := by
  rw [diskGreen_toReal_eq_signed_sine_sum hzmem hx]
  unfold bottomBoundaryColumnProfile
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold bottomBoundaryNormalResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineMode_bottom_face hz]
  unfold squareSineMode planeSineMode squareSineCoordinate
  ring

/-- The exact right-face edge gradient after the normal-frequency sum. -/
theorem diskGreen_toReal_right_face_target_edge_sub_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.1 = (R : ℤ))
    (hzmem : z ∈ squareDisk R) (e : Direction)
    (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R z (x + directionStep e)).toReal -
        (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (rightBoundaryColumnProfile R z (x + directionStep e) -
          rightBoundaryColumnProfile R z x) := by
  rw [diskGreen_toReal_right_face_eq_columnProfile hz hzmem hxe,
    diskGreen_toReal_right_face_eq_columnProfile hz hzmem hx]
  ring

theorem diskGreen_toReal_left_face_target_edge_sub_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.1 = -(R : ℤ))
    (hzmem : z ∈ squareDisk R) (e : Direction)
    (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R z (x + directionStep e)).toReal -
        (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (leftBoundaryColumnProfile R z (x + directionStep e) -
          leftBoundaryColumnProfile R z x) := by
  rw [diskGreen_toReal_left_face_eq_columnProfile hz hzmem hxe,
    diskGreen_toReal_left_face_eq_columnProfile hz hzmem hx]
  ring

theorem diskGreen_toReal_top_face_target_edge_sub_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.2 = (R : ℤ))
    (hzmem : z ∈ squareDisk R) (e : Direction)
    (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R z (x + directionStep e)).toReal -
        (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (topBoundaryColumnProfile R z (x + directionStep e) -
          topBoundaryColumnProfile R z x) := by
  rw [diskGreen_toReal_top_face_eq_columnProfile hz hzmem hxe,
    diskGreen_toReal_top_face_eq_columnProfile hz hzmem hx]
  ring

theorem diskGreen_toReal_bottom_face_target_edge_sub_eq_columnProfile
    {R : ℕ} {z x : Site} (hz : z.2 = -(R : ℤ))
    (hzmem : z ∈ squareDisk R) (e : Direction)
    (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R z (x + directionStep e)).toReal -
        (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (bottomBoundaryColumnProfile R z (x + directionStep e) -
          bottomBoundaryColumnProfile R z x) := by
  rw [diskGreen_toReal_bottom_face_eq_columnProfile hz hzmem hxe,
    diskGreen_toReal_bottom_face_eq_columnProfile hz hzmem hx]
  ring

/-- The one-dimensional-normal-resolvent profile selected by the crossed
face of an exit predecessor. -/
noncomputable def exitPredecessorColumnProfile
    (R : ℕ) (p : Direction) (y x : Site) : ℝ :=
  let z := y - directionStep p
  match p.1 with
  | 0 => rightBoundaryColumnProfile R z x
  | 1 => leftBoundaryColumnProfile R z x
  | 2 => topBoundaryColumnProfile R z x
  | _ => bottomBoundaryColumnProfile R z x

/-- Every admissible exit-predecessor Green column is the common positive
normalization times its single tangential signed sum. -/
theorem diskGreen_toReal_exit_predecessor_eq_columnProfile
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    (diskGreen R (y - directionStep p) x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        exitPredecessorColumnProfile R p y x := by
  have hface := exit_predecessor_coordinate p hy hp
  fin_cases p <;> simp only at hface ⊢
  · exact diskGreen_toReal_right_face_eq_columnProfile hface hp hx
  · exact diskGreen_toReal_left_face_eq_columnProfile hface hp hx
  · exact diskGreen_toReal_top_face_eq_columnProfile hface hp hx
  · exact diskGreen_toReal_bottom_face_eq_columnProfile hface hp hx

/-- Exact cancellation-preserving edge gradient in the regrouped
single-tangential-sum representation. -/
theorem diskGreen_toReal_exit_predecessor_target_edge_sub_eq_columnProfile
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (e : Direction) (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R (y - directionStep p)
          (x + directionStep e)).toReal -
        (diskGreen R (y - directionStep p) x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (exitPredecessorColumnProfile R p y (x + directionStep e) -
          exitPredecessorColumnProfile R p y x) := by
  rw [diskGreen_toReal_exit_predecessor_eq_columnProfile p hy hp hxe,
    diskGreen_toReal_exit_predecessor_eq_columnProfile p hy hp hx]
  ring

end Erdos1166.KilledGreen
