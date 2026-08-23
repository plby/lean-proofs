import ErdosProblems.Erdos1166.Erdos1166HLOZKilledGreenReflection

namespace Erdos1166.KilledGreen

open scoped BigOperators

noncomputable def planeSineMode
    (thetaX thetaY phaseX phaseY : ℝ) (x : Site) : ℝ :=
  Real.sin (thetaX * (x.1 : ℝ) + phaseX) *
    Real.sin (thetaY * (x.2 : ℝ) + phaseY)

theorem stepAverage_planeSineMode
    (thetaX thetaY phaseX phaseY : ℝ) (x : Site) :
    stepAverage (planeSineMode thetaX thetaY phaseX phaseY) x =
      ((Real.cos thetaX + Real.cos thetaY) / 2) *
        planeSineMode thetaX thetaY phaseX phaseY x := by
  unfold stepAverage planeSineMode
  rw [Fin.sum_univ_four]
  norm_num [directionStep]
  have hxplus : thetaX * ((x.1 : ℝ) + 1) + phaseX =
      (thetaX * (x.1 : ℝ) + phaseX) + thetaX := by ring
  have hxminus : thetaX * ((x.1 : ℝ) + -1) + phaseX =
      (thetaX * (x.1 : ℝ) + phaseX) - thetaX := by ring
  have hyplus : thetaY * ((x.2 : ℝ) + 1) + phaseY =
      (thetaY * (x.2 : ℝ) + phaseY) + thetaY := by ring
  have hyminus : thetaY * ((x.2 : ℝ) + -1) + phaseY =
      (thetaY * (x.2 : ℝ) + phaseY) - thetaY := by ring
  rw [hxplus, hxminus, hyplus, hyminus]
  have sin_add_sub (a t : ℝ) :
      Real.sin (a + t) + Real.sin (a - t) =
        2 * Real.sin a * Real.cos t := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  rw [show
      Real.sin ((thetaX * (x.1 : ℝ) + phaseX) + thetaX) *
          Real.sin (thetaY * (x.2 : ℝ) + phaseY) +
        Real.sin ((thetaX * (x.1 : ℝ) + phaseX) - thetaX) *
          Real.sin (thetaY * (x.2 : ℝ) + phaseY) +
        Real.sin (thetaX * (x.1 : ℝ) + phaseX) *
          Real.sin ((thetaY * (x.2 : ℝ) + phaseY) + thetaY) +
        Real.sin (thetaX * (x.1 : ℝ) + phaseX) *
          Real.sin ((thetaY * (x.2 : ℝ) + phaseY) - thetaY) =
        (Real.sin ((thetaX * (x.1 : ℝ) + phaseX) + thetaX) +
            Real.sin ((thetaX * (x.1 : ℝ) + phaseX) - thetaX)) *
            Real.sin (thetaY * (x.2 : ℝ) + phaseY) +
          Real.sin (thetaX * (x.1 : ℝ) + phaseX) *
            (Real.sin ((thetaY * (x.2 : ℝ) + phaseY) + thetaY) +
              Real.sin ((thetaY * (x.2 : ℝ) + phaseY) - thetaY)) by ring]
  rw [sin_add_sub, sin_add_sub]
  ring

/-- The one-dimensional Dirichlet frequencies for the integer interval
`[-R,R]`.  The endpoints just outside the interval are `-(R+1)` and
`R+1`, so the denominator is `2R+2`. -/
noncomputable def squareSineAngle (R : ℕ) (k : Fin (2 * R + 1)) : ℝ :=
  Real.pi * ((k : ℕ) + 1 : ℝ) / (2 * (R + 1) : ℝ)

/-- The tensor-product sine mode on the square `[-R,R]²`, extended to the
whole lattice by the same formula. -/
noncomputable def squareSineMode (R : ℕ)
    (k l : Fin (2 * R + 1)) : Site → ℝ :=
  planeSineMode (squareSineAngle R k) (squareSineAngle R l)
    (squareSineAngle R k * (R + 1 : ℝ))
    (squareSineAngle R l * (R + 1 : ℝ))

noncomputable def squareSineEigenvalue (R : ℕ)
    (k l : Fin (2 * R + 1)) : ℝ :=
  1 - (Real.cos (squareSineAngle R k) +
    Real.cos (squareSineAngle R l)) / 2

theorem squareSineAngle_pos (R : ℕ) (k : Fin (2 * R + 1)) :
    0 < squareSineAngle R k := by
  unfold squareSineAngle
  positivity

theorem squareSineAngle_lt_pi (R : ℕ) (k : Fin (2 * R + 1)) :
    squareSineAngle R k < Real.pi := by
  unfold squareSineAngle
  have hk : (((k : ℕ) + 1 : ℕ) : ℝ) < 2 * (R + 1 : ℝ) := by
    exact_mod_cast (show (k : ℕ) + 1 < 2 * (R + 1) by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at hk
  have hden : (0 : ℝ) < 2 * (R + 1 : ℝ) := by positivity
  apply (div_lt_iff₀ hden).2
  exact mul_lt_mul_of_pos_left hk Real.pi_pos

theorem squareSineEigenvalue_pos (R : ℕ)
    (k l : Fin (2 * R + 1)) :
    0 < squareSineEigenvalue R k l := by
  have hk : Real.cos (squareSineAngle R k) < 1 := by
    simpa using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show squareSineAngle R k ∈ Set.Icc 0 Real.pi from
        ⟨(squareSineAngle_pos R k).le, (squareSineAngle_lt_pi R k).le⟩)
      (squareSineAngle_pos R k)
  have hl : Real.cos (squareSineAngle R l) < 1 := by
    simpa using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show squareSineAngle R l ∈ Set.Icc 0 Real.pi from
        ⟨(squareSineAngle_pos R l).le, (squareSineAngle_lt_pi R l).le⟩)
      (squareSineAngle_pos R l)
  unfold squareSineEigenvalue
  linarith

/-- A quantitative lower bound for every square Dirichlet eigenvalue.  It
is the exact scale needed when the Green kernel is later estimated by its
finite sine expansion. -/
theorem squareSineAngle_sq_add_sq_div_pi_sq_le_eigenvalue
    (R : ℕ) (k l : Fin (2 * R + 1)) :
    (squareSineAngle R k ^ 2 + squareSineAngle R l ^ 2) /
        Real.pi ^ 2 ≤ squareSineEigenvalue R k l := by
  have hkabs : |squareSineAngle R k| ≤ Real.pi := by
    rw [abs_of_pos (squareSineAngle_pos R k)]
    exact (squareSineAngle_lt_pi R k).le
  have hlabs : |squareSineAngle R l| ≤ Real.pi := by
    rw [abs_of_pos (squareSineAngle_pos R l)]
    exact (squareSineAngle_lt_pi R l).le
  have hk := Real.cos_le_one_sub_mul_cos_sq hkabs
  have hl := Real.cos_le_one_sub_mul_cos_sq hlabs
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  unfold squareSineEigenvalue
  apply (div_le_iff₀ hpi).2
  have hk' := mul_le_mul_of_nonneg_right hk hpi.le
  have hl' := mul_le_mul_of_nonneg_right hl hpi.le
  have hkid :
      (1 - 2 / Real.pi ^ 2 * squareSineAngle R k ^ 2) * Real.pi ^ 2 =
        Real.pi ^ 2 - 2 * squareSineAngle R k ^ 2 := by
    field_simp
  have hlid :
      (1 - 2 / Real.pi ^ 2 * squareSineAngle R l ^ 2) * Real.pi ^ 2 =
        Real.pi ^ 2 - 2 * squareSineAngle R l ^ 2 := by
    field_simp
  rw [hkid] at hk'
  rw [hlid] at hl'
  nlinarith

theorem squareSineEigenvalue_le_two (R : ℕ)
    (k l : Fin (2 * R + 1)) :
    squareSineEigenvalue R k l ≤ 2 := by
  have hk := Real.neg_one_le_cos (squareSineAngle R k)
  have hl := Real.neg_one_le_cos (squareSineAngle R l)
  unfold squareSineEigenvalue
  linarith

theorem stepAverage_squareSineMode (R : ℕ)
    (k l : Fin (2 * R + 1)) (x : Site) :
    stepAverage (squareSineMode R k l) x =
      ((Real.cos (squareSineAngle R k) +
          Real.cos (squareSineAngle R l)) / 2) *
        squareSineMode R k l x := by
  exact stepAverage_planeSineMode _ _ _ _ x

/-- Every tensor sine mode is an eigenfunction of `I-P`. -/
theorem squareDirichletOperator_squareSineMode (R : ℕ)
    (k l : Fin (2 * R + 1)) (x : Site) :
    squareDirichletOperator (squareSineMode R k l) x =
      squareSineEigenvalue R k l * squareSineMode R k l x := by
  rw [show squareDirichletOperator (squareSineMode R k l) x =
      squareSineMode R k l x - stepAverage (squareSineMode R k l) x by
    rfl]
  rw [stepAverage_squareSineMode]
  unfold squareSineEigenvalue
  ring

theorem squareSineMode_left_boundary (R : ℕ)
    (k l : Fin (2 * R + 1)) (b : ℤ) :
    squareSineMode R k l (-(R + 1 : ℤ), b) = 0 := by
  unfold squareSineMode planeSineMode
  have hphase :
      squareSineAngle R k * ((-(R + 1 : ℤ) : ℤ) : ℝ) +
          squareSineAngle R k * (R + 1 : ℝ) = 0 := by
    push_cast
    ring
  rw [hphase]
  simp

theorem squareSineMode_bottom_boundary (R : ℕ)
    (k l : Fin (2 * R + 1)) (a : ℤ) :
    squareSineMode R k l (a, -(R + 1 : ℤ)) = 0 := by
  unfold squareSineMode planeSineMode
  have hphase :
      squareSineAngle R l * ((-(R + 1 : ℤ) : ℤ) : ℝ) +
          squareSineAngle R l * (R + 1 : ℝ) = 0 := by
    push_cast
    ring
  rw [hphase]
  simp

private theorem squareSineAngle_two_mul_radius (R : ℕ)
    (k : Fin (2 * R + 1)) :
    squareSineAngle R k * (R + 1 : ℝ) +
        squareSineAngle R k * (R + 1 : ℝ) =
      (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
  unfold squareSineAngle
  have hpos : (0 : ℝ) < (R + 1 : ℕ) := by positivity
  field_simp
  norm_num
  ring

theorem squareSineMode_right_boundary (R : ℕ)
    (k l : Fin (2 * R + 1)) (b : ℤ) :
    squareSineMode R k l ((R + 1 : ℕ), b) = 0 := by
  unfold squareSineMode planeSineMode
  norm_num
  rw [squareSineAngle_two_mul_radius]
  left
  simpa [mul_comm] using Real.sin_nat_mul_pi ((k : ℕ) + 1)

theorem squareSineMode_top_boundary (R : ℕ)
    (k l : Fin (2 * R + 1)) (a : ℤ) :
    squareSineMode R k l (a, (R + 1 : ℕ)) = 0 := by
  unfold squareSineMode planeSineMode
  norm_num
  rw [squareSineAngle_two_mul_radius]
  right
  simpa [mul_comm] using Real.sin_nat_mul_pi ((l : ℕ) + 1)

/-- A mode vanishes on every lattice site in the one-layer boundary of the
square.  The explicit four-line lemmas above make this corner-safe. -/
theorem squareSineMode_eq_zero_of_mem_succ_not_mem
    (R : ℕ) (k l : Fin (2 * R + 1)) {x : Site}
    (hx : x ∈ squareDisk (R + 1)) (hout : x ∉ squareDisk R) :
    squareSineMode R k l x = 0 := by
  rcases x with ⟨a, b⟩
  rcases Finset.mem_product.mp hx with ⟨ha, hb⟩
  rcases Finset.mem_Icc.mp ha with ⟨hal, hau⟩
  rcases Finset.mem_Icc.mp hb with ⟨hbl, hbu⟩
  have hedge :
      a = -(R + 1 : ℤ) ∨ a = (R + 1 : ℕ) ∨
        b = -(R + 1 : ℤ) ∨ b = (R + 1 : ℕ) := by
    by_contra h
    apply hout
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> omega
  rcases hedge with ha | ha | hb | hb
  · subst a
    exact squareSineMode_left_boundary R k l b
  · subst a
    exact squareSineMode_right_boundary R k l b
  · subst b
    exact squareSineMode_bottom_boundary R k l a
  · subst b
    exact squareSineMode_top_boundary R k l a

/-! ## The exact finite spectral resolvent candidate -/

theorem squareDirichletOperator_const_mul (c : ℝ) (u : Site → ℝ)
    (x : Site) :
    squareDirichletOperator (fun z ↦ c * u z) x =
      c * squareDirichletOperator u x := by
  unfold squareDirichletOperator
  rw [← Finset.mul_sum]
  ring

theorem squareDirichletOperator_sum {ι : Type*} [Fintype ι]
    (u : ι → Site → ℝ) (x : Site) :
    squareDirichletOperator (fun z ↦ ∑ i, u i z) x =
      ∑ i, squareDirichletOperator (u i) x := by
  unfold squareDirichletOperator
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.mul_sum]
  apply congrArg ((1 / 4 : ℝ) * ·)
  rw [Finset.sum_comm]

/-- Uniqueness for the finite square Dirichlet problem, derived from the
already proved square maximum principle. -/
theorem eq_on_squareDisk_of_dirichletOperator_eq_of_boundary_eq
    {R : ℕ} {u v : Site → ℝ}
    (hop : ∀ x ∈ squareDisk R,
      squareDirichletOperator u x = squareDirichletOperator v x)
    (hboundary : ∀ x ∈ squareDisk (R + 1), x ∉ squareDisk R →
      u x = v x) :
    ∀ x ∈ squareDisk R, u x = v x := by
  have huvHarm : ∀ x ∈ squareDisk R,
      u x - v x = stepAverage (fun z ↦ u z - v z) x := by
    intro x hx
    have h := hop x hx
    unfold squareDirichletOperator at h
    rw [stepAverage_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  have hvuHarm : ∀ x ∈ squareDisk R,
      v x - u x = stepAverage (fun z ↦ v z - u z) x := by
    intro x hx
    have h := hop x hx
    unfold squareDirichletOperator at h
    rw [stepAverage_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h.symm
  have huvBoundary : ∀ x ∈ squareDisk (R + 1), x ∉ squareDisk R →
      u x - v x ≤ 0 := by
    intro x hx hout
    rw [hboundary x hx hout]
    simp
  have hvuBoundary : ∀ x ∈ squareDisk (R + 1), x ∉ squareDisk R →
      v x - u x ≤ 0 := by
    intro x hx hout
    rw [hboundary x hx hout]
    simp
  intro x hx
  have huv := square_maximum_principle huvHarm huvBoundary x hx
  have hvu := square_maximum_principle hvuHarm hvuBoundary x hx
  linarith

/-- The finite double sine sum which is the square Green kernel once the
discrete sine completeness identity is applied.  Keeping the sum signed is
essential near corners: an absolute-value estimate term by term loses the
boundary cancellation needed by HLOZ. -/
noncomputable def squareSpectralGreenCandidate
    (R : ℕ) (z x : Site) : ℝ :=
  (4 / (2 * (R + 1 : ℝ)) ^ 2) *
    ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
      (squareSineMode R k l z / squareSineEigenvalue R k l) *
        squareSineMode R k l x

theorem squareSpectralGreenCandidate_eq_zero_of_mem_succ_not_mem
    (R : ℕ) (z : Site) {x : Site}
    (hx : x ∈ squareDisk (R + 1)) (hout : x ∉ squareDisk R) :
    squareSpectralGreenCandidate R z x = 0 := by
  unfold squareSpectralGreenCandidate
  simp_rw [squareSineMode_eq_zero_of_mem_succ_not_mem R _ _ hx hout]
  simp

/-- Applying `I-P` to the spectral candidate cancels the eigenvalue exactly.
The only missing algebraic step for identification with `diskGreen` is the
finite discrete-sine completeness relation on `[-R,R]²`. -/
theorem squareDirichletOperator_squareSpectralGreenCandidate
    (R : ℕ) (z x : Site) :
    squareDirichletOperator (squareSpectralGreenCandidate R z) x =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          squareSineMode R k l z * squareSineMode R k l x := by
  unfold squareSpectralGreenCandidate
  rw [squareDirichletOperator_const_mul,
    squareDirichletOperator_sum]
  simp_rw [squareDirichletOperator_sum,
    squareDirichletOperator_const_mul,
    squareDirichletOperator_squareSineMode]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hne : squareSineEigenvalue R k l ≠ 0 :=
    ne_of_gt (squareSineEigenvalue_pos R k l)
  field_simp

/-- Exact signed edge-gradient formula for the finite spectral candidate.
No triangle inequality is used: all cancellation between modes remains
visible in the double sum. -/
theorem squareSpectralGreenCandidate_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    squareSpectralGreenCandidate R z (x + directionStep e) -
        squareSpectralGreenCandidate R z x =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          (squareSineMode R k l z / squareSineEigenvalue R k l) *
            (squareSineMode R k l (x + directionStep e) -
              squareSineMode R k l x) := by
  unfold squareSpectralGreenCandidate
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Exact reduction of the Green-kernel identification to the remaining
finite discrete-sine completeness identity.  This theorem uses uniqueness of
the Dirichlet problem, not an assumed Harnack estimate. -/
theorem squareSpectralGreenCandidate_eq_diskGreen_toReal_of_completeness
    (R : ℕ) (z : Site)
    (hcomplete : ∀ x ∈ squareDisk R,
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
            squareSineMode R k l z * squareSineMode R k l x =
        if z = x then 1 else 0) :
    ∀ x ∈ squareDisk R,
      squareSpectralGreenCandidate R z x = (diskGreen R z x).toReal := by
  apply eq_on_squareDisk_of_dirichletOperator_eq_of_boundary_eq
  · intro x hx
    rw [squareDirichletOperator_squareSpectralGreenCandidate,
      hcomplete x hx, squareDirichletOperator_diskGreen R z x hx]
  · intro x hx hout
    rw [squareSpectralGreenCandidate_eq_zero_of_mem_succ_not_mem R z hx hout,
      diskGreen_toReal_eq_zero_of_target_not_mem hout]

end Erdos1166.KilledGreen
