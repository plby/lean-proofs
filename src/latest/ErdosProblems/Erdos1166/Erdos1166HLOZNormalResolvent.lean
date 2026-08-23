import ErdosProblems.Erdos1166.Erdos1166HLOZBoundarySine

namespace Erdos1166.KilledGreen
open scoped BigOperators

/-! # Exact one-dimensional normal resolvent of the square Green kernel

After separating the tangential Dirichlet sine mode, the remaining normal
frequency sum solves a one-dimensional massive Dirichlet equation.  This
file proves its exact hyperbolic-sine formula.  The proof does not assume a
matrix inverse: it lifts the one-dimensional equation back to the square and
uses the checked square maximum principle for uniqueness.

This removes one entire spectral summation while preserving the signed
tangential sum needed for the corner-robust Poisson-kernel gradient. -/

/-- The elementary multiple-angle bound in the precise form needed to
extract the common corner sine from every tangential mode.  Keeping the
factor `|sin x|`, instead of replacing it by one, is essential near either
corner of the square. -/
theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ (n : ℝ) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hphase : (((n + 1 : ℕ) : ℝ) * x) = (n : ℝ) * x + x := by
        push_cast
        ring
      rw [hphase, Real.sin_add]
      calc
        |Real.sin ((n : ℝ) * x) * Real.cos x +
            Real.cos ((n : ℝ) * x) * Real.sin x| ≤
            |Real.sin ((n : ℝ) * x) * Real.cos x| +
              |Real.cos ((n : ℝ) * x) * Real.sin x| := abs_add_le _ _
        _ = |Real.sin ((n : ℝ) * x)| * |Real.cos x| +
              |Real.cos ((n : ℝ) * x)| * |Real.sin x| := by
            rw [abs_mul, abs_mul]
        _ ≤ |Real.sin ((n : ℝ) * x)| + |Real.sin x| := by
            apply add_le_add
            · exact mul_le_of_le_one_right (abs_nonneg _)
                (Real.abs_cos_le_one _)
            · exact mul_le_of_le_one_left (abs_nonneg _)
                (Real.abs_cos_le_one _)
        _ ≤ (n : ℝ) * |Real.sin x| + |Real.sin x| := by
            gcongr
        _ = (((n + 1 : ℕ) : ℝ)) * |Real.sin x| := by
            push_cast
            ring

/-- Every tangential Dirichlet mode contains the same first-mode corner
factor.  This is the finite-square version of
`|sin (q t)| ≤ q |sin t|`. -/
theorem abs_squareSineCoordinate_le_mode_mul_first
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    |squareSineCoordinate R l a| ≤
      (((l : ℕ) + 1 : ℕ) : ℝ) *
        |squareSineCoordinate R ⟨0, by omega⟩ a| := by
  let t : ℝ := squareSineAngle R ⟨0, by omega⟩ * (a : ℝ) +
    squareSineAngle R ⟨0, by omega⟩ * (R + 1 : ℝ)
  have hphase :
      squareSineAngle R l * (a : ℝ) +
          squareSineAngle R l * (R + 1 : ℝ) =
        (((l : ℕ) + 1 : ℕ) : ℝ) * t := by
    dsimp only [t]
    unfold squareSineAngle
    push_cast
    ring
  unfold squareSineCoordinate
  rw [hphase]
  exact abs_sin_nat_mul_le ((l : ℕ) + 1) t

/-- The common first tangential mode is strictly positive at every interior
coordinate of the Dirichlet interval.  Consequently the corner factor can
later be cancelled without adding a boundary-atom positivity hypothesis. -/
theorem squareSineCoordinate_first_pos
    (R : ℕ) {a : ℤ} (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    0 < squareSineCoordinate R ⟨0, by omega⟩ a := by
  have hden : (0 : ℝ) < 2 * (R + 1 : ℝ) := by positivity
  have hnumLower : (1 : ℝ) ≤ (a : ℝ) + (R + 1 : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ a + ((R : ℤ) + 1) by omega)
  have hnumUpper : (a : ℝ) + (R + 1 : ℝ) < 2 * (R + 1 : ℝ) := by
    exact_mod_cast (show a + ((R : ℤ) + 1) < 2 * ((R : ℤ) + 1) by omega)
  have hargPos : 0 <
      Real.pi * ((a : ℝ) + (R + 1 : ℝ)) / (2 * (R + 1 : ℝ)) := by
    positivity
  have hargLt :
      Real.pi * ((a : ℝ) + (R + 1 : ℝ)) / (2 * (R + 1 : ℝ)) <
        Real.pi := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  unfold squareSineCoordinate squareSineAngle
  norm_num
  rw [show
      Real.pi / (2 * ((R : ℝ) + 1)) * (a : ℝ) +
          Real.pi / (2 * ((R : ℝ) + 1)) * ((R : ℝ) + 1) =
        Real.pi * ((a : ℝ) + ((R : ℝ) + 1)) /
          (2 * ((R : ℝ) + 1)) by ring]
  exact Real.sin_pos_of_pos_of_lt_pi hargPos hargLt

noncomputable def normalDecay (R : ℕ) (l : Fin (2 * R + 1)) : ℝ :=
  Real.arcosh (2 - Real.cos (squareSineAngle R l))

theorem normalDecay_pos (R : ℕ) (l : Fin (2 * R + 1)) :
    0 < normalDecay R l := by
  apply Real.arcosh_pos
  have := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
    (show squareSineAngle R l ∈ Set.Icc 0 Real.pi from
      ⟨(squareSineAngle_pos R l).le, (squareSineAngle_lt_pi R l).le⟩)
    (squareSineAngle_pos R l)
  have hc : Real.cos (squareSineAngle R l) < 1 := by simpa using this
  linarith

theorem one_add_sq_div_two_le_cosh {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hs : x / 2 ≤ Real.sinh (x / 2) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hs0 : 0 ≤ Real.sinh (x / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) hs0).2 hs
  rw [show x = 2 * (x / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
  nlinarith

theorem cosh_le_one_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cosh x ≤ 1 + x ^ 2 := by
  have hxsq : x ^ 2 ≤ 1 ^ 2 := (sq_le_sq₀ hx0 zero_le_one).2 hx1
  have hxSq0 : 0 ≤ x ^ 2 / 2 := by positivity
  have hxSqLt : x ^ 2 / 2 < 2 := by nlinarith
  calc
    Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
      Real.cosh_le_exp_half_sq x
    _ ≤ (2 + x ^ 2 / 2) / (2 - x ^ 2 / 2) :=
      Real.exp_le_two_add_div_two_sub hxSq0 hxSqLt
    _ ≤ 1 + x ^ 2 := by
      apply (div_le_iff₀ (by nlinarith : 0 < 2 - x ^ 2 / 2)).2
      nlinarith [sq_nonneg x]

/-- The elementary quadratic upper bound for `cosh` remains valid through
the slightly larger interval needed for the sharp decay comparison. -/
theorem cosh_le_one_add_sq_of_sq_le_two
    {x : ℝ} (hx0 : 0 ≤ x) (hxsq : x ^ 2 ≤ 2) :
    Real.cosh x ≤ 1 + x ^ 2 := by
  have hxSq0 : 0 ≤ x ^ 2 / 2 := by positivity
  have hxSqLt : x ^ 2 / 2 < 2 := by nlinarith
  calc
    Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
      Real.cosh_le_exp_half_sq x
    _ ≤ (2 + x ^ 2 / 2) / (2 - x ^ 2 / 2) :=
      Real.exp_le_two_add_div_two_sub hxSq0 hxSqLt
    _ ≤ 1 + x ^ 2 := by
      apply (div_le_iff₀ (by nlinarith : 0 < 2 - x ^ 2 / 2)).2
      nlinarith [sq_nonneg x]

theorem cosh_normalDecay (R : ℕ) (l : Fin (2 * R + 1)) :
    Real.cosh (normalDecay R l) =
      2 - Real.cos (squareSineAngle R l) := by
  apply Real.cosh_arcosh
  have hc := Real.cos_le_one (squareSineAngle R l)
  linarith

/-- The normal decay parameter is comparable to its tangential frequency,
with absolute constants.  These inequalities are the quantitative input for
subsequent resolvent summation estimates. -/
theorem normalDecay_le_squareSineAngle
    (R : ℕ) (l : Fin (2 * R + 1)) :
    normalDecay R l ≤ squareSineAngle R l := by
  have hcos :
      2 - Real.cos (squareSineAngle R l) ≤
        Real.cosh (squareSineAngle R l) := by
    have hc := Real.one_sub_sq_div_two_le_cos
      (x := squareSineAngle R l)
    have hh := one_add_sq_div_two_le_cosh
      (squareSineAngle_pos R l).le
    linarith
  have habs := Real.cosh_le_cosh.mp
    (show Real.cosh (normalDecay R l) ≤
        Real.cosh (squareSineAngle R l) by
      rw [cosh_normalDecay]
      exact hcos)
  simpa [abs_of_pos (normalDecay_pos R l),
    abs_of_pos (squareSineAngle_pos R l)] using habs

theorem squareSineAngle_div_four_le_normalDecay
    (R : ℕ) (l : Fin (2 * R + 1)) :
    squareSineAngle R l / 4 ≤ normalDecay R l := by
  let θ := squareSineAngle R l
  have hθ0 : 0 ≤ θ := (squareSineAngle_pos R l).le
  have hθ4 : θ / 4 ≤ 1 := by
    dsimp [θ]
    linarith [squareSineAngle_lt_pi R l, Real.pi_lt_four]
  have hcosh : Real.cosh (θ / 4) ≤ 1 + (θ / 4) ^ 2 :=
    cosh_le_one_add_sq (by positivity) hθ4
  have hpiSq : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcoef : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    nlinarith
  have hθabs : |θ| ≤ Real.pi := by
    rw [abs_of_nonneg hθ0]
    exact (squareSineAngle_lt_pi R l).le
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθabs
  have htarget : Real.cosh (θ / 4) ≤ 2 - Real.cos θ := by
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg θ)
    nlinarith [hcosh, hcos, hmul]
  have habs := Real.cosh_le_cosh.mp
    (show Real.cosh (θ / 4) ≤ Real.cosh (normalDecay R l) by
      rw [cosh_normalDecay]
      exact htarget)
  simpa [abs_of_nonneg (by positivity : 0 ≤ θ / 4),
    abs_of_pos (normalDecay_pos R l)] using habs

/-- Quantitative sharpening of the normal-mode decay.  The constant `2/5`
is still elementary but is strong enough for the remaining geometric mode
sum. -/
theorem two_fifths_mul_squareSineAngle_le_normalDecay
    (R : ℕ) (l : Fin (2 * R + 1)) :
    (2 / 5 : ℝ) * squareSineAngle R l ≤ normalDecay R l := by
  let θ := squareSineAngle R l
  have hθ0 : 0 ≤ θ := (squareSineAngle_pos R l).le
  have hθle : θ ≤ (3.15 : ℝ) :=
    (squareSineAngle_lt_pi R l).le.trans Real.pi_lt_d2.le
  have hθsq : θ ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
    (sq_le_sq₀ hθ0 (by norm_num)).2 hθle
  have hx0 : 0 ≤ (2 / 5 : ℝ) * θ := by positivity
  have hxsq : ((2 / 5 : ℝ) * θ) ^ 2 ≤ 2 := by
    nlinarith
  have hcosh :
      Real.cosh ((2 / 5 : ℝ) * θ) ≤
        1 + ((2 / 5 : ℝ) * θ) ^ 2 :=
    cosh_le_one_add_sq_of_sq_le_two hx0 hxsq
  have hpiSq : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
    (sq_le_sq₀ Real.pi_pos.le (by norm_num)).2 Real.pi_lt_d2.le
  have hcoef : (4 / 25 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    nlinarith
  have hθabs : |θ| ≤ Real.pi := by
    rw [abs_of_nonneg hθ0]
    exact (squareSineAngle_lt_pi R l).le
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθabs
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg θ)
  have htarget :
      Real.cosh ((2 / 5 : ℝ) * θ) ≤ 2 - Real.cos θ := by
    nlinarith [hcosh, hcos, hmul]
  have habs := Real.cosh_le_cosh.mp
    (show Real.cosh ((2 / 5 : ℝ) * θ) ≤
        Real.cosh (normalDecay R l) by
      rw [cosh_normalDecay]
      exact htarget)
  simpa [abs_of_nonneg hx0, abs_of_pos (normalDecay_pos R l)] using habs

theorem squareSineAngle_le_two_mul_mode_div
    (R : ℕ) (l : Fin (2 * R + 1)) :
    squareSineAngle R l ≤
      2 * (((l : ℕ) + 1 : ℕ) : ℝ) / (R + 1 : ℝ) := by
  unfold squareSineAngle
  rw [show (l : ℝ) + 1 = (((l : ℕ) + 1 : ℕ) : ℝ) by norm_num]
  have hL : 0 < (2 : ℝ) * (R + 1 : ℝ) := by positivity
  apply (div_le_iff₀ hL).2
  have hq : 0 ≤ (((l : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right Real.pi_le_four hq
  calc
    Real.pi * (((l : ℕ) + 1 : ℕ) : ℝ) ≤
        4 * (((l : ℕ) + 1 : ℕ) : ℝ) := hmul
    _ = (2 * (((l : ℕ) + 1 : ℕ) : ℝ) / (R + 1 : ℝ)) *
          (2 * (R + 1 : ℝ)) := by field_simp; ring

theorem one_sub_cos_half_eq_cosh_normalDecay_half
    (R : ℕ) (l : Fin (2 * R + 1)) :
    1 - Real.cos (squareSineAngle R l) / 2 =
      Real.cosh (normalDecay R l) / 2 := by
  rw [cosh_normalDecay]
  ring

noncomputable def normalDirichletOperator
    (R : ℕ) (l : Fin (2 * R + 1)) (f : ℤ → ℝ) (a : ℤ) : ℝ :=
  (1 - Real.cos (squareSineAngle R l) / 2) * f a -
    (1 / 4 : ℝ) * (f (a + 1) + f (a - 1))

theorem normalDirichletOperator_squareCoordinateSine
    (R : ℕ) (k l : Fin (2 * R + 1)) (a : ℤ) :
    normalDirichletOperator R l (squareSineCoordinate R k) a =
      squareSineEigenvalue R k l * squareSineCoordinate R k a := by
  unfold normalDirichletOperator squareSineCoordinate squareSineEigenvalue
  have hp : squareSineAngle R k * ((a + 1 : ℤ) : ℝ) +
      squareSineAngle R k * (R + 1 : ℝ) =
      (squareSineAngle R k * (a : ℝ) +
        squareSineAngle R k * (R + 1 : ℝ)) + squareSineAngle R k := by
    push_cast
    ring
  have hm : squareSineAngle R k * ((a - 1 : ℤ) : ℝ) +
      squareSineAngle R k * (R + 1 : ℝ) =
      (squareSineAngle R k * (a : ℝ) +
        squareSineAngle R k * (R + 1 : ℝ)) - squareSineAngle R k := by
    push_cast
    ring
  rw [hp, hm]
  let A := squareSineAngle R k * (a : ℝ) +
    squareSineAngle R k * (R + 1 : ℝ)
  let t := squareSineAngle R k
  have hs : Real.sin (A + t) + Real.sin (A - t) =
      2 * Real.sin A * Real.cos t := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  change (1 - Real.cos (squareSineAngle R l) / 2) * Real.sin A -
      1 / 4 * (Real.sin (A + t) + Real.sin (A - t)) = _
  rw [hs]
  dsimp only [A, t]
  ring

theorem normalDirichletOperator_sum
    {ι : Type*} [Fintype ι] (R : ℕ) (l : Fin (2 * R + 1))
    (F : ι → ℤ → ℝ) (a : ℤ) :
    normalDirichletOperator R l (fun b ↦ ∑ i, F i b) a =
      ∑ i, normalDirichletOperator R l (F i) a := by
  unfold normalDirichletOperator
  rw [Finset.mul_sum]
  rw [show (∑ i, F i (a + 1)) + ∑ i, F i (a - 1) =
      ∑ i, (F i (a + 1) + F i (a - 1)) by
    rw [Finset.sum_add_distrib]]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem normalDirichletOperator_rightBoundaryNormalResolvent
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    normalDirichletOperator R l
        (rightBoundaryNormalResolvent R l) a =
      ∑ k : Fin (2 * R + 1),
        -((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) *
          squareSineCoordinate R k a := by
  unfold rightBoundaryNormalResolvent
  rw [normalDirichletOperator_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (fun b ↦
      (-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
        squareSineEigenvalue R k l) * squareSineCoordinate R k b) =
      fun b ↦ (-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
        squareSineEigenvalue R k l) * squareSineCoordinate R k b by rfl]
  unfold normalDirichletOperator
  rw [show
      (1 - Real.cos (squareSineAngle R l) / 2) *
          ((-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
              squareSineEigenvalue R k l) * squareSineCoordinate R k a) -
        1 / 4 *
          ((-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
                squareSineEigenvalue R k l) * squareSineCoordinate R k (a + 1) +
            (-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
                squareSineEigenvalue R k l) * squareSineCoordinate R k (a - 1)) =
        (-((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) /
          squareSineEigenvalue R k l) *
          normalDirichletOperator R l (squareSineCoordinate R k) a by
      unfold normalDirichletOperator; ring]
  rw [normalDirichletOperator_squareCoordinateSine]
  field_simp [ne_of_gt (squareSineEigenvalue_pos R k l)]

theorem squareSineCoordinateTest_right
    (R : ℕ) (k : Fin (2 * R + 1)) :
    squareSineCoordinate R k (R : ℤ) =
      -((-1 : ℝ) ^ ((k : ℕ) + 1) * Real.sin (squareSineAngle R k)) := by
  unfold squareSineCoordinate
  norm_num only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hphase :
      squareSineAngle R k * (R : ℝ) +
          squareSineAngle R k * (R + 1 : ℝ) =
        (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi - squareSineAngle R k := by
    unfold squareSineAngle
    have hpos : (0 : ℝ) < (R + 1 : ℕ) := by positivity
    field_simp
    norm_num
    ring
  rw [hphase, Real.sin_nat_mul_pi_sub]

theorem normalDirichletOperator_rightBoundaryNormalResolvent_eq_indicator
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    normalDirichletOperator R l
        (rightBoundaryNormalResolvent R l) a =
      (R + 1 : ℝ) * (if a = (R : ℤ) then 1 else 0) := by
  rw [normalDirichletOperator_rightBoundaryNormalResolvent]
  simp_rw [← squareSineCoordinateTest_right R]
  change (∑ k : Fin (2 * R + 1),
      squareCoordinateSine R k (R : ℤ) * squareCoordinateSine R k a) =
    (R + 1 : ℝ) * (if a = (R : ℤ) then 1 else 0)
  have horth := normalized_squareCoordinateSineInner
    (R := R) (a := (R : ℤ)) (b := a)
    (by omega) (by omega) hal hau
  have hL : (0 : ℝ) < R + 1 := by positivity
  have hscale : 2 / (2 * (R + 1 : ℝ)) = 1 / (R + 1 : ℝ) := by
    field_simp
  rw [hscale] at horth
  by_cases ha : a = (R : ℤ)
  · subst a
    simp only [ite_true] at horth ⊢
    have hdiv : (∑ k : Fin (2 * R + 1),
        squareCoordinateSine R k (R : ℤ) *
          squareCoordinateSine R k (R : ℤ)) / (R + 1 : ℝ) = 1 := by
      simpa [div_eq_mul_inv, mul_comm] using horth
    simpa [mul_comm] using (div_eq_iff hL.ne').mp hdiv
  · simp only [if_neg ha]
    have hne : (R : ℤ) ≠ a := Ne.symm ha
    rw [if_neg hne] at horth
    have hdiv : (∑ k : Fin (2 * R + 1),
        squareCoordinateSine R k (R : ℤ) * squareCoordinateSine R k a) /
          (R + 1 : ℝ) = 0 := by
      simpa [div_eq_mul_inv, mul_comm] using horth
    rcases (div_eq_zero_iff).mp hdiv with hzero | hzero
    · simpa using hzero
    · exact (hL.ne' hzero).elim

noncomputable def rightNormalClosed
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  if -(R : ℤ) ≤ a ∧ a ≤ (R : ℤ) then
    (4 * (R + 1 : ℝ)) *
      Real.sinh (normalDecay R l *
        ((a : ℝ) + (R + 1 : ℝ))) /
      Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))
  else 0

theorem sinh_add_sub_two_mul_cosh (x t : ℝ) :
    Real.sinh (x + t) + Real.sinh (x - t) =
      2 * Real.cosh t * Real.sinh x := by
  rw [Real.sinh_add, Real.sinh_sub]
  ring

theorem sinh_add_sub_sub_eq_two_mul_cosh_mul_sinh (x t : ℝ) :
    Real.sinh (x + t) - Real.sinh (x - t) =
      2 * Real.cosh x * Real.sinh t := by
  rw [Real.sinh_add, Real.sinh_sub]
  ring

theorem sinh_eq_exp_mul_one_sub_exp_neg_two (x : ℝ) :
    Real.sinh x = Real.exp x * (1 - Real.exp (-2 * x)) / 2 := by
  rw [Real.sinh_eq]
  have hfactor : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  ring

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have hmono : Real.exp (-x) ≤ Real.exp x := by
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

theorem sinh_le_mul_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.exp x := by
  rw [sinh_eq_exp_mul_one_sub_exp_neg_two]
  have hlinear : 1 - Real.exp (-2 * x) ≤ 2 * x := by
    linarith [Real.add_one_le_exp (-2 * x)]
  have hexp0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  nlinarith [mul_le_mul_of_nonneg_left hlinear hexp0]

/-- Exponential form of the finite-interval normal resolvent.  It exposes
the geometric decay in the distance from the selected face while retaining
the two exact reflection factors. -/
theorem sinh_ratio_eq_exp_decay
    {γ j L : ℝ} (hγ : 0 < γ) (hL : 0 < L) :
    Real.sinh (γ * j) / Real.sinh (γ * L) =
      Real.exp (-γ * (L - j)) *
        ((1 - Real.exp (-2 * γ * j)) /
          (1 - Real.exp (-2 * γ * L))) := by
  have hsinh : Real.sinh (γ * L) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    positivity
  have hexpL : Real.exp (γ * L) ≠ 0 := Real.exp_ne_zero _
  have hone : 1 - Real.exp (-2 * γ * L) ≠ 0 := by
    have hneg : -2 * γ * L < 0 := by nlinarith
    have := Real.exp_lt_one_iff.mpr hneg
    linarith
  have hfactor (u : ℝ) :
      Real.exp u - Real.exp (-u) =
        Real.exp u * (1 - Real.exp (-2 * u)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  have hexp :
      Real.exp (-γ * (L - j)) =
        Real.exp (γ * j) / Real.exp (γ * L) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, Real.sinh_eq]
  rw [hfactor, hfactor, hexp]
  field_simp [hone, Real.exp_ne_zero]

theorem exp_neg_three_halves_lt_one_half :
    Real.exp (-(3 / 2 : ℝ)) < 1 / 2 := by
  have he : (2 : ℝ) < Real.exp (3 / 2 : ℝ) := by
    have := Real.add_one_le_exp (3 / 2 : ℝ)
    norm_num at this ⊢
    linarith
  rw [Real.exp_neg]
  simpa [one_div] using
    ((inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).2 he)

theorem exp_neg_one_fourth_le_four_fifths :
    Real.exp (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
  have h : (5 / 4 : ℝ) ≤ Real.exp (1 / 4 : ℝ) := by
    nlinarith [Real.add_one_le_exp (1 / 4 : ℝ)]
  rw [Real.exp_neg]
  simpa using ((inv_le_inv₀ (Real.exp_pos _) (by norm_num)).2 h)

/-- Exact finite domination by the differentiated geometric series at
ratio `4/5`. -/
theorem sum_fin_succ_mul_four_fifths_pow_le (n : ℕ) :
    (∑ l : Fin n, (((l : ℕ) + 1 : ℕ) : ℝ) *
      (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) ≤ 20 := by
  let a : ℝ := 4 / 5
  have ha : ‖a‖ < 1 := by norm_num [a, abs_of_nonneg]
  have hs0 : Summable (fun i : ℕ =>
      (((i + 1).choose 1 : ℕ) : ℝ) * a ^ i) :=
    summable_choose_mul_geometric_of_norm_lt_one 1 ha
  have hs : Summable (fun i : ℕ =>
      a * ((((i + 1).choose 1 : ℕ) : ℝ) * a ^ i)) := hs0.mul_left a
  have hpartial := hs.sum_le_tsum (Finset.range n) (by
    intro i hi
    positivity)
  have htsum : (∑' i : ℕ,
      a * ((((i + 1).choose 1 : ℕ) : ℝ) * a ^ i)) = 20 := by
    rw [tsum_mul_left]
    rw [tsum_choose_mul_geometric_of_norm_lt_one 1 ha]
    norm_num [a]
  rw [htsum] at hpartial
  calc
    (∑ l : Fin n, (((l : ℕ) + 1 : ℕ) : ℝ) *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) =
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ) *
          (4 / 5 : ℝ) ^ (i + 1)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => (((i + 1 : ℕ) : ℝ) * (4 / 5 : ℝ) ^ (i + 1))) n
    _ = ∑ i ∈ Finset.range n,
        a * ((((i + 1).choose 1 : ℕ) : ℝ) * a ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.choose_one_right]
      dsimp [a]
      push_cast
      rw [pow_succ']
      ring
    _ ≤ 20 := hpartial

/-- Exact finite domination by the second differentiated geometric series
at ratio `4/5`. -/
theorem sum_fin_succ_sq_mul_four_fifths_pow_le (n : ℕ) :
    (∑ l : Fin n, (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
      (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) ≤ 200 := by
  let a : ℝ := 4 / 5
  have ha : ‖a‖ < 1 := by norm_num [a, abs_of_nonneg]
  have hs0 : Summable (fun i : ℕ =>
      (((i + 2).choose 2 : ℕ) : ℝ) * a ^ i) :=
    summable_choose_mul_geometric_of_norm_lt_one 2 ha
  have hs : Summable (fun i : ℕ =>
      (2 * a) * ((((i + 2).choose 2 : ℕ) : ℝ) * a ^ i)) :=
    hs0.mul_left (2 * a)
  have hpartial := hs.sum_le_tsum (Finset.range n) (by
    intro i hi
    positivity)
  have htsum : (∑' i : ℕ,
      (2 * a) * ((((i + 2).choose 2 : ℕ) : ℝ) * a ^ i)) = 200 := by
    rw [tsum_mul_left]
    rw [tsum_choose_mul_geometric_of_norm_lt_one 2 ha]
    norm_num [a]
  rw [htsum] at hpartial
  calc
    (∑ l : Fin n, (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) =
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ (i + 1)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => (((i + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ (i + 1))) n
    _ ≤ ∑ i ∈ Finset.range n,
        (2 * a) * ((((i + 2).choose 2 : ℕ) : ℝ) * a ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hchoose : (2 : ℝ) * (((i + 2).choose 2 : ℕ) : ℝ) =
          ((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ) := by
        rw [Nat.cast_choose_two]
        norm_num
        push_cast
        ring
      have hsq : ((i + 1 : ℕ) : ℝ) ^ 2 ≤
          (2 : ℝ) * (((i + 2).choose 2 : ℕ) : ℝ) := by
        rw [hchoose]
        norm_num
        nlinarith
      have hp : 0 ≤ (4 / 5 : ℝ) ^ i := by positivity
      have hmul := mul_le_mul_of_nonneg_right hsq hp
      dsimp [a]
      calc
        ((i + 1 : ℕ) : ℝ) ^ 2 *
            (4 / 5 : ℝ) ^ (i + 1) =
          (4 / 5 : ℝ) *
            (((i + 1 : ℕ) : ℝ) ^ 2 * (4 / 5 : ℝ) ^ i) := by
              rw [pow_succ']
              ring
        _ ≤ (4 / 5 : ℝ) *
            ((2 * (((i + 2).choose 2 : ℕ) : ℝ)) *
              (4 / 5 : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = (2 * (4 / 5 : ℝ)) *
            ((((i + 2).choose 2 : ℕ) : ℝ) * (4 / 5 : ℝ) ^ i) := by ring
    _ ≤ 200 := hpartial

theorem one_half_lt_one_sub_exp_neg
    {x : ℝ} (hx : (3 / 2 : ℝ) ≤ x) :
    1 / 2 < 1 - Real.exp (-x) := by
  have hmono : Real.exp (-x) ≤ Real.exp (-(3 / 2 : ℝ)) := by
    rw [Real.exp_le_exp]
    linarith
  linarith [exp_neg_three_halves_lt_one_half]

/-- Even the lowest tangential mode has a uniformly nondegenerate
finite-interval reflection denominator.  This is the point at which the
mode lower bound `γ_l ≥ θ_l / 4` is used; no lower bound on an individual
boundary exit atom is involved. -/
theorem three_halves_lt_four_mul_normalDecay_mul
    (R : ℕ) (l : Fin (2 * R + 1)) :
    (3 / 2 : ℝ) < 4 * normalDecay R l * (R + 1 : ℝ) := by
  have hdec := squareSineAngle_div_four_le_normalDecay R l
  have hmul := mul_le_mul_of_nonneg_right hdec
    (show 0 ≤ 4 * (R + 1 : ℝ) by positivity)
  have hmode : (1 : ℝ) ≤ (((l : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (l : ℕ) + 1 by omega)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hangle : (3 / 2 : ℝ) <
      (squareSineAngle R l / 4) * (4 * (R + 1 : ℝ)) := by
    unfold squareSineAngle
    have hL : (0 : ℝ) < R + 1 := by positivity
    have hcancel :
        (Real.pi * (((l : ℕ) + 1 : ℕ) : ℝ) /
              (2 * ((R : ℝ) + 1)) / 4) *
            (4 * ((R : ℝ) + 1)) =
          Real.pi * (((l : ℕ) + 1 : ℕ) : ℝ) / 2 := by
      field_simp [ne_of_gt hL]
    have hlcast : ((l : ℕ) : ℝ) + 1 = (((l : ℕ) + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hlcast, hcancel]
    nlinarith
  nlinarith

theorem one_half_lt_normalDecay_reflection_denominator
    (R : ℕ) (l : Fin (2 * R + 1)) :
    (1 / 2 : ℝ) <
      1 - Real.exp (-4 * normalDecay R l * (R + 1 : ℝ)) := by
  convert one_half_lt_one_sub_exp_neg
      (three_halves_lt_four_mul_normalDecay_mul R l).le using 1 <;>
    ring_nf

theorem exp_two_normalDecay_mul_le_four_mul_sinh
    (R : ℕ) (l : Fin (2 * R + 1)) :
    Real.exp (2 * normalDecay R l * (R + 1 : ℝ)) ≤
      4 * Real.sinh (2 * normalDecay R l * (R + 1 : ℝ)) := by
  rw [sinh_eq_exp_mul_one_sub_exp_neg_two]
  have hreflect := one_half_lt_normalDecay_reflection_denominator R l
  have hexp0 : 0 ≤ Real.exp (2 * normalDecay R l * (R + 1 : ℝ)) :=
    (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hreflect.le hexp0
  rw [show -2 * (2 * normalDecay R l * (R + 1 : ℝ)) =
      -4 * normalDecay R l * (R + 1 : ℝ) by ring]
  nlinarith

theorem rightNormalClosed_left_boundary
    (R : ℕ) (l : Fin (2 * R + 1)) :
    rightNormalClosed R l (-(R : ℤ) - 1) = 0 := by
  unfold rightNormalClosed
  simp

theorem rightNormalClosed_right_boundary
    (R : ℕ) (l : Fin (2 * R + 1)) :
    rightNormalClosed R l ((R : ℤ) + 1) = 0 := by
  unfold rightNormalClosed
  simp

theorem normalDirichletOperator_rightNormalClosed_eq_indicator
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    normalDirichletOperator R l (rightNormalClosed R l) a =
      (R + 1 : ℝ) * (if a = (R : ℤ) then 1 else 0) := by
  have hγ : 0 < normalDecay R l := normalDecay_pos R l
  have hdenpos : 0 < Real.sinh
      (normalDecay R l * (2 * (R + 1 : ℝ))) := by
    rw [Real.sinh_pos_iff]
    positivity
  have hself : rightNormalClosed R l a =
      (4 * (R + 1 : ℝ)) *
        Real.sinh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ))) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
    simp [rightNormalClosed, hal, hau]
  by_cases haR : a = (R : ℤ)
  · subst a
    have hleft' : (R : ℤ) - 1 ≤ (R : ℤ) := by omega
    have hprev : rightNormalClosed R l ((R : ℤ) - 1) =
        (4 * (R + 1 : ℝ)) *
          Real.sinh (normalDecay R l *
            ((((R : ℤ) - 1 : ℤ) : ℝ) + (R + 1 : ℝ))) /
          Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
      by_cases hR : R = 0
      · subst R
        simp [rightNormalClosed]
      · have hleft : -(R : ℤ) ≤ (R : ℤ) - 1 := by omega
        simp [rightNormalClosed, hleft, hleft']
    unfold normalDirichletOperator
    rw [rightNormalClosed_right_boundary, hprev, hself]
    rw [one_sub_cos_half_eq_cosh_normalDecay_half]
    have hrec :
        2 * Real.cosh (normalDecay R l) *
              Real.sinh (normalDecay R l *
                ((R : ℝ) + (R + 1 : ℝ))) -
            Real.sinh (normalDecay R l *
              (((R : ℝ) - 1) + (R + 1 : ℝ))) =
          Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
      have h := sinh_add_sub_two_mul_cosh
        (normalDecay R l * ((R : ℝ) + (R + 1 : ℝ)))
        (normalDecay R l)
      rw [show normalDecay R l * ((R : ℝ) + (R + 1 : ℝ)) +
              normalDecay R l =
            normalDecay R l * (2 * (R + 1 : ℝ)) by ring,
          show normalDecay R l * ((R : ℝ) + (R + 1 : ℝ)) -
              normalDecay R l =
            normalDecay R l * (((R : ℝ) - 1) + (R + 1 : ℝ)) by ring]
        at h
      linarith
    field_simp [hdenpos.ne']
    push_cast
    ring_nf at hrec ⊢
    linear_combination 8 * ((R : ℝ) + 1) * hrec
  · have halt : a < (R : ℤ) := lt_of_le_of_ne hau haR
    have hsucc_lo : -(R : ℤ) ≤ a + 1 := by omega
    have hsucc_hi : a + 1 ≤ (R : ℤ) := by omega
    have hprev_hi : a - 1 ≤ (R : ℤ) := by omega
    by_cases hleft : a = -(R : ℤ)
    · subst a
      have hsucc :
          rightNormalClosed R l (-(R : ℤ) + 1) =
            (4 * (R + 1 : ℝ)) *
              Real.sinh (normalDecay R l *
                ((((-(R : ℤ) + 1 : ℤ) : ℝ) + (R + 1 : ℝ)))) /
              Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
        simp [rightNormalClosed]
        omega
      unfold normalDirichletOperator
      rw [rightNormalClosed_left_boundary, hsucc, hself]
      simp only [if_neg haR, mul_zero]
      rw [one_sub_cos_half_eq_cosh_normalDecay_half]
      field_simp [hdenpos.ne']
      push_cast
      rw [show normalDecay R l * ((-(R : ℝ)) + (R + 1 : ℝ)) =
          normalDecay R l by ring]
      rw [show normalDecay R l *
          (((-(R : ℝ)) + 1) + (R + 1 : ℝ)) =
          normalDecay R l + normalDecay R l by ring]
      rw [Real.sinh_add]
      ring
    · have hprev_lo : -(R : ℤ) ≤ a - 1 := by omega
      have hsucc : rightNormalClosed R l (a + 1) =
          (4 * (R + 1 : ℝ)) *
            Real.sinh (normalDecay R l *
              (((a + 1 : ℤ) : ℝ) + (R + 1 : ℝ))) /
            Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
        simp [rightNormalClosed, hsucc_lo, hsucc_hi]
      have hprev : rightNormalClosed R l (a - 1) =
          (4 * (R + 1 : ℝ)) *
            Real.sinh (normalDecay R l *
              (((a - 1 : ℤ) : ℝ) + (R + 1 : ℝ))) /
            Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
        simp [rightNormalClosed, hprev_lo, hprev_hi]
      unfold normalDirichletOperator
      rw [hself, hsucc, hprev]
      simp only [if_neg haR, mul_zero]
      rw [one_sub_cos_half_eq_cosh_normalDecay_half]
      field_simp [hdenpos.ne']
      push_cast
      rw [show normalDecay R l *
            (((a : ℝ) + 1) + (R + 1 : ℝ)) =
          normalDecay R l * ((a : ℝ) + (R + 1 : ℝ)) +
            normalDecay R l by ring]
      rw [show normalDecay R l *
            (((a : ℝ) - 1) + (R + 1 : ℝ)) =
          normalDecay R l * ((a : ℝ) + (R + 1 : ℝ)) -
            normalDecay R l by ring]
      rw [sinh_add_sub_two_mul_cosh]
      ring

noncomputable def normalLift
    (R : ℕ) (l : Fin (2 * R + 1)) (f : ℤ → ℝ) (x : Site) : ℝ :=
  f x.1 * squareSineCoordinate R l x.2

theorem squareDirichletOperator_normalLift
    (R : ℕ) (l : Fin (2 * R + 1)) (f : ℤ → ℝ) (x : Site) :
    squareDirichletOperator (normalLift R l f) x =
      normalDirichletOperator R l f x.1 *
        squareSineCoordinate R l x.2 := by
  unfold squareDirichletOperator normalLift
  rw [Fin.sum_univ_four]
  norm_num [directionStep]
  unfold normalDirichletOperator squareSineCoordinate
  have hp : squareSineAngle R l * (((x.2 : ℤ) + 1 : ℤ) : ℝ) +
      squareSineAngle R l * (R + 1 : ℝ) =
      (squareSineAngle R l * (x.2 : ℝ) +
        squareSineAngle R l * (R + 1 : ℝ)) + squareSineAngle R l := by
    push_cast
    ring
  have hm : squareSineAngle R l * (((x.2 : ℤ) + -1 : ℤ) : ℝ) +
      squareSineAngle R l * (R + 1 : ℝ) =
      (squareSineAngle R l * (x.2 : ℝ) +
        squareSineAngle R l * (R + 1 : ℝ)) - squareSineAngle R l := by
    push_cast
    ring
  rw [hp, hm]
  have hs : Real.sin
        ((squareSineAngle R l * (x.2 : ℝ) +
            squareSineAngle R l * (R + 1 : ℝ)) +
          squareSineAngle R l) +
      Real.sin
        ((squareSineAngle R l * (x.2 : ℝ) +
            squareSineAngle R l * (R + 1 : ℝ)) -
          squareSineAngle R l) =
      2 * Real.sin
          (squareSineAngle R l * (x.2 : ℝ) +
            squareSineAngle R l * (R + 1 : ℝ)) *
        Real.cos (squareSineAngle R l) := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  rw [show
      f (x.1 + 1) *
            Real.sin (squareSineAngle R l * (x.2 : ℝ) +
              squareSineAngle R l * (R + 1 : ℝ)) +
          f (x.1 + -1) *
            Real.sin (squareSineAngle R l * (x.2 : ℝ) +
              squareSineAngle R l * (R + 1 : ℝ)) +
        f x.1 * Real.sin
            ((squareSineAngle R l * (x.2 : ℝ) +
                squareSineAngle R l * (R + 1 : ℝ)) +
              squareSineAngle R l) +
        f x.1 * Real.sin
            ((squareSineAngle R l * (x.2 : ℝ) +
                squareSineAngle R l * (R + 1 : ℝ)) -
              squareSineAngle R l) =
      (f (x.1 + 1) + f (x.1 + -1)) *
          Real.sin (squareSineAngle R l * (x.2 : ℝ) +
            squareSineAngle R l * (R + 1 : ℝ)) +
        f x.1 *
          (Real.sin
              ((squareSineAngle R l * (x.2 : ℝ) +
                  squareSineAngle R l * (R + 1 : ℝ)) +
                squareSineAngle R l) +
            Real.sin
              ((squareSineAngle R l * (x.2 : ℝ) +
                  squareSineAngle R l * (R + 1 : ℝ)) -
                squareSineAngle R l)) by ring]
  rw [hs]
  rw [show x.1 - 1 = x.1 + -1 by ring]
  ring

theorem squareSineCoordinate_left_outer_eq_zero
    (R : ℕ) (l : Fin (2 * R + 1)) :
    squareSineCoordinate R l (-(R : ℤ) - 1) = 0 := by
  unfold squareSineCoordinate
  convert Real.sin_zero using 2
  push_cast
  ring

theorem squareSineCoordinate_right_outer_eq_zero
    (R : ℕ) (l : Fin (2 * R + 1)) :
    squareSineCoordinate R l ((R : ℤ) + 1) = 0 := by
  unfold squareSineCoordinate
  push_cast
  rw [show squareSineAngle R l * ((R : ℝ) + 1) +
      squareSineAngle R l * (R + 1 : ℝ) =
      (((l : ℕ) + 1 : ℕ) : ℝ) * Real.pi by
    unfold squareSineAngle
    have hpos : (0 : ℝ) < R + 1 := by positivity
    field_simp
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring]
  exact Real.sin_nat_mul_pi ((l : ℕ) + 1)

theorem eq_on_integerSquare_of_normalDirichletOperator_eq_of_boundary_eq
    {R : ℕ} {l : Fin (2 * R + 1)} {f g : ℤ → ℝ}
    (hop : ∀ a : ℤ, -(R : ℤ) ≤ a → a ≤ (R : ℤ) →
      normalDirichletOperator R l f a =
        normalDirichletOperator R l g a)
    (hleft : f (-(R : ℤ) - 1) = g (-(R : ℤ) - 1))
    (hright : f ((R : ℤ) + 1) = g ((R : ℤ) + 1)) :
    ∀ a : ℤ, -(R : ℤ) ≤ a → a ≤ (R : ℤ) → f a = g a := by
  have hlift :
      ∀ x ∈ squareDisk R,
        normalLift R l f x = normalLift R l g x := by
    apply eq_on_squareDisk_of_dirichletOperator_eq_of_boundary_eq
    · intro x hx
      rw [squareDirichletOperator_normalLift,
        squareDirichletOperator_normalLift]
      rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
      rcases Finset.mem_Icc.mp hx1 with ⟨hxl, hxu⟩
      rw [hop x.1 hxl hxu]
    · intro x hx hout
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
      unfold normalLift
      rcases hedge with ha | ha | hb | hb
      · have ha' : a = -(R : ℤ) - 1 := by omega
        rw [ha', hleft]
      · have ha' : a = (R : ℤ) + 1 := by omega
        rw [ha', hright]
      · have hb' : b = -(R : ℤ) - 1 := by omega
        rw [hb', squareSineCoordinate_left_outer_eq_zero]
        ring
      · have hb' : b = (R : ℤ) + 1 := by omega
        rw [hb', squareSineCoordinate_right_outer_eq_zero]
        ring
  intro a hal hau
  have ha := hlift (a, -(R : ℤ))
  have hmem : (a, -(R : ℤ)) ∈ squareDisk R := by
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> omega
  specialize ha hmem
  unfold normalLift at ha
  have hcoord :
      squareSineCoordinate R l (-(R : ℤ)) =
        Real.sin (squareSineAngle R l) := by
    unfold squareSineCoordinate
    congr 1
    push_cast
    ring
  rw [hcoord] at ha
  exact (mul_right_cancel₀
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (squareSineAngle_pos R l) (squareSineAngle_lt_pi R l))) ha)

theorem rightBoundaryNormalResolvent_left_outer_eq_zero
    (R : ℕ) (l : Fin (2 * R + 1)) :
    rightBoundaryNormalResolvent R l (-(R : ℤ) - 1) = 0 := by
  unfold rightBoundaryNormalResolvent
  simp_rw [squareSineCoordinate_left_outer_eq_zero]
  simp

theorem rightBoundaryNormalResolvent_right_outer_eq_zero
    (R : ℕ) (l : Fin (2 * R + 1)) :
    rightBoundaryNormalResolvent R l ((R : ℤ) + 1) = 0 := by
  unfold rightBoundaryNormalResolvent
  simp_rw [squareSineCoordinate_right_outer_eq_zero]
  simp

theorem rightBoundaryNormalResolvent_eq_rightNormalClosed
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l a = rightNormalClosed R l a := by
  apply eq_on_integerSquare_of_normalDirichletOperator_eq_of_boundary_eq
    (R := R) (l := l)
  · intro b hbl hbu
    rw [normalDirichletOperator_rightBoundaryNormalResolvent_eq_indicator
        R l hbl hbu,
      normalDirichletOperator_rightNormalClosed_eq_indicator
        R l hbl hbu]
  · rw [rightBoundaryNormalResolvent_left_outer_eq_zero,
      rightNormalClosed_left_boundary]
  · rw [rightBoundaryNormalResolvent_right_outer_eq_zero,
      rightNormalClosed_right_boundary]
  · exact hal
  · exact hau

theorem rightBoundaryNormalResolvent_eq_sinh_ratio
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l a =
      (4 * (R + 1 : ℝ)) *
        Real.sinh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ))) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  rw [rightBoundaryNormalResolvent_eq_rightNormalClosed R l hal hau]
  simp [rightNormalClosed, hal, hau]

theorem rightBoundaryNormalResolvent_eq_exp_decay
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l a =
      (4 * (R + 1 : ℝ)) *
        (Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (a : ℝ))) *
          ((1 - Real.exp (-2 * normalDecay R l *
              ((a : ℝ) + (R + 1 : ℝ)))) /
            (1 - Real.exp (-4 * normalDecay R l *
              (R + 1 : ℝ))))) := by
  rw [rightBoundaryNormalResolvent_eq_sinh_ratio R l hal hau]
  rw [show
      (4 * (R + 1 : ℝ)) *
          Real.sinh (normalDecay R l *
            ((a : ℝ) + (R + 1 : ℝ))) /
          Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) =
        (4 * (R + 1 : ℝ)) *
          (Real.sinh (normalDecay R l *
              ((a : ℝ) + (R + 1 : ℝ))) /
            Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))) by ring]
  rw [sinh_ratio_eq_exp_decay
    (normalDecay_pos R l) (by positivity : (0 : ℝ) < 2 * (R + 1 : ℝ))]
  congr 2
  · congr 1
    ring
  · congr 1
    · congr 1
      ring

/-- Uniform geometric envelope for a right-face normal mode.  The
reflection quotient is bounded by `2`, uniformly down to the lowest mode;
the exact tangential sum is deliberately left untouched. -/
theorem rightBoundaryNormalResolvent_le_exp_decay
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l a ≤
      (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ))) := by
  rw [rightBoundaryNormalResolvent_eq_exp_decay R l hal hau]
  let numerator : ℝ :=
    1 - Real.exp (-2 * normalDecay R l *
      ((a : ℝ) + (R + 1 : ℝ)))
  let denominator : ℝ :=
    1 - Real.exp (-4 * normalDecay R l * (R + 1 : ℝ))
  have hnum1 : numerator ≤ 1 := by
    dsimp [numerator]
    linarith [Real.exp_pos
      (-2 * normalDecay R l * ((a : ℝ) + (R + 1 : ℝ)))]
  have hdenhalf : (1 / 2 : ℝ) < denominator := by
    simpa only [denominator] using
      one_half_lt_normalDecay_reflection_denominator R l
  have hquot : numerator / denominator ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < denominator)).2
    nlinarith
  have hexp0 : 0 ≤ Real.exp
      (-normalDecay R l * ((R + 1 : ℝ) - (a : ℝ))) :=
    (Real.exp_pos _).le
  dsimp only [numerator, denominator] at hquot
  calc
    (4 * (R + 1 : ℝ)) *
          (Real.exp (-normalDecay R l *
              ((R + 1 : ℝ) - (a : ℝ))) *
            ((1 - Real.exp (-2 * normalDecay R l *
                ((a : ℝ) + (R + 1 : ℝ)))) /
              (1 - Real.exp (-4 * normalDecay R l *
                (R + 1 : ℝ))))) =
        ((4 * (R + 1 : ℝ)) *
          Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (a : ℝ)))) *
          ((1 - Real.exp (-2 * normalDecay R l *
              ((a : ℝ) + (R + 1 : ℝ)))) /
            (1 - Real.exp (-4 * normalDecay R l *
              (R + 1 : ℝ)))) := by ring
    _ ≤ ((4 * (R + 1 : ℝ)) *
          Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (a : ℝ)))) * 2 :=
      mul_le_mul_of_nonneg_left hquot (mul_nonneg (by positivity) hexp0)
    _ = (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ))) := by ring

/-- Exact adjacent normal-coordinate increment on a right-face mode. -/
theorem rightBoundaryNormalResolvent_add_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a + 1 ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l (a + 1) -
        rightBoundaryNormalResolvent R l a =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  rw [rightBoundaryNormalResolvent_eq_sinh_ratio R l (by omega) hau,
    rightBoundaryNormalResolvent_eq_sinh_ratio R l hal (by omega)]
  have hplus : normalDecay R l *
        ((((a + 1 : ℤ) : ℝ)) + (R + 1 : ℝ)) =
      normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2) +
        normalDecay R l / 2 := by
    push_cast
    ring
  have hminus : normalDecay R l *
        ((a : ℝ) + (R + 1 : ℝ)) =
      normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2) -
        normalDecay R l / 2 := by
    ring
  rw [hplus, hminus]
  let X := normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2)
  let t := normalDecay R l / 2
  let D := Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))
  change
    (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D -
        (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D = _
  calc
    (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D -
          (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D =
        (4 * (R + 1 : ℝ)) *
          (Real.sinh (X + t) - Real.sinh (X - t)) / D := by ring
    _ = (4 * (R + 1 : ℝ)) *
          (2 * Real.cosh X * Real.sinh t) / D := by
      rw [sinh_add_sub_sub_eq_two_mul_cosh_mul_sinh]
    _ = _ := by dsimp [X, t, D]; ring

theorem rightBoundaryNormalResolvent_sub_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a - 1) (hau : a ≤ (R : ℤ)) :
    rightBoundaryNormalResolvent R l (a - 1) -
        rightBoundaryNormalResolvent R l a =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  have h := rightBoundaryNormalResolvent_add_one_sub
    (R := R) (l := l) (a := a - 1) hal (by omega)
  push_cast at h
  rw [show ((a : ℝ) - 1) + (R + 1 : ℝ) + 1 / 2 =
      (a : ℝ) + (R + 1 : ℝ) - 1 / 2 by ring] at h
  simp only [sub_add_cancel] at h
  convert congrArg Neg.neg h using 1 <;> ring

theorem rightBoundaryNormalResolvent_pos
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    0 < rightBoundaryNormalResolvent R l a := by
  rw [rightBoundaryNormalResolvent_eq_sinh_ratio R l hal hau]
  have hjInt : 0 < a + ((R + 1 : ℕ) : ℤ) := by omega
  have hj : (0 : ℝ) < (a : ℝ) + (R + 1 : ℝ) := by
    exact_mod_cast hjInt
  have hnum : 0 < Real.sinh
      (normalDecay R l * ((a : ℝ) + (R + 1 : ℝ))) := by
    rw [Real.sinh_pos_iff]
    exact mul_pos (normalDecay_pos R l) hj
  have hden : 0 < Real.sinh
      (normalDecay R l * (2 * (R + 1 : ℝ))) := by
    rw [Real.sinh_pos_iff]
    exact mul_pos (normalDecay_pos R l) (by positivity)
  exact div_pos (mul_pos (by positivity) hnum) hden

theorem squareSineCoordinate_neg
    (R : ℕ) (k : Fin (2 * R + 1)) (a : ℤ) :
    squareSineCoordinate R k (-a) =
      -((-1 : ℝ) ^ ((k : ℕ) + 1)) * squareSineCoordinate R k a := by
  unfold squareSineCoordinate
  rw [show squareSineAngle R k * ((-a : ℤ) : ℝ) +
        squareSineAngle R k * (R + 1 : ℝ) =
      (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi -
        (squareSineAngle R k * (a : ℝ) +
          squareSineAngle R k * (R + 1 : ℝ)) by
    unfold squareSineAngle
    have hpos : (0 : ℝ) < R + 1 := by positivity
    push_cast
    field_simp
    ring]
  rw [Real.sin_nat_mul_pi_sub]
  ring

theorem leftBoundaryNormalResolvent_eq_right_reflect
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    leftBoundaryNormalResolvent R l a =
      rightBoundaryNormalResolvent R l (-a) := by
  unfold leftBoundaryNormalResolvent rightBoundaryNormalResolvent
  apply Finset.sum_congr rfl
  intro k hk
  rw [squareSineCoordinate_neg]
  have hpow : (-1 : ℝ) ^ ((k : ℕ) * 2) = 1 := by
    rw [show (k : ℕ) * 2 = 2 * (k : ℕ) by omega, pow_mul]
    norm_num
  ring_nf
  rw [hpow]
  ring

theorem leftBoundaryNormalResolvent_eq_sinh_ratio
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    leftBoundaryNormalResolvent R l a =
      (4 * (R + 1 : ℝ)) *
        Real.sinh (normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ))) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  rw [leftBoundaryNormalResolvent_eq_right_reflect]
  rw [rightBoundaryNormalResolvent_eq_sinh_ratio
    (R := R) (l := l) (a := -a) (by omega) (by omega)]
  congr 2
  push_cast
  ring

theorem leftBoundaryNormalResolvent_eq_exp_decay
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    leftBoundaryNormalResolvent R l a =
      (4 * (R + 1 : ℝ)) *
        (Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) + (a : ℝ))) *
          ((1 - Real.exp (-2 * normalDecay R l *
              ((R + 1 : ℝ) - (a : ℝ)))) /
            (1 - Real.exp (-4 * normalDecay R l *
              (R + 1 : ℝ))))) := by
  rw [leftBoundaryNormalResolvent_eq_right_reflect]
  rw [rightBoundaryNormalResolvent_eq_exp_decay
    (R := R) (l := l) (a := -a) (by omega) (by omega)]
  push_cast
  congr 2
  · congr 1
    ring
  · congr 1
    · congr 1
      ring

theorem leftBoundaryNormalResolvent_le_exp_decay
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    leftBoundaryNormalResolvent R l a ≤
      (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R l *
          ((R + 1 : ℝ) + (a : ℝ))) := by
  rw [leftBoundaryNormalResolvent_eq_right_reflect]
  convert rightBoundaryNormalResolvent_le_exp_decay
      (R := R) (l := l) (a := -a) (by omega) (by omega) using 1 <;>
    push_cast <;> ring

theorem leftBoundaryNormalResolvent_add_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a + 1 ≤ (R : ℤ)) :
    leftBoundaryNormalResolvent R l (a + 1) -
        leftBoundaryNormalResolvent R l a =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  rw [leftBoundaryNormalResolvent_eq_right_reflect,
    leftBoundaryNormalResolvent_eq_right_reflect]
  have h := rightBoundaryNormalResolvent_add_one_sub
    (R := R) (l := l) (a := -(a + 1)) (by omega) (by omega)
  push_cast at h
  rw [show (-((a : ℝ) + 1)) + (R + 1 : ℝ) + 1 / 2 =
      (R + 1 : ℝ) - (a : ℝ) - 1 / 2 by ring] at h
  have h' := congrArg Neg.neg h
  convert h' using 1 <;> ring

theorem leftBoundaryNormalResolvent_sub_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a - 1) (hau : a ≤ (R : ℤ)) :
    leftBoundaryNormalResolvent R l (a - 1) -
        leftBoundaryNormalResolvent R l a =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  rw [leftBoundaryNormalResolvent_eq_right_reflect,
    leftBoundaryNormalResolvent_eq_right_reflect]
  have h := rightBoundaryNormalResolvent_add_one_sub
    (R := R) (l := l) (a := -a) (by omega) (by omega)
  push_cast at h
  rw [show (-(a : ℝ)) + (R + 1 : ℝ) + 1 / 2 =
      (R + 1 : ℝ) - (a : ℝ) + 1 / 2 by ring] at h
  convert h using 1 <;> ring

theorem leftBoundaryNormalResolvent_pos
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    0 < leftBoundaryNormalResolvent R l a := by
  rw [leftBoundaryNormalResolvent_eq_sinh_ratio R l hal hau]
  have hjInt : 0 < (R : ℤ) + 1 - a := by omega
  have hj : (0 : ℝ) < (R + 1 : ℝ) - (a : ℝ) := by
    exact_mod_cast hjInt
  have hnum : 0 < Real.sinh
      (normalDecay R l * ((R + 1 : ℝ) - (a : ℝ))) := by
    rw [Real.sinh_pos_iff]
    exact mul_pos (normalDecay_pos R l) hj
  have hden : 0 < Real.sinh
      (normalDecay R l * (2 * (R + 1 : ℝ))) := by
    rw [Real.sinh_pos_iff]
    exact mul_pos (normalDecay_pos R l) (by positivity)
  exact div_pos (mul_pos (by positivity) hnum) hden

theorem squareSineEigenvalue_comm
    (R : ℕ) (k l : Fin (2 * R + 1)) :
    squareSineEigenvalue R k l = squareSineEigenvalue R l k := by
  unfold squareSineEigenvalue
  ring

theorem topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent
    (R : ℕ) (k : Fin (2 * R + 1)) (b : ℤ) :
    topBoundaryNormalResolvent R k b =
      rightBoundaryNormalResolvent R k b := by
  unfold topBoundaryNormalResolvent rightBoundaryNormalResolvent
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineEigenvalue_comm]

theorem bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent
    (R : ℕ) (k : Fin (2 * R + 1)) (b : ℤ) :
    bottomBoundaryNormalResolvent R k b =
      leftBoundaryNormalResolvent R k b := by
  unfold bottomBoundaryNormalResolvent leftBoundaryNormalResolvent
  apply Finset.sum_congr rfl
  intro l hl
  rw [squareSineEigenvalue_comm]

theorem topBoundaryNormalResolvent_eq_sinh_ratio
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    topBoundaryNormalResolvent R k b =
      (4 * (R + 1 : ℝ)) *
        Real.sinh (normalDecay R k *
          ((b : ℝ) + (R + 1 : ℝ))) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  rw [topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent,
    rightBoundaryNormalResolvent_eq_sinh_ratio R k hbl hbu]

theorem bottomBoundaryNormalResolvent_eq_sinh_ratio
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    bottomBoundaryNormalResolvent R k b =
      (4 * (R + 1 : ℝ)) *
        Real.sinh (normalDecay R k *
          ((R + 1 : ℝ) - (b : ℝ))) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  rw [bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent,
    leftBoundaryNormalResolvent_eq_sinh_ratio R k hbl hbu]

theorem topBoundaryNormalResolvent_le_exp_decay
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    topBoundaryNormalResolvent R k b ≤
      (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R k *
          ((R + 1 : ℝ) - (b : ℝ))) := by
  rw [topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent]
  exact rightBoundaryNormalResolvent_le_exp_decay R k hbl hbu

theorem bottomBoundaryNormalResolvent_le_exp_decay
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    bottomBoundaryNormalResolvent R k b ≤
      (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R k *
          ((R + 1 : ℝ) + (b : ℝ))) := by
  rw [bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent]
  exact leftBoundaryNormalResolvent_le_exp_decay R k hbl hbu

theorem topBoundaryNormalResolvent_add_one_sub
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b + 1 ≤ (R : ℤ)) :
    topBoundaryNormalResolvent R k (b + 1) -
        topBoundaryNormalResolvent R k b =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R k *
          ((b : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R k / 2) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  simp_rw [topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent]
  exact rightBoundaryNormalResolvent_add_one_sub R k hbl hbu

theorem topBoundaryNormalResolvent_sub_one_sub
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b - 1) (hbu : b ≤ (R : ℤ)) :
    topBoundaryNormalResolvent R k (b - 1) -
        topBoundaryNormalResolvent R k b =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R k *
          ((b : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R k / 2) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  simp_rw [topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent]
  exact rightBoundaryNormalResolvent_sub_one_sub R k hbl hbu

theorem bottomBoundaryNormalResolvent_add_one_sub
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b + 1 ≤ (R : ℤ)) :
    bottomBoundaryNormalResolvent R k (b + 1) -
        bottomBoundaryNormalResolvent R k b =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R k *
          ((R + 1 : ℝ) - (b : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R k / 2) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  simp_rw [bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent]
  exact leftBoundaryNormalResolvent_add_one_sub R k hbl hbu

theorem bottomBoundaryNormalResolvent_sub_one_sub
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b - 1) (hbu : b ≤ (R : ℤ)) :
    bottomBoundaryNormalResolvent R k (b - 1) -
        bottomBoundaryNormalResolvent R k b =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R k *
          ((R + 1 : ℝ) - (b : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R k / 2) /
        Real.sinh (normalDecay R k * (2 * (R + 1 : ℝ))) := by
  simp_rw [bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent]
  exact leftBoundaryNormalResolvent_sub_one_sub R k hbl hbu

/-! ## Exact tangential and normal edge increments

These formulas are the cancellation-preserving starting point for the
remaining one-dimensional signed-sum estimate.  They expose the small
half-angle in a tangential edge and the hyperbolic half-angle in a normal
edge, but do not take absolute values mode by mode. -/

theorem squareSineCoordinate_add_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (b : ℤ) :
    squareSineCoordinate R l (b + 1) - squareSineCoordinate R l b =
      2 * Real.cos (squareSineAngle R l *
        ((b : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
        Real.sin (squareSineAngle R l / 2) := by
  unfold squareSineCoordinate
  have hs (x t : ℝ) :
      Real.sin (x + t) - Real.sin (x - t) =
        2 * Real.cos x * Real.sin t := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  have hplus : squareSineAngle R l * (((b + 1 : ℤ) : ℝ)) +
        squareSineAngle R l * (R + 1 : ℝ) =
      squareSineAngle R l *
          ((b : ℝ) + (R + 1 : ℝ) + 1 / 2) +
        squareSineAngle R l / 2 := by
    push_cast
    ring
  have hminus : squareSineAngle R l * (b : ℝ) +
        squareSineAngle R l * (R + 1 : ℝ) =
      squareSineAngle R l *
          ((b : ℝ) + (R + 1 : ℝ) + 1 / 2) -
        squareSineAngle R l / 2 := by
    ring
  rw [hplus, hminus, hs]

theorem squareSineCoordinate_sub_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (b : ℤ) :
    squareSineCoordinate R l (b - 1) - squareSineCoordinate R l b =
      -2 * Real.cos (squareSineAngle R l *
        ((b : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
        Real.sin (squareSineAngle R l / 2) := by
  have h := squareSineCoordinate_add_one_sub R l (b - 1)
  push_cast at h
  rw [show ((b : ℝ) - 1) + (R + 1 : ℝ) + 1 / 2 =
      (b : ℝ) + (R + 1 : ℝ) - 1 / 2 by ring] at h
  simp only [sub_add_cancel] at h
  convert congrArg Neg.neg h using 1 <;> ring

theorem abs_squareSineCoordinate_add_one_sub_le_angle
    (R : ℕ) (l : Fin (2 * R + 1)) (b : ℤ) :
    |squareSineCoordinate R l (b + 1) -
        squareSineCoordinate R l b| ≤ squareSineAngle R l := by
  rw [squareSineCoordinate_add_one_sub]
  have hcos := Real.abs_cos_le_one
    (squareSineAngle R l * ((b : ℝ) + (R + 1 : ℝ) + 1 / 2))
  have hsin : |Real.sin (squareSineAngle R l / 2)| ≤
      |squareSineAngle R l / 2| := Real.abs_sin_le_abs
  have hhalf : 0 ≤ squareSineAngle R l / 2 :=
    div_nonneg (squareSineAngle_pos R l).le (by norm_num)
  rw [abs_of_nonneg hhalf] at hsin
  calc
    |2 * Real.cos (squareSineAngle R l *
          ((b : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
        Real.sin (squareSineAngle R l / 2)| =
      2 * |Real.cos (squareSineAngle R l *
          ((b : ℝ) + (R + 1 : ℝ) + 1 / 2))| *
        |Real.sin (squareSineAngle R l / 2)| := by
          rw [abs_mul, abs_mul]
          norm_num
    _ ≤
      2 * 1 * (squareSineAngle R l / 2) := by gcongr
    _ = squareSineAngle R l := by ring

theorem abs_squareSineCoordinate_sub_one_sub_le_angle
    (R : ℕ) (l : Fin (2 * R + 1)) (b : ℤ) :
    |squareSineCoordinate R l (b - 1) -
        squareSineCoordinate R l b| ≤ squareSineAngle R l := by
  have h := abs_squareSineCoordinate_add_one_sub_le_angle R l (b - 1)
  rw [sub_add_cancel] at h
  rw [show squareSineCoordinate R l (b - 1) -
      squareSineCoordinate R l b =
        -(squareSineCoordinate R l b -
          squareSineCoordinate R l (b - 1)) by ring, abs_neg]
  simpa using h

/-- Right-face column edge split.  Horizontal edges differentiate only the
closed normal resolvent, while vertical edges differentiate only the
tangential sine.  The outer sum remains signed. -/
theorem rightBoundaryColumnProfile_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    rightBoundaryColumnProfile R z (x + directionStep e) -
        rightBoundaryColumnProfile R z x =
      match e.1 with
      | 0 => ∑ l : Fin (2 * R + 1),
          squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            (rightBoundaryNormalResolvent R l (x.1 + 1) -
              rightBoundaryNormalResolvent R l x.1)
      | 1 => ∑ l : Fin (2 * R + 1),
          squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            (rightBoundaryNormalResolvent R l (x.1 - 1) -
              rightBoundaryNormalResolvent R l x.1)
      | 2 => ∑ l : Fin (2 * R + 1),
          squareSineCoordinate R l z.2 *
            (squareSineCoordinate R l (x.2 + 1) -
              squareSineCoordinate R l x.2) *
            rightBoundaryNormalResolvent R l x.1
      | _ => ∑ l : Fin (2 * R + 1),
          squareSineCoordinate R l z.2 *
            (squareSineCoordinate R l (x.2 - 1) -
              squareSineCoordinate R l x.2) *
            rightBoundaryNormalResolvent R l x.1 := by
  fin_cases e <;>
    unfold rightBoundaryColumnProfile <;>
    simp only [directionStep, Prod.fst_add, Prod.snd_add, Int.reduceNeg,
      add_zero, zero_add] <;>
    rw [← Finset.sum_sub_distrib] <;>
    apply Finset.sum_congr rfl <;>
    intro l hl <;> ring

/-! ## Fully resolved signed tangential profiles -/

noncomputable def rightResolvedNormalWeight
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  (4 * (R + 1 : ℝ)) *
    Real.sinh (normalDecay R l * ((a : ℝ) + (R + 1 : ℝ))) /
    Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))

noncomputable def leftResolvedNormalWeight
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  (4 * (R + 1 : ℝ)) *
    Real.sinh (normalDecay R l * ((R + 1 : ℝ) - (a : ℝ))) /
    Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))

theorem rightResolvedNormalWeight_eq_normalResolvent
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightResolvedNormalWeight R l a =
      rightBoundaryNormalResolvent R l a := by
  symm
  exact rightBoundaryNormalResolvent_eq_sinh_ratio R l hal hau

theorem rightResolvedNormalWeight_pos
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    0 < rightResolvedNormalWeight R l a := by
  rw [rightResolvedNormalWeight_eq_normalResolvent R l hal hau]
  exact rightBoundaryNormalResolvent_pos R l hal hau

theorem rightResolvedNormalWeight_le_exp_decay
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    rightResolvedNormalWeight R l a ≤
      (8 * (R + 1 : ℝ)) *
        Real.exp (-normalDecay R l * ((R + 1 : ℝ) - (a : ℝ))) := by
  rw [rightResolvedNormalWeight_eq_normalResolvent R l hal hau]
  exact rightBoundaryNormalResolvent_le_exp_decay R l hal hau

theorem rightResolvedNormalWeight_add_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    rightResolvedNormalWeight R l (a + 1) -
        rightResolvedNormalWeight R l a =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  unfold rightResolvedNormalWeight
  have hplus : normalDecay R l *
        (((a + 1 : ℤ) : ℝ) + (R + 1 : ℝ)) =
      normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2) +
        normalDecay R l / 2 := by
    push_cast
    ring
  have hminus : normalDecay R l *
        ((a : ℝ) + (R + 1 : ℝ)) =
      normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2) -
        normalDecay R l / 2 := by
    ring
  rw [hplus, hminus]
  let X := normalDecay R l * ((a : ℝ) + (R + 1 : ℝ) + 1 / 2)
  let t := normalDecay R l / 2
  let D := Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))
  change
    (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D -
        (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D = _
  calc
    (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D -
          (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D =
        (4 * (R + 1 : ℝ)) *
          (Real.sinh (X + t) - Real.sinh (X - t)) / D := by ring
    _ = (4 * (R + 1 : ℝ)) *
          (2 * Real.cosh X * Real.sinh t) / D := by
      rw [sinh_add_sub_sub_eq_two_mul_cosh_mul_sinh]
    _ = _ := by dsimp [X, t, D]; ring

theorem rightResolvedNormalWeight_sub_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    rightResolvedNormalWeight R l (a - 1) -
        rightResolvedNormalWeight R l a =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((a : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  have h := rightResolvedNormalWeight_add_one_sub R l (a - 1)
  push_cast at h
  rw [show ((a : ℝ) - 1) + (R + 1 : ℝ) + 1 / 2 =
      (a : ℝ) + (R + 1 : ℝ) - 1 / 2 by ring] at h
  simp only [sub_add_cancel] at h
  convert congrArg Neg.neg h using 1 <;> ring

/-- A normal-direction increment gains one factor of the mode decay.  The
exponential is measured from the endpoint of the oriented edge. -/
theorem abs_rightResolvedNormalWeight_add_one_sub_le
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a + 1 ≤ (R : ℤ)) :
    |rightResolvedNormalWeight R l (a + 1) -
        rightResolvedNormalWeight R l a| ≤
      (16 * (R + 1 : ℝ)) * normalDecay R l *
        Real.exp (-normalDecay R l *
          ((R + 1 : ℝ) - ((a + 1 : ℤ) : ℝ))) := by
  rw [rightResolvedNormalWeight_add_one_sub]
  let γ := normalDecay R l
  let L : ℝ := R + 1
  let X := γ * ((a : ℝ) + L + 1 / 2)
  let t := γ / 2
  let den := Real.sinh (γ * (2 * L))
  have hγ : 0 < γ := normalDecay_pos R l
  have hL : 0 < L := by dsimp [L]; positivity
  have hj : 0 ≤ (a : ℝ) + L + 1 / 2 := by
    have haj : (0 : ℤ) ≤ a + (R : ℤ) := by omega
    have hajReal : (0 : ℝ) ≤ (a : ℝ) + (R : ℝ) := by exact_mod_cast haj
    dsimp only [L]
    linarith
  have hX : 0 ≤ X := mul_nonneg hγ.le hj
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : 0 < den := by
    dsimp only [den, γ, L]
    rw [Real.sinh_pos_iff]
    positivity
  have hcosh : Real.cosh X ≤ Real.exp X := cosh_le_exp_of_nonneg hX
  have hsinh : Real.sinh t ≤ t * Real.exp t :=
    sinh_le_mul_exp_of_nonneg ht
  have hnum :
      (8 * L) * Real.cosh X * Real.sinh t ≤
        (4 * L) * γ * Real.exp (γ * ((a : ℝ) + L + 1)) := by
    calc
      (8 * L) * Real.cosh X * Real.sinh t ≤
          (8 * L) * Real.exp X * (t * Real.exp t) := by
        gcongr
      _ = (8 * L) * t * (Real.exp X * Real.exp t) := by ring
      _ = (8 * L) * t * Real.exp (X + t) := by
        rw [← Real.exp_add]
      _ = (4 * L) * γ * Real.exp (γ * ((a : ℝ) + L + 1)) := by
        dsimp only [X, t]
        congr 1 <;> ring
  have hdenLower :
      Real.exp (2 * γ * L) ≤ 4 * den := by
    convert exp_two_normalDecay_mul_le_four_mul_sinh R l using 1 <;>
      dsimp only [γ, L, den] <;> ring
  have hfactor0 : 0 ≤
      (4 * L) * γ *
        Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ)))) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hdenLower hfactor0
  have hbridge :
      (4 * L) * γ * Real.exp (γ * ((a : ℝ) + L + 1)) ≤
        ((16 * L) * γ *
          Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))))) * den := by
    calc
      (4 * L) * γ * Real.exp (γ * ((a : ℝ) + L + 1)) =
          ((4 * L) * γ *
            Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))))) *
              Real.exp (2 * γ * L) := by
        symm
        calc
          ((4 * L) * γ *
              Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))))) *
                Real.exp (2 * γ * L) =
              (4 * L) * γ *
                (Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ)))) *
                  Real.exp (2 * γ * L)) := by ring
          _ = (4 * L) * γ *
                Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))) +
                  2 * γ * L) := by rw [← Real.exp_add]
          _ = (4 * L) * γ * Real.exp (γ * ((a : ℝ) + L + 1)) := by
            push_cast
            congr 2
            ring
      _ ≤ ((4 * L) * γ *
            Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))))) *
              (4 * den) := hscaled
      _ = ((16 * L) * γ *
            Real.exp (-γ * (L - (((a + 1 : ℤ) : ℝ))))) * den := by ring
  rw [abs_of_nonneg]
  · apply (div_le_iff₀ hden).2
    exact hnum.trans hbridge
  · apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity) (Real.cosh_pos _).le)
        (Real.sinh_nonneg_iff.mpr ht)
    · exact hden.le

theorem abs_rightResolvedNormalWeight_sub_one_sub_le
    (R : ℕ) (l : Fin (2 * R + 1)) {a : ℤ}
    (hal : -(R : ℤ) ≤ a - 1) (hau : a ≤ (R : ℤ)) :
    |rightResolvedNormalWeight R l (a - 1) -
        rightResolvedNormalWeight R l a| ≤
      (16 * (R + 1 : ℝ)) * normalDecay R l *
        Real.exp (-normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ))) := by
  have h := abs_rightResolvedNormalWeight_add_one_sub_le
    (R := R) (l := l) (a := a - 1) hal (by omega)
  rw [sub_add_cancel] at h
  rw [show rightResolvedNormalWeight R l (a - 1) -
      rightResolvedNormalWeight R l a =
        -(rightResolvedNormalWeight R l a -
          rightResolvedNormalWeight R l (a - 1)) by ring, abs_neg]
  simpa using h

theorem leftResolvedNormalWeight_add_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    leftResolvedNormalWeight R l (a + 1) -
        leftResolvedNormalWeight R l a =
      -(8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ) - 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  unfold leftResolvedNormalWeight
  have hplus : normalDecay R l *
        ((R + 1 : ℝ) - (a : ℝ)) =
      normalDecay R l * ((R + 1 : ℝ) - (a : ℝ) - 1 / 2) +
        normalDecay R l / 2 := by
    ring
  have hminus : normalDecay R l *
        ((R + 1 : ℝ) - (((a + 1 : ℤ) : ℝ))) =
      normalDecay R l * ((R + 1 : ℝ) - (a : ℝ) - 1 / 2) -
        normalDecay R l / 2 := by
    push_cast
    ring
  rw [hminus, hplus]
  let X := normalDecay R l * ((R + 1 : ℝ) - (a : ℝ) - 1 / 2)
  let t := normalDecay R l / 2
  let D := Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ)))
  have hraw : Real.sinh (X - t) - Real.sinh (X + t) =
      -(2 * Real.cosh X * Real.sinh t) := by
    linarith [sinh_add_sub_sub_eq_two_mul_cosh_mul_sinh X t]
  change
    (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D -
        (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D = _
  calc
    (4 * (R + 1 : ℝ)) * Real.sinh (X - t) / D -
          (4 * (R + 1 : ℝ)) * Real.sinh (X + t) / D =
        (4 * (R + 1 : ℝ)) *
          (Real.sinh (X - t) - Real.sinh (X + t)) / D := by ring
    _ = (4 * (R + 1 : ℝ)) *
          (-(2 * Real.cosh X * Real.sinh t)) / D := by rw [hraw]
    _ = _ := by dsimp [X, t, D]; ring

theorem leftResolvedNormalWeight_sub_one_sub
    (R : ℕ) (l : Fin (2 * R + 1)) (a : ℤ) :
    leftResolvedNormalWeight R l (a - 1) -
        leftResolvedNormalWeight R l a =
      (8 * (R + 1 : ℝ)) *
        Real.cosh (normalDecay R l *
          ((R + 1 : ℝ) - (a : ℝ) + 1 / 2)) *
        Real.sinh (normalDecay R l / 2) /
        Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))) := by
  have h := leftResolvedNormalWeight_add_one_sub R l (a - 1)
  push_cast at h
  rw [show (R + 1 : ℝ) - ((a : ℝ) - 1) - 1 / 2 =
      (R + 1 : ℝ) - (a : ℝ) + 1 / 2 by ring] at h
  simp only [sub_add_cancel] at h
  convert congrArg Neg.neg h using 1 <;> ring

/-- Right-face column after substituting the exact hyperbolic normal
resolvent.  This is a single signed tangential sum. -/
noncomputable def rightBoundaryResolvedColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
      rightResolvedNormalWeight R l x.1

noncomputable def leftBoundaryResolvedColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ l : Fin (2 * R + 1),
    squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
      leftResolvedNormalWeight R l x.1

noncomputable def topBoundaryResolvedColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    squareSineCoordinate R k z.1 * squareSineCoordinate R k x.1 *
      rightResolvedNormalWeight R k x.2

noncomputable def bottomBoundaryResolvedColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  ∑ k : Fin (2 * R + 1),
    squareSineCoordinate R k z.1 * squareSineCoordinate R k x.1 *
      leftResolvedNormalWeight R k x.2

/-- The exact right-face edge derivative written as one signed tangential
sum with all one-dimensional differences evaluated. -/
noncomputable def rightBoundaryResolvedEdgeProfile
    (R : ℕ) (z x : Site) (e : Direction) : ℝ :=
  match e.1 with
  | 0 => ∑ l : Fin (2 * R + 1),
      squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
        ((8 * (R + 1 : ℝ)) *
          Real.cosh (normalDecay R l *
            ((x.1 : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
          Real.sinh (normalDecay R l / 2) /
          Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))))
  | 1 => ∑ l : Fin (2 * R + 1),
      squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
        (-(8 * (R + 1 : ℝ)) *
          Real.cosh (normalDecay R l *
            ((x.1 : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
          Real.sinh (normalDecay R l / 2) /
          Real.sinh (normalDecay R l * (2 * (R + 1 : ℝ))))
  | 2 => ∑ l : Fin (2 * R + 1),
      squareSineCoordinate R l z.2 *
        (2 * Real.cos (squareSineAngle R l *
            ((x.2 : ℝ) + (R + 1 : ℝ) + 1 / 2)) *
          Real.sin (squareSineAngle R l / 2)) *
        rightResolvedNormalWeight R l x.1
  | _ => ∑ l : Fin (2 * R + 1),
      squareSineCoordinate R l z.2 *
        (-2 * Real.cos (squareSineAngle R l *
            ((x.2 : ℝ) + (R + 1 : ℝ) - 1 / 2)) *
          Real.sin (squareSineAngle R l / 2)) *
        rightResolvedNormalWeight R l x.1

/-- The strictly positive tangential factor shared by all right-face modes.
It records the exact vanishing order at either corner. -/
noncomputable def rightBoundaryCornerFactor (R : ℕ) (z : Site) : ℝ :=
  squareSineCoordinate R ⟨0, by omega⟩ z.2

/-- The right-face column with its common corner sine divided out. -/
noncomputable def rightBoundaryCornerNormalizedColumnProfile
    (R : ℕ) (z x : Site) : ℝ :=
  rightBoundaryResolvedColumnProfile R z x /
    rightBoundaryCornerFactor R z

/-- The right-face edge derivative with the same corner sine divided out. -/
noncomputable def rightBoundaryCornerNormalizedEdgeProfile
    (R : ℕ) (z x : Site) (e : Direction) : ℝ :=
  rightBoundaryResolvedEdgeProfile R z x e /
    rightBoundaryCornerFactor R z

/-- Tangential mode coefficient after dividing by the common first sine at
the last-step predecessor. -/
noncomputable def rightBoundaryCornerModeRatio
    (R : ℕ) (z : Site) (l : Fin (2 * R + 1)) : ℝ :=
  squareSineCoordinate R l z.2 / rightBoundaryCornerFactor R z

noncomputable def rightBoundaryCornerNormalizedEdgeMode
    (R : ℕ) (z x : Site) (e : Direction)
    (l : Fin (2 * R + 1)) : ℝ :=
  rightBoundaryCornerModeRatio R z l *
    (squareSineCoordinate R l (x + directionStep e).2 *
        rightResolvedNormalWeight R l (x + directionStep e).1 -
      squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1)

theorem rightBoundaryCornerFactor_pos
    (R : ℕ) {z : Site} (hz : z ∈ squareDisk R) :
    0 < rightBoundaryCornerFactor R z := by
  unfold rightBoundaryCornerFactor
  unfold squareDisk at hz
  have hz' := Finset.mem_product.mp hz
  simp only [Finset.mem_Icc] at hz'
  exact squareSineCoordinate_first_pos R hz'.2.1 hz'.2.2

theorem rightBoundaryCornerModeRatio_zero
    (R : ℕ) {z : Site} (hz : z ∈ squareDisk R) :
    rightBoundaryCornerModeRatio R z ⟨0, by omega⟩ = 1 := by
  unfold rightBoundaryCornerModeRatio rightBoundaryCornerFactor
  exact div_self (ne_of_gt (rightBoundaryCornerFactor_pos R hz))

/-- After corner normalization, the `l`-th tangential coefficient grows at
most linearly in its frequency.  This is the precise summable envelope used
in the remaining one-dimensional estimate. -/
theorem abs_rightBoundaryCornerModeRatio_le
    (R : ℕ) {z : Site} (hz : z ∈ squareDisk R)
    (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerModeRatio R z l| ≤ (((l : ℕ) + 1 : ℕ) : ℝ) := by
  have hc : 0 < rightBoundaryCornerFactor R z :=
    rightBoundaryCornerFactor_pos R hz
  have hc0 : 0 < squareSineCoordinate R ⟨0, by omega⟩ z.2 := by
    simpa only [rightBoundaryCornerFactor] using hc
  unfold rightBoundaryCornerModeRatio
  rw [abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).2
  simpa only [rightBoundaryCornerFactor, abs_of_pos hc0] using
    abs_squareSineCoordinate_le_mode_mul_first R l z.2

/-- Exact single-sum formula for the corner-normalized right-face column. -/
theorem rightBoundaryCornerNormalizedColumnProfile_eq_sum
    (R : ℕ) (z x : Site) :
    rightBoundaryCornerNormalizedColumnProfile R z x =
      ∑ l : Fin (2 * R + 1),
        rightBoundaryCornerModeRatio R z l *
          squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1 := by
  unfold rightBoundaryCornerNormalizedColumnProfile
  unfold rightBoundaryResolvedColumnProfile rightBoundaryCornerModeRatio
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Absolute geometric envelope for one summand of the normalized column.
No boundary-position denominator remains: its only mode loss is `l+1`. -/
theorem abs_rightBoundaryCornerNormalizedColumnMode_le
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hxl : -(R : ℤ) ≤ x.1) (hxu : x.1 ≤ (R : ℤ))
    (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerModeRatio R z l *
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1| ≤
      (((l : ℕ) + 1 : ℕ) : ℝ) *
        ((8 * (R + 1 : ℝ)) *
          Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (x.1 : ℝ)))) := by
  have hratio := abs_rightBoundaryCornerModeRatio_le R hz l
  have hsine : |squareSineCoordinate R l x.2| ≤ 1 := by
    unfold squareSineCoordinate
    exact Real.abs_sin_le_one _
  have hweight : 0 < rightResolvedNormalWeight R l x.1 :=
    rightResolvedNormalWeight_pos R l hxl hxu
  have hweightUpper := rightResolvedNormalWeight_le_exp_decay R l hxl hxu
  rw [abs_mul, abs_mul, abs_of_pos hweight]
  calc
    |rightBoundaryCornerModeRatio R z l| *
          |squareSineCoordinate R l x.2| *
          rightResolvedNormalWeight R l x.1 ≤
        (((l : ℕ) + 1 : ℕ) : ℝ) * 1 *
          ((8 * (R + 1 : ℝ)) *
            Real.exp (-normalDecay R l *
              ((R + 1 : ℝ) - (x.1 : ℝ)))) := by
      gcongr
    _ = _ := by ring

/-- The same normalized mode envelope with the decay written directly in
the tangential frequency. -/
theorem abs_rightBoundaryCornerNormalizedColumnMode_le_angleDecay
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hxl : -(R : ℤ) ≤ x.1) (hxu : x.1 ≤ (R : ℤ))
    (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerModeRatio R z l *
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1| ≤
      (((l : ℕ) + 1 : ℕ) : ℝ) *
        ((8 * (R + 1 : ℝ)) *
          Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
            ((R + 1 : ℝ) - (x.1 : ℝ)))) := by
  have hbase := abs_rightBoundaryCornerNormalizedColumnMode_le
    R hz hxl hxu l
  have hdist : 0 ≤ (R + 1 : ℝ) - (x.1 : ℝ) := by
    have hxreal : (x.1 : ℝ) ≤ (R + 1 : ℝ) := by
      exact_mod_cast (show (x.1 : ℤ) ≤ (R : ℤ) + 1 by omega)
    linarith
  have hdecay := two_fifths_mul_squareSineAngle_le_normalDecay R l
  have hmul := mul_le_mul_of_nonneg_right hdecay hdist
  have hexp :
      Real.exp (-normalDecay R l * ((R + 1 : ℝ) - (x.1 : ℝ))) ≤
        Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
          ((R + 1 : ℝ) - (x.1 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    |rightBoundaryCornerModeRatio R z l *
          squareSineCoordinate R l x.2 *
          rightResolvedNormalWeight R l x.1| ≤
        (((l : ℕ) + 1 : ℕ) : ℝ) *
          ((8 * (R + 1 : ℝ)) *
            Real.exp (-normalDecay R l *
              ((R + 1 : ℝ) - (x.1 : ℝ)))) := hbase
    _ ≤ _ := by gcongr

/-- Summed geometric envelope for the complete normalized signed column. -/
theorem abs_rightBoundaryCornerNormalizedColumnProfile_le_angleDecaySum
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hxl : -(R : ℤ) ≤ x.1) (hxu : x.1 ≤ (R : ℤ)) :
    |rightBoundaryCornerNormalizedColumnProfile R z x| ≤
      ∑ l : Fin (2 * R + 1),
        (((l : ℕ) + 1 : ℕ) : ℝ) *
          ((8 * (R + 1 : ℝ)) *
            Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
              ((R + 1 : ℝ) - (x.1 : ℝ)))) := by
  rw [rightBoundaryCornerNormalizedColumnProfile_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  exact abs_rightBoundaryCornerNormalizedColumnMode_le_angleDecay
    R hz hxl hxu l

/-- A uniform `O(R)` upper bound for a corner-normalized column whose start
lies in the central half-square.  The numerical constant is intentionally
generous; its significance is that it is independent of the exit location
and of the square radius. -/
theorem abs_rightBoundaryCornerNormalizedColumnProfile_le_of_two_mul_inner
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R) :
    |rightBoundaryCornerNormalizedColumnProfile R z x| ≤
      160 * (R + 1 : ℝ) := by
  have hr_le : r ≤ R := by omega
  have hxsmall := Finset.mem_product.mp hx
  simp only [Finset.mem_Icc] at hxsmall
  have hxlR : -(R : ℤ) ≤ x.1 := by omega
  have hxuR : x.1 ≤ (R : ℤ) := by omega
  have hsum := abs_rightBoundaryCornerNormalizedColumnProfile_le_angleDecaySum
    R hz hxlR hxuR
  have hmode : ∀ l : Fin (2 * R + 1),
      Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
          ((R + 1 : ℝ) - (x.1 : ℝ))) ≤
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
    intro l
    let q : ℕ := (l : ℕ) + 1
    let L : ℝ := R + 1
    let dist : ℝ := (R + 1 : ℝ) - (x.1 : ℝ)
    have hcoord : (2 : ℝ) * (x.1 : ℝ) ≤ (R : ℝ) := by
      have hxint : (2 : ℤ) * x.1 ≤ (R : ℤ) := by omega
      exact_mod_cast hxint
    have hdist : L / 2 ≤ dist := by
      dsimp only [L, dist]
      push_cast
      linarith
    have hL : 0 < L := by dsimp [L]; positivity
    have hq : 0 < (q : ℝ) := by
      exact_mod_cast (show 0 < q by dsimp [q]; omega)
    have hfac : 0 ≤ Real.pi * (q : ℝ) / (2 * L) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdist hfac
    have hangleDist :
        Real.pi * (q : ℝ) / 4 ≤ squareSineAngle R l * dist := by
      have hangle : squareSineAngle R l =
          Real.pi * (q : ℝ) / (2 * L) := by
        unfold squareSineAngle
        dsimp only [q, L]
        norm_num
      rw [hangle]
      calc
        Real.pi * (q : ℝ) / 4 =
            (Real.pi * (q : ℝ) / (2 * L)) * (L / 2) := by
          field_simp [ne_of_gt hL] <;> ring
        _ ≤ (Real.pi * (q : ℝ) / (2 * L)) * dist := hmul
    have hpi : (q : ℝ) / 4 ≤
        (2 / 5 : ℝ) * (Real.pi * (q : ℝ) / 4) := by
      have hnonneg : 0 ≤ (Real.pi - 5 / 2) * (q : ℝ) := by
        exact mul_nonneg (by linarith [Real.pi_gt_three]) hq.le
      nlinarith
    have hexponent : (q : ℝ) / 4 ≤
        (2 / 5 : ℝ) * squareSineAngle R l * dist := by
      nlinarith [hangleDist]
    have hexp :
        Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) * dist) ≤
          Real.exp (-((q : ℝ) / 4)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hpowExp : Real.exp (-((q : ℝ) / 4)) =
        Real.exp (-(1 / 4 : ℝ)) ^ q := by
      rw [show -((q : ℝ) / 4) = (q : ℕ) * (-(1 / 4 : ℝ)) by
        push_cast
        ring]
      exact Real.exp_nat_mul _ _
    calc
      Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
          ((R + 1 : ℝ) - (x.1 : ℝ))) =
          Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) * dist) := rfl
      _ ≤ Real.exp (-((q : ℝ) / 4)) := hexp
      _ = Real.exp (-(1 / 4 : ℝ)) ^ q := hpowExp
      _ ≤ (4 / 5 : ℝ) ^ q :=
        pow_le_pow_left₀ (Real.exp_pos _).le
          exp_neg_one_fourth_le_four_fifths q
      _ = (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := rfl
  calc
    |rightBoundaryCornerNormalizedColumnProfile R z x| ≤
        ∑ l : Fin (2 * R + 1),
          (((l : ℕ) + 1 : ℕ) : ℝ) *
            ((8 * (R + 1 : ℝ)) *
              Real.exp (-((2 / 5 : ℝ) * squareSineAngle R l) *
                ((R + 1 : ℝ) - (x.1 : ℝ)))) := hsum
    _ ≤ ∑ l : Fin (2 * R + 1),
          (((l : ℕ) + 1 : ℕ) : ℝ) *
            ((8 * (R + 1 : ℝ)) *
              (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) := by
      apply Finset.sum_le_sum
      intro l hl
      gcongr
      exact hmode l
    _ = (8 * (R + 1 : ℝ)) *
          (∑ l : Fin (2 * R + 1),
            (((l : ℕ) + 1 : ℕ) : ℝ) *
              (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ (8 * (R + 1 : ℝ)) * 20 := by
      gcongr
      exact sum_fin_succ_mul_four_fifths_pow_le (2 * R + 1)
    _ = 160 * (R + 1 : ℝ) := by ring

/-- Uniform geometric decay of every normal mode from the boundary to the
central half-square. -/
theorem exp_neg_normalDecay_distance_le_four_fifths_pow
    (r R : ℕ) {x : Site} (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (l : Fin (2 * R + 1)) :
    Real.exp (-normalDecay R l * ((R + 1 : ℝ) - (x.1 : ℝ))) ≤
      (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℕ := (l : ℕ) + 1
  let L : ℝ := R + 1
  let dist : ℝ := (R + 1 : ℝ) - (x.1 : ℝ)
  have hxsmall := Finset.mem_product.mp hx
  simp only [Finset.mem_Icc] at hxsmall
  have hcoord : (2 : ℝ) * (x.1 : ℝ) ≤ (R : ℝ) := by
    have hxint : (2 : ℤ) * x.1 ≤ (R : ℤ) := by omega
    exact_mod_cast hxint
  have hdist : L / 2 ≤ dist := by
    dsimp only [L, dist]
    linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by dsimp [q]; omega)
  have hfac : 0 ≤ Real.pi * (q : ℝ) / (2 * L) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdist hfac
  have hangleDist :
      Real.pi * (q : ℝ) / 4 ≤ squareSineAngle R l * dist := by
    have hangle : squareSineAngle R l =
        Real.pi * (q : ℝ) / (2 * L) := by
      unfold squareSineAngle
      dsimp only [q, L]
      norm_num
    rw [hangle]
    calc
      Real.pi * (q : ℝ) / 4 =
          (Real.pi * (q : ℝ) / (2 * L)) * (L / 2) := by
        field_simp [ne_of_gt hL] <;> ring
      _ ≤ (Real.pi * (q : ℝ) / (2 * L)) * dist := hmul
  have hpi : (q : ℝ) / 4 ≤
      (2 / 5 : ℝ) * (Real.pi * (q : ℝ) / 4) := by
    have hnonneg : 0 ≤ (Real.pi - 5 / 2) * (q : ℝ) := by
      exact mul_nonneg (by linarith [Real.pi_gt_three]) hq.le
    nlinarith
  have hexponent : (q : ℝ) / 4 ≤
      (2 / 5 : ℝ) * squareSineAngle R l * dist := by
    nlinarith [hangleDist]
  have hnormal : (2 / 5 : ℝ) * squareSineAngle R l ≤
      normalDecay R l := two_fifths_mul_squareSineAngle_le_normalDecay R l
  have hdist0 : 0 ≤ dist := le_trans (by positivity : (0 : ℝ) ≤ L / 2) hdist
  have hnormalMul := mul_le_mul_of_nonneg_right hnormal hdist0
  have hexp :
      Real.exp (-normalDecay R l * dist) ≤
        Real.exp (-((q : ℝ) / 4)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpowExp : Real.exp (-((q : ℝ) / 4)) =
      Real.exp (-(1 / 4 : ℝ)) ^ q := by
    rw [show -((q : ℝ) / 4) = (q : ℕ) * (-(1 / 4 : ℝ)) by
      push_cast
      ring]
    exact Real.exp_nat_mul _ _
  calc
    Real.exp (-normalDecay R l * ((R + 1 : ℝ) - (x.1 : ℝ))) =
        Real.exp (-normalDecay R l * dist) := rfl
    _ ≤ Real.exp (-((q : ℝ) / 4)) := hexp
    _ = Real.exp (-(1 / 4 : ℝ)) ^ q := hpowExp
    _ ≤ (4 / 5 : ℝ) ^ q :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        exp_neg_one_fourth_le_four_fifths q
    _ = (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := rfl

theorem rightBoundaryCornerFactor_mul_normalizedColumn
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R) :
    rightBoundaryCornerFactor R z *
        rightBoundaryCornerNormalizedColumnProfile R z x =
      rightBoundaryResolvedColumnProfile R z x := by
  unfold rightBoundaryCornerNormalizedColumnProfile
  exact mul_div_cancel₀ _ (ne_of_gt (rightBoundaryCornerFactor_pos R hz))

theorem rightBoundaryCornerFactor_mul_normalizedEdge
    (R : ℕ) {z x : Site} (e : Direction) (hz : z ∈ squareDisk R) :
    rightBoundaryCornerFactor R z *
        rightBoundaryCornerNormalizedEdgeProfile R z x e =
      rightBoundaryResolvedEdgeProfile R z x e := by
  unfold rightBoundaryCornerNormalizedEdgeProfile
  exact mul_div_cancel₀ _ (ne_of_gt (rightBoundaryCornerFactor_pos R hz))

theorem rightBoundaryResolvedColumnProfile_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    rightBoundaryResolvedColumnProfile R z (x + directionStep e) -
        rightBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedEdgeProfile R z x e := by
  fin_cases e
  · unfold rightBoundaryResolvedColumnProfile
    simp only [directionStep, Prod.fst_add, Prod.snd_add, add_zero,
      zero_add, rightBoundaryResolvedEdgeProfile]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show
      squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l (x.1 + 1) -
          squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l x.1 =
        squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
          (rightResolvedNormalWeight R l (x.1 + 1) -
            rightResolvedNormalWeight R l x.1) by ring]
    rw [rightResolvedNormalWeight_add_one_sub]
  · unfold rightBoundaryResolvedColumnProfile
    simp only [directionStep, Prod.fst_add, Prod.snd_add, add_zero,
      zero_add, rightBoundaryResolvedEdgeProfile]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show x.1 + -1 = x.1 - 1 by ring]
    rw [show
      squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l (x.1 - 1) -
          squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l x.1 =
        squareSineCoordinate R l z.2 * squareSineCoordinate R l x.2 *
          (rightResolvedNormalWeight R l (x.1 - 1) -
            rightResolvedNormalWeight R l x.1) by ring]
    rw [rightResolvedNormalWeight_sub_one_sub]
  · unfold rightBoundaryResolvedColumnProfile
    simp only [directionStep, Prod.fst_add, Prod.snd_add, add_zero,
      zero_add, rightBoundaryResolvedEdgeProfile]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show
      squareSineCoordinate R l z.2 *
            squareSineCoordinate R l (x.2 + 1) *
            rightResolvedNormalWeight R l x.1 -
          squareSineCoordinate R l z.2 *
            squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l x.1 =
        squareSineCoordinate R l z.2 *
          (squareSineCoordinate R l (x.2 + 1) -
            squareSineCoordinate R l x.2) *
          rightResolvedNormalWeight R l x.1 by ring]
    rw [squareSineCoordinate_add_one_sub]
  · unfold rightBoundaryResolvedColumnProfile
    simp only [directionStep, Prod.fst_add, Prod.snd_add, add_zero,
      zero_add, rightBoundaryResolvedEdgeProfile]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show x.2 + -1 = x.2 - 1 by ring]
    rw [show
      squareSineCoordinate R l z.2 *
            squareSineCoordinate R l (x.2 - 1) *
            rightResolvedNormalWeight R l x.1 -
          squareSineCoordinate R l z.2 *
            squareSineCoordinate R l x.2 *
            rightResolvedNormalWeight R l x.1 =
        squareSineCoordinate R l z.2 *
          (squareSineCoordinate R l (x.2 - 1) -
            squareSineCoordinate R l x.2) *
          rightResolvedNormalWeight R l x.1 by ring]
    rw [squareSineCoordinate_sub_one_sub]

theorem rightBoundaryCornerNormalizedColumnProfile_edge_sub
    (R : ℕ) {z x : Site} (e : Direction) :
    rightBoundaryCornerNormalizedColumnProfile R z (x + directionStep e) -
        rightBoundaryCornerNormalizedColumnProfile R z x =
      rightBoundaryCornerNormalizedEdgeProfile R z x e := by
  unfold rightBoundaryCornerNormalizedColumnProfile
  unfold rightBoundaryCornerNormalizedEdgeProfile
  rw [← sub_div]
  rw [rightBoundaryResolvedColumnProfile_edge_sub]

theorem rightBoundaryCornerNormalizedEdgeProfile_eq_sum
    (R : ℕ) (z x : Site) (e : Direction) :
    rightBoundaryCornerNormalizedEdgeProfile R z x e =
      ∑ l : Fin (2 * R + 1),
        rightBoundaryCornerNormalizedEdgeMode R z x e l := by
  rw [← rightBoundaryCornerNormalizedColumnProfile_edge_sub]
  rw [rightBoundaryCornerNormalizedColumnProfile_eq_sum]
  rw [rightBoundaryCornerNormalizedColumnProfile_eq_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  unfold rightBoundaryCornerNormalizedEdgeMode
  ring

theorem abs_rightBoundaryCornerNormalizedEdgeMode_east_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r)
    (hxe : x + directionStep (0 : Direction) ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerNormalizedEdgeMode R z x (0 : Direction) l| ≤
      32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℝ := (((l : ℕ) + 1 : ℕ) : ℝ)
  let L : ℝ := R + 1
  have hdir : directionStep (0 : Direction) = ((1, 0) : Site) := rfl
  rw [hdir] at hxe
  have hr_le : r ≤ R := by omega
  have hxsmall := Finset.mem_product.mp hx
  have hxesm := Finset.mem_product.mp hxe
  simp only [Finset.mem_Icc] at hxsmall hxesm
  have hal : -(R : ℤ) ≤ x.1 := by omega
  have hau : x.1 + 1 ≤ (R : ℤ) := by
    have hau_r : x.1 + 1 ≤ (r : ℤ) := by
      simpa only [Prod.fst_add] using hxesm.1.2
    exact hau_r.trans (by exact_mod_cast hr_le)
  have hratio := abs_rightBoundaryCornerModeRatio_le R hz l
  have hsine : |squareSineCoordinate R l x.2| ≤ 1 := by
    unfold squareSineCoordinate
    exact Real.abs_sin_le_one _
  have hdiff := abs_rightResolvedNormalWeight_add_one_sub_le R l hal hau
  have hgamma : normalDecay R l ≤ 2 * q / L :=
    (normalDecay_le_squareSineAngle R l).trans (by
      simpa only [q, L] using squareSineAngle_le_two_mul_mode_div R l)
  have hL : 0 < L := by dsimp [L]; positivity
  have hcoef : (16 * L) * normalDecay R l ≤ 32 * q := by
    calc
      (16 * L) * normalDecay R l ≤ (16 * L) * (2 * q / L) := by
        gcongr
      _ = 32 * q := by field_simp [ne_of_gt hL]; ring
  have hpow := exp_neg_normalDecay_distance_le_four_fifths_pow
    r R hxe hrR l
  unfold rightBoundaryCornerNormalizedEdgeMode
  rw [hdir]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [show rightBoundaryCornerModeRatio R z l *
      (squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l (x.1 + 1) -
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1) =
      rightBoundaryCornerModeRatio R z l * squareSineCoordinate R l x.2 *
        (rightResolvedNormalWeight R l (x.1 + 1) -
          rightResolvedNormalWeight R l x.1) by ring]
  rw [abs_mul, abs_mul]
  calc
    |rightBoundaryCornerModeRatio R z l| *
          |squareSineCoordinate R l x.2| *
          |rightResolvedNormalWeight R l (x.1 + 1) -
            rightResolvedNormalWeight R l x.1| ≤
        q * 1 * ((16 * L) * normalDecay R l *
          Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (((x.1 + 1 : ℤ) : ℝ))))) := by
      gcongr
    _ ≤ q * (32 * q) *
          Real.exp (-normalDecay R l *
            ((R + 1 : ℝ) - (((x.1 + 1 : ℤ) : ℝ)))) := by
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      let E : ℝ := Real.exp (-normalDecay R l *
        ((R + 1 : ℝ) - (((x.1 + 1 : ℤ) : ℝ))))
      have hE0 : 0 ≤ E := by dsimp [E]; exact (Real.exp_pos _).le
      change q * 1 * ((16 * L) * normalDecay R l * E) ≤
        q * (32 * q) * E
      calc
        q * 1 * ((16 * L) * normalDecay R l * E) =
            q * (((16 * L) * normalDecay R l) * E) := by ring
        _ ≤ q * ((32 * q) * E) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoef hE0) hq0
        _ = q * (32 * q) * E := by ring
    _ ≤ q * (32 * q) * (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      gcongr
      simpa only [Prod.fst_add] using hpow
    _ = 32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [q]
      ring

theorem abs_rightBoundaryCornerNormalizedEdgeMode_west_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r)
    (hxe : x + directionStep (1 : Direction) ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerNormalizedEdgeMode R z x (1 : Direction) l| ≤
      32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℝ := (((l : ℕ) + 1 : ℕ) : ℝ)
  let L : ℝ := R + 1
  have hdir : directionStep (1 : Direction) = ((-1, 0) : Site) := rfl
  rw [hdir] at hxe
  have hr_le : r ≤ R := by omega
  have hxsmall := Finset.mem_product.mp hx
  have hxesm := Finset.mem_product.mp hxe
  simp only [Finset.mem_Icc] at hxsmall hxesm
  have hal : -(R : ℤ) ≤ x.1 - 1 := by
    have hal_r : -(r : ℤ) ≤ x.1 - 1 := by
      have hraw := hxesm.1.1
      simp only [Prod.fst_add] at hraw
      omega
    have hneg : -(R : ℤ) ≤ -(r : ℤ) := by omega
    exact hneg.trans hal_r
  have hau : x.1 ≤ (R : ℤ) := by omega
  have hratio := abs_rightBoundaryCornerModeRatio_le R hz l
  have hsine : |squareSineCoordinate R l x.2| ≤ 1 := by
    unfold squareSineCoordinate
    exact Real.abs_sin_le_one _
  have hdiff := abs_rightResolvedNormalWeight_sub_one_sub_le R l hal hau
  have hgamma : normalDecay R l ≤ 2 * q / L :=
    (normalDecay_le_squareSineAngle R l).trans (by
      simpa only [q, L] using squareSineAngle_le_two_mul_mode_div R l)
  have hL : 0 < L := by dsimp [L]; positivity
  have hcoef : (16 * L) * normalDecay R l ≤ 32 * q := by
    calc
      (16 * L) * normalDecay R l ≤ (16 * L) * (2 * q / L) := by
        gcongr
      _ = 32 * q := by field_simp [ne_of_gt hL]; ring
  have hpow := exp_neg_normalDecay_distance_le_four_fifths_pow
    r R hx hrR l
  unfold rightBoundaryCornerNormalizedEdgeMode
  rw [hdir]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [show x.1 + -1 = x.1 - 1 by ring]
  rw [show rightBoundaryCornerModeRatio R z l *
      (squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l (x.1 - 1) -
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1) =
      rightBoundaryCornerModeRatio R z l * squareSineCoordinate R l x.2 *
        (rightResolvedNormalWeight R l (x.1 - 1) -
          rightResolvedNormalWeight R l x.1) by ring]
  rw [abs_mul, abs_mul]
  let E : ℝ := Real.exp (-normalDecay R l *
    ((R + 1 : ℝ) - (x.1 : ℝ)))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; exact (Real.exp_pos _).le
  calc
    |rightBoundaryCornerModeRatio R z l| *
          |squareSineCoordinate R l x.2| *
          |rightResolvedNormalWeight R l (x.1 - 1) -
            rightResolvedNormalWeight R l x.1| ≤
        q * 1 * ((16 * L) * normalDecay R l * E) := by
      dsimp only [E]
      gcongr
    _ = q * (((16 * L) * normalDecay R l) * E) := by ring
    _ ≤ q * ((32 * q) * E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef hE0) hq0
    _ = q * (32 * q) * E := by ring
    _ ≤ q * (32 * q) * (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [E]
      gcongr
    _ = 32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [q]
      ring

theorem abs_rightBoundaryCornerNormalizedEdgeMode_north_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r)
    (hxe : x + directionStep (2 : Direction) ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerNormalizedEdgeMode R z x (2 : Direction) l| ≤
      32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℝ := (((l : ℕ) + 1 : ℕ) : ℝ)
  let L : ℝ := R + 1
  have hdir : directionStep (2 : Direction) = ((0, 1) : Site) := rfl
  rw [hdir] at hxe
  have hr_le : r ≤ R := by omega
  have hxsmall := Finset.mem_product.mp hx
  simp only [Finset.mem_Icc] at hxsmall
  have hxl : -(R : ℤ) ≤ x.1 := by omega
  have hxu : x.1 ≤ (R : ℤ) := by omega
  have hratio := abs_rightBoundaryCornerModeRatio_le R hz l
  have hdiff := abs_squareSineCoordinate_add_one_sub_le_angle R l x.2
  have hweightPos := rightResolvedNormalWeight_pos R l hxl hxu
  have hweight := rightResolvedNormalWeight_le_exp_decay R l hxl hxu
  have hangle : squareSineAngle R l ≤ 2 * q / L := by
    simpa only [q, L] using squareSineAngle_le_two_mul_mode_div R l
  have hL : 0 < L := by dsimp [L]; positivity
  have hcoef : squareSineAngle R l * (8 * L) ≤ 16 * q := by
    calc
      squareSineAngle R l * (8 * L) ≤ (2 * q / L) * (8 * L) := by
        gcongr
      _ = 16 * q := by field_simp [ne_of_gt hL]; ring
  have hpow := exp_neg_normalDecay_distance_le_four_fifths_pow
    r R hx hrR l
  unfold rightBoundaryCornerNormalizedEdgeMode
  rw [hdir]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [show rightBoundaryCornerModeRatio R z l *
      (squareSineCoordinate R l (x.2 + 1) * rightResolvedNormalWeight R l x.1 -
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1) =
      rightBoundaryCornerModeRatio R z l *
        (squareSineCoordinate R l (x.2 + 1) - squareSineCoordinate R l x.2) *
        rightResolvedNormalWeight R l x.1 by ring]
  rw [abs_mul, abs_mul, abs_of_pos hweightPos]
  let E : ℝ := Real.exp (-normalDecay R l *
    ((R + 1 : ℝ) - (x.1 : ℝ)))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqAngle0 : 0 ≤ q * squareSineAngle R l :=
    mul_nonneg hq0 (squareSineAngle_pos R l).le
  have hE0 : 0 ≤ E := by dsimp [E]; exact (Real.exp_pos _).le
  calc
    |rightBoundaryCornerModeRatio R z l| *
          |squareSineCoordinate R l (x.2 + 1) -
            squareSineCoordinate R l x.2| *
          rightResolvedNormalWeight R l x.1 ≤
        q * squareSineAngle R l * ((8 * L) * E) := by
      dsimp only [E]
      gcongr
    _ = q * (squareSineAngle R l * (8 * L)) * E := by ring
    _ ≤ q * (16 * q) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef hq0) hE0
    _ ≤ q * (16 * q) * (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [E]
      gcongr
    _ ≤ 32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [q]
      have hp : 0 ≤ (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by positivity
      nlinarith [sq_nonneg ((((l : ℕ) + 1 : ℕ) : ℝ))]

theorem abs_rightBoundaryCornerNormalizedEdgeMode_south_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r)
    (hxe : x + directionStep (3 : Direction) ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerNormalizedEdgeMode R z x (3 : Direction) l| ≤
      32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℝ := (((l : ℕ) + 1 : ℕ) : ℝ)
  let L : ℝ := R + 1
  have hdir : directionStep (3 : Direction) = ((0, -1) : Site) := rfl
  rw [hdir] at hxe
  have hr_le : r ≤ R := by omega
  have hxsmall := Finset.mem_product.mp hx
  simp only [Finset.mem_Icc] at hxsmall
  have hxl : -(R : ℤ) ≤ x.1 := by omega
  have hxu : x.1 ≤ (R : ℤ) := by omega
  have hratio := abs_rightBoundaryCornerModeRatio_le R hz l
  have hdiff := abs_squareSineCoordinate_sub_one_sub_le_angle R l x.2
  have hweightPos := rightResolvedNormalWeight_pos R l hxl hxu
  have hweight := rightResolvedNormalWeight_le_exp_decay R l hxl hxu
  have hangle : squareSineAngle R l ≤ 2 * q / L := by
    simpa only [q, L] using squareSineAngle_le_two_mul_mode_div R l
  have hL : 0 < L := by dsimp [L]; positivity
  have hcoef : squareSineAngle R l * (8 * L) ≤ 16 * q := by
    calc
      squareSineAngle R l * (8 * L) ≤ (2 * q / L) * (8 * L) := by
        gcongr
      _ = 16 * q := by field_simp [ne_of_gt hL]; ring
  have hpow := exp_neg_normalDecay_distance_le_four_fifths_pow
    r R hx hrR l
  unfold rightBoundaryCornerNormalizedEdgeMode
  rw [hdir]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [show x.2 + -1 = x.2 - 1 by ring]
  rw [show rightBoundaryCornerModeRatio R z l *
      (squareSineCoordinate R l (x.2 - 1) * rightResolvedNormalWeight R l x.1 -
        squareSineCoordinate R l x.2 * rightResolvedNormalWeight R l x.1) =
      rightBoundaryCornerModeRatio R z l *
        (squareSineCoordinate R l (x.2 - 1) - squareSineCoordinate R l x.2) *
        rightResolvedNormalWeight R l x.1 by ring]
  rw [abs_mul, abs_mul, abs_of_pos hweightPos]
  let E : ℝ := Real.exp (-normalDecay R l *
    ((R + 1 : ℝ) - (x.1 : ℝ)))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqAngle0 : 0 ≤ q * squareSineAngle R l :=
    mul_nonneg hq0 (squareSineAngle_pos R l).le
  have hE0 : 0 ≤ E := by dsimp [E]; exact (Real.exp_pos _).le
  calc
    |rightBoundaryCornerModeRatio R z l| *
          |squareSineCoordinate R l (x.2 - 1) -
            squareSineCoordinate R l x.2| *
          rightResolvedNormalWeight R l x.1 ≤
        q * squareSineAngle R l * ((8 * L) * E) := by
      dsimp only [E]
      gcongr
    _ = q * (squareSineAngle R l * (8 * L)) * E := by ring
    _ ≤ q * (16 * q) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef hq0) hE0
    _ ≤ q * (16 * q) * (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [E]
      gcongr
    _ ≤ 32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      dsimp only [q]
      have hp : 0 ≤ (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by positivity
      nlinarith [sq_nonneg ((((l : ℕ) + 1 : ℕ) : ℝ))]

theorem abs_rightBoundaryCornerNormalizedEdgeMode_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r) (e : Direction)
    (hxe : x + directionStep e ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (l : Fin (2 * R + 1)) :
    |rightBoundaryCornerNormalizedEdgeMode R z x e l| ≤
      32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  fin_cases e
  · exact abs_rightBoundaryCornerNormalizedEdgeMode_east_le
      r R hz hx hxe hrR l
  · exact abs_rightBoundaryCornerNormalizedEdgeMode_west_le
      r R hz hx hxe hrR l
  · exact abs_rightBoundaryCornerNormalizedEdgeMode_north_le
      r R hz hx hxe hrR l
  · exact abs_rightBoundaryCornerNormalizedEdgeMode_south_le
      r R hz hx hxe hrR l

/-- The complete normalized boundary-edge numerator is uniformly bounded.
All cancellation needed at a corner has already been retained in the common
first-sine normalization; the remaining estimate is an absolutely summable
one-dimensional mode envelope. -/
theorem abs_rightBoundaryCornerNormalizedEdgeProfile_le
    (r R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk r) (e : Direction)
    (hxe : x + directionStep e ∈ squareDisk r)
    (hrR : 2 * r ≤ R) :
    |rightBoundaryCornerNormalizedEdgeProfile R z x e| ≤ 6400 := by
  rw [rightBoundaryCornerNormalizedEdgeProfile_eq_sum]
  calc
    |∑ l : Fin (2 * R + 1),
        rightBoundaryCornerNormalizedEdgeMode R z x e l| ≤
      ∑ l : Fin (2 * R + 1),
        |rightBoundaryCornerNormalizedEdgeMode R z x e l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin (2 * R + 1),
        32 * (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact abs_rightBoundaryCornerNormalizedEdgeMode_le
        r R hz hx e hxe hrR l
    _ = 32 * (∑ l : Fin (2 * R + 1),
        (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2 *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ 32 * 200 := by
      gcongr
      exact sum_fin_succ_sq_mul_four_fifths_pow_le (2 * R + 1)
    _ = 6400 := by norm_num

def reflectFirstSite (x : Site) : Site := (-x.1, x.2)

def swapSiteCoordinates (x : Site) : Site := (x.2, x.1)

def reflectFirstDirection (e : Direction) : Direction :=
  match e.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | _ => 3

def swapDirectionCoordinates (e : Direction) : Direction :=
  match e.1 with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | _ => 1

theorem reflectFirstSite_add_directionStep (x : Site) (e : Direction) :
    reflectFirstSite (x + directionStep e) =
      reflectFirstSite x + directionStep (reflectFirstDirection e) := by
  fin_cases e <;>
    simp [reflectFirstSite, reflectFirstDirection, directionStep] <;> ring

theorem swapSiteCoordinates_add_directionStep (x : Site) (e : Direction) :
    swapSiteCoordinates (x + directionStep e) =
      swapSiteCoordinates x + directionStep (swapDirectionCoordinates e) := by
  fin_cases e <;> simp [swapSiteCoordinates, swapDirectionCoordinates, directionStep]

theorem leftBoundaryResolvedColumnProfile_eq_right_reflect
    (R : ℕ) (z x : Site) :
    leftBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedColumnProfile R
        (reflectFirstSite z) (reflectFirstSite x) := by
  unfold leftBoundaryResolvedColumnProfile
  unfold rightBoundaryResolvedColumnProfile
  apply Finset.sum_congr rfl
  intro l hl
  unfold leftResolvedNormalWeight rightResolvedNormalWeight reflectFirstSite
  dsimp
  rw [show (((-x.1 : ℤ) : ℝ) + (R + 1 : ℝ)) =
      (R + 1 : ℝ) - (x.1 : ℝ) by push_cast; ring]

theorem topBoundaryResolvedColumnProfile_eq_right_swap
    (R : ℕ) (z x : Site) :
    topBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedColumnProfile R
        (swapSiteCoordinates z) (swapSiteCoordinates x) := by
  rfl

theorem bottomBoundaryResolvedColumnProfile_eq_right_reflect_swap
    (R : ℕ) (z x : Site) :
    bottomBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedColumnProfile R
        (reflectFirstSite (swapSiteCoordinates z))
        (reflectFirstSite (swapSiteCoordinates x)) := by
  unfold bottomBoundaryResolvedColumnProfile
  unfold rightBoundaryResolvedColumnProfile
  apply Finset.sum_congr rfl
  intro k hk
  unfold leftResolvedNormalWeight rightResolvedNormalWeight
  unfold reflectFirstSite swapSiteCoordinates
  dsimp
  rw [show (((-x.2 : ℤ) : ℝ) + (R + 1 : ℝ)) =
      (R + 1 : ℝ) - (x.2 : ℝ) by push_cast; ring]

theorem leftBoundaryResolvedColumnProfile_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    leftBoundaryResolvedColumnProfile R z (x + directionStep e) -
        leftBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedEdgeProfile R
        (reflectFirstSite z) (reflectFirstSite x)
        (reflectFirstDirection e) := by
  rw [leftBoundaryResolvedColumnProfile_eq_right_reflect,
    leftBoundaryResolvedColumnProfile_eq_right_reflect,
    reflectFirstSite_add_directionStep,
    rightBoundaryResolvedColumnProfile_edge_sub]

theorem topBoundaryResolvedColumnProfile_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    topBoundaryResolvedColumnProfile R z (x + directionStep e) -
        topBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedEdgeProfile R
        (swapSiteCoordinates z) (swapSiteCoordinates x)
        (swapDirectionCoordinates e) := by
  rw [topBoundaryResolvedColumnProfile_eq_right_swap,
    topBoundaryResolvedColumnProfile_eq_right_swap,
    swapSiteCoordinates_add_directionStep,
    rightBoundaryResolvedColumnProfile_edge_sub]

theorem bottomBoundaryResolvedColumnProfile_edge_sub
    (R : ℕ) (z x : Site) (e : Direction) :
    bottomBoundaryResolvedColumnProfile R z (x + directionStep e) -
        bottomBoundaryResolvedColumnProfile R z x =
      rightBoundaryResolvedEdgeProfile R
        (reflectFirstSite (swapSiteCoordinates z))
        (reflectFirstSite (swapSiteCoordinates x))
        (reflectFirstDirection (swapDirectionCoordinates e)) := by
  rw [bottomBoundaryResolvedColumnProfile_eq_right_reflect_swap,
    bottomBoundaryResolvedColumnProfile_eq_right_reflect_swap,
    swapSiteCoordinates_add_directionStep,
    reflectFirstSite_add_directionStep,
    rightBoundaryResolvedColumnProfile_edge_sub]

/-- Isometry sending the face selected by `p` to the right face. -/
def canonicalRightFaceSite (p : Direction) (x : Site) : Site :=
  match p.1 with
  | 0 => x
  | 1 => reflectFirstSite x
  | 2 => swapSiteCoordinates x
  | _ => reflectFirstSite (swapSiteCoordinates x)

def canonicalRightFaceDirection (p e : Direction) : Direction :=
  match p.1 with
  | 0 => e
  | 1 => reflectFirstDirection e
  | 2 => swapDirectionCoordinates e
  | _ => reflectFirstDirection (swapDirectionCoordinates e)

theorem canonicalRightFaceSite_mem_squareDisk_iff
    (R : ℕ) (p : Direction) (x : Site) :
    canonicalRightFaceSite p x ∈ squareDisk R ↔ x ∈ squareDisk R := by
  fin_cases p <;>
    simp [canonicalRightFaceSite, reflectFirstSite, swapSiteCoordinates,
      squareDisk] <;> omega

theorem canonicalRightFaceSite_add_directionStep
    (p e : Direction) (x : Site) :
    canonicalRightFaceSite p (x + directionStep e) =
      canonicalRightFaceSite p x +
        directionStep (canonicalRightFaceDirection p e) := by
  fin_cases p <;> fin_cases e <;>
    simp [canonicalRightFaceSite, canonicalRightFaceDirection,
      reflectFirstSite, swapSiteCoordinates, reflectFirstDirection,
      swapDirectionCoordinates, directionStep] <;> ring

/-- The resolved profile selected by the crossed face. -/
noncomputable def exitPredecessorResolvedColumnProfile
    (R : ℕ) (p : Direction) (y x : Site) : ℝ :=
  let z := y - directionStep p
  match p.1 with
  | 0 => rightBoundaryResolvedColumnProfile R z x
  | 1 => leftBoundaryResolvedColumnProfile R z x
  | 2 => topBoundaryResolvedColumnProfile R z x
  | _ => bottomBoundaryResolvedColumnProfile R z x

theorem exitPredecessorResolvedColumnProfile_eq_canonicalRight
    (R : ℕ) (p : Direction) (y x : Site) :
    exitPredecessorResolvedColumnProfile R p y x =
      rightBoundaryResolvedColumnProfile R
        (canonicalRightFaceSite p (y - directionStep p))
        (canonicalRightFaceSite p x) := by
  fin_cases p
  · rfl
  · exact leftBoundaryResolvedColumnProfile_eq_right_reflect _ _ _
  · exact topBoundaryResolvedColumnProfile_eq_right_swap _ _ _
  · exact bottomBoundaryResolvedColumnProfile_eq_right_reflect_swap _ _ _

/-- Every face and every lattice edge is reduced exactly to the same
right-face signed tangential edge sum. -/
theorem exitPredecessorResolvedColumnProfile_edge_sub_eq_canonicalRight
    (R : ℕ) (p : Direction) (y x : Site) (e : Direction) :
    exitPredecessorResolvedColumnProfile R p y
          (x + directionStep e) -
        exitPredecessorResolvedColumnProfile R p y x =
      rightBoundaryResolvedEdgeProfile R
        (canonicalRightFaceSite p (y - directionStep p))
        (canonicalRightFaceSite p x)
        (canonicalRightFaceDirection p e) := by
  rw [exitPredecessorResolvedColumnProfile_eq_canonicalRight,
    exitPredecessorResolvedColumnProfile_eq_canonicalRight,
    canonicalRightFaceSite_add_directionStep,
    rightBoundaryResolvedColumnProfile_edge_sub]

/-- On the square, every normal-frequency column profile is definitionally
replaced by its exact hyperbolic quotient.  No absolute value enters this
rewrite, hence tangential corner cancellation is preserved. -/
theorem exitPredecessorColumnProfile_eq_resolved
    {R : ℕ} (p : Direction) (y : Site) {x : Site}
    (hx : x ∈ squareDisk R) :
    exitPredecessorColumnProfile R p y x =
      exitPredecessorResolvedColumnProfile R p y x := by
  have hx' :
      (-(R : ℤ) ≤ x.1 ∧ x.1 ≤ (R : ℤ)) ∧
        (-(R : ℤ) ≤ x.2 ∧ x.2 ≤ (R : ℤ)) := by
    simpa [squareDisk] using hx
  fin_cases p
  · simp only [exitPredecessorColumnProfile,
      exitPredecessorResolvedColumnProfile]
    unfold rightBoundaryColumnProfile rightBoundaryResolvedColumnProfile
    unfold rightResolvedNormalWeight
    apply Finset.sum_congr rfl
    intro l hl
    rw [rightBoundaryNormalResolvent_eq_sinh_ratio
      R l hx'.1.1 hx'.1.2]
  · simp only [exitPredecessorColumnProfile,
      exitPredecessorResolvedColumnProfile]
    unfold leftBoundaryColumnProfile leftBoundaryResolvedColumnProfile
    unfold leftResolvedNormalWeight
    apply Finset.sum_congr rfl
    intro l hl
    rw [leftBoundaryNormalResolvent_eq_sinh_ratio
      R l hx'.1.1 hx'.1.2]
  · simp only [exitPredecessorColumnProfile,
      exitPredecessorResolvedColumnProfile]
    unfold topBoundaryColumnProfile topBoundaryResolvedColumnProfile
    unfold rightResolvedNormalWeight
    apply Finset.sum_congr rfl
    intro k hk
    rw [topBoundaryNormalResolvent_eq_sinh_ratio
      R k hx'.2.1 hx'.2.2]
  · simp only [exitPredecessorColumnProfile,
      exitPredecessorResolvedColumnProfile]
    unfold bottomBoundaryColumnProfile bottomBoundaryResolvedColumnProfile
    unfold leftResolvedNormalWeight
    apply Finset.sum_congr rfl
    intro k hk
    rw [bottomBoundaryNormalResolvent_eq_sinh_ratio
      R k hx'.2.1 hx'.2.2]

/-- Direct Green-kernel identification of the fully resolved signed sum. -/
theorem diskGreen_toReal_exit_predecessor_eq_resolvedColumnProfile
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    (diskGreen R (y - directionStep p) x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        exitPredecessorResolvedColumnProfile R p y x := by
  rw [diskGreen_toReal_exit_predecessor_eq_columnProfile p hy hp hx,
    exitPredecessorColumnProfile_eq_resolved p y hx]

theorem exitPredecessorResolvedColumnProfile_nonneg
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    0 ≤ exitPredecessorResolvedColumnProfile R p y x := by
  have hgreen :
      0 ≤ (diskGreen R (y - directionStep p) x).toReal :=
    ENNReal.toReal_nonneg
  rw [diskGreen_toReal_exit_predecessor_eq_resolvedColumnProfile
    p hy hp hx] at hgreen
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hgreen

theorem diskGreen_toReal_exit_predecessor_target_edge_sub_eq_resolvedColumnProfile
    {R : ℕ} {y x : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R)
    (e : Direction) (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R (y - directionStep p)
          (x + directionStep e)).toReal -
        (diskGreen R (y - directionStep p) x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        (exitPredecessorResolvedColumnProfile R p y
            (x + directionStep e) -
          exitPredecessorResolvedColumnProfile R p y x) := by
  rw [diskGreen_toReal_exit_predecessor_eq_resolvedColumnProfile
      p hy hp hxe,
    diskGreen_toReal_exit_predecessor_eq_resolvedColumnProfile
      p hy hp hx]
  ring

theorem topBoundaryNormalResolvent_pos
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    0 < topBoundaryNormalResolvent R k b := by
  rw [topBoundaryNormalResolvent_eq_rightBoundaryNormalResolvent]
  exact rightBoundaryNormalResolvent_pos R k hbl hbu

theorem bottomBoundaryNormalResolvent_pos
    (R : ℕ) (k : Fin (2 * R + 1)) {b : ℤ}
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    0 < bottomBoundaryNormalResolvent R k b := by
  rw [bottomBoundaryNormalResolvent_eq_leftBoundaryNormalResolvent]
  exact leftBoundaryNormalResolvent_pos R k hbl hbu

end Erdos1166.KilledGreen
