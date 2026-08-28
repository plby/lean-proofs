import Wikipedia.HopfProblem.SpecialPeriodsLocal
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Elliptic rotations and covariance of the concrete local periods

The local period maps of `SpecialPeriodsLocal` come with actual analytic
order-three and order-four rotations of their base discs.  We prove their
period-matrix covariance with the integral matrices of §2, in the orientation
needed to transport the flat logarithmic action to complex coordinates.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods

def discZero : Disc := ⟨0, by simp [unitDisc]⟩

@[simp] theorem discZero_val : (discZero : ℂ) = 0 := rfl

/-- Multiplication by a unit-norm scalar on the actual open disc. -/
def discScalar (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) : Disc :=
  ⟨c * z, by
    have hn : ‖c * (z : ℂ)‖ < 1 := by simpa [norm_mul, hc] using disc_norm_lt_one z
    simpa [unitDisc] using hn⟩

@[simp] theorem discScalar_val (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) :
    (discScalar c hc z : ℂ) = c * z := rfl

theorem discScalar_holomorphic (c : ℂ) (hc : ‖c‖ = 1) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) := by
  intro z
  have he : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun w : Disc => (discScalar c hc w : ℂ)) z ↔
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_const.mul contMDiff_subtype_val) z)

theorem discScalar_iterate_val (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (z : Disc) :
    ((discScalar c hc)^[n] z : ℂ) = c ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', discScalar_val, ih, pow_succ']
    rw [mul_assoc]

def discRotateThree : Disc → Disc := discScalar (-rho) (by simpa using norm_rho)

def discRotateFour : Disc → Disc := discScalar (-Complex.I) (by simp)

@[simp] theorem discRotateThree_val (z : Disc) :
    (discRotateThree z : ℂ) = rotateThree z := rfl

@[simp] theorem discRotateFour_val (z : Disc) :
    (discRotateFour z : ℂ) = rotateFour z := rfl

theorem discRotateThree_holomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateThree :=
  discScalar_holomorphic _ _

theorem discRotateFour_holomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateFour :=
  discScalar_holomorphic _ _

theorem discRotateThree_cube (z : Disc) :
    discRotateThree (discRotateThree (discRotateThree z)) = z :=
  Subtype.ext (rotateThree_cube z)

theorem discRotateFour_fourth (z : Disc) :
    discRotateFour (discRotateFour (discRotateFour (discRotateFour z))) = z :=
  Subtype.ext (rotateFour_fourth z)

theorem discRotateThree_iterate_order : discRotateThree^[3] = id := by
  funext z
  exact discRotateThree_cube z

theorem discRotateFour_iterate_order : discRotateFour^[4] = id := by
  funext z
  exact discRotateFour_fourth z

/-- The first actual disc rotation as a biholomorphism. -/
def threeRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω where
  toFun := discRotateThree
  invFun := discRotateThree ∘ discRotateThree
  left_inv := discRotateThree_cube
  right_inv := discRotateThree_cube
  contMDiff_toFun := discRotateThree_holomorphic
  contMDiff_invFun := discRotateThree_holomorphic.comp discRotateThree_holomorphic

/-- The second actual disc rotation as a biholomorphism. -/
def fourRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω where
  toFun := discRotateFour
  invFun := discRotateFour ∘ discRotateFour ∘ discRotateFour
  left_inv := discRotateFour_fourth
  right_inv := discRotateFour_fourth
  contMDiff_toFun := discRotateFour_holomorphic
  contMDiff_invFun := discRotateFour_holomorphic.comp
    (discRotateFour_holomorphic.comp discRotateFour_holomorphic)

theorem neg_rho_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 3) : (-rho) ^ n ≠ 1 := by
  interval_cases n
  · simp only [pow_one]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.neg_im, Complex.one_im] at hh
    linarith [rho_im_pos]
  · rw [neg_sq, rho_sq]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
    linarith [rho_im_pos]

theorem neg_I_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 4) : (-Complex.I) ^ n ≠ 1 := by
  interval_cases n
  · intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  · norm_num
  · intro he
    have hh := congrArg Complex.im he
    norm_num [pow_succ] at hh

theorem discScalar_iterate_fixed_iff (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (hn : c ^ n ≠ 1)
    (z : Disc) : (discScalar c hc)^[n] z = z ↔ z = discZero := by
  constructor
  · intro he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    rw [discScalar_iterate_val] at hv
    by_contra hz
    apply hn
    exact mul_right_cancel₀ hz (by simpa using hv)
  · intro he
    subst z
    apply Subtype.ext
    rw [discScalar_iterate_val]
    simp

/-- No nontrivial power of the first base rotation fixes a nonzero point. -/
theorem discRotateThree_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3) (z : Disc) :
    discRotateThree^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_rho_pow_ne_one hn hn') z

/-- No nontrivial power of the second base rotation fixes a nonzero point. -/
theorem discRotateFour_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4) (z : Disc) :
    discRotateFour^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_I_pow_ne_one hn hn') z

theorem threePeriodMap_rotate (z : Disc) :
    threePeriodMap.point (discRotateThree z) = (threePeriodMap.point z).step₁ :=
  Subtype.ext (localThree_rotate (disc_norm_lt_one z))

theorem fourPeriodMap_rotate (z : Disc) :
    fourPeriodMap.point (discRotateFour z) = (fourPeriodMap.point z).step₂ :=
  Subtype.ext (localFour_rotate (disc_norm_lt_one z))

/-- Covariance in the direction used for the flat logarithmic action:
`Π(g z) A₁ = R₁(z) Π(z)`. -/
theorem threePeriodMap_matrix_covariance (z : Disc) :
    (threePeriodMap.point (discRotateThree z)).val.matrix * A₁.map (Int.castRingHom ℂ) =
      (threePeriodMap.point z).val.R₁ * (threePeriodMap.point z).val.matrix := by
  rw [threePeriodMap_rotate]
  change (threePeriodMap.point z).val.step₁.matrix * _ = _
  rw [PeriodPoint.step₁_matrix _ ((threePeriodMap.point z).val.τ_ne_zero
    (threePeriodMap.point z).property.1), Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

/-- Covariance in the direction used for the flat logarithmic action:
`Π(g z) A₂ = R₂(z) Π(z)`. -/
theorem fourPeriodMap_matrix_covariance (z : Disc) :
    (fourPeriodMap.point (discRotateFour z)).val.matrix * A₂.map (Int.castRingHom ℂ) =
      (fourPeriodMap.point z).val.R₂ * (fourPeriodMap.point z).val.matrix := by
  rw [fourPeriodMap_rotate]
  change (fourPeriodMap.point z).val.step₂.matrix * _ = _
  rw [PeriodPoint.step₂_matrix _ ((fourPeriodMap.point z).val.τ_ne_zero
    (fourPeriodMap.point z).property.1), Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

end Wikipedia.HopfProblem.SpecialPeriods
