import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierWeights

/-!
# Rapid Fourier decay from actual smoothness

Repeated application of the coordinate operators `1 - Dᵢ²` gives the
positive Fourier multiplier `∏ i, (1 + (2π kᵢ)²)`. The norm of the resulting
actual smooth function bounds the Fourier coefficients. No decay estimate
or Fourier reconstruction is assumed.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual coordinate elliptic operator `1 - Dᵢ²`. -/
def torusCoordinateElliptic (f : SmoothTorusFunction d) (i : d) :
    SmoothTorusFunction d where
  toContinuousMap := f.toContinuousMap -
    (torusDirectionalDerivative (torusDirectionalDerivative f (Pi.single i 1))
      (Pi.single i 1)).toContinuousMap
  smooth_lift := f.smooth_lift.sub
    (torusDirectionalDerivative (torusDirectionalDerivative f (Pi.single i 1))
      (Pi.single i 1)).smooth_lift

private theorem coordinate_multiplier_identity (t : ℝ) :
    (1 : ℂ) - (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2 =
      ((1 + (2 * Real.pi * t) ^ 2 : ℝ) : ℂ) := by
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem torusCoordinateElliptic_coeff (f : SmoothTorusFunction d) (i : d) (k : d → ℤ) :
    mFourierCoeff (torusCoordinateElliptic f i) k =
      ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ) * mFourierCoeff f k := by
  change mFourierCoeff (f.toContinuousMap -
    (torusDirectionalDerivative (torusDirectionalDerivative f (Pi.single i 1))
      (Pi.single i 1)).toContinuousMap) k = _
  rw [torusFourierCoeff_sub]
  rw [mFourierCoeff_torusCoordinateDerivative, mFourierCoeff_torusCoordinateDerivative]
  have h := coordinate_multiplier_identity (k i : ℝ)
  simp only [Complex.ofReal_intCast] at h
  rw [← h]
  ring

/-- Apply each member of a finite list of actual coordinate elliptic operators. -/
def torusEllipticList : List d → SmoothTorusFunction d → SmoothTorusFunction d
  | [], f => f
  | i :: s, f => torusCoordinateElliptic (torusEllipticList s f) i

theorem torusEllipticList_coeff (s : List d) (f : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (torusEllipticList s f) k =
      (s.map (fun i => ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ))).prod *
        mFourierCoeff f k := by
  induction s with
  | nil => simp [torusEllipticList]
  | cons i s ih =>
    rw [torusEllipticList, torusCoordinateElliptic_coeff, ih, List.map_cons,
      List.prod_cons]
    ring

/-- One complete pass through all coordinates. -/
def torusEllipticOperator (f : SmoothTorusFunction d) : SmoothTorusFunction d :=
  torusEllipticList Finset.univ.toList f

theorem torusEllipticOperator_coeff (f : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (torusEllipticOperator f) k =
      (fourierEllipticWeight k : ℂ) * mFourierCoeff f k := by
  rw [torusEllipticOperator, torusEllipticList_coeff]
  congr 1
  simp [fourierEllipticWeight]

/-- Arbitrarily many passes preserve actual smoothness. -/
def torusEllipticPower : ℕ → SmoothTorusFunction d → SmoothTorusFunction d
  | 0, f => f
  | n + 1, f => torusEllipticOperator (torusEllipticPower n f)

theorem torusEllipticPower_coeff (n : ℕ) (f : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (torusEllipticPower n f) k =
      (fourierEllipticWeight k : ℂ) ^ n * mFourierCoeff f k := by
  induction n with
  | zero => simp [torusEllipticPower]
  | succ n ih =>
    rw [torusEllipticPower, torusEllipticOperator_coeff, ih, pow_succ]
    ring

omit [DecidableEq d] in
/-- Every smooth torus function has arbitrarily rapid product decay. The
constant is the norm of an explicitly constructed differential operator. -/
theorem torusFourierCoeff_rapidDecay (f : SmoothTorusFunction d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : d → ℤ,
      ‖mFourierCoeff f k‖ ≤ C / fourierEllipticWeight k ^ n := by
  classical
  refine ⟨‖(torusEllipticPower n f).toContinuousMap‖, norm_nonneg _, fun k => ?_⟩
  have h := torusFourierCoeff_norm_le (torusEllipticPower n f).toContinuousMap k
  change ‖mFourierCoeff (torusEllipticPower n f) k‖ ≤ _ at h
  rw [torusEllipticPower_coeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (fourierEllipticWeight_pos k)] at h
  apply (le_div_iff₀ (pow_pos (fourierEllipticWeight_pos k) n)).mpr
  simpa only [mul_comm] using h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
