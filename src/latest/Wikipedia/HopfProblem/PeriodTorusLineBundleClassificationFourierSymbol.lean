import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Int

/-!
# The genuine Dolbeault Fourier symbol on a period torus

Real frequencies are pulled through the inverse of the actual period
isomorphism. For the convention `∂̄ = (∂x + I ∂y) / 2`, the symbol of
`exp (2 π I ξ)` is `π (I ξ(eᵢ) - ξ(I eᵢ))`. Its nondegeneracy is proved from
the four real coordinate directions, rather than assumed as ellipticity.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex
open scoped BigOperators

/-- The real frequency functional in the actual period coordinates. -/
noncomputable def frequencyFunctional (p : PeriodDomain) (v : Fin 4 → ℝ) :
    ComplexPlane₂ →ₗ[ℝ] ℝ :=
  (∑ j : Fin 4, v j • (LinearMap.proj j : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)).comp
    (PeriodTorusTypeOneOne.periodEquiv p).symm.toLinearMap

@[simp]
theorem frequencyFunctional_apply (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    frequencyFunctional p v z =
      ∑ j : Fin 4, v j * ((PeriodTorusTypeOneOne.periodEquiv p).symm z) j := by
  simp [frequencyFunctional, smul_eq_mul]

@[simp]
theorem frequencyFunctional_periodEquiv (p : PeriodDomain) (v x : Fin 4 → ℝ) :
    frequencyFunctional p v (PeriodTorusTypeOneOne.periodEquiv p x) =
      ∑ j : Fin 4, v j * x j := by
  simp only [frequencyFunctional_apply, LinearEquiv.symm_apply_apply]

@[simp]
theorem frequencyFunctional_basis (p : PeriodDomain) (v : Fin 4 → ℝ) (j : Fin 4) :
    frequencyFunctional p v (p.basis j) = v j := by
  rw [← PeriodTorusTypeOneOne.periodEquiv_single, frequencyFunctional_periodEquiv]
  simp [Pi.single_apply]

theorem frequencyFunctional_add (p : PeriodDomain) (v w : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    frequencyFunctional p (v + w) z = frequencyFunctional p v z +
      frequencyFunctional p w z := by
  simp [frequencyFunctional_apply, add_mul, Finset.sum_add_distrib]

theorem frequencyFunctional_smul (p : PeriodDomain) (r : ℝ) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    frequencyFunctional p (r • v) z = r * frequencyFunctional p v z := by
  simp [frequencyFunctional_apply, Finset.mul_sum, mul_assoc]

/-- A real-linear functional is determined by the real and imaginary coordinate
directions of the complex plane. -/
theorem realLinear_eq_of_coordinate_values (ν μ : ComplexPlane₂ →ₗ[ℝ] ℝ)
    (hRe : ∀ i : Fin 2, ν (Pi.single i 1) = μ (Pi.single i 1))
    (hIm : ∀ i : Fin 2, ν (I • Pi.single i 1) = μ (I • Pi.single i 1)) :
    ν = μ := by
  apply LinearMap.ext
  intro z
  have hDirection (i : Fin 2) :
      ν (z i • Pi.single i 1) = μ (z i • Pi.single i 1) := by
    rw [PeriodTorusTypeOneOne.complex_smul_decomposition (z i) (Pi.single i 1)]
    simp only [map_add, map_smul, hRe, hIm]
  conv_lhs => rw [pi_eq_sum_univ' z, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' z, map_sum]
  exact Finset.sum_congr rfl (fun i _ => hDirection i)

/-- The Dolbeault Fourier symbol, bundled as an actual real-linear map. -/
noncomputable def dolbeaultSymbol (p : PeriodDomain) :
    (Fin 4 → ℝ) →ₗ[ℝ] ComplexPlane₂ where
  toFun v i := (Real.pi : ℂ) *
    (I * (frequencyFunctional p v (Pi.single i 1) : ℂ) -
      (frequencyFunctional p v (I • Pi.single i 1) : ℂ))
  map_add' v w := by
    funext i
    simp only [frequencyFunctional_add, Complex.ofReal_add, Pi.add_apply]
    ring
  map_smul' r v := by
    funext i
    simp only [frequencyFunctional_smul, Pi.smul_apply, RingHom.id_apply]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, mul_left_comm]

@[simp]
theorem dolbeaultSymbol_apply (p : PeriodDomain) (v : Fin 4 → ℝ) (i : Fin 2) :
    dolbeaultSymbol p v i = (Real.pi : ℂ) *
      (I * (frequencyFunctional p v (Pi.single i 1) : ℂ) -
        (frequencyFunctional p v (I • Pi.single i 1) : ℂ)) := rfl

@[simp]
theorem dolbeaultSymbol_re (p : PeriodDomain) (v : Fin 4 → ℝ) (i : Fin 2) :
    (dolbeaultSymbol p v i).re =
      -Real.pi * frequencyFunctional p v (I • Pi.single i 1) := by
  simp [dolbeaultSymbol_apply]

@[simp]
theorem dolbeaultSymbol_im (p : PeriodDomain) (v : Fin 4 → ℝ) (i : Fin 2) :
    (dolbeaultSymbol p v i).im =
      Real.pi * frequencyFunctional p v (Pi.single i 1) := by
  simp [dolbeaultSymbol_apply]

/-- The actual symbol loses no real frequency information. -/
theorem dolbeaultSymbol_injective (p : PeriodDomain) :
    Function.Injective (dolbeaultSymbol p) := by
  intro v w h
  have hRe (i : Fin 2) : frequencyFunctional p v (Pi.single i 1) =
      frequencyFunctional p w (Pi.single i 1) := by
    have hi := congrArg (fun s : ComplexPlane₂ => (s i).im) h
    rw [dolbeaultSymbol_im, dolbeaultSymbol_im] at hi
    exact mul_left_cancel₀ Real.pi_ne_zero hi
  have hIm (i : Fin 2) : frequencyFunctional p v (I • Pi.single i 1) =
      frequencyFunctional p w (I • Pi.single i 1) := by
    have hi := congrArg (fun s : ComplexPlane₂ => (s i).re) h
    rw [dolbeaultSymbol_re, dolbeaultSymbol_re] at hi
    exact mul_left_cancel₀ (neg_ne_zero.mpr Real.pi_ne_zero) hi
  have hFunctional := realLinear_eq_of_coordinate_values
    (frequencyFunctional p v) (frequencyFunctional p w) hRe hIm
  funext j
  have hj := LinearMap.congr_fun hFunctional (p.basis j)
  simpa only [frequencyFunctional_basis] using hj

theorem dolbeaultSymbol_ne_zero (p : PeriodDomain) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    dolbeaultSymbol p v ≠ 0 := by
  intro h
  apply hv
  apply dolbeaultSymbol_injective p
  simpa only [map_zero] using h

/-- Finite-dimensional injectivity supplies a genuine positive elliptic lower
bound for this period matrix. -/
theorem dolbeaultSymbol_exists_pos_lowerBound (p : PeriodDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin 4 → ℝ, c * ‖v‖ ≤ ‖dolbeaultSymbol p v‖ := by
  obtain ⟨K, _, hK⟩ :=
    (dolbeaultSymbol p).injective_iff_antilipschitz.mp (dolbeaultSymbol_injective p)
  exact antilipschitzWith_iff_exists_mul_le_norm.mp ⟨K, hK⟩

/-- Integer Fourier frequencies regarded as real period-coordinate covectors. -/
noncomputable def integerFrequency (k : Fin 4 → ℤ) : Fin 4 → ℝ :=
  fun j => (k j : ℝ)

@[simp]
theorem integerFrequency_apply (k : Fin 4 → ℤ) (j : Fin 4) :
    integerFrequency k j = (k j : ℝ) := rfl

@[simp]
theorem integerFrequency_zero : integerFrequency 0 = 0 := by
  funext j
  simp [integerFrequency]

theorem integerFrequency_injective : Function.Injective integerFrequency := by
  intro k l h
  funext j
  have hj := congrFun h j
  change (k j : ℝ) = (l j : ℝ) at hj
  exact_mod_cast hj

theorem integerFrequency_ne_zero {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    integerFrequency k ≠ 0 := by
  intro h
  apply hk
  apply integerFrequency_injective
  simpa only [integerFrequency_zero] using h

@[simp]
theorem integerFrequency_norm (k : Fin 4 → ℤ) : ‖integerFrequency k‖ = ‖k‖ := by
  change ‖(fun j => (k j : ℝ))‖ = ‖k‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg k)).mpr
    intro j
    simpa only [Int.norm_cast_real] using norm_le_pi_norm k j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (k j : ℝ)))).mpr
    intro j
    simpa only [Int.norm_cast_real] using norm_le_pi_norm (fun j => (k j : ℝ)) j

theorem one_le_norm_integerVector {k : Fin 4 → ℤ} (hk : k ≠ 0) : 1 ≤ ‖k‖ := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    apply hk
    ext j
    simpa using not_exists.mp h j
  have h : (1 : ℤ) ≤ |k j| := by
    have hpos : 0 < |k j| := abs_pos.mpr hj
    omega
  have hreal : (1 : ℝ) ≤ ‖k j‖ := by
    rw [Int.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast h
  exact hreal.trans (norm_le_pi_norm k j)

theorem dolbeaultSymbol_integer_ne_zero (p : PeriodDomain) {k : Fin 4 → ℤ}
    (hk : k ≠ 0) : dolbeaultSymbol p (integerFrequency k) ≠ 0 :=
  dolbeaultSymbol_ne_zero p (integerFrequency_ne_zero hk)

/-- The elliptic lower bound retains the genuine integer-frequency norm. -/
theorem dolbeaultSymbol_integer_exists_pos_lowerBound (p : PeriodDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : Fin 4 → ℤ,
      c * ‖k‖ ≤ ‖dolbeaultSymbol p (integerFrequency k)‖ := by
  obtain ⟨c, hc, hbound⟩ := dolbeaultSymbol_exists_pos_lowerBound p
  refine ⟨c, hc, fun k => ?_⟩
  simpa only [integerFrequency_norm] using hbound (integerFrequency k)

/-- The nonzero integer modes have a uniform positive gap from the zero symbol. -/
theorem dolbeaultSymbol_integer_exists_pos_gap (p : PeriodDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : Fin 4 → ℤ, k ≠ 0 →
      c ≤ ‖dolbeaultSymbol p (integerFrequency k)‖ := by
  obtain ⟨c, hc, hbound⟩ := dolbeaultSymbol_integer_exists_pos_lowerBound p
  refine ⟨c, hc, fun k hk => ?_⟩
  calc
    c = c * 1 := (mul_one c).symm
    _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_left (one_le_norm_integerVector hk) hc.le
    _ ≤ ‖dolbeaultSymbol p (integerFrequency k)‖ := hbound k

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
