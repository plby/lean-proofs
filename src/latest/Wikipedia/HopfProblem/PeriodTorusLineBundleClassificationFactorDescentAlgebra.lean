import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentSection

/-!
# The scalar factor extracted from a nonvanishing cover frame

The ratio of the frame coefficients at two lattice-related points is independent
of the native bundle chart. It has the sign for the positive translation action:
the ratio times the frame at `z + l` is the frame at `z`.
-/

noncomputable section

open Bundle Set

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- The scalar which identifies the frame at `z + l` with the frame at `z`. -/
def frameFactorScalar (s : CoverSection p V) (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  coefficient s (p.lattice.mkQ z) z / coefficient s (p.lattice.mkQ z) (z + l)

/-- The ratio can be computed in any native chart containing the common base
point. The change-of-chart scalar cancels from numerator and denominator. -/
theorem frameFactorScalar_eq_coefficient_div (s : CoverSection p V)
    (l : p.lattice) (z : ComplexPlane₂) (i : p.Torus)
    (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    frameFactorScalar s l z = coefficient s i z / coefficient s i (z + l) := by
  have hj := FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)
  have hj' : p.lattice.mkQ (z + l) ∈
      (nativeTriv V (p.lattice.mkQ z)).baseSet := by
    rwa [quotient_add_lattice]
  have hi' : p.lattice.mkQ (z + l) ∈ (nativeTriv V i).baseSet := by
    rwa [quotient_add_lattice]
  have hz := coefficient_change s (p.lattice.mkQ z) i z hj hi
  have hzl := coefficient_change s (p.lattice.mkQ z) i (z + l) hj' hi'
  rw [quotient_add_lattice] at hzl
  unfold frameFactorScalar
  rw [← hz, ← hzl]
  exact (mul_div_mul_left _ _ (scalarTransition V (p.lattice.mkQ z) i
    (p.lattice.mkQ z)).ne_zero).symm

theorem frameFactorScalar_ne_zero (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l : p.lattice) (z : ComplexPlane₂) : frameFactorScalar s l z ≠ 0 := by
  have hi := FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)
  have hi' : p.lattice.mkQ (z + l) ∈
      (nativeTriv V (p.lattice.mkQ z)).baseSet := by
    rwa [quotient_add_lattice]
  exact div_ne_zero (coefficient_ne_zero s hne (p.lattice.mkQ z) z hi)
    (coefficient_ne_zero s hne (p.lattice.mkQ z) (z + l) hi')

@[simp] theorem frameFactorScalar_zero (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (z : ComplexPlane₂) : frameFactorScalar s 0 z = 1 := by
  simp only [frameFactorScalar, Submodule.coe_zero, add_zero]
  exact div_self (coefficient_ne_zero s hne (p.lattice.mkQ z) z
    (FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)))

/-- The ordinary scalar cancellation identity gives the positive-action
cocycle law for the actual lattice translations. -/
theorem frameFactorScalar_add (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l m : p.lattice) (z : ComplexPlane₂) :
    frameFactorScalar s (l + m) z =
      frameFactorScalar s l (z + m) * frameFactorScalar s m z := by
  have hi : p.lattice.mkQ (z + m) ∈
      (nativeTriv V (p.lattice.mkQ z)).baseSet := by
    rw [quotient_add_lattice]
    exact FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)
  have hmid := coefficient_ne_zero s hne (p.lattice.mkQ z) (z + m) hi
  simp only [frameFactorScalar, quotient_add_lattice, Submodule.coe_add]
  rw [show z + ((l : ComplexPlane₂) + (m : ComplexPlane₂)) =
    z + (m : ComplexPlane₂) + (l : ComplexPlane₂) by abel]
  exact (div_mul_div_cancel₀' hmid _ _).symm

/-- In any common native chart, the extracted factor carries the translated
frame coefficient to the original one. -/
theorem frameFactorScalar_mul_coefficient (s : CoverSection p V)
    (hne : ∀ z, s z ≠ 0) (l : p.lattice) (z : ComplexPlane₂) (i : p.Torus)
    (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    frameFactorScalar s l z * coefficient s i (z + l) = coefficient s i z := by
  rw [frameFactorScalar_eq_coefficient_div s l z i hi]
  apply div_mul_cancel₀
  apply coefficient_ne_zero s hne i (z + l)
  rwa [quotient_add_lattice]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
