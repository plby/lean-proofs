import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.PeriodFamily

/-!
# Integrality on the genuine period lattice

The real transport used for the alternating forms agrees with the actual
family period isomorphism and the actual integral period-vector map.
Consequently these forms take integral values on the genuine period
lattice. This does not identify them with cohomology or line-bundle classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open scoped Matrix

theorem periodEquiv_family {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    periodEquiv (P.point b) = P.periodEquiv b := rfl

/-- Integral coefficient vectors map to the already constructed actual period vectors. -/
theorem periodEquiv_integer_eq_periodVector (p : PeriodDomain) (x : Lattice) :
    periodEquiv p (fun i => (x i : ℝ)) = p.periodVector x := by
  rw [periodEquiv_coordinates, PeriodDomain.periodVector_apply]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Actual integral-valuedness on the actual lattice, stated without a cohomological comparison. -/
def IntegralOnPeriodLattice (p : PeriodDomain) (B : LinearMap.BilinForm ℝ ComplexPlane₂) : Prop :=
  ∀ x ∈ p.lattice, ∀ y ∈ p.lattice, ∃ n : ℤ, B x y = (n : ℝ)

theorem tangentForm_integral (p : PeriodDomain) (E : Fin 6 → ℤ) :
    IntegralOnPeriodLattice p (tangentForm p E) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (p.mem_lattice_iff x).mp hx
  obtain ⟨b, rfl⟩ := (p.mem_lattice_iff y).mp hy
  refine ⟨coordinateForm E a b, ?_⟩
  rw [← periodEquiv_integer_eq_periodVector, ← periodEquiv_integer_eq_periodVector]
  exact tangentForm_integer_periods p E a b

/-- The actual tangent form remembers every integral coefficient. -/
theorem tangentForm_injective (p : PeriodDomain) : Function.Injective (tangentForm p) := by
  intro E F h
  funext k
  have hk := congrArg (fun B : LinearMap.BilinForm ℝ ComplexPlane₂ =>
    B (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2)) h
  rw [tangentForm_basis_pair, tangentForm_basis_pair] at hk
  exact_mod_cast hk

/-- Scaling the coefficient form scales the genuine transported form. -/
theorem tangentForm_zsmul (p : PeriodDomain) (n : ℤ) (E : Fin 6 → ℤ) :
    tangentForm p (n • E) = (n : ℝ) • tangentForm p E := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change tangentForm p (n • E) x y = (n : ℝ) * tangentForm p E x y
  simp only [tangentForm_apply, coordinateForm_apply, coordinateValue,
    Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  ring

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
