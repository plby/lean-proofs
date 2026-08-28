import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFunctor

/-!
# Native coefficients on a manifold with one fixed coordinate chart

When the original preferred charts are independent of the point, the
native tangent trivializations agree. Hence the actual covectors of a
holomorphic form, viewed in that fixed model, vary holomorphically.
No new charted-space structure is substituted for the original atlas.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]

/-- The preferred native tangent covector, expressed in the model space. -/
def nativeCoefficients {p : ℕ} (θ : Form E M p) (x : M) : E [⋀^Fin p]→L[ℂ] ℂ :=
  inCoordinates E M θ x x

omit [FiniteDimensional ℂ E] in
@[simp] theorem nativeCoefficients_apply {p : ℕ} (θ : Form E M p)
    (x : M) (v : Fin p → E) : nativeCoefficients E M θ x v = θ x v := by
  rw [nativeCoefficients, inCoordinates_self]
  rfl

omit [FiniteDimensional ℂ E] in
/-- Constancy of the actual preferred charts makes the tangent-bundle
trivialization independent of the chosen center. -/
theorem tangent_trivialization_eq_of_constant_charts
    (hchart : ∀ x y : M, chartAt E x = chartAt E y) (x y : M) :
    trivializationAt E (TangentSpace 𝓘(ℂ, E)) x =
      trivializationAt E (TangentSpace 𝓘(ℂ, E)) y := by
  have ha : achart E x = achart E y := Subtype.ext (hchart x y)
  rw [TangentBundle.trivializationAt_eq_localTriv,
    TangentBundle.trivializationAt_eq_localTriv, ha]

omit [FiniteDimensional ℂ E] in
/-- Every preferred covector chart is the same actual covector chart. -/
theorem inCoordinates_eq_nativeCoefficients_of_constant_charts
    (hchart : ∀ x y : M, chartAt E x = chartAt E y)
    {p : ℕ} (θ : Form E M p) (x₀ x : M) :
    inCoordinates E M θ x₀ x = nativeCoefficients E M θ x := by
  ext v
  rw [inCoordinates_apply, nativeCoefficients, inCoordinates_apply]
  simp only [tangent_trivialization_eq_of_constant_charts E M hchart x₀ x]

/-- Coefficient covectors of a genuine holomorphic form are holomorphic
in the unchanged fixed-chart atlas. -/
theorem nativeCoefficients_holomorphic_of_constant_charts
    (hchart : ∀ x y : M, chartAt E x = chartAt E y)
    {p : ℕ} (θ : Form E M p) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E [⋀^Fin p]→L[ℂ] ℂ) ω
      (nativeCoefficients E M θ) := by
  intro x₀
  apply (inCoordinates_holomorphicAt E M θ x₀).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x =>
    (inCoordinates_eq_nativeCoefficients_of_constant_charts E M hchart θ x₀ x).symm

end Wikipedia.HopfProblem.HolomorphicDifferentialForms
