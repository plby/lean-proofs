import Wikipedia.HopfProblem.HolomorphicAlternatingBundle
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Holomorphic forms on the actual tangent bundle

A holomorphic p-form is an actual analytic section of Mathlib's bundle
of continuous alternating p-covectors on the native tangent spaces.
The total-space topology and the chart derivatives are those of the
original manifold. This is not a space of selected invariant coefficients.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]

/-- The full space of actual alternating tangent covectors at a point. -/
abbrev Covector (p : ℕ) (x : M) :=
  TangentSpace 𝓘(ℂ, E) x [⋀^Fin p]→L[ℂ] ℂ

/-- The genuine alternating cotangent bundle, retaining Mathlib's topology. -/
abbrev TotalSpace (p : ℕ) :=
  Bundle.TotalSpace (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p)

/-- All holomorphic p-forms on the given native complex manifold. -/
abbrev Form (p : ℕ) :=
  ContMDiffSection 𝓘(ℂ, E) (E [⋀^Fin p]→L[ℂ] ℂ) ω (Covector E M p)

/-- The full native alternating-covector bundle is holomorphic. -/
theorem covectorBundle_holomorphic (p : ℕ) :
    ContMDiffVectorBundle ω (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) 𝓘(ℂ, E) :=
  inferInstance

/-- The actual coefficient covector in the tangent trivialization at x₀. -/
def inCoordinates {p : ℕ} (θ : Form E M p) (x₀ x : M) : E [⋀^Fin p]→L[ℂ] ℂ :=
  (trivializationAt (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) x₀ ⟨x, θ x⟩).2

omit [FiniteDimensional ℂ E] in
/-- In coordinates these are the literal continuous alternating-map
bundle coordinates built from the actual tangent trivializations. -/
theorem inCoordinates_eq {p : ℕ} (θ : Form E M p) (x₀ x : M) :
    inCoordinates E M θ x₀ x =
      ContinuousAlternatingMap.inCoordinates E ℂ
        (E₁ := TangentSpace 𝓘(ℂ, E)) (E₂ := fun _ : M => ℂ) x₀ x x₀ x (θ x) :=
  rfl

/-- Every genuine local coefficient covector is holomorphic on its full
native trivialization domain. -/
theorem inCoordinates_holomorphicOn {p : ℕ} (θ : Form E M p) (x₀ : M) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E [⋀^Fin p]→L[ℂ] ℂ) ω
      (inCoordinates E M θ x₀)
      (trivializationAt (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) x₀).baseSet := by
  exact (Trivialization.contMDiffOn_section_baseSet_iff
    (trivializationAt (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) x₀)).mp
      θ.contMDiff.contMDiffOn

omit [FiniteDimensional ℂ E] in
/-- A form is zero precisely when every actual tangent covector is zero. -/
theorem eq_zero_iff {p : ℕ} (θ : Form E M p) : θ = 0 ↔ ∀ x, θ x = 0 := by
  constructor
  · rintro rfl x
    rfl
  · intro h
    exact ContMDiffSection.ext h

/-- At the chosen chart center all coefficient covectors are holomorphic. -/
theorem inCoordinates_holomorphicAt {p : ℕ} (θ : Form E M p) (x₀ : M) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E [⋀^Fin p]→L[ℂ] ℂ) ω
      (inCoordinates E M θ x₀) x₀ :=
  (inCoordinates_holomorphicOn E M θ x₀).contMDiffAt
    ((trivializationAt (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀))

omit [FiniteDimensional ℂ E] in
/-- Scalar coordinate evaluation uses the inverse actual tangent chart map. -/
theorem inCoordinates_apply {p : ℕ} (θ : Form E M p) (x₀ x : M) (v : Fin p → E) :
    inCoordinates E M θ x₀ x v =
      θ x (fun i => (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).symmL ℂ x (v i)) := by
  simp [inCoordinates_eq, ContinuousAlternatingMap.inCoordinates, Function.comp_def]

omit [FiniteDimensional ℂ E] in
/-- At its preferred chart center, the coordinate covector is the actual
native tangent covector. -/
theorem inCoordinates_self {p : ℕ} (θ : Form E M p) (x : M) :
    inCoordinates E M θ x x = θ x := by
  ext v
  rw [inCoordinates_apply]
  congr 1
  funext i
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source E x)]
  exact (tangentBundleCore 𝓘(ℂ, E) M).coordChange_self
    (achart E x) x (mem_chart_source E x) (v i)

end Wikipedia.HopfProblem.HolomorphicDifferentialForms
