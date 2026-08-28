import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorBase
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDescent

/-!
# Actual invariant descent in the finite sphere coordinate

Invariant holomorphic functions on saturated upstairs opens descend through
the actual triangle quotient, including its elliptic points.  The supplied
normalized sphere identification then gives actual holomorphic functions
on open subsets of the complex plane.  These constructions will be applied
to differences of the constructed local beta sections, not assumed cocycles.
-/

noncomputable section

open Set Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

/-- The actual image of an upstairs open set in the finite sphere coordinate. -/
def finiteDescentDomain (V : Opens ℍ) : Opens ℂ :=
  ⟨finiteOrbitInverse π hπ ⁻¹' (MuTorsor.descentDomain V : Set TriangleOrbitSpace),
    (MuTorsor.descentDomain V).isOpen.preimage (finiteOrbitInverse_holomorphic π hπ).continuous⟩

/-- The genuine descended function, evaluated on the inverse finite coordinate. -/
def finiteDescent (V : Opens ℍ) (f : ℍ → ℂ) : ℂ → ℂ :=
  MuTorsor.descend V f ∘ finiteOrbitInverse π hπ

theorem finiteDescentDomain_projection (V : Opens ℍ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V) (z : ℍ) :
    finiteProjection π z ∈ finiteDescentDomain π hπ V ↔ z ∈ V := by
  change finiteOrbitInverse π hπ (finiteOrbitCoordinate π (triangleOrbitProjection z)) ∈
    MuTorsor.descentDomain V ↔ z ∈ V
  rw [finiteOrbitInverse_coordinate]
  exact MuTorsor.project_mem_descentDomain_iff V hV z

theorem finiteDescent_projection (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z) {z : ℍ} (hz : z ∈ V) :
    finiteDescent π hπ V f (finiteProjection π z) = f z := by
  simp only [finiteDescent, finiteProjection, Function.comp_apply, finiteOrbitInverse_coordinate]
  exact MuTorsor.descend_project V f hV hInv hz

theorem finiteDescent_analytic (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) :
    AnalyticOnNhd ℂ (finiteDescent π hπ V f) (finiteDescentDomain π hπ V) :=
  analyticOnNhd_finite_pullback π hπ (MuTorsor.descentDomain V)
    (MuTorsor.descend_holomorphic V f hV hInv hf)

theorem finiteDescentDomain_top : finiteDescentDomain π hπ ⊤ = ⊤ := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨a, ha⟩ := triangleOrbitProjection_surjective (finiteOrbitInverse π hπ z)
    exact ⟨a, trivial, ha⟩

include hπ in
/-- An invariant global holomorphic upstairs function gives an actual
entire function, with the proved exact pullback identity. -/
theorem exists_entire_descent (f : ℍ → ℂ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      f (triangleGeometricRepresentation g z) = f z) :
    ∃ F : ℂ → ℂ, (∀ z, AnalyticAt ℂ F z) ∧
      ∀ z : ℍ, F (finiteProjection π z) = f z := by
  have htop : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ (⊤ : Opens ℍ) ↔ z ∈ (⊤ : Opens ℍ) :=
    fun _ _ => Iff.rfl
  have hi : ∀ g : TriangleGroup, ∀ z ∈ (⊤ : Opens ℍ),
      f (triangleGeometricRepresentation g z) = f z := fun g z _ => hInv g z
  refine ⟨finiteDescent π hπ ⊤ f, ?_, fun z => finiteDescent_projection π hπ ⊤ f htop hi trivial⟩
  have h := finiteDescent_analytic π hπ ⊤ f htop hi hf.contMDiffOn
  rw [finiteDescentDomain_top] at h
  exact fun z => h z trivial

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
