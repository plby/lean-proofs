import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDescent
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCompactExtension

/-!
# Vanishing of invariant holomorphic functions at the actual cusp

Global invariant holomorphic functions on the upper half-plane descend
through the actual full triangle quotient, including both elliptic
points.  A zero analytic germ at the actual cusp then forces vanishing
by the proved compact-curve extension theorem.  Neither a projective-line
coordinate nor a compact extension is assumed here.
-/

noncomputable section

open Filter Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleOrbitChartedSpace

/-- The global descent agrees with the original invariant function on
every actual upper-half-plane lift. -/
theorem descend_top_project {H : ℍ → ℂ}
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      H (triangleGeometricRepresentation g z) = H z) (z : ℍ) :
    descend ⊤ H (triangleOrbitProjection z) = H z := by
  apply descend_project ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · trivial

/-- Holomorphicity of the global descent on the entire actual quotient
is derived from the established open-domain descent theorem. -/
theorem descend_top_holomorphic {H : ℍ → ℂ}
    (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      H (triangleGeometricRepresentation g z) = H z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (descend ⊤ H) := by
  intro q
  apply descend_holomorphicAt ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · exact hH.contMDiffOn
  · exact ⟨orbitRepresentative q, trivial, project_orbitRepresentative q⟩

/-- A genuinely invariant holomorphic function with a zero analytic
cusp germ vanishes identically.  Both descent and compact extension are
constructed by the imported theorems. -/
theorem invariant_eq_zero_of_eventually_cusp {H : ℍ → ℂ}
    (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      H (triangleGeometricRepresentation g z) = H z)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (he : ∀ᶠ z in atImInfty, H z = g (Triangle.cuspQ z)) : H = 0 := by
  have hd : descend ⊤ H = 0 := by
    apply eq_zero_of_eventually_cusp (descend ⊤ H) g
      (descend_top_holomorphic hH hInv) hg hg0
    filter_upwards [he] with z hz
    exact (descend_top_project hInv z).trans hz
  funext z
  exact (descend_top_project hInv z).symm.trans (congrFun hd (triangleOrbitProjection z))

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
