import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDescentBasic
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorDescentRemovable

/-!
# Holomorphic descent through the full triangle quotient

Invariant holomorphic functions on saturated open subsets of the actual
upper half-plane descend to the constructed full triangle quotient.  This
includes both elliptic orbits: continuity comes from the actual open quotient
map, and the two possible singularities are removable in the quotient's
existing complex charts.
-/

noncomputable section

open Set Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

variable (V : Opens ℍ) (f : ℍ → ℂ)
  (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
    triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
  (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
    f (triangleGeometricRepresentation g z) = f z)
  (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V)

include hV hInv hf in
/-- Holomorphy on the entire actual quotient image, including its elliptic
points.  No descent or meromorphic extension is assumed. -/
theorem descend_holomorphic :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) (descentDomain V) := by
  apply contMDiffOn_of_continuousOn_of_finite
    (s := {triangleOrbitCenterOne, triangleOrbitCenterTwo}) (descentDomain V).isOpen
    ((Set.finite_singleton triangleOrbitCenterTwo).insert triangleOrbitCenterOne)
    (descend_continuousOn V f hV hInv hf.continuousOn)
  intro q hq hnot
  have h₁ : q ≠ triangleOrbitCenterOne := fun h => hnot (by simp [h])
  have h₂ : q ≠ triangleOrbitCenterTwo := fun h => hnot (by simp [h])
  exact descend_contMDiffAt_of_not_elliptic V f hV hInv hf hq h₁ h₂

include hV hInv hf in
theorem descend_holomorphicAt {q : TriangleOrbitSpace} (hq : q ∈ descentDomain V) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q :=
  (descend_holomorphic V f hV hInv hf).contMDiffAt ((descentDomain V).isOpen.mem_nhds hq)

include hV hInv hf in
/-- The same descent as a holomorphic function on the actual open submanifold. -/
theorem descend_restriction_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun q : descentDomain V => descend V f q) := by
  intro q
  exact (descend_holomorphicAt V f hV hInv hf q.property).comp q
    ((contMDiff_subtype_val (U := descentDomain V) (I := 𝓘(ℂ)) (n := ω)) q)

include hV hInv hf in
/-- Existence and uniqueness on the full quotient image are proved for the
actual projection, rather than included in a proposed descent structure. -/
theorem existsUnique_holomorphic_descent :
    ∃! F : descentDomain V → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧ ∀ z : V, F (descentProjection V z) = f z := by
  refine ⟨fun q => descend V f q,
    ⟨descend_restriction_holomorphic V f hV hInv hf,
      fun z => descend_project V f hV hInv z.property⟩, ?_⟩
  intro F hF
  funext q
  obtain ⟨z, rfl⟩ := (descentProjection_isOpenQuotientMap V).surjective q
  exact (hF.2 z).trans (descend_project V f hV hInv z.property).symm

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
