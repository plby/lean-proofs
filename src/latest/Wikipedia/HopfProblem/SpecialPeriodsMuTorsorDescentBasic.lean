import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph

/-!
# Invariant functions on actual open triangle quotients

The descent domain is the actual image of an open subset of the upper
half-plane.  An invariant function on a saturated open set has a uniquely
determined descent on this image.  We construct it by choosing actual orbit
representatives and extending by zero outside the image.  Continuity uses
the restricted open quotient map, and regular holomorphy uses the existing
local biholomorphic projection.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleGeometricAction triangleGeometricAction_continuous
  triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

/-- The open image in the actual full triangle orbit quotient. -/
def descentDomain (V : Opens ℍ) : Opens TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := TriangleGroup) V

@[simp] theorem mem_descentDomain (V : Opens ℍ) (q : TriangleOrbitSpace) :
    q ∈ descentDomain V ↔ ∃ z ∈ V, triangleOrbitProjection z = q := Iff.rfl

theorem project_mem_descentDomain (V : Opens ℍ) {z : ℍ} (hz : z ∈ V) :
    triangleOrbitProjection z ∈ descentDomain V := ⟨z, hz, rfl⟩

/-- The restricted projection uses the inherited open-subspace topologies. -/
def descentProjection (V : Opens ℍ) : V → descentDomain V :=
  LocalOrbitQuotient.imageProjection (G := TriangleGroup) V

@[simp] theorem descentProjection_val (V : Opens ℍ) (z : V) :
    (descentProjection V z : TriangleOrbitSpace) = triangleOrbitProjection z := rfl

theorem descentProjection_isOpenQuotientMap (V : Opens ℍ) :
    IsOpenQuotientMap (descentProjection V) :=
  LocalOrbitQuotient.imageProjection_isOpenQuotientMap V

/-- A chosen actual lift of an orbit, without a regularity assumption. -/
def orbitRepresentative (q : TriangleOrbitSpace) : ℍ :=
  (triangleOrbitProjection_surjective q).choose

@[simp] theorem project_orbitRepresentative (q : TriangleOrbitSpace) :
    triangleOrbitProjection (orbitRepresentative q) = q :=
  (triangleOrbitProjection_surjective q).choose_spec

/-- Explicit descent, extended by zero outside the saturated domain.  Its
definition needs no regularity or invariance assumptions; the theorems below
prove the descent property from the actual invariance equations. -/
def descend (V : Opens ℍ) (f : ℍ → ℂ) (q : TriangleOrbitSpace) : ℂ := by
  classical
  exact if orbitRepresentative q ∈ V then f (orbitRepresentative q) else 0

theorem project_mem_descentDomain_iff (V : Opens ℍ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V) (z : ℍ) :
    triangleOrbitProjection z ∈ descentDomain V ↔ z ∈ V := by
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff w z).mp h
    exact (hV g z).mp (hg ▸ hw)
  · exact project_mem_descentDomain V

theorem preimage_descentDomain (V : Opens ℍ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V) :
    triangleOrbitProjection ⁻¹' (descentDomain V : Set TriangleOrbitSpace) = V := by
  ext z
  exact project_mem_descentDomain_iff V hV z

theorem orbitRepresentative_mem_iff (V : Opens ℍ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V) (q : TriangleOrbitSpace) :
    orbitRepresentative q ∈ V ↔ q ∈ descentDomain V := by
  rw [← project_mem_descentDomain_iff V hV, project_orbitRepresentative]

theorem descend_project (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z) {z : ℍ} (hz : z ∈ V) :
    descend V f (triangleOrbitProjection z) = f z := by
  have hr : orbitRepresentative (triangleOrbitProjection z) ∈ V :=
    (orbitRepresentative_mem_iff V hV _).mpr (project_mem_descentDomain V hz)
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff
    (orbitRepresentative (triangleOrbitProjection z)) z).mp
    (project_orbitRepresentative (triangleOrbitProjection z))
  simp only [descend, if_pos hr]
  rw [← hg]
  exact hInv g z hz

theorem descend_eq_zero_of_not_mem (V : Opens ℍ) (f : ℍ → ℂ)
    {q : TriangleOrbitSpace} (hq : q ∉ descentDomain V) : descend V f q = 0 := by
  have hr : orbitRepresentative q ∉ V := by
    intro h
    exact hq ⟨orbitRepresentative q, h, project_orbitRepresentative q⟩
  simp only [descend, if_neg hr]

/-- Equality on the image can be checked on actual upper-half-plane lifts. -/
theorem eqOn_of_pullback_eq (V : Opens ℍ) {F G : TriangleOrbitSpace → ℂ}
    (h : ∀ z ∈ V, F (triangleOrbitProjection z) = G (triangleOrbitProjection z)) :
    EqOn F G (descentDomain V) := by
  rintro q ⟨z, hz, rfl⟩
  exact h z hz

theorem descend_unique (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z)
    {F : TriangleOrbitSpace → ℂ}
    (hF : ∀ z ∈ V, F (triangleOrbitProjection z) = f z) :
    EqOn F (descend V f) (descentDomain V) :=
  eqOn_of_pullback_eq V fun z hz => (hF z hz).trans (descend_project V f hV hInv hz).symm

theorem descend_continuousOn (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z)
    (hf : ContinuousOn f V) : ContinuousOn (descend V f) (descentDomain V) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply (descentProjection_isOpenQuotientMap V).isQuotientMap.continuous_iff.mpr
  have he : (fun q : descentDomain V => descend V f q) ∘ descentProjection V =
      fun z : V => f z := by
    funext z
    exact descend_project V f hV hInv z.property
  change Continuous ((fun q : descentDomain V => descend V f q) ∘ descentProjection V)
  rw [he]
  exact hf.domRestrict

/-- Holomorphy at every point other than the two actual elliptic orbits.
The following file removes these two exceptional points. -/
theorem descend_contMDiffAt_of_not_elliptic (V : Opens ℍ) (f : ℍ → ℂ)
    (hV : ∀ g : TriangleGroup, ∀ z : ℍ,
      triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv : ∀ g : TriangleGroup, ∀ z ∈ V,
      f (triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) {q : TriangleOrbitSpace}
    (hq : q ∈ descentDomain V) (h₁ : q ≠ triangleOrbitCenterOne)
    (h₂ : q ≠ triangleOrbitCenterTwo) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hp := triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (descend V f ∘ triangleOrbitProjection) z := by
    apply (hf.contMDiffAt (V.isOpen.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hz] with w hw
    exact descend_project V f hV hInv hw
  have h := hcomp.comp_of_eq hp.localInverse_contMDiffAt
    (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with r hr
  change descend V f r = descend V f (triangleOrbitProjection (hp.localInverse r))
  rw [show triangleOrbitProjection (hp.localInverse r) = r from hr]

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
