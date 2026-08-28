import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorLocalDivision
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticNeighborhoods

/-!
# Filling the two elliptic orbits in a homogeneous quotient

The apparent poles of a homogeneous quotient are filled by the values of
actual analytic division germs.  The chosen precisely invariant elliptic
neighbourhoods contain no other point of either elliptic orbit.  This
proves local equality with the division germ, rather than asserting that
the pointwise quotient at `0 / 0` is holomorphic.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division

attribute [local instance] triangleGeometricAction

/-- A precisely invariant elliptic neighbourhood meets its distinguished
orbit only at the actual fixed point. -/
theorem ellipticNeighborhood_projection_eq_iff (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ Triangle.ellipticNeighborhood j) :
    triangleOrbitProjection z = Triangle.ellipticOrbitCenter j ↔
      z = Triangle.ellipticCenter j := by
  constructor
  · intro he
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z
      (Triangle.ellipticCenter j)).mp he
    have hr : g ∈ Triangle.ellipticStabilizer j :=
      Triangle.ellipticNeighborhood_return j g
        ⟨z, ⟨Triangle.ellipticCenter j,
          Triangle.ellipticCenter_mem_neighborhood j, hg⟩, hz⟩
    have hfix : triangleGeometricRepresentation g (Triangle.ellipticCenter j) =
        Triangle.ellipticCenter j := hr
    exact hg.symm.trans hfix
  · rintro rfl
    rfl

/-- Off its centre, the chosen elliptic neighbourhood avoids both
exceptional orbits, not merely the other one. -/
theorem ellipticNeighborhood_projection_ne_centers (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ Triangle.ellipticNeighborhood j) (hne : z ≠ Triangle.ellipticCenter j) :
    triangleOrbitProjection z ≠ triangleOrbitCenterOne ∧
      triangleOrbitProjection z ≠ triangleOrbitCenterTwo := by
  have hself : triangleOrbitProjection z ≠ Triangle.ellipticOrbitCenter j :=
    fun h => hne ((ellipticNeighborhood_projection_eq_iff j z hz).mp h)
  have hother := Triangle.ellipticNeighborhood_avoids_other j z hz
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

/-- The quotient completed by one scalar value on each of the two
actual elliptic orbits.  The values will be obtained from analytic germs. -/
def completedQuotient (ν F : ℍ → ℂ) (v : Elliptic.Kind → ℂ) (z : ℍ) : ℂ := by
  classical
  exact if triangleOrbitProjection z = triangleOrbitCenterOne then v .three
    else if triangleOrbitProjection z = triangleOrbitCenterTwo then v .four
    else ν z / F z

theorem completedQuotient_center (ν F : ℍ → ℂ) (v : Elliptic.Kind → ℂ)
    (j : Elliptic.Kind) :
    completedQuotient ν F v (Triangle.ellipticCenter j) = v j := by
  cases j
  · simp only [Triangle.ellipticCenter, completedQuotient, triangleOrbitCenterOne,
      if_true]
  · have hne : triangleOrbitProjection Triangle.centerTwo ≠ triangleOrbitCenterOne :=
      triangleOrbitCenterOne_ne_centerTwo.symm
    simp only [Triangle.ellipticCenter, completedQuotient, hne, if_false,
      triangleOrbitCenterTwo, if_true]

/-- Away from both actual elliptic orbits, no completion is made. -/
theorem completedQuotient_eq_div (ν F : ℍ → ℂ) (v : Elliptic.Kind → ℂ) (z : ℍ)
    (h₁ : triangleOrbitProjection z ≠ triangleOrbitCenterOne)
    (h₂ : triangleOrbitProjection z ≠ triangleOrbitCenterTwo) :
    completedQuotient ν F v z = ν z / F z := by
  simp only [completedQuotient, h₁, h₂, if_false]

/-- Exact knowledge of the zero set identifies the completed quotient
with its analytic division germ on a genuine neighbourhood upstairs. -/
theorem completedQuotient_eventuallyEq_germ {ν F : ℍ → ℂ}
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hv : v j = h (Triangle.ellipticCenter j : ℂ))
    (hfactor : (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.ellipticCenter j : ℂ)]
      fun w => (F ∘ ofComplex) w * h w) :
    completedQuotient ν F v =ᶠ[𝓝 (Triangle.ellipticCenter j)]
      fun z => h (z : ℂ) := by
  have he : ∀ᶠ z : ℍ in 𝓝 (Triangle.ellipticCenter j),
      ν z = F z * h (z : ℂ) := by
    simpa only [Function.comp_apply, ofComplex_apply] using
      UpperHalfPlane.continuous_coe.continuousAt.eventually hfactor
  filter_upwards [he, Triangle.ellipticNeighborhood_mem_nhds j] with z hez hzn
  by_cases hz : z = Triangle.ellipticCenter j
  · subst z
    exact (completedQuotient_center ν F v j).trans hv
  · obtain ⟨h₁, h₂⟩ := ellipticNeighborhood_projection_ne_centers j z hzn hz
    have hFz : F z ≠ 0 := fun hzero => (hFzero z).mp hzero |>.elim h₁ h₂
    rw [completedQuotient_eq_div ν F v z h₁ h₂, hez]
    exact mul_div_cancel_left₀ _ hFz

/-- The analytic germ proves holomorphicity at the actual elliptic
centre of the completed quotient. -/
theorem completedQuotient_contMDiffAt_center {ν F : ℍ → ℂ}
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h (Triangle.ellipticCenter j : ℂ))
    (hv : v j = h (Triangle.ellipticCenter j : ℂ))
    (hfactor : (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.ellipticCenter j : ℂ)]
      fun w => (F ∘ ofComplex) w * h w) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v)
      (Triangle.ellipticCenter j) := by
  exact (hh.contDiffAt.contMDiffAt.comp _ (UpperHalfPlane.contMDiff_coe _)).congr_of_eventuallyEq
    (completedQuotient_eventuallyEq_germ hFzero v j h hv hfactor)

/-- At an ordinary point the completed quotient is locally the usual
quotient of two holomorphic functions with nonzero denominator. -/
theorem completedQuotient_contMDiffAt_of_ne_zero {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (z : ℍ) (hz : F z ≠ 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) z := by
  apply ((hν z).div₀ (hF z) hz).congr_of_eventuallyEq
  filter_upwards [(hF z).continuousAt.eventually_ne hz] with w hw
  have hn : ¬(triangleOrbitProjection w = triangleOrbitCenterOne ∨
      triangleOrbitProjection w = triangleOrbitCenterTwo) := fun he => hw ((hFzero w).mpr he)
  exact completedQuotient_eq_div ν F v w (fun h => hn (.inl h)) (fun h => hn (.inr h))

/-- An invariant function holomorphic at one point is holomorphic at
every point in its actual triangle orbit, by the actual biholomorphic action. -/
theorem contMDiffAt_orbit {H : ℍ → ℂ}
    (hH : ∀ g : TriangleGroup, ∀ z : ℍ,
      H (triangleGeometricRepresentation g z) = H z)
    {a : ℍ} (ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H a) (g : TriangleGroup) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H (triangleGeometricRepresentation g a) := by
  have hi : triangleGeometricRepresentation g⁻¹ (triangleGeometricRepresentation g a) = a := by
    rw [map_inv]
    exact (triangleGeometricRepresentation g).symm_apply_apply a
  have hh : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H
      (triangleGeometricRepresentation g⁻¹ (triangleGeometricRepresentation g a)) :=
    hi.symm ▸ ha
  apply (hh.comp _ (triangleGeometricRepresentation_holomorphic g⁻¹ _)).congr_of_eventuallyEq
  filter_upwards with z
  exact (hH g⁻¹ z).symm

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Division
