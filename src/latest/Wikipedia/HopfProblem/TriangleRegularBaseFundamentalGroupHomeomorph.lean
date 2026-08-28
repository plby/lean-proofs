import Wikipedia.HopfProblem.TriangleUniformization
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph
import Wikipedia.HopfProblem.FundamentalGroupHomeomorph

/-!
# The actual regular triangle base is the twice-punctured plane

Restrict the constructed normalized uniformization to the complement of
the two elliptic orbits.  The resulting map identifies the actual regular
covering quotient with `ℂ \ {0, 1}` and induces an equivalence of its
pointed fundamental groups.  The projection formulas retain the original
quotient projection and the actual normalized half-triangle map.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannMapping

/-- The standard plane with the two normalized finite marked points removed. -/
def twicePuncturedPlaneDomain : TopologicalSpace.Opens ℂ :=
  ⟨{z | z ≠ 0 ∧ z ≠ 1}, isOpen_ne.inter isOpen_ne⟩

/-- The twice-punctured complex plane with its inherited topology and atlas. -/
abbrev TwicePuncturedPlane : Type := twicePuncturedPlaneDomain

@[simp] theorem mem_twicePuncturedPlaneDomain (z : ℂ) :
    z ∈ twicePuncturedPlaneDomain ↔ z ≠ 0 ∧ z ≠ 1 := Iff.rfl

theorem twicePuncturedPlaneDomain_eq_compl :
    (twicePuncturedPlaneDomain : Set ℂ) = ({0, 1} : Set ℂ)ᶜ := by
  ext z
  change (z ≠ 0 ∧ z ≠ 1) ↔ z ∈ ({0, 1} : Set ℂ)ᶜ
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]

/-- The normalized uniformization carries the actual regular domain
exactly onto the standard two-puncture complement. -/
theorem trianglePlaneUniformizationHomeomorph_regular_iff (q : TriangleOrbitSpace) :
    q ∈ triangleOrbitRegularDomain ↔
      trianglePlaneUniformizationHomeomorph q ∈ twicePuncturedPlaneDomain := by
  rw [triangleOrbitRegularDomain_mem_iff, mem_twicePuncturedPlaneDomain,
    ← trianglePlaneUniformizationHomeomorph_centerOne,
    ← trianglePlaneUniformizationHomeomorph_centerTwo]
  simp only [ne_eq, trianglePlaneUniformizationHomeomorph.injective.eq_iff]

/-- Restrict the actual plane uniformization to the literal regular domain. -/
def triangleRegularDomainPlaneHomeomorph :
    triangleOrbitRegularDomain ≃ₜ TwicePuncturedPlane :=
  trianglePlaneUniformizationHomeomorph.subtype
    trianglePlaneUniformizationHomeomorph_regular_iff

/-- The original regular quotient is homeomorphic to `ℂ \ {0, 1}`. -/
def triangleRegularPlaneHomeomorph : TriangleRegularQuotient ≃ₜ TwicePuncturedPlane :=
  triangleRegularOrbitHomeomorph.trans triangleRegularDomainPlaneHomeomorph

@[simp] theorem triangleRegularPlaneHomeomorph_coe (q : TriangleRegularQuotient) :
    (triangleRegularPlaneHomeomorph q : ℂ) =
      trianglePlaneUniformizationHomeomorph (triangleRegularToOrbit q) := rfl

/-- The map on regular representatives uses the literal full orbit projection. -/
@[simp] theorem triangleRegularPlaneHomeomorph_project (z : TriangleRegularPoint) :
    (triangleRegularPlaneHomeomorph (triangleRegularProject z) : ℂ) =
      trianglePlaneUniformizationHomeomorph (triangleOrbitProjection z.val) := rfl

/-- On the actual half-Ford triangle this is precisely the constructed
normalized Riemann-map value. -/
theorem triangleRegularPlaneHomeomorph_project_half (z : TriangleRegularPoint)
    (hz : z.val ∈ halfFordRegion) :
    (triangleRegularPlaneHomeomorph (triangleRegularProject z) : ℂ) =
      triangleSignedHalfPlaneMap z.val :=
  trianglePlaneUniformizationHomeomorph_projection hz

/-- The equivalence on pointed fundamental groups is induced by the actual
regular-plane homeomorphism, at an arbitrary regular-quotient basepoint. -/
def triangleRegularFundamentalGroupEquiv (x : TriangleRegularQuotient) :
    FundamentalGroup TriangleRegularQuotient x ≃*
      FundamentalGroup TwicePuncturedPlane (triangleRegularPlaneHomeomorph x) :=
  homeomorphFundamentalGroupEquiv triangleRegularPlaneHomeomorph x

@[simp] theorem triangleRegularFundamentalGroupEquiv_toMonoidHom
    (x : TriangleRegularQuotient) :
    (triangleRegularFundamentalGroupEquiv x).toMonoidHom =
      FundamentalGroup.map
        ⟨triangleRegularPlaneHomeomorph, triangleRegularPlaneHomeomorph.continuous⟩ x := rfl

@[simp] theorem triangleRegularFundamentalGroupEquiv_apply (x : TriangleRegularQuotient)
    (γ : FundamentalGroup TriangleRegularQuotient x) :
    triangleRegularFundamentalGroupEquiv x γ =
      FundamentalGroup.map
        ⟨triangleRegularPlaneHomeomorph, triangleRegularPlaneHomeomorph.continuous⟩ x γ := rfl

/-- The same comparison starting at an arbitrary basepoint of the
twice-punctured plane, with no separately chosen path or basepoint. -/
def twicePuncturedPlaneFundamentalGroupEquiv (z : TwicePuncturedPlane) :
    FundamentalGroup TwicePuncturedPlane z ≃*
      FundamentalGroup TriangleRegularQuotient (triangleRegularPlaneHomeomorph.symm z) :=
  homeomorphFundamentalGroupEquiv triangleRegularPlaneHomeomorph.symm z

attribute [local instance] triangleRegularQuotientChartedSpace triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

/-- The regular-plane homeomorphism is holomorphic for the already
constructed covering atlas and the inherited standard complex atlas. -/
theorem triangleRegularPlaneHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularPlaneHomeomorph := by
  intro x
  have hsub : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun q : TriangleRegularQuotient => (triangleRegularPlaneHomeomorph q : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularPlaneHomeomorph x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply hsub.mp
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
    (trianglePlaneUniformization ∘ triangleRegularToOrbit) x
  exact (trianglePlaneUniformization.contMDiff.comp triangleRegularToOrbit_holomorphic) x

/-- The actual regular quotient is biholomorphic to the standard
twice-punctured plane; neither complex atlas is replaced. -/
def triangleRegularPlaneBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient TwicePuncturedPlane ω :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph triangleRegularPlaneHomeomorph
    triangleRegularPlaneHomeomorph_holomorphic

@[simp] theorem triangleRegularPlaneBiholomorph_toHomeomorph :
    triangleRegularPlaneBiholomorph.toHomeomorph = triangleRegularPlaneHomeomorph :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph_toHomeomorph _ _

@[simp] theorem triangleRegularPlaneBiholomorph_apply (q : TriangleRegularQuotient) :
    triangleRegularPlaneBiholomorph q = triangleRegularPlaneHomeomorph q := rfl

@[simp] theorem triangleRegularPlaneBiholomorph_project (z : TriangleRegularPoint) :
    (triangleRegularPlaneBiholomorph (triangleRegularProject z) : ℂ) =
      trianglePlaneUniformization (triangleOrbitProjection z.val) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
