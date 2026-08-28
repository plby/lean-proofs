import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlas

/-!
# The original triangle quotient inside its compact complex curve

The original quotient atlas agrees with the atlas inherited from the
complement of the newly added cusp.  In particular the literal inclusion
is locally biholomorphic, and the actual cusp complement is biholomorphic
to the original triangle orbit space.  No uniformization of either curve
is assumed.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

/-- An old quotient chart is an analytic partial coordinate in the
constructed compact atlas. -/
def triangleCompactifiedOldCoordinatePartial (q : TriangleOrbitSpace) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω where
  toPartialEquiv := (OnePointAtlas.oldChart q).toPartialEquiv
  open_source := (OnePointAtlas.oldChart q).open_source
  open_target := (OnePointAtlas.oldChart q).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (triangleCompactifiedAtlasData.chart_mem_atlas (some q)))
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (triangleCompactifiedAtlasData.chart_mem_atlas (some q)))

/-- Adding the cusp does not change the local complex structure at any
point of the original quotient. -/
theorem triangleOpenInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion := by
  intro q
  have hq : triangleOpenInclusion q ∈ (OnePointAtlas.oldChart q).source :=
    (OnePointAtlas.coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)
  have hpull := OnePointAtlas.oldChart_pullback_localDiffeomorph q q hq
  have hinv : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (OnePointAtlas.oldChart q).symm
      (OnePointAtlas.oldChart q (triangleOpenInclusion q)) :=
    (triangleCompactifiedOldCoordinatePartial q).symm.isLocalDiffeomorphAt _ _ _
      ((OnePointAtlas.oldChart q).map_source hq)
  have hcomp := hpull.comp (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ x in 𝓝 q, triangleOpenInclusion x ∈ (OnePointAtlas.oldChart q).source :=
    OnePoint.continuous_coe.continuousAt ((OnePointAtlas.oldChart q).open_source.mem_nhds hq)
  exact hU.mono fun x hx => ((OnePointAtlas.oldChart q).left_inv hx).symm

/-- The actual open complement of the distinguished cusp in the compact
complex quotient curve. -/
def triangleCuspComplement : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  ⟨{triangleCuspPoint}ᶜ, isClosed_singleton.isOpen_compl⟩

@[simp] theorem mem_triangleCuspComplement (x : TriangleCompactifiedOrbitSpace) :
    x ∈ triangleCuspComplement ↔ x ≠ triangleCuspPoint := Iff.rfl

/-- The literal inclusion, with its target restricted to the cusp complement. -/
def triangleOpenInclusionToComplement (q : TriangleOrbitSpace) : triangleCuspComplement :=
  ⟨triangleOpenInclusion q, triangleOpenInclusion_ne_cusp q⟩

@[simp] theorem triangleOpenInclusionToComplement_coe (q : TriangleOrbitSpace) :
    (triangleOpenInclusionToComplement q : TriangleCompactifiedOrbitSpace) =
      triangleOpenInclusion q := rfl

theorem triangleOpenInclusionToComplement_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusionToComplement :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ)
    triangleOpenInclusion_isLocalDiffeomorph triangleCuspComplement triangleOpenInclusion_ne_cusp

theorem triangleOpenInclusionToComplement_bijective :
    Function.Bijective triangleOpenInclusionToComplement := by
  constructor
  · intro x y h
    exact OnePoint.coe_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp x.property
    exact ⟨q, Subtype.ext hq⟩

/-- The full quotient before compactification is genuinely biholomorphic
to the actual open cusp complement, with its inherited compact-curve atlas. -/
def triangleOpenComplementBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace triangleCuspComplement ω :=
  triangleOpenInclusionToComplement_isLocalDiffeomorph.diffeomorphOfBijective
    triangleOpenInclusionToComplement_bijective

@[simp] theorem triangleOpenComplementBiholomorph_apply (q : TriangleOrbitSpace) :
    (triangleOpenComplementBiholomorph q : TriangleCompactifiedOrbitSpace) =
      triangleOpenInclusion q := rfl

@[simp] theorem triangleOpenComplementBiholomorph_symm_apply (q : triangleCuspComplement) :
    triangleOpenInclusion (triangleOpenComplementBiholomorph.symm q) = q :=
  congrArg Subtype.val (triangleOpenComplementBiholomorph.apply_symm_apply q)

/-- Away from the two elliptic orbits, the actual projection to the compact
curve remains a local biholomorphism. -/
theorem triangleCompactifiedProjection_isLocalDiffeomorphAt_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleCompactifiedProjection z :=
  (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular hz).comp
    (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace)
    (triangleOpenInclusion_isLocalDiffeomorph (triangleOrbitProjection z))

theorem triangleCompactifiedProjection_eq_iff (z w : ℍ) :
    triangleCompactifiedProjection z = triangleCompactifiedProjection w ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g w = z :=
  OnePoint.coe_eq_coe.trans (triangleOrbitProjection_eq_iff z w)

theorem triangleCompactifiedProjection_range :
    range triangleCompactifiedProjection = (triangleCuspComplement : Set _) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact triangleCompactifiedProjection_ne_cusp z
  · intro hx
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp hx
    obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective q
    exact ⟨z, hq⟩

end Wikipedia.HopfProblem.SpecialPeriods
