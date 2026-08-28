import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientComplex
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# The regular covering atlas agrees with the full quotient atlas

For the constructed full quotient complex structure, the original projection
is locally biholomorphic at every regular point.  The existing complex atlas
on the regular quotient agrees with the one inherited from its actual open
image in the full quotient; the previously proved homeomorphism is a genuine
biholomorphism.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleOrbitChartedSpace triangleRegularQuotientChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient := triangleRegularQuotient_isManifold

/-- Each supplied chart is analytic in the full quotient atlas that it helps
construct, with its analytic inverse on the exact target. -/
def triangleOrbitCoordinatePartial (i : TriangleOrbitChartIndex) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω where
  toPartialEquiv := (triangleOrbitChart i).toPartialEquiv
  open_source := (triangleOrbitChart i).open_source
  open_target := (triangleOrbitChart i).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))

/-- The actual quotient projection is a local biholomorphism at every
point with trivial stabilizer, in the full quotient's constructed atlas. -/
theorem triangleOrbitProjection_isLocalDiffeomorphAt_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z := by
  obtain ⟨r, hr⟩ := exists_regularFullChart (triangleOrbitProjection z)
    ((triangleOrbitProjection_mem_regularDomain_iff z).mpr hz)
  have hf := regularFullChart_pullback_isLocalDiffeomorphAt r hr
  have hinv : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart r).symm
      (regularFullChart r (triangleOrbitProjection z)) :=
    (triangleOrbitCoordinatePartial (.inl r)).symm.isLocalDiffeomorphAt _ _ _
      ((regularFullChart r).map_source hr)
  have hcomp := hf.comp (K := 𝓘(ℂ)) (P := TriangleOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ w in 𝓝 z, triangleOrbitProjection w ∈ (regularFullChart r).source :=
    triangleOrbitProjection_continuous.continuousAt ((regularFullChart r).open_source.mem_nhds hr)
  exact hU.mono fun w hw => ((regularFullChart r).left_inv hw).symm

theorem triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic {z : ℍ}
    (h₁ : triangleOrbitProjection z ≠ triangleOrbitCenterOne)
    (h₂ : triangleOrbitProjection z ≠ triangleOrbitCenterTwo) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z :=
  triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
    ((triangleOrbitProjection_mem_regularDomain_iff z).mp
      ((triangleOrbitRegularDomain_mem_iff _).mpr ⟨h₁, h₂⟩))

/-- The actual inclusion from the already constructed regular quotient is
holomorphic for the new full quotient atlas. -/
theorem triangleRegularToOrbit_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularToOrbit := by
  apply CoveringQuotient.contMDiff_of_comp triangleRegularProject_covering 𝓘(ℂ) ω
  have hf := triangleOrbitProjection_holomorphic.comp
    (contMDiff_subtype_val (U := triangleRegularDomain) (I := 𝓘(ℂ)) (n := ω))
  convert hf using 1
  funext z
  exact triangleRegularToOrbit_project z

theorem triangleRegularOrbitHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph := by
  intro x
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y : TriangleRegularQuotient =>
        (triangleRegularOrbitHomeomorph y : TriangleOrbitSpace)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (triangleRegularToOrbit_holomorphic x)

/-- The full quotient projection restricted to its regular source and target. -/
def triangleRegularFullProjection : TriangleRegularPoint → triangleOrbitRegularDomain :=
  fun z => ⟨triangleOrbitProjection z,
    (triangleOrbitProjection_mem_regularDomain_iff z).mpr z.property⟩

theorem triangleRegularFullProjection_eq :
    triangleRegularFullProjection = triangleRegularOrbitHomeomorph ∘ triangleRegularProject := by
  funext z
  apply Subtype.ext
  exact (triangleRegularToOrbit_project z).symm

theorem triangleRegularFullProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularFullProjection := by
  intro z
  exact isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular z.property)
    triangleRegularDomain triangleOrbitRegularDomain
    (fun w hw => (triangleOrbitProjection_mem_regularDomain_iff w).mpr hw) z.property

theorem triangleRegularFullProjection_surjective :
    Function.Surjective triangleRegularFullProjection := by
  rw [triangleRegularFullProjection_eq]
  exact triangleRegularOrbitHomeomorph.surjective.comp triangleRegularProject_surjective

theorem triangleRegularOrbitHomeomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph.symm := by
  apply contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
    triangleRegularFullProjection_isLocalDiffeomorph triangleRegularFullProjection_surjective
  have he : triangleRegularOrbitHomeomorph.symm ∘ triangleRegularFullProjection =
      triangleRegularProject := by
    rw [triangleRegularFullProjection_eq]
    funext z
    exact triangleRegularOrbitHomeomorph.symm_apply_apply (triangleRegularProject z)
  rw [he]
  exact triangleRegularProject_holomorphic

/-- The previously constructed regular covering quotient is biholomorphic
to its actual open submanifold of the full triangle quotient. -/
def triangleRegularOrbitBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient triangleOrbitRegularDomain ω where
  toEquiv := triangleRegularOrbitHomeomorph.toEquiv
  contMDiff_toFun := triangleRegularOrbitHomeomorph_holomorphic
  contMDiff_invFun := triangleRegularOrbitHomeomorph_symm_holomorphic

@[simp] theorem triangleRegularOrbitBiholomorph_project (z : TriangleRegularPoint) :
    (triangleRegularOrbitBiholomorph (triangleRegularProject z) : TriangleOrbitSpace) =
      triangleOrbitProjection z :=
  triangleRegularToOrbit_project z

end Wikipedia.HopfProblem.SpecialPeriods
