import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientOrdersTranslated
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph

/-!
# The exact ramification locus of the actual triangle quotient

The quotient projection is locally biholomorphic exactly on the regular
locus.  At an elliptic point, composing a hypothetical local biholomorphism
with the actual quotient coordinate and the upper-half-plane coordinate
would force analytic order one.  The proved orders three and four exclude
this possibility on both entire elliptic orbits.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

attribute [local instance] triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

/-- The differential equivalence of a local biholomorphism excludes a
zero complex scalar derivative. -/
private theorem complex_deriv_ne_zero_of_localDiffeomorph {f : ℂ → ℂ} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : deriv f z ≠ 0 := by
  let e : ℂ ≃L[ℂ] ℂ := hf.mfderivToContinuousLinearEquiv (by simp)
  have he : e 1 = deriv f z := by
    change (show ℂ →L[ℂ] ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f z) 1 = deriv f z
    rw [mfderiv_eq_fderiv]
    rfl
  intro h
  have h10 : e 1 = e 0 := by rw [he, h, map_zero]
  exact one_ne_zero (e.injective h10)

/-- A zero of a locally biholomorphic complex function is simple. -/
private theorem complex_order_eq_one_of_localDiffeomorph {f : ℂ → ℂ} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) (hz : f z = 0) :
    analyticOrderAt f z = 1 :=
  hf.contMDiffAt.contDiffAt.analyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    (complex_deriv_ne_zero_of_localDiffeomorph hf)

/-- The actual partial inverse of the upper-half-plane inclusion is
locally biholomorphic at each point of its genuine open source. -/
private theorem ofComplex_isLocalDiffeomorphAt (z : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω ofComplex (z : ℂ) := by
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℍ ω :=
    { toPartialEquiv := ofComplex.toPartialEquiv
      open_source := ofComplex.open_source
      open_target := ofComplex.open_target
      contMDiffOn_toFun := by
        intro w hw
        have he : ((ofComplex w : ℍ) : ℂ) = w := ofComplex.left_inv hw
        have hwim : 0 < w.im := by
          rw [← he]
          exact (ofComplex w).im_pos
        exact (contMDiffAt_ofComplex hwim).contMDiffWithinAt
      contMDiffOn_invFun := contMDiff_coe.contMDiffOn }
  refine ⟨Φ, ?_, fun _ _ => rfl⟩
  exact ofComplex.symm.map_source (mem_univ z)

/-- A hypothetical local biholomorphism of the projection gives a local
biholomorphism for its actual ambient complex coordinate germ. -/
private theorem elliptic_complexGerm_isLocalDiffeomorphAt
    (j : Elliptic.Kind) (z : ℍ)
    (hz : triangleOrbitProjection z ∈ (ellipticFullChart j).source)
    (hq : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex) (z : ℂ) := by
  have hc : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (ellipticFullChart j) (triangleOrbitProjection z) :=
    (triangleOrbitCoordinatePartial (.inr j)).isLocalDiffeomorphAt _ _ _ hz
  have hcomp := hq.comp (K := 𝓘(ℂ)) (P := ℂ) hc
  have hcomp' : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (ellipticFullChart j ∘ triangleOrbitProjection) (ofComplex (z : ℂ)) := by
    simpa only [ofComplex_apply] using hcomp
  simpa only [Function.comp_assoc] using
    (ofComplex_isLocalDiffeomorphAt z).comp (K := 𝓘(ℂ)) (P := ℂ) hcomp'

/-- The projection is not locally biholomorphic at any translate of either
elliptic center: its actual coordinate germ has order three or four. -/
theorem triangleOrbitProjection_not_isLocalDiffeomorphAt_elliptic
    (j : Elliptic.Kind) (g : TriangleGroup) :
    ¬ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection
      (triangleGeometricRepresentation g (ellipticCenter j)) := by
  intro hq
  let z : ℍ := triangleGeometricRepresentation g (ellipticCenter j)
  have hzq : triangleOrbitProjection z = ellipticOrbitCenter j := by
    dsimp only [z]
    rw [triangleOrbitProjection_smul]
    rfl
  have hz : triangleOrbitProjection z ∈ (ellipticFullChart j).source := by
    rw [hzq]
    exact ellipticFullChart_center_mem_source j
  have hf := elliptic_complexGerm_isLocalDiffeomorphAt j z hz hq
  have hzero : (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex) (z : ℂ) = 0 := by
    simp only [Function.comp_apply, ofComplex_apply, hzq, ellipticFullChart_center]
  have h1 := complex_order_eq_one_of_localDiffeomorph hf hzero
  have hm := ellipticFullChart_order_translated_center j g
  have horder : (j.order : ℕ∞) = 1 := hm.symm.trans h1
  cases j <;> norm_num [Elliptic.Kind.order] at horder

/-- In the constructed complex curve atlas, the actual quotient projection
is locally biholomorphic exactly at points with trivial stabilizer. -/
theorem triangleOrbitProjection_isLocalDiffeomorphAt_iff (z : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z ↔
      z ∈ triangleRegularLocus := by
  constructor
  · intro hq
    rw [triangleRegularLocus_eq_compl_ellipticSet]
    intro hz
    rcases hz with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact triangleOrbitProjection_not_isLocalDiffeomorphAt_elliptic .three g hq
    · exact triangleOrbitProjection_not_isLocalDiffeomorphAt_elliptic .four g hq
  · exact triangleOrbitProjection_isLocalDiffeomorphAt_of_regular

/-- The ramification points are exactly the two actual elliptic orbits. -/
theorem triangleOrbitProjection_not_isLocalDiffeomorphAt_iff (z : ℍ) :
    ¬ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z ↔
      z ∈ triangleEllipticSet := by
  simp only [triangleOrbitProjection_isLocalDiffeomorphAt_iff,
    triangleRegularLocus_eq_compl_ellipticSet, mem_compl_iff, not_not]

/-- Equality of the actual ramification set with the proved closed discrete
union of elliptic orbits. -/
theorem triangleOrbitProjection_ramificationSet :
    {z : ℍ | ¬ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z} =
      triangleEllipticSet := by
  ext z
  exact triangleOrbitProjection_not_isLocalDiffeomorphAt_iff z

/-- The only ramified values are the two distinguished elliptic orbit
points; every point above either value is ramified. -/
theorem triangleOrbitProjection_not_isLocalDiffeomorphAt_iff_value (z : ℍ) :
    ¬ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo := by
  rw [triangleOrbitProjection_isLocalDiffeomorphAt_iff,
    ← triangleOrbitProjection_mem_regularDomain_iff z, triangleOrbitRegularDomain_mem_iff]
  tauto

end Wikipedia.HopfProblem.SpecialPeriods
