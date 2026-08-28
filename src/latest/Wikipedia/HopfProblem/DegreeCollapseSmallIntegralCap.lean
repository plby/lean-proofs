import Wikipedia.HopfProblem.DegreeCollapseIntegralCapSupport

/-!
# Original integral cap localized on actual small chains

The proved support property places the original ambient cap in the
actual first subspace-chain image. Original chain inclusion is
injective, so it has a unique lift there. Both original piece formulas
and the actual ambient inclusion formula are retained.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyCup NoExoticSixSphere
open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev complex := (SingularSubcomplex.Small U V).chainComplex Coefficient

theorem inclusion_injective (q : ℕ) :
    Function.Injective (inducedChain (subtypeInclusion U) q) :=
  (ModuleCat.mono_iff_injective ((RelativeCoefficients.inclusion Coefficient U).f q)).mp
    inferInstance

def capInDegree {p q n : ℕ} (h : p + q = n) (α : RelativeIntegralCap.Cochain V p) :
    SmallChains Coefficient U V n →ₗ[ℤ] Chains U q :=
  LinearMap.codRestrictOfInjective
    ((IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p α)).comp
      (smallInclusionMap Coefficient U V n))
    (inducedChain (subtypeInclusion U) q) (inclusion_injective U q)
    (fun c => IntegralCap.relative_capInDegree_mem_range U V h α _
      (SingularSubcomplex.smallInclusion_mem_sup Coefficient U V n c))

theorem inclusion_capInDegree {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cochain V p) (c : SmallChains Coefficient U V n) :
    (inducedChain (subtypeInclusion U) q) (capInDegree U V h α c) =
      IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p α)
        (smallInclusionMap Coefficient U V n c) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ c

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U V h (0 : RelativeIntegralCap.Cochain V p) = 0 := by
  apply LinearMap.ext
  intro c
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V h 0 c).trans
  rw [map_zero, IntegralCap.capInDegree_zero, LinearMap.zero_apply]
  exact (inducedChain (subtypeInclusion U) q).map_zero.symm

theorem capInDegree_add {p q n : ℕ} (h : p + q = n)
    (α β : RelativeIntegralCap.Cochain V p) :
    capInDegree U V h (α + β) = capInDegree U V h α + capInDegree U V h β := by
  apply LinearMap.ext
  intro c
  apply inclusion_injective U q
  let z : Chains X n := smallInclusionMap Coefficient U V n c
  have he : IntegralCap.capInDegree (q := q) h (RelativeIntegralCap.toAbsolute V p (α + β)) =
      IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p α) +
        IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p β) :=
    (congrArg (IntegralCap.capInDegree (q := q) h)
      ((RelativeIntegralCap.toAbsolute V p).map_add α β)).trans
        (IntegralCap.capInDegree_add h _ _)
  exact (inclusion_capInDegree U V h (α + β) c).trans
    ((LinearMap.congr_fun he z).trans
      ((congrArg₂ (fun x y => x + y) (inclusion_capInDegree U V h α c).symm
        (inclusion_capInDegree U V h β c).symm).trans
          ((inducedChain (subtypeInclusion U) q).map_add _ _).symm))

/-- The left-piece formula is the original cap of the original restricted cochain. -/
theorem capInDegree_toSmallLeft {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cochain V p) (c : Chains U n) :
    capInDegree U V h α
        ((((SimplicialCoefficients.chains Coefficient).map
          (SingularSubcomplex.toSmallLeft U V)).f n).hom c) =
      IntegralCap.capInDegree h
        (pullback (subtypeInclusion U) p (RelativeIntegralCap.toAbsolute V p α)) c := by
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V h α _).trans
  have he := congrArg (fun m => (m.f n).hom c)
    (SingularSubcomplex.chainToSmallLeft_inclusion U V Coefficient)
  apply (congrArg (IntegralCap.capInDegree (q := q) h
    (RelativeIntegralCap.toAbsolute V p α)) he).trans
  exact (IntegralCap.naturality h (subtypeInclusion U)
    (RelativeIntegralCap.toAbsolute V p α) c).symm

/-- Original right-piece chains vanish under the actual relative integral cap. -/
theorem capInDegree_toSmallRight {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cochain V p) (c : Chains V n) :
    capInDegree U V h α
      ((((SimplicialCoefficients.chains Coefficient).map
        (SingularSubcomplex.toSmallRight U V)).f n).hom c) = 0 := by
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V h α _).trans
  have he := congrArg (fun m => (m.f n).hom c)
    (SingularSubcomplex.chainToSmallRight_inclusion U V Coefficient)
  apply (congrArg (IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p α)) he).trans
  exact (RelativeIntegralCap.cap_inclusion_zero V h α c).trans
    (inducedChain (subtypeInclusion U) q).map_zero.symm

end Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap
