import Wikipedia.HopfProblem.DegreeCollapseIntegralCapBoundary
import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCohomology

/-!
# The signed cap operation on the actual relative integral chains

A cochain on the genuine relative integral quotient pulls back to an
absolute cochain vanishing on subspace chains. Naturality makes its cap
operation kill that same subspace, so it factors through the original
relative chain group with values in the original absolute chains. The
integral boundary identity descends with its sign unchanged.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev Cochain (n : ℕ) := (complex U).X n →ₗ[ℤ] ℤ

abbrev cochainComplex := dualComplex (complex U)

def toAbsoluteMap : cochainComplex U ⟶ singularCochainComplex X := dualMap (projection U)

abbrev toAbsolute (p : ℕ) : Cochain U p →ₗ[ℤ] SingularCohomologyCup.Cochain X p :=
  ((toAbsoluteMap U).f p).hom

theorem toAbsolute_apply (p : ℕ) (α : Cochain U p) (c : Chains X p) :
    toAbsolute U p α c = α (quotientMap U p c) := rfl

theorem pullback_toAbsolute (p : ℕ) (α : Cochain U p) :
    SingularCohomologyCup.pullback (subtypeInclusion U) p (toAbsolute U p α) = 0 := by
  apply LinearMap.ext
  intro c
  change α (quotientMap U p (((inclusion U).f p).hom c)) = 0
  have he := congrArg (fun f ↦ (f.f p).hom c) (inclusion_projection U)
  exact (congrArg α he).trans α.map_zero

def coboundary {p : ℕ} (α : Cochain U p) : Cochain U (p + 1) :=
  ((cochainComplex U).d p (p + 1)).hom α

theorem toAbsolute_coboundary (p : ℕ) (α : Cochain U p) :
    toAbsolute U (p + 1) (coboundary U α) = SingularCohomologyCup.coboundary (toAbsolute U p α) :=
  (congrArg (fun f ↦ f.hom α) ((toAbsoluteMap U).comm p (p + 1))).symm

theorem cap_inclusion_zero {p q n : ℕ} (h : p + q = n) (α : Cochain U p) (c : Chains U n) :
    IntegralCap.capInDegree h (toAbsolute U p α) (inducedChain (subtypeInclusion U) n c) = 0 := by
  have he := IntegralCap.naturality h (subtypeInclusion U) (toAbsolute U p α) c
  rw [pullback_toAbsolute, IntegralCap.capInDegree_zero, LinearMap.zero_apply, map_zero] at he
  exact he.symm

theorem quotient_ker_le_cap_ker {p q n : ℕ} (h : p + q = n) (α : Cochain U p) :
    LinearMap.ker (quotientMap U n) ≤
      LinearMap.ker (IntegralCap.capInDegree h (toAbsolute U p α)) := by
  intro c hc
  have hs : c ∈ LinearMap.range (inducedChain (subtypeInclusion U) n) := by
    rw [subtypeInclusion_chain_range]
    exact (quotientMap_eq_zero_iff U n c).mp hc
  obtain ⟨b, rfl⟩ := hs
  exact cap_inclusion_zero U h α b

def capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain U p) :
    (complex U).X n →ₗ[ℤ] Chains X q := by
  let : Module ℤ (Chains X n ⧸ LinearMap.ker (quotientMap U n)) :=
    Submodule.Quotient.module (LinearMap.ker (quotientMap U n))
  exact ((LinearMap.ker (quotientMap U n)).liftQ
    (IntegralCap.capInDegree h (toAbsolute U p α)) (quotient_ker_le_cap_ker U h α)).comp
      ((quotientMap U n).quotKerEquivOfSurjective (quotientMap_surjective U n)).symm.toLinearMap

theorem capInDegree_quotientMap {p q n : ℕ} (h : p + q = n) (α : Cochain U p) (c : Chains X n) :
    capInDegree U h α (quotientMap U n c) = IntegralCap.capInDegree h (toAbsolute U p α) c := by
  let : Module ℤ (Chains X n ⧸ LinearMap.ker (quotientMap U n)) :=
    Submodule.Quotient.module (LinearMap.ker (quotientMap U n))
  let e := (quotientMap U n).quotKerEquivOfSurjective (quotientMap_surjective U n)
  have he : e.symm (quotientMap U n c) = Submodule.Quotient.mk c := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ c).symm
  change (LinearMap.ker (quotientMap U n)).liftQ
    (IntegralCap.capInDegree h (toAbsolute U p α)) (quotient_ker_le_cap_ker U h α)
      (e.symm (quotientMap U n c)) = _
  rw [he]
  rfl

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U h (0 : Cochain U p) = 0 := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := quotientMap_surjective U n c
  rw [capInDegree_quotientMap, map_zero, IntegralCap.capInDegree_zero]
  rfl

theorem capInDegree_add {p q n : ℕ} (h : p + q = n) (α β : Cochain U p) :
    capInDegree U h (α + β) = capInDegree U h α + capInDegree U h β := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := quotientMap_surjective U n c
  rw [LinearMap.add_apply, capInDegree_quotientMap, capInDegree_quotientMap,
    capInDegree_quotientMap, map_add, IntegralCap.capInDegree_add, LinearMap.add_apply]

theorem cap_boundary (p q : ℕ) (α : Cochain U p) (c : (complex U).X (p + q + 1)) :
    capInDegree U rfl α (((complex U).d (p + q + 1) (p + q)).hom c) =
      capInDegree U (p := p + 1) (q := q) (by omega) (coboundary U α) c +
        (-1 : ℤ) ^ p • ((singularComplex X).d (q + 1) q).hom
          (capInDegree U (p := p) (q := q + 1) (by omega) α c) := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective U (p + q + 1) c
  rw [boundary_quotientMap, capInDegree_quotientMap, capInDegree_quotientMap,
    capInDegree_quotientMap, toAbsolute_coboundary]
  exact IntegralCap.cap_boundary p q (toAbsolute U p α) b

theorem cap_boundary_inDegree {p q n : ℕ} (h : p + q + 1 = n)
    (α : Cochain U p) (c : (complex U).X n) :
    capInDegree U rfl α (((complex U).d n (p + q)).hom c) =
      capInDegree U (p := p + 1) (q := q) (by omega) (coboundary U α) c +
        (-1 : ℤ) ^ p • ((singularComplex X).d (q + 1) q).hom
          (capInDegree U (p := p) (q := q + 1) (by omega) α c) := by
  subst n
  exact cap_boundary U p q α c

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
