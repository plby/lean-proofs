import Wikipedia.NoExoticSixSphere.SmallModTwoCapBoundary

/-!
# Actual two-piece cap chains and their boundary formulas

When two small-chain representatives have the same original ambient
image, a difference of supported cochains gives the difference of
their actual localized cap chains. If the original chain boundary lies
in the annihilated subspace, localized cap has precisely the cap with
the original coboundary as its boundary.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- The original cap operation preserves differences in the actual cochain input. -/
theorem capInDegree_sub {p q n : ℕ} (h : p + q = n) (α β : Cochain X p) :
    capInDegree h (α - β) = capInDegree h α - capInDegree h β := by
  apply eq_sub_iff_add_eq.mpr
  rw [← capInDegree_add, sub_add_cancel]

end NoExoticSixSphere.ModTwoCapProduct

namespace NoExoticSixSphere.SmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X]

/-- The actual ambient cap splits into the two localized cap chains of the actual cochain lifts. -/
theorem capInDegree_difference (U V A B : Set X) {p q n : ℕ} (h : p + q = n)
    (α : ModTwoCapProduct.Cochain X p) (β : RelativeModTwoCochains.Cochain A p)
    (γ : RelativeModTwoCochains.Cochain B p)
    (hα : α = RelativeModTwoCochains.toAbsolute A p β - RelativeModTwoCochains.toAbsolute B p γ)
    (c : ModTwoChains.Chains X n) (cU : SmallChains Coefficient U A n)
    (hcU : smallInclusionMap Coefficient U A n cU = c) (cV : SmallChains Coefficient V B n)
    (hcV : smallInclusionMap Coefficient V B n cV = c) :
    ModTwoCapProduct.capInDegree h α c =
      ((RelativeCoefficients.inclusion Coefficient U).f q).hom (capInDegree U A h β cU) -
        ((RelativeCoefficients.inclusion Coefficient V).f q).hom (capInDegree V B h γ cV) := by
  rw [hα, ModTwoCapProduct.capInDegree_sub, LinearMap.sub_apply]
  exact congrArg₂ (fun x y => x - y)
    ((inclusion_capInDegree U A h β cU).trans
      (congrArg (ModTwoCapProduct.capInDegree h
        (RelativeModTwoCochains.toAbsolute A p β)) hcU)).symm
    ((inclusion_capInDegree V B h γ cV).trans
      (congrArg (ModTwoCapProduct.capInDegree h
        (RelativeModTwoCochains.toAbsolute B p γ)) hcV)).symm

/-- A relative-cycle boundary in the annihilated subspace leaves only the coboundary cap term. -/
theorem boundary_capInDegree_of_relative_cycle (U V : Set X) {p q n : ℕ}
    (h : p + q + 1 = n) (α : RelativeModTwoCochains.Cochain V p)
    (c : SmallChains Coefficient U V n)
    (hc : smallInclusionMap Coefficient U V (p + q) (((complex U V).d n (p + q)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient V).f (p + q)).hom) :
    ((modComplex 2 U).d (q + 1) q).hom
        (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
        (RelativeModTwoCochains.coboundary V α) c := by
  have hz : capInDegree U V (p := p) (q := q) rfl α
      (((complex U V).d n (p + q)).hom c) = 0 := by
    apply inclusion_injective U q
    apply (inclusion_capInDegree U V rfl α (((complex U V).d n (p + q)).hom c)).trans
    obtain ⟨b, hb⟩ := hc
    apply (congrArg (ModTwoCapProduct.capInDegree (q := q) rfl
      (RelativeModTwoCochains.toAbsolute V p α)) hb.symm).trans
    exact (RelativeModTwoCap.capInDegree_inclusion_zero V rfl α b).trans
      ((RelativeCoefficients.inclusion Coefficient U).f q).hom.map_zero.symm
  exact (boundary_capInDegree U V h α c).trans (by rw [hz, zero_add])

end NoExoticSixSphere.SmallModTwoCap
