import Wikipedia.NoExoticSixSphere.RelativeCoefficientSequence

/-!
# The coefficient quotient of actual relative homology

Whenever the original reduction map is surjective, its proved kernel gives
the actual scalar-quotient identification. An integral marking then gives
the corresponding finite cyclic marking, with its reduction formula.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RelativeCoefficients

attribute [local instance] Submodule.Quotient.module

variable {X : Type} [TopologicalSpace X] (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ)
  (hs : Function.Surjective (reductionMap p U n))

/-- The native reduction identifies its original target with the actual scalar quotient. -/
def quotientEquiv :
    (RelativeSingularHomology.Homology U n ⧸
      scalarImage p (RelativeSingularHomology.Homology U n)) ≃ₗ[ℤ] ModHomology p U n := by
  let e₁ := Submodule.quotEquivOfEq _ _ (reductionMap_ker p hp U n).symm
  let e₂ := (reductionMap p U n).quotKerEquivOfSurjective hs
  let e₃ := e₁.trans e₂
  let ea : (RelativeSingularHomology.Homology U n ⧸
      scalarImage p (RelativeSingularHomology.Homology U n)) ≃+ ModHomology p U n :=
    { toEquiv := e₃.toEquiv
      map_add' := fun x y => e₃.map_add x y }
  exact ea.toIntLinearEquiv

theorem quotientEquiv_mk (a : RelativeSingularHomology.Homology U n) :
    quotientEquiv p hp U n hs (Submodule.Quotient.mk a) = reductionMap p U n a := rfl

theorem quotientEquiv_symm_reduction (a : RelativeSingularHomology.Homology U n) :
    (quotientEquiv p hp U n hs).symm (reductionMap p U n a) = Submodule.Quotient.mk a := by
  apply (quotientEquiv p hp U n hs).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_mk]

/-- The coefficient marking is on native relative homology, with the original reduction map. -/
def markingEquiv (e : RelativeSingularHomology.Homology U n ≃ₗ[ℤ] ℤ) :
    ModHomology p U n ≃ₗ[ℤ] ZMod p :=
  (quotientEquiv p hp U n hs).symm.trans (scalarQuotientEquivZMod p e)

theorem markingEquiv_reduction (e : RelativeSingularHomology.Homology U n ≃ₗ[ℤ] ℤ)
    (a : RelativeSingularHomology.Homology U n) :
    markingEquiv p hp U n hs e (reductionMap p U n a) = (e a : ZMod p) := by
  rw [markingEquiv, LinearEquiv.trans_apply, quotientEquiv_symm_reduction,
    scalarQuotientEquivZMod_mk]

end NoExoticSixSphere.RelativeCoefficients
