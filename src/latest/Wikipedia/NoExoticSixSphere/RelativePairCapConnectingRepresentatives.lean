import Wikipedia.NoExoticSixSphere.RelativeModTwoCapDegree
import Wikipedia.NoExoticSixSphere.ModTwoCapNaturality

/-!
# The actual cap boundary primitive for a pair

An ambient cochain extending a subspace cocycle, and an ambient chain
lifting a relative cycle, give a concrete primitive for the difference
of the two capped cycles. The proof uses the original cap boundary
formula and the original subspace inclusion, with mod-two coefficients.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem pair_connecting_cap_representatives (p q : ℕ)
    (α : ModTwoCapProduct.Cocycle U p) (β : ModTwoCapProduct.Cochain X p)
    (γ : RelativeModTwoCochains.Cocycle U (p + 1))
    (hβ : ModTwoCapProduct.pullback (subtypeInclusion U) p β = α.val)
    (hγ : RelativeModTwoCochains.toAbsolute U (p + 1) γ.val =
      ModTwoCapProduct.coboundary β)
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q + 1))
    (c : ModTwoChains.Chains X (p + q + 1))
    (hc : RelativeCoefficients.quotientMap Coefficient U (p + q + 1) c = z.val)
    (w : ModuleHomology.Cycle (modComplex 2 U) (p + q))
    (hw : ((RelativeCoefficients.inclusion Coefficient U).f (p + q)).hom w.val =
      ((modComplex 2 X).d (p + q + 1) (p + q)).hom c) :
    ModuleHomology.cycleClass (modComplex 2 X) q
        (capCyclesInDegree U (p := p + 1) (q := q) (n := p + q + 1) (by omega) γ.val
          (RelativeModTwoCochains.cocycle_coboundary_zero U (p + 1) γ) z) =
      ModuleHomology.cycleClass (modComplex 2 X) q
        (ModuleHomology.mapCycles (RelativeCoefficients.inclusion Coefficient U) q
          (ModTwoCapProduct.capCycles p q α.val
            (ModTwoCapProduct.cocycle_coboundary_zero U p α) w)) := by
  let r := capCyclesInDegree U (p := p + 1) (q := q) (n := p + q + 1) (by omega) γ.val
    (RelativeModTwoCochains.cocycle_coboundary_zero U (p + 1) γ) z
  let v := ModuleHomology.mapCycles (RelativeCoefficients.inclusion Coefficient U) q
    (ModTwoCapProduct.capCycles p q α.val (ModTwoCapProduct.cocycle_coboundary_zero U p α) w)
  change ModuleHomology.cycleClass (modComplex 2 X) q r =
    ModuleHomology.cycleClass (modComplex 2 X) q v
  apply (ModuleHomology.cycleClass_eq_iff (modComplex 2 X) q _ _).mpr
  refine ⟨ModTwoCapProduct.capInDegree (p := p) (q := q + 1)
    (n := p + q + 1) (by omega) β c, ?_⟩
  have hr : r.val = capInDegree U (p := p + 1) (q := q)
      (n := p + q + 1) (by omega) γ.val z.val :=
    capCyclesInDegree_val U (p := p + 1) (q := q) (n := p + q + 1) (by omega) γ.val
      (RelativeModTwoCochains.cocycle_coboundary_zero U (p + 1) γ) z
  have hv : v.val = ((RelativeCoefficients.inclusion Coefficient U).f q).hom
      (ModTwoCapProduct.cap (q := q) α.val w.val) :=
    (ModuleHomology.mapCycles_val (RelativeCoefficients.inclusion Coefficient U) q _).trans
      (congrArg ((RelativeCoefficients.inclusion Coefficient U).f q).hom
        (ModTwoCapProduct.capCycles_val p q α.val
          (ModTwoCapProduct.cocycle_coboundary_zero U p α) w))
  have h₁ := ModTwoCapProduct.spaceMap_cap (subtypeInclusion U) p q β w.val
  rw [hβ, hw] at h₁
  have h₂ := capInDegree_quotientMap U (p := p + 1) (q := q)
    (n := p + q + 1) (by omega) γ.val c
  rw [hc, hγ] at h₂
  have he := ModTwoCapProduct.boundary_capInDegree (p := p) (q := q)
    (n := p + q + 1) rfl β c
  change _ = ModTwoCapProduct.cap (q := q) β
    (((modComplex 2 X).d (p + q + 1) (p + q)).hom c) + _ at he
  rw [← h₁, ← h₂] at he
  apply he.trans
  apply (congrArg₂ (fun x y : ModTwoChains.Chains X q ↦ x + y) hv.symm hr.symm).trans
  rw [sub_eq_add_neg, ModTwoChains.neg_eq_self, add_comm]

end NoExoticSixSphere.RelativeModTwoCap
