import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdeal

/-!
# The Cartier section and the actual ideal section on the generic set

On the dense finite chart, the constructed Cartier section is a genuine
holomorphic section of the native base-twist bundle. Under every valid
ideal-sheaf chart identification it is the literal constant-one ideal
section. This connects the particular meromorphic section, as well as
its line bundle, to the existing vanishing-ideal construction.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The actual Cartier section restricted to its dense open generic set. -/
def genericSection : BundleSection finiteChart where
  toFun p := cartier.rawSection p
  contMDiff_toFun := by
    intro p
    exact (cartier.rawSectionMap_holomorphicAt p.property).comp p
      contMDiff_subtype_val.contMDiffAt

@[simp] theorem genericSection_apply (p : finiteChart) :
    genericSection p = cartier.rawSection p := rfl

theorem genericSection_ne_zero (p : finiteChart) : genericSection p ≠ 0 :=
  cartier.rawSection_ne_zero p.property

/-- Its actual native coefficient on every smaller valid chart is the
corresponding Cartier fraction. -/
theorem genericSection_localCoefficient (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ frameChart b) (hfinite : U ≤ finiteChart) (p : U) :
    (bundle.localTriv b
      ⟨(p : RiemannSphere), bundleSectionRestrict hfinite genericSection p⟩).2 =
        cartier.localFraction b p :=
  cartier.rawSection_localCoefficient b (hU p.property) (hfinite p.property)

/-- The same native section represents the actual constant-one ideal
section on every subopen of the finite generic set, in either chart. -/
theorem idealEquiv_genericSection (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ frameChart b) (hfinite : U ≤ finiteChart) :
    idealEquiv b U hU (bundleSectionRestrict hfinite genericSection) =
      finiteFrame U hfinite := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rw [idealEquiv_apply, genericSection_localCoefficient b U hU hfinite p,
    idealFrameValue_eq_denominator]
  change (1 / denominator b p) * denominator b p = 1
  rw [one_div]
  exact inv_mul_cancel₀ (denominator_ne_zero b (hU p.property) (hfinite p.property))

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
