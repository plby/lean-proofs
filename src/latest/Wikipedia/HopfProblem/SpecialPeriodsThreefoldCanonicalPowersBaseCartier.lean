import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBasePoint

/-!
# The actual Cartier presentation of the point `1`

The numerator is the section already constructed in the original two
sphere charts; the denominator is one. The exact zero and simple-order
theorems therefore identify this presentation with the positive point
divisor, while its actual line is the dual of the original ideal line.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase

/-- The actual open complement of the sphere point `1`. -/
def pointOutside : TopologicalSpace.Opens RiemannSphere :=
  ⟨{((1 : ℂ) : RiemannSphere)}ᶜ, isClosed_singleton.isOpen_compl⟩

@[simp] theorem mem_pointOutside (p : RiemannSphere) :
    p ∈ pointOutside ↔ p ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

theorem pointOutside_dense : Dense (pointOutside : Set RiemannSphere) :=
  dense_compl_singleton ((1 : ℂ) : RiemannSphere)

/-- The Cartier presentation has genuine local defining functions for the point. -/
def cartier : CanonicalGlobal.CartierData 𝓘(ℂ) RiemannSphere Bool where
  transitions := data
  isHolomorphic := data_isHolomorphic
  numerator := pointCoefficient
  denominator := fun _ _ => 1
  numerator_holomorphic := pointCoefficient_holomorphic
  denominator_holomorphic _ := contMDiffOn_const
  genericSet := pointOutside
  genericSet_dense := pointOutside_dense
  numerator_ne_zero b p _ hp := (pointCoefficient_eq_zero_iff b p).not.mpr hp
  denominator_ne_zero _ _ _ _ := one_ne_zero
  ratio a b p hp := by
    simpa only [mul_one] using (pointCoefficient_compatible a b p hp).symm

@[simp] theorem cartier_transitions : cartier.transitions = data := rfl

@[simp] theorem cartier_localFraction (b : Bool) (p : RiemannSphere) :
    cartier.localFraction b p = pointCoefficient b p := by
  exact div_one _

@[simp] theorem cartier_rawSection (p : RiemannSphere) :
    cartier.rawSection p = pointSection p :=
  cartier_localFraction (data.indexAt p) p

theorem cartier_rawSectionMap : cartier.rawSectionMap = pointSectionMap := by
  funext p
  change (⟨p, cartier.rawSection p⟩ : bundle.TotalSpace) = ⟨p, pointSection p⟩
  rw [cartier_rawSection]

/-- The actual Cartier section is holomorphic even at its unique zero. -/
theorem cartier_rawSectionMap_holomorphic :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω cartier.rawSectionMap := by
  rw [cartier_rawSectionMap]
  exact pointSectionMap_holomorphic

theorem cartier_rawSection_eq_zero_iff (p : RiemannSphere) :
    cartier.rawSection p = 0 ↔ p = ((1 : ℂ) : RiemannSphere) := by
  rw [cartier_rawSection]
  exact pointSection_eq_zero_iff p

/-- The literal Cartier fraction in the finite chart is the centered coordinate. -/
theorem cartier_localFraction_centered (z : ℂ) :
    cartier.localFraction false (((1 + z : ℂ)) : RiemannSphere) = z := by
  rw [cartier_localFraction]
  change (1 + z) - 1 = z
  ring

theorem cartier_localFraction_simple_zero :
    analyticOrderAt (fun z : ℂ =>
      cartier.localFraction false (((1 + z : ℂ)) : RiemannSphere)) 0 = 1 := by
  have h : (fun z : ℂ => cartier.localFraction false
      (((1 + z : ℂ)) : RiemannSphere)) = id := funext cartier_localFraction_centered
  rw [h]
  exact analyticOrderAt_id

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase
