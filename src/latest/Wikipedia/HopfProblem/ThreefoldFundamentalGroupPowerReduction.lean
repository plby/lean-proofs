import Wikipedia.HopfProblem.ThreefoldFundamentalGroupLattice
import Wikipedia.HopfProblem.FundamentalGroupPresentationRealization

/-!
# The final algebraic step for the actual marked threefold group

All topology, generation, cusp, and lattice relations used here have
already been proved for the constructed space.  This reduction isolates
the two remaining elliptic power identities.  It does not assert those
identities: their geometric comparison with the joint meridians is
performed separately.  A common orientation reversal changes only the
choice of the central generator.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

/-- The central generator corresponding to the common meridian orientation. -/
def orientedCentral (reverse : Bool) : GlobalGroup := if reverse then c else c⁻¹

@[simp] theorem orientedCentral_false : orientedCentral false = c⁻¹ := rfl

@[simp] theorem orientedCentral_true : orientedCentral true = c := rfl

theorem orientedCentral_commute (reverse : Bool) (g : GlobalGroup) :
    Commute (orientedCentral reverse) g := all_commute _ _

theorem c_eq_one_of_orientedCentral_eq_one (reverse : Bool)
    (h : orientedCentral reverse = 1) : c = 1 := by
  cases reverse with
  | false => exact inv_eq_one.mp h
  | true => exact h

/-- The checked main presentation applies once the two actual elliptic
power identities have been established with the same orientation. -/
theorem trivial_of_oriented_elliptic_power_relations (reverse : Bool)
    (h₃ : meridian false ^ 3 = orientedCentral reverse)
    (h₄ : meridian true ^ 4 = (orientedCentral reverse)⁻¹) :
    ∀ g : GlobalGroup, g = 1 := by
  have hgen := TwistGroup.main_realization_generators_eq_one
    (orientedCentral reverse) (meridian false) (meridian true)
    (orientedCentral_commute reverse _) (orientedCentral_commute reverse _)
    meridian_product_eq_one h₃ h₄
  have hc : c = 1 := c_eq_one_of_orientedCentral_eq_one reverse hgen.1
  have hid : MonoidHom.id GlobalGroup = 1 := by
    apply hom_eq_one
    · intro v
      change latticeHom (Multiplicative.ofAdd v.toAdd) = 1
      rw [latticeHom_eq_c_zpow, hc, one_zpow]
    · intro b
      cases b
      · exact hgen.2.1
      · exact hgen.2.2
  intro g
  exact DFunLike.congr_fun hid g

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
