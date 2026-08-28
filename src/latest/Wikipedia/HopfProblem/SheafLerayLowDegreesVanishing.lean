import Wikipedia.HopfProblem.SheafLerayLowDegreesSequence

/-!
# The actual Leray edge map when the two outer groups vanish

This is a consequence of the proved unconditional low-degree sequence.
The comparison is the actual edge map, not an equivalence chosen from
dimensions or from a replacement cohomology model.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)
  [Subsingleton (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 2)]

/-- Vanishing of the two actual outer groups makes the actual edge map bijective. -/
theorem edge_bijective_of_vanishing : Function.Bijective (edge f F) := by
  constructor
  · intro a b hab
    have hz : edge f F (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := (exact_inflation_edge f F (a - b)).mp hz
    apply sub_eq_zero.mp
    exact hc.symm.trans ((congrArg (inflation f F) (Subsingleton.elim c 0)).trans (map_zero _))
  · intro a
    exact (exact_edge_transgression f F a).mp (Subsingleton.elim _ _)

/-- The actual edge map becomes an additive equivalence after the
proved vanishing conditions have been supplied. -/
def edgeEquivOfVanishing :
    CategoryTheory.Sheaf.H.{0} F 1 ≃+
      CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 :=
  AddEquiv.ofBijective (edge f F) (edge_bijective_of_vanishing f F)

@[simp] theorem edgeEquivOfVanishing_apply (x : CategoryTheory.Sheaf.H.{0} F 1) :
    edgeEquivOfVanishing f F x = edge f F x := rfl

end Wikipedia.HopfProblem.SheafLerayLowDegrees
