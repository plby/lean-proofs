import Wikipedia.HopfProblem.SheafLerayCurveSequence

/-!
# Native Leray short exact sequences in degrees two and three

The displayed hypotheses are explicit cohomology vanishings of the
actual right-derived sheaf pushforwards. The conclusions retain the
original maps and native Ext groups. No assertion about all abelian
sheaves on a curve, or about a value of any higher direct image, is made.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)

/-- The genuine degree-two sequence
`0 → H¹(Y,R¹f_*F) → H²(X,F) → H⁰(Y,R²f_*F) → 0`,
under precisely the three sufficient actual vanishings shown here. -/
theorem degreeTwo_short_exact
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2)) :
    Function.Injective (inflation f F 0 (cohomologyVanishing_three f F h02 h03 h12)) ∧
      Function.Exact (inflation f F 0 (cohomologyVanishing_three f F h02 h03 h12))
        (edge f F 0) ∧ Function.Surjective (edge f F 0) :=
  short_exact f F 0 (cohomologyVanishing_three f F h02 h03 h12)

/-- The same degree-two statement as genuine categorical short exactness. -/
theorem degreeTwo_shortExact
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2)) :
    (sequence f F 0 (cohomologyVanishing_three f F h02 h03 h12)).ShortExact :=
  sequence_shortExact f F 0 (cohomologyVanishing_three f F h02 h03 h12)

/-- The genuine degree-three sequence
`0 → H¹(Y,R²f_*F) → H³(X,F) → H⁰(Y,R³f_*F) → 0`,
under the six sufficient actual vanishings in the required finite range. -/
theorem degreeThree_short_exact
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h04 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 4))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2))
    (h13 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 3))
    (h22 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 2) 2)) :
    Function.Injective
        (inflation f F 1 (cohomologyVanishing_four f F h02 h03 h04 h12 h13 h22)) ∧
      Function.Exact
        (inflation f F 1 (cohomologyVanishing_four f F h02 h03 h04 h12 h13 h22))
        (edge f F 1) ∧ Function.Surjective (edge f F 1) :=
  short_exact f F 1 (cohomologyVanishing_four f F h02 h03 h04 h12 h13 h22)

/-- The same degree-three statement as genuine categorical short exactness. -/
theorem degreeThree_shortExact
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h04 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 4))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2))
    (h13 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 3))
    (h22 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 2) 2)) :
    (sequence f F 1 (cohomologyVanishing_four f F h02 h03 h04 h12 h13 h22)).ShortExact :=
  sequence_shortExact f F 1 (cohomologyVanishing_four f F h02 h03 h04 h12 h13 h22)

end Wikipedia.HopfProblem.SheafLerayCurve
