import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupNativeProduct
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupConstants

/-!
# The actual determinant in the original Haar coordinates

The formula is derived from multiplication of genuine native closed
Dolbeault representatives. Both coordinate maps are the original
Haar-mean comparisons; neither is changed to fix a sign or define cup.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

/-- Cup of literal constant native classes is the actual constant determinant class. -/
theorem cup_constants (a b : Fin 2 → ℂ) :
    cup p (h1Constant p a) (h1Constant p b) =
      h2Constant p (a 0 * b 1 - a 1 * b 0) :=
  (congrArg₂ (fun x y => cup p x y)
    (nativeH1Class_constant p a).symm (nativeH1Class_constant p b).symm).trans
      ((cup_nativeH1Class p (GlobalFourier.constantPairSection p a)
        (GlobalFourier.constantPairSection p b) (GlobalFourier.top_constantPairSection p a)
        (GlobalFourier.top_constantPairSection p b)).trans
          ((congrArg (nativeH2Class p) (constantPair_wedge p a b)).trans
            (nativeH2Class_constant p (a 0 * b 1 - a 1 * b 0))))

/-- The actual native cup is the class of the determinant of the original Haar markings. -/
theorem cup_eq_marked (a b : H p 1) :
    cup p a b = h2Constant p
      (h1Equiv p a 0 * h1Equiv p b 1 - h1Equiv p a 1 * h1Equiv p b 0) :=
  (congrArg₂ (fun x y => cup p x y)
    (h1Constant_marked p a).symm (h1Constant_marked p b).symm).trans
      (cup_constants p (h1Equiv p a) (h1Equiv p b))

/-- The original degree-two Haar mean of the actual cup is the positive determinant. -/
theorem h2Equiv_cup (a b : H p 1) :
    h2Equiv p (cup p a b) =
      h1Equiv p a 0 * h1Equiv p b 1 - h1Equiv p a 1 * h1Equiv p b 0 :=
  (congrArg (h2Equiv p) (cup_eq_marked p a b)).trans (h2Equiv_constant p _)

/-- The same formula with the original, unaliased native holomorphic cup map. -/
theorem h2Equiv_native_cup (a b : H p 1) :
    h2Equiv p (SheafCupProduct.holomorphicCup
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus a b) =
      h1Equiv p a 0 * h1Equiv p b 1 - h1Equiv p a 1 * h1Equiv p b 0 :=
  h2Equiv_cup p a b

/-- The two actual unit-marked degree-one classes cup to the actual unit-marked top class. -/
theorem cup_marked_generators :
    cup p (h1Constant p ![1, 0]) (h1Constant p ![0, 1]) = h2Constant p 1 := by
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_mul, sub_zero] using (cup_constants p ![1, 0] ![0, 1])

theorem cup_marked_generators_ne_zero :
    cup p (h1Constant p ![1, 0]) (h1Constant p ![0, 1]) ≠ 0 := by
  rw [cup_marked_generators]
  exact h2Constant_one_ne_zero p

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
