import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductUnit
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsTopClass
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusLoops

/-!
# Circle splitting and the actual Pontryagin product of a torus

Adding the first-circle insertion and the tail-torus insertion is exactly
the inverse coordinate-splitting homeomorphism. Naturality of the actual
cross product therefore identifies the positive circle-product summand
with the actual Pontryagin product. The proved Mayer--Vietoris normalization
of each torus top class is preserved by this identification.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris CircleTopology

/-- Insert a circle as the first coordinate and set all other coordinates to zero. -/
def torusHeadCircleMap (n : ℕ) : C(Circle, ProductTorus (n + 1)) :=
  coordinateCircleMap (Pi.single (0 : Fin (n + 1)) 1)

@[simp] theorem torusHeadCircleMap_apply (n : ℕ) (z : Circle) :
    torusHeadCircleMap n z = Fin.cons z 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]

/-- Insert the tail coordinates after a fixed zero first coordinate. -/
def torusTailMap (n : ℕ) : C(ProductTorus n, ProductTorus (n + 1)) :=
  ((productTorusSuccHomeomorph n).symm : C(_, _)).comp (productSection (ProductTorus n))

@[simp] theorem torusTailMap_apply (n : ℕ) (x : ProductTorus n) :
    torusTailMap n x = Fin.cons 0 x := rfl

theorem torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

@[simp] theorem torusTailMap_zero (n : ℕ) : torusTailMap n 0 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

/-- The tail insertion carries the actual vector loop to the tuple with an initial zero. -/
theorem torusTailMap_coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusTailMap n).continuous =
      (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)).cast (torusTailMap_zero n)
        (torusTailMap_zero n) := by
  apply Path.ext
  funext t
  apply funext
  intro i
  change torusTailMap n (coordinatePeriodLoop n v t) i =
    coordinatePeriodLoop (n + 1) (Fin.cons 0 v) t i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]

theorem torusTailMap_coordinatePeriodHomology (n : ℕ) (v : Fin n → ℤ) :
    singularHomologyMap (torusTailMap n) 1
        (loopHomologyClass (coordinatePeriodLoop n v)) =
      loopHomologyClass (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)) := by
  rw [singularHomologyMap_one, inducedHomology_loopHomologyClass,
    torusTailMap_coordinatePeriodLoop]
  rfl

/-- The inverse splitting is literally the addition of the two coordinate insertions. -/
theorem productTorusSucc_inverse_eq_add (n : ℕ) :
    ((productTorusSuccHomeomorph n).symm : C(Circle × ProductTorus n, ProductTorus (n + 1))) =
      (PeriodTorusHigherHomologyPontryagin.additionMap (ProductTorus (n + 1))).comp
        ((torusHeadCircleMap n).prodMap (torusTailMap n)) := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  change Fin.cons z x = torusHeadCircleMap n z + torusTailMap n x
  rw [torusHeadCircleMap_apply, torusTailMap_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- A circle cross product becomes the actual Pontryagin product of the insertion images. -/
theorem torusSplit_positiveCircleCross (r n : ℕ) (b : SingularHomology (ProductTorus r) n) :
    singularHomologyMap ((productTorusSuccHomeomorph r).symm : C(_, _)) (n + 1)
        (positiveCircleCross (ProductTorus r) n b) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (r + 1)) n
        (singularHomologyMap (torusHeadCircleMap r) 1
          (loopHomologyClass CirclePaths.positiveLoop))
        (singularHomologyMap (torusTailMap r) n b) := by
  rw [PeriodTorusHigherHomologyPontryagin.product_apply]
  have h := crossProductHomology_natural (torusHeadCircleMap r) (torusTailMap r) n
    (loopHomologyClass CirclePaths.positiveLoop) b
  rw [← h]
  rw [productTorusSucc_inverse_eq_add, singularHomologyMap_comp]
  rfl

/-- The first-circle insertion sends the positive loop to the first coordinate period loop. -/
theorem torusHeadCircleMap_positiveHomology (n : ℕ) :
    singularHomologyMap (torusHeadCircleMap n) 1 (loopHomologyClass CirclePaths.positiveLoop) =
      loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)) :=
  coordinateCircleMap_positiveHomology (Pi.single (0 : Fin (n + 1)) 1)

/-- The actual top class is the positive circle cross product of the previous top class. -/
theorem productTorusTopClass_succ_cross (n : ℕ) :
    productTorusTopClass (n + 1) =
      singularHomologyMap ((productTorusSuccHomeomorph n).symm : C(_, _)) (n + 1)
        (positiveCircleCross (ProductTorus n) n (productTorusTopClass n)) := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).injective
  apply (circleProductHomologyEquiv (ProductTorus n) n).injective
  rw [productTorusTopClass_succ_coordinates]
  change (0, productTorusTopClass n) =
    circleProductHomologyEquiv (ProductTorus n) n
      (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
        ((homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).symm
          (positiveCircleCross (ProductTorus n) n (productTorusTopClass n))))
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_positiveCircleCross]

/-- Recursive top classes are actual products of the positive first loop and the tail top class. -/
theorem productTorusTopClass_succ_product (n : ℕ) :
    productTorusTopClass (n + 1) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (n + 1)) n
        (loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)))
        (singularHomologyMap (torusTailMap n) n (productTorusTopClass n)) := by
  rw [productTorusTopClass_succ_cross, torusSplit_positiveCircleCross,
    torusHeadCircleMap_positiveHomology]

/-- The normalized one-dimensional torus top class is its actual positive coordinate loop. -/
theorem productTorusTopClass_one :
    productTorusTopClass 1 = loopHomologyClass (coordinatePeriodLoop 1 (Pi.single 0 1)) := by
  rw [productTorusTopClass_succ_cross, productTorusTopClass_zero, positiveCircleCross,
    crossProductHomology_pointClass_right]
  have hmap : ((productTorusSuccHomeomorph 0).symm :
        C(Circle × ProductTorus 0, ProductTorus 1)).comp
      (crossInsertRight (0 : ProductTorus 0)) = torusHeadCircleMap 0 := by
    apply ContinuousMap.ext
    intro z
    rw [torusHeadCircleMap_apply]
    rfl
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hmap]
  exact torusHeadCircleMap_positiveHomology 0

/-- The normalized two-torus class is the actual product of its two positive coordinate loops. -/
theorem productTorusTopClass_two :
    productTorusTopClass 2 =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus 2) 1
        (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_one,
    torusTailMap_coordinatePeriodHomology]
  congr 3
  decide

/-- The normalized three-torus class is the actual ordered product of its positive loops. -/
theorem productTorusTopClass_three :
    productTorusTopClass 3 =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 2 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_two,
    PeriodTorusHigherHomologyPontryagin.product_natural (torusTailMap 2) (torusTailMap_add 2),
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology]
  have h₁ : Fin.cons 0 (Pi.single 0 1 : Fin 2 → ℤ) = (Pi.single 1 1 : Fin 3 → ℤ) := by
    decide
  have h₂ : Fin.cons 0 (Pi.single 1 1 : Fin 2 → ℤ) = (Pi.single 2 1 : Fin 3 → ℤ) := by
    decide
  rw [h₁, h₂]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
