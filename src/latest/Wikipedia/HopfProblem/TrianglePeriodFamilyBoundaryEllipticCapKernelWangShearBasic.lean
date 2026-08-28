import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition

/-!
# Literal circle shears in the five-dimensional product torus

The shear subtracts a continuous character from the first circle coordinate
and preserves all four remaining coordinates. Coordinate splitting identifies
the two displayed continuous maps exactly, before passage to homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open PeriodTorusHigherHomology CircleTopology

/-- Subtract the circle-valued function from the first coordinate. -/
def shear (χ : C(ProductTorus 4, Circle)) : C(Circle × ProductTorus 4, Circle × ProductTorus 4) :=
  ⟨fun p => (p.1 - χ p.2, p.2),
    (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk continuous_snd⟩

@[simp] theorem shear_apply (χ : C(ProductTorus 4, Circle)) (p : Circle × ProductTorus 4) :
    shear χ p = (p.1 - χ p.2, p.2) := rfl

/-- The same shear on the original five circle coordinates. -/
def torusShear (χ : C(ProductTorus 4, Circle)) : C(ProductTorus 5, ProductTorus 5) where
  toFun z := Fin.cons (z 0 - χ (fun i => z i.succ)) (fun i => z i.succ)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (continuous_apply 0).sub
        (χ.continuous.comp (continuous_pi fun j => continuous_apply j.succ))
    · exact continuous_apply j.succ

@[simp] theorem torusShear_apply (χ : C(ProductTorus 4, Circle)) (z : ProductTorus 5) :
    torusShear χ z = Fin.cons (z 0 - χ (fun i => z i.succ)) (fun i => z i.succ) := rfl

/-- Exact conjugacy by the native coordinate-splitting homeomorphism. -/
theorem torusShear_comp_unsplit (χ : C(ProductTorus 4, Circle)) :
    (torusShear χ).comp
        ((productTorusSuccHomeomorph 4).symm : C(Circle × ProductTorus 4, ProductTorus 5)) =
      ((productTorusSuccHomeomorph 4).symm : C(Circle × ProductTorus 4, ProductTorus 5)).comp
        (shear χ) := rfl

/-- An additive circle-valued map sends zero to the native circle zero. -/
theorem character_zero (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) : χ 0 = 0 := by
  have h : χ 0 + χ 0 = χ 0 + 0 := by
    simpa only [zero_add, add_zero] using (hχ 0 0).symm
  exact add_left_cancel h

/-- A shear by an actual additive character is an additive continuous map. -/
theorem torusShear_add (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (z w : ProductTorus 5) :
    torusShear χ (z + w) = torusShear χ z + torusShear χ w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change z 0 + w 0 - χ ((fun j => z j.succ) + (fun j => w j.succ)) =
      (z 0 - χ (fun j => z j.succ)) + (w 0 - χ (fun j => w j.succ))
    rw [hχ]
    abel
  · rfl

@[simp] theorem torusShear_zero (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) : torusShear χ 0 = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 0 - χ 0 = 0
    rw [character_zero χ hχ, sub_self]
  · rfl

/-- A character shear fixes the entire first-coordinate circle insertion. -/
theorem torusShear_comp_head (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) :
    (torusShear χ).comp (torusHeadCircleMap 4) = torusHeadCircleMap 4 := by
  apply ContinuousMap.ext
  intro z
  change torusShear χ (torusHeadCircleMap 4 z) = torusHeadCircleMap 4 z
  rw [torusHeadCircleMap_apply, torusShear_apply]
  change Fin.cons (α := fun _ : Fin 5 => Circle) (z - χ 0) 0 = Fin.cons z 0
  rw [character_zero χ hχ, sub_zero]

/-- On the tail subtorus, the exact map is the tail insertion minus the
character followed by the first-circle insertion. -/
theorem torusShear_comp_tail (χ : C(ProductTorus 4, Circle)) :
    (torusShear χ).comp (torusTailMap 4) =
      torusTailMap 4 - (torusHeadCircleMap 4).comp χ := by
  apply ContinuousMap.ext
  intro x
  change torusShear χ (torusTailMap 4 x) =
    torusTailMap 4 x - torusHeadCircleMap 4 (χ x)
  simp only [torusTailMap_apply, torusShear_apply, torusHeadCircleMap_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
