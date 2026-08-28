import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual homology coordinates on a three-fold topological sum

We iterate the proved disjoint-union equivalence in the fixed order
`A ⊕ (B ⊕ C)`. The inverse and map-out formulas retain the actual continuous
inclusions and the actual singular homology functor maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

variable (A B C : Type) [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- Actual integral singular homology of a three-fold disjoint union, in order `0,(1,2)`. -/
def tripleSumHomologyEquiv (n : ℕ) :
    SingularHomology (A ⊕ (B ⊕ C)) n ≃ₗ[ℤ]
      (SingularHomology A n × (SingularHomology B n × SingularHomology C n)) :=
  (sumHomologyEquiv A (B ⊕ C) n).trans
    (((AddEquiv.refl (SingularHomology A n)).prodCongr
      (sumHomologyEquiv B C n).toAddEquiv).toIntLinearEquiv)

@[simp] theorem tripleSumHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (A ⊕ (B ⊕ C)) n) :
    tripleSumHomologyEquiv A B C n a =
      ((sumHomologyEquiv A (B ⊕ C) n a).1,
        sumHomologyEquiv B C n (sumHomologyEquiv A (B ⊕ C) n a).2) := rfl

/-- The inverse is the sum of all three actual topological inclusion maps. -/
theorem tripleSumHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology A n × (SingularHomology B n × SingularHomology C n)) :
    (tripleSumHomologyEquiv A B C n).symm a =
      singularHomologyMap (sumInlMap A (B ⊕ C)) n a.1 +
        (singularHomologyMap ((sumInrMap A (B ⊕ C)).comp (sumInlMap B C)) n a.2.1 +
          singularHomologyMap ((sumInrMap A (B ⊕ C)).comp (sumInrMap B C)) n a.2.2) := by
  change (sumHomologyEquiv A (B ⊕ C) n).symm
    (a.1, (sumHomologyEquiv B C n).symm a.2) = _
  rw [sumHomologyEquiv_symm_apply, sumHomologyEquiv_symm_apply, map_add,
    singularHomologyMap_comp, singularHomologyMap_comp]
  rfl

@[simp] theorem tripleSumHomologyEquiv_inclusion_zero (n : ℕ)
    (a : SingularHomology A n) :
    tripleSumHomologyEquiv A B C n
        (singularHomologyMap (sumInlMap A (B ⊕ C)) n a) = (a, (0, 0)) := by
  apply (tripleSumHomologyEquiv A B C n).symm.injective
  rw [LinearEquiv.symm_apply_apply, tripleSumHomologyEquiv_symm_apply]
  simp only [map_zero, add_zero]

@[simp] theorem tripleSumHomologyEquiv_inclusion_one (n : ℕ)
    (a : SingularHomology B n) :
    tripleSumHomologyEquiv A B C n
        (singularHomologyMap ((sumInrMap A (B ⊕ C)).comp (sumInlMap B C)) n a) =
      (0, (a, 0)) := by
  apply (tripleSumHomologyEquiv A B C n).symm.injective
  rw [LinearEquiv.symm_apply_apply, tripleSumHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add, add_zero]

@[simp] theorem tripleSumHomologyEquiv_inclusion_two (n : ℕ)
    (a : SingularHomology C n) :
    tripleSumHomologyEquiv A B C n
        (singularHomologyMap ((sumInrMap A (B ⊕ C)).comp (sumInrMap B C)) n a) =
      (0, (0, a)) := by
  apply (tripleSumHomologyEquiv A B C n).symm.injective
  rw [LinearEquiv.symm_apply_apply, tripleSumHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add]

variable {A B C} {D : Type} [TopologicalSpace D]

/-- A continuous map defined on the three summands acts by the sum of its actual maps. -/
theorem tripleSumHomologyEquiv_sumElim_symm
    (f : C(A, D)) (g : C(B, D)) (h : C(C, D)) (n : ℕ)
    (a : SingularHomology A n × (SingularHomology B n × SingularHomology C n)) :
    singularHomologyMap (sumElimMap f (sumElimMap g h)) n
        ((tripleSumHomologyEquiv A B C n).symm a) =
      singularHomologyMap f n a.1 +
        (singularHomologyMap g n a.2.1 + singularHomologyMap h n a.2.2) := by
  change singularHomologyMap (sumElimMap f (sumElimMap g h)) n
    ((sumHomologyEquiv A (B ⊕ C) n).symm
      (a.1, (sumHomologyEquiv B C n).symm a.2)) = _
  rw [sumHomologyEquiv_sumElim_symm, sumHomologyEquiv_sumElim_symm]

/-- Map-out formula on an arbitrary actual homology class of the three-fold sum. -/
theorem tripleSumHomologyEquiv_sumElim
    (f : C(A, D)) (g : C(B, D)) (h : C(C, D)) (n : ℕ)
    (a : SingularHomology (A ⊕ (B ⊕ C)) n) :
    singularHomologyMap (sumElimMap f (sumElimMap g h)) n a =
      singularHomologyMap f n (tripleSumHomologyEquiv A B C n a).1 +
        (singularHomologyMap g n (tripleSumHomologyEquiv A B C n a).2.1 +
          singularHomologyMap h n (tripleSumHomologyEquiv A B C n a).2.2) := by
  have hmap := tripleSumHomologyEquiv_sumElim_symm f g h n
    (tripleSumHomologyEquiv A B C n a)
  rwa [LinearEquiv.symm_apply_apply] at hmap

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
