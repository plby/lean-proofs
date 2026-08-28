import Wikipedia.HopfProblem.ThirdHurewiczHomologyDescent

/-!
# Constant singular three-simplices are actual boundaries

The five faces of the constant four-simplex have alternating signs
`+,-,+,-,+`; its boundary is exactly the constant three-simplex. Thus the
constant three-simplex represents zero in actual singular third homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The genuine singular generator of the constant three-simplex. -/
def constantThreeChain (x : X) : Chains X 3 :=
  simplexChain X 3 (ContinuousMap.const (Simplex 3) x)

/-- The genuine singular generator of the constant four-simplex. -/
def constantFourChain (x : X) : Chains X 4 :=
  simplexChain X 4 (ContinuousMap.const (Simplex 4) x)

/-- The four constant triangle faces cancel with alternating signs. -/
theorem boundaryThree_constantThreeChain (x : X) :
    ((singularComplex X).d 3 2).hom (constantThreeChain x) = 0 := by
  rw [constantThreeChain, boundary_simplex]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val •
    simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) = 0
  simp [Fin.sum_univ_succ]

/-- The constant four-simplex is an explicit actual boundary witness. -/
theorem boundaryFour_constantFourChain (x : X) :
    ((singularComplex X).d 4 3).hom (constantFourChain x) = constantThreeChain x := by
  rw [constantFourChain, boundary_simplex]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • constantThreeChain x) = constantThreeChain x
  simp [Fin.sum_univ_succ]

/-- The constant three-simplex as an actual singular three-cycle. -/
def constantThreeCycle (x : X) : ModuleHomology.Cycle (singularComplex X) 3 :=
  ModuleHomology.mkCycle (singularComplex X) 3 (constantThreeChain x)
    (boundaryThree_constantThreeChain x)

@[simp] theorem constantThreeCycle_val (x : X) :
    (constantThreeCycle x).1 = constantThreeChain x := rfl

/-- Its class vanishes in the original categorical singular homology group. -/
@[simp] theorem constantThreeCycle_class (x : X) :
    ModuleHomology.cycleClass (singularComplex X) 3 (constantThreeCycle x) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) 3 _).mpr
  exact ⟨constantFourChain x, boundaryFour_constantFourChain x⟩

end Wikipedia.HopfProblem.ThirdHurewicz
