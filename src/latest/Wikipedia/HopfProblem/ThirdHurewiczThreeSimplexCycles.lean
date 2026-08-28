import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexFaces

/-!
# Corrected three-simplex cycles in the actual singular chain complex

A three-simplex with constant faces is a cycle in the unnormalized complex:
the four alternating constant faces cancel. Subtracting the constant
three-simplex retains this cycle condition and normalizes the constant input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The four actual constant faces cancel with their original signs. -/
theorem basedThreeSimplex_boundary (τ : BasedThreeSimplex x) :
    ((singularComplex X).d 3 2).hom (simplexChain X 3 τ.val) = 0 := by
  change (singularComplex X).d 3 2 (simplexChain X 3 τ.val) = 0
  rw [boundary_simplex]
  simp [basedThreeSimplex_face, Fin.sum_univ_succ]

/-- The normalized original singular chain of a based three-simplex. -/
def basedThreeSimplexChain (τ : BasedThreeSimplex x) : Chains X 3 :=
  simplexChain X 3 τ.val - simplexChain X 3 (ContinuousMap.const (Simplex 3) x)

theorem basedThreeSimplexChain_boundary (τ : BasedThreeSimplex x) :
    ((singularComplex X).d 3 2).hom (basedThreeSimplexChain τ) = 0 := by
  rw [basedThreeSimplexChain, map_sub, basedThreeSimplex_boundary]
  have hc := basedThreeSimplex_boundary (constantBasedThreeSimplex x)
  change ((singularComplex X).d 3 2).hom
    (simplexChain X 3 (ContinuousMap.const (Simplex 3) x)) = 0 at hc
  rw [hc, sub_self]

/-- The corrected cycle in the kernel of the original singular differential. -/
def basedThreeSimplexCycle (τ : BasedThreeSimplex x) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  ModuleHomology.mkCycle (singularComplex X) 3 (basedThreeSimplexChain τ)
    (basedThreeSimplexChain_boundary τ)

@[simp] theorem basedThreeSimplexCycle_val (τ : BasedThreeSimplex x) :
    (basedThreeSimplexCycle τ).val =
      simplexChain X 3 τ.val - simplexChain X 3 (ContinuousMap.const (Simplex 3) x) := rfl

@[simp] theorem basedThreeSimplexCycle_constant (x : X) :
    basedThreeSimplexCycle (constantBasedThreeSimplex x) = 0 := by
  apply Subtype.ext
  exact sub_self _

end Wikipedia.HopfProblem.ThirdHurewicz
