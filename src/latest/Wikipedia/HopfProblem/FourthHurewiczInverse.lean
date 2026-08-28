import Wikipedia.HopfProblem.FourthHurewiczInverseChains
import Wikipedia.HopfProblem.FourthHurewiczInverseCube

/-!
# Both constructed inverse identities for the actual fourth Hurewicz map

The actual normalized simplex-class assignment descends through the
original singular homology because the genuine signed face relation
kills every five-boundary. Native cubical recovery proves the other
inverse identity on each original generalized four-loop.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The genuine inverse obtained by descending the constructed singular-chain assignment. -/
def hurewiczInverse : SingularHomology X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  HigherHurewicz.singularHomologyDesc 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x)

@[simp] theorem hurewiczInverse_cycleClass (c : ModuleHomology.Cycle (singularComplex X) 4) :
    hurewiczInverse x (ModuleHomology.cycleClass (singularComplex X) 4 c) =
      fourSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 4 _ _ c

theorem hurewiczMap_comp_hurewiczInverse :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_fourSimplexClassOperator_cycle x)

@[simp] theorem hurewiczMap_hurewiczInverse (c : SingularHomology X 4) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp] theorem hurewiczInverse_hurewiczMap_mk (p : GenLoop (Fin 4) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 4 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 4 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact fourSimplexClassOperator_cubeChain x p

/-- Recovery holds in the original quotient by homotopies relative to the whole cube boundary. -/
@[simp] theorem hurewiczInverse_hurewiczMap (a : Additive (π_ 4 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
    Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem hurewiczInverse_comp_hurewiczMap :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

theorem hurewiczMap_injective : Function.Injective (hurewiczMap x) :=
  Function.LeftInverse.injective (hurewiczInverse_hurewiczMap x)

/-- Bijectivity of the actual integral-linear fourth Hurewicz map. -/
theorem hurewiczMap_bijective : Function.Bijective (hurewiczMap x) :=
  ⟨hurewiczMap_injective x, hurewiczMap_surjective x⟩

/-- Bijectivity in Mathlib's original native multiplicative homotopy notation. -/
theorem hurewiczPi4_bijective : Function.Bijective (hurewiczPi4 x) := by
  constructor
  · intro a b h
    have h' : hurewiczMap x (Additive.ofMul a) = hurewiczMap x (Additive.ofMul b) :=
      congrArg Multiplicative.toAdd h
    exact congrArg Additive.toMul (hurewiczMap_injective x h')
  · exact hurewiczPi4_surjective x

end Wikipedia.HopfProblem.FourthHurewicz
