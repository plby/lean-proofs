import Wikipedia.HopfProblem.ThirdHurewiczInverseChains
import Wikipedia.HopfProblem.ThirdHurewiczInverseCube

/-!
# Both inverse identities for the genuine third Hurewicz map

The actual normalized-three-simplex assignment kills genuine four-boundaries
by the native five-face relation, so it descends to original singular
homology. Actual cubical subdivision and boundary-fixed normalization prove
the opposite inverse law on every original native third-homotopy class.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The genuine constructed inverse, descended from the actual singular-chain assignment. -/
def hurewiczInverse : SingularHomology X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  thirdHomologyDesc (threeSimplexClassOperator x) (threeSimplexClassOperator_boundary x)

@[simp] theorem hurewiczInverse_cycleClass (c : ModuleHomology.Cycle (singularComplex X) 3) :
    hurewiczInverse x (ModuleHomology.cycleClass (singularComplex X) 3 c) =
      threeSimplexClassOperator x c.val :=
  thirdHomologyDesc_cycleClass _ _ c

theorem hurewiczMap_comp_hurewiczInverse :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_thirdHomologyDesc_eq_id (threeSimplexClassOperator x)
    (threeSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_threeSimplexClassOperator_cycle x)

@[simp] theorem hurewiczMap_hurewiczInverse (c : SingularHomology X 3) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp] theorem hurewiczInverse_hurewiczMap_mk (p : GenLoop (Fin 3) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 3 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact threeSimplexClassOperator_cubeChain x p

/-- Recovery holds in the original native boundary-relative homotopy quotient. -/
@[simp] theorem hurewiczInverse_hurewiczMap (a : Additive (π_ 3 X x)) :
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

/-- Bijectivity of the actual integral-linear third Hurewicz map. -/
theorem hurewiczMap_bijective : Function.Bijective (hurewiczMap x) :=
  ⟨hurewiczMap_injective x, hurewiczMap_surjective x⟩

/-- Bijectivity in Mathlib's original multiplicative notation for native `π₃`. -/
theorem hurewiczPi3_bijective : Function.Bijective (hurewiczPi3 x) := by
  constructor
  · intro a b h
    have h' : hurewiczMap x (Additive.ofMul a) = hurewiczMap x (Additive.ofMul b) :=
      congrArg Multiplicative.toAdd h
    exact congrArg Additive.toMul (hurewiczMap_injective x h')
  · exact hurewiczPi3_surjective x

end Wikipedia.HopfProblem.ThirdHurewicz
