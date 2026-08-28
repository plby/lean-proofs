import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.InverseChains
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.InverseCube
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainClassHomology

/-!
# Both constructed inverse identities for the actual seventh Hurewicz map

The actual normalized simplex-class assignment descends through the
original singular homology because the genuine signed face relation
kills every eight-boundary. Native cubical recovery proves the other
inverse identity on each original generalized seven-loop.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The genuine inverse obtained by descending the constructed singular-chain assignment. -/
def hurewiczInverse : SingularHomology X 7 →ₗ[ℤ] Additive (π_ 7 X x) :=
  HigherHurewicz.singularHomologyDesc 7 (sevenSimplexClassOperator x)
    (sevenSimplexClassOperator_boundary x)

@[simp] theorem hurewiczInverse_cycleClass (c : ModuleHomology.Cycle (singularComplex X) 7) :
    hurewiczInverse x (ModuleHomology.cycleClass (singularComplex X) 7 c) =
      sevenSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 7 _ _ c

theorem hurewiczMap_comp_hurewiczInverse :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 7 (sevenSimplexClassOperator x)
    (sevenSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_sevenSimplexClassOperator_cycle x)

@[simp] theorem hurewiczMap_hurewiczInverse (c : SingularHomology X 7) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp] theorem hurewiczInverse_hurewiczMap_mk (p : GenLoop (Fin 7) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 7 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 7 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact sevenSimplexClassOperator_cubeChain x p

/-- Recovery holds in the original quotient by homotopies relative to the whole cube boundary. -/
@[simp] theorem hurewiczInverse_hurewiczMap (a : Additive (π_ 7 X x)) :
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

/-- Bijectivity of the actual integral-linear seventh Hurewicz map. -/
theorem hurewiczMap_bijective : Function.Bijective (hurewiczMap x) :=
  ⟨hurewiczMap_injective x, hurewiczMap_surjective x⟩

/-- Bijectivity in Mathlib's original native multiplicative homotopy notation. -/
theorem hurewiczPi7_bijective : Function.Bijective (hurewiczPi7 x) := by
  constructor
  · intro a b h
    have h' : hurewiczMap x (Additive.ofMul a) = hurewiczMap x (Additive.ofMul b) :=
      congrArg Multiplicative.toAdd h
    exact congrArg Additive.toMul (hurewiczMap_injective x h')
  · exact hurewiczPi7_surjective x

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
