import Wikipedia.NoExoticSixSphere.EndingPathPairRecovery
import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberNaturality

/-!
# Actual second fiber homology is detected by third relative homology

The ending-path pair supplies a right inverse to the descended map. Its
evaluation map of pairs and explicit fiber section transport recovery to
the original fiber. This proves surjectivity without requiring a separate
naturality theorem for the original singular prism.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeFiberHomology EndingPathPair

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def recoveryLift : SingularHomology (Fiber U a) 2 →ₗ[ℤ] RelativeSingularHomology.Homology U 3 :=
  (RelativeSingularHomology.map (evaluation U a) (evaluation_mapsTo U a) 3).comp
    ((transgression (subspace U a) (basepoint U a) 2).comp
      (singularHomologyMap (liftSection U a) 2))

variable [SimplyConnectedSpace X] [SimplyConnectedSpace U]
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

theorem homologyMap_recoveryLift (z : SingularHomology (Fiber U a) 2) :
    homologyMap U a hπ (recoveryLift U a z) = z := by
  let : SimplyConnectedSpace (Fiber U a) :=
    HomotopyFiberConnectivity.simplyConnectedSpace (subtypeInclusion U) a hπ
  let := subspace_simplyConnected U a
  have hn := LinearMap.congr_fun
    (homologyMap_naturality (subspace U a) U (basepoint U a) a
      (inclusion_surjective U a 2) hπ (evaluation U a) (evaluation_mapsTo U a) rfl)
    (transgression (subspace U a) (basepoint U a) 2
      (singularHomologyMap (liftSection U a) 2 z))
  have hr := EndingPathPair.homologyMap_transgression U a
    (singularHomologyMap (liftSection U a) 2 z)
  have hid : singularHomologyMap (fiberEvaluation U a) 2
      (singularHomologyMap (liftSection U a) 2 z) = z := by
    have hc := singularHomologyMap_comp (liftSection U a) (fiberEvaluation U a) 2
    rw [evaluation_liftSection, singularHomologyMap_id] at hc
    exact (LinearMap.congr_fun hc z).symm
  exact hn.trans ((congrArg (singularHomologyMap (fiberEvaluation U a) 2) hr).trans hid)

theorem homologyMap_surjective : Function.Surjective (homologyMap U a hπ) :=
  fun z ↦ ⟨recoveryLift U a z, homologyMap_recoveryLift U a hπ z⟩

include hπ in
theorem fiber_homologyTwo_subsingleton
    [Subsingleton (RelativeSingularHomology.Homology U 3)] :
    Subsingleton (SingularHomology (Fiber U a) 2) :=
  (homologyMap_surjective U a hπ).subsingleton

end NoExoticSixSphere.RelativeNormalizedFiberClasses
