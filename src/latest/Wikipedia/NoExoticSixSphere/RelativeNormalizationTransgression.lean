import Wikipedia.NoExoticSixSphere.RelativeFiberHomologyNaturality
import Wikipedia.NoExoticSixSphere.RelativeNormalizationRecovery

/-!
# Recovery is a left inverse for the original evaluation transgression

Naturality of the actual signed prism identifies the ending-path recovery
lift with the original transgression. The previously constructed recovery
therefore proves injectivity of this original homology map whenever the
specified source and ending-path normalization data have been constructed.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology EndingPathPair

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

theorem recoveryLift_eq_transgression (n : ℕ) :
    recoveryLift U a n = transgression U a (n + 2) := by
  apply LinearMap.ext
  intro z
  change RelativeSingularHomology.map (evaluation U a) (evaluation_mapsTo U a) (n + 3)
    (transgression (subspace U a) (EndingPathPair.basepoint U a) (n + 2)
      (singularHomologyMap (liftSection U a) (n + 2) z)) = transgression U a (n + 2) z
  rw [transgression_natural (evaluation U a) (evaluation_mapsTo U a)
    (EndingPathPair.basepoint U a) a rfl]
  change transgression U a (n + 2)
    (singularHomologyMap (fiberEvaluation U a) (n + 2)
      (singularHomologyMap (liftSection U a) (n + 2) z)) = _
  apply congrArg (transgression U a (n + 2))
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, evaluation_liftSection,
    singularHomologyMap_id, LinearMap.id_apply]

namespace Data

variable {U a} {n : ℕ} (D : Data U a n)
  (E : Data (subspace U a) (EndingPathPair.basepoint U a) n)

include E in
theorem fiberHomologyMap_transgression (z : SingularHomology (Fiber U a) (n + 2)) :
    D.fiberHomologyMap (transgression U a (n + 2) z) = z := by
  rw [← recoveryLift_eq_transgression]
  exact D.fiberHomologyMap_recoveryLift E z

include D E in
theorem transgression_injective : Function.Injective (transgression U a (n + 2)) := by
  intro x y hxy
  calc
    x = D.fiberHomologyMap (transgression U a (n + 2) x) :=
      (D.fiberHomologyMap_transgression E x).symm
    _ = D.fiberHomologyMap (transgression U a (n + 2) y) := congrArg D.fiberHomologyMap hxy
    _ = y := D.fiberHomologyMap_transgression E y

end Data

end NoExoticSixSphere.RelativeNormalization
