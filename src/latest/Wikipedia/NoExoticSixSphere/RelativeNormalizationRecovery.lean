import Wikipedia.NoExoticSixSphere.EndingPathPairProjection
import Wikipedia.NoExoticSixSphere.EndingPathPairNormalization
import Wikipedia.NoExoticSixSphere.RelativeNormalizationRecoveryLift
import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberNaturality
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# Ending-path recovery for actual normalization data in every degree

Projection is an isomorphism on all auxiliary fiber homology groups.
The two original connecting formulas give auxiliary recovery, and the
actual evaluation pair map and exact fiber section give a right inverse
for the original descended map. Only the supplied continuous normalization
data is used; existence of that data in all degrees is not assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U) (n : ℕ)

theorem normalization_transgression
    (E : RelativeNormalization.Data (subspace U a) (basepoint U a) n)
    (z : SingularHomology (Fiber (subspace U a) (basepoint U a)) (n + 2)) :
    E.fiberHomologyMap (transgression (subspace U a) (basepoint U a) (n + 2) z) = z := by
  apply (projection_homology_bijective U a (n + 2)).injective
  have h := LinearMap.congr_fun E.projection_fiberHomologyMap
    (transgression (subspace U a) (basepoint U a) (n + 2) z)
  have ht := connecting_transgression (subspace U a) (basepoint U a) (n + 2) z
  rw [CuspCentralHomology.singularHomologyMap_const_eq_zero _ _ (n + 2) (by omega),
    LinearMap.zero_apply, sub_zero] at ht
  exact h.trans ht

end NoExoticSixSphere.EndingPathPair

namespace NoExoticSixSphere.RelativeNormalization.Data

open RelativeFiberHomology EndingPathPair

variable {X : Type} [TopologicalSpace X] {U : Set X} {a : U} {n : ℕ}
  (D : Data U a n) (E : Data (subspace U a) (basepoint U a) n)

include E in
theorem fiberHomologyMap_recoveryLift (z : SingularHomology (Fiber U a) (n + 2)) :
    D.fiberHomologyMap (recoveryLift U a n z) = z := by
  have hn := LinearMap.congr_fun
    (E.fiberHomologyMap_naturality D (evaluation U a) (evaluation_mapsTo U a) rfl)
    (transgression (subspace U a) (basepoint U a) (n + 2)
      (singularHomologyMap (liftSection U a) (n + 2) z))
  have hr := normalization_transgression U a n E
    (singularHomologyMap (liftSection U a) (n + 2) z)
  have hid : singularHomologyMap (fiberEvaluation U a) (n + 2)
      (singularHomologyMap (liftSection U a) (n + 2) z) = z := by
    have hc := singularHomologyMap_comp (liftSection U a) (fiberEvaluation U a) (n + 2)
    rw [evaluation_liftSection, singularHomologyMap_id] at hc
    exact (LinearMap.congr_fun hc z).symm
  exact hn.trans ((congrArg (singularHomologyMap (fiberEvaluation U a) (n + 2)) hr).trans hid)

include E in
theorem fiberHomologyMap_surjective : Function.Surjective D.fiberHomologyMap :=
  fun z ↦ ⟨recoveryLift U a n z, D.fiberHomologyMap_recoveryLift E z⟩

include D E in
theorem fiber_homology_subsingleton [Subsingleton (RelativeSingularHomology.Homology U (n + 3))] :
    Subsingleton (SingularHomology (Fiber U a) (n + 2)) :=
  (D.fiberHomologyMap_surjective E).subsingleton

end NoExoticSixSphere.RelativeNormalization.Data

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)

theorem fiber_homology_subsingleton_of_fiberConnectivity (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n + 2 → ∀ b : U, ∀ p : Fiber U b,
      Subsingleton (π_ k (Fiber U b) p))
    [Subsingleton (RelativeSingularHomology.Homology U (n + 3))] :
    Subsingleton (SingularHomology (Fiber U a) (n + 2)) := by
  let : SimplyConnectedSpace (Fiber U a) :=
    HomotopyFiberConnectivity.simplyConnectedSpace (subtypeInclusion U) a
      (inclusion_surjective_of_fiberConnectivity U n hpi 2 (by omega) (by omega) a)
  exact (ofFiberConnectivity U a n hpi).fiber_homology_subsingleton
    (EndingPathPair.normalizationData U a n (fun k hk hkn p ↦ hpi k hk hkn a p))

end NoExoticSixSphere.RelativeNormalization
