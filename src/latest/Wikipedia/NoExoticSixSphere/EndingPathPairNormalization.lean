import Wikipedia.NoExoticSixSphere.EndingPathPairProjection
import Wikipedia.NoExoticSixSphere.EndingPathHigherHomotopy
import Wikipedia.NoExoticSixSphere.HomotopyEquivNativeConnectivity
import Wikipedia.NoExoticSixSphere.RelativeNormalizationConnectivity

/-!
# Actual ending-path normalization in every bounded connectivity range

The auxiliary inclusion fiber is homotopy equivalent to the original
fiber: its additional factor is the contractible actual ending-path loop
space. Native connectivity transfers at every point. This constructs the
auxiliary normalization from the original fiber's connectivity alone.
-/

noncomputable section

open scoped Topology ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def fiberEquiv : Fiber (subspace U a) (basepoint U a) ≃ₕ Fiber U a := by
  let : ContractibleSpace (EndingPath.Loops a.val) := EndingPath.loops_contractible a.val
  exact (fiberProductEquiv U a).trans
    (((Homeomorph.prodComm _ _).toHomotopyEquiv.trans
      (CircleTopology.contractibleProdHomotopyEquiv (EndingPath.Loops a.val) (subspace U a))).trans
        (homeomorph U a).symm.toHomotopyEquiv)

theorem fiber_pi_subsingleton (n : ℕ) (hn : 0 < n)
    (hpi : ∀ p : Fiber U a, Subsingleton (π_ n (Fiber U a) p))
    (q : Fiber (subspace U a) (basepoint U a)) :
    Subsingleton (π_ n (Fiber (subspace U a) (basepoint U a)) q) :=
  HomotopyEquivNativeConnectivity.subsingleton (fiberEquiv U a) hn hpi q

def normalizationData [SimplyConnectedSpace (Fiber U a)] (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n + 2 → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p)) :
    RelativeNormalization.Data (subspace U a) (basepoint U a) n := by
  let := subspace_simplyConnected U a
  let : SimplyConnectedSpace (Fiber (subspace U a) (basepoint U a)) := fiber_simplyConnected U a
  exact RelativeNormalization.ofConnectivity (subspace U a) (basepoint U a) n
    (fun k hk hkn q ↦ fiber_pi_subsingleton U a k hk (hpi k hk hkn) q)
    (fun d _ _ b ↦ inclusion_surjective_at U a d b)

end NoExoticSixSphere.EndingPathPair
