import Wikipedia.NoExoticSixSphere.RelativeNormalizationStep
import Wikipedia.NoExoticSixSphere.RelativeNormalizationPairHomotopy
import Wikipedia.NoExoticSixSphere.HomotopyFiberConnectivity

/-!
# Actual normalization in every bounded connectivity range

The two-skeleton construction supplies the initial data. The proved
successor construction then compresses each additional simplex dimension,
using only native fiber connectivity and surjectivity of the original
inclusion in the specified finite range.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere

namespace RelativeTwoSkeletonNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def data : RelativeNormalization.Data U a 0 where
  homotopy := homotopy U a hπ
  initial := homotopy_zero U a hπ
  face := homotopy_face U a hπ
  preserves := homotopy_mem U a hπ
  vertices := endpoint_verticesBased U a hπ
  edge := endpoint_edge U a hπ
  lower_mem := endpoint_triangle_mem U a hπ
  constant_zero := homotopy_const_zero U a hπ

end RelativeTwoSkeletonNormalization

namespace RelativeNormalization

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)

def ofConnectivity [PathConnectedSpace (Fiber U a)] : (n : ℕ) →
    (∀ k, 0 < k → k < n + 2 → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p)) →
    (∀ d, 2 ≤ d → d ≤ n + 2 → ∀ b : U, Function.Surjective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion U) (y := b) rfl)) → Data U a n
  | 0, _, hs => RelativeTwoSkeletonNormalization.data U a (hs 2 (by omega) (by omega) a)
  | n + 1, hpi, hs =>
    (ofConnectivity n (fun k hk hkn p ↦ hpi k hk (by omega) p)
      (fun d hd hdn b ↦ hs d hd (by omega) b)).next hpi (hs (n + 3) (by omega) (by omega))

omit [SimplyConnectedSpace X] [SimplyConnectedSpace U] in
theorem inclusion_surjective_of_fiberConnectivity (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n + 2 → ∀ b : U, ∀ p : Fiber U b,
      Subsingleton (π_ k (Fiber U b) p))
    (d : ℕ) (hd : 2 ≤ d) (_hdn : d ≤ n + 2) (b : U) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion U) (y := b) rfl) := by
  cases d with
  | zero => omega
  | succ k =>
    let : Subsingleton (π_ k
        (OrbitPair.HomotopyFiber.Space (subtypeInclusion U) ((subtypeInclusion U) b))
        (OrbitPair.HomotopyFiber.basepoint (subtypeInclusion U) b)) :=
      hpi k (by omega) (by omega) b _
    exact HomotopyFiberConnectivity.map_surjective_of_fiber_subsingleton k
      (subtypeInclusion U) b

def ofFiberConnectivity (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n + 2 → ∀ b : U, ∀ p : Fiber U b,
      Subsingleton (π_ k (Fiber U b) p)) : Data U a n := by
  let : PathConnectedSpace (Fiber U a) :=
    HomotopyFiberConnectivity.pathConnectedSpace (subtypeInclusion U) a
  exact ofConnectivity U a n (fun k hk hkn p ↦ hpi k hk hkn a p)
    (inclusion_surjective_of_fiberConnectivity U n hpi)

end RelativeNormalization

end NoExoticSixSphere
