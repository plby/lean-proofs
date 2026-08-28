import Wikipedia.NoExoticSixSphere.FiberQuotientComparison
import Wikipedia.NoExoticSixSphere.HomotopyFiberContractibleSource

/-!
# Quotient comparison with a contractible source

The existing boundary identity retains the original path-composition
map. Its boundary factor is bijective for a contractible source, so a
bijection induced by the quotient in the next degree makes the actual
fiber-to-quotient comparison bijective. Native currying then gives the
same statement for its literal map to the quotient loop space.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.FiberQuotientComparison

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [ContractibleSpace X]
  (f : C(X, Y)) (q : C(Y, Z)) (z₀ : Z) (h : ∀ x, q (f x) = z₀) (x₀ : X)

theorem hom_bijective_of_contractible (d : ℕ) [NeZero d]
    (hq : Function.Bijective (HigherHomotopy.map (N := Fin (d + 1)) q (h x₀))) :
    Function.Bijective (hom f q z₀ h x₀ d) := by
  have he : hom f q z₀ h x₀ d ∘ HomotopyFiber.boundaryHom d f x₀ =
      HigherHomotopy.map (N := Fin (d + 1)) q (h x₀) :=
    funext (hom_boundary f q z₀ h x₀ d)
  rw [← he] at hq
  exact (Function.Bijective.of_comp_iff _
    (HomotopyFiberContractibleSource.boundary_bijective f x₀ d)).mp hq

theorem toLoops_map_bijective_of_contractible (d : ℕ) [NeZero d]
    (hq : Function.Bijective (HigherHomotopy.map (N := Fin (d + 1)) q (h x₀))) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (toLoops f q z₀ h x₀)
      (toLoops_basepoint f q z₀ h x₀)) := by
  have hb := hom_bijective_of_contractible f q z₀ h x₀ d hq
  change Function.Bijective (GeneralizedLoopCurrying.homotopyMulEquiv d z₀ ∘
    HigherHomotopy.map (N := Fin d) (toLoops f q z₀ h x₀)
      (toLoops_basepoint f q z₀ h x₀)) at hb
  exact (Function.Bijective.of_comp_iff'
    (GeneralizedLoopCurrying.homotopyMulEquiv d z₀).bijective _).mp hb

end NoExoticSixSphere.FiberQuotientComparison
