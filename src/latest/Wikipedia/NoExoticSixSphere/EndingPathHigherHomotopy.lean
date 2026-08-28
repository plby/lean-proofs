import Wikipedia.NoExoticSixSphere.EndingPathPair
import Wikipedia.NoExoticSixSphere.ContractibleNativeHomotopy

/-!
# Native higher homotopy vanishes at the constant ending path

The explicit shortening contracts each actual generalized loop while
fixing its whole cube boundary. Thus the original native quotient is
trivial in every degree, including degree zero. Applied to the ending-path
pair, this gives the required inclusion surjectivity without assumptions.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.EndingPath

variable {X : Type} [TopologicalSpace X] (x : X)

def genLoopContraction (n : ℕ) (p : GenLoop (Fin n) (Space x) (constant x)) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → I) (constant x)) (Cube.boundary (Fin n)) where
  toHomotopy := (contraction (y₀ := x)).compContinuousMap p.val
  prop' r s hs := by
    change shorten r (p s) = p s
    have hp : p s = constant x := p.property s hs
    exact (congrArg (shorten r) hp).trans ((shorten_constant r).trans hp.symm)

theorem homotopyClass_eq_const (n : ℕ) (c : π_ n (Space x) (constant x)) :
    c = Quotient.mk' GenLoop.const := by
  refine Quotient.inductionOn c fun p ↦ ?_
  exact Quotient.sound ⟨genLoopContraction x n p⟩

theorem homotopy_subsingleton (n : ℕ) : Subsingleton (π_ n (Space x) (constant x)) :=
  ⟨fun p q ↦ (homotopyClass_eq_const x n p).trans (homotopyClass_eq_const x n q).symm⟩

end NoExoticSixSphere.EndingPath

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

theorem inclusion_surjective_at (n : ℕ) (b : subspace U a) :
    Function.Surjective (HigherHomotopy.map (N := Fin n)
      (subtypeInclusion (subspace U a)) (y := b) rfl) := by
  let : Subsingleton (π_ n (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) b)) := ContractibleNativeHomotopy.subsingleton n _
  intro c
  exact ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩

theorem inclusion_surjective (n : ℕ) :
    Function.Surjective (HigherHomotopy.map (N := Fin n)
      (subtypeInclusion (subspace U a)) (y := basepoint U a) rfl) := by
  let : Subsingleton (π_ n (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    EndingPath.homotopy_subsingleton a.val n
  intro c
  exact ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩

theorem fiber_simplyConnected [SimplyConnectedSpace (Fiber U a)] :
    SimplyConnectedSpace (Fiber (subspace U a) (basepoint U a)) := by
  let := subspace_simplyConnected U a
  exact HomotopyFiberConnectivity.simplyConnectedSpace
    (subtypeInclusion (subspace U a)) (basepoint U a) (inclusion_surjective U a 2)

end NoExoticSixSphere.EndingPathPair
