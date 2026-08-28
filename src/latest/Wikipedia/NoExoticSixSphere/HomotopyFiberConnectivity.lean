import Wikipedia.HopfProblem.OrbitPairHomotopyFiberExactSequence
import Wikipedia.HopfProblem.FundamentalGroupSimplyConnected

/-!
# Connectivity from the genuine homotopy-fiber exact sequence

Injectivity in degree `d` and surjectivity in degree `d + 1` of the
original induced maps annihilate the actual fiber's degree-`d` homotopy
classes. The degree-zero native quotient detects path components, and
the degree-one quotient is the original fundamental group. No replacement
fiber or abstract long exact sequence is introduced.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair.HomotopyFiber

namespace NoExoticSixSphere.HomotopyFiberConnectivity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem homotopy_subsingleton_of_maps (d : ℕ) (f : C(X, Y)) (x : X)
    (hi : Function.Injective (HigherHomotopy.map (N := Fin d) f (y := x) rfl))
    (hs : Function.Surjective (HigherHomotopy.map (N := Fin (d + 1)) f (y := x) rfl)) :
    Subsingleton (π_ d (Space f (f x)) (basepoint f x)) := by
  have hz (c : π_ d (Space f (f x)) (basepoint f x)) :
      c = Quotient.mk' GenLoop.const := by
    have hp : HigherHomotopy.map f rfl
        (HigherHomotopy.map (projection f (f x)) rfl c) =
          (Quotient.mk' GenLoop.const : π_ d Y (f x)) :=
      (map_eq_const_iff_exists_fiber_class f x _).mpr ⟨c, rfl⟩
    have hc : HigherHomotopy.map (N := Fin d) f (y := x) rfl
        (Quotient.mk' GenLoop.const) = Quotient.mk' GenLoop.const :=
      congrArg (fun p : GenLoop (Fin d) Y (f x) ↦ (Quotient.mk' p : π_ d Y (f x)))
        (HigherHomotopy.genLoopMap_const f rfl)
    obtain ⟨a, ha⟩ := (projection_eq_const_iff_exists_boundary_class d f x c).mp
      (hi (hp.trans hc.symm))
    exact ha.symm.trans ((boundary_eq_const_iff_exists_source_class d f x a).mpr (hs a))
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

theorem map_surjective_of_fiber_subsingleton (d : ℕ) (f : C(X, Y)) (x : X)
    [Subsingleton (π_ d (Space f (f x)) (basepoint f x))] :
    Function.Surjective (HigherHomotopy.map (N := Fin (d + 1)) f (y := x) rfl) := by
  intro c
  exact (boundary_eq_const_iff_exists_source_class d f x c).mp (Subsingleton.elim _ _)

theorem pathConnectedSpace [PathConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) : PathConnectedSpace (Space f (f x)) := by
  let : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (inferInstanceAs (PathConnectedSpace X))).2
  let : Subsingleton (π_ 0 X x) :=
    HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton
  let : Subsingleton (π_ 1 Y (f x)) :=
    HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
  let : Subsingleton (π_ 0 (Space f (f x)) (basepoint f x)) :=
    homotopy_subsingleton_of_maps 0 f x (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun a ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ a⟩)
  let E : π_ 0 (Space f (f x)) (basepoint f x) ≃ ZerothHomotopy (Space f (f x)) :=
    HomotopyGroup.pi0EquivZerothHomotopy
  exact pathConnectedSpace_iff_zerothHomotopy.mpr
    ⟨⟨E (Quotient.mk' GenLoop.const)⟩, E.symm.injective.subsingleton⟩

theorem simplyConnectedSpace [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X)
    (hs : Function.Surjective (HigherHomotopy.map (N := Fin 2) f (y := x) rfl)) :
    SimplyConnectedSpace (Space f (f x)) := by
  let := pathConnectedSpace f x
  let : Subsingleton (π_ 1 X x) :=
    HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
  let : Subsingleton (π_ 1 (Space f (f x)) (basepoint f x)) :=
    homotopy_subsingleton_of_maps 1 f x (fun _ _ _ ↦ Subsingleton.elim _ _) hs
  let : Subsingleton (FundamentalGroup (Space f (f x)) (basepoint f x)) :=
    HomotopyGroup.pi1EquivFundamentalGroup.symm.injective.subsingleton
  exact simplyConnectedSpace_of_fundamentalGroup_subsingleton (basepoint f x)

end NoExoticSixSphere.HomotopyFiberConnectivity
