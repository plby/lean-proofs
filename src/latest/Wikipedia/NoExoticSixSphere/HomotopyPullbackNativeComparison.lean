import Wikipedia.NoExoticSixSphere.HomotopyPullbackFiberEquivalence
import Wikipedia.NoExoticSixSphere.HomotopyEquivNativeConnectivity
import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionThree
import Wikipedia.NoExoticSixSphere.NativeHomotopyBasepointVanishing
import Wikipedia.HopfProblem.DegreeCollapsePointClassComponents

/-!
# Native isomorphisms give finite-domain homotopy reflection

The actual original fiber has trivial native groups, including degree
zero. The explicit projection-fiber equivalence transfers this to the
path-space pullback. Its left projection is injective in positive native
degrees; the diagonal is a literal section. Path components handle
degree zero. Thus the diagonal itself has the native isomorphisms needed
by finite-cell lifting, and original endpoint homotopies are reflected.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.HomotopyPullbackDiagonal

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (F : C(X, Y))

theorem diagonal_map_left (d : ℕ) (x : X) (c : π_ d X x) :
    HigherHomotopy.map (N := Fin d) (left F) (y := diagonal F x) rfl
      (HigherHomotopy.map (N := Fin d) (diagonal F) (y := x) rfl c) = c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

variable (hF : ∀ n (x : X), Function.Bijective
  (HigherHomotopy.map (N := Fin n) F (y := x) rfl))

include hF

theorem originalFiber_pathConnected (x : X) : PathConnectedSpace (HomotopyFiber.Space F (F x)) := by
  let : Subsingleton (π_ 0 (HomotopyFiber.Space F (F x)) (HomotopyFiber.basepoint F x)) :=
    HomotopyFiberConnectivity.homotopy_subsingleton_of_maps 0 F x
      (hF 0 x).injective (hF 1 x).surjective
  let E : π_ 0 (HomotopyFiber.Space F (F x)) (HomotopyFiber.basepoint F x) ≃
      ZerothHomotopy (HomotopyFiber.Space F (F x)) := HomotopyGroup.pi0EquivZerothHomotopy
  exact pathConnectedSpace_iff_zerothHomotopy.mpr
    ⟨⟨E (Quotient.mk' GenLoop.const)⟩, E.symm.injective.subsingleton⟩

theorem originalFiber_pi_subsingleton (d : ℕ) (hd : 0 < d) (x : X)
    (q : HomotopyFiber.Space F (F x)) : Subsingleton (π_ d (HomotopyFiber.Space F (F x)) q) := by
  let := originalFiber_pathConnected F hF x
  let : Subsingleton (π_ d (HomotopyFiber.Space F (F x)) (HomotopyFiber.basepoint F x)) :=
    HomotopyFiberConnectivity.homotopy_subsingleton_of_maps d F x
      (hF d x).injective (hF (d + 1) x).surjective
  exact NativeHomotopyBasepointVanishing.subsingleton d hd (HomotopyFiber.basepoint F x) q

theorem projectionFiber_pathConnected (x : X) : PathConnectedSpace (ProjectionFiber F x) := by
  let := originalFiber_pathConnected F hF x
  exact DegreeCollapse.MorseCancellation.pathConnectedSpace_of_homotopyEquiv
    (projectionFiberEquiv F x)

theorem projectionFiber_pi_subsingleton (d : ℕ) (hd : 0 < d) (x : X)
    (q : ProjectionFiber F x) : Subsingleton (π_ d (ProjectionFiber F x) q) :=
  HomotopyEquivNativeConnectivity.subsingleton (projectionFiberEquiv F x) hd
    (originalFiber_pi_subsingleton F hF d hd x) q

theorem joined_diagonal_left (p : Space F) : Joined (diagonal F (left F p)) p := by
  let q : ProjectionFiber F (left F p) := ⟨(p, ContinuousMap.const _ (left F p)), rfl, rfl⟩
  let b : ProjectionFiber F (left F p) :=
    HomotopyFiber.basepoint (left F) (diagonal F (left F p))
  let := projectionFiber_pathConnected F hF (left F p)
  exact (PathConnectedSpace.joined b q).map
      (HomotopyFiber.projection (left F) (left F p)).continuous

variable [PathConnectedSpace X]

theorem pullback_pathConnected : PathConnectedSpace (Space F) := by
  refine ⟨⟨diagonal F (Classical.arbitrary X)⟩, ?_⟩
  intro p q
  exact (joined_diagonal_left F hF p).symm.trans
    (((PathConnectedSpace.joined (left F p) (left F q)).map (diagonal F).continuous).trans
      (joined_diagonal_left F hF q))

theorem diagonal_pi_bijective (d : ℕ) (x : X) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (diagonal F) (y := x) rfl) := by
  refine ⟨(show Function.LeftInverse
    (HigherHomotopy.map (N := Fin d) (left F) (y := diagonal F x) rfl)
    (HigherHomotopy.map (N := Fin d) (diagonal F) (y := x) rfl) from
      diagonal_map_left F d x).injective, ?_⟩
  cases d with
  | zero =>
    let := pullback_pathConnected F hF
    let : Subsingleton (ZerothHomotopy (Space F)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp
        (inferInstanceAs (PathConnectedSpace (Space F)))).2
    let : Subsingleton (π_ 0 (Space F) (diagonal F x)) :=
      HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton
    exact fun c ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩
  | succ d =>
    let : Subsingleton (π_ (d + 1) (HomotopyFiber.Space (left F) (left F (diagonal F x)))
        (HomotopyFiber.basepoint (left F) (diagonal F x))) :=
      projectionFiber_pi_subsingleton F hF (d + 1) (Nat.succ_pos d) x _
    have hi := HomotopyFiberConnectivity.map_injective_of_fiber_subsingleton
      (d + 1) (left F) (diagonal F x)
    intro c
    refine ⟨HigherHomotopy.map (N := Fin (d + 1)) (left F) (y := diagonal F x) rfl c, hi ?_⟩
    exact diagonal_map_left F (d + 1) x _

theorem finiteCell_homotopic_reflect_of_native_bijective
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hZ : DegreeCollapse.FiniteCells.Built d Z)
    (u v : C(Z, X)) (H : (F.comp u).Homotopic (F.comp v)) : u.Homotopic v :=
  finiteCell_homotopic_reflect F (diagonal_pi_bijective F hF) hZ u v H

end NoExoticSixSphere.HomotopyPullbackDiagonal
