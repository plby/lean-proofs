import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameExactness
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity

/-!
# The stable balanced-orbit comparison with the orthogonal group

The total Stiefel space has trivial native homotopy groups below `n`.
The checked exactness constructions therefore make the actual connecting
homomorphism an isomorphism when both adjacent total-space groups vanish.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open HopfProblem.SecondHurewicz

variable {n d : ℕ} (A : Stiefel.Space (n + n) n)

theorem connecting_surjective (hd : d < n) : Function.Surjective (connecting A d) := by
  intro b
  induction b using Quotient.inductionOn with
  | h q =>
    obtain ⟨p, hp⟩ := exists_connecting_of_nullhomotopic A q
      (Stiefel.genLoop_homotopic_const_of_lt hd n A (fiberLoop A q))
    exact ⟨⟦p⟧, hp⟩

theorem connectingHom_injective [NeZero d] (hd : d + 1 < n) :
    Function.Injective (connectingHom A d) := by
  apply (injective_iff_map_eq_one (connectingHom A d)).mpr
  intro a
  refine Quotient.inductionOn a fun p hp ↦ ?_
  have he : (⟦(chosenLift A p).endpoint⟧ : HomotopyGroup (Fin d) (OrthogonalOperators n) 1) =
      ⟦GenLoop.const⟧ := hp
  obtain ⟨q, hq⟩ := exists_closed_lift A (chosenLift A p) (Quotient.exact he)
  have hh := mapGenLoop_homotopic (map n) A
    (Stiefel.genLoop_homotopic_const_of_lt hd n A q)
  rw [hq, mapGenLoop_const] at hh
  exact Quotient.sound hh

/-- The isomorphism is the original cubical connecting homomorphism. -/
def connectingMulEquiv (d : ℕ) [NeZero d] (hd : d + 1 < n) :
    HomotopyGroup (Fin (d + 1)) (Space n) (toBalanced A) ≃*
      HomotopyGroup (Fin d) (OrthogonalOperators n) 1 :=
  MulEquiv.ofBijective (connectingHom A d)
    ⟨connectingHom_injective A hd, connecting_surjective A (by omega)⟩

theorem connectingMulEquiv_apply [NeZero d] (hd : d + 1 < n)
    (a : HomotopyGroup (Fin (d + 1)) (Space n) (toBalanced A)) :
    connectingMulEquiv A d hd a = connecting A d a := rfl

theorem connectingMulEquiv_mk [NeZero d] (hd : d + 1 < n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) :
    connectingMulEquiv A d hd (⟦p⟧ : HomotopyGroup (Fin (d + 1)) (Space n) (toBalanced A)) =
      (⟦boundaryLoop A p⟧ : HomotopyGroup (Fin d) (OrthogonalOperators n) 1) := rfl

/-- A frame over the original balanced base point, chosen using proved surjectivity. -/
def standardFrame (n : ℕ) : Stiefel.Space (n + n) n :=
  Classical.choose (toBalanced_surjective n (standard n))

theorem toBalanced_standardFrame (n : ℕ) : toBalanced (standardFrame n) = standard n :=
  Classical.choose_spec (toBalanced_surjective n (standard n))

def balancedOrthogonalMulEquiv (n d : ℕ) [NeZero d] (hd : d + 1 < n) :
    HomotopyGroup (Fin (d + 1)) (Space n) (standard n) ≃*
      HomotopyGroup (Fin d) (OrthogonalOperators n) 1 :=
  (basepointEqMulEquiv (toBalanced_standardFrame n).symm).trans
    (connectingMulEquiv (standardFrame n) d hd)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
