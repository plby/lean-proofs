import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorExactness
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# The spinor connecting isomorphism on native homotopy groups

The total space is the actual seven-sphere. Its vanishing in the adjacent
degrees makes the constructed circle-valued connecting homomorphism an
isomorphism in positive degree below the indicated bound.
-/

noncomputable section

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

open Wikipedia.HopfProblem.SecondHurewicz

variable {d : ℕ} (A : UnitSpinor)

theorem connecting_surjective (hd : d < 7) : Function.Surjective (connecting A d) := by
  intro b
  induction b using Quotient.inductionOn with
  | h q =>
    obtain ⟨p, hp⟩ := exists_connecting_of_nullhomotopic A q
      (genLoop_homotopic_const_of_homeomorph_sphere hd unitSpinorHomeomorph A (fiberLoop A q))
    exact ⟨⟦p⟧, hp⟩

theorem connectingHom_injective [NeZero d] (hd : d + 1 < 7) :
    Function.Injective (connectingHom A d) := by
  apply (injective_iff_map_eq_one (connectingHom A d)).mpr
  intro a
  refine Quotient.inductionOn a fun p hp ↦ ?_
  have he : (⟦(chosenLift A p).endpoint⟧ : HomotopyGroup (Fin d) Circle 1) =
      ⟦GenLoop.const⟧ := hp
  obtain ⟨q, hq⟩ := exists_closed_lift A (chosenLift A p) (Quotient.exact he)
  have hh := mapGenLoop_homotopic map A
    (genLoop_homotopic_const_of_homeomorph_sphere hd unitSpinorHomeomorph A q)
  rw [hq, mapGenLoop_const] at hh
  exact Quotient.sound hh

def connectingMulEquiv (d : ℕ) [NeZero d] (hd : d + 1 < 7) :
    HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A) ≃*
      HomotopyGroup (Fin d) Circle 1 :=
  MulEquiv.ofBijective (connectingHom A d)
    ⟨connectingHom_injective A hd, connecting_surjective A (by omega)⟩

theorem connectingMulEquiv_apply [NeZero d] (hd : d + 1 < 7)
    (a : HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connectingMulEquiv A d hd a = connecting A d a := rfl

theorem connectingMulEquiv_mk [NeZero d] (hd : d + 1 < 7)
    (p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connectingMulEquiv A d hd
      (⟦p⟧ : HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) =
      (⟦boundaryLoop A p⟧ : HomotopyGroup (Fin d) Circle 1) := rfl

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
