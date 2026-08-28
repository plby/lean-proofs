import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.HomotopySurjectivity

/-! # Evaluation of the actual spinor connecting homomorphism -/

noncomputable section

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

theorem connectingHom_apply (A : UnitSpinor) (d : ℕ) [NeZero d]
    (a : HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connectingHom A d a = connecting A d a := rfl

theorem pointedMap_surjective_of_connecting_representatives
    {X : Type} [TopologicalSpace X] (A : UnitSpinor) (d : ℕ) [NeZero d] (hd : d + 1 < 7)
    (f : C(X, OrthogonalComplexStructures.Space 6)) (x : X) (hf : f x = fromSpinor A)
    (h : ∀ q : GenLoop (Fin d) Circle 1, ∃ p : GenLoop (Fin (d + 1)) X x,
      connecting A d (Wikipedia.HomotopyGroupsOfSpheres.pointedMap f x (fromSpinor A) hf
        (⟦p⟧ : HomotopyGroup (Fin (d + 1)) X x)) = (⟦q⟧ : HomotopyGroup (Fin d) Circle 1)) :
    Function.Surjective (Wikipedia.HomotopyGroupsOfSpheres.pointedMap
      (N := Fin (d + 1)) f x (fromSpinor A) hf) := by
  let m := Wikipedia.HomotopyGroupsOfSpheres.pointedMap (N := Fin (d + 1)) f x (fromSpinor A) hf
  have hs : Function.Surjective (fun g ↦ connecting A d (m g)) := by
    apply Wikipedia.HomotopyGroupsOfSpheres.homotopy_surjective_of_representatives
    intro q
    obtain ⟨p, hp⟩ := h q
    exact ⟨⟦p⟧, hp⟩
  intro a
  obtain ⟨b, hb⟩ := hs (connecting A d a)
  refine ⟨b, connectingHom_injective A hd ?_⟩
  exact (connectingHom_apply A d (m b)).trans (hb.trans (connectingHom_apply A d a).symm)

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
