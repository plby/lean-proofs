import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorConnectingEvaluation

/-! # The actual spinor connecting criterion for maps from the literal two-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open NoExoticSixSphere NoExoticSixSphere.RankSixComplexProjection

theorem spinorSphereTwo_pointed_surjective (A : UnitSpinor)
    (f : C(Sphere 2, OrthogonalComplexStructures.Space 6)) (x : Sphere 2)
    (hf : f x = fromSpinor A)
    (h : ∀ q : GenLoop (Fin 1) Circle 1, ∃ p : GenLoop (Fin 2) (Sphere 2) x,
      SpinorFibration.connecting A 1
        (pointedMap f x (fromSpinor A) hf (⟦p⟧ : π_ 2 (Sphere 2) x)) = (⟦q⟧ : π_ 1 Circle 1)) :
    Function.Surjective (pointedMap (N := Fin 2) f x (fromSpinor A) hf) :=
  SpinorFibration.pointedMap_surjective_of_connecting_representatives A 1 (by decide) f x hf h

end Wikipedia.HomotopyGroupsOfSpheres
