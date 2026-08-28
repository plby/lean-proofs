import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-! # Surjectivity from preimages of actual native homotopy representatives -/

namespace Wikipedia.HomotopyGroupsOfSpheres

theorem homotopy_surjective_of_representatives {N X Y : Type} [TopologicalSpace X]
    {x : X} (f : Y → HomotopyGroup N X x)
    (h : ∀ p : GenLoop N X x, ∃ y, f y = (⟦p⟧ : HomotopyGroup N X x)) :
    Function.Surjective f := fun a ↦ Quotient.inductionOn a h

theorem pointedMap_surjective_iff_rebase {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] [Nonempty N] (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    Function.Surjective (pointedMap (N := N) f x y h) ↔
      Function.Surjective (pointedMap (N := N) f x (f x) rfl) := by
  cases h
  rfl

end Wikipedia.HomotopyGroupsOfSpheres
