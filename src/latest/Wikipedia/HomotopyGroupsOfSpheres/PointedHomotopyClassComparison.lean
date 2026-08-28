import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies

/-! # The native cube homotopy induced by a based map homotopy -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
theorem pointedMapGenLoop_homotopic_of_homotopyRel (f g : C(X, Y)) (x : X) (y : Y)
    (hf : f x = y) (hg : g x = y) (H : f.HomotopyRel g {x}) (p : GenLoop N X x) :
    GenLoop.Homotopic (pointedMapGenLoop f x y hf p) (pointedMapGenLoop g x y hg p) := by
  refine ⟨{
    toFun := fun q ↦ H (q.1, p q.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (p.val.continuous.comp continuous_snd))
    map_zero_left := fun u ↦ H.apply_zero (p u)
    map_one_left := fun u ↦ H.apply_one (p u)
    prop' := ?_ }⟩
  intro t u hu
  apply H.eq_fst t
  change p u = x
  exact p.property u hu

end Wikipedia.HomotopyGroupsOfSpheres
