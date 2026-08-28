import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-! # Composition and based homotopy invariance of native pointed maps -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {N X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [DecidableEq N] [Nonempty N]

theorem pointedHomeomorphMulEquiv_apply (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y)
    (a : HomotopyGroup N X x) :
    pointedHomeomorphMulEquiv e x y h a = pointedMap (e : C(X, Y)) x y h a := rfl

theorem pointedMap_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) (y : Y) (z : Z)
    (hf : f x = y) (hg : g y = z) :
    pointedMap (N := N) (g.comp f) x z ((congrArg g hf).trans hg) =
      (pointedMap g y z hg).comp (pointedMap f x y hf) := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p ↦ ?_
  change pointedMap (g.comp f) x z _ (⟦p⟧ : HomotopyGroup N X x) =
    pointedMap g y z hg (pointedMap f x y hf (⟦p⟧ : HomotopyGroup N X x))
  rw [pointedMap_mk, pointedMap_mk, pointedMap_mk]
  rfl

theorem pointedMap_eq_of_homotopyRel (f g : C(X, Y)) (x : X) (y : Y)
    (hf : f x = y) (hg : g x = y) (H : f.HomotopyRel g {x}) :
    pointedMap (N := N) f x y hf = pointedMap g x y hg := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p ↦ ?_
  rw [pointedMap_mk, pointedMap_mk]
  apply Quotient.sound
  refine ⟨{
    toFun := fun q ↦ H (q.1, p q.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (p.val.continuous.comp continuous_snd))
    map_zero_left := fun u ↦ H.apply_zero (p u)
    map_one_left := fun u ↦ H.apply_one (p u)
    prop' := ?_ }⟩
  intro r u hu
  apply H.eq_fst r
  change p u = x
  exact p.property u hu

end Wikipedia.HomotopyGroupsOfSpheres
