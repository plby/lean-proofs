import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators

/-! # Evaluation and composition of actual pointed homotopy maps -/

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem pointedMapGenLoop_apply (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (p : GenLoop N X x) (u : N → unitInterval) :
    pointedMapGenLoop f x y hf p u = f (p u) := rfl

theorem pointedMap_comp_apply_of_eq {Z : Type} [TopologicalSpace Z]
    [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (g : C(Y, Z)) (h : C(X, Z)) (x : X) (y : Y) (z : Z)
    (hf : f x = y) (hg : g y = z) (hh : h x = z) (hgf : g.comp f = h)
    (a : HomotopyGroup N X x) :
    pointedMap h x z hh a = pointedMap g y z hg (pointedMap f x y hf a) := by
  subst h
  exact congrArg (fun k : HomotopyGroup N X x →* HomotopyGroup N Z z ↦ k a)
    (pointedMap_comp f g x y z hf hg)

theorem pointedMap_surjective_precompose_homeomorph_iff {Z : Type} [TopologicalSpace Z]
    [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (f : C(Y, Z)) (h : C(X, Z)) (x : X) (y : Y) (z : Z)
    (he : e x = y) (hf : f y = z) (hh : h x = z)
    (hfe : f.comp (e : C(X, Y)) = h) :
    Function.Surjective (pointedMap (N := N) h x z hh) ↔
      Function.Surjective (pointedMap (N := N) f y z hf) := by
  let ep := pointedHomeomorphMulEquiv (N := N) e x y he
  have hc (a : HomotopyGroup N X x) :
      pointedMap h x z hh a = pointedMap f y z hf (ep a) :=
    pointedMap_comp_apply_of_eq (e : C(X, Y)) f h x y z he hf hh hfe a
  constructor
  · intro hs a
    obtain ⟨u, hu⟩ := hs a
    exact ⟨ep u, (hc u).symm.trans hu⟩
  · intro hs a
    obtain ⟨v, hv⟩ := hs a
    refine ⟨ep.symm v, ?_⟩
    rw [hc, ep.apply_symm_apply]
    exact hv

theorem nativeEquiv_generates_iff {M : Type} [DecidableEq N] [Nonempty N]
    [DecidableEq M] [Nonempty M] {x : X} {y : Y}
    (e : HomotopyGroup N X x ≃* HomotopyGroup M Y y) (a : HomotopyGroup N X x) :
    Function.Surjective (fun k : ℤ ↦ (e a) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ a ^ k) :=
  CyclicGenerators.equiv_generates_iff e a

end Wikipedia.HomotopyGroupsOfSpheres
