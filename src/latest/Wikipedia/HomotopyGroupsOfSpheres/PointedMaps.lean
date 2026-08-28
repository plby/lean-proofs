import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-! # Native homotopy maps with an explicitly preserved base point -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem.SecondHurewicz

variable {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [DecidableEq N] [Nonempty N]

/-- Transport only along an equality of base points. -/
def basepointEqMulEquiv {x y : X} (h : x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N X y := by
  cases h
  exact MulEquiv.refl _

def pointedMapGenLoop (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.val, fun u hu => (congrArg f (p.property u hu)).trans h⟩

/-- Continuous postcomposition, with a supplied equality of the image base point. -/
def pointedMap (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y :=
  (basepointEqMulEquiv h).toMonoidHom.comp (map f x)

theorem pointedMap_mk (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (p : GenLoop N X x) :
    pointedMap f x y h (⟦p⟧ : HomotopyGroup N X x) =
      (⟦pointedMapGenLoop f x y h p⟧ : HomotopyGroup N Y y) := by
  cases h
  rfl

/-- A homeomorphism together with its stated base point gives a native group isomorphism. -/
def pointedHomeomorphMulEquiv (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y :=
  (homeomorphMulEquiv e x).trans (basepointEqMulEquiv h)

theorem pointedHomeomorphMulEquiv_mk (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y)
    (p : GenLoop N X x) :
    pointedHomeomorphMulEquiv e x y h (⟦p⟧ : HomotopyGroup N X x) =
      (⟦pointedMapGenLoop (e : C(X, Y)) x y h p⟧ : HomotopyGroup N Y y) := by
  cases h
  rfl

end Wikipedia.HomotopyGroupsOfSpheres
