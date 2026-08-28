import Wikipedia.SmoothSixDPoincare.OpenGluing
import Mathlib.Topology.Homeomorph.Quotient

/-! # Change both open patches while retaining their exact cross-patch identifications -/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph X' Y')
  (l : X ≃ₜ X') (r : Y ≃ₜ Y')
  (h : ∀ x y, left e x = right e y ↔ left f (l x) = right f (r y))

def congr : Space e ≃ₜ Space f := by
  apply Homeomorph.Quotient.congr (l.sumCongr r)
  rintro (x | y) (x' | y')
  · exact l.injective.eq_iff.symm
  · exact (left_eq_right e x y').symm.trans ((h x y').trans (left_eq_right f (l x) (r y')))
  · exact (right_eq_left e y x').symm.trans
      (eq_comm.trans ((h x' y).trans (eq_comm.trans (right_eq_left f (r y) (l x')))))
  · exact r.injective.eq_iff.symm

theorem congr_left (x : X) : congr e f l r h (left e x) = left f (l x) := rfl

theorem congr_right (y : Y) : congr e f l r h (right e y) = right f (r y) := rfl

theorem congr_symm_left (x : X') : (congr e f l r h).symm (left f x) = left e (l.symm x) := rfl

theorem congr_symm_right (y : Y') :
    (congr e f l r h).symm (right f y) = right e (r.symm y) := rfl

end Wikipedia.SmoothSixDPoincare.OpenGluing
