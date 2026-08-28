import Mathlib.Topology.Homotopy.Equiv

/-! # Canceling a commuting square of actual homotopy equivalences -/

open scoped ContinuousMap

namespace NoExoticSixSphere

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem homotopic_of_equiv_square (E : X ≃ₕ X) (T : Y ≃ₕ Y)
    (f g p : C(X, Y))
    (H : (T.invFun.comp (f.comp E.toFun)).Homotopic g)
    (hsquare : T.toFun.comp g = p.comp E.toFun) : f.Homotopic p := by
  have hleft : (T.toFun.comp (T.invFun.comp (f.comp E.toFun))).Homotopic
      (f.comp E.toFun) := T.right_inv.comp (ContinuousMap.Homotopic.refl _)
  have hright : (T.toFun.comp (T.invFun.comp (f.comp E.toFun))).Homotopic
      (p.comp E.toFun) := by
    rw [← hsquare]
    exact (ContinuousMap.Homotopic.refl T.toFun).comp H
  have hboth := (hleft.symm.trans hright).comp (ContinuousMap.Homotopic.refl E.invFun)
  have hf : ((f.comp E.toFun).comp E.invFun).Homotopic f :=
    (ContinuousMap.Homotopic.refl f).comp E.right_inv
  have hp : ((p.comp E.toFun).comp E.invFun).Homotopic p :=
    (ContinuousMap.Homotopic.refl p).comp E.right_inv
  exact hf.symm.trans (hboth.trans hp)

end NoExoticSixSphere
