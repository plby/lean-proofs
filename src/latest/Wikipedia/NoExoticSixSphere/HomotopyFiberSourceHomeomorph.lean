import Wikipedia.HopfProblem.OrbitPairHomotopyFiber

/-!
# Transporting the genuine homotopy fiber along a source homeomorphism

Only the source coordinate changes. The original path and its target
remain unchanged, so this gives a homeomorphism of actual fibers.
-/

noncomputable section

open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberSourceHomeomorph

variable {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

def equiv (f : C(B, X)) (e : A ≃ₜ B) (x : X) :
    HomotopyFiber.Space (f.comp (e : C(A, B))) x ≃ₜ HomotopyFiber.Space f x where
  toFun p := ⟨(e p.val.1, p.val.2), p.property⟩
  invFun q := ⟨(e.symm q.val.1, q.val.2),
    q.property.1.trans (congrArg f (e.apply_symm_apply q.val.1).symm), q.property.2⟩
  left_inv p := Subtype.ext (Prod.ext (e.symm_apply_apply p.val.1) rfl)
  right_inv q := Subtype.ext (Prod.ext (e.apply_symm_apply q.val.1) rfl)
  continuous_toFun :=
    ((e.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((e.symm.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem equiv_path (f : C(B, X)) (e : A ≃ₜ B) (x : X)
    (p : HomotopyFiber.Space (f.comp (e : C(A, B))) x) :
    (equiv f e x p).val.2 = p.val.2 := rfl

end NoExoticSixSphere.HomotopyFiberSourceHomeomorph
