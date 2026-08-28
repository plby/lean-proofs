import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy

/-!
# Native third-homotopy-group multiplication represented on the original sphere

Descend Mathlib's actual cubical concatenation through the constructed
smooth-interior quotient. The result is a continuous based map on the
original three-sphere, with the exact two half-cube formulas. Its class
is proved to be the product in the native third homotopy group.

This does not yet assert smoothness or intersection additivity of the
descended concatenation.
-/

noncomputable section

open Set Function
open scoped unitInterval Topology

namespace NoExoticSixSphere.SmoothCube

variable {X : Type*} [TopologicalSpace X] {x : X}

def concatenate (f g : BasedMap 3 X x) : BasedMap 3 X x :=
  (basedEquiv (by decide : 0 < 3)).symm (GenLoop.transAt 0 (toGenLoop f) (toGenLoop g))

theorem toGenLoop_concatenate (f g : BasedMap 3 X x) :
    toGenLoop (concatenate f g) = GenLoop.transAt 0 (toGenLoop f) (toGenLoop g) :=
  (basedEquiv (by decide : 0 < 3)).apply_symm_apply _

theorem sphereClass_concatenate (f g : BasedMap 3 X x) :
    sphereClass (concatenate f g) = sphereClass f * sphereClass g := by
  have hm : sphereClass g * sphereClass f =
      (⟦GenLoop.transAt 0 (toGenLoop f) (toGenLoop g)⟧ : HomotopyGroup (Fin 3) X x) :=
    HomotopyGroup.mul_spec (i := (0 : Fin 3))
  rw [mul_comm] at hm
  have he := congrArg (fun p : GenLoop (Fin 3) X x ↦
    (⟦p⟧ : HomotopyGroup (Fin 3) X x)) (toGenLoop_concatenate f g)
  exact he.trans hm.symm

theorem concatenate_quotient (f g : BasedMap 3 X x) (u : Fin 3 → I) :
    (concatenate f g).val (quotient 3 u) =
      GenLoop.transAt 0 (toGenLoop f) (toGenLoop g) u :=
  descend_quotient (by decide : 0 < 3) _ u

theorem concatenate_formula (f g : BasedMap 3 X x) (u : Fin 3 → I) :
    (concatenate f g).val (quotient 3 u) =
      if (u 0 : ℝ) ≤ 1 / 2 then
        f.val (quotient 3 (Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        g.val (quotient 3 (Function.update u 0 (projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)))) := by
  rw [concatenate_quotient]
  rfl

theorem concatenate_seam (f g : BasedMap 3 X x) (u : Fin 3 → I)
    (hu : (u 0 : ℝ) = 1 / 2) : (concatenate f g).val (quotient 3 u) = x := by
  have hmid : 2 * (u 0 : ℝ) = 1 := by rw [hu]; norm_num
  have hhalf : (u 0 : ℝ) ≤ 1 / 2 := hu.le
  rw [concatenate_formula, if_pos hhalf, hmid, projIcc_right]
  apply (congrArg f.val (quotient_boundary 3 _ ?_)).trans f.property
  exact ⟨0, Or.inr (by rw [Function.update_self]; apply Subtype.ext; rfl)⟩

end NoExoticSixSphere.SmoothCube
