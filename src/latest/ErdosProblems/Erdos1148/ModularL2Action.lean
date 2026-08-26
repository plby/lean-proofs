import ErdosProblems.Erdos1148.ModularRightTranslation
import ErdosProblems.Erdos1148.SpecialLinearMautner
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The continuous isometric right regular representation on modular L² -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

noncomputable abbrev ModularL2 := Lp ℝ 2 normalizedModularHaarMeasure

noncomputable instance modularL2Action : MulAction SL(2, ℝ) ModularL2 where
  smul g f := Lp.compMeasurePreserving (modularRightTranslate g)
    (measurePreserving_modularRightTranslate g) f
  one_smul f := by
    change Lp.compMeasurePreserving (modularRightTranslate 1) _ f = f
    simpa only [modularRightTranslate_one] using
      Lp.compMeasurePreserving_id_apply f
  mul_smul g h f := by
    change Lp.compMeasurePreserving (modularRightTranslate (g * h)) _ f =
      Lp.compMeasurePreserving (modularRightTranslate g) _
        (Lp.compMeasurePreserving (modularRightTranslate h) _ f)
    simpa only [modularRightTranslate_mul] using Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_modularRightTranslate h) (measurePreserving_modularRightTranslate g)

lemma modularL2_smul_eq (g : SL(2, ℝ)) (f : ModularL2) :
    g • f = Lp.compMeasurePreserving (modularRightTranslate g)
      (measurePreserving_modularRightTranslate g) f := rfl

instance modularL2Isometric : IsIsometricSMul SL(2, ℝ) ModularL2 where
  isometry_smul g := Lp.isometry_compMeasurePreserving (measurePreserving_modularRightTranslate g)

instance modularL2Continuous : ContinuousSMul SL(2, ℝ) ModularL2 where
  continuous_smul := by
    let a : C(SL(2, ℝ) × ModularOrbitSpace, ModularOrbitSpace) :=
      ⟨fun p => modularRightTranslate p.1 p.2, continuous_modularRightTranslate_joint⟩
    let c : C(SL(2, ℝ) × ModularL2, C(ModularOrbitSpace, ModularOrbitSpace)) :=
      a.curry.comp ContinuousMap.fst
    exact continuous_snd.compMeasurePreservingLp c.continuous
      (fun p => measurePreserving_modularRightTranslate p.1) (by norm_num)

theorem modularL2_fixed_of_time_one_fixed {f : ModularL2}
    (hf : diagonalFlow 1 • f = f) (g : SL(2, ℝ)) : g • f = f :=
  specialLinear_fixed_of_diagonal_fixed hf g

end Erdos1148.DukeArithmetic
