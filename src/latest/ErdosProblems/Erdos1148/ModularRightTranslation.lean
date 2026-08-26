import ErdosProblems.Erdos1148.ModularHaarMeasure

/-! # Joint continuity and composition of modular right translations -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma modularRightTranslate_one : modularRightTranslate (1 : SL(2, ℝ)) = id := by
  funext x
  induction x using Quotient.inductionOn' with | h g =>
    change modularMk (g * 1) = modularMk g
    rw [mul_one]

lemma modularRightTranslate_mul (g h : SL(2, ℝ)) :
    modularRightTranslate (g * h) = modularRightTranslate h ∘ modularRightTranslate g := by
  funext x
  induction x using Quotient.inductionOn' with | h k =>
    change modularMk (k * (g * h)) = modularMk ((k * g) * h)
    rw [mul_assoc]

theorem continuous_modularRightTranslate_joint :
    Continuous (fun p : SL(2, ℝ) × ModularOrbitSpace => modularRightTranslate p.1 p.2) := by
  have hq : IsOpenQuotientMap modularMk := MulAction.isOpenQuotientMap_quotientMk
  apply (IsOpenQuotientMap.id.prodMap hq).isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : SL(2, ℝ) × SL(2, ℝ) => modularMk (p.2 * p.1))
  exact continuous_modularMk.comp (continuous_snd.mul continuous_fst)

theorem measurePreserving_modularRightTranslate (g : SL(2, ℝ)) :
    MeasurePreserving (modularRightTranslate g) normalizedModularHaarMeasure
      normalizedModularHaarMeasure :=
  ⟨(continuous_modularRightTranslate g).measurable,
    normalizedModularHaarMeasure_right_invariant g⟩

end Erdos1148.DukeArithmetic
