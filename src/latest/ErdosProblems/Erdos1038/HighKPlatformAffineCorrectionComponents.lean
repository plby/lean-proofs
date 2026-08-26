import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerComponents

/-!
# Reusable affine circle-correction components

The affine table uses finitely many rational `qCap` and `rCap` values.  Circle
correction expressions read only their rational cap and the common `pi` box.
This module proves the structural transfer once; generated numerical modules
can therefore kernel-check each distinct correction globally and reuse it in
all matching cells.
-/

set_option warningAsError false

namespace Erdos1038.HighKPlatformAffineCorrectionComponents

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineCornerComponents

noncomputable section

abbrev E := HighKIntervalExpr 5

/-- Canonical boxes for correction checks.  The first four entries are never
read by a correction expression. -/
def correctionBoxes : Fin 5 → RatInterval :=
  ![zeroBox, zeroBox, zeroBox, zeroBox,
    Erdos1038.HighKPlatformIntervalSmoke.piBox]

def correctionE (logTerms trigDoubles N : ℕ) (q : Rat) : E :=
  circleCorrectionLowerE logTerms trigDoubles N (.rat q) piE

theorem agreeOn_circleSelfTerm_rat
    (X Y : Fin 5 → RatInterval) (trigDoubles n : ℕ) (q : Rat) :
    AgreeOn X Y (circleSelfTermE trigDoubles (.rat q : E) n) := by
  simp [circleSelfTermE, HighKIntervalExpr.div, HighKIntervalExpr.sq,
    AgreeOn]

theorem agreeOn_circleSelfSum_rat
    (X Y : Fin 5 → RatInterval) (trigDoubles N : ℕ) (q : Rat) :
    AgreeOn X Y (circleSelfSumE trigDoubles (.rat q : E) N) := by
  induction N with
  | zero => simp [circleSelfSumE, AgreeOn]
  | succ N ih =>
      simp [circleSelfSumE, AgreeOn, ih,
        agreeOn_circleSelfTerm_rat X Y trigDoubles N q]

theorem agreeOn_correctionE (d : Data)
    (logTerms trigDoubles N : ℕ) (q : Rat) :
    AgreeOn d.boxes correctionBoxes
      (correctionE logTerms trigDoubles N q) := by
  have hpi : d.boxes 4 = correctionBoxes 4 := by
    simp [Data.boxes, correctionBoxes]
  simp [correctionE, circleCorrectionLowerE, HighKIntervalExpr.sub,
    HighKIntervalExpr.div, HighKIntervalExpr.sq, AgreeOn,
    agreeOn_circleSelfSum_rat, hpi]

/-- Transfer one globally checked correction lower bound to any affine cell. -/
theorem evalLower_correctionE_of_global
    (d : Data) {logTerms trigDoubles N : ℕ} {q lower : Rat}
    (hglobal : EvalLower correctionBoxes
      (correctionE logTerms trigDoubles N q) lower) :
    EvalLower d.boxes
      (circleCorrectionLowerE logTerms trigDoubles N (.rat q) piE)
      lower := by
  obtain ⟨I, heval, hlower⟩ := hglobal
  refine ⟨I, ?_, hlower⟩
  exact (evalInterval_eq_of_agreeOn
    (agreeOn_correctionE d logTerms trigDoubles N q)).trans heval

end

end Erdos1038.HighKPlatformAffineCorrectionComponents
