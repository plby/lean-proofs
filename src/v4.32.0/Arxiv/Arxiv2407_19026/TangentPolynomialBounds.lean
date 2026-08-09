import Arxiv.Arxiv2407_19026.TangentNumerics

noncomputable section

namespace Arxiv2407_19026

def r1ForwardTReal (z : ℝ) : ℝ :=
  tangentLocalPoly (1 / 10) TangentAffine.r1ForwardCs z

def r1Back1TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (387 / 1000) TangentAffine.r1Back1Cs z

def r1Back2TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (3 / 5) TangentAffine.r1Back2Cs z

def r2ForwardTReal (z : ℝ) : ℝ :=
  tangentLocalPoly (1 / 10) TangentAffine.r2ForwardCs z

def r2Back1TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (189 / 500) TangentAffine.r2Back1Cs z

def r2Back2TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (3 / 5) TangentAffine.r2Back2Cs z

def r3ForwardTReal (z : ℝ) : ℝ :=
  tangentLocalPoly (1 / 10) TangentAffine.r3ForwardCs z

def r3Back1TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (3 / 8) TangentAffine.r3Back1Cs z

def r3Back2TReal (z : ℝ) : ℝ :=
  tangentLocalPoly (3 / 5) TangentAffine.r3Back2Cs z

lemma eval_r1ForwardT (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r1ForwardT =
      r1ForwardTReal z := by
  simp [TangentAffine.r1ForwardT, r1ForwardTReal,
    TangentAffine.eval_localPoly]

lemma eval_r1Back1T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r1Back1T =
      r1Back1TReal z := by
  simp [TangentAffine.r1Back1T, r1Back1TReal,
    TangentAffine.eval_localPoly]

lemma eval_r1Back2T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r1Back2T =
      r1Back2TReal z := by
  simp [TangentAffine.r1Back2T, r1Back2TReal,
    TangentAffine.eval_localPoly]

lemma eval_r2ForwardT (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r2ForwardT =
      r2ForwardTReal z := by
  simp [TangentAffine.r2ForwardT, r2ForwardTReal,
    TangentAffine.eval_localPoly]

lemma eval_r2Back1T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r2Back1T =
      r2Back1TReal z := by
  simp [TangentAffine.r2Back1T, r2Back1TReal,
    TangentAffine.eval_localPoly]

lemma eval_r2Back2T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r2Back2T =
      r2Back2TReal z := by
  simp [TangentAffine.r2Back2T, r2Back2TReal,
    TangentAffine.eval_localPoly]

lemma eval_r3ForwardT (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r3ForwardT =
      r3ForwardTReal z := by
  simp [TangentAffine.r3ForwardT, r3ForwardTReal,
    TangentAffine.eval_localPoly]

lemma eval_r3Back1T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r3Back1T =
      r3Back1TReal z := by
  simp [TangentAffine.r3Back1T, r3Back1TReal,
    TangentAffine.eval_localPoly]

lemma eval_r3Back2T (z : ℝ) :
    LeanCert.Core.Expr.eval (fun _ ↦ z) TangentAffine.r3Back2T =
      r3Back2TReal z := by
  simp [TangentAffine.r3Back2T, r3Back2TReal,
    TangentAffine.eval_localPoly]

end Arxiv2407_19026
