import Arxiv.Arxiv2407_19026.TangentAssembly
import Arxiv.Arxiv2407_19026.TangentPolyChecks

/-! Soundness wrappers shared by the certified tangent rounds. -/

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

lemma affineLowerEval
    (e : Expr) (lower lo hi : ℚ) (bps : List ℚ)
    (hsupp : ExprSupportedCore e)
    (hne : bps ≠ [])
    (hlast : bps.getLast hne = hi)
    (hcheck :
      checkLowerAffineCover e lower TangentAffine.cfg lo bps = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      (lower : ℝ) ≤ Expr.eval (fun _ ↦ x) e := by
  have h :=
    verify_lower_affine_cover e hsupp lower TangentAffine.cfg
      lo bps hne hcheck
  rw [hlast] at h
  exact h

lemma witness_mem_of_affine
    {T : Expr} {f : ℝ → ℝ} {lo hi : ℚ} {bps : List ℚ}
    (hsuppT : ExprSupportedCore T)
    (hsuppHi : ExprSupportedCore (TangentPolyNative.belowOne T))
    (heval : ∀ x, Expr.eval (fun _ ↦ x) T = f x)
    (hne : bps ≠ [])
    (hlast : bps.getLast hne = hi)
    (hlo :
      checkLowerAffineCover T (1 / 100000)
        TangentAffine.cfg lo bps = true)
    (hhi :
      checkLowerAffineCover (TangentPolyNative.belowOne T) (1 / 100000)
        TangentAffine.cfg lo bps = true) :
    ∀ x ∈ Set.Icc ((lo : ℚ) : ℝ) ((hi : ℚ) : ℝ),
      f x ∈ Set.Ioc (0 : ℝ) 1 := by
  have hlow := affineLowerEval T (1 / 100000) lo hi bps
    hsuppT hne hlast hlo
  have hupp := affineLowerEval (TangentPolyNative.belowOne T)
    (1 / 100000) lo hi bps hsuppHi hne hlast hhi
  intro x hx
  have hxlow := hlow x hx
  have hxupp := hupp x hx
  rw [heval x] at hxlow
  have hbelow :
      Expr.eval (fun _ ↦ x) (TangentPolyNative.belowOne T) =
        1 - f x := by
    simp [TangentPolyNative.belowOne, TangentAffine.sub,
      TangentAffine.c, heval, Expr.eval]
  rw [hbelow] at hxupp
  constructor <;> nlinarith

lemma r1ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      r1ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r1ForwardT) (f := r1ForwardTReal)
    (lo := 1 / 10) (hi := 269 / 1000)
    (bps := TangentPolyNative.r1ForwardBps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r1ForwardT
    (by native_decide) (by native_decide)
    TangentPolyNative.r1Forward_checks.1
    TangentPolyNative.r1Forward_checks.2
  norm_num at h ⊢
  exact h

lemma r1Back1TReal_mem :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      r1Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r1Back1T) (f := r1Back1TReal)
    (lo := 387 / 1000) (hi := 3 / 5)
    (bps := TangentPolyNative.r1Back1Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r1Back1T
    (by native_decide) (by native_decide)
    TangentPolyNative.r1Back1_checks.1
    TangentPolyNative.r1Back1_checks.2
  norm_num at h ⊢
  exact h

lemma r1Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r1Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r1Back2T) (f := r1Back2TReal)
    (lo := 3 / 5) (hi := 1)
    (bps := TangentPolyNative.back2Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r1Back2T
    (by native_decide) (by native_decide)
    TangentPolyNative.r1Back2_checks.1
    TangentPolyNative.r1Back2_checks.2
  norm_num at h ⊢
  exact h

lemma r2ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      r2ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r2ForwardT) (f := r2ForwardTReal)
    (lo := 1 / 10) (hi := 67 / 250)
    (bps := TangentPolyNative.r2ForwardBps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r2ForwardT
    (by native_decide) (by native_decide)
    TangentPolyNative.r2Forward_checks.1
    TangentPolyNative.r2Forward_checks.2
  norm_num at h ⊢
  exact h

lemma r2Back1TReal_mem :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      r2Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r2Back1T) (f := r2Back1TReal)
    (lo := 189 / 500) (hi := 3 / 5)
    (bps := TangentPolyNative.r2Back1Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r2Back1T
    (by native_decide) (by native_decide)
    TangentPolyNative.r2Back1_checks.1
    TangentPolyNative.r2Back1_checks.2
  norm_num at h ⊢
  exact h

lemma r2Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r2Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r2Back2T) (f := r2Back2TReal)
    (lo := 3 / 5) (hi := 1)
    (bps := TangentPolyNative.back2Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r2Back2T
    (by native_decide) (by native_decide)
    TangentPolyNative.r2Back2_checks.1
    TangentPolyNative.r2Back2_checks.2
  norm_num at h ⊢
  exact h

lemma r3ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      r3ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r3ForwardT) (f := r3ForwardTReal)
    (lo := 1 / 10) (hi := 67 / 250)
    (bps := TangentPolyNative.r3ForwardBps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r3ForwardT
    (by native_decide) (by native_decide)
    TangentPolyNative.r3Forward_checks.1
    TangentPolyNative.r3Forward_checks.2
  norm_num at h ⊢
  exact h

lemma r3Back1TReal_mem :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      r3Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r3Back1T) (f := r3Back1TReal)
    (lo := 3 / 8) (hi := 3 / 5)
    (bps := TangentPolyNative.r3Back1Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r3Back1T
    (by native_decide) (by native_decide)
    TangentPolyNative.r3Back1_checks.1
    TangentPolyNative.r3Back1_checks.2
  norm_num at h ⊢
  exact h

lemma r3Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r3Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 :=
by
  have h := witness_mem_of_affine
    (T := TangentAffine.r3Back2T) (f := r3Back2TReal)
    (lo := 3 / 5) (hi := 1)
    (bps := TangentPolyNative.back2Bps)
    (Expr.checkSupportedCore_correct (by native_decide))
    (Expr.checkSupportedCore_correct (by native_decide))
    eval_r3Back2T
    (by native_decide) (by native_decide)
    TangentPolyNative.r3Back2_checks.1
    TangentPolyNative.r3Back2_checks.2
  norm_num at h ⊢
  exact h

end Arxiv2407_19026
