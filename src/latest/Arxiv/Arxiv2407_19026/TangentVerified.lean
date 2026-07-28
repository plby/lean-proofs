import Arxiv.Arxiv2407_19026.TangentAssembly
import Arxiv.Arxiv2407_19026.TangentPolyChecks

/-! Soundness wrappers shared by the certified tangent rounds. -/

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

namespace TangentAffine

private lemma coeRange_ne (count : ℕ) (hc : count ≠ 0) :
    ((List.range count : List ℕ) : List ℚ) ≠ [] := by
  change (List.range count).flatMap (fun n : ℕ => [(n : ℚ)]) ≠ []
  cases count with
  | zero => exact (hc rfl).elim
  | succ n => simp [List.range_succ]

private lemma coeRange_getLast (count : ℕ) (hc : count ≠ 0)
    (h : ((List.range count : List ℕ) : List ℚ) ≠ []) :
    (((List.range count : List ℕ) : List ℚ)).getLast h =
      ((count - 1 : ℕ) : ℚ) := by
  change
    ((List.range count).flatMap (fun n : ℕ => [(n : ℚ)])).getLast h = _
  cases count with
  | zero => exact (hc rfl).elim
  | succ n => simp [List.range_succ]

/-- A nonempty natural-number range remains nonempty after coercion to
rationals and mapping. -/
lemma mappedCoeRange_ne (f : ℚ → ℚ) (count : ℕ) (hc : count ≠ 0) :
    (((List.range count : List ℕ) : List ℚ).map f) ≠ [] := by
  rw [ne_eq, List.map_eq_nil_iff]
  exact coeRange_ne count hc

/-- The final value in a mapped, rationally coerced natural-number range. -/
lemma mappedCoeRange_getLast (f : ℚ → ℚ) (count : ℕ) (hc : count ≠ 0)
    (h : (((List.range count : List ℕ) : List ℚ).map f) ≠ []) :
    ((((List.range count : List ℕ) : List ℚ).map f)).getLast h =
      f ((count - 1 : ℕ) : ℚ) := by
  rw [List.getLast_map, coeRange_getLast count hc]

/-- A positive-length mapped natural-number range is nonempty. -/
lemma mappedRange_ne {α : Type} (f : ℕ → α) (count : ℕ) (hc : count ≠ 0) :
    (List.range count).map f ≠ [] := by
  rw [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact hc

/-- The final value in a positive-length mapped natural-number range. -/
lemma mappedRange_getLast {α : Type} (f : ℕ → α) (count : ℕ)
    (h : (List.range count).map f ≠ []) :
    ((List.range count).map f).getLast h = f (count - 1) := by
  rw [List.getLast_map, List.getLast_range]

/-- A positive-length flat-mapped range is nonempty when its final block is
nonempty. -/
lemma flatMapRange_ne {α : Type} (f : ℕ → List α) (count : ℕ)
    (hc : count ≠ 0) (hlast : f (count - 1) ≠ []) :
    (List.range count).flatMap f ≠ [] := by
  cases count with
  | zero => exact (hc rfl).elim
  | succ n =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact List.append_ne_nil_of_right_ne_nil _ (by simpa using hlast)

/-- The final value in a positive-length flat-mapped range whose final block
is nonempty. -/
lemma flatMapRange_getLast {α : Type} (f : ℕ → List α) (count : ℕ)
    (hc : count ≠ 0) (hlast : f (count - 1) ≠ [])
    (h : (List.range count).flatMap f ≠ []) :
    ((List.range count).flatMap f).getLast h =
      (f (count - 1)).getLast hlast := by
  cases count with
  | zero => exact (hc rfl).elim
  | succ n =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact List.getLast_append_of_right_ne_nil _ _ (by simpa using hlast)

/-- A positive-length fine breakpoint grid is nonempty. -/
lemma fineBreakpoints_ne (start count : ℕ) (hc : count ≠ 0) :
    fineBreakpoints start count ≠ [] := by
  unfold fineBreakpoints
  exact mappedCoeRange_ne _ count hc

/-- The final point in a positive-length fine breakpoint grid. -/
lemma fineBreakpoints_getLast (start count : ℕ) (hc : count ≠ 0)
    (h : fineBreakpoints start count ≠ []) :
    (fineBreakpoints start count).getLast h =
      (((count - 1 : ℕ) : ℚ) + start + 1) / 10000 := by
  unfold fineBreakpoints at h ⊢
  exact mappedCoeRange_getLast _ count hc h

/-- A positive-length medium breakpoint grid is nonempty. -/
lemma mediumBreakpoints_ne (start count : ℕ) (hc : count ≠ 0) :
    mediumBreakpoints start count ≠ [] := by
  unfold mediumBreakpoints
  exact mappedCoeRange_ne _ count hc

/-- The final point in a positive-length medium breakpoint grid. -/
lemma mediumBreakpoints_getLast (start count : ℕ) (hc : count ≠ 0)
    (h : mediumBreakpoints start count ≠ []) :
    (mediumBreakpoints start count).getLast h =
      (((count - 1 : ℕ) : ℚ) + start + 1) / 1000 := by
  unfold mediumBreakpoints at h ⊢
  exact mappedCoeRange_getLast _ count hc h

end TangentAffine

private lemma r1ForwardBps_ne : TangentPolyNative.r1ForwardBps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 100 169 (by norm_num)

private lemma r1ForwardBps_last :
    TangentPolyNative.r1ForwardBps.getLast r1ForwardBps_ne = 269 / 1000 := by
  unfold TangentPolyNative.r1ForwardBps
  convert TangentAffine.mediumBreakpoints_getLast
    100 169 (by norm_num) r1ForwardBps_ne using 1
  all_goals norm_num

private lemma r1Back1Bps_ne : TangentPolyNative.r1Back1Bps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 387 213 (by norm_num)

private lemma r1Back1Bps_last :
    TangentPolyNative.r1Back1Bps.getLast r1Back1Bps_ne = 3 / 5 := by
  unfold TangentPolyNative.r1Back1Bps
  convert TangentAffine.mediumBreakpoints_getLast
    387 213 (by norm_num) r1Back1Bps_ne using 1
  all_goals norm_num

private lemma back2Bps_ne : TangentPolyNative.back2Bps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 600 400 (by norm_num)

private lemma back2Bps_last :
    TangentPolyNative.back2Bps.getLast back2Bps_ne = 1 := by
  unfold TangentPolyNative.back2Bps
  convert TangentAffine.mediumBreakpoints_getLast
    600 400 (by norm_num) back2Bps_ne using 1
  all_goals norm_num

private lemma r2ForwardBps_ne : TangentPolyNative.r2ForwardBps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 100 168 (by norm_num)

private lemma r2ForwardBps_last :
    TangentPolyNative.r2ForwardBps.getLast r2ForwardBps_ne = 67 / 250 := by
  unfold TangentPolyNative.r2ForwardBps
  convert TangentAffine.mediumBreakpoints_getLast
    100 168 (by norm_num) r2ForwardBps_ne using 1
  all_goals norm_num

private lemma r2Back1Bps_ne : TangentPolyNative.r2Back1Bps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 378 222 (by norm_num)

private lemma r2Back1Bps_last :
    TangentPolyNative.r2Back1Bps.getLast r2Back1Bps_ne = 3 / 5 := by
  unfold TangentPolyNative.r2Back1Bps
  convert TangentAffine.mediumBreakpoints_getLast
    378 222 (by norm_num) r2Back1Bps_ne using 1
  all_goals norm_num

private lemma r3ForwardBps_ne : TangentPolyNative.r3ForwardBps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 100 168 (by norm_num)

private lemma r3ForwardBps_last :
    TangentPolyNative.r3ForwardBps.getLast r3ForwardBps_ne = 67 / 250 := by
  unfold TangentPolyNative.r3ForwardBps
  convert TangentAffine.mediumBreakpoints_getLast
    100 168 (by norm_num) r3ForwardBps_ne using 1
  all_goals norm_num

private lemma r3Back1Bps_ne : TangentPolyNative.r3Back1Bps ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 375 225 (by norm_num)

private lemma r3Back1Bps_last :
    TangentPolyNative.r3Back1Bps.getLast r3Back1Bps_ne = 3 / 5 := by
  unfold TangentPolyNative.r3Back1Bps
  convert TangentAffine.mediumBreakpoints_getLast
    375 225 (by norm_num) r3Back1Bps_ne using 1
  all_goals norm_num

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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r1ForwardT
    r1ForwardBps_ne r1ForwardBps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r1Back1T
    r1Back1Bps_ne r1Back1Bps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r1Back2T
    back2Bps_ne back2Bps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r2ForwardT
    r2ForwardBps_ne r2ForwardBps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r2Back1T
    r2Back1Bps_ne r2Back1Bps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r2Back2T
    back2Bps_ne back2Bps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r3ForwardT
    r3ForwardBps_ne r3ForwardBps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r3Back1T
    r3Back1Bps_ne r3Back1Bps_last
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
    (Expr.checkSupportedCore_correct (by decide))
    (Expr.checkSupportedCore_correct (by decide))
    eval_r3Back2T
    back2Bps_ne back2Bps_last
    TangentPolyNative.r3Back2_checks.1
    TangentPolyNative.r3Back2_checks.2
  norm_num at h ⊢
  exact h

end Arxiv2407_19026
