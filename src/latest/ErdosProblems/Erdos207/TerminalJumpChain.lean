/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterInduction

/-! # Master induction along a chain which can jump to the terminal level -/

namespace Erdos207

open scoped NNReal

noncomputable section

def terminalJumpStage (ell length : ℕ) (hfit : length ≤ ell)
    (i : Fin (length + 1)) : Fin (ell + 1) :=
  if h : i.val < length then ⟨i.val, by omega⟩ else Fin.last ell

@[simp] theorem terminalJumpStage_last (ell length : ℕ) (hfit : length ≤ ell) :
    terminalJumpStage ell length hfit (Fin.last length) = Fin.last ell := by
  simp [terminalJumpStage]

@[simp] theorem terminalJumpStage_castSucc (ell length : ℕ) (hfit : length ≤ ell)
    (i : Fin length) :
    terminalJumpStage ell length hfit i.castSucc = ⟨i.val, by have := i.isLt; omega⟩ := by
  simp [terminalJumpStage, i.isLt]

@[simp] theorem terminalJumpStage_zero (ell length : ℕ) (hfit : length ≤ ell)
    (hlength : 0 < length) : terminalJumpStage ell length hfit 0 = 0 := by
  simp [terminalJumpStage, hlength]

theorem terminalJumpStage_strictMono (ell length : ℕ) (hfit : length ≤ ell) :
    StrictMono (terminalJumpStage ell length hfit) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hi : i.val < length := by have := j.isLt; omega
  by_cases hj : j.val < length
  · simpa only [terminalJumpStage, dif_pos hi, dif_pos hj, Fin.mk_lt_mk] using hij'
  · simp only [terminalJumpStage, dif_pos hi, dif_neg hj, Fin.lt_def,
      Fin.val_last]
    omega

theorem exists_residualCompressedMasterLaw_along_chain
    {V : Type*} [Fintype V] [DecidableEq V] {ell length : ℕ}
    (W : Vortex V ell) (stage : Fin (length + 1) → Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (Gzero : SimpleGraph V) (ambient : TripleSystemOn V)
    (p eta xi C b : Fin (length + 1) → ℝ≥0) (h : ℕ)
    (hbase : ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W (stage 0) F Gzero ambient
        (p 0) (eta 0) (xi 0) (C 0) (b 0) h)
    (hstep : ∀ i : Fin length, ∀ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W (stage i.castSucc) F Gzero ambient
          (p i.castSucc) (eta i.castSucc) (xi i.castSucc) (C i.castSucc) (b i.castSucc) h →
        ∃ law' : FiniteLaw (MasterStateOn V),
          IsResidualCompressedMasterLaw law' W (stage i.succ) F Gzero ambient
            (p i.succ) (eta i.succ) (xi i.succ) (C i.succ) (b i.succ) h) :
    ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W (stage (Fin.last length)) F Gzero ambient
        (p (Fin.last length)) (eta (Fin.last length)) (xi (Fin.last length))
        (C (Fin.last length)) (b (Fin.last length)) h := by
  have hlevel : ∀ i : Fin (length + 1), ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W (stage i) F Gzero ambient
        (p i) (eta i) (xi i) (C i) (b i) h := by
    intro i
    induction i using Fin.induction with
    | zero => exact hbase
    | succ i ih =>
      obtain ⟨law, hlaw⟩ := ih
      exact hstep i law hlaw
  exact hlevel (Fin.last length)

end

end Erdos207
