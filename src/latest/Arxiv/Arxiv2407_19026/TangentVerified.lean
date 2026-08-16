import Arxiv.Arxiv2407_19026.TangentAssembly
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back2Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back2Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back2Bounds

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

lemma r1ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      r1ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h := round1_forward_t_bounds hz
  exact ⟨h.1, h.2.1⟩

lemma r1Back1TReal_mem :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      r1Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound1Back1Bounds.round1_back1_t_bounds hz
  exact ⟨h.1, h.2.le⟩

lemma r1Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r1Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound1Back2Bounds.round1_back2_t_bounds hz
  exact ⟨h.1, h.2.trans (by norm_num)⟩

lemma r2ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      r2ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h := round2_forward_t_bounds hz
  exact ⟨h.1, h.2.1⟩

lemma r2Back1TReal_mem :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      r2Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound2Back1Bounds.round2_back1_t_bounds hz
  exact ⟨h.1, h.2.le⟩

lemma r2Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r2Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound2Back2Bounds.round2_back2_t_bounds hz
  exact ⟨h.1, h.2.trans (by norm_num)⟩

lemma r3ForwardTReal_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      r3ForwardTReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h := round3_forward_t_bounds hz
  exact ⟨h.1, h.2.1⟩

lemma r3Back1TReal_mem :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      r3Back1TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound3Back1Bounds.round3_back1_t_bounds hz
  exact ⟨h.1, h.2.le⟩

lemma r3Back2TReal_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      r3Back2TReal z ∈ Set.Ioc (0 : ℝ) 1 := by
  intro z hz
  have h :=
    BackwardCoordRound3Back2Bounds.round3_back2_t_bounds hz
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Arxiv2407_19026
