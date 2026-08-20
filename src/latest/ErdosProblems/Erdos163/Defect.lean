/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Basic
import Mathlib.Data.ENNReal.Inv

/-!
# Erdős Problem 163: common-neighborhood defect

This is the finite `ℝ≥0∞` version of Lee's defect.  The value at an empty
common neighborhood is genuinely infinite, so none of the later positivity
arguments can silently turn division by zero into zero.
-/

open scoped BigOperators ENNReal
open Finset

namespace Erdos163
namespace Defect

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Common neighbors in `T` of every entry of an indexed tuple. -/
def commonNeighbors (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) : Finset α :=
  T.filter fun x => ∀ i, G.Adj (q i) x

@[simp] theorem mem_commonNeighbors (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) (x : α) :
    x ∈ commonNeighbors G q T ↔ x ∈ T ∧ ∀ i, G.Adj (q i) x := by
  simp [commonNeighbors]

theorem commonNeighbors_subset_target (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) :
    commonNeighbors G q T ⊆ T :=
  filter_subset _ _

theorem commonNeighbors_mono_target (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) {T T' : Finset α} (hTT' : T ⊆ T') :
    commonNeighbors G q T ⊆ commonNeighbors G q T' := by
  intro x hx
  rw [mem_commonNeighbors] at hx ⊢
  exact ⟨hTT' hx.1, hx.2⟩

/-- Adding tuple coordinates can only shrink the common neighborhood. -/
theorem commonNeighbors_anti_coordinates (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → α) (q' : κ → α) (e : ι → κ) (he : q = q' ∘ e) (T : Finset α) :
    commonNeighbors G q' T ⊆ commonNeighbors G q T := by
  intro x hx
  rw [mem_commonNeighbors] at hx ⊢
  refine ⟨hx.1, fun i => ?_⟩
  simpa [he] using hx.2 (e i)

/-- Lee's threshold defect. -/
noncomputable def defect (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℝ≥0∞) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) : ℝ≥0∞ :=
  if θ ≤ (commonNeighbors G q T).card then 0
  else θ / (commonNeighbors G q T).card

theorem defect_eq_zero_of_threshold_le (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℝ≥0∞} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (h : θ ≤ (commonNeighbors G q T).card) : defect G θ q T = 0 := by
  simp [defect, h]

theorem defect_eq_div_of_card_lt (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℝ≥0∞} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (h : ((commonNeighbors G q T).card : ℝ≥0∞) < θ) :
    defect G θ q T = θ / (commonNeighbors G q T).card := by
  simp [defect, not_le_of_gt h]

theorem defect_eq_top_of_empty (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℝ≥0∞} (hθ : θ ≠ 0) {ι : Type*} [Fintype ι]
    {q : ι → α} {T : Finset α} (h : commonNeighbors G q T = ∅) :
    defect G θ q T = ∞ := by
  rw [defect]
  simp only [h, card_empty, Nat.cast_zero]
  rw [if_neg]
  · exact ENNReal.div_zero hθ
  · exact fun hle => hθ (nonpos_iff_eq_zero.mp hle)

theorem one_le_defect_of_ne_zero (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℝ≥0∞} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (h : defect G θ q T ≠ 0) : 1 ≤ defect G θ q T := by
  have hcard : ((commonNeighbors G q T).card : ℝ≥0∞) < θ := by
    by_contra hnot
    have hle : θ ≤ (commonNeighbors G q T).card := le_of_not_gt hnot
    exact h (defect_eq_zero_of_threshold_le G hle)
  rw [defect_eq_div_of_card_lt G hcard]
  have hθ0 : θ ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hcard)
  apply (ENNReal.le_div_iff_mul_le (Or.inr hθ0) (Or.inl (by simp))).2
  simpa using hcard.le

/-- Defect increases when the threshold increases, coordinates are added,
or the target set is restricted. -/
theorem defect_mono (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ θ' : ℝ≥0∞} (hθ : θ ≤ θ')
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → α) (q' : κ → α) (e : ι → κ) (he : q = q' ∘ e)
    {T T' : Finset α} (hT : T' ⊆ T) :
    defect G θ q T ≤ defect G θ' q' T' := by
  by_cases hsmall : θ ≤ (commonNeighbors G q T).card
  · rw [defect_eq_zero_of_threshold_le G hsmall]
    exact bot_le
  · have hcoord := commonNeighbors_anti_coordinates G q q' e he T'
    have htarget := commonNeighbors_mono_target G q hT
    have hsub : commonNeighbors G q' T' ⊆ commonNeighbors G q T := hcoord.trans htarget
    have hcard : (commonNeighbors G q' T').card ≤ (commonNeighbors G q T).card :=
      card_le_card hsub
    have hcard' : ((commonNeighbors G q' T').card : ℝ≥0∞) ≤
        (commonNeighbors G q T).card := by
      exact_mod_cast hcard
    have hold : ((commonNeighbors G q T).card : ℝ≥0∞) < θ := lt_of_not_ge hsmall
    have hnew : ((commonNeighbors G q' T').card : ℝ≥0∞) < θ' := by
      exact hcard'.trans_lt (hold.trans_le hθ)
    rw [defect_eq_div_of_card_lt G hold, defect_eq_div_of_card_lt G hnew]
    exact ENNReal.div_le_div hθ hcard'

/-- Powers used in defect moments use Lee's convention `0^0 = 0`. -/
noncomputable def defectPower (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℝ≥0∞) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α)
    (s : ℕ) : ℝ≥0∞ :=
  if defect G θ q T = 0 then 0 else defect G θ q T ^ s

/-- Average `s`-th defect over a product of coordinate sets. -/
noncomputable def moment (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℝ≥0∞) (s : ℕ) (A : Fin D → Finset α) (T : Finset α) : ℝ≥0∞ :=
  (∑ q : ∀ i, A i, defectPower G θ (fun i => (q i : α)) T s) /
    Fintype.card (∀ i, A i)

theorem moment_nonneg (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℝ≥0∞) (s : ℕ) (A : Fin D → Finset α) (T : Finset α) :
    0 ≤ moment G θ s A T :=
  bot_le

theorem defectPower_mono_exponent (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℝ≥0∞} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    {s t : ℕ} (hst : s ≤ t) :
    defectPower G θ q T s ≤ defectPower G θ q T t := by
  by_cases hzero : defect G θ q T = 0
  · simp [defectPower, hzero]
  · simp only [defectPower, hzero, if_false]
    exact pow_le_pow_right₀ (one_le_defect_of_ne_zero G hzero) hst

theorem moment_mono_exponent (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℝ≥0∞) (A : Fin D → Finset α) (T : Finset α)
    {s t : ℕ} (hst : s ≤ t) :
    moment G θ s A T ≤ moment G θ t A T := by
  unfold moment
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun q _ => defectPower_mono_exponent G hst

end Defect
end Erdos163
