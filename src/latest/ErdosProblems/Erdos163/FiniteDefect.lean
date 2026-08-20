/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Defect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Erdős Problem 163: finite real-valued defect

All host graphs in the proof are finite.  For real-valued finite expectations
we replace the infinite empty-neighborhood value by the sentinel
`θ * (|V| + 1)`.  It is larger than every finite reciprocal defect that can
occur.  The later small-moment hypotheses therefore exclude empty common
neighborhoods exactly as the extended-real definition does.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace FiniteDefect

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

def commonNeighbors (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) : Finset α :=
  Defect.commonNeighbors G q T

/-- Real-valued finite defect with a sentinel at denominator zero. -/
noncomputable def defect (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℕ) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) : ℝ :=
  let m := (commonNeighbors G q T).card
  if θ ≤ m then 0 else if m = 0 then θ * (Fintype.card α + 1) else θ / m

theorem defect_nonneg (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℕ) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) :
    0 ≤ defect G θ q T := by
  unfold defect
  dsimp
  split_ifs
  · exact le_rfl
  · positivity
  · positivity

theorem defect_eq_zero_of_threshold_le (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (h : θ ≤ (commonNeighbors G q T).card) : defect G θ q T = 0 := by
  simp [defect, h]

theorem defect_eq_sentinel_of_empty (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} (hθ : 0 < θ) {ι : Type*} [Fintype ι]
    {q : ι → α} {T : Finset α} (h : commonNeighbors G q T = ∅) :
    defect G θ q T = θ * (Fintype.card α + 1) := by
  simp [defect, h, Nat.not_le_of_lt hθ]

theorem defect_eq_div_of_pos_card_lt (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (hpos : 0 < (commonNeighbors G q T).card)
    (hlt : (commonNeighbors G q T).card < θ) :
    defect G θ q T = (θ : ℝ) / (commonNeighbors G q T).card := by
  simp [defect, Nat.not_le_of_lt hlt, Nat.ne_of_gt hpos]

theorem one_le_defect_of_ne_zero (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    (h : defect G θ q T ≠ 0) : 1 ≤ defect G θ q T := by
  have hlt : (commonNeighbors G q T).card < θ := by
    by_contra hnot
    exact h (defect_eq_zero_of_threshold_le G (Nat.le_of_not_gt hnot))
  by_cases hzero : (commonNeighbors G q T).card = 0
  · have hθ : 0 < θ := hzero ▸ hlt
    rw [defect_eq_sentinel_of_empty G hθ (card_eq_zero.mp hzero)]
    have hθR : (1 : ℝ) ≤ θ := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hθ)
    calc
      (1 : ℝ) ≤ θ := hθR
      _ ≤ θ * (Fintype.card α + 1) :=
        le_mul_of_one_le_right (by positivity) (by norm_num)
  · rw [defect_eq_div_of_pos_card_lt G (Nat.pos_of_ne_zero hzero) hlt]
    exact (one_le_div₀ (by positivity)).2 (by exact_mod_cast hlt.le)

/-- Adding tuple coordinates and restricting the target can only increase the
finite sentinel defect (at a fixed threshold). -/
theorem defect_mono_coordinates_target (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → α) (q' : κ → α) (e : ι → κ) (he : q = q' ∘ e)
    {T T' : Finset α} (hT : T' ⊆ T) :
    defect G θ q T ≤ defect G θ q' T' := by
  classical
  let m := (commonNeighbors G q T).card
  let m' := (commonNeighbors G q' T').card
  have hsub : commonNeighbors G q' T' ⊆ commonNeighbors G q T := by
    exact (Defect.commonNeighbors_anti_coordinates G q q' e he T').trans
      (Defect.commonNeighbors_mono_target G q hT)
  have hmm : m' ≤ m := Finset.card_le_card hsub
  by_cases hold : θ ≤ m
  · rw [defect_eq_zero_of_threshold_le G hold]
    exact defect_nonneg G θ q' T'
  have hmθ : m < θ := Nat.lt_of_not_ge hold
  by_cases hnewzero : m' = 0
  · have hθ : 0 < θ := lt_of_le_of_lt (Nat.zero_le m) hmθ
    have hnewempty : commonNeighbors G q' T' = ∅ :=
      Finset.card_eq_zero.mp hnewzero
    rw [defect_eq_sentinel_of_empty G hθ hnewempty]
    by_cases holdzero : m = 0
    · have holdempty : commonNeighbors G q T = ∅ := Finset.card_eq_zero.mp holdzero
      rw [defect_eq_sentinel_of_empty G hθ holdempty]
    · rw [defect_eq_div_of_pos_card_lt G (Nat.pos_of_ne_zero holdzero) hmθ]
      have hdiv : (θ : ℝ) / m ≤ θ := by
        exact div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr holdzero)
      exact hdiv.trans (le_mul_of_one_le_right (by positivity) (by norm_num))
  · have hm'pos : 0 < m' := Nat.pos_of_ne_zero hnewzero
    have hm'θ : m' < θ := hmm.trans_lt hmθ
    rw [defect_eq_div_of_pos_card_lt G (lt_of_lt_of_le hm'pos hmm) hmθ,
      defect_eq_div_of_pos_card_lt G hm'pos hm'θ]
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hm'pos)
      (by exact_mod_cast hmm)

/-- Lee's convention makes the zeroth power of zero defect equal to zero. -/
noncomputable def defectPower (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℕ) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α)
    (s : ℕ) : ℝ :=
  if defect G θ q T = 0 then 0 else defect G θ q T ^ s

theorem defectPower_nonneg (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ : ℕ) {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) (s : ℕ) :
    0 ≤ defectPower G θ q T s := by
  unfold defectPower
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (defect_nonneg G θ q T) _

theorem defectPower_mono_coordinates_target (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ s : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → α) (q' : κ → α) (e : ι → κ) (he : q = q' ∘ e)
    {T T' : Finset α} (hT : T' ⊆ T) :
    defectPower G θ q T s ≤ defectPower G θ q' T' s := by
  classical
  have hdef := defect_mono_coordinates_target G (θ := θ) q q' e he hT
  by_cases hz : defect G θ q T = 0
  · rw [defectPower, if_pos hz]
    exact defectPower_nonneg G θ q' T' s
  · have hz' : defect G θ q' T' ≠ 0 := by
      intro hnew
      apply hz
      have holdle : defect G θ q T ≤ 0 := by simpa [hnew] using hdef
      exact le_antisymm holdle (defect_nonneg G θ q T)
    simp only [defectPower, hz, hz', if_false]
    exact pow_le_pow_left₀ (defect_nonneg G θ q T) hdef s

theorem defectPower_mono_exponent (G : SimpleGraph α) [DecidableRel G.Adj]
    {θ : ℕ} {ι : Type*} [Fintype ι] {q : ι → α} {T : Finset α}
    {s t : ℕ} (hst : s ≤ t) :
    defectPower G θ q T s ≤ defectPower G θ q T t := by
  by_cases hzero : defect G θ q T = 0
  · simp [defectPower, hzero]
  · simp only [defectPower, hzero, if_false]
    exact pow_le_pow_right₀ (one_le_defect_of_ne_zero G hzero) hst

/-- The finite product of coordinate sets, represented as a finset of tuples. -/
def tuples {D : ℕ} (A : Fin D → Finset α) : Finset (Fin D → α) :=
  Fintype.piFinset A

@[simp] theorem mem_tuples {D : ℕ} (A : Fin D → Finset α) (q : Fin D → α) :
    q ∈ tuples A ↔ ∀ i, q i ∈ A i := by
  simp [tuples]

@[simp] theorem card_tuples {D : ℕ} (A : Fin D → Finset α) :
    (tuples A).card = ∏ i, (A i).card := by
  simp [tuples]

/-- Average defect over a product of coordinate sets. -/
noncomputable def moment (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℕ) (s : ℕ) (A : Fin D → Finset α) (T : Finset α) : ℝ :=
  𝔼 q ∈ tuples A, defectPower G θ q T s

theorem moment_nonneg (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℕ) (s : ℕ) (A : Fin D → Finset α) (T : Finset α) :
    0 ≤ moment G θ s A T := by
  unfold moment Finset.expect
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg fun q _ => defectPower_nonneg G θ q T s

theorem moment_mono_exponent (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ : ℕ) (A : Fin D → Finset α) (T : Finset α)
    {s t : ℕ} (hst : s ≤ t) :
    moment G θ s A T ≤ moment G θ t A T := by
  unfold moment
  exact Finset.expect_le_expect fun q _ => defectPower_mono_exponent G hst

/-- Uniform sample tuples from a fixed vertex set. -/
def samples (t : ℕ) (A : Finset α) : Finset (Fin t → α) :=
  Fintype.piFinset fun _ => A

@[simp] theorem mem_samples (t : ℕ) (A : Finset α) (x : Fin t → α) :
    x ∈ samples t A ↔ ∀ i, x i ∈ A := by
  simp [samples]

@[simp] theorem card_samples (t : ℕ) (A : Finset α) :
    (samples t A).card = A.card ^ t := by
  simp [samples]

/-! ## Products indexed by an arbitrary finite type -/

def familyTuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset α) : Finset (ι → α) :=
  Fintype.piFinset A

@[simp] theorem mem_familyTuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset α) (q : ι → α) :
    q ∈ familyTuples A ↔ ∀ i, q i ∈ A i := by
  simp [familyTuples]

@[simp] theorem card_familyTuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset α) :
    (familyTuples A).card = ∏ i, (A i).card := by
  simp [familyTuples]

noncomputable def familyMoment (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (θ s : ℕ)
    (A : ι → Finset α) (T : Finset α) : ℝ :=
  𝔼 q ∈ familyTuples A, defectPower G θ q T s

theorem familyMoment_nonneg (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (θ s : ℕ)
    (A : ι → Finset α) (T : Finset α) :
    0 ≤ familyMoment G θ s A T := by
  unfold familyMoment Finset.expect
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg fun q _ => defectPower_nonneg G θ q T s

theorem familyMoment_fin (G : SimpleGraph α) [DecidableRel G.Adj]
    {D : ℕ} (θ s : ℕ) (A : Fin D → Finset α) (T : Finset α) :
    familyMoment G θ s A T = moment G θ s A T := by
  rfl

end FiniteDefect
end Erdos163
