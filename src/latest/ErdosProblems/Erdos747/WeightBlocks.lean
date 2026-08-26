import ErdosProblems.Erdos747.ThinningAmplification

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Canonical finite top and bottom weight blocks -/

lemma exists_topWeightBlock {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) :
    ∀ d : ℕ, d ≤ s.card →
      ∃ Y : Finset α, Y ⊆ s ∧ Y.card = d ∧
        ∀ y ∈ Y, ∀ x ∈ s \ Y, W x ≤ W y := by
  intro d
  induction d generalizing s with
  | zero =>
      intro hd
      exact ⟨∅, Finset.empty_subset s, by simp, by simp⟩
  | succ d ih =>
      intro hd
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨z, hzs, hzmax⟩ := Finset.exists_max_image s W hs
      have hdErase : d ≤ (s.erase z).card := by
        rw [Finset.card_erase_of_mem hzs]
        omega
      obtain ⟨Y, hYs, hYcard, hYrank⟩ := ih (s.erase z) hdErase
      have hzY : z ∉ Y := by
        intro hz
        exact (Finset.mem_erase.mp (hYs hz)).1 rfl
      refine ⟨insert z Y, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxY
        · exact hzs
        · exact (Finset.mem_erase.mp (hYs hxY)).2
      · rw [Finset.card_insert_of_notMem hzY, hYcard]
      · intro y hy x hx
        rcases Finset.mem_insert.mp hy with rfl | hyY
        · exact hzmax x (Finset.mem_sdiff.mp hx).1
        · apply hYrank y hyY x
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, ?_⟩
          · apply Finset.mem_erase.mpr
            refine ⟨?_, (Finset.mem_sdiff.mp hx).1⟩
            intro hxz
            subst x
            exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_self _ _)
          · intro hxY
            exact (Finset.mem_sdiff.mp hx).2
              (Finset.mem_insert_of_mem hxY)

/-- A fixed choice of `d` largest elements, with ties resolved by choice.
It is empty only when `d` exceeds the size of the ambient set. -/
def topWeightBlock {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) : Finset α :=
  if h : d ≤ s.card then
    Classical.choose (exists_topWeightBlock s W d h)
  else ∅

lemma topWeightBlock_spec {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) (hd : d ≤ s.card) :
    topWeightBlock s W d ⊆ s ∧
      (topWeightBlock s W d).card = d ∧
      ∀ y ∈ topWeightBlock s W d,
        ∀ x ∈ s \ topWeightBlock s W d, W x ≤ W y := by
  rw [topWeightBlock, dif_pos hd]
  exact Classical.choose_spec (exists_topWeightBlock s W d hd)

lemma topWeightBlock_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) :
    topWeightBlock s W d ⊆ s := by
  by_cases hd : d ≤ s.card
  · exact (topWeightBlock_spec s W d hd).1
  · simp [topWeightBlock, hd]

lemma card_topWeightBlock {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) (hd : d ≤ s.card) :
    (topWeightBlock s W d).card = d :=
  (topWeightBlock_spec s W d hd).2.1

lemma topWeightBlock_mem_gt_of_many_gt {α : Type*} [DecidableEq α]
    (s X : Finset α) (W : α → ℝ) (d : ℕ) (a : ℝ)
    (hd : d ≤ s.card) (hXs : X ⊆ s) (hcard : d < X.card)
    (hX : ∀ x ∈ X, a < W x) :
    ∀ y ∈ topWeightBlock s W d, a < W y := by
  intro y hy
  by_contra hyLow
  have hXY : X ⊆ topWeightBlock s W d := by
    intro x hxX
    by_contra hxY
    have hxDiff : x ∈ s \ topWeightBlock s W d :=
      Finset.mem_sdiff.mpr ⟨hXs hxX, hxY⟩
    have hrank := (topWeightBlock_spec s W d hd).2.2 y hy x hxDiff
    exact (not_lt_of_ge (hrank.trans (le_of_not_gt hyLow))) (hX x hxX)
  have hle := Finset.card_le_card hXY
  rw [card_topWeightBlock s W d hd] at hle
  omega

def bottomWeightBlock {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) : Finset α :=
  topWeightBlock s (fun x ↦ -W x) d

lemma bottomWeightBlock_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) :
    bottomWeightBlock s W d ⊆ s :=
  topWeightBlock_subset s (fun x ↦ -W x) d

lemma card_bottomWeightBlock {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (d : ℕ) (hd : d ≤ s.card) :
    (bottomWeightBlock s W d).card = d :=
  card_topWeightBlock s (fun x ↦ -W x) d hd

lemma bottomWeightBlock_mem_lt_of_many_lt
    {α : Type*} [DecidableEq α]
    (s X : Finset α) (W : α → ℝ) (d : ℕ) (a : ℝ)
    (hd : d ≤ s.card) (hXs : X ⊆ s) (hcard : d < X.card)
    (hX : ∀ x ∈ X, W x < a) :
    ∀ y ∈ bottomWeightBlock s W d, W y < a := by
  intro y hy
  have htop := topWeightBlock_mem_gt_of_many_gt
    s X (fun x ↦ -W x) d (-a) hd hXs hcard
      (fun x hx ↦ by linarith [hX x hx]) y hy
  linarith

lemma filter_topWeightBlock_le_exception_card
    {α : Type*} [DecidableEq α]
    (s T : Finset α) (W : α → ℝ) (d : ℕ) (a : ℝ)
    (hd : d ≤ s.card)
    (hblock : ∀ y ∈ topWeightBlock s W d, a < W y) :
    ((T.filter fun y ↦ y ∈ topWeightBlock s W d).card : ℝ) ≤
      ((T.filter fun y ↦ a < W y).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyT, hyB⟩
    exact Finset.mem_filter.mpr ⟨hyT, hblock y hyB⟩)

lemma filter_bottomWeightBlock_le_exception_card
    {α : Type*} [DecidableEq α]
    (s T : Finset α) (W : α → ℝ) (d : ℕ) (a : ℝ)
    (hd : d ≤ s.card)
    (hblock : ∀ y ∈ bottomWeightBlock s W d, W y < a) :
    ((T.filter fun y ↦ y ∈ bottomWeightBlock s W d).card : ℝ) ≤
      ((T.filter fun y ↦ W y < a).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyT, hyB⟩
    exact Finset.mem_filter.mpr ⟨hyT, hblock y hyB⟩)

def TopBlockUnderhit {α : Type*} [DecidableEq α]
    (s T : Finset α) (W : α → ℝ) (d t : ℕ) : Prop :=
  (((T.filter fun y ↦ y ∈ topWeightBlock s W d).card : ℕ) : ℝ) ≤
    (3 / 4 : ℝ) * (t : ℝ) *
      (((topWeightBlock s W d).card : ℝ) / s.card)

def BottomBlockUnderhit {α : Type*} [DecidableEq α]
    (s T : Finset α) (W : α → ℝ) (d t : ℕ) : Prop :=
  (((T.filter fun y ↦ y ∈ bottomWeightBlock s W d).card : ℕ) : ℝ) ≤
    (3 / 4 : ℝ) * (t : ℝ) *
      (((bottomWeightBlock s W d).card : ℝ) / s.card)

lemma topBlockUnderhit_of_many_gt {α : Type*} [DecidableEq α]
    (s T X : Finset α) (W : α → ℝ) (d t e : ℕ) (a : ℝ)
    (hd : d ≤ s.card) (hXs : X ⊆ s) (hcard : d < X.card)
    (hX : ∀ x ∈ X, a < W x)
    (hexceptions :
      (T.filter fun y ↦ a < W y).card ≤ e)
    (he : (e : ℝ) ≤
      (3 / 4 : ℝ) * (t : ℝ) * ((d : ℝ) / s.card)) :
    TopBlockUnderhit s T W d t := by
  have hblock := topWeightBlock_mem_gt_of_many_gt
    s X W d a hd hXs hcard hX
  have hhit := filter_topWeightBlock_le_exception_card
    s T W d a hd hblock
  unfold TopBlockUnderhit
  rw [card_topWeightBlock s W d hd]
  exact hhit.trans ((Nat.cast_le.mpr hexceptions).trans he)

lemma bottomBlockUnderhit_of_many_lt {α : Type*} [DecidableEq α]
    (s T X : Finset α) (W : α → ℝ) (d t e : ℕ) (a : ℝ)
    (hd : d ≤ s.card) (hXs : X ⊆ s) (hcard : d < X.card)
    (hX : ∀ x ∈ X, W x < a)
    (hexceptions :
      (T.filter fun y ↦ W y < a).card ≤ e)
    (he : (e : ℝ) ≤
      (3 / 4 : ℝ) * (t : ℝ) * ((d : ℝ) / s.card)) :
    BottomBlockUnderhit s T W d t := by
  have hblock := bottomWeightBlock_mem_lt_of_many_lt
    s X W d a hd hXs hcard hX
  have hhit := filter_bottomWeightBlock_le_exception_card
    s T W d a hd hblock
  unfold BottomBlockUnderhit
  rw [card_bottomWeightBlock s W d hd]
  exact hhit.trans ((Nat.cast_le.mpr hexceptions).trans he)

lemma topBlockUnderhit_powersetCard_probability_le
    {n d t : ℕ} (s : Finset (Edge n)) (W : Edge n → ℝ)
    (hd : d ≤ s.card) (ht : t ≤ s.card)
    (hs : s.Nonempty) (hcollision : 2 * t * t ≤ s.card) :
    finsetProbability (s.powersetCard t)
        (fun T ↦ TopBlockUnderhit s T W d t) ≤
      2 * Real.exp (-((t : ℝ) * ((d : ℝ) / s.card)) / 64) := by
  have htail := powersetCard_hitCount_three_quarters_le_mean
    s (topWeightBlock s W d)
      (topWeightBlock_subset s W d) ht hs hcollision
  simpa only [TopBlockUnderhit, card_topWeightBlock s W d hd] using htail

lemma bottomBlockUnderhit_powersetCard_probability_le
    {n d t : ℕ} (s : Finset (Edge n)) (W : Edge n → ℝ)
    (hd : d ≤ s.card) (ht : t ≤ s.card)
    (hs : s.Nonempty) (hcollision : 2 * t * t ≤ s.card) :
    finsetProbability (s.powersetCard t)
        (fun T ↦ BottomBlockUnderhit s T W d t) ≤
      2 * Real.exp (-((t : ℝ) * ((d : ℝ) / s.card)) / 64) := by
  have htail := powersetCard_hitCount_three_quarters_le_mean
    s (bottomWeightBlock s W d)
      (bottomWeightBlock_subset s W d) ht hs hcollision
  simpa only [BottomBlockUnderhit, card_bottomWeightBlock s W d hd] using htail

end

end Erdos747
