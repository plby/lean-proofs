/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringPrefix

/-! # Original-support preservation for every selected covering edge -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v}

def coverHistoryChoice {j m : ℕ} (h : j < m) (s : CoverHistory I Ω m) :
    I j → Option (Ω j) := (coverHistoryPrefix (Nat.succ_le_of_lt h) s).2

theorem coverHistoryChoice_last (m : ℕ) (s : CoverHistory I Ω (m + 1)) :
    coverHistoryChoice (Nat.lt_succ_self m) s = s.2 := by
  simp only [coverHistoryChoice, coverHistoryPrefix_self]

theorem coverHistoryChoice_succ {j m : ℕ} (h : j < m) (s : CoverHistory I Ω (m + 1)) :
    coverHistoryChoice (Nat.lt_succ_of_lt h) s = coverHistoryChoice h s.1 := by
  simp only [coverHistoryChoice, coverHistoryPrefix_succ (Nat.succ_le_of_lt h)]

variable {α : Type w} [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]
  (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)

def coveringSelectedEdge {j m : ℕ} (h : j < m) (s : CoverHistory I Ω m) (i : I j) :
    Finset α := (F j).optionalEdge i (coverHistoryChoice h s i)

theorem coveringSelectedEdge_last (m : ℕ) (s : CoverHistory I Ω (m + 1)) (i : I m) :
    coveringSelectedEdge F (Nat.lt_succ_self m) s i = (F m).optionalEdge i (s.2 i) := by
  simp only [coveringSelectedEdge, coverHistoryChoice_last]

theorem coveringSelectedEdge_succ {j m : ℕ} (h : j < m)
    (s : CoverHistory I Ω (m + 1)) (i : I j) :
    coveringSelectedEdge F (Nat.lt_succ_of_lt h) s i =
      coveringSelectedEdge F h s.1 i := by
  simp only [coveringSelectedEdge, coverHistoryChoice_succ h]

theorem coveringSelectedEdge_prefix {i j m : ℕ} (hij : i < j) (hjm : j ≤ m)
    (s : CoverHistory I Ω m) (a : I i) :
    coveringSelectedEdge F hij (coverHistoryPrefix hjm s) a =
      coveringSelectedEdge F (hij.trans_le hjm) s a := by
  simp only [coveringSelectedEdge, coverHistoryChoice, coverHistoryPrefix_comp]

theorem coveringCovered_mem_iff (m : ℕ) (s : CoverHistory I Ω m) (a : α) :
    a ∈ coveringCovered F m s ↔
      ∃ (j : ℕ) (h : j < m) (i : I j), a ∈ coveringSelectedEdge F h s i := by
  induction m with
  | zero =>
    simp only [coveringCovered, Finset.notMem_empty]
    constructor
    · exact False.elim
    · rintro ⟨j, hj, _, _⟩
      exact (Nat.not_lt_zero j) hj
  | succ m ih =>
    change a ∈ coveringCovered F m s.1 ∪ _ ↔ _
    rw [Finset.mem_union, ih s.1]
    constructor
    · rintro (⟨j, hj, i, hai⟩ | ha)
      · refine ⟨j, Nat.lt_succ_of_lt hj, i, ?_⟩
        simpa only [coveringSelectedEdge_succ F hj] using hai
      · obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp ha
        refine ⟨m, Nat.lt_succ_self m, i, ?_⟩
        simpa only [coveringSelectedEdge_last] using hai
    · rintro ⟨j, hj, i, hai⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hjm | rfl
      · left
        refine ⟨j, hjm, i, ?_⟩
        simpa only [coveringSelectedEdge_succ F hjm] using hai
      · right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ i, ?_⟩
        simpa only [coveringSelectedEdge_last] using hai

theorem coveringRemaining_mem_iff (V : Finset α) (m : ℕ)
    (s : CoverHistory I Ω m) (a : α) :
    a ∈ coveringRemaining F V m s ↔
      a ∈ V ∧ ∀ (j : ℕ) (h : j < m) (i : I j), a ∉ coveringSelectedEdge F h s i := by
  rw [coveringRemaining_eq_sdiff, Finset.mem_sdiff, coveringCovered_mem_iff]
  simp only [not_exists]

theorem coveringHistoryMass_succ_pos (V : Finset α) (δ : ℝ) (j : ℕ)
    (hτ : ∀ k < j + 1, coveringThreshold δ (k + 1) < 1)
    (s : CoverHistory I Ω (j + 1)) (hs : 0 < coveringHistoryMass F V δ (j + 1) s) :
    0 < coveringHistoryMass F V δ j s.1 ∧
      ∀ i, 0 < (F j).reweightedMass (coveringSurvival F j) (coveringRemaining F V j s.1)
        (coveringThreshold δ (j + 1)) i (s.2 i) := by
  have hnon i : 0 ≤ (F j).reweightedMass (coveringSurvival F j)
      (coveringRemaining F V j s.1) (coveringThreshold δ (j + 1)) i (s.2 i) :=
    (F j).reweightedMass_nonneg (fun a _ => coveringSurvival_pos F j a) _
      (hτ j (Nat.lt_succ_self j)) i (s.2 i)
  change 0 < coveringHistoryMass F V δ j s.1 * ∏ i, _ at hs
  have hprev := pos_of_mul_pos_left hs (Finset.prod_nonneg (fun i _ => hnon i))
  have hprod := pos_of_mul_pos_right hs hprev.le
  refine ⟨hprev, fun i => ?_⟩
  exact lt_of_le_of_ne (hnon i) fun hzero =>
    hprod.ne' (Finset.prod_eq_zero (Finset.mem_univ i) hzero.symm)

theorem coveringHistoryMass_prefix_pos (V : Finset α) (δ : ℝ) {j m : ℕ}
    (h : j ≤ m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1)
    (s : CoverHistory I Ω m) (hs : 0 < coveringHistoryMass F V δ m s) :
    0 < coveringHistoryMass F V δ j (coverHistoryPrefix h s) := by
  induction h with
  | refl => simpa only [coverHistoryPrefix_self] using hs
  | @step m h ih =>
    rw [coverHistoryPrefix_succ h]
    exact ih (fun k hk => hτ k (Nat.lt_succ_of_lt hk)) s.1
      (coveringHistoryMass_succ_pos F V δ m hτ s hs).1

theorem coveringSelectedEdge_support (V : Finset α) (δ : ℝ) {j m : ℕ}
    (h : j < m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1)
    (s : CoverHistory I Ω m) (hs : 0 < coveringHistoryMass F V δ m s) (i : I j) :
    coveringSelectedEdge F h s i = ∅ ∨
      ∃ ω, 0 < (F j).mass i ω ∧ coveringSelectedEdge F h s i = (F j).edge i ω := by
  let t := coverHistoryPrefix (Nat.succ_le_of_lt h) s
  have ht : 0 < coveringHistoryMass F V δ (j + 1) t :=
    coveringHistoryMass_prefix_pos F V δ (Nat.succ_le_of_lt h) hτ s hs
  have hτ' k (hk : k < j + 1) := hτ k (hk.trans_le (Nat.succ_le_of_lt h))
  have hi := (coveringHistoryMass_succ_pos F V δ j hτ' t ht).2 i
  rcases (F j).reweightedMass_pos_support (fun a _ => coveringSurvival_pos F j a)
      (coveringRemaining F V j t.1) (hτ j h) i (t.2 i) hi with hempty | ⟨ω, hω, heq, _⟩
  · exact Or.inl hempty
  · exact Or.inr ⟨ω, hω, heq⟩

end

end Erdos4b.FGKMT
