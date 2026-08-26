/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Partitioning distinct root counts with exact endpoint corrections.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.IntervalMoments
import ErdosProblems.Erdos521.SignGridExpectation

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem intervalRootCount_split (ε : ℕ → ℝ) (n : ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    intervalRootCount ε n a c + intervalRootCount ε n b b =
      intervalRootCount ε n a b + intervalRootCount ε n b c := by
  classical
  let A := (realRoots ε n).filter (fun x ↦ x ∈ Set.Icc a b)
  let B := (realRoots ε n).filter (fun x ↦ x ∈ Set.Icc b c)
  have hunion : A ∪ B = (realRoots ε n).filter (fun x ↦ x ∈ Set.Icc a c) := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Set.mem_Icc]
    constructor
    · rintro (⟨hx, hxa, hxb⟩ | ⟨hx, hxb, hxc⟩)
      · exact ⟨hx, hxa, hxb.trans hbc⟩
      · exact ⟨hx, hab.trans hxb, hxc⟩
    · rintro ⟨hx, hxa, hxc⟩
      rcases le_total x b with h | h
      · exact Or.inl ⟨hx, hxa, h⟩
      · exact Or.inr ⟨hx, h, hxc⟩
  have hinter : A ∩ B = (realRoots ε n).filter (fun x ↦ x ∈ Set.Icc b b) := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_filter, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hx, _, hxb⟩, ⟨_, hbx, _⟩⟩
      exact ⟨hx, hbx, hxb⟩
    · rintro ⟨hx, hbx, hxb⟩
      exact ⟨⟨hx, hab.trans hbx, hxb⟩, ⟨hx, hbx, hxb.trans hbc⟩⟩
  have h := Finset.card_union_add_card_inter A B
  rw [hunion, hinter] at h
  exact h

theorem intervalRootCount_grid_identity (ε : ℕ → ℝ) (n : ℕ) (g : ℕ → ℝ) (hg : Monotone g) (N : ℕ) :
    (∑ i ∈ Finset.range N, intervalRootCount ε n (g i) (g (i + 1))) + intervalRootCount ε n (g 0) (g 0) =
      intervalRootCount ε n (g 0) (g N) + ∑ i ∈ Finset.range N, intervalRootCount ε n (g i) (g i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := intervalRootCount_split ε n (hg (Nat.zero_le N)) (hg (Nat.le_succ N))
    simp only [Finset.sum_range_succ, Nat.succ_eq_add_one] at h ⊢
    omega

theorem intervalRootCount_singleton (ε : ℕ → ℝ) (n : ℕ) (hε : ε 0 ≠ 0) (x : ℝ) :
    intervalRootCount ε n x x = if powerSum ε (n + 1) x = 0 then 1 else 0 := by
  classical
  simp only [intervalRootCount, Set.Icc_self, Set.mem_singleton_iff,
    Finset.filter_eq', mem_realRoots ε n hε x]
  split <;> simp

theorem integral_intervalRootCount_singleton (n : ℕ) (x : ℝ) :
    (∫ ε, (intervalRootCount ε n x x : ℝ) ∂sequenceLaw) =
      sequenceLaw.real {ε | powerSum ε (n + 1) x = 0} := by
  have hE : MeasurableSet {ε : ℕ → ℝ | powerSum ε (n + 1) x = 0} :=
    measurableSet_eq_fun (measurable_powerSum _ x) measurable_const
  rw [← integral_indicator_one hE]
  apply integral_congr_ae
  filter_upwards [ae_sequence_signs] with ε hε
  have hε₀ : ε 0 ≠ 0 := by rcases hε 0 with h | h <;> simp [h]
  rw [intervalRootCount_singleton ε n hε₀ x]
  by_cases h : powerSum ε (n + 1) x = 0 <;> simp [h]

end Erdos521
