/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact root counts on a finite grid with at most one simple root in each cell.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignChanges

namespace Erdos521

open scoped BigOperators

theorem intervalRootCount_add (ε : ℕ → ℝ) (n : ℕ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hb : (polynomial ε n).eval b ≠ 0) :
    intervalRootCount ε n a c = intervalRootCount ε n a b + intervalRootCount ε n b c := by
  classical
  let F := realRoots ε n
  let L := F.filter fun x ↦ x ∈ Set.Icc a b
  let R := F.filter fun x ↦ x ∈ Set.Icc b c
  have hunion : F.filter (fun x ↦ x ∈ Set.Icc a c) = L ∪ R := by
    ext x
    simp only [L, R, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      rcases le_total x b with h | h
      · exact Or.inl ⟨hx, hlo, h⟩
      · exact Or.inr ⟨hx, h, hhi⟩
    · rintro (⟨hx, hlo, hhi⟩ | ⟨hx, hlo, hhi⟩)
      · exact ⟨hx, hlo, hhi.trans hbc⟩
      · exact ⟨hx, hab.trans hlo, hhi⟩
  have hdisjoint : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxroot, _, hxhi⟩ := Finset.mem_filter.mp hx
    have hxlo := (Finset.mem_filter.mp hy).2.1
    have hxb : x = b := le_antisymm hxhi hxlo
    have hzero : (polynomial ε n).eval x = 0 :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxroot)
    exact hb (hxb ▸ hzero)
  exact (congrArg Finset.card hunion).trans (Finset.card_union_of_disjoint hdisjoint)

theorem intervalRootCount_self (ε : ℕ → ℝ) (n : ℕ) {a : ℝ}
    (ha : (polynomial ε n).eval a ≠ 0) : intervalRootCount ε n a a = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxroot, hxlo, hxhi⟩ := Finset.mem_filter.mp hx
  have hxa : x = a := le_antisymm hxhi hxlo
  have hzero : (polynomial ε n).eval x = 0 :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxroot)
  exact ha (hxa ▸ hzero)

theorem intervalRootCount_sum_grid (ε : ℕ → ℝ) (n : ℕ) (g : ℕ → ℝ) (hg : Monotone g)
    (N : ℕ) (hgrid : ∀ i ≤ N, (polynomial ε n).eval (g i) ≠ 0) :
    intervalRootCount ε n (g 0) (g N) =
      ∑ i ∈ Finset.range N, intervalRootCount ε n (g i) (g (i + 1)) := by
  induction N with
  | zero => simpa only [Finset.sum_range_zero] using intervalRootCount_self ε n (hgrid 0 le_rfl)
  | succ N ih =>
    rw [Finset.sum_range_succ, intervalRootCount_add ε n (hg (Nat.zero_le N))
      (hg (Nat.le_succ N)) (hgrid N (Nat.le_succ N))]
    rw [ih (fun i hi ↦ hgrid i (hi.trans (Nat.le_succ N)))]

theorem intervalRootCount_eq_sum_signChanges (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0)
    (g : ℕ → ℝ) (hg : Monotone g) (N : ℕ)
    (hgrid : ∀ i ≤ N, (polynomial ε n).eval (g i) ≠ 0)
    (hcount : ∀ i < N, intervalRootCount ε n (g i) (g (i + 1)) ≤ 1)
    (hsimple : ∀ x ∈ Set.Icc (g 0) (g N), (polynomial ε n).eval x = 0 →
      (polynomial ε n).derivative.eval x ≠ 0) :
    intervalRootCount ε n (g 0) (g N) =
      ∑ i ∈ Finset.range N, signChange ((polynomial ε n).eval (g i)) ((polynomial ε n).eval (g (i + 1))) := by
  rw [intervalRootCount_sum_grid ε n g hg N hgrid]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  apply intervalRootCount_eq_signChange ε n hε₀ (hg (Nat.le_succ i))
    (hgrid i hiN.le) (hgrid (i + 1) (by omega)) (hcount i hiN)
  intro x hx hzero
  exact hsimple x ⟨(hg (Nat.zero_le i)).trans hx.1, hx.2.trans (hg (by omega))⟩ hzero

end Erdos521
