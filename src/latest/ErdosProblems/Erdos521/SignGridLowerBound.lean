/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Every sign change accounts for a different root, without a simplicity assumption.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignGridProbability

namespace Erdos521

theorem gridSignChanges_le_intervalRootCount (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0)
    (g : ℕ → ℝ) (hg : Monotone g) (N : ℕ) :
    gridSignChanges ε n g N ≤ intervalRootCount ε n (g 0) (g N) := by
  classical
  let F := (Finset.range N).filter fun i ↦ (polynomial ε n).eval (g i) *
    (polynomial ε n).eval (g (i + 1)) < 0
  let G := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc (g 0) (g N)
  have hcard : F.card = gridSignChanges ε n g N := by
    simp [F, gridSignChanges, signChange]
  have hpair : ∀ i : F, ∃ r : G, g i < (r : ℝ) ∧ (r : ℝ) < g ((i : ℕ) + 1) := by
    intro i
    obtain ⟨hiN, hi⟩ := Finset.mem_filter.mp i.2
    have hiN' : (i : ℕ) < N := Finset.mem_range.mp hiN
    obtain ⟨r, hr, hrzero⟩ := polynomial_exists_root_of_mul_nonpos (polynomial ε n)
      (hg (Nat.le_succ (i : ℕ))) hi.le
    have hends := mul_ne_zero_iff.mp hi.ne
    have hrlo : g i < r := by
      apply lt_of_le_of_ne hr.1
      intro heq
      exact hends.1 (heq.symm ▸ hrzero)
    have hrhi : r < g ((i : ℕ) + 1) := by
      apply lt_of_le_of_ne hr.2
      intro heq
      exact hends.2 (heq ▸ hrzero)
    have hrroot : r ∈ realRoots ε n := (mem_realRoots ε n hε₀ r).mpr
      ((polynomial_eval ε n r).symm.trans hrzero)
    have hrG : r ∈ G := Finset.mem_filter.mpr ⟨hrroot,
      (hg (Nat.zero_le (i : ℕ))).trans hr.1, hr.2.trans (hg (by omega))⟩
    exact ⟨⟨r, hrG⟩, hrlo, hrhi⟩
  choose f hf using hpair
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have heq : (f i : ℝ) = (f j : ℝ) := congrArg Subtype.val hij
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt : (f i : ℝ) < (f j : ℝ) :=
        ((hf i).2.trans_le (hg (show (i : ℕ) + 1 ≤ j by omega))).trans (hf j).1
      exact hlt.ne heq
    · have hlt : (f j : ℝ) < (f i : ℝ) :=
        ((hf j).2.trans_le (hg (show (j : ℕ) + 1 ≤ i by omega))).trans (hf i).1
      exact hlt.ne heq.symm
  have h := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, hcard, G, intervalRootCount] using h

end Erdos521
