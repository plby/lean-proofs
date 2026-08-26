/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite-set decompositions of the distinct interior roots.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignSymmetry

namespace Erdos521

theorem positiveRootCount_le_decomposition (ε : ℕ → ℝ) (n : ℕ) (a b : ℝ) :
    intervalRootCount ε n 0 1 ≤ smallRootCount ε n a +
      intervalRootCount ε n a b + intervalRootCount ε n b 1 := by
  classical
  let S := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc (0 : ℝ) 1
  let F₀ := (realRoots ε n).filter fun x ↦ |x| ≤ a
  let F₁ := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc a b
  let F₂ := (realRoots ε n).filter fun x ↦ x ∈ Set.Icc b 1
  have hsub : S ⊆ F₀ ∪ (F₁ ∪ F₂) := by
    intro x hx
    obtain ⟨hxroot, hxlo, hxhi⟩ := Finset.mem_filter.mp hx
    by_cases hxa : x ≤ a
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hxroot, by simpa only [abs_of_nonneg hxlo] using hxa⟩))
    · apply Finset.mem_union.mpr
      apply Or.inr
      by_cases hxb : x ≤ b
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨hxroot, (lt_of_not_ge hxa).le, hxb⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨hxroot, (lt_of_not_ge hxb).le, hxhi⟩))
  have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (add_le_add le_rfl (Finset.card_union_le _ _)))
  simpa only [S, F₀, F₁, F₂, intervalRootCount, smallRootCount, add_assoc] using hcard

theorem interiorRootCount_eq_positive_add_alternate (ε : ℕ → ℝ) (n : ℕ) (hε : ε 0 ≠ 0) :
    interiorRootCount ε n = intervalRootCount ε n 0 1 +
      intervalRootCount (alternateSigns ε) n 0 1 := by
  classical
  rw [intervalRootCount_alternateSigns ε n hε, neg_zero]
  let F := realRoots ε n
  let P := F.filter fun x ↦ x ∈ Set.Icc (0 : ℝ) 1
  let M := F.filter fun x ↦ x ∈ Set.Icc (-1 : ℝ) 0
  have hzero : (0 : ℝ) ∉ F := by
    intro h
    have hp := (mem_realRoots ε n hε 0).mp h
    rw [← polynomial_eval, polynomial_eval_zero] at hp
    exact hε hp
  have hdisjoint : Disjoint P M := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxroot, hxlo, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, _, hxhi⟩ := Finset.mem_filter.mp hy
    have hx₀ : x = 0 := le_antisymm hxhi hxlo
    exact hzero (hx₀ ▸ hxroot)
  have hunion : F.filter (fun x ↦ x ∈ Set.Icc (-1 : ℝ) 1) = P ∪ M := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, P, M]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      rcases le_total 0 x with h | h
      · exact Or.inl ⟨hx, h, hhi⟩
      · exact Or.inr ⟨hx, hlo, h⟩
    · rintro (⟨hx, hlo, hhi⟩ | ⟨hx, hlo, hhi⟩)
      · exact ⟨hx, by linarith, hhi⟩
      · exact ⟨hx, hlo, by linarith⟩
  exact (congrArg Finset.card hunion).trans (Finset.card_union_of_disjoint hdisjoint)

theorem positiveRootCount_comparison (ε : ℕ → ℝ) (n m : ℕ) {a b K E L : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hbulk : |(intervalRootCount ε m a b : ℝ) - (intervalRootCount ε n a b : ℝ)| ≤ L)
    (hnsmall : (smallRootCount ε n a : ℝ) ≤ K)
    (hmsmall : (smallRootCount ε m a : ℝ) ≤ K)
    (hnend : (intervalRootCount ε n b 1 : ℝ) ≤ E)
    (hmend : (intervalRootCount ε m b 1 : ℝ) ≤ E) :
    |(intervalRootCount ε m 0 1 : ℝ) - (intervalRootCount ε n 0 1 : ℝ)| ≤ L + K + E := by
  have hnlow : (intervalRootCount ε n a b : ℝ) ≤ (intervalRootCount ε n 0 1 : ℝ) := by
    exact_mod_cast intervalRootCount_mono ε n ha hb
  have hmlow : (intervalRootCount ε m a b : ℝ) ≤ (intervalRootCount ε m 0 1 : ℝ) := by
    exact_mod_cast intervalRootCount_mono ε m ha hb
  have hnhigh : (intervalRootCount ε n 0 1 : ℝ) ≤ (smallRootCount ε n a : ℝ) +
      (intervalRootCount ε n a b : ℝ) + (intervalRootCount ε n b 1 : ℝ) := by
    exact_mod_cast positiveRootCount_le_decomposition ε n a b
  have hmhigh : (intervalRootCount ε m 0 1 : ℝ) ≤ (smallRootCount ε m a : ℝ) +
      (intervalRootCount ε m a b : ℝ) + (intervalRootCount ε m b 1 : ℝ) := by
    exact_mod_cast positiveRootCount_le_decomposition ε m a b
  have hdiff := abs_le.mp hbulk
  exact abs_le.mpr ⟨by linarith [hdiff.1], by linarith [hdiff.2]⟩

end Erdos521
