import ErdosProblems.Erdos4.FGKMTSelectionError

/-!
# One actual finite covering round

Conditioned on the current survivor set, the reweighted edge choices
are independent. Their union is removed. The resulting survivor law
has an exact product formula, ready for the quantitative induction.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def afterRound (W : Finset V) (choice : I → Finset V) : Finset V :=
  W \ Finset.univ.biUnion choice

theorem subset_afterRound (W T : Finset V) (choice : I → Finset V) :
    T ⊆ afterRound W choice ↔ T ⊆ W ∧ ∀ i, Disjoint T (choice i) := by
  simp only [afterRound, Finset.subset_sdiff, Finset.disjoint_biUnion_right,
    Finset.mem_univ, forall_const]

noncomputable def roundLaw (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (t : ℝ) : FiniteLaw (Finset V) :=
  ν.bind (fun W => (FiniteLaw.independent (fun i => selectLaw (μ i) p hp t W)).map (afterRound W))

theorem round_survival (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (t : ℝ) (T : Finset V) :
    survival (roundLaw ν μ p hp t) T = ν.mean (fun W => if T ⊆ W then
      ∏ i, (1 - (selectLaw (μ i) p hp t W).prob (fun e => ¬Disjoint T e)) else 0) := by
  classical
  unfold survival roundLaw
  rw [FiniteLaw.prob_bind]
  apply ν.mean_congr
  intro W
  rw [FiniteLaw.prob_map]
  let choices := FiniteLaw.independent (fun i => selectLaw (μ i) p hp t W)
  by_cases hT : T ⊆ W
  · rw [if_pos hT]
    have heq : choices.prob (fun choice => T ⊆ afterRound W choice) =
        choices.prob (fun choice => ∀ i, Disjoint T (choice i)) := by
      apply le_antisymm
      · exact choices.prob_mono (fun choice h => ((subset_afterRound W T choice).mp h).2)
      · exact choices.prob_mono (fun choice h => (subset_afterRound W T choice).mpr ⟨hT, h⟩)
    rw [heq, FiniteLaw.independent_prob_all]
    apply Finset.prod_congr rfl
    intro i _hi
    have hh := (selectLaw (μ i) p hp t W).prob_compl (fun e => ¬Disjoint T e)
    simpa only [not_not] using hh
  · rw [if_neg hT]
    have hnot : ∀ choice : I → Finset V, ¬T ⊆ afterRound W choice :=
      fun choice h => hT ((subset_afterRound W T choice).mp h).1
    change choices.prob (fun choice => T ⊆ afterRound W choice) = 0
    unfold FiniteLaw.prob
    simp only [if_neg (hnot _), Finset.sum_const_zero]

end Erdos4.FGKMT
