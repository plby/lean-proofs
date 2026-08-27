import ErdosProblems.Erdos4.FGKMTRound

/-! Positive-mass outcomes of the constructed finite laws are actual choices. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω Λ I : Type*} [Fintype Ω] [Fintype Λ] [Fintype I] [DecidableEq I]

theorem bind_support (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Λ) (l : Λ)
    (hl : 0 < (μ.bind ν).weight l) :
    ∃ o, 0 < μ.weight o ∧ 0 < (ν o).weight l := by
  change 0 < ∑ o, μ.weight o * (ν o).weight l at hl
  obtain ⟨o, _ho, hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun o _ho => mul_nonneg (μ.nonneg o) ((ν o).nonneg l))).mp hl
  have hh := (mul_pos_iff.mp hpos).resolve_right
    (fun h => (not_lt_of_ge (μ.nonneg o)) h.1)
  exact ⟨o, hh⟩

theorem map_support (μ : FiniteLaw Ω) (f : Ω → Λ) (l : Λ)
    (hl : 0 < (μ.map f).weight l) : ∃ o, 0 < μ.weight o ∧ f o = l := by
  classical
  obtain ⟨o, ho, hf⟩ := bind_support μ (fun o => dirac (f o)) l hl
  refine ⟨o, ho, ?_⟩
  by_contra hne
  simp only [dirac, if_neg (Ne.symm hne)] at hf
  linarith

theorem independent_support (μ : I → FiniteLaw Ω) (choice : I → Ω)
    (hchoice : 0 < (independent μ).weight choice) :
    ∀ i, 0 < (μ i).weight (choice i) := by
  intro i
  by_contra hi
  have heq : (μ i).weight (choice i) = 0 := le_antisymm (le_of_not_gt hi) ((μ i).nonneg _)
  have hprod : (∏ j, (μ j).weight (choice j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) heq
  change 0 < ∏ j, (μ j).weight (choice j) at hchoice
  rw [hprod] at hchoice
  linarith

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem roundLaw_support (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (hp : ∀ v, 0 < p v)
    (t : ℝ) (W' : Finset V)
    (hW' : 0 < (roundLaw ν μ p hp t).weight W') :
    ∃ W choice, 0 < ν.weight W ∧ W' = afterRound W choice ∧
      ∀ i, choice i ⊆ W ∧ (choice i = ∅ ∨ 0 < (μ i).weight (choice i)) := by
  obtain ⟨W, hW, hchoice⟩ := FiniteLaw.bind_support ν
    (fun W => (FiniteLaw.independent (fun i => selectLaw (μ i) p hp t W)).map (afterRound W))
    W' hW'
  obtain ⟨choice, hc, heq⟩ := FiniteLaw.map_support
    (FiniteLaw.independent (fun i => selectLaw (μ i) p hp t W)) (afterRound W) W' hchoice
  refine ⟨W, choice, hW, heq.symm, ?_⟩
  intro i
  exact selectLaw_support (μ i) p hp t W (choice i)
    (FiniteLaw.independent_support (fun i => selectLaw (μ i) p hp t W) choice hc i)

end Erdos4.FGKMT
