import ErdosProblems.Erdos4.FGKMTRoundAccuracy
import ErdosProblems.Erdos4.FGKMTSupport

/-! The actual iterated covering process, starting with all vertices present. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def modelSequence (μ : ℕ → I → FiniteLaw (Finset V)) : ℕ → V → ℝ
  | 0 => fun _ => 1
  | n + 1 => nextModel (μ n) (modelSequence μ n)

theorem modelSequence_pos (μ : ℕ → I → FiniteLaw (Finset V)) :
    ∀ n v, 0 < modelSequence μ n v := by
  intro n
  induction n with
  | zero => intro v; exact zero_lt_one
  | succ n ih => exact nextModel_pos (μ n) (modelSequence μ n) ih

theorem modelSequence_le_one (μ : ℕ → I → FiniteLaw (Finset V)) :
    ∀ n v, modelSequence μ n v ≤ 1 := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    exact (nextModel_le (μ n) (modelSequence μ n) (modelSequence_pos μ n) v).trans (ih v)

noncomputable def survivorProcess (μ : ℕ → I → FiniteLaw (Finset V)) (t : ℕ → ℝ) :
    ℕ → FiniteLaw (Finset V)
  | 0 => FiniteLaw.dirac Finset.univ
  | n + 1 => roundLaw (survivorProcess μ t n) (μ n) (modelSequence μ n)
      (modelSequence_pos μ n) (t n)

theorem initial_accuracy (A : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    SurvivalAccurate (FiniteLaw.dirac (Finset.univ : Finset V)) (fun _ => 1) A ε := by
  intro T _hT
  unfold survival
  rw [FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac]
  simpa [setProduct] using hε

/-- The recursive error budget is a scalar condition; every probability
law in the conclusion is explicitly constructed. -/
theorem survivorProcess_accuracy (μ : ℕ → I → FiniteLaw (Finset V)) (t ε : ℕ → ℝ)
    {m r A : ℕ} {κ δ D : ℝ} (hrA : 2 * r ≤ A)
    (hround : ∀ j < m, RoundBounds (μ j) (modelSequence μ j) r κ δ D)
    (hε : ∀ j ≤ m, 0 ≤ ε j ∧ ε j ≤ 1 / 2)
    (ht : ∀ j < m, 0 < t j ∧ t j ≤ 1 / 2)
    (hstep : ∀ j < m, roundNextError r A κ δ (ε j) (t j) D ≤ ε (j + 1)) :
    SurvivalAccurate (survivorProcess μ t m) (modelSequence μ m) A (ε m) := by
  have haux : ∀ j ≤ m, SurvivalAccurate (survivorProcess μ t j) (modelSequence μ j) A (ε j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact initial_accuracy A (hε 0 hj).1
    | succ j ih =>
      intro hj
      have hjm : j < m := by omega
      have hprev := ih (by omega)
      have hh := round_accuracy (survivorProcess μ t j) (hround j hjm)
        (hε j (by omega)).1 (hε j (by omega)).2 (ht j hjm).1 (ht j hjm).2 hprev hrA
      intro T hT
      exact (hh T hT).trans (hstep j hjm)
  exact haux m le_rfl

end Erdos4.FGKMT
