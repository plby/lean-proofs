import Arxiv.Arxiv2411_18291.CliqueRemovalProcess
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Exact conditional averages for a uniformly selected remaining clique -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem integral_uniform_finset {S : Type*} [Finite S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (s : Finset S) (hs : s.Nonempty) (f : S → ℝ) :
    (∫ a, f a ∂(PMF.uniformOfFinset s hs).toMeasure) = (∑ a ∈ s, f a) / s.card := by
  classical
  let : Fintype S := Fintype.ofFinite S
  rw [PMF.integral_eq_sum]
  calc
    _ = ∑ a ∈ s, ((PMF.uniformOfFinset s hs) a).toReal • f a := by
      symm
      apply sum_subset (subset_univ s)
      intro a _ ha
      simp [PMF.uniformOfFinset_apply, ha]
    _ = ∑ a ∈ s, (s.card : ℝ)⁻¹ * f a := by
      apply sum_congr rfl
      intro a ha
      simp [PMF.uniformOfFinset_apply, ha, smul_eq_mul]
    _ = (s.card : ℝ)⁻¹ * (∑ a ∈ s, f a) := (mul_sum _ _ _).symm
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r n : ℕ}

theorem step_mean (H : Finset (Block V q))
    (h : FiniteHistoryProcess.History (State V q) n) (f : Block V q → ℝ) :
    (∫ a, Option.elim a 0 f ∂(step r H n h).toMeasure) =
      (∑ Q ∈ remainingCliques r H (historyCliques h), f Q) /
        (remainingCliques r H (historyCliques h)).card := by
  classical
  let : MeasurableSpace (Block V q) := ⊤
  by_cases hs : (remainingCliques r H (historyCliques h)).Nonempty
  · have hm : Measurable (chosen : Block V q → State V q) :=
      measurable_of_finite _
    rw [step, dif_pos hs, ← PMF.toMeasure_map _ _ hm,
      integral_map hm.aemeasurable (measurable_of_finite
        (fun a : State V q => Option.elim a 0 f)).aestronglyMeasurable]
    exact integral_uniform_finset _ hs f
  · have heq := not_nonempty_iff_eq_empty.mp hs
    rw [step, dif_neg hs, PMF.toMeasure_pure, integral_dirac]
    simp [heq, aborted]

theorem condExp_chosen_step (H : Finset (Block V q))
    (f : FiniteHistoryProcess.History (State V q) n → Block V q → ℝ) :
    (probability r H)[fun ω => Option.elim (ω (n + 1)) 0 (f (frestrictLe n ω)) |
      Filtration.piLE n] =ᵐ[probability r H] fun ω =>
        (∑ Q ∈ remainingCliques r H (trajectoryCliques ω n), f (frestrictLe n ω) Q) /
          (remainingCliques r H (trajectoryCliques ω n)).card := by
  have hc := FiniteHistoryProcess.condExp_step (aborted V q) (step r H) n
    (fun h a => Option.elim a 0 (f h))
  filter_upwards [hc] with ω hω
  have hs := step_mean (r := r) H (frestrictLe n ω) (f (frestrictLe n ω))
  exact hω.trans (by simpa only [historyCliques_prefix] using hs)

end CliqueRemovalProcess

end Arxiv2411_18291
