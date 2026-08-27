import Arxiv.Arxiv2411_18291.FiniteHistoryConcentration

/-! # Simultaneous bounded sums for finite random choices -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem exists_finite_choices_below_double_budget {A S : Type*} [Fintype A] [Finite S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (start : S) (p : ℕ → PMF S) (f : A → S → ℝ) (t : ℕ) {μ : ℝ}
    (hf : ∀ a s, 0 ≤ f a s ∧ f a s ≤ 1)
    (hμ : ∀ a, (∑ i ∈ range t, ∫ s, f a s ∂(p i).toMeasure) ≤ μ)
    (hfailure : Fintype.card A * Real.exp (-(μ / 3)) < 1) :
    ∃ z : Fin t → S, (∀ i : Fin t, z i ∈ (p (i : ℕ)).support) ∧
      ∀ a, (∑ i, f a (z i)) < 2 * μ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let step : (i : ℕ) → FiniteHistoryProcess.History S i → PMF S := fun i _ => p i
  let P := FiniteHistoryProcess.probability start step
  have htail (a : A) :
      P.real {ω | 2 * μ ≤ ∑ i ∈ range t, f a (ω (i + 1))} ≤
        Real.exp (-(μ / 3)) :=
    FiniteHistoryProcess.indicator_double_tail start step (fun _ => f a) t
      (fun i => ∫ s, f a s ∂(p i).toMeasure) (fun _ _ => hf a)
      (fun _ _ _ => le_rfl) (hμ a)
  have hbad : P.real {ω | ¬ ∀ a, (∑ i ∈ range t, f a (ω (i + 1))) < 2 * μ} < 1 := by
    have heq : {ω : ℕ → S | ¬ ∀ a, (∑ i ∈ range t, f a (ω (i + 1))) < 2 * μ} =
        ⋃ a, {ω | 2 * μ ≤ ∑ i ∈ range t, f a (ω (i + 1))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, not_forall, not_lt, Set.mem_iUnion]
    rw [heq]
    calc
      _ ≤ ∑ a, P.real {ω | 2 * μ ≤ ∑ i ∈ range t, f a (ω (i + 1))} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _a : A, Real.exp (-(μ / 3)) := sum_le_sum fun a _ => htail a
      _ = Fintype.card A * Real.exp (-(μ / 3)) := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
      _ < 1 := hfailure
  obtain ⟨ω, hs, hg⟩ := FiniteHistoryProcess.exists_supported_path start step
    (fun ω => ∀ a, (∑ i ∈ range t, f a (ω (i + 1))) < 2 * μ) hbad
  refine ⟨fun i => ω (i + 1), fun i => hs i, ?_⟩
  intro a
  rw [Fin.sum_univ_eq_sum_range (fun i => f a (ω (i + 1)))]
  exact hg a

end Arxiv2411_18291
