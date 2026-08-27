import Arxiv.Arxiv2411_18291.FiniteHistoryProcess

/-!
# Concentration for the constructed finite-state process

Uniform bounds on the expectations of each transition give an almost-sure
bound on the sum of conditional means along the trajectory. The adaptive
concentration theorem applies directly; no independent domination is used.
-/

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] in
theorem stronglyMeasurable_coordinate [Finite S] (n : ℕ) (f : S → ℝ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => S) n] (fun ω => f (ω n)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let g : History S n → ℝ := fun h => f (h ⟨n, mem_Iic.mpr le_rfl⟩)
  change StronglyMeasurable[MeasurableSpace.comap (frestrictLe (π := fun _ => S) n) inferInstance]
    (g ∘ frestrictLe (π := fun _ => S) n)
  exact ((measurable_of_finite g).comp (comap_measurable _)).stronglyMeasurable

/-- Tail bound from a deterministic budget on all transition expectations. -/
theorem upper_tail_ge (start : S) (p : (n : ℕ) → History S n → PMF S)
    (f : ℕ → S → ℝ) (t : ℕ) (a : ℕ → ℝ) {C c μ : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ i < t, ∀ s, 0 ≤ f i s ∧ f i s ≤ C)
    (ha : ∀ i < t, ∀ h, (∫ s, f i s ∂(p i h).toMeasure) ≤ a i)
    (hμ : (∑ i ∈ range t, a i) ≤ μ) :
    (probability start p).real {ω | (1 + c) * μ ≤ ∑ i ∈ range t, f i (ω (i + 1))} ≤
      Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) := by
  apply adaptive_nonnegative_upper_tail_ge (ℱ := Filtration.piLE) hC hc
  · intro i _
    exact stronglyMeasurable_coordinate (i + 1) (f i)
  · intro i hi
    exact ae_of_all _ fun ω => hf i hi (ω (i + 1))
  · have hall : ∀ᵐ ω ∂probability start p, ∀ i,
        (probability start p)[(fun x => f i (x (i + 1))) | Filtration.piLE i] ω =
          ∫ s, f i s ∂(p i (frestrictLe i ω)).toMeasure :=
      ae_all_iff.mpr fun i => condExp_next start p i (f i)
    filter_upwards [hall] with ω hω
    calc
      _ ≤ ∑ i ∈ range t, a i := by
        apply sum_le_sum
        intro i hi
        rw [hω i]
        exact ha i (mem_range.mp hi) _
      _ ≤ _ := hμ

/-- For indicators, reaching twice the mean budget has exponentially small probability. -/
theorem indicator_double_tail (start : S) (p : (n : ℕ) → History S n → PMF S)
    (f : ℕ → S → ℝ) (t : ℕ) (a : ℕ → ℝ) {μ : ℝ}
    (hf : ∀ i < t, ∀ s, 0 ≤ f i s ∧ f i s ≤ 1)
    (ha : ∀ i < t, ∀ h, (∫ s, f i s ∂(p i h).toMeasure) ≤ a i)
    (hμ : (∑ i ∈ range t, a i) ≤ μ) :
    (probability start p).real {ω | 2 * μ ≤ ∑ i ∈ range t, f i (ω (i + 1))} ≤
      Real.exp (-(μ / 3)) := by
  simpa only [one_add_one_eq_two, one_pow, mul_one, show (2 : ℝ) + 1 = 3 by norm_num] using
    upper_tail_ge start p f t a (C := 1) (c := 1) (by norm_num) (by norm_num) hf ha hμ

end Arxiv2411_18291.FiniteHistoryProcess
