import Arxiv.Arxiv2411_18291.CriticalWindowProcess

/-! # Concentration for one attempted crossing of a critical interval -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def windowAttempt (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (A : ℕ → Ω → ℝ)
    (G : ℕ → Set Ω) (l a v : ℝ) (s n : ℕ) : Set Ω :=
  {ω | ∃ j ≤ n, s ≤ j ∧ A s ω + a ≤ A j ω ∧ (∀ k < j, ω ∈ G k) ∧
    (∀ k, s ≤ k → k < j → l ≤ A k ω) ∧
    (∑ i ∈ range j, Var[fun ω => A (i + 1) ω - A i ω; P | ℱ i] ω) ≤ v}

variable {ℱ : Filtration ℕ mΩ} {P : Measure Ω} [IsProbabilityMeasure P]
variable {A : ℕ → Ω → ℝ} {G : ℕ → Set Ω} {l a b v : ℝ} {n : ℕ}

theorem critical_window_attempt_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hA : ∀ i ≤ n, StronglyMeasurable[ℱ i] (A i))
    (hAb : ∀ i < n, ∀ᵐ ω ∂P, |A (i + 1) ω - A i ω| ≤ b)
    (hG : ∀ i < n, MeasurableSet[ℱ i] (G i))
    (htrend : ∀ i < n, ∀ᵐ ω ∂P, ω ∈ G i → l ≤ A i ω →
      P[fun ω => A (i + 1) ω - A i ω | ℱ i] ω ≤ 0) (s : ℕ) :
    P.real (windowAttempt ℱ P A G l a v s n) ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  let X := fun i ω => A (i + 1) ω - A i ω
  let S := fun i => windowActive A G l s i
  have hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i) := by
    intro i hi
    exact (hA (i + 1) (by omega)).sub ((hA i hi.le).mono (ℱ.mono (Nat.le_succ i)))
  have hS : ∀ i < n, MeasurableSet[ℱ i] (S i) := by
    intro i hi
    exact windowActive_measurableSet (fun k hk => hA k (by omega))
      (fun k hk => hG k (by omega))
  have hmean : ∀ i < n, ∀ᵐ ω ∂P, ω ∈ S i → P[X i | ℱ i] ω ≤ 0 := by
    intro i hi
    filter_upwards [htrend i hi] with ω hω
    intro hs
    obtain ⟨hg, hl⟩ := windowActive_current hs
    exact hω hg hl
  have hsub : windowAttempt ℱ P A G l a v s n ⊆
      {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, (S i).indicator (X i) ω ∧
        (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} := by
    rintro ω ⟨j, hj, hsj, hcross, hgood, hwindow, hvar⟩
    refine ⟨j, hj, ?_, hvar⟩
    change a ≤ ∑ i ∈ range j, (windowActive A G l s i).indicator
      (fun ω => A (i + 1) ω - A i ω) ω
    rw [windowActive_sum_eq hsj hgood hwindow]
    linarith only [hcross]
  exact (measureReal_mono hsub).trans
    (freedman_predictable_indicator_bound ha hb hv hX hAb hS hmean)

end Arxiv2411_18291
