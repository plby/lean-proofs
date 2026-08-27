import Arxiv.Arxiv2411_18291.CriticalWindowAttempt
import Arxiv.Arxiv2411_18291.CriticalWindowEntrance

/-!
# Concentration from drift inside a critical interval

A crossing before the good events fail enters the interval at some start
time. Its entrance overshoot costs one increment bound. The union bound
over possible starts gives the explicit finite-horizon factor `n`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ}
variable {A : ℕ → Ω → ℝ} {G : ℕ → Set Ω} {l u b v : ℝ} {n : ℕ}

theorem critical_window_upper_bound (hb : 0 < b) (hv : 0 ≤ v) (hgap : l + b < u)
    (hA : ∀ i ≤ n, StronglyMeasurable[ℱ i] (A i))
    (h0 : ∀ᵐ ω ∂P, A 0 ω < l)
    (hAb : ∀ i < n, ∀ᵐ ω ∂P, |A (i + 1) ω - A i ω| ≤ b)
    (hG : ∀ i < n, MeasurableSet[ℱ i] (G i))
    (htrend : ∀ i < n, ∀ᵐ ω ∂P, ω ∈ G i → l ≤ A i ω →
      P[fun ω => A (i + 1) ω - A i ω | ℱ i] ω ≤ 0) :
    P.real {ω | ∃ j ≤ n, u ≤ A j ω ∧ (∀ k < j, ω ∈ G k) ∧
      (∑ i ∈ range j, Var[fun ω => A (i + 1) ω - A i ω; P | ℱ i] ω) ≤ v} ≤
      n * Real.exp (-((u - l - b) ^ 2 / (2 * (v + (u - l - b) * b)))) := by
  let a := u - l - b
  have ha : 0 < a := by dsimp [a]; linarith only [hgap]
  have hstep : ∀ i, ∀ᵐ ω ∂P, i < n → |A (i + 1) ω - A i ω| ≤ b := by
    intro i
    by_cases hi : i < n
    · exact (hAb i hi).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => (hi h).elim
  have hsub : {ω | ∃ j ≤ n, u ≤ A j ω ∧ (∀ k < j, ω ∈ G k) ∧
      (∑ i ∈ range j, Var[fun ω => A (i + 1) ω - A i ω; P | ℱ i] ω) ≤ v} ≤ᵐ[P]
      ⋃ s ∈ range n, windowAttempt ℱ P A G l a v s n := by
    filter_upwards [h0, ae_all_iff.mpr hstep] with ω h0 hstep
    rintro ⟨j, hj, hcross, hgood, hvar⟩
    obtain ⟨s, _, hsj, hs, hwindow⟩ := exists_critical_window_start (A := fun i => A i ω)
      hb.le h0 hgap hcross (fun i hi => (le_abs_self _).trans (hstep i (hi.trans_le hj)))
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨mem_range.mpr (hsj.trans_le hj), ?_⟩⟩
    refine ⟨j, hj, hsj.le, ?_, hgood, hwindow, hvar⟩
    dsimp only [a]
    linarith only [hs, hcross]
  calc
    _ ≤ P.real (⋃ s ∈ range n, windowAttempt ℱ P A G l a v s n) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ s ∈ range n, P.real (windowAttempt ℱ P A G l a v s n) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ range n, Real.exp (-(a ^ 2 / (2 * (v + a * b)))) :=
      sum_le_sum fun s _ => critical_window_attempt_bound ha hb hv hA hAb hG htrend s
    _ = _ := by simp [a, nsmul_eq_mul]

end Arxiv2411_18291
