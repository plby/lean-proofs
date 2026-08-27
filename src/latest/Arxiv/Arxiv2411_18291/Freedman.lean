import Arxiv.Arxiv2411_18291.FreedmanFiniteIncrements

/-!
# The paper's martingale and supermartingale concentration bounds

The finite-process theorem requires hypotheses only through its horizon.
Its conditional variance is that of the next process value, exactly as
in the paper. The supermartingale extension uses the repaired centering
argument and retains the printed numerical bound.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {A : ℕ → Ω → ℝ}
variable {a b v : ℝ} {n : ℕ}

theorem freedman_finite_process_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hA : ∀ i ≤ n, StronglyMeasurable[ℱ i] (A i))
    (hAi : ∀ i ≤ n, Integrable (A i) P)
    (hAb : ∀ i < n, ∀ᵐ ω ∂P, |A (i + 1) ω - A i ω| ≤ b)
    (hmean : ∀ i < n, P[A (i + 1) | ℱ i] ≤ᵐ[P] A i) :
    P.real {ω | ∃ j ≤ n, A 0 ω + a ≤ A j ω ∧
      (∑ i ∈ range j, Var[A (i + 1); P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  let X := fun i ω => A (i + 1) ω - A i ω
  have hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i) := by
    intro i hi
    exact (hA (i + 1) (by omega)).sub ((hA i hi.le).mono (ℱ.mono (Nat.le_succ i)))
  have hXmean : ∀ i < n, P[X i | ℱ i] ≤ᵐ[P] 0 := by
    intro i hi
    have hsub := condExp_sub (hAi (i + 1) (by omega)) (hAi i hi.le) (ℱ i)
    rw [condExp_of_stronglyMeasurable (ℱ.le i) (hA i hi.le) (hAi i hi.le)] at hsub
    filter_upwards [hsub, hmean i hi] with ω heq hle
    change P[X i | ℱ i] ω = P[A (i + 1) | ℱ i] ω - A i ω at heq
    change P[X i | ℱ i] ω ≤ 0
    rw [heq]
    exact sub_nonpos.mpr hle
  have hVar : ∀ i, ∀ᵐ ω ∂P, i < n →
      Var[X i; P | ℱ i] ω = Var[A (i + 1); P | ℱ i] ω := by
    intro i
    by_cases hi : i < n
    · exact (condVar_sub_predictable (ℱ.le i) (hAi (i + 1) (by omega))
        (hAi i hi.le) (hA i hi.le)).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => (hi h).elim
  have hsub : {ω | ∃ j ≤ n, A 0 ω + a ≤ A j ω ∧
      (∑ i ∈ range j, Var[A (i + 1); P | ℱ i] ω) ≤ v} ≤ᵐ[P]
      {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
        (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} := by
    filter_upwards [ae_all_iff.mpr hVar] with ω hω
    rintro ⟨j, hj, hs, hv⟩
    refine ⟨j, hj, ?_, ?_⟩
    · have heq : (∑ i ∈ range j, X i ω) = A j ω - A 0 ω :=
        sum_range_sub (fun i => A i ω) j
      rw [heq]
      linarith only [hs]
    · calc
        _ = ∑ i ∈ range j, Var[A (i + 1); P | ℱ i] ω := by
          apply sum_congr rfl
          intro i hi
          exact hω i ((mem_range.mp hi).trans_le hj)
        _ ≤ v := hv
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (freedman_finite_conditionalVariance_bound ha hb hv hX hAb hXmean)

theorem freedman_supermartingale (hA : Supermartingale A ℱ P)
    (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hAb : ∀ i < n, ∀ᵐ ω ∂P, |A (i + 1) ω - A i ω| ≤ b) :
    P.real {ω | ∃ j ≤ n, A 0 ω + a ≤ A j ω ∧
      (∑ i ∈ range j, Var[A (i + 1); P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) :=
  freedman_finite_process_bound ha hb hv (fun i _ => hA.stronglyMeasurable i)
    (fun i _ => hA.integrable i) hAb (fun i _ => hA.condExp_ae_le (Nat.le_succ i))

theorem freedman_martingale (hA : Martingale A ℱ P)
    (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hAb : ∀ i < n, ∀ᵐ ω ∂P, |A (i + 1) ω - A i ω| ≤ b) :
    P.real {ω | ∃ j ≤ n, A 0 ω + a ≤ A j ω ∧
      (∑ i ∈ range j, Var[A (i + 1); P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) :=
  freedman_supermartingale hA.supermartingale ha hb hv hAb

end Arxiv2411_18291
