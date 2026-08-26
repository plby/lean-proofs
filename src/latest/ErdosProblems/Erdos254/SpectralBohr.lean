/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.AtomicBohr
import ErdosProblems.Erdos254.BohrReturns

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- Uniformly vanishing nonnegative interval averages leave arbitrarily long
intervals on which every individual value is small. -/
lemma thick_of_uniform_small_averages (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (havg : ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop, ∀ m : ℕ,
      (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), f (m + k) < ε)
    {δ : ℝ} (hδ : 0 < δ) : IsThick {n | f n < δ} := by
  classical
  intro L
  let η : ℝ := δ / (L + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN⟩ := (havg η hη).exists
  have hNp : (0 : ℝ) < N + 1 := by positivity
  have hsum (k : ℕ) : ∑ m ∈ Finset.range (N + 1), f (m + k) < (N + 1 : ℝ) * η := by
    simpa only [Nat.add_comm] using (inv_mul_lt_iff₀ hNp).mp (hN k)
  let g : ℕ → ℝ := fun m ↦ ∑ k ∈ Finset.range (L + 1), f (m + k)
  have htotal : ∑ m ∈ Finset.range (N + 1), g m < (N + 1 : ℝ) * δ := by
    calc
      _ = ∑ k ∈ Finset.range (L + 1), ∑ m ∈ Finset.range (N + 1), f (m + k) := by
        exact Finset.sum_comm
      _ < ∑ _k ∈ Finset.range (L + 1), (N + 1 : ℝ) * η :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
          (fun k _ ↦ hsum k)
      _ = (N + 1 : ℝ) * δ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
          Nat.cast_one, η]
        field_simp
  have hex : ∃ m ∈ Finset.range (N + 1), g m < δ := by
    by_contra! h
    have hh := Finset.sum_le_sum (fun m hm ↦ h m hm)
    have hle : (N + 1 : ℝ) * δ ≤ ∑ m ∈ Finset.range (N + 1), g m := by
      simpa using hh
    exact (not_lt_of_ge hle) htotal
  obtain ⟨m, _, hm⟩ := hex
  refine ⟨m, fun k hk ↦ ?_⟩
  exact (Finset.single_le_sum (fun j _ ↦ hf (m + j))
    (Finset.mem_range.mpr (by omega : k < L + 1))).trans_lt hm

lemma thick_small_circleCoeff (μ : Measure Circle) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {ε : ℝ} (hε : 0 < ε) :
    IsThick {n | ‖circleCoeff μ n‖ < ε} := by
  have h := thick_of_uniform_small_averages (fun n ↦ ‖circleCoeff μ n‖ ^ 2)
    (fun n ↦ sq_nonneg _) (fun δ hδ ↦ uniform_wiener μ hδ) (sq_pos_of_pos hε)
  intro L
  obtain ⟨m, hm⟩ := h L
  refine ⟨m, fun k hk ↦ ?_⟩
  have hsq := hm k hk
  change ‖circleCoeff μ (m + k)‖ ^ 2 < ε ^ 2 at hsq
  change ‖circleCoeff μ (m + k)‖ < ε
  nlinarith [norm_nonneg (circleCoeff μ (m + k))]

/-- The spectral form of Følner's Bohr argument: a finite circle measure with
a positive atom at `1` has a piecewise Bohr set of nonzero Fourier coefficients. -/
theorem spectral_piecewiseBohr (μ : Measure Circle) [IsFiniteMeasure μ]
    (ha : 0 < μ.real {1}) : ContainsPiecewiseBohr {n | circleCoeff μ n ≠ 0} := by
  obtain ⟨d, θ, U, hU, hU0, hUpos⟩ := exists_bohr_atomic_lower μ ha
  let J : Set ℕ := {n | ‖circleCoeff (circleContinuousPart μ) n‖ < μ.real {1} / 4}
  have hJ : IsThick J := thick_small_circleCoeff (circleContinuousPart μ) (by positivity)
  refine ⟨d, θ, U, J, hU, hJ, thick_meets_bohr_zero θ hU hU0 hJ, ?_⟩
  intro n hn hphase hzero
  have hatom := hUpos n hphase
  have hsum : circleCoeff (circleAtomicPart μ) n + circleCoeff (circleContinuousPart μ) n = 0 := by
    rw [← circleCoeff_add, circle_atomic_add_continuous, hzero]
  have hre := congrArg Complex.re hsum
  have hb := Complex.abs_re_le_norm (circleCoeff (circleContinuousPart μ) n)
  have hl := neg_abs_le (circleCoeff (circleContinuousPart μ) n).re
  change ‖circleCoeff (circleContinuousPart μ) n‖ < μ.real {1} / 4 at hn
  simp only [Complex.add_re, Complex.zero_re] at hre
  linarith

end Erdos254
