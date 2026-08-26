import ErdosProblems.Erdos1002.ProbabilityFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Two-parameter approximation controlled by a tight count

Finite-cell shot approximations have deterministic error at most
`meshError * pointCount`.  This file proves the probability-theoretic
closure step: a mesh error tending to zero and uniform tightness of the
counts imply exactly the two-parameter closeness condition used by the
converging-together theorem.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ]

/-- Deterministic `η_m C_N` control plus uniform tightness of the integer
counts gives two-parameter convergence in probability. -/
theorem twoParameter_close_of_count_control
    (X : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (C : ℕ → Ω → ℕ) (η : ℕ → ℝ)
    (hηnonneg : ∀ m, 0 ≤ η m)
    (hη : Tendsto η atTop (nhds 0))
    (hCtight : ∀ δ > 0, ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      μ.real {ω | K < C N ω} < δ)
    (herror : ∀ m N ω,
      |X N ω - Y m N ω| ≤ η m * (C N ω : ℝ)) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        μ.real {ω | r ≤ ‖X N ω - Y m N ω‖} < δ := by
  intro r hr δ hδ
  obtain ⟨K, hKevent⟩ := hCtight δ hδ
  have hden : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have htarget : 0 < r / ((K : ℝ) + 1) := div_pos hr hden
  have hηevent : ∀ᶠ m : ℕ in atTop,
      η m < r / ((K : ℝ) + 1) := hη (Iio_mem_nhds htarget)
  filter_upwards [hηevent] with m hm
  filter_upwards [hKevent] with N hKN
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans_lt hKN
  intro ω hω
  by_contra hcount
  have hCle : C N ω ≤ K := Nat.le_of_not_gt hcount
  have hηK : η m * (C N ω : ℝ) ≤ η m * (K : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast hCle
    · exact hηnonneg m
  have hηKlt : η m * (K : ℝ) < r := by
    calc
      η m * (K : ℝ) ≤ η m * ((K : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (hηnonneg m)
      _ < (r / ((K : ℝ) + 1)) * ((K : ℝ) + 1) := by
        exact mul_lt_mul_of_pos_right hm hden
      _ = r := by field_simp
  have herrlt : |X N ω - Y m N ω| < r :=
    (herror m N ω).trans_lt (hηK.trans_lt hηKlt)
  simp only [Real.norm_eq_abs] at hω
  exact (not_lt_of_ge hω) herrlt

/-- Uniform first moments imply uniform tightness of natural-valued counts.
All integrability and measurability hypotheses are explicit. -/
theorem count_tight_of_uniform_firstMoment
    (C : ℕ → Ω → ℕ)
    (hCint : ∀ N, Integrable (fun ω ↦ (C N ω : ℝ)) μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hmean : ∀ N,
      ∫ ω, (C N ω : ℝ) ∂μ ≤ M) :
    ∀ δ > 0, ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      μ.real {ω | K < C N ω} < δ := by
  intro δ hδ
  obtain ⟨K, hK⟩ : ∃ K : ℕ, M / δ < K := exists_nat_gt (M / δ)
  have hKpos : 0 < (K : ℝ) := by
    have hnonneg : 0 ≤ M / δ := div_nonneg hM hδ.le
    exact hnonneg.trans_lt (by exact_mod_cast hK)
  refine ⟨K, Eventually.of_forall fun N ↦ ?_⟩
  let f : Ω → ℝ := fun ω ↦ (C N ω : ℝ)
  have hfnonneg : 0 ≤ᵐ[μ] f :=
    Eventually.of_forall fun _ω ↦ by positivity
  have hfint : Integrable f μ := hCint N
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) hfnonneg hfint (K : ℝ)
  have hset : {ω | K < C N ω} ⊆ {ω | (K : ℝ) ≤ f ω} := by
    intro ω hω
    change (K : ℝ) ≤ (C N ω : ℝ)
    exact_mod_cast (Nat.le_of_lt hω)
  have hmeasure : μ.real {ω | K < C N ω} ≤
      μ.real {ω | (K : ℝ) ≤ f ω} :=
    measureReal_mono hset (measure_ne_top _ _)
  have hmul : (K : ℝ) * μ.real {ω | K < C N ω} ≤ M := by
    calc
      (K : ℝ) * μ.real {ω | K < C N ω} ≤
          (K : ℝ) * μ.real {ω | (K : ℝ) ≤ f ω} := by
        gcongr
      _ ≤ ∫ ω, f ω ∂μ := hmarkov
      _ ≤ M := hmean N
  have hprob : μ.real {ω | K < C N ω} ≤ M / (K : ℝ) := by
    apply (le_div_iff₀ hKpos).2
    simpa only [mul_comm] using! hmul
  have hMK : M / (K : ℝ) < δ := by
    apply (div_lt_iff₀ hKpos).2
    have hKr : M / δ < (K : ℝ) := by exact_mod_cast hK
    have hprod : M < (K : ℝ) * δ := (div_lt_iff₀ hδ).1 hKr
    nlinarith
  exact hprob.trans_lt hMK

/-- Convergence of first moments is enough for the eventual uniform
tightness needed by the mesh argument. -/
theorem count_tight_of_tendsto_firstMoment
    (C : ℕ → Ω → ℕ)
    (hCint : ∀ N, Integrable (fun ω ↦ (C N ω : ℝ)) μ)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hmean : Tendsto
      (fun N ↦ ∫ ω, (C N ω : ℝ) ∂μ) atTop (nhds lam)) :
    ∀ δ > 0, ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      μ.real {ω | K < C N ω} < δ := by
  intro δ hδ
  let M : ℝ := lam + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hmeanEvent : ∀ᶠ N : ℕ in atTop,
      ∫ ω, (C N ω : ℝ) ∂μ < M := by
    exact hmean.eventually_lt_const (by dsimp [M]; linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, M / δ < K := exists_nat_gt (M / δ)
  have hKpos : 0 < (K : ℝ) := by
    have hnonneg : 0 ≤ M / δ := div_nonneg hM hδ.le
    exact hnonneg.trans_lt (by exact_mod_cast hK)
  refine ⟨K, ?_⟩
  filter_upwards [hmeanEvent] with N hNmean
  let f : Ω → ℝ := fun ω ↦ (C N ω : ℝ)
  have hfnonneg : 0 ≤ᵐ[μ] f :=
    Eventually.of_forall fun _ω ↦ by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) hfnonneg (hCint N) (K : ℝ)
  have hset : {ω | K < C N ω} ⊆ {ω | (K : ℝ) ≤ f ω} := by
    intro ω hω
    change (K : ℝ) ≤ (C N ω : ℝ)
    exact_mod_cast (Nat.le_of_lt hω)
  have hmeasure : μ.real {ω | K < C N ω} ≤
      μ.real {ω | (K : ℝ) ≤ f ω} :=
    measureReal_mono hset (measure_ne_top _ _)
  have hmul : (K : ℝ) * μ.real {ω | K < C N ω} < M := by
    calc
      (K : ℝ) * μ.real {ω | K < C N ω} ≤
          (K : ℝ) * μ.real {ω | (K : ℝ) ≤ f ω} := by
        gcongr
      _ ≤ ∫ ω, f ω ∂μ := hmarkov
      _ < M := hNmean
  have hprob : μ.real {ω | K < C N ω} < M / (K : ℝ) := by
    apply (lt_div_iff₀ hKpos).2
    simpa only [mul_comm] using! hmul
  have hMK : M / (K : ℝ) < δ := by
    apply (div_lt_iff₀ hKpos).2
    have hKr : M / δ < (K : ℝ) := by exact_mod_cast hK
    have hprod : M < (K : ℝ) * δ := (div_lt_iff₀ hδ).1 hKr
    nlinarith
  exact hprob.trans hMK

end

end Erdos1002
