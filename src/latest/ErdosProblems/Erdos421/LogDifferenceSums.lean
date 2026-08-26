import ErdosProblems.Erdos421.LogDifference
import ErdosProblems.Erdos421.LogarithmicSecondDerivative
import ErdosProblems.Erdos421.VanDerCorput

/-! # Phase spacing for the correlations of logarithmic sums -/

namespace Erdos421

noncomputable def logarithmicDifferencePhase (M h : ℕ) (τ : ℝ) (n : ℕ) : ℝ :=
  τ * (Real.log (M + n : ℕ) - Real.log (M + n + h : ℕ))

theorem logarithmicDifferencePhase_increment (M h n : ℕ) (τ : ℝ) :
    phaseIncrement (logarithmicDifferencePhase M h τ) n =
      τ * logDifferenceIncrement (M + n : ℝ) h := by
  unfold phaseIncrement logarithmicDifferencePhase logDifferenceIncrement
  simp only [Nat.cast_add, Nat.cast_one]
  have h₁ : (M : ℝ) + (n + 1) = M + n + 1 := by ring
  have h₂ : (M : ℝ) + n + 1 + h = M + n + h + 1 := by ring
  rw [h₁, h₂]
  ring

theorem logarithmicDifferencePhase_antitone {M h : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) :
    Antitone (phaseIncrement (logarithmicDifferencePhase M h τ)) := by
  intro i j hij
  rw [logarithmicDifferencePhase_increment, logarithmicDifferencePhase_increment]
  apply mul_le_mul_of_nonneg_left _ hτ
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  exact logDifferenceIncrement_antitone (by positivity)
    (by exact_mod_cast Nat.add_le_add_left hij M) (Nat.cast_nonneg h)

theorem logarithmicDifferencePhase_nonneg {M h : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) (n : ℕ) :
    0 ≤ phaseIncrement (logarithmicDifferencePhase M h τ) n := by
  rw [logarithmicDifferencePhase_increment]
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  exact mul_nonneg hτ (logDifferenceIncrement_nonneg (by positivity) (Nat.cast_nonneg h))

theorem logarithmicDifferencePhase_upper {M h : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) (n : ℕ) :
    phaseIncrement (logarithmicDifferencePhase M h τ) n ≤ τ * h / (M : ℝ) ^ 2 := by
  have ha := logarithmicDifferencePhase_antitone (h := h) hM hτ (Nat.zero_le n)
  rw [logarithmicDifferencePhase_increment M h 0 τ, Nat.cast_zero, add_zero] at ha
  have hp : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := mul_le_mul_of_nonneg_left (logDifferenceIncrement_upper hp (Nat.cast_nonneg h)) hτ
  exact ha.trans (by simpa only [mul_div_assoc] using hb)

theorem logarithmicDifferencePhase_spacing {M L h i j : ℕ} {τ : ℝ}
    (hM : 0 < M) (hh : 0 < h) (hτ : 0 ≤ τ) (hij : i ≤ j) (hj : j ≤ L) :
    (τ * h / (M + L + h + 1 : ℝ) ^ 3) * ((j : ℝ) - i) ≤
      phaseIncrement (logarithmicDifferencePhase M h τ) i -
        phaseIncrement (logarithmicDifferencePhase M h τ) j := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hxy : (M + i : ℝ) ≤ M + j := by exact_mod_cast Nat.add_le_add_left hij M
  have hyB : (M + j + h + 1 : ℝ) ≤ M + L + h + 1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left hj M) h) 1
  have hd := logDifferenceIncrement_drop_lower_bounded (by positivity : (0 : ℝ) < M + i)
    hxy hhp hyB
  have hm := mul_le_mul_of_nonneg_left hd hτ
  rw [logarithmicDifferencePhase_increment, logarithmicDifferencePhase_increment]
  calc
    _ = τ * ((h : ℝ) * ((M + j : ℝ) - (M + i)) / (M + L + h + 1 : ℝ) ^ 3) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

theorem logarithmicDifference_sum_spacing_bound {M h : ℕ} (hM : 0 < M) (hh : 0 < h)
    (L : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖∑ n ∈ Finset.range L, oscillatoryPhase 1 (logarithmicDifferencePhase M h τ n)‖ ≤
      ((⌈τ * h / (M : ℝ) ^ 2⌉₊ : ℕ) + 2 : ℝ) *
        (2 + 12 / δ + 2 * δ * (M + L + h + 1 : ℝ) ^ 3 / (τ * h)) := by
  let K := ⌈τ * h / (M : ℝ) ^ 2⌉₊
  let η := τ * h / (M + L + h + 1 : ℝ) ^ 3
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hη : 0 < η := by dsimp only [η]; positivity
  have ha := logarithmicDifferencePhase_antitone (h := h) hM hτ.le
  have hrange : ∀ n < L,
      0 ≤ phaseIncrement (logarithmicDifferencePhase M h τ) n ∧
        phaseIncrement (logarithmicDifferencePhase M h τ) n ≤ 2 * Real.pi * K := by
    intro n _
    refine ⟨logarithmicDifferencePhase_nonneg hM hτ.le n, ?_⟩
    have hu := logarithmicDifferencePhase_upper (h := h) hM hτ.le n
    have hk : τ * h / (M : ℝ) ^ 2 ≤ K := Nat.le_ceil _
    have hkn : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hpi := Real.one_le_pi_div_two
    nlinarith
  have hs : ∀ i < L, ∀ j < L, i ≤ j →
      η * ((j : ℝ) - i) ≤ phaseIncrement (logarithmicDifferencePhase M h τ) i -
        phaseIncrement (logarithmicDifferencePhase M h τ) j := by
    intro i _ j hj hij
    exact logarithmicDifferencePhase_spacing hM hh hτ.le hij hj.le
  have hb := separated_increment_sum_bound (logarithmicDifferencePhase M h τ) L K
    (fun _ _ _ _ hij ↦ ha hij) hδ hη hrange hs
  have heq : 2 * δ / η = 2 * δ * (M + L + h + 1 : ℝ) ^ 3 / (τ * h) := by
    dsimp only [η]
    rw [div_div_eq_mul_div]
  rwa [heq] at hb

theorem logarithmic_finiteCorrelation_eq (M N h : ℕ) (τ : ℝ) :
    finiteCorrelation (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) τ) N h =
      ∑ n ∈ Finset.range (N - h), oscillatoryPhase 1 (logarithmicDifferencePhase M h τ n) := by
  unfold finiteCorrelation
  apply Finset.sum_congr rfl
  intro n _
  rw [RCLike.inner_apply, oscillatoryPhase_mul_conj]
  unfold logarithmicDifferencePhase oscillatoryPhase
  congr 1
  simp only [Nat.add_assoc, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_sub, mul_one]
  ring

end Erdos421
