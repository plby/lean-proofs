import ErdosProblems.Erdos321.FinalAsymptotic

/-!
# Erdős Problem 320

For `N : ℕ`, `S N` is the number of distinct rational numbers of the form

`sum n in A, 1 / n`, where `A ⊆ Finset.Icc 1 N`.

The theorem below gives the resolved order of magnitude at the terminal
iterated-logarithm depth.  If `d` is the last depth for which the logarithmic
tower starting at `log (log n)` stays above a fixed constant, then `log (S n)`
is bounded above and below by positive constant multiples of

`n / log n * ∏ j in Finset.Icc 3 (d + 2), log^[j] n`.

The exact finite product is represented by
`Erdos321.iteratedLogTailProduct d (log (log n))`; its identification with the
displayed product is `Erdos321.iteratedLogTailProduct_eq_prod`.
-/

namespace Erdos320

open Filter
open scoped Topology

/-- The exact counting function in Erdős Problem 320.  The empty subset is
included, as it is in the mathematical definition. -/
def S (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.image Erdos321.reciprocalSubsetSum).card

/-- `S` is definitionally the harmonic subset-sum count developed as part of
the proof of Erdős Problem 321. -/
theorem S_eq_harmonicSubsetSumCount (N : ℕ) :
    S N = Erdos321.harmonicSubsetSumCount N :=
  rfl

/-- Natural logarithm of the number of distinct harmonic subset sums. -/
noncomputable def logS (N : ℕ) : ℝ :=
  Real.log (S N)

theorem logS_eq_harmonicEntropy (N : ℕ) :
    logS N = Erdos321.harmonicEntropy N :=
  rfl

/-- Resolution of Erdős Problem 320.

The retained depth `d` may depend on `n`, but the stopping threshold `B` and
the comparison constants are absolute.  Thus this is a fully quantified
version of

`log S(n) ≍ (n / log n) * ∏_{j=3}^{k(n)} log_j n`,

where `k(n) = d + 2` is chosen so that the next iterated logarithm is bounded
by the fixed constant `B`. -/
theorem erdos_320 :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 < C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ,
        d ≤ n ∧ Erdos321.IsTerminalLogDepth B n d ∧
          c * Erdos321.terminalReciprocalScale n d ≤ logS n ∧
          logS n ≤ C * Erdos321.terminalReciprocalScale n d := by
  obtain ⟨Nₗ, B, cₗ, Cₗ, hNₗ, hB, hcₗ, hCₗ, hR⟩ :=
    Erdos321.erdos321_asymptotic
  obtain ⟨Aₑ, K, hAₑ64, hK0, hentropy⟩ :=
    Erdos321.exists_normalizedEntropy_le_neumannModel
  obtain ⟨Aᵤ, hAᵤ, hupperData₀⟩ :=
    Erdos321.exists_upperIterationData_threshold
  have hthirdEvent : ∀ᶠ n : ℕ in atTop,
      0 ≤ Erdos321.thirdIteratedLog n := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h₁ := Real.tendsto_log_atTop.comp hcast
    have h₂ := Real.tendsto_log_atTop.comp h₁
    have h₃ := Real.tendsto_log_atTop.comp h₂
    exact h₃.eventually (eventually_ge_atTop 0)
  rcases eventually_atTop.1 hthirdEvent with ⟨A₃, hA₃⟩
  let A := max Nₗ (max Aₑ (max Aᵤ (max A₃ 3)))
  have hNₗA : Nₗ ≤ A := le_max_left _ _
  have hAₑA : Aₑ ≤ A :=
    (le_max_left Aₑ (max Aᵤ (max A₃ 3))).trans (le_max_right _ _)
  have hAᵤA : Aᵤ ≤ A :=
    (le_max_left Aᵤ (max A₃ 3)).trans
      ((le_max_right Aₑ _).trans (le_max_right Nₗ _))
  have hA₃A : A₃ ≤ A :=
    (le_max_left A₃ 3).trans
      ((le_max_right Aᵤ _).trans
        ((le_max_right Aₑ _).trans (le_max_right Nₗ _)))
  have hA3 : 3 ≤ A :=
    (le_max_right A₃ 3).trans
      ((le_max_right Aᵤ _).trans
        ((le_max_right Aₑ _).trans (le_max_right Nₗ _)))
  have hupperData : ∀ n, A ≤ n → Erdos321.AdaptiveUpperIterationData n := by
    intro n hn
    exact hupperData₀ n (hAᵤA.trans hn)
  have hthirdA : 0 ≤ Erdos321.thirdIteratedLog A := hA₃ A hA₃A
  obtain ⟨K₂, hK₂1, hcompare⟩ :=
    Erdos321.adaptiveNeumannModel_threshold_comparable
      (show 2 ≤ Aₑ by omega) hAₑA
  have hB4 : (4 : ℝ) ≤ B :=
    (show (4 : ℝ) ≤ 192 by norm_num).trans hB
  let Cₜ : ℝ := 3 * (1 + Erdos321.terminalModelConstant A B)
  let C₀ : ℝ := K * K₂ * Cₜ
  let c : ℝ := cₗ * Real.log 2
  let C : ℝ := 1 + C₀
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK₂0 : 0 ≤ K₂ := (by norm_num : (0 : ℝ) ≤ 1).trans hK₂1
  have hCₜ0 : 0 ≤ Cₜ := by
    dsimp [Cₜ]
    have hterminalConstant :=
      Erdos321.terminalModelConstant_nonneg (show 2 ≤ A by omega) B
    positivity
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨A, B, c, C, hA3, hB, hc, hC, ?_⟩
  intro n hn
  obtain ⟨d, hdn, hterminal, hlowerR, hupperR⟩ :=
    hR n (hNₗA.trans hn)
  let x : ℝ := Real.log (Real.log (n : ℝ))
  let P : ℝ := Erdos321.iteratedLogTailProduct d x
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hP0 : 0 ≤ P := by
    dsimp [P, x]
    exact Erdos321.iteratedLogTailProduct_nonneg
      (Erdos321.logPositive_of_tower hBpos hterminal.1)
  have hlower : c * Erdos321.terminalReciprocalScale n d ≤ logS n := by
    have hmul := mul_le_mul_of_nonneg_right hlowerR hlog2.le
    calc
      c * Erdos321.terminalReciprocalScale n d =
          (cₗ * Erdos321.terminalReciprocalScale n d) * Real.log 2 := by
            dsimp [c]
            ring
      _ ≤ (Erdos321.extremalSize n : ℝ) * Real.log 2 := hmul
      _ ≤ Erdos321.harmonicEntropy n :=
        Erdos321.extremal_mul_log_two_le_entropy n
      _ = logS n := (logS_eq_harmonicEntropy n).symm
  have hmodelUpper := Erdos321.adaptiveNeumannModel_le_terminalProduct
    hA3 hthirdA hupperData hB4 hn hterminal.1 hterminal.2
  have hnormalizedUpper₀ : Erdos321.normalizedEntropy n ≤ C₀ * P := by
    calc
      Erdos321.normalizedEntropy n ≤
          K * Erdos321.adaptiveNeumannModel Aₑ n :=
        hentropy n (hAₑA.trans hn)
      _ ≤ K * (K₂ * Erdos321.adaptiveNeumannModel A n) :=
        mul_le_mul_of_nonneg_left (hcompare n) hK0
      _ ≤ K * (K₂ * (Cₜ * P)) := by
        have hm := mul_le_mul_of_nonneg_left hmodelUpper hK₂0
        exact mul_le_mul_of_nonneg_left hm hK0
      _ = C₀ * P := by
        dsimp [C₀, Cₜ, P, x]
        ring
  have hnormalizedUpper : Erdos321.normalizedEntropy n ≤ C * P := by
    exact hnormalizedUpper₀.trans
      (mul_le_mul_of_nonneg_right (show C₀ ≤ C by dsimp [C]; linarith) hP0)
  have hn3 : 3 ≤ n := hA3.trans hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let s : ℝ := (n : ℝ) / Real.log n
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hcancel :
      s * Erdos321.normalizedEntropy n = Erdos321.harmonicEntropy n := by
    dsimp [s, Erdos321.normalizedEntropy]
    field_simp [ne_of_gt hnpos, ne_of_gt hlogpos]
  have hupperEntropy :
      Erdos321.harmonicEntropy n ≤ C * (s * P) := by
    have hm := mul_le_mul_of_nonneg_left hnormalizedUpper hspos.le
    rw [hcancel] at hm
    calc
      Erdos321.harmonicEntropy n ≤ s * (C * P) := hm
      _ = C * (s * P) := by ring
  have hupper : logS n ≤ C * Erdos321.terminalReciprocalScale n d := by
    rw [logS_eq_harmonicEntropy]
    simpa [Erdos321.terminalReciprocalScale, s, P, x, mul_assoc] using
      hupperEntropy
  exact ⟨d, hdn, hterminal, hlower, hupper⟩

#print axioms erdos_320

end Erdos320
