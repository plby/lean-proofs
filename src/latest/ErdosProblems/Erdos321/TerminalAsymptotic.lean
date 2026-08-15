import ErdosProblems.Erdos321.TerminalModelUpper
import ErdosProblems.Erdos321.ImplicitAsymptotic

namespace Erdos321

open Filter
open scoped Topology

/-- Complete terminal-product evaluation of the original normalized extremal
function. -/
theorem exists_normalizedExtremal_terminalProduct_bounds :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ n d, N₀ ≤ n → d ≤ n →
        LogTowerAbove B d (Real.log (Real.log (n : ℝ))) →
        realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B →
        c * iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) ≤
            normalizedExtremal n ∧
          normalizedExtremal n ≤
            C * iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) := by
  obtain ⟨Aₗ, Bₗ, hAₗ, hBₗ, hBₗA, hlower⟩ :=
    exists_uniform_iteratedLogProduct_lower
  obtain ⟨Aᵢ, Cᵢ, hAᵢ, hCᵢ, himplicit⟩ :=
    exists_normalizedExtremal_neumannModel_bounds
  obtain ⟨Aᵤ, hAᵤ, hupperData₀⟩ := exists_upperIterationData_threshold
  have hthirdEvent : ∀ᶠ n : ℕ in atTop, 0 ≤ thirdIteratedLog n := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h1 := Real.tendsto_log_atTop.comp hcast
    have h2 := Real.tendsto_log_atTop.comp h1
    have h3 := Real.tendsto_log_atTop.comp h2
    exact h3.eventually (eventually_ge_atTop 0)
  rcases eventually_atTop.1 hthirdEvent with ⟨A₃, hA₃⟩
  let A := max Aₗ (max Aᵢ (max Aᵤ (max A₃ 3)))
  let B : ℝ := max Bₗ (max 192 (8 * (A : ℝ)))
  have hAₗA : Aₗ ≤ A := le_max_left _ _
  have hAᵢA : Aᵢ ≤ A :=
    (le_max_left Aᵢ (max Aᵤ (max A₃ 3))).trans (le_max_right _ _)
  have hAᵤA : Aᵤ ≤ A :=
    (le_max_left Aᵤ (max A₃ 3)).trans
      ((le_max_right Aᵢ _).trans (le_max_right Aₗ _))
  have hA₃A : A₃ ≤ A :=
    (le_max_left A₃ 3).trans
      ((le_max_right Aᵤ _).trans
        ((le_max_right Aᵢ _).trans (le_max_right Aₗ _)))
  have hA3 : 3 ≤ A :=
    (le_max_right A₃ 3).trans
      ((le_max_right Aᵤ _).trans
        ((le_max_right Aᵢ _).trans (le_max_right Aₗ _)))
  have hBₗB : Bₗ ≤ B := le_max_left _ _
  have hB192 : (192 : ℝ) ≤ B :=
    (le_max_left (192 : ℝ) (8 * (A : ℝ))).trans (le_max_right _ _)
  have hB4 : (4 : ℝ) ≤ B :=
    (show (4 : ℝ) ≤ 192 by norm_num).trans hB192
  have hupperData : ∀ n, A ≤ n → AdaptiveUpperIterationData n := by
    intro n hn
    exact hupperData₀ n (hAᵤA.trans hn)
  have hthirdA : 0 ≤ thirdIteratedLog A := hA₃ A hA₃A
  obtain ⟨Kₗ, hKₗ1, hcompareLower⟩ :=
    adaptiveNeumannModel_threshold_comparable
      (show 2 ≤ Aₗ by omega) hAₗA
  obtain ⟨Kᵢ, hKᵢ1, hcompareUpper⟩ :=
    adaptiveNeumannModel_threshold_comparable
      (show 2 ≤ Aᵢ by omega) hAᵢA
  let Cₜ := 3 * (1 + terminalModelConstant A B)
  let c : ℝ := 1 / (128 * Kₗ)
  let C : ℝ := Cᵢ * Kᵢ * Cₜ
  have hKₗpos : 0 < Kₗ := lt_of_lt_of_le (by norm_num) hKₗ1
  have hKᵢ0 : 0 ≤ Kᵢ := (by norm_num : (0 : ℝ) ≤ 1).trans hKᵢ1
  have hCₜ0 : 0 ≤ Cₜ := by
    dsimp [Cₜ]
    have := terminalModelConstant_nonneg (show 2 ≤ A by omega) B
    positivity
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨A, B, c, C, hA3, hB192, hcpos, hC0, ?_⟩
  intro n d hnA hdN htower hterminal
  let x := Real.log (Real.log (n : ℝ))
  let P := iteratedLogTailProduct d x
  have hTowerLower : LogTowerAbove Bₗ d x := by
    intro j hj
    exact hBₗB.trans (htower j hj)
  have hnAₗ : Aₗ ≤ n := hAₗA.trans hnA
  have hnAᵢ : Aᵢ ≤ n := hAᵢA.trans hnA
  have hlowerP : P / 16 ≤ adaptiveNeumannModel Aₗ n := by
    simpa [P, x] using hlower n d hnAₗ hdN hTowerLower
  have hcompareL := hcompareLower n
  have hPcommon : P / (16 * Kₗ) ≤ adaptiveNeumannModel A n := by
    have hPK : P / 16 ≤ Kₗ * adaptiveNeumannModel A n :=
      hlowerP.trans hcompareL
    apply (le_of_mul_le_mul_left
      (show Kₗ * (P / (16 * Kₗ)) ≤
        Kₗ * adaptiveNeumannModel A n by
          calc
            Kₗ * (P / (16 * Kₗ)) = P / 16 := by field_simp
            _ ≤ Kₗ * adaptiveNeumannModel A n := hPK)
      hKₗpos)
  have himpl := himplicit n hnAᵢ
  have hanti : adaptiveNeumannModel A n ≤ adaptiveNeumannModel Aᵢ n :=
    adaptiveNeumannModel_anti_threshold (show 2 ≤ Aᵢ by omega) hAᵢA n
  have hlowerNorm : P / (128 * Kₗ) ≤ normalizedExtremal n := by
    have hm := mul_le_mul_of_nonneg_left hanti (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hmodelNorm : (1 / 8 : ℝ) * adaptiveNeumannModel A n ≤
        normalizedExtremal n := hm.trans himpl.1
    calc
      P / (128 * Kₗ) = (1 / 8 : ℝ) * (P / (16 * Kₗ)) := by ring
      _ ≤ (1 / 8 : ℝ) * adaptiveNeumannModel A n :=
        mul_le_mul_of_nonneg_left hPcommon (by norm_num)
      _ ≤ normalizedExtremal n := hmodelNorm
  have hmodelUpper := adaptiveNeumannModel_le_terminalProduct
    hA3 hthirdA hupperData hB4 hnA htower hterminal
  have hcompareI := hcompareUpper n
  have hnormalizedUpper : normalizedExtremal n ≤ C * P := by
    calc
      normalizedExtremal n ≤ Cᵢ * adaptiveNeumannModel Aᵢ n := himpl.2
      _ ≤ Cᵢ * (Kᵢ * adaptiveNeumannModel A n) :=
        mul_le_mul_of_nonneg_left hcompareI hCᵢ
      _ ≤ Cᵢ * (Kᵢ * (Cₜ * P)) := by
        have hm := mul_le_mul_of_nonneg_left hmodelUpper hKᵢ0
        exact mul_le_mul_of_nonneg_left hm hCᵢ
      _ = C * P := by dsimp [C, Cₜ, P, x]; ring
  constructor
  · change (1 / (128 * Kₗ)) * P ≤ normalizedExtremal n
    calc
      (1 / (128 * Kₗ)) * P = P / (128 * Kₗ) := by ring
      _ ≤ normalizedExtremal n := hlowerNorm
  · simpa [P, x] using hnormalizedUpper

end Erdos321
