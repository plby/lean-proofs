import ErdosProblems.Erdos4.TiltedPrimeExposure
import ErdosProblems.Erdos4.TiltedPrimeDegree
import ErdosProblems.Erdos4.TiltedPrimeErrorBudget

/-! The actual tilted prime-edge laws meet the degree, sparsity, and legality requirements. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem eventually_prime_initialization {c G C : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ (D : PrimeExposureData c x G C) (hτ : 0 ≤ tiltExponent x),
      let ν := primeSurvivorLaw c x hτ
      (∀ v, v ∉ D.bad → (conditionSurvival ν {v}).prob
        (fun W => vertexDegree (fun p => cappedEdgeLaw ν (D.law p) W) v < 4) ≤
          1 / Real.log (x : ℝ) ^ (40 : ℕ)) ∧
      (∀ W p v, (cappedEdgeLaw ν (D.law p) W).prob (fun E => v ∈ E) ≤ (x : ℝ) ^ (-4 / 5 : ℝ)) ∧
      (∀ W v w, v ≠ w → pairDegree (fun p => cappedEdgeLaw ν (D.law p) W) v w ≤ (x : ℝ) ^ (-4 / 5 : ℝ)) ∧
      (∀ W p E, 0 < (cappedEdgeLaw ν (D.law p) W).weight E → E.card ≤ sieveDimension (growingIndex x) ∧
        ∃ b : ZMod p.val, ∀ v ∈ E, (v.val : ZMod p.val) = b) := by
  classical
  filter_upwards [eventually_primeSurvivorLaw_accurate hc, eventually_tilted_prime_error_budget]
    with x hacc hbudget
  intro D hτ
  dsimp only
  let ν := primeSurvivorLaw c x hτ
  let k := sieveDimension (growingIndex x)
  let σ := primeDensity x
  let ε := 1 / Real.log (x : ℝ) ^ (80 : ℕ)
  let δ := (k : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ)
  have hr : 1 ≤ k := Nat.one_le_two_pow
  have hσ : 0 < σ := primeDensity_pos x
  have hσ1 : σ ≤ 1 := primeDensity_le_one x
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hε : ε ≤ 1 / 16 := hbudget.1
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsize : ∀ p E, 0 < (D.law p).weight E → E.card ≤ k := fun p E hE => (D.legal p E hE).1
  have hinv : ∀ p E, 0 < (D.law p).weight E → 1 / survival ν E ≤ 2 / σ ^ k := by
    intro p E hE
    exact constant_survival_inverse_le ν hσ hσ1 (by linarith : ε ≤ 1 / 2) (hacc hτ)
      (by omega : k ≤ 3 * k) E (hsize p E hE)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hh := capped_prime_degree_error ν D.law v hr hσ hσ1 hε0 hε hδ (hacc hτ) hsize
      D.marginal (fun w hw => D.pair_degree v w hw.symm)
      (primeSurvivorLaw_singleton c x hτ v) (D.degree v hv)
    exact hh.trans hbudget.2.1
  · intro W p v
    calc
      _ ≤ ((2 / σ ^ k) / 2) * (D.law p).prob (fun E => v ∈ E) :=
        cappedEdgeLaw_event_le ν (D.law p) W (fun E => v ∈ E) (by simp) (by positivity) (hinv p)
      _ ≤ ((2 / σ ^ k) / 2) * δ := mul_le_mul_of_nonneg_left (D.marginal p v) (by positivity)
      _ = δ / σ ^ k := by ring
      _ ≤ _ := hbudget.2.2
  · intro W v w hvw
    calc
      _ ≤ ((2 / σ ^ k) / 2) * pairDegree D.law v w :=
        cappedEdgeLaw_pairDegree_le ν D.law W v w (by positivity) hinv
      _ ≤ ((2 / σ ^ k) / 2) * δ := mul_le_mul_of_nonneg_left (D.pair_degree v w hvw) (by positivity)
      _ = δ / σ ^ k := by ring
      _ ≤ _ := hbudget.2.2
  · intro W p E hE
    rcases cappedEdgeLaw_support ν (D.law p) W E hE with hz | ⟨hpos, _⟩
    · subst E
      exact ⟨Nat.zero_le _, 0, by simp⟩
    · exact D.legal p E hpos

end Erdos4.Tilted
