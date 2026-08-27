import Arxiv.Arxiv2411_18291.NibbleSurvivalError

/-! # Concrete comparison increments satisfy the edge drift requirements -/

namespace Arxiv2411_18291

theorem nibbleDegreeUpper_step_control {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D) (hs : 0 < s) (hsp : s ≤ p)
    (hp1 : p ≤ 1) (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g)
    (hap : a ≤ p ^ k) (hsmall : (16 * (k : ℝ)) ^ 2 * a ≤ 1)
    (hlarge : 16 * (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    let δ := nibbleDegreeUpper k a D s - nibbleDegreeUpper k a D p
    |δ| ≤ 2 * nibbleEdgeSlope k g D p ∧ δ ≤ 0 ∧
      -nibbleEdgeSlope k g D p +
        (6 * ((k - 1 : ℕ) : ℝ) + 4) * nibbleEdgeStepScale k a g D p ≤ δ := by
  have hp : 0 < p := hs.trans_le hsp
  have hlarge' : (k : ℝ) ^ 3 ≤ a ^ 2 * g := by
    have h := pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 3
    linarith only [hlarge, h]
  obtain ⟨hlo, hhi⟩ := nibbleDegreeUpper_increment_bounds hk hD.le hs hsp hhalf hstep
  have hT := nibbleEdgeTaylor_le_scale hk hg hD.le hp hp1 hlarge'
  have hdom := nibbleEdgeSlope_dominates_errors hk ha hg hD.le hp hap hsmall
  have hS := nibbleEdgeStepScale_nonneg k (a := a) (p := p) hg.le hD.le
  have hL := nibbleEdgeSlope_nonneg k hg.le hD.le hp.le
  have h16 := mul_nonneg (show 0 ≤ 16 * (k : ℝ) by positivity) hS
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff : 6 * ((k - 1 : ℕ) : ℝ) + 4 ≤ 16 * k := by linarith only [hκ, hk']
  have hcoeffS := mul_le_mul_of_nonneg_right hcoeff hS
  dsimp only
  have hδ : nibbleDegreeUpper k a D s - nibbleDegreeUpper k a D p ≤ 0 := by
    nlinarith only [hhi, hT, hdom]
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, hδ, ?_⟩ <;> nlinarith only [hlo, hδ, hL, h16, hcoeffS]

theorem nibbleDegreeLower_step_control {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D) (hs : 0 < s) (hsp : s ≤ p)
    (hp1 : p ≤ 1) (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g)
    (hap : a ≤ p ^ k) (hsmall : (16 * (k : ℝ)) ^ 2 * a ≤ 1)
    (hlarge : 16 * (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    let δ := nibbleDegreeLower k a D s - nibbleDegreeLower k a D p
    |δ| ≤ 2 * nibbleEdgeSlope k g D p ∧
      δ ≤ -nibbleEdgeSlope k g D p -
        6 * ((k - 1 : ℕ) : ℝ) * nibbleEdgeStepScale k a g D p -
          4 * nibbleDegreeMain k D p * (2 * nibbleEdgeSlope k g D p) /
            nibbleCliqueMain k g D p := by
  have hp : 0 < p := hs.trans_le hsp
  have hlarge' : (k : ℝ) ^ 3 ≤ a ^ 2 * g := by
    have h := pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 3
    linarith only [hlarge, h]
  obtain ⟨hlo, hhi⟩ := nibbleDegreeLower_increment_bounds hk hD.le hs hsp hhalf hstep
  have hT := nibbleEdgeTaylor_le_scale hk hg hD.le hp hp1 hlarge'
  have hdom := nibbleEdgeSlope_dominates_errors hk ha hg hD.le hp hap hsmall
  have hsurvive := nibbleEdgeSurvival_le_scale hk hg hD hp hp1 hlarge
  have hS := nibbleEdgeStepScale_nonneg k (a := a) (p := p) hg.le hD.le
  have hL := nibbleEdgeSlope_nonneg k hg.le hD.le hp.le
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff : 6 * ((k - 1 : ℕ) : ℝ) + 2 ≤ 16 * k := by linarith only [hκ, hk']
  have hcoeffS := mul_le_mul_of_nonneg_right hcoeff hS
  have h16S : nibbleEdgeStepScale k a g D p ≤ 16 * k * nibbleEdgeStepScale k a g D p := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (by linarith only [hk'] : 1 ≤ 16 * (k : ℝ)) hS
  dsimp only
  have hδ : nibbleDegreeLower k a D s - nibbleDegreeLower k a D p ≤ 0 := by
    nlinarith only [hhi, hT, h16S, hL]
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · nlinarith only [hlo, hdom, hS]
  · nlinarith only [hδ, hL]
  · nlinarith only [hhi, hT, hcoeffS, hsurvive]

end Arxiv2411_18291
