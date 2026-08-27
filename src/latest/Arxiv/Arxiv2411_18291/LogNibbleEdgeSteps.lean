import Arxiv.Arxiv2411_18291.LogNibbleIncrements
import Arxiv.Arxiv2411_18291.LogNibbleScaleBounds
import Arxiv.Arxiv2411_18291.NibbleEdgeIncrements

/-! # Finite edge-comparison steps for logarithmic tracking -/

noncomputable section

namespace Arxiv2411_18291

def logNibbleDegreeUpper (k : ℕ) (a D p : ℝ) : ℝ :=
  nibbleDegreeMain k D p + logNibbleDegreeError k a D p

def logNibbleDegreeLower (k : ℕ) (a D p : ℝ) : ℝ :=
  nibbleDegreeMain k D p - logNibbleDegreeError k a D p

def logNibbleEdgeStepScale (k : ℕ) (a g D p : ℝ) : ℝ :=
  (k : ℝ) * a ^ 2 * D / (p * g)

theorem logNibbleEdgeStepScale_eq {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (hg : g ≠ 0) (hD : D ≠ 0) (hp : p ≠ 0) :
    logNibbleEdgeStepScale k a g D p =
      a ^ 2 * D * nibbleDegreeMain k D p / nibbleCliqueMain k g D p := by
  rw [mul_div_assoc, nibbleDegreeMain_clique_ratio hk hg hD hp]
  unfold logNibbleEdgeStepScale
  ring

theorem logNibbleDegree_increment_bounds {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p) (hhalf : p ≤ 2 * s)
    (hstep : p - s = (k : ℝ) / g) :
    let S := logNibbleEdgeStepScale k a g D p
    let M := nibbleEdgeSlope k g D p
    let T := nibbleEdgeTaylor k g D p
    let δu := logNibbleDegreeUpper k a D s - logNibbleDegreeUpper k a D p
    let δl := logNibbleDegreeLower k a D s - logNibbleDegreeLower k a D p;
    -M + 3 * k * S ≤ δu ∧ δu ≤ -M + T + 6 * k * S ∧
      -M - 6 * k * S ≤ δl ∧ δl ≤ -M + T - 3 * k * S := by
  have hp := hs.trans_le hsp
  have hm : -nibbleEdgeSlope k g D p ≤ nibbleDegreeMain k D s - nibbleDegreeMain k D p ∧
      nibbleDegreeMain k D s - nibbleDegreeMain k D p ≤
        -nibbleEdgeSlope k g D p + nibbleEdgeTaylor k g D p := by
    have h := scaled_power_increment_bounds hs.le hsp hD (k - 1)
    rw [hstep, show k - 1 - 1 = k - 2 by omega,
      show k - 1 - 2 = k - 3 by omega] at h
    unfold nibbleDegreeMain nibbleEdgeSlope nibbleEdgeTaylor
    ring_nf at h ⊢
    exact h
  obtain ⟨helo, hehi⟩ := logNibbleDegreeError_increment_bounds k hs hsp hD
  have hden : 1 / s ≤ 2 / p := (div_le_div_iff₀ hs hp).mpr (by linarith only [hhalf])
  have hden' := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 3 * (k : ℝ) * a ^ 2 * D * (p - s) by positivity)
  have hehi' : logNibbleDegreeError k a D s - logNibbleDegreeError k a D p ≤
      6 * k * a ^ 2 * D * (p - s) / p := by
    apply hehi.trans
    convert! hden' using 1 <;> ring
  rw [hstep] at helo hehi'
  have he : 3 * k * logNibbleEdgeStepScale k a g D p ≤
        logNibbleDegreeError k a D s - logNibbleDegreeError k a D p ∧
      logNibbleDegreeError k a D s - logNibbleDegreeError k a D p ≤
        6 * k * logNibbleEdgeStepScale k a g D p := by
    unfold logNibbleEdgeStepScale
    constructor
    · convert! helo using 1
      ring
    · convert! hehi' using 1
      ring
  dsimp only [logNibbleDegreeUpper, logNibbleDegreeLower]
  exact ⟨by linarith only [hm.1, he.1], by linarith only [hm.2, he.2],
    by linarith only [hm.1, he.2], by linarith only [hm.2, he.1]⟩

theorem LogNibbleScalarConditions.width_small {k : ℕ} {a p : ℝ}
    (P : LogNibbleScalarConditions k a p) (hp : 0 < p) (hp1 : p ≤ 1) :
    72 * a ^ 2 ≤ p ^ (k - 1) := by
  have hL := nibbleLogFactor_one_le k hp hp1
  have hL2 : 1 ≤ (nibbleLogFactor k p) ^ 2 := by nlinarith only [hL]
  have hmul := mul_le_mul_of_nonneg_right hL2 (sq_nonneg a)
  have hh := P.degree_sq
  nlinarith only [hmul, hh]

theorem logNibbleEdgeSlope_dominates_errors {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (P : LogNibbleScalarConditions k a p) :
    (6 * k + 1 / 8) * logNibbleEdgeStepScale k a g D p ≤ nibbleEdgeSlope k g D p := by
  have hκ : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 6 * (k : ℝ) + 1 / 8 ≤ 72 * ((k - 1 : ℕ) : ℝ) := by
    rw [hκ]
    linarith only [hkR]
  have hnum : (6 * (k : ℝ) + 1 / 8) * a ^ 2 ≤
      ((k - 1 : ℕ) : ℝ) * p ^ (k - 1) := by
    have h₁ := mul_le_mul_of_nonneg_right hc (sq_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_left (P.width_small hp hp1) (Nat.cast_nonneg (k - 1))
    nlinarith only [h₁, h₂]
  have hpow : p ^ (k - 2) * p = p ^ (k - 1) := by
    rw [← pow_succ, show k - 2 + 1 = k - 1 by omega]
  calc
    _ = ((k : ℝ) * D / (p * g)) * ((6 * k + 1 / 8) * a ^ 2) := by
      unfold logNibbleEdgeStepScale
      ring
    _ ≤ ((k : ℝ) * D / (p * g)) * (((k - 1 : ℕ) : ℝ) * p ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by unfold nibbleEdgeSlope; rw [← hpow]; field_simp

theorem logNibbleEdgeTaylor_le_scale {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hlarge : 8 * (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    nibbleEdgeTaylor k g D p ≤ logNibbleEdgeStepScale k a g D p / 8 := by
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hκ₂ : ((k - 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 2
  have hc : ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k ≤ (k : ℝ) ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul hκ hκ₂ (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg k)
    nlinarith only [hh]
  have hnum : (((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k) * p ^ (k - 2) ≤
      a ^ 2 * g / 8 := by
    have hpow : p ^ (k - 2) ≤ 1 := pow_le_one₀ hp.le hp1
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k by positivity)
    nlinarith only [hh, hc, hlarge]
  have hpow : p ^ (k - 3) * p = p ^ (k - 2) := by
    rw [← pow_succ, show k - 3 + 1 = k - 2 by omega]
  calc
    _ = (D * k / (p * g ^ 2)) *
        ((((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k) * p ^ (k - 2)) := by
      unfold nibbleEdgeTaylor
      rw [← hpow]
      field_simp
    _ ≤ (D * k / (p * g ^ 2)) * (a ^ 2 * g / 8) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by unfold logNibbleEdgeStepScale; field_simp

theorem logNibbleDegree_step_control {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p) (hp1 : p ≤ 1)
    (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g)
    (P : LogNibbleScalarConditions k a p) (hlarge : 8 * (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    let S := logNibbleEdgeStepScale k a g D p
    let M := nibbleEdgeSlope k g D p
    let δu := logNibbleDegreeUpper k a D s - logNibbleDegreeUpper k a D p
    let δl := logNibbleDegreeLower k a D s - logNibbleDegreeLower k a D p
    |δu| ≤ 2 * M ∧ δu ≤ 0 ∧ -M + (3 * k - 1 / 8) * S ≤ δu ∧
      |δl| ≤ 2 * M ∧ δl ≤ -M - (3 * k - 1 / 8) * S := by
  have hp := hs.trans_le hsp
  obtain ⟨hulo, huhi, hllo, hlhi⟩ := logNibbleDegree_increment_bounds hk hD hs hsp hhalf hstep
  have hdom := logNibbleEdgeSlope_dominates_errors hk hg hD hp hp1 P
  have hT := logNibbleEdgeTaylor_le_scale hk hg hD hp hp1 hlarge
  have hS : 0 ≤ logNibbleEdgeStepScale k a g D p := by
    unfold logNibbleEdgeStepScale
    positivity
  have hM : 0 ≤ nibbleEdgeSlope k g D p := by unfold nibbleEdgeSlope; positivity
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkS := mul_nonneg (Nat.cast_nonneg k (α := ℝ)) hS
  dsimp only at hulo huhi hllo hlhi ⊢
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_, ?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩ <;>
    nlinarith only [hulo, huhi, hllo, hlhi, hdom, hT, hS, hM, hkS, hkR]

theorem logNibbleEdgeSlope_le_width {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hlarge : 200 * (k : ℝ) ^ 2 ≤ a ^ 2 * g) :
    2 * nibbleEdgeSlope k g D p ≤ a ^ 2 * D / 100 := by
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hc : ((k - 1 : ℕ) : ℝ) * k ≤ (k : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg k (α := ℝ))
    nlinarith only [hh]
  have hpow : p ^ (k - 2) ≤ 1 := pow_le_one₀ hp hp1
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ ((k - 1 : ℕ) : ℝ) * k by positivity)
  have hnum : 200 * (((k - 1 : ℕ) : ℝ) * k * p ^ (k - 2)) ≤ a ^ 2 * g := by
    nlinarith only [hh, hc, hlarge]
  have hmul := mul_le_mul_of_nonneg_right hnum hD
  unfold nibbleEdgeSlope
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hg).mpr
  nlinarith only [hmul]

end Arxiv2411_18291
