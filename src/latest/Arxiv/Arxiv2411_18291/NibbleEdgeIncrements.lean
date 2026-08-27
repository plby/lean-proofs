import Arxiv.Arxiv2411_18291.NibbleCliqueScaleBounds

/-! # Finite increments of the concrete edge comparison functions -/

noncomputable section

namespace Arxiv2411_18291

def nibbleEdgeSlope (k : ℕ) (g D p : ℝ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * D * p ^ (k - 2) * k / g

def nibbleEdgeTaylor (k : ℕ) (g D p : ℝ) : ℝ :=
  D * ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * p ^ (k - 3) * ((k : ℝ) / g) ^ 2

def nibbleEdgeStepScale (k : ℕ) (a g D p : ℝ) : ℝ :=
  (k : ℝ) * a ^ 2 * D / (p ^ 2 * g)

theorem nibbleEdgeSlope_eq_main_ratio {k : ℕ} (hk : 2 ≤ k) {g D p : ℝ}
    (hg : g ≠ 0) (hD : D ≠ 0) (hp : p ≠ 0) :
    nibbleEdgeSlope k g D p = ((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p ^ 2 /
      nibbleCliqueMain k g D p := by
  have hk0 : 0 < k := by omega
  have hexp : k - 2 + 1 = k - 1 := by omega
  have hpow : p ^ (k - 1) = p ^ (k - 2) * p := by
    simpa only [hexp] using pow_succ p (k - 2)
  symm
  calc
    _ = ((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p *
        (nibbleDegreeMain k D p / nibbleCliqueMain k g D p) := by ring
    _ = ((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p * ((k : ℝ) / (p * g)) := by
      rw [nibbleDegreeMain_clique_ratio hk0 hg hD hp]
    _ = _ := by
      unfold nibbleDegreeMain nibbleEdgeSlope
      rw [hpow]
      field_simp

theorem nibbleEdgeStepScale_eq {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (hg : g ≠ 0) (hD : D ≠ 0) (hp : p ≠ 0) :
    nibbleEdgeStepScale k a g D p = nibbleEdgeScale a D p * nibbleDegreeMain k D p /
      nibbleCliqueMain k g D p :=
  (nibbleEdgeScale_clique_ratio hk hg hD hp).symm

theorem nibbleDegreeUpper_increment_bounds {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p) (hhalf : p ≤ 2 * s)
    (hstep : p - s = (k : ℝ) / g) :
    -nibbleEdgeSlope k g D p + 16 * k * nibbleEdgeStepScale k a g D p ≤
        nibbleDegreeUpper k a D s - nibbleDegreeUpper k a D p ∧
      nibbleDegreeUpper k a D s - nibbleDegreeUpper k a D p ≤
        -nibbleEdgeSlope k g D p + nibbleEdgeTaylor k g D p +
          32 * k * nibbleEdgeStepScale k a g D p := by
  have h := power_add_reciprocal_increment_bounds hs hsp hhalf hD
    (show 0 ≤ 16 * (k : ℝ) * a ^ 2 * D by positivity) (k - 1)
  dsimp only at h
  have hidx₁ : k - 1 - 1 = k - 2 := by omega
  have hidx₂ : k - 1 - 2 = k - 3 := by omega
  rw [hstep, hidx₁, hidx₂] at h
  unfold nibbleDegreeUpper nibbleDegreeMain nibbleDegreeError nibbleEdgeScale
    nibbleEdgeSlope nibbleEdgeTaylor nibbleEdgeStepScale
  ring_nf at h ⊢
  exact h

theorem nibbleDegreeLower_increment_bounds {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p) (hhalf : p ≤ 2 * s)
    (hstep : p - s = (k : ℝ) / g) :
    -nibbleEdgeSlope k g D p - 32 * k * nibbleEdgeStepScale k a g D p ≤
        nibbleDegreeLower k a D s - nibbleDegreeLower k a D p ∧
      nibbleDegreeLower k a D s - nibbleDegreeLower k a D p ≤
        -nibbleEdgeSlope k g D p + nibbleEdgeTaylor k g D p -
          16 * k * nibbleEdgeStepScale k a g D p := by
  have h := power_sub_reciprocal_increment_bounds hs hsp hhalf hD
    (show 0 ≤ 16 * (k : ℝ) * a ^ 2 * D by positivity) (k - 1)
  dsimp only at h
  have hidx₁ : k - 1 - 1 = k - 2 := by omega
  have hidx₂ : k - 1 - 2 = k - 3 := by omega
  rw [hstep, hidx₁, hidx₂] at h
  unfold nibbleDegreeLower nibbleDegreeMain nibbleDegreeError nibbleEdgeScale
    nibbleEdgeSlope nibbleEdgeTaylor nibbleEdgeStepScale
  ring_nf at h ⊢
  exact h

end Arxiv2411_18291
