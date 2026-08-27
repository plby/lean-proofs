import Arxiv.Arxiv2411_18291.NibbleEdgeSequenceSteps

/-! # Uniform frozen-edge loss and increment scales -/

noncomputable section

namespace Arxiv2411_18291

def nibbleEdgeStepBound (k : ℕ) (g D L : ℝ) : ℝ := (k : ℝ) * L + 2 * (k : ℝ) ^ 2 * D / g

theorem nibbleEdgeSlope_le (k : ℕ) {g D p : ℝ} (hg : 0 < g) (hD : 0 ≤ D)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : nibbleEdgeSlope k g D p ≤ (k : ℝ) ^ 2 * D / g := by
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hpow : p ^ (k - 2) ≤ 1 := pow_le_one₀ hp hp1
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Nat.cast_nonneg (k - 1)) hD)
  have h₂ := mul_le_mul_of_nonneg_right hκ hD
  have hbase : ((k - 1 : ℕ) : ℝ) * D * p ^ (k - 2) ≤ (k : ℝ) * D := by
    nlinarith only [h₁, h₂]
  unfold nibbleEdgeSlope
  calc
    _ ≤ ((k : ℝ) * D) * k / g := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg k)) hg.le
    _ = _ := by ring

theorem nibbleEdgeStepBound_nonneg (k : ℕ) {g D L : ℝ}
    (hg : 0 ≤ g) (hD : 0 ≤ D) (hL : 0 ≤ L) : 0 ≤ nibbleEdgeStepBound k g D L := by
  unfold nibbleEdgeStepBound
  positivity

theorem NibbleComparisonParameters.edge_increment_scale_le {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) {p δ : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hδ : |δ| ≤ 2 * nibbleEdgeSlope k g D p) :
    (k : ℝ) * L + |δ| ≤ nibbleEdgeStepBound k g D L := by
  have hmain := nibbleEdgeSlope_le k P.graph_pos P.degree_pos.le
    (P.floor_pos.trans_le hp).le hp1
  unfold nibbleEdgeStepBound
  apply add_le_add le_rfl
  calc
    _ ≤ 2 * nibbleEdgeSlope k g D p := hδ
    _ ≤ 2 * ((k : ℝ) ^ 2 * D / g) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = _ := by ring

theorem NibbleComparisonParameters.edge_average_loss_le {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) {p x h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1)
    (hx : x ≤ nibbleDegreeMain k D p + nibbleDegreeError k a D p)
    (hhalf : nibbleCliqueMain k g D p / 2 ≤ h) :
    (x / h) * ((k - 1 : ℕ) : ℝ) *
      (nibbleDegreeMain k D p + nibbleDegreeError k a D p) ≤ 8 * nibbleEdgeSlope k g D p := by
  have hp0 := P.floor_pos.trans_le hp
  obtain ⟨hm, hu, _, _, _, hum, _, hh₀, _, _, _⟩ := P.edge_conditions hp hp1
  have hh := (half_pos hh₀).trans_le hhalf
  have hdegree : nibbleDegreeMain k D p + nibbleDegreeError k a D p ≤
      2 * nibbleDegreeMain k D p := by linarith only [hum]
  have hprod := mul_le_mul (hx.trans hdegree) hdegree (add_nonneg hm.le hu)
    (mul_nonneg (by norm_num) hm.le)
  have hprod' := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _)
  have hN := mul_le_mul_of_nonneg_right hprod' hh₀.le
  have hh' := mul_le_mul_of_nonneg_left hhalf
    (mul_nonneg (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _) (sq_nonneg (nibbleDegreeMain k D p)))
  rw [nibbleEdgeSlope_eq_main_ratio (by have h := P.rank; omega)
    P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
  calc
    _ = (x * ((k - 1 : ℕ) : ℝ) *
        (nibbleDegreeMain k D p + nibbleDegreeError k a D p)) / h := by ring
    _ ≤ (8 * ((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p ^ 2) /
        nibbleCliqueMain k g D p := by
      apply (div_le_div_iff₀ hh hh₀).mpr
      nlinarith only [hN, hh']
    _ = _ := by ring

end Arxiv2411_18291
