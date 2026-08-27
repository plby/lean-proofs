import Arxiv.Arxiv2411_18291.NibbleControlScales

/-! # Each increment fits inside half its critical interval -/

namespace Arxiv2411_18291

open CliqueRemovalProcess

theorem nibbleCountStepBound_le {k : ℕ} (hk : 0 < k) {D : ℝ} (hD : 0 ≤ D) :
    nibbleCountStepBound k D ≤ 132 * (k : ℝ) ^ 3 * D := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk']
  have hk3 := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg k)
  have h := mul_le_mul_of_nonneg_right hk3 hD
  unfold nibbleCountStepBound
  nlinarith only [h]

namespace NibbleComparisonParameters

variable {k : ℕ} {a g D p₀ L : ℝ} (P : NibbleComparisonParameters k a g D p₀ L)

include P

theorem edge_step_half_width : nibbleEdgeStepBound k g D L ≤ a ^ 2 * D / 2 := by
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hkprod := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg k)
  have hcoef : 4 * (k : ℝ) ≤ (k : ℝ) ^ 2 + k := by nlinarith only [hkprod]
  have hL := mul_le_mul_of_nonneg_right hcoef P.codegree_nonneg
  have hcode := P.codegree_bound
  have hfirst : (k : ℝ) * L ≤ a ^ 2 * D / 4 := by nlinarith only [hL, hcode]
  have hcoef' : 8 * (k : ℝ) ^ 2 ≤ 16 * (k : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left (by linarith only [hk] : (1 : ℝ) ≤ 2 * k)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg (k : ℝ)))
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_right (hcoef'.trans P.many_edges) P.degree_pos.le
  have hsecond : 2 * (k : ℝ) ^ 2 * D / g ≤ a ^ 2 * D / 4 := by
    apply (div_le_iff₀ P.graph_pos).mpr
    nlinarith only [hmul]
  unfold nibbleEdgeStepBound
  linarith only [hfirst, hsecond]

theorem density_step_le_error_quarter : (k : ℝ) / g ≤ a / 4 := by
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk]
  have hk3 := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg k)
  have hk3n : (0 : ℝ) ≤ (k : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
  have hcoef : 4 * (k : ℝ) ≤ 16 * (k : ℝ) ^ 3 := by nlinarith only [hk3, hk3n]
  have ha1 : a ≤ 1 := P.error_half.trans (by norm_num)
  have ha2 : a ^ 2 ≤ a := by
    have h := mul_le_mul_of_nonneg_left ha1 P.error_pos.le
    nlinarith only [h]
  have hlarge := (hcoef.trans P.many_edges).trans
    (mul_le_mul_of_nonneg_right ha2 P.graph_pos.le)
  apply (div_le_iff₀ P.graph_pos).mpr
  nlinarith only [hlarge]

theorem face_step_half_width {n d : ℝ} (hn : 0 ≤ n) (hwidth : 4 * d ≤ a * n) :
    d + (k : ℝ) * n / g ≤ a * n / 2 := by
  have h := mul_le_mul_of_nonneg_right P.density_step_le_error_quarter hn
  calc
    _ = d + ((k : ℝ) / g) * n := by ring
    _ ≤ d + (a / 4) * n := add_le_add le_rfl h
    _ ≤ _ := by nlinarith only [hwidth]

theorem count_step_half_width (hlarge : 264 * (k : ℝ) ^ 3 ≤ a ^ 3 * g) :
    nibbleCountStepBound k D ≤ a ^ 3 * D * g / 2 := by
  have hk : 0 < k := by have h := P.rank; omega
  have hb := nibbleCountStepBound_le hk P.degree_pos.le
  have h := mul_le_mul_of_nonneg_right hlarge P.degree_pos.le
  nlinarith only [hb, h]

end NibbleComparisonParameters

end Arxiv2411_18291
