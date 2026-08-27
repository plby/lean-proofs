import Arxiv.Arxiv2411_18291.NibbleEndConditions

/-! # Polynomial margin conditions implying a common concentration exponent -/

namespace Arxiv2411_18291

structure NibbleExponentConditions (k d : ℕ) (a g D n L ξ cg : ℝ) : Prop where
  graph_constant_pos : 0 < cg
  count_margin : 16 * (132 * (k : ℝ) ^ 3) ^ 2 * ξ ≤ a ^ 6 * g
  edge_codegree_margin : 176 * (k : ℝ) ^ 3 * ξ * L ≤ a ^ 4 * D
  edge_graph_margin : 352 * (k : ℝ) ^ 4 * ξ ≤ a ^ 4 * g
  face_margin : 8 * (4 * (d : ℝ) * (1 + 128 * (k : ℝ)) * k +
    ((d : ℝ) + k / cg)) * ξ ≤ a ^ 2 * n
  graph_linear : cg * n ≤ g

namespace NibbleExponentConditions

variable {k d : ℕ} {a g D n L ξ cg : ℝ}
variable (S : NibbleExponentConditions k d a g D n L ξ cg)

include S

theorem count_ratio (hk : 0 < k) : ξ ≤ a ^ 6 * g / (16 * (132 * (k : ℝ) ^ 3) ^ 2) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ (by positivity : 0 < 16 * (132 * (k : ℝ) ^ 3) ^ 2)).mpr
  simpa only [mul_comm] using S.count_margin

theorem edge_ratio (hk : 0 < k) (hg : 0 < g) (hD : 0 < D) (hL : 0 ≤ L) :
    ξ ≤ a ^ 4 * D / (88 * (k : ℝ) ^ 2 * nibbleEdgeStepBound k g D L) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hB : 0 < nibbleEdgeStepBound k g D L := by unfold nibbleEdgeStepBound; positivity
  have hfirst : 2 * (88 * (k : ℝ) ^ 2 * ξ) * ((k : ℝ) * L) ≤ a ^ 4 * D := by
    calc
      _ = 176 * (k : ℝ) ^ 3 * ξ * L := by ring
      _ ≤ _ := S.edge_codegree_margin
  have hsecond : 2 * (88 * (k : ℝ) ^ 2 * ξ) * (2 * (k : ℝ) ^ 2 * D / g) ≤ a ^ 4 * D := by
    calc
      _ = (352 * (k : ℝ) ^ 4 * ξ) * (D / g) := by ring
      _ ≤ (a ^ 4 * g) * (D / g) :=
        mul_le_mul_of_nonneg_right S.edge_graph_margin (div_nonneg hD.le hg.le)
      _ = _ := by field_simp
  apply (le_div_iff₀ (by positivity : 0 < 88 * (k : ℝ) ^ 2 * nibbleEdgeStepBound k g D L)).mpr
  unfold nibbleEdgeStepBound
  nlinarith only [hfirst, hsecond]

theorem face_step (hg : 0 < g) : (d : ℝ) + (k : ℝ) * n / g ≤ (d : ℝ) + k / cg := by
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ hg S.graph_constant_pos).mpr
  have h := mul_le_mul_of_nonneg_left S.graph_linear (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith only [h]

theorem face_ratio (hk : 0 < k) :
    ξ ≤ a ^ 2 * n /
      (8 * (4 * (d : ℝ) * (1 + 128 * (k : ℝ)) * k + ((d : ℝ) + k / cg))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hcg := S.graph_constant_pos
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using S.face_margin

end NibbleExponentConditions

end Arxiv2411_18291
