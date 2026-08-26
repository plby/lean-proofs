import ErdosProblems.Erdos547.RegularityTypical

/-!
# Slicing regular pairs, including trimming one vertex per cluster
-/

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem regular_pair_slicing {δ ε : ℝ} {X Y X' Y' : Finset V}
    (hreg : G.IsUniform δ X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hbaseX : (X.card : ℝ) * δ ≤ X'.card) (hbaseY : (Y.card : ℝ) * δ ≤ Y'.card)
    (hscaleX : (X.card : ℝ) * δ ≤ X'.card * ε)
    (hscaleY : (Y.card : ℝ) * δ ≤ Y'.card * ε) (hε : 2 * δ ≤ ε) :
    G.IsUniform ε X' Y' := by
  intro A hA B hB hAs hBs
  have hlarge := hreg (hA.trans hX) (hB.trans hY) (hscaleX.trans hAs) (hscaleY.trans hBs)
  have hbase := hreg hX hY hbaseX hbaseY
  have hbase' : |(G.edgeDensity X Y : ℝ) - (G.edgeDensity X' Y' : ℝ)| < δ := by
    rwa [abs_sub_comm]
  have htriangle := abs_sub_le (G.edgeDensity A B : ℝ) (G.edgeDensity X Y : ℝ)
    (G.edgeDensity X' Y' : ℝ)
  linarith only [hlarge, hbase', htriangle, hε]

theorem regular_pair_trim_one {δ ε : ℝ} {X Y X' Y' : Finset V}
    (hreg : G.IsUniform δ X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hXcard : X.card ≤ X'.card + 1) (hYcard : Y.card ≤ Y'.card + 1)
    (hXpos : 1 ≤ X'.card) (hYpos : 1 ≤ Y'.card) (hδ : 2 * δ ≤ ε) (hε : ε ≤ 1) :
    G.IsUniform ε X' Y' := by
  have hδ0 := hreg.pos.le
  have hε0 : 0 ≤ ε := by linarith
  have hscale (s t : ℕ) (hcard : s ≤ t + 1) (ht : 1 ≤ t) : (s : ℝ) * δ ≤ t * ε := by
    have hst : (s : ℝ) ≤ 2 * t := by exact_mod_cast (show s ≤ 2 * t by omega)
    have hh := mul_le_mul_of_nonneg_right hst hδ0
    have he := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg t)
    nlinarith only [hh, he]
  have hsX := hscale X.card X'.card hXcard hXpos
  have hsY := hscale Y.card Y'.card hYcard hYpos
  apply regular_pair_slicing G hreg hX hY _ _ hsX hsY hδ
  · exact hsX.trans (by nlinarith only [mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg X'.card)])
  · exact hsY.trans (by nlinarith only [mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg Y'.card)])

end Erdos547

#print axioms Erdos547.regular_pair_slicing
#print axioms Erdos547.regular_pair_trim_one
