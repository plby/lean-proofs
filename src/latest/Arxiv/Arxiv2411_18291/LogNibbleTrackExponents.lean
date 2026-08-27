import Arxiv.Arxiv2411_18291.LogNibbleEndConditions
import Arxiv.Arxiv2411_18291.NibbleTrackExponents

/-! # The existing concentration exponents apply to logarithmic tracking -/

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}

variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
variable (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (R : LogNibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) (q - r))

include hqr P R

theorem log_nibble_count_exponent_ge (b : Bool) (N : ℕ) (hN : (N : ℝ) ≤ G.card) :
    a ^ 6 * G.card / (16 * (132 * (q.choose (r + 1) : ℝ) ^ 3) ^ 2) ≤
      nibbleTrackExponent q G a D N (.inl b) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  have hk' : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast hk
  have hc : (1 : ℝ) ≤ 132 * (q.choose (r + 1) : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (q.choose (r + 1) : ℝ) ^ 3 := one_le_pow₀ hk'
    linarith only [hpow]
  exact count_criticalExponent_ge P.error_pos.le (P.error_le_one)
    P.graph_pos P.degree_pos hc (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inl b))
    (nibbleCountStepBound_le hk P.degree_pos.le) (log_nibble_all_half_widths G P R (.inl b))
    (Nat.cast_nonneg _) hN

theorem log_nibble_edge_exponent_ge (e : Block V (r + 1)) (b : Bool) (N : ℕ)
    (hN : (N : ℝ) ≤ G.card) :
    a ^ 4 * D / (88 * (q.choose (r + 1) : ℝ) ^ 2 *
      nibbleEdgeStepBound (q.choose (r + 1)) G.card D
        ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1))) ≤
      nibbleTrackExponent q G a D N (.inr (.inl (e, b))) := by
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by
    exact_mod_cast (show 1 ≤ q.choose (r + 1) by have h := P.rank; omega)
  exact edge_criticalExponent_ge P.error_pos.le (P.error_le_one)
    P.graph_pos P.degree_pos hk
    (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inr (.inl (e, b))))
    (log_nibble_all_half_widths G P R (.inr (.inl (e, b)))) (Nat.cast_nonneg _) hN

theorem log_nibble_face_exponent_ge (f : Block V r) (N : ℕ) (hN : (N : ℝ) ≤ G.card)
    {cb : ℝ} (hcb : ((q - r : ℕ) : ℝ) +
      (q.choose (r + 1) : ℝ) * Fintype.card V / G.card ≤ cb) :
    a ^ 2 * Fintype.card V /
      (8 * (4 * ((q - r : ℕ) : ℝ) * (1 + 128 * (q.choose (r + 1) : ℝ)) *
        q.choose (r + 1) + cb)) ≤ nibbleTrackExponent q G a D N (.inr (.inr f)) := by
  exact face_criticalExponent_ge (P.error_le_one) P.graph_pos
    (vertex_card_pos_of_graph_pos G P.graph_pos) (by positivity)
    (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inr (.inr f))) hcb
    (log_nibble_all_half_widths G P R (.inr (.inr f))) (Nat.cast_nonneg _) hN

end Arxiv2411_18291.CliqueRemovalProcess
