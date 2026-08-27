import Arxiv.Arxiv2411_18291.NibbleEndConditions
import Arxiv.Arxiv2411_18291.NibbleExponentScales

/-! # Lower bounds on the three exponents in the actual failure estimate -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}

def nibbleTrackExponent (q : ℕ) (G : Hypergraph V (r + 1)) (a D : ℝ) (N : ℕ)
    (t : NibbleTrack V r) : ℝ :=
  criticalExponent (nibbleCriticalWidth G a D t) (nibbleStepBound q G D t)
    ((N : ℝ) * nibbleVarianceRate q G D t)

theorem nibbleFailureBound_eq_sum (G : Hypergraph V (r + 1)) (a D : ℝ) (N : ℕ) :
    nibbleFailureBound q G a D N =
      ∑ t : NibbleTrack V r, (N : ℝ) * Real.exp (-nibbleTrackExponent q G a D N t) := rfl

theorem vertex_card_pos_of_graph_pos (G : Hypergraph V (r + 1)) (hg : 0 < (G.card : ℝ)) :
    (0 : ℝ) < Fintype.card V := by
  obtain ⟨e, _⟩ := card_pos.mp (by exact_mod_cast hg : 0 < G.card)
  have hepos : 0 < e.val.card := by rw [e.property]; omega
  exact_mod_cast hepos.trans_le (card_le_univ e.val)

variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
variable (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))

include hqr P R

theorem nibble_count_exponent_ge (b : Bool) (N : ℕ) (hN : (N : ℝ) ≤ G.card) :
    a ^ 6 * G.card / (16 * (132 * (q.choose (r + 1) : ℝ) ^ 3) ^ 2) ≤
      nibbleTrackExponent q G a D N (.inl b) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  have hk' : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast hk
  have hc : (1 : ℝ) ≤ 132 * (q.choose (r + 1) : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (q.choose (r + 1) : ℝ) ^ 3 := one_le_pow₀ hk'
    linarith only [hpow]
  exact count_criticalExponent_ge P.error_pos.le (P.error_half.trans (by norm_num))
    P.graph_pos P.degree_pos hc (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inl b))
    (nibbleCountStepBound_le hk P.degree_pos.le) (nibble_all_half_widths G P R (.inl b))
    (Nat.cast_nonneg _) hN

theorem nibble_edge_exponent_ge (e : Block V (r + 1)) (b : Bool) (N : ℕ)
    (hN : (N : ℝ) ≤ G.card) :
    a ^ 4 * D / (88 * (q.choose (r + 1) : ℝ) ^ 2 *
      nibbleEdgeStepBound (q.choose (r + 1)) G.card D
        ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1))) ≤
      nibbleTrackExponent q G a D N (.inr (.inl (e, b))) := by
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by
    exact_mod_cast (show 1 ≤ q.choose (r + 1) by have h := P.rank; omega)
  exact edge_criticalExponent_ge P.error_pos.le (P.error_half.trans (by norm_num))
    P.graph_pos P.degree_pos hk
    (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inr (.inl (e, b))))
    (nibble_all_half_widths G P R (.inr (.inl (e, b)))) (Nat.cast_nonneg _) hN

theorem nibble_face_exponent_ge (f : Block V r) (N : ℕ) (hN : (N : ℝ) ≤ G.card)
    {cb : ℝ} (hcb : ((q - r : ℕ) : ℝ) +
      (q.choose (r + 1) : ℝ) * Fintype.card V / G.card ≤ cb) :
    a ^ 2 * Fintype.card V /
      (8 * (4 * ((q - r : ℕ) : ℝ) * (1 + 128 * (q.choose (r + 1) : ℝ)) *
        q.choose (r + 1) + cb)) ≤ nibbleTrackExponent q G a D N (.inr (.inr f)) := by
  exact face_criticalExponent_ge (P.error_half.trans (by norm_num)) P.graph_pos
    (vertex_card_pos_of_graph_pos G P.graph_pos) (by positivity)
    (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos (.inr (.inr f))) hcb
    (nibble_all_half_widths G P R (.inr (.inr f))) (Nat.cast_nonneg _) hN

end Arxiv2411_18291.CliqueRemovalProcess
