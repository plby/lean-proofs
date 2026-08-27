import Arxiv.Arxiv2411_18291.NibbleExponentConditions
import Arxiv.Arxiv2411_18291.NibbleFailurePrefactor

/-! # One exponent controls every track in the nibble failure estimate -/

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}
variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) {a D p₀ ξ cg : ℝ}
variable (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
variable (S : NibbleExponentConditions (q.choose (r + 1)) (q - r) a G.card D (Fintype.card V)
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)) ξ cg)

include hqr P R S

theorem nibble_all_exponents_ge (N : ℕ) (hN : (N : ℝ) ≤ G.card) (t : NibbleTrack V r) :
    ξ ≤ nibbleTrackExponent q G a D N t := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  rcases t with b | (⟨e, b⟩ | f)
  · exact (S.count_ratio hk).trans (nibble_count_exponent_ge hqr G P R b N hN)
  · exact (S.edge_ratio hk P.graph_pos P.degree_pos P.codegree_nonneg).trans
      (nibble_edge_exponent_ge hqr G P R e b N hN)
  · exact (S.face_ratio hk).trans
      (nibble_face_exponent_ge hqr G P R f N hN (S.face_step P.graph_pos))

theorem nibbleFailureBound_le_of_margins (N : ℕ) (hN : (N : ℝ) ≤ G.card) :
    nibbleFailureBound q G a D N ≤
      5 * (Fintype.card V : ℝ) ^ (2 * (r + 1)) * Real.exp (-ξ) := by
  have hn : 1 ≤ Fintype.card V := by exact_mod_cast vertex_card_pos_of_graph_pos G P.graph_pos
  exact nibbleFailureBound_le_polynomial G a D N hn hN (nibble_all_exponents_ge hqr G P R S N hN)

end Arxiv2411_18291.CliqueRemovalProcess
