import Arxiv.Arxiv2411_18291.ExplicitReserve
import Arxiv.Arxiv2411_18291.ExplicitCliqueCover

/-! # A coverable reserve at the paper's explicit threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_coverable_reserve_paper_threshold (q r n : ℕ) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let ρ := paperRho q (r + 1)
    ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), Disjoint L R →
        IsGraphBounded L ((n : ℝ) ^ (-(3 * K * ρ))) →
        ∃ Q : L → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q := by
  dsimp only
  obtain ⟨R, hR, hcount⟩ := exists_reserve_paper_threshold q r n hqr hn
  exact ⟨R, hR, fun L hLR hL =>
    exists_clique_cover_paper_threshold hqr hn R L hLR hL (fun e _ => hcount e)⟩

theorem exists_reserve_cover_decompositions_paper_threshold (q r n : ℕ)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let ρ := paperRho q (r + 1)
    ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), Disjoint L R →
        IsGraphBounded L ((n : ℝ) ^ (-(3 * K * ρ))) →
        ∃ G : Hypergraph (Fin n) (r + 1), ∃ D : Finset (Block (Fin n) q),
          L ⊆ G ∧ G ⊆ L ∪ R ∧ IsDecomposition G D ∧ D.card = L.card := by
  dsimp only
  obtain ⟨R, hR, hcover⟩ := exists_coverable_reserve_paper_threshold q r n hqr hn
  refine ⟨R, hR, ?_⟩
  intro L hLR hL
  obtain ⟨Q, hQ⟩ := hcover L hLR hL
  exact hQ.leave_decomposition

end Arxiv2411_18291
