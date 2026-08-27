import Arxiv.Arxiv2411_18291.ActiveEliminationBounds
import Arxiv.Arxiv2411_18291.FiniteUniformElimination

/-! # Constructed elimination with a separate bound on its active cliques

The same actual placement controls every subgraph of the pattern. Applying
that simultaneous bound to the near support removes the full exchange size
from the density cost of the cliques that can retain high multiplicity.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

def activeEliminationCoefficient (q r : ℕ) : ℕ :=
  2 * (q - r) + 2 + 16 * (r + 1).factorial * (q.choose (r + 1) - 1) ^ 2

theorem exists_elimination_family_with_active_bound_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (e : Block W (r + 1)) (hpair : IsEliminationPair S N e)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))
    (B : Hypergraph (Fin n) (r + 1)) (hB : IsGraphBounded B θ)
    (J : Type) [Fintype J] (P Q : J → Block (Fin n) q)
    (hsupport : ∀ i, cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) ⊆ B)
    (hP : ∀ T : Block (Fin n) r, (familyDegree P T.val : ℝ) < θ * n)
    (hQ : ∀ T : Block (Fin n) r, (familyDegree Q T.val : ℝ) < θ * n)
    (hinter : ∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) :
    ∃ F : EliminationFamily S N B P Q (θ + S.graph.card * (4 * (r + 1).factorial * θ)),
      IsGraphBounded F.activeGraph
        (θ + (2 * (q.choose (r + 1) - 1) ^ 2 : ℕ) *
          (4 * (r + 1).factorial * θ)) ∧
      IsCliqueFamilyBounded r F.activeCliques (activeEliminationCoefficient q r * θ) := by
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  obtain ⟨F, hsubgraph⟩ := exists_uniform_elimination_family_with_bounds_paper_threshold
    S N e hpair hqr hn hw hS hlo hhi B hB J P Q hsupport hP hQ hinter
  have hG : IsGraphBounded F.activeGraph
      (θ + (2 * (q.choose (r + 1) - 1) ^ 2 : ℕ) *
        (4 * (r + 1).factorial * θ)) := by
    apply (hsubgraph (cliqueSupport (r + 1) (S.eliminationNear N))
      (S.eliminationNear_support_subset N)).mono
    have hc : ((newEdges (S.base.val ∪ N.val)
        (cliqueSupport (r + 1) (S.eliminationNear N))).card : ℝ) ≤
        (2 * (q.choose (r + 1) - 1) ^ 2 : ℕ) := by
      exact_mod_cast S.eliminationNear_newEdges_card_le hpair
    gcongr
  refine ⟨F, hG, ?_⟩
  have hb := F.active_bounded_from_degrees hpair hG
    (fun T => by simpa only [Fintype.card_fin] using (hP T).le)
    (fun T => by simpa only [Fintype.card_fin] using (hQ T).le)
  convert hb using 1
  unfold activeEliminationCoefficient
  push_cast
  ring

end Arxiv2411_18291
