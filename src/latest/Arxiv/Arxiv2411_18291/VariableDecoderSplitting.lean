import Arxiv.Arxiv2411_18291.VariableDecoderRepresentation
import Arxiv.Arxiv2411_18291.VariableSplittingFamily

/-! # One variable-capacity splitting family for all generated leaves

The algebraic correction and the actual finite splitting construction now
compose without a uniform edge-multiplicity bound. The weighted decoder
capacity bound and the finite placement inequalities are explicit inputs;
this does not yet establish the source's global design threshold.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_variable_decoder_splitting
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] {q r : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (D : Finset (Block V q)) (B B' : Hypergraph V (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (Z : B → Block V (q + (r + 1)))
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hcapacity : IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
      (edgewiseDecoderCapacity D Z) θ)
    (hB' : IsGraphBounded B' θ)
    (hDB' : cliqueSupport (r + 1) (D ∪ cliqueRefinement q (univ.image Z)) ⊆ B')
    (d : ℕ) (hconflict : (q.choose r : ℝ) * (2 * θ * Fintype.card V) ≤ d)
    (hnpos : 0 < Fintype.card V) (hn : 4 * Fintype.card W ^ 2 ≤ Fintype.card V)
    (hsize : 4 * Fintype.card W * (d * Fintype.card W) ≤ Fintype.card V)
    (hsmall : S.graph.card * (2 * θ + S.graph.card *
      (8 * (r + 1).factorial * (2 * θ))) ≤ 1 / 4)
    (hfailure : S.graph.card * Fintype.card (Block V r) *
      Real.exp (-(4 * (r + 1).factorial * (2 * θ) * Fintype.card V / 3)) < 1) :
    ∃ F : VariableSplittingFamily S (D ∪ cliqueRefinement q (univ.image Z)) B'
        (edgewiseDecoderCapacity D Z) (θ + S.graph.card * (16 * (r + 1).factorial * θ)),
      ∀ L : Hypergraph V (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
        ∃ P N : Finset (Block V q),
          P ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧
          N ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧ Disjoint P N ∧
          boundary (r + 1) (indicator P - indicator N) = indicator L := by
  obtain ⟨F⟩ := exists_variable_splitting_family S hqr.le
    (D ∪ cliqueRefinement q (univ.image Z)) (edgewiseDecoderCapacity D Z) B'
    hθ hcapacity hB' hDB' d hconflict hnpos hn hsize hsmall hfailure
  refine ⟨F, ?_⟩
  intro L hLB hgen
  obtain ⟨Φ, hΦ, hs, hcap⟩ :=
    edgewise_representation_of_local_decoders hqr D B L hDB hLB Z hZ hgen
  obtain ⟨P, N, hP, hN, hdis, hboundary⟩ := F.signed_representation hqr.le Φ hcap hs
  exact ⟨P, N, hP, hN, hdis, hboundary.trans hΦ⟩

end Arxiv2411_18291
