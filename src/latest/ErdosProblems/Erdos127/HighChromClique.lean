import ErdosProblems.Erdos127.Chromatic
import Mathlib.Tactic

open scoped ENat
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- High chromatic number at the square edge scale forces an explicitly sized
clique.  The edge hypothesis is the division-free form `|E(G)| = N^2 / 2`.
The witness `s` records the critical induced graph used in the proof. -/
lemma exists_exact_clique_of_high_chromatic
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (N L : ℕ) (hN : 0 < N) (hNL : 2 * L ≤ N)
    (hedges : 2 * G.edgeFinset.card = N ^ 2)
    (hhigh : N - L < ENat.toNat G.chromaticNumber) :
    let q := ENat.toNat G.chromaticNumber
    q ≤ N ∧
      ∃ s : Finset V,
        (G.induce (s : Set V)).chromaticNumber = q ∧
        Fintype.card s ≤ N + 2 * L ∧
        ∃ U : Finset V, G.IsClique (U : Set V) ∧ U.card = N - 4 * L := by
  classical
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, -⟩ := exists_optimal_coloring_toNat G
  have hedge : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    nlinarith [sq_pos_of_pos hN]
  have hquad := chromatic_toNat_mul_pred_le_twice_card_edges G hedge
  change q * (q - 1) ≤ 2 * G.edgeFinset.card at hquad
  rw [hedges] at hquad
  have hqN : q ≤ N := by
    by_contra! hNq
    have hpred : N ≤ q - 1 := by omega
    nlinarith
  have hNLpos : 0 < N - L := by omega
  have hqpos : 0 < q := by omega
  obtain ⟨s, hsχ, -, -, hhand, K, hK, hKcard⟩ :=
    exists_induced_critical_with_handshake_and_clique G q hqpos hχ
  let H := G.induce (s : Set V)
  have hHedge : H.edgeFinset.card ≤ G.edgeFinset.card := by
    simpa only [edgeFinset, Set.toFinset_card] using
      Fintype.card_le_of_embedding (Copy.induce G (s : Set V)).mapEdgeSet
  have hhand' : Fintype.card s * (q - 1) ≤ N ^ 2 :=
    hhand.trans ((Nat.mul_le_mul_left 2 hHedge).trans_eq hedges)
  have hqpred : N - L ≤ q - 1 := by omega
  have hsub : N - L + L = N := by omega
  have hsBound : Fintype.card s ≤ N + 2 * L := by
    by_contra! hsLarge
    have hprod : N ^ 2 < Fintype.card s * (q - 1) := by
      nlinarith
    exact (Nat.not_lt_of_ge hhand') hprod
  have hKlarge : N - 4 * L ≤ K.card := by omega
  let W : Finset V := K.map (Function.Embedding.subtype (· ∈ (s : Set V)))
  have hWcard : W.card = K.card := by simp [W]
  have hWclique : G.IsClique (W : Set V) := by
    have himage := (isClique_induce_iff.mp hK)
    simpa [W] using himage
  have htarget : N - 4 * L ≤ W.card := by rw [hWcard]; exact hKlarge
  obtain ⟨U, hUW, hUcard⟩ := W.exists_subset_card_eq htarget
  have hUclique : G.IsClique (U : Set V) :=
    hWclique.subset (by simpa using hUW)
  exact ⟨hqN, s, hsχ, hsBound, U, hUclique, hUcard⟩

end SimpleGraph

