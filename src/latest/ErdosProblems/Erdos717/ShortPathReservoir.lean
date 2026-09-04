/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The complete natural-number short-path reservoir theorem. -/

import ErdosProblems.Erdos717.ReservoirSubdivision

open Function Set
open SimpleGraph

namespace Erdos717

/-- A parameterized integer form of the short-path reservoir lemma.  The
single arithmetic hypothesis is exactly what the DRC double count consumes;
later real estimates instantiate `X0` and `L`. -/
theorem exists_short_path_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G)
    (X0 L : ℕ)
    (hE : 0 < H.edgeFinset.card)
    (hX0 : 20 ≤ X0) (hLX : 5 * L ≤ X0)
    (harith : ∀ s t e : ℕ,
      s ≤ Fintype.card V → t ≤ Fintype.card V →
      H.edgeFinset.card ≤ 2 * e →
      t * (t * (X0 * X0) + 40 * (s * s * L)) ≤ e * e) :
    ∃ U : Finset V,
      X0 / 5 ≤ U.card ∧ (U : Set V) ⊆ H.support ∧
      ∀ {r : ℕ} (branch : Fin r ↪ V),
        Set.range branch ⊆ (U : Set V) →
        6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
          ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
        Erdos718.ContainsCliqueSubdivision G r := by
  classical
  obtain ⟨B, hBG, hBbip, hBedgesSet⟩ :=
    MaximumCut.exists_bipartite_spanning_subgraph_half_edges H
  let : DecidableRel B.Adj := Classical.decRel B.Adj
  have hBedges : H.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
    rw [Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet,
      Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
    exact hBedgesSet
  have hBEpos : 0 < B.edgeFinset.card := by omega
  obtain ⟨s, t, hst⟩ := hBbip.exists_isBipartiteWith
  let hsfin : s.Finite := Set.toFinite s
  let htfin : t.Finite := Set.toFinite t
  let S : Finset V := hsfin.toFinset
  let T : Finset V := htfin.toFinset
  have hScoe : (S : Set V) = s := hsfin.coe_toFinset
  have hTcoe : (T : Set V) = t := htfin.coe_toFinset
  have hST : B.IsBipartiteWith (S : Set V) (T : Set V) := by
    simpa only [hScoe, hTcoe] using hst
  have hScard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hTcard : T.card ≤ Fintype.card V := Finset.card_le_univ T
  have hlarge : T.card *
      (T.card * (X0 * X0) + 40 * (S.card * S.card * L)) ≤
        B.edgeFinset.card * B.edgeFinset.card :=
    harith S.card T.card B.edgeFinset.card hScard hTcard hBedges
  obtain ⟨X, hXS, hXsupport, hXcard, hfew⟩ :=
    exists_neighborhood_with_few_bad_pairs B S T hST X0 L hBEpos hlarge
  have hXpos : 0 < X.card := by omega
  obtain ⟨U, hUX, hUcard, hclean⟩ :=
    exists_clean_reservoir_subset B X T L hXpos hfew
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUcard]
    omega
  · intro x hx
    rw [H.mem_support]
    have hxB : x ∈ B.support := hXsupport (hUX hx)
    obtain ⟨y, hxy⟩ := B.mem_support.mp hxB
    exact ⟨y, hBG hxy⟩
  · intro r branch hbranch hmissing
    exact containsCliqueSubdivision_of_clean_reservoir B G (hBG.trans hHG) S T X U L hST
      hXS hUX (by omega) (by omega) hUcard hclean branch hbranch hmissing

end Erdos717
