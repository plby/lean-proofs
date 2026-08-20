/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Combining the short-path reservoir with the nearly-complete-set lemma. -/

import ErdosProblems.Erdos717.NearlyComplete

open Function Set
open SimpleGraph

namespace Erdos717

private def branchPairEmbedding {V : Type*} {r : ℕ} (branch : Fin r ↪ V) :
    Erdos718.CliqueEdge r ↪ V × V where
  toFun e := (branch e.1.1, branch e.1.2)
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext
    · exact branch.injective (congrArg Prod.fst hef)
    · exact branch.injective (congrArg Prod.snd hef)

theorem missing_cliqueEdge_card_le_ordered
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (branch : Fin r ↪ V) (T : Finset V)
    (hbranch : Set.range branch ⊆ (T : Set V)) :
    (Finset.univ.filter fun e : Erdos718.CliqueEdge r =>
      ¬G.Adj (branch e.1.1) (branch e.1.2)).card ≤
        (missingOrderedPairs G T).card := by
  classical
  let E := Finset.univ.filter fun e : Erdos718.CliqueEdge r =>
    ¬G.Adj (branch e.1.1) (branch e.1.2)
  apply Finset.card_le_card_of_injOn
      (fun e : Erdos718.CliqueEdge r => (branch e.1.1, branch e.1.2))
  · intro e he
    have hne : branch e.1.1 ≠ branch e.1.2 := by
      intro h
      exact (ne_of_lt e.2) (branch.injective h)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hne, ?_⟩
    · exact hbranch ⟨e.1.1, rfl⟩
    · exact hbranch ⟨e.1.2, rfl⟩
    · exact (Finset.mem_filter.mp he).2
  · exact (branchPairEmbedding branch).injective.injOn

/-- Turn a routing reservoir and a local independence bound into a large
topological clique.  This is the reusable combinatorial heart of both the
dense and sparse cases. -/
theorem exists_large_cliqueSubdivision_of_local_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (X0 L R a : ℕ)
    (hUcard : X0 / 5 ≤ U.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (hR : 1 ≤ R) (ha : 1 ≤ a) (hind : IndepBoundOn G U a)
    (hroute : ∀ t : ℕ, t ≤ U.card →
      6 * (t * t) + 2 * R ≤ L * R) :
    ∃ r : ℕ, Erdos718.ContainsCliqueSubdivision G r ∧
      X0 / 5 ≤ R ^ (a - 1) * r := by
  classical
  have haeq : a - 1 + 1 = a := by omega
  obtain ⟨T, hTU, hUT, hmissingOrdered⟩ :=
    exists_nearly_complete_subset_aux G U R (a - 1) hR (by
      simpa only [haeq] using hind)
  let enum : T ≃ Fin T.card := T.equivFinOfCardEq rfl
  let branch : Fin T.card ↪ V := enum.symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩
  have hbranch (i : Fin T.card) : branch i ∈ T := by
    exact (enum.symm i).property
  have hrange : Set.range branch ⊆ (U : Set V) := by
    rintro _ ⟨i, rfl⟩
    exact hTU (hbranch i)
  let missing := Finset.univ.filter fun e : Erdos718.CliqueEdge T.card =>
    ¬G.Adj (branch e.1.1) (branch e.1.2)
  have hmissingLe : missing.card ≤ (missingOrderedPairs G T).card := by
    apply missing_cliqueEdge_card_le_ordered G branch T
    rintro _ ⟨i, rfl⟩
    exact hbranch i
  have hmulMissing : R * missing.card ≤ T.card * T.card :=
    (Nat.mul_le_mul_left R hmissingLe).trans hmissingOrdered
  have hrouteT := hroute T.card (Finset.card_le_card hTU)
  have hrouteMissing : 6 * missing.card + 2 ≤ L := by
    have hscaled : R * (6 * missing.card + 2) ≤ R * L := by
      calc
        R * (6 * missing.card + 2) = 6 * (R * missing.card) + 2 * R := by ring
        _ ≤ 6 * (T.card * T.card) + 2 * R := by omega
        _ ≤ L * R := hrouteT
        _ = R * L := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  refine ⟨T.card, ?_, ?_⟩
  · apply hreservoir branch hrange
    exact hrouteMissing
  · exact hUcard.trans hUT

/-- A numerical wrapper around the two structural lemmas.  It deliberately
uses only natural-number inequalities: the later analytic argument is thus
separated from all graph and routing bookkeeping. -/
theorem exists_large_cliqueSubdivision_of_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X0 L R a : ℕ)
    (hE : 0 < G.edgeFinset.card)
    (hX0 : 20 ≤ X0) (hLX : 5 * L ≤ X0)
    (harith : ∀ s t e : ℕ,
      s ≤ Fintype.card V → t ≤ Fintype.card V →
      G.edgeFinset.card ≤ 2 * e →
      t * (t * (X0 * X0) + 40 * (s * s * L)) ≤ e * e)
    (hR : 1 ≤ R) (ha : 1 ≤ a) (hind : G.indepNum ≤ a)
    (hroute : ∀ t : ℕ, t ≤ Fintype.card V →
      6 * (t * t) + 2 * R ≤ L * R) :
    ∃ r : ℕ, Erdos718.ContainsCliqueSubdivision G r ∧
      X0 / 5 ≤ R ^ (a - 1) * r := by
  classical
  obtain ⟨U, hUcard, _hUsupport, hreservoir⟩ :=
    exists_short_path_reservoir G G le_rfl X0 L hE hX0 hLX harith
  apply exists_large_cliqueSubdivision_of_local_reservoir G U X0 L R a
    hUcard hreservoir hR ha
  exact indepBoundOn_of_indepNum_le hind
  intro t ht
  exact hroute t (ht.trans (Finset.card_le_univ U))

end Erdos717
