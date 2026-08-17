import ErdosProblems.Erdos127.CriticalClique

open scoped ENat
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- For a finite graph, `chromaticNumber.toNat` is its actual chromatic
number and admits a surjective optimal coloring. -/
lemma exists_optimal_coloring_toNat (G : SimpleGraph V) :
    let q := ENat.toNat G.chromaticNumber
    ∃ C : G.Coloring (Fin q), G.chromaticNumber = q ∧ Function.Surjective C := by
  let q := ENat.toNat G.chromaticNumber
  have hcol : G.Colorable q := colorable_chromaticNumber_of_fintype G
  have hne : G.chromaticNumber ≠ ⊤ :=
    (hcol.chromaticNumber_le.trans_lt (ENat.natCast_lt_top q)).ne
  have hχ : G.chromaticNumber = q :=
    (ENat.natCast_toNat_eq_self.mpr hne).symm
  let C : G.Coloring (Fin q) := hcol.some
  have hqχ : Fintype.card (Fin q) ≤ G.chromaticNumber := by simp [hχ]
  exact ⟨C, hχ, card_le_chromaticNumber_iff_forall_surjective.mp hqχ C⟩

/-- An induced subgraph has no more edges than the original graph. -/
lemma card_edgeFinset_induce_le (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)] :
    (G.induce s).edgeFinset.card ≤ G.edgeFinset.card := by
  have h := congrArg Finset.card (G.map_edgeFinset_induce (s := s))
  rw [Finset.card_map] at h
  rw [h]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Instance-independent edge-count monotonicity for induced subgraphs. -/
lemma ncard_edgeSet_induce_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).edgeSet.ncard ≤ G.edgeSet.ncard := by
  let f : Sym2 s ↪ Sym2 V := (Function.Embedding.subtype (· ∈ s)).sym2Map
  have hmaps : f '' (G.induce s).edgeSet ⊆ G.edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.inductionOn with
    | _ u v => simpa [f, SimpleGraph.mem_edgeSet] using he
  calc
    (G.induce s).edgeSet.ncard = (f '' (G.induce s).edgeSet).ncard :=
      (Set.ncard_image_of_injective _ f.injective).symm
    _ ≤ G.edgeSet.ncard := Set.ncard_le_ncard hmaps

/-- The standard critical-subgraph argument gives the quadratic lower bound
on the edge count in terms of the finite chromatic number. -/
lemma chromatic_toNat_mul_pred_le_twice_card_edges
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hedge : G.edgeFinset.Nonempty) :
    let q := ENat.toNat G.chromaticNumber
    q * (q - 1) ≤ 2 * G.edgeFinset.card := by
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, -⟩ := exists_optimal_coloring_toNat G
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2q : 2 ≤ q := by
    have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
      two_le_chromaticNumber_iff_ne_bot.mpr hnebot
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  obtain ⟨s, hsχ, _, _, hhand, _⟩ :=
    exists_induced_critical_with_handshake_and_clique G q (by omega) hχ
  have hqcard : q ≤ Fintype.card s := by
    have h := (G.induce (s : Set V)).chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hhand' : Fintype.card s * (q - 1) ≤
      2 * (G.induce (s : Set V)).edgeSet.ncard := by
    simpa [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] using hhand
  have hHedge : (G.induce (s : Set V)).edgeSet.ncard ≤ G.edgeSet.ncard :=
    ncard_edgeSet_induce_le G (s : Set V)
  have hGcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  calc
    q * (q - 1) ≤ Fintype.card s * (q - 1) :=
      Nat.mul_le_mul_right (q - 1) hqcard
    _ ≤ 2 * (G.induce (s : Set V)).edgeSet.ncard := hhand'
    _ ≤ 2 * G.edgeSet.ncard := Nat.mul_le_mul_left 2 hHedge
    _ = 2 * G.edgeFinset.card := by rw [hGcard]

end SimpleGraph
