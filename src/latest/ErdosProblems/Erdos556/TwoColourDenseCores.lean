import ErdosProblems.Erdos556.TwoColourPruning
import ErdosProblems.Erdos556.TwoColourCoreArithmetic
import ErdosProblems.Erdos556.ComplementEdgeCounts

/-!
# Two large almost complete cores

At order close to `4L`, a putative two-colouring without a cycle of
length at least `2L` has one large almost complete core in each colour.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_uniform_two_colour_dense_cores (B : ℕ) (hB : 0 < B) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L b : ℕ),
      N₀ ≤ L → 2 ≤ L → 1 ≤ b → b ≤ L →
      4 * L ≤ Fintype.card V + b → Fintype.card V ≤ 4 * L → Fintype.card V ≤ B * b →
      NoLongCycles G (2 * L) → NoLongCycles Gᶜ (2 * L) →
      ∃ S T : Finset V,
        2 * L ≤ S.card + 24 * b ∧ S.card ≤ 2 * L + b ∧
        2 * L ≤ T.card + 24 * b ∧ T.card ≤ 2 * L + b ∧
        ((Gᶜ.induce (S : Set V)).edgeFinset.card : ℝ) ≤ 12 * (b : ℝ) * L ∧
        ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤ 12 * (b : ℝ) * L := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_two_colour_pruned_core 4 B (by decide) hB
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ L b hLlarge hL hb hbL hNlo hNhi hbudget hG hGc
  classical
  have hfloor : L + b + 1 ≤ Fintype.card V := by omega
  obtain ⟨S, hSlo, hShi, heS⟩ := hN₀ G L b hLlarge hL hfloor hNhi hbudget hG hGc
  obtain ⟨T, hTlo, hThi, heT⟩ := hN₀ Gᶜ L b hLlarge hL hfloor hNhi hbudget hGc
    (by simpa only [compl_compl] using hG)
  have hcard (U : Finset V) : Fintype.card (U : Set V) = U.card := by
    calc
      Fintype.card (U : Set V) = (U : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = U.card := Set.ncard_coe_finset U
  have hSe := twice_edge_count_le_order_real (G.induce (S : Set V))
  have hTe := twice_edge_count_le_order_real (Gᶜ.induce (T : Set V))
  rw [hcard S] at hSe
  rw [hcard T] at hTe
  have hNloR : 4 * (L : ℝ) - b ≤ Fintype.card V := by
    have h : 4 * (L : ℝ) ≤ (Fintype.card V : ℝ) + b := by exact_mod_cast hNlo
    linarith
  have heSR : (G.edgeFinset.card : ℝ) - ((L : ℝ) + b) * Fintype.card V ≤
      ((G.induce (S : Set V)).edgeFinset.card : ℝ) - ((L : ℝ) + b) * S.card := by
    simpa only [Nat.cast_add] using heS
  have heTR : (Gᶜ.edgeFinset.card : ℝ) - ((L : ℝ) + b) * Fintype.card V ≤
      ((Gᶜ.induce (T : Set V)).edgeFinset.card : ℝ) - ((L : ℝ) + b) * T.card := by
    simpa only [Nat.cast_add] using heT
  obtain ⟨hs, ht, hmissS, hmissT⟩ := two_colour_core_size_and_missing_edges
    (L : ℝ) b (Fintype.card V) S.card T.card G.edgeFinset.card Gᶜ.edgeFinset.card
    (G.induce (S : Set V)).edgeFinset.card (Gᶜ.induce (T : Set V)).edgeFinset.card
    (by exact_mod_cast (show 0 < L by omega)) (by exact_mod_cast hb)
    hNloR (by exact_mod_cast hNhi) (by exact_mod_cast hSlo) (by exact_mod_cast hShi)
    (by exact_mod_cast hTlo) (by exact_mod_cast hThi)
    (twice_edge_count_add_complement_real G) heSR heTR hSe hTe
  have hsN : 2 * L ≤ S.card + 24 * b := by
    exact_mod_cast (show 2 * (L : ℝ) ≤ (S.card : ℝ) + 24 * b by linarith only [hs])
  have htN : 2 * L ≤ T.card + 24 * b := by
    exact_mod_cast (show 2 * (L : ℝ) ≤ (T.card : ℝ) + 24 * b by linarith only [ht])
  have hisoS : (G.induce (S : Set V))ᶜ ≃g Gᶜ.induce (S : Set V) := by
    rw [complement_induce_eq]
  have hisoT : (Gᶜ.induce (T : Set V))ᶜ ≃g G.induce (T : Set V) := by
    rw [complement_induce_eq, compl_compl]
  have hcountS := twice_edge_count_add_complement_real (G.induce (S : Set V))
  have hcountT := twice_edge_count_add_complement_real (Gᶜ.induce (T : Set V))
  rw [hisoS.card_edgeFinset_eq, hcard S] at hcountS
  rw [hisoT.card_edgeFinset_eq, hcard T] at hcountT
  exact ⟨S, T, hsN, hShi, htN, hThi, by nlinarith only [hcountS, hmissS],
    by nlinarith only [hcountT, hmissT]⟩

#print axioms exists_uniform_two_colour_dense_cores

end Erdos556
