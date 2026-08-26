import ErdosProblems.Erdos556.TwoColourDenseCores
import ErdosProblems.Erdos556.TwoCoreCycles
import ErdosProblems.Erdos556.TwoCoreParameters

/-!
# Long cycles in a two-colouring near twice the target order

For sufficiently large `L`, every two-colouring on at least
`4L - L/100000` vertices has a monochromatic cycle of length at least `2L`.
The proof uses the pruned cores, cleans them, and applies closure absorption.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_uniform_two_colour_long_cycle_contradiction (B : ℕ) (hB : 0 < B) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L b : ℕ),
      N₀ ≤ L → 1 ≤ b → 100000 * b ≤ L →
      4 * L ≤ Fintype.card V + b → Fintype.card V ≤ 4 * L → Fintype.card V ≤ B * b →
      NoLongCycles G (2 * L) → NoLongCycles Gᶜ (2 * L) → False := by
  obtain ⟨N₁, hN₁⟩ := exists_uniform_two_colour_dense_cores B hB
  refine ⟨max N₁ 200, ?_⟩
  intro V _ _ G _ L b hlarge hb hsmall hNlo hNhi hbudget hG hGc
  classical
  obtain ⟨S, T, hSlo, hShi, hTlo, hThi, hSmiss, hTmiss⟩ :=
    hN₁ G L b (by omega) (by omega) hb (by omega) hNlo hNhi hbudget hG hGc
  obtain ⟨hr, hrt, hloss, hlargeA, hroom, hsum⟩ := two_core_parameters L b (by omega) hb hsmall
  have hSm : 2 * (Gᶜ.induce (S : Set V)).edgeFinset.card ≤ 24 * b * L := by
    exact_mod_cast (show 2 * ((Gᶜ.induce (S : Set V)).edgeFinset.card : ℝ) ≤
      24 * (b : ℝ) * L by nlinarith only [hSmiss])
  have hTm : 2 * (G.induce (T : Set V)).edgeFinset.card ≤ 24 * b * L := by
    exact_mod_cast (show 2 * ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤
      24 * (b : ℝ) * L by nlinarith only [hTmiss])
  obtain ⟨A, C, hAS, hCT, hdis, hAc, hCc, hA, hC⟩ :=
    exists_disjoint_dense_cores G S T (L / 100) (L / 10) hr (hSm.trans hrt) (hTm.trans hrt)
  have hAsize : 2 * L - L / 4 ≤ A.card := by omega
  have hCsize : 2 * L - L / 4 ≤ C.card := by omega
  rcases exists_cycle_from_two_dense_cores G A C (2 * L - L / 4) (L / 4) (L / 100 + 1)
      hdis hAsize hCsize hlargeA hroom (by omega) hA hC with
    ⟨v, c, hc, hlen⟩ | ⟨v, c, hc, hlen⟩
  · have h := hG v c hc
    omega
  · have h := hGc v c hc
    omega

theorem exists_uniform_two_colour_long_cycle :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ),
      N₀ ≤ L → 4 * L - L / 100000 ≤ Fintype.card V →
      (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ 2 * L ≤ c.length) ∨
      (∃ (v : V) (c : Gᶜ.Walk v v), c.IsCycle ∧ 2 * L ≤ c.length) := by
  obtain ⟨N₁, hN₁⟩ := exists_uniform_two_colour_long_cycle_contradiction 800000 (by decide)
  refine ⟨max N₁ 200000, ?_⟩
  intro V _ _ G _ L hL hN
  classical
  by_contra hnone
  have hG : NoLongCycles G (2 * L) := by
    intro v c hc
    by_contra! hlen
    exact hnone (Or.inl ⟨v, c, hc, hlen⟩)
  have hGc : NoLongCycles Gᶜ (2 * L) := by
    intro v c hc
    by_contra! hlen
    exact hnone (Or.inr ⟨v, c, hc, hlen⟩)
  obtain ⟨S, _, hSc⟩ := exists_subset_card_eq
    (show 4 * L - L / 100000 ≤ (univ : Finset V).card by simpa using hN)
  have hcard : Fintype.card (S : Set V) = 4 * L - L / 100000 := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
      _ = 4 * L - L / 100000 := hSc
  apply hN₁ (G.induce (S : Set V)) L (L / 100000) (by omega) (by omega) (by omega)
  · rw [hcard]
    omega
  · rw [hcard]
    omega
  · rw [hcard]
    omega
  · exact hG.induce (S : Set V)
  · exact hGc.complement_induce S

#print axioms exists_uniform_two_colour_long_cycle

end Erdos556
