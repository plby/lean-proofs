import ErdosProblems.Erdos556.ReservoirDensity
import ErdosProblems.Erdos556.BipartiteCore
import ErdosProblems.Erdos556.SurvivingCore

/-!
# The density dichotomy for a highly connected induced core

Either nonbipartiteness survives a small deletion, and the parity reservoir
applies, or a small deletion exposes a bipartite core. The two previously
proved density bounds give one uniform estimate in both cases.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_uniform_core_density_bound (D B : ℕ) (hD : 0 < D) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (b d k : ℕ),
      TwoConnected G → ¬ G.Colorable 2 → N₀ + (b + 3 * D + 3) + 2 ≤ S.card →
      ConnectedAfterDeleting (G.induce (S : Set V)) (2 * (b + 3 * D + 3)) →
      (∀ w : S, d + 2 * (b + 3 * D + 3) ≤ (G.induce (S : Set V)).degree w) →
      S.card ≤ D * d → S.card ≤ B * b → 1 ≤ k →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ((G.induce (S : Set V)).edgeFinset.card : ℝ) ≤
        (k : ℝ) * S.card + 2 * q * (S.card : ℝ) ^ 2 + (b + 3 * D + 5 : ℕ) * (S.card : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := exists_uniform_robust_odd_cycle_density_bound D B hB q hq0 hq1
  obtain ⟨N₂, hN₂⟩ := exists_uniform_bipartite_core_density_bound D B hD hB q hq0 hq1
  refine ⟨max N₁ N₂, ?_⟩
  intro V _ _ G _ S b d k hG hnb hN hc hg hd hb hk ho
  classical
  let J := G.induce (S : Set V)
  let t := b + 3 * D + 3
  have hScard : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hoJ (w : (S : Set V)) (c : J.Walk w w) (hcyc : c.IsCycle) (hodd : Odd c.length) :
      c.length ≤ 2 * k := by
    let f : J ↪g G := SimpleGraph.Embedding.induce (S : Set V)
    have h := ho (f w) (c.map f.toHom) (hcyc.map f.injective)
      (by simpa only [Walk.length_map] using hodd)
    simpa only [Walk.length_map] using h
  by_cases hrobust : NonbipartiteAfterDeleting J t
  · have hg' (w : (S : Set V)) : d + (b + 3 * D + 3) ≤ J.degree w := by
      have h := hg w
      change d + 2 * (b + 3 * D + 3) ≤ J.degree w at h
      omega
    have hcore := hN₁ J b d k (by rw [hScard]; omega) (hc.mono (by omega))
      hrobust hg' (by simpa only [hScard] using hd) (by simpa only [hScard] using hb) hk hoJ
    rw [hScard] at hcore
    have hnonneg : (0 : ℝ) ≤ (b + 3 * D + 5 : ℕ) * (S.card : ℝ) := by positivity
    exact hcore.trans (le_add_of_nonneg_right hnonneg)
  · obtain ⟨T, hT, hcol⟩ : ∃ T : Finset (S : Set V), T.card ≤ t ∧
        (J.induce (T : Set (S : Set V))ᶜ).Colorable 2 := by
      simpa only [NonbipartiteAfterDeleting, not_forall, not_not, exists_prop] using hrobust
    let K := survivingCore S T
    let H := J.induce (T : Set (S : Set V))ᶜ
    let e : H ≃g G.induce (K : Set V) := induceSurvivingCoreIso G S T
    have hK : K.card = S.card - T.card := card_survivingCore S T
    have hKle : K.card ≤ S.card := by omega
    have hKcard : Fintype.card (K : Set V) = K.card := by
      calc
        Fintype.card (K : Set V) = (K : Set V).ncard := Nat.card_eq_fintype_card.symm
        _ = K.card := Set.ncard_coe_finset K
    have hHC : ConnectedAfterDeleting H b :=
      (hc.mono (show b + t ≤ 2 * (b + 3 * D + 3) by dsimp [t]; omega)).induce_compl T hT
    have hHD (w : ↥((T : Set (S : Set V))ᶜ)) : d + b ≤ H.degree w := by
      have h := degree_le_induce_compl_degree_add_card J T w
      have hdeg := hg w.val
      change d + 2 * (b + 3 * D + 3) ≤ J.degree w.val at hdeg
      change J.degree w.val ≤ H.degree w + T.card at h
      dsimp [t] at hT
      omega
    have hKD (v : (K : Set V)) : d + b ≤ (G.induce (K : Set V)).degree v := by
      calc
        d + b ≤ H.degree (e.symm v) := hHD _
        _ = (G.induce (K : Set V)).degree v := by rw [← e.degree_eq, e.apply_symm_apply]
    have hcolK : (G.induce (K : Set V)).Colorable 2 := hcol.of_hom e.symm.toHom
    have hcore := hN₂ G K b d k hG hnb (by dsimp [t] at hT; omega)
      (by rw [hKcard]; dsimp [t] at hT; omega) (hHC.iso e) hKD
      (by rw [hKcard]; omega) (by rw [hKcard]; omega) hk hcolK ho
    rw [hKcard] at hcore
    have hKL : (K.card : ℝ) ≤ S.card := by exact_mod_cast hKle
    have hmain : (k : ℝ) * K.card + 2 * q * (K.card : ℝ) ^ 2 + 2 * K.card ≤
        (k : ℝ) * S.card + 2 * q * (S.card : ℝ) ^ 2 + 2 * S.card := by
      gcongr
    have hdel := edge_count_le_induce_compl_add_card_mul J T
    change J.edgeFinset.card ≤ H.edgeFinset.card + T.card * Fintype.card (S : Set V) at hdel
    rw [e.card_edgeFinset_eq, hScard] at hdel
    have hdelR : (J.edgeFinset.card : ℝ) ≤ ((G.induce (K : Set V)).edgeFinset.card : ℝ) +
        (T.card : ℝ) * S.card := by exact_mod_cast hdel
    have hTR : (T.card : ℝ) ≤ (b + 3 * D + 3 : ℕ) := by exact_mod_cast hT
    have hmul := mul_le_mul_of_nonneg_right hTR (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
    push_cast at hmul ⊢
    nlinarith

#print axioms exists_uniform_core_density_bound

end Erdos556
