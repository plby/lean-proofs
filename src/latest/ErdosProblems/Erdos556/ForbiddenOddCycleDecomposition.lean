import ErdosProblems.Erdos556.CycleSpectrum
import ErdosProblems.Erdos556.OddCycleDecomposition
import ErdosProblems.Erdos556.MappedDensity

/-!
# A uniform decomposition from a single forbidden odd cycle

Pruning supplies the degree hypothesis for the cycle-spectrum theorem.
The resulting odd-cycle cutoff permits the bipartite/sparse decomposition,
which is then extended back to the original vertex set.
-/

namespace Erdos556

open SimpleGraph Finset

open scoped Classical in
theorem exists_forbidden_odd_cycle_decomposition (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ),
      n₀ ≤ n → Odd n → n ≤ Fintype.card V → Fintype.card V ≤ 4 * n →
      (¬ cycleGraph n ⊑ G) →
      ∃ (B F : SimpleGraph V) (T : Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v, B.Adj u v → u ∉ T ∧ v ∉ T) ∧
        (∀ u v, F.Adj u v → u ∈ T ∧ v ∈ T) ∧
        (G.edgeFinset.card : ℝ) ≤ B.edgeFinset.card + F.edgeFinset.card +
          ε * (Fintype.card V : ℝ) ^ 2 ∧
        (∀ A : Finset V, ((F.induce (A : Set V)).edgeFinset.card : ℝ) ≤
          ((n : ℝ) / 2 + ε * Fintype.card V) * A.card) := by
  obtain ⟨D, hDreal⟩ := exists_nat_gt (2 / ε)
  have hD : 0 < D := by
    have hp : 0 < 2 / ε := by positivity
    have hpD : 0 < (D : ℝ) := hp.trans hDreal
    exact_mod_cast hpD
  have hDε : 2 ≤ ε * (D : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hDreal
    nlinarith
  obtain ⟨N₁, K, hspec⟩ := exists_odd_cycle_cutoff_of_forbidden_cycle D hD
  obtain ⟨N₂, hdecomp⟩ := exists_odd_cycle_decomposition (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_ge ((K : ℝ) / ε)
  have hKM : (K : ℝ) ≤ ε * M := by
    have h := (div_le_iff₀ hε).mp hM
    nlinarith
  let R := max N₁ N₂
  refine ⟨max (D * (R + 1)) (max K (max M 3)), ?_⟩
  intro V _ _ G _ n hn hodd hnN hNn hno
  classical
  let N := Fintype.card V
  let q := N / D
  have hn3 : 3 ≤ n := by omega
  have hnK : K ≤ n := by omega
  have hKN : (K : ℝ) ≤ ε * N := by
    have hMN : M ≤ N := by omega
    exact hKM.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hε.le)
  have hqN : (D : ℝ) * q ≤ N := by exact_mod_cast (Nat.mul_div_le N D)
  have hqsmall : 2 * (q : ℝ) ≤ ε * N := by
    have h₁ := mul_le_mul_of_nonneg_right hDε (show 0 ≤ (q : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hqN hε.le
    nlinarith only [h₁, h₂]
  have hpruneLoss : (q : ℝ) * N ≤ ε / 2 * (N : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hqsmall (show 0 ≤ (N : ℝ) by positivity)
    nlinarith only [h]
  obtain ⟨S, hprune, hdegree⟩ := exists_induced_core G (q : ℝ)
  have hcardS : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hSN : S.card ≤ N := card_le_univ S
  have hcoreLoss : (G.edgeFinset.card : ℝ) ≤ (G.induce (S : Set V)).edgeFinset.card +
      ε / 2 * (N : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ (q : ℝ) * S.card := by positivity
    change (G.edgeFinset.card : ℝ) - (q : ℝ) * N ≤
      ((G.induce (S : Set V)).edgeFinset.card : ℝ) - (q : ℝ) * S.card at hprune
    linarith
  by_cases hSempty : S = ∅
  · have hezero : (G.induce (S : Set V)).edgeFinset.card = 0 := by
      have h := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
      have hSc : S.card = 0 := by rw [hSempty, card_empty]
      rw [hcardS, hSc] at h
      exact Nat.eq_zero_of_le_zero (by simpa only [Nat.choose_zero_succ] using h)
    rw [hezero, Nat.cast_zero, zero_add] at hcoreLoss
    refine ⟨⊥, ⊥, ∅, bot_le, bot_le, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨{ toFun := fun _ => (0 : Fin 2), map_rel' := fun h => h.elim }⟩
    · intro u v h
      exact h.elim
    · intro u v h
      exact h.elim
    · have hbot : Nat.card (⊥ : SimpleGraph V).edgeSet = 0 := by
        rw [edgeSet_bot]
        simp
      have hnonneg : 0 ≤ ε * (N : ℝ) ^ 2 := by positivity
      have hres : (G.edgeFinset.card : ℝ) ≤ ε * (N : ℝ) ^ 2 := by linarith
      simpa only [edgeFinset_card_eq_natCard_edgeSet, hbot, Nat.cast_zero, zero_add] using hres
    · intro A
      have he : Nat.card (((⊥ : SimpleGraph V).induce (A : Set V)).edgeSet) = 0 := by
        change Nat.card (⊥ : SimpleGraph (A : Set V)).edgeSet = 0
        rw [edgeSet_bot]
        simp
      simpa only [edgeFinset_card_eq_natCard_edgeSet, he, Nat.cast_zero] using
        (show (0 : ℝ) ≤ ((n : ℝ) / 2 + ε * Fintype.card V) * A.card by positivity)
  · have hqR : R + 1 ≤ q := by
      apply (Nat.le_div_iff_mul_le hD).mpr
      have hnR : D * (R + 1) ≤ n := by omega
      exact (by simpa only [Nat.mul_comm] using hnR.trans hnN)
    obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr hSempty
    have hdegNat (v : (S : Set V)) : q + 1 ≤ (G.induce (S : Set V)).degree v := by
      have h : q < (G.induce (S : Set V)).degree v := by exact_mod_cast hdegree v
      omega
    have hSlarge : R ≤ Fintype.card (S : Set V) := by
      have h₁ := hdegNat ⟨s, hs⟩
      have h₂ := (G.induce (S : Set V)).degree_lt_card_verts ⟨s, hs⟩
      omega
    have hscale : Fintype.card (S : Set V) ≤ D * (q + 1) := by
      rw [hcardS]
      exact hSN.trans (Nat.lt_mul_div_succ N hD).le
    have hnoS : ¬ cycleGraph n ⊑ G.induce (S : Set V) := fun h =>
      hno (h.trans (Embedding.induce (S : Set V)).isContained)
    have hcut := hspec (G.induce (S : Set V)) (q + 1) n
      (by dsimp only [R] at hSlarge; omega) hscale hdegNat hn3 hodd hnK hnoS
    let k := (n + K) / 2
    have hkN : Fintype.card (S : Set V) ≤ 16 * k := by
      rw [hcardS]
      have h : 4 * n ≤ 16 * k := by dsimp only [k]; omega
      exact hSN.trans (hNn.trans h)
    have hoddBound (v : (S : Set V)) (w : (G.induce (S : Set V)).Walk v v)
        (hw : w.IsCycle) (ho : Odd w.length) : w.length ≤ 2 * k := by
      have h := hcut v w hw ho
      dsimp only [k]
      omega
    obtain ⟨B, F, T, hBG, hFG, hBcol, hBoff, hFon, hE, hFden⟩ :=
      hdecomp (G.induce (S : Set V)) k (by dsimp only [R] at hSlarge; omega) hkN hoddBound
    let f : (S : Set V) ↪ V := Function.Embedding.subtype _
    have hBmap : B.map f ≤ G := (map_le_iff_le_comap f B G).mpr hBG
    have hFmap : F.map f ≤ G := (map_le_iff_le_comap f F G).mpr hFG
    refine ⟨B.map f, F.map f, T.map f, hBmap, hFmap, hBcol.map f,
      mapped_edges_off_set B f T hBoff, mapped_edges_in_set F f T hFon, ?_, ?_⟩
    · have hBcard := card_edgeFinset_map f B
      have hFcard := card_edgeFinset_map f F
      simp only [edgeFinset_card_eq_natCard_edgeSet] at hBcard hFcard ⊢
      rw [hBcard, hFcard]
      have hSNreal : (S.card : ℝ) ≤ N := by exact_mod_cast hSN
      have hsq : (S.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
      have herror := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε / 2 by positivity)
      rw [hcardS] at hE
      simp only [edgeFinset_card_eq_natCard_edgeSet] at hE hcoreLoss
      change (Nat.card G.edgeSet : ℝ) ≤ (Nat.card B.edgeSet : ℝ) + Nat.card F.edgeSet + ε * (N : ℝ) ^ 2
      linarith
    · have hkReal : 2 * (k : ℝ) ≤ (n : ℝ) + K := by
        exact_mod_cast (show 2 * k ≤ n + K from Nat.mul_div_le (n + K) 2)
      have hSNreal : (Fintype.card (S : Set V) : ℝ) ≤ N := by rw [hcardS]; exact_mod_cast hSN
      have hmul := mul_le_mul_of_nonneg_left hSNreal hε.le
      have hcoef : (k : ℝ) + ε / 2 * Fintype.card (S : Set V) ≤ (n : ℝ) / 2 + ε * N := by
        nlinarith only [hkReal, hKN, hmul]
      have hden := hereditary_density_map_embedding F f
        ((k : ℝ) + ε / 2 * Fintype.card (S : Set V)) (by positivity) hFden
      intro A
      have hres := (hden A).trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
      simpa only [edgeFinset_card_eq_natCard_edgeSet] using hres

#print axioms exists_forbidden_odd_cycle_decomposition

end Erdos556
