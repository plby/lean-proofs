import Arxiv.Arxiv2411_18291.ExplicitEliminationFamily
import Arxiv.Arxiv2411_18291.TwoStageElimination

/-! # Both cancellation stages under explicit finite density bounds -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r n : ℕ}

theorem exists_first_elimination_paper_threshold (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q)) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * (2 * C * M + 2) : ℕ) : ℝ) *
      (((2 * C * M + 2 : ℕ) : ℝ) * A) ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (F : SplittingFamily S D B C (A * (n : ℝ) ^ (-ρ)))
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M) :
    Nonempty (EliminationFamily T N F.graph F.pairPositive F.pairNegative
      (firstEliminationFactor T C M A * (n : ℝ) ^ (-ρ))) := by
  let K : ℕ := 2 * C * M + 2
  have hK : 0 < K := by dsimp only [K]; omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAK : A ≤ (K : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKreal hAnonneg
  have hKA : 1 ≤ (K : ℝ) * A := hA.trans hAK
  have hD' : IsCliqueFamilyBounded r F.cliques ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) := by
    simpa only [K, mul_assoc] using F.cliques_bounded hmult
  have hB' : IsGraphBounded F.graph ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) :=
    F.bounded.mono (mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  rw [firstEliminationFactor, eliminationFactor_mul]
  exact exists_elimination_family_paper_threshold T N e₀ hpair hqr hn hw hT K hK hKA
    hAb hρ hρhalf F.cliques F.graph hD' hB' F.cliques_support (F.clique_multiplicity hmult)
    F.NearPairs F.pairPositive F.pairNegative F.pairPositive_mem F.pairNegative_mem
    F.near_pair_injective (F.near_pair_inter hA₀)

theorem exists_second_elimination_paper_threshold (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q)) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * (M + 4 * q.choose (r + 1) * M ^ 2 + 2) : ℕ) : ℝ) *
      (((M + 4 * q.choose (r + 1) * M ^ 2 + 2 : ℕ) : ℝ) * A) ≤
        (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1)) (θ : ℝ)
    (F : SplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative (A * (n : ℝ) ^ (-ρ)))
    (L : FurtherEliminationPairs F E)
    (hmult : ∀ f : Block (Fin n) (r + 1), (F.cliques.filter fun Q => f.val ⊆ Q.val).card ≤ M) :
    let K : ℕ := M + 4 * q.choose (r + 1) * M ^ 2 + 2
    Nonempty (EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
      (eliminationFactor T K ((K : ℝ) * A) * (n : ℝ) ^ (-ρ))) := by
  dsimp only
  let K : ℕ := M + 4 * q.choose (r + 1) * M ^ 2 + 2
  have hK : 0 < K := by dsimp only [K]; omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAK : A ≤ (K : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKreal hAnonneg
  have hKA : 1 ≤ (K : ℝ) * A := hA.trans hAK
  have hcommon (i : F.NearPairs) :
      r + 1 ≤ ((F.pairPositive i).val ∩ (F.pairNegative i).val).card := by
    obtain ⟨e, he⟩ := F.near_pair_inter hA₀ i
    rw [he, e.property]
  have hD' : IsCliqueFamilyBounded r (F.cliques ∪ E.cliques)
      ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) := by
    have h := E.union_cliques_bounded hpair F.cliques F.cliques_support
      F.pairPositive_mem F.pairNegative_mem F.near_pair_injective hcommon hmult
    simpa only [K, mul_assoc] using h
  have hB' : IsGraphBounded E.graph ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) :=
    E.bounded.mono (mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  rw [eliminationFactor_mul]
  apply exists_elimination_family_paper_threshold T N e₀ hpair hqr hn hw hT K hK hKA
    hAb hρ hρhalf (F.cliques ∪ E.cliques) E.graph hD' hB'
    (E.union_cliques_support hpair F.cliques F.cliques_support)
    (E.union_cliques_multiplicity hpair F.cliques F.pairPositive_mem F.pairNegative_mem
      F.near_pair_injective hcommon hmult) E.badNegative L.positive (fun i => i.val)
  · intro i
    exact mem_union_left _ (L.positive_mem_cliques i)
  · intro i
    apply mem_union_right
    rw [E.cliques_eq_signs]
    exact mem_union_right _ (mem_sdiff.mp i.property).1
  · exact L.pair_injective
  · intro i
    exact ⟨L.edge i, L.vertex_inter i⟩

/-- The complete two-stage construction has no unspecified size threshold.
The two displayed scalar bounds are its remaining density requirements. -/
theorem exists_two_stage_elimination_paper_threshold (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q)) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A)
    (hfirst : ((q.choose (r + 1) * (2 * C * M + 2) : ℕ) : ℝ) *
      (((2 * C * M + 2 : ℕ) : ℝ) * A) ≤ (4 * q : ℝ) ^ (24 * q))
    (hsecond : let K₀ := 2 * C * M + 2
      let K₁ := K₀ + 4 * q.choose (r + 1) * K₀ ^ 2 + 2
      ((q.choose (r + 1) * K₁ : ℕ) : ℝ) *
        ((K₁ : ℝ) * firstEliminationFactor T C M A) ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (F : SplittingFamily S D B C (A * (n : ℝ) ^ (-ρ)))
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M) :
    ∃ E : EliminationFamily T N F.graph F.pairPositive F.pairNegative
        (firstEliminationFactor T C M A * (n : ℝ) ^ (-ρ)),
      ∃ L : FurtherEliminationPairs F E,
        ∃ G : EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
            (secondEliminationFactor T C M A * (n : ℝ) ^ (-ρ)),
          IsDecomposition (cliqueSupport (r + 1) (finalNegative F E L G))
            (finalNegative F E L G) ∧
          Disjoint (cliqueSupport (r + 1) (finalNegative F E L G)) B ∧
          IsGraphBounded (cliqueSupport (r + 1) (finalNegative F E L G))
            (secondEliminationFactor T C M A * (n : ℝ) ^ (-ρ)) := by
  obtain ⟨E⟩ := exists_first_elimination_paper_threshold S hA₀ T N e₀ hpair hqr hn hw hT
    C M hA hfirst hρ hρhalf D B F hmult
  obtain ⟨L⟩ := exists_further_elimination_pairs F hA₀ E hpair
  obtain ⟨G⟩ := exists_second_elimination_paper_threshold S hA₀ T N e₀ hpair hqr hn hw hT
    C (2 * C * M + 2) (one_le_firstEliminationFactor T C M hA) hsecond hρ hρhalf
    D B (A * (n : ℝ) ^ (-ρ)) F E L (F.clique_multiplicity hmult)
  exact ⟨E, L, G, finalNegative_decomposition F E L G hpair,
    finalNegative_avoids_original F E L G hpair, finalNegative_bounded F E L G hpair⟩

end Arxiv2411_18291
