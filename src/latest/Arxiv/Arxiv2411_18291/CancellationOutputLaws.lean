import Arxiv.Arxiv2411_18291.EliminationFamilyProbability
import Arxiv.Arxiv2411_18291.ExplicitEliminationStages

/-!
# Conditional output laws for both cancellation stages

For every successful previous output, the roots can be fixed before the
next trajectory is sampled. The failure bound is uniform over previous
outputs, so these laws can be composed without assuming independence.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r n : ℕ}

theorem exists_first_elimination_output_law (S : ExchangeSystem W q (r + 1))
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
    ∃ Φ : ℕ → ↥(T.base.val ∪ N.val) ↪ Fin n,
      (eliminationFamilyOutputLaw T N F.graph F.pairPositive F.pairNegative Φ
        (firstEliminationFactor T C M A * (n : ℝ) ^ (-ρ)) none).toReal <
          Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
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
  obtain ⟨Φ, _, hp⟩ := exists_elimination_family_output_probability_paper_threshold
    T N e₀ hpair hqr hn hw hT K hK hKA hAb hρ hρhalf
    F.cliques F.graph hD' hB' F.cliques_support (F.clique_multiplicity hmult)
    F.NearPairs F.pairPositive F.pairNegative F.pairPositive_mem F.pairNegative_mem
    F.near_pair_injective (F.near_pair_inter hA₀)
  refine ⟨Φ, ?_⟩
  rw [eliminationFamilyOutputLaw_failure_real]
  linarith only [hp]

theorem exists_second_elimination_output_law (S : ExchangeSystem W q (r + 1))
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
    ∃ Φ : ℕ → ↥(T.base.val ∪ N.val) ↪ Fin n,
      (eliminationFamilyOutputLaw T N E.graph L.positive (fun i : E.badNegative => i.val) Φ
        (eliminationFactor T K ((K : ℝ) * A) * (n : ℝ) ^ (-ρ)) none).toReal <
          Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
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
  have hP (i : E.badNegative) : L.positive i ∈ F.cliques ∪ E.cliques :=
    mem_union_left _ (L.positive_mem_cliques i)
  have hQ (i : E.badNegative) : i.val ∈ F.cliques ∪ E.cliques := by
    apply mem_union_right
    rw [E.cliques_eq_signs]
    exact mem_union_right _ (mem_sdiff.mp i.property).1
  obtain ⟨Φ, _, hp⟩ := exists_elimination_family_output_probability_paper_threshold
    T N e₀ hpair hqr hn hw hT K hK hKA hAb hρ hρhalf
    (F.cliques ∪ E.cliques) E.graph hD' hB'
    (E.union_cliques_support hpair F.cliques F.cliques_support)
    (E.union_cliques_multiplicity hpair F.cliques F.pairPositive_mem F.pairNegative_mem
      F.near_pair_injective hcommon hmult) E.badNegative L.positive (fun i => i.val)
    hP hQ L.pair_injective (fun i => ⟨L.edge i, L.vertex_inter i⟩)
  refine ⟨Φ, ?_⟩
  rw [eliminationFamilyOutputLaw_failure_real]
  linarith only [hp]

end Arxiv2411_18291
