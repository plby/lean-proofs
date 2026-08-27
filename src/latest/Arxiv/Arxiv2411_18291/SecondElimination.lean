import Arxiv.Arxiv2411_18291.FurtherEliminationPairs

/-!
# Constructing the second elimination stage

The input consists of the splitting and first-elimination clique families.
Their combined multiplicity and sparse support bounds are proved, not
assumed. Applying the general placement theorem constructs all further
exchanges on the actual bad-clique partners at the same density exponent.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

theorem eventually_exists_second_elimination (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 ≤ q) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let K : ℕ := M + 4 * q.choose (r + 1) * M ^ 2 + 2
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1), ∀ θ : ℝ, ∀ F : SplittingFamily S D B C θ,
      ∀ E : EliminationFamily T N F.graph F.pairPositive F.pairNegative (A * (n : ℝ) ^ (-ρ)),
      ∀ L : FurtherEliminationPairs F E,
      (∀ f : Block (Fin n) (r + 1), (F.cliques.filter fun Q => f.val ⊆ Q.val).card ≤ M) →
      Nonempty (EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
        ((K : ℝ) * A * (n : ℝ) ^ (-ρ) + T.graph.card *
          (8 * (r + 1).factorial * (((q.choose (r + 1) * K : ℕ) : ℝ) *
            ((K : ℝ) * A) * (n : ℝ) ^ (-ρ))))) := by
  dsimp only
  let K : ℕ := M + 4 * q.choose (r + 1) * M ^ 2 + 2
  have hK : 0 < K := by dsimp only [K]; omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hAnonneg : 0 ≤ A := by linarith
  have hAK : A ≤ (K : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKreal hAnonneg
  have hKA : 1 ≤ (K : ℝ) * A := hA.trans hAK
  filter_upwards [eventually_exists_elimination_family T N e₀ hpair hqr K hK hKA hρ hρ1]
    with n hplace
  intro D B θ F E L hmult
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
  apply hplace (F.cliques ∪ E.cliques) E.graph hD' hB'
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

end Arxiv2411_18291
