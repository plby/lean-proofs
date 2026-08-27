import Arxiv.Arxiv2411_18291.FinalNegativeFamily

/-!
# Both elimination stages and the sparse negative host

Combine the uniform existence theorems at their explicit constant
factors. The resulting negative host has a true clique decomposition,
avoids the original graph, and remains bounded at the original density
exponent. The subsequent signed-representation argument is separate.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

def eliminationFactor (T : ExchangeSystem U q (r + 1)) (M : ℕ) (A : ℝ) : ℝ :=
  A + T.graph.card * (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) * A))

theorem eliminationFactor_mul (T : ExchangeSystem U q (r + 1)) (M : ℕ) (A x : ℝ) :
    eliminationFactor T M A * x = A * x + T.graph.card *
      (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) * A * x)) := by
  unfold eliminationFactor
  ring

theorem one_le_eliminationFactor (T : ExchangeSystem U q (r + 1)) (M : ℕ) {A : ℝ}
    (hA : 1 ≤ A) : 1 ≤ eliminationFactor T M A := by
  have hAnonneg : 0 ≤ A := by linarith
  apply hA.trans
  unfold eliminationFactor
  exact le_add_of_nonneg_right (by positivity)

def firstEliminationFactor (T : ExchangeSystem U q (r + 1)) (C M : ℕ) (A : ℝ) : ℝ :=
  eliminationFactor T (2 * C * M + 2) (((2 * C * M + 2 : ℕ) : ℝ) * A)

def secondEliminationFactor (T : ExchangeSystem U q (r + 1)) (C M : ℕ) (A : ℝ) : ℝ :=
  let K₀ : ℕ := 2 * C * M + 2
  let K₁ : ℕ := K₀ + 4 * q.choose (r + 1) * K₀ ^ 2 + 2
  eliminationFactor T K₁ ((K₁ : ℝ) * firstEliminationFactor T C M A)

theorem one_le_firstEliminationFactor (T : ExchangeSystem U q (r + 1)) (C M : ℕ)
    {A : ℝ} (hA : 1 ≤ A) : 1 ≤ firstEliminationFactor T C M A := by
  apply one_le_eliminationFactor
  have hK : (1 : ℝ) ≤ (2 * C * M + 2 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * C * M + 2 by omega)
  exact one_le_mul_of_one_le_of_one_le hK hA

theorem eventually_exists_two_stage_elimination (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 ≤ q) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      ∀ F : SplittingFamily S D B C (A * (n : ℝ) ^ (-ρ)),
      (∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M) →
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
  have hA₁ := one_le_firstEliminationFactor T C M hA
  filter_upwards [eventually_exists_first_elimination S hA₀ T N e₀ hpair hqr C M hA hρ hρ1,
    eventually_exists_second_elimination S hA₀ T N e₀ hpair hqr C (2 * C * M + 2) hA₁ hρ hρ1]
    with n hfirst hsecond
  intro D B F hmult
  have hE : Nonempty (EliminationFamily T N F.graph F.pairPositive F.pairNegative
      (firstEliminationFactor T C M A * (n : ℝ) ^ (-ρ))) := by
    rw [firstEliminationFactor, eliminationFactor_mul]
    exact hfirst D B F hmult
  obtain ⟨E⟩ := hE
  obtain ⟨L⟩ := exists_further_elimination_pairs F hA₀ E hpair
  have hG : Nonempty (EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
      (secondEliminationFactor T C M A * (n : ℝ) ^ (-ρ))) := by
    dsimp only [secondEliminationFactor]
    rw [eliminationFactor_mul]
    exact hsecond D B (A * (n : ℝ) ^ (-ρ)) F E L (F.clique_multiplicity hmult)
  obtain ⟨G⟩ := hG
  exact ⟨E, L, G, finalNegative_decomposition F E L G hpair,
    finalNegative_avoids_original F E L G hpair, finalNegative_bounded F E L G hpair⟩

end Arxiv2411_18291
