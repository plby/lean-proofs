import Arxiv.Arxiv2411_18291.SignedAbsorption
import Arxiv.Arxiv2411_18291.TwoStageElimination

/-!
# Sparse hosts absorbing every bounded representation

Construct the splitting and both elimination families before choosing the
represented leave. The resulting host is disjoint from the input graph,
has a true decomposition, and absorbs all its bounded representations.
Every fixed density exponent between zero and one is preserved.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

def splittingFactor (S : ExchangeSystem W q (r + 1)) (C : ℕ) (A : ℝ) : ℝ :=
  A + S.graph.card * (8 * (r + 1).factorial * (((2 * C : ℕ) : ℝ) * A))

theorem splittingFactor_mul (S : ExchangeSystem W q (r + 1)) (C : ℕ) (A x : ℝ) :
    splittingFactor S C A * x = A * x + S.graph.card *
      (8 * (r + 1).factorial * (((2 * C : ℕ) : ℝ) * A * x)) := by
  unfold splittingFactor
  ring

theorem one_le_splittingFactor (S : ExchangeSystem W q (r + 1)) (C : ℕ) {A : ℝ}
    (hA : 1 ≤ A) : 1 ≤ splittingFactor S C A := by
  have hAnonneg : 0 ≤ A := by linarith
  apply hA.trans
  unfold splittingFactor
  exact le_add_of_nonneg_right (by positivity)

theorem one_le_secondEliminationFactor (T : ExchangeSystem U q (r + 1)) (C M : ℕ)
    {A : ℝ} (hA : 1 ≤ A) : 1 ≤ secondEliminationFactor T C M A := by
  apply one_le_eliminationFactor
  apply one_le_mul_of_one_le_of_one_le _ (one_le_firstEliminationFactor T C M hA)
  exact_mod_cast (show 1 ≤ (2 * C * M + 2) +
    4 * q.choose (r + 1) * (2 * C * M + 2) ^ 2 + 2 by omega)

theorem eventually_exists_sparse_signed_absorber (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hS : IsExchangeFamily S A₀)
    (hlocal : IsPositiveFrameLocal S A₀) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 ≤ q) (C M : ℕ) (hC : 0 < C)
    {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)) →
      IsGraphBounded B (A * (n : ℝ) ^ (-ρ)) → cliqueSupport (r + 1) D ⊆ B →
      (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M) →
      ∃ H : Hypergraph (Fin n) (r + 1), HasDecomposition q H ∧ Disjoint H B ∧
        IsGraphBounded H
          (secondEliminationFactor T C M (splittingFactor S C A) * (n : ℝ) ^ (-ρ)) ∧
        AbsorbsBoundedRepresentations D B H C := by
  have hA' := one_le_splittingFactor S C hA
  filter_upwards [eventually_exists_splitting_family S hqr C M hC hA hρ hρ1,
    eventually_exists_two_stage_elimination S hS T N e₀ hpair hqr C M hA' hρ hρ1]
    with n hsplit helim
  intro D B hD hB hDB hmult
  have hF : Nonempty (SplittingFamily S D B C (splittingFactor S C A * (n : ℝ) ^ (-ρ))) := by
    rw [splittingFactor_mul]
    exact hsplit D B hD hB hDB hmult
  obtain ⟨F⟩ := hF
  obtain ⟨E, L, G, hdecomp, hdis, hbound⟩ := helim D B F hmult
  exact ⟨cliqueSupport (r + 1) (finalNegative F E L G), ⟨_, hdecomp⟩, hdis, hbound,
    two_stage_absorbs_bounded_representations F hS hlocal hcross E L G hpair hqr⟩

omit [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] in
/-- An unconditional sparse construction, with no exchange or placement
hypotheses left over. Only the input support and multiplicity are prescribed. -/
theorem exists_sparse_absorber_for_bounded_representations (hqr : r + 1 < q)
    (C M : ℕ) (hC : 0 < C) {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)) →
      IsGraphBounded B (A * (n : ℝ) ^ (-ρ)) → cliqueSupport (r + 1) D ⊆ B →
      (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M) →
      ∃ H : Hypergraph (Fin n) (r + 1), HasDecomposition q H ∧ Disjoint H B ∧
        IsGraphBounded H (K * (n : ℝ) ^ (-ρ)) ∧ AbsorbsBoundedRepresentations D B H C := by
  obtain ⟨S, A₀, _, hS, hcross, hlocal⟩ :=
    exists_local_crossSimple_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨T, N, e₀, hpair, _⟩ := exists_elimination_pattern q r hqr
  refine ⟨secondEliminationFactor T.system C M (splittingFactor S.system C A),
    one_le_secondEliminationFactor T.system C M (one_le_splittingFactor S.system C hA), ?_⟩
  exact eventually_exists_sparse_signed_absorber S.system hS hlocal hcross T.system N e₀
    hpair hqr.le C M hC hA hρ hρ1

end Arxiv2411_18291
