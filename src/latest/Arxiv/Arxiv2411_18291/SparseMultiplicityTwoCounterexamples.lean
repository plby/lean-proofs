import Arxiv.Arxiv2411_18291.MultiplicityTwoCounterexample
import Arxiv.Arxiv2411_18291.SmallSupportAsymptotics

/-!
# Sparse counterexamples to multiplicity-two integral generation and flattening

The obstructions persist at every fixed density scale `C * n^(-η)` with
`C > 0` and `η < 1`, for all sufficiently large ambient sizes. No change
to a size threshold or to the output boundedness can repair multiplicity two.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_sparse_reserve_not_generated_with_multiplicity_two
    (q r : ℕ) (hqr : r + 1 ≤ q) (hk : 2 < q.choose (r + 1))
    {ρ : ℝ} (hρ : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ B : Hypergraph (Fin n) (r + 1),
      B.Nonempty ∧ IsGraphBounded B ((n : ℝ) ^ (-ρ)) ∧
        ¬∃ D : Finset (Block (Fin n) q),
          (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
            ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
              IntegrallyDecomposable q J → GeneratedBy D J := by
  filter_upwards [eventually_ge_atTop (q + (r + 1)),
    eventually_const_lt_scaled_decay 1 (C := 1) (by norm_num) hρ] with n hn hbound
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq
    (s := (univ : Finset (Fin n))) (show r + 1 ≤ (univ : Finset (Fin n)).card by
      simpa only [card_univ, Fintype.card_fin] using (show r + 1 ≤ n by omega))
  let e : Block (Fin n) (r + 1) := ⟨s, hs⟩
  refine ⟨{e}, singleton_nonempty e, graphBounded_singleton e ?_, ?_⟩
  · simpa only [one_mul, Fintype.card_fin] using hbound
  · exact not_exists_multiplicity_two_integral_generators hqr hk
      (by simpa only [Fintype.card_fin] using hn) {e} (singleton_nonempty e)

theorem eventually_sparse_cliques_not_flattenable_to_two
    (q r : ℕ) (hqr : r + 1 ≤ q) (hk : 2 < q.choose (r + 1))
    {C η : ℝ} (hC : 0 < C) (hη : η < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D (C * (n : ℝ) ^ (-η)) ∧
        ¬∃ F : Finset (Block (Fin n) q),
          (∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
            ∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J := by
  filter_upwards [eventually_ge_atTop (q + (r + 1)),
    eventually_const_lt_scaled_decay
      (((q - r : ℕ) : ℝ) * (q + (r + 1)).choose q) hC hη] with n hn hbound
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq
    (s := (univ : Finset (Fin n))) (by simpa only [card_univ, Fintype.card_fin] using hn)
  let Z : Block (Fin n) (q + (r + 1)) := ⟨s, hs⟩
  obtain ⟨t, ht, htcard⟩ := exists_subset_card_eq
    (s := s) (show r + 1 ≤ s.card by omega)
  let e : Block (Fin n) (r + 1) := ⟨t, htcard⟩
  refine ⟨cliqueEdges q Z, cliqueFamilyBounded_of_card _ ?_, ?_⟩
  · simpa only [card_cliqueEdges, Fintype.card_fin] using hbound
  · exact local_cliques_not_flattenable_to_two hqr hk Z e ht

end Arxiv2411_18291
