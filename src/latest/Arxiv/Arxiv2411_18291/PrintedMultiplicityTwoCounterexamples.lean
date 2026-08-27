import Arxiv.Arxiv2411_18291.SparseMultiplicityTwoCounterexamples
import Arxiv.Arxiv2411_18291.IntegralGeneratorParameters

/-!
# Counterexamples at the printed integral-absorber and flattening parameters

Lemma 6.1 (`lem:Aint`) and Lemma 6.5 (`lem:flat`) both require edge
multiplicity at most two. When `choose(q,r)>2` this is impossible, even
without imposing their output boundedness condition. The following
counterexamples meet their input boundedness conditions for all sufficiently
large sizes, so no finite size threshold repairs those conclusions.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_integral_absorber_paper_counterexample
    (q r : ℕ) (hqr : r + 1 < q) (hk : 2 < q.choose (r + 1)) :
    let ρ : ℝ := 1 / (6 * q.choose (r + 1) : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∃ B : Hypergraph (Fin n) (r + 1),
      B.Nonempty ∧ IsGraphBounded B ((n : ℝ) ^ (-ρ)) ∧
        ¬∃ D : Finset (Block (Fin n) q),
          (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
            ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
              IntegrallyDecomposable q J → GeneratedBy D J := by
  exact eventually_sparse_reserve_not_generated_with_multiplicity_two q r hqr.le hk
    (integral_generator_parameters q r hqr).2.2.2

theorem eventually_flattening_paper_counterexample
    (q r : ℕ) (hqr : r + 1 < q) (hk : 2 < q.choose (r + 1))
    {u : ℝ} (hu : 0 < u) :
    let ρ : ℝ := 1 / (6 * q.choose (r + 1) : ℝ) ^ 2
    let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
    ∀ᶠ n : ℕ in atTop, ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D
        ((2 : ℝ) ^ (q + 2) * (4 * q : ℝ) ^ (r + 1) * u *
          (n : ℝ) ^ (-(7 * α / 10))) ∧
        ¬∃ F : Finset (Block (Fin n) q),
          (∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
            ∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J := by
  dsimp only
  obtain ⟨hα, _, hαρ, hρ1⟩ := integral_generator_parameters q r hqr
  have hk1 : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have h2 := le_mul_of_one_le_right (by positivity : 0 ≤ 2 *
      ((1 / (6 * q.choose (r + 1) : ℝ) ^ 2) / (2 * q : ℝ) ^ (r + 1))) hk1
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply eventually_sparse_cliques_not_flattenable_to_two q r hqr.le hk (by positivity)
  nlinarith only [hα, h2, hαρ, hρ1]

end Arxiv2411_18291
