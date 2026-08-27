import Arxiv.Arxiv2411_18291.SparseIntegralGenerators
import Arxiv.Arxiv2411_18291.GlobalDivisibility

/-!
# Unconditional existence of sparse integral generators

Construct the finite exchange pattern, then apply the rainbow, focusing,
and decoding arguments. Only numerical restrictions on the fixed density
exponents remain. The family generates all degree-divisible signed vectors
on the reserve, but flattening its edge multiplicities is still required.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_sparse_integral_generators (q r : ℕ) (hqr : r + 1 < q)
    {α ρ η : ℝ} (hα : 0 < α)
    (hαO : α * ((3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 : ℕ) : ℝ) ≤ 1 / 12)
    (hρ : 2 * α * q.choose (r + 1) ≤ ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) (hηα : η < 7 * α / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D ((n : ℝ) ^ (-η)) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  obtain ⟨T, A, hcard, hA, hcross⟩ :=
    exists_crossSimple_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr.le T.system.base
  obtain ⟨P, hP, hPe⟩ := hA.2.2.1 e he
  have hpair : IsEliminationPair T.system P e := by
    refine ⟨hA.1 hP, ?_, fun f hf => hA.pair_local hP hf, hcross⟩
    rw [inter_comm]
    exact vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r) P T.system.base e hPe
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have hk2 : q.choose (r + 1) ≤ q.choose (r + 1) * q.choose (r + 1) :=
    Nat.le_mul_of_pos_left _ hk
  have hqh := hk2.trans (hA.choose_sq_le (Nat.succ_pos r))
  have hαh : α * T.system.graph.card ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) hα.le).trans hαO
  obtain ⟨F, _, hF⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (show r + 1 ≤ univ.card by simpa only [card_univ, Fintype.card_fin] using hqr.le)
  exact eventually_exists_sparse_integral_generators_with_exchange ⟨F, hF⟩
    (Fintype.card_fin q) hA hpair hqr T.system.graph.card hqh le_rfl hα hαh hρ hρ1 hη hηα

theorem eventually_exists_sparse_divisible_generators (q r : ℕ) (hqr : r + 1 < q)
    {α ρ η : ℝ} (hα : 0 < α)
    (hαO : α * ((3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 : ℕ) : ℝ) ≤ 1 / 12)
    (hρ : 2 * α * q.choose (r + 1) ≤ ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) (hηα : η < 7 * α / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D ((n : ℝ) ^ (-η)) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          DegreeDivisible q J → GeneratedBy D J := by
  filter_upwards [eventually_exists_sparse_integral_generators q r hqr hα hαO hρ hρ1 hη hηα,
    eventually_ge_atTop (q + (r + 1))] with n hgen hn
  intro B hB
  obtain ⟨D, hD, hJ⟩ := hgen B hB
  refine ⟨D, hD, fun J hs hdiv => hJ J hs ?_⟩
  exact integrallyDecomposable_of_degreeDivisible_of_le hqr.le
    (by simpa only [Fintype.card_fin] using hn) hdiv

end Arxiv2411_18291
