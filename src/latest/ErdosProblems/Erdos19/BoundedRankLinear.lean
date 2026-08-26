import ErdosProblems.Erdos19.FiniteModel

/-! # Approximate colorings of bounded-rank linear hypergraphs -/

namespace Erdos19.SetHypergraph

open Erdos76 Erdos76.FiniteHypergraph

/-- The ordinary approximation theorem applied to a linear set-valued
hypergraph with fixed minimum and maximum edge sizes. The displayed quotient
is the exact degree bound from linearity. -/
theorem eventually_bounded_rank_approximate
    (r k : ℕ) (hr : 0 < r) (hk : 2 ≤ k) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, k ≤ e.val.ncard) → (∀ e : H, e.val.ncard ≤ r) →
      ∃ q : ℕ, 0 < q ∧
        (q : ℝ) ≤ (1 + epsilon) * (((n - 1) / (k - 1) : ℕ) : ℝ) ∧
        H.EdgeColorable q := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    Erdos19.bounded_approximate_edgeColoring r hr epsilon hepsilon
  obtain ⟨D₁, hD₁⟩ := exists_nat_gt (1 / delta)
  let Dmin := max D₀ D₁
  refine ⟨(k - 1) * Dmin + 1, ?_⟩
  intro n hn H hlinear hmin hmax
  let D := (n - 1) / (k - 1)
  have hDmin : Dmin ≤ D := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k - 1)).mpr
    have hprod : (k - 1) * Dmin ≤ n - 1 := by omega
    simpa only [Nat.mul_comm] using hprod
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDmin
  have hD₁le : D₁ ≤ D := (le_max_right _ _).trans hDmin
  have hratio : 1 / delta < (D : ℝ) := hD₁.trans_le (by exact_mod_cast hD₁le)
  have hdeltaD : 1 < delta * (D : ℝ) := by
    have h := (div_lt_iff₀ hdelta).mp hratio
    nlinarith
  have hbound : H.finiteModel.IsBounded r := by
    intro e
    simpa only [H.finiteModel_support_card] using hmax e
  have hdeg : ∀ v ∈ H.finiteModel.vertexSet, H.finiteModel.edgeDegree v ≤ D := by
    intro v _
    simpa only [Fintype.card_fin] using H.finiteModel_edgeDegree_le_div hlinear k hk hmin v
  have hpair : ∀ u ∈ H.finiteModel.vertexSet, ∀ v ∈ H.finiteModel.vertexSet, u ≠ v →
      (H.finiteModel.edgePairDegree u v : ℝ) < delta * (D : ℝ) := by
    intro u _ v _ huv
    have hle : (H.finiteModel.edgePairDegree u v : ℝ) ≤ 1 := by
      exact_mod_cast H.finiteModel_edgePairDegree_le_one hlinear huv
    exact hle.trans_lt hdeltaD
  obtain ⟨q, hq, hqbound, hc⟩ := hround (Fin n) H H.finiteModel D hD₀ hbound hdeg hpair
  exact ⟨q, hq, hqbound, H.edgeColorable_of_finiteModel q hc⟩

/-- In particular, fixed bounded rank and minimum edge size three leave a
constant fraction of the `n` colors unused, for all sufficiently large `n`. -/
theorem eventually_bounded_rank_min_three
    (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 3 ≤ e.val.ncard) → (∀ e : H, e.val.ncard ≤ r) →
      ∃ q : ℕ, 4 * q ≤ 3 * n ∧ H.EdgeColorable q := by
  obtain ⟨N, hN⟩ := eventually_bounded_rank_approximate r 3 hr (by norm_num)
    (1 / 2) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn H hlinear hmin hmax
  obtain ⟨q, _, hq, hc⟩ := hN n hn H hlinear hmin hmax
  have hdiv : 2 * ((n - 1) / 2) ≤ n := (Nat.mul_div_le (n - 1) 2).trans (by omega)
  have hdivR : (2 : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hdiv
  have hqR : (4 : ℝ) * q ≤ 3 * n := by
    norm_num at hq
    linarith
  exact ⟨q, by exact_mod_cast hqR, hc⟩

#print axioms eventually_bounded_rank_approximate
#print axioms eventually_bounded_rank_min_three

end Erdos19.SetHypergraph
