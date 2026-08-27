import Arxiv.Arxiv2411_18291.SplittingDisjointness
import Arxiv.Arxiv2411_18291.IntegralSpan

/-!
# The signed sum produced by splitting

Sum selected signed exchange replacements. Their boundary is exactly the
same signed sum of base cliques. Disjoint replacement families ensure that
each resulting coefficient is in `{-1,0,1}`. The vector therefore equals
the difference of two disjoint sets of cliques, both contained in the
constructed replacement family.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r : ℕ}

def exchangeSum (T : I → ExchangeSystem V q r) (c : I → ℤ) : Block V q → ℤ :=
  ∑ i, fun P => c i * (T i).replacementVector P

def exchangeSupport (T : I → ExchangeSystem V q r) : Finset (Block V q) :=
  univ.biUnion fun i => (T i).replacementCliques

theorem boundary_exchangeSum (T : I → ExchangeSystem V q r) (c : I → ℤ) :
    boundary r (exchangeSum T c) =
      ∑ i, fun e => c i * indicator (cliqueEdges r (T i).base) e := by
  rw [exchangeSum, boundary_sum]
  apply sum_congr rfl
  intro i _
  rw [boundary_mul, ExchangeSystem.boundary_replacement]

theorem exchangeSum_support (T : I → ExchangeSystem V q r) (c : I → ℤ)
    (P : Block V q) (hP : P ∉ exchangeSupport T) : exchangeSum T c P = 0 := by
  rw [exchangeSum, Finset.sum_apply]
  apply sum_eq_zero
  intro i _
  have hi : P ∉ (T i).replacementCliques :=
    fun h => hP (mem_biUnion.mpr ⟨i, mem_univ _, h⟩)
  rw [(T i).replacementVector_support P hi, mul_zero]

theorem exchangeSum_abs_le_one (T : I → ExchangeSystem V q r) (c : I → ℤ)
    (hsep : Pairwise fun i j => Disjoint (T i).replacementCliques (T j).replacementCliques)
    (hc : ∀ i, |c i| ≤ 1) (P : Block V q) : |exchangeSum T c P| ≤ 1 := by
  classical
  by_cases hex : ∃ i, P ∈ (T i).replacementCliques
  · obtain ⟨i, hi⟩ := hex
    rw [exchangeSum, Finset.sum_apply, sum_eq_single i]
    · rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hc i) ((T i).replacementVector_abs_le P)
        (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)
    · intro j _ hji
      have hj : P ∉ (T j).replacementCliques :=
        fun h => disjoint_left.mp (hsep hji) h hi
      rw [(T j).replacementVector_support P hj, mul_zero]
    · intro h
      exact (h (mem_univ _)).elim
  · have hP : P ∉ exchangeSupport T := by
      intro h
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
      exact hex ⟨i, hi⟩
    rw [exchangeSum_support T c P hP, abs_zero]
    norm_num

omit [Fintype V] in
theorem signed_sets_of_unit_coefficients [Finite V] (Φ : Block V q → ℤ)
    (hΦ : ∀ P, |Φ P| ≤ 1) (F : Finset (Block V q)) (hs : ∀ P, P ∉ F → Φ P = 0) :
    ∃ P N : Finset (Block V q), P ⊆ F ∧ N ⊆ F ∧ Disjoint P N ∧ Φ = indicator P - indicator N := by
  let : Fintype V := Fintype.ofFinite V
  let P := univ.filter fun Q => Φ Q = 1
  let N := univ.filter fun Q => Φ Q = -1
  have hP : P ⊆ F := by
    intro Q hQ
    by_contra hQF
    have h1 := (mem_filter.mp hQ).2
    rw [hs Q hQF] at h1
    norm_num at h1
  have hN : N ⊆ F := by
    intro Q hQ
    by_contra hQF
    have h1 := (mem_filter.mp hQ).2
    rw [hs Q hQF] at h1
    norm_num at h1
  refine ⟨P, N, hP, hN, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro Q hQP hQN
    have hp := (mem_filter.mp hQP).2
    have hn := (mem_filter.mp hQN).2
    omega
  · funext Q
    have hb := abs_le.mp (hΦ Q)
    simp only [Pi.sub_apply, indicator, P, N, mem_filter, mem_univ, true_and]
    split_ifs <;> omega

theorem exchangeSum_signed_sets (T : I → ExchangeSystem V q r) (c : I → ℤ)
    (hsep : Pairwise fun i j => Disjoint (T i).replacementCliques (T j).replacementCliques)
    (hc : ∀ i, |c i| ≤ 1) :
    ∃ P N : Finset (Block V q), P ⊆ exchangeSupport T ∧ N ⊆ exchangeSupport T ∧
      Disjoint P N ∧ boundary r (indicator P - indicator N) =
        ∑ i, fun e => c i * indicator (cliqueEdges r (T i).base) e := by
  obtain ⟨P, N, hP, hN, hdis, hΦ⟩ := signed_sets_of_unit_coefficients (exchangeSum T c)
    (exchangeSum_abs_le_one T c hsep hc) (exchangeSupport T) (exchangeSum_support T c)
  exact ⟨P, N, hP, hN, hdis, hΦ ▸ boundary_exchangeSum T c⟩

end Arxiv2411_18291
