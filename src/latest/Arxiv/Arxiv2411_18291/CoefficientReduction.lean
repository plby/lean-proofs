import Arxiv.Arxiv2411_18291.IntegralSpan
import Arxiv.Arxiv2411_18291.CliqueRefinement

/-!
# Reducing an integral representation to small coefficients

Reduce clique coefficients to the interval `[0,N-1]`. If every edge is in
at most two supporting cliques and the original boundary is a graph, the
boundary correction is a multiple of `N` with quotient either `-1` or `0`.
This one-sided remainder choice avoids a separate parity argument for
balanced remainders and retains the coefficient bound needed by absorption.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem boundary_eq_sum_supported (D : Finset (Block V q)) (Φ : Block V q → ℤ)
    (hs : ∀ Q, Q ∉ D → Φ Q = 0) (e : Block V r) :
    boundary r Φ e = ∑ Q ∈ D.filter (fun Q => e.val ⊆ Q.val), Φ Q := by
  rw [boundary, sum_filter]
  symm
  apply sum_subset (subset_univ _)
  intro Q _ hQD
  rw [hs Q hQD]
  simp only [ite_self]

theorem boundary_nonneg_int (Φ : Block V q → ℤ) (hΦ : ∀ Q, 0 ≤ Φ Q) (e : Block V r) :
    0 ≤ boundary r Φ e := by
  apply sum_nonneg
  intro Q _
  split_ifs
  · exact hΦ Q
  · exact le_rfl

theorem boundary_le_of_supported_coefficients (D : Finset (Block V q))
    (Φ : Block V q → ℤ) (hs : ∀ Q, Q ∉ D → Φ Q = 0) {C : ℤ} (hΦ : ∀ Q, Φ Q ≤ C)
    (e : Block V r) :
    boundary r Φ e ≤ ((D.filter fun Q => e.val ⊆ Q.val).card : ℤ) * C := by
  rw [boundary_eq_sum_supported D Φ hs e]
  calc
    _ ≤ ∑ _Q ∈ D.filter (fun Q => e.val ⊆ Q.val), C := sum_le_sum fun Q _ => hΦ Q
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem boundary_dvd_of_coefficients (N : ℤ) (Φ : Block V q → ℤ)
    (hΦ : ∀ Q, N ∣ Φ Q) (e : Block V r) : N ∣ boundary r Φ e := by
  apply Finset.dvd_sum
  intro Q _
  split_ifs
  · exact hΦ Q
  · exact dvd_zero _

theorem boundary_remainder_congr (N : ℤ) (Φ : Block V q → ℤ) (e : Block V r) :
    N ∣ boundary r Φ e - boundary r (fun Q => Φ Q % N) e := by
  have h := boundary_dvd_of_coefficients N (Φ - fun Q => Φ Q % N)
    (fun _ => Int.dvd_self_sub_emod) e
  simpa only [boundary_sub, Pi.sub_apply] using h

theorem boundary_zero_outside_support (D : Finset (Block V q)) (B : Hypergraph V r)
    (Φ : Block V q → ℤ) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (hDB : cliqueSupport r D ⊆ B) (e : Block V r) (he : e ∉ B) : boundary r Φ e = 0 := by
  apply sum_eq_zero
  intro Q _
  by_cases heQ : e.val ⊆ Q.val
  · rw [if_pos heQ]
    apply hs Q
    intro hQ
    exact he (hDB (mem_biUnion.mpr ⟨Q, hQ, (mem_cliqueEdges _ _).mpr heQ⟩))
  · exact if_neg heQ

theorem reduced_boundary_correction_small (N : ℤ) (hN : 2 ≤ N)
    (D : Finset (Block V q)) (L : Hypergraph V r) (Φ : Block V q → ℤ)
    (hΦ : boundary r Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (e : Block V r) :
    (indicator L e - boundary r (fun Q => Φ Q % N) e) / N = -1 ∨
      (indicator L e - boundary r (fun Q => Φ Q % N) e) / N = 0 := by
  have hNpos : 0 < N := by omega
  have hrem0 (Q : Block V q) : 0 ≤ Φ Q % N := Int.emod_nonneg _ hNpos.ne'
  have hrem1 (Q : Block V q) : Φ Q % N ≤ N - 1 := by
    have h := Int.emod_lt_of_pos (Φ Q) hNpos
    omega
  have hsrem : ∀ Q, Q ∉ D → Φ Q % N = 0 := by
    intro Q hQ
    rw [hs Q hQ, Int.zero_emod]
  have hb0 := boundary_nonneg_int (fun Q => Φ Q % N) hrem0 e
  have hb1 : boundary r (fun Q => Φ Q % N) e ≤ 2 * (N - 1) := by
    apply (boundary_le_of_supported_coefficients D _ hsrem hrem1 e).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmult e) (by omega)
  have hL0 : 0 ≤ indicator L e := by unfold indicator; split_ifs <;> omega
  have hL1 : indicator L e ≤ 1 := by unfold indicator; split_ifs <;> omega
  let J := indicator L e - boundary r (fun Q => Φ Q % N) e
  have hdiv : N ∣ J := by
    simpa only [hΦ, J] using boundary_remainder_congr N Φ e
  have hprod : N * (J / N) = J := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  have hlo : -2 < J / N := by
    apply (mul_lt_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    linarith
  have hhi : J / N < 1 := by
    apply (mul_lt_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    linarith
  change J / N = -1 ∨ J / N = 0
  omega

end Arxiv2411_18291
