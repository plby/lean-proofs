/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star

@[expose] public section

/-!
# van der Corput's fundamental inequality

This file proves **van der Corput's fundamental inequality** (the van der Corput difference
inequality): for positive integers `a`, `N`, complex numbers `u₁, …, u_N`, and a positive integer
`L` with `aL ≤ N`,
`L² · ‖∑_{n=1}^N uₙ‖² ≤ L (N + a(L-1)) · ∑_{n=1}^N ‖uₙ‖²`
`  + 2 (N + a(L-1)) · ∑_{ℓ=1}^{L-1} (L-ℓ) · Re ∑_{n=1}^{N-aℓ} uₙ · conj(u_{n+aℓ})`.

This is the Cauchy–Schwarz / autocorrelation estimate underlying the van der Corput difference
theorem in the theory of uniform distribution modulo one.

The main statement is `vanDerCorput_fundamental_inequality` (indexed by `ℕ`). The proof runs through
the auxiliary `vanDerCorput_core`, stated for the zero-extension `w : ℤ → ℂ` of `u` (so all the
index shifts are clean): writing `vₚ = ∑_{ℓ < L} w (p - aℓ)`, the regrouping identity
`L · ∑ w = ∑ₚ vₚ` together with Cauchy–Schwarz gives `L² ‖∑ w‖² ≤ (N + a(L-1)) · ∑ₚ ‖vₚ‖²`;
expanding `‖vₚ‖²` into the autocorrelation `∑_{ℓ,j} ∑ₘ w m · conj (w (m + a(ℓ-j)))` and regrouping by
the difference `d = ℓ - j` (which occurs `L - |d|` times in the `L × L` box) produces the stated
correlation sum.

## References
* J. G. van der Corput, *Diophantische Ungleichungen. I. Zur Gleichverteilung modulo Eins*,
  Acta Math. 56 (1931), 373–456.
* Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts in
  Mathematics 193, Cambridge University Press, 2012, Lemma 1.5.
-/

open Finset

/-- **van der Corput's fundamental inequality**, core form: for a finitely-supported
`w : ℤ → ℂ` (supported on `[1, N]`), positive integers `a` and `L` with `aL ≤ N`,
the `L²`-scaled square of the sum is bounded by the diagonal `‖·‖²` term plus the autocorrelation
terms. This is proved directly; `vanDerCorput_fundamental_inequality` is the `ℕ`-indexed
specialisation. -/
private theorem vanDerCorput_core (a N : ℤ) (L : ℕ) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hLN : a * (L:ℤ) ≤ N) (w : ℤ → ℂ) (hsupp : ∀ k, w k ≠ 0 → k ∈ Finset.Icc (1:ℤ) N) :
    (L : ℝ) ^ 2 * ‖∑ k ∈ Finset.Icc (1:ℤ) N, w k‖ ^ 2 ≤
      (L:ℝ) * (↑(N + a * ((L:ℤ) - 1))) * (∑ k ∈ Finset.Icc (1:ℤ) N, ‖w k‖ ^ 2)
      + 2 * (↑(N + a * ((L:ℤ) - 1))) * ∑ e ∈ Finset.Icc 1 (L - 1), ((L:ℝ) - (e:ℝ)) *
          (∑ m ∈ Finset.Icc (1:ℤ) (N - a * (e:ℤ)),
            w m * (starRingEnd ℂ) (w (m + a * (e:ℤ)))).re := by
  have hL1 : (1:ℤ) ≤ (L:ℤ) := by exact_mod_cast hL
  set f0 : ℤ → ℂ := fun e => ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * e)) with hf0
  have hident : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), ∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)
      = (L:ℂ) * ∑ k ∈ Finset.Icc (1:ℤ) N, w k := by
    rw [Finset.sum_comm]
    have hper : ∀ ℓ ∈ Finset.range L,
        ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), w (p - a * ↑ℓ)
          = ∑ k ∈ Finset.Icc (1:ℤ) N, w k := by
      intro ℓ hℓ; rw [Finset.mem_range] at hℓ
      have hmap : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), w (p - a * ↑ℓ)
          = ∑ m ∈ Finset.Icc (1 + -(a * ↑ℓ)) (N + a * ((L:ℤ) - 1) + -(a * ↑ℓ)), w m := by
        rw [← Finset.map_add_right_Icc (1:ℤ) (N + a * ((L:ℤ) - 1)) (-(a * ↑ℓ)), Finset.sum_map]
        exact Finset.sum_congr rfl (fun p _ => by rw [addRightEmbedding_apply, sub_eq_add_neg])
      rw [hmap]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro k hk
        rw [Finset.mem_Icc] at hk ⊢
        have h1 : (0:ℤ) ≤ a * ↑ℓ := mul_nonneg (by linarith) (Int.natCast_nonneg _)
        have h2 : a * ↑ℓ ≤ a * ((L:ℤ) - 1) := mul_le_mul_of_nonneg_left (by omega) (by linarith)
        constructor <;> linarith [hk.1, hk.2]
      · intro k _ hk
        by_contra hwk; exact hk (hsupp k hwk)
    rw [Finset.sum_congr rfl hper, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hCS : (L:ℝ)^2 * ‖∑ k ∈ Finset.Icc (1:ℤ) N, w k‖^2
      ≤ (↑(N + a * ((L:ℤ) - 1)):ℝ)
        * ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2 := by
    set S := Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)) with hS
    have hnormeq : ‖∑ p ∈ S, ∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖
        = (L:ℝ) * ‖∑ k ∈ Finset.Icc (1:ℤ) N, w k‖ := by
      rw [hident, norm_mul]; congr 1; rw [Complex.norm_natCast]
    have hsq : ‖∑ p ∈ S, ∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2
        ≤ (∑ p ∈ S, ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖)^2 := by
      gcongr; exact norm_sum_le _ _
    have hpos : (0:ℤ) ≤ N + a * ((L:ℤ) - 1) + 1 - 1 := by
      have h1 : (0:ℤ) ≤ a * ((L:ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
      have h2 : (0:ℤ) ≤ a * (L:ℤ) := mul_nonneg (by linarith) (by linarith)
      linarith [hLN]
    have hcard : (S.card:ℝ) = (↑(N + a * ((L:ℤ) - 1)):ℝ) := by
      rw [hS, Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg hpos]; push_cast; ring
    calc (L:ℝ)^2 * ‖∑ k ∈ Finset.Icc (1:ℤ) N, w k‖^2
        = ‖∑ p ∈ S, ∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2 := by rw [hnormeq]; ring
      _ ≤ (∑ p ∈ S, ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖)^2 := hsq
      _ ≤ (S.card:ℝ) * ∑ p ∈ S, ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2 := sq_sum_le_card_mul_sum_sq
      _ = (↑(N + a * ((L:ℤ) - 1)):ℝ) * ∑ p ∈ S, ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2 := by
          rw [hcard]
  have hexp : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2
      = (∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
          ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * ((ℓ:ℤ) - (j:ℤ))))).re := by
    have hpe : ∀ p : ℤ, ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2
        = (∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
            w (p - a * ↑ℓ) * (starRingEnd ℂ) (w (p - a * ↑j))).re := by
      intro p
      have h1 : ∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
          w (p - a * ↑ℓ) * (starRingEnd ℂ) (w (p - a * ↑j))
          = (∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ))
            * (starRingEnd ℂ) (∑ j ∈ Finset.range L, w (p - a * ↑j)) := by
        rw [map_sum, Finset.sum_mul_sum]
      rw [h1, Complex.mul_conj]; exact (Complex.normSq_eq_norm_sq _).symm
    have hd : ∀ ℓ ∈ Finset.range L, ∀ j ∈ Finset.range L,
        ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)),
          w (p - a * ↑ℓ) * (starRingEnd ℂ) (w (p - a * ↑j))
          = ∑ m ∈ Finset.Icc (1:ℤ) N,
              w m * (starRingEnd ℂ) (w (m + a * ((ℓ:ℤ) - (j:ℤ)))) := by
      intro ℓ hℓ j hj
      rw [Finset.mem_range] at hℓ hj
      have step1 : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)),
            w (p - a * ↑ℓ) * (starRingEnd ℂ) (w (p - a * ↑j))
          = ∑ m ∈ Finset.Icc (1 + -(a * ↑ℓ)) (N + a * ((L:ℤ) - 1) + -(a * ↑ℓ)),
              w m * (starRingEnd ℂ) (w (m + a * ((ℓ:ℤ) - (j:ℤ)))) := by
        rw [← Finset.map_add_right_Icc (1:ℤ) (N + a * ((L:ℤ) - 1)) (-(a * ↑ℓ)), Finset.sum_map]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [addRightEmbedding_apply,
          show p + -(a * ↑ℓ) + a * ((ℓ:ℤ) - ↑j) = p - a * ↑j from by ring,
          show p + -(a * ↑ℓ) = p - a * ↑ℓ from by ring]
      rw [step1]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro k hk
        rw [Finset.mem_Icc] at hk ⊢
        have h1 : (0:ℤ) ≤ a * ↑ℓ := mul_nonneg (by linarith) (Int.natCast_nonneg _)
        have h2 : a * ↑ℓ ≤ a * ((L:ℤ) - 1) := mul_le_mul_of_nonneg_left (by omega) (by linarith)
        constructor <;> linarith [hk.1, hk.2]
      · intro k _ hk
        have : w k = 0 := by by_contra h; exact hk (hsupp k h)
        rw [this, zero_mul]
    have hcomplex : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)),
          (∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
            w (p - a * ↑ℓ) * (starRingEnd ℂ) (w (p - a * ↑j)))
        = ∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
            ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * ((ℓ:ℤ) - (j:ℤ)))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j hj => hd ℓ hℓ j hj)
    rw [Finset.sum_congr rfl (fun p _ => hpe p), ← Complex.re_sum, hcomplex]
  have hcount : ∀ F : ℤ → ℂ,
      ∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L, F ((ℓ:ℤ) - (j:ℤ))
        = ∑ e ∈ Finset.range L, ((L - e : ℕ):ℂ) * F (e:ℤ)
          + ∑ e ∈ Finset.Icc 1 (L-1), ((L - e : ℕ):ℂ) * F (-(e:ℤ)) := by
    intro F
    have hsplit : ∀ ℓ ∈ Finset.range L,
        ∑ j ∈ Finset.range L, F ((ℓ:ℤ) - (j:ℤ))
          = (∑ j ∈ Finset.range (ℓ + 1), F ((ℓ:ℤ) - (j:ℤ)))
            + ∑ j ∈ Finset.Ico (ℓ + 1) L, F ((ℓ:ℤ) - (j:ℤ)) := by
      intro ℓ hℓ; rw [Finset.mem_range] at hℓ
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : ℓ + 1 ≤ L)]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    · have hinner : ∀ ℓ : ℕ, ∑ j ∈ Finset.range (ℓ + 1), F ((ℓ:ℤ) - (j:ℤ))
          = ∑ e ∈ Finset.range (ℓ + 1), F (e:ℤ) := by
        intro ℓ
        rw [← Finset.sum_range_reflect (fun e => F (e:ℤ)) (ℓ + 1)]
        exact Finset.sum_congr rfl (fun j hj => by rw [Finset.mem_range] at hj; congr 1; omega)
      rw [Finset.sum_congr rfl (fun ℓ _ => hinner ℓ)]
      have hfilt : ∀ ℓ ∈ Finset.range L, ∑ e ∈ Finset.range (ℓ + 1), F (e:ℤ)
          = ∑ e ∈ Finset.range L, (if e ≤ ℓ then F (e:ℤ) else 0) := by
        intro ℓ hℓ; rw [Finset.mem_range] at hℓ
        rw [← Finset.sum_filter]
        exact Finset.sum_congr (by ext e; simp only [Finset.mem_range, Finset.mem_filter]; omega)
          (fun _ _ => rfl)
      rw [Finset.sum_congr rfl hfilt, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [Finset.mem_range] at he
      rw [← Finset.sum_filter, Finset.sum_const,
        show (Finset.range L).filter (fun ℓ => e ≤ ℓ) = Finset.Ico e L from by
          ext ℓ; simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Ico]; omega,
        Nat.card_Ico, nsmul_eq_mul]
    · have hinner : ∀ ℓ ∈ Finset.range L, ∑ j ∈ Finset.Ico (ℓ + 1) L, F ((ℓ:ℤ) - (j:ℤ))
          = ∑ e ∈ Finset.Ico 1 (L - ℓ), F (-(e:ℤ)) := by
        intro ℓ hℓ; rw [Finset.mem_range] at hℓ
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by rw [show L - (ℓ + 1) = L - ℓ - 1 from by omega]) (fun i _ => ?_)
        congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hinner]
      have hfilt : ∀ ℓ ∈ Finset.range L, ∑ e ∈ Finset.Ico 1 (L - ℓ), F (-(e:ℤ))
          = ∑ e ∈ Finset.Icc 1 (L - 1), (if ℓ < L - e then F (-(e:ℤ)) else 0) := by
        intro ℓ hℓ; rw [Finset.mem_range] at hℓ
        rw [← Finset.sum_filter]
        exact Finset.sum_congr
          (by ext e; simp only [Finset.mem_Ico, Finset.mem_Icc, Finset.mem_filter]; omega)
          (fun _ _ => rfl)
      rw [Finset.sum_congr rfl hfilt, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [Finset.mem_Icc] at he
      rw [← Finset.sum_filter, Finset.sum_const,
        show (Finset.range L).filter (fun ℓ => ℓ < L - e) = Finset.range (L - e) from by
          ext ℓ; simp only [Finset.mem_range, Finset.mem_filter]; omega,
        Finset.card_range, nsmul_eq_mul]
  have hC0 : (f0 0).re = ∑ k ∈ Finset.Icc (1:ℤ) N, ‖w k‖^2 := by
    show (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * 0))).re = _
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun m _ => by
      rw [mul_zero, add_zero, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq])
  have hrestr : ∀ e : ℤ, 1 ≤ e → (f0 e).re
      = (∑ m ∈ Finset.Icc (1:ℤ) (N - a * e), w m * (starRingEnd ℂ) (w (m + a * e))).re := by
    intro e he
    show (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * e))).re = _
    congr 1
    refine (Finset.sum_subset (fun k hk => ?_) (fun k hkN hk => ?_)).symm
    · rw [Finset.mem_Icc] at hk ⊢
      have : (0:ℤ) ≤ a * e := mul_nonneg (by linarith) (by linarith)
      exact ⟨hk.1, by linarith [hk.2]⟩
    · rw [Finset.mem_Icc] at hkN hk; push Not at hk
      have hlt : N - a * e < k := hk hkN.1
      have hz : w (k + a * e) = 0 := by
        by_contra h; have h2 := hsupp _ h; rw [Finset.mem_Icc] at h2; omega
      rw [hz, map_zero, mul_zero]
  have hsym : ∀ e : ℤ, 1 ≤ e → (f0 (-e)).re = (f0 e).re := by
    intro e he
    show (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * (-e)))).re
        = (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * e))).re
    have hae : (0:ℤ) ≤ a * e := mul_nonneg (by linarith) (by linarith)
    have hLHS : ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * (-e)))
        = ∑ m ∈ Finset.Icc (1:ℤ) (N - a * e), w (m + a * e) * (starRingEnd ℂ) (w m) := by
      have hdrop : ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * (-e)))
          = ∑ m ∈ Finset.Icc (1 + a * e) N, w m * (starRingEnd ℂ) (w (m + a * (-e))) := by
        refine (Finset.sum_subset (fun k hk => ?_) (fun k hkN hk => ?_)).symm
        · rw [Finset.mem_Icc] at hk ⊢; exact ⟨by linarith [hk.1], hk.2⟩
        · rw [Finset.mem_Icc] at hkN hk
          have hz : w (k + a * (-e)) = 0 := by
            by_contra h; have h2 := hsupp _ h; rw [Finset.mem_Icc, mul_neg] at h2; omega
          rw [hz, map_zero, mul_zero]
      rw [hdrop,
        show Finset.Icc (1 + a * e) N = (Finset.Icc (1:ℤ) (N - a * e)).map (addRightEmbedding (a * e))
          from by rw [Finset.map_add_right_Icc]; congr 1; ring,
        Finset.sum_map]
      exact Finset.sum_congr rfl (fun m' _ => by
        rw [addRightEmbedding_apply, show m' + a * e + a * (-e) = m' from by ring])
    have hRHS : (starRingEnd ℂ) (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * e)))
        = ∑ m ∈ Finset.Icc (1:ℤ) (N - a * e), w (m + a * e) * (starRingEnd ℂ) (w m) := by
      rw [map_sum]
      have hdrop : ∑ m ∈ Finset.Icc (1:ℤ) N, (starRingEnd ℂ) (w m * (starRingEnd ℂ) (w (m + a * e)))
          = ∑ m ∈ Finset.Icc (1:ℤ) (N - a * e),
              (starRingEnd ℂ) (w m * (starRingEnd ℂ) (w (m + a * e))) := by
        refine (Finset.sum_subset (fun k hk => ?_) (fun k hkN hk => ?_)).symm
        · rw [Finset.mem_Icc] at hk ⊢; exact ⟨hk.1, by linarith [hk.2]⟩
        · rw [Finset.mem_Icc] at hkN hk; push Not at hk
          have hlt : N - a * e < k := hk hkN.1
          have hz : w (k + a * e) = 0 := by
            by_contra h; have h2 := hsupp _ h; rw [Finset.mem_Icc] at h2; omega
          rw [hz, map_zero, mul_zero, map_zero]
      rw [hdrop]
      exact Finset.sum_congr rfl (fun m _ => by rw [map_mul, Complex.conj_conj, mul_comm])
    rw [← Complex.conj_re (∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * e))),
      hRHS, ← hLHS]
  have hkey : ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)),
        ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2
      = (L:ℝ) * (∑ k ∈ Finset.Icc (1:ℤ) N, ‖w k‖^2)
        + 2 * ∑ e ∈ Finset.Icc 1 (L - 1), ((L:ℝ) - (e:ℝ)) *
            (∑ m ∈ Finset.Icc (1:ℤ) (N - a * (e:ℤ)),
              w m * (starRingEnd ℂ) (w (m + a * (e:ℤ)))).re := by
    rw [hexp,
      show (∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L,
            ∑ m ∈ Finset.Icc (1:ℤ) N, w m * (starRingEnd ℂ) (w (m + a * ((ℓ:ℤ) - (j:ℤ)))))
          = ∑ ℓ ∈ Finset.range L, ∑ j ∈ Finset.range L, f0 ((ℓ:ℤ) - (j:ℤ)) from rfl,
      hcount f0]
    have hterm : ∀ (n : ℕ) (z : ℂ), ((n:ℂ) * z).re = (n:ℝ) * z.re := fun n z => by
      simp [Complex.mul_re]
    rw [Complex.add_re, Complex.re_sum, Complex.re_sum]
    simp only [hterm]
    have hsnd : ∑ e ∈ Finset.Icc 1 (L - 1), ((L - e : ℕ):ℝ) * (f0 (-(e:ℤ))).re
        = ∑ e ∈ Finset.Icc 1 (L - 1), ((L - e : ℕ):ℝ) * (f0 (e:ℤ)).re :=
      Finset.sum_congr rfl (fun e he => by
        rw [Finset.mem_Icc] at he; rw [hsym (e:ℤ) (by exact_mod_cast he.1)])
    have hsplitr : Finset.range L = insert 0 (Finset.Icc 1 (L - 1)) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplitr, Finset.sum_insert (by simp), hsnd]
    have h0 : ((L - 0 : ℕ):ℝ) * (f0 ((0:ℕ):ℤ)).re
        = (L:ℝ) * ∑ k ∈ Finset.Icc (1:ℤ) N, ‖w k‖^2 := by
      rw [Nat.sub_zero, Nat.cast_zero, hC0]
    rw [h0]
    have hper : ∀ e ∈ Finset.Icc 1 (L - 1), ((L - e : ℕ):ℝ) * (f0 (e:ℤ)).re
        = ((L:ℝ) - (e:ℝ)) * (∑ m ∈ Finset.Icc (1:ℤ) (N - a * (e:ℤ)),
              w m * (starRingEnd ℂ) (w (m + a * (e:ℤ)))).re :=
      fun e he => by
        rw [Finset.mem_Icc] at he
        rw [hrestr (e:ℤ) (by exact_mod_cast he.1), Nat.cast_sub (by omega)]
    rw [Finset.sum_congr rfl hper]; ring
  calc (L:ℝ)^2 * ‖∑ k ∈ Finset.Icc (1:ℤ) N, w k‖^2
      ≤ (↑(N + a * ((L:ℤ) - 1)):ℝ)
        * ∑ p ∈ Finset.Icc (1:ℤ) (N + a * ((L:ℤ) - 1)), ‖∑ ℓ ∈ Finset.range L, w (p - a * ↑ℓ)‖^2 :=
        hCS
    _ = (↑(N + a * ((L:ℤ) - 1)):ℝ) * ((L:ℝ) * (∑ k ∈ Finset.Icc (1:ℤ) N, ‖w k‖^2)
        + 2 * ∑ e ∈ Finset.Icc 1 (L - 1), ((L:ℝ) - (e:ℝ)) *
            (∑ m ∈ Finset.Icc (1:ℤ) (N - a * (e:ℤ)),
              w m * (starRingEnd ℂ) (w (m + a * (e:ℤ)))).re) := by rw [hkey]
    _ = _ := by ring

/-- **van der Corput's fundamental inequality** (with step `a`). Let `a, N` be positive integers,
`u₁, …, u_N` complex numbers, and `L` a positive integer with `aL ≤ N`. Then
`L² · ‖∑_{n=1}^N uₙ‖² ≤ L (N + a(L-1)) · ∑_{n=1}^N ‖uₙ‖²`
`  + 2 (N + a(L-1)) · ∑_{ℓ=1}^{L-1} (L-ℓ) · Re ∑_{n=1}^{N-aℓ} uₙ · conj(u_{n+aℓ})`. -/
theorem vanDerCorput_fundamental_inequality (a N : ℕ) (ha : 0 < a) (u : ℕ → ℂ) (L : ℕ)
    (hL : 1 ≤ a * L) (hLN : a * L ≤ N) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.Icc 1 N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) * ∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) *
        ∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (N - a * ℓ), u n * (starRingEnd ℂ) (u (n + a * ℓ))).re := by
  classical
  have hcast : ∀ {M : Type} [AddCommMonoid M] (P : ℕ) (f : ℤ → M),
      ∑ k ∈ Finset.Icc (1:ℤ) (P:ℤ), f k = ∑ n ∈ Finset.Icc 1 P, f (n:ℤ) := by
    intro M _ P f
    rw [show Finset.Icc (1:ℤ) (P:ℤ) = (Finset.Icc 1 P).image (fun n : ℕ => (n:ℤ)) from by
        ext k; simp only [Finset.mem_image, Finset.mem_Icc]
        exact ⟨fun ⟨h1, h2⟩ => ⟨k.toNat, ⟨by omega, by omega⟩, by omega⟩,
          fun ⟨n, ⟨h1, h2⟩, hk⟩ => hk ▸ ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩⟩,
      Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]
  set w : ℤ → ℂ := fun k => if 1 ≤ k ∧ k ≤ (N:ℤ) then u k.toNat else 0 with hw
  have hLge1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hL)
  have hwn : ∀ n : ℕ, 1 ≤ n → n ≤ N → w (n:ℤ) = u n := by
    intro n h1 h2
    simp only [hw]
    rw [if_pos ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, Int.toNat_natCast]
  have hsupp : ∀ k, w k ≠ 0 → k ∈ Finset.Icc (1:ℤ) (N:ℤ) := by
    intro k hk; by_contra hc; rw [Finset.mem_Icc] at hc
    simp only [hw] at hk; rw [if_neg hc] at hk; exact hk rfl
  have hcore := vanDerCorput_core (a:ℤ) (N:ℤ) L (by exact_mod_cast ha) hLge1
    (by exact_mod_cast hLN) w hsupp
  have e1 : ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), w k = ∑ n ∈ Finset.Icc 1 N, u n := by
    rw [hcast]; exact Finset.sum_congr rfl (fun n hn => by
      rw [Finset.mem_Icc] at hn; rw [hwn n hn.1 hn.2])
  have e2 : ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), ‖w k‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2 := by
    rw [hcast]; exact Finset.sum_congr rfl (fun n hn => by
      rw [Finset.mem_Icc] at hn; rw [hwn n hn.1 hn.2])
  have e3 : ∀ ℓ ∈ Finset.Icc 1 (L - 1),
      ((L:ℝ) - (ℓ:ℝ)) * (∑ m ∈ Finset.Icc (1:ℤ) ((N:ℤ) - (a:ℤ) * (ℓ:ℤ)),
          w m * (starRingEnd ℂ) (w (m + (a:ℤ) * (ℓ:ℤ)))).re
      = ((L:ℝ) - (ℓ:ℝ)) * (∑ n ∈ Finset.Icc 1 (N - a * ℓ),
          u n * (starRingEnd ℂ) (u (n + a * ℓ))).re := by
    intro ℓ hℓ; rw [Finset.mem_Icc] at hℓ
    have hℓL : ℓ ≤ L := by omega
    have haℓ : a * ℓ ≤ N := le_trans (by gcongr) hLN
    have hcorr : (∑ m ∈ Finset.Icc (1:ℤ) ((N:ℤ) - (a:ℤ) * (ℓ:ℤ)),
          w m * (starRingEnd ℂ) (w (m + (a:ℤ) * (ℓ:ℤ))))
        = ∑ n ∈ Finset.Icc 1 (N - a * ℓ), u n * (starRingEnd ℂ) (u (n + a * ℓ)) := by
      rw [show (N:ℤ) - (a:ℤ) * (ℓ:ℤ) = ((N - a * ℓ : ℕ):ℤ) from by
          rw [Nat.cast_sub haℓ]; push_cast; ring, hcast (N - a * ℓ) _]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      rw [hwn n hn.1 (by omega),
        show (n:ℤ) + (a:ℤ) * (ℓ:ℤ) = ((n + a * ℓ : ℕ):ℤ) from by push_cast; ring,
        hwn (n + a * ℓ) (by omega) (by omega)]
    rw [hcorr]
  rw [e1, e2, Finset.sum_congr rfl e3] at hcore
  have hcoef : (↑((N:ℤ) + (a:ℤ) * ((L:ℤ) - 1)) : ℝ) = (N:ℝ) + (a:ℝ) * ((L:ℝ) - 1) := by
    push_cast; ring
  rw [hcoef] at hcore
  exact hcore

