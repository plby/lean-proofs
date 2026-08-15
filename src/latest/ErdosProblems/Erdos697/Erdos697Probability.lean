/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Finite probability estimates for Erdős Problem 697

This file contains only elementary finite-sum arguments.  In particular,
the estimates do not use Mathlib's measure-theoretic probability API, which
makes them convenient for the exact CRT models used in the main proof.
-/

open scoped BigOperators

namespace Erdos697.Probability

noncomputable section

/-- Chebyshev's inequality for an explicitly weighted finite sample space. -/
theorem finite_chebyshev {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → ℝ) (μ V t : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hsecond : (∑ x, w x * (X x - μ) ^ 2) ≤ V)
    (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|), w x) ≤ V / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  calc
    (∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|), w x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|),
            (w x * (X x - μ) ^ 2) / t ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hxlarge : t ≤ |X x - μ| := (Finset.mem_filter.mp hx).2
          have hsquare : t ^ 2 ≤ (X x - μ) ^ 2 := by
            nlinarith [sq_nonneg (|X x - μ| - t), sq_abs (X x - μ)]
          have hmul : w x * t ^ 2 ≤ w x * (X x - μ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquare (hw x)
          exact (le_div_iff₀ ht2).2 (by simpa [mul_comm] using hmul)
    _ = (∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|),
            w x * (X x - μ) ^ 2) / t ^ 2 := by
          rw [Finset.sum_div]
    _ ≤ (∑ x, w x * (X x - μ) ^ 2) / t ^ 2 := by
          apply div_le_div_of_nonneg_right _ ht2.le
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact (Finset.mem_filter.mp hx).1
          · intro x _ _
            exact mul_nonneg (hw x) (sq_nonneg _)
    _ ≤ V / t ^ 2 := div_le_div_of_nonneg_right hsecond ht2.le

/-- A one-sided lower tail is contained in the corresponding absolute tail. -/
theorem finite_lower_tail_le_chebyshev {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → ℝ) (μ V t : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hsecond : (∑ x, w x * (X x - μ) ^ 2) ≤ V)
    (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter (fun x => X x ≤ μ - t), w x) ≤ V / t ^ 2 := by
  calc
    (∑ x ∈ Finset.univ.filter (fun x => X x ≤ μ - t), w x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|), w x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            have hle : X x ≤ μ - t := (Finset.mem_filter.mp hx).2
            have habs : t ≤ |X x - μ| := by
              rw [abs_of_nonpos (by linarith)]
              linarith
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, habs⟩
          · intro x _ _
            exact hw x
    _ ≤ V / t ^ 2 := finite_chebyshev w X μ V t hw hsecond ht

/-- A one-sided upper tail is contained in the corresponding absolute tail. -/
theorem finite_upper_tail_le_chebyshev {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → ℝ) (μ V t : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hsecond : (∑ x, w x * (X x - μ) ^ 2) ≤ V)
    (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter (fun x => μ + t ≤ X x), w x) ≤ V / t ^ 2 := by
  calc
    (∑ x ∈ Finset.univ.filter (fun x => μ + t ≤ X x), w x)
        ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ |X x - μ|), w x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            have hle : μ + t ≤ X x := (Finset.mem_filter.mp hx).2
            have habs : t ≤ |X x - μ| := by
              rw [abs_of_nonneg (by linarith)]
              linarith
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, habs⟩
          · intro x _ _
            exact hw x
    _ ≤ V / t ^ 2 := finite_chebyshev w X μ V t hw hsecond ht

/-- Triangle inequality for product measures.  The `L¹` distance between
two product measures is at most the sum of the marginal `L¹` distances. -/
theorem prod_tv_le_sum_tv {G : Type*} [Fintype G] [DecidableEq G]
    {K : ℕ} (f : Fin K → G → ℝ) (u : G → ℝ)
    (hu_nn : ∀ g, 0 ≤ u g)
    (hu_sum : (∑ g, u g) = 1)
    (hf_nn : ∀ i g, 0 ≤ f i g)
    (hf_sum : ∀ i, (∑ g, f i g) = 1)
    (ε : ℝ)
    (h_tv : ∀ i, (∑ g, |f i g - u g|) ≤ ε) :
    (∑ gvec : Fin K → G,
      |(∏ i, f i (gvec i)) - (∏ i, u (gvec i))|) ≤ K * ε := by
  induction K with
  | zero =>
    simp [Finset.prod_empty, sub_self, abs_zero]
  | succ K ih =>
    have h_sum_split : (∑ gvec : Fin (K + 1) → G,
        |(∏ i, f i (gvec i)) - (∏ i, u (gvec i))|) =
      ∑ p : G × (Fin K → G),
        |(∏ i : Fin (K + 1),
            f i ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i)) -
         (∏ i : Fin (K + 1),
            u ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i))| := by
      apply Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (K + 1) => G)).symm
      intro gvec
      have h_eq :
          (Fin.cons
            ((Fin.consEquiv (fun _ : Fin (K + 1) => G)).symm gvec).1
            ((Fin.consEquiv (fun _ : Fin (K + 1) => G)).symm gvec).2 :
              Fin (K + 1) → G) = gvec := by
        ext i
        simp [Fin.consEquiv, Fin.cons_self_tail]
      rw [h_eq]
    rw [h_sum_split]
    have h_prod_expand : ∀ p : G × (Fin K → G),
        (∏ i : Fin (K + 1),
          f i ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i)) =
        f 0 p.1 * ∏ i : Fin K, f i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    have h_prod_expand_u : ∀ p : G × (Fin K → G),
        (∏ i : Fin (K + 1),
          u ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i)) =
        u p.1 * ∏ i : Fin K, u (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    have h_pointwise : ∀ p : G × (Fin K → G),
        |(∏ i : Fin (K + 1),
            f i ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i)) -
         (∏ i : Fin (K + 1),
            u ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i))| ≤
        |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
        f 0 p.1 *
          |(∏ i : Fin K, f i.succ (p.2 i)) -
            (∏ i : Fin K, u (p.2 i))| := by
      intro p
      rw [h_prod_expand p, h_prod_expand_u p]
      have ha_nn : 0 ≤ f 0 p.1 := hf_nn 0 p.1
      have hd_nn : 0 ≤ ∏ i : Fin K, u (p.2 i) :=
        Finset.prod_nonneg (fun i _ => hu_nn (p.2 i))
      calc
        |f 0 p.1 * (∏ i : Fin K, f i.succ (p.2 i)) -
            u p.1 * (∏ i : Fin K, u (p.2 i))| =
            |f 0 p.1 *
                ((∏ i : Fin K, f i.succ (p.2 i)) -
                  (∏ i : Fin K, u (p.2 i))) +
              (f 0 p.1 - u p.1) *
                (∏ i : Fin K, u (p.2 i))| := by ring_nf
        _ ≤ |f 0 p.1 *
                ((∏ i : Fin K, f i.succ (p.2 i)) -
                  (∏ i : Fin K, u (p.2 i)))| +
              |(f 0 p.1 - u p.1) *
                (∏ i : Fin K, u (p.2 i))| := abs_add_le _ _
        _ = f 0 p.1 *
                |(∏ i : Fin K, f i.succ (p.2 i)) -
                  (∏ i : Fin K, u (p.2 i))| +
              |f 0 p.1 - u p.1| *
                (∏ i : Fin K, u (p.2 i)) := by
              rw [abs_mul, abs_of_nonneg ha_nn, abs_mul,
                abs_of_nonneg hd_nn]
        _ = |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
              f 0 p.1 *
                |(∏ i : Fin K, f i.succ (p.2 i)) -
                  (∏ i : Fin K, u (p.2 i))| := by ring
    have h_sum_le :
        (∑ p : G × (Fin K → G),
          |(∏ i : Fin (K + 1),
              f i ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i)) -
           (∏ i : Fin (K + 1),
              u ((Fin.cons p.1 p.2 : Fin (K + 1) → G) i))|) ≤
        (∑ p : G × (Fin K → G),
          (|f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
           f 0 p.1 *
            |(∏ i : Fin K, f i.succ (p.2 i)) -
              (∏ i : Fin K, u (p.2 i))|)) :=
      Finset.sum_le_sum (fun p _ => h_pointwise p)
    refine le_trans h_sum_le ?_
    rw [Finset.sum_add_distrib]
    have h_sum_prod_u :
        (∑ tail : Fin K → G, ∏ i : Fin K, u (tail i)) = 1 := by
      rw [← Fintype.piFinset_univ]
      rw [← Finset.prod_univ_sum
        (fun _ : Fin K => (Finset.univ : Finset G)) (fun _ x => u x)]
      simp [hu_sum]
    have h_term1_split :
        (∑ p : G × (Fin K → G),
          |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i))) =
        (∑ g₀ : G, |f 0 g₀ - u g₀|) *
          (∑ tail : Fin K → G, ∏ i : Fin K, u (tail i)) := by
      rw [Finset.sum_mul_sum]
      exact Fintype.sum_prod_type'
        (fun (g₀ : G) (tail : Fin K → G) =>
          |f 0 g₀ - u g₀| * ∏ i : Fin K, u (tail i))
    have h_term1_le :
        (∑ p : G × (Fin K → G),
          |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i))) ≤ ε := by
      rw [h_term1_split, h_sum_prod_u, mul_one]
      exact h_tv 0
    have h_term2_split :
        (∑ p : G × (Fin K → G),
          f 0 p.1 *
            |(∏ i : Fin K, f i.succ (p.2 i)) -
              (∏ i : Fin K, u (p.2 i))|) =
        (∑ g₀ : G, f 0 g₀) *
          (∑ tail : Fin K → G,
            |(∏ i : Fin K, f i.succ (tail i)) -
              (∏ i : Fin K, u (tail i))|) := by
      rw [Finset.sum_mul_sum]
      exact Fintype.sum_prod_type'
        (fun (g₀ : G) (tail : Fin K → G) =>
          f 0 g₀ *
            |(∏ i : Fin K, f i.succ (tail i)) -
              (∏ i : Fin K, u (tail i))|)
    have h_ih_applied :
        (∑ tail : Fin K → G,
          |(∏ i : Fin K, f i.succ (tail i)) -
            (∏ i : Fin K, u (tail i))|) ≤ K * ε :=
      ih (fun i => f i.succ) (fun i g => hf_nn i.succ g)
        (fun i => hf_sum i.succ) (fun i => h_tv i.succ)
    have h_term2_le :
        (∑ p : G × (Fin K → G),
          f 0 p.1 *
            |(∏ i : Fin K, f i.succ (p.2 i)) -
              (∏ i : Fin K, u (p.2 i))|) ≤ K * ε := by
      rw [h_term2_split, hf_sum 0, one_mul]
      exact h_ih_applied
    have hKε_succ : (K : ℝ) * ε + ε = (↑(K + 1)) * ε := by
      push_cast
      ring
    linarith

end

end Erdos697.Probability
