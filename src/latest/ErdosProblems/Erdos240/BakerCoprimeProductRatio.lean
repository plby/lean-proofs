/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeFactorialCancellation
import ErdosProblems.Erdos240.CoprimeHermiteBasis

/-!
# The factorial-cancelled product ratio for coprime nodes

For the positive integer nodes at most `R` which are coprime to a prime
`q`, this file compares the nodal product at a deleted multiple of `q` with
the spacing product at a retained node.  Splitting off all multiples of `q`
turns the comparison into exactly the two factorial ratios proved in
`BakerCoprimeFactorialCancellation`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeProductRatio

open Complex Finset Polynomial
open BakerCoprimeInterpolation BakerCoprimeFactorialCancellation
open CoprimeHermiteBasis InterpolationProducts

/-- Distance from the positive integer node indexed by `i` to `x`. -/
private def nodeDistance (x i : ℕ) : ℝ :=
  ‖(x : ℂ) - ((i + 1 : ℕ) : ℂ)‖

private theorem nodeDistance_eq_abs (x i : ℕ) :
    nodeDistance x i = |(x : ℝ) - (i + 1 : ℕ)| := by
  rw [nodeDistance, show (x : ℂ) - ((i + 1 : ℕ) : ℂ) =
    (((x : ℝ) - (i + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

/-- The product of all noncentral spacings in the full integer grid is the
usual pair of factorials. -/
private theorem prod_range_erase_nodeDistance_eq_factorial_pair
    {R x : ℕ} (hx : 1 ≤ x) (hxR : x ≤ R) :
    ∏ i ∈ (range R).erase (x - 1), nodeDistance x i =
      (x - 1).factorial * (R - x).factorial := by
  have hsets : (range R).erase (x - 1) =
      range (x - 1) ∪ Ico x R := by
    ext i
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range (x - 1)) (Ico x R) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [mem_range] at hi
    simp only [mem_Ico] at hj
    omega
  rw [hsets, prod_union hdisj]
  have hleft : ∏ i ∈ range (x - 1), nodeDistance x i =
      ((x - 1).factorial : ℝ) := by
    rw [← prod_range_cast_sub_eq_factorial (x - 1)]
    apply prod_congr rfl
    intro i hi
    have hix : i + 1 ≤ x := by
      have hi' := mem_range.mp hi
      omega
    rw [nodeDistance, ← Nat.cast_sub hix, Complex.norm_natCast]
    norm_cast
    omega
  have hright : ∏ i ∈ Ico x R, nodeDistance x i =
      ((R - x).factorial : ℝ) := by
    rw [prod_Ico_eq_prod_range]
    rw [← prod_range_cast_add_one_eq_factorial (R - x)]
    apply prod_congr rfl
    intro i hi
    have hxi : x ≤ x + i + 1 := by omega
    rw [nodeDistance, norm_sub_rev, ← Nat.cast_sub hxi, Complex.norm_natCast]
    congr 1
    omega
  rw [hleft, hright]

/-- For prime `q`, the indices of deleted nodes in `1,…,qM` are exactly
`q(k+1)-1`, for `k < M`. -/
private theorem prod_deleted_indices_eq_prod_range
    {q M : ℕ} (hq : q.Prime) (f : ℕ → ℝ) :
    ∏ i ∈ (range (q * M)).filter (fun i ↦ ¬ (i + 1).Coprime q), f i =
      ∏ k ∈ range M, f (q * (k + 1) - 1) := by
  symm
  refine Finset.prod_bij (fun k _ ↦ q * (k + 1) - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hkM : k + 1 ≤ M := by simpa only [mem_range] using Nat.succ_le_iff.mpr (mem_range.mp hk)
    have hpos : 0 < q * (k + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k)
    have hle : q * (k + 1) ≤ q * M := Nat.mul_le_mul_left q hkM
    simp only [mem_filter, mem_range]
    constructor
    · omega
    · have hdvd : q ∣ q * (k + 1) := dvd_mul_right q (k + 1)
      have hnot : ¬ (q * (k + 1)).Coprime q := by
        rw [Nat.coprime_comm, ← hq.dvd_iff_not_coprime]
        exact hdvd
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
      exact hnot
  · intro k₁ hk₁ k₂ hk₂ heq
    have hp₁ : 0 < q * (k₁ + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k₁)
    have hp₂ : 0 < q * (k₂ + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k₂)
    have : q * (k₁ + 1) = q * (k₂ + 1) := by omega
    have := Nat.mul_left_cancel hq.pos this
    omega
  · intro i hi
    rw [mem_filter] at hi
    have hdiv : q ∣ i + 1 := by
      rw [hq.dvd_iff_not_coprime]
      simpa [Nat.coprime_comm] using hi.2
    obtain ⟨u, hu⟩ := hdiv
    have hu0 : 0 < u := by
      by_contra h
      simp only [not_lt] at h
      have : u = 0 := Nat.eq_zero_of_le_zero h
      subst u
      simp at hu
    have hiR : i < q * M := mem_range.mp hi.1
    have huM : u ≤ M := by
      apply Nat.le_of_mul_le_mul_left (c := q) _ hq.pos
      omega
    refine ⟨u - 1, by simp only [mem_range]; omega, ?_⟩
    have hqu : 0 < q * u := Nat.mul_pos hq.pos hu0
    rw [Nat.sub_add_cancel hu0]
    omega
  · intro k hk
    rfl

/-- The preceding reindexing remains valid after deleting the central
multiple `qt`. -/
private theorem prod_deleted_indices_erase_eq_prod_range_erase
    {q M t : ℕ} (hq : q.Prime) (ht : 1 ≤ t) (f : ℕ → ℝ) :
    ∏ i ∈ ((range (q * M)).filter
        (fun i ↦ ¬ (i + 1).Coprime q)).erase (q * t - 1), f i =
      ∏ k ∈ (range M).erase (t - 1), f (q * (k + 1) - 1) := by
  symm
  refine Finset.prod_bij (fun k _ ↦ q * (k + 1) - 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_erase] at hk ⊢
    refine ⟨?_, ?_⟩
    · intro heq
      have hkpos : 0 < q * (k + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k)
      have htpos : 0 < q * t := Nat.mul_pos hq.pos (by omega)
      have hmul : q * (k + 1) = q * t := by omega
      have : k + 1 = t := Nat.mul_left_cancel hq.pos hmul
      omega
    · have hkM : k + 1 ≤ M := by
        rw [mem_range] at hk
        omega
      have hpos : 0 < q * (k + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k)
      have hle : q * (k + 1) ≤ q * M := Nat.mul_le_mul_left q hkM
      simp only [mem_filter, mem_range]
      constructor
      · omega
      · have hdvd : q ∣ q * (k + 1) := dvd_mul_right q (k + 1)
        rw [Nat.coprime_comm, ← hq.dvd_iff_not_coprime]
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
        exact hdvd
  · intro k₁ hk₁ k₂ hk₂ heq
    have hp₁ : 0 < q * (k₁ + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k₁)
    have hp₂ : 0 < q * (k₂ + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k₂)
    have : q * (k₁ + 1) = q * (k₂ + 1) := by omega
    have := Nat.mul_left_cancel hq.pos this
    omega
  · intro i hi
    rw [mem_erase] at hi
    rw [mem_filter] at hi
    have hdiv : q ∣ i + 1 := by
      rw [hq.dvd_iff_not_coprime]
      simpa [Nat.coprime_comm] using hi.2.2
    obtain ⟨u, hu⟩ := hdiv
    have hu0 : 0 < u := by
      by_contra h
      simp only [not_lt] at h
      have : u = 0 := Nat.eq_zero_of_le_zero h
      subst u
      simp at hu
    have hiR : i < q * M := mem_range.mp hi.2.1
    have huM : u ≤ M := by
      apply Nat.le_of_mul_le_mul_left (c := q) _ hq.pos
      omega
    have hut : u ≠ t := by
      intro hut
      subst u
      have hqt : 0 < q * t := Nat.mul_pos hq.pos (by omega)
      apply hi.1
      omega
    refine ⟨u - 1, ?_, ?_⟩
    · rw [mem_erase]
      constructor
      · omega
      · rw [mem_range]
        omega
    · have hqu : 0 < q * u := Nat.mul_pos hq.pos hu0
      rw [Nat.sub_add_cancel hu0]
      omega
  · intro k hk
    rfl

private theorem nodeDistance_mul_index (q x k : ℕ) (hq : 0 < q) :
    nodeDistance (q * x) (q * (k + 1) - 1) =
      (q : ℝ) * nodeDistance x k := by
  rw [nodeDistance_eq_abs, nodeDistance_eq_abs]
  have hpos : 0 < q * (k + 1) := Nat.mul_pos hq (Nat.succ_pos k)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
  push_cast
  rw [show (q : ℝ) * x - q * (k + 1) =
    (q : ℝ) * (x - (k + 1)) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)]

/-- Exact deleted-multiple product at a deleted node. -/
private theorem deleted_product_at_multiple
    {q M t : ℕ} (hq : q.Prime) (ht : 1 ≤ t) (htM : t ≤ M) :
    ∏ i ∈ ((range (q * M)).filter
        (fun i ↦ ¬ (i + 1).Coprime q)).erase (q * t - 1),
        nodeDistance (q * t) i =
      (q : ℝ) ^ (M - 1) *
        (((t - 1).factorial : ℝ) * (M - t).factorial) := by
  rw [prod_deleted_indices_erase_eq_prod_range_erase hq ht]
  simp_rw [nodeDistance_mul_index q t _ hq.pos]
  rw [prod_mul_distrib, prod_const]
  have htmem : t - 1 ∈ range M := by simp only [mem_range]; omega
  rw [card_erase_of_mem htmem, card_range]
  rw [prod_range_erase_nodeDistance_eq_factorial_pair ht htM]

/-- At a retained node, the product of its distances from all deleted
multiples is bounded by the corresponding factorial pair after scaling by
`q^M`. -/
private theorem deleted_product_at_coprime_node_le
    {q M a : ℕ} (hq : q.Prime) (haR : a ≤ q * M) :
    ∏ i ∈ (range (q * M)).filter
        (fun i ↦ ¬ (i + 1).Coprime q), nodeDistance a i ≤
      (q : ℝ) ^ M *
        (((a / q).factorial : ℝ) * (M - a / q).factorial) := by
  rw [prod_deleted_indices_eq_prod_range hq]
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hterm (k : ℕ) : nodeDistance a (q * (k + 1) - 1) =
      (q : ℝ) * |(a : ℝ) / q - (k + 1 : ℕ)| := by
    rw [nodeDistance_eq_abs]
    have hpos : 0 < q * (k + 1) := Nat.mul_pos hq.pos (Nat.succ_pos k)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
    push_cast
    rw [show (a : ℝ) - q * (k + 1) =
      (q : ℝ) * ((a : ℝ) / q - (k + 1)) by
        field_simp,
      abs_mul, abs_of_nonneg hqreal.le]
  simp_rw [hterm]
  rw [prod_mul_distrib, prod_const, card_range]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply abs_prod_range_sub_le_factorial_mul_factorial
  · apply (le_div_iff₀ hqreal).2
    exact_mod_cast (by simpa [mul_comm] using Nat.div_mul_le_self a q)
  · apply (div_le_iff₀ hqreal).2
    have hmod : a % q < q := Nat.mod_lt a hq.pos
    have hnat : a ≤ q * (a / q + 1) := by
      calc
        a = q * (a / q) + a % q := (Nat.div_add_mod a q).symm
        _ ≤ q * (a / q) + q := Nat.add_le_add_left (Nat.le_of_lt hmod) _
        _ = q * (a / q + 1) := by ring
    exact_mod_cast (by simpa [mul_comm] using hnat)
  · exact Nat.div_le_of_le_mul (by simpa [mul_comm] using haR)

/-- Splitting the full noncentral grid into retained and deleted nodes at a
deleted multiple. -/
private theorem coprime_mul_deleted_eq_full_at_deleted
    {q R l : ℕ} (hl : 1 ≤ l) (hlq : ¬ l.Coprime q) :
    (∏ i ∈ coprimeNodeIndices q R, nodeDistance l i) *
        (∏ i ∈ ((range R).filter (fun i ↦ ¬ (i + 1).Coprime q)).erase (l - 1),
          nodeDistance l i) =
      ∏ i ∈ (range R).erase (l - 1), nodeDistance l i := by
  rw [← Finset.prod_union]
  · apply prod_congr
    · ext i
      simp only [coprimeNodeIndices, mem_union, mem_filter, mem_range, mem_erase]
      constructor
      · rintro (hi | hi)
        · refine ⟨?_, hi.1⟩
          intro hil
          subst i
          apply hlq
          simpa only [Nat.sub_add_cancel hl] using hi.2
        · exact ⟨hi.1, hi.2.1⟩
      · rintro ⟨hil, hiR⟩
        by_cases hcop : (i + 1).Coprime q
        · exact Or.inl ⟨hiR, hcop⟩
        · exact Or.inr ⟨hil, hiR, hcop⟩
    · intro i hi
      rfl
  · rw [Finset.disjoint_left]
    intro i hi hj
    rw [mem_coprimeNodeIndices] at hi
    rw [mem_erase, mem_filter] at hj
    exact hj.2.2 hi.2

/-- Splitting the full noncentral grid at a retained coprime node. -/
private theorem coprime_erase_mul_deleted_eq_full_at_coprime
    {q R r : ℕ} (hr : r ∈ coprimeNodeIndices q R) :
    (∏ i ∈ (coprimeNodeIndices q R).erase r, nodeDistance (r + 1) i) *
        (∏ i ∈ (range R).filter (fun i ↦ ¬ (i + 1).Coprime q),
          nodeDistance (r + 1) i) =
      ∏ i ∈ (range R).erase r, nodeDistance (r + 1) i := by
  rw [← Finset.prod_union]
  · apply prod_congr
    · ext i
      simp only [coprimeNodeIndices, mem_union, mem_filter, mem_range, mem_erase]
      constructor
      · rintro (hi | hi)
        · exact ⟨hi.1, hi.2.1⟩
        · refine ⟨?_, hi.1⟩
          intro hir
          subst i
          exact hi.2 (mem_coprimeNodeIndices.mp hr).2
      · rintro ⟨hir, hiR⟩
        by_cases hcop : (i + 1).Coprime q
        · exact Or.inl ⟨hir, hiR, hcop⟩
        · exact Or.inr ⟨hiR, hcop⟩
    · intro i hi
      rfl
  · rw [Finset.disjoint_left]
    intro i hi hj
    rw [mem_erase, mem_coprimeNodeIndices] at hi
    rw [mem_filter] at hj
    exact hj.2 hi.2.2

/-- The key coprime-node factorial/product ratio.  The index `r` is
zero-based, so its retained node is `r+1`. -/
theorem norm_finiteNodePolynomial_eval_le
    {q R l r : ℕ} (hq : q.Prime) (hqR : q ∣ R)
    (hl : 1 ≤ l) (hlR : l ≤ R) (hlq : ¬ l.Coprime q)
    (hr : r ∈ coprimeNodeIndices q R) :
    ‖(finiteNodePolynomial (coprimeNodeIndices q R)).eval (l : ℂ)‖ ≤
      ((q : ℝ) * 2 ^ (3 * R)) *
        finiteSpacingProduct (coprimeNodeIndices q R) r := by
  obtain ⟨M, rfl⟩ := hqR
  have hql : q ∣ l := by
    rw [hq.dvd_iff_not_coprime]
    simpa [Nat.coprime_comm] using hlq
  obtain ⟨t, rfl⟩ := hql
  have ht : 1 ≤ t := by
    have : 0 < q * t := hl
    exact Nat.pos_of_mul_pos_left this
  have htM : t ≤ M := by
    exact Nat.le_of_mul_le_mul_left hlR hq.pos
  have hra := mem_coprimeNodeIndices.mp hr
  have hra1 : 1 ≤ r + 1 := Nat.succ_pos r
  have hraR : r + 1 ≤ q * M := Nat.succ_le_iff.mpr hra.1
  let Aₗ : ℝ := ((q * t - 1).factorial : ℝ) * (q * M - q * t).factorial
  let Aᵣ : ℝ := (r.factorial : ℝ) * (q * M - (r + 1)).factorial
  let Bₗ : ℝ := (q : ℝ) ^ (M - 1) *
    (((t - 1).factorial : ℝ) * (M - t).factorial)
  let Bᵣ : ℝ := ∏ i ∈ (range (q * M)).filter
    (fun i ↦ ¬ (i + 1).Coprime q), nodeDistance (r + 1) i
  let N : ℝ := ∏ i ∈ coprimeNodeIndices q (q * M), nodeDistance (q * t) i
  let D : ℝ := ∏ i ∈ (coprimeNodeIndices q (q * M)).erase r,
    nodeDistance (r + 1) i
  have hABl : N * Bₗ = Aₗ := by
    dsimp only [N, Bₗ, Aₗ]
    rw [← deleted_product_at_multiple hq ht htM]
    rw [coprime_mul_deleted_eq_full_at_deleted hl hlq]
    exact prod_range_erase_nodeDistance_eq_factorial_pair hl hlR
  have hABr : D * Bᵣ = Aᵣ := by
    dsimp only [D, Bᵣ, Aᵣ]
    rw [coprime_erase_mul_deleted_eq_full_at_coprime hr]
    simpa only [Nat.add_sub_cancel] using
      (prod_range_erase_nodeDistance_eq_factorial_pair hra1 hraR)
  have hBr : Bᵣ ≤ (q : ℝ) ^ M *
      (((((r + 1) / q).factorial : ℝ) *
        (M - (r + 1) / q).factorial)) := by
    exact deleted_product_at_coprime_node_le hq hraR
  have hfullratio : Aₗ / Aᵣ ≤ (2 : ℝ) ^ (q * M) := by
    exact factorial_pair_div_factorial_pair_le_two_pow hl hlR hra1 hraR
  have hdelratio :
      (((((r + 1) / q).factorial : ℝ) *
          (M - (r + 1) / q).factorial)) /
        (((t - 1).factorial : ℝ) * (M - t).factorial) ≤
          (2 : ℝ) ^ (2 * M) := by
    apply deleted_factorial_pair_div_le_two_pow
    · exact Nat.div_le_of_le_mul (by simpa [mul_comm] using hraR)
    · exact ht
    · exact htM
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hAlpos : 0 < Aₗ := by dsimp only [Aₗ]; positivity
  have hArpos : 0 < Aᵣ := by dsimp only [Aᵣ]; positivity
  have hBlpos : 0 < Bₗ := by dsimp only [Bₗ]; positivity
  have hDrpos : 0 < D := by
    dsimp only [D]
    apply Finset.prod_pos
    intro i hi
    rw [mem_erase] at hi
    exact lt_of_lt_of_le zero_lt_one
      (CoprimeHermiteBasis.one_le_norm_positiveNode_sub_of_ne hi.1.symm)
  have hNratio : N / D = (Aₗ / Aᵣ) * (Bᵣ / Bₗ) := by
    field_simp [hDrpos.ne', hArpos.ne', hBlpos.ne']
    nlinarith [hABl, hABr]
  have hBratio : Bᵣ / Bₗ ≤ (q : ℝ) * (2 : ℝ) ^ (2 * M) := by
    let C : ℝ := (((r + 1) / q).factorial : ℝ) *
      (M - (r + 1) / q).factorial
    let F : ℝ := ((t - 1).factorial : ℝ) * (M - t).factorial
    have hFpos : 0 < F := by dsimp only [F]; positivity
    have hC : C ≤ (2 : ℝ) ^ (2 * M) * F := by
      apply (div_le_iff₀ hFpos).mp
      exact hdelratio
    apply (div_le_iff₀ hBlpos).2
    calc
      Bᵣ ≤ (q : ℝ) ^ M * C := hBr
      _ ≤ (q : ℝ) ^ M * ((2 : ℝ) ^ (2 * M) * F) := by
        gcongr
      _ = ((q : ℝ) * (2 : ℝ) ^ (2 * M)) * Bₗ := by
        dsimp only [Bₗ, F]
        have hM : M = (M - 1) + 1 := by omega
        rw [show (q : ℝ) ^ M = q * q ^ (M - 1) by
          nth_rewrite 1 [hM]
          rw [pow_add]
          ring]
        ring
  have hBrnonneg : 0 ≤ Bᵣ := by
    dsimp only [Bᵣ]
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hAfratio_nonneg : 0 ≤ Aₗ / Aᵣ := div_nonneg hAlpos.le hArpos.le
  have hBratio_nonneg : 0 ≤ Bᵣ / Bₗ := div_nonneg hBrnonneg hBlpos.le
  have hratio : N / D ≤ (q : ℝ) * (2 : ℝ) ^ (3 * (q * M)) := by
    rw [hNratio]
    calc
      (Aₗ / Aᵣ) * (Bᵣ / Bₗ) ≤
          (2 : ℝ) ^ (q * M) * ((q : ℝ) * (2 : ℝ) ^ (2 * M)) := by
        exact mul_le_mul hfullratio hBratio hBratio_nonneg (by positivity)
      _ ≤ (q : ℝ) * (2 : ℝ) ^ (3 * (q * M)) := by
        calc
          (2 : ℝ) ^ (q * M) * ((q : ℝ) * (2 : ℝ) ^ (2 * M)) =
              (q : ℝ) * (2 : ℝ) ^ (q * M + 2 * M) := by
            rw [pow_add]
            ring
          _ ≤ (q : ℝ) * (2 : ℝ) ^ (3 * (q * M)) := by
            have hM : M ≤ q * M := Nat.le_mul_of_pos_left M hq.pos
            have hexp : q * M + 2 * M ≤ 3 * (q * M) := by
              calc
                q * M + 2 * M ≤ q * M + 2 * (q * M) :=
                  Nat.add_le_add_left (Nat.mul_le_mul_left 2 hM) _
                _ = 3 * (q * M) := by ring
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp) hqpos.le
  have hND : N ≤ ((q : ℝ) * (2 : ℝ) ^ (3 * (q * M))) * D := by
    exact (div_le_iff₀ hDrpos).mp hratio
  simpa only [CoprimeHermiteBasis.eval_finiteNodePolynomial,
    norm_prod, D, N, nodeDistance, CoprimeHermiteBasis.finiteSpacingProduct]
    using hND

end Erdos240.BakerCoprimeProductRatio

#print axioms Erdos240.BakerCoprimeProductRatio.norm_finiteNodePolynomial_eval_le
