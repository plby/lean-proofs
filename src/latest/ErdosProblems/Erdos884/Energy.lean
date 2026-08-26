/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.Chebyshev

set_option linter.mathlibStandardSet false

/-!
# Erdős Problem 884 — Lemma D: energy lower bound (Tao eq. (1.2))

For a finite set `A ⊆ ℕ` with `k := |A| ≥ 4` contained in an interval of length `H ≥ 1`,

`pairSum A ≥ k² · log(k/2) / (4H)`.

Proof by chain decomposition: for each index-distance `m ≤ k/2`, split the indices into `m`
arithmetic chains; per chain the consecutive gaps telescope to `≤ H` and Cauchy–Schwarz gives
`Σ 1/gap ≥ L²/H`; Cauchy–Schwarz again over the chains gives `≥ (k−m)²/(mH)`; summing over `m`
and using the harmonic sum lower bound `Σ_{m≤M} 1/m ≥ log(M+1)` finishes.
-/

namespace Erdos884

/-! ### The increasing enumeration of a finset of naturals -/

/-- The `i`-th element (0-based) of `A` in increasing order (junk value for `i ≥ A.card`). -/
def nth (A : Finset ℕ) (i : ℕ) : ℕ := (A.sort (· ≤ ·)).getD i 0

lemma nth_mem (A : Finset ℕ) {i : ℕ} (h : i < A.card) : nth A i ∈ A := by
  have hl : i < (A.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact h
  rw [nth, List.getD_eq_getElem _ _ hl]
  exact (Finset.mem_sort _).1 (List.getElem_mem hl)

lemma nth_lt_nth (A : Finset ℕ) {i j : ℕ} (hij : i < j) (hj : j < A.card) :
    nth A i < nth A j := by
  have hjl : j < (A.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact hj
  have hil : i < (A.sort (· ≤ ·)).length := lt_trans hij hjl
  rw [nth, nth, List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hjl]
  exact (Finset.sortedLT_sort A).getElem_lt_getElem_of_lt hij

lemma nth_le_nth (A : Finset ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < A.card) :
    nth A i ≤ nth A j := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (nth_lt_nth A h hj).le

lemma nth_inj (A : Finset ℕ) {i j : ℕ} (hi : i < A.card) (hj : j < A.card)
    (h : nth A i = nth A j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (nth_lt_nth A hlt hj).ne
  · exact heq
  · exact absurd h.symm (nth_lt_nth A hgt hi).ne

/- `nth` is only accessed through the API above; make it irreducible so that unification
never tries to evaluate the underlying sorted list. -/
attribute [irreducible] nth

/-! ### Reindexing bound: `pairSum` dominates any injectively indexed family of gaps -/

lemma pairSum_eq_sum_filter (A : Finset ℕ) :
    pairSum A = ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 < p.2), invGap p.1 p.2 := by
  rw [pairSum, pairSumOn]
  congr 1
  ext p
  simp

lemma sum_le_pairSum {ι : Type*} (A : Finset ℕ) (s : Finset ι) (a b : ι → ℕ)
    (hab : ∀ x ∈ s, a x < b x ∧ b x < A.card)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, a x = a y → b x = b y → x = y) :
    ∑ x ∈ s, invGap (nth A (a x)) (nth A (b x)) ≤ pairSum A := by
  classical
  have hinj' : Set.InjOn (fun x => (nth A (a x), nth A (b x))) ↑s := by
    intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    have hax := hab x (Finset.mem_coe.1 hx)
    have hay := hab y (Finset.mem_coe.1 hy)
    exact hinj x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy)
      (nth_inj A (hax.1.trans hax.2) (hay.1.trans hay.2) hxy.1)
      (nth_inj A hax.2 hay.2 hxy.2)
  calc ∑ x ∈ s, invGap (nth A (a x)) (nth A (b x))
      = ∑ q ∈ s.image (fun x => (nth A (a x), nth A (b x))), invGap q.1 q.2 := by
        rw [Finset.sum_image hinj']
    _ ≤ ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 < p.2), invGap p.1 p.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [Finset.mem_image] at hq
          obtain ⟨x, hx, rfl⟩ := hq
          obtain ⟨h1, h2⟩ := hab x hx
          simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨nth_mem A (h1.trans h2), nth_mem A h2⟩, nth_lt_nth A h1 h2⟩
        · intro p hp _
          simp only [Finset.mem_filter] at hp
          exact (invGap_pos hp.2).le
    _ = pairSum A := (pairSum_eq_sum_filter A).symm

/-- Specialization of `sum_le_pairSum` to families of index pairs `(m, i) ↦ (i, i + m)`. -/
lemma sum_pairs_le_pairSum (A : Finset ℕ) (P : Finset (ℕ × ℕ))
    (hab : ∀ p ∈ P, p.2 < p.2 + p.1 ∧ p.2 + p.1 < A.card)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, x.2 = y.2 → x.2 + x.1 = y.2 + y.1 → x = y) :
    ∑ p ∈ P, invGap (nth A p.2) (nth A (p.2 + p.1)) ≤ pairSum A :=
  sum_le_pairSum A P (fun p => p.2) (fun p => p.2 + p.1) hab hinj

/-! ### Telescoping bound for ordered disjoint intervals -/

/-- If the intervals `[u i, v i]`, `i ∈ C`, are "ordered disjoint" (`v i ≤ u j` for `i < j`
in `C`) and all contained in `[lo, hi]`, then the total length is at most `hi - lo`. -/
lemma interval_telescope (u v : ℕ → ℝ) (C : Finset ℕ) :
    ∀ lo hi : ℝ, lo ≤ hi →
      (∀ i ∈ C, lo ≤ u i) → (∀ i ∈ C, v i ≤ hi) →
      (∀ i ∈ C, ∀ j ∈ C, i < j → v i ≤ u j) →
      ∑ i ∈ C, (v i - u i) ≤ hi - lo := by
  induction C using Finset.strongInduction with
  | _ C ih =>
    intro lo hi hlohi h1 h2 h3
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simpa using hlohi
    have hMC : C.max' hne ∈ C := C.max'_mem hne
    have hE := ih (C.erase (C.max' hne)) (Finset.erase_ssubset hMC) lo (u (C.max' hne))
      (h1 _ hMC)
      (fun i hi => h1 i (Finset.mem_of_mem_erase hi))
      (fun i hi => h3 i (Finset.mem_of_mem_erase hi) _ hMC
        (lt_of_le_of_ne (Finset.le_max' C i (Finset.mem_of_mem_erase hi))
          (Finset.ne_of_mem_erase hi)))
      (fun i hi j hj hij =>
        h3 i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij)
    have hsplit : ∑ i ∈ C, (v i - u i)
        = (v (C.max' hne) - u (C.max' hne)) + ∑ i ∈ C.erase (C.max' hne), (v i - u i) :=
      (Finset.add_sum_erase C _ hMC).symm
    have hvM : v (C.max' hne) ≤ hi := h2 _ hMC
    linarith

/-! ### Cauchy–Schwarz helpers -/

/-- Cauchy–Schwarz in the AM–HM form: `card² ≤ (Σ g)·(Σ g⁻¹)` for positive `g`. -/
lemma sq_card_le_sum_mul_sum_inv {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 < g i) :
    (s.card : ℝ) ^ 2 ≤ (∑ i ∈ s, g i) * ∑ i ∈ s, (g i)⁻¹ := by
  have h1 : ∑ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹ = (s.card : ℝ) := by
    have hone : ∀ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹ = 1 := fun i hi =>
      mul_inv_cancel₀ (Real.sqrt_pos.2 (hg i hi)).ne'
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ s, (Real.sqrt (g i)) ^ 2 = ∑ i ∈ s, g i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hg i hi).le
  have h3 : ∑ i ∈ s, ((Real.sqrt (g i))⁻¹) ^ 2 = ∑ i ∈ s, (g i)⁻¹ :=
    Finset.sum_congr rfl fun i hi => by
      rw [inv_pow, Real.sq_sqrt (hg i hi).le]
  calc (s.card : ℝ) ^ 2
      = (∑ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹) ^ 2 := by rw [h1]
    _ ≤ (∑ i ∈ s, (Real.sqrt (g i)) ^ 2) * ∑ i ∈ s, ((Real.sqrt (g i))⁻¹) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = (∑ i ∈ s, g i) * ∑ i ∈ s, (g i)⁻¹ := by rw [h2, h3]

/-- Cauchy–Schwarz: `(Σ f)² ≤ card · Σ f²`. -/
lemma sq_sum_le_card_mul_sum_sq' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-! ### The chain bound for a fixed index-distance `m` -/

/-- For a fixed index-distance `m ≥ 1`, splitting the indices into `m` arithmetic chains,
telescoping each chain and applying Cauchy–Schwarz twice gives
`Σ_{i+m<k} 1/(nth(i+m) − nth i) ≥ (k−m)²/(mH)`. -/
lemma chain_sum_ge (A : Finset ℕ) {H : ℝ} {m : ℕ} (hm : 1 ≤ m) (hH : 0 < H)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (b : ℝ) - (a : ℝ) ≤ H) (hne : A.Nonempty) :
    ((A.card - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) ≤
      ∑ i ∈ Finset.range (A.card - m), invGap (nth A i) (nth A (i + m)) := by
  classical
  set k := A.card with hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hHne : H ≠ 0 := ne_of_gt hH
  have hmaps : ∀ i ∈ Finset.range (k - m), i % m ∈ Finset.range m :=
    fun i _ => Finset.mem_range.2 (Nat.mod_lt i hm)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- per-chain bound: telescoping + Cauchy–Schwarz
  have hfiber : ∀ r ∈ Finset.range m,
      ((((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ)) ^ 2 / H ≤
        ∑ i ∈ (Finset.range (k - m)).filter (fun i => i % m = r),
          invGap (nth A i) (nth A (i + m)) := by
    intro r _
    set C := (Finset.range (k - m)).filter (fun i => i % m = r) with hC
    have hCsub : ∀ i ∈ C, i < k - m := fun i hi =>
      Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hgap_pos : ∀ i ∈ C, (0 : ℝ) < (nth A (i + m) : ℝ) - (nth A i : ℝ) := by
      intro i hi
      have h2 : i + m < k := by have := hCsub i hi; omega
      have h3 : nth A i < nth A (i + m) := nth_lt_nth A (by omega) h2
      have h4 : (nth A i : ℝ) < (nth A (i + m) : ℝ) := by exact_mod_cast h3
      linarith
    have hlb : ∀ i ∈ C, ((A.min' hne : ℕ) : ℝ) ≤ (nth A i : ℝ) := by
      intro i hi
      have hik : i < k := by have := hCsub i hi; omega
      exact_mod_cast A.min'_le _ (nth_mem A hik)
    have hub : ∀ i ∈ C, (nth A (i + m) : ℝ) ≤ ((A.min' hne : ℕ) : ℝ) + H := by
      intro i hi
      have hik : i + m < k := by have := hCsub i hi; omega
      have := hdiam (A.min' hne) (A.min'_mem hne) (nth A (i + m)) (nth_mem A hik)
      linarith
    have horder : ∀ i ∈ C, ∀ j ∈ C, i < j → (nth A (i + m) : ℝ) ≤ (nth A j : ℝ) := by
      intro i hi j hj hij
      have hri : i % m = r := (Finset.mem_filter.1 hi).2
      have hrj : j % m = r := (Finset.mem_filter.1 hj).2
      have hmod : i ≡ j [MOD m] := by
        unfold Nat.ModEq
        rw [hri, hrj]
      have hdvd : m ∣ j - i := (Nat.modEq_iff_dvd' hij.le).1 hmod
      have hji : m ≤ j - i := Nat.le_of_dvd (by omega) hdvd
      have hjk : j < k := by have := hCsub j hj; omega
      exact_mod_cast nth_le_nth A (by omega) hjk
    have htel : ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))
        ≤ (((A.min' hne : ℕ) : ℝ) + H) - ((A.min' hne : ℕ) : ℝ) :=
      interval_telescope (fun i => (nth A i : ℝ)) (fun i => (nth A (i + m) : ℝ)) C
        ((A.min' hne : ℕ) : ℝ) (((A.min' hne : ℕ) : ℝ) + H) (by linarith) hlb hub horder
    have htel' : ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ)) ≤ H := by linarith
    have hinv_nonneg : 0 ≤ ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
      Finset.sum_nonneg fun i hi => (inv_pos.2 (hgap_pos i hi)).le
    have hcs : (C.card : ℝ) ^ 2 ≤
        (∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))) *
          ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
      sq_card_le_sum_mul_sum_inv C _ hgap_pos
    rw [div_le_iff₀ hH]
    calc (C.card : ℝ) ^ 2
        ≤ (∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))) *
            ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ := hcs
      _ ≤ H * ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right htel' hinv_nonneg
      _ = (∑ i ∈ C, invGap (nth A i) (nth A (i + m))) * H := by
          rw [mul_comm]
  -- counting: the chains partition the index range
  have hcardsum : (k - m) = ∑ r ∈ Finset.range m,
      ((Finset.range (k - m)).filter (fun i => i % m = r)).card := by
    have h := Finset.card_eq_sum_card_fiberwise hmaps
    rwa [Finset.card_range] at h
  have hsum : ((k - m : ℕ) : ℝ) = ∑ r ∈ Finset.range m,
      (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) := by
    exact_mod_cast hcardsum
  -- Cauchy–Schwarz over the chains
  have hCS : ((k - m : ℕ) : ℝ) ^ 2 ≤
      (m : ℝ) * ∑ r ∈ Finset.range m,
        (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq' (Finset.range m)
      (fun r => (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ))
    rw [Finset.card_range] at h
    rw [hsum]
    exact h
  calc ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H)
      ≤ ∑ r ∈ Finset.range m,
          (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 / H := by
        rw [div_le_iff₀ (mul_pos hm0 hH)]
        calc ((k - m : ℕ) : ℝ) ^ 2
            ≤ (m : ℝ) * ∑ r ∈ Finset.range m,
                (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 := hCS
          _ = (∑ r ∈ Finset.range m,
                (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 / H) *
                ((m : ℝ) * H) := by
              rw [← Finset.sum_div, div_mul_eq_mul_div, mul_div_assoc,
                mul_div_cancel_right₀ _ hHne, mul_comm]
    _ ≤ ∑ r ∈ Finset.range m, ∑ i ∈ (Finset.range (k - m)).filter (fun i => i % m = r),
          invGap (nth A i) (nth A (i + m)) := Finset.sum_le_sum hfiber

/-! ### Harmonic sum lower bound -/

lemma log_le_sum_inv (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ := by
  have h := log_add_one_le_harmonic M
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-! ### Lemma D: the energy lower bound (Tao eq. (1.2)) -/

theorem pairSum_ge_energy {A : Finset ℕ} {H : ℝ} (hcard : 4 ≤ A.card) (hH : 1 ≤ H)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (b : ℝ) - (a : ℝ) ≤ H) :
    (A.card : ℝ)^2 * Real.log ((A.card : ℝ) / 2) / (4 * H) ≤ pairSum A := by
  classical
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hH0 : (0 : ℝ) < H := by linarith
  have hHne : H ≠ 0 := ne_of_gt hH0
  set k := A.card with hk
  set M := k / 2 with hM
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk2 : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  -- Step 1: the double sum over index-distances m and start indices i is ≤ pairSum A
  have hdouble : ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
      invGap (nth A i) (nth A (i + m)) ≤ pairSum A := by
    have hchar : ∀ p : ℕ × ℕ,
        p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter (fun p => p.2 + p.1 < k) ↔
          p.1 ∈ Finset.Icc 1 M ∧ p.2 ∈ Finset.range (k - p.1) := by
      intro p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      omega
    have heq : ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
        invGap (nth A i) (nth A (i + m))
        = ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter (fun p => p.2 + p.1 < k),
            invGap (nth A p.2) (nth A (p.2 + p.1)) :=
      (Finset.sum_finset_product' _ (Finset.Icc 1 M) (fun m => Finset.range (k - m)) hchar
        (f := fun c a => invGap (nth A a) (nth A (a + c)))).symm
    have hab : ∀ p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k), p.2 < p.2 + p.1 ∧ p.2 + p.1 < A.card := by
      intro p hp
      rw [hchar p] at hp
      simp only [Finset.mem_Icc, Finset.mem_range] at hp
      omega
    have hinj : ∀ x ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k),
        ∀ y ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k),
        x.2 = y.2 → x.2 + x.1 = y.2 + y.1 → x = y := by
      intro x _ y _ h1 h2
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      simp only [Prod.mk.injEq]
      simp only at h1 h2
      omega
    rw [heq]
    exact sum_pairs_le_pairSum A ((Finset.Icc 1 M ×ˢ Finset.range k).filter
      (fun p : ℕ × ℕ => p.2 + p.1 < k)) hab hinj
  -- Step 2: per-m chain bound
  have hper : ∀ m ∈ Finset.Icc 1 M, ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) ≤
      ∑ i ∈ Finset.range (k - m), invGap (nth A i) (nth A (i + m)) := by
    intro m hm
    exact chain_sum_ge A (Finset.mem_Icc.1 hm).1 hH0 hdiam hne
  -- Step 3: (k−m)² ≥ (k/2)² for m ≤ M
  have hquarter : ∀ m ∈ Finset.Icc 1 M,
      ((k : ℝ) / 2) ^ 2 / ((m : ℝ) * H) ≤ ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have hmH : (0 : ℝ) < (m : ℝ) * H := mul_pos hm0 hH0
    have hmk : m ≤ k := by omega
    have h2m : 2 * m ≤ k := by omega
    have h2m' : 2 * (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2m
    have hge : (k : ℝ) / 2 ≤ ((k - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hmk]
      linarith
    have hsq : ((k : ℝ) / 2) ^ 2 ≤ ((k - m : ℕ) : ℝ) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hk2.le hge
    rw [div_le_iff₀ hmH]
    calc ((k : ℝ) / 2) ^ 2 ≤ ((k - m : ℕ) : ℝ) ^ 2 := hsq
      _ = ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) * ((m : ℝ) * H) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hmH)]
  -- Step 4: harmonic sum lower bound
  have hlog : Real.log ((k : ℝ) / 2) ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_le_log hk2
    have h1 : k ≤ 2 * M + 1 := by omega
    have h2 : (k : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hlogsum : Real.log ((k : ℝ) / 2) ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
    hlog.trans (log_le_sum_inv M)
  -- Assemble
  calc (k : ℝ) ^ 2 * Real.log ((k : ℝ) / 2) / (4 * H)
      = ((k : ℝ) / 2) ^ 2 / H * Real.log ((k : ℝ) / 2) := by
        field_simp
        ring
    _ ≤ ((k : ℝ) / 2) ^ 2 / H * ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hlogsum (div_nonneg (by positivity) hH0.le)
    _ = ∑ m ∈ Finset.Icc 1 M, ((k : ℝ) / 2) ^ 2 / ((m : ℝ) * H) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm0 : ((m : ℝ)) ≠ 0 := by
          have h1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
          have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h1
          exact ne_of_gt this
        field_simp
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) :=
        Finset.sum_le_sum hquarter
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
          invGap (nth A i) (nth A (i + m)) := Finset.sum_le_sum hper
    _ ≤ pairSum A := hdouble

end Erdos884
