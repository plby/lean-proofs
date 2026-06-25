/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 481.
https://www.erdosproblems.com/forum/thread/481

Informal authors:
- Kevin Barreto

Formal authors:
- Claude Opus 4.5
- Kevin Barreto

URLs:
- https://www.erdosproblems.com/forum/thread/481#post-1930
-/
/-
Proven and formalised (with assistance from Claude Opus 4.5) by Kevin Barreto
-/

import Mathlib

/-!
# Erdős Problem #481

## Problem Statement

Let $a_1, \ldots, a_r, b_1, \ldots, b_r \in \mathbb{N}$ (positive integers, i.e., $\geq 1$)
such that $\sum_i \frac{1}{a_i} > 1$. For any finite sequence of $n$ (not necessarily distinct)
integers $A = (x_1, \ldots, x_n)$ let $T(A)$ denote the sequence of length $rn$ given by
$(a_i x_j + b_i)_{1 \leq j \leq n, 1 \leq i \leq r}$.

Prove that, if $A_1 = (1)$ and $A_{i+1} = T(A_i)$, then there must be some $A_k$ with
repeated elements.

## Proof

Assume, for contradiction, that all entries of $A_k$ are distinct. Write
$$\Sigma_k := \sum_{x \in A_k} \frac{1}{x},$$
and set
$$C := \sum_{i=1}^r \frac{1}{a_i} > 1 \quad \text{and} \quad B := \sum_{i=1}^r \frac{b_i}{a_i^2}.$$

Since $A_k$ has $r^{k-1}$ distinct positive integers,
$$\Sigma_k \leq \sum_{j=1}^{r^{k-1}} \frac{1}{j} \leq 1 + \log(r^{k-1}) = 1 + (k-1)\log(r),$$
so $\Sigma_k = O(k)$.

From $A_{k+1} = \{a_i x + b_i : x \in A_k, 1 \leq i \leq r\}$ and the identity
$$\frac{1}{a_i x + b_i} = \frac{1}{a_i x} - \frac{b_i}{a_i x (a_i x + b_i)},$$
we obtain
$$\Sigma_{k+1} = C \Sigma_k - \sum_{i=1}^r \sum_{x \in A_k} \frac{b_i}{a_i x (a_i x + b_i)}
              \geq C \Sigma_k - \sum_{i=1}^r \sum_{x \in A_k} \frac{b_i}{a_i^2 x^2}
              = C \Sigma_k - B \sum_{x \in A_k} \frac{1}{x^2}.$$

Let $m_k := \min(A_k)$. As $m_1 = 1$ and $m_{k+1} = \min_{i,x}(a_i x + b_i) \geq m_k + 1$,
we have $m_k \geq k$. Hence, for every $x \in A_k$, we have $x \geq k$, and therefore
$$\Sigma_{k+1} \geq C \Sigma_k - B \sum_{x \in A_k} \frac{1}{x^2}
              \geq C \Sigma_k - \frac{B}{k} \sum_{x \in A_k} \frac{1}{x}
              = \left(C - \frac{B}{k}\right) \Sigma_k.$$

Now choose $K \in \mathbb{N}$ with $K > \frac{B}{C-1}$. Then for all $k \geq K$,
set $C' := C - \frac{B}{K} > 1$, giving
$$\Sigma_{k+1} \geq C' \Sigma_k \quad \forall k \geq K
  \implies \Sigma_k \geq (C')^{k-K} \Sigma_K \quad \forall k \geq K.$$

So $\Sigma_k$ grows exponentially for large $k$. This contradicts the harmonic upper bound
$\Sigma_k = O(k)$. Thus, for some $k$, the sequence $A_k$ contains repeated elements.

## References

* Erdős Problem #481: https://www.erdosproblems.com/481
-/

open Finset BigOperators

namespace Erdos481

/-! ## Basic Definitions -/

variable {r : ℕ}
variable (a b : Fin r → ℕ+)

/-- The constant C = ∑(1/a_i) -/
noncomputable def C : ℝ := ∑ i : Fin r, (1 : ℝ) / (a i : ℝ)

/-- The constant B = ∑(b_i/a_i²) -/
noncomputable def B : ℝ := ∑ i : Fin r, (b i : ℝ) / ((a i : ℝ) ^ 2)

/-- The transformation T applied to a list of positive integers -/
def T (L : List ℕ+) : List ℕ+ :=
  L.flatMap fun x : ℕ+ => (List.finRange r).map fun i =>
    ⟨a i * x + b i, Nat.add_pos_right _ (b i).2⟩

/-- The sequence A_k with A_1 = [1], A_{k+1} = T(A_k). We use 1-indexing.
    A 0 is defined as [] for convenience but is not used in the theorem. -/
def A : ℕ → List ℕ+
  | 0 => []
  | 1 => [1]
  | n + 2 => T a b (A (n + 1))

/-- Sum of reciprocals: Σ = ∑_{x ∈ L} 1/x -/
noncomputable def Sigma (L : List ℕ+) : ℝ :=
  L.foldr (fun x acc => (1 : ℝ) / (x : ℝ) + acc) 0

lemma Sigma_nil : Sigma [] = 0 := rfl

lemma Sigma_cons (x : ℕ+) (xs : List ℕ+) : Sigma (x :: xs) = 1 / (x : ℝ) + Sigma xs := rfl

lemma Sigma_append (L₁ L₂ : List ℕ+) : Sigma (L₁ ++ L₂) = Sigma L₁ + Sigma L₂ := by
  induction L₁ with
  | nil => simp [Sigma_nil]
  | cons x xs ih => simp [Sigma_cons, ih]; ring

lemma Sigma_eq_finset_sum (L : List ℕ+) (hnodup : L.Nodup) :
    Sigma L = ∑ x ∈ L.toFinset, (1 : ℝ) / (x : ℝ) := by
  induction L with
  | nil => simp [Sigma_nil]
  | cons x xs ih =>
    have hx_not_mem : x ∉ xs := List.nodup_cons.mp hnodup |>.1
    rw [Sigma_cons, ih hnodup.of_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simp_all)]

lemma Sigma_nonneg (L : List ℕ+) : 0 ≤ Sigma L := by
  induction L with
  | nil => rfl
  | cons x xs ih => exact add_nonneg (by positivity) ih

lemma Sigma_pos (L : List ℕ+) (hne : L ≠ []) : 0 < Sigma L := by
  cases L with
  | nil => contradiction
  | cons x xs => exact add_pos_of_pos_of_nonneg (by positivity) (Sigma_nonneg xs)

/-- Correction term: ∑_{x ∈ L} ∑_i b_i/(a_i x (a_i x + b_i)) -/
noncomputable def CorrectionTerm (a b : Fin r → ℕ+) (L : List ℕ+) : ℝ :=
  L.foldr (fun x acc =>
    (∑ i : Fin r, (b i : ℝ) / ((a i : ℝ) * (x : ℝ) * ((a i : ℝ) * (x : ℝ) + (b i : ℝ)))) + acc) 0

lemma CorrectionTerm_nil : CorrectionTerm a b [] = 0 := rfl

lemma CorrectionTerm_cons (x : ℕ+) (xs : List ℕ+) :
    CorrectionTerm a b (x :: xs) =
      (∑ i : Fin r, (b i : ℝ) / ((a i : ℝ) * (x : ℝ) * ((a i : ℝ) * (x : ℝ) + (b i : ℝ)))) +
      CorrectionTerm a b xs := rfl

/-! ## Key Lemmas -/

/-- |A_k| = r^{k-1} -/
lemma length_A (k : ℕ) (hk : 1 ≤ k) : (A a b k).length = r ^ (k - 1) := by
  classical
  match k with
  | 0 => omega
  | 1 => simp [A]
  | k + 2 =>
    have ih : (A a b (k + 1)).length = r ^ k := length_A (k + 1) (by omega)
    simp only [A, T, List.length_flatMap, List.length_map, List.length_finRange,
               List.map_const', List.sum_replicate, smul_eq_mul, ih,
               Nat.succ_sub_succ_eq_sub, Nat.sub_zero, pow_succ, mul_comm]

/-- m_k = min(A_k) ≥ k since m_1 = 1 and m_{k+1} ≥ m_k + 1 -/
lemma min_A_ge (k : ℕ) (hk : 1 ≤ k) : ∀ x ∈ A a b k, (k : ℕ) ≤ (x : ℕ) := by
  classical
  match k with
  | 0 => omega
  | 1 =>
    intro x hx
    simp [A] at hx
    simp [hx]
  | k + 2 =>
    intro x hx
    have ih : ∀ y ∈ A a b (k + 1), (k + 1 : ℕ) ≤ (y : ℕ) := min_A_ge (k + 1) (by omega)
    dsimp [A] at hx
    unfold T at hx
    rcases List.mem_flatMap.1 hx with ⟨y, hy_mem, hy_map⟩
    rcases List.mem_map.1 hy_map with ⟨i, _, hi_eq⟩
    have hy_bound : (k + 1 : ℕ) ≤ (y : ℕ) := ih y hy_mem
    have ha_ge1 : 1 ≤ (a i : ℕ) := Nat.succ_le_of_lt (a i).pos
    have hb_ge1 : 1 ≤ (b i : ℕ) := Nat.succ_le_of_lt (b i).pos
    have hx_eq : (x : ℕ) = (a i : ℕ) * (y : ℕ) + (b i : ℕ) := by
      have := congrArg (fun z : ℕ+ => (z : ℕ)) hi_eq.symm
      simpa using this
    have hy_le_mul : (y : ℕ) ≤ (a i : ℕ) * (y : ℕ) := by
      simpa [Nat.one_mul] using (Nat.mul_le_mul_right (y : ℕ) ha_ge1)
    calc (k + 2 : ℕ) ≤ (y : ℕ) + 1 := Nat.add_le_add_right hy_bound 1
      _ ≤ (a i : ℕ) * (y : ℕ) + 1 := Nat.add_le_add_right hy_le_mul 1
      _ ≤ (a i : ℕ) * (y : ℕ) + (b i : ℕ) := Nat.add_le_add_left hb_ge1 _
      _ = (x : ℕ) := hx_eq.symm

/-- b/(ax(ax+b)) ≤ b/(a²x²) since ax(ax+b) ≥ a²x² -/
lemma recip_bound (ai x bi : ℝ) (hai : 0 < ai) (hx : 0 < x) (hbi : 0 ≤ bi) :
    bi / (ai * x * (ai * x + bi)) ≤ bi / (ai ^ 2 * x ^ 2) := by
  rcases eq_or_lt_of_le hbi with hbi0 | hbi_pos
  · simp [← hbi0]
  · have hax : 0 < ai * x := mul_pos hai hx
    have h1 : ai ^ 2 * x ^ 2 ≤ ai * x * (ai * x + bi) := by nlinarith
    exact div_le_div_of_nonneg_left (le_of_lt hbi_pos) (by positivity) h1

/-- Sigma of a mapped finRange equals sum over Fin -/
lemma Sigma_map_finRange {n : ℕ} (f : Fin n → ℕ+) :
    Sigma ((List.finRange n).map f) = ∑ i : Fin n, (1 : ℝ) / (f i : ℝ) := by
  induction n with
  | zero => simp [Sigma_nil]
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, Sigma_cons, Fin.sum_univ_succ]
    simp only [List.map_map, Function.comp_def]; congr 1; convert ih (f ∘ Fin.succ) using 1

/-- From 1/(ax+b) = 1/(ax) - b/(ax(ax+b)), we get Σ_{k+1} = C·Σ_k - CorrectionTerm -/
lemma sigma_eq (k : ℕ) (hk : 1 ≤ k) :
    Sigma (A a b (k + 1)) = C a * Sigma (A a b k) - CorrectionTerm a b (A a b k) := by
  have hA : A a b (k + 1) = T a b (A a b k) := by
    match k with | 0 => omega | 1 => rfl | _ + 2 => rfl
  rw [hA, T]
  induction (A a b k) with
  | nil => simp [Sigma, CorrectionTerm, C]
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [Sigma_append, CorrectionTerm_cons, Sigma_cons]
    have h_term : ∀ z : ℕ+,
        Sigma ((List.finRange r).map fun i =>
          ⟨(a i : ℕ) * (z : ℕ) + (b i : ℕ), Nat.add_pos_right _ (b i).2⟩) =
        C a * ((1 : ℝ) / (z : ℝ)) -
        (∑ i : Fin r, (b i : ℝ) / ((a i : ℝ) * (z : ℝ) * ((a i : ℝ) * (z : ℝ) + (b i : ℝ)))) := by
      intro z
      rw [Sigma_map_finRange]
      simp only [C, PNat.mk_coe]
      -- Apply 1/(ax+b) = 1/(ax) - b/(ax(ax+b))
      have h_decomp : ∀ i : Fin r,
          (1 : ℝ) / (((a i : ℕ) * (z : ℕ) + (b i : ℕ) : ℕ) : ℝ) =
          1 / (a i : ℝ) * (1 / (z : ℝ)) -
          (b i : ℝ) / ((a i : ℝ) * (z : ℝ) * ((a i : ℝ) * (z : ℝ) + (b i : ℝ))) := by
        intro i
        have hai : (a i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (a i).pos)
        have hz : (z : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp z.pos)
        have haxb : (a i : ℝ) * (z : ℝ) + (b i : ℝ) ≠ 0 := by positivity
        have heq : (((a i : ℕ) * (z : ℕ) + (b i : ℕ) : ℕ) : ℝ) =
            (a i : ℝ) * (z : ℝ) + (b i : ℝ) := by push_cast; ring
        rw [heq]; field_simp [mul_ne_zero hai hz, haxb]; ring
      simp_rw [h_decomp]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [h_term x, ih]; ring

/-- For x ≥ k: ∑_i b_i/(a_i x(a_i x + b_i)) ≤ ∑_i b_i/(a_i² x²) = B/x² ≤ B/(kx) -/
lemma CorrectionTerm_le (k : ℕ) (hk : 1 ≤ k) :
    CorrectionTerm a b (A a b k) ≤ (B a b / k) * Sigma (A a b k) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
  have hB_nonneg : 0 ≤ B a b := Finset.sum_nonneg fun i _ => by positivity
  have hall : ∀ x ∈ A a b k, (k : ℕ) ≤ (x : ℕ) := min_A_ge a b k hk
  suffices h : ∀ L : List ℕ+, (∀ x ∈ L, (k : ℕ) ≤ (x : ℕ)) →
      CorrectionTerm a b L ≤ (B a b / k) * Sigma L by exact h (A a b k) hall
  intro L hL
  induction L with
  | nil => simp [CorrectionTerm, Sigma]
  | cons x xs ih =>
    rw [CorrectionTerm_cons, Sigma_cons]
    have hx_ge_k : (k : ℝ) ≤ (x : ℝ) := Nat.cast_le.mpr (hL x (List.Mem.head _))
    have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr x.pos
    have h_term : (∑ i : Fin r, (b i : ℝ) / ((a i : ℝ) * x * ((a i : ℝ) * x + (b i : ℝ)))) ≤
        (B a b / k) * (1 / (x : ℝ)) := by
      have h1 : (∑ i, (b i : ℝ) / ((a i : ℝ) * x * ((a i : ℝ) * x + (b i : ℝ)))) ≤
                (∑ i, (b i : ℝ) / ((a i : ℝ) ^ 2 * x ^ 2)) :=
        Finset.sum_le_sum fun i _ =>
          recip_bound _ _ _ (Nat.cast_pos.mpr (a i).pos) hx_pos (Nat.cast_nonneg _)
      have h2 : (∑ i, (b i : ℝ) / ((a i : ℝ) ^ 2 * x ^ 2)) = B a b / x ^ 2 := by
        simp only [B, Finset.sum_div]; congr 1; ext i; field_simp
      have h3 : B a b / (x : ℝ) ^ 2 ≤ B a b / (k * x) := by
        apply div_le_div_of_nonneg_left hB_nonneg (by positivity)
        calc (k : ℝ) * x ≤ x * x := by nlinarith
          _ = (x : ℝ) ^ 2 := (sq (x : ℝ)).symm
      calc _ ≤ B a b / x ^ 2 := by rw [← h2]; exact h1
        _ ≤ B a b / (k * x) := h3
        _ = (B a b / k) * (1 / x) := by field_simp
    have h_xs := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    linarith

/-- Σ_{k+1} ≥ (C - B/k)·Σ_k -/
lemma sigma_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Sigma (A a b (k + 1)) ≥ (C a - B a b / k) * Sigma (A a b k) := by
  rw [sigma_eq a b k hk]; linarith [CorrectionTerm_le a b k hk, Sigma_nonneg (A a b k)]

/-- Σ_k ≤ H_{r^{k-1}} ≤ 1 + (k-1)·log(r) since A_k has r^{k-1} distinct positive integers -/
lemma sigma_upper_bound (k : ℕ) (hk : 1 ≤ k) (hnodup : (A a b k).Nodup) :
    Sigma (A a b k) ≤ 1 + (k - 1) * Real.log r := by
  have hlen : (A a b k).length = r ^ (k - 1) := length_A a b k hk
  classical
  let S := (A a b k).toFinset
  have hS_card : S.card = r ^ (k - 1) := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have hS_pos : ∀ x ∈ S, 0 < (x : ℕ) := fun x _ => x.pos
  have hSigma_eq : Sigma (A a b k) = ∑ x ∈ S, (1 : ℝ) / (x : ℝ) := Sigma_eq_finset_sum _ hnodup
  rw [hSigma_eq]
  have h_sum_bound : ∑ x ∈ S, (1 : ℝ) / (x : ℝ) ≤
      ∑ j ∈ Finset.range (r ^ (k - 1)), (1 : ℝ) / ((j : ℝ) + 1) := by
    let n := r ^ (k - 1)
    have hn : S.card = n := hS_card
    let e := S.orderEmbOfFin hn
    rw [← Fin.sum_univ_eq_sum_range (fun j => (1 : ℝ) / ((j : ℝ) + 1))]
    have hmap : Finset.map e.toEmbedding Finset.univ = S := S.map_orderEmbOfFin_univ hn
    calc ∑ x ∈ S, (1 : ℝ) / (x : ℝ)
      = ∑ x ∈ Finset.map e.toEmbedding Finset.univ, (1 : ℝ) / (x : ℝ) := by rw [hmap]
      _ = ∑ i : Fin n, (1 : ℝ) / ((e i : ℕ) : ℝ) := by rw [Finset.sum_map]; rfl
      _ ≤ ∑ i : Fin n, (1 : ℝ) / ((i : ℕ) + 1) := by
          apply Finset.sum_le_sum
          intro i _
          have h_pos_ei : (0 : ℝ) < (e i : ℕ) := Nat.cast_pos.mpr (e i).pos
          have h_pos_i : (0 : ℝ) < (i : ℕ) + 1 := by positivity
          rw [one_div_le_one_div h_pos_ei h_pos_i]
          have h_strict : StrictMono e := (S.orderEmbOfFin hn).strictMono
          have h_mono : ∀ j : Fin n, (j : ℕ) + 1 ≤ (e j : ℕ) := fun j => by
            have : ∀ m : ℕ, ∀ hm : m < n, (m : ℕ) + 1 ≤ (e ⟨m, hm⟩ : ℕ) := by
              intro m
              induction m with
              | zero => intro _; exact (e ⟨0, ‹_›⟩).pos
              | succ m' ih =>
                intro hm
                have hm' : m' < n := Nat.lt_of_succ_lt hm
                have ih_val := ih hm'
                have hlt : (e ⟨m', hm'⟩ : ℕ+) < e ⟨m' + 1, hm⟩ :=
                  h_strict (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m'))
                have hlt_nat : (e ⟨m', hm'⟩ : ℕ) < (e ⟨m' + 1, hm⟩ : ℕ) := hlt
                omega
            exact this j.val j.isLt
          exact_mod_cast h_mono i
  have h_harmonic_bound : ∑ j ∈ Finset.range (r ^ (k - 1)), (1 : ℝ) / ((j : ℝ) + 1) ≤
      1 + Real.log ↑(r ^ (k - 1)) := by
    have := harmonic_le_one_add_log (r ^ (k - 1))
    unfold harmonic at this
    convert this using 1
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    ext j
    simp
  calc ∑ x ∈ S, (1 : ℝ) / (x : ℝ)
    ≤ ∑ j ∈ Finset.range (r ^ (k - 1)), (1 : ℝ) / ((j : ℝ) + 1) := h_sum_bound
    _ ≤ 1 + Real.log ↑(r ^ (k - 1)) := h_harmonic_bound
    _ = 1 + (k - 1) * Real.log r := by
        rw [Nat.cast_pow, Real.log_pow]
        ring_nf
        rw [Nat.cast_sub hk]
        ring

/-- Choose K > B/(C-1), then C' = C - B/K > 1 -/
lemma exists_K (hC : 1 < C a) : ∃ K : ℕ, 1 ≤ K ∧ 1 < C a - B a b / K := by
  have hCm1 : 0 < C a - 1 := sub_pos.mpr hC
  have hB_nonneg : 0 ≤ B a b := Finset.sum_nonneg fun i _
    => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rcases eq_or_lt_of_le hB_nonneg with hB | hB_pos
  · exact ⟨1, le_refl 1, by simp [← hB, hC]⟩
  · use Nat.ceil (B a b / (C a - 1)) + 1
    refine ⟨by omega, ?_⟩
    have hK_large : B a b / (C a - 1) < (Nat.ceil (B a b / (C a - 1)) + 1 : ℝ) :=
      by linarith [Nat.le_ceil (B a b / (C a - 1))]
    have hdiv_bound := div_lt_div_of_pos_left hB_pos (div_pos hB_pos hCm1) hK_large
    simp only [Nat.cast_add, Nat.cast_one]
    calc C a - B a b / (Nat.ceil (B a b / (C a - 1)) + 1 : ℝ)
      > C a - B a b / (B a b / (C a - 1)) := sub_lt_sub_left hdiv_bound _
      _ = 1 := by field_simp; ring

/-- For k ≥ K: Σ_{k+1} ≥ C'·Σ_k where C' = C - B/K > 1 -/
lemma sigma_exponential_growth (hC : 1 < C a) :
    ∃ K : ℕ, ∃ C' : ℝ, 1 ≤ K ∧ 1 < C' ∧
      (∀ k ≥ K, (A a b k).Nodup →
        Sigma (A a b (k + 1)) ≥ C' * Sigma (A a b k)) := by
  obtain ⟨K, hK1, hC'⟩ := exists_K a b hC
  use K, C a - B a b / K
  refine ⟨hK1, hC', fun k hk _ => ?_⟩
  have hB_nonneg : 0 ≤ B a b := by
    apply Finset.sum_nonneg; intro i _
    apply div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hK_pos : 0 < (K : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hK1))
  have hk_pos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (le_trans hK1 hk)))
  have hSigma_nonneg : 0 ≤ Sigma (A a b k) := Sigma_nonneg _
  calc Sigma (A a b (k + 1))
    ≥ (C a - B a b / k) * Sigma (A a b k) := sigma_lower_bound a b k (le_trans hK1 hk)
    _ ≥ (C a - B a b / K) * Sigma (A a b k) := by
        apply mul_le_mul_of_nonneg_right _ hSigma_nonneg
        apply sub_le_sub_left
        apply div_le_div_of_nonneg_left hB_nonneg hK_pos
        exact Nat.cast_le.mpr hk

/-! ## Main Theorem -/

/-- Main theorem: there exists some k such that A_k has repeated elements -/
theorem erdos_481 (hr : 0 < r) (hC : 1 < C a) :
    ∃ k, 1 ≤ k ∧ ¬(A a b k).Nodup := by
  -- Assume for contradiction that all A_k have distinct elements
  by_contra h
  push Not at h
  obtain ⟨K, C', hK1, hC'_gt_1, hgrowth⟩ := sigma_exponential_growth a b hC
  have hSigmaK_pos : 0 < Sigma (A a b K) := by
    have hlen : (A a b K).length = r ^ (K - 1) := length_A a b K hK1
    have hne : (A a b K) ≠ [] := by
      intro heq
      rw [heq] at hlen
      simp only [List.length_nil] at hlen
      exact Nat.not_lt.mpr (Nat.one_le_pow _ _ hr) (hlen ▸ Nat.lt_one_iff.mpr rfl)
    exact Sigma_pos _ hne
  -- Upper bound: Σ_k ≤ 1 + (k-1)·log(r) = O(k)
  have h_upper : ∀ k ≥ 1, Sigma (A a b k) ≤ 1 + (k - 1) * Real.log r := fun k hk =>
    sigma_upper_bound a b k hk (h k hk)
  -- Lower bound: Σ_k ≥ (C')^{k-K} · Σ_K for k ≥ K (exponential growth)
  have h_lower : ∀ k ≥ K, Sigma (A a b k) ≥ C' ^ (k - K) * Sigma (A a b K) := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      by_cases hn : n < K
      · have : n + 1 = K := by omega
        simp [this]
      · push Not at hn
        have ih' := ih hn
        have hnodup_n : (A a b n).Nodup := h n (le_trans hK1 hn)
        have hgrowth_n := hgrowth n hn hnodup_n
        calc Sigma (A a b (n + 1))
          ≥ C' * Sigma (A a b n) := hgrowth_n
          _ ≥ C' * (C' ^ (n - K) * Sigma (A a b K)) := by
              apply mul_le_mul_of_nonneg_left ih' (le_of_lt (lt_trans zero_lt_one hC'_gt_1))
          _ = C' ^ (n - K + 1) * Sigma (A a b K) := by ring
          _ = C' ^ (n + 1 - K) * Sigma (A a b K) := by rw [Nat.sub_add_comm hn]
  -- Contradiction: exponential growth vs O(k) bound
  have hlog_r_nonneg : 0 ≤ Real.log r := Real.log_nonneg (Nat.one_le_cast.mpr hr)
  have h_poly_div_exp : Filter.Tendsto (fun n : ℕ => (n : ℝ) / C' ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_const_div_const_pow_of_one_lt 1 hC'_gt_1
    simp only [pow_one] at this
    exact this
  have h_ratio_tendsto :
      Filter.Tendsto (fun n : ℕ => C' ^ n / (n : ℝ)) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    have hpos : (0 : ℝ) < 1 / (|b| + 1) := by positivity
    rw [Metric.tendsto_atTop] at h_poly_div_exp
    obtain ⟨N, hN⟩ := h_poly_div_exp (1 / (|b| + 1)) hpos
    use max N 1
    intro n hn
    have hn_ge_N : N ≤ n := le_of_max_le_left hn
    have hn_ge_1 : 1 ≤ n := le_of_max_le_right hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_ge_1
    have hCn_pos : (0 : ℝ) < C' ^ n := pow_pos (lt_trans zero_lt_one hC'_gt_1) n
    specialize hN n hn_ge_N
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hn_pos hCn_pos)] at hN
    have h3 : C' ^ n / n > |b| + 1 := by
      have hab_pos : (0 : ℝ) < |b| + 1 := by positivity
      rw [gt_iff_lt, lt_div_iff₀ hn_pos]
      rw [div_lt_iff₀ hCn_pos] at hN
      -- hN : n < 1 / (|b| + 1) * C'^n = C'^n / (|b| + 1)
      have h4 : n * (|b| + 1) < C' ^ n := by
        calc (n : ℝ) * (|b| + 1)
          < 1 / (|b| + 1) * C' ^ n * (|b| + 1) := by
              apply mul_lt_mul_of_pos_right hN hab_pos
          _ = C' ^ n * (1 / (|b| + 1) * (|b| + 1)) := by ring
          _ = C' ^ n * 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hab_pos)]
          _ = C' ^ n := by ring
      linarith
    have h_final : b ≤ C' ^ n / n := le_of_lt (calc
      b ≤ |b| := le_abs_self b
      _ < |b| + 1 := lt_add_one _
      _ < C' ^ n / n := h3)
    exact h_final
  rw [Filter.tendsto_atTop] at h_ratio_tendsto
  have hSigmaK_pos' : Sigma (A a b K) ≠ 0 := ne_of_gt hSigmaK_pos
  have hev := h_ratio_tendsto ((K + 2) * (1 + Real.log r) / Sigma (A a b K))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  set n := max M 1 with hn_def
  have hn_ge_M : M ≤ n := le_max_left _ _
  have hn_ge_1 : 1 ≤ n := le_max_right _ _
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_ge_1
  have h_ratio := hM n hn_ge_M
  have h_prod : (K + 2) * (1 + Real.log r) * n ≤ C' ^ n * Sigma (A a b K) := by
    have h1 : (K + 2) * (1 + Real.log r) / Sigma (A a b K) * n ≤ C' ^ n / n * n := by
      apply mul_le_mul_of_nonneg_right h_ratio (le_of_lt hn_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)] at h1
    have h2 : (↑K + 2) * (1 + Real.log r) / Sigma (A a b K) * n * Sigma (A a b K) ≤
        C' ^ n * Sigma (A a b K) := by
      apply mul_le_mul_of_nonneg_right h1 (le_of_lt hSigmaK_pos)
    have h3 : (↑K + 2) * (1 + Real.log r) / Sigma (A a b K) * (n : ℝ) * Sigma (A a b K)
            = (↑K + 2) * (1 + Real.log r) * (n : ℝ) := by
      field_simp
    rw [h3] at h2
    exact h2
  have h_nK_pos : (1 : ℕ) ≤ n + K := le_trans hn_ge_1 (Nat.le_add_right n K)
  have h_nK_cast : ((n + K : ℕ) : ℝ) = (n : ℝ) + K := by simp
  have h_sub_cast_eq : ((n + K : ℕ) : ℝ) - 1 = ((n + K - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h_nK_pos]; simp
  have h_linear_bound : (1 : ℝ) + ((n + K : ℕ) - 1) * Real.log r ≤ (n + K) * (1 + Real.log r) := by
    have h_sub_le : ((n + K : ℕ) : ℝ) - 1 ≤ (n + K : ℕ) := by linarith
    calc (1 : ℝ) + (((n + K : ℕ) : ℝ) - 1) * Real.log r
      ≤ 1 + (n + K : ℕ) * Real.log r := by
          gcongr
      _ ≤ (n + K : ℕ) + (n + K : ℕ) * Real.log r := by
          have h_one_le : (1 : ℝ) ≤ (n + K : ℕ) := Nat.one_le_cast.mpr h_nK_pos
          linarith
      _ = (n + K : ℕ) * (1 + Real.log r) := by ring
      _ = (n + K) * (1 + Real.log r) := by rw [h_nK_cast]
  have h_nK_bound : (n + K : ℝ) * (1 + Real.log r) < (K + 2) * (1 + Real.log r) * n := by
    have h_log_nonneg : 0 ≤ 1 + Real.log r := by linarith
    have h_strict : (n : ℝ) + K < (K + 2) * n := by
      have h_one_le_n : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn_ge_1
      have h_one_le_K : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK1
      nlinarith
    have h_log_pos : 0 < 1 + Real.log r := by linarith
    calc (n + K : ℝ) * (1 + Real.log r)
      < ((K + 2) * n) * (1 + Real.log r) := by
          apply mul_lt_mul_of_pos_right h_strict h_log_pos
      _ = (K + 2) * (1 + Real.log r) * n := by ring
  let k := n + K
  have hk_ge_K : K ≤ k := Nat.le_add_left K n
  have hk_ge_1 : 1 ≤ k := le_trans hn_ge_1 (Nat.le_add_right n K)
  have hkK : k - K = n := Nat.add_sub_cancel_right n K
  have h_low := h_lower k hk_ge_K
  rw [hkK] at h_low
  have h_up := h_upper k hk_ge_1
  have hk_eq_nK : (k : ℝ) = (n + K : ℕ) := by simp [k]
  rw [hk_eq_nK] at h_up
  have h_chain : 1 + (((n + K : ℕ) : ℝ) - 1) * Real.log r < C' ^ n * Sigma (A a b K) := by
    calc 1 + (((n + K : ℕ) : ℝ) - 1) * Real.log r
      ≤ ((n : ℝ) + K) * (1 + Real.log r) := h_linear_bound
      _ < (↑K + 2) * (1 + Real.log r) * n := h_nK_bound
      _ ≤ C' ^ n * Sigma (A a b K) := h_prod
  linarith

#print axioms erdos_481
-- 'Erdos481.erdos_481' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos481
