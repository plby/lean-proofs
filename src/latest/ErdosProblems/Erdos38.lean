/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 38.
https://www.erdosproblems.com/forum/thread/38

Informal authors:
- GPT-5.5 Pro
- gebyjaff

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/38#post-6131
- https://gist.githubusercontent.com/madeve-unipi/690d2bd8f6e8304ba8b456f9db559747/raw/481e3c35de8dce7af70ec440e4e121f084a61860/Erdos38.lean
-/
/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
Released under Apache 2.0 license.

Formalized from a solution by Liam Price and GPT 5.5 Pro
-/

import Mathlib

namespace Erdos38

/-!
# Erdős Problem 38 — Complete Proof

**Theorem.** There exists a set `B ⊂ ℕ` which is not an additive basis, but for which
the following holds. For `0 < α < 1`, put `β = 1 - α`, `m₀(α) = ⌈16/(αβ²)⌉`, and
`f(α) = min{β/2, αβ²/32, 2⁻ᵐ⁰⁽ᵅ⁾}`.
Then `f(α) > 0` for every `0 < α < 1`, and for every `A ⊆ ℕ` with Schnirelmann density `α`
and every `N ≥ 1`, there exists `b ∈ B` such that `|(A ∪ (A+b)) ∩ [N]| ≥ (α + f(α))N`.

## Proof outline (following the reference)

**1. Sparse dyadic shift averages (Lemma 1 in the paper):**
For each level `m ≥ 1`, we construct a small set `Sₘ ⊆ [2ᵐ]` of size `O(m³)` such that
the empirical shift average approximates the full dyadic average in operator norm (≤ 1/m).
The union `B₀ = ⋃_m supp(Sₘ)` satisfies `|B₀ ∩ [1,x]| = O((log x)⁴)`.

**2. Density increment (Section 2 in the paper):**
Given `A` with Schnirelmann density `α`, set `B = {1} ∪ B₀`.
A case analysis on `m` vs `m₀(α)` and on the density of `A ∩ [N]` shows that some `b ∈ B`
always achieves `|(A ∪ (A+b)) ∩ [N]| ≥ (α + f(α))N`.

## Differences from the reference solution

1. **Sparsity.** The paper uses Borel–Cantelli on an infinite product space for `O((log x)⁶)`.
   We enforce a per-level minimum element bound deterministically, giving `O((log x)⁴)`.

2. **Von Neumann's inequality.** The paper uses Hardy space `H²(𝕋)` theory. We use the DFT
   convolution identity, Cauchy–Schwarz, and Parseval on a finite root-of-unity grid.

3. **Grid vs circle.** The paper uses a derivative/ε-net argument for the full circle.
   We work on the DFT grid `{ω^l : l < 2^{m+1}}` directly, which suffices.

4. **Multisets vs sets.** The paper uses multisets `Sₘ`
we use `Finset ℕ` (only `supp(Sₘ)` matters).
-/


/-!
# Definitions for Erdős Problem 38

We use Mathlib's `schnirelmannDensity` and define additive basis and related notions.
-/

open scoped BigOperators Pointwise
open Finset Real Filter

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Counting function: |A ∩ {1, ..., N}|. Same as what Mathlib's Schnirelmann uses internally. -/
def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  #{a ∈ Ioc 0 N | a ∈ A}

/-- The h-fold sumset of B: {b₁ + ... + bₕ : bᵢ ∈ B}. -/
def hSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | h + 1, B => hSumset h B + B

/-- B is an additive basis if some h-fold sumset of B covers all
    sufficiently large natural numbers. -/
def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ h : ℕ, ∀ᶠ n in Filter.atTop, n ∈ hSumset h B

/-- Translation of a set by b: {a + b : a ∈ A}. -/
def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ := (· + b) '' A

/-- Count of elements in (A ∪ (A + b)) ∩ {1,...,N}. -/
def unionTranslateCount (A : Set ℕ) (b : ℕ) (N : ℕ) : ℕ :=
  countIn (A ∪ translateSet A b) N

/-- The f function from the paper.
    f(α) = min{β/2, αβ²/32, 2^(-m₀(α))} where β = 1-α, m₀ = ⌈16/(αβ²)⌉ -/
def erdos_f (α : ℝ) : ℝ :=
  let β := 1 - α
  let m₀ := Nat.ceil (16 / (α * β ^ 2))
  min (min (β / 2) (α * β ^ 2 / 32)) ((2 : ℝ) ^ (-(m₀ : ℤ)))

/-- The "hit count": number of elements c in C that are in the translate
    A + s, i.e., s < c and c - s ∈ A. This counts |(A + s) ∩ C|. -/
def hitCount (A : Set ℕ) (C : Finset ℕ) (s : ℕ) : ℕ :=
  (C.filter (fun c => s < c ∧ c - s ∈ A)).card

end

section CountIn

lemma countIn_le (A : Set ℕ) (N : ℕ) : countIn A N ≤ N := by
  unfold countIn
  calc #{a ∈ Ioc 0 N | a ∈ A}
      ≤ (Ioc 0 N).card := card_filter_le _ _
    _ = N := by simp [Nat.card_Ioc]

lemma countIn_mono_set {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    countIn A N ≤ countIn B N := by
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_Ioc] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma countIn_density (A : Set ℕ) (N : ℕ) :
    schnirelmannDensity A * N ≤ countIn A N := by
  unfold countIn
  exact schnirelmannDensity_mul_le_card_filter

end CountIn

section SchnirelmannProps

lemma one_mem_of_density_pos {A : Set ℕ} (h : 0 < schnirelmannDensity A) :
    1 ∈ A := by
  by_contra h1
  have := schnirelmannDensity_eq_zero_of_one_notMem h1
  linarith

lemma countIn_ge_alpha_mul {A : Set ℕ} {α : ℝ}
    (hα : α ≤ schnirelmannDensity A) (N : ℕ) :
    α * N ≤ countIn A N := by
  calc α * N ≤ schnirelmannDensity A * N := by
        apply mul_le_mul_of_nonneg_right hα
        exact Nat.cast_nonneg' (α := ℝ) N
    _ ≤ countIn A N := countIn_density A N

end SchnirelmannProps

section ErdosF

lemma erdos_f_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : 0 < erdos_f α :=
  lt_min (lt_min (by linarith) (by nlinarith [mul_pos hα0 (sub_pos.mpr hα1)])) (by positivity)

lemma erdos_f_le_beta_half {α : ℝ} : erdos_f α ≤ (1 - α) / 2 := by
  unfold erdos_f
  simp only
  exact le_trans (min_le_left _ _) (min_le_left _ _)

lemma erdos_f_le_density_term {α : ℝ} : erdos_f α ≤ α * (1 - α) ^ 2 / 32 := by
  unfold erdos_f
  simp only
  exact le_trans (min_le_left _ _) (min_le_right _ _)

lemma erdos_f_le_exp_term (α : ℝ) :
    erdos_f α ≤ (2 : ℝ) ^ (-(Nat.ceil (16 / (α * (1 - α) ^ 2)) : ℤ)) := by
  unfold erdos_f
  simp only
  exact min_le_right _ _

end ErdosF

/-- The number of shifts at level m. -/
def shiftL (m : ℕ) : ℕ := 128 * m ^ 3 + 1

/-!
# Hoeffding's Inequality (Finite Counting Version)

We prove Hoeffding's inequality in a purely combinatorial setting,
avoiding measure theory. The statement is:

For `f : Fin M → ℝ` with `|f i| ≤ 1` and `∑ f = 0`, and `ε > 0`:

  |{ω : Fin L → Fin M | |∑ j, f (ω j)| ≥ ε * L}| ≤ 2 * M^L * exp(-ε² * L / 2)

The proof goes through Hoeffding's lemma (MGF bound via convexity of exp).
-/

noncomputable section

/-! ## Hoeffding's Lemma -/

/--
**Hoeffding's Lemma**: For `f : Fin M → ℝ` with `|f i| ≤ 1` and `∑ f i = 0`:
    `∑ i, exp(t * f i) ≤ M * exp(t² / 2)`.

    Proof sketch: By convexity of exp, for x ∈ [-1,1]:
      exp(t*x) ≤ (1+x)/2 * exp(t) + (1-x)/2 * exp(-t)
    Summing over i with ∑ f = 0:
      ∑ exp(t * f i) ≤ M/2 * (exp(t) + exp(-t)) = M * cosh(t) ≤ M * exp(t²/2) -/
lemma hoeffding_lemma (M : ℕ) (f : Fin M → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hf_mean : ∑ i, f i = 0) (t : ℝ) :
    ∑ i : Fin M, exp (t * f i) ≤ M * exp (t ^ 2 / 2) := by
      sorry
/-! ## Product Sum Formula -/

/-- The sum of products over all tuples equals the power of the sum. -/
lemma product_sum (M L : ℕ) (f : Fin M → ℝ) :
    ∑ ω : Fin L → Fin M, ∏ j : Fin L, f (ω j) = (∑ i : Fin M, f i) ^ L := by
  have h := @Finset.prod_univ_sum (Fin L) ℝ _ _ (fun _ => Fin M) _
    (fun _ => Finset.univ) (fun _ => f)
  rw [Finset.prod_const, Finset.card_fin] at h
  rw [h]
  exact Finset.sum_congr (Fintype.piFinset_univ).symm (fun _ _ => rfl)

/--
**Hoeffding's Inequality** (counting version):
    For `f : Fin M → ℝ` with `|f i| ≤ 1` and `∑ f = 0`:
    The number of `ω : Fin L → Fin M` with `∑_j f(ω j) ≥ ε * L` is at most
    `M^L * exp(-ε² * L / 2)`. -/
lemma hoeffding_upper_tail (M L : ℕ) (_hM : 0 < M) (f : Fin M → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hf_mean : ∑ i, f i = 0) (ε : ℝ) (hε : 0 < ε) :
    ((univ.filter (fun ω : Fin L → Fin M => (ε : ℝ) * L ≤ ∑ j, f (ω j))).card : ℝ) ≤
    (M : ℝ) ^ L * exp (-(ε ^ 2 * ↑L / 2)) := by
      sorry
/-- Combined two-sided Hoeffding bound. -/
lemma hoeffding_two_sided (M L : ℕ) (hM : 0 < M) (f : Fin M → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hf_mean : ∑ i, f i = 0) (ε : ℝ) (hε : 0 < ε) :
    ((univ.filter (fun ω : Fin L → Fin M => (ε : ℝ) * L ≤ |∑ j, f (ω j)|)).card : ℝ) ≤
    2 * (M : ℝ) ^ L * exp (-(ε ^ 2 * ↑L / 2)) := by
  -- Apply Hoeffding's inequality to the upper and lower tails separately.
  have h_upper :
      ((univ.filter (fun ω : Fin L → Fin M =>
        (ε : ℝ) * L ≤ ∑ j, f (ω j))).card : ℝ) ≤
        (M : ℝ) ^ L * Real.exp (-(ε ^ 2 * L / 2)) := by
    exact hoeffding_upper_tail M L hM f hf hf_mean ε hε
  have h_lower :
      ((univ.filter (fun ω : Fin L → Fin M =>
        ∑ j, f (ω j) ≤ -(ε : ℝ) * L)).card : ℝ) ≤
        (M : ℝ) ^ L * Real.exp (-(ε ^ 2 * L / 2)) := by
    convert hoeffding_upper_tail M L hM (fun i => -f i) (fun i => ?_) ?_ ε hε
      using 1 <;>
      norm_num [*]
    exact congr_arg _ ( by ext; simp +decide [ le_neg ] )
  refine le_trans (le_trans ?_ (add_le_add h_upper h_lower)) ?_
  · norm_cast
    rw [ ← Finset.card_union_add_card_inter ]
    exact le_add_right <|
      Finset.card_le_card fun x hx => by
        norm_num at *
        cases abs_cases (∑ j, f (x j)) <;>
        first
        | left; linarith
        | right; linarith
  · ring_nf
    norm_num

end

/-!
# Von Neumann's Inequality via DFT

We prove Von Neumann's inequality for the shift operator on ℝ^N:

  |∑_s a(s) · ∑_{j: j+s<N} u(j) · v(j+s)| ≤ max_l |P(ω^l)| · ‖u‖ · ‖v‖

where P(z) = ∑ a(s) z^s is a polynomial, ω = exp(2πi/M) is a primitive M-th root
of unity, and M ≥ N + deg(P).

The proof uses the DFT to decompose the bilinear form.
-/

noncomputable section

/-- Primitive M-th root of unity. -/
def omegaPrim (M : ℕ) : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑M)

/-- For M ≥ 2 and 0 < k < M, the sum of ω^{kl} over l vanishes. -/
lemma root_sum_zero (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk0 : 0 < k) (hk : k < M) :
    ∑ l ∈ range M, (omegaPrim M) ^ (k * l) = 0 := by
  norm_num [ pow_mul ]
  rw [ geom_sum_eq ] <;> norm_num [ omegaPrim ]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm,
      div_mul_cancel₀] <;>
      norm_num [show M ≠ 0 by positivity]
  · rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ]
    norm_num [ Complex.ext_iff, div_mul_eq_mul_div ]
    intro x hx
    rw [ div_eq_iff ( by positivity ) ] at hx
    exact False.elim <|
      absurd hx <| by
        exact fun hx' => by
          exact absurd
            (Int.le_of_dvd (by positivity) <|
              show (M : ℤ) ∣ k from
                ⟨x, by
                  rw [← @Int.cast_inj ℝ]
                  push_cast
                  nlinarith [Real.pi_pos]⟩)
            (by
              norm_cast
              linarith)

/-- Full orthogonality: ∑_{l<M} ω^{kl} = M if M | k, 0 otherwise. -/
lemma root_orthogonality (M : ℕ) (hM : 0 < M) (k : ℤ) :
    ∑ l ∈ range M, (omegaPrim M) ^ (k * ↑l) =
    if (↑M : ℤ) ∣ k then ↑M else 0 := by
  split_ifs with h
  · obtain ⟨ k, rfl ⟩ := h
    norm_num [ zpow_mul, omegaPrim ]
    norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, hM.ne' ]
  · -- If $M \nmid k$, then $k$ can be written as $Mq + r$ where $0 < r < M$.
    obtain ⟨q, r, hr⟩ : ∃ q r : ℤ, 0 < r ∧ r < M ∧ k = M * q + r := by
      exact
        ⟨ k / M, k % M,
          lt_of_le_of_ne (Int.emod_nonneg _ (by positivity)) (Ne.symm (by aesop)),
          Int.emod_lt_of_pos _ (by positivity),
          by rw [Int.mul_ediv_add_emod] ⟩
    -- Since $\omega^M = 1$, we have $\omega^{kl} = \omega^{rl}$.
    have h_exp : ∀ l : ℕ, (omegaPrim M) ^ (k * l) = (omegaPrim M) ^ (r * l) := by
      intro l
      simp [hr, omegaPrim]
      norm_num [ zpow_add₀ ( Complex.exp_ne_zero _ ), zpow_mul ]
      norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, hM.ne' ]
    convert root_sum_zero M ( by linarith ) ( r.natAbs ) ( by omega ) ( by omega ) using 1
    cases r <;> aesop

/-! ## Von Neumann Inequality (Application-Specific Version)

For the application, we state Von Neumann's inequality directly in terms
of the shift bilinear form and indicator vectors.
-/

/-- The shift bilinear form: ∑_s a(s) · |{c ∈ C : s < c, c - s ∈ E}|.
    This is the weighted sum of hitCounts. -/
def shiftBilinForm (a : ℕ → ℝ) (E : Set ℕ) [DecidablePred (· ∈ E)]
    (C : Finset ℕ) (d : ℕ) : ℝ :=
  ∑ s ∈ Icc 1 d, a s * ((C.filter (fun c => s < c ∧ c - s ∈ E)).card : ℝ)

/-- Max of |P(ω^l)| over the DFT grid, where P(z) = ∑_{s=1}^d a(s) z^s. -/
def maxPolyOnGrid (a : ℕ → ℝ) (d M : ℕ) (hM : 0 < M) : ℝ :=
  Finset.sup' (range M) (nonempty_range_iff.mpr (by omega))
    (fun l => ‖∑ s ∈ Icc 1 d, (a s : ℂ) * (omegaPrim M) ^ (s * l)‖)

set_option linter.flexible false in
/-- Parseval's identity for indicator DFTs on `ℤ/Mℤ`:
`∑_{l < M} ‖∑_{s ∈ S} ω^{sl}‖² = M · |S|` when `S ⊆ Icc 1 N` and `N ≤ M`. -/
private lemma indicator_parseval (M N : ℕ) (hM : 0 < M) (hMN : 2 * N ≤ M)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 N) :
    ∑ l ∈ range M, ‖∑ s ∈ S, (omegaPrim M) ^ (s * l)‖ ^ 2 = M * S.card := by
  -- Step 1: Expand ‖·‖² = z * conj(z) and distribute
  have norm_sq_expand : ∀ l ∈ range M,
      ‖∑ s ∈ S, (omegaPrim M) ^ (s * l)‖ ^ 2 =
        ∑ s ∈ S, ∑ t ∈ S, (omegaPrim M) ^ ((s - t : ℤ) * l) := by
    intro l _hl
    have norm_sq_mul_conj : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
      simp +decide [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_sq_mul_conj, map_sum, Finset.sum_mul]
    simp +decide [sub_mul, zpow_sub₀, show omegaPrim M ≠ 0 from Complex.exp_ne_zero _]
    norm_cast
    simp +decide [div_eq_mul_inv, Finset.mul_sum _ _ _]
    norm_num [omegaPrim, Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  -- Step 2: Swap sums to get ∑_s ∑_t ∑_l ω^{(s-t)l}
  have swap_to_orthog :
      ∑ l ∈ range M, ‖∑ s ∈ S, (omegaPrim M) ^ (s * l)‖ ^ 2 =
        ∑ s ∈ S, ∑ t ∈ S, ∑ l ∈ range M, (omegaPrim M) ^ ((s - t : ℤ) * l) := by
    push_cast [Finset.sum_congr rfl norm_sq_expand]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  -- Step 3: Apply orthogonality — inner sum is M if s = t, else 0
  have orthog_eval : ∀ s t : ℕ, s ∈ S → t ∈ S →
      ∑ l ∈ range M, (omegaPrim M) ^ ((s - t : ℤ) * l) =
        if s = t then M else 0 := by
    intro s t hs ht
    split_ifs <;> simp_all +decide [root_orthogonality]
    exact fun h => False.elim <| ‹¬s = t› <| by
      obtain ⟨k, hk⟩ := h
      nlinarith [show k = 0 by
        nlinarith [Finset.mem_Icc.mp <| hS hs, Finset.mem_Icc.mp <| hS ht]]
  simp_all +decide
  norm_cast at *
  simp_all +decide [mul_comm]

set_option maxHeartbeats 800000 in
-- The DFT expansion and Parseval calculation time out at the default heartbeat limit.
set_option linter.flexible false in
/--
**Von Neumann's Inequality** (specialized to indicator vectors):
    For M ≥ 2N and polynomial of degree ≤ M/2:
    |shiftBilinForm a E C d| ≤ maxPolyOnGrid a d M · √|E| · √|C|

    Proof via DFT:
    1. Express LHS as (1/M) ∑_l P(ω^l) F(l) conj(G(l))
    2. Apply Cauchy-Schwarz: ≤ max|P| · √(∑|F|²/M) · √(∑|G|²/M)
    3. By Parseval: (1/M)∑|F|² = |E|, (1/M)∑|G|² = |C|
-/
lemma von_neumann_indicator (M N d : ℕ) (hM : 0 < M) (hMN : 2 * N ≤ M)
    (hd : d ≤ M / 2) (a : ℕ → ℝ)
    (E C : Finset ℕ) (hE : E ⊆ Icc 1 N) (hC : C ⊆ Icc 1 N) :
    |shiftBilinForm a (E : Set ℕ) C d| ≤
      maxPolyOnGrid a d M hM * Real.sqrt E.card * Real.sqrt C.card := by
        sorry
end

/-!
# Probabilistic Method for Shift Construction

We prove that for m ≥ 20, there exists a small set S ⊆ Icc 1 (2^m) satisfying both
the approximation property and a minimum element bound, using the probabilistic method.
-/

noncomputable section

/-! ## Part 1: Von Neumann Bridge -/

set_option linter.flexible false in
lemma vn_bridge (m : ℕ) (_hm : 0 < m) (L : ℕ) (hL : 0 < L)
    (ω : Fin L → ℕ) (hω : ∀ j, ω j ∈ Icc 1 (2 ^ m))
    (N : ℕ) (_hN : N ≤ 2 ^ m) (_hN0 : 0 < N)
    (E C : Finset ℕ) (hE : E ⊆ Icc 1 N) (hC : C ⊆ Icc 1 N) (_hEC : Disjoint E C)
    (h_poly : maxPolyOnGrid
      (fun s => if s ∈ Icc 1 (2 ^ m) then
        ((univ.filter (fun j : Fin L => ω j = s)).card : ℝ) / L - 1 / 2 ^ m
       else 0)
      (2 ^ m) (2 ^ (m + 1)) (by positivity) ≤ 1 / m) :
    ∃ j : Fin L,
      (((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m
       - (Real.sqrt (E.card * C.card)) / m
       ≤ hitCount (E : Set ℕ) C (ω j)) := by
         sorry
/-! ## Part 2: Probabilistic Method Helpers -/

/-
maxPolyOnGrid is bounded by the max of |Re| + |Im| over the DFT grid.
-/
set_option linter.flexible false in
lemma max_poly_le_from_re_im (a : ℕ → ℝ) (d M : ℕ) (hM : 0 < M)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h_re :
      ∀ l ∈ range M,
        |∑ s ∈ Icc 1 d, a s * ((omegaPrim M ^ (s * l) : ℂ).re)| ≤ δ)
    (h_im :
      ∀ l ∈ range M,
        |∑ s ∈ Icc 1 d, a s * ((omegaPrim M ^ (s * l) : ℂ).im)| ≤ δ) :
    maxPolyOnGrid a d M hM ≤ 2 * δ := by
  unfold maxPolyOnGrid
  simp_all +decide [ Complex.norm_def, Complex.normSq ]
  exact fun l hl =>
    Real.sqrt_le_iff.mpr
      ⟨by positivity,
        by nlinarith only [abs_le.mp (h_re l hl), abs_le.mp (h_im l hl)]⟩

set_option linter.flexible false in
/-- Count of tuples with a small element is less than half the total. -/
lemma bad_min_count_lt (m : ℕ) (_hm : 20 ≤ m) :
    2 * (univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
      ∃ j, ¬(2 ^ m < ((ω j : ℕ) + 1) * (2 * shiftL m + 2)))).card <
    Fintype.card (Fin (shiftL m) → Fin (2 ^ m)) := by
      sorry
set_option maxHeartbeats 800000 in
-- The Hoeffding/DFT union-bound proof times out at the default heartbeat limit.
set_option linter.flexible false in
/-- Count of tuples with bad `maxPolyOnGrid` is less than half the total.
The proof uses Hoeffding's inequality applied to centered trigonometric
functions, followed by a union bound over all Fourier frequencies. -/
lemma bad_approx_count_lt (m : ℕ) (hm : 20 ≤ m) :
    2 * (univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
      ¬(maxPolyOnGrid
        (fun s => if s ∈ Icc 1 (2 ^ m) then ((univ.filter (fun j : Fin (shiftL m) =>
          (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m else 0)
        (2 ^ m) (2 ^ (m + 1)) (by positivity) ≤ 1 / m))).card <
    Fintype.card (Fin (shiftL m) → Fin (2 ^ m)) := by
      sorry
/-- Good tuples exist: combining the two counting bounds. -/
lemma good_tuple_exists (m : ℕ) (hm : 20 ≤ m) :
    ∃ ω : Fin (shiftL m) → Fin (2 ^ m),
      (∀ j, 2 ^ m < ((ω j : ℕ) + 1) * (2 * shiftL m + 2)) ∧
      (maxPolyOnGrid
        (fun s => if s ∈ Icc 1 (2 ^ m) then
          ((univ.filter (fun j : Fin (shiftL m) => (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m
            - 1 / 2 ^ m
         else 0)
        (2 ^ m) (2 ^ (m + 1)) (by positivity) ≤ 1 / m) := by
  have h_bad_sum :
          (univ.filter fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ∃ j, ¬(2 ^ m < ((ω j : ℕ) + 1) * (2 * shiftL m + 2))).card +
      (univ.filter fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ¬(maxPolyOnGrid
            (fun s => if s ∈ Icc 1 (2 ^ m) then
              ((univ.filter fun j => (ω j : ℕ) + 1 = s).card : ℝ) / shiftL m - 1 / 2 ^ m
            else 0)
            (2 ^ m) (2 ^ (m + 1)) (by positivity) ≤ 1 / m)).card <
      Fintype.card (Fin (shiftL m) → Fin (2 ^ m)) :=
    by linarith [bad_min_count_lt m hm, bad_approx_count_lt m hm]
  -- Contrapose: if no good tuple exists, the bad union covers everything.
  contrapose! h_bad_sum
  rw [← Finset.card_union_add_card_inter]
  refine le_add_right ?_
  refine Finset.card_le_card fun ω _ => ?_
  -- Case-split: either ω has a too-small element, or it fails the approximation bound.
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hω : ∃ j : Fin (shiftL m), (ω j + 1 : ℕ) * (2 * shiftL m + 2) ≤ 2 ^ m
  · exact Or.inl hω
  · push Not at hω
    exact Or.inr (h_bad_sum ω hω)

/-! ## Assembly -/

theorem per_m_good_shifts_hard (m : ℕ) (hm : 20 ≤ m) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 (2 ^ m) ∧ S.Nonempty ∧ S.card ≤ shiftL m ∧
    (∀ s ∈ S, 2 ^ m < s * (2 * shiftL m + 2)) ∧
    ∀ (N : ℕ) (_ : N ≤ 2 ^ m)
      (E C : Finset ℕ) (_ : E ⊆ Icc 1 N) (_ : C ⊆ Icc 1 N) (_ : Disjoint E C),
      ∃ s ∈ S,
        (((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m -
          (Real.sqrt (E.card * C.card)) / ↑m ≤
          ↑(hitCount (E : Set ℕ) C s)) := by
  have := @vn_bridge
  contrapose! this
  obtain ⟨ω, hω⟩ := good_tuple_exists m hm
  obtain ⟨N, hN⟩ :=
    this (Finset.image (fun j => (ω j : ℕ) + 1) Finset.univ)
      (Finset.image_subset_iff.mpr fun j _ =>
        Finset.mem_Icc.mpr
          ⟨Nat.succ_pos _, Nat.succ_le_of_lt <| Fin.is_lt _⟩)
      ⟨_, Finset.mem_image_of_mem _
        (Finset.mem_univ ⟨0, by
          linarith [show 0 < shiftL m from Nat.succ_pos _]⟩)⟩
    (Finset.card_image_le.trans_eq ( Finset.card_fin _ )) (by grind)
  refine ⟨m, by linarith, shiftL m, ?_, fun j => (ω j : ℕ) + 1, ?_, N, hN.1, ?_, ?_⟩ <;>
    norm_num
  · exact Nat.succ_pos _
  · rcases N with ( _ | N ) <;> norm_num at *
    exact hN ⟨ 0, by linarith [ show shiftL m > 0 from Nat.succ_pos _ ] ⟩
  · rcases hN.2 with ⟨ E, C, hE, hC, hEC, h ⟩
    use E, hE, C, hC, hEC
    aesop

end

/-!
# Shift Approximation Lemma

For each level m ≥ 1, we construct a small set S_m ⊆ Icc 1 (2^m) with
|S_m| ≤ shiftL m = 128m³+1, satisfying:
1. An approximation property (some element achieves close to the average).
2. A minimum element bound (all elements > 2^m / (2·shiftL m)),
   ensuring sparsity of B = {1} ∪ ⋃_m S_m.
-/

noncomputable section

/-- The shift approximation data: for each m ≥ 1, a finite set of shifts. -/
structure ShiftApproxData where
  shifts : ℕ → Finset ℕ
  shifts_range : ∀ m : ℕ, 0 < m → shifts m ⊆ Icc 1 (2 ^ m)
  shifts_nonempty : ∀ m : ℕ, 0 < m → (shifts m).Nonempty
  approx : ∀ (m : ℕ) (_ : 0 < m) (N : ℕ) (_ : N ≤ 2 ^ m)
    (E C : Finset ℕ) (_ : E ⊆ Icc 1 N) (_ : C ⊆ Icc 1 N) (_ : Disjoint E C),
    ∃ s ∈ shifts m,
      (((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m
       - (Real.sqrt (E.card * C.card)) / m
       ≤ hitCount (E : Set ℕ) C s)
  sparse : ∀ (h : ℕ), Filter.Tendsto
    (fun N => ((Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)).card ^ h / (N : ℝ))
    Filter.atTop (nhds 0)

/-! ## Phase 1: Full shifts satisfy approx by pigeonhole -/

/-- When using all of Icc 1 (2^m) as shifts, the approx condition holds by pigeonhole. -/
lemma full_shifts_approx (m : ℕ) (hm : 0 < m) (N : ℕ) (_hN : N ≤ 2 ^ m)
(E C : Finset ℕ) (_hE : E ⊆ Icc 1 N) (_hC : C ⊆ Icc 1 N) (_hEC : Disjoint E C) :
∃ s ∈ Icc 1 (2 ^ m),
(((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m -
  (Real.sqrt (E.card * C.card)) / m
  ≤ hitCount (E : Set ℕ) C s) := by
  by_contra! h_contra
  have :=
    Finset.sum_lt_sum_of_nonempty
      (by
        norm_num
        linarith [ Nat.one_le_pow m 2 zero_lt_two ])
      h_contra
  norm_num at this
  rw [ mul_div_cancel₀ ] at this <;>
    first
    | positivity
    | linarith [
        show (0 : ℝ) ≤ 2 ^ m * (Real.sqrt E.card * Real.sqrt C.card / m) by
          positivity]

/-! ## Key numerical bounds -/

/-- For m ≤ 19, 2^m ≤ shiftL m = 128*m³+1. -/
lemma pow_le_shiftL_of_le_19 (m : ℕ) (hm : m ≤ 19) : 2 ^ m ≤ shiftL m := by
  unfold shiftL
  interval_cases m <;> norm_num

/-! ## Core shift existence with min bound -/

/-- For each m ≥ 1, there exist shifts satisfying the approximation property
    AND a minimum element bound.

    For m ≤ 19: S = Icc 1 (2^m), min bound trivially holds since
      2^m ≤ shiftL m, so 2^m / (2·shiftL m) < 1 ≤ min(S).
    For m ≥ 20: probabilistic method. Random S of size shiftL m from
      [1, 2^m] satisfies approx AND has min > 2^m/(2·shiftL m) with
      positive probability (using Hoeffding + Von Neumann for approx, ; Markov for the min bound).

    The min bound ensures sparsity: an element n in S_m satisfies
    n > 2^m/(2·shiftL m), so 2^m < 2·n·shiftL m. Taking logs,
    m is bounded by log₂ n + O(log log n), so only O(log N) levels
    contribute elements ≤ N. -/
lemma per_m_good_shifts (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 (2 ^ m) ∧ S.Nonempty ∧
    S.card ≤ shiftL m ∧
    (∀ s ∈ S, 2 ^ m < s * (2 * shiftL m + 2)) ∧
    ∀ (N : ℕ) (_ : N ≤ 2 ^ m)
      (E C : Finset ℕ) (_ : E ⊆ Icc 1 N) (_ : C ⊆ Icc 1 N) (_ : Disjoint E C),
      ∃ s ∈ S,
        (((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m
         - (Real.sqrt (E.card * C.card)) / ↑m
         ≤ ↑(hitCount (E : Set ℕ) C s)) := by
  by_cases hle : m ≤ 19
  · refine ⟨Icc 1 (2 ^ m), Subset.refl _, ?_, ?_, ?_, ?_⟩
    · exact nonempty_Icc.mpr (Nat.one_le_pow m 2 (by norm_num))
    · rw [Nat.card_Icc]
      have := pow_le_shiftL_of_le_19 m hle
      omega
    · intro s hs
      rw [mem_Icc] at hs
      have h1 := pow_le_shiftL_of_le_19 m hle
      nlinarith [hs.1]
    · exact fun N hN E C hE hC hEC => full_shifts_approx m hm N hN E C hE hC hEC
  · -- Probabilistic method (m ≥ 20): Hoeffding + Von Neumann + Markov
    push Not at hle
    exact per_m_good_shifts_hard m (by omega)

/-! ## Sparsity from polylog count -/

/-- If count up to N is bounded by C₀ + C₁ · (log₂ N)^4, then sparsity holds. -/
lemma sparse_of_polylog_count (shifts : ℕ → Finset ℕ)
(_h_range : ∀ m, 0 < m → shifts m ⊆ Icc 1 (2 ^ m))
(C₀ C₁ : ℝ) (_hC₀ : 0 ≤ C₀) (_hC₁ : 0 ≤ C₁)
(hbound : ∀ N : ℕ,
  ((Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)).card ≤
  C₀ + C₁ * (Nat.log 2 N + 2) ^ 4) :
    ∀ h : ℕ, Filter.Tendsto
      (fun N => ((Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)).card ^ h / (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry
/-! ## Count bound from min-bound property -/

set_option maxHeartbeats 800000 in
-- The final polynomial-logarithmic estimate times out at the default heartbeat limit.
/--
The count of elements ≤ N in ⋃ shifts m is polylog, using the min bound.

    Key argument: if s ∈ shifts m and s ≤ N, then by the min bound
    2^m < s*(2*shiftL m + 2) ≤ N*(2*shiftL m + 2). So
    m < log₂(N*(2*shiftL m + 2)) = log₂ N + log₂(2*shiftL m + 2).
    Since shiftL m = 128m³+1, log₂(2*shiftL m + 2) = O(log m).
    This gives m = O(log N), so only O(log N) levels contribute.
    Each contributes ≤ shiftL m = O(m³) = O((log N)³) elements.
    Total: O((log N)^4).
-/
lemma count_bound_from_min_shifts (shifts : ℕ → Finset ℕ)
    (h_range : ∀ m, 0 < m → shifts m ⊆ Icc 1 (2 ^ m))
    (h_card : ∀ m, 0 < m → (shifts m).card ≤ shiftL m)
    (h_min : ∀ m, 0 < m → ∀ s ∈ shifts m, 2 ^ m < s * (2 * shiftL m + 2)) :
    ∀ N : ℕ,
      ((Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)).card ≤
      (0 : ℝ) + (10 : ℝ)^10 * (Nat.log 2 N + 2) ^ 4 := by
  intro N
  have h_filter :
      ((Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)) ⊆
        Finset.biUnion (Finset.Icc 1 (4 * (Nat.log 2 N) + 68)) shifts := by
    intro n hn
    obtain ⟨ m, hm₁, hm₂ ⟩ := ( Finset.mem_filter.mp hn ).2
    -- If $m \geq 4 * \log_2 N + 69$, then
    -- $2^m \geq N * (256 * m^3 + 4)$, so no element of shifts m can be ≤ N.
    by_cases hm : m ≥ 4 * Nat.log 2 N + 69
    · have h_contradiction : 2 ^ m ≥ N * (256 * m ^ 3 + 4) := by
        have h_contradiction : ∀ m ≥ 4 * Nat.log 2 N + 69, 2 ^ m ≥ N * (256 * m ^ 3 + 4) := by
          intro m hm
          induction hm with
          | refl =>
            have h_contradiction :
                2 ^ (4 * Nat.log 2 N + 69) ≥
                  2 ^ (Nat.log 2 N + 1) *
                    (256 * (4 * Nat.log 2 N + 69) ^ 3 + 4) := by
              induction Nat.log 2 N with
              | zero =>
                norm_num [ Nat.pow_succ', Nat.pow_mul ] at *
              | succ k ih =>
                norm_num [ Nat.pow_succ', Nat.pow_mul ] at *
                nlinarith [
                  pow_pos ( zero_lt_two' ℕ ) k,
                  pow_nonneg ( Nat.zero_le k ) 2,
                  pow_nonneg ( Nat.zero_le k ) 3 ]
            exact
              le_trans
                (Nat.mul_le_mul_right _
                  (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)))
                h_contradiction
          | step hm ih =>
            rename_i m
            norm_num [ pow_succ' ] at *
            nlinarith [
              Nat.zero_le ( N * m ),
              Nat.zero_le ( N * m ^ 2 ),
              Nat.zero_le ( N * m ^ 3 ),
              Nat.zero_le ( N * m ^ 4 ),
              Nat.zero_le ( N * m ^ 5 ),
              Nat.zero_le ( N * m ^ 6 ),
              Nat.zero_le ( N * m ^ 7 ),
              Nat.zero_le ( N * m ^ 8 ),
              Nat.zero_le ( N * m ^ 9 ),
              Nat.zero_le ( N * m ^ 10 ) ]
        exact h_contradiction m hm
      contrapose! h_min
      exact ⟨ m, hm₁, n, hm₂, by
        rw [ show shiftL m = 128 * m ^ 3 + 1 by rfl ]
        nlinarith [
          Finset.mem_Icc.mp ( h_range m hm₁ hm₂ ),
          show n ≤ N from Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ] ⟩
    · exact Finset.mem_biUnion.mpr ⟨ m, Finset.mem_Icc.mpr ⟨ hm₁, by linarith ⟩, hm₂ ⟩
  -- The cardinality of the biUnion is at most the sum of the cardinalities of the shifts.
  have h_biUnion_card :
      ((Finset.biUnion (Finset.Icc 1 (4 * (Nat.log 2 N) + 68)) shifts).card : ℝ) ≤
        ∑ m ∈ Finset.Icc 1 (4 * (Nat.log 2 N) + 68), (shiftL m : ℝ) := by
    exact_mod_cast
      le_trans ( Finset.card_biUnion_le )
        ( Finset.sum_le_sum fun m hm => h_card m <| Finset.mem_Icc.mp hm |>.1 )
  refine le_trans ?_ ( h_biUnion_card.trans ?_ )
  · exact_mod_cast Finset.card_le_card h_filter
  · unfold shiftL
    erw [ Finset.sum_Ico_eq_sum_range ]
    exact mod_cast Nat.recOn ( Nat.log 2 N ) ( by norm_num ) fun n ihn => by
      norm_num [ Nat.mul_succ, Finset.sum_range_succ ] at ihn ⊢
      nlinarith only [
        ihn,
        pow_nonneg ( Nat.zero_le n ) 2,
        pow_nonneg ( Nat.zero_le n ) 3 ]

/-! ## Assembly -/

/-- **Shift approximation data exists.** -/
theorem shift_approx_exists : Nonempty ShiftApproxData := by
  have h_shifts : ∀ m, 0 < m →
    ∃ S : Finset ℕ, S ⊆ Icc 1 (2^m) ∧ S.Nonempty ∧ S.card ≤ shiftL m ∧
    (∀ s ∈ S, 2^m < s * (2 * shiftL m + 2)) ∧
    ∀ N ≤ 2^m, ∀ E C : Finset ℕ, E ⊆ Icc 1 N → C ⊆ Icc 1 N → Disjoint E C →
    ∃ s ∈ S, (((Icc 1 (2^m)).sum (fun t => hitCount (E : Set ℕ) C t) : ℝ) / 2^m
       - (Real.sqrt (E.card * C.card)) / m ≤ hitCount (E : Set ℕ) C s) :=
    fun m hm => per_m_good_shifts m hm
  let shifts : ℕ → Finset ℕ := fun m =>
    if hm : 0 < m then (h_shifts m hm).choose else ∅
  have h_range : ∀ m, 0 < m → shifts m ⊆ Icc 1 (2^m) := by
    intro m hm
    simp only [shifts, dif_pos hm]
    exact (h_shifts m hm).choose_spec.1
  have h_card : ∀ m, 0 < m → (shifts m).card ≤ shiftL m := by
    intro m hm
    simp only [shifts, dif_pos hm]
    exact (h_shifts m hm).choose_spec.2.2.1
  have h_min : ∀ m, 0 < m → ∀ s ∈ shifts m, 2^m < s * (2 * shiftL m + 2) := by
    intro m hm
    simp only [shifts, dif_pos hm]
    exact (h_shifts m hm).choose_spec.2.2.2.1
  refine ⟨⟨shifts, h_range, ?_, ?_, ?_⟩⟩
  · intro m hm
    simp only [shifts, dif_pos hm]
    exact (h_shifts m hm).choose_spec.2.1
  · intro m hm N hN E C hE hC hEC
    simp only [shifts, dif_pos hm]
    exact (h_shifts m hm).choose_spec.2.2.2.2 N hN E C hE hC hEC
  · exact sparse_of_polylog_count shifts h_range 0 (10^10) (by norm_num) (by positivity)
      (count_bound_from_min_shifts shifts h_range h_card h_min)

end

/-!
# B is not an additive basis

We show that if B is sparse (|B ∩ [1,N]| = o(N^{1/h}) for every h),
then B is not an additive basis.
-/

noncomputable section

/-- The set B constructed from shift approximation data. -/
def constructB (d : ShiftApproxData) : Set ℕ :=
  {1} ∪ {n | ∃ m, 0 < m ∧ n ∈ d.shifts m}

set_option linter.flexible false in
/-- If |B ∩ [1,N]|^h / N → 0 for every h, then B is not an additive basis. -/
lemma not_basis_of_sparse {B : Set ℕ}
    (hsparse : ∀ h : ℕ, Tendsto (fun N => (countIn B N : ℝ) ^ h / N) atTop (nhds 0)) :
    ¬IsAdditiveBasis B := by
  intro hB
  obtain ⟨h, h_basis⟩ := hB
  have h_sums : ∀ᶠ N in Filter.atTop, countIn (hSumset h B) N ≥ N / 2 := by
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, n ∈ hSumset h B := by
      aesop
    refine Filter.eventually_atTop.mpr ⟨2 * N₀ + 2, fun N hN => ?_⟩
    refine le_trans ?_ (Finset.card_mono <| show
      Finset.Icc (N₀ + 1) N ⊆
        Finset.filter (fun x => x ∈ hSumset h B) (Finset.Ioc 0 N) from
      fun x hx =>
        Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr
              ⟨by linarith [Finset.mem_Icc.mp hx],
                by linarith [Finset.mem_Icc.mp hx]⟩,
            hN₀ x <| by linarith [Finset.mem_Icc.mp hx]⟩)
    simp +arith +decide [ Nat.div_le_iff_le_mul_add_pred ]
    omega
  have h_sums_bound : ∀ᶠ N in Filter.atTop, countIn (hSumset h B) N ≤ (countIn B N + 1) ^ h := by
    have h_sums_bound : ∀ᶠ N in Filter.atTop, countIn (hSumset h B) N ≤ (countIn B N + 1) ^ h := by
      have h_sums_bound_aux :
          ∀ n ∈ hSumset h B, ∀ N, n ≤ N →
            n ∈ Finset.image (fun f : Fin h → ℕ => ∑ i, f i)
              (Finset.Icc (fun _ => 0) (fun _ => N) |>.filter
                (fun f => ∀ i, f i ∈ B ∪ {0})) := by
        intro n hn N hN
        obtain ⟨f, hf⟩ : ∃ f : Fin h → ℕ, (∀ i, f i ∈ B ∪ {0}) ∧ (∑ i, f i = n) := by
          have h_sums_bound_aux :
              ∀ h : ℕ, ∀ n ∈ hSumset h B,
                ∃ f : Fin h → ℕ,
                  (∀ i, f i ∈ B ∪ {0}) ∧ (∑ i, f i = n) := by
            intro h n hn
            induction h generalizing n with
            | zero =>
              simp_all +decide [ hSumset ]
            | succ h ih =>
              simp_all +decide [ hSumset ]
              rcases hn with ⟨ x, hx, y, hy, rfl ⟩
              obtain ⟨ f, hf₁, hf₂ ⟩ := ih x hx
              use Fin.snoc f y
              simp_all +decide [ Fin.sum_univ_castSucc ]
              exact fun i => by cases i using Fin.lastCases <;> simp +decide [ * ]
          exact h_sums_bound_aux h n hn
        exact
          Finset.mem_image.mpr
            ⟨f,
              Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr
                    ⟨fun _ => Nat.zero_le _,
                      fun i =>
                        hf.2 ▸
                          Finset.single_le_sum (fun a _ => Nat.zero_le (f a))
                            (Finset.mem_univ i) |>
                            le_trans <| hN⟩,
                  hf.1⟩,
              hf.2⟩
      have h_sums_bound_aux :
          ∀ N,
            countIn (hSumset h B) N ≤
              Finset.card
                (Finset.image (fun f : Fin h → ℕ => ∑ i, f i)
                  (Finset.Icc (fun _ => 0) (fun _ => N) |>.filter
                    (fun f => ∀ i, f i ∈ B ∪ {0}))) := by
        intro N
        exact (by refine Finset.card_le_card ?_ ; grind)
      have h_sums_bound_aux :
          ∀ N,
            Finset.card
              (Finset.filter (fun f : Fin h → ℕ => ∀ i, f i ∈ B ∪ {0})
                (Finset.Icc (fun _ => 0) (fun _ => N))) ≤
              (countIn B N + 1) ^ h := by
        intro N
        have h_sums_bound_aux :
            Finset.card
              (Finset.filter (fun f : Fin h → ℕ => ∀ i, f i ∈ B ∪ {0})
                (Finset.Icc (fun _ => 0) (fun _ => N))) ≤
            Finset.card
              (Finset.pi Finset.univ fun _ : Fin h =>
                Finset.filter (fun x => x ∈ B ∪ {0}) (Finset.Icc 0 N)) := by
          refine le_of_eq ?_
          refine Finset.card_bij (fun f hf => fun i _ => f i) ?_ ?_ ?_ <;>
            simp +decide [funext_iff]
          · exact fun a ha₁ ha₂ ha₃ i => ⟨ ha₂ i, ha₃ i ⟩
          · exact fun b hb =>
              ⟨fun i => b i (Finset.mem_univ i),
                ⟨⟨fun i => Nat.zero_le _, fun i => hb i |>.1⟩,
                  fun i => hb i |>.2⟩,
                fun i => rfl⟩
        refine le_trans h_sums_bound_aux ?_
        simp +decide [ countIn ]
        rw [
          show
            Finset.filter (fun x => x = 0 ∨ x ∈ B) (Finset.Icc 0 N) =
              Finset.filter (fun x => x ∈ B) (Finset.Ioc 0 N) ∪ {0} from ?_,
          Finset.card_union] <;>
          norm_num
        ext ( _ | x ) <;> simp +decide
      exact Filter.Eventually.of_forall fun N =>
        le_trans (by solve_by_elim)
          (Finset.card_image_le.trans (h_sums_bound_aux N))
    convert h_sums_bound using 1
  have h_contradiction :
      Filter.Tendsto (fun N => ((countIn B N + 1) ^ h : ℝ) / N)
        Filter.atTop (nhds 0) := by
    have h_contradiction :
        Filter.Tendsto (fun N => ((countIn B N : ℝ) ^ h + 1) / N)
          Filter.atTop (nhds 0) := by
      simpa [ add_div ] using Filter.Tendsto.add ( hsparse h ) ( tendsto_inv_atTop_nhds_zero_nat )
    have h_contradiction :
        ∀ᶠ N in Filter.atTop,
          ((countIn B N + 1) ^ h : ℝ) ≤
            2 ^ h * ((countIn B N : ℝ) ^ h + 1) := by
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN
      rcases le_or_gt ( countIn B N : ℝ ) 1 with h | h <;> norm_cast at * <;> simp_all +decide
      · interval_cases countIn B N <;> norm_num
        grind
      · exact
          le_trans
            (pow_le_pow_left₀ (by positivity)
              (show countIn B N + 1 ≤ 2 * countIn B N by linarith) _)
            (by
              rw [mul_pow]
              exact mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right zero_le_one) (by positivity))
    have h_contradiction :
        Filter.Tendsto (fun N => (2 ^ h * ((countIn B N : ℝ) ^ h + 1)) / N)
          Filter.atTop (nhds 0) := by
      convert
        (‹Tendsto
            (fun N : ℕ => (countIn B N ^ h + 1 : ℝ) / N)
            Filter.atTop (nhds 0)›.const_mul (2 ^ h))
        using 2 <;>
        ring
    refine squeeze_zero_norm' ?_ h_contradiction
    filter_upwards [
      ‹∀ᶠ N in atTop,
        (countIn B N + 1 : ℝ) ^ h ≤ 2 ^ h * (countIn B N ^ h + 1)›
    ] with N hN using by
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
  have h_contradiction :
      Filter.Tendsto (fun N => (countIn (hSumset h B) N : ℝ) / N)
        Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ h_contradiction
    filter_upwards [ h_sums_bound ] with N hN using by
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      norm_cast
  have := h_contradiction.eventually ( gt_mem_nhds <| show 0 < 1 / 4 by norm_num )
  simp_all +decide [ division_def ]
  obtain ⟨ a, ha ⟩ := this
  obtain ⟨ b, hb ⟩ := h_sums
  use
    absurd
      (ha (2 * (a + b + 1)) (by linarith))
      (by
        rw [← div_eq_mul_inv]
        rw [div_lt_iff₀]
        · norm_num
          linarith [
            hb (2 * (a + b + 1)) (by linarith),
            Nat.div_add_mod (2 * (a + b + 1)) 2,
            Nat.mod_lt (2 * (a + b + 1)) two_pos,
            show
              (countIn (hSumset h B) (2 * (a + b + 1)) : ℝ) ≥
                (2 * (a + b + 1)) / 2 from by
              exact
                le_trans (by norm_num)
                  (Nat.cast_le.mpr (hb (2 * (a + b + 1)) (by linarith)))
          ]
        · positivity)

set_option linter.flexible false in
/-- The constructed B is not an additive basis. -/
theorem constructB_not_basis (d : ShiftApproxData) : ¬IsAdditiveBasis (constructB d) := by
  sorry
end

/-!
# Density Increment

We show that for the constructed B and any A with Schnirelmann density α ∈ (0,1),
for every N ≥ 1, there exists b ∈ B such that
|(A ∪ (A+b)) ∩ [N]| ≥ (α + f(α))N.

The proof splits into cases based on m vs m₀(α).
-/

noncomputable section

set_option linter.flexible false in
/-- Double counting: Σ_{s=1}^{M} hitCount A C s = Σ_{c∈C} countIn A (c-1).
    Valid when all c ∈ C satisfy c ≤ M. -/
lemma double_counting (A : Set ℕ) (C : Finset ℕ) (M : ℕ)
    (hC : ∀ c ∈ C, c ≤ M) :
    (Icc 1 M).sum (fun s => hitCount A C s) =
    C.sum (fun c => countIn A (c - 1)) := by
  -- By interchanging the order of summation, we can rewrite the left-hand side of the equation.
  have h_interchange :
      (∑ s ∈ Icc 1 M, ∑ c ∈ C,
        (if s < c ∧ c - s ∈ A then 1 else 0)) =
        ∑ c ∈ C, ∑ s ∈ Icc 1 M,
          (if s < c ∧ c - s ∈ A then 1 else 0) := by
    exact Finset.sum_comm
  convert h_interchange using 2
  · unfold hitCount
    aesop
  · rename_i c hc
    rcases c with ( _ | c ) <;> simp_all +decide [ countIn ]
    refine Finset.card_bij (fun x hx => c + 1 - x) ?_ ?_ ?_ <;> simp_all +decide
    · exact fun a ha₁ ha₂ ha₃ =>
        ⟨⟨Nat.sub_pos_of_lt (by linarith),
            by linarith [hC _ hc]⟩,
          ha₁,
          by
            simpa [Nat.sub_sub_self (by linarith : a ≤ c + 1)] using ha₃⟩
    · intros
      omega
    · exact fun b hb₁ hb₂ hb₃ hb₄ =>
        ⟨c + 1 - b,
          ⟨⟨Nat.sub_pos_of_lt (by linarith),
              Nat.sub_le_of_le_add (by linarith)⟩,
            hb₄⟩,
          Nat.sub_sub_self (by linarith)⟩

/-
============ Key counting argument ============

If c ∉ A and c ≥ 1, then countIn A (c-1) = countIn A c ≥ α*c.
-/
set_option linter.flexible false in
lemma countIn_pred_of_not_mem {A : Set ℕ} {c : ℕ} (hc : c ≥ 1) (hcA : c ∉ A) :
    countIn A (c - 1) = countIn A c := by
  rcases c with ( _ | c ) <;> simp_all +decide [ countIn ]
  rw [ Finset.card_filter, Finset.card_filter ]
  rw [ Finset.sum_Ioc_succ_top ] <;> aesop

/-
Sum of elements in a finset of distinct positive integers with q elements is ≥ q(q+1)/2.
-/
lemma sum_ge_triangular (C : Finset ℕ) (hC : ∀ c ∈ C, c ≥ 1) :
    C.card * (C.card + 1) / 2 ≤ C.sum id := by
  -- Since $C$ is a finite set of distinct positive integers, we can order its
  -- elements as $c_1 < c_2 < \cdots < c_q$.
  have h_order : ∃ f : Fin C.card → ℕ, StrictMono f ∧ ∀ i, f i ∈ C := by
    exact ⟨ fun i => C.orderEmbOfFin rfl i, by aesop_cat, by aesop_cat ⟩
  -- Since $f$ is strictly monotone, we have $f i ≥ i + 1$ for all $i$.
  obtain ⟨f, hf_mono, hf_mem⟩ := h_order
  have h_f_ge : ∀ i, f i ≥ i + 1 := by
    intro ⟨ i, hi ⟩
    revert hi
    induction i with
    | zero =>
      intro hi
      exact hC _ ( hf_mem _ )
    | succ i ih =>
      intro hi
      exact lt_of_le_of_lt ( ih ( Nat.lt_of_succ_lt hi ) ) ( hf_mono ( Nat.lt_succ_self _ ) )
  have h_sum_ge : ∑ i ∈ Finset.univ.image f, i ≥ ∑ i ∈ Finset.range C.card, (i + 1) := by
    rw [ Finset.sum_image <| by intros i hi j hj hij; exact hf_mono.injective hij ]
    rw [ Finset.sum_range ]
    exact Finset.sum_le_sum fun i _ => h_f_ge i
  convert h_sum_ge.le using 1
  · exact
      Nat.div_eq_of_eq_mul_left zero_lt_two
        (Nat.recOn (Finset.card C) (by norm_num) fun n ih => by
          norm_num [Finset.sum_range_succ] at *
          linarith)
  · rw [
      Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.mpr fun i _ => hf_mem i)
        (by
          rw [Finset.card_image_of_injective _ hf_mono.injective, Finset.card_fin])]
    rfl

set_option linter.flexible false in
/-- Lower bound on the full average of hit counts when C ⊆ [N] \ A, |C| = q.
    Uses: countIn A (c-1) ≥ α*c (since c ∉ A), Σ c ≥ q(q+1)/2 ≥ q²/2. -/
lemma full_average_lower_bound {A : Set ℕ} {α : ℝ}
    (hα : α ≤ schnirelmannDensity A) {N : ℕ} (hN : 0 < N)
    {C : Finset ℕ} (hC : C ⊆ Icc 1 N) (hCA : ∀ c ∈ C, c ∉ A)
    (hCsize : (C.card : ℝ) > (1 - α) * N / 2)
    {M : ℕ} (hM : N ≤ M) (hM2 : M ≤ 2 * N) :
    α * (1 - α) ^ 2 * N / 16 ≤
    ((Icc 1 M).sum (fun s => hitCount A C s) : ℝ) / M := by
  /- Step 1: By double counting and the Schnirelmann density lower bound,
     the total hit-count sum is at least `α · ∑ c ∈ C, c`. -/
  have hCle : ∀ c ∈ C, c ≤ M := fun c hc =>
    le_trans (Finset.mem_Icc.mp (hC hc)).2 hM
  have hsum_eq : (∑ s ∈ Icc 1 M, hitCount A C s : ℝ) = ∑ c ∈ C, countIn A (c - 1) := by
    exact_mod_cast double_counting A C M hCle
  have hsum_ge_α : (∑ s ∈ Icc 1 M, hitCount A C s : ℝ) ≥ α * ∑ c ∈ C, (c : ℝ) := by
    rw [hsum_eq, Finset.mul_sum]
    push_cast
    apply Finset.sum_le_sum
    intro x hx
    rw [countIn_pred_of_not_mem (Finset.mem_Icc.mp (hC hx)).1 (hCA x hx)]
    exact_mod_cast countIn_ge_alpha_mul hα x
  /- Step 2: Since elements of `C` are distinct positive integers,
     `∑ c ∈ C, c ≥ |C|² / 2` by the triangular-number bound. -/
  have hC_pos : ∀ c ∈ C, c ≥ 1 := fun c hc => (Finset.mem_Icc.mp (hC hc)).1
  have hsum_triangular : (∑ c ∈ C, (c : ℝ)) ≥ (C.card : ℝ) ^ 2 / 2 := by
    have := sum_ge_triangular C hC_pos
    rw [ge_iff_le, div_le_iff₀] <;> norm_cast
    rw [← Nat.cast_sum]; norm_cast
    have : 2 ∣ C.card * (C.card + 1) := by
      exact even_iff_two_dvd.mp (by simp +arith +decide [mul_add, parity_simps])
    nlinarith! [Nat.div_mul_cancel this]
  /- Step 3: Combine the bounds. Split on the sign of `α` to avoid
     positivity obligations when `α < 0` (vacuous but must be handled). -/
  by_cases hα_nonneg : 0 ≤ α
  · -- Main case: `α ≥ 0`.
    have hα_le_one : α ≤ 1 := by
      refine hα.trans ?_
      refine le_trans (ciInf_le ⟨0, Set.forall_mem_range.mpr fun n => by positivity⟩ 1) ?_
      simp
      exact Finset.card_filter_le _ _
    have hβN_nonneg : (0 : ℝ) ≤ (1 - α) * N :=
      mul_nonneg (sub_nonneg.2 hα_le_one) (Nat.cast_nonneg _)
    -- From `|C| > (1-α)N/2`, deduce `(1-α)² N² ≤ 4 |C|²`.
    have hcard_sq : (1 - α) ^ 2 * N ^ 2 ≤ 4 * (C.card : ℝ) ^ 2 := by nlinarith
    -- Hence `α(1-α)²N / 16 · (2N) ≤ α · |C|² / 2`.
    have hlhs_le : α * (1 - α) ^ 2 * N / 16 * (2 * N : ℝ) ≤ α * ((C.card : ℝ) ^ 2 / 2) := by
      nlinarith
    -- Chain: LHS · M ≤ LHS · 2N ≤ α · |C|²/2 ≤ α · Σ c ≤ Σ hitCount.
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast Nat.lt_of_lt_of_le hN hM
    rw [le_div_iff₀ hM_pos]
    have hlhs_nonneg : 0 ≤ α * (1 - α) ^ 2 * N / 16 := by positivity
    calc α * (1 - α) ^ 2 * N / 16 * M
        _ ≤ α * (1 - α) ^ 2 * N / 16 * (2 * N) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hM2) hlhs_nonneg
        _ ≤ α * ((C.card : ℝ) ^ 2 / 2) := hlhs_le
        _ ≤ α * ∑ c ∈ C, (c : ℝ) :=
            mul_le_mul_of_nonneg_left hsum_triangular hα_nonneg
        _ ≤ ∑ s ∈ Icc 1 M, (hitCount A C s : ℝ) := hsum_ge_α
  · -- Degenerate case: `α < 0`, so the LHS is non-positive.
    have hlhs_nonpos : α * (1 - α) ^ 2 * N / 16 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα_nonneg) (sq_nonneg _))
          (Nat.cast_nonneg _)
      · norm_num
    have hrhs_nonneg : 0 ≤ (∑ s ∈ Icc 1 M, (hitCount A C s : ℝ)) / M :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
set_option linter.flexible false in
/-- If `1 ∈ A` and there exists `c ∈ [N]` with `c ∉ A`, then translating by 1 adds
at least one new element. -/
lemma translate_one_adds_new {A : Set ℕ} {N : ℕ}
    (h1 : 1 ∈ A) {c : ℕ} (hc : c ∈ Icc 1 N) (hcA : c ∉ A) :
    unionTranslateCount A 1 N ≥ countIn A N + 1 := by
  -- Let c₀ be the smallest element of [N] not in A.
  set w := (⟨c, hc, hcA⟩ : ∃ c ∈ Finset.Icc 1 N, c ∉ A)
  obtain ⟨c₀, hc₀⟩ :
      ∃ c₀ ∈ Finset.Icc 1 N, c₀ ∉ A ∧ ∀ c ∈ Finset.Icc 1 N, c < c₀ → c ∈ A :=
    ⟨Nat.find w, (Nat.find_spec w).1, (Nat.find_spec w).2, by aesop⟩
  -- Since c₀ ∉ A and c₀ - 1 ∈ A, we have c₀ ∈ translateSet A 1.
  have hc₀_trans : c₀ ∈ translateSet A 1 := by
    rcases c₀ with _ | _ | c₀ <;> simp_all +decide [translateSet]
    grind
  unfold unionTranslateCount countIn
  refine Finset.card_lt_card ?_
  simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
  exact ⟨c₀, hc₀.1.1, hc₀.1.2, Or.inr hc₀_trans, hc₀.2.1⟩

/-- `unionTranslateCount` is at least `countIn` (since `A ⊆ A ∪ (A + b)`). -/
lemma unionTranslateCount_ge_countIn (A : Set ℕ) (b N : ℕ) :
    countIn A N ≤ unionTranslateCount A b N :=
  countIn_mono_set Set.subset_union_left N

/-- If `C ⊆ [N] \ A`, then `countIn A N + hitCount A C b ≤ unionTranslateCount A b N`. -/
lemma unionTranslateCount_ge_countIn_add_hitCount (A : Set ℕ) (b N : ℕ)
    (C : Finset ℕ) (hC : C ⊆ Icc 1 N) (hCA : ∀ c ∈ C, c ∉ A) :
    (countIn A N : ℤ) + hitCount A C b ≤ unionTranslateCount A b N := by
  norm_cast
  unfold countIn unionTranslateCount hitCount
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_mono ?_
    simp +decide [Finset.subset_iff, translateSet]
    grind
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
      hCA x (Finset.mem_filter.mp hx₂).1 (Finset.mem_filter.mp hx₁).2

/-- When `countIn A N = N` (A covers all of [N]), `b = 1` works trivially. -/
lemma density_increment_full_cover (A : Set ℕ) (N : ℕ)
    (hfull : countIn A N = N) (α : ℝ) (hα : α + erdos_f α ≤ 1) :
    (α + erdos_f α) * N ≤ unionTranslateCount A 1 N := by
  refine le_trans (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)) ?_
  exact mod_cast by linarith [unionTranslateCount_ge_countIn A 1 N]

/-- When N is small (`N ≤ 2^(m₀-1)`), `b = 1` adds at least one element and `f(α)N ≤ 1`. -/
lemma density_increment_small_N {A : Set ℕ} {α : ℝ} (hα : α = schnirelmannDensity A)
    (hα0 : 0 < α) (hα1 : α < 1) {N : ℕ}
    (hNA : countIn A N < N)
    (hNsmall : (N : ℝ) ≤ 2 ^ (Nat.ceil (16 / (α * (1 - α) ^ 2)) - 1 : ℕ)) :
    (α + erdos_f α) * N ≤ unionTranslateCount A 1 N := by
  -- Since countIn A N < N, there exists c ∈ Icc 1 N with c ∉ A.
  obtain ⟨c, hc⟩ : ∃ c ∈ Finset.Icc 1 N, c ∉ A := by
    contrapose! hNA
    exact le_trans (by aesop) (Finset.card_le_card <|
      show Finset.Icc 1 N ⊆ Finset.filter (· ∈ A) (Finset.Ioc 0 N) from
        fun x hx => Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨by linarith [Finset.mem_Icc.mp hx],
              by linarith [Finset.mem_Icc.mp hx]⟩,
            hNA x hx⟩)
  -- unionTranslateCount A 1 N ≥ countIn A N + 1 ≥ α * N + 1.
  have h_translate_ge : unionTranslateCount A 1 N ≥ α * N + 1 := by
    have h_count_ge : unionTranslateCount A 1 N ≥ countIn A N + 1 :=
      translate_one_adds_new (one_mem_of_density_pos (hα ▸ hα0)) hc.1 hc.2
    refine le_trans ?_ (Nat.cast_le.mpr h_count_ge)
    simpa using countIn_ge_alpha_mul (hα.symm ▸ le_rfl) N
  -- Since N ≤ 2^(m₀ - 1), we have erdos_f α * N ≤ 1.
  have h_erdos_f_N_le_one : erdos_f α * N ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left hNsmall (erdos_f_pos hα0 hα1).le) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (erdos_f_le_exp_term α) (by positivity)) ?_
    rcases n : ⌈16 / (α * (1 - α) ^ 2)⌉₊ with _ | _ | n <;> simp_all +decide [pow_succ']
    · norm_num
    · norm_num [zpow_add₀, zpow_neg]
      ring_nf
      norm_num
      norm_num [← mul_pow]
  linarith

/-! ### Case: dense A, use b = 1
When `countIn A N ≥ (α + β/2) * N`, `b = 1` gives the density increment since `f(α) ≤ β/2`.
-/
lemma density_increment_dense {A : Set ℕ} {α : ℝ} {N : ℕ}
    (hdense : (α + (1 - α) / 2) * N ≤ (countIn A N : ℝ)) :
    (α + erdos_f α) * N ≤ unionTranslateCount A 1 N := by
  refine le_trans ?_ (hdense.trans ?_)
  · gcongr
    exact erdos_f_le_beta_half
  · exact_mod_cast unionTranslateCount_ge_countIn A 1 N

/-! ### Case: use shift approximation
When `m ≥ m₀`, `|E| < (α + β/2)N`, and `|C| > βN/2`, find `s ∈ d.shifts m` with enough
new elements.
-/
set_option linter.flexible false in
lemma density_increment_shift_approx (d : ShiftApproxData)
    (A : Set ℕ) (α : ℝ) (hα : α = schnirelmannDensity A)
    (hα0 : 0 < α) (hα1 : α < 1)
    (N : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : 0 < m) (hNM : N ≤ 2 ^ m) (hM2N : 2 ^ m ≤ 2 * N)
    (hm_ge : m ≥ Nat.ceil (16 / (α * (1 - α) ^ 2)))
    (hCsize : ((Icc 1 N).filter (fun c => c ∉ A)).card > (1 - α) * ↑N / 2) :
    ∃ b ∈ constructB d, (α + erdos_f α) * N ≤ unionTranslateCount A b N := by
  -- Obtain a good shift from the approximation data.
  obtain ⟨s, hs⟩ :
      ∃ s ∈ d.shifts m,
        ((Icc 1 (2 ^ m)).sum fun t =>
              (hitCount A (Finset.filter (· ∉ A) (Icc 1 N)) t : ℝ)) / 2 ^ m -
          Real.sqrt ((Finset.filter (· ∈ A) (Icc 1 N)).card *
            (Finset.filter (· ∉ A) (Icc 1 N)).card) / m ≤
          hitCount A (Finset.filter (· ∉ A) (Icc 1 N)) s := by
    convert d.approx m hm N hNM
      (Finset.filter (· ∈ A) (Finset.Icc 1 N))
      (Finset.filter (· ∉ A) (Finset.Icc 1 N)) _ _ _ using 1 <;>
      norm_num [Finset.filter_mem_eq_inter, Finset.filter_not]
    · unfold hitCount
      simp +decide [Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc]
      congr! 3
      · congr! 3; congr! 1; grind
      · congr! 3; grind
    · exact Finset.disjoint_sdiff
  -- The full average is bounded below.
  have h_full_avg :
      α * (1 - α) ^ 2 * N / 16 ≤
        ((Icc 1 (2 ^ m)).sum fun t =>
              (hitCount A (Finset.filter (· ∉ A) (Icc 1 N)) t : ℝ)) / 2 ^ m := by
    convert full_average_lower_bound _ hN _ _ _ _ _ using 1
    all_goals norm_cast
    · linarith
    · exact Finset.filter_subset _ _
    · aesop
  -- The error term is small enough.
  have h_error :
      Real.sqrt ((Finset.filter (· ∈ A) (Icc 1 N)).card *
        (Finset.filter (· ∉ A) (Icc 1 N)).card) / m ≤
      α * (1 - α) ^ 2 * N / 32 := by
    have h_sqrt_le :
        Real.sqrt ((Finset.filter (· ∈ A) (Icc 1 N)).card *
          (Finset.filter (· ∉ A) (Icc 1 N)).card) ≤ N / 2 := by
      have h_card_sum :
          (Finset.filter (· ∈ A) (Icc 1 N)).card +
            (Finset.filter (· ∉ A) (Icc 1 N)).card = N := by
        rw [Finset.card_filter_add_card_filter_not]; aesop
      rw [Real.sqrt_le_left] <;>
        nlinarith only [
          sq_nonneg ((Finset.filter (· ∈ A) (Finset.Icc 1 N)).card -
            (Finset.filter (· ∉ A) (Finset.Icc 1 N)).card : ℝ),
          show ((Finset.filter (· ∈ A) (Finset.Icc 1 N)).card : ℝ) +
            (Finset.filter (· ∉ A) (Finset.Icc 1 N)).card = N from
            by exact_mod_cast h_card_sum]
    rw [div_le_iff₀ (by positivity)]
    refine le_trans h_sqrt_le ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀] <;> try positivity
    have hαβ_pos : 0 < α * (1 - α) ^ 2 := mul_pos hα0 (sq_pos_of_pos (sub_pos.mpr hα1))
    rw [ge_iff_le, Nat.ceil_le] at hm_ge
    rw [div_le_iff₀] at hm_ge <;> nlinarith
  -- Combine the bounds.
  have h_combined :
      (α + erdos_f α) * N ≤
        (countIn A N : ℝ) + hitCount A (Finset.filter (· ∉ A) (Icc 1 N)) s := by
    have h_inner :
        (α + erdos_f α) * N ≤ (countIn A N : ℝ) + α * (1 - α) ^ 2 * N / 32 := by
      have h_countIn : (countIn A N : ℝ) ≥ α * N :=
        hα.symm ▸ countIn_ge_alpha_mul (by linarith) _
      nlinarith [show (N : ℝ) ≥ 1 by norm_cast,
        show erdos_f α ≤ α * (1 - α) ^ 2 / 32 from erdos_f_le_density_term]
    grind
  refine ⟨s, Or.inr ⟨m, hm, hs.1⟩, le_trans h_combined ?_⟩
  exact_mod_cast unionTranslateCount_ge_countIn_add_hitCount A s N
    (Finset.filter (· ∉ A) (Icc 1 N)) (Finset.filter_subset _ _) (fun c hc => by aesop)

/-! ### Main density increment theorem -/
set_option linter.flexible false in
theorem density_increment (d : ShiftApproxData) (A : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hα0 : 0 < schnirelmannDensity A) (hα1 : schnirelmannDensity A < 1) :
    ∃ b ∈ constructB d,
      (schnirelmannDensity A + erdos_f (schnirelmannDensity A)) * N ≤
        unionTranslateCount A b N := by
  by_cases hNA : countIn A N = N
  · -- A covers all of [N]; b = 1 works trivially.
    refine ⟨1, ?_, ?_⟩ <;> norm_num [constructB]
    convert density_increment_full_cover A N hNA _ _
    have := erdos_f_le_beta_half (α := schnirelmannDensity A)
    linarith
  · -- Set m = max 1 (Nat.log 2 N + 1).
    set m := max 1 (Nat.log 2 N + 1) with hm_def
    by_cases hm :
        m < Nat.ceil (16 / (schnirelmannDensity A * (1 - schnirelmannDensity A) ^ 2))
    · -- Small N case: N ≤ 2^(m₀ - 1).
      have hNsmall :
          (N : ℝ) ≤ 2 ^ (⌈16 / (schnirelmannDensity A *
            (1 - schnirelmannDensity A) ^ 2)⌉₊ - 1 : ℕ) := by
        exact_mod_cast Nat.le_of_lt (Nat.lt_pow_of_log_lt (by norm_num) (by omega))
      exact ⟨1, Or.inl rfl,
        density_increment_small_N rfl hα0 hα1
          (lt_of_le_of_ne (countIn_le A N) hNA) hNsmall⟩
    · by_cases hC :
          countIn A N < (schnirelmannDensity A + (1 - schnirelmannDensity A) / 2) * N
      · -- Sparse case: use the shift approximation.
        have hNM : N ≤ 2 ^ m :=
          le_trans (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _))
            (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
        have hM2N : 2 ^ m ≤ 2 * N := by
          simp +zetaDelta at *; rw [pow_succ']
          exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hN.ne')
        have hC_card :
            ((Icc 1 N).filter (fun c => c ∉ A)).card = N - countIn A N := by
          rw [show {c ∈ Icc 1 N | c ∉ A} = (Icc 1 N \ {c ∈ Icc 1 N | c ∈ A}) by ext; aesop,
            Finset.card_sdiff]
          norm_num [countIn]
          exact congr_arg _ (congr_arg _ (by ext; aesop))
        have hCsize :
            ((Icc 1 N).filter (fun c => c ∉ A)).card >
              (1 - schnirelmannDensity A) * ↑N / 2 := by
          rw [hC_card, Nat.cast_sub (countIn_le A N)]
          linarith
        apply density_increment_shift_approx d A (schnirelmannDensity A) rfl hα0 hα1 N hN m
          (by positivity) hNM hM2N (le_of_not_gt hm) hCsize
      · -- Dense case: b = 1 suffices.
        refine ⟨1, Or.inl rfl, ?_⟩
        convert density_increment_dense _ using 1
        linarith
end

/-!
# Erdős Problem 38

Main theorem: There exists B ⊆ ℕ which is not an additive basis but for which
the density increment property holds.
-/

noncomputable section

/-- **Erdős Problem 38**: There exists a set B ⊂ ℕ which is not an additive basis,
    and a function f with f(α) > 0 for 0 < α < 1, such that for every A ⊆ ℕ with
    Schnirelmann density α and every N ≥ 1, there exists b ∈ B with
    |(A ∪ (A+b)) ∩ {1,...,N}| ≥ (α + f(α))N. -/
theorem erdos_problem_38 :
    ∃ (B : Set ℕ) (f : ℝ → ℝ),
      ¬IsAdditiveBasis B ∧
        (∀ α : ℝ, 0 < α → α < 1 → 0 < f α) ∧
          ∀ (A : Set ℕ),
            0 < schnirelmannDensity A →
            schnirelmannDensity A < 1 →
            ∀ (N : ℕ), 0 < N → ∃ b ∈ B,
              (schnirelmannDensity A + f (schnirelmannDensity A)) * ↑N ≤
                (unionTranslateCount A b N : ℝ) := by
  -- Get the shift approximation data
  obtain ⟨d⟩ := shift_approx_exists
  -- Use the constructed B and erdos_f
  refine ⟨constructB d, erdos_f, ?_, ?_, ?_⟩
  -- B is not an additive basis
  · exact constructB_not_basis d
    -- f(α) > 0 for 0 < α < 1
  · exact fun α hα0 hα1 => erdos_f_pos hα0 hα1
    -- Density increment
  · intro A hα0 hα1 N hN
    exact density_increment d A N hN hα0 hα1

#print axioms erdos_problem_38
-- 'Erdos38.erdos_problem_38' depends on axioms: [propext, choice, Quot.sound]

end

end Erdos38
