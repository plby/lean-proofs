/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
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
  -- By convexity of exp, for x ∈ [-1,1]:
  -- exp(t*x) ≤ ((1+x)/2)*exp(t) + ((1-x)/2)*exp(-t).
  have h_convex :
      ∀ i,
        Real.exp (t * f i) ≤
          ((1 + f i) / 2) * Real.exp t + ((1 - f i) / 2) * Real.exp (-t) := by
    -- Apply the convexity of the exponential function to each term in the sum.
    have h_convex :
        ∀ i,
          Real.exp (t * f i) ≤
            ((1 + f i) / 2) * Real.exp t + ((1 - f i) / 2) * Real.exp (-t) := by
      intro i
      have h_convexity : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
        exact convexOn_exp
      convert h_convexity.2 (Set.mem_univ t) (Set.mem_univ (-t)) _ _ _ using 1 <;>
        norm_num <;>
        ring_nf <;>
        nlinarith [abs_le.mp (hf i)]
    assumption
  refine le_trans ( Finset.sum_le_sum fun i _ => h_convex i ) ?_
  norm_num [ Finset.sum_add_distrib, ← Finset.sum_div _ _ _, ← Finset.sum_mul, hf_mean ]
  -- We'll use the fact that $\cosh(t) \leq \exp(t^2 / 2)$ for all $t$.
  have h_cosh : Real.cosh t ≤ Real.exp (t^2 / 2) := by
    exact cosh_le_exp_half_sq t
  rw [ Real.cosh_eq ] at h_cosh
  nlinarith

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
  -- Apply counting_markov with the exponential bound from hoeffding_lemma.
  have h_markov :
      (∑ ω : Fin L → Fin M, Real.exp (ε * (∑ j, f (ω j) - ε * L))) ≤
        M ^ L * Real.exp (-(ε ^ 2 * L / 2)) := by
    -- Apply Hoeffding's lemma to the sum of exponentials.
    have h_sum_exp :
        ∑ ω : Fin L → Fin M, Real.exp (ε * (∑ j, f (ω j))) ≤
          (M * Real.exp (ε ^ 2 / 2)) ^ L := by
      convert pow_le_pow_left₀ ( by positivity ) ( hoeffding_lemma M f hf hf_mean ε ) L using 1
      convert product_sum M L ( fun i => Real.exp ( ε * f i ) ) using 1
      simp +decide only [Finset.mul_sum _ _ _, ← exp_sum]
    convert
      mul_le_mul_of_nonneg_right h_sum_exp (Real.exp_nonneg (-(ε ^ 2 * L)))
      using 1 <;>
      ring_nf
    · rw [ Finset.sum_mul _ _ _ ]
      exact Finset.sum_congr rfl fun _ _ => by rw [ ← Real.exp_add ] ; ring_nf
    · rw [ ← Real.exp_nat_mul ]
      ring_nf
      simpa only [ mul_assoc, ← Real.exp_add ] using by ring_nf
  refine le_trans ?_ h_markov
  rw [ Finset.card_filter ]
  push_cast
  exact Finset.sum_le_sum fun x hx => by
    split_ifs
    · exact Real.one_le_exp (by nlinarith)
    · exact Real.exp_nonneg _

set_option linter.style.refine false in
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
  refine' le_trans _ (add_le_add h_upper h_lower) |> le_trans <| by
    ring_nf
    norm_num
  norm_cast
  rw [ ← Finset.card_union_add_card_inter ]
  exact le_add_right <|
    Finset.card_le_card fun x hx => by
      norm_num at *
      cases abs_cases (∑ j, f (x j)) <;>
        first
        | left; linarith
        | right; linarith

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
set_option linter.style.multiGoal false in
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
  /- ── Step 1: DFT convolution identity ── -/
  -- Express each indicator inner product via orthogonality.
  have h_inner : ∀ s ∈ Icc 1 d, ∀ e ∈ E, ∀ c ∈ C,
      (if s + e = c then 1 else 0 : ℝ) =
        (1 / M : ℝ) * ∑ l ∈ range M, (omegaPrim M) ^ (l * (s + e - c : ℤ)) := by
    intro s hs e he c hc
    split_ifs <;> simp_all +decide [hM.ne']
    · norm_num [show (s : ℤ) + e - c = 0 by linarith, omegaPrim]
      rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hM.ne')]
    · convert root_orthogonality M hM (s + e - c) using 1
      · ac_rfl
      · split_ifs <;> norm_num at *
        exact False.elim <| ‹¬s + e = c› <| by
          obtain ⟨k, hk⟩ := ‹(M : ℤ) ∣ s + e - c›
          nlinarith [show k = 0 by
            nlinarith [Finset.mem_Icc.mp <| hE he,
                       Finset.mem_Icc.mp <| hC hc,
                       Nat.div_mul_le_self M 2]]
  -- Rewrite the LHS as a four-fold sum, then factor.
  have h_expand :
      ∑ s ∈ Icc 1 d, a s * (∑ c ∈ C, ∑ e ∈ E, if s + e = c then 1 else 0) =
        (1 / M : ℝ) * ∑ l ∈ range M,
          ∑ s ∈ Icc 1 d, ∑ e ∈ E, ∑ c ∈ C,
            a s * (omegaPrim M) ^ (l * (s + e - c : ℤ)) := by
    push_cast [Finset.mul_sum _ _ _, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm, Finset.sum_congr rfl, Finset.sum_comm]
    intro s hs
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun e he =>
      Finset.sum_congr rfl fun c hc => by rw [h_inner s hs e he c hc]]
    simp +decide [mul_comm, Finset.mul_sum _ _ _]
    exact Eq.symm (by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring_nf))
  -- Factor the four-fold sum into P(ω^l) · F(l) · conj(G(l)).
  have h_factor :
      ∑ s ∈ Icc 1 d, a s * (∑ c ∈ C, ∑ e ∈ E, if s + e = c then 1 else 0) =
        (1 / M : ℝ) * ∑ l ∈ range M,
          (∑ s ∈ Icc 1 d, a s * (omegaPrim M) ^ (l * s)) *
          (∑ e ∈ E, (omegaPrim M) ^ (l * e)) *
          (∑ c ∈ C, (omegaPrim M) ^ (-l * c : ℤ)) := by
    convert h_expand using 3
    norm_num [Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_left_comm, ← pow_add]
    ring_nf
    norm_num [zpow_add₀ (show omegaPrim M ≠ 0 from Complex.exp_ne_zero _),
              zpow_sub₀ (show omegaPrim M ≠ 0 from Complex.exp_ne_zero _),
              mul_assoc, mul_comm, mul_left_comm,
              Finset.mul_sum _ _ _, Finset.sum_mul]
    rw [Finset.sum_comm]
    norm_cast
    simp +decide [div_eq_mul_inv]
    exact Eq.symm (by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring))
  -- Combine into the standard DFT form (with s·l instead of l·s, and conj instead of neg).
  have h_conv :
      ∑ s ∈ Icc 1 d, a s * (∑ c ∈ C, ∑ e ∈ E, if s + e = c then 1 else 0) =
        (1 / M : ℝ) * ∑ l ∈ range M,
          (∑ s ∈ Icc 1 d, a s * (omegaPrim M) ^ (s * l)) *
          (∑ e ∈ E, (omegaPrim M) ^ (e * l)) *
          (∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))) := by
    convert h_factor using 3
    norm_num [mul_comm]
    norm_num [omegaPrim, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    norm_num [← Complex.exp_nat_mul, ← Complex.exp_neg,
              Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp]
    exact Or.inl <| Finset.sum_congr rfl fun _ _ => by norm_cast
  /- ── Step 2: Triangle inequality + Cauchy–Schwarz bound ── -/
  -- First, bound by max|P| · ∑ ‖F‖ · ‖G‖.
  have h_triangle :
      ‖∑ l ∈ range M,
          (∑ s ∈ Icc 1 d, a s * (omegaPrim M) ^ (s * l)) *
          (∑ e ∈ E, (omegaPrim M) ^ (e * l)) *
          (∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l)))‖ ≤
        maxPolyOnGrid a d M hM *
          (∑ l ∈ range M,
            ‖∑ e ∈ E, (omegaPrim M) ^ (e * l)‖ *
            ‖∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum _ _ _]
    refine Finset.sum_le_sum fun i hi => ?_
    simp +decide [mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_sup' (fun l => ‖∑ s ∈ Icc 1 d, (a s : ℂ) * omegaPrim M ^ (s * l)‖) hi)
      (by positivity)
  -- Then, apply Cauchy–Schwarz to the sum ∑ ‖F‖ · ‖G‖.
  have h_cauchy_schwarz :
      ∑ l ∈ range M,
        ‖∑ e ∈ E, (omegaPrim M) ^ (e * l)‖ *
        ‖∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))‖ ≤
      Real.sqrt (∑ l ∈ range M, ‖∑ e ∈ E, (omegaPrim M) ^ (e * l)‖ ^ 2) *
      Real.sqrt (∑ l ∈ range M,
        ‖∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  -- Combine and factor out 1/M.
  have h_bound :
      ‖(1 / M : ℝ) * ∑ l ∈ range M,
          (∑ s ∈ Icc 1 d, a s * (omegaPrim M) ^ (s * l)) *
          (∑ e ∈ E, (omegaPrim M) ^ (e * l)) *
          (∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l)))‖ ≤
        maxPolyOnGrid a d M hM *
          Real.sqrt (∑ l ∈ range M, ‖∑ e ∈ E, (omegaPrim M) ^ (e * l)‖ ^ 2 / M) *
          Real.sqrt (∑ l ∈ range M,
            ‖∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))‖ ^ 2 / M) := by
    simp_all +decide [← Finset.sum_div _ _ _, mul_assoc]
    convert mul_le_mul_of_nonneg_left
      (h_triangle.trans (mul_le_mul_of_nonneg_left h_cauchy_schwarz <|
        show 0 ≤ maxPolyOnGrid a d M hM from
          Finset.le_sup' (fun l => ‖∑ s ∈ Icc 1 d, (a s : ℂ) * omegaPrim M ^ (s * l)‖)
            (Finset.mem_range.mpr hM) |> le_trans (by positivity)))
      (by positivity : 0 ≤ (M : ℝ)⁻¹) using 1
    ring_nf
    norm_num [hM.ne']
    ring
  /- ── Step 3: Apply Parseval to simplify √-terms ── -/
  have h_parseval_E :
      ∑ l ∈ range M, ‖∑ e ∈ E, (omegaPrim M) ^ (e * l)‖ ^ 2 / M = E.card := by
    rw [← Finset.sum_div, indicator_parseval M N hM hMN E hE,
      mul_div_cancel_left₀ _ (ne_of_gt (Nat.cast_pos.mpr hM))]
  have h_parseval_C :
      ∑ l ∈ range M,
        ‖∑ c ∈ C, (starRingEnd ℂ) ((omegaPrim M) ^ (c * l))‖ ^ 2 / M = C.card := by
    rw [← Finset.sum_div, div_eq_iff (by positivity)]
    convert indicator_parseval M N hM hMN C hC using 1
    · norm_num [Complex.normSq, Complex.sq_norm]
      norm_num [← map_pow, Complex.exp_re, Complex.exp_im]
    · ring
  /- ── Conclusion ── -/
  convert h_bound using 1
  · rw [← h_conv]
    unfold shiftBilinForm
    norm_cast
    congr! 3
    simp +decide [eq_comm]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    split_ifs <;> simp_all +decide
    · rw [Finset.card_eq_one.mpr]
      aesop
      exact ⟨x - _, Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨by tauto,
          by rw [Nat.add_sub_of_le (by linarith)]⟩,
         fun y hy => by rw [Finset.mem_filter] at hy; omega⟩⟩
    · norm_cast
      symm
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      rw [Finset.mem_filter] at hy
      simp_all only [lt_add_iff_pos_right, add_tsub_cancel_left, not_true_eq_false, imp_false,
        not_lt, nonpos_iff_eq_zero, add_zero]
      have := Finset.mem_of_subset hE hy.1
      simp at this
  · rw [h_parseval_E, h_parseval_C]

end

/-!
# Probabilistic Method for Shift Construction

We prove that for m ≥ 20, there exists a small set S ⊆ Icc 1 (2^m) satisfying both
the approximation property and a minimum element bound, using the probabilistic method.
-/

noncomputable section

/-! ## Part 1: Von Neumann Bridge -/

set_option linter.flexible false in
set_option linter.style.multiGoal false in
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
  have h_shift :
      |∑ s ∈ Icc 1 (2 ^ m),
        ((if s ∈ Icc 1 (2 ^ m) then
            (univ.filter (fun j => ω j = s)).card / L - 1 / 2 ^ m
          else 0) : ℝ) * hitCount (E : Set ℕ) C s| ≤
        (1 / m : ℝ) * Real.sqrt (E.card * C.card) := by
    have :=
      von_neumann_indicator (2 ^ (m + 1)) N (2 ^ m)
        (by positivity) (by ring_nf; linarith) (by ring_nf; norm_num)
        (fun s =>
          if s ∈ Icc 1 (2 ^ m) then
            (Finset.card (Finset.filter (fun j => ω j = s) Finset.univ) : ℝ) / L -
              1 / 2 ^ m
          else 0)
        E C hE hC
    convert
      this.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h_poly <| Real.sqrt_nonneg _)
          <| Real.sqrt_nonneg _)
      using 1
    norm_num [ shiftBilinForm ]
    · unfold hitCount
      aesop
    · rw [ Real.sqrt_mul ( Nat.cast_nonneg _ ), mul_assoc ]
  have h_sum :
      ∑ s ∈ Icc 1 (2 ^ m),
          ((if s ∈ Icc 1 (2 ^ m) then
              (univ.filter (fun j => ω j = s)).card / L - 1 / 2 ^ m
            else 0) : ℝ) * hitCount (E : Set ℕ) C s =
        (1 / L : ℝ) * ∑ j, hitCount (E : Set ℕ) C (ω j) -
          (∑ t ∈ Icc 1 (2 ^ m), hitCount (E : Set ℕ) C t) / 2 ^ m := by
    have h_split :
        ∑ s ∈ Icc 1 (2 ^ m),
            ((if s ∈ Icc 1 (2 ^ m) then
                (univ.filter (fun j => ω j = s)).card / L
              else 0) : ℝ) * hitCount (E : Set ℕ) C s =
          (1 / L : ℝ) * ∑ j, hitCount (E : Set ℕ) C (ω j) := by
      have h_split :
          ∑ s ∈ Icc 1 (2 ^ m),
              ((univ.filter (fun j => ω j = s)).card : ℝ) *
                hitCount (E : Set ℕ) C s =
            ∑ j, hitCount (E : Set ℕ) C (ω j) := by
        push_cast [ Finset.card_filter ]
        simp +decide only [Finset.sum_mul _ _ _]
        rw [ Finset.sum_comm ]
        aesop
      rw [ ← h_split, Finset.mul_sum _ _ _ ]
      exact Finset.sum_congr rfl fun x hx => by
        rw [ if_pos hx ]
        ring
    simp_all +decide [ sub_mul ]
    rw [ Finset.sum_div _ _ _ ]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h_pigeonhole :
      ∃ j : Fin L,
        (hitCount (E : Set ℕ) C (ω j) : ℝ) ≥
          (∑ j : Fin L, hitCount (E : Set ℕ) C (ω j)) / L := by
    have :=
      Finset.exists_max_image Finset.univ
        (fun j => hitCount (E : Set ℕ) C (ω j))
        ⟨⟨0, hL⟩, Finset.mem_univ _⟩
    obtain ⟨ j, hj₁, hj₂ ⟩ := this
    exact ⟨ j, by
      rw [ ge_iff_le, div_le_iff₀ (by positivity) ]
      exact mod_cast by
        simpa [ mul_comm ] using
          Finset.sum_le_sum fun i (hi : i ∈ Finset.univ) => hj₂ i hi ⟩
  obtain ⟨ j, hj ⟩ := h_pigeonhole
  use j
  norm_num at *
  ring_nf at *
  linarith [ abs_le.mp h_shift ]

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
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
/-- Count of tuples with a small element is less than half the total. -/
lemma bad_min_count_lt (m : ℕ) (_hm : 20 ≤ m) :
    2 * (univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
      ∃ j, ¬(2 ^ m < ((ω j : ℕ) + 1) * (2 * shiftL m + 2)))).card <
    Fintype.card (Fin (shiftL m) → Fin (2 ^ m)) := by
  -- For each $j$, the number of bad values $t \in \text{Fin } M$ with
  -- $(t : ℕ) < M / (2L + 2)$ is $\leq M / (2L + 2)$.
  have h_bad_count :
      ∀ j : Fin (shiftL m),
        (Finset.univ.filter (fun t : Fin (2 ^ m) =>
          (t : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card ≤
        2 ^ m / (2 * shiftL m + 2) := by
    intro j
    rw [ Finset.card_eq_of_bijective ]
    use fun i hi => ⟨ i, by linarith [ Nat.div_le_self ( 2 ^ m ) ( 2 * shiftL m + 2 ) ] ⟩
    · aesop
    · aesop
    · aesop
  -- By union bound, the number of bad tuples is at most the sum of the
  -- number of bad values for each $j$.
  have h_union_bound :
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ∃ j, (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card ≤
      shiftL m * (2 ^ m / (2 * shiftL m + 2)) *
        (2 ^ m) ^ (shiftL m - 1) := by
    have h_union_bound :
        (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
          ∃ j, (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card ≤
        ∑ j : Fin (shiftL m),
          (Finset.univ.filter (fun t : Fin (2 ^ m) =>
            (t : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card *
            (2 ^ m) ^ (shiftL m - 1) := by
      have h_union_bound :
          ∀ j : Fin (shiftL m),
            (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
              (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card ≤
            (Finset.univ.filter (fun t : Fin (2 ^ m) =>
              (t : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card *
              (2 ^ m) ^ (shiftL m - 1) := by
        intro j
        have h_card_filter_j :
            (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
              (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card ≤
            (Finset.univ.filter (fun t : Fin (2 ^ m) =>
              (t : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2))).card *
              (2 ^ m) ^ (shiftL m - 1) := by
          have h_card_filter_j :
              Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
                  (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2)) ⊆
                Finset.image
                  (fun (p : Fin (2 ^ m) × (Fin (shiftL m - 1) → Fin (2 ^ m))) =>
                    Fin.insertNth j p.1 p.2)
                  (Finset.univ.filter (fun t : Fin (2 ^ m) =>
                    (t : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2)) ×ˢ
                    Finset.univ) := by
            intro ω hω
            simp_all +decide
            refine' ⟨ ω j, hω, Fin.removeNth j ω, _ ⟩
            grind +suggestions
          refine le_trans ( Finset.card_le_card h_card_filter_j ) ?_
          refine' Finset.card_image_le.trans _
          norm_num [ Finset.card_univ ]
        convert h_card_filter_j using 1
      refine' le_trans _ ( Finset.sum_le_sum fun j _ => h_union_bound j )
      rw [
        show
          (Finset.univ.filter fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
            ∃ j : Fin (shiftL m),
              (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2)) =
            Finset.biUnion Finset.univ fun j =>
              Finset.univ.filter fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
                (ω j : ℕ) + 1 ≤ 2 ^ m / (2 * shiftL m + 2) by
          ext
          aesop]
      exact Finset.card_biUnion_le
    refine le_trans h_union_bound ?_
    rw [ ← Finset.sum_mul _ _ _ ]
    gcongr
    convert Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_bad_count i
    norm_num
  -- Simplify the right-hand side of the inequality.
  have h_simplify :
      2 * shiftL m * (2 ^ m / (2 * shiftL m + 2)) *
          (2 ^ m) ^ (shiftL m - 1) <
        (2 ^ m) ^ shiftL m := by
    have h_simplify :
        2 * shiftL m * (2 ^ m / (2 * shiftL m + 2)) < 2 ^ m := by
      nlinarith [
        Nat.div_mul_le_self (2 ^ m) (2 * shiftL m + 2),
        Nat.one_le_pow m 2 zero_lt_two,
        show shiftL m > 0 from by
          unfold shiftL
          positivity]
    convert
      mul_lt_mul_of_pos_right h_simplify
        (pow_pos (pow_pos (zero_lt_two' ℕ) m) (shiftL m - 1))
      using 1
    rw [ ← pow_succ', Nat.sub_add_cancel ( show 1 ≤ shiftL m from Nat.succ_pos _ ) ]
  convert lt_of_le_of_lt ( Nat.mul_le_mul_left 2 h_union_bound ) _ using 1
  · norm_num [ Nat.le_div_iff_mul_le ( by positivity : 0 < ( 2 * shiftL m + 2 ) ) ]
  · convert h_simplify using 1
    ring
    norm_num [ Fintype.card_pi ]

set_option maxHeartbeats 800000 in
-- The Hoeffding/DFT union-bound proof times out at the default heartbeat limit.
set_option linter.flexible false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
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
  -- ── Step 1. Hoeffding bound for the real part of each Fourier coefficient ──
  have h_reduction :
      ∀ l ∈ Finset.range (2 ^ (m + 1)), ∀ component ∈ [0, 1],
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        |∑ s ∈ Finset.Icc 1 (2 ^ m),
          (if s ∈ Finset.Icc 1 (2 ^ m)
           then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                   (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
           else 0) *
          (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re| >
        1 / (2 * m))).card ≤
      2 * (2 ^ m) ^ shiftL m *
        Real.exp (-(shiftL m) / (32 * m ^ 2)) := by
    intros l hl component hcomponent
    -- Rewrite the sum as |∑_j g(ω_j)| · (2 / L) for a centered function g.
    have h_centered :
        ∀ ω : Fin (shiftL m) → Fin (2 ^ m),
        |∑ s ∈ Finset.Icc 1 (2 ^ m),
          (if s ∈ Finset.Icc 1 (2 ^ m)
           then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                   (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
           else 0) *
          (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re| =
        |(∑ j : Fin (shiftL m),
          (fun t : Fin (2 ^ m) =>
            ((omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re -
             (∑ t : Fin (2 ^ m),
               (omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re) /
             2 ^ m) / 2)
          (ω j))| *
        (2 / shiftL m) := by
      intro ω
      have h_centered :
          ∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re =
          (2 / shiftL m) *
          (∑ j : Fin (shiftL m),
            (fun t : Fin (2 ^ m) =>
              ((omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re -
               (∑ t : Fin (2 ^ m),
                 (omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re) /
               2 ^ m) / 2)
            (ω j)) := by
        -- Decompose into (1/L)·∑_j ω(j+1)^l·re − (1/2^m)·∑_s ω(s)^l·re.
        have h_centered :
            ∑ s ∈ Finset.Icc 1 (2 ^ m),
              (if s ∈ Finset.Icc 1 (2 ^ m)
               then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                       (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
               else 0) *
              (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re =
            (1 / shiftL m) *
              (∑ j : Fin (shiftL m),
                (omegaPrim (2 ^ (m + 1)) ^ (((ω j : ℕ) + 1) * l) : ℂ).re) -
            (1 / 2 ^ m) *
              (∑ s ∈ Finset.Icc 1 (2 ^ m),
                (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re) := by
          simp +decide [Finset.sum_ite, Finset.mul_sum _ _ _, div_eq_inv_mul]
          rw [show (Finset.filter (fun x => 1 ≤ x ∧ x ≤ 2 ^ m)
                (Finset.Icc 1 (2 ^ m))) = Finset.Icc 1 (2 ^ m)
              from Finset.filter_true_of_mem fun x hx =>
                Finset.mem_Icc.mp hx]
          simp +decide [sub_mul, Finset.sum_sub_distrib]
          rw [← Finset.sum_subset
            (show Finset.image (fun j : Fin (shiftL m) =>
                  (ω j : ℕ) + 1) Finset.univ ⊆ Finset.Icc 1 (2 ^ m)
              from Finset.image_subset_iff.mpr fun j _ =>
                Finset.mem_Icc.mpr ⟨Nat.succ_pos _,
                  Nat.succ_le_of_lt <| Fin.is_lt _⟩)]
          · rw [Finset.sum_image']
            simp +decide [mul_comm]
            intro i
            rw [Finset.sum_congr rfl fun x hx => by
              rw [show (ω x : ℕ) = ω i
                from Finset.mem_filter.mp hx |>.2]]
            simp +decide [mul_assoc, mul_comm, mul_left_comm]
          · aesop
        -- Reindex the Icc sum as a sum over Fin (2^m).
        have h_sum_eq :
            ∑ s ∈ Finset.Icc 1 (2 ^ m),
              (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re =
            ∑ t : Fin (2 ^ m),
              (omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re := by
          erw [Finset.sum_Ico_eq_sub _ _] <;>
            norm_num [Finset.sum_range, Fin.sum_univ_succ]
        simp_all +decide [Finset.sum_div _ _ _]
        norm_num [← Finset.sum_div _ _ _, ← Finset.sum_mul] ; ring_nf
        rw [mul_inv_cancel₀
          (by
            norm_cast
            exact Nat.ne_of_gt (show 0 < shiftL m from Nat.succ_pos _))]
        ring_nf
      rw [h_centered, abs_mul, abs_of_nonneg (by positivity)] ; ring
    -- Apply Hoeffding's inequality for bounded, zero-mean sums.
    have h_hoeffding :
        ∀ (f : Fin (2 ^ m) → ℝ),
          (∀ t, |f t| ≤ 1) → (∑ t : Fin (2 ^ m), f t = 0) →
          (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
            |∑ j : Fin (shiftL m), f (ω j)| >
            (shiftL m : ℝ) / (4 * m))).card ≤
          2 * (2 ^ m) ^ shiftL m *
            Real.exp (-(shiftL m : ℝ) / (32 * m ^ 2)) := by
      intros f hf_bound hf_sum_zero
      have h_hoeffding :
          (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
            |∑ j : Fin (shiftL m), f (ω j)| ≥
            (shiftL m : ℝ) / (4 * m))).card ≤
          2 * (2 ^ m) ^ shiftL m *
            Real.exp (-(shiftL m : ℝ) / (32 * m ^ 2)) := by
        convert hoeffding_two_sided (2 ^ m) (shiftL m) (by positivity)
            f hf_bound hf_sum_zero (1 / (4 * m)) (by positivity)
          using 1 ; norm_num ; ring_nf
        norm_num ; ring
      refine le_trans ?_ h_hoeffding
      exact_mod_cast Finset.card_mono fun x hx =>
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, le_of_lt <| Finset.mem_filter.mp hx |>.2⟩
    -- Instantiate Hoeffding with the centered cosine function.
    convert h_hoeffding _ _ _ using 3
    rotate_left
    use fun t =>
      ((omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re -
       (∑ t : Fin (2 ^ m),
         (omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re) /
       2 ^ m) / 2
    · -- Bound |g(t)| ≤ 1
      intro t
      have h_bound :
          ∀ t : Fin (2 ^ m),
            |(omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ).re| ≤ 1 := by
        intro t
        exact (by
          have h_bound :
              ∀ t : Fin (2 ^ m),
                ‖(omegaPrim (2 ^ (m + 1)) ^ (((t : ℕ) + 1) * l) : ℂ)‖ ≤ 1 := by
            norm_num [omegaPrim] ; norm_num [Complex.norm_exp]
            norm_num [div_eq_mul_inv, Complex.exp_re] ; norm_cast ; norm_num
          exact le_trans (Complex.abs_re_le_norm _) (h_bound t))
      rw [abs_le]
      have h_re_sum_bound :
          |∑ t : Fin (2 ^ m),
            (omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).re| ≤ 2 ^ m :=
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (le_trans (Finset.sum_le_sum fun _ _ => h_bound _) (by norm_num))
      have h_avg_le :
          (∑ t : Fin (2 ^ m),
            (omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).re) / 2 ^ m ≤ 1 :=
        div_le_one_of_le₀
          (le_trans (Finset.sum_le_sum fun _ _ => le_of_abs_le (h_bound _))
            (by norm_num))
          (by positivity)
      have h_avg_ge :
          (∑ t : Fin (2 ^ m),
            (omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).re) / 2 ^ m ≥ -1 :=
        le_div_iff₀ (by positivity) |>.2
          (by linarith [show (∑ t : Fin (2 ^ m),
                (omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).re) ≥
                  -(2 ^ m : ℝ)
              from le_trans (by norm_num)
                (Finset.sum_le_sum fun _ _ =>
                  neg_le_of_abs_le (h_bound _))])
      constructor <;>
        linarith [abs_le.mp (h_bound t), abs_le.mp h_re_sum_bound,
          h_avg_le, h_avg_ge]
    · -- Zero mean
      norm_num [← Finset.sum_div _ _ _]
    · -- The filtered sets agree (extensionality)
      ext ω
      simp
      simp +zetaDelta at *
      rw [h_centered ω]
      ring_nf
      field_simp
      rw [lt_div_iff₀] <;> norm_cast ; ring_nf
      · norm_num [add_comm, mul_comm]
      · exact Nat.succ_pos _
  -- ── Step 2. Hoeffding bound for the imaginary part ──
  have h_reduction_im :
      ∀ l ∈ Finset.range (2 ^ (m + 1)), ∀ component ∈ [0, 1],
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        |∑ s ∈ Finset.Icc 1 (2 ^ m),
          (if s ∈ Finset.Icc 1 (2 ^ m)
           then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                   (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
           else 0) *
          (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).im| >
        1 / (2 * m))).card ≤
      2 * (2 ^ m) ^ shiftL m *
        Real.exp (-(shiftL m) / (32 * m ^ 2)) := by
    intros l hl component hcomponent
    -- Package the centered sine function g and verify its properties.
    have h_centered :
        ∃ g : Fin (2 ^ m) → ℝ,
          (∀ t, |g t| ≤ 1) ∧ (∑ t, g t = 0) ∧
          ∀ ω : Fin (shiftL m) → Fin (2 ^ m),
            (∑ s ∈ Finset.Icc 1 (2 ^ m),
              (if s ∈ Finset.Icc 1 (2 ^ m)
               then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                       (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
               else 0) *
              (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).im) =
            (2 / shiftL m) * (∑ j : Fin (shiftL m), g (ω j)) := by
      refine ⟨fun t =>
        ((omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).im -
         (∑ t : Fin (2 ^ m),
           (omegaPrim (2 ^ (m + 1)) ^ ((t + 1) * l) : ℂ).im) / 2 ^ m) / 2,
        ?_, ?_, ?_⟩ <;>
        norm_num [Finset.sum_div _ _ _]
      · -- Bound |g(t)| ≤ 1
        intro t
        have h_im_bound :
            |(omegaPrim (2 ^ (m + 1)) ^ ((t.val + 1) * l) : ℂ).im| ≤ 1 := by
          have h_im_bound : ∀ z : ℂ, ‖z‖ = 1 → |z.im| ≤ 1 :=
            fun z hz => hz ▸ Complex.abs_im_le_norm z
          apply h_im_bound
          norm_num [omegaPrim] ; norm_num [Complex.norm_exp]
          norm_num [div_eq_mul_inv, Complex.exp_re] ; norm_cast ; norm_num
        have h_sum_im_bound :
            |∑ i : Fin (2 ^ m),
              (omegaPrim (2 ^ (m + 1)) ^ ((i.val + 1) * l) : ℂ).im /
              2 ^ m| ≤ 1 := by
          have h_sum_im_bound :
              |∑ i : Fin (2 ^ m),
                (omegaPrim (2 ^ (m + 1)) ^ ((i.val + 1) * l) : ℂ).im| ≤
              2 ^ m := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine le_trans (Finset.sum_le_sum fun _ _ =>
                show |_| ≤ 1 from ?_) ?_ <;> norm_num
            unfold omegaPrim
            norm_num [← Complex.exp_nat_mul, Complex.exp_im]
            norm_num [div_eq_mul_inv, Complex.normSq,
              Complex.exp_re, Complex.exp_im]
            norm_cast ; norm_num
            exact Real.abs_sin_le_one _
          rw [← Finset.sum_div _ _ _, abs_div,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ m)]
          exact div_le_one_of_le₀ h_sum_im_bound (by positivity)
        exact abs_le.mpr
          ⟨by linarith [abs_le.mp h_im_bound, abs_le.mp h_sum_im_bound],
           by linarith [abs_le.mp h_im_bound, abs_le.mp h_sum_im_bound]⟩
      · -- Zero mean
        norm_num [← Finset.sum_div _ _ _, ← Finset.sum_mul]
      · -- Sum identity for each ω
        intro ω
        rw [Finset.sum_congr rfl fun x hx =>
          if_pos ⟨Finset.mem_Icc.mp hx |>.1, Finset.mem_Icc.mp hx |>.2⟩]
        simp +decide [Finset.mul_sum _ _ _, Finset.sum_mul _ _ _,
          div_eq_mul_inv, mul_assoc, mul_left_comm,
          Finset.sum_sub_distrib, sub_mul, mul_sub]
        congr! 1
        · rw [← Finset.sum_subset
            (show Finset.image (fun x : Fin (shiftL m) =>
                  (ω x : ℕ) + 1) Finset.univ ⊆ Finset.Icc 1 (2 ^ m)
              from ?_)]
          · rw [Finset.sum_image']
            simp +decide [mul_comm]
            intro i
            rw [Finset.sum_congr rfl fun x hx => by
              rw [show (ω x : ℕ) = ω i
                from Finset.mem_filter.mp hx |>.2]]
            simp +decide
            ring
          · simp +contextual
          · exact Finset.image_subset_iff.mpr fun x _ =>
              Finset.mem_Icc.mpr ⟨Nat.succ_pos _,
                Nat.succ_le_of_lt <| Fin.is_lt _⟩
        · erw [Finset.sum_Ico_eq_sum_range]
          norm_num [mul_comm, Finset.sum_range, shiftL]
          exact Finset.sum_congr rfl fun _ _ => by
            rw [mul_left_comm, mul_inv_cancel₀ (by positivity), mul_one]
            ring_nf
    -- Apply Hoeffding to the centered sine function.
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := h_centered
    have := hoeffding_two_sided (2 ^ m) (shiftL m) (by positivity)
      g hg₁ hg₂ (1 / (4 * m)) (by positivity)
    simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    refine le_trans ?_ (this.trans ?_) <;> ring_nf <;> norm_num
    refine Finset.card_mono ?_
    intro ω hω ; norm_num at *
    nlinarith [
      inv_pos.mpr (show 0 < (m : ℝ) by positivity),
      inv_pos.mpr (show 0 < (shiftL m : ℝ)
        from Nat.cast_pos.mpr (Nat.succ_pos _)),
      mul_inv_cancel₀ (show (m : ℝ) ≠ 0 by positivity),
      mul_inv_cancel₀ (show (shiftL m : ℝ) ≠ 0
        from Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))]
  -- ── Step 3. Union bound over all frequencies ──
  have h_union_bound :
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ∃ l ∈ Finset.range (2 ^ (m + 1)),
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re| > 1 / (2 * m) ∨
        ∃ l ∈ Finset.range (2 ^ (m + 1)),
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).im| >
          1 / (2 * m))).card ≤
      2 * (2 ^ (m + 1)) * 2 * (2 ^ m) ^ shiftL m *
        Real.exp (-(shiftL m) / (32 * m ^ 2)) := by
    refine' le_trans (Nat.cast_le.mpr <| Finset.card_le_card _) _
    -- Embed into the union of per-frequency bad sets (real ∪ imaginary).
    exact
      Finset.biUnion (Finset.range (2 ^ (m + 1))) (fun l =>
        Finset.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then (Finset.card (Finset.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s) Finset.univ) : ℝ) / shiftL m -
                   1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) |> Complex.re)| >
          1 / (2 * m)) Finset.univ) ∪
      Finset.biUnion (Finset.range (2 ^ (m + 1))) (fun l =>
        Finset.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then (Finset.card (Finset.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s) Finset.univ) : ℝ) / shiftL m -
                   1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) |> Complex.im)| >
          1 / (2 * m)) Finset.univ)
    · grind
    · -- Bound the union cardinality by summing individual bounds.
      refine le_trans (Nat.cast_le.mpr <| Finset.card_union_le _ _) ?_
      refine le_trans (Nat.cast_le.mpr <|
        add_le_add Finset.card_biUnion_le Finset.card_biUnion_le) ?_
      push_cast [← Finset.sum_add_distrib]
      refine le_trans (Finset.sum_le_sum fun x hx =>
        add_le_add (h_reduction x hx 0 (by norm_num))
          (h_reduction_im x hx 1 (by norm_num))) ?_
      norm_num
      ring_nf
      norm_num
  -- ── Step 4. The union bound is less than half the total ──
  have h_simplified :
      2 * (2 ^ (m + 1)) * 2 * (2 ^ m) ^ shiftL m *
        Real.exp (-(shiftL m) / (32 * m ^ 2)) <
      (2 ^ m) ^ shiftL m / 2 := by
    -- Cancel the common factor (2^m)^L from both sides.
    suffices h_cancel :
        8 * 2 ^ m * Real.exp (-(shiftL m) / (32 * m ^ 2)) < 1 / 2 by
      convert mul_lt_mul_of_pos_right h_cancel
        (show 0 < (2 ^ m : ℝ) ^ shiftL m by positivity) using 1 <;> ring
    -- Key estimate: e^{-4m} < 1/(16·2^m) for m ≥ 20.
    have h_exp_bound₁ : Real.exp (-4 * m) < 1 / (16 * 2 ^ m) := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
      ring_nf ; norm_num
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_le_sub_one_of_pos zero_lt_two,
        (by norm_cast : (20 : ℝ) ≤ m)]
    -- The exponent -(shiftL m)/(32m²) is at most -4m.
    have h_exp_bound₂ :
        Real.exp (-(shiftL m) / (32 * m ^ 2)) < Real.exp (-4 * m) := by
      norm_num [shiftL]
      rw [div_lt_iff₀] <;>
        nlinarith only [show (m : ℝ) ≥ 20 by norm_cast]
    rw [lt_div_iff₀] at * <;>
      first | positivity | nlinarith [pow_pos (zero_lt_two' ℝ) m]
  -- ── Step 5. Connect maxPolyOnGrid to the Fourier conditions ──
  have h_final :
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ¬maxPolyOnGrid
          (fun s => if s ∈ Finset.Icc 1 (2 ^ m)
           then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                   (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
           else 0)
          (2 ^ m) (2 ^ (m + 1)) (by positivity) ≤ 1 / (m : ℝ))).card ≤
      (Finset.univ.filter (fun ω : Fin (shiftL m) → Fin (2 ^ m) =>
        ∃ l ∈ Finset.range (2 ^ (m + 1)),
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).re| > 1 / (2 * m) ∨
        ∃ l ∈ Finset.range (2 ^ (m + 1)),
          |∑ s ∈ Finset.Icc 1 (2 ^ m),
            (if s ∈ Finset.Icc 1 (2 ^ m)
             then ((Finset.univ.filter (fun j : Fin (shiftL m) =>
                     (ω j : ℕ) + 1 = s)).card : ℝ) / shiftL m - 1 / 2 ^ m
             else 0) *
            (omegaPrim (2 ^ (m + 1)) ^ (s * l) : ℂ).im| >
          1 / (2 * m))).card := by
    refine Finset.card_mono ?_
    intro ω hω
    contrapose! hω
    simp +zetaDelta at *
    refine' le_trans (max_poly_le_from_re_im _ _ _ _ _ _ _ _) _
    exact (m : ℝ)⁻¹ * 2⁻¹
    · positivity
    · intro l hl
      specialize hω l (Finset.mem_range.mp hl)
      simp_all +decide [Finset.sum_ite]
    · intro l hl
      specialize hω l (Finset.mem_range.mp hl)
      aesop
    · ring_nf
      norm_num
  -- ── Conclusion: combine all bounds ──
  norm_num [Fintype.card_pi] at *
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 h_final)
    (by rw [← @Nat.cast_lt ℝ] ; push_cast; linarith)

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

set_option linter.style.refine false in
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
  refine' ⟨ m, by linarith, shiftL m, _, fun j => ( ω j : ℕ ) + 1, _, N, hN.1, _, _ ⟩ <;> norm_num
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

set_option linter.style.refine false in
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
  intro h
  have h_log_div_N_zero :
      ∀ k : ℕ,
        Filter.Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) ^ k) / N)
          Filter.atTop (nhds 0) := by
    intro k
    suffices h_log :
        Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ k / 2 ^ x) Filter.atTop (nhds 0) by
      have h_log :
          Filter.Tendsto
            (fun N : ℕ => (Nat.log 2 N : ℝ) ^ k / 2 ^ (Nat.log 2 N))
            Filter.atTop (nhds 0) := by
        exact h_log.comp <|
          Filter.tendsto_atTop_atTop.mpr fun x =>
            ⟨2 ^ x, fun n hn => Nat.le_log_of_pow_le (by norm_num) hn⟩
      refine' squeeze_zero_norm' _ h_log
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by
        rw [ Real.norm_of_nonneg (by positivity) ]
        gcongr
        norm_cast
        exact Nat.pow_log_le_self 2 hn.ne'
    suffices h_log :
        Filter.Tendsto (fun y : ℝ => (y / Real.log 2) ^ k / Real.exp y)
          Filter.atTop (nhds 0) by
      convert
        h_log.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
        using 2
      norm_num [ Real.exp_nat_mul, Real.exp_log ]
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    convert this.div_const (Real.log 2 ^ k) using 2 <;>
      norm_num [ Real.exp_neg, div_eq_mul_inv, mul_pow, mul_assoc, mul_comm,
        mul_left_comm ]
  have h_poly_div_N :
      ∃ P : Polynomial ℝ,
        ∀ N : ℕ,
          N ≥ 1 →
            ((Finset.filter (fun n => ∃ m, 0 < m ∧ n ∈ shifts m)
              (Finset.Icc 1 N)).card : ℝ) ^ h / N ≤
              P.eval (Nat.log 2 N : ℝ) / N := by
    use (Polynomial.C C₀ + Polynomial.C C₁ * (Polynomial.X + 2) ^ 4) ^ h
    intro N hN
    gcongr
    simpa using pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( hbound N ) h
  obtain ⟨ P, hP ⟩ := h_poly_div_N
  have h_poly_div_N_zero :
      Filter.Tendsto (fun N : ℕ => P.eval (Nat.log 2 N : ℝ) / N)
        Filter.atTop (nhds 0) := by
    simp_all +decide [ Polynomial.eval_eq_sum_range ]
    simpa [ Finset.sum_div _ _ _, mul_div_assoc ] using
      tendsto_finset_sum _ fun i hi =>
        Filter.Tendsto.const_mul ( P.coeff i ) ( h_log_div_N_zero i )
  exact squeeze_zero_norm'
    (Filter.eventually_atTop.mpr ⟨ 1, fun N hN => by
      rw [ Real.norm_of_nonneg (by positivity) ]
      exact hP N hN ⟩)
    h_poly_div_N_zero

/-! ## Count bound from min-bound property -/

set_option maxHeartbeats 800000 in
-- The final polynomial-logarithmic estimate times out at the default heartbeat limit.
set_option linter.style.induction false in
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
          induction' hm with m ih
          · have h_contradiction :
                2 ^ (4 * Nat.log 2 N + 69) ≥
                  2 ^ (Nat.log 2 N + 1) *
                    (256 * (4 * Nat.log 2 N + 69) ^ 3 + 4) := by
              induction' Nat.log 2 N with k ih <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] at *
              nlinarith [
                pow_pos ( zero_lt_two' ℕ ) k,
                pow_nonneg ( Nat.zero_le k ) 2,
                pow_nonneg ( Nat.zero_le k ) 3 ]
            exact
              le_trans
                (Nat.mul_le_mul_right _
                  (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)))
                h_contradiction
          · norm_num [ pow_succ' ] at *
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
set_option linter.style.induction false in
set_option linter.style.refine false in
/-- If |B ∩ [1,N]|^h / N → 0 for every h, then B is not an additive basis. -/
lemma not_basis_of_sparse {B : Set ℕ}
    (hsparse : ∀ h : ℕ, Tendsto (fun N => (countIn B N : ℝ) ^ h / N) atTop (nhds 0)) :
    ¬IsAdditiveBasis B := by
  intro hB
  obtain ⟨h, h_basis⟩ := hB
  have h_sums : ∀ᶠ N in Filter.atTop, countIn (hSumset h B) N ≥ N / 2 := by
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, n ∈ hSumset h B := by
      aesop
    refine' Filter.eventually_atTop.mpr ⟨ 2 * N₀ + 2, fun N hN => _ ⟩
    refine' le_trans _ (Finset.card_mono <| show
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
            induction' h with h ih generalizing n <;> simp_all +decide [ hSumset ]
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
        exact (by refine' Finset.card_le_card _ ; grind)
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
          refine' le_of_eq _
          refine' Finset.card_bij (fun f hf => fun i _ => f i) _ _ _ <;>
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
    refine' squeeze_zero_norm' _ h_contradiction
    filter_upwards [
      ‹∀ᶠ N in atTop,
        (countIn B N + 1 : ℝ) ^ h ≤ 2 ^ h * (countIn B N ^ h + 1)›
    ] with N hN using by
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
  have h_contradiction :
      Filter.Tendsto (fun N => (countIn (hSumset h B) N : ℝ) / N)
        Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ h_contradiction
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
set_option linter.style.refine false in
/-- The constructed B is not an additive basis. -/
theorem constructB_not_basis (d : ShiftApproxData) : ¬IsAdditiveBasis (constructB d) := by
  -- To establish sparsity of B, we set A = {n | ∃ m, 0 < m ∧ n ∈ d.shifts m}.
  set A := {n | ∃ m, 0 < m ∧ n ∈ d.shifts m} with hA_def
  -- By definition of $A$, we know that for any $h$, $(countIn A N)^h / N \to 0$ as $N \to \infty$.
  have hA_sparse :
      ∀ h : ℕ,
        Filter.Tendsto (fun N => (countIn A N : ℝ) ^ h / N)
          Filter.atTop (nhds 0) := by
    intro h
    have := d.sparse h
    simp_all +decide [ countIn ]
    convert this using 1
  -- Since $B = \{1\} \cup A$, we have $countIn B N \leq 1 + countIn A N$.
  have hB_count : ∀ N : ℕ, countIn (constructB d) N ≤ 1 + countIn A N := by
    intro N
    exact le_trans
      (Finset.card_le_card
        (show _ ⊆ {1} ∪ Finset.filter (fun a => a ∈ A) (Finset.Ioc 0 N) from
          fun x hx => by aesop))
      (Finset.card_union_le _ _)
  -- Using the sparsity of A, we can show that $(1 + countIn A N)^h / N \to 0$ as $N \to \infty$.
  have hB_sparse :
      ∀ h : ℕ,
        Filter.Tendsto (fun N => (1 + countIn A N : ℝ) ^ h / N)
          Filter.atTop (nhds 0) := by
    intro h
    have h_expand :
        Filter.Tendsto
          (fun N =>
            (∑ i ∈ Finset.range (h + 1),
              Nat.choose h i * (countIn A N : ℝ) ^ i) / N)
          Filter.atTop (nhds 0) := by
      simp_all +decide [ Finset.sum_div _ _ _ ]
      simpa [ mul_div_assoc ] using
        tendsto_finset_sum _ fun i hi =>
          Filter.Tendsto.const_mul _ (hA_sparse i)
    convert h_expand using 2
    rw [ add_comm, add_pow ]
    norm_num [ mul_comm ]
  apply not_basis_of_sparse
  intro h
  specialize hB_sparse h
  refine' squeeze_zero ( fun N => by positivity ) ( fun N => _ ) hB_sparse
  gcongr
  norm_cast
  aesop

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
set_option linter.style.refine false in
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
    refine' Finset.card_bij ( fun x hx => c + 1 - x ) _ _ _ <;> simp_all +decide
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
set_option linter.style.induction false in
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
    induction' i with i ih
    · exact hC _ ( hf_mem _ )
    · exact lt_of_le_of_lt ( ih ( Nat.lt_of_succ_lt hi ) ) ( hf_mono ( Nat.lt_succ_self _ ) )
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
set_option linter.style.multiGoal false in
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
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα_nonneg) (sq_nonneg _))
        (Nat.cast_nonneg _)
      norm_num
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
