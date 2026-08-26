/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import Mathlib

namespace Erdos696

-- === Inlined from Erdos696/Defs.lean ===
/-
# Fundamental definitions for Erdős Problem #696.

Mirrors §1 and §2 of `erdos_696_paper.tex`.

Definitions provided:

* `Erdos696.IsPrimeChain`        — predicate on a list of primes
                                    `p₁ < ⋯ < pₗ` with `p_{i+1} ≡ 1 (mod p_i)`.
* `Erdos696.IsDivisorChain`      — analogous predicate for divisors.
* `Erdos696.hChain n`            — Erdős's `h(n)` function.
* `Erdos696.HChain n`            — Erdős's `H(n)` function.
* `Erdos696.iteratedLog k x`     — `log^{(k)}(x)` (k-fold natural logarithm).
* `Erdos696.logStar x`           — `log_*(x) = min{k ≥ 0 : log^{(k)}(x) ≤ e}`.
* `Erdos696.tower m`             — `T_m`, the iterated tower
                                    (`T_0 = e`, `T_{m+1} = exp T_m`).
* `Erdos696.Um m`                — `U_m := T_m^3`.
* `Erdos696.almostAll P`         — density-one predicate
                                    `#{n ≤ x : ¬P(n)} = o(x)`.
-/



open scoped BigOperators
open Real

/-! ### Prime and divisor chains -/

/-- A list of natural numbers `p₁, …, pₗ` is a *prime chain dividing `n`*
if all entries are primes that divide `n`, the list is strictly
increasing, and consecutive entries satisfy `p_{i+1} ≡ 1 (mod p_i)`.

This is the predicate underlying `hChain n` in §1 of the paper. -/
def IsPrimeChain (n : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime ∧ p ∣ n) ∧
  ps.Pairwise (· < ·) ∧
  (∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      ps.get ⟨i.val + 1, hi⟩ % ps.get i = 1)

/-- A list of natural numbers `d₁, …, dᵤ` is a *divisor chain of `n`* if
every entry divides `n`, the list is strictly increasing, every entry is
at least 1, and consecutive entries satisfy `d_{i+1} ≡ 1 (mod d_i)`.

This is the predicate underlying `HChain n` in §1 of the paper.

We use `Nat.ModEq` (which checks `e % d = 1 % d`) rather than the raw
`e % d = 1`.  These agree when `d ≥ 2` (so the prime-chain definition
is unaffected), but for `d = 1` the paper's vacuous-modulo-1 convention
requires the `ModEq` form: `e ≡ 1 [MOD 1]` is true (everything is congruent
mod 1), while `e % 1 = 1` is false (since `e % 1 = 0`).  Paper §7 (line 1891)
constructs lower-bound chains starting with `d_1 = 1`. -/
def IsDivisorChain (n : ℕ) (ds : List ℕ) : Prop :=
  (∀ d ∈ ds, 1 ≤ d ∧ d ∣ n) ∧
  ds.Pairwise (· < ·) ∧
  (∀ i : Fin ds.length, ∀ hi : i.val + 1 < ds.length,
      Nat.ModEq (ds.get i) (ds.get ⟨i.val + 1, hi⟩) 1)

/-- `h(n)` of the paper: the largest length of a prime chain dividing `n`,
with `hChain 1 = 0` by convention. -/
noncomputable def hChain (n : ℕ) : ℕ :=
  sSup {ℓ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ}

/-- `H(n)` of the paper: the largest length of a divisor chain of `n`,
with `HChain 1 = 0` by paper convention (paper line 88).

Without the `n = 1` special case the singleton chain `[1]` would give
`sSup … = 1`, so we hard-code the paper convention. -/
noncomputable def HChain (n : ℕ) : ℕ :=
  if n = 1 then 0
  else sSup {u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u}

/-! ### Iterated logarithms and the tower -/

/-- The `k`-fold natural logarithm `log^{(k)}(x)`. -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0,     x => x
  | k+1,   x => Real.log (iteratedLog k x)

/-- `log_* x = min{k ≥ 0 : log^{(k)} x ≤ e}`.

Defined classically.  We use `Classical.propDecidable` to get a
`Decidable` instance for the existence statement, then use `Nat.find`
to extract the minimum.  If no such `k` exists (e.g. for `x = 0`) we
fall back to `0` for definability; since the iterated logarithm
eventually drops below `e` for any `x ≥ 1`, this fallback is irrelevant
for the regime of interest. -/
noncomputable def logStar (x : ℝ) : ℕ := by
  classical
  exact
    if h : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 then Nat.find h else 0

/-- The tower `T_m` of base-`e` exponentials: `T₀ = e`, `T_{m+1} = exp T_m`.
Mirrors equation (2.3) of the paper. -/
noncomputable def tower : ℕ → ℝ
  | 0   => Real.exp 1
  | m+1 => Real.exp (tower m)

/-- The auxiliary scale `U_m := T_m^3` of equation (2.5). -/
noncomputable def Um (m : ℕ) : ℝ := (tower m) ^ 3

/-! ### Almost-all (density-one) predicate -/

/-- A property `P` holds *for almost all `n`* (equivalently, with density one)
if `#{n ≤ x : ¬P(n)} = o(x)` as `x → ∞`.

This is equation (2.2) of the paper.  We express it as a `Filter.Tendsto`
statement in the `Filter.atTop` sense on real `x`. -/
def almostAll (P : ℕ → Prop) : Prop :=
  Filter.Tendsto
    (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x)
    Filter.atTop (nhds 0)

/-! ### Trivial monotonicity lemma -/
/-! ### `almostAll` helpers (moved here from Main.lean to break import cycles) -/

/-- `almostAll` is monotone under pointwise implication. -/
lemma almostAll_mono {P Q : ℕ → Prop} (hP : almostAll P) (hPQ : ∀ n, P n → Q n) :
    almostAll Q := by
  classical
  unfold almostAll at hP ⊢
  refine squeeze_zero' ?_ ?_ hP
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hsub : {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n} ⊆ {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} := by
      intro n hn
      exact ⟨hn.1, fun hp => hn.2 (hPQ n hp)⟩
    have hfinite : Set.Finite {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hcard := Nat.card_mono hfinite hsub
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hx.le

/-- The intersection of two density-one properties is density-one. -/
lemma almostAll_and {P Q : ℕ → Prop} (hP : almostAll P) (hQ : almostAll Q) :
    almostAll (fun n => P n ∧ Q n) := by
  classical
  unfold almostAll at hP hQ ⊢
  have hsum : Filter.Tendsto
      (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x +
        ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n} : ℕ) : ℝ) / x)
      Filter.atTop (nhds 0) := by
    simpa using hP.add hQ
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    let sA : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ (P n ∧ Q n)}
    let sP : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n}
    let sQ : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n}
    have hsub : sA ⊆ sP ∪ sQ := by
      intro n hn
      dsimp [sA] at hn
      by_cases hp : P n
      · exact Or.inr ⟨hn.1, fun hq => hn.2 ⟨hp, hq⟩⟩
      · exact Or.inl ⟨hn.1, hp⟩
    have hfiniteP : Set.Finite sP := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hfiniteQ : Set.Finite sQ := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hfiniteU : Set.Finite (sP ∪ sQ) := hfiniteP.union hfiniteQ
    have hcard1 : Nat.card sA ≤ Nat.card ↑(sP ∪ sQ) := Nat.card_mono hfiniteU hsub
    have hcard2 : Nat.card ↑(sP ∪ sQ) ≤ Nat.card sP + Nat.card sQ :=
      Set.card_union_le sP sQ
    have hcard : Nat.card sA ≤ Nat.card sP + Nat.card sQ := hcard1.trans hcard2
    calc
      ((Nat.card sA : ℕ) : ℝ) / x ≤ ((Nat.card sP + Nat.card sQ : ℕ) : ℝ) / x := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hx.le
      _ = ((Nat.card sP : ℕ) : ℝ) / x + ((Nat.card sQ : ℕ) : ℝ) / x := by
        rw [Nat.cast_add, add_div]

end Erdos696
