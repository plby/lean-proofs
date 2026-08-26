/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.LowerBoundH

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

variable [sw : SiegelWalfisz]
include sw

-- === Inlined from Erdos696/Main.lean ===
/-
# Main theorem for Erdős Problem #696

Mirrors §8 of `erdos_696_paper.tex`.

The four bounds combined yield, for almost all `n ≤ x`:

* `h(n) = (1/2 + o(1)) log_* n`
* `H(n) = (1 + o(1)) log_* n`
* `H(n) / h(n) = 2 + o(1)`

In particular, Erdős's conjectured `H(n)/h(n) → ∞` is **false** on a
density-one set.
-/



-- almostAll_mono and almostAll_and moved to Defs.lean to break import cycles.

/-- **Main theorem** (Theorem 1.1 in `erdos_696_paper.tex`).

For every `ε > 0`:
* `h(n) = (1/2 + o(1)) log_* n` for almost all `n`,
* `H(n) = (1 + o(1)) log_* n` for almost all `n`,
* `H(n) / h(n) = 2 + o(1)` for almost all `n`.

The conclusion is stated as: the density-one set on which the relevant
bounds hold has density tending to `1` as `x → ∞`, simultaneously for
all three quantities. -/
theorem erdos_696_of_siegel_walfisz :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n =>
        |(hChain n : ℝ) - (logStar n : ℝ) / 2| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
        |(HChain n : ℝ) - (logStar n : ℝ)| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
        n ≥ 2 →
          |(HChain n : ℝ) / (hChain n : ℝ) - 2| ≤ ε) := by
  -- Combine `upper_bound_h`, `lower_bound_h`, `upper_bound_H`,
  -- `lower_bound_H`.
  --
  --  * The first two-sided bound on `h(n)` is the conjunction of
  --    `lower_bound_h ε` and `upper_bound_h ε`.
  --  * Likewise for `H(n)`.
  --  * The ratio bound follows from the two-sided bounds via division
  --    (using the lower bound `h(n) ≥ (1/2 - ε) log_* n` to ensure the
  --    denominator is bounded away from `0`).
  --
  -- §8 of the paper additionally argues that `log_* x` and `log_* n`
  -- agree up to `O(1)` for `n ∈ [x^{1/2}, x]` and that the residual
  -- `n ≤ x^{1/2}` is an `o(x)` exceptional set.  The Lean formalization
  -- uses `log_* n` directly throughout `almostAll`, so the conversion
  -- is built into the definitions.
  intro ε hε
  classical
  have hhAbsBase : almostAll (fun n =>
      (hChain n : ℝ) ≥ (1 / 2 - ε) * (logStar n : ℝ) ∧
        (hChain n : ℝ) ≤ (1 / 2 + ε) * (logStar n : ℝ)) :=
    almostAll_and (lower_bound_h ε hε) (upper_bound_h ε hε)
  have hhAbs : almostAll (fun n =>
      |(hChain n : ℝ) - (logStar n : ℝ) / 2| ≤ ε * (logStar n : ℝ)) := by
    refine almostAll_mono hhAbsBase ?_
    intro n hn
    rw [abs_le]
    constructor <;> nlinarith [hn.1, hn.2]
  have hHAbsBase : almostAll (fun n =>
      (HChain n : ℝ) ≥ (1 - ε) * (logStar n : ℝ) ∧
        (HChain n : ℝ) ≤ (1 + ε) * (logStar n : ℝ)) :=
    almostAll_and (lower_bound_H ε hε) (upper_bound_H ε hε)
  have hHAbs : almostAll (fun n =>
      |(HChain n : ℝ) - (logStar n : ℝ)| ≤ ε * (logStar n : ℝ)) := by
    refine almostAll_mono hHAbsBase ?_
    intro n hn
    rw [abs_le]
    constructor <;> nlinarith [hn.1, hn.2]
  let δ : ℝ := min (ε / 16) (1 / 4)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by norm_num)
  have hδ_le_eps16 : δ ≤ ε / 16 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    dsimp [δ]
    exact min_le_right _ _
  have hquarter_le_half_sub : (1 / 4 : ℝ) ≤ 1 / 2 - δ := by
    linarith
  have hthree_delta_le_eps_quarter : 3 * δ ≤ ε / 4 := by
    nlinarith [hδ_le_eps16]
  rcases eventually_logStar_ge 1 with ⟨N, hN⟩
  have hlarge : almostAll (fun n => (1 : ℝ) ≤ (logStar n : ℝ)) := by
    refine almostAll_of_forall_ge N ?_
    intro n hn
    exact_mod_cast hN n hn
  have hhδ : almostAll (fun n =>
      (hChain n : ℝ) ≥ (1 / 2 - δ) * (logStar n : ℝ) ∧
        (hChain n : ℝ) ≤ (1 / 2 + δ) * (logStar n : ℝ)) :=
    almostAll_and (lower_bound_h δ hδpos) (upper_bound_h δ hδpos)
  have hHδ : almostAll (fun n =>
      (HChain n : ℝ) ≥ (1 - δ) * (logStar n : ℝ) ∧
        (HChain n : ℝ) ≤ (1 + δ) * (logStar n : ℝ)) :=
    almostAll_and (lower_bound_H δ hδpos) (upper_bound_H δ hδpos)
  have hboundsδ := almostAll_and (almostAll_and hhδ hHδ) hlarge
  have hratio : almostAll (fun n =>
      n ≥ 2 → |(HChain n : ℝ) / (hChain n : ℝ) - 2| ≤ ε) := by
    refine almostAll_mono hboundsδ ?_
    intro n hn _hn2
    rcases hn with ⟨⟨hh, hH⟩, hL1⟩
    rcases hh with ⟨hhlo, hhup⟩
    rcases hH with ⟨hHlo, hHup⟩
    let L : ℝ := (logStar n : ℝ)
    let b : ℝ := (hChain n : ℝ)
    let a : ℝ := (HChain n : ℝ)
    have hhlo' : (1 / 2 - δ) * L ≤ b := by simpa [L, b] using hhlo
    have hhup' : b ≤ (1 / 2 + δ) * L := by simpa [L, b] using hhup
    have hHlo' : (1 - δ) * L ≤ a := by simpa [L, a] using hHlo
    have hHup' : a ≤ (1 + δ) * L := by simpa [L, a] using hHup
    have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
    have hLnonneg : 0 ≤ L := le_trans (by norm_num) hL1'
    have hbge : (1 / 4 : ℝ) * L ≤ b := by
      exact (mul_le_mul_of_nonneg_right hquarter_le_half_sub hLnonneg).trans hhlo'
    have hbpos : 0 < b := by nlinarith [hbge, hL1']
    have hnum : |a - 2 * b| ≤ 3 * δ * L := by
      rw [abs_le]
      constructor
      · nlinarith [hHlo', hhup']
      · nlinarith [hHup', hhlo']
    have hnum_le : |a - 2 * b| ≤ (ε / 4) * L := by
      have hcomp : 3 * δ * L ≤ (ε / 4) * L := by
        exact mul_le_mul_of_nonneg_right hthree_delta_le_eps_quarter hLnonneg
      exact hnum.trans hcomp
    have htarget_num : |a - 2 * b| ≤ ε * b := by
      have hcomp : (ε / 4) * L ≤ ε * b := by
        calc
          (ε / 4) * L = ε * ((1 / 4) * L) := by ring
          _ ≤ ε * b := mul_le_mul_of_nonneg_left hbge hε.le
      exact hnum_le.trans hcomp
    have hrewrite : a / b - 2 = (a - 2 * b) / b := by
      field_simp [hbpos.ne']
    have habs : |a / b - 2| = |a - 2 * b| / b := by
      rw [hrewrite, abs_div, abs_of_pos hbpos]
    calc
      |(HChain n : ℝ) / (hChain n : ℝ) - 2| = |a / b - 2| := by simp [a, b]
      _ = |a - 2 * b| / b := habs
      _ ≤ ε := (div_le_iff₀ hbpos).2 htarget_num
  exact ⟨hhAbs, hHAbs, hratio⟩

end Erdos696
