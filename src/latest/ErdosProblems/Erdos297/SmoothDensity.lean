/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.RoughCounts

/-!
# The smooth-density input for Erdős Problem 297

In the Liu--Sawhney lower-bound argument two scales have distinct roles:

* `M = N / sqrt (log (log (log N)))` is the lower endpoint of the interval
  from which denominators are selected;
* `S = N / (log N)^4` is the upper bound on every exact prime-power part of
  an admissible denominator.

This file records both integer cutoffs and proves the density assertion needed
for the second one.  Namely, the number of `n ≤ N` having an exact prime-power
part larger than `S` is `o(N)`.  The proof reuses the finite union bound and
prime-power Mertens estimate in `Erdos285.RoughCounts`.
-/

namespace Erdos297.SmoothDensity

open Filter Finset Real
open scoped Topology

noncomputable section

open Erdos285.PrimePowers Erdos285.RoughCounts

attribute [local instance] Classical.propDecidable

/-- Liu--Sawhney's lower endpoint `M`, rounded down to a natural number. -/
def liuDenominatorLowerEndpoint (N : ℕ) : ℕ :=
  ⌊(N : ℝ) /
    Real.sqrt (Real.log (Real.log (Real.log (N : ℝ))))⌋₊

/-- Liu--Sawhney's prime-power smoothness cutoff
`S = floor (N / (log N)^4)`. -/
def liuPrimePowerCutoff (N : ℕ) : ℕ :=
  logPowerCutoff 4 N

/-- Integers in `[1,N]` all of whose exact prime-power parts are at most
Liu--Sawhney's cutoff `S`. -/
def smoothNumbersUpTo (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (PrimePowerSmooth (liuPrimePowerCutoff N))

/-- The exceptional integers in `[1,N]`, namely those having some exact
prime-power part larger than `S`. -/
def nonsmoothNumbersUpTo (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n ↦ ¬ PrimePowerSmooth (liuPrimePowerCutoff N) n

@[simp] lemma liuPrimePowerCutoff_eq (N : ℕ) :
    liuPrimePowerCutoff N =
      ⌊(N : ℝ) / Real.log (N : ℝ) ^ 4⌋₊ := by
  rfl

/-- Failure of prime-power smoothness is exactly the rough-number predicate
used by the prime-power union bound. -/
lemma nonsmoothNumbersUpTo_eq_roughNumbersIn (N : ℕ) :
    nonsmoothNumbersUpTo N =
      roughNumbersIn 1 N (liuPrimePowerCutoff N) := by
  ext n
  simp only [nonsmoothNumbersUpTo, mem_filter, mem_Icc,
    mem_roughNumbersIn]
  rw [← largestPrimePowerPart_le_iff]
  omega

/-- The source-faithful rough-set form: the number of integers `n ≤ N` with
an exact prime-power part larger than `floor (N / (log N)^4)` is `o(N)`. -/
theorem roughNumbersIn_liuPrimePowerCutoff_card_isLittleO :
    (fun N : ℕ ↦
      ((roughNumbersIn 1 N (liuPrimePowerCutoff N)).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [liuPrimePowerCutoff] using
    roughNumbersIn_logPowerCutoff_card_isLittleO 4

/-- All but `o(N)` integers in `[1,N]` are prime-power smooth at
`S = floor (N / (log N)^4)`. -/
theorem nonsmoothNumbersUpTo_card_isLittleO :
    (fun N : ℕ ↦ ((nonsmoothNumbersUpTo N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [nonsmoothNumbersUpTo_eq_roughNumbersIn] using
    roughNumbersIn_liuPrimePowerCutoff_card_isLittleO

end

end Erdos297.SmoothDensity
