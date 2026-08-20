/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Transferring relative prime densities through the prime number theorem

This file isolates the asymptotic bookkeeping needed after a Chebotarev-style
argument has counted a set relative to all primes.  Its main input from the
prime number theorem is
`BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent`.

There is a small but important zero-density caveat.  In mathlib,
`f ~[l] 0` is equivalent to `f =ᶠ[l] 0`; it does *not* express the usual
statement `f = o(g)`.  Thus `count_isEquivalent_pntMain` is valid for every
constant, including zero, but a zero-valued hypothesis of its stated form is
much stronger than ordinary density zero.  The ratio formulation below asks
that the density be nonzero.
-/

namespace Erdos980.NaturalChebotarev

open Asymptotics Filter

/-- Transfer an asymptotic equivalence through multiplication by a fixed
scalar.  Keeping this lemma independent of primes makes the bookkeeping
reusable for other reference counting functions. -/
theorem const_mul_equivalent_trans
    {α : Type*} {l : Filter α} {count reference main : α → ℝ} (δ : ℝ)
    (hcount : count ~[l] (fun x ↦ δ * reference x))
    (href : reference ~[l] main) :
    count ~[l] (fun x ↦ δ * main x) := by
  refine hcount.trans ?_
  rw [IsEquivalent] at href ⊢
  rw [isLittleO_iff] at href ⊢
  intro c hc
  filter_upwards [href hc] with x hx
  simpa only [Pi.sub_apply, ← mul_sub, norm_mul] using
    (calc
      ‖δ‖ * ‖reference x - main x‖ ≤ ‖δ‖ * (c * ‖main x‖) :=
        mul_le_mul_of_nonneg_left hx (norm_nonneg δ)
      _ = c * (‖δ‖ * ‖main x‖) := by ring)

/-- If a real-valued counting function is asymptotic to `δ` times the number
of primes up to `n`, then it is asymptotic to `δ n / log n`.

For `δ = 0`, the hypothesis says that `count` is eventually identically zero;
see `isEquivalent_zero_iff_eventually_zero`. -/
theorem count_isEquivalent_pntMain
    {count : ℕ → ℝ} (δ : ℝ)
    (hcount : count ~[atTop]
      (fun n ↦ δ * (Nat.primeCounting n : ℝ))) :
    count ~[atTop]
      (fun n ↦ δ * ((n : ℝ) / Real.log (n : ℝ))) := by
  exact const_mul_equivalent_trans δ hcount
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent

/-- The correct zero-density transfer: a count which is little-oh of the
number of primes is little-oh of `n / log n`. -/
theorem count_isLittleO_pntMain
    {count : ℕ → ℝ}
    (hcount : count =o[atTop]
      (fun n ↦ (Nat.primeCounting n : ℝ))) :
    count =o[atTop]
      (fun n ↦ (n : ℝ) / Real.log (n : ℝ)) := by
  exact hcount.trans_isEquivalent
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent

/-- Ratio form of the zero-density case. -/
theorem count_isLittleO_pntMain_of_ratio_zero
    {count : ℕ → ℝ}
    (hdensity : Tendsto
      (fun n ↦ count n / (Nat.primeCounting n : ℝ))
      atTop (nhds 0)) :
    count =o[atTop]
      (fun n ↦ (n : ℝ) / Real.log (n : ℝ)) := by
  apply count_isLittleO_pntMain
  have hmainPos : ∀ᶠ n : ℕ in atTop,
      0 < (n : ℝ) / Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_pos
      (by exact_mod_cast (show 0 < n by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hpiPos : ∀ᶠ n : ℕ in atTop,
      0 < (Nat.primeCounting n : ℝ) :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent.eventually_pos
      hmainPos
  rw [isLittleO_iff_tendsto']
  · simpa only [Pi.div_apply] using hdensity
  · exact hpiPos.mono fun _ hn hzero ↦ (hn.ne' hzero).elim

/-- Ratio form of `count_isEquivalent_pntMain`: a nonzero relative density
among the primes gives the corresponding `n / log n` asymptotic.

The nonzero assumption is mathematically necessary for an
`IsEquivalent` conclusion: when `δ = 0`, relative density zero should instead
be recorded as a little-oh statement. -/
theorem count_isEquivalent_pntMain_of_ratio
    {count : ℕ → ℝ} {δ : ℝ} (hδ : δ ≠ 0)
    (hdensity : Tendsto
      (fun n ↦ count n / (Nat.primeCounting n : ℝ))
      atTop (nhds δ)) :
    count ~[atTop]
      (fun n ↦ δ * ((n : ℝ) / Real.log (n : ℝ))) := by
  apply count_isEquivalent_pntMain δ
  have hpiNe : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≠ 0 := by
    filter_upwards [hdensity.eventually_ne hδ] with n hn
    exact (div_ne_zero_iff.mp hn).2
  have htargetNe : ∀ᶠ n : ℕ in atTop,
      δ * (Nat.primeCounting n : ℝ) ≠ 0 :=
    hpiNe.mono fun _ hn ↦ mul_ne_zero hδ hn
  rw [isEquivalent_iff_tendsto_one htargetNe]
  have hratio : Tendsto
      (fun n ↦ (count n / (Nat.primeCounting n : ℝ)) / δ)
      atTop (nhds 1) := by
    simpa [hδ] using hdensity.div_const δ
  apply hratio.congr'
  filter_upwards [hpiNe] with n hn
  simp only [Pi.div_apply]
  field_simp [hδ, hn]

end Erdos980.NaturalChebotarev
