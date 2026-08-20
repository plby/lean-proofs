/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.OddRayNormRosser

/-!
# Finite-fibre assembly for the odd medium-prime estimate

The arithmetic construction splits the exceptional rational primes into a
fixed finite family of correction/ray fibres.  This file contains only the
numerical assembly step.  If every fibre has a Rosser main term with constant
`mainConstant i` and a lattice-boundary envelope with constant
`errorConstant i`, then the union has the same estimate with the two constants
summed over the finite index set.

No disjointness of the fibres is required.  The final theorem feeds the
assembled estimate directly to
`OddMediumParameters.primeExponentMediumEstimate_of_rosserCellEnvelope`.
-/

open Filter
open scoped BigOperators

namespace Erdos980.ElliottTail.OddFiniteFibreAssembly

open OddMediumParameters
open OddRayNormRosser

/-- The main-term constant obtained by summing a finite family of fibres. -/
def finiteFibreMainConstant {ι : Type*} (indices : Finset ι)
    (mainConstant : ι → ℝ) : ℝ :=
  ∑ i ∈ indices, mainConstant i

/-- The Rosser-cell error constant obtained by summing a finite family of
fibres. -/
def finiteFibreErrorConstant {ι : Type*} (indices : Finset ι)
    (errorConstant : ι → ℝ) : ℝ :=
  ∑ i ∈ indices, errorConstant i

/-- The global error constant when, in addition to the correction fibres,
there is a finite sieve-loss set with its own Rosser-cell envelope. -/
def finiteFibreErrorConstantWithLoss {ι : Type*} (indices : Finset ι)
    (errorConstant : ι → ℝ) (lossConstant : ℝ) : ℝ :=
  lossConstant + finiteFibreErrorConstant indices errorConstant

theorem finiteFibreMainConstant_nonneg
    {ι : Type*} (indices : Finset ι) (mainConstant : ι → ℝ)
    (hmain : ∀ i ∈ indices, 0 ≤ mainConstant i) :
    0 ≤ finiteFibreMainConstant indices mainConstant := by
  exact Finset.sum_nonneg hmain

theorem finiteFibreErrorConstant_nonneg
    {ι : Type*} (indices : Finset ι) (errorConstant : ι → ℝ)
    (herror : ∀ i ∈ indices, 0 ≤ errorConstant i) :
    0 ≤ finiteFibreErrorConstant indices errorConstant := by
  exact Finset.sum_nonneg herror

theorem finiteFibreErrorConstantWithLoss_nonneg
    {ι : Type*} (indices : Finset ι) (errorConstant : ι → ℝ)
    (lossConstant : ℝ) (herror : ∀ i ∈ indices, 0 ≤ errorConstant i)
    (hloss : 0 ≤ lossConstant) :
    0 ≤ finiteFibreErrorConstantWithLoss indices errorConstant
      lossConstant := by
  exact add_nonneg hloss
    (finiteFibreErrorConstant_nonneg indices errorConstant herror)

/-- Assemble eventual Rosser-cell bounds over a fixed finite cover.

The cover is allowed to overlap.  Its cardinality is bounded by the sum of
the fibre cardinalities using
`OddRayNormRosser.exceptional_card_le_sum_fibreCards`; linearity then sums the
main and error constants exactly.  Both the fibre bounds and the conclusion
are uniform in `t ≤ smoothParameterY x`. -/
theorem eventually_exceptional_card_le_finiteFibreRosserCellEnvelope
    {ι : Type*}
    (indices : Finset ι) (fibre : ι → ℕ → ℕ → Finset ℕ)
    {ell r k : ℕ} {eta : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        indices.biUnion (fun i ↦ fibre i t x))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstant indices errorConstant) (x : ℝ) := by
  classical
  have hall := (Finset.eventually_all indices).2 hfibre
  filter_upwards [hall] with x hx
  intro t ht
  have hcardNat :
      (exceptionalPrimes ell t x).card ≤
        ∑ i ∈ indices, (fibre i t x).card :=
    exceptional_card_le_sum_fibreCards indices (fun i ↦ fibre i t x)
      (exceptionalPrimes ell t x) (hcover x t)
  have hcardReal :
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        ∑ i ∈ indices, ((fibre i t x).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((exceptionalPrimes ell t x).card : ℝ) ≤
        ∑ i ∈ indices, ((fibre i t x).card : ℝ) := hcardReal
    _ ≤ ∑ i ∈ indices,
          (mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) := by
      exact Finset.sum_le_sum fun i hi ↦ hx i hi t ht
    _ = finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstant indices errorConstant) (x : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · unfold finiteFibreMainConstant
        rw [← Finset.sum_div, Finset.sum_mul]
      · unfold finiteFibreErrorConstant realRosserCellEnvelope
        rw [Finset.sum_mul, Finset.sum_mul]

/-- Existential form of finite-fibre assembly, recording that the global
constants are literally the finite sums of the local constants. -/
theorem exists_nonneg_global_constants_of_finiteFibreRosserCellEnvelopes
    {ι : Type*}
    (indices : Finset ι) (fibre : ι → ℕ → ℕ → Finset ℕ)
    {ell r k : ℕ} {eta : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hmain : ∀ i ∈ indices, 0 ≤ mainConstant i)
    (herror : ∀ i ∈ indices, 0 ≤ errorConstant i)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        indices.biUnion (fun i ↦ fibre i t x))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    ∃ A C : ℝ,
      A = finiteFibreMainConstant indices mainConstant ∧
      C = finiteFibreErrorConstant indices errorConstant ∧
      0 ≤ A ∧ 0 ≤ C ∧
      ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta C (x : ℝ) := by
  refine ⟨finiteFibreMainConstant indices mainConstant,
    finiteFibreErrorConstant indices errorConstant, rfl, rfl,
    finiteFibreMainConstant_nonneg indices mainConstant hmain,
    finiteFibreErrorConstant_nonneg indices errorConstant herror, ?_⟩
  exact eventually_exceptional_card_le_finiteFibreRosserCellEnvelope
    indices fibre mainConstant errorConstant hcover hfibre

/-- Finite-fibre assembly with an additional sieve-loss set.

This is the form needed when only the complement of a small family of
`inSievePrimes` exceptions injects into the norm-sifted generator fibres.
The finite loss may depend on `x` and `t`, but its bound is uniform in
`t ≤ smoothParameterY x` and has the same Rosser-cell envelope shape.  Its
constant is added exactly to the sum of the fibre error constants. -/
theorem eventually_exceptional_card_le_finiteFibreRosserCellEnvelope_withLoss
    {ι : Type*}
    (indices : Finset ι) (fibre : ι → ℕ → ℕ → Finset ℕ)
    (finiteLoss : ℕ → ℕ → Finset ℕ)
    {ell r k : ℕ} {eta lossConstant : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        finiteLoss t x ∪ indices.biUnion (fun i ↦ fibre i t x))
    (hloss : ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((finiteLoss t x).card : ℝ) ≤
          realRosserCellEnvelope r k eta lossConstant (x : ℝ))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstantWithLoss indices errorConstant
              lossConstant) (x : ℝ) := by
  classical
  have hall := (Finset.eventually_all indices).2 hfibre
  filter_upwards [hall, hloss] with x hx hxloss
  intro t ht
  have hcardNat :
      (exceptionalPrimes ell t x).card ≤
        (finiteLoss t x).card + ∑ i ∈ indices, (fibre i t x).card := by
    calc
      (exceptionalPrimes ell t x).card ≤
          (finiteLoss t x ∪
            indices.biUnion (fun i ↦ fibre i t x)).card :=
        Finset.card_le_card (hcover x t)
      _ ≤ (finiteLoss t x).card +
          (indices.biUnion (fun i ↦ fibre i t x)).card :=
        Finset.card_union_le _ _
      _ ≤ (finiteLoss t x).card +
          ∑ i ∈ indices, (fibre i t x).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hcardReal :
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        ((finiteLoss t x).card : ℝ) +
          ∑ i ∈ indices, ((fibre i t x).card : ℝ) := by
    exact_mod_cast hcardNat
  have hfibreSum :
      (∑ i ∈ indices, ((fibre i t x).card : ℝ)) ≤
        ∑ i ∈ indices,
          (mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :=
    Finset.sum_le_sum fun i hi ↦ hx i hi t ht
  calc
    ((exceptionalPrimes ell t x).card : ℝ) ≤
        ((finiteLoss t x).card : ℝ) +
          ∑ i ∈ indices, ((fibre i t x).card : ℝ) := hcardReal
    _ ≤ realRosserCellEnvelope r k eta lossConstant (x : ℝ) +
        ∑ i ∈ indices,
          (mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta
              (errorConstant i) (x : ℝ)) :=
      add_le_add (hxloss t ht) hfibreSum
    _ = finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstantWithLoss indices errorConstant
              lossConstant) (x : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hmainSum :
          (∑ i ∈ indices,
              mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2)) =
            finiteFibreMainConstant indices mainConstant *
                ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2) := by
        unfold finiteFibreMainConstant
        rw [← Finset.sum_div, Finset.sum_mul]
      have herrorSum :
          (∑ i ∈ indices,
              realRosserCellEnvelope r k eta
                (errorConstant i) (x : ℝ)) =
            realRosserCellEnvelope r k eta
              (finiteFibreErrorConstant indices errorConstant) (x : ℝ) := by
        unfold finiteFibreErrorConstant realRosserCellEnvelope
        rw [Finset.sum_mul, Finset.sum_mul]
      rw [hmainSum, herrorSum]
      unfold finiteFibreErrorConstantWithLoss realRosserCellEnvelope
      ring

/-- Direct medium-estimate wrapper including an envelope-sized finite sieve
loss. -/
theorem primeExponentMediumEstimate_of_finiteFibreRosserCellEnvelopes_withLoss
    {ι : Type*}
    (indices : Finset ι) (fibre : ι → ℕ → ℕ → Finset ℕ)
    (finiteLoss : ℕ → ℕ → Finset ℕ)
    {ell r k : ℕ} (hell : 2 ≤ ell) {eta lossConstant : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hr : 0 < r) (heta : eta < (r : ℝ)⁻¹)
    (hmain : ∀ i ∈ indices, 0 ≤ mainConstant i)
    (herror : ∀ i ∈ indices, 0 ≤ errorConstant i)
    (hlossConstant : 0 ≤ lossConstant)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        finiteLoss t x ∪ indices.biUnion (fun i ↦ fibre i t x))
    (hloss : ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((finiteLoss t x).card : ℝ) ≤
          realRosserCellEnvelope r k eta lossConstant (x : ℝ))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    PrimeExponentMediumEstimate ell := by
  apply primeExponentMediumEstimate_of_rosserCellEnvelope
    hell hr heta
      (finiteFibreErrorConstantWithLoss_nonneg indices errorConstant
        lossConstant herror hlossConstant)
      (finiteFibreMainConstant_nonneg indices mainConstant hmain)
  exact eventually_exceptional_card_le_finiteFibreRosserCellEnvelope_withLoss
    indices fibre finiteLoss mainConstant errorConstant hcover hloss hfibre

/-- A fixed finite cover by Rosser-controlled fibres implies the required
odd-prime medium estimate.  This is the direct consumer-facing assembly
theorem: all correction/tag bookkeeping is confined to `indices`, `fibre`,
and `hcover`. -/
theorem primeExponentMediumEstimate_of_finiteFibreRosserCellEnvelopes
    {ι : Type*}
    (indices : Finset ι) (fibre : ι → ℕ → ℕ → Finset ℕ)
    {ell r k : ℕ} (hell : 2 ≤ ell) {eta : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hr : 0 < r) (heta : eta < (r : ℝ)⁻¹)
    (hmain : ∀ i ∈ indices, 0 ≤ mainConstant i)
    (herror : ∀ i ∈ indices, 0 ≤ errorConstant i)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        indices.biUnion (fun i ↦ fibre i t x))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    PrimeExponentMediumEstimate ell := by
  apply primeExponentMediumEstimate_of_rosserCellEnvelope
    hell hr heta
      (finiteFibreErrorConstant_nonneg indices errorConstant herror)
      (finiteFibreMainConstant_nonneg indices mainConstant hmain)
  exact eventually_exceptional_card_le_finiteFibreRosserCellEnvelope
    indices fibre mainConstant errorConstant hcover hfibre

end Erdos980.ElliottTail.OddFiniteFibreAssembly
