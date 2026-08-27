/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MonotoneBernoulliCoupling
import ErdosProblems.Erdos207.FiniteCoordinateProduct

/-! # Independent Bernoulli batches coupled below an unchanged proposal law -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def independentMonotoneBits
    {I : Type*} [Fintype I] [DecidableEq I] (p q : I → ℝ≥0)
    (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1) : FiniteLaw (I → Bool × Bool) :=
  productCoordinates (fun i ↦ monotoneBitCoupling (p i) (q i) (hpq i) (hq i))

theorem productCoordinates_bernoulliBitLaw
    {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    productCoordinates (fun i ↦ bernoulliBitLaw (p i) (hp i)) = independentBits p hp := by
  apply FiniteLaw.ext
  intro x
  rfl

theorem independentMonotoneBits_proposal
    {I : Type*} [Fintype I] [DecidableEq I] (p q : I → ℝ≥0)
    (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1) :
    map (fun x i ↦ (x i).1) (independentMonotoneBits p q hpq hq) = independentBits q hq := by
  unfold independentMonotoneBits
  rw [map_productCoordinates]
  simp_rw [monotoneBitCoupling_first]
  exact productCoordinates_bernoulliBitLaw q hq

theorem independentMonotoneBits_actual
    {I : Type*} [Fintype I] [DecidableEq I] (p q : I → ℝ≥0)
    (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1) :
    map (fun x i ↦ (x i).2) (independentMonotoneBits p q hpq hq) =
      independentBits p (fun i ↦ (hpq i).trans (hq i)) := by
  unfold independentMonotoneBits
  rw [map_productCoordinates]
  simp_rw [monotoneBitCoupling_second]
  exact productCoordinates_bernoulliBitLaw p (fun i ↦ (hpq i).trans (hq i))

theorem independentMonotoneBits_supported
    {I : Type*} [Fintype I] [DecidableEq I] (p q : I → ℝ≥0)
    (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1) :
    (independentMonotoneBits p q hpq hq).SupportedOn
      (fun x ↦ selectedByBits (fun i ↦ (x i).2) ⊆ selectedByBits (fun i ↦ (x i).1)) := by
  have hsupport := productCoordinates_supported
    (fun i ↦ monotoneBitCoupling (p i) (q i) (hpq i) (hq i))
    (fun _ x ↦ x.2 = true → x.1 = true)
    (fun i ↦ monotoneBitCoupling_supported (p i) (q i) (hpq i) (hq i))
  intro x hx i hi
  have hi' : (x i).2 = true := by simpa only [mem_selectedByBits_iff] using hi
  have hproposal : (x i).1 = true := hsupport x hx i hi'
  simpa only [mem_selectedByBits_iff] using hproposal

end

end Erdos207.FiniteLaw
