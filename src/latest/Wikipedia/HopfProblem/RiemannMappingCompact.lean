/-
Parts of this file are derived from Yury Kudryashov's Mathlib development.

Source: https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov
-/
import Wikipedia.HopfProblem.RiemannMappingNormalFamily

/-!
# Compactness of the bounded holomorphic family

The compact-convergence function space, its countably generated
uniformity, and its genuine Arzelà–Ascoli compact closure are used to
attain the extremal derivative in the Riemann mapping theorem.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Uniformity UniformConvergence

namespace Wikipedia.HopfProblem.RiemannMapping

/-- Compact subsets of the given complex domain. -/
def compactSubsets (U : Set ℂ) : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}

/-- Actual uniform convergence on compact subsets of the given domain. -/
abbrev FunctionSpace (U : Set ℂ) := ℂ →ᵤ[compactSubsets U] ℂ

def evaluation {U : Set ℂ} (f : FunctionSpace U) : ℂ → ℂ :=
  UniformOnFun.toFun (compactSubsets U) f

theorem uniformity_isCountablyGenerated {U : Set ℂ} (hUo : IsOpen U) :
    (𝓤 (FunctionSpace U)).IsCountablyGenerated := by
  have := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let φ : CompactExhaustion U := default
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' φ n)
  · intro n
    exact ⟨image_val_subset, (φ.isCompact n).image continuous_subtype_val⟩
  · exact monotone_image.comp φ.subset
  · rintro K ⟨hKU, hKc⟩
    lift K to Set U using hKU
    rw [← Subtype.isCompact_iff] at hKc
    exact (φ.exists_superset_of_isCompact hKc).imp fun n hn => by gcongr

/-- Neighborhood convergence in the actual compact-convergence space
is locally uniform convergence of the corresponding complex functions. -/
theorem evaluation_tendstoLocallyUniformlyOn {U : Set ℂ} (hUo : IsOpen U)
    {f : FunctionSpace U} {s : Set (FunctionSpace U)} :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[s] f) U := by
  have h : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp h) K ⟨hKU, hK⟩

/-- Uniform bounds and holomorphicity give an actual compact closure,
proved by Arzelà–Ascoli and the checked Schwarz estimate. -/
theorem isCompact_closure_of_bounded_holomorphic {U : Set ℂ} (hUo : IsOpen U)
    {s : Set (FunctionSpace U)}
    (hsd : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    (hsb : ∃ C : ℝ, ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C) :
    IsCompact (closure s) := by
  obtain ⟨C, hC⟩ := hsb
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := compactSubsets U) (fun K hK => hK.2) (F := evaluation) .id
  · rintro K ⟨hKU, _⟩ z hz
    exact (equicontinuousAt_of_forall_norm_le (hUo.mem_nhds (hKU hz))
      (fun f : s => hsd f.val f.property)
      ⟨C, fun f z hz => hC f.val f.property z hz⟩).equicontinuousWithinAt K
  · intro K hK x hx
    exact ⟨closedBall 0 C, isCompact_closedBall _ _, fun f hf => by
      simpa only [mem_closedBall_zero_iff] using hC f hf x (hK.1 hx)⟩

end Wikipedia.HopfProblem.RiemannMapping
