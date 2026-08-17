/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.Density
import ErdosProblems.Erdos144.TransferBridge

/-!
# Abstract final transfer for Erdős Problem 144

This file isolates the last limiting argument.  It assumes convergence of
the bounded equal-subsum probability in the harmonic model, convergence of
the exact prime-block occupancy error, and eventual logarithmic resolution.
The finite CRT transfer at one sufficiently large scale then supplies a set
of existing density at least `1 - ε` inside the close-divisor set.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos144.FinalTransfer

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Abstract final density theorem for the prime-block transfer.

No particular construction of the scale sequences is assumed here.  The
input consists only of the two limiting statements, pointwise positivity of
the denominator and lower interval endpoint, and eventual resolution of the
prime logarithm mesh. -/
theorem hasDensity_one_of_harmonic_prob_and_occupancy_error
    (C N K B : ℕ → ℕ)
    (hK : ∀ s, 0 < K s) (hC : ∀ s, 0 < C s)
    (hprob : Tendsto
      (fun s ↦ HarmonicProb.prob (Finset.Ioc (C s) (N s))
        (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ B s))
      atTop (nhds 1))
    (herror : Tendsto
      (fun s ↦ 2 * ∑ i : ↥(Finset.Ioc (C s) (N s)),
        |PrimeBlocks.logBlockOccupancy (K s) i.1 - 1 / (i.1 : ℝ)|)
      atTop (nhds 0))
    (hresolution : ∀ᶠ s : ℕ in atTop,
      2 * (B s : ℝ) / (K s : ℝ) < Real.log 2) :
    {n : ℕ | CRTClose.HasCloseDivisors n}.HasDensity 1 := by
  apply Erdos144.hasDensity_one_of_approximate_subsets
  intro ε hε
  have hprobEventually : ∀ᶠ s : ℕ in atTop,
      1 - ε / 2 <
        HarmonicProb.prob (Finset.Ioc (C s) (N s))
          (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ B s) :=
    (tendsto_order.1 hprob).1 (1 - ε / 2) (by linarith)
  have herrorEventually : ∀ᶠ s : ℕ in atTop,
      2 * ∑ i : ↥(Finset.Ioc (C s) (N s)),
          |PrimeBlocks.logBlockOccupancy (K s) i.1 - 1 / (i.1 : ℝ)| <
        ε / 2 :=
    (tendsto_order.1 herror).2 (ε / 2) (by linarith)
  have hscale : ∀ᶠ s : ℕ in atTop,
      1 - ε / 2 <
          HarmonicProb.prob (Finset.Ioc (C s) (N s))
            (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ B s) ∧
        2 * ∑ i : ↥(Finset.Ioc (C s) (N s)),
            |PrimeBlocks.logBlockOccupancy (K s) i.1 - 1 / (i.1 : ℝ)| <
          ε / 2 ∧
        2 * (B s : ℝ) / (K s : ℝ) < Real.log 2 := by
    filter_upwards [hprobEventually, herrorEventually, hresolution] with s hsP hsE hsR
    exact ⟨hsP, hsE, hsR⟩
  obtain ⟨s, hsP, hsE, hsR⟩ := hscale.exists
  obtain ⟨A, d, hAsub, hAdensity, hd⟩ :=
    PrimeTransfer.exists_logInterval_primeCRT_subset_density
      (K s) (C s) (N s) (B s) (hK s) (hC s) hsR
  rw [TransferBridge.harmonicSubtypeGoodMass_eq_prob] at hd
  refine ⟨A, d, hAsub, hAdensity, ?_⟩
  linarith

end

end Erdos144.FinalTransfer
