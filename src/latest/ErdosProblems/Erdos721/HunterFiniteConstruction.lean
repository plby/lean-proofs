/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterProgressions

/-!
# Abstract finite Hunter construction

This theorem assembles the two Haar union bounds, the explicit binomial
Fourier cutoff, the shell-label union bound, and the deterministic annulus
argument.  All remaining work after this file is numerical specialization.
-/

namespace Erdos721.HunterFiniteConstruction

open Set
open scoped ENNReal

open HunterTorus HunterAnnulus HunterCenters HunterDistributedCenters
  HunterSeparatedCenters HunterDiophantine HunterFourierCutoff HunterKernel
  HunterColoring HunterProgressions

/-- Existence of one red set which is 3-AP-free and meets every progression
of length `2L-1`, under the explicit finite inequalities used in Hunter's
construction. -/
theorem exists_hunter_badSet
    {D H R Y S Q K N L : ℕ}
    {phaseRadius cutoffRadius epsilon delta q rhoOuter tau error : ℝ}
    (hphase0 : 0 ≤ phaseRadius) (hphaseHalf : 2 * phaseRadius ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdeltaPeriod : 2 * delta ≤ 1)
    (hQ : 2 ≤ Q) (hmesh : (Q : ℝ)⁻¹ ≤ phaseRadius)
    (hcenterSmall :
      (Fintype.card (HunterDistributedCenters.PhaseRequest D H R Q) * Y : ℕ) *
          (1 - ENNReal.ofReal (2 * phaseRadius) ^ R) ^ S +
        (Y * S) ^ 3 * ENNReal.ofReal (2 * delta) ^ D < 1)
    (hepsilon0 : 0 ≤ epsilon) (hepsilonPeriod : 2 * epsilon ≤ 1)
    (htau0 : 0 ≤ tau) (htauPeriod : 2 * tau ≤ 1)
    (hdirectionSmall :
      (N * ((2 * H + 1) ^ D) ^ R : ℕ) *
          ENNReal.ofReal (2 * epsilon) ^ R +
        N * ENNReal.ofReal (2 * tau) ^ D < 1)
    (hcutoff0 : 0 ≤ cutoffRadius)
    (hdecay : 2 * (2 * H + 1) ^ D *
      Real.exp (-4 * H * cutoffRadius ^ 2) ≤ 1)
    (hepsilon : 0 < epsilon)
    (hlarge : (2 * (2 * H + 1) ^ D : ℝ) *
      (2 * epsilon)⁻¹ ^ 2 < (L : ℝ) ^ 2)
    (hq : 0 < q)
    (herror : 2 * Real.sqrt R * phaseRadius +
      Real.sqrt D * cutoffRadius ≤ error)
    (herrorShell : error < (K : ℝ) * q)
    (herrorHalf : error < 1 / 2)
    (hL : 2 ≤ L) (hK : 0 < K)
    (hlabelSmall : (N ^ 2 : ℕ) *
      (1 - (K : ℝ≥0∞)⁻¹) ^ Y < 1)
    (hshell : ∀ k : Fin K,
      ((k.val + 1 : ℕ) : ℝ) * q ≤ rhoOuter)
    (houter : ∀ k : Fin K,
      2 * (k.val : ℝ) * q + q ≤ 1 / 4)
    (hfourrho : 4 * rhoOuter ≤ delta)
    (hdeltaHalf : delta ≤ 1 / 2)
    (hfourrhoHalf : 4 * rhoOuter < 1 / 2)
    (htauShell : Real.sqrt q / 2 ≤ tau)
    (htauHalf : tau ≤ 1 / 2) :
    ∃ red : ℕ → Prop,
      ThreeAPFreeBelow N red ∧ HitsEveryAP N (2 * L - 1) red := by
  obtain ⟨x, hdist, hsep⟩ :=
    exists_phaseDistributed_affinelySeparated
      hphase0 hphaseHalf hdelta0 hdeltaPeriod hQ hmesh hcenterSmall
  obtain ⟨theta, hres, hsmall⟩ :=
    exists_goodDirection hepsilon0 hepsilonPeriod htau0 htauPeriod
      hdirectionSmall
  let F : FourierCutoff D H cutoffRadius
      (2 * (2 * H + 1) ^ D) :=
    binomialFourierCutoff D H cutoffRadius hcutoff0 hdecay
  obtain ⟨label, hhit⟩ := exists_labeling_hitsEveryAP
    hdist hres F hcutoff0 hepsilon hlarge hq herror herrorShell
      herrorHalf hL hK hlabelSmall
  refine ⟨IsHunterRed q theta x label, ?_, hhit⟩
  exact threeAPFreeBelow_of_geometric_data hq hshell houter hsep
    hfourrho hdeltaHalf hfourrhoHalf htauShell htauHalf hsmall

end Erdos721.HunterFiniteConstruction
