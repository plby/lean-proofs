/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block00
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block01
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block02
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block03
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block04
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block05
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block06
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block07
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block08
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block09
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block10
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block11
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block12
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block13
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block14
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block15
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block16
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block17
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block18
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block19
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block20
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block21
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block22
import ErdosProblems.Erdos232.CertificateCancellationBlocks.Block23

namespace Erdos232

theorem congruenceContribution_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ i : Fin 24, ∀ c ∈ atomCongruenceWeights i,
      maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * congruenceContributionReal s) = 0 := by
  simp only [congruenceContributionReal, atomCongruenceContributionInt,
    Int.cast_add, mul_add, Finset.sum_add_distrib]
  have h00 := congruenceBlock00_expectation_zero a
    (fun c hc => hmass (0 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h01 := congruenceBlock01_expectation_zero a
    (fun c hc => hmass (1 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h02 := congruenceBlock02_expectation_zero a
    (fun c hc => hmass (2 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h03 := congruenceBlock03_expectation_zero a
    (fun c hc => hmass (3 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h04 := congruenceBlock04_expectation_zero a
    (fun c hc => hmass (4 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h05 := congruenceBlock05_expectation_zero a
    (fun c hc => hmass (5 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h06 := congruenceBlock06_expectation_zero a
    (fun c hc => hmass (6 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h07 := congruenceBlock07_expectation_zero a
    (fun c hc => hmass (7 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h08 := congruenceBlock08_expectation_zero a
    (fun c hc => hmass (8 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h09 := congruenceBlock09_expectation_zero a
    (fun c hc => hmass (9 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h10 := congruenceBlock10_expectation_zero a
    (fun c hc => hmass (10 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h11 := congruenceBlock11_expectation_zero a
    (fun c hc => hmass (11 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h12 := congruenceBlock12_expectation_zero a
    (fun c hc => hmass (12 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h13 := congruenceBlock13_expectation_zero a
    (fun c hc => hmass (13 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h14 := congruenceBlock14_expectation_zero a
    (fun c hc => hmass (14 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h15 := congruenceBlock15_expectation_zero a
    (fun c hc => hmass (15 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h16 := congruenceBlock16_expectation_zero a
    (fun c hc => hmass (16 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h17 := congruenceBlock17_expectation_zero a
    (fun c hc => hmass (17 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h18 := congruenceBlock18_expectation_zero a
    (fun c hc => hmass (18 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h19 := congruenceBlock19_expectation_zero a
    (fun c hc => hmass (19 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h20 := congruenceBlock20_expectation_zero a
    (fun c hc => hmass (20 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h21 := congruenceBlock21_expectation_zero a
    (fun c hc => hmass (21 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h22 := congruenceBlock22_expectation_zero a
    (fun c hc => hmass (22 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  have h23 := congruenceBlock23_expectation_zero a
    (fun c hc => hmass (23 : Fin 24) c (by
      simpa [atomCongruenceWeights] using hc))
  linear_combination h00 + h01 + h02 + h03 + h04 + h05 + h06 + h07 + h08 + h09 + h10 + h11 + h12 + h13 + h14 + h15 + h16 + h17 + h18 + h19 + h20 + h21 + h22 + h23

end Erdos232
