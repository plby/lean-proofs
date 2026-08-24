/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeRandomAssembly
import ErdosProblems.Erdos360.CoarseOrdinaryCertificate

/-!
# Constant-loss ordinary growth for one CFP random pool

This file specializes the checked coarse modular phase theorem to the exact
parameters of a random pool.  The absolute loss is harmless for the final
order-of-growth theorem: one fixes a sufficiently large absolute `ell`
(rather than the temporarily attempted value `4`).

No analytic assertion is assumed here.  Every numerical condition which
the eventual prime/divisor ledger must establish is visible in the theorem
statement.
-/

namespace Erdos360

open scoped BigOperators

/-- Number of coarse modular phases exposed inside one pool. -/
def primePoolCoarsePhaseCount (z ell : ℕ) : ℕ :=
  primeRandomPoolSize z ell / 8

/-- Residue gain sufficient for the requested ordinary target once the
balanced split retains one quarter of the pool as pivots. -/
def primePoolCoarseResidueGain (y z ell d : ℕ) : ℕ :=
  primeRandomNzero y z ell d ⌈/⌉ (primeRandomPoolSize z ell / 4)

/-- A source-facing, general-`ell` local certificate.  In the intended
application `ell` is a fixed absolute constant at least a few thousand;
`hmod` records the exact constant-loss requirement instead of concealing it
behind an asymptotic notation. -/
theorem exists_primePoolOrdinaryGrowthCertificate_of_coarse_numerics
    {y z ell d : ℕ} {P : Finset ℕ}
    (hcard : P.card = primeRandomPoolSize z ell)
    (hrange : P ⊆ Finset.Icc (y / d + 1) (2 * y / d))
    (hdiverse :
      DiverseSampling.DiverseNat P (primeRandomPoolDiversity y ell))
    (hprobability :
      (2 : ℝ) * (((2 * y / d : ℕ) : ℝ) + 1) *
        Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) < 1)
    (hscale : 2 * (2 * y / d) ≤
      (primeRandomPoolDiversity y ell / 4 + 1) *
        (primeRandomPoolSize z ell / 4))
    (hlog : 4 * (Nat.log 2 (2 * y / d) + 1) ^ 2 ≤
      primePoolCoarsePhaseCount z ell)
    (hhalf : 2 * primePoolCoarsePhaseCount z ell ≤
      primeRandomPoolSize z ell / 4)
    (hmod : 64 * primePoolCoarseResidueGain y z ell d ≤ y / d + 1)
    (hquad : 64 * primePoolCoarseResidueGain y z ell d ≤
      primePoolCoarsePhaseCount z ell *
        (primeRandomPoolSize z ell / 4))
    (hpool : 0 < primeRandomPoolSize z ell / 4)
    (hdiversity : 0 < primeRandomPoolDiversity y ell)
    (hsum : primeRandomPoolSize z ell * (2 * y / d) ≤
      primeRandomDiameter y z ell d) :
    Nonempty (CFPOrdinaryGrowthCertificate P
      (primeRandomNzero y z ell d)
      (primeRandomDiameter y z ell d)) := by
  apply exists_CFPOrdinaryGrowthCertificate_of_diverse_shortInterval
    (lo := y / d + 1) (hi := 2 * y / d + 1)
    (K := primeRandomPoolDiversity y ell)
    (phaseCount := primePoolCoarsePhaseCount z ell)
    (residueGain := primePoolCoarseResidueGain y z ell d)
    (nzero := primeRandomNzero y z ell d)
    (diameter := primeRandomDiameter y z ell d)
  · exact Nat.zero_lt_succ _
  · intro a ha
    have haI := Finset.mem_Icc.mp (hrange ha)
    exact Finset.mem_Ico.mpr ⟨haI.1, by omega⟩
  · exact hdiverse
  · simpa using hprobability
  · have hdiv := Nat.add_div_le_div_add_div_add_one y y d
    have htwo : 2 * y / d ≤ y / d + y / d + 1 := by
      simpa [two_mul] using hdiv
    omega
  · simpa [hcard] using hscale
  · simpa using hlog
  · simpa [hcard] using hhalf
  · exact hmod
  · simpa [hcard] using hquad
  · have hceil : primeRandomNzero y z ell d ≤
        (primeRandomPoolSize z ell / 4) *
          primePoolCoarseResidueGain y z ell d := by
      exact le_smul_ceilDiv hpool
    rw [hcard]
    exact hceil.trans (Nat.le_add_left _ _)
  · exact hdiversity
  · simpa [hcard] using hsum

/-- The corrected global ordinary-growth principle.  Unlike the earlier
range-free formulation, it is conditional on the explicit finite numerical
ledger and is therefore both true and directly usable by the random-source
assembly. -/
theorem cfpPrimePoolOrdinaryGrowthPrinciple
    (ell : ℕ) : CFPPrimePoolOrdinaryGrowthPrinciple ell := by
  intro y z d P hnum hcard hrange hdiverse
  apply exists_primePoolOrdinaryGrowthCertificate_of_coarse_numerics
    hcard hrange hdiverse hnum.probability hnum.scale hnum.log
  · unfold primePoolCoarsePhaseCount
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    have hmul := Nat.div_mul_le_self (primeRandomPoolSize z ell) 8
    omega
  · simpa [primePoolCoarseResidueGain] using hnum.modulus
  · simpa [primePoolCoarsePhaseCount, primePoolCoarseResidueGain] using
      hnum.quadratic
  · exact hnum.pool_pos
  · exact hnum.diversity_pos
  · exact hnum.sum

end Erdos360

#print axioms Erdos360.exists_primePoolOrdinaryGrowthCertificate_of_coarse_numerics
#print axioms Erdos360.cfpPrimePoolOrdinaryGrowthPrinciple
