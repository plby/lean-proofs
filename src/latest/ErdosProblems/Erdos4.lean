/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4.ResidualPrimeFiberTail
import ErdosProblems.Erdos4.SingletonAsymptotics
import ErdosProblems.Erdos4.DirectMoments
import ErdosProblems.Erdos4.PrimitiveProfile
import ErdosProblems.Erdos4.SliceBounds
import ErdosProblems.Erdos4.DoubleMeanSquare
import ErdosProblems.Erdos4.PrimeMeanSquare
import ErdosProblems.Erdos4.UnitFourier
import ErdosProblems.Erdos4.CoefficientMass
import ErdosProblems.Erdos4.ProductProjectionComparison
import ErdosProblems.Erdos4.CutoffSimplex
import ErdosProblems.Erdos4.ReciprocalTail
import ErdosProblems.Erdos4.WeightedHarmonic
import ErdosProblems.Erdos4.EulerDensity
import ErdosProblems.Erdos4.ProductPrimeMeanSquare
import ErdosProblems.Erdos4.AnchoredFourierAverage
import ErdosProblems.Erdos4.AffineResidueMean
import ErdosProblems.Erdos4.ExposureBounds
import ErdosProblems.Erdos4.CoveringError
import ErdosProblems.Erdos4.ProbabilityFallback
import ErdosProblems.Erdos4.PrimeExposure
import ErdosProblems.Erdos4.OuterCover
import ErdosProblems.Erdos4.OuterThreshold
import ErdosProblems.Erdos4.FGKMTAllEndpoints

/-!
# Erdős Problem 4: large prime gaps at the FGKMT18 scale

Sieve, residue-covering, and variational estimates from the large-prime-gap development.

The fixed-cutoff candidate additionally has checked direct covering-moment
inequalities, an explicit monotone profile with arbitrary pointwise gain,
and exact product orthogonality and Parseval identities. A weak
prime-supported large sieve is proved from the optimized square majorant
and elementary primitive-character cancellation. The actual product-cutoff
divisor coefficients now have checked slice bounds and a uniform
product-character Fourier estimate, with exact conductor support at `R^2`
and the principal coefficient identified as a restricted product norm.
An exact coefficient-energy tail bound is also available for controlling
the occupied primes' reciprocal mass in the principal-term argument.
The ideal projection action, its energy-sensitive comparison with the
true principal projection, and the uniform weighted fixed-modulus harmonic
transfer are proved. Squarefree completions now give the actual arithmetic
fiber lower bound, with frozen-prime exclusions controlled by coefficient
energy. The resulting principal deletion forms have arbitrarily large
normalized gain, with all fixed parameters chosen before the outer cutoff
tends to infinity, and the lower prime cutoff may then be freely enlarged.
Product-character Fourier inversion and injective encoding by primitive
conductors are checked, as is the double prime mean-square bound for the
actual Fourier coefficients. The nonnegative anchored-ratio weights now
have an exact principal-plus-error source-average identity and the
corresponding mean-square discrepancy bound. The actual affine weights
have an exact divisor-indicator expansion, a finite CRT normalization
estimate, and a fixed-cutoff probability normalization with uniform
`t⁻³⁰` atom bounds at `R = t⁵`, `Y ≥ t⁵⁰`. Their prime source averages
obey the real mean-square estimate, and the total-exposure lower bound
and exceptional-target inequality are proved. The preliminary random
residue sieve has exact conditional survival probabilities and joint
survival asymptotics uniform over moving prime sets and bounded tuples.
The tuple intersection and small-atom collision estimates supply all
three conditional moments used by the direct covering inequality, and
an explicit conditional noncoverage bound with survival, exposure,
and collision error terms is checked. Actual two-stage choices, the
exceptional-target budget, zero-residue initial sieve, and smooth-number
cleanup now give a full finite interval cover with a primorial modulus
bound. An integer outer ray has checked cutoff ordering, prime supply,
two-sided sieve density, and uniform random-sieve accuracy. The entire
unfiltered smooth set has a uniform Rankin bound. Actual prime exposure
holds outside an explicitly bounded exceptional set.

The exposure is instantiated on the outer ray and the numerical cleanup
budget is closed. A uniform comparison with the original iterated-log
threshold completes the passage from residue covers to indexed prime gaps.

The theorem `Erdos4.erdos4` below is unconditional for every real `C > 0`.
`Erdos4/Verification.lean` checks its exact statement and kernel axiom
dependencies. No claim of historical novelty is asserted here.

The growing-dimension construction also proves the full FGKMT18 bound.
`Erdos4.fgkmt18` supplies a consecutive-prime gap with right endpoint at
most `X`, for every sufficiently large real `X`, and with size at least
an absolute positive constant times `log X * log₂ X * log₄ X / log₃ X`.
Its arithmetic input, disjoint covering rounds, smooth-number cleanup,
and endpoint comparison are proved in the supporting `FGKMT` modules.
`Erdos4/FGKMTVerification.lean` checks the explicit statement and kernel
dependencies of this stronger theorem as well as its intermediate results.
-/

namespace Erdos4

/-- Erdős's original arbitrary-constant large-prime-gap assertion. -/
theorem erdos4 (C : ℝ) (hC : 0 < C) : Erdos4For C := by
  classical
  obtain ⟨a, hcovers⟩ := OuterCover.exists_arbitrary_length_covers
  obtain ⟨D, hDlarge⟩ := exists_nat_gt (OuterThreshold.coefficient C a)
  have hD : 1 ≤ D := by
    have hh : (0 : ℝ) < D := (OuterThreshold.coefficient_nonneg hC.le a).trans_lt hDlarge
    exact_mod_cast hh
  obtain ⟨N₀, hstart⟩ := OuterThreshold.exists_log_start
  apply erdos4For_of_forall_exists_ge C
  intro N
  let N' := max N N₀
  let L := max 2 (Nat.nth Nat.Prime N')
  let B := max L 1 + 1
  have hB : 0 < B := by dsimp [B]; omega
  obtain ⟨r, hr, ⟨cover, hmod⟩, hend⟩ :=
    ((Filter.eventually_ge_atTop (max a 4)).and
      ((hcovers D hD).and (OuterThreshold.eventually_log_endpoint a B hB))).exists
  have hra : a ≤ r := (le_max_left a 4).trans hr
  have hr4 : 4 ≤ r := (le_max_right a 4).trans hr
  obtain ⟨x, hLx, hxupper, hcomp⟩ := cover.exists_composite_block_ge L
  have hx2 : 2 ≤ x := (le_max_left 2 _).trans hLx
  have hxN : Nat.nth Nat.Prime N' ≤ x := (le_max_right 2 _).trans hLx
  obtain ⟨n, hNn, hnx, hgap⟩ :=
    exists_index_gap_gt_of_composite_block N' x (OuterRay.length a D r) hx2 hxN hcomp
  have hN₀n : N₀ ≤ n := (le_max_right N N₀).trans hNn
  have hlogs := hstart n hN₀n
  have hnupper : n ≤ B * primorial (OuterRay.frontier a r) :=
    (hnx.trans_lt hxupper).le.trans (Nat.mul_le_mul_left B hmod)
  have hthreshold := OuterThreshold.threshold_le hC.le hra hr4
    hlogs.2.1 hlogs.2.2.1 hlogs.2.2.2 (hend n hlogs.1 hnupper)
  have hscale : 0 < (OuterRay.frontier a r : ℝ) * SmoothParameters.core r * r := by
    have hX : (0 : ℝ) < OuterRay.frontier a r := by exact_mod_cast OuterRay.frontier_pos a r
    have hV : (0 : ℝ) < SmoothParameters.core r := by exact_mod_cast SmoothParameters.core_pos r
    have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    positivity
  have hlength : (D : ℝ) * ((OuterRay.frontier a r : ℝ) * SmoothParameters.core r * r) =
      (OuterRay.length a D r : ℝ) := by
    rw [OuterRay.length]
    push_cast
    ring
  have hlt : threshold C n < (OuterRay.length a D r : ℝ) :=
    (hthreshold.trans_lt (mul_lt_mul_of_pos_right hDlarge hscale)).trans_eq hlength
  exact ⟨n, (le_max_left N N₀).trans hNn, hlt.trans hgap⟩

/-- The exact large-prime-gap statement with its proposition expanded. -/
theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
      C * Real.log (Real.log n) * Real.log (Real.log (Real.log (Real.log n))) /
        (Real.log (Real.log (Real.log n))) ^ 2 * Real.log n}.Infinite := by
  simpa [Erdos4For] using erdos4 C hC

/-- The full FGKMT18 scale, below every sufficiently large real endpoint. -/
theorem fgkmt18 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in Filter.atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        c * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  simpa only [FGKMT.gapScale, FGKMT.realOuterScale] using FGKMT.exists_all_endpoint_gaps

/-- An explicit-threshold form of the all-endpoint FGKMT18 theorem. -/
theorem fgkmt18_forall_ge :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        c * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hlarge⟩ := fgkmt18
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hlarge
  exact ⟨c, X₀, hc, hX₀⟩

end Erdos4
