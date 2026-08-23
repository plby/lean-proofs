/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Erdos469
import ErdosProblems.Erdos6.LargeKCandidate
import ErdosProblems.Erdos6.GenericS1
import ErdosProblems.Erdos6.GenericS2Restricted
import ErdosProblems.Erdos6.LargeRestrictedGKernelLimit
import BoundedGaps.Maynard.MaynardWeights
import BoundedGaps.Maynard.MaynardS1CrossCorrection
import BoundedGaps.Maynard.MaynardS1CrossCorrectionBound
import BoundedGaps.Maynard.ImprovedGPY.CongruenceCount
import BoundedGaps.Maynard.ImprovedGPY.MainTerm
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Erdős Problem 4: base development

This file uses exactly the statement from `google-deepmind/formal-conjectures`:
the prime index is zero-based (`Nat.nth Nat.Prime 0 = 2`) and every logarithm
is the real logarithm after coercion from `ℕ`.

Progress log (2026-08-15):
* Phase 1 is complete in `tex/4.tex`: it reconstructs the Maynard--FGKMT
  large-gap proof and records the complete dependency/Leanization audit.
* Phase 2: the exact target, finite-probability selection, residue-cover CRT,
  prime-gap, finite-to-infinite endpoints, exact doubled-Selberg finite algebra,
  an explicit unbounded Maynard variational family, and the separated tensor
  coefficient normalization with an explicit aggregate CRT-error envelope are
  formalized below.  The first compatible quadratic has been transported to the
  generic finite-tuple moment theorem and proved to converge to the exact
  variational integral.  Smooth companion cofactors are absorbed exactly; more
  importantly, the radius-two companion support is a singleton, its quadratic
  is exactly one, and its entire CRT endpoint envelope is proved to be `o` of
  the ordinary Maynard scale.  The scaled auxiliary multiplier `W*q` now has
  an exact positive normalization, its raw residue classes partition that
  mass, and every coordinate preimage gives a certified lower contribution
  to the class hitting a residual prime.  The remaining work is the prime-`q`
  coverage asymptotic and the final survivor/fresh-prime assembly.
* Fresh audit (2026-08-16): `GeneralCrt.lean` now proves the exact lcm-period
  normalization for arbitrary cross-family overlaps, and
  `GeneralPinned.lean` proves its pinned prime-variable analogue, reducedness
  of the canonical residue, the exact pinned main/error decomposition, and
  the pointwise maximal-progression-discrepancy bound without any
  cross-family coprimality assumption.  The unresolved analytic boundary is
  now exact: (i) the Maier--Pomerance shifted smooth-number estimate needed
  to show `smoothResidualException` has `o(x / log x)` cardinality, and
  (ii) the uniform evaluation of `doubledSelbergCoordinateLcmKernel` and
  `pinnedGeneralArithmeticKernel` (Maynard's auxiliary `a_{i,j}` expansion)
  needed for normalization and coverage.  Repository-wide searches find
  unconditional Bombieri--Vinogradov and PNT inputs, but no theorem stating
  either of these two estimates.
* Continued audit (2026-08-16): `GeneralTau.lean` closes the elementary
  multiplicity and distribution part of item (ii).  It embeds every lcm
  fiber into four functions valued in the divisor set, proves the sharp-enough
  bound `(2^(4*|H|))^omega(M)`, proves every occurring lcm is squarefree, and
  feeds the resulting coefficient-mass envelope into the repository's
  explicit tau-weighted Bombieri--Vinogradov theorem.  Thus the remaining
  part of (ii) is specifically the main-term `a_{i,j}` Euler-product
  evaluation and its uniform coverage lower bound, not the progression-error
  estimate.  The generalized CRT converse is also closed: for positive
  moduli, solvability is equivalent to the full family of pairwise gcd
  congruences, including the pinned and unpinned doubled systems.  Hence no
  CRT existence assumption remains hidden in the proposed `a_{i,j}`
  translation.
* Resumed audit (2026-08-16): `SmoothParameters.lean` now closes item (i)
  on an explicit unbounded dyadic ray using the stronger unshifted Rankin
  majorant; no Maier--Pomerance input remains necessary for the smooth
  exception used by this development.  `GeneralSingularSeries.lean` defines
  the actual local forbidden-residue union for the doubled affine system,
  proves its exact cardinality below the pre-sieve cutoff, identifies every
  rough multiplicity drop with a divisor of the affine exceptional modulus,
  and proves the exact inverse-factor powerset expansion together with its
  first Bonferroni lower bound.  A separate no-go calculation was also
  checked: deleting every first/companion cross collision at the coefficient
  level leaves an uncancelled `phi(P_y)/P_y` and loses the full `log y`
  required by the target.  The remaining analytic boundary is therefore
  precisely Maynard's uniform singular-series/main-Euler-product evaluation
  for the normalization and pinned coverage kernels, followed by the
  residual-prime-fibre sieve asymptotic and finite parameter assembly.
* Latest source audit (2026-08-16): the unpinned and pinned decomposition
  modules now expose the genuine kernels literally as, respectively, a
  product or sum of products of ordinary Maynard quadratic faces plus the
  compatible-amplification correction minus the incompatible-removal
  correction.  These composed identities type-check, so no CRT or tensor
  factorization remains implicit.  The completed Erdős 851 finite beta-sieve
  is a reusable route toward an upper bound for the residual prime fibre,
  but it has no existing specialization to the asymmetric prime/affine
  sequence `p * (m*p - 1)`.  The source-level analytic gap is therefore the
  uniform Euler-product evaluation of the explicit normalization corrections
  into the `q`-dependent singular factor and the corresponding pinned lower
  estimate after inverse-factor expansion (Maynard 2016, Lemmas 6 and 7,
  equations (6.22)--(6.30)), together
  with that prime-fibre specialization and the final parameter assembly.
* Residual-fibre update (2026-08-16):
  `ResidualPrimeFiberSieve.lean`, `ResidualPrimeFiberBeta.lean`, and
  `ResidualPrimeFiberMertens.lean` now carry out that missing pointwise
  specialization.  They construct the exact reduced affine residue, reduce
  every remainder to the two endpoint Bombieri--Vinogradov sums, prove the
  dimension-one product hypothesis for the density `1 / (p - 1)`, build the
  filtered Rosser cutoff, and conclude a finite cardinality upper bound with
  both BV losses displayed.  The local Euler product is then bounded by
  `C * (m / Nat.totient m) / log y`, using a direct Mertens estimate and an
  exact extraction of the primes dividing `m`.
  `ResidualPrimeFiberTail.lean` proves the sharp multiplicative-interval
  estimate `∑ 1 / φ(m) ≤ 4 * (1 + log (B / A))`, sums the complete principal
  term over all even cofactors in the interval, and leaves the two endpoint
  BV losses as an explicit finite sum.  Thus only elementary parameter
  absorption of that displayed error sum remains on the residual branch.
  The principal analytic boundary is still the uniform normalization and
  pinned singular-series evaluation described in the preceding item, then
  finite parameter assembly.
-/

open Filter Real Asymptotics
open scoped BigOperators Asymptotics

namespace Erdos4

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The exact set of prime indices occurring in Erdős Problem 4. -/
def Erdos4For (C : ℝ) : Prop :=
  {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
    C * log (log n) * log (log (log (log n))) /
      (log (log (log n))) ^ 2 * log n}.Infinite

/-- The exact right-hand side of the prime-gap inequality. -/
noncomputable def threshold (C : ℝ) (n : ℕ) : ℝ :=
  C * log (log n) * log (log (log (log n))) /
    (log (log (log n))) ^ 2 * log n

/-- The stronger FGKMT scale, with only one factor of the third iterated
logarithm in the denominator. -/
noncomputable def strongThreshold (c : ℝ) (n : ℕ) : ℝ :=
  c * log (log n) * log (log (log (log n))) /
    log (log (log n)) * log n

/-- Indexed form of the Ford--Green--Konyagin--Maynard--Tao conclusion. -/
def StrongErdos4For (c : ℝ) : Prop :=
  {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
    strongThreshold c n}.Infinite

/-- Prime number theorem in the primorial form used by the CRT construction. -/
theorem log_primorial_natCast_isEquivalent :
    (fun n : ℕ => Real.log (primorial n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  simpa [Chebyshev.theta_eq_log_primorial] using
    BoundedGaps.PrimeNumberTheorem.chebyshevTheta_natCast_isEquivalent

/-- A convenient eventual explicit consequence of the primorial PNT. -/
theorem eventually_log_primorial_lt_two_mul :
    ∀ᶠ x : ℕ in atTop,
      Real.log (primorial x : ℝ) < 2 * (x : ℝ) := by
  have hne : ∀ᶠ x : ℕ in atTop, (x : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact_mod_cast (show x ≠ 0 by omega)
  have hratio : Tendsto
      (fun x : ℕ => Real.log (primorial x : ℝ) / (x : ℝ))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hne).mp
      log_primorial_natCast_isEquivalent
  have hlt : ∀ᶠ x : ℕ in atTop,
      Real.log (primorial x : ℝ) / (x : ℝ) < 2 :=
    ((tendsto_order.1 hratio).2 2 (by norm_num))
  filter_upwards [hlt, eventually_ge_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  exact (div_lt_iff₀ hxpos).mp hx

/-- The product of any subset of the primes through `x` divides, and hence is
at most, the `x`th primorial. -/
theorem primeProduct_le_primorial {P : Finset ℕ} {x : ℕ}
    (hP : P ⊆ Nat.primesLE x) :
    (∏ p ∈ P, p) ≤ primorial x := by
  apply Nat.le_of_dvd (primorial_pos x)
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset P (Nat.primesLE x) id hP

/-! ## Arbitrary-dimensional admissible tuples -/

/-- The residue-cardinality formulation of admissibility used in Maynard's
sieve. -/
def AdmissibleShifts (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (H.image fun h => h % p).card < p

/-- A simple admissible `k`-tuple: distinct multiples of the `k`-primorial. -/
def primorialShifts (k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun i => primorial k * i

theorem card_primorialShifts (k : ℕ) :
    (primorialShifts k).card = k := by
  rw [primorialShifts, Finset.card_image_iff.mpr]
  · simp
  · intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left (primorial_pos k) hab

/-- The construction gives admissible tuples in every finite dimension. -/
theorem primorialShifts_admissible (k : ℕ) :
    AdmissibleShifts (primorialShifts k) := by
  intro p hp
  by_cases hpk : p ≤ k
  · have hpPrimorial : p ∣ primorial k := hp.dvd_primorial_iff.mpr hpk
    have hsubset :
        (primorialShifts k).image (fun h => h % p) ⊆ {0} := by
      intro r hr
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hh
      simp only [Finset.mem_singleton]
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpPrimorial i)
    calc
      ((primorialShifts k).image (fun h => h % p)).card ≤
          ({0} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 1 := by simp
      _ < p := hp.one_lt
  · have hkp : k < p := by omega
    calc
      ((primorialShifts k).image (fun h => h % p)).card ≤
          (primorialShifts k).card := Finset.card_image_le
      _ = k := card_primorialShifts k
      _ < p := hkp

/-! ## Fixed large-dimensional Maynard variational input -/

/-- The checked large-dimensional test function already developed for
Erdős Problem 6 supplies more variational mass than the covering argument
needs.  Its dimension and decay parameter are fixed absolute constants; this
is enough because the FGKMT scale has one fewer factor of the third iterated
logarithm than the scale in Erdős's question. -/
theorem large_maynard_candidate_ratio_gt_twelve :
    12 < BoundedGaps.Maynard.maynardRatio
      Erdos6.Maynard.largeK Erdos6.Maynard.largeCandidate :=
  Erdos6.Maynard.maynardRatio_largeCandidate_gt_twelve

/-- The same test function satisfies all support and integrability hypotheses
of the Maynard variational problem. -/
theorem large_maynard_candidate_admissible :
    BoundedGaps.Maynard.MaynardAdmissible
      Erdos6.Maynard.largeK Erdos6.Maynard.largeCandidate :=
  Erdos6.Maynard.largeCandidate_admissible

/-! ### A variable-dimensional variational family

The fixed candidate above is useful for checking the analytic interface, but
Erdős's quantifier over every constant needs variational quotients of
arbitrary size.  We therefore generalize the same inverse-affine product
construction to a dimension `K` and decay parameter `A`. -/

namespace VariableMaynard

open MeasureTheory Set
open scoped Interval

/-- The one-dimensional inverse-affine factor. -/
noncomputable def factor (A u : ℝ) : ℝ := (1 + A * u)⁻¹

/-- The untruncated product factor in dimension `K`. -/
noncomputable def product (K : ℕ) (A : ℝ) (t : Fin K → ℝ) : ℝ :=
  ∏ i, factor A ((K : ℝ) * t i)

/-- The product factor, extended by zero outside Maynard's simplex. -/
noncomputable def candidate (K : ℕ) (A : ℝ) (t : Fin K → ℝ) : ℝ := by
  classical
  exact if t ∈ BoundedGaps.Maynard.maynardSimplex K then
    product K A t else 0

theorem factor_pos {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    0 < factor A u := by
  unfold factor
  apply inv_pos.mpr
  nlinarith

theorem factor_nonneg {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    0 ≤ factor A u :=
  (factor_pos hA hu).le

theorem factor_le_one {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    factor A u ≤ 1 := by
  rw [factor, inv_le_one₀]
  · nlinarith
  · nlinarith

theorem measurable_factor (A : ℝ) : Measurable (factor A) := by
  unfold factor
  fun_prop

theorem measurable_product (K : ℕ) (A : ℝ) :
    Measurable (product K A) := by
  unfold product
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_factor A).comp
      (measurable_const.mul (measurable_pi_apply i))

theorem measurable_candidate (K : ℕ) (A : ℝ) :
    Measurable (candidate K A) := by
  classical
  unfold candidate
  exact Measurable.ite
    (BoundedGaps.Maynard.maynardSimplex_measurable (k := K))
    (measurable_product K A) measurable_const

theorem candidate_simplexSupported (K : ℕ) (A : ℝ) :
    BoundedGaps.Maynard.MaynardSimplexSupported K (candidate K A) := by
  classical
  intro t ht
  simp [candidate, ht]

theorem product_nonneg_of_mem_cube {K : ℕ} {A : ℝ} (hA : 0 < A)
    {t : Fin K → ℝ} (ht : t ∈ BoundedGaps.Maynard.maynardCube K) :
    0 ≤ product K A t := by
  unfold product
  exact Finset.prod_nonneg fun i _ =>
    factor_nonneg hA (mul_nonneg (Nat.cast_nonneg _)
      (ht i (Set.mem_univ i)).1)

theorem product_le_one_of_mem_cube {K : ℕ} {A : ℝ} (hA : 0 < A)
    {t : Fin K → ℝ} (ht : t ∈ BoundedGaps.Maynard.maynardCube K) :
    product K A t ≤ 1 := by
  unfold product
  calc
    ∏ i : Fin K, factor A ((K : ℝ) * t i) ≤
        ∏ _i : Fin K, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact factor_nonneg hA (mul_nonneg (Nat.cast_nonneg _)
          (ht i (Set.mem_univ i)).1)
      · intro i _
        exact factor_le_one hA (mul_nonneg (Nat.cast_nonneg _)
          (ht i (Set.mem_univ i)).1)
    _ = 1 := Finset.prod_const_one

theorem candidate_nonneg_of_mem_cube {K : ℕ} {A : ℝ} (hA : 0 < A)
    {t : Fin K → ℝ} (ht : t ∈ BoundedGaps.Maynard.maynardCube K) :
    0 ≤ candidate K A t := by
  classical
  unfold candidate
  split_ifs
  · exact product_nonneg_of_mem_cube hA ht
  · exact le_rfl

theorem candidate_le_one_of_mem_cube {K : ℕ} {A : ℝ} (hA : 0 < A)
    {t : Fin K → ℝ} (ht : t ∈ BoundedGaps.Maynard.maynardCube K) :
    candidate K A t ≤ 1 := by
  classical
  unfold candidate
  split_ifs
  · exact product_le_one_of_mem_cube hA ht
  · norm_num

theorem candidate_nonneg {K : ℕ} {A : ℝ} (hA : 0 < A)
    (t : Fin K → ℝ) : 0 ≤ candidate K A t := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex K
  · rw [candidate, if_pos ht]
    exact product_nonneg_of_mem_cube hA ht.1
  · simp [candidate, ht]

theorem candidate_le_one {K : ℕ} {A : ℝ} (hA : 0 < A)
    (t : Fin K → ℝ) : candidate K A t ≤ 1 := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex K
  · rw [candidate, if_pos ht]
    exact product_le_one_of_mem_cube hA ht.1
  · simp [candidate, ht]

theorem candidate_norm_le_one {K : ℕ} {A : ℝ} (hA : 0 < A)
    (t : Fin K → ℝ) : ‖candidate K A t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (candidate_nonneg hA t)]
  exact candidate_le_one hA t

theorem candidate_sq_integrableOn {K : ℕ} {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun t : Fin K → ℝ => candidate K A t ^ 2)
      (BoundedGaps.Maynard.maynardCube K) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCube K)
    (hs := BoundedGaps.Maynard.maynardCube_measurable K)
    (hsfinite := BoundedGaps.Maynard.maynardCube_measure_lt_top K)
    (f := fun t : Fin K → ℝ => candidate K A t ^ 2)
    ((measurable_candidate K A).pow_const 2) 1 ?_
  intro t _
  rw [norm_pow]
  simpa using pow_le_one₀ (n := 2) (norm_nonneg (candidate K A t))
    (candidate_norm_le_one hA t)

theorem measurable_insertCoordinate_left {K : ℕ} (m : Fin K)
    (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ) :
    Measurable (fun x : ℝ =>
      BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i = m
  · simp only [BoundedGaps.Maynard.maynardInsertCoordinate, dif_pos hi]
    exact measurable_id
  · simp [BoundedGaps.Maynard.maynardInsertCoordinate, hi]

theorem candidate_face_integrableOn {K : ℕ} {A : ℝ} (hA : 0 < A)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ) :
    IntegrableOn (fun x : ℝ => candidate K A
      (BoundedGaps.Maynard.maynardInsertCoordinate m x t))
      (Set.Icc 0 1) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := fun x : ℝ => candidate K A
      (BoundedGaps.Maynard.maynardInsertCoordinate m x t))
    ((measurable_candidate K A).comp (measurable_insertCoordinate_left m t))
    1 ?_
  intro x _
  exact candidate_norm_le_one hA _

noncomputable def faceJoint (K : ℕ) (A : ℝ) (m : Fin K) :
    ((BoundedGaps.Maynard.maynardFaceIndex K m → ℝ) × ℝ) → ℝ :=
  fun z => if z.2 ∈ Set.Icc (0 : ℝ) 1 then
    candidate K A
      (BoundedGaps.Maynard.maynardInsertCoordinate m z.2 z.1) else 0

theorem faceJoint_measurable (K : ℕ) (A : ℝ) (m : Fin K) :
    Measurable (faceJoint K A m) := by
  have hinsert : Measurable
      (fun z : (BoundedGaps.Maynard.maynardFaceIndex K m → ℝ) × ℝ =>
        BoundedGaps.Maynard.maynardInsertCoordinate m z.2 z.1) := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = m
    · simp only [BoundedGaps.Maynard.maynardInsertCoordinate, dif_pos hi]
      exact measurable_snd
    · let j : BoundedGaps.Maynard.maynardFaceIndex K m := ⟨i, hi⟩
      simpa [BoundedGaps.Maynard.maynardInsertCoordinate, hi, j,
        Function.comp_def] using
        ((measurable_pi_apply j).comp measurable_fst)
  unfold faceJoint
  apply Measurable.ite (measurableSet_Icc.preimage measurable_snd)
  · exact (measurable_candidate K A).comp hinsert
  · exact measurable_const

theorem faceInner_measurable (K : ℕ) (A : ℝ) (m : Fin K) :
    Measurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
      ∫ x in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) := by
  have hsm : StronglyMeasurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
      ∫ x : ℝ, faceJoint K A m (t, x)) :=
    (faceJoint_measurable K A m).stronglyMeasurable.integral_prod_right'
  have hm : Measurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
      ∫ x, faceJoint K A m (t, x)) := hsm.measurable
  convert hm using 1
  funext t
  simp only [faceJoint]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [Set.indicator, hx]

theorem faceInner_norm_le_one {K : ℕ} {A : ℝ} (hA : 0 < A)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ) :
    ‖∫ x in Set.Icc (0 : ℝ) 1,
      candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)‖ ≤ 1 := by
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)‖ ≤
      1 * volume.real (Set.Icc (0 : ℝ) 1) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
          (fun x _ => candidate_norm_le_one hA _)
    _ = 1 := by rw [Real.volume_real_Icc_of_le] <;> norm_num

theorem candidate_face_integrand_integrableOn
    {K : ℕ} {A : ℝ} (hA : 0 < A) (m : Fin K) :
    IntegrableOn
      (fun t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
        (∫ x in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
      (BoundedGaps.Maynard.maynardCubeOf
        (BoundedGaps.Maynard.maynardFaceIndex K m)) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf
      (BoundedGaps.Maynard.maynardFaceIndex K m))
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top _)
    (f := fun t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ =>
      (∫ x in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
    ((faceInner_measurable K A m).pow_const 2) 1 ?_
  intro t _
  rw [norm_pow]
  simpa using pow_le_one₀ (n := 2) (norm_nonneg
    (∫ x in Set.Icc (0 : ℝ) 1,
      candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)))
    (faceInner_norm_le_one hA m t)

theorem candidate_admissible {K : ℕ} {A : ℝ} (hA : 0 < A) :
    BoundedGaps.Maynard.MaynardAdmissible K (candidate K A) := by
  exact ⟨candidate_simplexSupported K A, candidate_sq_integrableOn hA,
    candidate_face_integrableOn hA,
    candidate_face_integrand_integrableOn hA⟩

/-! #### Exact normalization integrals -/

theorem integral_factor_sq_interval {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    (∫ x : ℝ in (0 : ℝ)..1, factor A ((K : ℝ) * x) ^ 2) =
      (1 + A * (K : ℝ))⁻¹ := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  simpa only [factor, mul_assoc] using
    (Erdos6.Maynard.integral_inverseAffine_sq hA hKR)

theorem setIntegral_factor_sq_Icc {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      factor A ((K : ℝ) * x) ^ 2) =
      (1 + A * (K : ℝ))⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_factor_sq_interval hK hA

theorem integral_factor_interval {K : ℕ} {A B : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hB : 0 ≤ B) :
    (∫ x : ℝ in (0 : ℝ)..B, factor A ((K : ℝ) * x)) =
      Real.log (1 + A * (K : ℝ) * B) / (A * (K : ℝ)) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  simpa only [factor, mul_assoc] using
    (Erdos6.Maynard.integral_inverseAffine hA hKR hB)

theorem setIntegral_factor_Icc {K : ℕ} {A B : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hB : 0 ≤ B) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) B,
      factor A ((K : ℝ) * x)) =
      Real.log (1 + A * (K : ℝ) * B) / (A * (K : ℝ)) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hB]
  exact integral_factor_interval hK hA hB

noncomputable def squareDensity (K : ℕ) (A x : ℝ) : ℝ :=
  factor A ((K : ℝ) * x) ^ 2

noncomputable def baseMass (K : ℕ) (A : ℝ) : ℝ :=
  (1 + A * (K : ℝ))⁻¹

theorem baseMass_pos {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    0 < baseMass K A := by
  unfold baseMass
  apply inv_pos.mpr
  positivity

theorem integral_squareDensity_Icc {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1, squareDensity K A x) =
      baseMass K A := by
  exact setIntegral_factor_sq_Icc hK hA

theorem measurable_squareDensity (K : ℕ) (A : ℝ) :
    Measurable (squareDensity K A) := by
  unfold squareDensity
  exact ((measurable_factor A).comp
    (measurable_const.mul measurable_id)).pow_const 2

theorem squareDensity_nonneg (K : ℕ) (A x : ℝ) :
    0 ≤ squareDensity K A x := by
  exact sq_nonneg _

theorem squareDensity_le_one {K : ℕ} {A x : ℝ} (hA : 0 < A)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : squareDensity K A x ≤ 1 := by
  unfold squareDensity
  have hg0 : 0 ≤ factor A ((K : ℝ) * x) :=
    factor_nonneg hA (mul_nonneg (Nat.cast_nonneg _) hx.1)
  have hg1 : factor A ((K : ℝ) * x) ≤ 1 :=
    factor_le_one hA (mul_nonneg (Nat.cast_nonneg _) hx.1)
  nlinarith

theorem product_squareDensity_integrableOn_cube
    (K : ℕ) (A : ℝ) (hA : 0 < A) (ι : Type*) [Fintype ι] :
    IntegrableOn (fun t : ι → ℝ => ∏ i, squareDensity K A (t i))
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf ι)
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top ι)
    (f := fun t : ι → ℝ => ∏ i, squareDensity K A (t i))
    (Finset.measurable_prod _ fun i _ =>
      (measurable_squareDensity K A).comp (measurable_pi_apply i)) 1 ?_
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ∏ i : ι, squareDensity K A (t i) ≤ ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          exact squareDensity_nonneg K A _
        · intro i _
          exact squareDensity_le_one hA (ht i (Set.mem_univ i))
      _ = 1 := Finset.prod_const_one
  · exact Finset.prod_nonneg fun i _ => squareDensity_nonneg K A _

theorem integral_product_squareDensity_cube
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      ∏ i, squareDensity K A (t i)) =
      baseMass K A ^ Fintype.card ι := by
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  rw [MeasureTheory.integral_fintype_prod_eq_pow]
  exact congrArg (fun z : ℝ => z ^ Fintype.card ι)
    (integral_squareDensity_Icc hK hA)

theorem product_sq_eq_density_product (K : ℕ) (A : ℝ)
    (t : Fin K → ℝ) :
    product K A t ^ 2 = ∏ i, squareDensity K A (t i) := by
  unfold product squareDensity
  rw [Finset.prod_pow]

theorem candidate_sq_le_density_product {K : ℕ} {A : ℝ}
    (t : Fin K → ℝ) :
    candidate K A t ^ 2 ≤ ∏ i, squareDensity K A (t i) := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex K
  · rw [candidate, if_pos ht, product_sq_eq_density_product]
  · rw [candidate, if_neg ht, zero_pow (by omega : 2 ≠ 0)]
    exact Finset.prod_nonneg fun i _ => squareDensity_nonneg K A _

theorem maynardI_candidate_le {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    BoundedGaps.Maynard.maynardI K (candidate K A) ≤
      baseMass K A ^ K := by
  unfold BoundedGaps.Maynard.maynardI
  calc
    (∫ t in BoundedGaps.Maynard.maynardCube K,
      candidate K A t ^ 2) ≤
        ∫ t in BoundedGaps.Maynard.maynardCube K,
          ∏ i, squareDensity K A (t i) := by
      apply setIntegral_mono_on (candidate_sq_integrableOn hA)
        (product_squareDensity_integrableOn_cube K A hA (Fin K))
        (BoundedGaps.Maynard.maynardCube_measurable K)
      intro t _
      exact candidate_sq_le_density_product t
    _ = baseMass K A ^ K := by
      change (∫ t : Fin K → ℝ in
        BoundedGaps.Maynard.maynardCubeOf (Fin K),
          ∏ i, squareDensity K A (t i)) = _
      simpa only [Fintype.card_fin] using
        (integral_product_squareDensity_cube hK hA (Fin K))

/-! #### First moment and product concentration -/

noncomputable def firstMoment (K : ℕ) (A : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) 1, x * squareDensity K A x

theorem firstMoment_integrand_le {K : ℕ} {A x : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x * squareDensity K A x ≤
      (A * (K : ℝ))⁻¹ * factor A ((K : ℝ) * x) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hc : 0 < A * (K : ℝ) := mul_pos hA hKR
  have hgeneric : ∀ {c x : ℝ}, 0 < c → 0 ≤ x →
      x * (1 + c * x)⁻¹ ^ 2 ≤ c⁻¹ * (1 + c * x)⁻¹ := by
    intro c x hc hx
    have hy : 0 < 1 + c * x := by positivity
    have hxle : x ≤ c⁻¹ * (1 + c * x) := by
      have heq : c⁻¹ * (1 + c * x) = x + c⁻¹ := by
        field_simp [hc.ne']
        ring
      rw [heq]
      exact le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
    calc
      x * (1 + c * x)⁻¹ ^ 2 ≤
          (c⁻¹ * (1 + c * x)) * (1 + c * x)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hxle (sq_nonneg _)
      _ = c⁻¹ * (1 + c * x)⁻¹ := by
        field_simp [hy.ne', hc.ne']
  simpa only [squareDensity, factor, mul_assoc] using
    (hgeneric hc hx.1)

theorem firstMoment_le {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    firstMoment K A ≤
      Real.log (1 + A * (K : ℝ)) /
        (A ^ 2 * (K : ℝ) ^ 2) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hAK : 0 < A * (K : ℝ) := mul_pos hA hKR
  have hleft : IntegrableOn (fun x : ℝ => x * squareDensity K A x)
      (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ => x * squareDensity K A x)
      (measurable_id.mul (measurable_squareDensity K A)) 1 ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · calc
        x * squareDensity K A x ≤ 1 * squareDensity K A x :=
          mul_le_mul_of_nonneg_right hx.2 (squareDensity_nonneg K A x)
        _ ≤ 1 := by simpa using squareDensity_le_one hA hx
    · exact mul_nonneg hx.1 (squareDensity_nonneg K A x)
  have hright : IntegrableOn
      (fun x : ℝ => (A * (K : ℝ))⁻¹ * factor A ((K : ℝ) * x))
      (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ => (A * (K : ℝ))⁻¹ *
        factor A ((K : ℝ) * x))
      (measurable_const.mul
        ((measurable_factor A).comp
          (measurable_const.mul measurable_id)))
      ((A * (K : ℝ))⁻¹) ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact mul_le_of_le_one_right (inv_nonneg.mpr hAK.le)
        (factor_le_one hA (mul_nonneg (Nat.cast_nonneg K) hx.1))
    · exact mul_nonneg (inv_nonneg.mpr hAK.le)
        (factor_nonneg hA (mul_nonneg (Nat.cast_nonneg K) hx.1))
  unfold firstMoment
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, x * squareDensity K A x) ≤
        ∫ x in Set.Icc (0 : ℝ) 1,
          (A * (K : ℝ))⁻¹ * factor A ((K : ℝ) * x) := by
      exact setIntegral_mono_on hleft hright measurableSet_Icc
        (fun x hx => firstMoment_integrand_le hK hA hx)
    _ = (A * (K : ℝ))⁻¹ *
        (Real.log (1 + A * (K : ℝ)) / (A * (K : ℝ))) := by
      rw [integral_const_mul, setIntegral_factor_Icc hK hA
        (by norm_num : (0 : ℝ) ≤ 1)]
      simp only [mul_one]
    _ = Real.log (1 + A * (K : ℝ)) /
        (A ^ 2 * (K : ℝ) ^ 2) := by
      field_simp [hA.ne', hKR.ne']

noncomputable def productDensity (K : ℕ) (A : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∏ i, squareDensity K A (t i)

def coordinateSum {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∑ i, t i

theorem integral_coordinate_mul_productDensity_cube
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      t i * productDensity K A t) =
      firstMoment K A * baseMass K A ^ (Fintype.card ι - 1) := by
  classical
  let f : ι → ℝ → ℝ := fun j x =>
    if j = i then x * squareDensity K A x else squareDensity K A x
  have hpoint (t : ι → ℝ) :
      ∏ j, f j (t j) = t i * productDensity K A t := by
    unfold productDensity
    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (t j))
      (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => squareDensity K A (t j)) (Finset.mem_univ i)]
    have hrest :
        ∏ j ∈ Finset.univ.erase i, f j (t j) =
          ∏ j ∈ Finset.univ.erase i, squareDensity K A (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [f, if_neg hji]
    rw [hrest]
    simp only [f, if_pos]
    ring
  have hintegrals : ∏ j : ι,
      ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      firstMoment K A * baseMass K A ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : ι => ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Finset.mem_univ i)]
    simp only [f, if_pos]
    rw [show (∫ x : ℝ,
        x * squareDensity K A x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
        firstMoment K A by rfl]
    congr 1
    calc
      ∏ j ∈ Finset.univ.erase i,
          ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
          ∏ _j ∈ Finset.univ.erase i, baseMass K A := by
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            have hfj : f j = squareDensity K A := by
              funext x
              simp only [f, if_neg hji]
            rw [hfj]
            exact integral_squareDensity_Icc hK hA
      _ = baseMass K A ^ (Fintype.card ι - 1) := by
        simp only [Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ]
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  rw [← hintegrals, ← MeasureTheory.integral_fintype_prod_eq_prod f]
  congr 1
  funext t
  exact (hpoint t).symm

theorem coordinate_mul_productDensity_integrableOn_cube
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    {ι : Type*} [Fintype ι] (i : ι) :
    IntegrableOn (fun t : ι → ℝ => t i * productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf ι)
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top ι)
    (f := fun t : ι → ℝ => t i * productDensity K A t)
    ((measurable_pi_apply i).mul
      (Finset.measurable_prod _ fun j _ =>
        (measurable_squareDensity K A).comp (measurable_pi_apply j))) 1 ?_
  intro t ht
  have hti : 0 ≤ t i := (ht i (Set.mem_univ i)).1
  have hti1 : t i ≤ 1 := (ht i (Set.mem_univ i)).2
  have hprod0 : 0 ≤ productDensity K A t := by
    unfold productDensity
    exact Finset.prod_nonneg fun j _ => squareDensity_nonneg K A _
  have hprod1 : productDensity K A t ≤ 1 := by
    unfold productDensity
    calc
      ∏ j : ι, squareDensity K A (t j) ≤ ∏ _j : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro j _
          exact squareDensity_nonneg K A _
        · intro j _
          exact squareDensity_le_one hA (ht j (Set.mem_univ j))
      _ = 1 := Finset.prod_const_one
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hti hprod0)]
  nlinarith

theorem integral_coordinateSum_mul_productDensity_cube
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      coordinateSum t * productDensity K A t) =
      (Fintype.card ι : ℝ) * firstMoment K A *
        baseMass K A ^ (Fintype.card ι - 1) := by
  classical
  unfold coordinateSum
  have hfun : (fun t : ι → ℝ =>
      (∑ i, t i) * productDensity K A t) =
      (fun t : ι → ℝ => ∑ i, t i * productDensity K A t) := by
    funext t
    simpa using
      (Finset.sum_mul Finset.univ (fun i : ι => t i)
        (productDensity K A t))
  rw [hfun]
  change (∫ t : ι → ℝ,
      ∑ i, t i * productDensity K A t
      ∂(volume.restrict (BoundedGaps.Maynard.maynardCubeOf ι))) = _
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_coordinate_mul_productDensity_cube hK hA]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · intro i _
    exact coordinate_mul_productDensity_integrableOn_cube hA i

theorem measurable_coordinateSum (ι : Type*) [Fintype ι] :
    Measurable (coordinateSum : (ι → ℝ) → ℝ) := by
  unfold coordinateSum
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

theorem productDensity_nonneg (K : ℕ) (A : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    0 ≤ productDensity K A t := by
  unfold productDensity
  exact Finset.prod_nonneg fun i _ => squareDensity_nonneg K A _

theorem productDensity_integrableOn_cube
    (K : ℕ) (A : ℝ) (hA : 0 < A) (ι : Type*) [Fintype ι] :
    IntegrableOn (productDensity K A : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  change IntegrableOn (fun t : ι → ℝ =>
    ∏ i, squareDensity K A (t i))
    (BoundedGaps.Maynard.maynardCubeOf ι)
  exact product_squareDensity_integrableOn_cube K A hA ι

theorem coordinateSum_mul_productDensity_integrableOn_cube
    (K : ℕ) (A : ℝ) (hA : 0 < A) (ι : Type*) [Fintype ι] :
    IntegrableOn (fun t : ι → ℝ =>
      coordinateSum t * productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  classical
  have hsum : IntegrableOn
      (fun t : ι → ℝ => ∑ i, t i * productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
    exact integrable_finsetSum Finset.univ fun i _ =>
      coordinate_mul_productDensity_integrableOn_cube hA i
  have hfun : (fun t : ι → ℝ =>
      coordinateSum t * productDensity K A t) =
      (fun t : ι → ℝ => ∑ i, t i * productDensity K A t) := by
    funext t
    unfold coordinateSum
    simpa using
      (Finset.sum_mul Finset.univ (fun i : ι => t i)
        (productDensity K A t))
  rw [hfun]
  exact hsum

theorem card_faceIndex {K : ℕ} (m : Fin K) :
    Fintype.card (BoundedGaps.Maynard.maynardFaceIndex K m) = K - 1 := by
  let e : BoundedGaps.Maynard.maynardFaceIndex K m ≃
      {i : Fin K // ¬i = m} := Equiv.refl _
  have he := Fintype.card_congr e
  have hc := @Fintype.card_subtype_compl (Fin K) inferInstance
    (fun i : Fin K => i = m) inferInstance inferInstance
  calc
    Fintype.card (BoundedGaps.Maynard.maynardFaceIndex K m) =
        Fintype.card {i : Fin K // ¬i = m} := he
    _ = K - 1 := by
      simpa only [Fintype.card_fin, Fintype.card_subtype_eq,
        Finset.filter_eq, Finset.card_singleton] using hc

def goodRegion (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  BoundedGaps.Maynard.maynardCubeOf ι ∩
    {t | coordinateSum t ≤ (1 : ℝ) / 2}

theorem goodRegion_measurable (ι : Type*) [Fintype ι] :
    MeasurableSet (goodRegion ι) := by
  unfold goodRegion
  exact (MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Icc)).inter
      (measurableSet_Iic.preimage (measurable_coordinateSum ι))

theorem goodRegion_subset_cube (ι : Type*) [Fintype ι] :
    goodRegion ι ⊆ BoundedGaps.Maynard.maynardCubeOf ι := by
  intro t ht
  exact ht.1

/-- Markov's inequality in the unnormalized product measure. -/
theorem badRegion_productDensity_integral_le
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι,
      productDensity K A t) ≤
      2 * (Fintype.card ι : ℝ) * firstMoment K A *
        baseMass K A ^ (Fintype.card ι - 1) := by
  have hleft : IntegrableOn
      (productDensity K A : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι) :=
    (productDensity_integrableOn_cube K A hA ι).mono_set Set.sdiff_subset
  have hright : IntegrableOn (fun t : ι → ℝ =>
      2 * (coordinateSum t * productDensity K A t))
      (BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι) := by
    have hfull : IntegrableOn (fun t : ι → ℝ =>
        2 * (coordinateSum t * productDensity K A t))
        (BoundedGaps.Maynard.maynardCubeOf ι) :=
      (coordinateSum_mul_productDensity_integrableOn_cube K A hA ι).const_mul 2
    exact hfull.mono_set Set.sdiff_subset
  have hmeas : MeasurableSet
      (BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι) :=
    (MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc)).diff (goodRegion_measurable ι)
  calc
    (∫ t : ι → ℝ in
        BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι,
        productDensity K A t) ≤
        ∫ t : ι → ℝ in
          BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι,
          2 * (coordinateSum t * productDensity K A t) := by
      apply setIntegral_mono_on hleft hright hmeas
      intro t ht
      have hcube := ht.1
      have hnmem := ht.2
      have hsum : (1 : ℝ) / 2 < coordinateSum t := by
        by_contra hnot
        exact hnmem ⟨hcube, le_of_not_gt hnot⟩
      have hd := productDensity_nonneg K A t
      nlinarith
    _ ≤ ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          2 * (coordinateSum t * productDensity K A t) := by
      have hfull : IntegrableOn (fun t : ι → ℝ =>
          2 * (coordinateSum t * productDensity K A t))
          (BoundedGaps.Maynard.maynardCubeOf ι) :=
        (coordinateSum_mul_productDensity_integrableOn_cube K A hA ι).const_mul 2
      apply setIntegral_mono_set hfull
      · exact (ae_restrict_mem (MeasurableSet.pi Set.countable_univ
          (fun _ _ => measurableSet_Icc))).mono (fun t ht =>
            mul_nonneg (by norm_num)
              (mul_nonneg (by
                unfold coordinateSum
                exact Finset.sum_nonneg fun i _ =>
                  (ht i (Set.mem_univ i)).1)
                (productDensity_nonneg K A t)))
      · exact Filter.Eventually.of_forall fun _ ht => Set.sdiff_subset ht
    _ = 2 * (Fintype.card ι : ℝ) * firstMoment K A *
        baseMass K A ^ (Fintype.card ι - 1) := by
      rw [integral_const_mul,
        integral_coordinateSum_mul_productDensity_cube hK hA]
      ring

theorem weighted_bad_bound_lt_half {K : ℕ} (hK2 : 2 ≤ K)
    {a b : ℝ} (ha : 0 < a)
    (hb : b < (1 / (4 * (K : ℝ))) * a) :
    2 * ((K - 1 : ℕ) : ℝ) * b * a ^ (K - 1 - 1) <
      ((1 : ℝ) / 2) * a ^ (K - 1) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hK1 : 1 ≤ K := by omega
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]
    norm_num
  have hratio : ((K - 1 : ℕ) : ℝ) *
      (1 / (4 * (K : ℝ))) < (1 : ℝ) / 4 := by
    rw [hcast]
    have hden : 0 < (4 : ℝ) * (K : ℝ) := by positivity
    rw [show ((K : ℝ) - 1) * (1 / (4 * (K : ℝ))) =
      ((K : ℝ) - 1) / (4 * (K : ℝ)) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hfactor : 0 < 2 * ((K - 1 : ℕ) : ℝ) * a ^ (K - 2) := by
    have hkminus : 0 < ((K - 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    positivity
  have hmoment := mul_lt_mul_of_pos_left hb hfactor
  have hpoweq : a ^ (K - 2) * a = a ^ (K - 1) := by
    have hexp : K - 1 = (K - 2) + 1 := by omega
    rw [hexp, pow_succ]
  have hratio_mul := mul_lt_mul_of_pos_right hratio
    (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos ha (K - 1)))
  have hexp : K - 1 - 1 = K - 2 := by omega
  rw [hexp]
  calc
    2 * ((K - 1 : ℕ) : ℝ) * b * a ^ (K - 2) =
        (2 * ((K - 1 : ℕ) : ℝ) * a ^ (K - 2)) * b := by ring
    _ < (2 * ((K - 1 : ℕ) : ℝ) * a ^ (K - 2)) *
        ((1 / (4 * (K : ℝ))) * a) := hmoment
    _ = (((K - 1 : ℕ) : ℝ) * (1 / (4 * (K : ℝ)))) *
        (2 * a ^ (K - 1)) := by
      rw [← hpoweq]
      ring
    _ < ((1 : ℝ) / 4) * (2 * a ^ (K - 1)) := hratio_mul
    _ = ((1 : ℝ) / 2) * a ^ (K - 1) := by ring

theorem badFace_productDensity_integral_lt_half
    {K : ℕ} {A : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A)
    (m : Fin K) :
    (∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
      BoundedGaps.Maynard.maynardCubeOf
          (BoundedGaps.Maynard.maynardFaceIndex K m) \
        goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m),
      productDensity K A t) <
      ((1 : ℝ) / 2) * baseMass K A ^ (K - 1) := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex K m
  have hbound := badRegion_productDensity_integral_le
    (K := K) (A := A) (by omega : 0 < K) hA ι
  rw [card_faceIndex m] at hbound
  exact hbound.trans_lt (weighted_bad_bound_lt_half hK2
    (baseMass_pos (by omega) hA) hmoment)

theorem goodFace_productDensity_integral_gt_half
    {K : ℕ} {A : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A)
    (m : Fin K) :
    ((1 : ℝ) / 2) * baseMass K A ^ (K - 1) <
      ∫ t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ in
        goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m),
        productDensity K A t := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex K m
  have hdiff := setIntegral_sdiff (goodRegion_measurable ι)
    (productDensity_integrableOn_cube K A hA ι)
    (goodRegion_subset_cube ι)
  have htotal := integral_product_squareDensity_cube
    (K := K) (A := A) (by omega : 0 < K) hA ι
  change (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
    productDensity K A t) = _ at htotal
  rw [card_faceIndex m] at htotal
  have hbad := badFace_productDensity_integral_lt_half hK2 hA hmoment m
  change (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ goodRegion ι,
      productDensity K A t) < _ at hbad
  change ((1 : ℝ) / 2) * baseMass K A ^ (K - 1) <
    ∫ t : ι → ℝ in goodRegion ι, productDensity K A t
  rw [htotal] at hdiff
  have hbase : 0 < baseMass K A :=
    baseMass_pos (K := K) (A := A) (by omega) hA
  have hpow : 0 < baseMass K A ^ (K - 1) := pow_pos hbase _
  nlinarith

/-! #### Face lower bounds -/

noncomputable def faceProduct (K : ℕ) (A : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∏ j, factor A ((K : ℝ) * t j)

theorem faceProduct_sq_eq_productDensity (K : ℕ) (A : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    faceProduct K A t ^ 2 = productDensity K A t := by
  unfold faceProduct productDensity squareDensity
  rw [Finset.prod_pow]

theorem faceProduct_pos_of_mem_cube {K : ℕ} {A : ℝ}
    (hA : 0 < A) {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 < faceProduct K A t := by
  unfold faceProduct
  apply Finset.prod_pos
  intro j _
  exact factor_pos hA (mul_nonneg (Nat.cast_nonneg _)
    (ht j (Set.mem_univ j)).1)

theorem candidate_insert_eq_on_half_interval
    {K : ℕ} {A : ℝ} (hK : 0 < K)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
      factor A ((K : ℝ) * x) * faceProduct K A t := by
  have htnonneg : ∀ j, 0 ≤ t j := fun j =>
    (ht.1 j (Set.mem_univ j)).1
  have hsum : x + ∑ j, t j ≤ 1 := by
    have hface := ht.2
    change coordinateSum t ≤ (1 : ℝ) / 2 at hface
    change x + coordinateSum t ≤ 1
    nlinarith [hx.2]
  have hsimp := Erdos6.Maynard.maynardInsertCoordinate_mem_simplex_of_pos
    hK m x t hx.1 htnonneg hsum
  rw [candidate, if_pos hsimp]
  unfold product
  have hp := Erdos6.Maynard.prod_maynardInsertCoordinate_of_pos hK m x t
    (fun y : ℝ => factor A ((K : ℝ) * y))
  simpa only [faceProduct] using hp

noncomputable def shortMass (K : ℕ) (A : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
    factor A ((K : ℝ) * x)

theorem shortMass_eq {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    shortMass K A =
      Real.log (1 + A * (K : ℝ) * (1 / 2 : ℝ)) /
        (A * (K : ℝ)) := by
  unfold shortMass
  exact setIntegral_factor_Icc hK hA (by norm_num)

theorem shortMass_pos {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    0 < shortMass K A := by
  rw [shortMass_eq hK hA]
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hlog : 0 < Real.log (1 + A * (K : ℝ) * (1 / 2 : ℝ)) := by
    apply Real.log_pos
    have hterm : 0 < A * (K : ℝ) * (1 / 2 : ℝ) := by positivity
    linarith
  exact div_pos hlog (mul_pos hA hKR)

theorem shortCandidateIntegral_eq {K : ℕ} {A : ℝ} (hK : 0 < K)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m)) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      candidate K A
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
      faceProduct K A t * shortMass K A := by
  calc
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
        ∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
          faceProduct K A t * factor A ((K : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
        faceProduct K A t * factor A ((K : ℝ) * x)
      rw [candidate_insert_eq_on_half_interval hK m t ht hx]
      ring
    _ = faceProduct K A t * shortMass K A := by
      rw [integral_const_mul]
      rfl

theorem faceInnerIntegral_ge {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m)) :
    faceProduct K A t * shortMass K A ≤
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
  have hmono :
      (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ≤
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
    apply setIntegral_mono_set (candidate_face_integrableOn hA m t)
    · exact Filter.Eventually.of_forall fun x => candidate_nonneg hA _
    · exact Filter.Eventually.of_forall fun _ hx =>
        ⟨hx.1, hx.2.trans (by norm_num)⟩
  rw [← shortCandidateIntegral_eq hK m t ht]
  exact hmono

theorem faceInnerIntegral_sq_ge {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    (m : Fin K) (t : BoundedGaps.Maynard.maynardFaceIndex K m → ℝ)
    (ht : t ∈ goodRegion (BoundedGaps.Maynard.maynardFaceIndex K m)) :
    shortMass K A ^ 2 * productDensity K A t ≤
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
  have hfacepos : 0 < faceProduct K A t :=
    faceProduct_pos_of_mem_cube hA ht.1
  have hshortpos : 0 < shortMass K A := shortMass_pos hK hA
  have hlowerpos : 0 < faceProduct K A t * shortMass K A :=
    mul_pos hfacepos hshortpos
  have hinner := faceInnerIntegral_ge hK hA m t ht
  have hsq : (faceProduct K A t * shortMass K A) ^ 2 ≤
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        candidate K A
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    nlinarith
  calc
    shortMass K A ^ 2 * productDensity K A t =
        (faceProduct K A t * shortMass K A) ^ 2 := by
      rw [← faceProduct_sq_eq_productDensity]
      ring
    _ ≤ _ := hsq

theorem maynardJ_candidate_gt {K : ℕ} {A : ℝ}
    (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A)
    (m : Fin K) :
    ((1 : ℝ) / 2) * shortMass K A ^ 2 *
        baseMass K A ^ (K - 1) <
      BoundedGaps.Maynard.maynardJ K m (candidate K A) := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex K m
  let c : ℝ := shortMass K A ^ 2
  have hc : 0 < c := sq_pos_of_pos (shortMass_pos (by omega) hA)
  have hgood := goodFace_productDensity_integral_gt_half
    hK2 hA hmoment m
  change ((1 : ℝ) / 2) * baseMass K A ^ (K - 1) <
    ∫ t : ι → ℝ in goodRegion ι, productDensity K A t at hgood
  have hscaled := mul_lt_mul_of_pos_left hgood hc
  have hdensityCube : IntegrableOn (fun t : ι → ℝ =>
      c * productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) :=
    (productDensity_integrableOn_cube K A hA ι).const_mul c
  have hsquareCube : IntegrableOn
      (fun t : ι → ℝ =>
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
      (BoundedGaps.Maynard.maynardCubeOf ι) :=
    candidate_face_integrand_integrableOn hA m
  have hpointwise :
      (∫ t : ι → ℝ in goodRegion ι,
        c * productDensity K A t) ≤
      ∫ t : ι → ℝ in goodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    apply setIntegral_mono_on
      (hdensityCube.mono_set (goodRegion_subset_cube ι))
      (hsquareCube.mono_set (goodRegion_subset_cube ι))
      (goodRegion_measurable ι)
    intro t ht
    exact faceInnerIntegral_sq_ge (by omega) hA m t ht
  have hsubset :
      (∫ t : ι → ℝ in goodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2) ≤
      ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    apply setIntegral_mono_set hsquareCube
    · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    · exact Filter.Eventually.of_forall fun _ ht =>
        goodRegion_subset_cube ι ht
  unfold BoundedGaps.Maynard.maynardJ
  calc
    ((1 : ℝ) / 2) * shortMass K A ^ 2 *
        baseMass K A ^ (K - 1) =
        c * (((1 : ℝ) / 2) * baseMass K A ^ (K - 1)) := by
      unfold c
      ring
    _ < c * (∫ t : ι → ℝ in goodRegion ι,
        productDensity K A t) := hscaled
    _ = (∫ t : ι → ℝ in goodRegion ι,
        c * productDensity K A t) := by rw [integral_const_mul]
    _ ≤ (∫ t : ι → ℝ in goodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          candidate K A
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2) :=
      hpointwise
    _ ≤ _ := hsubset

/-! #### Positivity and the variational quotient -/

noncomputable def positiveBoxWidth (K : ℕ) : ℝ :=
  (2 * (K : ℝ))⁻¹

def positiveBox (K : ℕ) : Set (Fin K → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => positiveBoxWidth K)

theorem positiveBoxWidth_pos {K : ℕ} (hK : 0 < K) :
    0 < positiveBoxWidth K := by
  unfold positiveBoxWidth
  exact inv_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hK))

theorem positiveBoxWidth_le_one {K : ℕ} (hK : 0 < K) :
    positiveBoxWidth K ≤ 1 := by
  unfold positiveBoxWidth
  rw [inv_le_one₀]
  · have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  · exact mul_pos (by norm_num) (Nat.cast_pos.mpr hK)

theorem positiveBox_volume_pos {K : ℕ} (hK : 0 < K) :
    0 < volume (positiveBox K) := by
  unfold positiveBox
  rw [Real.volume_Icc_pi]
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (ENNReal.ofReal_pos.mpr (by
    simpa only [sub_zero] using positiveBoxWidth_pos hK)).ne'

theorem positiveBox_subset_simplex {K : ℕ} (hK : 0 < K) :
    positiveBox K ⊆ BoundedGaps.Maynard.maynardSimplex K := by
  intro t ht
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hcube : t ∈ BoundedGaps.Maynard.maynardCube K := by
    intro i _
    exact ⟨ht.1 i, (ht.2 i).trans (positiveBoxWidth_le_one hK)⟩
  refine ⟨hcube, ?_⟩
  have hsum : (∑ i, t i) ≤ ∑ _i : Fin K, positiveBoxWidth K :=
    Finset.sum_le_sum fun i _ => ht.2 i
  have hwidthsum : (∑ _i : Fin K, positiveBoxWidth K) = (1 : ℝ) / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold positiveBoxWidth
    field_simp [hKR.ne']
  rw [hwidthsum] at hsum
  linarith

theorem candidate_pos_on_positiveBox {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    {t : Fin K → ℝ} (ht : t ∈ positiveBox K) :
    0 < candidate K A t := by
  have hsimp := positiveBox_subset_simplex hK ht
  rw [candidate, if_pos hsimp]
  unfold product
  apply Finset.prod_pos
  intro i _
  exact factor_pos hA (mul_nonneg (Nat.cast_nonneg _) (ht.1 i))

theorem maynardI_candidate_pos {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    0 < BoundedGaps.Maynard.maynardI K (candidate K A) := by
  unfold BoundedGaps.Maynard.maynardI
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => sq_nonneg (candidate K A t))
    (candidate_sq_integrableOn hA)).2
  have hsubset : positiveBox K ⊆
      Function.support (fun t : Fin K → ℝ => candidate K A t ^ 2) ∩
        BoundedGaps.Maynard.maynardCube K := by
    intro t ht
    have hpos := candidate_pos_on_positiveBox hK hA ht
    refine ⟨pow_ne_zero 2 hpos.ne', (positiveBox_subset_simplex hK ht).1⟩
  exact (positiveBox_volume_pos hK).trans_le (measure_mono hsubset)

theorem sum_maynardJ_candidate_gt {K : ℕ} {A : ℝ}
    (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A) :
    (K : ℝ) * (((1 : ℝ) / 2) * shortMass K A ^ 2 *
        baseMass K A ^ (K - 1)) <
      ∑ m : Fin K, BoundedGaps.Maynard.maynardJ K m (candidate K A) := by
  have huniv : (Finset.univ : Finset (Fin K)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  calc
    (K : ℝ) * (((1 : ℝ) / 2) * shortMass K A ^ 2 *
        baseMass K A ^ (K - 1)) =
        ∑ _m : Fin K, ((1 : ℝ) / 2) * shortMass K A ^ 2 *
          baseMass K A ^ (K - 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ∑ m : Fin K,
        BoundedGaps.Maynard.maynardJ K m (candidate K A) := by
      exact Finset.sum_lt_sum_of_nonempty huniv fun m _ =>
        maynardJ_candidate_gt hK2 hA hmoment m

theorem explicit_ratio_identity {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    ((K : ℝ) * (((1 : ℝ) / 2) * shortMass K A ^ 2 *
        baseMass K A ^ (K - 1))) /
        baseMass K A ^ K =
      ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A := by
  have hbase := baseMass_pos hK hA
  have hpow : baseMass K A ^ K =
      baseMass K A ^ (K - 1) * baseMass K A := by
    have hexp : K = (K - 1) + 1 := by omega
    calc
      baseMass K A ^ K = baseMass K A ^ ((K - 1) + 1) := by
        exact congrArg (fun n : ℕ => baseMass K A ^ n) hexp
      _ = baseMass K A ^ (K - 1) * baseMass K A := pow_succ _ _
  rw [hpow]
  field_simp [hbase.ne', pow_ne_zero _ hbase.ne']

theorem maynardRatio_candidate_gt {K : ℕ} {A : ℝ}
    (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A) :
    ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A <
      BoundedGaps.Maynard.maynardRatio K (candidate K A) := by
  let L : ℝ := (K : ℝ) * (((1 : ℝ) / 2) * shortMass K A ^ 2 *
    baseMass K A ^ (K - 1))
  let S : ℝ := ∑ m : Fin K,
    BoundedGaps.Maynard.maynardJ K m (candidate K A)
  let I : ℝ := BoundedGaps.Maynard.maynardI K (candidate K A)
  have hK : 0 < K := by omega
  have hbase : 0 < baseMass K A := baseMass_pos hK hA
  have hshort : 0 < shortMass K A := shortMass_pos hK hA
  have hL : 0 < L := by
    unfold L
    positivity
  have hsum : L < S := sum_maynardJ_candidate_gt hK2 hA hmoment
  have hIpos : 0 < I := maynardI_candidate_pos hK hA
  have hIle : I ≤ baseMass K A ^ K := maynardI_candidate_le hK hA
  have hid := explicit_ratio_identity hK hA
  unfold BoundedGaps.Maynard.maynardRatio
  change ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A < S / I
  calc
    ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A =
        L / baseMass K A ^ K := hid.symm
    _ ≤ L / I := div_le_div_of_nonneg_left hL.le hIpos hIle
    _ < S / I := div_lt_div_of_pos_right hsum hIpos

/-! #### An explicit unbounded family -/

/-- A convenient sufficient condition for concentration inside the half-simplex. -/
theorem firstMoment_lt_quarter_of_log_lt
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hAK : 1 < A * (K : ℝ))
    (hlog : Real.log (1 + A * (K : ℝ)) < A / 8) :
    firstMoment K A <
      (1 / (4 * (K : ℝ))) * baseMass K A := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hm := firstMoment_le hK hA
  have hden : 0 < A ^ 2 * (K : ℝ) ^ 2 := by positivity
  have hmain : Real.log (1 + A * (K : ℝ)) /
        (A ^ 2 * (K : ℝ) ^ 2) <
      (A / 8) / (A ^ 2 * (K : ℝ) ^ 2) :=
    div_lt_div_of_pos_right hlog hden
  have hsimp : (A / 8) / (A ^ 2 * (K : ℝ) ^ 2) =
      1 / (8 * A * (K : ℝ) ^ 2) := by
    field_simp [hA.ne', hKR.ne']
  have hcomp : 1 / (8 * A * (K : ℝ) ^ 2) <
      (1 / (4 * (K : ℝ))) * baseMass K A := by
    unfold baseMass
    rw [div_eq_mul_inv]
    have hright : 0 < 4 * (K : ℝ) * (1 + A * (K : ℝ)) := by
      positivity
    rw [show (1 / (4 * (K : ℝ))) * (1 + A * (K : ℝ))⁻¹ =
      1 / (4 * (K : ℝ) * (1 + A * (K : ℝ))) by field_simp]
    exact one_div_lt_one_div_of_lt hright (by nlinarith)
  exact hm.trans_lt (hmain.trans_eq hsimp |>.trans hcomp)

/-- Number of variables in the `r`th member of the variational family. -/
def parameterK (r : ℕ) : ℕ := 2 ^ r

/-- Decay parameter in the `r`th member of the variational family. -/
def parameterA (r : ℕ) : ℝ := 16 * (r : ℝ)

theorem sixteen_mul_add_one_lt_two_pow {r : ℕ} (hr : 8 ≤ r) :
    16 * r + 1 < 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      have hstep : 16 * (n + 1) + 1 < (16 * n + 1) * 2 := by omega
      exact hstep.trans (Nat.mul_lt_mul_of_pos_right ih (by omega))

theorem parameterK_pos (r : ℕ) : 0 < parameterK r := by
  unfold parameterK
  positivity

theorem parameterA_pos {r : ℕ} (hr : 0 < r) : 0 < parameterA r := by
  unfold parameterA
  positivity

theorem one_lt_parameterA_mul_parameterK {r : ℕ} (hr : 0 < r) :
    1 < parameterA r * (parameterK r : ℝ) := by
  have hK : (1 : ℝ) ≤ parameterK r := by
    exact_mod_cast (parameterK_pos r)
  unfold parameterA
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

theorem parameter_log_upper {r : ℕ} (hr : 8 ≤ r) :
    Real.log (1 + parameterA r * (parameterK r : ℝ)) <
      parameterA r / 8 := by
  have hKpos : 0 < parameterK r := parameterK_pos r
  have hlin := sixteen_mul_add_one_lt_two_pow hr
  have hnat : 1 + 16 * r * parameterK r <
      parameterK r * parameterK r := by
    calc
      1 + 16 * r * parameterK r ≤
          (16 * r + 1) * parameterK r := by nlinarith
      _ < parameterK r * parameterK r :=
        Nat.mul_lt_mul_of_pos_right hlin hKpos
  have hineq : 1 + parameterA r * (parameterK r : ℝ) <
      (parameterK r : ℝ) ^ 2 := by
    unfold parameterA
    rw [pow_two]
    exact_mod_cast hnat
  have hleftpos : 0 < 1 + parameterA r * (parameterK r : ℝ) := by
    unfold parameterA parameterK
    positivity
  have hrightpos : 0 < (parameterK r : ℝ) ^ 2 := by positivity
  have hlog := Real.strictMonoOn_log hleftpos hrightpos hineq
  rw [Real.log_pow] at hlog
  have hlogK : Real.log (parameterK r : ℝ) =
      (r : ℝ) * Real.log 2 := by
    unfold parameterK
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlogK] at hlog
  norm_num at hlog
  have hlogTwo : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  unfold parameterA
  exact hlog.trans (by nlinarith)

/-- The elementary part of the quotient lower bound.  The extra factor
`1 + A K` in the reciprocal base mass makes this inequality strict. -/
theorem explicit_ratio_lower_log {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    Real.log (1 + A * (K : ℝ) * (1 / 2 : ℝ)) ^ 2 / (2 * A) <
      ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hterm : 0 < A * (K : ℝ) * (1 / 2 : ℝ) := by positivity
  have harg : 1 < 1 + A * (K : ℝ) * (1 / 2 : ℝ) := by linarith
  have hlog : 0 < Real.log (1 + A * (K : ℝ) * (1 / 2 : ℝ)) :=
    Real.log_pos harg
  let L := Real.log (1 + A * (K : ℝ) * (1 / 2 : ℝ))
  have hden : 0 < 2 * A ^ 2 * (K : ℝ) := by positivity
  calc
    L ^ 2 / (2 * A) = L ^ 2 * (A * (K : ℝ)) /
        (2 * A ^ 2 * (K : ℝ)) := by
      field_simp [hA.ne', hKR.ne']
    _ < L ^ 2 * (1 + A * (K : ℝ)) /
        (2 * A ^ 2 * (K : ℝ)) := by
      apply (div_lt_div_iff₀ hden hden).2
      have : 0 < L ^ 2 := sq_pos_of_pos hlog
      nlinarith
    _ = ((K : ℝ) / 2) * shortMass K A ^ 2 / baseMass K A := by
      rw [shortMass_eq hK hA]
      unfold baseMass L
      field_simp [hA.ne', hKR.ne']

/-- The short one-dimensional mass retains a logarithm of size at least
`(2/3) r` for the explicit parameter family. -/
theorem parameter_short_log_lower {r : ℕ} (hr : 8 ≤ r) :
    (2 / 3 : ℝ) * (r : ℝ) <
      Real.log
        (1 + parameterA r * (parameterK r : ℝ) * (1 / 2 : ℝ)) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hKpos : (0 : ℝ) < parameterK r := by
    exact_mod_cast parameterK_pos r
  have hKlog : Real.log (parameterK r : ℝ) =
      (r : ℝ) * Real.log 2 := by
    unfold parameterK
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have harg : (parameterK r : ℝ) <
      1 + parameterA r * (parameterK r : ℝ) * (1 / 2 : ℝ) := by
    unfold parameterA
    have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    nlinarith
  have hargpos : 0 <
      1 + parameterA r * (parameterK r : ℝ) * (1 / 2 : ℝ) :=
    hKpos.trans harg
  have hmono := Real.strictMonoOn_log hKpos hargpos harg
  rw [hKlog] at hmono
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  nlinarith

/-- The quotient of the explicit `r`th candidate grows at least linearly. -/
theorem parameter_ratio_gt {r : ℕ} (hr : 8 ≤ r) :
    (r : ℝ) / 72 <
      BoundedGaps.Maynard.maynardRatio (parameterK r)
        (candidate (parameterK r) (parameterA r)) := by
  have hrN : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrN
  have hK2 : 2 ≤ parameterK r := by
    unfold parameterK
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : 0 < parameterA r := parameterA_pos hrN
  have hAK : 1 < parameterA r * (parameterK r : ℝ) :=
    one_lt_parameterA_mul_parameterK hrN
  have hmoment : firstMoment (parameterK r) (parameterA r) <
      (1 / (4 * (parameterK r : ℝ))) *
        baseMass (parameterK r) (parameterA r) :=
    firstMoment_lt_quarter_of_log_lt (parameterK_pos r) hA hAK
      (parameter_log_upper hr)
  have hratio := maynardRatio_candidate_gt hK2 hA hmoment
  have hexplicit := explicit_ratio_lower_log (parameterK_pos r) hA
  have hloglower := parameter_short_log_lower hr
  have hsq : ((2 / 3 : ℝ) * (r : ℝ)) ^ 2 <
      Real.log
        (1 + parameterA r * (parameterK r : ℝ) * (1 / 2 : ℝ)) ^ 2 := by
    have : 0 < (2 / 3 : ℝ) * (r : ℝ) := by positivity
    nlinarith
  have hlower : (r : ℝ) / 72 <
      Real.log
          (1 + parameterA r * (parameterK r : ℝ) * (1 / 2 : ℝ)) ^ 2 /
        (2 * parameterA r) := by
    unfold parameterA
    have hden : 0 < 2 * (16 * (r : ℝ)) := by positivity
    rw [lt_div_iff₀ hden]
    calc
      (r : ℝ) / 72 * (2 * (16 * (r : ℝ))) =
          ((2 / 3 : ℝ) * (r : ℝ)) ^ 2 := by ring
      _ < _ := hsq
  exact hlower.trans (hexplicit.trans hratio)

/-- In particular, the Maynard variational quotient is unbounded. -/
theorem exists_admissible_ratio_gt (L : ℝ) :
    ∃ K : ℕ, ∃ F : (Fin K → ℝ) → ℝ,
      BoundedGaps.Maynard.MaynardAdmissible K F ∧
        L < BoundedGaps.Maynard.maynardRatio K F := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max (8 : ℝ) (72 * L))
  have hr8R : (8 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr8 : 8 ≤ r := by exact_mod_cast hr8R.le
  have hL72 : 72 * L < (r : ℝ) :=
    (le_max_right (8 : ℝ) (72 * L)).trans_lt hr
  have hL : L < (r : ℝ) / 72 := by linarith
  refine ⟨parameterK r, candidate (parameterK r) (parameterA r), ?_, ?_⟩
  · exact candidate_admissible (parameterA_pos (by omega))
  · exact hL.trans (parameter_ratio_gt hr8)

end VariableMaynard

/-- Since the third iterated logarithm tends to infinity, the fixed positive
FGKMT constant eventually dominates every constant on Rankin's older scale. -/
theorem eventually_threshold_lt_strongThreshold {C c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, threshold C n < strongThreshold c n := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp h0
  have h2 : Tendsto (fun n : ℕ => log (log (n : ℝ))) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun n : ℕ => log (log (log (n : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp h2
  have hL1large : ∀ᶠ n : ℕ in atTop, 1 < log (n : ℝ) :=
    h1.eventually (eventually_gt_atTop 1)
  have hL2large : ∀ᶠ n : ℕ in atTop, 1 < log (log (n : ℝ)) :=
    h2.eventually (eventually_gt_atTop 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      max 1 (C / c + 1) < log (log (log (n : ℝ))) :=
    h3.eventually (eventually_gt_atTop (max 1 (C / c + 1)))
  filter_upwards [hL1large, hL2large, hlarge] with n hL1big hL2big hn
  have hL3 : 0 < log (log (log (n : ℝ))) :=
    lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hn.le)
  have hL4 : 0 < log (log (log (log (n : ℝ)))) :=
    Real.log_pos ((le_max_left _ _).trans_lt hn)
  have hL2 : 0 < log (log (n : ℝ)) := lt_trans zero_lt_one hL2big
  have hCd : C < c * log (log (log (n : ℝ))) := by
    have hquot : C / c + 1 < log (log (log (n : ℝ))) :=
      (le_max_right _ _).trans_lt hn
    have hquot' : C / c < log (log (log (n : ℝ))) := by linarith
    rw [div_lt_iff₀ hc] at hquot'
    simpa [mul_comm] using hquot'
  have hL1 : 0 < log (n : ℝ) := lt_trans zero_lt_one hL1big
  unfold threshold strongThreshold
  have hB : 0 < log (log (n : ℝ)) * log (log (log (log (n : ℝ)))) *
      log (n : ℝ) := by positivity
  field_simp
  nlinarith [mul_pos hB hL3]

/-- Finite covering data: each offset `1, ..., y` occupies a selected
residue class modulo one of a finite set of primes. -/
structure ResidueCover (y : ℕ) where
  primes : Finset ℕ
  residue : ℕ → ℕ
  prime : ∀ p ∈ primes, p.Prime
  covers : ∀ i : ℕ, 1 ≤ i → i ≤ y →
    ∃ p ∈ primes, i ≡ residue p [MOD p]

namespace ResidueCover

variable {y : ℕ} (cover : ResidueCover y)

/-- Product of all prime moduli in a finite cover. -/
def modulus : ℕ := ∏ p ∈ cover.primes, p

theorem modulus_pos : 0 < cover.modulus := by
  unfold modulus
  exact Finset.prod_pos fun p hp => (cover.prime p hp).pos

theorem pairwise_coprime :
    Set.Pairwise (↑cover.primes : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (cover.prime p hp) (cover.prime q hq)).2 hpq

/-- Simultaneous CRT solution to `x ≡ -residue(p) (mod p)`. -/
noncomputable def base : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p => p - cover.residue p % p) id cover.primes
    (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime

theorem base_modEq (p : ℕ) (hp : p ∈ cover.primes) :
    cover.base ≡ p - cover.residue p % p [MOD p] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p => p - cover.residue p % p) id cover.primes
    (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime).prop p hp

theorem base_lt_modulus : cover.base < cover.modulus := by
  exact Nat.chineseRemainderOfFinset_lt_prod
    (fun p => p - cover.residue p % p) id
    (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime

theorem negResidue_add_modEq_zero {p r i : ℕ} (hp : 0 < p)
    (h : i ≡ r [MOD p]) : p - r % p + i ≡ 0 [MOD p] := by
  rw [Nat.ModEq] at h ⊢
  rw [Nat.add_mod, h]
  have hr := Nat.mod_lt r hp
  by_cases hr0 : r % p = 0
  · simp [hr0]
  · rw [Nat.mod_eq_of_lt (Nat.sub_lt hp (Nat.pos_of_ne_zero hr0))]
    rw [Nat.sub_add_cancel hr.le, Nat.mod_self, Nat.zero_mod]

theorem prime_dvd_modulus {p : ℕ} (hp : p ∈ cover.primes) :
    p ∣ cover.modulus := by
  unfold modulus
  exact Finset.dvd_prod_of_mem id hp

/-- The CRT solution may be lifted beyond an arbitrary lower bound; every
covered offset is then composite because its covering prime is a proper
divisor. -/
theorem exists_composite_block_ge (cover : ResidueCover y) (L : ℕ) :
    ∃ x : ℕ, L ≤ x ∧ x < (max L 1 + 1) * cover.modulus ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(x + i).Prime := by
  let t := max L 1
  let x := cover.base + t * cover.modulus
  have ht : 1 ≤ t := le_max_right L 1
  have hM : 0 < cover.modulus := cover.modulus_pos
  have htx : t * cover.modulus ≤ x := Nat.le_add_left _ _
  have hLx : L ≤ x := by
    have hLt : L ≤ t := le_max_left L 1
    have htprod : t ≤ t * cover.modulus := Nat.le_mul_of_pos_right t hM
    exact hLt.trans (htprod.trans htx)
  have hxupper : x < (max L 1 + 1) * cover.modulus := by
    calc
      x = cover.base + t * cover.modulus := rfl
      _ < cover.modulus + t * cover.modulus :=
        Nat.add_lt_add_right cover.base_lt_modulus _
      _ = (max L 1 + 1) * cover.modulus := by
        simp [t, Nat.add_mul, Nat.add_comm]
  refine ⟨x, hLx, hxupper, ?_⟩
  intro i hi1 hiy
  obtain ⟨p, hpP, hi⟩ := cover.covers i hi1 hiy
  have hp : p.Prime := cover.prime p hpP
  have hpM : p ∣ cover.modulus := cover.prime_dvd_modulus hpP
  have hzero : t * cover.modulus ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hpM t)
  have hxmod : x ≡ p - cover.residue p % p [MOD p] := by
    dsimp [x]
    exact (cover.base_modEq p hpP).add hzero
  have hdiv : p ∣ x + i := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact (hxmod.add_right i).trans
      (negResidue_add_modEq_zero hp.pos hi)
  have hp_le_M : p ≤ cover.modulus := Nat.le_of_dvd hM hpM
  have hM_le_prod : cover.modulus ≤ t * cover.modulus := by
    nlinarith
  have hp_lt : p < x + i := by
    dsimp [x]
    omega
  exact Nat.not_prime_of_dvd_of_ne hdiv hp.ne_one (ne_of_lt hp_lt)

end ResidueCover

/-! ## Composing partial residue covers -/

/-- Residue data covering a specified finite set of offsets.  The analytic
construction assembles several disjoint prime ranges before obtaining a cover
of the whole interval. -/
structure PartialResidueCover (S : Finset ℕ) where
  primes : Finset ℕ
  residue : ℕ → ℕ
  prime : ∀ p ∈ primes, p.Prime
  covers : ∀ i ∈ S, ∃ p ∈ primes, i ≡ residue p [MOD p]

namespace PartialResidueCover

variable {S T : Finset ℕ}

/-- Combine covers supported on disjoint prime sets. -/
def union (left : PartialResidueCover S) (right : PartialResidueCover T)
    (hdisjoint : Disjoint left.primes right.primes) :
    PartialResidueCover (S ∪ T) where
  primes := left.primes ∪ right.primes
  residue p := if p ∈ left.primes then left.residue p else right.residue p
  prime p hp := by
    obtain hpLeft | hpRight := Finset.mem_union.mp hp
    · exact left.prime p hpLeft
    · exact right.prime p hpRight
  covers i hi := by
    obtain hiLeft | hiRight := Finset.mem_union.mp hi
    · obtain ⟨p, hp, hmod⟩ := left.covers i hiLeft
      refine ⟨p, Finset.mem_union_left _ hp, ?_⟩
      simpa [hp] using hmod
    · obtain ⟨p, hp, hmod⟩ := right.covers i hiRight
      have hpNotLeft : p ∉ left.primes := by
        intro hpLeft
        exact Finset.disjoint_left.mp hdisjoint hpLeft hp
      refine ⟨p, Finset.mem_union_right _ hp, ?_⟩
      simpa [hpNotLeft] using hmod

/-- Transport the covered set along an equality while preserving the prime
and residue data definitionally. -/
def reindex {V : Finset ℕ} (cover : PartialResidueCover S) (h : S = V) :
    PartialResidueCover V where
  primes := cover.primes
  residue := cover.residue
  prime := cover.prime
  covers i hi := cover.covers i (by simpa [h] using hi)

@[simp] theorem reindex_primes {V : Finset ℕ}
    (cover : PartialResidueCover S) (h : S = V) :
    (cover.reindex h).primes = cover.primes := rfl

/-- A partial cover of the entire offset interval is a `ResidueCover`. -/
def toResidueCover {y : ℕ}
    (cover : PartialResidueCover (Finset.Icc 1 y)) : ResidueCover y where
  primes := cover.primes
  residue := cover.residue
  prime := cover.prime
  covers i hi1 hiy := cover.covers i (Finset.mem_Icc.mpr ⟨hi1, hiy⟩)

/-- Assign each leftover offset injectively to a fresh prime and choose the
corresponding residue. -/
noncomputable def ofInjection {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (f : ↥S ↪ ↥P) :
    PartialResidueCover S where
  primes := P
  residue p :=
    if hp : p ∈ P then
      if hpre : ∃ i : ↥S, f i = ⟨p, hp⟩ then
        (Classical.choose hpre).1
      else 0
    else 0
  prime := hprime
  covers i hi := by
    let si : ↥S := ⟨i, hi⟩
    let p : ↥P := f si
    have hpre : ∃ j : ↥S, f j = p := ⟨si, rfl⟩
    refine ⟨p.1, p.2, ?_⟩
    simp only [p.2, dite_true]
    rw [dif_pos hpre]
    have hj : Classical.choose hpre = si :=
      f.injective (Classical.choose_spec hpre)
    rw [hj]

/-- Cardinality form of the fresh-prime cleanup step. -/
theorem exists_of_card_le {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hcard : S.card ≤ P.card) :
    ∃ cover : PartialResidueCover S, cover.primes = P := by
  classical
  have hcard' : Fintype.card ↥S ≤ Fintype.card ↥P := by simpa using hcard
  let f : ↥S ↪ ↥P :=
    (Function.Embedding.nonempty_of_card_le hcard').some
  exact ⟨ofInjection hprime f, rfl⟩

end PartialResidueCover

/-- A subset of `ℕ` containing a member beyond every threshold is infinite. -/
theorem infinite_natSet_of_forall_exists_ge {S : Set ℕ}
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n ∈ S) : S.Infinite := by
  intro hfinite
  obtain ⟨a, ha⟩ := hfinite.bddAbove
  obtain ⟨n, hn, hmem⟩ := h (a + 1)
  have hna := ha hmem
  omega

/-- Counting primes is unchanged across a block containing no primes.  The
right endpoint is written as `x + y + 1` because `Nat.count p t` counts the
members of `p` strictly below `t`. -/
theorem count_prime_eq_of_composite_block (x y : ℕ)
    (hcomp : ∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(x + i).Prime) :
    Nat.count Nat.Prime (x + y + 1) = Nat.count Nat.Prime (x + 1) := by
  induction y with
  | zero => simp
  | succ y ih =>
      have ih' := ih (fun i hi1 hiy => hcomp i hi1 (by omega))
      have hpnew : ¬(x + y + 1).Prime := by
        simpa [Nat.add_assoc] using hcomp (y + 1) (by omega) (by omega)
      rw [show x + (y + 1) + 1 = (x + y + 1) + 1 by omega, Nat.count_succ,
        if_neg hpnew, ih']
      simp

/-- A prime-free block `x+1, ..., x+y` supplies an indexed consecutive-prime
gap longer than `y`.  If the block begins beyond the `N`th prime, the index of
that gap is at least `N`. -/
theorem exists_index_gap_gt_of_composite_block (N x y : ℕ) (hx : 2 ≤ x)
    (hxN : Nat.nth Nat.Prime N ≤ x)
    (hcomp : ∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(x + i).Prime) :
    ∃ n : ℕ, N ≤ n ∧ n ≤ x ∧
      (y : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  let c := Nat.count Nat.Prime (x + 1)
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    rw [Nat.count_ne_iff_exists]
    exact ⟨2, by omega, Nat.prime_two⟩
  let n := c - 1
  have hnadd : n + 1 = c := Nat.sub_add_cancel hcpos
  have hnltc : n < c := by omega
  have hNc : N < c := by
    apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2
    exact hxN.trans_lt (Nat.lt_succ_self x)
  have hNn : N ≤ n := by omega
  have hpnx : Nat.nth Nat.Prime n ≤ x := by
    have := Nat.nth_lt_of_lt_count hnltc
    omega
  have hcount := count_prime_eq_of_composite_block x y hcomp
  have hq : x + y + 1 ≤ Nat.nth Nat.Prime (n + 1) := by
    have hle := Nat.le_nth_count Nat.infinite_setOfPred_prime (x + y + 1)
    rw [hcount] at hle
    simpa only [hnadd, c] using hle
  have hnle : n ≤ x := by
    exact (Nat.le_trans (Nat.le_add_right n 2) (Nat.add_two_le_nth_prime n)).trans hpnx
  refine ⟨n, hNn, hnle, ?_⟩
  have hqR : (x + y + 1 : ℝ) ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by
    exact_mod_cast hq
  have hpR : (Nat.nth Nat.Prime n : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hpnx
  linarith

/-- Logical endpoint used after the quantitative large-gap construction:
arbitrarily large witnesses give the required infinite set. -/
theorem erdos4For_of_forall_exists_ge (C : ℝ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (n + 1).nth Nat.Prime - n.nth Nat.Prime >
        C * log (log n) * log (log (log (log n))) /
          (log (log (log n))) ^ 2 * log n) :
    Erdos4For C := by
  apply infinite_natSet_of_forall_exists_ge
  exact h

/-- The published FGKMT lower bound implies Erdős's requested bound for an
arbitrary constant `C`. -/
theorem erdos4For_of_strongErdos4For {c : ℝ} (hc : 0 < c)
    (hstrong : StrongErdos4For c) (C : ℝ) : Erdos4For C := by
  have hcompare := eventually_threshold_lt_strongThreshold (C := C) hc
  rw [Filter.eventually_atTop] at hcompare
  obtain ⟨N₀, hN₀⟩ := hcompare
  apply erdos4For_of_forall_exists_ge C
  intro N
  obtain ⟨n, hnstrong, hnlarge⟩ := hstrong.exists_gt (max N N₀)
  refine ⟨n, by omega, ?_⟩
  exact (hN₀ n (by omega)).trans hnstrong

/-- Final logical assembly from the stronger theorem proved by
Ford--Green--Konyagin--Maynard--Tao. -/
theorem erdos_4_of_strong_large_gaps
    (hFGKMT : ∃ c > 0, StrongErdos4For c) :
    (∀ C > 0, Erdos4For C) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ C _hC
    obtain ⟨c, hc, hstrong⟩ := hFGKMT
    exact erdos4For_of_strongErdos4For hc hstrong C
  · intro _
    trivial

/-- Covering-form endpoint.  It is enough to construct, beyond every indexed
threshold `N`, a prime-free block whose length dominates the target for every
possible prime index preceding that block.  This formulation deliberately
keeps the finite covering theorem independent of any eventual-monotonicity
lemma for the iterated-log expression. -/
theorem erdos4For_of_composite_blocks (C : ℝ)
    (hblocks : ∀ N : ℕ, ∃ x y : ℕ,
      2 ≤ x ∧ Nat.nth Nat.Prime N ≤ x ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(x + i).Prime) ∧
      (∀ n : ℕ, N ≤ n → n ≤ x → threshold C n < y)) :
    Erdos4For C := by
  apply erdos4For_of_forall_exists_ge C
  intro N
  obtain ⟨x, y, hx, hxN, hcomp, hscale⟩ := hblocks N
  obtain ⟨n, hNn, hnx, hgap⟩ :=
    exists_index_gap_gt_of_composite_block N x y hx hxN hcomp
  refine ⟨n, hNn, ?_⟩
  exact (hscale n hNn hnx).trans hgap

/-- Exact finite covering contract for the analytic part of the proof.  The
CRT representative is less than one modulus beyond the chosen lower lift, so
it suffices to dominate `threshold` up to the displayed finite endpoint. -/
theorem erdos4For_of_residue_covers (C : ℝ)
    (hcovers : ∀ N : ℕ, ∃ y : ℕ, ∃ cover : ResidueCover y,
      ∀ n : ℕ, N ≤ n →
        n < (max (max 2 (Nat.nth Nat.Prime N)) 1 + 1) * cover.modulus →
          threshold C n < y) :
    Erdos4For C := by
  apply erdos4For_of_composite_blocks C
  intro N
  obtain ⟨y, cover, hscale⟩ := hcovers N
  let L := max 2 (Nat.nth Nat.Prime N)
  obtain ⟨x, hLx, hxupper, hcomp⟩ := cover.exists_composite_block_ge L
  refine ⟨x, y, ?_, ?_, hcomp, ?_⟩
  · exact (le_max_left 2 (Nat.nth Nat.Prime N)).trans hLx
  · exact (le_max_right 2 (Nat.nth Nat.Prime N)).trans hLx
  · intro n hNn hnx
    apply hscale n hNn
    have : n < (max L 1 + 1) * cover.modulus := hnx.trans_lt hxupper
    simpa [L] using this

/-! ## Smooth residual exception

The first deterministic sieving stage leaves, among other fibres, integers
whose prime factors are all at most `y` and whose predecessor is coprime to
the primorial.  The completed Erdős 469 development contains the Rankin and
finite Euler-product estimates needed for the smooth-number part. -/

/-- The smooth exceptional set after the initial residues `1 (mod p)` for
small primes have been selected. -/
def smoothResidualException (U y : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo U (y + 1)).filter
    (fun m => Nat.Coprime (m - 1) (primorial y))

theorem smoothResidualException_subset_smoothNumbersUpTo (U y : ℕ) :
    smoothResidualException U y ⊆ Nat.smoothNumbersUpTo U (y + 1) := by
  exact Finset.filter_subset _ _

theorem card_smoothResidualException_le_smoothNumbersUpTo (U y : ℕ) :
    (smoothResidualException U y).card ≤
      (Nat.smoothNumbersUpTo U (y + 1)).card := by
  exact Finset.card_le_card (smoothResidualException_subset_smoothNumbersUpTo U y)

/-- Rankin's finite smooth-number estimate, specialized to the residual
exception.  The additional shifted-coprimality condition can only decrease
the cardinality. -/
theorem card_smoothResidualException_rankin_le
    {U y : ℕ} {δ : ℝ} (hU : 0 < U) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((smoothResidualException U y).card : ℝ) ≤
      (U : ℝ) ^ (1 - δ) * Erdos469.smoothRankinEulerProduct δ y := by
  have hcard : ((smoothResidualException U y).card : ℝ) ≤
      ((Nat.smoothNumbersUpTo U (y + 1)).card : ℝ) := by
    exact_mod_cast card_smoothResidualException_le_smoothNumbersUpTo U y
  exact hcard.trans
    (Erdos469.card_smoothNumbersUpTo_rankin_le hU hδ hδ1)

/-- Fully explicit elementary majorant for the same exceptional set. -/
theorem card_smoothResidualException_rankin_exp_le
    {U y : ℕ} {δ : ℝ} (hU : 0 < U) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) :
    ((smoothResidualException U y).card : ℝ) ≤
      (U : ℝ) ^ (1 - δ) *
        Real.exp (Erdos469.rankinEulerConstant * (y : ℝ) ^ δ *
          (1 + Real.log (y : ℝ))) := by
  exact (card_smoothResidualException_rankin_le hU hδ
    (hδhalf.trans_lt (by norm_num))).trans
      (mul_le_mul_of_nonneg_left
        (Erdos469.smoothRankinEulerProduct_le hδ.le hδhalf)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Survivors after choosing residue `1` for primes through `y` and residue
`0` for primes in `(y,z]`. -/
def initialSieveSurvivors (U y z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun j =>
    Nat.Coprime (j - 1) (primorial y) ∧
      ∀ p ∈ Nat.primesLE z, y < p → ¬p ∣ j

theorem mem_initialSieveSurvivors {U y z j : ℕ} :
    j ∈ initialSieveSurvivors U y z ↔
      1 ≤ j ∧ j ≤ U ∧ Nat.Coprime (j - 1) (primorial y) ∧
        ∀ p ∈ Nat.primesLE z, y < p → ¬p ∣ j := by
  rw [initialSieveSurvivors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hj1, hjU⟩, hcop, hfac⟩
    exact ⟨hj1, hjU, hcop, hfac⟩
  · rintro ⟨hj1, hjU, hcop, hfac⟩
    exact ⟨⟨hj1, hjU⟩, hcop, hfac⟩

/-- Exact residual decomposition: a survivor is either in the smooth
exception or has a prime divisor beyond `z`. -/
theorem initialSieveSurvivor_smooth_or_largePrime
    {U y z j : ℕ} (hj : j ∈ initialSieveSurvivors U y z) :
    j ∈ smoothResidualException U y ∨
      ∃ p : ℕ, p.Prime ∧ z < p ∧ p ∣ j := by
  have hjdata := mem_initialSieveSurvivors.mp hj
  by_cases hsmooth : j ∈ Nat.smoothNumbers (y + 1)
  · left
    rw [smoothResidualException, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo]
    exact ⟨⟨hjdata.2.1, hsmooth⟩, hjdata.2.2.1⟩
  · right
    rw [Nat.mem_smoothNumbers'] at hsmooth
    push Not at hsmooth
    obtain ⟨p, hpPrime, hpDiv, hpNotLt⟩ := hsmooth
    refine ⟨p, hpPrime, ?_, hpDiv⟩
    have hyp : y < p := by omega
    by_contra hpz
    have hpz' : p ≤ z := by omega
    exact hjdata.2.2.2 p (Nat.mem_primesLE.mpr ⟨hpz', hpPrime⟩) hyp hpDiv

/-- Under the standard `U < z²` separation, a survivor has at most one
prime divisor larger than `z`; this is the uniqueness used to index the
residual fibres by `m`. -/
theorem largePrimeDivisor_unique {U z j p q : ℕ}
    (hjpos : 0 < j) (hjU : j ≤ U) (hU : U < z * z)
    (hp : p.Prime) (hzp : z < p) (hpj : p ∣ j)
    (hq : q.Prime) (hzq : z < q) (hqj : q ∣ j) :
    p = q := by
  by_contra hpq
  have hpqdvd : p * q ∣ j := hp.dvd_mul_of_dvd_ne hpq hq hpj hqj
  have hpqle : p * q ≤ j := Nat.le_of_dvd hjpos hpqdvd
  have hzzlt : z * z < p * q := by nlinarith
  omega

/-- The prime fibre `R_m` after the deterministic initial sieve. -/
def residualPrimeFiber (U y z m : ℕ) : Finset ℕ :=
  (Nat.primesLE U).filter fun p =>
    z < p ∧ m * p ≤ U ∧ Nat.Coprime (m * p - 1) (primorial y)

theorem mem_residualPrimeFiber {U y z m p : ℕ} :
    p ∈ residualPrimeFiber U y z m ↔
      p ≤ U ∧ p.Prime ∧ z < p ∧ m * p ≤ U ∧
        Nat.Coprime (m * p - 1) (primorial y) := by
  rw [residualPrimeFiber, Finset.mem_filter, Nat.mem_primesLE]
  tauto

/-- Every nonsmooth survivor has an exact residual-fibre representation. -/
theorem initialSieveSurvivor_exists_residualPrimeFiber
    {U y z j : ℕ} (hj : j ∈ initialSieveSurvivors U y z)
    (hjnot : j ∉ smoothResidualException U y) :
    ∃ m p : ℕ, p ∈ residualPrimeFiber U y z m ∧ j = m * p := by
  have hjdata := mem_initialSieveSurvivors.mp hj
  obtain hsmooth | ⟨p, hpPrime, hzp, hpDiv⟩ :=
    initialSieveSurvivor_smooth_or_largePrime hj
  · exact (hjnot hsmooth).elim
  · let m := j / p
    have hjmp : j = m * p := by
      dsimp [m]
      rw [Nat.div_mul_cancel hpDiv]
    have hpj : p ≤ j := Nat.le_of_dvd (by omega) hpDiv
    refine ⟨m, p, ?_, hjmp⟩
    rw [mem_residualPrimeFiber]
    refine ⟨hpj.trans hjdata.2.1, hpPrime, hzp, ?_, ?_⟩
    · simpa [← hjmp] using hjdata.2.1
    · simpa [← hjmp] using hjdata.2.2.1

/-- The cofactor left after removing the unique prime above `z` is smooth. -/
theorem residualCofactor_smooth
    {U y z j p : ℕ} (hj : j ∈ initialSieveSurvivors U y z)
    (hU : U < z * z) (hp : p.Prime) (hzp : z < p) (hpj : p ∣ j) :
    j / p ∈ Nat.smoothNumbers (y + 1) := by
  have hjdata := mem_initialSieveSurvivors.mp hj
  let m := j / p
  have hjmp : j = m * p := by
    dsimp [m]
    rw [Nat.div_mul_cancel hpj]
  have hmpos : 0 < m := by
    have hjpos : 0 < j := by omega
    have hppos : 0 < p := hp.pos
    nlinarith
  rw [Nat.mem_smoothNumbers']
  intro r hrPrime hrm
  have hrj : r ∣ j := by
    rw [hjmp]
    exact dvd_mul_of_dvd_left hrm p
  by_contra hry
  have hyr : y < r := by omega
  have hzr : z < r := by
    by_contra hrz
    have hrz' : r ≤ z := by omega
    exact hjdata.2.2.2 r (Nat.mem_primesLE.mpr ⟨hrz', hrPrime⟩) hyr hrj
  have hrp : r = p := largePrimeDivisor_unique (by omega) hjdata.2.1 hU
    hrPrime hzr hrj hp hzp hpj
  subst r
  have hpm : p ≤ m := Nat.le_of_dvd hmpos hrm
  have hpple : p * p ≤ m * p := Nat.mul_le_mul_right p hpm
  have hzzlt : z * z < p * p := by nlinarith
  omega

/-- Full exact decomposition of a nonsmooth survivor into a smooth cofactor
and a member of its residual prime fibre. -/
theorem initialSieveSurvivor_residual_decomposition
    {U y z j : ℕ} (hj : j ∈ initialSieveSurvivors U y z)
    (hjnot : j ∉ smoothResidualException U y) (hU : U < z * z) :
    ∃ m p : ℕ, m ∈ Nat.smoothNumbers (y + 1) ∧
      p ∈ residualPrimeFiber U y z m ∧ j = m * p := by
  obtain ⟨m, p, hpFiber, hjmp⟩ :=
    initialSieveSurvivor_exists_residualPrimeFiber hj hjnot
  have hpData := mem_residualPrimeFiber.mp hpFiber
  have hpdvd : p ∣ j := by
    rw [hjmp]
    exact dvd_mul_left p m
  refine ⟨m, p, ?_, hpFiber, hjmp⟩
  have hcofactor :=
    residualCofactor_smooth hj hU hpData.2.1 hpData.2.2.1 hpdvd
  rw [hjmp, Nat.mul_div_left m hpData.2.1.pos] at hcofactor
  exact hcofactor

/-- The cofactor `m` is even: the initial residue at `2` forces `mp` to be
even, while the large prime `p` is odd. -/
theorem residualCofactor_even
    {U y z j m p : ℕ} (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hj : j ∈ initialSieveSurvivors U y z)
    (hpFiber : p ∈ residualPrimeFiber U y z m) (hjmp : j = m * p) :
    Even m := by
  have hjdata := mem_initialSieveSurvivors.mp hj
  have hpData := mem_residualPrimeFiber.mp hpFiber
  have htwoPrimorial : 2 ∣ primorial y :=
    Nat.prime_two.dvd_primorial_iff.mpr hy
  have hcopTwo : Nat.Coprime (j - 1) 2 :=
    hjdata.2.2.1.of_dvd_right htwoPrimorial
  have hpredOdd : Odd (j - 1) := hcopTwo.odd_of_right
  have hjEven : Even j := by
    have := hpredOdd.add_one
    simpa [Nat.sub_add_cancel hjdata.1] using this
  have hpOdd : Odd p := hpData.2.1.odd_iff.mpr (by omega)
  by_contra hmEven
  have hmOdd : Odd m := Nat.not_even_iff_odd.mp hmEven
  have hjOdd : Odd j := by
    rw [hjmp]
    exact hmOdd.mul hpOdd
  exact (Nat.not_odd_iff_even.mpr hjEven) hjOdd

/-- The deterministic first sieve as a partial residue cover.  Primes through
`y` receive residue `1`, and primes in `(y,z]` receive residue `0`; precisely
the offsets outside `initialSieveSurvivors` are thereby covered. -/
def initialSievePartialCover (U y z : ℕ) (hyz : y ≤ z) :
    PartialResidueCover
      (Finset.Icc 1 U \ initialSieveSurvivors U y z) where
  primes := Nat.primesLE z
  residue p := if p ≤ y then 1 else 0
  prime p hp := (Nat.mem_primesLE.mp hp).2
  covers j hj := by
    obtain ⟨hjRange, hjNotSurvivor⟩ := Finset.mem_sdiff.mp hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjRange).1
    by_cases hcop : Nat.Coprime (j - 1) (primorial y)
    · have hnotAll : ¬(∀ p ∈ Nat.primesLE z, y < p → ¬p ∣ j) := by
        intro hall
        exact hjNotSurvivor (Finset.mem_filter.mpr ⟨hjRange, hcop, hall⟩)
      push Not at hnotAll
      obtain ⟨p, hpP, hyp, hpj⟩ := hnotAll
      refine ⟨p, hpP, ?_⟩
      simp only [not_le.mpr hyp, ↓reduceIte]
      exact Nat.modEq_zero_iff_dvd.mpr hpj
    · obtain ⟨p, hpPrime, hpPred, hpPrimorial⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpy : p ≤ y := hpPrime.dvd_primorial_iff.mp hpPrimorial
      have hpP : p ∈ Nat.primesLE z :=
        Nat.mem_primesLE.mpr ⟨hpy.trans hyz, hpPrime⟩
      refine ⟨p, hpP, ?_⟩
      simp only [hpy, ↓reduceIte]
      have hzero : j - 1 ≡ 0 [MOD p] :=
        Nat.modEq_zero_iff_dvd.mpr hpPred
      simpa [Nat.sub_add_cancel hj1] using hzero.add_right 1

/-- Assemble the deterministic initial sieve with any cover of the survivor
set whose prime support lies strictly above `z`. -/
theorem residueCover_of_initial_and_survivor_cover
    {U y z : ℕ} (hyz : y ≤ z)
    (survivorCover : PartialResidueCover (initialSieveSurvivors U y z))
    (hsupport : ∀ p ∈ survivorCover.primes, z < p) :
    ∃ cover : ResidueCover U,
      cover.primes = Nat.primesLE z ∪ survivorCover.primes := by
  have hdisjoint : Disjoint (Nat.primesLE z) survivorCover.primes := by
    rw [Finset.disjoint_left]
    intro p hpSmall hpLarge
    have hpz : p ≤ z := (Nat.mem_primesLE.mp hpSmall).1
    exact (not_lt_of_ge hpz) (hsupport p hpLarge)
  let combined :=
    (initialSievePartialCover U y z hyz).union survivorCover hdisjoint
  have hsubset : initialSieveSurvivors U y z ⊆ Finset.Icc 1 U := by
    intro j hj
    exact Finset.mem_Icc.mpr
      ⟨(mem_initialSieveSurvivors.mp hj).1,
        (mem_initialSieveSurvivors.mp hj).2.1⟩
  have hunion :
      (Finset.Icc 1 U \ initialSieveSurvivors U y z) ∪
        initialSieveSurvivors U y z = Finset.Icc 1 U :=
    Finset.sdiff_union_of_subset hsubset
  refine ⟨(combined.reindex hunion).toResidueCover, ?_⟩
  rfl

/-! ## Finite probability endpoint

The Maynard covering argument first constructs probability measures on a
finite family of residue choices.  The following lemmas isolate the entirely
finite part of that argument from the missing analytic estimates. -/

/-- Normalize a finite nonnegative weight into a probability mass. -/
noncomputable def normalizeFiniteWeight
    {α : Type*} [Fintype α] (weight : α → ℝ) (a : α) : ℝ :=
  weight a / ∑ b, weight b

theorem normalizeFiniteWeight_nonneg
    {α : Type*} [Fintype α] (weight : α → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (a : α) :
    0 ≤ normalizeFiniteWeight weight a := by
  exact div_nonneg (hweight a) (Finset.sum_nonneg fun b _ => hweight b)

theorem sum_normalizeFiniteWeight_eq_one
    {α : Type*} [Fintype α] (weight : α → ℝ)
    (hsum : 0 < ∑ a, weight a) :
    ∑ a, normalizeFiniteWeight weight a = 1 := by
  simp only [normalizeFiniteWeight]
  rw [← Finset.sum_div]
  exact div_self hsum.ne'

/-- The normalized mass of a nonnegative raw weight.  Unlike
`normalizedSquareMass`, this form is convenient when the raw Selberg weight
already contains a finite sum of squares. -/
noncomputable def normalizedRawMass
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (weight : ∀ q, A q → ℝ) (q : Q) (a : A q) : ℝ :=
  normalizeFiniteWeight (weight q) a

theorem normalizedRawMass_nonneg
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (weight : ∀ q, A q → ℝ) (hweight : ∀ q a, 0 ≤ weight q a)
    (q : Q) (a : A q) :
    0 ≤ normalizedRawMass weight q a := by
  exact normalizeFiniteWeight_nonneg _ (hweight q) a

theorem sum_normalizedRawMass_eq_one
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (weight : ∀ q, A q → ℝ)
    (hsum : ∀ q, 0 < ∑ a, weight q a) (q : Q) :
    ∑ a, normalizedRawMass weight q a = 1 := by
  exact sum_normalizeFiniteWeight_eq_one _ (hsum q)

/-- A finite family of square weights has positive total mass as soon as one
weight is nonzero. -/
theorem sum_sq_pos_of_exists_ne_zero
    {α : Type*} [Fintype α] (weight : α → ℝ)
    (h : ∃ a, weight a ≠ 0) :
    0 < ∑ a, weight a ^ 2 := by
  obtain ⟨a, ha⟩ := h
  apply Finset.sum_pos' (fun b _ => sq_nonneg (weight b))
  exact ⟨a, Finset.mem_univ a, sq_pos_of_ne_zero ha⟩

/-- Probability mass obtained by normalizing the square of a finite family of
amplitudes, matching the Selberg-weight construction. -/
noncomputable def normalizedSquareMass
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (amplitude : ∀ q, A q → ℝ) (q : Q) (a : A q) : ℝ :=
  normalizeFiniteWeight (fun b => amplitude q b ^ 2) a

theorem normalizedSquareMass_nonneg
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (amplitude : ∀ q, A q → ℝ) (q : Q) (a : A q) :
    0 ≤ normalizedSquareMass amplitude q a := by
  exact normalizeFiniteWeight_nonneg _ (fun b => sq_nonneg _) a

theorem sum_normalizedSquareMass_eq_one
    {Q : Type*} [Fintype Q] {A : Q → Type*} [∀ q, Fintype (A q)]
    (amplitude : ∀ q, A q → ℝ)
    (hnonzero : ∀ q, ∃ a, amplitude q a ≠ 0) (q : Q) :
    ∑ a, normalizedSquareMass amplitude q a = 1 := by
  exact sum_normalizeFiniteWeight_eq_one _
    (sum_sq_pos_of_exists_ne_zero _ (hnonzero q))

/-! ## Exact doubled Selberg weights

These definitions are the finite algebraic objects in Maynard's large-gap
measure.  The first divisor tuple detects the forms `n + h*q`; the second
detects the companion forms `m*(n+h*q)-1`.  Keeping both finite supports
explicit makes every sum below kernel-reducible and separates the later
uniform asymptotic estimates from the probability argument. -/

/-- Simultaneous divisibility conditions for one pair of divisor tuples. -/
def largeGapDivisorCondition (H : Finset ℕ) (m q n : ℕ)
    (d e : H → ℕ) : Prop :=
  ∀ h : H,
    d h ∣ n + h.1 * q ∧ e h ∣ m * (n + h.1 * q) - 1

instance (H : Finset ℕ) (m q n : ℕ) (d e : H → ℕ) :
    Decidable (largeGapDivisorCondition H m q n d e) := by
  unfold largeGapDivisorCondition
  infer_instance

/-- The inner doubled Selberg divisor sum. -/
noncomputable def doubledSelbergInner (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q n : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ D, ∑ e ∈ E,
    if largeGapDivisorCondition H m q n d e then lambda d e else 0

/-- Maynard's nonnegative doubled square weight at an integer `n`. -/
noncomputable def doubledSelbergWeight (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q n : ℕ) : ℝ :=
  doubledSelbergInner H D E lambda m q n ^ 2

theorem doubledSelbergWeight_nonneg (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q n : ℕ) :
    0 ≤ doubledSelbergWeight H D E lambda m q n := by
  exact sq_nonneg _

/-- Expanding the square gives the exact four-tuple divisor sum used before
the CRT count in the normalization argument. -/
theorem doubledSelbergWeight_eq_quadrupleSum (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q n : ℕ) :
    doubledSelbergWeight H D E lambda m q n =
      ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        if largeGapDivisorCondition H m q n d e ∧
            largeGapDivisorCondition H m q n d' e' then
          lambda d e * lambda d' e'
        else 0 := by
  classical
  unfold doubledSelbergWeight doubledSelbergInner
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hde : largeGapDivisorCondition H m q n d e
  · by_cases hde' : largeGapDivisorCondition H m q n d' e'
    · simp [hde, hde']
    · simp [hde, hde']
  · simp [hde]

/-! ### CRT form of the doubled divisor conditions -/

/-- The unique residue modulo `e` for which the companion linear form
`m * (n + c)` is congruent to one.  It is used only when `m` is coprime to
`e`, as imposed by the doubled Selberg support. -/
noncomputable def companionResidue (m e c : ℕ) : ℕ :=
  (((m : ZMod e)⁻¹ - (c : ZMod e))).val

theorem companionResidue_lt {m e c : ℕ} (he : 0 < e) :
    companionResidue m e c < e := by
  let _ : NeZero e := ⟨he.ne'⟩
  exact ZMod.val_lt _

/-- The modular inverse defining `companionResidue` solves its companion
linear congruence. -/
theorem companionResidue_spec {m e c : ℕ}
    (he : 0 < e) (hme : m.Coprime e) :
    m * (companionResidue m e c + c) ≡ 1 [MOD e] := by
  let _ : NeZero e := ⟨he.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [show (companionResidue m e c : ZMod e) =
      (m : ZMod e)⁻¹ - (c : ZMod e) by
    exact ZMod.natCast_zmod_val _]
  have hmUnit : IsUnit (m : ZMod e) :=
    (ZMod.isUnit_iff_coprime m e).2 hme
  rw [sub_add_cancel]
  exact ZMod.mul_inv_of_unit (m : ZMod e) hmUnit

/-- Divisibility by the companion modulus is exactly membership in the
inverse residue class.  The positivity hypotheses exclude the sole natural
subtraction edge case at zero. -/
theorem modEq_companionResidue_iff_dvd_sub {m e c n : ℕ}
    (hm : 0 < m) (he : 0 < e) (hme : m.Coprime e)
    (hnc : 0 < n + c) :
    n ≡ companionResidue m e c [MOD e] ↔
      e ∣ m * (n + c) - 1 := by
  have hnprod : 1 ≤ m * (n + c) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hnc.ne')
  have hrmod := companionResidue_spec (m := m) (c := c) he hme
  constructor
  · intro hn
    have hadd : n + c ≡ companionResidue m e c + c [MOD e] :=
      hn.add_right c
    have hmul : m * (n + c) ≡
        m * (companionResidue m e c + c) [MOD e] :=
      hadd.mul_left m
    have hone : m * (n + c) ≡ 1 [MOD e] := hmul.trans hrmod
    have hzero := hone.sub hnprod (by omega) (Nat.ModEq.refl 1)
    exact Nat.modEq_zero_iff_dvd.mp hzero
  · intro hdiv
    have hzero : m * (n + c) - 1 ≡ 0 [MOD e] :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    have hone : m * (n + c) ≡ 1 [MOD e] := by
      have hadd := hzero.add_right 1
      simpa [Nat.sub_add_cancel hnprod] using hadd
    have hmul : m * (n + c) ≡
        m * (companionResidue m e c + c) [MOD e] :=
      hone.trans hrmod.symm
    have hadd : n + c ≡ companionResidue m e c + c [MOD e] := by
      exact Nat.ModEq.cancel_left_of_coprime hme.symm hmul
    exact Nat.ModEq.add_right_cancel' c hadd

/-- After expanding the square, the two copies of each divisor tuple combine
coordinatewise by least common multiples. -/
theorem largeGapDivisorCondition_pair_iff_lcm
    (H : Finset ℕ) (m q n : ℕ) (d e d' e' : H → ℕ) :
    largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e' ↔
      ∀ h : H,
        Nat.lcm (d h) (d' h) ∣ n + h.1 * q ∧
        Nat.lcm (e h) (e' h) ∣ m * (n + h.1 * q) - 1 := by
  constructor
  · rintro ⟨hde, hde'⟩ h
    exact ⟨Nat.lcm_dvd (hde h).1 (hde' h).1,
      Nat.lcm_dvd (hde h).2 (hde' h).2⟩
  · intro hlcm
    constructor
    · intro h
      exact ⟨(Nat.lcm_dvd_iff.mp (hlcm h).1).1,
        (Nat.lcm_dvd_iff.mp (hlcm h).2).1⟩
    · intro h
      exact ⟨(Nat.lcm_dvd_iff.mp (hlcm h).1).2,
        (Nat.lcm_dvd_iff.mp (hlcm h).2).2⟩

/-- If two first-form divisor tuples occur simultaneously, then their
different coordinates are cross-coprime.  Besides the standard
shift-difference pre-sieve, the large prime `q` must be coprime to both tuple
products because the shifts are `h*q`. -/
theorem firstForms_crossCoordinateCoprime_of_conditions
    {H : Finset ℕ} {RD W m q n : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (hcoverage : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d))
    (hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d'))
    (hcond : largeGapDivisorCondition H m q n d e)
    (hcond' : largeGapDivisorCondition H m q n d' e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' := by
  intro a b hab
  constructor
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpa' : p ∣ n + a.1 * q := dvd_trans hpa (hcond a).1
    have hpb' : p ∣ n + b.1 * q := dvd_trans hpb (hcond' b).1
    have hdist : p ∣ Nat.dist (a.1 * q) (b.1 * q) := by
      by_cases hab' : a.1 * q ≤ b.1 * q
      · have hsub : p ∣ (n + b.1 * q) - (n + a.1 * q) :=
          Nat.dvd_sub hpb' hpa'
        rw [Nat.dist_eq_sub_of_le hab']
        simpa [Nat.add_sub_add_left] using hsub
      · have hle : b.1 * q ≤ a.1 * q := le_of_not_ge hab'
        have hsub : p ∣ (n + a.1 * q) - (n + b.1 * q) :=
          Nat.dvd_sub hpa' hpb'
        rw [Nat.dist_comm (a.1 * q) (b.1 * q),
          Nat.dist_eq_sub_of_le hle]
        simpa [Nat.add_sub_add_left] using hsub
    rw [Nat.dist_mul_right] at hdist
    obtain hpdist | hpq := hp.dvd_mul.mp hdist
    · have hpW : p ∣ W := hcoverage hab p hp hpdist
      have hpcop : p.Coprime W :=
        (hd.coordinate_coprime_W a).coprime_dvd_left hpa
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
    · have hqa : q.Coprime (d a) :=
        Nat.Coprime.of_dvd_right
          (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d a) hqD
      have hpqcop : p.Coprime q :=
        Nat.Coprime.of_dvd_left hpa hqa.symm
      exact (hp.coprime_iff_not_dvd.mp hpqcop) hpq
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpa' : p ∣ n + a.1 * q := dvd_trans hpa (hcond' a).1
    have hpb' : p ∣ n + b.1 * q := dvd_trans hpb (hcond b).1
    have hdist : p ∣ Nat.dist (a.1 * q) (b.1 * q) := by
      by_cases hab' : a.1 * q ≤ b.1 * q
      · have hsub : p ∣ (n + b.1 * q) - (n + a.1 * q) :=
          Nat.dvd_sub hpb' hpa'
        rw [Nat.dist_eq_sub_of_le hab']
        simpa [Nat.add_sub_add_left] using hsub
      · have hle : b.1 * q ≤ a.1 * q := le_of_not_ge hab'
        have hsub : p ∣ (n + a.1 * q) - (n + b.1 * q) :=
          Nat.dvd_sub hpa' hpb'
        rw [Nat.dist_comm (a.1 * q) (b.1 * q),
          Nat.dist_eq_sub_of_le hle]
        simpa [Nat.add_sub_add_left] using hsub
    rw [Nat.dist_mul_right] at hdist
    obtain hpdist | hpq := hp.dvd_mul.mp hdist
    · have hpW : p ∣ W := hcoverage hab p hp hpdist
      have hpcop : p.Coprime W :=
        (hd'.coordinate_coprime_W a).coprime_dvd_left hpa
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
    · have hqa : q.Coprime (d' a) :=
        Nat.Coprime.of_dvd_right
          (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d' a) hqD'
      have hpqcop : p.Coprime q :=
        Nat.Coprime.of_dvd_left hpa hqa.symm
      exact (hp.coprime_iff_not_dvd.mp hpqcop) hpq

/-- The analogous support lemma for the companion forms
`m*(n+h*q)-1`.  Their difference has the three factors `m`, `q`, and the
shift difference, all of which are excluded by the hypotheses. -/
theorem companionForms_crossCoordinateCoprime_of_conditions
    {H : Finset ℕ} {RE W m q n : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hn : 0 < n) (hq : 0 < q)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e')
    (hcoverage : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e))
    (hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e'))
    (hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e))
    (hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e'))
    (hcond : largeGapDivisorCondition H m q n d e)
    (hcond' : largeGapDivisorCondition H m q n d' e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' := by
  intro a b hab
  have hdist_dvd {f g : H → ℕ}
      (ha : ∀ x : H, f x ∣ m * (n + x.1 * q) - 1)
      (hb : ∀ x : H, g x ∣ m * (n + x.1 * q) - 1)
      {a b : H} : ∀ p, p ∣ f a → p ∣ g b →
        p ∣ m * (Nat.dist a.1 b.1 * q) := by
    intro p hpea hpeb
    have hpa' : p ∣ m * (n + a.1 * q) - 1 := dvd_trans hpea (ha a)
    have hpb' : p ∣ m * (n + b.1 * q) - 1 := dvd_trans hpeb (hb b)
    have hAone : 1 ≤ m * (n + a.1 * q) :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hm.ne' (by omega))
    have hBone : 1 ≤ m * (n + b.1 * q) :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hm.ne' (by omega))
    by_cases hab' : a.1 * q ≤ b.1 * q
    · have hsub : p ∣
          (m * (n + b.1 * q) - 1) - (m * (n + a.1 * q) - 1) :=
        Nat.dvd_sub hpb' hpa'
      have habval : a.1 ≤ b.1 := Nat.le_of_mul_le_mul_right hab' hq
      rw [Nat.sub_sub_sub_cancel_right hAone] at hsub
      rw [← Nat.mul_sub_left_distrib, Nat.add_sub_add_left,
        ← Nat.mul_sub_right_distrib] at hsub
      rw [Nat.dist_eq_sub_of_le habval]
      exact hsub
    · have hle : b.1 * q ≤ a.1 * q := le_of_not_ge hab'
      have hsub : p ∣
          (m * (n + a.1 * q) - 1) - (m * (n + b.1 * q) - 1) :=
        Nat.dvd_sub hpa' hpb'
      have hbaval : b.1 ≤ a.1 := Nat.le_of_mul_le_mul_right hle hq
      rw [Nat.sub_sub_sub_cancel_right hBone] at hsub
      rw [← Nat.mul_sub_left_distrib, Nat.add_sub_add_left,
        ← Nat.mul_sub_right_distrib] at hsub
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hbaval]
      exact hsub
  constructor
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hdiv : p ∣ m * (Nat.dist a.1 b.1 * q) :=
      hdist_dvd (fun x => (hcond x).2) (fun x => (hcond' x).2)
        p hpa hpb
    obtain hpm | hprest := hp.dvd_mul.mp hdiv
    · have hma : m.Coprime (e a) := Nat.Coprime.of_dvd_right
          (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e a) hmE
      have hpcop : p.Coprime m := Nat.Coprime.of_dvd_left hpa hma.symm
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpm
    · obtain hpdist | hpq := hp.dvd_mul.mp hprest
      · have hpW := hcoverage hab p hp hpdist
        have hpcop : p.Coprime W :=
          (he.coordinate_coprime_W a).coprime_dvd_left hpa
        exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
      · have hqa : q.Coprime (e a) := Nat.Coprime.of_dvd_right
            (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e a) hqE
        have hpcop : p.Coprime q := Nat.Coprime.of_dvd_left hpa hqa.symm
        exact (hp.coprime_iff_not_dvd.mp hpcop) hpq
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hdiv : p ∣ m * (Nat.dist a.1 b.1 * q) :=
      hdist_dvd (fun x => (hcond' x).2) (fun x => (hcond x).2)
        p hpa hpb
    obtain hpm | hprest := hp.dvd_mul.mp hdiv
    · have hma : m.Coprime (e' a) := Nat.Coprime.of_dvd_right
          (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' a) hmE'
      have hpcop : p.Coprime m := Nat.Coprime.of_dvd_left hpa hma.symm
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpm
    · obtain hpdist | hpq := hp.dvd_mul.mp hprest
      · have hpW := hcoverage hab p hp hpdist
        have hpcop : p.Coprime W :=
          (he'.coordinate_coprime_W a).coprime_dvd_left hpa
        exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
      · have hqa : q.Coprime (e' a) := Nat.Coprime.of_dvd_right
            (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' a) hqE'
        have hpcop : p.Coprime q := Nat.Coprime.of_dvd_left hpa hqa.symm
        exact (hp.coprime_iff_not_dvd.mp hpcop) hpq

/-- Coordinates of the combined CRT system: the left copy records the first
linear forms and the right copy records their companions. -/
abbrev LargeGapCrtIndex (H : Finset ℕ) := Sum H H

def largeGapCrtModulus (H : Finset ℕ) (d e d' e' : H → ℕ) :
    LargeGapCrtIndex H → ℕ
  | Sum.inl h => Nat.lcm (d h) (d' h)
  | Sum.inr h => Nat.lcm (e h) (e' h)

noncomputable def largeGapCrtResidue (H : Finset ℕ)
    (m q : ℕ) (d e d' e' : H → ℕ) : LargeGapCrtIndex H → ℕ
  | Sum.inl h => BoundedGaps.Maynard.negativeShiftResidue
      (Nat.lcm (d h) (d' h)) (h.1 * q)
  | Sum.inr h => companionResidue m (Nat.lcm (e h) (e' h)) (h.1 * q)

/-- The expanded doubled divisor condition is precisely the coordinatewise
congruence system consumed by the generic pre-sieved CRT theorem. -/
theorem largeGapDivisorCondition_pair_iff_modEq
    (H : Finset ℕ) (m q n : ℕ) (d e d' e' : H → ℕ)
    (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hnshift : ∀ h : H, 0 < n + h.1 * q) :
    largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e' ↔
      ∀ i : LargeGapCrtIndex H,
        n ≡ largeGapCrtResidue H m q d e d' e' i
          [MOD largeGapCrtModulus H d e d' e' i] := by
  rw [largeGapDivisorCondition_pair_iff_lcm]
  constructor
  · intro hdiv i
    cases i with
    | inl h =>
        exact (BoundedGaps.Maynard.modEq_negativeShiftResidue_iff_dvd_add
          _ _ _ (hDpos h)).2 (hdiv h).1
    | inr h =>
        exact (modEq_companionResidue_iff_dvd_sub hm (hEpos h)
          (hmE h) (hnshift h)).2 (hdiv h).2
  · intro hmod h
    exact ⟨
      (BoundedGaps.Maynard.modEq_negativeShiftResidue_iff_dvd_add
        _ _ _ (hDpos h)).1 (hmod (Sum.inl h)),
      (modEq_companionResidue_iff_dvd_sub hm (hEpos h)
        (hmE h) (hnshift h)).1 (hmod (Sum.inr h))⟩

/-- A duplicate-free list of every coordinate in the doubled CRT system. -/
noncomputable def largeGapCrtList (H : Finset ℕ) :
    List (LargeGapCrtIndex H) :=
  (Finset.univ : Finset (LargeGapCrtIndex H)).toList

/-- Pairwise coprimality of the doubled coordinate moduli, together with
coprimality from the pre-sieving modulus. -/
def LargeGapCrtCompatible (H : Finset ℕ) (W : ℕ)
    (d e d' e' : H → ℕ) : Prop :=
  BoundedGaps.Maynard.IsPreSievedModuliCompatible W
    (largeGapCrtModulus H d e d' e') (largeGapCrtList H)

/-- A direct constructor for the doubled CRT compatibility predicate. -/
theorem largeGapCrtCompatible_of_pairwise
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hW : ∀ i : LargeGapCrtIndex H,
      Nat.Coprime W (largeGapCrtModulus H d e d' e' i))
    (hpair : ∀ i j : LargeGapCrtIndex H, i ≠ j →
      Nat.Coprime (largeGapCrtModulus H d e d' e' i)
        (largeGapCrtModulus H d e d' e' j)) :
    LargeGapCrtCompatible H W d e d' e' := by
  unfold LargeGapCrtCompatible
    BoundedGaps.Maynard.IsPreSievedModuliCompatible
  constructor
  · intro i hi
    exact hW i
  · apply (Finset.univ : Finset (LargeGapCrtIndex H)).nodup_toList.pairwise_of_forall_ne
    intro i hi j hj hij
    exact hpair i j hij

/-- Any two distinct coordinate moduli in a compatible doubled CRT system
are coprime. -/
theorem largeGapCrtCompatible_pairwise
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hc : LargeGapCrtCompatible H W d e d' e')
    {i j : LargeGapCrtIndex H} (hij : i ≠ j) :
    Nat.Coprime (largeGapCrtModulus H d e d' e' i)
      (largeGapCrtModulus H d e d' e' j) := by
  have hpair := hc.2
  have hnodup : (largeGapCrtList H).Nodup := by
    unfold largeGapCrtList
    exact (Finset.univ : Finset (LargeGapCrtIndex H)).nodup_toList
  have hset :=
    (List.pairwise_iff_coe_toFinset_pairwise hnodup).mpr hpair
  apply hset
  · simp [largeGapCrtList]
  · simp [largeGapCrtList]
  · exact hij

theorem firstForms_crossCoordinateCoprime_of_crtCompatible
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hc : LargeGapCrtCompatible H W d e d' e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' := by
  intro a b hab
  have hcop := show Nat.Coprime
      (largeGapCrtModulus H d e d' e' (Sum.inl a))
      (largeGapCrtModulus H d e d' e' (Sum.inl b)) from
    largeGapCrtCompatible_pairwise H W d e d' e' hc (by
      intro heq
      exact hab (Sum.inl.inj heq))
  change Nat.Coprime (Nat.lcm (d a) (d' a))
    (Nat.lcm (d b) (d' b)) at hcop
  exact ⟨
    Nat.Coprime.of_dvd (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _) hcop,
    Nat.Coprime.of_dvd (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_left _ _) hcop⟩

theorem companionForms_crossCoordinateCoprime_of_crtCompatible
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hc : LargeGapCrtCompatible H W d e d' e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' := by
  intro a b hab
  have hcop := show Nat.Coprime
      (largeGapCrtModulus H d e d' e' (Sum.inr a))
      (largeGapCrtModulus H d e d' e' (Sum.inr b)) from
    largeGapCrtCompatible_pairwise H W d e d' e' hc (by
      intro heq
      exact hab (Sum.inr.inj heq))
  change Nat.Coprime (Nat.lcm (e a) (e' a))
    (Nat.lcm (e b) (e' b)) at hcop
  exact ⟨
    Nat.Coprime.of_dvd (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _) hcop,
    Nat.Coprime.of_dvd (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_left _ _) hcop⟩

/-- It is enough to check compatibility separately within the first family,
within the companion family, and across the two families. -/
theorem largeGapCrtCompatible_of_two_families
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hWD : ∀ h : H, Nat.Coprime W (Nat.lcm (d h) (d' h)))
    (hWE : ∀ h : H, Nat.Coprime W (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      Nat.Coprime (Nat.lcm (d a) (d' a)) (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      Nat.Coprime (Nat.lcm (e a) (e' a)) (Nat.lcm (e b) (e' b)))
    (hDE : ∀ a b : H,
      Nat.Coprime (Nat.lcm (d a) (d' a)) (Nat.lcm (e b) (e' b))) :
    LargeGapCrtCompatible H W d e d' e' := by
  apply largeGapCrtCompatible_of_pairwise
  · intro i
    cases i with
    | inl h => exact hWD h
    | inr h => exact hWE h
  · intro i j hij
    cases i with
    | inl a =>
        cases j with
        | inl b =>
            apply hDD
            intro hab
            subst b
            exact hij rfl
        | inr b => exact hDE a b
    | inr a =>
        cases j with
        | inl b => exact (hDE b a).symm
        | inr b =>
            apply hEE
            intro hab
            subst b
            exact hij rfl

/-- Maynard tuple support supplies all within-family coprimality conditions;
only the four cross-family coordinate conditions remain to be checked. -/
theorem largeGapCrtCompatible_of_maynard_tuples
    {H : Finset ℕ} {W RD RE : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e')
    (hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e')
    (hde : ∀ a b : H, Nat.Coprime (d a) (e b))
    (hde' : ∀ a b : H, Nat.Coprime (d a) (e' b))
    (hd'e : ∀ a b : H, Nat.Coprime (d' a) (e b))
    (hd'e' : ∀ a b : H, Nat.Coprime (d' a) (e' b)) :
    LargeGapCrtCompatible H W d e d' e' := by
  apply largeGapCrtCompatible_of_two_families
  · intro h
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d h) (d' h))
    exact (hd.coordinate_coprime_W h).symm.mul_right
      (hd'.coordinate_coprime_W h).symm
  · intro h
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
    exact (he.coordinate_coprime_W h).symm.mul_right
      (he'.coordinate_coprime_W h).symm
  · intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hd.coordinates_coprime hab) (hDD hab).1
      (hDD hab).2 (hd'.coordinates_coprime hab)
  · intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (he.coordinates_coprime hab) (hEE hab).1
      (hEE hab).2 (he'.coordinates_coprime hab)
  · intro a b
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hde a b) (hde' a b) (hd'e a b) (hd'e' a b)

/-- The simultaneous CRT representative for one allowed pre-sieving residue
and all first/companion divisor coordinates. -/
noncomputable def largeGapFullCrtResidue (H : Finset ℕ)
    (W v m q : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e') : ℕ :=
  Nat.chineseRemainderOfList
    (BoundedGaps.Maynard.preSievedResidue v
      (largeGapCrtResidue H m q d e d' e'))
    (BoundedGaps.Maynard.preSievedModulus W
      (largeGapCrtModulus H d e d' e'))
    (BoundedGaps.Maynard.preSievedModulusList (largeGapCrtList H))
    (BoundedGaps.Maynard.preSievedModulusList_pairwise W
      (largeGapCrtModulus H d e d' e') (largeGapCrtList H) hcompat)

/-- Product modulus of the full doubled CRT system. -/
noncomputable def largeGapFullCrtModulus (H : Finset ℕ) (W : ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  ((BoundedGaps.Maynard.preSievedModulusList (largeGapCrtList H)).map
    (BoundedGaps.Maynard.preSievedModulus W
      (largeGapCrtModulus H d e d' e'))).prod

theorem largeGapFullCrtModulus_eq (H : Finset ℕ) (W : ℕ)
    (d e d' e' : H → ℕ) :
    largeGapFullCrtModulus H W d e d' e' =
      W * ∏ i : LargeGapCrtIndex H,
        largeGapCrtModulus H d e d' e' i := by
  classical
  rw [largeGapFullCrtModulus,
    BoundedGaps.Maynard.preSievedModulusList_prod]
  simp [largeGapCrtList]

/-- Exact pre-sieved CRT equivalence used to count each quadruple in the
expanded doubled Selberg normalization. -/
theorem modEq_largeGapFullCrtResidue_iff
    (H : Finset ℕ) (W v m q n : ℕ) (d e d' e' : H → ℕ)
    (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hnshift : ∀ h : H, 0 < n + h.1 * q)
    (hcompat : LargeGapCrtCompatible H W d e d' e') :
    n ≡ largeGapFullCrtResidue H W v m q d e d' e' hcompat
        [MOD largeGapFullCrtModulus H W d e d' e'] ↔
      n ≡ v [MOD W] ∧
        largeGapDivisorCondition H m q n d e ∧
          largeGapDivisorCondition H m q n d' e' := by
  have hcrt := BoundedGaps.Maynard.modEq_preSieved_crt_iff
    (largeGapCrtResidue H m q d e d' e')
    (largeGapCrtModulus H d e d' e') (largeGapCrtList H)
    W v n hcompat
  rw [largeGapDivisorCondition_pair_iff_modEq H m q n d e d' e'
    hm hDpos hEpos hmE hnshift]
  simpa [largeGapFullCrtResidue, largeGapFullCrtModulus,
    largeGapCrtList] using hcrt

/-- The small-prime coprimality condition in Maynard's measure (equation
`(4.4)` in the notation reconstructed in `tex/4.tex`). -/
def largeGapPreSieved (w m n : ℕ) : Prop :=
  Nat.Coprime (n * (m * n - 1)) (primorial w)

instance (w m n : ℕ) : Decidable (largeGapPreSieved w m n) := by
  unfold largeGapPreSieved
  infer_instance

/-- The polynomial whose coprimality with the small-prime modulus is imposed
by `largeGapPreSieved`. -/
def preSievePolynomial (m n : ℕ) : ℕ := n * (m * n - 1)

/-- On positive inputs the pre-sieving polynomial respects congruence.  The
positivity is essential because subtraction on `ℕ` is truncated at zero. -/
theorem preSievePolynomial_modEq {W m n v : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hv : 0 < v)
    (hnv : n ≡ v [MOD W]) :
    preSievePolynomial m n ≡ preSievePolynomial m v [MOD W] := by
  have hmn : 1 ≤ m * n :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hn.ne')
  have hmv : 1 ≤ m * v :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hv.ne')
  have hmul : m * n ≡ m * v [MOD W] := hnv.mul_left m
  have hsub : m * n - 1 ≡ m * v - 1 [MOD W] :=
    hmul.sub hmn hmv (Nat.ModEq.refl 1)
  exact hnv.mul hsub

theorem preSievePolynomial_coprime_congr {W m n v : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hv : 0 < v)
    (hnv : n ≡ v [MOD W]) :
    (preSievePolynomial m n).Coprime W ↔
      (preSievePolynomial m v).Coprime W := by
  have hpoly := preSievePolynomial_modEq hm hn hv hnv
  rw [← ZMod.coprime_mod_iff_coprime (preSievePolynomial m n) W,
    ← ZMod.coprime_mod_iff_coprime (preSievePolynomial m v) W]
  exact iff_of_eq (congrArg (fun x => x.Coprime W) hpoly)

/-- Allowed nonzero residue representatives for the pre-sieve.  The zero
class cannot occur when the modulus is greater than one and `n > 0`. -/
def allowedPreSieveResidues (W m : ℕ) : Finset ℕ :=
  (Finset.Ico 1 W).filter fun v => (preSievePolynomial m v).Coprime W

/-- The coprimality pre-sieve is a disjoint union of its allowed residue
classes.  This is the finite decomposition summed before applying CRT. -/
theorem preSieved_iff_exists_allowed_residue {W m n : ℕ}
    (hW : 1 < W) (hm : 0 < m) (hn : 0 < n) :
    (preSievePolynomial m n).Coprime W ↔
      ∃ v ∈ allowedPreSieveResidues W m, n ≡ v [MOD W] := by
  constructor
  · intro hpre
    let v := n % W
    have hWpos : 0 < W := by omega
    have hvlt : v < W := Nat.mod_lt n hWpos
    have hvpos : 0 < v := by
      by_contra hv
      have hvzero : v = 0 := by omega
      have hWdvdn : W ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hvzero
      have hWdvdpoly : W ∣ preSievePolynomial m n :=
        dvd_mul_of_dvd_left hWdvdn _
      have hWone := Nat.eq_one_of_dvd_coprimes hpre hWdvdpoly (dvd_refl W)
      omega
    have hnv : n ≡ v [MOD W] := (Nat.mod_modEq n W).symm
    refine ⟨v, ?_, hnv⟩
    rw [allowedPreSieveResidues, Finset.mem_filter]
    exact ⟨Finset.mem_Ico.mpr ⟨hvpos, hvlt⟩,
      (preSievePolynomial_coprime_congr hm hn hvpos hnv).mp hpre⟩
  · rintro ⟨v, hv, hnv⟩
    have hv' : v ∈ Finset.Ico 1 W ∧
        (preSievePolynomial m v).Coprime W := by
      simpa only [allowedPreSieveResidues, Finset.mem_filter] using hv
    exact (preSievePolynomial_coprime_congr hm hn
      (Finset.mem_Ico.mp hv'.1).1 hnv).mpr hv'.2

theorem one_lt_primorial_of_two_le {w : ℕ} (hw : 2 ≤ w) :
    1 < primorial w := by
  have hdvd : 2 ∣ primorial w :=
    Nat.prime_two.dvd_primorial_iff.mpr hw
  exact (by norm_num : 1 < 2).trans_le
    (Nat.le_of_dvd (primorial_pos w) hdvd)

theorem largeGapPreSieved_iff_exists_allowed_residue
    {w m n : ℕ} (hw : 2 ≤ w) (hm : 0 < m) (hn : 0 < n) :
    largeGapPreSieved w m n ↔
      ∃ v ∈ allowedPreSieveResidues (primorial w) m,
        n ≡ v [MOD primorial w] := by
  simpa [largeGapPreSieved, preSievePolynomial] using
    preSieved_iff_exists_allowed_residue (one_lt_primorial_of_two_le hw) hm hn

/-- Exact finite partition of a pre-sieved interval by its allowed residue
classes.  The auxiliary predicate is where the four divisor conditions will
be inserted. -/
theorem sum_allowed_residue_filter_card
    (W m T : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hW : 1 < W) (hm : 0 < m) :
    (∑ v ∈ allowedPreSieveResidues W m,
      ((Finset.Icc 1 T).filter fun n => n ≡ v [MOD W] ∧ P n).card) =
      ((Finset.Icc 1 T).filter fun n =>
        (preSievePolynomial m n).Coprime W ∧ P n).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ v ∈ allowedPreSieveResidues W m,
        ((Finset.Icc 1 T).filter fun n => n ≡ v [MOD W] ∧ P n).card) =
        ∑ v ∈ allowedPreSieveResidues W m,
          ∑ n ∈ Finset.Icc 1 T, if n ≡ v [MOD W] ∧ P n then 1 else 0 := by
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 T,
          ∑ v ∈ allowedPreSieveResidues W m,
            if n ≡ v [MOD W] ∧ P n then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 T,
          if (preSievePolynomial m n).Coprime W ∧ P n then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
          by_cases hpre : (preSievePolynomial m n).Coprime W
          · obtain ⟨v, hv, hnv⟩ :=
              (preSieved_iff_exists_allowed_residue hW hm hnpos).mp hpre
            rw [Finset.sum_eq_single v]
            · by_cases hp : P n <;> simp [hpre, hnv, hp]
            · intro b hb hbv
              have hbne : ¬n ≡ b [MOD W] := by
                intro hnb
                have hvlt : v < W :=
                  (Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1).2
                have hblt : b < W :=
                  (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).2
                have : v = b := by
                  exact (hnv.symm.trans hnb).eq_of_lt_of_lt hvlt hblt
                exact hbv this.symm
              simp [hbne]
            · intro hnot
              exact (hnot hv).elim
          · have hnone : ∀ v ∈ allowedPreSieveResidues W m,
                ¬n ≡ v [MOD W] := by
              intro v hv hnv
              apply hpre
              exact (preSieved_iff_exists_allowed_residue hW hm hnpos).mpr
                ⟨v, hv, hnv⟩
            rw [if_neg (by simp [hpre])]
            apply Finset.sum_eq_zero
            intro v hv
            simp [hnone v hv]
    _ = ∑ n ∈ Finset.Icc 1 T,
          if (preSievePolynomial m n).Coprime W ∧ P n then 1 else 0 := rfl

/-- Number of positive integers in the normalization interval satisfying the
pre-sieve and one expanded quadruple of doubled Selberg divisibility
conditions. -/
def preSievedLargeGapQuadrupleCount (H : Finset ℕ) (W m q T : ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter fun n =>
    (preSievePolynomial m n).Coprime W ∧
      largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e').card

/-- Cardinality of the single CRT class associated to an allowed small-prime
residue and an expanded divisor quadruple. -/
noncomputable def largeGapCrtClassCount (H : Finset ℕ)
    (W v m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e') : ℕ :=
  ((Finset.Icc 1 T).filter fun n =>
    n ≡ largeGapFullCrtResidue H W v m q d e d' e' hcompat
      [MOD largeGapFullCrtModulus H W d e d' e']).card

/-- The pre-sieved quadruple count is exactly the sum of its one-class CRT
counts.  No asymptotic estimate has entered yet. -/
theorem preSievedLargeGapQuadrupleCount_eq_sum_crt
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hW : 1 < W) (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hcompat : LargeGapCrtCompatible H W d e d' e') :
    preSievedLargeGapQuadrupleCount H W m q T d e d' e' =
      ∑ v ∈ allowedPreSieveResidues W m,
        largeGapCrtClassCount H W v m q T d e d' e' hcompat := by
  classical
  rw [preSievedLargeGapQuadrupleCount,
    ← sum_allowed_residue_filter_card W m T
      (fun n => largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e') hW hm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [largeGapCrtClassCount]
  apply congrArg Finset.card
  ext n
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hncond⟩
    refine ⟨hn, ?_⟩
    have hnshift : ∀ h : H, 0 < n + h.1 * q := by
      intro h
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact (modEq_largeGapFullCrtResidue_iff H W v m q n d e d' e'
      hm hDpos hEpos hmE hnshift hcompat).2 hncond
  · rintro ⟨hn, hncond⟩
    refine ⟨hn, ?_⟩
    have hnshift : ∀ h : H, 0 < n + h.1 * q := by
      intro h
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact (modEq_largeGapFullCrtResidue_iff H W v m q n d e d' e'
      hm hDpos hEpos hmE hnshift hcompat).1 hncond

/-- The exact discrepancy of a single doubled CRT class from interval length
divided by its modulus. -/
noncomputable def largeGapCrtClassError (H : Finset ℕ)
    (W v m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e') : ℝ :=
  BoundedGaps.Maynard.intervalModEqCardError 1 (T + 1)
    (largeGapFullCrtModulus H W d e d' e')
    (largeGapFullCrtResidue H W v m q d e d' e' hcompat)

theorem largeGapCrtClassCount_eq_main_add_error
    (H : Finset ℕ) (W v m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e') :
    (largeGapCrtClassCount H W v m q T d e d' e' hcompat : ℝ) =
      (T : ℝ) / largeGapFullCrtModulus H W d e d' e' +
        largeGapCrtClassError H W v m q T d e d' e' hcompat := by
  have hinterval : Finset.Icc 1 T = Finset.Ico 1 (T + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold largeGapCrtClassCount largeGapCrtClassError
  rw [hinterval,
    BoundedGaps.Maynard.intervalModEq_card_eq_length_div_add_error]
  congr 1
  push_cast
  ring

theorem largeGapCrtClassError_abs_le_one
    (H : Finset ℕ) (W v m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e')
    (hmodpos : 0 < largeGapFullCrtModulus H W d e d' e') :
    |largeGapCrtClassError H W v m q T d e d' e' hcompat| ≤ 1 := by
  exact BoundedGaps.Maynard.intervalModEqCardError_abs_le_one
    1 (T + 1) (largeGapFullCrtModulus H W d e d' e')
    (largeGapFullCrtResidue H W v m q d e d' e' hcompat)
    (by omega) hmodpos

/-- Sum of the one-class interval errors over all allowed pre-sieving
residues. -/
noncomputable def preSievedLargeGapQuadrupleError (H : Finset ℕ)
    (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e') : ℝ :=
  ∑ v ∈ allowedPreSieveResidues W m,
    largeGapCrtClassError H W v m q T d e d' e' hcompat

/-- Exact main-term/error decomposition of one expanded divisor quadruple. -/
theorem preSievedLargeGapQuadrupleCount_eq_main_add_error
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hW : 1 < W) (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hcompat : LargeGapCrtCompatible H W d e d' e') :
    (preSievedLargeGapQuadrupleCount H W m q T d e d' e' : ℝ) =
      (allowedPreSieveResidues W m).card *
          ((T : ℝ) / largeGapFullCrtModulus H W d e d' e') +
        preSievedLargeGapQuadrupleError H W m q T d e d' e' hcompat := by
  rw [preSievedLargeGapQuadrupleCount_eq_sum_crt H W m q T d e d' e'
    hW hm hDpos hEpos hmE hcompat]
  push_cast
  simp_rw [largeGapCrtClassCount_eq_main_add_error]
  rw [Finset.sum_add_distrib]
  simp [preSievedLargeGapQuadrupleError]

/-- The aggregate interval-count error is bounded by the number of allowed
small-prime residues. -/
theorem preSievedLargeGapQuadrupleError_abs_le_card
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapCrtCompatible H W d e d' e')
    (hmodpos : 0 < largeGapFullCrtModulus H W d e d' e') :
    |preSievedLargeGapQuadrupleError H W m q T d e d' e' hcompat| ≤
      (allowedPreSieveResidues W m).card := by
  rw [preSievedLargeGapQuadrupleError]
  calc
    |∑ v ∈ allowedPreSieveResidues W m,
        largeGapCrtClassError H W v m q T d e d' e' hcompat| ≤
        ∑ v ∈ allowedPreSieveResidues W m,
          |largeGapCrtClassError H W v m q T d e d' e' hcompat| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ allowedPreSieveResidues W m, (1 : ℝ) := by
      gcongr with v hv
      exact largeGapCrtClassError_abs_le_one H W v m q T d e d' e'
        hcompat hmodpos
    _ = (allowedPreSieveResidues W m).card := by simp

/-! ### Lifting the CRT count through the doubled Selberg expansion -/

theorem not_largeGapPreSieved_zero {w m : ℕ} (hw : 2 ≤ w) :
    ¬largeGapPreSieved w m 0 := by
  rw [largeGapPreSieved]
  simp only [zero_mul]
  rw [Nat.coprime_zero_left]
  exact ne_of_gt (one_lt_primorial_of_two_le hw)

theorem sum_Icc_zero_eq_sum_Icc_one {T : ℕ} (f : ℕ → ℝ)
    (hf : f 0 = 0) :
    (∑ n ∈ Finset.Icc 0 T, f n) = ∑ n ∈ Finset.Icc 1 T, f n := by
  have hset : Finset.Icc 0 T = insert 0 (Finset.Icc 1 T) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert]
  · simp [hf]
  · simp

theorem sum_indicator_eq_mul_card (S : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (c : ℝ) :
    (∑ n ∈ S, if P n then c else 0) =
      c * ((S.filter P).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Exact expansion of the pre-sieved doubled square weight into its four
divisor tuples and the corresponding arithmetic counts. -/
theorem preSievedDoubledWeightSum_eq_quadrupleCounts
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H D E lambda m q n else 0) =
      ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        lambda d e * lambda d' e' *
          (preSievedLargeGapQuadrupleCount H (primorial w) m q T
            d e d' e' : ℝ) := by
  classical
  rw [sum_Icc_zero_eq_sum_Icc_one]
  · simp_rw [doubledSelbergWeight_eq_quadrupleSum]
    have hdistribute (n : ℕ) :
        (if largeGapPreSieved w m n then
          ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
            if largeGapDivisorCondition H m q n d e ∧
                largeGapDivisorCondition H m q n d' e' then
              lambda d e * lambda d' e' else 0
          else 0) =
          ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
            if largeGapPreSieved w m n then
              if largeGapDivisorCondition H m q n d e ∧
                  largeGapDivisorCondition H m q n d' e' then
                lambda d e * lambda d' e' else 0
            else 0 := by
      by_cases hpre : largeGapPreSieved w m n <;> simp [hpre]
    simp_rw [hdistribute]
    rw [Finset.sum_comm (s := Finset.Icc 1 T) (t := D)]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_comm (s := Finset.Icc 1 T) (t := E)]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm (s := Finset.Icc 1 T) (t := D)]
    apply Finset.sum_congr rfl
    intro d' hd'
    rw [Finset.sum_comm (s := Finset.Icc 1 T) (t := E)]
    apply Finset.sum_congr rfl
    intro e' he'
    rw [preSievedLargeGapQuadrupleCount]
    rw [← sum_indicator_eq_mul_card]
    apply Finset.sum_congr rfl
    intro n hn
    change (if largeGapPreSieved w m n then
        if largeGapDivisorCondition H m q n d e ∧
            largeGapDivisorCondition H m q n d' e' then
          lambda d e * lambda d' e' else 0
      else 0) =
      if largeGapPreSieved w m n ∧
          largeGapDivisorCondition H m q n d e ∧
            largeGapDivisorCondition H m q n d' e' then
        lambda d e * lambda d' e' else 0
    by_cases hpre : largeGapPreSieved w m n
    · by_cases hcond : largeGapDivisorCondition H m q n d e ∧
          largeGapDivisorCondition H m q n d' e'
      · simp [hpre, hcond]
      · simp [hpre, hcond]
    · simp [hpre]
  · simp [not_largeGapPreSieved_zero hw]

/-- Arithmetic support conditions ensuring that every expanded divisor
quadruple gives a positive, pairwise-coprime CRT system. -/
structure DoubledSelbergCrtSupport (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (W m : ℕ) : Prop where
  first_lcm_pos : ∀ d ∈ D, ∀ d' ∈ D, ∀ h : H,
    0 < Nat.lcm (d h) (d' h)
  companion_lcm_pos : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    0 < Nat.lcm (e h) (e' h)
  companion_coprime : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    m.Coprime (Nat.lcm (e h) (e' h))
  compatible : ∀ d ∈ D, ∀ e ∈ E, ∀ d' ∈ D, ∀ e' ∈ E,
    LargeGapCrtCompatible H W d e d' e'

theorem DoubledSelbergCrtSupport.full_modulus_pos
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {W m : ℕ}
    (support : DoubledSelbergCrtSupport H D E W m)
    (hW : 0 < W) {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E) :
    0 < largeGapFullCrtModulus H W d e d' e' := by
  rw [largeGapFullCrtModulus_eq]
  apply Nat.mul_pos hW
  apply Finset.prod_pos
  intro i hi
  cases i with
  | inl h => exact support.first_lcm_pos d hd d' hd' h
  | inr h => exact support.companion_lcm_pos e he e' he' h

/-- Four nested finite sums inherit the pointwise absolute bound with the
expected cardinality factor. -/
theorem abs_fourfold_sum_le_card_mul_bound
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (f : A → B → A → B → ℝ) (L : ℝ)
    (hf : ∀ a ∈ S, ∀ b ∈ T, ∀ c ∈ S, ∀ d ∈ T,
      |f a b c d| ≤ L) :
    |∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ S, ∑ d ∈ T, f a b c d| ≤
      (S.card : ℝ) ^ 2 * (T.card : ℝ) ^ 2 * L := by
  calc
    |∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ S, ∑ d ∈ T, f a b c d| ≤
        ∑ a ∈ S, |∑ b ∈ T, ∑ c ∈ S, ∑ d ∈ T, f a b c d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, ∑ b ∈ T, |∑ c ∈ S, ∑ d ∈ T, f a b c d| := by
      gcongr with a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ S, |∑ d ∈ T, f a b c d| := by
      gcongr with a ha b hb
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ S, ∑ d ∈ T, |f a b c d| := by
      gcongr with a ha b hb c hc
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ S, ∑ _b ∈ T, ∑ _c ∈ S, ∑ _d ∈ T, L := by
      gcongr with a ha b hb c hc d hd
      exact hf a ha b hb c hc d hd
    _ = (S.card : ℝ) ^ 2 * (T.card : ℝ) ^ 2 * L := by
      simp
      ring

/-- The exact CRT main term in the doubled normalization. -/
noncomputable def doubledSelbergNormalizationMain (H : Finset ℕ)
    (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m _q T : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' *
      ((allowedPreSieveResidues W m).card *
        ((T : ℝ) / largeGapFullCrtModulus H W d e d' e'))

/-- The exact aggregate CRT counting error in the doubled normalization. -/
noncomputable def doubledSelbergNormalizationError (H : Finset ℕ)
    (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) (support : DoubledSelbergCrtSupport H D E W m) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' *
      if hd : d ∈ D then
        if he : e ∈ E then
          if hd' : d' ∈ D then
            if he' : e' ∈ E then
              preSievedLargeGapQuadrupleError H W m q T d e d' e'
                (support.compatible d hd e he d' hd' e' he')
            else 0
          else 0
        else 0
      else 0

/-- Fully expanded exact normalization identity.  The analytic part of the
large-gap theorem starts only after this equality, by evaluating `Main` and
showing that `Error` is negligible for the chosen divisor support. -/
theorem preSievedDoubledWeightSum_eq_main_add_error
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) (hm : 0 < m)
    (support : DoubledSelbergCrtSupport H D E (primorial w) m) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H D E lambda m q n else 0) =
      doubledSelbergNormalizationMain H D E lambda (primorial w) m q T +
        doubledSelbergNormalizationError H D E lambda
          (primorial w) m q T support := by
  classical
  rw [preSievedDoubledWeightSum_eq_quadrupleCounts H D E lambda
    w m q T hw]
  unfold doubledSelbergNormalizationMain doubledSelbergNormalizationError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e' he'
  simp only [hd, he, hd', he', dite_true]
  rw [preSievedLargeGapQuadrupleCount_eq_main_add_error
    H (primorial w) m q T d e d' e'
    (one_lt_primorial_of_two_le hw) hm
    (support.first_lcm_pos d hd d' hd')
    (support.companion_lcm_pos e he e' he')
    (support.companion_coprime e he e' he')
    (support.compatible d hd e he d' hd' e' he')]
  ring

/-- Uniform coefficient control and the one-class endpoint bound give an
explicit aggregate normalization-error envelope. -/
theorem doubledSelbergNormalizationError_abs_le
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) (support : DoubledSelbergCrtSupport H D E W m)
    (hW : 0 < W) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    |doubledSelbergNormalizationError H D E lambda W m q T support| ≤
      (D.card : ℝ) ^ 2 * (E.card : ℝ) ^ 2 *
        (L ^ 2 * (allowedPreSieveResidues W m).card) := by
  unfold doubledSelbergNormalizationError
  apply abs_fourfold_sum_le_card_mul_bound
  intro d hd e he d' hd' e' he'
  simp only [hd, he, hd', he', dite_true]
  rw [abs_mul, abs_mul]
  have herr := preSievedLargeGapQuadrupleError_abs_le_card
    H W m q T d e d' e'
    (support.compatible d hd e he d' hd' e' he')
    (support.full_modulus_pos hW hd hd' he he')
  have hcard : (0 : ℝ) ≤ (allowedPreSieveResidues W m).card := by positivity
  calc
    |lambda d e| * |lambda d' e'| *
        |preSievedLargeGapQuadrupleError H W m q T d e d' e'
          (support.compatible d hd e he d' hd' e' he')| ≤
      L * L * (allowedPreSieveResidues W m).card := by
        gcongr
        · exact hcoeff d hd e he
        · exact hcoeff d' hd' e' he'
    _ = L ^ 2 * (allowedPreSieveResidues W m).card := by ring

/-! ### Compatibility-filtered normalization

The standard Maynard support does not make every pair of divisor tuples
cross-coordinate coprime.  Instead, an incompatible pair has no simultaneous
integer solution and contributes zero.  The following support contract and
exact identity record that mathematically correct route; the stronger
`DoubledSelbergCrtSupport` above remains useful for specially separated
supports. -/

/-- Positivity and companion coprimality for every tuple, together with the
fact that a non-pairwise-coprime CRT system has no solution on the support. -/
structure DoubledSelbergResolvableSupport (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (W m q T : ℕ) : Prop where
  first_lcm_pos : ∀ d ∈ D, ∀ d' ∈ D, ∀ h : H,
    0 < Nat.lcm (d h) (d' h)
  companion_lcm_pos : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    0 < Nat.lcm (e h) (e' h)
  companion_coprime : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    m.Coprime (Nat.lcm (e h) (e' h))
  incompatible_count_zero : ∀ d ∈ D, ∀ e ∈ E,
    ∀ d' ∈ D, ∀ e' ∈ E,
      ¬LargeGapCrtCompatible H W d e d' e' →
        preSievedLargeGapQuadrupleCount H W m q T d e d' e' = 0

/-- Checkable arithmetic hypotheses on two ordinary Maynard tuple supports.
They are arranged so that every simultaneously occurring quadruple is a
valid doubled CRT system. -/
structure DoubledMaynardSupportConditions (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (RD RE W m q : ℕ) : Prop where
  m_pos : 0 < m
  q_pos : 0 < q
  first_tuple : ∀ d ∈ D,
    BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d
  companion_tuple : ∀ e ∈ E,
    BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e
  covers_shift_differences :
    BoundedGaps.Maynard.CoversShiftDifferencePrimes H W
  q_first_coprime : ∀ d ∈ D,
    q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d)
  q_companion_coprime : ∀ e ∈ E,
    q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e)
  m_companion_coprime : ∀ e ∈ E,
    m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e)
  cross_family : ∀ d ∈ D, ∀ e ∈ E, ∀ a b : H,
    Nat.Coprime (d a) (e b)

/-- The ordinary Maynard support conditions imply the exact
compatibility-or-zero contract consumed by the filtered normalization. -/
theorem DoubledMaynardSupportConditions.toResolvable
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q T : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q) :
    DoubledSelbergResolvableSupport H D E W m q T := by
  refine
    { first_lcm_pos := ?_
      companion_lcm_pos := ?_
      companion_coprime := ?_
      incompatible_count_zero := ?_ }
  · intro d hd d' hd' h
    exact Nat.lcm_pos
      (Nat.pos_of_ne_zero
        ((support.first_tuple d hd).coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero
        ((support.first_tuple d' hd').coordinate_squarefree h).ne_zero)
  · intro e he e' he' h
    exact Nat.lcm_pos
      (Nat.pos_of_ne_zero
        ((support.companion_tuple e he).coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero
        ((support.companion_tuple e' he').coordinate_squarefree h).ne_zero)
  · intro e he e' he' h
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
    exact (Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e h)
      (support.m_companion_coprime e he)).mul_right
      (Nat.Coprime.of_dvd_right
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' h)
        (support.m_companion_coprime e' he'))
  · intro d hd e he d' hd' e' he' hnot
    apply Finset.card_eq_zero.mpr
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn.1).1
      have hcond := hn.2.2.1
      have hcond' := hn.2.2.2
      have hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' :=
        firstForms_crossCoordinateCoprime_of_conditions
          (hd := support.first_tuple d hd)
          (hd' := support.first_tuple d' hd')
          (hcoverage := support.covers_shift_differences)
          (hqD := support.q_first_coprime d hd)
          (hqD' := support.q_first_coprime d' hd')
          (hcond := hcond) (hcond' := hcond')
      have hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' :=
        companionForms_crossCoordinateCoprime_of_conditions
          (hm := support.m_pos) (hn := hnpos) (hq := support.q_pos)
          (he := support.companion_tuple e he)
          (he' := support.companion_tuple e' he')
          (hcoverage := support.covers_shift_differences)
          (hmE := support.m_companion_coprime e he)
          (hmE' := support.m_companion_coprime e' he')
          (hqE := support.q_companion_coprime e he)
          (hqE' := support.q_companion_coprime e' he')
          (hcond := hcond) (hcond' := hcond')
      exfalso
      apply hnot
      exact largeGapCrtCompatible_of_maynard_tuples
        (support.first_tuple d hd) (support.first_tuple d' hd')
        (support.companion_tuple e he) (support.companion_tuple e' he')
        hDD hEE
        (support.cross_family d hd e he)
        (support.cross_family d hd e' he')
        (support.cross_family d' hd' e he)
        (support.cross_family d' hd' e' he')
    · intro hn
      simp at hn

/-- On a doubled Maynard support, CRT compatibility is exactly the conjunction
of the two standard within-family cross-coordinate predicates. -/
theorem DoubledMaynardSupportConditions.compatible_iff_cross
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E) :
    LargeGapCrtCompatible H W d e d' e' ↔
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
        BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' := by
  constructor
  · intro hcompat
    exact ⟨
      firstForms_crossCoordinateCoprime_of_crtCompatible
        H W d e d' e' hcompat,
      companionForms_crossCoordinateCoprime_of_crtCompatible
        H W d e d' e' hcompat⟩
  · rintro ⟨hDD, hEE⟩
    exact largeGapCrtCompatible_of_maynard_tuples
      (support.first_tuple d hd) (support.first_tuple d' hd')
      (support.companion_tuple e he) (support.companion_tuple e' he')
      hDD hEE
      (support.cross_family d hd e he)
      (support.cross_family d hd e' he')
      (support.cross_family d' hd' e he)
      (support.cross_family d' hd' e' he')

/-! #### A separated concrete support -/

/-- First-form tuples use no prime at most `Y`.  This separates them from
the companion tuples, whose total product will be below `Y`. -/
noncomputable def separatedFirstSupport
    (H : Finset ℕ) (RD Y : ℕ) : Finset (H → ℕ) :=
  BoundedGaps.Maynard.maynardDivisorTupleSupport H RD (primorial Y)

/-- Companion tuples have the ordinary `W` pre-sieve and are additionally
restricted to be coprime to the fixed multiplier `m`. -/
noncomputable def separatedCompanionSupport
    (H : Finset ℕ) (RE W m : ℕ) : Finset (H → ℕ) := by
  classical
  exact (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE W).filter
    (fun e => m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e))

theorem prime_coprime_of_pos_of_lt {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hap : a < p) : p.Coprime a := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  exact (not_le_of_gt hap) (Nat.le_of_dvd ha hdvd)

/-- The separated supports satisfy every arithmetic hypothesis of the
filtered doubled normalization. -/
theorem separatedSupportConditions
    {H : Finset ℕ} {RD RE W Y m q : ℕ}
    (hm : 0 < m) (hq : q.Prime)
    (hWdiv : W ∣ primorial Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y) :
    DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE W m) RD RE W m q := by
  refine
    { m_pos := hm
      q_pos := hq.pos
      first_tuple := ?_
      companion_tuple := ?_
      covers_shift_differences := hcover
      q_first_coprime := ?_
      q_companion_coprime := ?_
      m_companion_coprime := ?_
      cross_family := ?_ }
  · intro d hd
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact ⟨hdY.1, Nat.Coprime.of_dvd_right hWdiv hdY.2.1, hdY.2.2⟩
  · intro e he
    exact BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support
      (Finset.mem_filter.mp he).1
  · intro d hd
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact prime_coprime_of_pos_of_lt hq
      (Nat.pos_of_ne_zero hdY.2.2.ne_zero) (hdY.1.trans_le hRDq)
  · intro e he
    have heW := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support
      (Finset.mem_filter.mp he).1
    exact prime_coprime_of_pos_of_lt hq
      (Nat.pos_of_ne_zero heW.2.2.ne_zero) (heW.1.trans_le hREq)
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro d hd e he a b
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    have heW := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support
      (Finset.mem_filter.mp he).1
    by_contra hnot
    obtain ⟨p, hp, hpd, hpe⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpdprod : p ∣ BoundedGaps.Maynard.divisorTupleProduct H d :=
      dvd_trans hpd
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d a)
    have hpeprod : p ∣ BoundedGaps.Maynard.divisorTupleProduct H e :=
      dvd_trans hpe
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e b)
    have heprodpos : 0 < BoundedGaps.Maynard.divisorTupleProduct H e :=
      Nat.pos_of_ne_zero heW.2.2.ne_zero
    have hpY : p ≤ Y :=
      (Nat.le_of_dvd heprodpos hpeprod).trans (heW.1.le.trans hREY)
    have hpprim : p ∣ primorial Y := hp.dvd_primorial_iff.mpr hpY
    have hpcop : p.Coprime (primorial Y) :=
      hdY.2.1.coprime_dvd_left hpdprod
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpprim

/-- A companion support with coprimality to `m` built into its Maynard
pre-sieve modulus.  Unlike the filtered presentation above, this remains a
full ordinary Maynard support and is therefore preferable for asymptotic
diagonalization. -/
noncomputable def fullySeparatedCompanionSupport
    (H : Finset ℕ) (RE W m : ℕ) : Finset (H → ℕ) :=
  BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)

/-- The two full ordinary Maynard supports satisfy the doubled arithmetic
conditions when the first family uses primes above `Y` and the companion
product is below `Y`. -/
theorem fullySeparatedSupportConditions
    {H : Finset ℕ} {RD RE W Y m q : ℕ}
    (hm : 0 < m) (hq : q.Prime)
    (hWdiv : W ∣ primorial Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y) :
    DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE W m) RD RE W m q := by
  refine
    { m_pos := hm
      q_pos := hq.pos
      first_tuple := ?_
      companion_tuple := ?_
      covers_shift_differences := hcover
      q_first_coprime := ?_
      q_companion_coprime := ?_
      m_companion_coprime := ?_
      cross_family := ?_ }
  · intro d hd
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact ⟨hdY.1, Nat.Coprime.of_dvd_right hWdiv hdY.2.1, hdY.2.2⟩
  · intro e he
    have heWM := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    exact ⟨heWM.1,
      Nat.Coprime.of_dvd_right (dvd_mul_right W m) heWM.2.1,
      heWM.2.2⟩
  · intro d hd
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact prime_coprime_of_pos_of_lt hq
      (Nat.pos_of_ne_zero hdY.2.2.ne_zero) (hdY.1.trans_le hRDq)
  · intro e he
    have heWM := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    exact prime_coprime_of_pos_of_lt hq
      (Nat.pos_of_ne_zero heWM.2.2.ne_zero) (heWM.1.trans_le hREq)
  · intro e he
    have heWM := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    exact (Nat.Coprime.of_dvd_right (dvd_mul_left m W) heWM.2.1).symm
  · intro d hd e he a b
    have hdY := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    have heWM := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    by_contra hnot
    obtain ⟨p, hp, hpd, hpe⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpdprod : p ∣ BoundedGaps.Maynard.divisorTupleProduct H d :=
      dvd_trans hpd
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d a)
    have hpeprod : p ∣ BoundedGaps.Maynard.divisorTupleProduct H e :=
      dvd_trans hpe
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e b)
    have heprodpos : 0 < BoundedGaps.Maynard.divisorTupleProduct H e :=
      Nat.pos_of_ne_zero heWM.2.2.ne_zero
    have hpY : p ≤ Y :=
      (Nat.le_of_dvd heprodpos hpeprod).trans (heWM.1.le.trans hREY)
    have hpprim : p ∣ primorial Y := hp.dvd_primorial_iff.mpr hpY
    have hpcop : p.Coprime (primorial Y) :=
      hdY.2.1.coprime_dvd_left hpdprod
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpprim

/-! #### Tensor coefficients on the separated support -/

/-- The ordinary Maynard coefficient for the first family, whose divisor
primes are forced above `Y` by the larger primorial pre-sieve. -/
noncomputable def separatedFirstCoefficient
    (H : Finset ℕ) (RD Y : ℕ) (F : (H → ℝ) → ℝ) (d : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardCoefficient H RD (primorial Y) F d

/-- The ordinary Maynard coefficient for the companion family.  Its support
is filtered separately by coprimality with `m`; on that support no change to
the coefficient itself is necessary. -/
noncomputable def separatedCompanionCoefficient
    (H : Finset ℕ) (RE W : ℕ) (G : (H → ℝ) → ℝ) (e : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardCoefficient H RE W G e

/-- Product coefficient used in the doubled Selberg square. -/
noncomputable def separatedDoubledCoefficient
    (H : Finset ℕ) (RD RE Y W : ℕ)
    (F G : (H → ℝ) → ℝ) (d e : H → ℕ) : ℝ :=
  separatedFirstCoefficient H RD Y F d *
    separatedCompanionCoefficient H RE W G e

/-- Companion coefficient with the multiplier included in its pre-sieve
modulus, paired with `fullySeparatedCompanionSupport`. -/
noncomputable def fullySeparatedCompanionCoefficient
    (H : Finset ℕ) (RE W m : ℕ) (G : (H → ℝ) → ℝ) (e : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardCoefficient H RE (W * m) G e

/-- Tensor coefficient built from two full ordinary Maynard families. -/
noncomputable def fullySeparatedDoubledCoefficient
    (H : Finset ℕ) (RD RE Y W m : ℕ)
    (F G : (H → ℝ) → ℝ) (d e : H → ℕ) : ℝ :=
  separatedFirstCoefficient H RD Y F d *
    fullySeparatedCompanionCoefficient H RE W m G e

theorem card_maynardDivisorTupleBox (H : Finset ℕ) (R : ℕ) :
    (BoundedGaps.Maynard.maynardDivisorTupleBox H R).card =
      (R - 1) ^ Fintype.card H := by
  classical
  have hrange : (Finset.range R).filter (fun n => 0 < n) =
      Finset.Ico 1 R := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp [BoundedGaps.Maynard.maynardDivisorTupleBox, hrange]

theorem card_separatedFirstSupport_le
    (H : Finset ℕ) (RD Y : ℕ) :
    (separatedFirstSupport H RD Y).card ≤
      (RD - 1) ^ Fintype.card H := by
  rw [← card_maynardDivisorTupleBox H RD]
  apply Finset.card_le_card
  intro d hd
  exact (BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff.mp hd).1

theorem card_fullySeparatedCompanionSupport_le
    (H : Finset ℕ) (RE W m : ℕ) :
    (fullySeparatedCompanionSupport H RE W m).card ≤
      (RE - 1) ^ Fintype.card H := by
  rw [← card_maynardDivisorTupleBox H RE]
  apply Finset.card_le_card
  intro e he
  exact (BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff.mp he).1

theorem separatedFirstCoefficient_abs_le
    {H : Finset ℕ} {RD Y : ℕ} {F : (H → ℝ) → ℝ}
    {d : H → ℕ} (hd : d ∈ separatedFirstSupport H RD Y)
    {BF : ℝ} (hBF : 0 ≤ BF) (hF : ∀ x, |F x| ≤ BF) :
    |separatedFirstCoefficient H RD Y F d| ≤
      (RD : ℝ) *
        (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF := by
  have htuple :=
    BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  have hraw := BoundedGaps.Maynard.abs_maynardCoefficient_le_of_bound
    H RD (primorial Y) F d BF hBF hF
  have hprod :
      (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ) ≤ RD := by
    exact_mod_cast htuple.1.le
  unfold separatedFirstCoefficient
  exact hraw.trans (by gcongr)

theorem separatedCompanionCoefficient_abs_le
    {H : Finset ℕ} {RE W m : ℕ} {G : (H → ℝ) → ℝ}
    {e : H → ℕ} (he : e ∈ separatedCompanionSupport H RE W m)
    {BG : ℝ} (hBG : 0 ≤ BG) (hG : ∀ x, |G x| ≤ BG) :
    |separatedCompanionCoefficient H RE W G e| ≤
      (RE : ℝ) *
        (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG := by
  have htuple := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support
    (Finset.mem_filter.mp he).1
  have hraw := BoundedGaps.Maynard.abs_maynardCoefficient_le_of_bound
    H RE W G e BG hBG hG
  have hprod :
      (BoundedGaps.Maynard.divisorTupleProduct H e : ℝ) ≤ RE := by
    exact_mod_cast htuple.1.le
  unfold separatedCompanionCoefficient
  exact hraw.trans (by gcongr)

theorem fullySeparatedCompanionCoefficient_abs_le
    {H : Finset ℕ} {RE W m : ℕ} {G : (H → ℝ) → ℝ}
    {e : H → ℕ} (he : e ∈ fullySeparatedCompanionSupport H RE W m)
    {BG : ℝ} (hBG : 0 ≤ BG) (hG : ∀ x, |G x| ≤ BG) :
    |fullySeparatedCompanionCoefficient H RE W m G e| ≤
      (RE : ℝ) *
        (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG := by
  have htuple := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
  have hraw := BoundedGaps.Maynard.abs_maynardCoefficient_le_of_bound
    H RE (W * m) G e BG hBG hG
  have hprod :
      (BoundedGaps.Maynard.divisorTupleProduct H e : ℝ) ≤ RE := by
    exact_mod_cast htuple.1.le
  unfold fullySeparatedCompanionCoefficient
  exact hraw.trans (by gcongr)

/-- A completely explicit uniform coefficient envelope for the tensor
weight.  This is the only coefficient input needed by the aggregate CRT
endpoint-error estimate. -/
theorem separatedDoubledCoefficient_abs_le
    {H : Finset ℕ} {RD RE Y W m : ℕ}
    {F G : (H → ℝ) → ℝ} {BF BG : ℝ}
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, |F x| ≤ BF) (hG : ∀ x, |G x| ≤ BG)
    {d e : H → ℕ} (hd : d ∈ separatedFirstSupport H RD Y)
    (he : e ∈ separatedCompanionSupport H RE W m) :
    |separatedDoubledCoefficient H RD RE Y W F G d e| ≤
      ((RD : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
        ((RE : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG) := by
  rw [separatedDoubledCoefficient, abs_mul]
  exact mul_le_mul
    (separatedFirstCoefficient_abs_le hd hBF hF)
    (separatedCompanionCoefficient_abs_le he hBG hG)
    (abs_nonneg _) (by positivity)

theorem fullySeparatedDoubledCoefficient_abs_le
    {H : Finset ℕ} {RD RE Y W m : ℕ}
    {F G : (H → ℝ) → ℝ} {BF BG : ℝ}
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, |F x| ≤ BF) (hG : ∀ x, |G x| ≤ BG)
    {d e : H → ℕ} (hd : d ∈ separatedFirstSupport H RD Y)
    (he : e ∈ fullySeparatedCompanionSupport H RE W m) :
    |fullySeparatedDoubledCoefficient H RD RE Y W m F G d e| ≤
      ((RD : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
        ((RE : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG) := by
  rw [fullySeparatedDoubledCoefficient, abs_mul]
  exact mul_le_mul
    (separatedFirstCoefficient_abs_le hd hBF hF)
    (fullySeparatedCompanionCoefficient_abs_le he hBG hG)
    (abs_nonneg _) (by positivity)

/-- The first compatible quadratic form is exactly the Maynard `Y`-diagonal
minus the cross-coordinate collision correction.  This is the canonical
starting point of the analytic evaluation already developed in the
`BoundedGaps` dependency. -/
theorem separatedFirstTotientExpanded_eq_yDiagonal_sub_incompatible
    (H : Finset ℕ) (RD Y : ℕ) (F : (H → ℝ) → ℝ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
        (separatedFirstSupport H RD Y)
        (separatedFirstCoefficient H RD Y F) =
      BoundedGaps.Maynard.maynardYDiagonalSum H RD (primorial Y)
          (BoundedGaps.Maynard.maynardYValue H RD (primorial Y) F) -
        BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
          (separatedFirstSupport H RD Y)
          (separatedFirstCoefficient H RD Y F) := by
  rw [BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum]
  exact BoundedGaps.Maynard.compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible
    H RD (primorial Y) F

theorem maynardYValue_abs_le
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    (r : H → ℕ) :
    |BoundedGaps.Maynard.maynardYValue H R W F r| ≤ B := by
  unfold BoundedGaps.Maynard.maynardYValue
  split_ifs
  · exact hF _
  · simpa using hB

/-- Explicit collision bound for the first full support.  Its decisive factor
is `1 / Y`; all other factors are finite logarithmic envelopes at fixed
dimension. -/
theorem separatedFirstIncompatible_abs_le_log
    {H : Finset ℕ} {RD Y : ℕ} {F : (H → ℝ) → ℝ} {BF : ℝ}
    (hRD : 0 < RD) (hY : 0 < Y) (hBF : 0 ≤ BF)
    (hprimLog : (primorial Y : ℝ) ≤ 1 + Real.log RD)
    (hF : ∀ t, |F t| ≤ BF) :
    |BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
      (separatedFirstSupport H RD Y)
      (separatedFirstCoefficient H RD Y F)| ≤
      BF ^ 2 *
        ((8 * Real.exp 8 / (Y : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
            (Real.exp 8) ^
              ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (8 * ((Nat.totient (primorial Y) : ℝ) / primorial Y) *
          (1 + Real.log RD)) ^ Fintype.card H := by
  let y := BoundedGaps.Maynard.maynardYValue H RD (primorial Y) F
  have hy : BoundedGaps.Maynard.IsSupportedMaynardY H RD (primorial Y) y :=
    BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue H RD
      (primorial Y) F
  have hyBound : ∀ r, |y r| ≤ BF := by
    intro r
    exact maynardYValue_abs_le H RD (primorial Y) F hBF hF r
  have hcoeff : separatedFirstCoefficient H RD Y F =
      BoundedGaps.Maynard.maynardCoefficientFromY H RD (primorial Y) y := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue
      H RD (primorial Y) F d
  rw [hcoeff]
  exact BoundedGaps.Maynard.abs_incompatibleSum_le_log
    hRD hY hBF hprimLog hyBound hy

/-- The full companion quadratic form has the identical canonical
`Y`-diagonal-minus-collision expansion. -/
theorem fullySeparatedCompanionTotientExpanded_eq_yDiagonal_sub_incompatible
    (H : Finset ℕ) (RE W m : ℕ) (G : (H → ℝ) → ℝ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
        (fullySeparatedCompanionSupport H RE W m)
        (fullySeparatedCompanionCoefficient H RE W m G) =
      BoundedGaps.Maynard.maynardYDiagonalSum H RE (W * m)
          (BoundedGaps.Maynard.maynardYValue H RE (W * m) G) -
        BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
          (fullySeparatedCompanionSupport H RE W m)
          (fullySeparatedCompanionCoefficient H RE W m G) := by
  rw [BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum]
  exact BoundedGaps.Maynard.compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible
    H RE (W * m) G

/-- Main term with precisely the compatible quadruples retained. -/
noncomputable def doubledSelbergFilteredNormalizationMain
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m _q T : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if LargeGapCrtCompatible H W d e d' e' then
        lambda d e * lambda d' e' *
          ((allowedPreSieveResidues W m).card *
            ((T : ℝ) / largeGapFullCrtModulus H W d e d' e'))
      else 0

/-- Aggregate interval endpoint error over the compatible quadruples. -/
noncomputable def doubledSelbergFilteredNormalizationError
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if hcompat : LargeGapCrtCompatible H W d e d' e' then
        lambda d e * lambda d' e' *
          preSievedLargeGapQuadrupleError H W m q T d e d' e' hcompat
      else 0

/-- Exact normalization identity for the ordinary (compatibility-filtered)
Maynard support. -/
theorem preSievedDoubledWeightSum_eq_filteredMain_add_error
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) (hm : 0 < m)
    (support : DoubledSelbergResolvableSupport H D E
      (primorial w) m q T) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H D E lambda m q n else 0) =
      doubledSelbergFilteredNormalizationMain H D E lambda
          (primorial w) m q T +
        doubledSelbergFilteredNormalizationError H D E lambda
          (primorial w) m q T := by
  classical
  rw [preSievedDoubledWeightSum_eq_quadrupleCounts H D E lambda
    w m q T hw]
  unfold doubledSelbergFilteredNormalizationMain
    doubledSelbergFilteredNormalizationError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hcompat : LargeGapCrtCompatible H (primorial w) d e d' e'
  · simp only [hcompat, if_true, dite_true]
    rw [preSievedLargeGapQuadrupleCount_eq_main_add_error
      H (primorial w) m q T d e d' e'
      (one_lt_primorial_of_two_le hw) hm
      (support.first_lcm_pos d hd d' hd')
      (support.companion_lcm_pos e he e' he')
      (support.companion_coprime e he e' he') hcompat]
    ring
  · rw [support.incompatible_count_zero d hd e he d' hd' e' he' hcompat]
    simp [hcompat]

theorem DoubledSelbergResolvableSupport.full_modulus_pos
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {W m q T : ℕ}
    (support : DoubledSelbergResolvableSupport H D E W m q T)
    (hW : 0 < W) {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E) :
    0 < largeGapFullCrtModulus H W d e d' e' := by
  rw [largeGapFullCrtModulus_eq]
  apply Nat.mul_pos hW
  apply Finset.prod_pos
  intro i hi
  cases i with
  | inl h => exact support.first_lcm_pos d hd d' hd' h
  | inr h => exact support.companion_lcm_pos e he e' he' h

/-- The filtered endpoint error has the same elementary cardinality bound as
the separated-support version. -/
theorem doubledSelbergFilteredNormalizationError_abs_le
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) (support : DoubledSelbergResolvableSupport H D E W m q T)
    (hW : 0 < W) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    |doubledSelbergFilteredNormalizationError H D E lambda W m q T| ≤
      (D.card : ℝ) ^ 2 * (E.card : ℝ) ^ 2 *
        (L ^ 2 * (allowedPreSieveResidues W m).card) := by
  unfold doubledSelbergFilteredNormalizationError
  apply abs_fourfold_sum_le_card_mul_bound
  intro d hd e he d' hd' e' he'
  by_cases hcompat : LargeGapCrtCompatible H W d e d' e'
  · simp only [hcompat, dite_true]
    rw [abs_mul, abs_mul]
    have herr := preSievedLargeGapQuadrupleError_abs_le_card
      H W m q T d e d' e' hcompat
      (support.full_modulus_pos hW hd hd' he he')
    have hcard : (0 : ℝ) ≤ (allowedPreSieveResidues W m).card := by
      positivity
    calc
      |lambda d e| * |lambda d' e'| *
          |preSievedLargeGapQuadrupleError H W m q T d e d' e' hcompat| ≤
        L * L * (allowedPreSieveResidues W m).card := by
          gcongr
          · exact hcoeff d hd e he
          · exact hcoeff d' hd' e' he'
      _ = L ^ 2 * (allowedPreSieveResidues W m).card := by ring
  · simp only [hcompat, dite_false, abs_zero]
    exact mul_nonneg (sq_nonneg L) (by positivity)

/-! ### Local density of the doubled pre-sieve -/

theorem prime_dvd_preSievePolynomial_iff {p m v : ℕ}
    (hp : p.Prime) (_hm : 0 < m) (hv : 0 < v) (hvp : v < p) :
    p ∣ preSievePolynomial m v ↔ p ∣ m * v - 1 := by
  rw [preSievePolynomial, hp.dvd_mul]
  simp only [or_iff_right_iff_imp]
  intro hpv
  have := Nat.le_of_dvd hv hpv
  omega

theorem preSievePolynomial_coprime_prime_iff {p m v : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hv : 0 < v) (hvp : v < p) :
    (preSievePolynomial m v).Coprime p ↔ ¬p ∣ m * v - 1 := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd,
    prime_dvd_preSievePolynomial_iff hp hm hv hvp]

theorem companionResidue_pos_of_prime {p m : ℕ}
    (hp : p.Prime) (hme : m.Coprime p) :
    0 < companionResidue m p 0 := by
  have hspec := companionResidue_spec (m := m) (e := p) (c := 0) hp.pos hme
  by_contra hzero
  have hrzero : companionResidue m p 0 = 0 := by omega
  rw [hrzero] at hspec
  have heq : 0 = 1 := by
    apply hspec.eq_of_lt_of_lt
    · exact hp.pos
    · exact hp.one_lt
  omega

/-- At a prime `p`, the doubled pre-sieve removes one residue if `p ∣ m`
and two otherwise.  This is the local Euler factor in the normalization. -/
theorem card_allowedPreSieveResidues_prime {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    (allowedPreSieveResidues p m).card =
      if p ∣ m then p - 1 else p - 2 := by
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    have hset : allowedPreSieveResidues p m = Finset.Ico 1 p := by
      ext v
      simp only [allowedPreSieveResidues, Finset.mem_filter]
      constructor
      · exact And.left
      · intro hv
        have hvrange := Finset.mem_Ico.mp hv
        refine ⟨hv, ?_⟩
        rw [preSievePolynomial_coprime_prime_iff hp hm
          hvrange.1 hvrange.2]
        intro hdvd
        have hpmv : p ∣ m * v := dvd_mul_of_dvd_left hpm v
        have hone : p ∣ 1 := by
          have hsub := Nat.dvd_sub hpmv hdvd
          have hmv : 1 ≤ m * v :=
            Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero hm.ne' (by omega))
          simpa [show m * v - (m * v - 1) = 1 by omega] using hsub
        exact hp.not_dvd_one hone
    rw [hset]
    simp
  · rw [if_neg hpm]
    have hcop : m.Coprime p :=
      (hp.coprime_iff_not_dvd.mpr hpm).symm
    let r := companionResidue m p 0
    have hrpos : 0 < r := companionResidue_pos_of_prime hp hcop
    have hrlt : r < p := companionResidue_lt hp.pos
    have hrmem : r ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨hrpos, hrlt⟩
    have hset : allowedPreSieveResidues p m = (Finset.Ico 1 p).erase r := by
      ext v
      simp only [allowedPreSieveResidues, Finset.mem_filter,
        Finset.mem_erase, Finset.mem_Ico]
      constructor
      · rintro ⟨hvrange, hcopv⟩
        refine ⟨?_, hvrange⟩
        intro hvr
        apply (preSievePolynomial_coprime_prime_iff hp hm
          hvrange.1 hvrange.2).mp hcopv
        apply (modEq_companionResidue_iff_dvd_sub hm hp.pos hcop
          (by omega : 0 < v + 0)).mp
        rw [hvr]
      · rintro ⟨hvr, hvrange⟩
        refine ⟨hvrange, ?_⟩
        rw [preSievePolynomial_coprime_prime_iff hp hm
          hvrange.1 hvrange.2]
        intro hdvd
        have hmod := (modEq_companionResidue_iff_dvd_sub hm hp.pos hcop
          (by omega : 0 < v + 0)).mpr hdvd
        have hvrEq : v = r := by
          apply hmod.eq_of_lt_of_lt hvrange.2 hrlt
        exact hvr hvrEq
    rw [hset, Finset.card_erase_of_mem hrmem]
    simp
    omega

/-- Residues modulo `W` for which both pre-sieving factors are units.  This
form exposes multiplicativity through the `ZMod` Chinese remainder theorem. -/
abbrev PreSieveUnitResidue (W m : ℕ) :=
  {x : ZMod W // IsUnit x ∧ IsUnit ((m : ZMod W) * x - 1)}

/-- The doubled unit-residue set is multiplicative over coprime moduli. -/
noncomputable def preSieveUnitResidueCrtEquiv {A B m : ℕ}
    (hAB : A.Coprime B) :
    PreSieveUnitResidue (A * B) m ≃
      PreSieveUnitResidue A m × PreSieveUnitResidue B m := by
  let e := ZMod.chineseRemainder hAB
  let P : ZMod (A * B) → Prop := fun x =>
    IsUnit x ∧ IsUnit ((m : ZMod (A * B)) * x - 1)
  let Q : ZMod A × ZMod B → Prop := fun x =>
    (IsUnit x.1 ∧ IsUnit ((m : ZMod A) * x.1 - 1)) ∧
      (IsUnit x.2 ∧ IsUnit ((m : ZMod B) * x.2 - 1))
  have heq (x : ZMod (A * B)) : P x ↔ Q (e x) := by
    have hpoly : e ((m : ZMod (A * B)) * x - 1) =
        ((m : ZMod A) * (e x).1 - 1,
          (m : ZMod B) * (e x).2 - 1) := by
      apply Prod.ext <;> simp [e]
    constructor
    · rintro ⟨hx, hmx⟩
      have hxe : IsUnit (e x) := hx.map e.toRingHom
      have hmxe : IsUnit (e ((m : ZMod (A * B)) * x - 1)) :=
        hmx.map e.toRingHom
      rw [Prod.isUnit_iff] at hxe
      rw [hpoly, Prod.isUnit_iff] at hmxe
      exact ⟨⟨hxe.1, hmxe.1⟩, hxe.2, hmxe.2⟩
    · rintro ⟨⟨hxA, hmxA⟩, hxB, hmxB⟩
      have hxe : IsUnit (e x) := Prod.isUnit_iff.mpr ⟨hxA, hxB⟩
      have hmxe : IsUnit (e ((m : ZMod (A * B)) * x - 1)) := by
        rw [hpoly, Prod.isUnit_iff]
        exact ⟨hmxA, hmxB⟩
      have hx : IsUnit x := by
        have := hxe.map e.symm.toRingHom
        simpa using this
      have hmx : IsUnit ((m : ZMod (A * B)) * x - 1) := by
        have := hmxe.map e.symm.toRingHom
        simpa using this
      exact ⟨hx, hmx⟩
  let eP : Subtype P ≃ Subtype Q := Equiv.subtypeEquiv e.toEquiv heq
  let eQ : Subtype Q ≃ PreSieveUnitResidue A m × PreSieveUnitResidue B m :=
    { toFun := fun x =>
        (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact eP.trans eQ

noncomputable def preSieveResidueCount (W m : ℕ) [NeZero W] : ℕ := by
  classical
  exact Fintype.card (PreSieveUnitResidue W m)

/-- Totalized form of `preSieveResidueCount`; the zero modulus is assigned
count zero and every positive modulus uses its canonical `NeZero` instance. -/
noncomputable def preSieveResidueCountTotal (W m : ℕ) : ℕ := by
  classical
  exact if hW : W = 0 then 0 else
    let _ : NeZero W := ⟨hW⟩
    Fintype.card (PreSieveUnitResidue W m)

theorem preSieveResidueCount_mul {A B m : ℕ}
    [NeZero A] [NeZero B] [NeZero (A * B)] (hAB : A.Coprime B) :
    preSieveResidueCount (A * B) m =
      preSieveResidueCount A m * preSieveResidueCount B m := by
  classical
  unfold preSieveResidueCount
  rw [Fintype.card_congr (preSieveUnitResidueCrtEquiv hAB),
    Fintype.card_prod]

theorem preSieveResidueCountTotal_mul {A B m : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B) :
    preSieveResidueCountTotal (A * B) m =
      preSieveResidueCountTotal A m * preSieveResidueCountTotal B m := by
  classical
  let _ : NeZero A := ⟨hA.ne'⟩
  let _ : NeZero B := ⟨hB.ne'⟩
  let _ : NeZero (A * B) := ⟨Nat.mul_ne_zero hA.ne' hB.ne'⟩
  simp only [preSieveResidueCountTotal, dif_neg hA.ne', dif_neg hB.ne',
    dif_neg (Nat.mul_ne_zero hA.ne' hB.ne')]
  rw [Fintype.card_congr (preSieveUnitResidueCrtEquiv (m := m) hAB),
    Fintype.card_prod]

@[simp] theorem preSieveResidueCountTotal_one (m : ℕ) :
    preSieveResidueCountTotal 1 m = 1 := by
  classical
  rw [preSieveResidueCountTotal, dif_neg (by omega : (1 : ℕ) ≠ 0)]
  apply Fintype.card_eq_one_iff.mpr
  have hunit (x : ZMod 1) : IsUnit x := by
    rw [show x = 1 from Subsingleton.elim _ _]
    exact isUnit_one
  refine ⟨⟨0, ⟨hunit _, hunit _⟩⟩, ?_⟩
  intro y
  exact Subtype.ext (Subsingleton.elim _ _)

/-- Natural representatives in `allowedPreSieveResidues` and doubled unit
residues in `ZMod W` are the same finite set. -/
noncomputable def allowedPreSieveResiduesEquiv (W m : ℕ)
    (hW : 1 < W) (hm : 0 < m) :
    ↥(allowedPreSieveResidues W m) ≃ PreSieveUnitResidue W m := by
  classical
  let _ : NeZero W := ⟨by omega⟩
  have toProp (v : ↥(allowedPreSieveResidues W m)) :
      IsUnit (v.1 : ZMod W) ∧
        IsUnit ((m : ZMod W) * (v.1 : ZMod W) - 1) := by
    have hv := Finset.mem_filter.mp v.2
    have hvrange := Finset.mem_Ico.mp hv.1
    have hcop := Nat.coprime_mul_iff_left.mp hv.2
    constructor
    · exact (ZMod.isUnit_iff_coprime v.1 W).2 hcop.1
    · have hmv : 1 ≤ m * v.1 :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero hm.ne' (by omega))
      have hcast : ((m * v.1 - 1 : ℕ) : ZMod W) =
          (m : ZMod W) * (v.1 : ZMod W) - 1 := by
        push_cast [Nat.cast_sub hmv]
        ring
      rw [← hcast, ZMod.isUnit_iff_coprime]
      exact hcop.2
  have invProp (x : PreSieveUnitResidue W m) :
      x.1.val ∈ allowedPreSieveResidues W m := by
    have hxunitCast : IsUnit (x.1.val : ZMod W) := by
      simpa using x.2.1
    have hxunit : x.1.val.Coprime W :=
      (ZMod.isUnit_iff_coprime x.1.val W).1 hxunitCast
    have hxpos : 0 < x.1.val := by
      by_contra hxzero
      have hvalzero : x.1.val = 0 := by omega
      rw [hvalzero, Nat.coprime_zero_left] at hxunit
      omega
    have hmv : 1 ≤ m * x.1.val :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hxpos.ne')
    have hcast : ((m * x.1.val - 1 : ℕ) : ZMod W) =
        (m : ZMod W) * (x.1.val : ZMod W) - 1 := by
      push_cast [Nat.cast_sub hmv]
      ring
    have hxpolyCast : IsUnit ((m * x.1.val - 1 : ℕ) : ZMod W) := by
      rw [hcast]
      simpa using x.2.2
    have hxpoly : (m * x.1.val - 1).Coprime W :=
      (ZMod.isUnit_iff_coprime (m * x.1.val - 1) W).1 hxpolyCast
    rw [allowedPreSieveResidues, Finset.mem_filter]
    exact ⟨Finset.mem_Ico.mpr ⟨hxpos, ZMod.val_lt x.1⟩,
      hxunit.mul_left hxpoly⟩
  exact
    { toFun := fun v => ⟨(v.1 : ZMod W), toProp v⟩
      invFun := fun x => ⟨x.1.val, invProp x⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact ZMod.val_natCast_of_lt (Finset.mem_Ico.mp
          (Finset.mem_filter.mp v.2).1).2
      right_inv := by
        intro x
        apply Subtype.ext
        exact ZMod.natCast_zmod_val x.1 }

theorem card_allowedPreSieveResidues_eq_count {W m : ℕ}
    (hW : 1 < W) (hm : 0 < m) :
    (allowedPreSieveResidues W m).card =
      @preSieveResidueCount W m ⟨by omega⟩ := by
  classical
  let _ : NeZero W := ⟨by omega⟩
  simpa [preSieveResidueCount] using
    Fintype.card_congr (allowedPreSieveResiduesEquiv W m hW hm)

theorem preSieveResidueCountTotal_eq_allowed {W m : ℕ}
    (hW : 1 < W) (hm : 0 < m) :
    preSieveResidueCountTotal W m =
      (allowedPreSieveResidues W m).card := by
  rw [card_allowedPreSieveResidues_eq_count hW hm]
  classical
  rw [preSieveResidueCountTotal, dif_neg (by omega : W ≠ 0)]
  rfl

/-- Multiplicativity iterated over a finite set of distinct primes. -/
theorem preSieveResidueCountTotal_prod_primes (P : Finset ℕ) (m : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    preSieveResidueCountTotal (∏ p ∈ P, p) m =
      ∏ p ∈ P, preSieveResidueCountTotal p m := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p S hnot ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hSprime : ∀ q ∈ S, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hSpos : 0 < ∏ q ∈ S, q :=
        Finset.prod_pos fun q hq => (hSprime q hq).pos
      have hcop : p.Coprime (∏ q ∈ S, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hp (hSprime q hq)).2
        intro hpq
        subst q
        exact hnot hq
      rw [Finset.prod_insert hnot, Finset.prod_insert hnot,
        preSieveResidueCountTotal_mul hp.pos hSpos hcop,
        ih hSprime]

/-- Exact Euler product for the number of allowed residues modulo the
primorial.  This is the finite singular-density factor used in the doubled
Selberg normalization. -/
theorem card_allowedPreSieveResidues_primorial {w m : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) :
    (allowedPreSieveResidues (primorial w) m).card =
      ∏ p ∈ Nat.primesLE w, if p ∣ m then p - 1 else p - 2 := by
  have hprim : 1 < primorial w := one_lt_primorial_of_two_le hw
  rw [← preSieveResidueCountTotal_eq_allowed hprim hm,
    primorial_eq_prod_primesLE,
    preSieveResidueCountTotal_prod_primes (Nat.primesLE w) m
      (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  rw [preSieveResidueCountTotal_eq_allowed hpprime.one_lt hm,
    card_allowedPreSieveResidues_prime hpprime hm]

/-- Finite local density associated to the doubled pre-sieve. -/
noncomputable def preSieveDensity (w m : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE w,
    if p ∣ m then ((p : ℝ) - 1) / p else ((p : ℝ) - 2) / p

theorem card_allowedPreSieveResidues_div_primorial
    {w m : ℕ} (hw : 2 ≤ w) (hm : 0 < m) :
    ((allowedPreSieveResidues (primorial w) m).card : ℝ) /
        (primorial w : ℝ) = preSieveDensity w m := by
  rw [card_allowedPreSieveResidues_primorial hw hm,
    primorial_eq_prod_primesLE]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  by_cases hpm : p ∣ m
  · simp only [hpm, if_true]
    rw [Nat.cast_sub hpprime.one_le]
    norm_num
  · simp only [hpm, if_false]
    rw [Nat.cast_sub hpprime.two_le]
    norm_num

/-- For even `m`, the bad two-residue local factor at `p=2` is replaced by
the positive one-residue factor, so the finite density is positive. -/
theorem preSieveDensity_pos_of_even {w m : ℕ} (hmEven : Even m) :
    0 < preSieveDensity w m := by
  unfold preSieveDensity
  apply Finset.prod_pos
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    have hpOneR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    exact div_pos (by linarith) hpR
  · rw [if_neg hpm]
    have hpneTwo : p ≠ 2 := by
      intro hpTwo
      subst p
      exact hpm hmEven.two_dvd
    have hpThree : 3 ≤ p := by
      have := hpprime.two_le
      omega
    have hpTwoR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
    exact div_pos (by linarith) hpR

/-! ### Arithmetic main term after local-density extraction -/

def firstLcmProduct (H : Finset ℕ) (d d' : H → ℕ) : ℕ :=
  ∏ h : H, Nat.lcm (d h) (d' h)

def companionLcmProduct (H : Finset ℕ) (e e' : H → ℕ) : ℕ :=
  ∏ h : H, Nat.lcm (e h) (e' h)

theorem largeGapFullCrtModulus_eq_products
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ) :
    largeGapFullCrtModulus H W d e d' e' =
      W * firstLcmProduct H d d' * companionLcmProduct H e e' := by
  rw [largeGapFullCrtModulus_eq]
  rw [Fintype.prod_sum_type]
  simp [largeGapCrtModulus, firstLcmProduct, companionLcmProduct]
  ac_rfl

/-- Compatibility-filtered four-tuple arithmetic sum. -/
noncomputable def doubledSelbergFilteredArithmeticSum (H : Finset ℕ)
    (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (W : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if LargeGapCrtCompatible H W d e d' e' then
        lambda d e * lambda d' e' /
          ((firstLcmProduct H d d' : ℝ) * companionLcmProduct H e e')
      else 0

/-- Exact separation of interval length and the doubled pre-sieve density
from the compatibility-filtered normalization main term. -/
theorem doubledSelbergFilteredNormalizationMain_eq_density_mul_arithmeticSum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) (hm : 0 < m) :
    doubledSelbergFilteredNormalizationMain H D E lambda
        (primorial w) m q T =
      (T : ℝ) * preSieveDensity w m *
        doubledSelbergFilteredArithmeticSum H D E lambda (primorial w) := by
  classical
  have hden := card_allowedPreSieveResidues_div_primorial hw hm
  unfold doubledSelbergFilteredNormalizationMain
    doubledSelbergFilteredArithmeticSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hcompat : LargeGapCrtCompatible H (primorial w) d e d' e'
  · simp only [hcompat, if_true]
    rw [largeGapFullCrtModulus_eq_products]
    push_cast
    rw [← hden]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · simp [hcompat]

theorem indicatorCompatibleLcmSum_eq
    (H : Finset ℕ) (D : Finset (H → ℕ)) (a : (H → ℕ) → ℝ) :
    (∑ d ∈ D, ∑ d' ∈ D,
      if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
        a d * a d' / (firstLcmProduct H d d' : ℝ)
      else 0) =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H D a := by
  classical
  unfold BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  simp [firstLcmProduct, BoundedGaps.Maynard.divisorTupleLcm]

/-- Once the first and companion prime supports are separated, the filtered
doubled arithmetic main term is the tensor product of the two ordinary
Maynard compatible quadratic forms. -/
theorem doubledSelbergFilteredArithmeticSum_tensor
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    (a b : (H → ℕ) → ℝ) :
    doubledSelbergFilteredArithmeticSum H D E (fun d e => a d * b e) W =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H D a *
        BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H E b := by
  classical
  let f : (H → ℕ) → (H → ℕ) → ℝ := fun d d' =>
    if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
      a d * a d' / (firstLcmProduct H d d' : ℝ) else 0
  let g : (H → ℕ) → (H → ℕ) → ℝ := fun e e' =>
    if BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' then
      b e * b e' / (companionLcmProduct H e e' : ℝ) else 0
  have hterm (d : H → ℕ) (hd : d ∈ D) (e : H → ℕ) (he : e ∈ E)
      (d' : H → ℕ) (hd' : d' ∈ D) (e' : H → ℕ) (he' : e' ∈ E) :
      (if LargeGapCrtCompatible H W d e d' e' then
          (a d * b e) * (a d' * b e') /
            ((firstLcmProduct H d d' : ℝ) * companionLcmProduct H e e')
        else 0) = f d d' * g e e' := by
    rw [support.compatible_iff_cross hd hd' he he']
    by_cases hD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
    · by_cases hE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e'
      · simp [f, g, hD, hE]
        ring
      · simp [f, g, hD, hE]
    · simp [f, g, hD]
  unfold doubledSelbergFilteredArithmeticSum
  calc
    (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
      if LargeGapCrtCompatible H W d e d' e' then
        (a d * b e) * (a d' * b e') /
          ((firstLcmProduct H d d' : ℝ) * companionLcmProduct H e e')
      else 0) =
        ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
          f d d' * g e e' := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d' hd'
      apply Finset.sum_congr rfl
      intro e' he'
      exact hterm d hd e he d' hd' e' he'
    _ = (∑ d ∈ D, ∑ d' ∈ D, f d d') *
        (∑ e ∈ E, ∑ e' ∈ E, g e e') := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_mul_sum]
    _ = _ := by
      rw [show (∑ d ∈ D, ∑ d' ∈ D, f d d') =
          BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H D a by
        simpa [f] using indicatorCompatibleLcmSum_eq H D a]
      rw [show (∑ e ∈ E, ∑ e' ∈ E, g e e') =
          BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H E b by
        simpa [g, companionLcmProduct, firstLcmProduct] using
          indicatorCompatibleLcmSum_eq H E b]

/-- Exact filtered normalization main term for tensor coefficients, expressed
in the totient-expanded forms used by the existing Maynard machinery. -/
theorem doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE w m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m)
    (support : DoubledMaynardSupportConditions H D E RD RE
      (primorial w) m q)
    (a b : (H → ℕ) → ℝ) :
    doubledSelbergFilteredNormalizationMain H D E (fun d e => a d * b e)
        (primorial w) m q T =
      (T : ℝ) * preSieveDensity w m *
        (BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
            H D a *
          BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
            H E b) := by
  rw [doubledSelbergFilteredNormalizationMain_eq_density_mul_arithmeticSum
    H D E (fun d e => a d * b e) w m q T hw hm]
  rw [doubledSelbergFilteredArithmeticSum_tensor support a b]
  rw [BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum_eq_totientExpanded
    support.first_tuple]
  rw [BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum_eq_totientExpanded
    support.companion_tuple]

/-! #### The concrete separated normalization package -/

/-- The pre-sieved mass of the concrete separated tensor weight is exactly
the product of the two ordinary Maynard quadratic forms, times the interval
length and doubled local density, plus the explicitly defined endpoint
error. -/
theorem preSievedSeparatedDoubledWeightSum_eq_main_add_error
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    (F G : (H → ℝ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (separatedFirstSupport H RD Y)
          (separatedCompanionSupport H RE (primorial w) m)
          (separatedDoubledCoefficient H RD RE Y (primorial w) F G)
          m q n
      else 0) =
      (T : ℝ) * preSieveDensity w m *
        (BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (separatedFirstSupport H RD Y)
            (separatedFirstCoefficient H RD Y F) *
          BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (separatedCompanionSupport H RE (primorial w) m)
            (separatedCompanionCoefficient H RE (primorial w) G)) +
        doubledSelbergFilteredNormalizationError H
          (separatedFirstSupport H RD Y)
          (separatedCompanionSupport H RE (primorial w) m)
          (separatedDoubledCoefficient H RD RE Y (primorial w) F G)
          (primorial w) m q T := by
  let support : DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m q :=
    separatedSupportConditions hm hq (primorial_dvd_primorial hwY)
      hcover hRDq hREq hREY
  rw [preSievedDoubledWeightSum_eq_filteredMain_add_error
    H (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE (primorial w) m)
      (separatedDoubledCoefficient H RD RE Y (primorial w) F G)
      w m q T hw hm support.toResolvable]
  congr 1
  exact doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    hw hm support
      (separatedFirstCoefficient H RD Y F)
      (separatedCompanionCoefficient H RE (primorial w) G)

/-- Preferred version of the preceding identity: both tensor factors are
full Maynard supports.  Coprimality with `m` is encoded in the companion
pre-sieve modulus, so both displayed quadratic forms have the same standard
`Y`-transform diagonalization. -/
theorem preSievedFullySeparatedDoubledWeightSum_eq_main_add_error
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    (F G : (H → ℝ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD RE Y
            (primorial w) m F G)
          m q n
      else 0) =
      (T : ℝ) * preSieveDensity w m *
        (BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (separatedFirstSupport H RD Y)
            (separatedFirstCoefficient H RD Y F) *
          BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (fullySeparatedCompanionSupport H RE (primorial w) m)
            (fullySeparatedCompanionCoefficient H RE (primorial w) m G)) +
        doubledSelbergFilteredNormalizationError H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD RE Y
            (primorial w) m F G)
          (primorial w) m q T := by
  let support : DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m q :=
    fullySeparatedSupportConditions hm hq (primorial_dvd_primorial hwY)
      hcover hRDq hREq hREY
  rw [preSievedDoubledWeightSum_eq_filteredMain_add_error
    H (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      (fullySeparatedDoubledCoefficient H RD RE Y
        (primorial w) m F G)
      w m q T hw hm support.toResolvable]
  congr 1
  exact doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    hw hm support
      (separatedFirstCoefficient H RD Y F)
      (fullySeparatedCompanionCoefficient H RE (primorial w) m G)

/-- The main term in the preferred full-support normalization is the product
of two explicit `Y` diagonals after subtracting their respective collision
corrections. -/
theorem fullySeparatedNormalizationMain_eq_diagonals
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    (F G : (H → ℝ) → ℝ) :
    doubledSelbergFilteredNormalizationMain H
        (separatedFirstSupport H RD Y)
        (fullySeparatedCompanionSupport H RE (primorial w) m)
        (fullySeparatedDoubledCoefficient H RD RE Y
          (primorial w) m F G)
        (primorial w) m q T =
      (T : ℝ) * preSieveDensity w m *
        ((BoundedGaps.Maynard.maynardYDiagonalSum H RD (primorial Y)
              (BoundedGaps.Maynard.maynardYValue H RD (primorial Y) F) -
            BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
              (separatedFirstSupport H RD Y)
              (separatedFirstCoefficient H RD Y F)) *
          (BoundedGaps.Maynard.maynardYDiagonalSum H RE
                (primorial w * m)
              (BoundedGaps.Maynard.maynardYValue H RE
                (primorial w * m) G) -
            BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
              (fullySeparatedCompanionSupport H RE (primorial w) m)
              (fullySeparatedCompanionCoefficient H RE
                (primorial w) m G))) := by
  let support : DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m q :=
    fullySeparatedSupportConditions hm hq (primorial_dvd_primorial hwY)
      hcover hRDq hREq hREY
  rw [show fullySeparatedDoubledCoefficient H RD RE Y
      (primorial w) m F G = fun d e =>
        separatedFirstCoefficient H RD Y F d *
          fullySeparatedCompanionCoefficient H RE (primorial w) m G e by
    rfl]
  rw [doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    hw hm support
      (separatedFirstCoefficient H RD Y F)
      (fullySeparatedCompanionCoefficient H RE (primorial w) m G)]
  rw [separatedFirstTotientExpanded_eq_yDiagonal_sub_incompatible,
    fullySeparatedCompanionTotientExpanded_eq_yDiagonal_sub_incompatible]

/-- Explicit aggregate endpoint-error bound for the concrete separated
weight.  In the later asymptotic step `RD` and `RE` are small powers of the
interval scale, so this entirely elementary envelope is negligible. -/
theorem separatedDoubledNormalizationError_abs_le
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    {F G : (H → ℝ) → ℝ} {BF BG : ℝ}
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, |F x| ≤ BF) (hG : ∀ x, |G x| ≤ BG) :
    |doubledSelbergFilteredNormalizationError H
      (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE (primorial w) m)
      (separatedDoubledCoefficient H RD RE Y (primorial w) F G)
      (primorial w) m q T| ≤
      ((separatedFirstSupport H RD Y).card : ℝ) ^ 2 *
        ((separatedCompanionSupport H RE (primorial w) m).card : ℝ) ^ 2 *
        (((((RD : ℝ) *
              (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
            ((RE : ℝ) *
              (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG)) ^ 2) *
          (allowedPreSieveResidues (primorial w) m).card) := by
  let support : DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m q :=
    separatedSupportConditions hm hq (primorial_dvd_primorial hwY)
      hcover hRDq hREq hREY
  apply doubledSelbergFilteredNormalizationError_abs_le
    H (separatedFirstSupport H RD Y)
      (separatedCompanionSupport H RE (primorial w) m)
      (separatedDoubledCoefficient H RD RE Y (primorial w) F G)
      (primorial w) m q T support.toResolvable (primorial_pos w)
      (((RD : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
        ((RE : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG))
  · positivity
  · intro d hd e he
    exact separatedDoubledCoefficient_abs_le hBF hBG hF hG hd he

theorem fullySeparatedDoubledNormalizationError_abs_le
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    {F G : (H → ℝ) → ℝ} {BF BG : ℝ}
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, |F x| ≤ BF) (hG : ∀ x, |G x| ≤ BG) :
    |doubledSelbergFilteredNormalizationError H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      (fullySeparatedDoubledCoefficient H RD RE Y
        (primorial w) m F G)
      (primorial w) m q T| ≤
      ((separatedFirstSupport H RD Y).card : ℝ) ^ 2 *
        ((fullySeparatedCompanionSupport H RE
          (primorial w) m).card : ℝ) ^ 2 *
        (((((RD : ℝ) *
              (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
            ((RE : ℝ) *
              (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG)) ^ 2) *
          (allowedPreSieveResidues (primorial w) m).card) := by
  let support : DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m q :=
    fullySeparatedSupportConditions hm hq (primorial_dvd_primorial hwY)
      hcover hRDq hREq hREY
  apply doubledSelbergFilteredNormalizationError_abs_le
    H (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      (fullySeparatedDoubledCoefficient H RD RE Y
        (primorial w) m F G)
      (primorial w) m q T support.toResolvable (primorial_pos w)
      (((RD : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RD).card * BF) *
        ((RE : ℝ) *
          (BoundedGaps.Maynard.maynardDivisorTupleBox H RE).card * BG))
  · positivity
  · intro d hd e he
    exact fullySeparatedDoubledCoefficient_abs_le hBF hBG hF hG hd he

/-- Four-tuple divisor arithmetic remaining after extracting interval length
and the finite pre-sieve density. -/
noncomputable def doubledSelbergArithmeticSum (H : Finset ℕ)
    (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' /
      ((firstLcmProduct H d d' : ℝ) * companionLcmProduct H e e')

/-- Exact separation of the normalization main term into interval length,
local density, and divisor arithmetic. -/
theorem doubledSelbergNormalizationMain_eq_density_mul_arithmeticSum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) (hm : 0 < m) :
    doubledSelbergNormalizationMain H D E lambda (primorial w) m q T =
      (T : ℝ) * preSieveDensity w m *
        doubledSelbergArithmeticSum H D E lambda := by
  classical
  have hden := card_allowedPreSieveResidues_div_primorial hw hm
  unfold doubledSelbergNormalizationMain doubledSelbergArithmeticSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [largeGapFullCrtModulus_eq_products]
  push_cast
  rw [← hden]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Standard LCM quadratic form for one family of divisor tuples. -/
noncomputable def lcmQuadraticSum (H : Finset ℕ)
    (D : Finset (H → ℕ)) (coeff : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ d' ∈ D,
    coeff d * coeff d' / (firstLcmProduct H d d' : ℝ)

/-- On a support whose distinct coordinates are pairwise coprime, the
unrestricted LCM quadratic form is exactly the compatible Maynard main term.
This permits reuse of the finite totient expansion already developed for
the bounded-gap sieve; no asymptotic estimate is used here. -/
theorem lcmQuadraticSum_eq_compatibleMain
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (coeff : (H → ℕ) → ℝ)
    (hcross : ∀ d ∈ D, ∀ d' ∈ D,
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') :
    lcmQuadraticSum H D coeff =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
        H D coeff := by
  classical
  unfold lcmQuadraticSum
    BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
    firstLcmProduct BoundedGaps.Maynard.divisorTupleLcm
  apply Finset.sum_congr rfl
  intro d hd
  have hfilter :
      D.filter (fun d' =>
        BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') = D := by
    ext d'
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hd'
      exact ⟨hd', hcross d hd d' hd'⟩
  rw [hfilter]
  push_cast
  rfl

/-- Consequently the LCM quadratic form has the exact common-divisor
totient expansion used in the Maynard sieve. -/
theorem lcmQuadraticSum_eq_totientExpanded
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {coeff : (H → ℕ) → ℝ} {R W : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hcross : ∀ d ∈ D, ∀ d' ∈ D,
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') :
    lcmQuadraticSum H D coeff =
      BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        H D coeff := by
  rw [lcmQuadraticSum_eq_compatibleMain H D coeff hcross]
  exact
    BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum_eq_totientExpanded
      hD

/-- When the doubled coefficient is a tensor product, its arithmetic main
term factors into independent first-form and companion-form quadratic sums. -/
theorem doubledSelbergArithmeticSum_tensor
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (a b : (H → ℕ) → ℝ) :
    doubledSelbergArithmeticSum H D E (fun d e => a d * b e) =
      lcmQuadraticSum H D a * lcmQuadraticSum H E b := by
  classical
  unfold doubledSelbergArithmeticSum lcmQuadraticSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm (s := E) (t := D)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  simp only [firstLcmProduct, companionLcmProduct]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- For tensor coefficients, the normalization main term is therefore the
product of the two exact totient-expanded Maynard quadratic forms.  This is
the finite algebraic endpoint immediately before the Euler-product and
Riemann-sum estimates in Maynard's normalization lemma. -/
theorem doubledSelbergNormalizationMain_tensor_eq_totientExpanded
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    {a b : (H → ℕ) → ℝ} {RD RE w m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (primorial w) e)
    (hcrossD : ∀ d ∈ D, ∀ d' ∈ D,
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hcrossE : ∀ e ∈ E, ∀ e' ∈ E,
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e') :
    doubledSelbergNormalizationMain H D E (fun d e => a d * b e)
        (primorial w) m q T =
      (T : ℝ) * preSieveDensity w m *
        (BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
          H D a *
         BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
          H E b) := by
  rw [doubledSelbergNormalizationMain_eq_density_mul_arithmeticSum
    H D E (fun d e => a d * b e) w m q T hw hm]
  rw [doubledSelbergArithmeticSum_tensor]
  rw [lcmQuadraticSum_eq_totientExpanded hD hcrossD]
  rw [lcmQuadraticSum_eq_totientExpanded hE hcrossE]

/-- Raw mass assigned to one residue modulo `q`, before normalization. -/
noncomputable def largeGapResidueRawWeight (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (U w m q : ℕ) (a : Fin q) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc 0 (U / m),
    if n % q = a.1 ∧ largeGapPreSieved w m n then
      doubledSelbergWeight H D E lambda m q n
    else 0

theorem largeGapResidueRawWeight_nonneg (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (U w m q : ℕ) (a : Fin q) :
    0 ≤ largeGapResidueRawWeight H D E lambda U w m q a := by
  classical
  unfold largeGapResidueRawWeight
  exact Finset.sum_nonneg fun n _ => by
    split_ifs
    · exact doubledSelbergWeight_nonneg H D E lambda m q n
    · exact le_rfl

/-- A finite sum over all residues modulo a positive modulus partitions a
finite integer sum according to `n % q`. -/
theorem sum_fin_mod_indicator {q : ℕ} (hq : 0 < q)
    (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ a : Fin q, ∑ n ∈ S, if n % q = a.1 then f n else 0) =
      ∑ n ∈ S, f n := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let a : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
  rw [Finset.sum_eq_single a]
  · simp [a]
  · intro b hb hba
    have : n % q ≠ b.1 := by
      intro heq
      exact hba (Fin.ext heq.symm)
    simp [this]
  · simp

/-- Exact normalization denominator: summing the raw residue masses removes
the residue condition and leaves the total pre-sieved square weight. -/
theorem sum_largeGapResidueRawWeight {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (U w m : ℕ) :
    (∑ a : Fin q,
      largeGapResidueRawWeight H D E lambda U w m q a) =
      ∑ n ∈ Finset.Icc 0 (U / m),
        if largeGapPreSieved w m n then
          doubledSelbergWeight H D E lambda m q n
        else 0 := by
  classical
  unfold largeGapResidueRawWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let a : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
  rw [Finset.sum_eq_single a]
  · by_cases hpre : largeGapPreSieved w m n
    · simp [a, hpre]
    · simp [a, hpre]
  · intro b hb hba
    have hne : n % q ≠ b.1 := by
      intro heq
      exact hba (Fin.ext heq.symm)
    simp [hne]
  · simp

/-- The normalized residue measure associated with the doubled Selberg raw
weights. -/
noncomputable def largeGapResidueMass (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (U w m q : ℕ) (a : Fin q) : ℝ :=
  normalizeFiniteWeight
    (largeGapResidueRawWeight H D E lambda U w m q) a

theorem largeGapResidueMass_nonneg (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (U w m q : ℕ) (a : Fin q) :
    0 ≤ largeGapResidueMass H D E lambda U w m q a := by
  exact normalizeFiniteWeight_nonneg _
    (largeGapResidueRawWeight_nonneg H D E lambda U w m q) a

theorem sum_largeGapResidueMass_eq_one {q : ℕ}
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (U w m : ℕ)
    (hq : 0 < q)
    (hpos : 0 < ∑ n ∈ Finset.Icc 0 (U / m),
      if largeGapPreSieved w m n then
        doubledSelbergWeight H D E lambda m q n
      else 0) :
    ∑ a : Fin q, largeGapResidueMass H D E lambda U w m q a = 1 := by
  apply sum_normalizeFiniteWeight_eq_one
  rw [sum_largeGapResidueRawWeight hq]
  exact hpos

/-- A nonnegative weighted average of finitely many real values is at least
one of those values. -/
theorem exists_value_le_weighted_average
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (weight value : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hsum : ∑ ω, weight ω = 1) :
    ∃ ω, value ω ≤ ∑ ξ, weight ξ * value ξ := by
  obtain ⟨ω, _hω, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω) value Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  calc
    value ω = (∑ ξ, weight ξ) * value ω := by rw [hsum, one_mul]
    _ = ∑ ξ, weight ξ * value ω := by rw [Finset.sum_mul]
    _ ≤ ∑ ξ, weight ξ * value ξ := by
      apply Finset.sum_le_sum
      intro ξ hξ
      exact mul_le_mul_of_nonneg_left (hmin ξ hξ) (hweight ξ)

/-- If the expected number of uncovered elements is at most `B`, some
deterministic choice leaves at most `B` elements uncovered. -/
theorem expectation_to_deterministic_cover
    {Ω P : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq P]
    (weight : Ω → ℝ) (uncovered : Ω → Finset P)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hsum : ∑ ω, weight ω = 1) (B : ℝ)
    (haverage : ∑ ω, weight ω * (uncovered ω).card ≤ B) :
    ∃ ω, ((uncovered ω).card : ℝ) ≤ B := by
  obtain ⟨ω, hω⟩ := exists_value_le_weighted_average weight
    (fun ξ => ((uncovered ξ).card : ℝ)) hweight hsum
  exact ⟨ω, hω.trans haverage⟩

/-- The elementary exponential estimate used to bound the probability that
independent residue choices all miss one element. -/
theorem prod_one_sub_le_exp_neg_sum
    {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (hμ1 : ∀ i ∈ s, μ i ≤ 1) :
    ∏ i ∈ s, (1 - μ i) ≤ Real.exp (-(∑ i ∈ s, μ i)) := by
  calc
    ∏ i ∈ s, (1 - μ i) ≤ ∏ i ∈ s, Real.exp (-μ i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hμ1 i hi)
      · intro i _hi
        exact Real.one_sub_le_exp_neg (μ i)
    _ = Real.exp (∑ i ∈ s, -μ i) := by
      symm
      exact Real.exp_sum s (fun i => -μ i)
    _ = Real.exp (-(∑ i ∈ s, μ i)) := by
      rw [Finset.sum_neg_distrib]

/-- Product probability weights normalize when every coordinate probability
mass normalizes. -/
theorem assignmentWeight_sum
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {A : Q → Type*} [∀ q, Fintype (A q)]
    (μ : ∀ q, A q → ℝ) (hμ : ∀ q, ∑ a, μ q a = 1) :
    ∑ choice : ∀ q, A q, ∏ q, μ q (choice q) = 1 := by
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum]
  simp only [hμ, Finset.prod_const_one]

theorem assignmentWeight_nonneg
    {Q : Type*} [Fintype Q]
    {A : Q → Type*} [∀ q, Fintype (A q)]
    (μ : ∀ q, A q → ℝ) (hμ : ∀ q a, 0 ≤ μ q a) :
    ∀ choice : ∀ q, A q, 0 ≤ ∏ q, μ q (choice q) := by
  intro choice
  exact Finset.prod_nonneg fun q _hq => hμ q (choice q)

/-- Exact independence identity for the mass of assignments satisfying a
coordinatewise condition. -/
theorem independent_assignment_miss_mass
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {A : Q → Type*} [∀ q, Fintype (A q)]
    (μ : ∀ q, A q → ℝ) (miss : ∀ q, A q → Prop)
    [∀ q a, Decidable (miss q a)] :
    (∑ choice : ∀ q, A q,
        if (∀ q, miss q (choice q)) then ∏ q, μ q (choice q) else 0) =
      ∏ q, ∑ a, if miss q a then μ q a else 0 := by
  classical
  let t : ∀ q, Finset (A q) := fun q => Finset.univ.filter (miss q)
  calc
    (∑ choice : ∀ q, A q,
        if (∀ q, miss q (choice q)) then ∏ q, μ q (choice q) else 0) =
        ∑ choice ∈ Fintype.piFinset t, ∏ q, μ q (choice q) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext choice
        simp [t]
      · intro choice _hchoice
        rfl
    _ = ∏ q, ∑ a ∈ t q, μ q a := by
      symm
      exact Finset.prod_univ_sum t μ
    _ = ∏ q, ∑ a, if miss q a then μ q a else 0 := by
      apply Finset.prod_congr rfl
      intro q _hq
      simp only [t]
      rw [Finset.sum_filter]

/-- Independent choices miss a fixed element with probability at most the
exponential of minus its total coverage mass. -/
theorem independent_assignment_all_miss_le_exp
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {A : Q → Type*} [∀ q, Fintype (A q)]
    (μ : ∀ q, A q → ℝ) (hit : ∀ q, A q → Prop)
    [∀ q a, Decidable (hit q a)]
    (hμ0 : ∀ q a, 0 ≤ μ q a) (hμsum : ∀ q, ∑ a, μ q a = 1) :
    (∑ choice : ∀ q, A q,
        if (∀ q, ¬hit q (choice q)) then ∏ q, μ q (choice q) else 0) ≤
      Real.exp (-(∑ q, ∑ a, if hit q a then μ q a else 0)) := by
  rw [independent_assignment_miss_mass μ (fun q a => ¬hit q a)]
  have hlocal : ∀ q,
      (∑ a, if ¬hit q a then μ q a else 0) =
        1 - ∑ a, if hit q a then μ q a else 0 := by
    intro q
    rw [← hμsum q, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : hit q a <;> simp [ha]
  simp_rw [hlocal]
  apply prod_one_sub_le_exp_neg_sum
  intro q _hq
  calc
    (∑ a, if hit q a then μ q a else 0) ≤ ∑ a, μ q a := by
      apply Finset.sum_le_sum
      intro a _ha
      split_ifs
      · exact le_rfl
      · exact hμ0 q a
    _ = 1 := hμsum q

/-- Finite form of Maynard's expectation-to-cover argument.  Given
independent coordinate measures and an arbitrary finite set of objects, it
produces one deterministic assignment whose uncovered cardinality is bounded
by the sum of the exponential miss bounds. -/
theorem exists_assignment_uncovered_card_le
    {Q P : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq P]
    {A : Q → Type*} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
    (μ : ∀ q, A q → ℝ) (hit : ∀ q, A q → P → Prop)
    [∀ q a p, Decidable (hit q a p)]
    (hμ0 : ∀ q a, 0 ≤ μ q a) (hμsum : ∀ q, ∑ a, μ q a = 1)
    (S : Finset P) :
    ∃ choice : ∀ q, A q,
      (((S.filter fun p => ∀ q, ¬hit q (choice q) p).card : ℕ) : ℝ) ≤
        ∑ p ∈ S, Real.exp (-(∑ q, ∑ a, if hit q a p then μ q a else 0)) := by
  classical
  let weight : (∀ q, A q) → ℝ := fun choice => ∏ q, μ q (choice q)
  let uncovered : (∀ q, A q) → Finset P := fun choice =>
    S.filter fun p => ∀ q, ¬hit q (choice q) p
  apply expectation_to_deterministic_cover weight uncovered
    (assignmentWeight_nonneg μ hμ0) (assignmentWeight_sum μ hμsum)
  calc
    (∑ choice, weight choice * (uncovered choice).card) =
        ∑ choice, ∑ p ∈ S,
          if (∀ q, ¬hit q (choice q) p) then weight choice else 0 := by
      apply Finset.sum_congr rfl
      intro choice _hchoice
      simp only [uncovered, Finset.card_filter, Nat.cast_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      split_ifs <;> simp
    _ = ∑ p ∈ S, ∑ choice,
          if (∀ q, ¬hit q (choice q) p) then weight choice else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ S,
        Real.exp (-(∑ q, ∑ a, if hit q a p then μ q a else 0)) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact independent_assignment_all_miss_le_exp μ
        (fun q a => hit q a p) hμ0 hμsum

/-- Convert a deterministic assignment of one residue to each prime in `P`
into a partial cover of an arbitrary finite set `S`. -/
theorem exists_partialResidueCover_of_choice {S P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (choice : ∀ p : ↥P, Fin p.1)
    (hcovers : ∀ i ∈ S, ∃ p : ↥P, i % p.1 = (choice p).1) :
    ∃ cover : PartialResidueCover S, cover.primes = P := by
  let residue : ℕ → ℕ := fun p =>
    if hp : p ∈ P then (choice ⟨p, hp⟩).1 else 0
  refine ⟨⟨P, residue, hprime, ?_⟩, rfl⟩
  intro i hi
  obtain ⟨p, hp⟩ := hcovers i hi
  refine ⟨p.1, p.2, ?_⟩
  rw [Nat.ModEq]
  simp only [residue, p.2, dite_true]
  rw [Nat.mod_eq_of_lt (choice ⟨p.1, p.2⟩).2]
  exact hp

/-- Finite probabilistic criterion for covering any specified finite set of
offsets with one residue per prime. -/
theorem exists_partialResidueCover_of_independent_measures
    (S P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (μ : ∀ p : ↥P, Fin p.1 → ℝ)
    (hμ0 : ∀ p a, 0 ≤ μ p a)
    (hμsum : ∀ p, ∑ a, μ p a = 1)
    (hexp :
      (∑ i ∈ S, Real.exp (-(∑ p : ↥P, ∑ a,
        if i % p.1 = a.1 then μ p a else 0))) < 1) :
    ∃ cover : PartialResidueCover S, cover.primes = P := by
  classical
  let _ : ∀ p : ↥P, Nonempty (Fin p.1) := fun p =>
    ⟨⟨0, (hprime p.1 p.2).pos⟩⟩
  obtain ⟨choice, hchoice⟩ :=
    exists_assignment_uncovered_card_le μ
      (fun p a i => i % p.1 = a.1) hμ0 hμsum S
  have hcardlt :
      ((S.filter (fun i => ∀ p : ↥P,
        i % p.1 ≠ (choice p).1)).card : ℕ) < 1 := by
    exact_mod_cast hchoice.trans_lt hexp
  have hcardzero :
      (S.filter (fun i => ∀ p : ↥P,
        i % p.1 ≠ (choice p).1)).card = 0 := by
    omega
  apply exists_partialResidueCover_of_choice hprime choice
  intro i hi
  by_contra hnone
  push Not at hnone
  have himem : i ∈ S.filter
      (fun j => ∀ p : ↥P, j % p.1 ≠ (choice p).1) := by
    exact Finset.mem_filter.mpr ⟨hi, hnone⟩
  have : 0 < (S.filter
      (fun j => ∀ p : ↥P, j % p.1 ≠ (choice p).1)).card :=
    Finset.card_pos.mpr ⟨i, himem⟩
  omega

/-- Maynard's two-stage finite endpoint: use independent residue measures to
cover most of `S`, then inject the remaining offsets into a disjoint set of
fresh primes. -/
theorem exists_partialResidueCover_of_measures_and_fresh_primes
    (S P R : Finset ℕ)
    (hprimeP : ∀ p ∈ P, p.Prime) (hprimeR : ∀ p ∈ R, p.Prime)
    (hdisjoint : Disjoint P R)
    (μ : ∀ p : ↥P, Fin p.1 → ℝ)
    (hμ0 : ∀ p a, 0 ≤ μ p a)
    (hμsum : ∀ p, ∑ a, μ p a = 1)
    (hcapacity :
      (∑ i ∈ S, Real.exp (-(∑ p : ↥P, ∑ a,
        if i % p.1 = a.1 then μ p a else 0))) < (R.card : ℝ) + 1) :
    ∃ cover : PartialResidueCover S, cover.primes = P ∪ R := by
  classical
  let _ : ∀ p : ↥P, Nonempty (Fin p.1) := fun p =>
    ⟨⟨0, (hprimeP p.1 p.2).pos⟩⟩
  obtain ⟨choice, hchoice⟩ :=
    exists_assignment_uncovered_card_le μ
      (fun p a i => i % p.1 = a.1) hμ0 hμsum S
  let uncovered : Finset ℕ :=
    S.filter fun i => ∀ p : ↥P, i % p.1 ≠ (choice p).1
  let covered : Finset ℕ := S \ uncovered
  have hcardReal : (uncovered.card : ℝ) < (R.card : ℝ) + 1 := by
    exact hchoice.trans_lt hcapacity
  have hcardNat : uncovered.card ≤ R.card := by
    have : uncovered.card < R.card + 1 := by exact_mod_cast hcardReal
    omega
  have hcovered : ∀ i ∈ covered,
      ∃ p : ↥P, i % p.1 = (choice p).1 := by
    intro i hi
    have hiData := Finset.mem_sdiff.mp hi
    by_contra hnone
    push Not at hnone
    have hiUncovered : i ∈ uncovered := by
      exact Finset.mem_filter.mpr ⟨hiData.1, hnone⟩
    exact hiData.2 hiUncovered
  obtain ⟨coverP, hcoverP⟩ :=
    exists_partialResidueCover_of_choice hprimeP choice hcovered
  obtain ⟨coverR, hcoverR⟩ :=
    PartialResidueCover.exists_of_card_le hprimeR hcardNat
  have hsupports : Disjoint coverP.primes coverR.primes := by
    simpa [hcoverP, hcoverR] using hdisjoint
  have hunion : covered ∪ uncovered = S := by
    exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  refine ⟨(coverP.union coverR hsupports).reindex hunion, ?_⟩
  simp [PartialResidueCover.union, hcoverP, hcoverR]

/-- Finite data produced by the Maynard covering estimate for the survivor
set at parameters `(U,y,z)`.  `measurePrimes` implement the weighted random
cover and `freshPrimes` clean up its remaining exceptions. -/
structure SurvivorCoverData (U y z : ℕ) where
  measurePrimes : Finset ℕ
  freshPrimes : Finset ℕ
  measure_prime : ∀ p ∈ measurePrimes, p.Prime
  fresh_prime : ∀ p ∈ freshPrimes, p.Prime
  measure_support : ∀ p ∈ measurePrimes, z < p
  fresh_support : ∀ p ∈ freshPrimes, z < p
  supports_disjoint : Disjoint measurePrimes freshPrimes
  mass : ∀ p : ↥measurePrimes, Fin p.1 → ℝ
  mass_nonneg : ∀ p a, 0 ≤ mass p a
  mass_sum_one : ∀ p, ∑ a, mass p a = 1
  capacity :
    (∑ i ∈ initialSieveSurvivors U y z,
      Real.exp (-(∑ p : ↥measurePrimes, ∑ a,
        if i % p.1 = a.1 then mass p a else 0))) <
      (freshPrimes.card : ℝ) + 1

namespace SurvivorCoverData

variable {U y z : ℕ} (data : SurvivorCoverData U y z)

/-- Build survivor-cover data from arbitrary nonnegative raw residue weights.
This is the direct constructor used by the doubled Selberg weights, whose raw
mass is already a sum of squares rather than the square of one amplitude. -/
noncomputable def ofRawWeights
    (P R : Finset ℕ)
    (hprimeP : ∀ p ∈ P, p.Prime) (hprimeR : ∀ p ∈ R, p.Prime)
    (hsupportP : ∀ p ∈ P, z < p) (hsupportR : ∀ p ∈ R, z < p)
    (hdisjoint : Disjoint P R)
    (weight : ∀ p : ↥P, Fin p.1 → ℝ)
    (hweight : ∀ p a, 0 ≤ weight p a)
    (hsumpos : ∀ p, 0 < ∑ a, weight p a)
    (hcapacity :
      (∑ i ∈ initialSieveSurvivors U y z,
        Real.exp (-(∑ p : ↥P, ∑ a,
          if i % p.1 = a.1 then
            normalizedRawMass weight p a else 0))) <
        (R.card : ℝ) + 1) :
    SurvivorCoverData U y z where
  measurePrimes := P
  freshPrimes := R
  measure_prime := hprimeP
  fresh_prime := hprimeR
  measure_support := hsupportP
  fresh_support := hsupportR
  supports_disjoint := hdisjoint
  mass := normalizedRawMass weight
  mass_nonneg := normalizedRawMass_nonneg weight hweight
  mass_sum_one := sum_normalizedRawMass_eq_one weight hsumpos
  capacity := hcapacity

/-- Build survivor-cover data directly from unnormalized Selberg amplitudes. -/
noncomputable def ofAmplitudes
    (P R : Finset ℕ)
    (hprimeP : ∀ p ∈ P, p.Prime) (hprimeR : ∀ p ∈ R, p.Prime)
    (hsupportP : ∀ p ∈ P, z < p) (hsupportR : ∀ p ∈ R, z < p)
    (hdisjoint : Disjoint P R)
    (amplitude : ∀ p : ↥P, Fin p.1 → ℝ)
    (hnonzero : ∀ p, ∃ a, amplitude p a ≠ 0)
    (hcapacity :
      (∑ i ∈ initialSieveSurvivors U y z,
        Real.exp (-(∑ p : ↥P, ∑ a,
          if i % p.1 = a.1 then
            normalizedSquareMass amplitude p a else 0))) <
        (R.card : ℝ) + 1) :
    SurvivorCoverData U y z where
  measurePrimes := P
  freshPrimes := R
  measure_prime := hprimeP
  fresh_prime := hprimeR
  measure_support := hsupportP
  fresh_support := hsupportR
  supports_disjoint := hdisjoint
  mass := normalizedSquareMass amplitude
  mass_nonneg := normalizedSquareMass_nonneg amplitude
  mass_sum_one := sum_normalizedSquareMass_eq_one amplitude hnonzero
  capacity := hcapacity

theorem exists_partialCover :
    ∃ cover : PartialResidueCover (initialSieveSurvivors U y z),
      cover.primes = data.measurePrimes ∪ data.freshPrimes := by
  exact exists_partialResidueCover_of_measures_and_fresh_primes
    (initialSieveSurvivors U y z) data.measurePrimes data.freshPrimes
    data.measure_prime data.fresh_prime data.supports_disjoint data.mass
    data.mass_nonneg data.mass_sum_one data.capacity

theorem exists_residueCover (hyz : y ≤ z) :
    ∃ cover : ResidueCover U,
      cover.primes = Nat.primesLE z ∪
        (data.measurePrimes ∪ data.freshPrimes) := by
  obtain ⟨partialCover, hpartial⟩ := data.exists_partialCover
  have hsupport : ∀ p ∈ partialCover.primes, z < p := by
    intro p hp
    rw [hpartial] at hp
    obtain hpMeasure | hpFresh := Finset.mem_union.mp hp
    · exact data.measure_support p hpMeasure
    · exact data.fresh_support p hpFresh
  obtain ⟨cover, hcover⟩ :=
    residueCover_of_initial_and_survivor_cover hyz partialCover hsupport
  exact ⟨cover, hcover.trans (congrArg (Nat.primesLE z ∪ ·) hpartial)⟩

end SurvivorCoverData

/-- Exact finite-data contract between the Maynard survivor-cover estimate
and the already proved prime-gap endpoint. -/
theorem erdos4For_of_survivor_cover_data (C : ℝ)
    (hcovers : ∀ N : ℕ, ∃ U y z : ℕ,
      ∃ data : SurvivorCoverData U y z,
      y ≤ z ∧
      ∀ n : ℕ, N ≤ n →
        n < (max (max 2 (Nat.nth Nat.Prime N)) 1 + 1) *
          (∏ p ∈ Nat.primesLE z ∪
            (data.measurePrimes ∪ data.freshPrimes), p) →
        threshold C n < U) :
    Erdos4For C := by
  apply erdos4For_of_residue_covers C
  intro N
  obtain ⟨U, y, z, data, hyz, hscale⟩ := hcovers N
  obtain ⟨cover, hprimes⟩ := data.exists_residueCover hyz
  refine ⟨U, cover, ?_⟩
  intro n hN hn
  apply hscale n hN
  simpa [ResidueCover.modulus, hprimes] using hn

/-- A more convenient quantitative contract: if all cover primes are at most
`x`, their exact product can be replaced by `primorial x`. -/
theorem erdos4For_of_bounded_survivor_cover_data (C : ℝ)
    (hcovers : ∀ N : ℕ, ∃ U y z x : ℕ,
      ∃ data : SurvivorCoverData U y z,
      y ≤ z ∧ z ≤ x ∧
      (∀ p ∈ data.measurePrimes, p ≤ x) ∧
      (∀ p ∈ data.freshPrimes, p ≤ x) ∧
      ∀ n : ℕ, N ≤ n →
        n < (max (max 2 (Nat.nth Nat.Prime N)) 1 + 1) * primorial x →
        threshold C n < U) :
    Erdos4For C := by
  apply erdos4For_of_residue_covers C
  intro N
  obtain ⟨U, y, z, x, data, hyz, hzx, hmeasure, hfresh, hscale⟩ :=
    hcovers N
  obtain ⟨cover, hprimes⟩ := data.exists_residueCover hyz
  refine ⟨U, cover, ?_⟩
  intro n hN hn
  apply hscale n hN
  have hsubset : cover.primes ⊆ Nat.primesLE x := by
    rw [hprimes]
    intro p hp
    obtain hpSmall | hpLarge := Finset.mem_union.mp hp
    · have hpData := Nat.mem_primesLE.mp hpSmall
      exact Nat.mem_primesLE.mpr ⟨hpData.1.trans hzx, hpData.2⟩
    · obtain hpMeasure | hpFresh := Finset.mem_union.mp hpLarge
      · exact Nat.mem_primesLE.mpr
          ⟨hmeasure p hpMeasure, data.measure_prime p hpMeasure⟩
      · exact Nat.mem_primesLE.mpr
          ⟨hfresh p hpFresh, data.fresh_prime p hpFresh⟩
  have hproduct : cover.modulus ≤ primorial x := by
    unfold ResidueCover.modulus
    exact primeProduct_le_primorial hsubset
  exact hn.trans_le (Nat.mul_le_mul_left _ hproduct)

/-- Convert an explicit choice of one residue modulo every prime in `P` into
the `ResidueCover` structure used by the CRT endpoint. -/
theorem exists_residueCover_of_choice {y : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (choice : ∀ p : ↥P, Fin p.1)
    (hcovers : ∀ i : ℕ, 1 ≤ i → i ≤ y →
      ∃ p : ↥P, i % p.1 = (choice p).1) :
    ∃ cover : ResidueCover y, cover.primes = P := by
  let residue : ℕ → ℕ := fun p =>
    if hp : p ∈ P then (choice ⟨p, hp⟩).1 else 0
  refine ⟨⟨P, residue, hprime, ?_⟩, rfl⟩
  intro i hi1 hiy
  obtain ⟨p, hp⟩ := hcovers i hi1 hiy
  refine ⟨p.1, p.2, ?_⟩
  rw [Nat.ModEq]
  simp only [residue, p.2, dite_true]
  rw [Nat.mod_eq_of_lt (choice ⟨p.1, p.2⟩).2]
  exact hp

/-- Exact finite probabilistic criterion for a prime residue cover.  It is
the form in which the normalization and coverage estimates of the
Maynard--FGKMT sieve feed into the already formalized CRT construction. -/
theorem exists_residueCover_of_independent_measures {y : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (μ : ∀ p : ↥P, Fin p.1 → ℝ)
    (hμ0 : ∀ p a, 0 ≤ μ p a)
    (hμsum : ∀ p, ∑ a, μ p a = 1)
    (hexp :
      (∑ i ∈ Finset.Icc 1 y,
        Real.exp (-(∑ p : ↥P, ∑ a,
          if i % p.1 = a.1 then μ p a else 0))) < 1) :
    ∃ cover : ResidueCover y, cover.primes = P := by
  classical
  let _ : ∀ p : ↥P, Nonempty (Fin p.1) := fun p =>
    ⟨⟨0, (hprime p.1 p.2).pos⟩⟩
  obtain ⟨choice, hchoice⟩ :=
    exists_assignment_uncovered_card_le μ
      (fun p a i => i % p.1 = a.1) hμ0 hμsum (Finset.Icc 1 y)
  have hcardlt :
      (((Finset.Icc 1 y).filter
        (fun i => ∀ p : ↥P, i % p.1 ≠ (choice p).1)).card : ℕ) < 1 := by
    exact_mod_cast hchoice.trans_lt hexp
  have hcardzero :
      ((Finset.Icc 1 y).filter
        (fun i => ∀ p : ↥P, i % p.1 ≠ (choice p).1)).card = 0 := by
    omega
  apply exists_residueCover_of_choice P hprime choice
  intro i hi1 hiy
  have hi : i ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr ⟨hi1, hiy⟩
  by_contra hnone
  push Not at hnone
  have himem : i ∈ (Finset.Icc 1 y).filter
      (fun j => ∀ p : ↥P, j % p.1 ≠ (choice p).1) := by
    exact Finset.mem_filter.mpr ⟨hi, hnone⟩
  have : 0 < ((Finset.Icc 1 y).filter
      (fun j => ∀ p : ↥P, j % p.1 ≠ (choice p).1)).card :=
    Finset.card_pos.mpr ⟨i, himem⟩
  omega

/-- All finite data required at one scale by the probabilistic covering
argument.  The deep analytic part of Maynard--FGKMT is precisely the
construction of such data with a sufficiently small prime product. -/
structure ProbabilisticCoverData (y : ℕ) where
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime
  mass : ∀ p : ↥primes, Fin p.1 → ℝ
  mass_nonneg : ∀ p a, 0 ≤ mass p a
  mass_sum_one : ∀ p, ∑ a, mass p a = 1
  exponential_miss_sum_lt_one :
    (∑ i ∈ Finset.Icc 1 y,
      Real.exp (-(∑ p : ↥primes, ∑ a,
        if i % p.1 = a.1 then mass p a else 0))) < 1

namespace ProbabilisticCoverData

variable {y : ℕ} (data : ProbabilisticCoverData y)

theorem exists_residueCover :
    ∃ cover : ResidueCover y, cover.primes = data.primes := by
  exact exists_residueCover_of_independent_measures data.primes data.prime
    data.mass data.mass_nonneg data.mass_sum_one
    data.exponential_miss_sum_lt_one

end ProbabilisticCoverData

/-- Quantitative finite-probability contract for the unresolved analytic
input.  Once suitable probability data are available at every requested
scale, the theorem follows through the proved expectation and CRT bridges. -/
theorem erdos4For_of_probabilistic_covers (C : ℝ)
    (hcovers : ∀ N : ℕ, ∃ y : ℕ, ∃ data : ProbabilisticCoverData y,
      ∀ n : ℕ, N ≤ n →
        n < (max (max 2 (Nat.nth Nat.Prime N)) 1 + 1) *
          (∏ p ∈ data.primes, p) →
        threshold C n < y) :
    Erdos4For C := by
  apply erdos4For_of_residue_covers C
  intro N
  obtain ⟨y, data, hscale⟩ := hcovers N
  obtain ⟨cover, hprimes⟩ := data.exists_residueCover
  refine ⟨y, cover, ?_⟩
  intro n hN hn
  apply hscale n hN
  simpa [ResidueCover.modulus, hprimes] using hn

/-! ## Transporting the variable Maynard candidate to the shift tuple

The generic diagonal limit in `ErdosProblems.Erdos6.GenericDiagonal` is
indexed by the subtype of the concrete shift finset.  The variational family
above is indexed by `Fin K`.  The following coordinate equivalence transports
both the simplex and Lebesgue measure, and hence identifies the generic
arithmetic diagonal limit with the already certified integral `maynardI`.
-/

open MeasureTheory Set

noncomputable section

noncomputable def primorialShiftsIndexEquiv (K : ℕ) :
    ↑(primorialShifts K) ≃ Fin K :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, card_primorialShifts])

noncomputable def primorialShiftsReindex (K : ℕ) :
    (↑(primorialShifts K) → ℝ) ≃ᵐ (Fin K → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin K => ℝ)
    (primorialShiftsIndexEquiv K)

theorem primorialShiftsReindex_apply (K : ℕ)
    (t : ↑(primorialShifts K) → ℝ) :
    primorialShiftsReindex K t =
      fun i => t ((primorialShiftsIndexEquiv K).symm i) := by
  ext i
  simp [primorialShiftsReindex, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply]

/-- A globally continuous version of the inverse-affine factor.  Clipping
at zero removes its irrelevant pole on the negative half-line. -/
noncomputable def variableContinuousFactor (A u : ℝ) : ℝ :=
  (1 + A * max u 0)⁻¹

noncomputable def primorialShiftsContinuousProduct
    (K : ℕ) (A : ℝ) (t : ↑(primorialShifts K) → ℝ) : ℝ :=
  ∏ h, variableContinuousFactor A ((K : ℝ) * t h)

noncomputable def variableContinuousProduct
    (K : ℕ) (A : ℝ) (t : Fin K → ℝ) : ℝ :=
  ∏ i, variableContinuousFactor A ((K : ℝ) * t i)

/-- The variational candidate after reindexing its coordinates by the
concrete admissible shift tuple. -/
noncomputable def primorialShiftsCandidate
    (K : ℕ) (A : ℝ) (t : ↑(primorialShifts K) → ℝ) : ℝ :=
  VariableMaynard.candidate K A (primorialShiftsReindex K t)

theorem continuous_variableContinuousFactor {A : ℝ} (hA : 0 < A) :
    Continuous (variableContinuousFactor A) := by
  unfold variableContinuousFactor
  apply Continuous.inv₀
  · fun_prop
  · intro u
    have hnonneg : 0 ≤ A * max u 0 :=
      mul_nonneg hA.le (le_max_right _ _)
    linarith

theorem continuous_primorialShiftsContinuousProduct
    {K : ℕ} {A : ℝ} (hA : 0 < A) :
    Continuous (primorialShiftsContinuousProduct K A) := by
  unfold primorialShiftsContinuousProduct
  exact Erdos6.Maynard.continuous_scaledCoordinateProduct
    (continuous_variableContinuousFactor hA) K

theorem primorialShiftsReindex_mem_simplex_iff
    {K : ℕ} {t : ↑(primorialShifts K) → ℝ} :
    primorialShiftsReindex K t ∈ BoundedGaps.Maynard.maynardSimplex K ↔
      t ∈ BoundedGaps.Maynard.finiteSimplexOf (primorialShifts K) := by
  constructor
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro h hh
      have hi := ht.1 (primorialShiftsIndexEquiv K h) (Set.mem_univ _)
      simpa [primorialShiftsReindex_apply] using hi
    · have hsum :
          (∑ i : Fin K, primorialShiftsReindex K t i) =
            ∑ h : ↑(primorialShifts K), t h := by
        simpa [primorialShiftsReindex_apply] using
          ((primorialShiftsIndexEquiv K).symm.sum_comp t)
      rw [← hsum]
      exact ht.2
  · intro ht
    constructor
    · rw [BoundedGaps.Maynard.maynardCube,
        BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
      intro i hi
      have hh := ht.1 ((primorialShiftsIndexEquiv K).symm i)
        (Set.mem_univ _)
      simpa [primorialShiftsReindex_apply] using hh
    · have hsum :
          (∑ i : Fin K, primorialShiftsReindex K t i) =
            ∑ h : ↑(primorialShifts K), t h := by
        simpa [primorialShiftsReindex_apply] using
          ((primorialShiftsIndexEquiv K).symm.sum_comp t)
      rw [hsum]
      exact ht.2

theorem variableContinuousFactor_eq_factor {A u : ℝ}
    (hu : 0 ≤ u) :
    variableContinuousFactor A u = VariableMaynard.factor A u := by
  simp [variableContinuousFactor, VariableMaynard.factor, max_eq_left hu]

theorem primorialShiftsContinuousProduct_eq_candidate_of_mem_simplex
    {K : ℕ} {A : ℝ} {t : ↑(primorialShifts K) → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf (primorialShifts K)) :
    primorialShiftsContinuousProduct K A t =
      primorialShiftsCandidate K A t := by
  have hreindex := primorialShiftsReindex_mem_simplex_iff.mpr ht
  unfold primorialShiftsCandidate VariableMaynard.candidate
  rw [if_pos hreindex]
  rw [primorialShiftsReindex_apply]
  unfold primorialShiftsContinuousProduct VariableMaynard.product
  calc
    (∏ h : ↑(primorialShifts K),
        variableContinuousFactor A ((K : ℝ) * t h)) =
        ∏ h : ↑(primorialShifts K),
          VariableMaynard.factor A ((K : ℝ) * t h) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [variableContinuousFactor_eq_factor]
      exact mul_nonneg (Nat.cast_nonneg _) (ht.1 h (Set.mem_univ h)).1
    _ = ∏ i : Fin K,
        VariableMaynard.factor A
          ((K : ℝ) * t ((primorialShiftsIndexEquiv K).symm i)) := by
      exact ((primorialShiftsIndexEquiv K).symm.prod_comp
        (fun h => VariableMaynard.factor A ((K : ℝ) * t h))).symm

theorem primorialShiftsContinuousProduct_sq_bounds
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    (t : ↑(primorialShifts K) → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf (primorialShifts K)) :
    0 ≤ primorialShiftsContinuousProduct K A t ^ 2 ∧
      primorialShiftsContinuousProduct K A t ^ 2 ≤ 1 := by
  rw [primorialShiftsContinuousProduct_eq_candidate_of_mem_simplex ht]
  have hnonneg := VariableMaynard.candidate_nonneg hA
    (primorialShiftsReindex K t)
  have hle := VariableMaynard.candidate_le_one hA
    (primorialShiftsReindex K t)
  exact ⟨sq_nonneg _, pow_le_one₀ hnonneg hle⟩

theorem primorialShiftsReindex_preimage_simplex (K : ℕ) :
    primorialShiftsReindex K ⁻¹'
        BoundedGaps.Maynard.maynardSimplex K =
      BoundedGaps.Maynard.finiteSimplexOf (primorialShifts K) := by
  ext t
  exact primorialShiftsReindex_mem_simplex_iff

theorem primorialShiftsReindex_measurePreserving (K : ℕ) :
    MeasurePreserving (primorialShiftsReindex K) volume volume := by
  exact MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin K => ℝ) (primorialShiftsIndexEquiv K)

theorem primorialShiftsContinuousProduct_eq_reindex
    (K : ℕ) (A : ℝ) (t : ↑(primorialShifts K) → ℝ) :
    primorialShiftsContinuousProduct K A t =
      variableContinuousProduct K A (primorialShiftsReindex K t) := by
  unfold primorialShiftsContinuousProduct variableContinuousProduct
  rw [primorialShiftsReindex_apply]
  exact ((primorialShiftsIndexEquiv K).symm.prod_comp
    (fun h => variableContinuousFactor A ((K : ℝ) * t h))).symm

theorem variableContinuousProduct_eq_product_of_mem_cube
    {K : ℕ} {A : ℝ} {t : Fin K → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube K) :
    variableContinuousProduct K A t = VariableMaynard.product K A t := by
  unfold variableContinuousProduct VariableMaynard.product
  apply Finset.prod_congr rfl
  intro i _
  rw [variableContinuousFactor_eq_factor]
  exact mul_nonneg (Nat.cast_nonneg _) (ht i (Set.mem_univ i)).1

theorem integral_primorialShiftsContinuousProduct_sq_eq_maynardI
    {K : ℕ} {A : ℝ} :
    (∫ t in BoundedGaps.Maynard.finiteSimplexOf (primorialShifts K),
      primorialShiftsContinuousProduct K A t ^ 2) =
      BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A) := by
  have htransport := (primorialShiftsReindex_measurePreserving K).setIntegral_preimage_emb
    (primorialShiftsReindex K).measurableEmbedding
    (fun s : Fin K → ℝ => variableContinuousProduct K A s ^ 2)
    (BoundedGaps.Maynard.maynardSimplex K)
  rw [primorialShiftsReindex_preimage_simplex] at htransport
  have hleft :
      (fun t : ↑(primorialShifts K) → ℝ =>
        variableContinuousProduct K A (primorialShiftsReindex K t) ^ 2) =
      fun t => primorialShiftsContinuousProduct K A t ^ 2 := by
    funext t
    exact congrArg (fun x : ℝ => x ^ 2)
      (primorialShiftsContinuousProduct_eq_reindex K A t).symm
  rw [hleft] at htransport
  rw [htransport]
  have hsimplex : BoundedGaps.Maynard.maynardSimplex K ⊆
      BoundedGaps.Maynard.maynardCube K := fun _ ht => ht.1
  have hcubeMeas := BoundedGaps.Maynard.maynardCube_measurable K
  have hrestrict :
      (∫ t in BoundedGaps.Maynard.maynardCube K,
        VariableMaynard.candidate K A t ^ 2) =
      ∫ t in BoundedGaps.Maynard.maynardSimplex K,
        VariableMaynard.candidate K A t ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hcubeMeas hsimplex
    intro t ht
    simp [VariableMaynard.candidate, ht.2]
  unfold BoundedGaps.Maynard.maynardI
  rw [hrestrict]
  apply MeasureTheory.setIntegral_congr_fun
    (BoundedGaps.Maynard.maynardSimplex_measurable (k := K))
  intro t ht
  change variableContinuousProduct K A t ^ 2 =
    VariableMaynard.candidate K A t ^ 2
  rw [VariableMaynard.candidate, if_pos ht,
    variableContinuousProduct_eq_product_of_mem_cube ht.1]

/-- Exact algebraic bridge from the independent squarefree moment to the
actual Maynard diagonal, with coordinate collisions subtracted. -/
theorem normalized_primorialShiftsMaynardDiagonal_eq_independent_sub_collision
    {K : ℕ} {A alpha : ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hscale : Erdos6.Maynard.tupleNaturalScale
      (primorialShifts K) alpha N ≠ 0) :
    Erdos6.Maynard.normalizedTupleMaynardDiagonal
        (primorialShifts K) alpha (primorialShiftsCandidate K A) N =
      Erdos6.Maynard.normalizedTupleWeightedMoment
          (primorialShifts K) alpha
          (fun t => primorialShiftsContinuousProduct K A t ^ 2) N -
        Erdos6.Maynard.normalizedTupleCollisionMoment
          (primorialShifts K) alpha
          (fun t => primorialShiftsContinuousProduct K A t ^ 2) N := by
  have hsplit := Erdos6.Maynard.tupleWeightedMoment_sq_eq_diagonal_add_collision
    (H := primorialShifts K) (F := primorialShiftsCandidate K A)
    (G := primorialShiftsContinuousProduct K A) hR
    (fun t ht => primorialShiftsContinuousProduct_eq_candidate_of_mem_simplex ht)
  unfold Erdos6.Maynard.normalizedTupleMaynardDiagonal
    Erdos6.Maynard.normalizedTupleWeightedMoment
    Erdos6.Maynard.normalizedTupleCollisionMoment
  rw [hsplit]
  field_simp [hscale]
  ring

/-- At fixed dimension and decay parameter, the concrete shift tuple's
Maynard diagonal converges to the exact variational integral. -/
theorem tendsto_normalizedPrimorialShiftsMaynardDiagonal
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal
        (primorialShifts K) alpha (primorialShiftsCandidate K A) N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  have hH : (primorialShifts K).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_primorialShifts]
    exact hK
  let h0 : ↑(primorialShifts K) := ⟨hH.choose, hH.choose_spec⟩
  have hind := Erdos6.Maynard.tendsto_normalizedTupleWeightedMoment
    (f := fun t => primorialShiftsContinuousProduct K A t ^ 2)
    h0 halpha
    ((continuous_primorialShiftsContinuousProduct hA).pow 2)
    (primorialShiftsContinuousProduct_sq_bounds hA)
  rw [integral_primorialShiftsContinuousProduct_sq_eq_maynardI] at hind
  have hcoll := Erdos6.Maynard.tendsto_normalizedTupleCollisionMoment_zero
    (H := primorialShifts K) halpha
    (f := fun t => primorialShiftsContinuousProduct K A t ^ 2)
    (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (primorialShiftsContinuousProduct_sq_bounds hA x hx).2)
  have hdiff := hind.sub hcoll
  simpa using hdiff.congr' (by
    filter_upwards [
      BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha,
      Erdos6.Maynard.eventually_tupleNaturalScale_pos
        (H := primorialShifts K) halpha] with N hR hscale
    exact (normalized_primorialShiftsMaynardDiagonal_eq_independent_sub_collision
      hR hscale.ne').symm)

/-- The first-family `Y`-diagonal at the concrete Engelsma radius and
pre-sieve modulus. -/
noncomputable def primorialShiftsYDiagonal
    (K : ℕ) (A alpha : ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardYDiagonalSum (primorialShifts K)
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
    (BoundedGaps.Maynard.maynardYValue (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)
      (primorialShiftsCandidate K A))

theorem primorialShiftsYDiagonal_eq_tupleMaynardDiagonal
    (K : ℕ) (A alpha : ℝ) (N : ℕ) :
    primorialShiftsYDiagonal K A alpha N =
      Erdos6.Maynard.tupleMaynardDiagonal (primorialShifts K) alpha
        (primorialShiftsCandidate K A) N := by
  unfold primorialShiftsYDiagonal
  rw [BoundedGaps.Maynard.maynardYDiagonalSum_maynardYValue_eq_explicit]
  unfold Erdos6.Maynard.tupleMaynardDiagonal
    Erdos6.Maynard.tupleNormalizedLogPoint
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos6.Maynard.reciprocalTotientTupleWeight_eq_one_div_product]
  ring

theorem eventually_normalizedPrimorialShiftsYDiagonal_eq_natural_mul_logRatio
    {K : ℕ} {A alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
          primorialShiftsYDiagonal K A alpha N) /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N =
        Erdos6.Maynard.normalizedTupleMaynardDiagonal
            (primorialShifts K) alpha (primorialShiftsCandidate K A) N *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
              Fintype.card ↑(primorialShifts K) := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR, eventually_ge_atTop 3] with N hRN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : (0 : ℝ) < BoundedGaps.Maynard.engelsmaMaynardModulus N := by
    exact_mod_cast primorial_pos
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hphi : (0 : ℝ) < Nat.totient
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
  have hLnat : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  have hLreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :=
    Real.log_pos hRreal
  rw [primorialShiftsYDiagonal_eq_tupleMaynardDiagonal]
  unfold Erdos6.Maynard.normalizedTupleMaynardDiagonal
    Erdos6.Maynard.tupleNaturalScale Erdos6.Maynard.tupleMaynardScale
  simpa only [BoundedGaps.Maynard.engelsmaMaynardModulus] using
    (Erdos6.Maynard.normalized_maynardScale_eq_natural_mul_logRatio
      (H := primorialShifts K)
      (D := BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (N := N)
      (Rnat := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (Rreal := BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
      (Y := Erdos6.Maynard.tupleMaynardDiagonal (primorialShifts K) alpha
        (primorialShiftsCandidate K A) N)
      hNpos hW hphi hLnat hLreal)

/-- The scaled arithmetic `Y`-diagonal has the precise variational limit. -/
theorem tendsto_normalizedPrimorialShiftsYDiagonal
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
        primorialShiftsYDiagonal K A alpha N) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  have hnatural := tendsto_normalizedPrimorialShiftsMaynardDiagonal
    hK hA halpha
  have hratio :=
    (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
      halpha).pow (Fintype.card ↑(primorialShifts K))
  have hmul := hnatural.mul hratio
  simpa using hmul.congr' (by
    filter_upwards [
      eventually_normalizedPrimorialShiftsYDiagonal_eq_natural_mul_logRatio
        (K := K) (A := A) halpha] with N hN
    exact hN.symm)

theorem primorialShiftsCandidate_abs_le_one
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    (t : ↑(primorialShifts K) → ℝ) :
    |primorialShiftsCandidate K A t| ≤ 1 := by
  rw [abs_of_nonneg]
  · exact VariableMaynard.candidate_le_one hA _
  · exact VariableMaynard.candidate_nonneg hA _

/-- In the fixed dimension and with the fixed slope used in the already
verified large-candidate analysis, our transported candidate is exactly the
generic finite-tuple product candidate.  This lets us reuse the coordinate
fiber estimates without changing the admissible shift values. -/
theorem primorialShiftsCandidate_large_eq_tupleLargeCandidate :
    primorialShiftsCandidate Erdos6.Maynard.largeK Erdos6.Maynard.largeA =
      Erdos6.Maynard.tupleLargeCandidate
        (primorialShifts Erdos6.Maynard.largeK) := by
  funext t
  by_cases ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf
      (primorialShifts Erdos6.Maynard.largeK)
  · rw [Erdos6.Maynard.tupleLargeCandidate_eq_product_of_mem ht]
    unfold primorialShiftsCandidate VariableMaynard.candidate
    rw [if_pos (primorialShiftsReindex_mem_simplex_iff.mpr ht)]
    unfold VariableMaynard.product
    rw [primorialShiftsReindex_apply]
    calc
      (∏ i : Fin Erdos6.Maynard.largeK,
          VariableMaynard.factor Erdos6.Maynard.largeA
            ((Erdos6.Maynard.largeK : ℝ) *
              t ((primorialShiftsIndexEquiv
                Erdos6.Maynard.largeK).symm i))) =
          ∏ h : ↑(primorialShifts Erdos6.Maynard.largeK),
            VariableMaynard.factor Erdos6.Maynard.largeA
              ((Erdos6.Maynard.largeK : ℝ) * t h) := by
        exact (primorialShiftsIndexEquiv Erdos6.Maynard.largeK).symm.prod_comp
          (fun h => VariableMaynard.factor Erdos6.Maynard.largeA
            ((Erdos6.Maynard.largeK : ℝ) * t h))
      _ = ∏ h : ↑(primorialShifts Erdos6.Maynard.largeK),
          Erdos6.Maynard.largeFiberProfile (t h) := by
        apply Finset.prod_congr rfl
        intro h _
        have hx : 0 ≤ t h := (ht.1 h (Set.mem_univ h)).1
        rw [Erdos6.Maynard.largeFiberProfile_eq_largeG hx]
        rfl
  · have hreindex : primorialShiftsReindex Erdos6.Maynard.largeK t ∉
        BoundedGaps.Maynard.maynardSimplex Erdos6.Maynard.largeK := by
      simpa [primorialShiftsReindex_mem_simplex_iff] using ht
    simp [primorialShiftsCandidate, VariableMaynard.candidate,
      Erdos6.Maynard.tupleLargeCandidate, ht, hreindex]

/-- The exact first tensor quadratic form (including compatibility) has the
same positive variational limit: the cross-coordinate term is `o(1)`. -/
theorem tendsto_normalizedPrimorialShiftsCompatibleQuadratic
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
        BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
          (primorialShifts K)
          (separatedFirstSupport (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
          (separatedFirstCoefficient (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
            (primorialShiftsCandidate K A))) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  have hdiag := tendsto_normalizedPrimorialShiftsYDiagonal hK hA halpha
  have hcross := Erdos6.Maynard.tendsto_normalized_tupleMaynardS1Cross_zero
    (primorialShifts K) halpha (primorialShiftsCandidate K A)
    (B := 1) (by norm_num) (primorialShiftsCandidate_abs_le_one hA)
  have hsub := hdiag.sub hcross
  convert hsub using 1
  · funext N
    rw [separatedFirstTotientExpanded_eq_yDiagonal_sub_incompatible]
    unfold primorialShiftsYDiagonal Erdos6.Maynard.tupleMaynardS1Cross
      Erdos6.Maynard.tupleMaynardSupport
      Erdos6.Maynard.tupleMaynardCoefficient
      Erdos6.Maynard.maynardRadius Erdos6.Maynard.maynardModulus
      BoundedGaps.Maynard.engelsmaMaynardModulus
      separatedFirstSupport separatedFirstCoefficient
    ring_nf
  · ring_nf

/-! ### Removing the residual cofactor from the companion pre-sieve

Only the prime support of a pre-sieve modulus matters to Maynard's support
and coefficient.  A residual cofactor is smooth, so every one of its prime
divisors already divides the surrounding primorial. -/

def PrimeFactorsSubsumed (m W : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ∣ W

theorem coprime_mul_right_iff_of_primeFactorsSubsumed
    {a m W : ℕ} (hsub : PrimeFactorsSubsumed m W) :
    a.Coprime (W * m) ↔ a.Coprime W := by
  constructor
  · intro h
    exact Nat.Coprime.of_dvd_right (dvd_mul_right W m) h
  · intro hW
    apply Nat.Coprime.mul_right hW
    by_contra ham
    obtain ⟨p, hp, hpa, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp ham
    have hpW := hsub p hp hpm
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, hpW⟩) hW

theorem primeFactorsSubsumed_primorial_of_smooth
    {m y w : ℕ} (hm : m ∈ Nat.smoothNumbers (y + 1)) (hyw : y ≤ w) :
    PrimeFactorsSubsumed m (primorial w) := by
  rw [Nat.mem_smoothNumbers'] at hm
  intro p hp hpm
  apply hp.dvd_primorial_iff.mpr
  have hpy : p < y + 1 := hm p hp hpm
  omega

theorem isMaynardDivisorTuple_mul_right_iff_of_primeFactorsSubsumed
    {H : Finset ℕ} {R m W : ℕ}
    (hsub : PrimeFactorsSubsumed m W) (d : H → ℕ) :
    BoundedGaps.Maynard.IsMaynardDivisorTuple H R (W * m) d ↔
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d := by
  unfold BoundedGaps.Maynard.IsMaynardDivisorTuple
  rw [coprime_mul_right_iff_of_primeFactorsSubsumed hsub]

theorem maynardDivisorTupleSupport_mul_right_eq_of_primeFactorsSubsumed
    {H : Finset ℕ} {R m W : ℕ}
    (hsub : PrimeFactorsSubsumed m W) :
    BoundedGaps.Maynard.maynardDivisorTupleSupport H R (W * m) =
      BoundedGaps.Maynard.maynardDivisorTupleSupport H R W := by
  classical
  ext d
  simp only [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff]
  rw [isMaynardDivisorTuple_mul_right_iff_of_primeFactorsSubsumed hsub]

theorem maynardCoefficient_mul_right_eq_of_primeFactorsSubsumed
    {H : Finset ℕ} {R m W : ℕ}
    (hsub : PrimeFactorsSubsumed m W) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) :
    BoundedGaps.Maynard.maynardCoefficient H R (W * m) F d =
      BoundedGaps.Maynard.maynardCoefficient H R W F d := by
  classical
  unfold BoundedGaps.Maynard.maynardCoefficient
  simp only [coprime_mul_right_iff_of_primeFactorsSubsumed hsub]

theorem fullySeparatedCompanionSupport_eq_standard_of_primeFactorsSubsumed
    {H : Finset ℕ} {RE W m : ℕ}
    (hsub : PrimeFactorsSubsumed m W) :
    fullySeparatedCompanionSupport H RE W m =
      BoundedGaps.Maynard.maynardDivisorTupleSupport H RE W := by
  exact maynardDivisorTupleSupport_mul_right_eq_of_primeFactorsSubsumed hsub

theorem fullySeparatedCompanionCoefficient_eq_standard_of_primeFactorsSubsumed
    {H : Finset ℕ} {RE W m : ℕ}
    (hsub : PrimeFactorsSubsumed m W) (G : (H → ℝ) → ℝ) :
    fullySeparatedCompanionCoefficient H RE W m G =
      BoundedGaps.Maynard.maynardCoefficient H RE W G := by
  funext e
  exact maynardCoefficient_mul_right_eq_of_primeFactorsSubsumed hsub G e

theorem fullySeparatedCompanionTotientExpanded_eq_standard_of_primeFactorsSubsumed
    {H : Finset ℕ} {RE W m : ℕ}
    (hsub : PrimeFactorsSubsumed m W) (G : (H → ℝ) → ℝ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
        (fullySeparatedCompanionSupport H RE W m)
        (fullySeparatedCompanionCoefficient H RE W m G) =
      BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE W)
        (BoundedGaps.Maynard.maynardCoefficient H RE W G) := by
  rw [fullySeparatedCompanionSupport_eq_standard_of_primeFactorsSubsumed hsub,
    fullySeparatedCompanionCoefficient_eq_standard_of_primeFactorsSubsumed hsub]

/-- The companion quadratic has the same variational limit uniformly for an
arbitrary sequence of cofactors whose prime support is already pre-sieved. -/
theorem tendsto_normalizedPrimorialShiftsCompanionCompatibleQuadratic
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (m : ℕ → ℕ)
    (hsub : ∀ N, PrimeFactorsSubsumed (m N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
        BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
          (primorialShifts K)
          (fullySeparatedCompanionSupport (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N))
          (fullySeparatedCompanionCoefficient (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
            (primorialShiftsCandidate K A))) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  have hfirst := tendsto_normalizedPrimorialShiftsCompatibleQuadratic
    hK hA halpha
  convert hfirst using 1
  funext N
  rw [fullySeparatedCompanionTotientExpanded_eq_standard_of_primeFactorsSubsumed
    (hsub N)]
  unfold separatedFirstSupport separatedFirstCoefficient
  rfl

/-! ### The normalized tensor main term -/

noncomputable def normalizedFirstCompatibleQuadratic
    (K : ℕ) (A alpha : ℝ) (N : ℕ) : ℝ :=
  (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
      (primorialShifts K)
      (separatedFirstSupport (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
      (separatedFirstCoefficient (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
        (primorialShiftsCandidate K A))) /
    Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N

noncomputable def normalizedCompanionCompatibleQuadratic
    (K : ℕ) (A alpha : ℝ) (m N : ℕ) : ℝ :=
  (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
      (primorialShifts K)
      (fullySeparatedCompanionSupport (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
      (fullySeparatedCompanionCoefficient (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
        (primorialShiftsCandidate K A))) /
    Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N

theorem tendsto_normalizedFirstCompatibleQuadratic
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) :
    Tendsto (normalizedFirstCompatibleQuadratic K A alpha) atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  exact tendsto_normalizedPrimorialShiftsCompatibleQuadratic hK hA halpha

theorem tendsto_normalizedCompanionCompatibleQuadratic
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (m : ℕ → ℕ)
    (hsub : ∀ N, PrimeFactorsSubsumed (m N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    Tendsto (fun N => normalizedCompanionCompatibleQuadratic
      K A alpha (m N) N) atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A))) := by
  exact tendsto_normalizedPrimorialShiftsCompanionCompatibleQuadratic
    hK hA halpha m hsub

theorem tendsto_normalizedSeparatedTensorQuadratic
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (m : ℕ → ℕ)
    (hsub : ∀ N, PrimeFactorsSubsumed (m N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    Tendsto (fun N =>
      normalizedFirstCompatibleQuadratic K A alpha N *
        normalizedCompanionCompatibleQuadratic K A alpha (m N) N)
      atTop
      (nhds (BoundedGaps.Maynard.maynardI K
        (VariableMaynard.candidate K A) ^ 2)) := by
  simpa [pow_two] using
    (tendsto_normalizedFirstCompatibleQuadratic hK hA halpha).mul
      (tendsto_normalizedCompanionCompatibleQuadratic hK hA halpha m hsub)

/-- A uniform eventual positive lower bound for the tensor arithmetic main
term.  This is the denominator-positivity input for the residue measures. -/
theorem eventually_normalizedSeparatedTensorQuadratic_gt_half
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (m : ℕ → ℕ)
    (hsub : ∀ N, PrimeFactorsSubsumed (m N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A) ^ 2 / 2 <
        normalizedFirstCompatibleQuadratic K A alpha N *
          normalizedCompanionCompatibleQuadratic K A alpha (m N) N := by
  have hI := VariableMaynard.maynardI_candidate_pos hK hA
  have hlim := tendsto_normalizedSeparatedTensorQuadratic
    hK hA halpha m hsub
  apply (tendsto_order.1 hlim).1
  nlinarith [sq_pos_of_pos hI]

/-! ### A degenerate companion divisor family

For radius `2`, the all-ones tuple is the entire companion support.  Its
coefficient and compatible quadratic are exactly one.  This parameter
choice leaves the companion polynomial in the pre-sieve while avoiding a
second growing divisor scale. -/

noncomputable def constantOneTuple (H : Finset ℕ) : H → ℕ :=
  fun _ => 1

theorem maynardDivisorTupleBox_two_eq_singleton (H : Finset ℕ) :
    BoundedGaps.Maynard.maynardDivisorTupleBox H 2 =
      {constantOneTuple H} := by
  classical
  ext d
  simp only [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff,
    Finset.mem_singleton]
  constructor
  · intro hd
    funext h
    have := hd h
    change d h = 1
    omega
  · intro hd
    subst d
    simp [constantOneTuple]

theorem divisorTupleProduct_constantOneTuple (H : Finset ℕ) :
    BoundedGaps.Maynard.divisorTupleProduct H (constantOneTuple H) = 1 := by
  simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]

theorem maynardDivisorTupleSupport_two_eq_singleton
    (H : Finset ℕ) (W : ℕ) :
    BoundedGaps.Maynard.maynardDivisorTupleSupport H 2 W =
      {constantOneTuple H} := by
  classical
  ext d
  rw [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff,
    maynardDivisorTupleBox_two_eq_singleton]
  simp only [Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · intro hd
    subst d
    refine ⟨rfl, ?_⟩
    simp [BoundedGaps.Maynard.IsMaynardDivisorTuple,
      divisorTupleProduct_constantOneTuple]

theorem maynardCoefficient_two_constant_one_at_one
    (H : Finset ℕ) (W : ℕ) :
    BoundedGaps.Maynard.maynardCoefficient H 2 W (fun _ => (1 : ℝ))
      (constantOneTuple H) = 1 := by
  classical
  unfold BoundedGaps.Maynard.maynardCoefficient
  rw [divisorTupleProduct_constantOneTuple]
  rw [maynardDivisorTupleBox_two_eq_singleton]
  simp [constantOneTuple, divisorTupleProduct_constantOneTuple]

theorem fullySeparatedCompanionSupport_two_eq_singleton
    (H : Finset ℕ) (W m : ℕ) :
    fullySeparatedCompanionSupport H 2 W m = {constantOneTuple H} := by
  unfold fullySeparatedCompanionSupport
  exact maynardDivisorTupleSupport_two_eq_singleton H (W * m)

theorem fullySeparatedCompanionCoefficient_two_constant_one_at_one
    (H : Finset ℕ) (W m : ℕ) :
    fullySeparatedCompanionCoefficient H 2 W m (fun _ => (1 : ℝ))
      (constantOneTuple H) = 1 := by
  unfold fullySeparatedCompanionCoefficient
  exact maynardCoefficient_two_constant_one_at_one H (W * m)

theorem fullySeparatedCompanionTotientExpanded_two_constant_one
    (H : Finset ℕ) (W m : ℕ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
        (fullySeparatedCompanionSupport H 2 W m)
        (fullySeparatedCompanionCoefficient H 2 W m
          (fun _ => (1 : ℝ))) = 1 := by
  classical
  rw [fullySeparatedCompanionSupport_two_eq_singleton]
  unfold BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
  have hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H
      (constantOneTuple H) (constantOneTuple H) := by
    intro a b hab
    simp [constantOneTuple]
  simp only [Finset.sum_singleton]
  rw [Finset.filter_eq_self.mpr]
  · simp [constantOneTuple,
      fullySeparatedCompanionCoefficient_two_constant_one_at_one,
      BoundedGaps.Maynard.commonDivisorTotientSum_eq_gcd]
  · intro e he
    rw [Finset.mem_singleton] at he
    subst e
    exact hcross

/-- Exact finite normalization with the degenerate companion family.  The
entire main term is the first compatible Maynard quadratic; the displayed
remainder is still the literal aggregate CRT endpoint error. -/
theorem preSievedTrivialCompanionWeightSum_eq_main_add_error
    {H : Finset ℕ} {RD w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (htwoq : 2 ≤ q) (htwoY : 2 ≤ Y)
    (F : (H → ℝ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H 2 (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD 2 Y
            (primorial w) m F (fun _ => (1 : ℝ)))
          m q n
      else 0) =
      (T : ℝ) * preSieveDensity w m *
        BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
          (separatedFirstSupport H RD Y)
          (separatedFirstCoefficient H RD Y F) +
        doubledSelbergFilteredNormalizationError H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H 2 (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD 2 Y
            (primorial w) m F (fun _ => (1 : ℝ)))
          (primorial w) m q T := by
  have h := preSievedFullySeparatedDoubledWeightSum_eq_main_add_error
    (H := H) (RD := RD) (RE := 2) (w := w) (Y := Y)
    (m := m) (q := q) (T := T) hw hm hq hwY hcover hRDq htwoq htwoY
    F (fun _ => (1 : ℝ))
  rw [fullySeparatedCompanionTotientExpanded_two_constant_one] at h
  simpa using h

/-! The actual covering measure uses residues modulo a prime `q`, but its
shifted forms may use the auxiliary multiplier `W*q`.  This forces every
shift to vanish modulo the pre-sieve modulus `W` while preserving the residue
modulo `q`. -/

/-- The two full separated supports remain admissible after replacing the
auxiliary prime multiplier `q` by `W*q`.  The extra factor is harmless because
every divisor tuple is already coprime to the pre-sieve modulus `W`. -/
theorem fullySeparatedScaledSupportConditions
    {H : Finset ℕ} {RD RE w Y m q : ℕ}
    (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y) :
    DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      RD RE (primorial w) m (primorial w * q) := by
  let base := fullySeparatedSupportConditions hm hq
    (primorial_dvd_primorial hwY) hcover hRDq hREq hREY
  refine
    { m_pos := hm
      q_pos := Nat.mul_pos (primorial_pos w) hq.pos
      first_tuple := base.first_tuple
      companion_tuple := base.companion_tuple
      covers_shift_differences := hcover
      q_first_coprime := ?_
      q_companion_coprime := ?_
      m_companion_coprime := base.m_companion_coprime
      cross_family := base.cross_family }
  · intro d hd
    exact (base.first_tuple d hd).2.1.symm.mul_left
      (base.q_first_coprime d hd)
  · intro e he
    exact (base.companion_tuple e he).2.1.symm.mul_left
      (base.q_companion_coprime e he)

/-- Exact normalization for the full separated tensor weight when the
covering shifts use the scaled multiplier `W*q`. -/
theorem preSievedScaledFullySeparatedDoubledWeightSum_eq_main_add_error
    {H : Finset ℕ} {RD RE w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y)
    (F G : (H → ℝ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD RE Y
            (primorial w) m F G)
          m (primorial w * q) n
      else 0) =
      (T : ℝ) * preSieveDensity w m *
        (BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (separatedFirstSupport H RD Y)
            (separatedFirstCoefficient H RD Y F) *
          BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
            (fullySeparatedCompanionSupport H RE (primorial w) m)
            (fullySeparatedCompanionCoefficient H RE (primorial w) m G)) +
        doubledSelbergFilteredNormalizationError H
          (separatedFirstSupport H RD Y)
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD RE Y
            (primorial w) m F G)
          (primorial w) m (primorial w * q) T := by
  let support := fullySeparatedScaledSupportConditions
    (H := H) (RD := RD) (RE := RE) (w := w) (Y := Y)
    (m := m) (q := q) hm hq hwY hcover hRDq hREq hREY
  rw [preSievedDoubledWeightSum_eq_filteredMain_add_error
    H (separatedFirstSupport H RD Y)
      (fullySeparatedCompanionSupport H RE (primorial w) m)
      (fullySeparatedDoubledCoefficient H RD RE Y
        (primorial w) m F G)
      w m (primorial w * q) T hw hm support.toResolvable]
  congr 1
  exact doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    hw hm support
      (separatedFirstCoefficient H RD Y F)
      (fullySeparatedCompanionCoefficient H RE (primorial w) m G)

theorem trivialCompanionScaledSupportConditions
    {H : Finset ℕ} {RD w m q : ℕ}
    (_hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q) :
    DoubledMaynardSupportConditions H
      (separatedFirstSupport H RD w)
      (fullySeparatedCompanionSupport H 2 (primorial w) m)
      RD 2 (primorial w) m (primorial w * q) := by
  refine
    { m_pos := hm
      q_pos := Nat.mul_pos (primorial_pos w) hq.pos
      first_tuple := ?_
      companion_tuple := ?_
      covers_shift_differences := hcover
      q_first_coprime := ?_
      q_companion_coprime := ?_
      m_companion_coprime := ?_
      cross_family := ?_ }
  · intro d hd
    simpa [separatedFirstSupport] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  · intro e he
    have he' : e = constantOneTuple H := by
      rw [fullySeparatedCompanionSupport_two_eq_singleton H (primorial w) m]
        at he
      exact Finset.mem_singleton.mp he
    subst e
    refine ⟨?_, ?_, ?_⟩
    · simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]
    · simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]
    · simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]
  · intro d hd
    have hdMay : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD
        (primorial w) d := by
      simpa [separatedFirstSupport] using
        BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    apply Nat.Coprime.mul_left
    · exact hdMay.2.1.symm
    · apply (hq.coprime_iff_not_dvd).2
      intro hqdiv
      have hprodpos : 0 < BoundedGaps.Maynard.divisorTupleProduct H d :=
        Nat.pos_of_ne_zero hdMay.2.2.ne_zero
      have hqle : q ≤ BoundedGaps.Maynard.divisorTupleProduct H d :=
        Nat.le_of_dvd hprodpos hqdiv
      have hprodlt : BoundedGaps.Maynard.divisorTupleProduct H d < RD :=
        hdMay.1
      omega
  · intro e he
    have he' : e = constantOneTuple H := by
      rw [fullySeparatedCompanionSupport_two_eq_singleton H (primorial w) m]
        at he
      exact Finset.mem_singleton.mp he
    subst e
    simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]
  · intro e he
    have he' : e = constantOneTuple H := by
      rw [fullySeparatedCompanionSupport_two_eq_singleton H (primorial w) m]
        at he
      exact Finset.mem_singleton.mp he
    subst e
    simp [BoundedGaps.Maynard.divisorTupleProduct, constantOneTuple]
  · intro d hd e he a b
    have he' : e = constantOneTuple H := by
      rw [fullySeparatedCompanionSupport_two_eq_singleton H (primorial w) m]
        at he
      exact Finset.mem_singleton.mp he
    subst e
    simp [constantOneTuple]

/-- Exact normalization for the scaled auxiliary multiplier `W*q`.  The
main term is unchanged; only the literal CRT remainder records the scaled
multiplier. -/
theorem preSievedScaledTrivialCompanionWeightSum_eq_main_add_error
    {H : Finset ℕ} {RD w m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hRDq : RD ≤ q)
    (F : (H → ℝ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (separatedFirstSupport H RD w)
          (fullySeparatedCompanionSupport H 2 (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD 2 w
            (primorial w) m F (fun _ => (1 : ℝ)))
          m (primorial w * q) n
      else 0) =
      (T : ℝ) * preSieveDensity w m *
        BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum H
          (separatedFirstSupport H RD w)
          (separatedFirstCoefficient H RD w F) +
        doubledSelbergFilteredNormalizationError H
          (separatedFirstSupport H RD w)
          (fullySeparatedCompanionSupport H 2 (primorial w) m)
          (fullySeparatedDoubledCoefficient H RD 2 w
            (primorial w) m F (fun _ => (1 : ℝ)))
          (primorial w) m (primorial w * q) T := by
  let support := trivialCompanionScaledSupportConditions
    (H := H) (RD := RD) (w := w) (m := m) (q := q)
    hw hm hq hcover hRDq
  rw [preSievedDoubledWeightSum_eq_filteredMain_add_error
    H (separatedFirstSupport H RD w)
      (fullySeparatedCompanionSupport H 2 (primorial w) m)
      (fullySeparatedDoubledCoefficient H RD 2 w
        (primorial w) m F (fun _ => (1 : ℝ)))
      w m (primorial w * q) T hw hm support.toResolvable]
  congr 1
  change doubledSelbergFilteredNormalizationMain H
      (separatedFirstSupport H RD w)
      (fullySeparatedCompanionSupport H 2 (primorial w) m)
      (fun d e => separatedFirstCoefficient H RD w F d *
        fullySeparatedCompanionCoefficient H 2 (primorial w) m
          (fun _ => (1 : ℝ)) e)
      (primorial w) m (primorial w * q) T = _
  rw [doubledSelbergFilteredNormalizationMain_tensor_eq_totientExpanded
    hw hm support
      (separatedFirstCoefficient H RD w F)
      (fullySeparatedCompanionCoefficient H 2 (primorial w) m
        (fun _ => (1 : ℝ)))]
  rw [fullySeparatedCompanionTotientExpanded_two_constant_one]
  ring

/-- A logarithmic-envelope bound for the degenerate companion's entire
aggregate CRT endpoint error. -/
noncomputable def trivialCompanionErrorEnvelope
    (H : Finset ℕ) (alpha B : ℝ) (N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) *
    (((BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) *
      (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
        Fintype.card H) ^ 2 *
    ((BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) * B *
      (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
        (2 * Fintype.card H)) ^ 2)

theorem allowedPreSieveResidues_card_le (W m : ℕ) :
    (allowedPreSieveResidues W m).card ≤ W := by
  unfold allowedPreSieveResidues
  calc
    (Finset.filter (fun v => (preSievePolynomial m v).Coprime W)
      (Finset.Ico 1 W)).card ≤ (Finset.Ico 1 W).card :=
        Finset.card_filter_le _ _
    _ ≤ W := by simp

theorem trivialCompanionNormalizationError_abs_le_envelope
    {H : Finset ℕ} {alpha B : ℝ} {N m q T : ℕ}
    {F : (H → ℝ) → ℝ}
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hm : 0 < m) (hq : q.Prime)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hRq : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q) :
    |doubledSelbergFilteredNormalizationError H
      (separatedFirstSupport H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
      (fullySeparatedCompanionSupport H 2
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
      (fullySeparatedDoubledCoefficient H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
        F (fun _ => (1 : ℝ)))
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) m q T| ≤
        trivialCompanionErrorEnvelope H alpha B N := by
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let DS := separatedFirstSupport H R D
  let ES := fullySeparatedCompanionSupport H 2 W m
  let L : ℝ := (R : ℝ) * B *
    (1 + Real.log R) ^ (2 * Fintype.card H)
  let lambda := fullySeparatedDoubledCoefficient H R 2 D W m
    F (fun _ => (1 : ℝ))
  have hsupport : DoubledMaynardSupportConditions H DS ES R 2 W m q := by
    apply fullySeparatedSupportConditions hm hq
      (show W ∣ primorial D by rfl) hcover hRq hq.two_le hD
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hcoeff : ∀ d ∈ DS, ∀ e ∈ ES, |lambda d e| ≤ L := by
    intro d hd e he
    have he' : e = constantOneTuple H := by
      have hES : ES = {constantOneTuple H} :=
        fullySeparatedCompanionSupport_two_eq_singleton H W m
      rw [hES] at he
      exact Finset.mem_singleton.mp he
    subst e
    unfold lambda fullySeparatedDoubledCoefficient
    rw [fullySeparatedCompanionCoefficient_two_constant_one_at_one]
    simp only [mul_one]
    unfold separatedFirstCoefficient
    exact BoundedGaps.Maynard.abs_maynardCoefficient_le_log_envelope
      H R (primorial D) F d B hB hF hd
  have herr := doubledSelbergFilteredNormalizationError_abs_le
    H DS ES lambda W m q T hsupport.toResolvable
      (show 0 < W by exact primorial_pos D) L hL hcoeff
  have hDcard : ((DS.card : ℕ) : ℝ) ≤
      (R : ℝ) * (1 + Real.log R) ^ Fintype.card H := by
    exact Erdos6.Maynard.tupleMaynardSupport_card_le_log H alpha N
  have hDcardSq := pow_le_pow_left₀ (Nat.cast_nonneg DS.card) hDcard 2
  have hEcard : ES.card = 1 := by
    rw [show ES = {constantOneTuple H} by
      exact fullySeparatedCompanionSupport_two_eq_singleton H W m]
    simp
  have hallowedNat := allowedPreSieveResidues_card_le W m
  have hallowed : ((allowedPreSieveResidues W m).card : ℝ) ≤ W := by
    exact_mod_cast hallowedNat
  calc
    _ ≤ ((DS.card : ℕ) : ℝ) ^ 2 * ((ES.card : ℕ) : ℝ) ^ 2 *
        (L ^ 2 * (allowedPreSieveResidues W m).card) := herr
    _ = ((DS.card : ℕ) : ℝ) ^ 2 * (L ^ 2 *
        (allowedPreSieveResidues W m).card) := by rw [hEcard]; norm_num
    _ ≤ (((R : ℝ) * (1 + Real.log R) ^ Fintype.card H) ^ 2) *
        (L ^ 2 * (W : ℝ)) := by
      gcongr
    _ = trivialCompanionErrorEnvelope H alpha B N := by
      unfold trivialCompanionErrorEnvelope L R W
      ring

/-- The same endpoint envelope applies when the auxiliary shift multiplier
is `W*q`; the bound is uniform in that multiplier once CRT resolvability has
been established. -/
theorem scaledTrivialCompanionNormalizationError_abs_le_envelope
    {H : Finset ℕ} {alpha B : ℝ} {N m q T : ℕ}
    {F : (H → ℝ) → ℝ}
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hm : 0 < m) (hq : q.Prime)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hRq : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q) :
    |doubledSelbergFilteredNormalizationError H
      (separatedFirstSupport H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
      (fullySeparatedCompanionSupport H 2
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
      (fullySeparatedDoubledCoefficient H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
        F (fun _ => (1 : ℝ)))
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
        (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) T| ≤
        trivialCompanionErrorEnvelope H alpha B N := by
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let DS := separatedFirstSupport H R D
  let ES := fullySeparatedCompanionSupport H 2 W m
  let L : ℝ := (R : ℝ) * B *
    (1 + Real.log R) ^ (2 * Fintype.card H)
  let lambda := fullySeparatedDoubledCoefficient H R 2 D W m
    F (fun _ => (1 : ℝ))
  have hsupport : DoubledMaynardSupportConditions H DS ES R 2 W m
      (W * q) := by
    simpa [DS, ES, W, D,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      (trivialCompanionScaledSupportConditions
        (H := H) (RD := R) (w := D) (m := m) (q := q)
        hD hm hq hcover hRq)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hcoeff : ∀ d ∈ DS, ∀ e ∈ ES, |lambda d e| ≤ L := by
    intro d hd e he
    have he' : e = constantOneTuple H := by
      have hES : ES = {constantOneTuple H} :=
        fullySeparatedCompanionSupport_two_eq_singleton H W m
      rw [hES] at he
      exact Finset.mem_singleton.mp he
    subst e
    unfold lambda fullySeparatedDoubledCoefficient
    rw [fullySeparatedCompanionCoefficient_two_constant_one_at_one]
    simp only [mul_one]
    unfold separatedFirstCoefficient
    exact BoundedGaps.Maynard.abs_maynardCoefficient_le_log_envelope
      H R (primorial D) F d B hB hF hd
  have herr := doubledSelbergFilteredNormalizationError_abs_le
    H DS ES lambda W m (W * q) T hsupport.toResolvable
      (show 0 < W by exact primorial_pos D) L hL hcoeff
  have hDcard : ((DS.card : ℕ) : ℝ) ≤
      (R : ℝ) * (1 + Real.log R) ^ Fintype.card H := by
    exact Erdos6.Maynard.tupleMaynardSupport_card_le_log H alpha N
  have hEcard : ES.card = 1 := by
    rw [show ES = {constantOneTuple H} by
      exact fullySeparatedCompanionSupport_two_eq_singleton H W m]
    simp
  have hallowedNat := allowedPreSieveResidues_card_le W m
  have hallowed : ((allowedPreSieveResidues W m).card : ℝ) ≤ W := by
    exact_mod_cast hallowedNat
  calc
    _ ≤ ((DS.card : ℕ) : ℝ) ^ 2 * ((ES.card : ℕ) : ℝ) ^ 2 *
        (L ^ 2 * (allowedPreSieveResidues W m).card) := herr
    _ = ((DS.card : ℕ) : ℝ) ^ 2 * (L ^ 2 *
        (allowedPreSieveResidues W m).card) := by rw [hEcard]; norm_num
    _ ≤ (((R : ℝ) * (1 + Real.log R) ^ Fintype.card H) ^ 2) *
        (L ^ 2 * (W : ℝ)) := by
      gcongr
    _ = trivialCompanionErrorEnvelope H alpha B N := by
      unfold trivialCompanionErrorEnvelope L R W
      ring

/-- The explicit aggregate endpoint envelope is negligible on the ordinary
Maynard sieve scale.  The extra primorial factor is still subpolynomial;
the proof keeps it as one additional `eps` in the exponent audit. -/
theorem tendsto_trivialCompanionErrorEnvelope_div_scale_zero
    (H : Finset ℕ) {alpha B : ℝ} (halpha : 0 < alpha)
    (hB : 0 ≤ B) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ =>
      trivialCompanionErrorEnvelope H alpha B N /
        Erdos6.Maynard.tupleMaynardScale H alpha N)
      atTop (nhds 0) := by
  let k : ℕ := Fintype.card H
  let eps : ℝ := (1 - 4 * alpha) / (2 * (k + 2 : ℕ))
  have hkpos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    exact div_pos (by linarith) (by positivity)
  have hexp : 4 * alpha + (k + 2 : ℕ) * eps < 1 := by
    dsimp [eps]
    field_simp
    nlinarith
  have hscale := Erdos6.Maynard.tupleMaynardScale_ge_rpow H halpha heps
  have hscalePos := Erdos6.Maynard.eventually_tupleMaynardScale_pos
    (H := H) halpha
  have hW := BoundedGaps.Maynard.engelsmaMaynardModulus_le_rpow heps
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop 1)
  have hR : ∀ᶠ N : ℕ in atTop,
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) ≤
        Real.rpow (N : ℝ) alpha := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    unfold BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    have hfloor :
        ((⌊Real.rpow ((N - 1 : ℕ) : ℝ) alpha⌋₊ : ℕ) : ℝ) ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) alpha :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)
    exact hfloor.trans (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.sub_le N 1) halpha.le)
  have hlogR :=
    BoundedGaps.Maynard.eventually_one_add_log_engelsmaMaynardRadius_le halpha
  let logPower : ℕ := 6 * k
  let C : ℝ := B ^ 2 * (1 + alpha) ^ (6 * k)
  have hLnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ 1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    by_cases hz : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N = 0
    · simp [hz]
    · have hge : (1 : ℝ) ≤
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      linarith [Real.log_nonneg hge]
  have hCLogNonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + alpha) * Real.log (N : ℝ) := by
    filter_upwards [hlogN] with N hN
    positivity
  have hEbound : ∀ᶠ N : ℕ in atTop,
      trivialCompanionErrorEnvelope H alpha B N ≤
        C * Real.rpow (N : ℝ) eps *
          (Real.rpow (N : ℝ) alpha) ^ 4 *
            Real.log (N : ℝ) ^ logPower := by
    filter_upwards [hW, hR, hlogR, hLnonneg, hCLogNonneg] with
        N hWN hRN hlogRN hL hCL
    let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
    have hp1 :
        (1 + Real.log R) ^ k ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ k :=
      pow_le_pow_left₀ hL hlogRN k
    have hb1 :
        (R : ℝ) * (1 + Real.log R) ^ k ≤
          Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k :=
      mul_le_mul hRN hp1 (pow_nonneg hL _)
        (Real.rpow_nonneg (by positivity) _)
    have hp2 :
        (1 + Real.log R) ^ (2 * k) ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) :=
      pow_le_pow_left₀ hL hlogRN (2 * k)
    have hb2 :
        (R : ℝ) * B * (1 + Real.log R) ^ (2 * k) ≤
          Real.rpow (N : ℝ) alpha * B *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) := by
      have hRB : (R : ℝ) * B ≤
          Real.rpow (N : ℝ) alpha * B :=
        mul_le_mul_of_nonneg_right hRN hB
      exact mul_le_mul hRB hp2 (pow_nonneg hL _)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) hB)
    have hsq1 := pow_le_pow_left₀ (by positivity) hb1 2
    have hsq2 := pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (by positivity) hB) (pow_nonneg hL _)) hb2 2
    unfold trivialCompanionErrorEnvelope
    change (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) *
        (((R : ℝ) * (1 + Real.log R) ^ k) ^ 2 *
          (((R : ℝ) * B * (1 + Real.log R) ^ (2 * k)) ^ 2)) ≤ _
    calc
      _ ≤ Real.rpow (N : ℝ) eps *
          ((Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k) ^ 2 *
          (Real.rpow (N : ℝ) alpha * B *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k)) ^ 2) := by
        apply mul_le_mul hWN
        · exact mul_le_mul hsq1 hsq2 (sq_nonneg _) (sq_nonneg _)
        · positivity
        · exact Real.rpow_nonneg (by positivity) _
      _ = C * Real.rpow (N : ℝ) eps *
          (Real.rpow (N : ℝ) alpha) ^ 4 *
            Real.log (N : ℝ) ^ logPower := by
        dsimp [C, logPower]
        simp_rw [mul_pow]
        ring
  have hgeneric : Tendsto
      (fun N : ℕ =>
        C * Real.rpow (N : ℝ)
            (4 * alpha + (k + 2 : ℕ) * eps) *
          Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_div_assoc] using
      (BoundedGaps.Maynard.tendsto_natCast_rpow_mul_log_rpow_div
        (a := 4 * alpha + (k + 2 : ℕ) * eps)
        (b := (logPower : ℝ)) hexp).const_mul C
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hgeneric
  filter_upwards [hEbound, hscale, hscalePos, hlogN,
    eventually_ge_atTop 1] with N hEN hSN hSpos hLN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlowerpos : 0 < Real.rpow (N : ℝ)
      (1 - (k + 1 : ℕ) * eps) := Real.rpow_pos_of_pos hNpos _
  have hboundnonneg : 0 ≤
      C * Real.rpow (N : ℝ) eps *
        (Real.rpow (N : ℝ) alpha) ^ 4 *
          Real.log (N : ℝ) ^ logPower := by
    dsimp [C]
    positivity
  have hpowE : Real.rpow (N : ℝ) eps *
        (Real.rpow (N : ℝ) alpha) ^ 4 =
      Real.rpow (N : ℝ) (eps + 4 * alpha) := by
    rw [show (Real.rpow (N : ℝ) alpha) ^ 4 =
      Real.rpow (N : ℝ) (4 * alpha) by
        calc
          _ = Real.rpow (Real.rpow (N : ℝ) alpha) (4 : ℝ) :=
            (Real.rpow_natCast _ 4).symm
          _ = Real.rpow (N : ℝ) (alpha * 4) :=
            (Real.rpow_mul hNpos.le alpha 4).symm
          _ = _ := by
            congr 1
            ring]
    exact (Real.rpow_add hNpos eps (4 * alpha)).symm
  have hlogpow : Real.log (N : ℝ) ^ logPower =
      Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) :=
    (Real.rpow_natCast _ logPower).symm
  calc
    _ ≤ (C * Real.rpow (N : ℝ) eps *
        (Real.rpow (N : ℝ) alpha) ^ 4 *
          Real.log (N : ℝ) ^ logPower) /
            Erdos6.Maynard.tupleMaynardScale H alpha N := by
      rw [abs_div, abs_of_nonneg (by
        unfold trivialCompanionErrorEnvelope
        positivity), abs_of_pos hSpos]
      exact div_le_div_of_nonneg_right hEN hSpos.le
    _ ≤ (C * Real.rpow (N : ℝ) eps *
        (Real.rpow (N : ℝ) alpha) ^ 4 *
          Real.log (N : ℝ) ^ logPower) /
            Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps) :=
      div_le_div_of_nonneg_left hboundnonneg hlowerpos hSN
    _ = C * Real.rpow (N : ℝ)
          (4 * alpha + (k + 2 : ℕ) * eps) *
        Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) / (N : ℝ) := by
      rw [mul_assoc C (Real.rpow (N : ℝ) eps)
          ((Real.rpow (N : ℝ) alpha) ^ 4),
        hpowE, hlogpow, div_eq_mul_inv,
        show (Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps))⁻¹ =
          Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps)) by
            exact (Real.rpow_neg hNpos.le _).symm]
      have hcombine := Real.rpow_add hNpos
        (eps + 4 * alpha) (-(1 - (k + 1 : ℕ) * eps))
      have hsplit := Real.rpow_add hNpos
        (4 * alpha + (k + 2 : ℕ) * eps) (-1)
      have hminusone : Real.rpow (N : ℝ) (-1) = (N : ℝ)⁻¹ := by
        calc
          Real.rpow (N : ℝ) (-1) = (Real.rpow (N : ℝ) 1)⁻¹ :=
            Real.rpow_neg hNpos.le 1
          _ = (N : ℝ)⁻¹ := congrArg Inv.inv (Real.rpow_one _)
      calc
        C * Real.rpow (N : ℝ) (eps + 4 * alpha) *
              Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) *
              Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps)) =
            C * Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) *
              (Real.rpow (N : ℝ) (eps + 4 * alpha) *
                Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps))) := by
          ring
        _ = C * Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) *
              Real.rpow (N : ℝ)
                (eps + 4 * alpha + -(1 - (k + 1 : ℕ) * eps)) := by
          exact congrArg
            (fun t : ℝ => C *
              Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) * t)
            hcombine.symm
        _ = C * Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) *
              Real.rpow (N : ℝ)
                ((4 * alpha + (k + 2 : ℕ) * eps) + -1) := by
          congr 2
          push_cast
          ring
        _ = C * Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) *
              (Real.rpow (N : ℝ)
                (4 * alpha + (k + 2 : ℕ) * eps) *
                Real.rpow (N : ℝ) (-1)) := by
          exact congrArg
            (fun t : ℝ => C *
              Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) * t)
            hsplit
        _ = C * Real.rpow (N : ℝ)
              (4 * alpha + (k + 2 : ℕ) * eps) *
            Real.rpow (Real.log (N : ℝ)) (logPower : ℝ) /
              (N : ℝ) := by
          rw [hminusone]
          ring

/-! ### Positivity of the concrete finite normalization -/

/-- The exact finite mass used to normalize the degenerate-companion Selberg
weights at scale `N`. -/
noncomputable def trivialCompanionNormalizationMass
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N,
    if largeGapPreSieved
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) (m N) n then
      doubledSelbergWeight (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
        (fullySeparatedCompanionSupport (primorialShifts K) 2
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N))
        (fullySeparatedDoubledCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
          (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
        (m N) (q N) n
    else 0

/-- The literal aggregate CRT endpoint error in the preceding mass. -/
noncomputable def trivialCompanionNormalizationError
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ) : ℝ :=
  doubledSelbergFilteredNormalizationError (primorialShifts K)
    (separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (fullySeparatedCompanionSupport (primorialShifts K) 2
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N))
    (fullySeparatedDoubledCoefficient (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
      (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
    (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N) (q N) N

/-- After division by the ordinary Maynard scale, the doubled pre-sieve main
term is exactly the first compatible quadratic multiplied by the integral
number of allowed residue classes. -/
theorem normalized_trivialCompanion_main_eq_card_mul
    {K N m : ℕ} {A alpha : ℝ}
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hm : 0 < m)
    (hscale : Erdos6.Maynard.tupleMaynardScale
      (primorialShifts K) alpha N ≠ 0) :
    ((N : ℝ) * preSieveDensity
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m *
      BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (primorialShiftsCandidate K A))) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N =
      ((allowedPreSieveResidues
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) m).card : ℝ) *
        normalizedFirstCompatibleQuadratic K A alpha N := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let Q := BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D)
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D
          (primorialShiftsCandidate K A))
  have hWpos : (0 : ℝ) < W := by
    exact_mod_cast primorial_pos D
  have hdensity :
      ((allowedPreSieveResidues W m).card : ℝ) / W =
        preSieveDensity D m := by
    simpa [W, D, BoundedGaps.Maynard.engelsmaMaynardModulus] using
      (card_allowedPreSieveResidues_div_primorial hD hm)
  rw [← hdensity]
  unfold normalizedFirstCompatibleQuadratic
  dsimp [D, W, Q]
  field_simp

/-- For arbitrary positive even companion cofactors and prime auxiliary
moduli above the divisor radius, the concrete Selberg mass is eventually
strictly positive.  Thus its normalization into a probability measure is
legitimate, with no unproved nonvanishing assumption. -/
theorem eventually_trivialCompanionNormalizationMass_pos
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (m q : ℕ → ℕ) (hm : ∀ N, 0 < m N) (hmEven : ∀ N, Even (m N))
    (hq : ∀ N, (q N).Prime)
    (hRq : ∀ N, BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q N) :
    ∀ᶠ N : ℕ in atTop,
      0 < trivialCompanionNormalizationMass K A alpha m q N := by
  let I := BoundedGaps.Maynard.maynardI K
    (VariableMaynard.candidate K A)
  have hI : 0 < I := VariableMaynard.maynardI_candidate_pos hK hA
  dsimp [I] at hI
  have hfirst : ∀ᶠ N : ℕ in atTop,
      I / 2 < normalizedFirstCompatibleQuadratic K A alpha N := by
    exact (tendsto_order.1
      (tendsto_normalizedFirstCompatibleQuadratic hK hA halpha)).1 (I / 2)
      (by linarith)
  have herrlim := tendsto_trivialCompanionErrorEnvelope_div_scale_zero
    (primorialShifts K) halpha (by norm_num : (0 : ℝ) ≤ 1) halphaQuarter
  have herrsmall : ∀ᶠ N : ℕ in atTop,
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N /
          Erdos6.Maynard.tupleMaynardScale
            (primorialShifts K) alpha N < I / 4 :=
    (tendsto_order.1 herrlim).2 _ (by linarith)
  obtain ⟨N₀, hN₀⟩ :=
    BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  filter_upwards [hfirst, herrsmall,
    Erdos6.Maynard.eventually_tupleMaynardScale_pos
      (H := primorialShifts K) halpha,
    Erdos6.Maynard.eventually_tupleMaynard_coverage (primorialShifts K),
    eventually_ge_atTop (N₀ + 1)] with N hfirstN herrsmallN hscale hcover hN
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let Q := BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D)
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D
          (primorialShiftsCandidate K A))
  let E := trivialCompanionNormalizationError K A alpha m q N
  have hD : 2 ≤ D := hN₀ (N - 1) (by omega)
  have hmass : trivialCompanionNormalizationMass K A alpha m q N =
      (N : ℝ) * preSieveDensity D (m N) * Q + E := by
    unfold trivialCompanionNormalizationMass
    dsimp [E, trivialCompanionNormalizationError, D, W, Q]
    simpa [BoundedGaps.Maynard.engelsmaMaynardModulus] using
      (preSievedTrivialCompanionWeightSum_eq_main_add_error
        (H := primorialShifts K)
        (RD := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (w := D) (Y := D) (m := m N) (q := q N) (T := N)
        hD (hm N) (hq N) (by rfl) hcover (hRq N)
        (hq N).two_le hD (primorialShiftsCandidate K A))
  have hEbound : |E| ≤
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N := by
    dsimp [E, trivialCompanionNormalizationError, D, W]
    exact trivialCompanionNormalizationError_abs_le_envelope
      (H := primorialShifts K) (alpha := alpha) (B := 1)
      (N := N) (m := m N) (q := q N) (T := N)
      (F := primorialShiftsCandidate K A)
      (by norm_num) (primorialShiftsCandidate_abs_le_one hA)
      (hm N) (hq N) hD hcover (hRq N)
  have hcardpos : 0 <
      ((allowedPreSieveResidues W (m N)).card : ℝ) := by
    have hdens : 0 < preSieveDensity D (m N) :=
      preSieveDensity_pos_of_even (hmEven N)
    have hquot : ((allowedPreSieveResidues W (m N)).card : ℝ) / W =
        preSieveDensity D (m N) := by
      simpa [W, D, BoundedGaps.Maynard.engelsmaMaynardModulus] using
        (card_allowedPreSieveResidues_div_primorial hD (hm N))
    have hWpos : (0 : ℝ) < W := by
      exact_mod_cast primorial_pos D
    have : 0 < ((allowedPreSieveResidues W (m N)).card : ℝ) / W := by
      rw [hquot]
      exact hdens
    rcases (div_pos_iff.mp this) with h | h
    · exact h.1
    · exact (not_lt_of_ge hWpos.le h.2).elim
  have hcardone : (1 : ℝ) ≤
      ((allowedPreSieveResidues W (m N)).card : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.ne_of_gt (Nat.cast_pos.mp hcardpos)))
  have hmainnorm :
      ((N : ℝ) * preSieveDensity D (m N) * Q) /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N =
        ((allowedPreSieveResidues W (m N)).card : ℝ) *
          normalizedFirstCompatibleQuadratic K A alpha N := by
    simpa [D, W, Q] using
      (normalized_trivialCompanion_main_eq_card_mul
        (K := K) (N := N) (m := m N) (A := A) (alpha := alpha)
        hD (hm N) hscale.ne')
  have hfirstpos : 0 < normalizedFirstCompatibleQuadratic K A alpha N := by
    linarith
  have hmainlower : I / 2 <
      ((N : ℝ) * preSieveDensity D (m N) * Q) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
    rw [hmainnorm]
    exact hfirstN.trans_le
      (le_mul_of_one_le_left hfirstpos.le hcardone)
  have hEnorm : |E| /
      Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N < I / 4 :=
    (div_le_div_of_nonneg_right hEbound hscale.le).trans_lt herrsmallN
  have hposnorm : 0 <
      ((N : ℝ) * preSieveDensity D (m N) * Q + E) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
    rw [add_div]
    have hElower : -(I / 4) < E /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
      have habs : |E /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N| <
          I / 4 := by
        rw [abs_div, abs_of_pos hscale]
        exact hEnorm
      exact (abs_lt.mp habs).1
    linarith
  rw [hmass]
  rcases (div_pos_iff.mp hposnorm) with h | h
  · exact h.1
  · exact (not_lt_of_ge hscale.le h.2).elim

/-! ### The scaled normalization used by the residue measures -/

/-- Total raw residue mass when the actual residue modulus is `q` and all
Selberg shifts are multiplied by `W*q`. -/
noncomputable def scaledTrivialCompanionNormalizationMass
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N,
    if largeGapPreSieved
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) (m N) n then
      doubledSelbergWeight (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
        (fullySeparatedCompanionSupport (primorialShifts K) 2
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N))
        (fullySeparatedDoubledCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
          (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
        (m N) (BoundedGaps.Maynard.engelsmaMaynardModulus N * q N) n
    else 0

noncomputable def scaledTrivialCompanionNormalizationError
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ) : ℝ :=
  doubledSelbergFilteredNormalizationError (primorialShifts K)
    (separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (fullySeparatedCompanionSupport (primorialShifts K) 2
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N))
    (fullySeparatedDoubledCoefficient (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
      (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
    (BoundedGaps.Maynard.engelsmaMaynardModulus N) (m N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N * q N) N

/-- Positivity of the exact scaled mass.  The proof is identical at main-term
level to the unscaled case and uses the uniform scaled CRT-error estimate. -/
theorem eventually_scaledTrivialCompanionNormalizationMass_pos
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (m q : ℕ → ℕ) (hm : ∀ N, 0 < m N) (hmEven : ∀ N, Even (m N))
    (hq : ∀ N, (q N).Prime)
    (hRq : ∀ N, BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q N) :
    ∀ᶠ N : ℕ in atTop,
      0 < scaledTrivialCompanionNormalizationMass K A alpha m q N := by
  let I := BoundedGaps.Maynard.maynardI K
    (VariableMaynard.candidate K A)
  have hI : 0 < I := VariableMaynard.maynardI_candidate_pos hK hA
  dsimp [I] at hI
  have hfirst : ∀ᶠ N : ℕ in atTop,
      I / 2 < normalizedFirstCompatibleQuadratic K A alpha N := by
    exact (tendsto_order.1
      (tendsto_normalizedFirstCompatibleQuadratic hK hA halpha)).1 (I / 2)
      (by linarith)
  have herrlim := tendsto_trivialCompanionErrorEnvelope_div_scale_zero
    (primorialShifts K) halpha (by norm_num : (0 : ℝ) ≤ 1) halphaQuarter
  have herrsmall : ∀ᶠ N : ℕ in atTop,
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N /
          Erdos6.Maynard.tupleMaynardScale
            (primorialShifts K) alpha N < I / 4 :=
    (tendsto_order.1 herrlim).2 _ (by linarith)
  obtain ⟨N₀, hN₀⟩ :=
    BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  filter_upwards [hfirst, herrsmall,
    Erdos6.Maynard.eventually_tupleMaynardScale_pos
      (H := primorialShifts K) halpha,
    Erdos6.Maynard.eventually_tupleMaynard_coverage (primorialShifts K),
    eventually_ge_atTop (N₀ + 1)] with N hfirstN herrsmallN hscale hcover hN
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let Q := BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D)
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D
          (primorialShiftsCandidate K A))
  let E := scaledTrivialCompanionNormalizationError K A alpha m q N
  have hD : 2 ≤ D := hN₀ (N - 1) (by omega)
  have hmass : scaledTrivialCompanionNormalizationMass K A alpha m q N =
      (N : ℝ) * preSieveDensity D (m N) * Q + E := by
    unfold scaledTrivialCompanionNormalizationMass
    dsimp [E, scaledTrivialCompanionNormalizationError, D, W, Q]
    simpa [BoundedGaps.Maynard.engelsmaMaynardModulus] using
      (preSievedScaledTrivialCompanionWeightSum_eq_main_add_error
        (H := primorialShifts K)
        (RD := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (w := D) (m := m N) (q := q N) (T := N)
        hD (hm N) (hq N) hcover (hRq N)
        (primorialShiftsCandidate K A))
  have hEbound : |E| ≤
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N := by
    dsimp [E, scaledTrivialCompanionNormalizationError, D, W]
    exact scaledTrivialCompanionNormalizationError_abs_le_envelope
      (H := primorialShifts K) (alpha := alpha) (B := 1)
      (N := N) (m := m N) (q := q N) (T := N)
      (F := primorialShiftsCandidate K A)
      (by norm_num) (primorialShiftsCandidate_abs_le_one hA)
      (hm N) (hq N) hD hcover (hRq N)
  have hcardpos : 0 <
      ((allowedPreSieveResidues W (m N)).card : ℝ) := by
    have hdens : 0 < preSieveDensity D (m N) :=
      preSieveDensity_pos_of_even (hmEven N)
    have hquot : ((allowedPreSieveResidues W (m N)).card : ℝ) / W =
        preSieveDensity D (m N) := by
      simpa [W, D, BoundedGaps.Maynard.engelsmaMaynardModulus] using
        (card_allowedPreSieveResidues_div_primorial hD (hm N))
    have hWpos : (0 : ℝ) < W := by
      exact_mod_cast primorial_pos D
    have : 0 < ((allowedPreSieveResidues W (m N)).card : ℝ) / W := by
      rw [hquot]
      exact hdens
    rcases (div_pos_iff.mp this) with h | h
    · exact h.1
    · exact (not_lt_of_ge hWpos.le h.2).elim
  have hcardone : (1 : ℝ) ≤
      ((allowedPreSieveResidues W (m N)).card : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.ne_of_gt (Nat.cast_pos.mp hcardpos)))
  have hmainnorm :
      ((N : ℝ) * preSieveDensity D (m N) * Q) /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N =
        ((allowedPreSieveResidues W (m N)).card : ℝ) *
          normalizedFirstCompatibleQuadratic K A alpha N := by
    simpa [D, W, Q] using
      (normalized_trivialCompanion_main_eq_card_mul
        (K := K) (N := N) (m := m N) (A := A) (alpha := alpha)
        hD (hm N) hscale.ne')
  have hfirstpos : 0 < normalizedFirstCompatibleQuadratic K A alpha N := by
    linarith
  have hmainlower : I / 2 <
      ((N : ℝ) * preSieveDensity D (m N) * Q) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
    rw [hmainnorm]
    exact hfirstN.trans_le
      (le_mul_of_one_le_left hfirstpos.le hcardone)
  have hEnorm : |E| /
      Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N < I / 4 :=
    (div_le_div_of_nonneg_right hEbound hscale.le).trans_lt herrsmallN
  have hposnorm : 0 <
      ((N : ℝ) * preSieveDensity D (m N) * Q + E) /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
    rw [add_div]
    have hElower : -(I / 4) < E /
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
      have habs : |E /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N| <
          I / 4 := by
        rw [abs_div, abs_of_pos hscale]
        exact hEnorm
      exact (abs_lt.mp habs).1
    linarith
  rw [hmass]
  rcases (div_pos_iff.mp hposnorm) with h | h
  · exact h.1
  · exact (not_lt_of_ge hscale.le h.2).elim

/-! ### Raw probability mass on residue classes -/

/-- The portion of the scaled Selberg mass lying in one residue class modulo
the actual prime `q`. -/
noncomputable def scaledTrivialResidueRawWeight
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (a : Fin q) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N,
    if largeGapPreSieved
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m n ∧
        n % q = a.1 then
      doubledSelbergWeight (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
        (fullySeparatedCompanionSupport (primorialShifts K) 2
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
        (fullySeparatedDoubledCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
          (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
        m (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) n
    else 0

theorem scaledTrivialResidueRawWeight_nonneg
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (a : Fin q) :
    0 ≤ scaledTrivialResidueRawWeight K A alpha m N q a := by
  unfold scaledTrivialResidueRawWeight
  exact Finset.sum_nonneg fun n _ => by
    split_ifs
    · exact doubledSelbergWeight_nonneg _ _ _ _ _ _ _
    · exact le_rfl

/-- Residue classes modulo a positive modulus partition the raw mass exactly. -/
theorem sum_scaledTrivialResidueRawWeight
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (hq : 0 < q) :
    (∑ a : Fin q, scaledTrivialResidueRawWeight K A alpha m N q a) =
      ∑ n ∈ Finset.Icc 0 N,
        if largeGapPreSieved
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m n then
          doubledSelbergWeight (primorialShifts K)
            (separatedFirstSupport (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
            (fullySeparatedCompanionSupport (primorialShifts K) 2
              (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
            (fullySeparatedDoubledCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
              (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
            m (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) n
        else 0 := by
  classical
  unfold scaledTrivialResidueRawWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpre : largeGapPreSieved
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m n
  · simp only [hpre, true_and, if_true]
    let a : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
    rw [show (∑ x : Fin q,
        if n % q = x.1 then
          doubledSelbergWeight (primorialShifts K)
            (separatedFirstSupport (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
            (fullySeparatedCompanionSupport (primorialShifts K) 2
              (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
            (fullySeparatedDoubledCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
              (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
            m (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) n
        else 0) =
      doubledSelbergWeight (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
        (fullySeparatedCompanionSupport (primorialShifts K) 2
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
        (fullySeparatedDoubledCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
          (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
        m (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) n by
      classical
      rw [Finset.sum_eq_single a]
      · simp [a]
      · intro b hb hba
        have hne : n % q ≠ b.1 := by
          intro heq
          apply hba
          exact Fin.ext heq.symm
        simp [hne]
      · simp]
  · simp [hpre]

theorem sum_scaledTrivialResidueRawWeight_eq_mass
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ) (hq : 0 < q N) :
    (∑ a : Fin (q N),
      scaledTrivialResidueRawWeight K A alpha (m N) N (q N) a) =
      scaledTrivialCompanionNormalizationMass K A alpha m q N := by
  simpa [scaledTrivialCompanionNormalizationMass] using
    (sum_scaledTrivialResidueRawWeight K A alpha (m N) N (q N) hq)

/-- The actual probability assigned to a residue class modulo `q`. -/
noncomputable def scaledTrivialResidueMass
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (a : Fin q) : ℝ :=
  normalizeFiniteWeight
    (scaledTrivialResidueRawWeight K A alpha m N q) a

theorem scaledTrivialResidueMass_nonneg
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (a : Fin q) :
    0 ≤ scaledTrivialResidueMass K A alpha m N q a := by
  exact normalizeFiniteWeight_nonneg _
    (scaledTrivialResidueRawWeight_nonneg K A alpha m N q) a

/-- Once the exact Selberg denominator is positive, the scaled residue masses
sum to one. -/
theorem sum_scaledTrivialResidueMass_eq_one
    (K : ℕ) (A alpha : ℝ) (m q : ℕ → ℕ) (N : ℕ)
    (hq : 0 < q N)
    (hmass : 0 <
      scaledTrivialCompanionNormalizationMass K A alpha m q N) :
    (∑ a : Fin (q N),
      scaledTrivialResidueMass K A alpha (m N) N (q N) a) = 1 := by
  apply sum_normalizeFiniteWeight_eq_one
  rw [sum_scaledTrivialResidueRawWeight_eq_mass K A alpha m q N hq]
  exact hmass

/-- The point weight occurring in the scaled residue mass. -/
noncomputable def scaledTrivialPointWeight
    (K : ℕ) (A alpha : ℝ) (m N q n : ℕ) : ℝ :=
  doubledSelbergWeight (primorialShifts K)
    (separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (fullySeparatedCompanionSupport (primorialShifts K) 2
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) m)
    (fullySeparatedDoubledCoefficient (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 2
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) m
      (primorialShiftsCandidate K A) (fun _ => (1 : ℝ)))
    m (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) n

theorem scaledTrivialPointWeight_nonneg
    (K : ℕ) (A alpha : ℝ) (m N q n : ℕ) :
    0 ≤ scaledTrivialPointWeight K A alpha m N q n :=
  doubledSelbergWeight_nonneg _ _ _ _ _ _ _

/-- Divisibility by the first-family forms with auxiliary shift multiplier
`W*q`. -/
def scaledFirstDivisorCondition
    (K : ℕ) (N q n : ℕ) (d : ↑(primorialShifts K) → ℕ) : Prop :=
  ∀ h : ↑(primorialShifts K),
    d h ∣ n + h.1 *
      (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)

/-- The ordinary first-family divisor sum left after the radius-two companion
support collapses to the all-one tuple. -/
noncomputable def scaledFirstInner
    (K : ℕ) (A alpha : ℝ) (N q n : ℕ) : ℝ :=
  ∑ d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
    if scaledFirstDivisorCondition K N q n d then
      separatedFirstCoefficient (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
        (primorialShiftsCandidate K A) d
    else 0

/-- With the degenerate companion, the doubled point weight is literally the
square of the ordinary first-family Selberg divisor sum. -/
theorem scaledTrivialPointWeight_eq_first_sq
    (K : ℕ) (A alpha : ℝ) (m N q n : ℕ) :
    scaledTrivialPointWeight K A alpha m N q n =
      scaledFirstInner K A alpha N q n ^ 2 := by
  classical
  unfold scaledTrivialPointWeight doubledSelbergWeight
  unfold doubledSelbergInner scaledFirstInner
  rw [fullySeparatedCompanionSupport_two_eq_singleton]
  simp only [Finset.sum_singleton]
  unfold fullySeparatedDoubledCoefficient largeGapDivisorCondition
  rw [fullySeparatedCompanionCoefficient_two_constant_one_at_one]
  simp [scaledFirstDivisorCondition, constantOneTuple]

/-- Expanding the remaining square gives the exact ordered divisor-pair
sum at one point. -/
theorem scaledFirstInner_sq_eq_pairSum
    (K : ℕ) (A alpha : ℝ) (N q n : ℕ) :
    scaledFirstInner K A alpha N q n ^ 2 =
      ∑ d ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
        ∑ e ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
          if scaledFirstDivisorCondition K N q n d ∧
              scaledFirstDivisorCondition K N q n e then
            separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) d *
              separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) e
          else 0 := by
  classical
  unfold scaledFirstInner
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp_all

/-- Number of auxiliary moduli in `Q` for which a pinned prime satisfies one
ordered pair of divisor-tuple conditions. -/
noncomputable def pinnedPairQCount
    (K N p : ℕ) (h : ↑(primorialShifts K)) (Q : Finset ℕ)
    (d e : ↑(primorialShifts K) → ℕ) : ℕ :=
  (Q.filter fun q =>
    scaledFirstDivisorCondition K N q
        (p - h.1 *
          (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) d ∧
      scaledFirstDivisorCondition K N q
        (p - h.1 *
          (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) e).card

/-- Summing all coordinate preimages over a finite family of auxiliary
moduli is exactly the corresponding divisor-pair count. -/
theorem sum_pinned_pointWeights_eq_pairCounts
    (K : ℕ) (A alpha : ℝ) (m N p : ℕ) (Q : Finset ℕ) :
    (∑ q ∈ Q, ∑ h : ↑(primorialShifts K),
      scaledTrivialPointWeight K A alpha m N q
        (p - h.1 *
          (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) =
      ∑ h : ↑(primorialShifts K),
        ∑ d ∈ separatedFirstSupport (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
          ∑ e ∈ separatedFirstSupport (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
            separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) d *
              separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) e *
              (pinnedPairQCount K N p h Q d e : ℝ) := by
  classical
  simp_rw [scaledTrivialPointWeight_eq_first_sq,
    scaledFirstInner_sq_eq_pairSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simpa [pinnedPairQCount] using
    (sum_indicator_eq_mul_card Q
      (fun q =>
        scaledFirstDivisorCondition K N q
            (p - h.1 *
              (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) d ∧
          scaledFirstDivisorCondition K N q
            (p - h.1 *
              (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) e)
      (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (primorialShiftsCandidate K A) d *
        separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (primorialShiftsCandidate K A) e))

/-- A supported coordinate dividing a prime at least as large as the tuple
cutoff must equal one. -/
theorem maynard_coordinate_eq_one_of_dvd_prime
    {H : Finset ℕ} {R W p : ℕ} {d : H → ℕ} (h : H)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hp : p.Prime) (hRp : R ≤ p) (hdp : d h ∣ p) :
    d h = 1 := by
  rcases hp.eq_one_or_self_of_dvd (d h) hdp with hone | hself
  · exact hone
  · exfalso
    have hcoord : d h ≤ BoundedGaps.Maynard.divisorTupleProduct H d :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.2.ne_zero)
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d h)
    rw [hself] at hcoord
    have hprodlt := hd.1
    omega

/-- A prime at least as large as the tuple cutoff stays coprime to the tuple
product; adjoining the pre-sieve modulus preserves this coprimality. -/
theorem prime_mul_modulus_coprime_tupleProduct
    {H : Finset ℕ} {R W q : ℕ} {d : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hq : q.Prime) (hRq : R ≤ q) :
    (W * q).Coprime (BoundedGaps.Maynard.divisorTupleProduct H d) := by
  apply Nat.Coprime.mul_left
  · exact hd.2.1.symm
  · apply hq.coprime_iff_not_dvd.mpr
    intro hdiv
    have hprodpos : 0 < BoundedGaps.Maynard.divisorTupleProduct H d :=
      Nat.pos_of_ne_zero hd.2.2.ne_zero
    have hqle : q ≤ BoundedGaps.Maynard.divisorTupleProduct H d :=
      Nat.le_of_dvd hprodpos hdiv
    have hprodlt := hd.1
    omega

/-- Any divisor pair contributing to the pinned prime sum is a compatible
pair and has both distinguished coordinates equal to one. -/
theorem pinnedPair_conditions_restricted
    {K N p q : ℕ} {alpha : ℝ}
    (h : ↑(primorialShifts K))
    {d e : ↑(primorialShifts K) → ℕ}
    (hdmem : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hemem : e ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hp : p.Prime)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hq : q.Prime)
    (hRq : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q)
    (hmargin : h.1 *
      (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hcond :
      scaledFirstDivisorCondition K N q
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) d ∧
        scaledFirstDivisorCondition K N q
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q)) e) :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime
        (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1 := by
  let H := primorialShifts K
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let n := p - h.1 * (W * q)
  have hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d := by
    simpa [separatedFirstSupport, H, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem
  have he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e := by
    simpa [separatedFirstSupport, H, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  have hnadd : n + h.1 * (W * q) = p := Nat.sub_add_cancel hmargin
  have hdprime : d h ∣ p := by
    rw [← hnadd]
    exact hcond.1 h
  have heprime : e h ∣ p := by
    rw [← hnadd]
    exact hcond.2 h
  have hdh : d h = 1 :=
    maynard_coordinate_eq_one_of_dvd_prime h hd hp hRp hdprime
  have heh : e h = 1 :=
    maynard_coordinate_eq_one_of_dvd_prime h he hp hRp heprime
  have hdq := prime_mul_modulus_coprime_tupleProduct hd hq hRq
  have heq := prime_mul_modulus_coprime_tupleProduct he hq hRq
  let one : H → ℕ := constantOneTuple H
  have hcondD : largeGapDivisorCondition H 1 (W * q) n d one := by
    intro j
    refine ⟨?_, by simp [one, constantOneTuple]⟩
    exact hcond.1 j
  have hcondE : largeGapDivisorCondition H 1 (W * q) n e one := by
    intro j
    refine ⟨?_, by simp [one, constantOneTuple]⟩
    exact hcond.2 j
  have hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e :=
    firstForms_crossCoordinateCoprime_of_conditions
      (H := H) (RD := R) (W := W) (m := 1) (q := W * q) (n := n)
      (d := d) (e := one) (d' := e) (e' := one)
      hd he hcover hdq heq hcondD hcondE
  exact ⟨hcross, hdh, heh⟩

theorem pinnedPairQCount_eq_zero_of_not_restricted
    {K N p : ℕ} {alpha : ℝ}
    (h : ↑(primorialShifts K)) (Q : Finset ℕ)
    {d e : ↑(primorialShifts K) → ℕ}
    (hdmem : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hemem : e ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hp : p.Prime)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQR : ∀ q ∈ Q,
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q)
    (hmargin : ∀ q ∈ Q,
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hnot : ¬(BoundedGaps.Maynard.IsCrossCoordinateCoprime
        (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1)) :
    pinnedPairQCount K N p h Q d e = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro q hqQ hcond
  exact hnot (pinnedPair_conditions_restricted h hdmem hemem hp hRp
    (hQprime q hqQ) (hQR q hqQ) (hmargin q hqQ) hcover hcond)

/-- The exact pinned prime sum after deleting all pairs which cannot
contribute. -/
noncomputable def pinnedRestrictedPairSum
    (K : ℕ) (A alpha : ℝ) (N p : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ h : ↑(primorialShifts K),
    ∑ d ∈ separatedFirstSupport (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
      ∑ e ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime
              (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1 then
          separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) d *
            separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) e *
            (pinnedPairQCount K N p h Q d e : ℝ)
        else 0

/-- Under the prime, cutoff, and margin hypotheses the full pinned expansion
is exactly its compatible coordinate-one restriction. -/
theorem sum_pinned_pointWeights_eq_restrictedPairSum
    (K : ℕ) (A alpha : ℝ) (m N p : ℕ) (Q : Finset ℕ)
    (hp : p.Prime)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQR : ∀ q ∈ Q,
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q)
    (hmargin : ∀ q ∈ Q, ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    (∑ q ∈ Q, ∑ h : ↑(primorialShifts K),
      scaledTrivialPointWeight K A alpha m N q
        (p - h.1 *
          (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) =
      pinnedRestrictedPairSum K A alpha N p Q := by
  rw [sum_pinned_pointWeights_eq_pairCounts]
  unfold pinnedRestrictedPairSum
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hr : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1
  · rw [if_pos hr]
  · rw [if_neg hr]
    have hz := pinnedPairQCount_eq_zero_of_not_restricted h Q hd he hp hRp
      hQprime hQR (fun q hq => hmargin q hq h) hcover hr
    rw [hz]
    norm_num

/-- Restricted totient kernel associated to one distinguished coordinate in
the pinned prime sum. -/
noncomputable def pinnedRestrictedArithmeticKernel
    (K : ℕ) (A alpha : ℝ) (N : ℕ)
    (h : ↑(primorialShifts K)) : ℝ :=
  BoundedGaps.Maynard.compatibleDivisorPairRestrictedTotientKernel
    (primorialShifts K)
    (separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (separatedFirstCoefficient (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (primorialShiftsCandidate K A)) h

theorem pinnedRestrictedArithmeticKernel_eq_tuple
    (K : ℕ) (A alpha : ℝ) (N : ℕ)
    (h : ↑(primorialShifts K)) :
    pinnedRestrictedArithmeticKernel K A alpha N h =
      Erdos6.Maynard.tupleRestrictedTotientKernel
        (primorialShifts K) alpha (primorialShiftsCandidate K A) N h := by
  rfl

/-- Raw-finset form of the restricted arithmetic kernel. -/
theorem pinnedRestrictedArithmeticKernel_eq_raw
    (K : ℕ) (A alpha : ℝ) (N : ℕ)
    (h : ↑(primorialShifts K)) :
    pinnedRestrictedArithmeticKernel K A alpha N h =
      ∑ d ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
        ∑ e ∈ separatedFirstSupport (primorialShifts K)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime
                (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1 then
            (separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) d *
              separatedFirstCoefficient (primorialShifts K)
                (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
                (primorialShiftsCandidate K A) e) /
              ∏ j : ↑(primorialShifts K),
                (Nat.totient
                  (BoundedGaps.Maynard.divisorTupleLcm
                    (primorialShifts K) d e j) : ℝ)
          else 0 := by
  classical
  let D := separatedFirstSupport (primorialShifts K)
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  let lambda := separatedFirstCoefficient (primorialShifts K)
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (primorialShiftsCandidate K A)
  let g : (↑(primorialShifts K) → ℕ) →
      (↑(primorialShifts K) → ℕ) → ℝ := fun d e =>
    if d h = 1 ∧ e h = 1 then
      (lambda d * lambda e) /
        ∏ j : ↑(primorialShifts K),
          (Nat.totient (BoundedGaps.Maynard.divisorTupleLcm
            (primorialShifts K) d e j) : ℝ)
    else 0
  change (∑ d : D, ∑ e : D.filter
      (fun e => BoundedGaps.Maynard.IsCrossCoordinateCoprime
        (primorialShifts K) d.1 e), g d.1 e.1) = _
  symm
  calc
    _ = ∑ d ∈ D, ∑ e ∈ D.filter
        (fun e => BoundedGaps.Maynard.IsCrossCoordinateCoprime
          (primorialShifts K) d e), g d e := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hc : BoundedGaps.Maynard.IsCrossCoordinateCoprime
          (primorialShifts K) d e <;>
        by_cases ho : d h = 1 ∧ e h = 1 <;>
          simp [g, lambda, hc, ho]
    _ = ∑ d ∈ D, ∑ e : D.filter
        (fun e => BoundedGaps.Maynard.IsCrossCoordinateCoprime
          (primorialShifts K) d e), g d e.1 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_subtype
        (D.filter (fun e => BoundedGaps.Maynard.IsCrossCoordinateCoprime
          (primorialShifts K) d e)) (fun _ => Iff.rfl) (g d)
    _ = _ := Finset.sum_subtype D (fun _ => Iff.rfl) _

/-- Uniform prime-count main term for one contributing divisor pair. -/
noncomputable def pinnedPairExpectedCount
    (K : ℕ) (Q : Finset ℕ)
    (d e : ↑(primorialShifts K) → ℕ) : ℝ :=
  (Q.card : ℝ) /
    ∏ j : ↑(primorialShifts K),
      (Nat.totient
        (BoundedGaps.Maynard.divisorTupleLcm
          (primorialShifts K) d e j) : ℝ)

/-- Literal discrepancy between a pinned divisor-pair count and its uniform
reduced-residue main term. -/
noncomputable def pinnedPairCountError
    (K N p : ℕ) (h : ↑(primorialShifts K)) (Q : Finset ℕ)
    (d e : ↑(primorialShifts K) → ℕ) : ℝ :=
  (pinnedPairQCount K N p h Q d e : ℝ) -
    pinnedPairExpectedCount K Q d e

noncomputable def pinnedRestrictedPairErrorSum
    (K : ℕ) (A alpha : ℝ) (N p : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ h : ↑(primorialShifts K),
    ∑ d ∈ separatedFirstSupport (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
      ∑ e ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime
              (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1 then
          separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) d *
            separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) e *
            pinnedPairCountError K N p h Q d e
        else 0

/-- Exact main-term/error decomposition of the compatible pinned prime sum.
The main arithmetic factor is precisely the standard restricted `S₂` kernel. -/
theorem pinnedRestrictedPairSum_eq_main_add_error
    (K : ℕ) (A alpha : ℝ) (N p : ℕ) (Q : Finset ℕ) :
    pinnedRestrictedPairSum K A alpha N p Q =
      (Q.card : ℝ) *
          ∑ h : ↑(primorialShifts K),
            pinnedRestrictedArithmeticKernel K A alpha N h +
        pinnedRestrictedPairErrorSum K A alpha N p Q := by
  classical
  unfold pinnedRestrictedPairSum pinnedRestrictedPairErrorSum
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [pinnedRestrictedArithmeticKernel_eq_raw]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hr : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1
  · simp [hr]
    unfold pinnedPairCountError pinnedPairExpectedCount
    simp only [Finset.univ_eq_attach]
    ring
  · simp [hr]

/-! ### CRT description of the pinned divisor-pair counts -/

/-- Reduced residue solving `c*q + p ≡ 0 (mod l)`. -/
noncomputable def negativeLinearResidue (c p l : ℕ) : ℕ :=
  ((-(p : ZMod l)) * (c : ZMod l)⁻¹).val

/-- Reduced residue solving `c*q ≡ p (mod l)`. -/
noncomputable def positiveLinearResidue (c p l : ℕ) : ℕ :=
  ((p : ZMod l) * (c : ZMod l)⁻¹).val

theorem negativeLinearResidue_spec {c p l : ℕ}
    (hl : 0 < l) (hcop : c.Coprime l) :
    c * negativeLinearResidue c p l + p ≡ 0 [MOD l] := by
  let _ : NeZero l := ⟨hl.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [show (negativeLinearResidue c p l : ZMod l) =
      (-(p : ZMod l)) * (c : ZMod l)⁻¹ by
    exact ZMod.natCast_zmod_val _]
  have hcUnit : IsUnit (c : ZMod l) :=
    (ZMod.isUnit_iff_coprime c l).2 hcop
  rw [show (c : ZMod l) * (-(p : ZMod l) * (c : ZMod l)⁻¹) + p =
      -(p : ZMod l) * ((c : ZMod l) * (c : ZMod l)⁻¹) + p by ring,
    ZMod.mul_inv_of_unit (c : ZMod l) hcUnit]
  ring

theorem positiveLinearResidue_spec {c p l : ℕ}
    (hl : 0 < l) (hcop : c.Coprime l) :
    c * positiveLinearResidue c p l ≡ p [MOD l] := by
  let _ : NeZero l := ⟨hl.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [show (positiveLinearResidue c p l : ZMod l) =
      (p : ZMod l) * (c : ZMod l)⁻¹ by
    exact ZMod.natCast_zmod_val _]
  have hcUnit : IsUnit (c : ZMod l) :=
    (ZMod.isUnit_iff_coprime c l).2 hcop
  rw [show (c : ZMod l) * ((p : ZMod l) * (c : ZMod l)⁻¹) =
      (p : ZMod l) * ((c : ZMod l) * (c : ZMod l)⁻¹) by ring,
    ZMod.mul_inv_of_unit (c : ZMod l) hcUnit]
  ring

theorem modEq_negativeLinearResidue_iff_dvd_add
    {c p l q : ℕ} (hl : 0 < l) (hcop : c.Coprime l) :
    q ≡ negativeLinearResidue c p l [MOD l] ↔
      l ∣ p + c * q := by
  have hspec := negativeLinearResidue_spec (c := c) (p := p) hl hcop
  constructor
  · intro hq
    have hmul := hq.mul_left c
    have hadd := hmul.add_right p
    have hzero : c * q + p ≡ 0 [MOD l] := hadd.trans hspec
    rw [Nat.add_comm]
    exact Nat.modEq_zero_iff_dvd.mp hzero
  · intro hdiv
    have hzero : c * q + p ≡ 0 [MOD l] := by
      rw [Nat.add_comm]
      exact Nat.modEq_zero_iff_dvd.mpr hdiv
    have hmul : c * q ≡ c * negativeLinearResidue c p l [MOD l] :=
      Nat.ModEq.add_right_cancel' p (hzero.trans hspec.symm)
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm hmul

theorem modEq_positiveLinearResidue_iff_dvd_sub
    {c p l q : ℕ} (hl : 0 < l) (hcop : c.Coprime l)
    (hcqp : c * q ≤ p) :
    q ≡ positiveLinearResidue c p l [MOD l] ↔
      l ∣ p - c * q := by
  have hspec := positiveLinearResidue_spec (c := c) (p := p) hl hcop
  constructor
  · intro hq
    have hmul := (hq.mul_left c).trans hspec
    exact (Nat.modEq_iff_dvd' hcqp).mp hmul
  · intro hdiv
    have hmul : c * q ≡ p [MOD l] :=
      (Nat.modEq_iff_dvd' hcqp).mpr hdiv
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm
      (hmul.trans hspec.symm)

/-- Coordinate residue for the affine pinned form.  Coordinates to the right
of the distinguished shift use `c*q + p`; coordinates to its left use
`p - c*q`. -/
noncomputable def pinnedCoordinateResidue
    (p W h j l : ℕ) : ℕ :=
  if h ≤ j then negativeLinearResidue (W * (j - h)) p l
  else positiveLinearResidue (W * (h - j)) p l

/-- The affine coefficient attached to any off-coordinate is invertible
modulo its coordinate LCM. -/
theorem pinned_coefficient_coprime_lcm
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    {h j : H} (hj : j ≠ h) :
    (W * Nat.dist j.1 h.1).Coprime
      (BoundedGaps.Maynard.divisorTupleLcm H d e j) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e j
  have hWl : W.Coprime l := by
    have hWd : W.Coprime (d j) := (hd.coordinate_coprime_W j).symm
    have hWe : W.Coprime (e j) := (he.coordinate_coprime_W j).symm
    exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d j) (e j))
      (hWd.mul_right hWe)
  have hdistl : (Nat.dist j.1 h.1).Coprime l := by
    by_contra hnot
    obtain ⟨r, hr, hrdist, hrl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    obtain hrd | hre := hr.dvd_lcm.mp hrl
    · have hrW := hcover hj r hr hrdist
      have hcop : r.Coprime W :=
        (hd.coordinate_coprime_W j).coprime_dvd_left hrd
      exact (hr.coprime_iff_not_dvd.mp hcop) hrW
    · have hrW := hcover hj r hr hrdist
      have hcop : r.Coprime W :=
        (he.coordinate_coprime_W j).coprime_dvd_left hre
      exact (hr.coprime_iff_not_dvd.mp hcop) hrW
  exact hWl.mul_left hdistl

/-- One off-coordinate divisibility condition is exactly one reduced residue
condition on the auxiliary prime. -/
theorem modEq_pinnedCoordinateResidue_iff
    {H : Finset ℕ} {R W p q : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    {h j : H} (hj : j ≠ h)
    (hmargin : h.1 * (W * q) ≤ p) :
    q ≡ pinnedCoordinateResidue p W h.1 j.1
          (BoundedGaps.Maynard.divisorTupleLcm H d e j)
        [MOD BoundedGaps.Maynard.divisorTupleLcm H d e j] ↔
      BoundedGaps.Maynard.divisorTupleLcm H d e j ∣
        p - h.1 * (W * q) + j.1 * (W * q) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e j
  have hl : 0 < l :=
    BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he j
  by_cases hhj : h.1 ≤ j.1
  · have hlt : h.1 < j.1 := lt_of_le_of_ne hhj (by
      intro heq
      exact hj (Subtype.ext heq.symm))
    have hcop : (W * (j.1 - h.1)).Coprime l := by
      have hdist : Nat.dist j.1 h.1 = j.1 - h.1 :=
        by rw [Nat.dist_comm]; exact Nat.dist_eq_sub_of_le hhj
      simpa [l, hdist] using
        (pinned_coefficient_coprime_lcm hd he hcover hj)
    have hshift : j.1 * (W * q) =
        h.1 * (W * q) + (W * (j.1 - h.1)) * q := by
      have hjdecomp : j.1 = h.1 + (j.1 - h.1) := by omega
      calc
        j.1 * (W * q) = (h.1 + (j.1 - h.1)) * (W * q) := by
          exact congrArg (fun x => x * (W * q)) hjdecomp
        _ = _ := by ring
    have hform : p - h.1 * (W * q) + j.1 * (W * q) =
        p + (W * (j.1 - h.1)) * q := by
      rw [hshift]
      omega
    rw [pinnedCoordinateResidue, if_pos hhj, hform]
    exact modEq_negativeLinearResidue_iff_dvd_add hl hcop
  · have hjh : j.1 < h.1 := lt_of_not_ge hhj
    have hcop : (W * (h.1 - j.1)).Coprime l := by
      have hdist : Nat.dist j.1 h.1 = h.1 - j.1 :=
        Nat.dist_eq_sub_of_le hjh.le
      simpa [l, hdist] using
        (pinned_coefficient_coprime_lcm hd he hcover hj)
    have hshift : h.1 * (W * q) =
        j.1 * (W * q) + (W * (h.1 - j.1)) * q := by
      have hhdecomp : h.1 = j.1 + (h.1 - j.1) := by omega
      calc
        h.1 * (W * q) = (j.1 + (h.1 - j.1)) * (W * q) := by
          exact congrArg (fun x => x * (W * q)) hhdecomp
        _ = _ := by ring
    have hcqp : (W * (h.1 - j.1)) * q ≤ p := by
      have : (W * (h.1 - j.1)) * q ≤ h.1 * (W * q) := by
        rw [hshift]
        omega
      exact this.trans hmargin
    have hform : p - h.1 * (W * q) + j.1 * (W * q) =
        p - (W * (h.1 - j.1)) * q := by
      rw [hshift]
      omega
    rw [pinnedCoordinateResidue, if_neg hhj, hform]
    exact modEq_positiveLinearResidue_iff_dvd_sub hl hcop hcqp

/-- Product of the coordinate LCMs away from the coordinate pinned to one. -/
def pinnedPairOffModulus
    (H : Finset ℕ) (h : H) (d e : H → ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.erase h,
    BoundedGaps.Maynard.divisorTupleLcm H d e j

theorem pinnedPairOffLcm_pos
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (h : H) {j : H} (_hj : j ∈ Finset.univ.erase h) :
    0 < BoundedGaps.Maynard.divisorTupleLcm H d e j :=
  BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he j

theorem pinnedPairOffLcm_pairwise
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    (h : H) :
    Set.Pairwise (↑(Finset.univ.erase h) : Set H)
      (fun a b => Nat.Coprime
        (BoundedGaps.Maynard.divisorTupleLcm H d e a)
        (BoundedGaps.Maynard.divisorTupleLcm H d e b)) := by
  intro a ha b hb hab
  have hdd : (d a).Coprime (d b) := hd.coordinates_coprime hab
  have hee : (e a).Coprime (e b) := he.coordinates_coprime hab
  obtain ⟨hde, hed⟩ := hcross hab
  exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four hdd hde hed hee

/-- The simultaneous CRT residue determined by all unpinned coordinates. -/
noncomputable def pinnedPairCrtResidue
    {H : Finset ℕ} {R W : ℕ} (p : ℕ) (h : H) (d e : H → ℕ)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun j => pinnedCoordinateResidue p W h.1 j.1
      (BoundedGaps.Maynard.divisorTupleLcm H d e j))
    (BoundedGaps.Maynard.divisorTupleLcm H d e)
    (Finset.univ.erase h)
    (fun j hj => (pinnedPairOffLcm_pos hd he h hj).ne')
    (pinnedPairOffLcm_pairwise hd he hcross h)

theorem pinnedPairCrtResidue_mod
    {H : Finset ℕ} {R W p : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    {j : H} (hj : j ∈ Finset.univ.erase h) :
    pinnedPairCrtResidue p h d e hd he hcross ≡
      pinnedCoordinateResidue p W h.1 j.1
        (BoundedGaps.Maynard.divisorTupleLcm H d e j)
      [MOD BoundedGaps.Maynard.divisorTupleLcm H d e j] := by
  exact (Nat.chineseRemainderOfFinset
    (fun j => pinnedCoordinateResidue p W h.1 j.1
      (BoundedGaps.Maynard.divisorTupleLcm H d e j))
    (BoundedGaps.Maynard.divisorTupleLcm H d e)
    (Finset.univ.erase h)
    (fun j hj => (pinnedPairOffLcm_pos hd he h hj).ne')
    (pinnedPairOffLcm_pairwise hd he hcross h)).prop j hj

theorem pinnedPairCrtResidue_lt_modulus
    {H : Finset ℕ} {R W p : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e) :
    pinnedPairCrtResidue p h d e hd he hcross <
      pinnedPairOffModulus H h d e := by
  unfold pinnedPairCrtResidue pinnedPairOffModulus
  exact Nat.chineseRemainderOfFinset_lt_prod
    (fun j => pinnedCoordinateResidue p W h.1 j.1
      (BoundedGaps.Maynard.divisorTupleLcm H d e j))
    (BoundedGaps.Maynard.divisorTupleLcm H d e)
    (fun j hj => (pinnedPairOffLcm_pos hd he h hj).ne')
    (pinnedPairOffLcm_pairwise hd he hcross h)

/-- Subject to the pinning and support hypotheses, all doubled divisor
conditions are equivalent to membership in the single CRT residue class. -/
theorem modEq_pinnedPairCrtResidue_iff
    {H : Finset ℕ} {R W p q : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    (hdh : d h = 1) (heh : e h = 1)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hmargin : h.1 * (W * q) ≤ p) :
    q ≡ pinnedPairCrtResidue p h d e hd he hcross
        [MOD pinnedPairOffModulus H h d e] ↔
      (∀ j : H,
        d j ∣ p - h.1 * (W * q) + j.1 * (W * q)) ∧
      (∀ j : H,
        e j ∣ p - h.1 * (W * q) + j.1 * (W * q)) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e
  let S : Finset H := Finset.univ.erase h
  have hpairSet := pinnedPairOffLcm_pairwise hd he hcross h
  have hpairList : S.toList.Pairwise
      (fun a b => Nat.Coprime (l a) (l b)) := by
    apply List.Nodup.pairwise_of_forall_ne S.nodup_toList
    intro a ha b hb hab
    exact hpairSet (by simpa [S] using ha) (by simpa [S] using hb) hab
  have hprodIff :
      q ≡ pinnedPairCrtResidue p h d e hd he hcross
          [MOD pinnedPairOffModulus H h d e] ↔
        ∀ j ∈ S.toList,
          q ≡ pinnedPairCrtResidue p h d e hd he hcross [MOD l j] := by
    simpa [pinnedPairOffModulus, S, l] using
      (Nat.modEq_list_map_prod_iff
        (a := q) (b := pinnedPairCrtResidue p h d e hd he hcross)
        hpairList)
  rw [hprodIff]
  constructor
  · intro hq
    constructor
    · intro j
      by_cases hj : j = h
      · subst j
        simp [hdh]
      · have hjS : j ∈ S.toList := by simp [S, hj]
        have hqCoord := (hq j hjS).trans
          (pinnedPairCrtResidue_mod hd he hcross (by simp [S, hj]))
        have hlcm := (modEq_pinnedCoordinateResidue_iff hd he hcover hj
          hmargin).mp hqCoord
        exact (Nat.lcm_dvd_iff.mp hlcm).1
    · intro j
      by_cases hj : j = h
      · subst j
        simp [heh]
      · have hjS : j ∈ S.toList := by simp [S, hj]
        have hqCoord := (hq j hjS).trans
          (pinnedPairCrtResidue_mod hd he hcross (by simp [S, hj]))
        have hlcm := (modEq_pinnedCoordinateResidue_iff hd he hcover hj
          hmargin).mp hqCoord
        exact (Nat.lcm_dvd_iff.mp hlcm).2
  · rintro ⟨hdivD, hdivE⟩
    intro j hjS
    have hj : j ≠ h := by simpa [S] using hjS
    have hlcm : l j ∣ p - h.1 * (W * q) + j.1 * (W * q) :=
      Nat.lcm_dvd (hdivD j) (hdivE j)
    have hqCoord := (modEq_pinnedCoordinateResidue_iff hd he hcover hj
      hmargin).mpr hlcm
    exact hqCoord.trans
      (pinnedPairCrtResidue_mod hd he hcross (by simp [S, hj])).symm

/-- A residue congruent to a multiple of itself times a prime can only have
prime factors already present in the prime or the modulus. -/
theorem residue_coprime_of_mul_modEq_prime
    {c r p l : ℕ} (hp : p.Prime) (hpl : p.Coprime l)
    (hmod : c * r ≡ p [MOD l]) : r.Coprime l := by
  by_contra hnot
  obtain ⟨s, hs, hsr, hsl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hscp : s ∣ c * r := dvd_mul_of_dvd_right hsr c
  have hsp : s ∣ p := (hmod.dvd_iff hsl).mp hscp
  rcases (Nat.dvd_prime hp).mp hsp with hs1 | hspeq
  · exact hs.ne_one hs1
  · subst s
    exact (hp.coprime_iff_not_dvd.mp hpl) hsl

theorem coprime_modulus_iff_of_modEq {a b m : ℕ}
    (h : a ≡ b [MOD m]) : a.Coprime m ↔ b.Coprime m := by
  have hab : a % m = b % m := h
  constructor
  · intro ha
    apply (ZMod.coprime_mod_iff_coprime b m).mp
    rw [← hab]
    exact (ZMod.coprime_mod_iff_coprime a m).mpr ha
  · intro hb
    apply (ZMod.coprime_mod_iff_coprime a m).mp
    rw [hab]
    exact (ZMod.coprime_mod_iff_coprime b m).mpr hb

theorem residue_coprime_of_mul_add_modEq_zero_prime
    {c r p l : ℕ} (hp : p.Prime) (hpl : p.Coprime l)
    (hmod : c * r + p ≡ 0 [MOD l]) : r.Coprime l := by
  by_contra hnot
  obtain ⟨s, hs, hsr, hsl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hscp : s ∣ c * r := dvd_mul_of_dvd_right hsr c
  have hlsum : l ∣ c * r + p := Nat.modEq_zero_iff_dvd.mp hmod
  have hssum : s ∣ c * r + p := hsl.trans hlsum
  have hsp : s ∣ p := (Nat.dvd_add_iff_right hscp).mpr hssum
  rcases (Nat.dvd_prime hp).mp hsp with hs1 | hspeq
  · exact hs.ne_one hs1
  · subst s
    exact (hp.coprime_iff_not_dvd.mp hpl) hsl

theorem prime_coprime_divisorTupleLcm
    {H : Finset ℕ} {R W p : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hp : p.Prime) (hRp : R ≤ p) (j : H) :
    p.Coprime (BoundedGaps.Maynard.divisorTupleLcm H d e j) := by
  have hpDprod : p.Coprime
      (BoundedGaps.Maynard.divisorTupleProduct H d) :=
    Nat.Coprime.of_dvd_left (show p ∣ W * p by exact ⟨W, by ring⟩)
      (prime_mul_modulus_coprime_tupleProduct hd hp hRp)
  have hpEprod : p.Coprime
      (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (show p ∣ W * p by exact ⟨W, by ring⟩)
      (prime_mul_modulus_coprime_tupleProduct he hp hRp)
  have hpD : p.Coprime (d j) := Nat.Coprime.of_dvd_right
    (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d j) hpDprod
  have hpE : p.Coprime (e j) := Nat.Coprime.of_dvd_right
    (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e j) hpEprod
  exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d j) (e j))
    (hpD.mul_right hpE)

theorem pinnedCoordinateResidue_coprime_lcm
    {H : Finset ℕ} {R W p : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRp : R ≤ p)
    {h j : H} (hj : j ≠ h) :
    (pinnedCoordinateResidue p W h.1 j.1
      (BoundedGaps.Maynard.divisorTupleLcm H d e j)).Coprime
        (BoundedGaps.Maynard.divisorTupleLcm H d e j) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e j
  have hl : 0 < l :=
    BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he j
  have hpl : p.Coprime l := prime_coprime_divisorTupleLcm hd he hp hRp j
  by_cases hhj : h.1 ≤ j.1
  · rw [pinnedCoordinateResidue, if_pos hhj]
    have hlt : h.1 < j.1 := lt_of_le_of_ne hhj (by
      intro heq
      exact hj (Subtype.ext heq.symm))
    have hdist : Nat.dist j.1 h.1 = j.1 - h.1 := by
      rw [Nat.dist_comm]
      exact Nat.dist_eq_sub_of_le hhj
    exact residue_coprime_of_mul_add_modEq_zero_prime hp hpl
      (negativeLinearResidue_spec hl (by
        simpa [hdist] using
          (pinned_coefficient_coprime_lcm hd he hcover hj)))
  · rw [pinnedCoordinateResidue, if_neg hhj]
    have hjh : j.1 < h.1 := lt_of_not_ge hhj
    have hdist : Nat.dist j.1 h.1 = h.1 - j.1 :=
      Nat.dist_eq_sub_of_le hjh.le
    exact residue_coprime_of_mul_modEq_prime hp hpl
      (positiveLinearResidue_spec hl (by
        simpa [hdist] using
          (pinned_coefficient_coprime_lcm hd he hcover hj)))

/-- The CRT class attached to a contributing pair is a reduced residue
class, as required by Bombieri--Vinogradov. -/
theorem pinnedPairCrtResidue_coprime_modulus
    {H : Finset ℕ} {R W p : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRp : R ≤ p) :
    (pinnedPairCrtResidue p h d e hd he hcross).Coprime
      (pinnedPairOffModulus H h d e) := by
  unfold pinnedPairOffModulus
  apply Nat.Coprime.prod_right
  intro j hj
  exact (coprime_modulus_iff_of_modEq
    (pinnedPairCrtResidue_mod hd he hcross hj)).mpr
      (pinnedCoordinateResidue_coprime_lcm hd he hcover hp hRp
        (by simpa using hj))

/-- Auxiliary primes in a half-open interval. -/
def auxiliaryPrimeInterval (A B : ℕ) : Finset ℕ :=
  (Finset.Ico A B).filter Nat.Prime

theorem mem_auxiliaryPrimeInterval {A B q : ℕ} :
    q ∈ auxiliaryPrimeInterval A B ↔ A ≤ q ∧ q < B ∧ q.Prime := by
  simp [auxiliaryPrimeInterval, and_assoc]

theorem cast_auxiliaryPrimeInterval_card
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    ((auxiliaryPrimeInterval A B).card : ℝ) =
      (BoundedGaps.Maynard.primeCountTotal (B - 1) : ℝ) -
        (BoundedGaps.Maynard.primeCountTotal (A - 1) : ℝ) := by
  have hB : 0 < B := hA.trans_le hAB
  have hupper : B - 1 + 1 = B := Nat.sub_add_cancel hB
  have hlower : A - 1 + 1 = A := Nat.sub_add_cancel hA
  unfold auxiliaryPrimeInterval BoundedGaps.Maynard.primeCountTotal
    Nat.primeCounting Nat.primeCounting'
  rw [hupper, hlower, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  exact Finset.sum_Ico_eq_sub _ hAB

/-- For a compatible pinned pair, its exact auxiliary-prime count is the
standard prime count in the CRT progression. -/
theorem pinnedPairQCount_primeInterval_eq_progressionCount
    {K N p A B : ℕ} {alpha : ℝ}
    (h : ↑(primorialShifts K))
    {d e : ↑(primorialShifts K) → ℕ}
    (hdmem : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hemem : e ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      (primorialShifts K) d e)
    (hdh : d h = 1) (heh : e h = 1)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p) :
    pinnedPairQCount K N p h (auxiliaryPrimeInterval A B) d e =
      BoundedGaps.Maynard.primeVariableProgressionCount A B
        (pinnedPairOffModulus (primorialShifts K) h d e)
        (pinnedPairCrtResidue p h d e
          (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem)
          (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
          hcross) := by
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  have hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W d := by
    simpa [separatedFirstSupport, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem
  have he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W e := by
    simpa [separatedFirstSupport, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  unfold pinnedPairQCount auxiliaryPrimeInterval
    BoundedGaps.Maynard.primeVariableProgressionCount
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hqI, hqprime⟩, hcondD, hcondE⟩
    refine ⟨hqI, hqprime, ?_⟩
    apply (modEq_pinnedPairCrtResidue_iff hd he hcross hdh heh hcover
      (hmargin q (by simpa only [Finset.mem_Ico] using hqI))).mpr
    exact ⟨hcondD, hcondE⟩
  · rintro ⟨hqI, hqprime, hmod⟩
    refine ⟨⟨hqI, hqprime⟩, ?_⟩
    exact (modEq_pinnedPairCrtResidue_iff hd he hcross hdh heh hcover
      (hmargin q (by simpa only [Finset.mem_Ico] using hqI))).mp hmod

/-- Removing the pinned coordinate, whose LCM is one, does not change the
product of coordinate totients. -/
theorem totient_pinnedPairOffModulus
    {H : Finset ℕ} {R W : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    (hdh : d h = 1) (heh : e h = 1) :
    Nat.totient (pinnedPairOffModulus H h d e) =
      ∏ j : H, Nat.totient
        (BoundedGaps.Maynard.divisorTupleLcm H d e j) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e
  have hpair := pinnedPairOffLcm_pairwise hd he hcross h
  rw [pinnedPairOffModulus]
  rw [BoundedGaps.Maynard.totient_finsetProd_of_pairwise_coprime
    (Finset.univ.erase h) l hpair]
  have hlh : l h = 1 := by
    simp [l, BoundedGaps.Maynard.divisorTupleLcm, hdh, heh]
  have hdecomp := Finset.prod_erase_mul
    (s := (Finset.univ : Finset H))
    (f := fun j => Nat.totient (l j)) (Finset.mem_univ h)
  simp [hlh] at hdecomp
  exact hdecomp

/-- The exact error of one compatible pinned pair is bounded by the two
endpoint progression discrepancies. -/
theorem abs_pinnedPairCountError_primeInterval_le_global_sum
    {K N p A B : ℕ} {alpha : ℝ}
    (h : ↑(primorialShifts K))
    {d e : ↑(primorialShifts K) → ℕ}
    (hdmem : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hemem : e ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      (primorialShifts K) d e)
    (hdh : d h = 1) (heh : e h = 1)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedPairCountError K N p h (auxiliaryPrimeInterval A B) d e| ≤
      BoundedGaps.Maynard.progressionDiscrepancy (B - 1)
          (pinnedPairOffModulus (primorialShifts K) h d e)
          (pinnedPairCrtResidue p h d e
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
            hcross) +
        BoundedGaps.Maynard.progressionDiscrepancy (A - 1)
          (pinnedPairOffModulus (primorialShifts K) h d e)
          (pinnedPairCrtResidue p h d e
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
            hcross) := by
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  have hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W d := by
    simpa [separatedFirstSupport, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem
  have he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W e := by
    simpa [separatedFirstSupport, R, W,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  have htot := totient_pinnedPairOffModulus hd he hcross hdh heh
  have htotR :
      (Nat.totient (pinnedPairOffModulus (primorialShifts K) h d e) : ℝ) =
        ∏ j : ↑(primorialShifts K),
          (Nat.totient (BoundedGaps.Maynard.divisorTupleLcm
            (primorialShifts K) d e j) : ℝ) := by
    exact_mod_cast htot
  have hcount := pinnedPairQCount_primeInterval_eq_progressionCount h hdmem
    hemem hcross hdh heh hcover hmargin
  have hcard := cast_auxiliaryPrimeInterval_card hA hAB
  unfold pinnedPairCountError pinnedPairExpectedCount
  rw [hcount, hcard]
  rw [← htotR]
  exact BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
    hA hAB

theorem pinnedPairOffModulus_pos
    {H : Finset ℕ} {R W : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e) :
    0 < pinnedPairOffModulus H h d e := by
  unfold pinnedPairOffModulus
  apply Finset.prod_pos
  intro j hj
  exact BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he j

/-- Since the CRT residue is reduced, the pairwise discrepancy is bounded by
the maximum discrepancy for its modulus at the two endpoints. -/
theorem abs_pinnedPairCountError_primeInterval_le_max
    {K N p A B : ℕ} {alpha : ℝ}
    (h : ↑(primorialShifts K))
    {d e : ↑(primorialShifts K) → ℕ}
    (hdmem : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hemem : e ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      (primorialShifts K) d e)
    (hdh : d h = 1) (heh : e h = 1)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hp : p.Prime)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedPairCountError K N p h (auxiliaryPrimeInterval A B) d e| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
          (pinnedPairOffModulus (primorialShifts K) h d e) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
          (pinnedPairOffModulus (primorialShifts K) h d e) := by
  let hd := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdmem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  let M := pinnedPairOffModulus (primorialShifts K) h d e
  let r := pinnedPairCrtResidue p h d e hd he hcross
  have hM : 0 < M := pinnedPairOffModulus_pos hd he
  have hcop : r.Coprime M :=
    pinnedPairCrtResidue_coprime_modulus hd he hcross hcover hp hRp
  have hrlt : r < M := pinnedPairCrtResidue_lt_modulus hd he hcross
  have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues M := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hcop⟩
  calc
    _ ≤ BoundedGaps.Maynard.progressionDiscrepancy (B - 1) M r +
          BoundedGaps.Maynard.progressionDiscrepancy (A - 1) M r := by
      exact abs_pinnedPairCountError_primeInterval_le_global_sum h hdmem hemem
        hcross hdh heh hcover hmargin hA hAB
    _ ≤ _ := add_le_add
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)

theorem pinnedPairOffModulus_eq_divisorPairModulus_one
    {H : Finset ℕ} {h : H} {d e : H → ℕ}
    (hdh : d h = 1) (heh : e h = 1) :
    pinnedPairOffModulus H h d e =
      BoundedGaps.Maynard.divisorPairModulus H 1 d e := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e
  have hlh : l h = 1 := by
    simp [l, BoundedGaps.Maynard.divisorTupleLcm, hdh, heh]
  have hdecomp := Finset.prod_erase_mul
    (s := (Finset.univ : Finset H)) (f := l) (Finset.mem_univ h)
  simp [hlh] at hdecomp
  simpa [pinnedPairOffModulus, BoundedGaps.Maynard.divisorPairModulus, l]
    using hdecomp

/-- Reindex the raw restricted triple sum by the standard compatible
pair-shift finset used by the Maynard distribution library. -/
theorem sum_compatiblePairShiftIndex_eq
    {H : Finset ℕ} (D : Finset (H → ℕ))
    (f : H → (H → ℕ) → (H → ℕ) → ℝ) :
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex H D,
      f i.2 i.1.1 i.1.2) =
      ∑ h : H, ∑ d ∈ D, ∑ e ∈ D,
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
            d h = 1 ∧ e h = 1 then f h d e else 0 := by
  unfold BoundedGaps.Maynard.compatiblePairShiftIndex
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ ((D ×ˢ D).filter (fun de =>
          BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2)).product
          Finset.univ,
        if a.1.1 a.2 = 1 ∧ a.1.2 a.2 = 1 then
          f a.2 a.1.1 a.1.2 else 0) =
        ∑ de ∈ (D ×ˢ D).filter (fun de =>
          BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2),
          ∑ h : H, if de.1 h = 1 ∧ de.2 h = 1 then
            f h de.1 de.2 else 0 :=
      Finset.sum_product _ Finset.univ _
    _ = ∑ de ∈ D ×ˢ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2 then
            ∑ h : H, if de.1 h = 1 ∧ de.2 h = 1 then
              f h de.1 de.2 else 0
          else 0 :=
      Finset.sum_filter
        (fun de : (H → ℕ) × (H → ℕ) =>
          BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2) _
    _ = ∑ d ∈ D, ∑ e ∈ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e then
            ∑ h : H, if d h = 1 ∧ e h = 1 then f h d e else 0
          else 0 := Finset.sum_product D D _
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ h : H,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
              d h = 1 ∧ e h = 1 then f h d e else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      by_cases hc : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e <;>
        simp [hc]
    _ = _ := by
      calc
        (∑ d ∈ D, ∑ e ∈ D, ∑ h : H,
            if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
                d h = 1 ∧ e h = 1 then f h d e else 0) =
            ∑ d ∈ D, ∑ h : H, ∑ e ∈ D,
              if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
                  d h = 1 ∧ e h = 1 then f h d e else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

/-- Coefficient-weighted maximal progression discrepancy for the pinned
restricted divisor pairs. -/
noncomputable def pinnedRestrictedWeightedDiscrepancySum
    (K : ℕ) (A alpha : ℝ) (N x : ℕ) : ℝ :=
  ∑ h : ↑(primorialShifts K),
    ∑ d ∈ separatedFirstSupport (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
      ∑ e ∈ separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)),
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime
              (primorialShifts K) d e ∧ d h = 1 ∧ e h = 1 then
          |separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) d *
            separatedFirstCoefficient (primorialShifts K)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
              (primorialShiftsCandidate K A) e| *
            BoundedGaps.Maynard.maxProgressionDiscrepancy x
              (pinnedPairOffModulus (primorialShifts K) h d e)
        else 0

theorem pinnedRestrictedWeightedDiscrepancySum_eq_standard
    (K : ℕ) (A alpha : ℝ) (N x : ℕ) :
    pinnedRestrictedWeightedDiscrepancySum K A alpha N x =
      BoundedGaps.Maynard.compatiblePairShiftWeightedDiscrepancySum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))) 1 x
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
          (primorialShiftsCandidate K A)) := by
  let H := primorialShifts K
  let D := separatedFirstSupport H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  let lambda := separatedFirstCoefficient H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (primorialShiftsCandidate K A)
  rw [BoundedGaps.Maynard.compatiblePairShiftWeightedDiscrepancySum]
  rw [sum_compatiblePairShiftIndex_eq D
    (fun h d e => |lambda d * lambda e| *
      BoundedGaps.Maynard.maxProgressionDiscrepancy x
        (BoundedGaps.Maynard.compatiblePairShiftModulus H 1 ((d, e), h)))]
  unfold pinnedRestrictedWeightedDiscrepancySum
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hr : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
      d h = 1 ∧ e h = 1
  · rw [if_pos hr, if_pos hr]
    rw [pinnedPairOffModulus_eq_divisorPairModulus_one hr.2.1 hr.2.2]
    rfl
  · rw [if_neg hr, if_neg hr]

/-- Triangle inequality and the pointwise Bombieri--Vinogradov discrepancy
bound reduce the entire pinned error to the two standard weighted sums. -/
theorem abs_pinnedRestrictedPairErrorSum_le_weightedDiscrepancies
    {K N p A B : ℕ} {Ac alpha : ℝ}
    (hp : p.Prime)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hmargin : ∀ q ∈ Finset.Ico A B, ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) ≤ p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedRestrictedPairErrorSum K Ac alpha N p
        (auxiliaryPrimeInterval A B)| ≤
      pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (B - 1) +
        pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (A - 1) := by
  let H := primorialShifts K
  let D := separatedFirstSupport H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  let lambda := separatedFirstCoefficient H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (primorialShiftsCandidate K Ac)
  calc
    |pinnedRestrictedPairErrorSum K Ac alpha N p
        (auxiliaryPrimeInterval A B)| ≤
        ∑ h : H, |∑ d ∈ D, ∑ e ∈ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
              d h = 1 ∧ e h = 1 then
            lambda d * lambda e *
              pinnedPairCountError K N p h (auxiliaryPrimeInterval A B) d e
          else 0| := by
      unfold pinnedRestrictedPairErrorSum
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : H, ∑ d ∈ D, |∑ e ∈ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
              d h = 1 ∧ e h = 1 then
            lambda d * lambda e *
              pinnedPairCountError K N p h (auxiliaryPrimeInterval A B) d e
          else 0| := by
      apply Finset.sum_le_sum
      intro h hh
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : H, ∑ d ∈ D, ∑ e ∈ D,
          |if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
              d h = 1 ∧ e h = 1 then
            lambda d * lambda e *
              pinnedPairCountError K N p h (auxiliaryPrimeInterval A B) d e
          else 0| := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : H, ∑ d ∈ D, ∑ e ∈ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
              d h = 1 ∧ e h = 1 then
            |lambda d * lambda e| *
              (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
                  (pinnedPairOffModulus H h d e) +
                BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
                  (pinnedPairOffModulus H h d e))
          else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      by_cases hr : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
          d h = 1 ∧ e h = 1
      · rw [if_pos hr, if_pos hr, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_pinnedPairCountError_primeInterval_le_max h hd he
            hr.1 hr.2.1 hr.2.2 hcover hp hRp
            (fun q hq => hmargin q hq h) hA hAB)
          (mul_nonneg (abs_nonneg (lambda d)) (abs_nonneg (lambda e)))
      · simp [hr]
    _ = pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (B - 1) +
        pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (A - 1) := by
      unfold pinnedRestrictedWeightedDiscrepancySum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hr : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e ∧
          d h = 1 ∧ e h = 1
      · dsimp [H, lambda] at hr ⊢
        by_cases hc : BoundedGaps.Maynard.IsCrossCoordinateCoprime
            (primorialShifts K) d e
        · simp [hc, hr.2.1, hr.2.2]
          ring
        · exact (hc hr.1).elim
      · dsimp [H, lambda] at hr ⊢
        by_cases hc : BoundedGaps.Maynard.IsCrossCoordinateCoprime
            (primorialShifts K) d e <;>
          by_cases hd1 : d h = 1 <;>
            by_cases he1 : e h = 1 <;> simp_all

noncomputable def pinnedSharpCoefficientEnvelope
    (K : ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
    (2 * (Fintype.card ↑(primorialShifts K)) ^ 2)

theorem pinnedSharpCoefficientEnvelope_nonneg
    (K : ℕ) (alpha : ℝ) (N : ℕ) :
    0 ≤ pinnedSharpCoefficientEnvelope K alpha N := by
  unfold pinnedSharpCoefficientEnvelope
  rw [pow_mul]
  positivity

theorem separatedFirstCoefficient_abs_le_sharp
    {K N : ℕ} {Ac alpha : ℝ} (hK : 0 < K) (hAc : 0 < Ac)
    {d : ↑(primorialShifts K) → ℕ}
    (hd : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))) :
    |separatedFirstCoefficient (primorialShifts K)
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
        (primorialShiftsCandidate K Ac) d| ≤
      pinnedSharpCoefficientEnvelope K alpha N := by
  have hH : (primorialShifts K).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_primorialShifts]
    exact hK
  simpa [separatedFirstCoefficient, separatedFirstSupport,
    pinnedSharpCoefficientEnvelope] using
    (BoundedGaps.Maynard.abs_maynardCoefficient_le_sharp_log
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (primorial (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
      (primorialShiftsCandidate K Ac) d 1 (by norm_num)
      (primorialShiftsCandidate_abs_le_one hAc) hH hd)

theorem isMaynardDivisorTuple_one_of_separatedSupport
    {K N : ℕ} {alpha : ℝ}
    {d : ↑(primorialShifts K) → ℕ}
    (hd : d ∈ separatedFirstSupport (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))) :
    BoundedGaps.Maynard.IsMaynardDivisorTuple (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) 1 d := by
  have ht := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  exact ⟨ht.1, Nat.coprime_one_right _, ht.2.2⟩

/-- The full pinned weighted discrepancy inherits the sharp tau-weighted
Bombieri--Vinogradov envelope, with no polynomial support-cardinality loss. -/
theorem PrimeLevelWitness.pinnedRestrictedWeightedDiscrepancySum_le_tau
    {theta E C : ℝ} {X₀ K N x : ℕ} {Ac alpha : ℝ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta E C X₀)
    (hx : X₀ ≤ x) (hK : 0 < K) (hAc : 0 < Ac)
    (hsize : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ x + 1)
    (hcut : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤
          BoundedGaps.Maynard.modulusCutoff theta x) :
    pinnedRestrictedWeightedDiscrepancySum K Ac alpha N x ≤
      pinnedSharpCoefficientEnvelope K alpha N ^ 2 *
        ((Fintype.card ↑(primorialShifts K) : ℝ) *
          (Real.sqrt
              ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
                (1 + Real.log
                  (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
                    BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
                  (2 * (3 * Fintype.card ↑(primorialShifts K)) ^ 2)) *
            Real.sqrt
              (C * (x : ℝ) /
                Real.rpow (Real.log (x : ℝ)) E))) := by
  let H := primorialShifts K
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let D := separatedFirstSupport H R
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  let lambda := separatedFirstCoefficient H R
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (primorialShiftsCandidate K Ac)
  let L := pinnedSharpCoefficientEnvelope K alpha N
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    simpa [H, card_primorialShifts] using hK
  have hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R 1 d := by
    intro d hd
    exact isMaynardDivisorTuple_one_of_separatedSupport hd
  have hL : 0 ≤ L := pinnedSharpCoefficientEnvelope_nonneg K alpha N
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact separatedFirstCoefficient_abs_le_sharp hK hAc hd
  have hSQ := BoundedGaps.Maynard.compatiblePairShiftModulus_image_subset_radius
    (H := H) (D := D) (R := R) (W := 1) (by norm_num) hD
  have hcut' := BoundedGaps.Maynard.compatiblePairShiftModulus_image_subset_cutoff
    (H := H) (D := D) (R := R) (W := 1) (θ := theta) (x := x)
    (by norm_num) hD (by simpa [R] using hcut)
  have hsum := hw.sum_maxProgressionDiscrepancy_compatiblePairShift_tau
    hx hH squarefree_one hD
    (by simpa [R] using hSQ) (by simpa [R] using hsize) hcut'
  rw [pinnedRestrictedWeightedDiscrepancySum_eq_standard]
  exact (BoundedGaps.Maynard.compatiblePairShiftWeightedDiscrepancySum_le
    hL hbound).trans (mul_le_mul_of_nonneg_left
      (by simpa only [H, R, Nat.cast_mul] using hsum) (sq_nonneg L))

/-- Subtracting a multiple of `W*q` preserves both the class modulo `W`
and the class modulo `q`. -/
theorem sub_scaledShift_modEq
    {W q p h : ℕ} (hW : 0 < W) (hq : 0 < q)
    (hshift : h * (W * q) ≤ p) :
    p - h * (W * q) ≡ p [MOD W] ∧
      p - h * (W * q) ≡ p [MOD q] := by
  let s := h * (W * q)
  let n := p - s
  have hns : n + s = p := Nat.sub_add_cancel hshift
  have hWdiv : W ∣ s := by
    dsimp [s]
    exact ⟨h * q, by ring⟩
  have hqdiv : q ∣ s := by
    dsimp [s]
    exact ⟨h * W, by ring⟩
  have aux {M : ℕ} (_hM : 0 < M) (hdiv : M ∣ s) : n ≡ p [MOD M] := by
    have hs0 : s ≡ 0 [MOD M] := Nat.modEq_zero_iff_dvd.mpr hdiv
    have hsum : n + s ≡ n + 0 [MOD M] :=
      (Nat.ModEq.refl n).add hs0
    exact (show p ≡ n [MOD M] by simpa [hns] using hsum).symm
  exact ⟨aux hW hWdiv, aux hq hqdiv⟩

/-- The doubled small-prime condition propagates from a target survivor to
every shifted preimage used to hit it. -/
theorem largeGapPreSieved_sub_scaledShift
    {w m q p h : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hshift : h * (primorial w * q) < p)
    (hp : largeGapPreSieved w m p) :
    largeGapPreSieved w m (p - h * (primorial w * q)) := by
  let n := p - h * (primorial w * q)
  have hn : 0 < n := Nat.sub_pos_of_lt hshift
  have hmod : n ≡ p [MOD primorial w] :=
    (sub_scaledShift_modEq (primorial_pos w) hq hshift.le).1
  unfold largeGapPreSieved at hp ⊢
  change (preSievePolynomial m n).Coprime (primorial w)
  change (preSievePolynomial m p).Coprime (primorial w) at hp
  exact (preSievePolynomial_coprime_congr hm hn
    (Nat.zero_lt_of_lt hshift) hmod).mpr hp

theorem sub_scaledShift_mod
    {W q p h : ℕ} (hW : 0 < W) (hq : 0 < q)
    (hshift : h * (W * q) ≤ p) :
    (p - h * (W * q)) % q = p % q :=
  (sub_scaledShift_modEq hW hq hshift).2

/-- All coordinate shifts give distinct admissible summands in the residue
class that hits `p`. -/
theorem sum_shift_pointWeights_le_residueRawWeight
    {K m N q p : ℕ} {A alpha : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hpN : p ≤ N)
    (hpre : largeGapPreSieved
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m p)
    (hmargin : ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) < p) :
    (∑ h : ↑(primorialShifts K),
      scaledTrivialPointWeight K A alpha m N q
        (p - h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) ≤
      scaledTrivialResidueRawWeight K A alpha m N q
        ⟨p % q, Nat.mod_lt p hq⟩ := by
  classical
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let f : ↑(primorialShifts K) → ℕ := fun h => p - h.1 * (W * q)
  let S : Finset ℕ := Finset.univ.image f
  let g : ℕ → ℝ := fun n =>
    if largeGapPreSieved
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m n ∧
        n % q = p % q then
      scaledTrivialPointWeight K A alpha m N q n
    else 0
  have hfInj : Function.Injective f := by
    intro a b hab
    have ha : a.1 * (W * q) ≤ p := (hmargin a).le
    have hb : b.1 * (W * q) ≤ p := (hmargin b).le
    have hmul : a.1 * (W * q) = b.1 * (W * q) :=
      (tsub_right_inj ha hb).mp hab
    have hWq : 0 < W * q := Nat.mul_pos (by
      dsimp [W, BoundedGaps.Maynard.engelsmaMaynardModulus]
      exact primorial_pos _) hq
    have habval : a.1 = b.1 := Nat.eq_of_mul_eq_mul_right hWq hmul
    exact Subtype.ext habval
  have hSsub : S ⊆ Finset.Icc 0 N := by
    intro n hn
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le _ _).trans hpN⟩
  have hgSelected : ∀ h : ↑(primorialShifts K),
      g (f h) = scaledTrivialPointWeight K A alpha m N q (f h) := by
    intro h
    have hpre' := largeGapPreSieved_sub_scaledShift hm hq (hmargin h) hpre
    have hpre'' : largeGapPreSieved
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m (f h) := by
      simpa [f, W, BoundedGaps.Maynard.engelsmaMaynardModulus] using hpre'
    have hmod := sub_scaledShift_mod (by
      dsimp [W, BoundedGaps.Maynard.engelsmaMaynardModulus]
      exact primorial_pos _) hq (hmargin h).le
    rw [show g (f h) = scaledTrivialPointWeight K A alpha m N q (f h) by
      unfold g
      rw [if_pos ⟨hpre'', hmod⟩]]
  calc
    _ = ∑ n ∈ S, scaledTrivialPointWeight K A alpha m N q n := by
      simp only [S]
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hfInj hab
    _ = ∑ n ∈ S, g n := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hn
      exact (hgSelected h).symm
    _ ≤ ∑ n ∈ Finset.Icc 0 N, g n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun n _ _ => by
          unfold g
          split_ifs
          · exact scaledTrivialPointWeight_nonneg K A alpha m N q n
          · exact le_rfl)
    _ = _ := by
      unfold scaledTrivialResidueRawWeight g scaledTrivialPointWeight
      rfl

/-! ### Finite global assembly for fibrewise residue measures -/

/-- Split the exponential miss sum into an arbitrary exceptional set and a
uniformly covered complement.  This is the exact finite inequality used when
the smooth and endpoint exceptions are handed to fresh primes. -/
theorem sum_exp_neg_le_bad_add_good
    {S B : Finset ℕ} (hBS : B ⊆ S) (coverage : ℕ → ℝ) (t : ℝ)
    (hcoverage : ∀ i ∈ S, 0 ≤ coverage i)
    (hgood : ∀ i ∈ S, i ∉ B → t ≤ coverage i) :
    (∑ i ∈ S, Real.exp (-coverage i)) ≤
      (B.card : ℝ) + ((S \ B).card : ℝ) * Real.exp (-t) := by
  classical
  rw [← Finset.sum_sdiff hBS]
  rw [add_comm]
  apply add_le_add
  · calc
      (∑ i ∈ B, Real.exp (-coverage i)) ≤ ∑ _i ∈ B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hiB
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (hcoverage i (hBS hiB))
      _ = (B.card : ℝ) := by simp
  · calc
      (∑ i ∈ S \ B, Real.exp (-coverage i)) ≤
          ∑ _i ∈ S \ B, Real.exp (-t) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (hgood i (Finset.mem_sdiff.mp hi).1
          (Finset.mem_sdiff.mp hi).2)
      _ = ((S \ B).card : ℝ) * Real.exp (-t) := by simp

/-- Package raw residue weights into `SurvivorCoverData` once a uniform
coverage estimate and a fresh-prime capacity inequality have been proved. -/
theorem exists_survivorCoverData_of_rawWeights_and_good_coverage
    {U y z : ℕ} (P R B : Finset ℕ)
    (hprimeP : ∀ p ∈ P, p.Prime) (hprimeR : ∀ p ∈ R, p.Prime)
    (hsupportP : ∀ p ∈ P, z < p) (hsupportR : ∀ p ∈ R, z < p)
    (hdisjoint : Disjoint P R)
    (weight : ∀ p : ↥P, Fin p.1 → ℝ)
    (hweight : ∀ p a, 0 ≤ weight p a)
    (hsumpos : ∀ p, 0 < ∑ a, weight p a)
    (t : ℝ)
    (hB : B ⊆ initialSieveSurvivors U y z)
    (hgood : ∀ i ∈ initialSieveSurvivors U y z, i ∉ B →
      t ≤ ∑ p : ↥P, ∑ a,
        if i % p.1 = a.1 then normalizedRawMass weight p a else 0)
    (hcapacity :
      (B.card : ℝ) +
          ((initialSieveSurvivors U y z \ B).card : ℝ) * Real.exp (-t) <
        (R.card : ℝ) + 1) :
    ∃ data : SurvivorCoverData U y z,
      data.measurePrimes = P ∧ data.freshPrimes = R := by
  let coverage : ℕ → ℝ := fun i =>
    ∑ p : ↥P, ∑ a,
      if i % p.1 = a.1 then normalizedRawMass weight p a else 0
  have hcoverage : ∀ i ∈ initialSieveSurvivors U y z,
      0 ≤ coverage i := by
    intro i hi
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact normalizedRawMass_nonneg weight hweight p a
    · exact le_rfl
  have hsumexp :
      (∑ i ∈ initialSieveSurvivors U y z,
        Real.exp (-coverage i)) < (R.card : ℝ) + 1 := by
    exact (sum_exp_neg_le_bad_add_good hB coverage t hcoverage
      (by simpa [coverage] using hgood)).trans_lt hcapacity
  let data := SurvivorCoverData.ofRawWeights P R hprimeP hprimeR
    hsupportP hsupportR hdisjoint weight hweight hsumpos (by
      simpa [coverage] using hsumexp)
  exact ⟨data, rfl, rfl⟩

/-- Push a probability distribution on the prime factor `p (mod q)` to the
residue of the actual offset `m*p (mod q)`. -/
noncomputable def pushResidueMass (m q : ℕ) (μ : Fin q → ℝ)
    (b : Fin q) : ℝ :=
  ∑ a : Fin q, if (m * a.1) % q = b.1 then μ a else 0

theorem pushResidueMass_nonneg {m q : ℕ} {μ : Fin q → ℝ}
    (hμ : ∀ a, 0 ≤ μ a) (b : Fin q) :
    0 ≤ pushResidueMass m q μ b := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact hμ a
  · exact le_rfl

theorem sum_pushResidueMass {m q : ℕ} (hq : 0 < q)
    (μ : Fin q → ℝ) :
    ∑ b : Fin q, pushResidueMass m q μ b = ∑ a : Fin q, μ a := by
  classical
  unfold pushResidueMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  let b : Fin q := ⟨(m * a.1) % q, Nat.mod_lt _ hq⟩
  rw [Finset.sum_eq_single b]
  · simp [b]
  · intro x hx hxb
    have hne : (m * a.1) % q ≠ x.1 := by
      intro heq
      apply hxb
      exact Fin.ext heq.symm
    simp [hne]
  · simp

theorem residueMass_le_pushResidueMass_hit
    {m q p : ℕ} (hq : 0 < q) (μ : Fin q → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) :
    μ ⟨p % q, Nat.mod_lt p hq⟩ ≤
      pushResidueMass m q μ
        ⟨(m * p) % q, Nat.mod_lt (m * p) hq⟩ := by
  classical
  unfold pushResidueMass
  let a₀ : Fin q := ⟨p % q, Nat.mod_lt p hq⟩
  let f : Fin q → ℝ := fun a =>
    if (m * a.1) % q = (m * p) % q then μ a else 0
  have hterm : f a₀ = μ a₀ := by
    dsimp [f]
    rw [if_pos]
    simp [a₀, Nat.mul_mod]
  change μ a₀ ≤ ∑ a, f a
  rw [← hterm]
  apply Finset.single_le_sum (fun a ha => by
    dsimp [f]
    split_ifs
    · exact hμ a
    · exact le_rfl) (Finset.mem_univ _)

noncomputable def scaledTrivialOffsetResidueMass
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (b : Fin q) : ℝ :=
  pushResidueMass m q (scaledTrivialResidueMass K A alpha m N q) b

theorem scaledTrivialOffsetResidueMass_nonneg
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (b : Fin q) :
    0 ≤ scaledTrivialOffsetResidueMass K A alpha m N q b := by
  exact pushResidueMass_nonneg
    (fun a => scaledTrivialResidueMass_nonneg K A alpha m N q a) b

theorem sum_scaledTrivialOffsetResidueMass_eq_one
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (hq : 0 < q)
    (hmass : 0 < scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N) :
    ∑ b : Fin q, scaledTrivialOffsetResidueMass K A alpha m N q b = 1 := by
  unfold scaledTrivialOffsetResidueMass
  rw [sum_pushResidueMass hq]
  exact sum_scaledTrivialResidueMass_eq_one K A alpha
    (fun _ => m) (fun _ => q) N hq hmass

theorem scaledTrivialResidueMass_le_offset_hit
    (K : ℕ) (A alpha : ℝ) (m N q p : ℕ) (hq : 0 < q) :
    scaledTrivialResidueMass K A alpha m N q
        ⟨p % q, Nat.mod_lt p hq⟩ ≤
      scaledTrivialOffsetResidueMass K A alpha m N q
        ⟨(m * p) % q, Nat.mod_lt (m * p) hq⟩ := by
  exact residueMass_le_pushResidueMass_hit hq _
    (fun a => scaledTrivialResidueMass_nonneg K A alpha m N q a)

end

end Erdos4
