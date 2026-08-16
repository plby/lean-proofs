import Wikipedia.GreenTao.Sieve.ComplexLocalFactorControl
import Wikipedia.GreenTao.Sieve.FourierZetaParameters

/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic finite-product second-order remainder -/

/-- The part of `∏ q, (1 + e q)` supported on subsets of cardinality at
least two. -/
noncomputable def complexProductHigherOrderRemainder
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ → ℂ) : ℂ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ∏ q ∈ s, e q

/-- Exact separation of the empty, singleton, and higher-order supports in
a finite product. -/
theorem fintype_prod_one_add_eq_firstOrder_add_remainder
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ → ℂ) :
    (∏ q, (1 + e q)) =
      1 + ∑ q, e q +
        complexProductHigherOrderRemainder e := by
  let u : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℂ :=
    fun s => ∏ q ∈ s, e q
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      u (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ u.filter (fun s => ¬ 2 ≤ s.card),
        term s) =
        1 + ∑ q, e q := by
    rw [show u.filter (fun s => ¬ 2 ≤ s.card) =
        (Finset.univ : Finset κ).powerset.filter
          (fun s => ¬ 2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two_complex]
    simp [term]
  rw [Finset.prod_one_add]
  change (∑ s ∈ u, term s) =
    1 + ∑ q, e q +
      complexProductHigherOrderRemainder e
  rw [← hsplit, hlow]
  unfold complexProductHigherOrderRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s) +
        (1 + ∑ q, e q) =
      1 + ∑ q, e q +
        ∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s
  ac_rfl

/-- If every `e q` has norm at most `B ≤ 1`, the supports of size at least
two contribute at most `2^m B²`. -/
theorem norm_complexProductHigherOrderRemainder_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : κ → ℂ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (he : ∀ q, ‖e q‖ ≤ B) :
    ‖complexProductHigherOrderRemainder e‖ ≤
      (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
  have hcard :
      (higherOrderSelectedSupports κ).card ≤
        2 ^ Fintype.card κ := by
    calc
      (higherOrderSelectedSupports κ).card ≤
          ((Finset.univ : Finset κ).powerset).card := by
        apply Finset.card_le_card
        intro s hs
        exact Finset.mem_powerset.mpr
          ((Finset.mem_filter.mp hs).1 |>
            Finset.mem_powerset.mp)
      _ = 2 ^ Fintype.card κ := by
        rw [Finset.card_powerset]
        simp
  unfold complexProductHigherOrderRemainder
  calc
    ‖∑ s ∈ higherOrderSelectedSupports κ,
        ∏ q ∈ s, e q‖ ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          ‖∏ q ∈ s, e q‖ :=
      norm_sum_le
        (higherOrderSelectedSupports κ)
        (fun s => ∏ q ∈ s, e q)
    _ ≤
        ∑ _s ∈ higherOrderSelectedSupports κ,
          B ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hs2 : 2 ≤ s.card :=
        (mem_higherOrderSelectedSupports s).mp hs
      rw [norm_prod]
      calc
        (∏ q ∈ s, ‖e q‖) ≤ B ^ s.card :=
          (Finset.prod_le_prod
            (fun q _hq => norm_nonneg (e q))
            (fun q _hq => he q)).trans_eq (by
              simp)
        _ ≤ B ^ 2 :=
          pow_le_pow_of_le_one hB0 hB1 hs2
    _ =
        ((higherOrderSelectedSupports κ).card : ℝ) *
          B ^ 2 := by
      simp
    _ ≤
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity

/-- Abstract finite-product comparison.  Each factor is allowed a
first-order error `D`; the products of two or more factor errors are
controlled by `B²`. -/
theorem norm_fintypeProd_sub_combinedFirstOrder_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q a : κ → ℂ) (r : ℂ)
    {B D : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hQ : ∀ q, ‖Q q - 1‖ ≤ B)
    (hlinear :
      ∀ q, ‖Q q - (1 - r * a q)‖ ≤ D) :
    ‖(∏ q, Q q) -
        (1 - r * ∑ q, a q)‖ ≤
      Fintype.card κ * D +
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
  let e : κ → ℂ := fun q => Q q - 1
  have hprod :
      (∏ q, Q q) =
        1 + ∑ q, e q +
          complexProductHigherOrderRemainder e := by
    rw [show Q = fun q => 1 + e q by
      funext q
      simp [e]]
    exact fintype_prod_one_add_eq_firstOrder_add_remainder e
  have hsum :
      ‖∑ q, (e q + r * a q)‖ ≤
        Fintype.card κ * D := by
    calc
      ‖∑ q, (e q + r * a q)‖ ≤
          ∑ q, ‖e q + r * a q‖ :=
        norm_sum_le Finset.univ
          (fun q => e q + r * a q)
      _ ≤ ∑ _q : κ, D := by
        apply Finset.sum_le_sum
        intro q _hq
        have hrewrite :
            e q + r * a q =
              Q q - (1 - r * a q) := by
          simp [e]
          ring
        rw [hrewrite]
        exact hlinear q
      _ = Fintype.card κ * D := by
        simp
  have hrem :
      ‖complexProductHigherOrderRemainder e‖ ≤
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 :=
    norm_complexProductHigherOrderRemainder_le
      hB0 hB1 (fun q => by simpa [e] using hQ q)
  rw [hprod]
  have hrearrange :
      (1 + ∑ q, e q +
          complexProductHigherOrderRemainder e) -
          (1 - r * ∑ q, a q) =
        (∑ q, (e q + r * a q)) +
          complexProductHigherOrderRemainder e := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hrearrange]
  exact
    (norm_add_le _ _).trans
      (add_le_add hsum hrem)

/-! ## One paired phase -/

/-- First-order local model for one pair of phases. -/
noncomputable def phasePairFirstOrderLocalModel
    (p : ℕ) (z w : ℂ) : ℂ :=
  1 - (p : ℂ)⁻¹ * (z + w - z * w)

/-- Exact local Euler factor of one zeta quotient, written in its
phase coordinates. -/
noncomputable def phasePairZetaEulerLocalModel
    (p : ℕ) (z w : ℂ) : ℂ :=
  ((1 - (p : ℂ)⁻¹ * z) *
      (1 - (p : ℂ)⁻¹ * w)) /
    (1 - (p : ℂ)⁻¹ * z * w)

/-- The zeta-model denominator has norm at least one half at a prime when
both phases lie in the unit ball. -/
theorem one_half_le_norm_phasePairZetaDenominator
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (1 : ℝ) / 2 ≤
      ‖1 - (p : ℂ)⁻¹ * z * w‖ := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hinv :
      ‖(p : ℂ)⁻¹ * z * w‖ ≤
        (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z * w‖ =
          (1 / (p : ℝ)) * ‖z‖ * ‖w‖ := by
        rw [norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 * 1 := by
        gcongr
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  calc
    (1 : ℝ) / 2 ≤
        1 - ‖(p : ℂ)⁻¹ * z * w‖ := by
      linarith
    _ =
        ‖(1 : ℂ)‖ -
          ‖(p : ℂ)⁻¹ * z * w‖ := by
      rw [norm_one]
    _ ≤
        ‖1 - (p : ℂ)⁻¹ * z * w‖ :=
      norm_sub_norm_le _ _

theorem phasePairZetaDenominator_ne_zero
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    1 - (p : ℂ)⁻¹ * z * w ≠ 0 := by
  exact norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (one_half_le_norm_phasePairZetaDenominator
        hp hz hw))

/-- Exact second-order cancellation between the zeta Euler factor and its
first-order truncation. -/
theorem phasePairZetaEulerLocalModel_sub_firstOrder_eq
    {p : ℕ} {z w : ℂ}
    (hden : 1 - (p : ℂ)⁻¹ * z * w ≠ 0) :
    phasePairZetaEulerLocalModel p z w -
        phasePairFirstOrderLocalModel p z w =
      ((p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)) /
        (1 - (p : ℂ)⁻¹ * z * w) := by
  rw [phasePairZetaEulerLocalModel,
    phasePairFirstOrderLocalModel]
  apply (eq_div_iff hden).2
  rw [sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- Uniform one-pair difference estimate. -/
theorem norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖phasePairZetaEulerLocalModel p z w -
        phasePairFirstOrderLocalModel p z w‖ ≤
      (8 : ℝ) / (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hdenHalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hw
  have hdenPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * w‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdenHalf
  have hzsub : ‖1 - z‖ ≤ 2 := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one]
        linarith
  have hwsub : ‖1 - w‖ ≤ 2 := by
    calc
      ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one]
        linarith
  have hnum :
      ‖(p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)‖ ≤
        (4 : ℝ) / (p : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul,
      norm_pow, norm_inv, Complex.norm_natCast]
    have hinv0 : 0 ≤ ((p : ℝ)⁻¹) ^ 2 := by
      positivity
    calc
      ((p : ℝ)⁻¹) ^ 2 * ‖z‖ * ‖w‖ *
          ‖1 - z‖ * ‖1 - w‖ ≤
          ((p : ℝ)⁻¹) ^ 2 * 1 * 1 * 2 * 2 := by
        gcongr
      _ = (4 : ℝ) / (p : ℝ) ^ 2 := by
        field_simp
        ring
  rw [phasePairZetaEulerLocalModel_sub_firstOrder_eq
    (phasePairZetaDenominator_ne_zero hp hz hw),
    Complex.norm_div]
  calc
    ‖(p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)‖ /
          ‖1 - (p : ℂ)⁻¹ * z * w‖ ≤
        2 *
          ‖(p : ℂ)⁻¹ ^ 2 * z * w *
            (1 - z) * (1 - w)‖ := by
      rw [div_le_iff₀ hdenPos]
      have hnonneg :
          0 ≤
            ‖(p : ℂ)⁻¹ ^ 2 * z * w *
              (1 - z) * (1 - w)‖ :=
        norm_nonneg _
      nlinarith
    _ ≤ 2 * ((4 : ℝ) / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    _ = (8 : ℝ) / (p : ℝ) ^ 2 := by
      ring

/-- Each one-pair zeta factor differs from one by at most `7/p`. -/
theorem norm_phasePairZetaEulerLocalModel_sub_one_le
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖phasePairZetaEulerLocalModel p z w - 1‖ ≤
      (7 : ℝ) / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hcoeff :
      ‖z + w - z * w‖ ≤ 3 :=
    norm_add_sub_mul_le_three hz hw
  have hfirst :
      ‖phasePairFirstOrderLocalModel p z w - 1‖ ≤
        (3 : ℝ) / (p : ℝ) := by
    rw [phasePairFirstOrderLocalModel]
    have hrearrange :
        1 - (p : ℂ)⁻¹ * (z + w - z * w) - 1 =
          -(p : ℂ)⁻¹ * (z + w - z * w) := by
      ring
    rw [hrearrange, norm_mul, norm_neg, norm_inv,
      Complex.norm_natCast]
    exact
      (mul_le_mul_of_nonneg_left hcoeff
        (inv_nonneg.mpr hpR.le)).trans_eq (by
          ring)
  have hsecond :=
    norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
      hp hz hw
  calc
    ‖phasePairZetaEulerLocalModel p z w - 1‖ ≤
        ‖phasePairZetaEulerLocalModel p z w -
            phasePairFirstOrderLocalModel p z w‖ +
          ‖phasePairFirstOrderLocalModel p z w - 1‖ := by
      have hsum :
          phasePairZetaEulerLocalModel p z w - 1 =
            (phasePairZetaEulerLocalModel p z w -
              phasePairFirstOrderLocalModel p z w) +
            (phasePairFirstOrderLocalModel p z w - 1) := by
        ring
      rw [hsum]
      exact norm_add_le _ _
    _ ≤
        (8 : ℝ) / (p : ℝ) ^ 2 +
          (3 : ℝ) / (p : ℝ) :=
      add_le_add hsecond hfirst
    _ ≤ (7 : ℝ) / (p : ℝ) := by
      have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast hp.two_le
      field_simp
      nlinarith

/-! ## Exact cpow coordinates -/

/-- The per-form local Euler factor of the zeta quotient in complex-power
coordinates. -/
noncomputable def pairedZetaEulerLocalFactor
    (p : ℕ) (u v : ℂ) : ℂ :=
  ((1 - (p : ℂ) ^ (-((1 : ℂ) + u))) *
      (1 - (p : ℂ) ^ (-((1 : ℂ) + v)))) /
    (1 - (p : ℂ) ^
      (-((1 : ℂ) + u + v)))

/-- Pull the `p⁻¹` term out of a shifted negative complex power. -/
theorem natCast_cpow_neg_one_add
    {p : ℕ} (hp : p ≠ 0) (u : ℂ) :
    (p : ℂ) ^ (-((1 : ℂ) + u)) =
      (p : ℂ)⁻¹ * (p : ℂ) ^ (-u) := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp
  rw [show -((1 : ℂ) + u) =
      (-1 : ℂ) + (-u) by ring,
    Complex.cpow_add _ _ hpC,
    Complex.cpow_neg_one]

/-- The analogous identity for the denominator shift `1 + u + v`. -/
theorem natCast_cpow_neg_one_add_add
    {p : ℕ} (hp : p ≠ 0) (u v : ℂ) :
    (p : ℂ) ^ (-((1 : ℂ) + u + v)) =
      (p : ℂ)⁻¹ *
        (p : ℂ) ^ (-u) *
          (p : ℂ) ^ (-v) := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp
  rw [show -((1 : ℂ) + u + v) =
      (-1 : ℂ) + ((-u) + (-v)) by ring,
    Complex.cpow_add _ _ hpC,
    Complex.cpow_neg_one,
    Complex.cpow_add _ _ hpC]
  ring

/-- The cpow zeta factor is exactly the elementary phase-coordinate
factor. -/
theorem pairedZetaEulerLocalFactor_eq_phase
    {p : ℕ} (hp : p ≠ 0) (u v : ℂ) :
    pairedZetaEulerLocalFactor p u v =
      phasePairZetaEulerLocalModel p
        ((p : ℂ) ^ (-u))
        ((p : ℂ) ^ (-v)) := by
  rw [pairedZetaEulerLocalFactor,
    phasePairZetaEulerLocalModel,
    natCast_cpow_neg_one_add hp,
    natCast_cpow_neg_one_add hp,
    natCast_cpow_neg_one_add_add hp]

/-- Per-form zeta Euler factor at the exact Fourier shifts fixed by
`FourierZetaParameters`. -/
noncomputable def fourierPairZetaEulerLocalFactor
    (R p : ℕ) (t u : ℝ) : ℂ :=
  pairedZetaEulerLocalFactor p
    (cutoffZetaShift R t)
    (cutoffZetaShift R u)

/-- Exact identification of the cpow factor with the two divisor phases.
This is where the sign and `2π` normalization enter. -/
theorem fourierPairZetaEulerLocalFactor_eq_phase
    {R p : ℕ} (hR : 1 < R) (hp : p.Prime)
    (t u : ℝ) :
    fourierPairZetaEulerLocalFactor R p t u =
      phasePairZetaEulerLocalModel p
        (SmoothSieveCutoff.divisorMultiplicativePhase
          R p t)
        (SmoothSieveCutoff.divisorMultiplicativePhase
          R p u) := by
  rw [fourierPairZetaEulerLocalFactor,
    pairedZetaEulerLocalFactor_eq_phase hp.ne_zero,
    ← divisorMultiplicativePhase_eq_cpow hR hp.pos t,
    ← divisorMultiplicativePhase_eq_cpow hR hp.pos u]

/-! ## Finite systems -/

/-- Product of the elementary phase-coordinate zeta Euler factors for a
finite system. -/
noncomputable def phaseZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z w : κ → ℂ) : ℂ :=
  ∏ q, phasePairZetaEulerLocalModel p (z q) (w q)

/-- Product of the exact cpow zeta Euler factors for all paired Fourier
parameters. -/
noncomputable def fourierZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R p : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ q, fourierPairZetaEulerLocalFactor
    R p (t q) (u q)

/-- Exact conversion of the system cpow model to phase coordinates. -/
theorem fourierZetaSystemEulerLocalFactor_eq_phase
    {κ : Type*} [Fintype κ]
    {R p : ℕ} (hR : 1 < R) (hp : p.Prime)
    (t u : κ → ℝ) :
    fourierZetaSystemEulerLocalFactor R p t u =
      phaseZetaSystemEulerLocalFactor p
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R p (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R p (u q)) := by
  apply Finset.prod_congr rfl
  intro q _hq
  exact fourierPairZetaEulerLocalFactor_eq_phase
    hR hp (t q) (u q)

/-- Explicit finite-system difference constant. -/
noncomputable def complexZetaModelDifferenceConstant
    (m : ℕ) : ℝ :=
  8 * m + 49 * (2 : ℝ) ^ m

theorem complexZetaModelDifferenceConstant_nonneg
    (m : ℕ) :
    0 ≤ complexZetaModelDifferenceConstant m := by
  rw [complexZetaModelDifferenceConstant]
  positivity

/-- The product of the per-form zeta factors differs from the combined
first-order model by `O_m(p⁻²)`. -/
theorem norm_phaseZetaSystemEulerLocalFactor_sub_firstOrder_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p : ℕ} (hp : p.Prime) (hseven : 7 ≤ p)
    (z w : κ → ℂ)
    (hz : ∀ q, ‖z q‖ ≤ 1)
    (hw : ∀ q, ‖w q‖ ≤ 1) :
    ‖phaseZetaSystemEulerLocalFactor p z w -
        complexFirstOrderLocalModel p
          (fun q => z q + w q - z q * w q)‖ ≤
      complexZetaModelDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsevenR : (7 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hseven
  have habstract :=
    norm_fintypeProd_sub_combinedFirstOrder_le
      (Q := fun q =>
        phasePairZetaEulerLocalModel p (z q) (w q))
      (a := fun q => z q + w q - z q * w q)
      ((p : ℂ)⁻¹)
      (B := (7 : ℝ) / (p : ℝ))
      (D := (8 : ℝ) / (p : ℝ) ^ 2)
      (by positivity)
      (by
        rw [div_le_one hpR]
        exact hsevenR)
      (fun q =>
        norm_phasePairZetaEulerLocalModel_sub_one_le
          hp (hz q) (hw q))
      (fun q => by
        simpa [phasePairFirstOrderLocalModel] using
          (norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
            hp (hz q) (hw q)))
  have hright :
      Fintype.card κ * ((8 : ℝ) / (p : ℝ) ^ 2) +
          (2 : ℝ) ^ Fintype.card κ *
            ((7 : ℝ) / (p : ℝ)) ^ 2 =
        complexZetaModelDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    rw [complexZetaModelDifferenceConstant]
    ring
  have hleft :
      (1 - (p : ℂ)⁻¹ *
          ∑ q : κ, (z q + w q - z q * w q)) =
        complexFirstOrderLocalModel p
          (fun q => z q + w q - z q * w q) := by
    rw [complexFirstOrderLocalModel]
    simp only [div_eq_mul_inv]
    ring
  rw [phaseZetaSystemEulerLocalFactor, ← hleft]
  exact habstract.trans_eq hright

/-- Fourier-uniform version of the finite-system difference estimate. -/
theorem norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hseven : 7 ≤ p)
    (t u : κ → ℝ) :
    ‖fourierZetaSystemEulerLocalFactor R p t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      complexZetaModelDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  rw [fourierZetaSystemEulerLocalFactor_eq_phase
    (by omega) hp]
  exact norm_phaseZetaSystemEulerLocalFactor_sub_firstOrder_le
    hp hseven _ _
    (fun q =>
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR hp (t q))
    (fun q =>
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR hp (u q))

/-- Ratio of the zeta Euler model to the combined first-order model. -/
noncomputable def fourierZetaToFirstOrderLocalRatio
    {κ : Type*} [Fintype κ]
    (R p : ℕ) (t u : κ → ℝ) : ℂ :=
  fourierZetaSystemEulerLocalFactor R p t u /
    pairedFourierFirstOrderLocalModel R p t u

/-- Explicit error constant for the zeta/first-order ratio. -/
noncomputable def complexZetaModelRatioErrorConstant
    (m : ℕ) : ℝ :=
  2 * complexZetaModelDifferenceConstant m

theorem complexZetaModelRatioErrorConstant_nonneg
    (m : ℕ) :
    0 ≤ complexZetaModelRatioErrorConstant m := by
  rw [complexZetaModelRatioErrorConstant,
    complexZetaModelDifferenceConstant]
  positivity

/-- The zeta-model/first-order ratio is `1 + O_m(p⁻²)`, uniformly in all
Fourier parameters. -/
theorem norm_fourierZetaToFirstOrderLocalRatio_sub_one_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hseven : 7 ≤ p)
    (hcard : 6 * Fintype.card κ ≤ p)
    (t u : κ → ℝ) :
    ‖fourierZetaToFirstOrderLocalRatio R p t u - 1‖ ≤
      complexZetaModelRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let model :=
    pairedFourierFirstOrderLocalModel R p t u
  have hmodelHalf :
      (1 : ℝ) / 2 ≤ ‖model‖ := by
    exact one_half_le_norm_complexFirstOrderLocalModel
      hp hcard
      (fun q =>
        norm_pairedFourierPrimeCoefficient_le_three
          hR hp (t q) (u q))
  have hmodelPos : 0 < ‖model‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hmodelHalf
  have hdiff :
      ‖fourierZetaSystemEulerLocalFactor R p t u -
          model‖ ≤
        complexZetaModelDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    simpa [model] using
      norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
        hR hp hseven t u
  have hmodelNe : model ≠ 0 :=
    norm_pos_iff.mp hmodelPos
  rw [fourierZetaToFirstOrderLocalRatio,
    div_sub_one hmodelNe, Complex.norm_div]
  calc
    ‖fourierZetaSystemEulerLocalFactor R p t u -
          model‖ / ‖model‖ ≤
        2 *
          ‖fourierZetaSystemEulerLocalFactor R p t u -
            model‖ := by
      rw [div_le_iff₀ hmodelPos]
      have hnonneg :
          0 ≤
            ‖fourierZetaSystemEulerLocalFactor R p t u -
              model‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        2 *
          (complexZetaModelDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexZetaModelRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexZetaModelRatioErrorConstant]
      ring

/-- Single explicit numerical cutoff for the system comparison. -/
def complexZetaModelComparisonCutoff (m : ℕ) : ℕ :=
  max 7 (6 * m)

/-- Cutoff-packaged form of the uniform ratio estimate. -/
theorem norm_fourierZetaToFirstOrderLocalRatio_sub_one_le_of_cutoff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hcut :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖fourierZetaToFirstOrderLocalRatio R p t u - 1‖ ≤
      complexZetaModelRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  exact norm_fourierZetaToFirstOrderLocalRatio_sub_one_le
    hR hp
    ((Nat.le_max_left _ _).trans hcut)
    ((Nat.le_max_right _ _).trans hcut)
    t u

/-! ## Direct arithmetic/zeta comparison -/

/-- Difference constant after combining the affine local calculation with
the zeta-model comparison. -/
noncomputable def complexArithmeticZetaDifferenceConstant
    (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m +
    complexZetaModelDifferenceConstant m

theorem complexArithmeticZetaDifferenceConstant_nonneg
    (m : ℕ) :
    0 ≤ complexArithmeticZetaDifferenceConstant m := by
  rw [complexArithmeticZetaDifferenceConstant,
    complexZetaModelDifferenceConstant]
  positivity

/-- The actual affine local factor and the exact cpow zeta Euler model
differ by `O_m(p⁻²)`. -/
theorem norm_pairedFourierLocalFactor_sub_zetaModel_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hseven : 7 ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p forms t u -
        fourierZetaSystemEulerLocalFactor R p t u‖ ≤
      complexArithmeticZetaDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  have harithmetic :=
    norm_pairedFourierLocalFactor_sub_firstOrder_le
      hnonzero hindependent hR hp hlarge t u
  have hzeta :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hp hseven t u
  have htriangle :
      ‖pairedFourierLocalFactor R p forms t u -
          fourierZetaSystemEulerLocalFactor R p t u‖ ≤
        ‖pairedFourierLocalFactor R p forms t u -
            pairedFourierFirstOrderLocalModel R p t u‖ +
          ‖fourierZetaSystemEulerLocalFactor R p t u -
            pairedFourierFirstOrderLocalModel R p t u‖ := by
    have hrearrange :
        pairedFourierLocalFactor R p forms t u -
            fourierZetaSystemEulerLocalFactor R p t u =
          (pairedFourierLocalFactor R p forms t u -
              pairedFourierFirstOrderLocalModel R p t u) -
            (fourierZetaSystemEulerLocalFactor R p t u -
              pairedFourierFirstOrderLocalModel R p t u) := by
      ring
    rw [hrearrange]
    exact norm_sub_le _ _
  calc
    ‖pairedFourierLocalFactor R p forms t u -
        fourierZetaSystemEulerLocalFactor R p t u‖ ≤
        ‖pairedFourierLocalFactor R p forms t u -
            pairedFourierFirstOrderLocalModel R p t u‖ +
          ‖fourierZetaSystemEulerLocalFactor R p t u -
            pairedFourierFirstOrderLocalModel R p t u‖ :=
      htriangle
    _ ≤
        (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2 +
          complexZetaModelDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2 :=
      add_le_add harithmetic hzeta
    _ =
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaDifferenceConstant]
      ring

/-- A natural-valued copy of the zeta-model difference constant, used only
to state a numerical stability cutoff. -/
def complexZetaModelDifferenceNat (m : ℕ) : ℕ :=
  8 * m + 49 * 2 ^ m

theorem complexZetaModelDifferenceConstant_eq_natCast
    (m : ℕ) :
    complexZetaModelDifferenceConstant m =
      (complexZetaModelDifferenceNat m : ℝ) := by
  rw [complexZetaModelDifferenceConstant,
    complexZetaModelDifferenceNat]
  push_cast
  ring

/-- A cutoff large enough both for the first-order stability estimates and
to keep the exact zeta model at norm at least `1/4`. -/
def complexZetaModelNonzeroCutoff (m : ℕ) : ℕ :=
  max
    (complexZetaModelComparisonCutoff m)
    (4 * complexZetaModelDifferenceNat m)

/-- Above the stability cutoff, the exact finite-system zeta Euler model
has norm at least one quarter. -/
theorem one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    (1 : ℝ) / 4 ≤
      ‖fourierZetaSystemEulerLocalFactor R p t u‖ := by
  let m := Fintype.card κ
  let model :=
    pairedFourierFirstOrderLocalModel R p t u
  have hcomparison :
      complexZetaModelComparisonCutoff m ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hcard :
      6 * m ≤ p :=
    (Nat.le_max_right 7 (6 * m)).trans
      hcomparison
  have hfirst :
      (1 : ℝ) / 2 ≤ ‖model‖ := by
    exact one_half_le_norm_complexFirstOrderLocalModel
      hp hcard
      (fun q =>
        norm_pairedFourierPrimeCoefficient_le_three
          hR hp (t q) (u q))
  have hdiff :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hp
      ((Nat.le_max_left 7 (6 * m)).trans
        hcomparison)
      t u
  have hCnat :
      4 * complexZetaModelDifferenceNat m ≤ p :=
    (Nat.le_max_right
      (complexZetaModelComparisonCutoff m)
      (4 * complexZetaModelDifferenceNat m)).trans
        hcut
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hCcast :
      4 * (complexZetaModelDifferenceNat m : ℝ) ≤
        (p : ℝ) := by
    exact_mod_cast hCnat
  have hpSq :
      (p : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith
  have hsmall :
      complexZetaModelDifferenceConstant m /
          (p : ℝ) ^ 2 ≤
        (1 : ℝ) / 4 := by
    rw [complexZetaModelDifferenceConstant_eq_natCast]
    rw [div_le_iff₀ (sq_pos_of_pos hpR)]
    nlinarith
  have hdiffQuarter :
      ‖fourierZetaSystemEulerLocalFactor R p t u -
          model‖ ≤ (1 : ℝ) / 4 :=
    hdiff.trans hsmall
  calc
    (1 : ℝ) / 4 ≤
        ‖model‖ -
          ‖model -
            fourierZetaSystemEulerLocalFactor R p t u‖ := by
      rw [norm_sub_rev]
      linarith
    _ ≤
        ‖model -
          (model -
            fourierZetaSystemEulerLocalFactor R p t u)‖ :=
      norm_sub_norm_le _ _
    _ =
        ‖fourierZetaSystemEulerLocalFactor R p t u‖ := by
      congr 1
      ring

/-- Direct ratio of the arithmetic affine local factor to the exact zeta
Euler model. -/
noncomputable def pairedFourierArithmeticToZetaLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) : ℂ :=
  pairedFourierLocalFactor R p forms t u /
    fourierZetaSystemEulerLocalFactor R p t u

/-- Error constant for the direct arithmetic/zeta ratio. -/
noncomputable def complexArithmeticZetaRatioErrorConstant
    (m : ℕ) : ℝ :=
  4 * complexArithmeticZetaDifferenceConstant m

theorem complexArithmeticZetaRatioErrorConstant_nonneg
    (m : ℕ) :
    0 ≤ complexArithmeticZetaRatioErrorConstant m := by
  rw [complexArithmeticZetaRatioErrorConstant,
    complexArithmeticZetaDifferenceConstant,
    complexZetaModelDifferenceConstant]
  positivity

/-- The direct arithmetic/zeta ratio is `1 + O_m(p⁻²)` above the explicit
rank, size, and nonvanishing cutoffs. -/
theorem norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio
          R p forms t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let zeta :=
    fourierZetaSystemEulerLocalFactor R p t u
  have hzetaQuarter :
      (1 : ℝ) / 4 ≤ ‖zeta‖ := by
    exact one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
      hR hp hcut t u
  have hzetaPos : 0 < ‖zeta‖ :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      hzetaQuarter
  have hcomparison :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hdiff :
      ‖pairedFourierLocalFactor R p forms t u -
          zeta‖ ≤
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    simpa [zeta] using
      norm_pairedFourierLocalFactor_sub_zetaModel_le
        hnonzero hindependent hR hp hlarge
        ((Nat.le_max_left 7
          (6 * Fintype.card κ)).trans hcomparison)
        t u
  have hzetaNe : zeta ≠ 0 :=
    norm_pos_iff.mp hzetaPos
  rw [pairedFourierArithmeticToZetaLocalRatio,
    div_sub_one hzetaNe, Complex.norm_div]
  calc
    ‖pairedFourierLocalFactor R p forms t u - zeta‖ /
          ‖zeta‖ ≤
        4 *
          ‖pairedFourierLocalFactor R p forms t u - zeta‖ := by
      rw [div_le_iff₀ hzetaPos]
      have hnonneg :
          0 ≤
            ‖pairedFourierLocalFactor R p forms t u - zeta‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        4 *
          (complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaRatioErrorConstant]
      ring

end Wikipedia.SzemeredisTheorem
