import Wikipedia.GreenTao.Parameters
import Wikipedia.GreenTao.Sieve.CFZCanonicalCyclicBoundaryLimit
import Wikipedia.GreenTao.Sieve.CFZCarryFourierEulerNormalization

/-!
# Fixed-primorial Fourier schedules

The Green--Tao parameter order first chooses a large primorial cutoff `w`
and then lets the cyclic modulus tend to infinity.  This file records the
analytic consequences of that order for the concrete sieve level
`sieveLevel k N`.

For fixed `w`, the conventional Fourier radius

`T N = sqrt (log (sieveLevel k N))`

is already small enough for the finite small-prime correction.  Indeed its
quadratic error scale is `O_w(1 / log (sieveLevel k N))`.  Thus no smaller
sub-box is needed.

The large-prime correction has a different quantifier order.  For a fixed
cutoff it need not converge to one as the carry block varies.  What the
uniform prime-square estimate gives, and what the Green--Tao argument
actually uses, is:

`∀ ε > 0, ∃ w₀, ∀ carry blocks with w ≥ w₀, ‖largeCorrection - 1‖ < ε`.

The results below record the fixed-`w` limits and this uniform tail
statement side by side, together with a completed-correction wrapper that
isolates the exact remaining large-prime hypothesis.  They deliberately do
not assert a false fixed-`w` limit for the actual carry correction.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## The fixed-primorial phase scale -/

/-- The conventional Fourier box continues to grow after the natural
radius is evaluated at the floored Green--Tao sieve level. -/
theorem tendsto_sqrt_log_sieveLevel_atTop
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun N =>
        Real.sqrt (Real.log (sieveLevel k N)))
      atTop atTop :=
  SmoothSieveCutoff.tendsto_sqrt_log_nat_atTop.comp
    (tendsto_sieveLevel_atTop hk)

/-- At a fixed primorial cutoff, the phase magnitude on the conventional
Fourier box tends to zero along every sieve scale tending to infinity. -/
theorem tendsto_cutoffPhaseMagnitudeBound_sqrt_log_fixed
    (R : ℕ → ℕ) (w : ℕ)
    (hR : Tendsto R atTop atTop) :
    Tendsto
      (fun n =>
        cutoffPhaseMagnitudeBound
          (R n) w (Real.sqrt (Real.log (R n))))
      atTop (𝓝 0) := by
  have hbox :
      Tendsto
        (fun n =>
          (1 + 2 * Real.pi *
              Real.sqrt (Real.log (R n))) /
            Real.log (R n))
        atTop (𝓝 0) :=
    tendsto_fourierZetaBoxRadius_nat.comp hR
  have hscaled :
      Tendsto
        (fun n =>
          Real.log (w : ℝ) *
            ((1 + 2 * Real.pi *
                Real.sqrt (Real.log (R n))) /
              Real.log (R n)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hbox :
        Tendsto
          (fun n =>
            Real.log (w : ℝ) *
              ((1 + 2 * Real.pi *
                  Real.sqrt (Real.log (R n))) /
                Real.log (R n)))
          atTop (𝓝 (Real.log (w : ℝ) * 0)))
  apply hscaled.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [cutoffPhaseMagnitudeBound]
    ring

/-- The exact quadratic scale used by
`tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale` vanishes for a
fixed primorial and the full `sqrt (log R)` Fourier box. -/
theorem tendsto_fixedPrimorialPhaseScale_sqrt_log
    (R : ℕ → ℕ) (w : ℕ)
    (hR : Tendsto R atTop atTop) :
    Tendsto
      (fun n =>
        (((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound
            (R n) w (Real.sqrt (Real.log (R n))) ^ 2))
      atTop (𝓝 0) := by
  have hphase :=
    tendsto_cutoffPhaseMagnitudeBound_sqrt_log_fixed R w hR
  simpa using
    (tendsto_const_nhds.mul (hphase.pow 2) :
      Tendsto
        (fun n =>
          (((w + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
              (R n) w (Real.sqrt (Real.log (R n))) ^ 2))
        atTop (𝓝 (((w + 1 : ℕ) : ℝ) * 0 ^ 2)))

/-- Specialization of the preceding phase calculation to the standard
Green--Tao sieve level. -/
theorem tendsto_fixedPrimorialSievePhaseScale_sqrt_log
    {k : ℕ} (hk : 3 ≤ k) (w : ℕ) :
    Tendsto
      (fun N =>
        (((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound
            (sieveLevel k N) w
              (Real.sqrt (Real.log (sieveLevel k N))) ^ 2))
      atTop (𝓝 0) :=
  tendsto_fixedPrimorialPhaseScale_sqrt_log
    (sieveLevel k) w (tendsto_sieveLevel_atTop hk)

/-! ## Fixed-primorial finite correction limits -/

/-- The normalized correction from the finitely many primes dividing the
fixed primorial tends uniformly to one throughout the conventional growing
Fourier box. -/
theorem tendsto_normalizedSmallPrimeZetaCorrection_sieveLevel_fixed
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        normalizedSmallPrimeZetaCorrection
          (sieveLevel k N) w (t N) (u N))
      atTop (𝓝 1) := by
  apply
    tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
      (sieveLevel k) (fun _ => w)
      (fun N => Real.sqrt (Real.log (sieveLevel k N)))
      t u
  · exact eventually_two_le_sieveLevel hk
  · exact Filter.Eventually.of_forall fun _ => hw
  · exact Filter.Eventually.of_forall fun _ =>
      Real.sqrt_nonneg _
  · exact ht
  · exact hu
  · simpa using
      tendsto_fixedPrimorialSievePhaseScale_sqrt_log hk w

/-- The completed finite zeta factor also tends to one on the same box. -/
theorem tendsto_cutoffZetaSystemFactor_sieveLevel_sqrt_log
    {κ : Type*} [Fintype κ]
    {k : ℕ} (hk : 3 ≤ k)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        cutoffZetaSystemFactor
          (sieveLevel k N) (t N) (u N))
      atTop (𝓝 1) :=
  tendsto_cutoffZetaSystemFactor_on_growing_box
    (sieveLevel k) t u
    (tendsto_sieveLevel_atTop hk) ht hu

/-- The two residual factors controlled solely by the fixed primorial and
the Fourier box converge jointly to one. -/
theorem tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        normalizedSmallPrimeZetaCorrection
            (sieveLevel k N) w (t N) (u N) *
          cutoffZetaSystemFactor
            (sieveLevel k N) (t N) (u N))
      atTop (𝓝 1) := by
  simpa using
    (tendsto_normalizedSmallPrimeZetaCorrection_sieveLevel_fixed
        hk hw t u ht hu).mul
      (tendsto_cutoffZetaSystemFactor_sieveLevel_sqrt_log
        hk t u ht hu)

/-- Concrete fixed-primorial specialization of the completed normalized
Euler correction theorem.  The only remaining limit hypothesis is the
large-prime correction itself.  For an actual carry block at fixed `w`,
that hypothesis should not be asserted in general; the uniform
epsilon-tail theorem below is the honest replacement used by the nested
parameter choice. -/
theorem tendsto_normalizedCompletedFourierEulerCorrection_sieveLevel_fixed
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    (t u : ℕ → κ → ℝ)
    (largeCorrection : ℕ → ℂ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hlarge :
      Tendsto largeCorrection atTop (𝓝 1)) :
    Tendsto
      (fun N =>
        normalizedCompletedFourierEulerCorrection
          (sieveLevel k N) w (t N) (u N)
          (largeCorrection N))
      atTop (𝓝 1) := by
  apply
    tendsto_normalizedCompletedFourierEulerCorrection_one
      (sieveLevel k) (fun _ => w)
      (fun N => Real.sqrt (Real.log (sieveLevel k N)))
      t u largeCorrection
  · exact tendsto_sieveLevel_atTop hk
  · exact eventually_two_le_sieveLevel hk
  · exact Filter.Eventually.of_forall fun _ => hw
  · exact Filter.Eventually.of_forall fun _ =>
      Real.sqrt_nonneg _
  · exact ht
  · exact hu
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · simpa using
      tendsto_fixedPrimorialSievePhaseScale_sqrt_log hk w
  · exact hlarge

/-! ## The honest large-prime tail bridge -/

/-- Uniform threshold form of the carry-block large-prime Euler tail.

This is the fixed-primorial statement needed by the nested Green--Tao
parameter choice.  It is stronger than a statement about one prescribed
sequence: after `w` is large, it controls every selected family, divisor
choice, carry block, residue representative, and pair of Fourier
parameters at once. -/
theorem
    exists_uniform_cutoff_selectedCFZCarryLargePrimeEulerCorrection_close_one
    {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℕ,
      ∀ d : SelectedCFZCarryFourierBlockData k,
        w₀ ≤ d.w →
        2 ≤ d.R →
        ‖d.largePrimeEulerCorrection - 1‖ < ε := by
  by_contra h
  push Not at h
  choose d hdw hdR hfar using h
  have hwtop :
      Tendsto (fun n => (d n).w) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro W
    exact ⟨W, fun n hn => hn.trans (hdw n)⟩
  have hlarge :
      Tendsto
        (fun n => (d n).largePrimeEulerCorrection)
        atTop (𝓝 1) :=
    tendsto_selectedCFZCarryLargePrimeEulerCorrection_one
      hk d hwtop
      (Filter.Eventually.of_forall hdR)
  have hclose :
      ∀ᶠ n in atTop,
        ‖(d n).largePrimeEulerCorrection - 1‖ < ε := by
    have hdist :
        ∀ᶠ n in atTop,
          dist ((d n).largePrimeEulerCorrection) 1 < ε :=
      (Metric.tendsto_nhds.mp hlarge) ε hε
    simpa only [dist_eq_norm] using hdist
  obtain ⟨n, hn⟩ := hclose.exists
  exact (not_lt_of_ge (hfar n)) hn

end Wikipedia.SzemeredisTheorem
