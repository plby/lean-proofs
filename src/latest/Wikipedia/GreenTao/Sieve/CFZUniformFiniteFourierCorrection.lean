import Wikipedia.GreenTao.Sieve.FixedPrimorialSieveSchedule
import Wikipedia.GreenTao.Sieve.CFZCarryFourierBridge

/-!
# Uniform finite Fourier correction on the Green--Tao box

For a fixed primorial cutoff, the small-prime normalization and the
completed finite zeta factor converge jointly to one along every sequence
of Fourier parameters in the box of radius

`sqrt (log (sieveLevel k N))`.

This file upgrades that sequential statement to uniform convergence on
the whole box.  A failure of uniformity would provide cofinally many bad
indices.  Choosing a bad pair at those indices and zero elsewhere gives a
single box-valued sequence contradicting
`tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel`.

The final theorem intersects these estimates over the finite type of
selected CFZ exponents.  No large-prime Euler correction occurs here.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-- For a fixed finite index type and primorial cutoff, the product of the
two finite Fourier corrections is eventually uniformly close to one on
the full Green--Tao Fourier box. -/
theorem
    eventually_uniform_fixedPrimorialFiniteFourierCorrection_sieveLevel
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (t u : κ → ℝ),
        (∀ q,
          |t q| ≤
            Real.sqrt (Real.log (sieveLevel k N))) →
        (∀ q,
          |u q| ≤
            Real.sqrt (Real.log (sieveLevel k N))) →
        ‖normalizedSmallPrimeZetaCorrection
              (sieveLevel k N) w t u *
            cutoffZetaSystemFactor
              (sieveLevel k N) t u -
          1‖ < ε := by
  classical
  let radius : ℕ → ℝ :=
    fun N => Real.sqrt (Real.log (sieveLevel k N))
  let Bad :
      (N : ℕ) →
        (κ → ℝ) → (κ → ℝ) → Prop :=
    fun N t u =>
      (∀ q, |t q| ≤ radius N) ∧
        (∀ q, |u q| ≤ radius N) ∧
          ε ≤
            ‖normalizedSmallPrimeZetaCorrection
                  (sieveLevel k N) w t u *
                cutoffZetaSystemFactor
                  (sieveLevel k N) t u -
              1‖
  let witness :
      ℕ → ((κ → ℝ) × (κ → ℝ)) :=
    fun N =>
      if h : ∃ t u, Bad N t u then
        (Classical.choose h,
          Classical.choose (Classical.choose_spec h))
      else
        (0, 0)
  have witness_spec
      (N : ℕ) (hN : ∃ t u, Bad N t u) :
      Bad N (witness N).1 (witness N).2 := by
    simp only [witness, dif_pos hN]
    exact Classical.choose_spec (Classical.choose_spec hN)
  have hwitness :
      ∀ N q, |(witness N).1 q| ≤ radius N := by
    intro N q
    by_cases hN : ∃ t u, Bad N t u
    · exact (witness_spec N hN).1 q
    · simp [witness, hN, radius]
  have hvitness :
      ∀ N q, |(witness N).2 q| ≤ radius N := by
    intro N q
    by_cases hN : ∃ t u, Bad N t u
    · exact (witness_spec N hN).2.1 q
    · simp [witness, hN, radius]
  have hlimit :
      Tendsto
        (fun N =>
          normalizedSmallPrimeZetaCorrection
                (sieveLevel k N) w
                (witness N).1 (witness N).2 *
              cutoffZetaSystemFactor
                (sieveLevel k N)
                (witness N).1 (witness N).2)
        atTop (𝓝 1) := by
    apply
      tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel
        hk hw
    · exact Filter.Eventually.of_forall hwitness
    · exact Filter.Eventually.of_forall hvitness
  have hclose :
      ∀ᶠ N : ℕ in atTop,
        ‖normalizedSmallPrimeZetaCorrection
              (sieveLevel k N) w
              (witness N).1 (witness N).2 *
            cutoffZetaSystemFactor
              (sieveLevel k N)
              (witness N).1 (witness N).2 -
          1‖ < ε := by
    have hdist :=
      (Metric.tendsto_nhds.mp hlimit) ε hε
    simpa only [dist_eq_norm] using hdist
  rw [eventually_atTop] at hclose ⊢
  obtain ⟨N₀, hN₀⟩ := hclose
  refine ⟨N₀, fun N hN t u ht hu => ?_⟩
  by_contra hfar
  have hbad : Bad N t u := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [radius] using ht
    · simpa only [radius] using hu
    · simpa only [not_lt] using hfar
  have hchosen := witness_spec N ⟨t, u, hbad⟩
  exact
    (not_lt_of_ge hchosen.2.2)
      (hN₀ N hN)

/-- Uniform finite-correction convergence for every selected CFZ exponent
at once.  The canonical exceptional cutoff implies the elementary
`2 ≤ w` hypothesis needed by the fixed-primorial schedule. -/
theorem
    eventually_uniform_selectedCFZFiniteFourierCorrection_sieveLevel
    {k w : ℕ} (hk : 3 ≤ k)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ e : LinearFormsExponent k,
        ∀ tu ∈
            SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt
                (Real.log (sieveLevel k N))),
          ‖normalizedSmallPrimeZetaCorrection
                (sieveLevel k N) w tu.1 tu.2 *
              cutoffZetaSystemFactor
                (sieveLevel k N) tu.1 tu.2 -
            1‖ < ε := by
  have hwTwo : 2 ≤ w := by
    have hcut :
        2 ≤ wTrickedCFZComplexExceptionalBound k := by
      simp [wTrickedCFZComplexExceptionalBound,
        complexZetaModelNonzeroCutoff,
        complexZetaModelComparisonCutoff]
    exact hcut.trans hw
  have heventual :
      ∀ e : LinearFormsExponent k,
        ∀ᶠ N : ℕ in atTop,
          ∀ tu ∈
              SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt
                  (Real.log (sieveLevel k N))),
            ‖normalizedSmallPrimeZetaCorrection
                  (sieveLevel k N) w tu.1 tu.2 *
                cutoffZetaSystemFactor
                  (sieveLevel k N) tu.1 tu.2 -
              1‖ < ε := by
    intro e
    have hfixed :=
      eventually_uniform_fixedPrimorialFiniteFourierCorrection_sieveLevel
        (κ := SelectedCFZFormIndex e) hk hwTwo hε
    filter_upwards [hfixed] with N hN
    intro tu htu
    exact hN tu.1 tu.2
      ((SmoothSieveCutoff.mem_fourierProductBox_iff
          (Real.sqrt_nonneg _)
          tu.1).mp htu.1)
      ((SmoothSieveCutoff.mem_fourierProductBox_iff
          (Real.sqrt_nonneg _)
          tu.2).mp htu.2)
  exact Filter.eventually_all.mpr heventual

end Wikipedia.SzemeredisTheorem
