import APAP.Prereqs.FourierTransform.Discrete
import APAP.Prereqs.Inner.Hoelder.Compact
import APAP.Prereqs.LpNorm.Compact
import APAP.Prereqs.LpNorm.Discrete.Basic
import APAP.Physics.AlmostPeriodicity
import ErdosProblems.Erdos140.BohrBasic
import ErdosProblems.Erdos140.CrootSisask
import ErdosProblems.Erdos140.FiniteFourier
import ErdosProblems.Erdos140.LocalSpectrum
import ErdosProblems.Erdos140.RelativeChangSanders
import ErdosProblems.Erdos140.RelativeBohrVolume

/-!
# The normalization step in localized almost-periodicity

The analytic Schoen--Sisask argument naturally controls the unnormalized
three-fold convolution `1_(-A₂) ⋆ 1_A₁ ⋆ 1_(-S)`.

The quantitative Roth iteration uses instead the probability-normalized
difference convolution `μ_A₁ ∘ μ_A₂` and convolution by a Bohr probability
measure.  This file proves the exact finite-sum change of variables between
the conventions and the final convexity step.  There is no implicit factor
of the order of the ambient group.
-/

open scoped BigOperators ENNReal Indicator NNReal Pointwise translate mu
open Finset Function MeasureTheory RCLike

namespace Erdos140.LocalizedAlmostPeriodicity

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-! ## Fourier control of a translation -/

/-- The `ℓ¹` norm of the normalized Fourier coefficients. -/
noncomputable def fourierL1 (f : G → ℂ) : ℝ :=
  ∑ ψ : AddChar G ℂ, ‖Erdos140.FiniteFourier.coeff f ψ‖

/-- Fourier inversion bounds a pointwise translation error by the spectral
weighted `ℓ¹` norm.  This is the exact estimate used when the Bohr set
annihilates the large spectrum of the Croot--Sisask smoothing measure. -/
theorem norm_sub_translate_le_fourier_sum (f : G → ℂ) (t x : G) :
    ‖f (x - t) - f x‖ ≤
      ∑ ψ : AddChar G ℂ,
        ‖Erdos140.FiniteFourier.coeff f ψ‖ * ‖ψ (-t) - 1‖ := by
  classical
  rw [← Erdos140.FiniteFourier.inversion f (x - t),
    ← Erdos140.FiniteFourier.inversion f x, ← Finset.sum_sub_distrib]
  calc
    ‖∑ ψ : AddChar G ℂ,
        (Erdos140.FiniteFourier.coeff f ψ * ψ (x - t) -
          Erdos140.FiniteFourier.coeff f ψ * ψ x)‖
        ≤ ∑ ψ : AddChar G ℂ,
            ‖Erdos140.FiniteFourier.coeff f ψ * ψ (x - t) -
              Erdos140.FiniteFourier.coeff f ψ * ψ x‖ :=
          norm_sum_le _ _
    _ = ∑ ψ : AddChar G ℂ,
          ‖Erdos140.FiniteFourier.coeff f ψ‖ * ‖ψ (-t) - 1‖ := by
      apply sum_congr rfl
      intro ψ _
      have hfactor :
          Erdos140.FiniteFourier.coeff f ψ * ψ (x - t) -
              Erdos140.FiniteFourier.coeff f ψ * ψ x =
            (Erdos140.FiniteFourier.coeff f ψ * ψ x) * (ψ (-t) - 1) := by
        have hmap : ψ (x - t) = ψ x * ψ (-t) := by
          rw [sub_eq_add_neg, ψ.map_add_eq_mul]
        rw [hmap]
        ring
      rw [hfactor, norm_mul, norm_mul, AddChar.norm_apply, mul_one]

/-- Uniform annihilation of every Fourier mode controls every translate by
`delta * fourierL1 f`. -/
theorem norm_sub_translate_le_mul_fourierL1
    (f : G → ℂ) (t x : G) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hann : ∀ ψ : AddChar G ℂ, ‖ψ (-t) - 1‖ ≤ delta) :
    ‖f (x - t) - f x‖ ≤ delta * fourierL1 f := by
  calc
    ‖f (x - t) - f x‖ ≤
        ∑ ψ : AddChar G ℂ,
          ‖Erdos140.FiniteFourier.coeff f ψ‖ * ‖ψ (-t) - 1‖ :=
      norm_sub_translate_le_fourier_sum f t x
    _ ≤ ∑ ψ : AddChar G ℂ,
        ‖Erdos140.FiniteFourier.coeff f ψ‖ * delta := by
      gcongr with ψ
      exact hann ψ
    _ = delta * fourierL1 f := by
      rw [fourierL1]
      change Finset.univ.sum
          (fun ψ : AddChar G ℂ ↦ ‖Erdos140.FiniteFourier.coeff f ψ‖ * delta) =
        delta * Finset.univ.sum
          (fun ψ : AddChar G ℂ ↦ ‖Erdos140.FiniteFourier.coeff f ψ‖)
      calc
        Finset.univ.sum
            (fun ψ : AddChar G ℂ ↦ ‖Erdos140.FiniteFourier.coeff f ψ‖ * delta) =
            Finset.univ.sum
              (fun ψ : AddChar G ℂ ↦ ‖Erdos140.FiniteFourier.coeff f ψ‖) * delta :=
          (Finset.sum_mul _ _ _).symm
        _ = _ := mul_comm _ _

/-- A spectral cutoff version of Fourier inversion.  On the chosen spectrum
`Omega` one uses the supplied character-annihilation estimate; off `Omega`
one uses the universal chord bound `2`.  This is the finite Fourier step in
the Schoen--Sisask argument, separated from the construction of `Omega`. -/
theorem norm_sub_translate_le_spectrum_cutoff
    (f : G → ℂ) (Omega : Finset (AddChar G ℂ)) (t x : G)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hann : ∀ psi ∈ Omega, ‖psi (-t) - 1‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤
      theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
        ‖Erdos140.FiniteFourier.coeff f psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ := by
  classical
  calc
    ‖f (x - t) - f x‖ ≤
        ∑ psi : AddChar G ℂ,
          ‖Erdos140.FiniteFourier.coeff f psi‖ * ‖psi (-t) - 1‖ :=
      norm_sub_translate_le_fourier_sum f t x
    _ = ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ * ‖psi (-t) - 1‖ +
        ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ * ‖psi (-t) - 1‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun psi : AddChar G ℂ ↦ psi ∈ Omega)]
    _ ≤ ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ * theta +
        ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ * 2 := by
      gcongr with psi hpsi psi hpsi
      · exact hann psi (by simpa using hpsi)
      · calc
          ‖psi (-t) - 1‖ ≤ ‖psi (-t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by norm_num
    _ = theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff f psi‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- Transfer a Fourier cutoff estimate through a uniform approximation. -/
theorem norm_sub_translate_le_of_uniform_approx_and_spectrum_cutoff
    (f p : G → ℂ) (Omega : Finset (AddChar G ℂ)) (t x : G)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) (htheta : 0 ≤ theta)
    (happrox : ∀ y, ‖p y - f y‖ ≤ delta)
    (hann : ∀ psi ∈ Omega, ‖psi (-t) - 1‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤
      2 * delta +
        theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖Erdos140.FiniteFourier.coeff p psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff p psi‖ := by
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ := by
      calc
        _ ≤ ‖(f (x - t) - p (x - t)) + (p (x - t) - p x)‖ +
            ‖p x - f x‖ := norm_add_le _ _
        _ ≤ ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ +
            ‖p x - f x‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ delta + ‖p (x - t) - p x‖ + delta := by
      gcongr
      · simpa only [norm_sub_rev] using happrox (x - t)
      · exact happrox x
    _ ≤ delta +
        (theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
            ‖Erdos140.FiniteFourier.coeff p psi‖ +
          2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
            ‖Erdos140.FiniteFourier.coeff p psi‖) + delta := by
      gcongr
      exact norm_sub_translate_le_spectrum_cutoff p Omega t x htheta hann
    _ = 2 * delta +
        theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖Erdos140.FiniteFourier.coeff p psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖Erdos140.FiniteFourier.coeff p psi‖ := by ring

/-- Chord distance from one is unchanged by negating the group argument. -/
lemma norm_character_neg_sub_one (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

/-! ## Fourier smoothing for a Croot--Sisask averaging measure -/

/-- Fourier inversion and the elementary large-spectrum split.  On Fourier
modes where the normalized indicator of `X` is at least `eta`, use the
supplied phase bound; on all remaining modes, the `m`-fold smoothing supplies
the factor `eta ^ m` and the universal chord bound two. -/
theorem smoothing_translate_dLinfty_le
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (X : Finset G) (hX : X.Nonempty) (m : ℕ) (F : G → ℂ)
    (eta theta : ℝ) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (t : G)
    (hphase : ∀ psi : AddChar G ℂ,
      eta ≤ ‖dft (μ_[ℂ] X) psi‖ → ‖1 - psi t‖ ≤ theta) :
    ‖τ t (μ X ∗ᵈ^ m ∗ᵈ F) - (μ X ∗ᵈ^ m ∗ᵈ F)‖_[∞] ≤
      (theta + 2 * eta ^ m) * ‖dft F‖ₙ_[1] := by
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  let P : G → ℂ := μ X ∗ᵈ^ m ∗ᵈ F
  have hpoint :
      (τ t P - P) x =
        𝔼 psi : AddChar G ℂ,
          dft P psi * (psi (x - t) - psi x) := by
    simp only [Pi.sub_apply, translate_apply]
    rw [← dft_inversion P (x - t), ← dft_inversion P x,
      ← Finset.expect_sub_distrib]
    apply Finset.expect_congr rfl
    intro psi _
    ring
  rw [hpoint]
  calc
    ‖𝔼 psi : AddChar G ℂ,
        dft P psi * (psi (x - t) - psi x)‖
        ≤ 𝔼 psi : AddChar G ℂ,
            ‖dft P psi * (psi (x - t) - psi x)‖ :=
          RCLike.norm_expect_le (K := ℝ)
    _ ≤ 𝔼 psi : AddChar G ℂ,
          (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
      refine expect_le_expect fun psi _ ↦ ?_
      rw [norm_mul]
      have hfactor :
          ‖psi (x - t) - psi x‖ = ‖1 - psi t‖ := by
        have hmap : psi (x - t) = psi x * psi (-t) := by
          rw [sub_eq_add_neg, psi.map_add_eq_mul]
        rw [hmap]
        calc
          ‖psi x * psi (-t) - psi x‖ = ‖psi x * (psi (-t) - 1)‖ := by ring_nf
          _ = ‖psi (-t) - 1‖ := by rw [norm_mul, AddChar.norm_apply, one_mul]
          _ = ‖1 - psi t‖ := norm_character_neg_sub_one psi t
      rw [hfactor]
      simp only [P, dft_ddconv_apply, dft_iterConv_apply, norm_mul, norm_pow]
      have hmu : ‖dft (μ_[ℂ] X) psi‖ ≤ 1 := by
        calc
          ‖dft (μ_[ℂ] X) psi‖ ≤ ‖(μ_[ℂ] X)‖_[1] := norm_dft_le_dL1Norm _ _
          _ = 1 := MeasureTheory.dL1Norm_mu hX
      by_cases hlarge : eta ≤ ‖dft (μ_[ℂ] X) psi‖
      · have hpow : ‖dft (μ_[ℂ] X) psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi hlarge
        calc
          ‖dft (μ_[ℂ] X) psi‖ ^ m * ‖dft F psi‖ * ‖1 - psi t‖ ≤
              1 * ‖dft F psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hF : 0 ≤ ‖dft F psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖dft (μ_[ℂ] X) psi‖ ^ m ≤ eta ^ m := by
          exact pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖dft (μ_[ℂ] X) psi‖ ^ m * ‖dft F psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖dft F psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hF : 0 ≤ ‖dft F psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * ‖dft F‖ₙ_[1] := by
      rw [MeasureTheory.cL1Norm_eq_expect_norm, Finset.mul_expect]

/-- The Fourier `L¹` norm of the three-factor convolution appearing in the
Schoen--Sisask argument is bounded by the square root of the ratio of the last
two set sizes.  This is exactly Cauchy--Schwarz and Parseval; the first
probability factor has Fourier `L∞` norm at most one. -/
theorem dft_threefold_cL1Norm_le
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (A B C : Finset G) (hA : A.Nonempty) (hC : C.Nonempty) :
    ‖dft ((μ_[ℂ] A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ μ C)‖ₙ_[1] ≤
      Real.sqrt ((B.card : ℝ) / C.card) := by
  calc
    ‖dft ((μ_[ℂ] A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ μ C)‖ₙ_[1]
        = ‖dft (μ_[ℂ] A) *
            (dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C))‖ₙ_[1] := by
          rw [dft_ddconv, dft_ddconv]
          congr 1
          funext psi
          ring
    _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] := by
      calc
        _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] *
              ‖dft (μ_[ℂ] A)‖ₙ_[∞] := by
            simpa [mul_comm] using
              (cL1Norm_mul_le (f := dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C))
                (g := dft (μ_[ℂ] A)) 1 ∞)
        _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] * 1 := by
            gcongr
            exact (cLinftyNorm_dft_le_dL1Norm _).trans_eq (dL1Norm_mu hA)
        _ = _ := mul_one _
    _ ≤ ‖dft (𝟭_[B] : G → ℂ)‖ₙ_[2] * ‖dft (μ_[ℂ] C)‖ₙ_[2] :=
      cL1Norm_mul_le 2 2
    _ = Real.sqrt (B.card : ℝ) * (C.card : ℝ) ^ (-2⁻¹ : ℝ) := by
      rw [cL2Norm_dft, dL2Norm_indicator_one, cL2Norm_dft, dL2Norm_mu hC]
    _ = Real.sqrt ((B.card : ℝ) / C.card) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow,
        Real.sqrt_eq_rpow, div_eq_mul_inv]
      congr 1
      rw [← Real.rpow_neg (by positivity)]
      congr 1
      norm_num

/-- The unnormalized DFT of the uniform probability measure is the mass
Fourier coefficient at the negative character. -/
lemma dft_mu_eq_massCoeff_neg (X : Finset G) (psi : AddChar G ℂ) :
    dft (μ_[ℂ] X) psi =
      Erdos140.massCoeff (Erdos140.normalizedIndicator X) (-psi) := by
  classical
  rw [dft_apply, wInner_one_eq_sum]
  simp only [inner_apply', Erdos140.massCoeff, Pi.neg_apply,
    AddChar.neg_apply, AddChar.inv_apply_eq_conj]
  apply Finset.sum_congr rfl
  intro x _
  unfold mu Erdos140.normalizedIndicator
  by_cases hx : x ∈ X
  · simp [hx, smul_eq_mul, ← AddChar.inv_apply_eq_conj,
      ← AddChar.map_neg_eq_inv, mul_comm]
  · simp [hx, smul_eq_mul]

/-- Translation changes a discrete Fourier coefficient only by a unit
character phase, so its norm is unchanged. -/
lemma norm_dft_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    ‖dft (τ a f) psi‖ = ‖dft f psi‖ := by
  rw [dft_apply, dft_apply, wInner_one_eq_sum, wInner_one_eq_sum]
  simp only [inner_apply', translate_apply]
  have hsum :
      (∑ x : G, starRingEnd ℂ (psi x) * f (x - a)) =
        starRingEnd ℂ (psi a) * ∑ x : G, starRingEnd ℂ (psi x) * f x := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (-a)) _ _ (fun x ↦ ?_)
    simp only [Equiv.coe_addRight, sub_eq_add_neg, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, map_mul, map_inv₀]
    have hne : starRingEnd ℂ (psi a) ≠ 0 := by
      have hpsi : psi a ≠ 0 := by
        intro h
        have hnorm := AddChar.norm_apply psi a
        rw [h, norm_zero] at hnorm
        norm_num at hnorm
      simpa using hpsi
    field_simp
  rw [hsum, norm_mul]
  simp

/-- The Fourier norm of the uniform measure on a translated finite set is
unchanged. -/
lemma norm_dft_mu_vaddFinset (T : Finset G) (a : G) (psi : AddChar G ℂ) :
    ‖dft (μ_[ℂ] (a +ᵥ T)) psi‖ = ‖dft (μ_[ℂ] T) psi‖ := by
  rw [← translate_mu (K := ℂ)]
  exact norm_dft_translate (μ_[ℂ] T) a psi

/-- The half-large DFT spectrum of the probability measure agrees with the
half-large Chang spectrum used by the relative selector. -/
theorem mem_largeSpectrum_of_half_le_norm_dft_mu
    (X : Finset G) (hX : X.Nonempty) (psi : AddChar G ℂ)
    (hpsi : (1 / 2 : ℝ) ≤ ‖dft (μ_[ℂ] X) psi‖) :
    psi ∈ Erdos140.Chang.largeSpectrum X (1 / 2) := by
  classical
  by_contra hnot
  have hneg : -psi ∉ Erdos140.Chang.largeSpectrum X (1 / 2) := by
    intro hn
    have := Erdos140.RelativeChangSanders.neg_mem_chang_largeSpectrum hn
    exact hnot (by simpa only [neg_neg] using this)
  have hltSpec :
      ‖Erdos140.Chang.spectrumSum X (-psi)‖ < (1 / 2 : ℝ) * X.card := by
    exact lt_of_not_ge fun h ↦ hneg (Erdos140.Chang.mem_largeSpectrum.mpr h)
  have hcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hlt :
      ‖Erdos140.massCoeff (Erdos140.normalizedIndicator X) (-psi)‖ < 1 / 2 := by
    rw [Erdos140.massCoeff_normalizedIndicator, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcard]
    calc
      (X.card : ℝ)⁻¹ * ‖Erdos140.Chang.spectrumSum X (-psi)‖ <
          (X.card : ℝ)⁻¹ * ((1 / 2 : ℝ) * X.card) := by gcongr
      _ = 1 / 2 := by field_simp
  rw [dft_mu_eq_massCoeff_neg] at hpsi
  linarith

/-- A half-large Fourier mode of a translate of T is already in the
half-large Chang spectrum of T. -/
theorem mem_largeSpectrum_of_half_le_norm_dft_mu_vaddFinset
    (T : Finset G) (hT : T.Nonempty) (a : G) (psi : AddChar G ℂ)
    (hpsi : (1 / 2 : ℝ) ≤ ‖dft (μ_[ℂ] (a +ᵥ T)) psi‖) :
    psi ∈ Erdos140.Chang.largeSpectrum T (1 / 2) := by
  apply mem_largeSpectrum_of_half_le_norm_dft_mu T hT psi
  rw [← norm_dft_mu_vaddFinset T a psi]
  exact hpsi

/-- An explicit number of arc cells sufficient to annihilate a spectrum of
real-valued dimension at most `D`.  The `max` makes the definition total even
when it is used outside the positive-dimensional application. -/
noncomputable def spectralQuantization (D : ℝ) : ℕ :=
  ⌈2 * Real.pi * max D 0⌉₊ + 1

lemma spectralQuantization_pos (D : ℝ) : 0 < spectralQuantization D := by
  simp [spectralQuantization]

lemma mul_inv_spectralQuantization_le (D : ℝ) :
    D * ((((spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ)) ≤
      (2 * Real.pi)⁻¹ := by
  let n := spectralQuantization D
  have hnNat : 0 < n := spectralQuantization_pos D
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hceil : 2 * Real.pi * max D 0 ≤
      (Nat.ceil (2 * Real.pi * max D 0) : ℝ) := Nat.le_ceil _
  have hmain : 2 * Real.pi * D ≤ (n : ℝ) := by
    calc
      2 * Real.pi * D ≤ 2 * Real.pi * max D 0 := by
        gcongr
        exact le_max_left _ _
      _ ≤ (Nat.ceil (2 * Real.pi * max D 0) : ℝ) := hceil
      _ ≤ (n : ℝ) := by
        dsimp [n, spectralQuantization]
        exact_mod_cast Nat.le_succ _
  have hcoe : ((((n : ℕ) : ℝ≥0)⁻¹ : ℝ)) = (n : ℝ)⁻¹ := by
    norm_cast
  rw [hcoe]
  rw [← div_eq_mul_inv, div_le_iff₀ hn]
  calc
    D ≤ (n : ℝ) / (2 * Real.pi) :=
      (le_div_iff₀ hpi).2 (by nlinarith [hmain])
    _ = (2 * Real.pi)⁻¹ * (n : ℝ) := by
      field_simp

/-- Multiplying the number of spectral cells by a positive integer makes the
new-spectrum phase loss explicitly at most 2 / q.  This is the quantitative
form used by the density step: the dimension bound on Delta is the only
input beyond positivity of the scale multiplier. -/
lemma scaled_spectral_phase_le (D : ℝ) (d q : ℕ)
    (hd : (d : ℝ) ≤ D) (hq : 0 < q) :
    4 * Real.pi * (d : ℝ) *
        (((((q * spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ))) ≤
      2 / (q : ℝ) := by
  have hs : 0 < spectralQuantization D := spectralQuantization_pos D
  have hsR : (0 : ℝ) < spectralQuantization D := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase : D * ((spectralQuantization D : ℝ)⁻¹) ≤
      (2 * Real.pi)⁻¹ := by
    have h := mul_inv_spectralQuantization_le D
    have hcoe : ((((spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ)) =
        (spectralQuantization D : ℝ)⁻¹ := by norm_cast
    simpa [hcoe] using h
  have hdsmall : (d : ℝ) * ((spectralQuantization D : ℝ)⁻¹) ≤
      (2 * Real.pi)⁻¹ := by
    calc
      (d : ℝ) * ((spectralQuantization D : ℝ)⁻¹) ≤
          D * ((spectralQuantization D : ℝ)⁻¹) := by gcongr
      _ ≤ _ := hbase
  have hcoe : (((((q * spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ))) =
      ((q : ℝ) * (spectralQuantization D : ℝ))⁻¹ := by
    norm_cast
  rw [hcoe, mul_inv]
  calc
    4 * Real.pi * (d : ℝ) *
        ((q : ℝ)⁻¹ * (spectralQuantization D : ℝ)⁻¹) =
        (q : ℝ)⁻¹ *
          (4 * Real.pi * ((d : ℝ) * (spectralQuantization D : ℝ)⁻¹)) := by ring
    _ ≤ (q : ℝ)⁻¹ * (4 * Real.pi * (2 * Real.pi)⁻¹) := by gcongr
    _ = 2 / (q : ℝ) := by
      field_simp
      ring

/-- Transfer almost-periodicity through a uniform smoothing approximation. -/
theorem transfer_smoothing_translate
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (F P : G → ℂ) (t : G) {delta E : ℝ}
    (hdelta : ‖P - F‖_[∞] ≤ delta)
    (hperiod : ‖τ t P - P‖_[∞] ≤ E) :
    ‖τ t F - F‖_[∞] ≤ 2 * delta + E := by
  have hfirst :
      ‖τ t F - F‖_[∞] ≤ ‖τ t F - τ t P‖_[∞] + ‖τ t P - F‖_[∞] :=
    dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub le_top
  have hsecond :
      ‖τ t P - F‖_[∞] ≤ ‖τ t P - P‖_[∞] + ‖P - F‖_[∞] :=
    dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub le_top
  calc
    ‖τ t F - F‖_[∞] ≤ ‖τ t F - τ t P‖_[∞] + ‖τ t P - F‖_[∞] := hfirst
    _ ≤ ‖τ t F - τ t P‖_[∞] +
          (‖τ t P - P‖_[∞] + ‖P - F‖_[∞]) := by gcongr
    _ = ‖F - P‖_[∞] + (‖τ t P - P‖_[∞] + ‖P - F‖_[∞]) := by
      have htrans : τ t F - τ t P = τ t (F - P) := by rfl
      rw [htrans, dLpNorm_translate]
    _ ≤ delta + (E + delta) := by
      gcongr
      simpa [dLpNorm_sub_comm] using hdelta
    _ = 2 * delta + E := by ring

/-! ## Global Chang spectrum converted to a Bohr datum -/

/-- Geometry/volume assembly for any proved spectrum cover.  This is the
interface expected from the relative Chang--Sanders step: once `Omega` is
covered by the signed span of `Delta`, no further analytic assumption is
needed to obtain rank, subordination, relative volume, and annihilation. -/
theorem controlled_bohr_of_spectrum_cover
    (B : Erdos140.BohrData G) (Omega Delta : Finset (AddChar G ℂ))
    (kappa : ℝ≥0) (m : ℕ) (hm : 0 < m) (S : Finset G)
    (hS : S ⊆ (B.dilate kappa).carrier)
    (hcover : Omega ⊆ Delta.addSpan)
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹) :
    let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
      (kappa + kappa) (m : ℝ≥0)⁻¹
    D.rank ≤ B.rank + Delta.card ∧
      D.carrier ⊆ (B.dilate (kappa + kappa)).carrier ∧
      S.card ≤ m ^ Delta.card * D.carrier.card ∧
      ∀ t ∈ D.carrier, ∀ psi ∈ Omega,
        ‖1 - psi t‖ ≤
          4 * Real.pi * (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hcontrolled := Erdos140.RelativeBohrVolume.controlled_adjoinBasis
    B Delta kappa hm S hS
  refine ⟨hcontrolled.1, hcontrolled.2.1, hcontrolled.2.2, ?_⟩
  intro t ht psi hpsi
  simpa only [D, mul_assoc, NNReal.coe_inv, NNReal.coe_natCast] using
    (Erdos140.LocalSpectrum.norm_one_sub_character_le_of_mem_adjoinBasis
      B hsmall ht (hcover hpsi))

/-- Relative Chang--Sanders geometry interface.  A local spectral selector
need only return the displayed signed-span-plus-old-spectrum cover; this
theorem supplies the adjoined datum, its relative volume, and its explicit
character-annihilation error. -/
theorem controlled_bohr_of_relativeSpectrum_cover
    (C : Erdos140.BohrData G) (hCreg : C.IsRankRegular)
    (Q Delta : Finset (AddChar G ℂ)) (kappa : ℝ≥0)
    (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (C.dilate kappa).carrier)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Erdos140.Chang.largeSpectrum C.carrier (1 / 2), psi = z + s) :
    let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
      (kappa + kappa) (m : ℝ≥0)⁻¹
    D.rank ≤ C.rank + Delta.card ∧
      D.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * D.carrier.card ∧
      ∀ t ∈ D.carrier, ∀ psi ∈ Q,
        ‖1 - psi t‖ ≤
          4 * Real.pi * ((Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ)) +
            400 * ((max C.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hcontrolled := Erdos140.RelativeBohrVolume.controlled_adjoinBasis
    C Delta kappa hm X hX
  refine ⟨hcontrolled.1, hcontrolled.2.1, hcontrolled.2.2, ?_⟩
  intro t ht psi hpsi
  simpa only [D, NNReal.coe_inv, NNReal.coe_natCast] using
    (Erdos140.LocalSpectrum.norm_one_sub_character_le_of_localSpectrum_cover
      C hCreg hsigma hsmall hcover t ht psi hpsi)

/-- Every finite Bohr datum has a rank-regular sub-dilate of the same rank.
Passing to it costs at most `4 ^ rank` in cardinality. -/
theorem exists_rankRegular_subdatum (D : Erdos140.BohrData G) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank = D.rank ∧ R.carrier ⊆ D.carrier ∧
        D.carrier.card ≤ 4 ^ D.rank * R.carrier.card := by
  classical
  obtain ⟨rho, hrhoHalf, hrhoOne, hreg⟩ := D.exists_rankRegular_dilate
  refine ⟨D.dilate rho, hreg, by simp, ?_, ?_⟩
  · simpa only [Erdos140.BohrData.dilate_one] using
      (Erdos140.BohrData.carrier_dilate_mono (B := D) hrhoOne)
  · have hbase := Erdos140.BohrData.card_unit_le_four_pow_rank_mul_card_half D
    have hhalf : (D.dilate (1 / 2)).carrier.card ≤
        (D.dilate rho).carrier.card :=
      Finset.card_le_card (Erdos140.BohrData.carrier_dilate_mono hrhoHalf)
    calc
      D.carrier.card = (D.dilate 1).carrier.card := by simp
      _ ≤ 4 ^ D.rank * (D.dilate (1 / 2)).carrier.card := hbase
      _ ≤ 4 ^ D.rank * (D.dilate rho).carrier.card :=
        Nat.mul_le_mul_left _ hhalf

/-- Rank-regular form of `controlled_bohr_of_spectrum_cover`. -/
theorem exists_regular_controlled_bohr_of_spectrum_cover
    (B : Erdos140.BohrData G) (Omega Delta : Finset (AddChar G ℂ))
    (kappa : ℝ≥0) (m : ℕ) (hm : 0 < m) (S : Finset G)
    (hS : S ⊆ (B.dilate kappa).carrier)
    (hcover : Omega ⊆ Delta.addSpan)
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
      R.carrier ⊆ (B.dilate (kappa + kappa)).carrier ∧
      S.card ≤ m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier, ∀ psi ∈ Omega,
        ‖1 - psi t‖ ≤
          4 * Real.pi * (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hD := controlled_bohr_of_spectrum_cover
    B Omega Delta kappa m hm S hS hcover hsmall
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ := exists_rankRegular_subdatum D
  refine ⟨R, hRreg, hRrank.le.trans hD.1, hRD.trans hD.2.1, ?_, ?_⟩
  · calc
      S.card ≤ m ^ Delta.card * D.carrier.card := hD.2.2.1
      _ ≤ m ^ Delta.card * (4 ^ D.rank * R.carrier.card) :=
        Nat.mul_le_mul_left _ hDcard
      _ ≤ m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) := by
        have hpow : 4 ^ D.rank ≤ 4 ^ (B.rank + Delta.card) :=
          Nat.pow_le_pow_right (by omega) hD.1
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
  · intro t ht psi hpsi
    exact hD.2.2.2 t (hRD ht) psi hpsi

/-- Rank-regular output for the relative Chang--Sanders cover interface. -/
theorem exists_regular_controlled_bohr_of_relativeSpectrum_cover
    (C : Erdos140.BohrData G) (hCreg : C.IsRankRegular)
    (Q Delta : Finset (AddChar G ℂ)) (kappa : ℝ≥0)
    (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (C.dilate kappa).carrier)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Erdos140.Chang.largeSpectrum C.carrier (1 / 2), psi = z + s) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank ≤ C.rank + Delta.card ∧
      R.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * (4 ^ (C.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier, ∀ psi ∈ Q,
        ‖1 - psi t‖ ≤
          4 * Real.pi * ((Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ)) +
            400 * ((max C.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hD := controlled_bohr_of_relativeSpectrum_cover
    C hCreg Q Delta kappa m hm X hX hsigma hsmall hcover
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ := exists_rankRegular_subdatum D
  refine ⟨R, hRreg, hRrank.le.trans hD.1, hRD.trans hD.2.1, ?_, ?_⟩
  · calc
      X.card ≤ m ^ Delta.card * D.carrier.card := hD.2.2.1
      _ ≤ m ^ Delta.card * (4 ^ D.rank * R.carrier.card) :=
        Nat.mul_le_mul_left _ hDcard
      _ ≤ m ^ Delta.card * (4 ^ (C.rank + Delta.card) * R.carrier.card) := by
        have hpow : 4 ^ D.rank ≤ 4 ^ (C.rank + Delta.card) :=
          Nat.pow_le_pow_right (by omega) hD.1
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
  · intro t ht psi hpsi
    exact hD.2.2.2 t (hRD ht) psi hpsi

/-- Unconditional local Chang--Sanders geometry, including regularization and
relative volume.  The logarithmic dimension parameter involves only the
density of `X` inside `B`; no ambient-group cardinality occurs.

The intermediate datum `C` is the explicit rank-regular small dilate selected
by `exists_relativeLargeSpectrum_cover`.  The final datum is subordinate to a
doubled dilate of `C`, has the advertised rank increment, annihilates the whole
`eta`-large spectrum of `X`, and has an explicit relative-cardinality loss. -/
theorem exists_regular_local_largeSpectrum_controlled_bohr
    (B : Erdos140.BohrData G) (hBreg : B.IsRankRegular)
    (X : Finset G) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) (kappa : ℝ≥0) (m : ℕ) (hm : 0 < m)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsmall :
      Erdos140.RelativeChangSanders.localChangDimension B X eta *
          (((m : ℝ≥0)⁻¹ : ℝ)) ≤ (2 * Real.pi)⁻¹) :
    ∃ rho : ℝ≥0, ∃ C : Erdos140.BohrData G,
      ∃ Delta : Finset (AddChar G ℂ), ∃ R : Erdos140.BohrData G,
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.dilate (rho *
          Erdos140.RelativeChangSanders.localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤
          Erdos140.RelativeChangSanders.localChangDimension B X eta ∧
        Delta ⊆ Erdos140.Chang.largeSpectrum X eta ∧
        R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
        R.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
        (C.dilate kappa).carrier.card ≤
          m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) ∧
        ∀ t ∈ R.carrier,
          ∀ psi ∈ Erdos140.Chang.largeSpectrum X eta,
            ‖1 - psi t‖ ≤
              4 * Real.pi *
                  (Delta.card : ℝ) * (((m : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) := by
  classical
  obtain ⟨rho, C, Delta, hrhoHalf, hrhoOne, hC, hCreg,
      hDeltaCard, hDeltaSpec, hcover⟩ :=
    Erdos140.RelativeChangSanders.exists_relativeLargeSpectrum_cover
      B hBreg X hX hXB eta heta
  have hCrank : C.rank = B.rank := by simp [hC]
  have hsigmaC : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0) := by
    simpa [hCrank] using hsigma
  have hinv : 0 ≤ (((m : ℝ≥0)⁻¹ : ℝ)) := by positivity
  have hsmallDelta :
      (Delta.card : ℝ) * (((m : ℝ≥0)⁻¹ : ℝ)) ≤
        (2 * Real.pi)⁻¹ :=
    (mul_le_mul_of_nonneg_right hDeltaCard hinv).trans hsmall
  obtain ⟨R, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_controlled_bohr_of_relativeSpectrum_cover
      C hCreg (Erdos140.Chang.largeSpectrum X eta) Delta kappa m hm
        (C.dilate kappa).carrier (fun _ hx ↦ hx) hsigmaC hsmallDelta hcover
  refine ⟨rho, C, Delta, R, hrhoHalf, hrhoOne, hC, hCreg,
    hDeltaCard, hDeltaSpec, hRreg, ?_, hRsub, ?_, ?_⟩
  · simpa [hCrank] using hRrank
  · simpa [hCrank] using hRcard
  · intro t ht psi hpsi
    simpa only [hCrank, mul_assoc] using hphase t ht psi hpsi

/-- **Unconditional localized `L∞` almost-periodicity.**  The theorem
assembles the subset-preserving boosted Croot--Sisask theorem, the genuine
relative Chang--Sanders selector, the rank/volume Bohr construction, and the
Fourier large-spectrum split.

The sampling set `S₀` is required only through the natural local support
condition `S₀ - S₀ ⊆ B₀`.  All losses are displayed: the raw
Croot--Sisask lower bound for `T`, the local logarithmic dimension of its
recentered translate `X`, the regular-child rank and relative-cardinality
loss, and the final uniform error. -/
theorem exists_unconditional_localized_linfty_almostPeriods_scaled
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S₀ : Finset G} (hA : A.Nonempty) (hS₀ : S₀.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) (hm : m ≠ 0)
    (M L : Finset G) (hM : M.Nonempty) (hL : L.Nonempty)
    (B₀ : Erdos140.BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : ℝ≥0)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : ℕ) : ℝ≥0))
    (qQuant : ℕ) (hqQuant : 0 < qQuant) :
    let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
    let sampleK := Erdos140.crootSisaskSampleSize q
      ((delta / m) / Real.exp 1)
    ∃ (T X : Finset G) (z : G) (rho : ℝ≥0),
      ∃ (C₀ : Erdos140.BohrData G)
        (Delta : Finset (AddChar G ℂ)) (R : Erdos140.BohrData G),
      T ⊆ S₀ ∧ z ∈ T ∧ X = -z +ᵥ T ∧ X.Nonempty ∧
      X ⊆ B₀.carrier ∧
      (((A.card : ℝ) ^ sampleK / 2 * S₀.card) /
          ((A + S₀).card : ℝ) ^ sampleK ≤ T.card) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        Erdos140.RelativeChangSanders.localChangBaseScale B₀ X (1 / 2)) ∧
      C₀.IsRankRegular ∧
      (Delta.card : ℝ) ≤
        Erdos140.RelativeChangSanders.localChangDimension B₀ X (1 / 2) ∧
      Delta ⊆ Erdos140.Chang.largeSpectrum X (1 / 2) ∧
      R.IsRankRegular ∧ R.rank ≤ B₀.rank + Delta.card ∧
      R.carrier ⊆ (C₀.dilate (kappa + kappa)).carrier ∧
      (C₀.dilate kappa).carrier.card ≤
        (qQuant * spectralQuantization
              (Erdos140.RelativeChangSanders.localChangDimension B₀ X (1 / 2))) ^
            Delta.card *
          (4 ^ (B₀.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier,
        ‖τ t ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L) -
            ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L)‖_[∞] ≤
          2 * delta +
            (4 * Real.pi *
                  (Delta.card : ℝ) *
                    ((((qQuant * spectralQuantization
                      (Erdos140.RelativeChangSanders.localChangDimension
                        B₀ X (1 / 2)) : ℕ) : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B₀.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) +
                2 * (1 / 2 : ℝ) ^ m) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  classical
  let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
  let sampleK := Erdos140.crootSisaskSampleSize q
    ((delta / m) / Real.exp 1)
  obtain ⟨T, z, hTS₀, hzT, hXne, hXdiff, hTcard, hsmooth⟩ :=
    Erdos140.croot_sisask_linfty_subset_boosted
      hA hS₀ delta hdelta m hm M L hM hL
  let X : Finset G := -z +ᵥ T
  have hXB₀ : X ⊆ B₀.carrier := by
    intro x hx
    exact hlocal (hXdiff (by simpa [X] using hx))
  let dim := Erdos140.RelativeChangSanders.localChangDimension B₀ X (1 / 2)
  let n := qQuant * spectralQuantization dim
  have hn : 0 < n := Nat.mul_pos hqQuant (spectralQuantization_pos dim)
  have hsmall : dim * (((n : ℝ≥0)⁻¹ : ℝ)) ≤ (2 * Real.pi)⁻¹ := by
    have hdim : 0 ≤ dim := by
      have hXcard : (0 : ℝ) < X.card := by
        exact_mod_cast (by simpa [X] using hXne.card_pos)
      have hcard : (X.card : ℝ) ≤ B₀.carrier.card := by
        exact_mod_cast Finset.card_le_card hXB₀
      have hratio : (1 : ℝ) ≤ 2 * (B₀.carrier.card : ℝ) / X.card := by
        rw [le_div_iff₀ hXcard]
        nlinarith
      have hlog : 0 ≤ Real.log (2 * (B₀.carrier.card : ℝ) / X.card) :=
        Real.log_nonneg hratio
      dsimp [dim, Erdos140.RelativeChangSanders.localChangDimension]
      positivity
    have hbase : dim *
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) ≤
          (2 * Real.pi)⁻¹ :=
      mul_inv_spectralQuantization_le dim
    have hbase_le_n : spectralQuantization dim ≤ n := by
      dsimp [n]
      exact Nat.le_mul_of_pos_left _ hqQuant
    have hinv : (((n : ℝ≥0)⁻¹ : ℝ)) ≤
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) := by
      have hbase_pos : (0 : ℝ≥0) <
          (spectralQuantization dim : ℕ) := by
        exact_mod_cast spectralQuantization_pos dim
      have hn_pos : (0 : ℝ≥0) < n := by exact_mod_cast hn
      have hbase_le_n' : (spectralQuantization dim : ℝ≥0) ≤ n := by
        exact_mod_cast hbase_le_n
      exact_mod_cast (inv_le_inv₀ hn_pos hbase_pos).2 hbase_le_n'
    exact (mul_le_mul_of_nonneg_left hinv hdim).trans hbase
  obtain ⟨rho, C₀, Delta, R, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, hDeltaSpec, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_local_largeSpectrum_controlled_bohr
      B₀ hB₀reg X (by simpa [X] using hXne) hXB₀ (1 / 2) (by norm_num)
        kappa n hn hkappa (by simpa [dim] using hsmall)
  let F : G → ℂ := (μ A ∗ᵈ 𝟭_[M]) ∗ᵈ μ L
  let P : G → ℂ := μ X ∗ᵈ^ m ∗ᵈ F
  let phase : ℝ :=
    4 * Real.pi * (Delta.card : ℝ) * (((n : ℝ≥0)⁻¹ : ℝ)) +
      400 * ((max B₀.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0)
  have hphase0 : 0 ≤ phase := by
    dsimp [phase]
    positivity
  have hFfourier : ‖dft F‖ₙ_[1] ≤ Real.sqrt ((M.card : ℝ) / L.card) := by
    simpa [F] using dft_threefold_cL1Norm_le A M L hA hL
  have hsmooth' : ‖P - F‖_[∞] ≤ delta := by
    simpa [P, F, X] using hsmooth
  have hperiod : ∀ t ∈ R.carrier,
      ‖τ t F - F‖_[∞] ≤
        2 * delta + (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
    intro t ht
    have hP := smoothing_translate_dLinfty_le X (by simpa [X] using hXne) m F
      (1 / 2) phase (by norm_num) hphase0 t (fun psi hpsi ↦
        hphase t ht psi
          (mem_largeSpectrum_of_half_le_norm_dft_mu X (by simpa [X] using hXne) psi hpsi))
    have hP' : ‖τ t P - P‖_[∞] ≤
        (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
      calc
        ‖τ t P - P‖_[∞] ≤
            (phase + 2 * (1 / 2 : ℝ) ^ m) * ‖dft F‖ₙ_[1] := by
              simpa [P] using hP
        _ ≤ (phase + 2 * (1 / 2 : ℝ) ^ m) *
            Real.sqrt ((M.card : ℝ) / L.card) := by
              gcongr
    exact transfer_smoothing_translate F P t hsmooth' hP'
  refine ⟨T, X, z, rho, C₀, Delta, R, hTS₀, hzT, rfl,
    by simpa [X] using hXne, hXB₀, ?_, hrhoHalf, hrhoOne, ?_, hC₀reg,
    ?_, hDeltaSpec, hRreg, hRrank, hRsub, ?_, ?_⟩
  · simpa [q, sampleK] using hTcard
  · simpa [X] using hC₀
  · simpa [dim] using hDeltaCard
  · simpa [n, dim] using hRcard
  · intro t ht
    simpa [F, phase, n, dim, mul_assoc] using hperiod t ht

/-- Localized almost-periodicity with the relative Chang step applied to the
original Croot--Sisask set T inside the parent Bohr set.  The smoothing
measure still uses the recentered translate X, but translation invariance of
Fourier norms transfers every large mode of X back to T.  Consequently the
dimension and rank loss are controlled by the density of T in B₀. -/
theorem exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} (hA : A.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) (hm : m ≠ 0)
    (M L : Finset G) (hM : M.Nonempty) (hL : L.Nonempty)
    (B₀ : Erdos140.BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : ℝ≥0)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : ℕ) : ℝ≥0))
    (qQuant : ℕ) (hqQuant : 0 < qQuant) :
    let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
    let sampleK := Erdos140.crootSisaskSampleSize q
      ((delta / m) / Real.exp 1)
    ∃ (T X : Finset G) (z : G) (rho : ℝ≥0),
      ∃ (C₀ : Erdos140.BohrData G)
        (Delta : Finset (AddChar G ℂ)) (R : Erdos140.BohrData G),
      T ⊆ B₀.carrier ∧ z ∈ T ∧ X = -z +ᵥ T ∧ X.Nonempty ∧
      (((A.card : ℝ) ^ sampleK / 2 * B₀.carrier.card) /
          ((A + B₀.carrier).card : ℝ) ^ sampleK ≤ T.card) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        Erdos140.RelativeChangSanders.localChangBaseScale B₀ T (1 / 2)) ∧
      C₀.IsRankRegular ∧
      (Delta.card : ℝ) ≤
        Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      Delta ⊆ Erdos140.Chang.largeSpectrum T (1 / 2) ∧
      R.IsRankRegular ∧ R.rank ≤ B₀.rank + Delta.card ∧
      R.carrier ⊆ (C₀.dilate (kappa + kappa)).carrier ∧
      (C₀.dilate kappa).carrier.card ≤
        (qQuant * spectralQuantization
              (Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
            Delta.card *
          (4 ^ (B₀.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier,
        ‖τ t ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L) -
            ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L)‖_[∞] ≤
          2 * delta +
            (4 * Real.pi *
                  (Delta.card : ℝ) *
                    ((((qQuant * spectralQuantization
                      (Erdos140.RelativeChangSanders.localChangDimension
                        B₀ T (1 / 2)) : ℕ) : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B₀.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) +
                2 * (1 / 2 : ℝ) ^ m) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  classical
  let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
  let sampleK := Erdos140.crootSisaskSampleSize q
    ((delta / m) / Real.exp 1)
  obtain ⟨T, z, hTB₀, hzT, hXne, _hXdiff, hTcard, hsmooth⟩ :=
    Erdos140.croot_sisask_linfty_subset_boosted
      hA B₀.carrier_nonempty delta hdelta m hm M L hM hL
  let X : Finset G := -z +ᵥ T
  have hTne : T.Nonempty := ⟨z, hzT⟩
  let dim := Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2)
  let n := qQuant * spectralQuantization dim
  have hn : 0 < n := Nat.mul_pos hqQuant (spectralQuantization_pos dim)
  have hsmall : dim * (((n : ℝ≥0)⁻¹ : ℝ)) ≤ (2 * Real.pi)⁻¹ := by
    have hdim : 0 ≤ dim := by
      have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
      have hcard : (T.card : ℝ) ≤ B₀.carrier.card := by
        exact_mod_cast Finset.card_le_card hTB₀
      have hratio : (1 : ℝ) ≤ 2 * (B₀.carrier.card : ℝ) / T.card := by
        rw [le_div_iff₀ hTcard]
        nlinarith
      have hlog : 0 ≤ Real.log (2 * (B₀.carrier.card : ℝ) / T.card) :=
        Real.log_nonneg hratio
      dsimp [dim, Erdos140.RelativeChangSanders.localChangDimension]
      positivity
    have hbase : dim *
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) ≤
          (2 * Real.pi)⁻¹ :=
      mul_inv_spectralQuantization_le dim
    have hbase_le_n : spectralQuantization dim ≤ n := by
      dsimp [n]
      exact Nat.le_mul_of_pos_left _ hqQuant
    have hinv : (((n : ℝ≥0)⁻¹ : ℝ)) ≤
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) := by
      have hbase_pos : (0 : ℝ≥0) <
          (spectralQuantization dim : ℕ) := by
        exact_mod_cast spectralQuantization_pos dim
      have hn_pos : (0 : ℝ≥0) < n := by exact_mod_cast hn
      have hbase_le_n' : (spectralQuantization dim : ℝ≥0) ≤ n := by
        exact_mod_cast hbase_le_n
      exact_mod_cast (inv_le_inv₀ hn_pos hbase_pos).2 hbase_le_n'
    exact (mul_le_mul_of_nonneg_left hinv hdim).trans hbase
  obtain ⟨rho, C₀, Delta, R, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, hDeltaSpec, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_local_largeSpectrum_controlled_bohr
      B₀ hB₀reg T hTne hTB₀ (1 / 2) (by norm_num)
        kappa n hn hkappa (by simpa [dim] using hsmall)
  let F : G → ℂ := (μ A ∗ᵈ 𝟭_[M]) ∗ᵈ μ L
  let P : G → ℂ := μ X ∗ᵈ^ m ∗ᵈ F
  let phase : ℝ :=
    4 * Real.pi * (Delta.card : ℝ) * (((n : ℝ≥0)⁻¹ : ℝ)) +
      400 * ((max B₀.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0)
  have hphase0 : 0 ≤ phase := by
    dsimp [phase]
    positivity
  have hFfourier : ‖dft F‖ₙ_[1] ≤ Real.sqrt ((M.card : ℝ) / L.card) := by
    simpa [F] using dft_threefold_cL1Norm_le A M L hA hL
  have hsmooth' : ‖P - F‖_[∞] ≤ delta := by
    simpa [P, F, X] using hsmooth
  have hperiod : ∀ t ∈ R.carrier,
      ‖τ t F - F‖_[∞] ≤
        2 * delta + (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
    intro t ht
    have hP := smoothing_translate_dLinfty_le X (by simpa [X] using hXne) m F
      (1 / 2) phase (by norm_num) hphase0 t (fun psi hpsi ↦
        hphase t ht psi
          (mem_largeSpectrum_of_half_le_norm_dft_mu_vaddFinset
            T hTne (-z) psi (by simpa [X] using hpsi)))
    have hP' : ‖τ t P - P‖_[∞] ≤
        (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
      calc
        ‖τ t P - P‖_[∞] ≤
            (phase + 2 * (1 / 2 : ℝ) ^ m) * ‖dft F‖ₙ_[1] := by
              simpa [P] using hP
        _ ≤ (phase + 2 * (1 / 2 : ℝ) ^ m) *
            Real.sqrt ((M.card : ℝ) / L.card) := by
              gcongr
    exact transfer_smoothing_translate F P t hsmooth' hP'
  refine ⟨T, X, z, rho, C₀, Delta, R, hTB₀, hzT, rfl,
    by simpa [X] using hXne, ?_, hrhoHalf, hrhoOne, ?_, hC₀reg,
    ?_, hDeltaSpec, hRreg, hRrank, hRsub, ?_, ?_⟩
  · simpa [q, sampleK] using hTcard
  · simpa using hC₀
  · simpa [dim] using hDeltaCard
  · simpa [n, dim] using hRcard
  · intro t ht
    simpa [F, phase, n, dim, mul_assoc] using hperiod t ht

/-- The original one-cell-scale form of localized almost-periodicity.  It is
the qQuant = 1 specialization of the scaled theorem above and is retained
as the stable API for callers that do not need an extra phase margin. -/
theorem exists_unconditional_localized_linfty_almostPeriods
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S₀ : Finset G} (hA : A.Nonempty) (hS₀ : S₀.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) (hm : m ≠ 0)
    (M L : Finset G) (hM : M.Nonempty) (hL : L.Nonempty)
    (B₀ : Erdos140.BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : ℝ≥0)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : ℕ) : ℝ≥0)) :
    let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
    let sampleK := Erdos140.crootSisaskSampleSize q
      ((delta / m) / Real.exp 1)
    ∃ (T X : Finset G) (z : G) (rho : ℝ≥0),
      ∃ (C₀ : Erdos140.BohrData G)
        (Delta : Finset (AddChar G ℂ)) (R : Erdos140.BohrData G),
      T ⊆ S₀ ∧ z ∈ T ∧ X = -z +ᵥ T ∧ X.Nonempty ∧
      X ⊆ B₀.carrier ∧
      (((A.card : ℝ) ^ sampleK / 2 * S₀.card) /
          ((A + S₀).card : ℝ) ^ sampleK ≤ T.card) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        Erdos140.RelativeChangSanders.localChangBaseScale B₀ X (1 / 2)) ∧
      C₀.IsRankRegular ∧
      (Delta.card : ℝ) ≤
        Erdos140.RelativeChangSanders.localChangDimension B₀ X (1 / 2) ∧
      Delta ⊆ Erdos140.Chang.largeSpectrum X (1 / 2) ∧
      R.IsRankRegular ∧ R.rank ≤ B₀.rank + Delta.card ∧
      R.carrier ⊆ (C₀.dilate (kappa + kappa)).carrier ∧
      (C₀.dilate kappa).carrier.card ≤
        spectralQuantization
              (Erdos140.RelativeChangSanders.localChangDimension B₀ X (1 / 2)) ^
            Delta.card *
          (4 ^ (B₀.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier,
        ‖τ t ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L) -
            ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L)‖_[∞] ≤
          2 * delta +
            (4 * Real.pi *
                  (Delta.card : ℝ) *
                    ((((spectralQuantization
                      (Erdos140.RelativeChangSanders.localChangDimension
                        B₀ X (1 / 2)) : ℕ) : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B₀.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) +
                2 * (1 / 2 : ℝ) ^ m) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  simpa using
    (exists_unconditional_localized_linfty_almostPeriods_scaled
      hA hS₀ delta hdelta m hm M L hM hL B₀ hB₀reg hlocal
        kappa hkappa 1 (by norm_num))

/-- Explicit regular-Bohr `L∞` almost-periodicity assembled from a uniform
Croot--Sisask approximation and a relative Chang--Sanders spectrum cover. -/
theorem exists_regular_fourier_almostPeriods_of_relativeSpectrum_cover
    (f p : G → ℂ) (C : Erdos140.BohrData G) (hCreg : C.IsRankRegular)
    (Q Delta : Finset (AddChar G ℂ)) (kappa : ℝ≥0)
    (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (C.dilate kappa).carrier)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Erdos140.Chang.largeSpectrum C.carrier (1 / 2), psi = z + s)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (happrox : ∀ y, ‖p y - f y‖ ≤ delta) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank ≤ C.rank + Delta.card ∧
      R.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * (4 ^ (C.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier, ∀ x : G,
        ‖f (x - t) - f x‖ ≤
          2 * delta +
          (4 * Real.pi * ((Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ)) +
              400 * ((max C.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0)) *
            ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Q),
              ‖Erdos140.FiniteFourier.coeff p psi‖ +
          2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Q),
            ‖Erdos140.FiniteFourier.coeff p psi‖ := by
  classical
  obtain ⟨R, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_controlled_bohr_of_relativeSpectrum_cover
      C hCreg Q Delta kappa m hm X hX hsigma hsmall hcover
  refine ⟨R, hRreg, hRrank, hRsub, hRcard, ?_⟩
  intro t ht x
  apply norm_sub_translate_le_of_uniform_approx_and_spectrum_cutoff
    f p Q t x hdelta (by positivity) happrox
  intro psi hpsi
  rw [norm_character_neg_sub_one]
  exact hphase t ht psi hpsi

/-- The (global) Chang cover, converted into explicit finite Bohr data.

This lemma is unconditional and is useful on its own.  The stronger localized
Schoen--Sisask theorem replaces the ambient logarithm in the displayed rank
bound by a relative-density logarithm; the geometric conversion from a signed
span to character annihilation is exactly the same one proved here. -/
theorem exists_global_largeSpectrum_bohr
    (B : Erdos140.BohrData G) (A : Finset G) (eta : ℝ)
    (kappa r : ℝ≥0) (hA : A.Nonempty) (heta : 0 < eta)
    (hshort : (Nat.ceil (2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2) : ℝ) * (r : ℝ) ≤ (2 * Real.pi)⁻¹) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta.card ≤ ⌈2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2⌉₊ ∧
      (Erdos140.LocalSpectrum.adjoinBasis B Delta kappa r).rank ≤
        B.rank + Delta.card ∧
      (Erdos140.LocalSpectrum.adjoinBasis B Delta kappa r).carrier ⊆
        (B.dilate kappa).carrier ∧
      ∀ t ∈ (Erdos140.LocalSpectrum.adjoinBasis B Delta kappa r).carrier,
        ∀ psi ∈ Erdos140.Chang.largeSpectrum A eta,
          ‖1 - psi t‖ ≤ 4 * Real.pi * (Delta.card : ℝ) * (r : ℝ) := by
  classical
  obtain ⟨Delta, hDeltaSpec, hDeltaCard, hspan⟩ :=
    Erdos140.Chang.exists_largeSpectrum_subset_addSpan A eta hA heta
  refine ⟨Delta, hDeltaCard,
    Erdos140.LocalSpectrum.adjoinBasis_rank_le B Delta kappa r,
    Erdos140.LocalSpectrum.adjoinBasis_carrier_subset_dilate B Delta kappa r, ?_⟩
  intro t ht psi hpsi
  have harc :=
    Erdos140.LocalSpectrum.norm_circleLogCharacter_le_card_mul_of_mem_adjoinBasis
      B ht (hspan hpsi)
  have hDeltaReal : (Delta.card : ℝ) ≤
      Nat.ceil (2 * Real.log ((Fintype.card G : ℝ) / A.card) / eta ^ 2) := by
    exact_mod_cast hDeltaCard
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hsmall : (Delta.card : ℝ) * (r : ℝ) ≤ (2 * Real.pi)⁻¹ :=
    (mul_le_mul_of_nonneg_right hDeltaReal hr).trans hshort
  simpa only [mul_assoc] using
    (Erdos140.LocalSpectrum.norm_one_sub_character_le_of_mem_adjoinBasis
      B hsmall ht (hspan hpsi))

/-- Global Chang together with the subset-relative volume theorem.  The
explicit output datum is subordinate to the doubled input scale and its
relative-cardinality loss is exactly `m ^ |Delta|`. -/
theorem exists_global_largeSpectrum_controlled_bohr
    (B : Erdos140.BohrData G) (A : Finset G) (eta : ℝ)
    (kappa : ℝ≥0) (m : ℕ) (hA : A.Nonempty) (heta : 0 < eta)
    (hm : 0 < m)
    (hshort : (Nat.ceil (2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2) : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤ (2 * Real.pi)⁻¹) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta.card ≤ ⌈2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2⌉₊ ∧
      let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
        (kappa + kappa) (m : ℝ≥0)⁻¹
      D.rank ≤ B.rank + Delta.card ∧
      D.carrier ⊆ (B.dilate (kappa + kappa)).carrier ∧
      (B.dilate kappa).carrier.card ≤ m ^ Delta.card * D.carrier.card ∧
      ∀ t ∈ D.carrier, ∀ psi ∈ Erdos140.Chang.largeSpectrum A eta,
        ‖1 - psi t‖ ≤
          4 * Real.pi * (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) := by
  classical
  obtain ⟨Delta, _hDeltaSpec, hDeltaCard, hspan⟩ :=
    Erdos140.Chang.exists_largeSpectrum_subset_addSpan A eta hA heta
  let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hcontrolled :=
    Erdos140.RelativeBohrVolume.controlled_adjoinBasis
      B Delta kappa hm (B.dilate kappa).carrier (fun _ hx ↦ hx)
  refine ⟨Delta, hDeltaCard, hcontrolled.1, hcontrolled.2.1,
    hcontrolled.2.2, ?_⟩
  intro t ht psi hpsi
  have hDeltaReal : (Delta.card : ℝ) ≤
      Nat.ceil (2 * Real.log ((Fintype.card G : ℝ) / A.card) / eta ^ 2) := by
    exact_mod_cast hDeltaCard
  have hr : 0 ≤ ((m : ℝ≥0)⁻¹ : ℝ) := by positivity
  have hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹ :=
    (mul_le_mul_of_nonneg_right hDeltaReal hr).trans hshort
  simpa only [D, mul_assoc, NNReal.coe_inv, NNReal.coe_natCast] using
    (Erdos140.LocalSpectrum.norm_one_sub_character_le_of_mem_adjoinBasis
      B hsmall ht (hspan hpsi))

/-- Fully unconditional regular-Bohr form of global Chang, with explicit
relative-volume loss. -/
theorem exists_regular_global_largeSpectrum_controlled_bohr
    (B : Erdos140.BohrData G) (A : Finset G) (eta : ℝ)
    (kappa : ℝ≥0) (m : ℕ) (hA : A.Nonempty) (heta : 0 < eta)
    (hm : 0 < m)
    (hshort : (Nat.ceil (2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2) : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤ (2 * Real.pi)⁻¹) :
    ∃ Delta : Finset (AddChar G ℂ), ∃ R : Erdos140.BohrData G,
      Delta.card ≤ ⌈2 * Real.log ((Fintype.card G : ℝ) / A.card) /
        eta ^ 2⌉₊ ∧
      R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
      R.carrier ⊆ (B.dilate (kappa + kappa)).carrier ∧
      (B.dilate kappa).carrier.card ≤
        m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier, ∀ psi ∈ Erdos140.Chang.largeSpectrum A eta,
        ‖1 - psi t‖ ≤
          4 * Real.pi * (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) := by
  classical
  obtain ⟨Delta, hDeltaCard, hD⟩ :=
    exists_global_largeSpectrum_controlled_bohr B A eta kappa m hA heta hm hshort
  let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ := exists_rankRegular_subdatum D
  refine ⟨Delta, R, hDeltaCard, hRreg, hRrank.le.trans hD.1,
    hRD.trans hD.2.1, ?_, ?_⟩
  · calc
      (B.dilate kappa).carrier.card ≤ m ^ Delta.card * D.carrier.card := hD.2.2.1
      _ ≤ m ^ Delta.card * (4 ^ D.rank * R.carrier.card) :=
        Nat.mul_le_mul_left _ hDcard
      _ ≤ m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) := by
        have hpow : 4 ^ D.rank ≤ 4 ^ (B.rank + Delta.card) :=
          Nat.pow_le_pow_right (by omega) hD.1
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
  · intro t ht psi hpsi
    exact hD.2.2.2 t (hRD ht) psi hpsi

/-- Probability-normalized indicator, equal to `1 / |A|` on `A`. -/
noncomputable def probabilityIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

/-- Unnormalized finite-sum convolution of two probability densities. -/
noncomputable def sumConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

/-- Difference convolution with counting measure. -/
noncomputable def differenceConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (y - x)

/-- Counting-measure inner product. -/
noncomputable def countingInner (f g : G → ℝ) : ℝ :=
  ∑ x : G, f x * g x

/-- The `{0,1}`-valued indicator of a finite set. -/
noncomputable def setIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then 1 else 0

@[simp] lemma setIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    setIndicator A x = 1 := by simp [setIndicator, hx]

@[simp] lemma setIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    setIndicator A x = 0 := by simp [setIndicator, hx]

lemma setIndicator_nonneg (A : Finset G) (x : G) : 0 ≤ setIndicator A x := by
  simp only [setIndicator]
  split <;> positivity

/-- The unnormalized sum obtained by expanding
`1_(-A₂) ⋆ 1_A₁ ⋆ 1_(-S)` at `-t`. -/
noncomputable def tripleIndicatorSum
    (A₁ A₂ S : Finset G) (t : G) : ℝ :=
  ∑ a₁ : G, ∑ a₂ : G,
    setIndicator A₁ a₁ * setIndicator A₂ a₂ * setIndicator S (t + a₁ - a₂)

lemma tripleIndicatorSum_nonneg (A₁ A₂ S : Finset G) (t : G) :
    0 ≤ tripleIndicatorSum A₁ A₂ S t := by
  exact sum_nonneg fun a₁ _ ↦ sum_nonneg fun a₂ _ ↦
    mul_nonneg (mul_nonneg (setIndicator_nonneg A₁ _) (setIndicator_nonneg A₂ _))
      (setIndicator_nonneg S _)

/-- Exact normalization bridge, with no ambient-cardinality factor.

The left side is `<(μ_A₁ ∘ μ_A₂)(·-t), 1_S>` in the convention
where each `μ_A` has total mass one. -/
theorem finiteInner_translate_differenceConvolution_eq
    {A₁ A₂ : Finset G} (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (S : Finset G) (t : G) :
    countingInner
        (fun x ↦ differenceConvolution (probabilityIndicator A₁)
          (probabilityIndicator A₂) (x - t))
        (setIndicator S) =
      tripleIndicatorSum A₁ A₂ S t / (A₁.card * A₂.card : ℝ) := by
  classical
  simp only [countingInner, differenceConvolution, probabilityIndicator,
    tripleIndicatorSum]
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  calc
    ∑ y : G, ∑ x : G,
        ((if y ∈ A₁ then (#A₁ : ℝ)⁻¹ else 0) *
          (if y - (x - t) ∈ A₂ then (#A₂ : ℝ)⁻¹ else 0)) * setIndicator S x
        = ((#A₁ : ℝ)⁻¹ * (#A₂ : ℝ)⁻¹) *
            ∑ y : G, ∑ x : G,
              setIndicator A₁ y * setIndicator A₂ (y - (x - t)) *
                setIndicator S x := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro x _
          simp only [setIndicator]
          split_ifs <;> ring
    _ = ((#A₁ : ℝ)⁻¹ * (#A₂ : ℝ)⁻¹) *
            ∑ a₁ : G, ∑ a₂ : G,
              setIndicator A₁ a₁ * setIndicator A₂ a₂ *
                setIndicator S (t + a₁ - a₂) := by
          congr 1
          apply sum_congr rfl
          intro a₁ _
          refine (Fintype.sum_equiv (Equiv.subLeft (t + a₁)) _ _ fun a₂ ↦ ?_).symm
          simp only [Equiv.subLeft_apply]
          congr 2 <;> abel
    _ = (∑ a₁ : G, ∑ a₂ : G,
            setIndicator A₁ a₁ * setIndicator A₂ a₂ *
              setIndicator S (t + a₁ - a₂)) /
          (A₁.card * A₂.card : ℝ) := by
          rw [div_eq_inv_mul]
          field_simp [hA₁.card_ne_zero, hA₂.card_ne_zero]

/-- Convolution by a nonempty normalized indicator is the uniform average of
translates. -/
lemma normalizedConvolution_normalizedIndicator_apply
    {D : Finset G} (hD : D.Nonempty) (f : G → ℝ) (x : G) :
    sumConvolution (probabilityIndicator D) f x =
      (∑ t ∈ D, f (x - t)) / D.card := by
  classical
  simp only [sumConvolution, probabilityIndicator]
  rw [← sum_subset (s₁ := D) (s₂ := univ)]
  · rw [div_eq_inv_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro t ht
    rw [if_pos ht]
  · simp
  · intro t _ ht
    simp [ht]

/-- Averaging pointwise almost-periods over a nonempty set preserves the same
error. -/
theorem smoothing_inner_error_of_pointwise
    {D : Finset G} (hD : D.Nonempty)
    (f h : G → ℝ) {eps : ℝ}
    (hperiod : ∀ t ∈ D,
      |countingInner (fun x ↦ f (x - t)) h - countingInner f h| ≤ eps) :
    |countingInner (sumConvolution (probabilityIndicator D) f) h -
        countingInner f h| ≤ eps := by
  classical
  have hcard : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hsmooth :
      countingInner (sumConvolution (probabilityIndicator D) f) h =
        (∑ t ∈ D, countingInner (fun x ↦ f (x - t)) h) / D.card := by
    simp only [countingInner]
    simp_rw [normalizedConvolution_normalizedIndicator_apply hD]
    simp_rw [div_mul_eq_mul_div, sum_div, Finset.sum_mul]
    rw [sum_comm]
    simp_rw [← sum_div]
  rw [hsmooth]
  have hrewrite :
      (∑ t ∈ D, countingInner (fun x ↦ f (x - t)) h) / D.card - countingInner f h =
        (∑ t ∈ D,
          (countingInner (fun x ↦ f (x - t)) h - countingInner f h)) / D.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard.ne']
  rw [hrewrite, abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  calc
    |∑ t ∈ D, (countingInner (fun x ↦ f (x - t)) h - countingInner f h)|
        ≤ ∑ t ∈ D,
            |countingInner (fun x ↦ f (x - t)) h - countingInner f h| :=
          abs_sum_le_sum_abs (fun t ↦
            countingInner (fun x ↦ f (x - t)) h - countingInner f h) D
    _ ≤ ∑ _t ∈ D, eps := sum_le_sum fun t ht ↦ hperiod t ht
    _ = eps * D.card := by simp [mul_comm]

/-- Localized normalized conclusion from an unnormalized `L∞`
almost-periodicity estimate for the triple sum. -/
theorem localized_inner_error_of_triple_almost_periods
    {D : BohrData G} {A₁ A₂ S : Finset G} {eps : ℝ}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (htriple : ∀ t ∈ D.carrier,
      |tripleIndicatorSum A₁ A₂ S t - tripleIndicatorSum A₁ A₂ S 0| ≤
        eps * (A₁.card : ℝ) * A₂.card) :
    |countingInner
          (sumConvolution (probabilityIndicator D.carrier)
            (differenceConvolution
              (probabilityIndicator A₁) (probabilityIndicator A₂)))
          (setIndicator S) -
        countingInner
          (differenceConvolution
            (probabilityIndicator A₁) (probabilityIndicator A₂))
          (setIndicator S)| ≤ eps := by
  classical
  apply smoothing_inner_error_of_pointwise D.carrier_nonempty
  intro t ht
  have hzero := finiteInner_translate_differenceConvolution_eq hA₁ hA₂ S (0 : G)
  simp only [sub_zero] at hzero
  rw [finiteInner_translate_differenceConvolution_eq hA₁ hA₂, hzero]
  rw [← sub_div, abs_div]
  have hcard : (0 : ℝ) < (A₁.card : ℝ) * A₂.card :=
    mul_pos (by exact_mod_cast hA₁.card_pos) (by exact_mod_cast hA₂.card_pos)
  rw [abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  simpa [mul_assoc] using htriple t ht

/-- Final localized smoothing bundle for a spectrum cover.  This theorem
records in one declaration the rank, subordination, relative-volume, and
normalized inner-product conclusions consumed by the density-increment
argument.  The remaining analytic input is precisely the pointwise triple
almost-period estimate on the explicit datum `D`. -/
theorem controlled_localized_inner_error_of_spectrum_cover
    (B : Erdos140.BohrData G) (Omega Delta : Finset (AddChar G ℂ))
    (kappa : ℝ≥0) (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (B.dilate kappa).carrier)
    (hcover : Omega ⊆ Delta.addSpan)
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    {A₁ A₂ S : Finset G} {eps : ℝ}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (htriple : ∀ t ∈ (Erdos140.LocalSpectrum.adjoinBasis B Delta
        (kappa + kappa) (m : ℝ≥0)⁻¹).carrier,
        |tripleIndicatorSum A₁ A₂ S t - tripleIndicatorSum A₁ A₂ S 0| ≤
          eps * (A₁.card : ℝ) * A₂.card) :
    let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
      (kappa + kappa) (m : ℝ≥0)⁻¹
    D.rank ≤ B.rank + Delta.card ∧
      D.carrier ⊆ (B.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * D.carrier.card ∧
      |countingInner
          (sumConvolution (probabilityIndicator D.carrier)
            (differenceConvolution
              (probabilityIndicator A₁) (probabilityIndicator A₂)))
          (setIndicator S) -
        countingInner
          (differenceConvolution
            (probabilityIndicator A₁) (probabilityIndicator A₂))
          (setIndicator S)| ≤ eps := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis B Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hgeometry := controlled_bohr_of_spectrum_cover
    B Omega Delta kappa m hm X hX hcover hsmall
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1, ?_⟩
  exact localized_inner_error_of_triple_almost_periods hA₁ hA₂ htriple

#print axioms finiteInner_translate_differenceConvolution_eq
#print axioms smoothing_inner_error_of_pointwise
#print axioms localized_inner_error_of_triple_almost_periods
#print axioms controlled_bohr_of_spectrum_cover
#print axioms controlled_bohr_of_relativeSpectrum_cover
#print axioms exists_rankRegular_subdatum
#print axioms exists_regular_controlled_bohr_of_spectrum_cover
#print axioms exists_regular_controlled_bohr_of_relativeSpectrum_cover
#print axioms exists_regular_fourier_almostPeriods_of_relativeSpectrum_cover
#print axioms smoothing_translate_dLinfty_le
#print axioms dft_threefold_cL1Norm_le
#print axioms dft_mu_eq_massCoeff_neg
#print axioms norm_dft_translate
#print axioms norm_dft_mu_vaddFinset
#print axioms mem_largeSpectrum_of_half_le_norm_dft_mu
#print axioms mem_largeSpectrum_of_half_le_norm_dft_mu_vaddFinset
#print axioms mul_inv_spectralQuantization_le
#print axioms scaled_spectral_phase_le
#print axioms transfer_smoothing_translate
#print axioms exists_regular_local_largeSpectrum_controlled_bohr
#print axioms exists_unconditional_localized_linfty_almostPeriods_scaled
#print axioms exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
#print axioms exists_unconditional_localized_linfty_almostPeriods
#print axioms exists_global_largeSpectrum_controlled_bohr
#print axioms exists_regular_global_largeSpectrum_controlled_bohr
#print axioms controlled_localized_inner_error_of_spectrum_cover

end Erdos140.LocalizedAlmostPeriodicity
