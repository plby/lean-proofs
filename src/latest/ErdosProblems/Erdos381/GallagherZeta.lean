import ErdosProblems.Erdos381.VariableZeta
import ErdosProblems.Erdos48.GallagherPowerDensity

namespace Erdos381

open Complex Metric Set
open BoundedGaps.Maynard
open Erdos48

noncomputable section

noncomputable local instance zetaGallagherPrimitiveCharactersOneUnique :
    Unique (primitiveCharacters 1) where
  default := zetaPrimitiveCharacter
  uniq psi := by
    apply Subtype.ext
    exact DirichletCharacter.level_one psi.1

theorem intervalIntegral_zetaVariableDetector_eq_unweightedPrimitiveNegativeDirichletMass
    (Y N T : ℕ) (c : ℕ → ℂ) :
    (∫ u in (0 : ℝ)..(T : ℝ),
        ‖∑ n ∈ Finset.Ioc Y N,
          c n * (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
      ∫ u in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass 1
          (Finset.Ioc Y N) c u := by
  have hdefault : (default : primitiveCharacters 1).1 =
      (1 : DirichletCharacter ℂ 1) := DirichletCharacter.level_one _
  apply intervalIntegral.integral_congr
  intro u hu
  unfold unweightedPrimitiveNegativeDirichletMass
  norm_num [zetaPrimitiveCharacter, hdefault]

theorem exists_zeta_variable_unweightedIntegral_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (T : ℕ), 1 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (zetaHighZeroRectangleMass eta T : ℝ) *
                (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                  unweightedPrimitiveNegativeDirichletMass 1
                    (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
                    (variableNormalizedDetectorCoefficient eta J j) u := by
  obtain ⟨κ, D, hκ, hD, hselection⟩ :=
    exists_zeta_variable_detected_zero_selection
  obtain ⟨A, hA, hcoverBound⟩ :=
    exists_zetaHighZeroRectangleMass_cover_bound
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Y : ℕ → ℕ := fun j ↦ variableDetectorLowerCutoff E eta j
  let c : ℕ → ℕ → ℂ := fun j ↦
    variableNormalizedDetectorCoefficient eta J j
  let Klocal : ℝ := 48 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  have hB : (1 : ℝ) ≤ B := by
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [B]
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hdelta1 : delta ≤ 1 := by
    simpa only [delta] using variableDetectorPropagationRadius_le_one hJpos
  have heta1 : eta ≤ 1 := by linarith
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
    positivity
  obtain ⟨S, order, hSsub, hsep, hcover, horder⟩ :=
    hselection T hT eta heta heta8
  have hSrange : ∀ t ∈ S, 0 ≤ t ∧ t ≤ T := by
    intro t ht
    have htOrd := hSsub ht
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht1, htT⟩ :=
      (mem_zetaHighZeroOrdinates_iff heta1 (by exact_mod_cast hT) t).mp
        htOrd
    exact ⟨by linarith, by simpa only using htT⟩
  have horderRange : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J := by
    intro t ht
    exact ⟨by simpa only [L] using (horder t ht).1,
      (horder t ht).2.1⟩
  have hlower : ∀ t ∈ S, ∀ u : ℝ,
      |u - t| ≤ delta * eta →
      (1 / 32 : ℝ) ≤
        ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
          c (order t) n * (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
    intro t ht u hu
    have hlarge := (horder t ht).2.2.2.2 u hu
    let j := order t
    let f : ℝ := ((j - 1).factorial : ℝ)
    let G : ℝ := (578 : ℝ) ^ J / 2
    have hf : 0 < f := by
      dsimp [f]
      exact_mod_cast Nat.factorial_pos (j - 1)
    have hscaled : f / 32 <
        G * (2 * eta) ^ j *
          ‖variableBandZeroDetectorPolynomial
            (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
      simpa only [j, f, G] using hlarge.1
    have hdiv := div_lt_div_of_pos_right hscaled hf
    have hnormScale :
        ‖(variableDetectorNormalization eta J j : ℂ) *
            variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ =
          variableDetectorNormalization eta J j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg
          (variableDetectorNormalization_nonneg heta.le J j)]
    apply le_of_lt
    calc
      (1 / 32 : ℝ) = (f / 32) / f := by field_simp
      _ < (G * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖) / f := hdiv
      _ = variableDetectorNormalization eta J j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
        dsimp [variableDetectorNormalization, G, f]
        ring
      _ = ‖(variableDetectorNormalization eta J j : ℂ) *
            variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := hnormScale.symm
      _ = ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
            c (order t) n * (1 : DirichletCharacter ℂ 1) n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
        rw [variable_normalized_polynomial_eq_smul]
  have hselected := selectedOrdinates_card_mul_le_variableDetector_integrals
    zetaPrimitiveCharacter Y c N T L J eta delta (1 / 32 : ℝ)
      heta heta1 hdelta hdelta1 (by norm_num) S order
      hSrange hsep horderRange hlower
  have hselectedMass :
      (S.card : ℝ) * (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass 1
              (Finset.Ioc (Y j) N) (c j) u := by
    calc
      (S.card : ℝ) * (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * (1 : DirichletCharacter ℂ 1) n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 :=
        hselected
      _ = ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass 1
              (Finset.Ioc (Y j) N) (c j) u := by
        apply Finset.sum_congr rfl
        intro j hj
        exact intervalIntegral_zetaVariableDetector_eq_unweightedPrimitiveNegativeDirichletMass
          (Y j) N (T + 1) (c j)
  have hlogGlobal : eta * Real.log ((T : ℝ) + 2) ≤
      eta * Real.log B := by
    apply mul_le_mul_of_nonneg_left _ heta.le
    apply Real.log_le_log (by positivity)
    dsimp [B]
    nlinarith
  have hmass := hcoverBound eta (T : ℝ) (eta * Real.log B) delta
    heta heta1 (by exact_mod_cast hT) hdelta.le hdelta1 hlogGlobal
    S hSsub hcover
  have hmass' : (zetaHighZeroRectangleMass eta T : ℝ) ≤
      (S.card : ℝ) * Klocal := by
    simpa only [Klocal] using hmass
  let c₀ : ℝ := (delta * eta) * (1 / 32 : ℝ) ^ 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) *
          (delta * eta) * (1 / 32 : ℝ) ^ 2 =
        (zetaHighZeroRectangleMass eta T : ℝ) * c₀ := by
      dsimp [c₀]
      ring
    _ ≤ ((S.card : ℝ) * Klocal) * c₀ :=
      mul_le_mul_of_nonneg_right hmass' hc₀
    _ = Klocal * ((S.card : ℝ) * c₀) := by ring
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass 1
              (Finset.Ioc (Y j) N) (c j) u := by
      apply mul_le_mul_of_nonneg_left _ hKlocal
      simpa only [c₀, mul_assoc] using hselectedMass
    _ = _ := by rfl

theorem exists_zeta_gallagher_rawDensity_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (T Amp : ℕ), 1 ≤ T →
        ∀ (eta W : ℝ), 0 < eta → eta ≤ 1 / 8 → 0 ≤ W →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (∀ q ∈ Finset.Ioc 0 1,
            W ≤ roughAmplifierCoefficient q Amp) →
          (∀ j ∈ Finset.Icc L J,
            2 ≤ variableDetectorLowerCutoff E eta j ∧
            variableDetectorLowerCutoff E eta j ≤ N ∧
            4 * ((T + 1) + 1) ≤ variableDetectorLowerCutoff E eta j ∧
            Amp ≤ variableDetectorLowerCutoff E eta j ∧
            2 * (((T + 1) + 1) * Amp ^ 2) ≤
              variableDetectorLowerCutoff E eta j ∧
            2 * ((T + 1) + 1) ≤
              variableDetectorLowerCutoff E eta j) →
          W * ((zetaHighZeroRectangleMass eta T : ℝ) *
                (delta * eta) * (1 / 32 : ℝ) ^ 2) ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                gallagherRawDensityTermAt 1 (T + 1) E N J j W eta R := by
  obtain ⟨κ, D, A, hκ, hD, hA, hselection⟩ :=
    exists_zeta_variable_unweightedIntegral_parameters
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro T Amp hT eta W heta heta8 hW
  dsimp only
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 48 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  intro hcoeff hcutoffs
  have hselected := hselection T hT eta heta heta8
  have hHpos : 1 ≤ H := by
    dsimp [H]
    apply Nat.mul_pos (variableDetectorHeightDilation_pos E)
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hBone : (1 : ℝ) ≤ B := by
        dsimp [B]
        have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
        nlinarith
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hBone
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal, B]
    have hBlog : 0 ≤ Real.log (2 * ((T : ℝ) + 2)) := by
      apply Real.log_nonneg
      have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith
    positivity
  have hterms :
      W * (∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          unweightedPrimitiveNegativeDirichletMass 1
            (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
            (variableNormalizedDetectorCoefficient eta J j) u) ≤
        ∑ j ∈ Finset.Icc L J,
          gallagherRawDensityTermAt 1 (T + 1) E N J j W eta R := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hY2, hYN, hheight, hrough, hroughConductor, hconductor⟩ :=
      hcutoffs j hj
    have hj2 : 2 ≤ j := by
      have hjLower := (Finset.mem_Icc.mp hj).1
      dsimp [L] at hjLower
      have hDH : 1 ≤ D * H := Nat.mul_pos hD hHpos
      omega
    simpa only [gallagherRawDensityTermAt] using
      mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le_band
        1 Amp (variableDetectorLowerCutoff E eta j) N (T + 1) J j W
          heta hj2 hY2 hYN hW hcoeff hheight (by simpa using hrough)
          (by simpa using hroughConductor) (by simpa using hconductor)
  calc
    W * ((zetaHighZeroRectangleMass eta T : ℝ) *
          (delta * eta) * (1 / 32 : ℝ) ^ 2) ≤
      W * (Klocal *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass 1
              (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
              (variableNormalizedDetectorCoefficient eta J j) u) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [E, B, H₀, H, J, delta, R, N, L, Klocal] using hselected) hW
    _ = Klocal * (W *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass 1
              (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
              (variableNormalizedDetectorCoefficient eta J j) u) := by ring
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          gallagherRawDensityTermAt 1 (T + 1) E N J j W eta R :=
      mul_le_mul_of_nonneg_left hterms hKlocal
    _ = _ := by rfl

theorem exists_zeta_gallagher_rawDensity_globalProduct_parameters :
    ∃ κ D A : ℕ, ∃ K Camp : ℝ,
      1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧ 0 < K ∧
      ∀ (T : ℕ), 1 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let Amp := 2 * (T + 2)
          let W := Real.log Amp / 2
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          2 ≤ Real.log Amp →
          20 * (K + (Real.log (Real.log Amp) + Camp + 2) + Real.log 2) ≤
            Real.log Amp →
          W * ((zetaHighZeroRectangleMass eta T : ℝ) *
                (delta * eta) * (1 / 32 : ℝ) ^ 2) ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                gallagherRawDensityTermAt 1 (T + 1) E N J j W eta R := by
  obtain ⟨κ, D, A, hκ, hD, hA, hraw⟩ :=
    exists_zeta_gallagher_rawDensity_parameters
  obtain ⟨K, Camp, hK, hcoeffUniform⟩ :=
    exists_uniform_roughAmplifierCoefficient_half_log_lower_up_to
  refine ⟨κ, D, A, K, Camp, hκ, hD, hA, hK, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  intro hlogAmp hdom
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let Amp : ℕ := 2 * (T + 2)
  let W : ℝ := Real.log Amp / 2
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hAmp2 : 2 ≤ Amp := by dsimp [Amp]; omega
  have hOneAmp : 1 < Amp := lt_of_lt_of_le (by omega) hAmp2
  have hcoeff : ∀ q ∈ Finset.Ioc 0 1,
      W ≤ roughAmplifierCoefficient q Amp := by
    simpa only [W] using hcoeffUniform hOneAmp hlogAmp hdom
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  apply hraw T Amp hT eta W heta heta8 hW hcoeff
  intro j hj
  have hjLower : D * H + 1 ≤ j := by
    simpa only [L] using (Finset.mem_Icc.mp hj).1
  have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
  have hYcompare : zeroDetectorLowerCutoff B ≤
      variableDetectorLowerCutoff E eta j := by
    exact zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
      hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
  have hcast : (Amp : ℝ) = B := by
    dsimp [Amp, B]
    push_cast
    ring
  have hpow : Amp ^ 4 ≤ zeroDetectorLowerCutoff B := by
    rw [← hcast]
    exact pow_four_le_zeroDetectorLowerCutoff Amp hAmp2
  have hbig : Amp ^ 4 ≤ variableDetectorLowerCutoff E eta j :=
    hpow.trans hYcompare
  have hAmpPow : Amp ^ 3 ≤ Amp ^ 4 := by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ Amp) (by omega)
  have hmain :
      2 * ((T + 1 + 1) * Amp ^ 2) ≤ Amp ^ 4 := by
    have heq : 2 * ((T + 1 + 1) * Amp ^ 2) = Amp ^ 3 := by
      dsimp [Amp]
      ring
    rw [heq]
    exact hAmpPow
  have hheight : 4 * (T + 1 + 1) ≤ Amp ^ 4 := by
    have htwo : 2 ≤ Amp ^ 2 := hAmp2.trans (Nat.le_pow (by omega : 0 < 2))
    calc
      4 * (T + 1 + 1) ≤ 2 * ((T + 1 + 1) * Amp ^ 2) := by
        have hm := Nat.mul_le_mul_left (2 * (T + 1 + 1)) htwo
        convert hm using 1 <;> ring
      _ ≤ Amp ^ 4 := hmain
  have hrough : Amp ≤ Amp ^ 4 :=
    Nat.le_pow (by omega : 0 < 4)
  have hconductor : 2 * (T + 1 + 1) ≤ Amp ^ 4 := by
    calc
      2 * (T + 1 + 1) ≤ 4 * (T + 1 + 1) := by omega
      _ ≤ Amp ^ 4 := hheight
  refine ⟨hAmp2.trans (hrough.trans hbig),
    variableDetectorLowerCutoff_le_zeroDetectorCutoff hjJ heta,
    hheight.trans hbig, hrough.trans hbig, hmain.trans hbig,
    hconductor.trans hbig⟩

theorem exists_zeta_gallagher_logFreeDensity_power_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ K Camp C c : ℝ, 0 < K ∧ 0 < C ∧ 0 < c ∧
      ∀ (T : ℕ), 2 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let B := 2 * ((T : ℝ) + 2)
          lambda ≤ eta * Real.log B →
          let Amp := 2 * (T + 2)
          2 ≤ Real.log Amp →
          20 * (K + (Real.log (Real.log Amp) + Camp + 2) + Real.log 2) ≤
            Real.log Amp →
          (zetaHighZeroRectangleMass eta T : ℝ) ≤
            C * B ^ (c * eta) := by
  obtain ⟨κ, D, A, K, Camp, hκ, hD, hA, hK, hraw⟩ :=
    exists_zeta_gallagher_rawDensity_globalProduct_parameters
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let kBase : ℝ := 48 * C₀ + 256 * (A : ℝ) / 3
  let kCoeff : ℝ := 4 * kBase
  let P0 : ℝ := rCoeff * (a : ℝ) * (1 + 2 / lambda) + 2
  let P : ℝ := 2 * P0
  let S : ℝ := gallagherPageMeanEnvelope P
  let uCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + 4 * rCoeff * (a : ℝ) + 1
  let gCoeff : ℝ :=
    Real.log ((578 : ℝ) ^ 2) * (a : ℝ) + Real.log 16 * (a : ℝ) + 2
  let gConst : ℝ := (40 / Real.log 2) * ((a : ℝ) + 1) ^ 2
  let cTerm : ℝ := uCoeff + gCoeff + 3
  let termConst : ℝ := 2 + 2 * gConst * P0
  let c : ℝ := cTerm + 3 + Real.log 2312 * (a : ℝ)
  let Craw : ℝ :=
    512 * kCoeff * (S * ((a : ℝ) + 1) * termConst) *
      (12 * C₀ * (a : ℝ)) / lambda
  let C : ℝ := Craw * Real.exp (2 * c)
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) := Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hkBase : 0 < kBase := by dsimp [kBase]; positivity
  have hkCoeff : 0 < kCoeff := by dsimp [kCoeff]; positivity
  have hP0 : 0 < P0 := by
    dsimp [P0]
    have hscale : 0 < 1 + 2 / lambda := by positivity
    positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 < S := by
    dsimp [S]
    unfold gallagherPageMeanEnvelope
    positivity
  have hgConst : 0 < gConst := by dsimp [gConst]; positivity
  have huCoeff : 0 < uCoeff := by
    dsimp [uCoeff]
    have hlog : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    positivity
  have hgCoeff : 0 < gCoeff := by
    dsimp [gCoeff]
    have hlog1 : 0 ≤ Real.log ((578 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
    have hlog2 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    positivity
  have hcTerm : 0 < cTerm := by dsimp [cTerm]; positivity
  have htermConst : 0 < termConst := by dsimp [termConst]; positivity
  have hc : 0 < c := by
    dsimp [c]
    have hlog : 0 < Real.log (2312 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hCraw : 0 < Craw := by dsimp [Craw]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K, Camp, C, c, hK, hC, hc, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  intro hlower hlogAmp hamp
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let Amp : ℕ := 2 * (T + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 48 * C₀ + (256 * (A : ℝ) / 3) * h
  have hbCast : (Amp : ℝ) = B := by
    dsimp [Amp, B]
    push_cast
    ring
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hlogBone : (1 : ℝ) ≤ Real.log B := by
    rw [← hbCast]
    linarith
  have hh : 0 < h := by
    dsimp [h]
    exact hlambda.trans_le hlower
  have hlambdaH : lambda ≤ h := by simpa only [h, B] using hlower
  obtain ⟨hJ, hJbound, hJexp, hJoneExp, _hKgeneric, _henv⟩ :=
    variable_envelope_parameter_bounds (A := A) hκ hD
      (by norm_num : 2 ≤ (2 : ℕ)) hT heta heta8
  change (J : ℝ) ≤ (a : ℝ) * (h + 2) at hJbound
  change (J : ℝ) ≤ (a : ℝ) * Real.exp (h + 2) at hJexp
  change ((J + 1 : ℕ) : ℝ) ≤
      ((a : ℝ) + 1) * Real.exp (h + 2) at hJoneExp
  have hsum :
      (∑ j ∈ Finset.Icc L J,
        gallagherRawDensityTermAt 1 (T + 1) E N J j
          (Real.log Amp / 2) eta R) ≤
        S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2)) := by
    simpa only [E, a, C₀, cTail, rCoeff, P0, P, S, uCoeff, gCoeff,
      gConst, cTerm, termConst, B, Amp, h, H₀, H, J, R, N, L,
      gallagherRawDensityTermAt, Nat.cast_ofNat] using
      gallagher_rawDensity_sum_le_exp_envelope hlambda hκ hD
        (by norm_num : 2 ≤ (2 : ℕ)) hT heta heta8 hlower hlogAmp
  have hbase := hraw T (by omega) eta heta heta8
  dsimp only at hbase
  have hraw0 : (Real.log Amp / 2) *
      ((zetaHighZeroRectangleMass eta T : ℝ) * (delta * eta) *
        (1 / 32 : ℝ) ^ 2) ≤ Klocal *
        (S * ((a : ℝ) + 1) * termConst *
          Real.exp ((cTerm + 1) * (h + 2))) := by
    have h0 := hbase hlogAmp hamp
    have h1 : (Real.log Amp / 2) *
        ((zetaHighZeroRectangleMass eta T : ℝ) * (delta * eta) *
          (1 / 32 : ℝ) ^ 2) ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            gallagherRawDensityTermAt 1 (T + 1) E N J j
              (Real.log Amp / 2) eta R := by
      simpa only [E, B, Amp, h, H₀, H, J, delta, R, N, L, Klocal, C₀] using h0
    exact h1.trans (mul_le_mul_of_nonneg_left hsum (by dsimp [Klocal]; positivity))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact variableDetectorPropagationRadius_pos hJ
  have hleft : (Real.log Amp / 2) *
      ((zetaHighZeroRectangleMass eta T : ℝ) * (delta * eta) *
        (1 / 32 : ℝ) ^ 2) =
      (zetaHighZeroRectangleMass eta T : ℝ) * (delta * h / 2048) := by
    rw [show Real.log (Amp : ℝ) = Real.log B by rw [hbCast]]
    dsimp [h]
    ring
  rw [hleft] at hraw0
  let X : ℝ := S * ((a : ℝ) + 1) * termConst *
    Real.exp ((cTerm + 1) * (h + 2))
  have hraw512 : (zetaHighZeroRectangleMass eta T : ℝ) *
      (delta * h / 512) ≤ (4 * Klocal) * X := by
    calc
      (zetaHighZeroRectangleMass eta T : ℝ) * (delta * h / 512) =
          4 * ((zetaHighZeroRectangleMass eta T : ℝ) *
            (delta * h / 2048)) := by ring
      _ ≤ 4 * (Klocal * X) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [X] using hraw0
      _ = (4 * Klocal) * X := by ring
  have hdeltaInv : delta⁻¹ = 12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J := by
    dsimp [delta, variableDetectorPropagationRadius, C₀]
    rw [inv_inv]
  have hKbase : Klocal ≤ kBase * Real.exp (h + 2) := by
    have hpre : Klocal ≤ kBase * (h + 2) := by
      let k₀ : ℝ := 48 * C₀
      let k₁ : ℝ := 256 * (A : ℝ) / 3
      have hk₀ : 0 ≤ k₀ := by dsimp [k₀]; positivity
      have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
      have hdiff : 0 ≤ k₀ * (h + 1) + 2 * k₁ := by positivity
      have hsmall : k₀ + k₁ * h ≤ (k₀ + k₁) * (h + 2) := by
        calc
          k₀ + k₁ * h ≤ k₀ + k₁ * h +
              (k₀ * (h + 1) + 2 * k₁) := le_add_of_nonneg_right hdiff
          _ = (k₀ + k₁) * (h + 2) := by ring
      simpa only [Klocal, kBase, k₀, k₁] using hsmall
    exact hpre.trans (mul_le_mul_of_nonneg_left
      add_two_le_exp_add_two hkBase.le)
  have hKbound : 4 * Klocal ≤ kCoeff * Real.exp (h + 2) := by
    dsimp [kCoeff]
    calc
      4 * Klocal ≤ 4 * (kBase * Real.exp (h + 2)) :=
        mul_le_mul_of_nonneg_left hKbase (by norm_num)
      _ = (4 * kBase) * Real.exp (h + 2) := by ring
  have hbefore : (zetaHighZeroRectangleMass eta T : ℝ) ≤
      Craw * Real.exp (c * (h + 2)) := by
    simpa only [Craw, c, X] using
      gallagher_density_algebra hdelta hh hlambda hlambdaH hraw512 hKbound
        hJexp hJbound hdeltaInv hkCoeff.le hS.le (zero_le_one.trans ha)
        htermConst.le hC₀.le
  have hpowB : Real.exp (c * h) = B ^ (c * eta) := by
    dsimp [h]
    rw [Real.rpow_def_of_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hB8)]
    congr 1
    ring
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) ≤
        Craw * Real.exp (c * (h + 2)) := hbefore
    _ = Craw * (Real.exp (2 * c) * Real.exp (c * h)) := by
      rw [show c * (h + 2) = 2 * c + c * h by ring, Real.exp_add]
    _ = C * B ^ (c * eta) := by
      rw [hpowB]
      dsimp only [C]
      ac_rfl

private theorem eventually_twenty_log_add_const_le_self_zeta (D : ℝ) :
    ∀ᶠ y : ℝ in Filter.atTop, 20 * Real.log y + D ≤ y := by
  have hlog := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 40 by norm_num)
  filter_upwards [hlog, Filter.eventually_ge_atTop (max 1 (2 * max D 0))]
      with y hylog hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  simp only [id] at hylog
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hy0] at hylog
  have hD : D ≤ y / 2 := by
    have htwo : 2 * max D 0 ≤ y := (le_max_right _ _).trans hy
    nlinarith [le_max_left D 0]
  nlinarith

theorem eventually_zetaGallagher_size_conditions (K Camp : ℝ) :
    ∀ᶠ T : ℕ in Filter.atTop,
      2 ≤ T ∧
      2 ≤ Real.log (2 * (T + 2) : ℕ) ∧
      20 * (K +
          (Real.log (Real.log (2 * (T + 2) : ℕ)) + Camp + 2) +
          Real.log 2) ≤
        Real.log (2 * (T + 2) : ℕ) := by
  let Amp : ℕ → ℕ := fun T ↦ 2 * (T + 2)
  have hAmpNatTop : Filter.Tendsto Amp Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := fun T : ℕ ↦ T)
    · intro T
      dsimp [Amp]
      omega
    · exact Filter.tendsto_id
  have hAmpRealTop : Filter.Tendsto (fun T ↦ (Amp T : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hAmpNatTop
  have hlogAmpTop : Filter.Tendsto
      (fun T ↦ Real.log (Amp T : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hAmpRealTop
  have hlogAmp : ∀ᶠ T : ℕ in Filter.atTop,
      2 ≤ Real.log (Amp T : ℝ) :=
    hlogAmpTop.eventually_ge_atTop 2
  let D : ℝ := 20 * (K + Camp + 2 + Real.log 2)
  have hamp : ∀ᶠ T : ℕ in Filter.atTop,
      20 * (K + (Real.log (Real.log (Amp T : ℝ)) + Camp + 2) +
          Real.log 2) ≤ Real.log (Amp T : ℝ) := by
    have hcomp := hlogAmpTop.eventually
      (eventually_twenty_log_add_const_le_self_zeta D)
    filter_upwards [hcomp] with T hT
    dsimp [D] at hT
    nlinarith
  filter_upwards [Filter.eventually_ge_atTop 2, hlogAmp, hamp]
      with T hT hlog hamp
  simpa only [Amp] using And.intro hT (And.intro hlog hamp)

theorem exists_zeta_logFreeDensity_power_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ C c : ℝ, ∃ T₀ : ℕ, 0 < C ∧ 0 < c ∧
      ∀ T : ℕ, T₀ ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          lambda ≤ eta * Real.log (2 * ((T : ℝ) + 2)) →
          (zetaHighZeroRectangleMass eta T : ℝ) ≤
            C * (2 * ((T : ℝ) + 2)) ^ (c * eta) := by
  obtain ⟨K, Camp, C, c, hK, hC, hc, hdensity⟩ :=
    exists_zeta_gallagher_logFreeDensity_power_bound hlambda
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1
    (eventually_zetaGallagher_size_conditions K Camp)
  refine ⟨C, c, T₀, hC, hc, ?_⟩
  intro T hT eta heta heta8 hlower
  obtain ⟨hTtwo, hlogAmp, hamp⟩ := hT₀ T hT
  exact hdensity T hTtwo eta heta heta8 hlower hlogAmp hamp

#print axioms intervalIntegral_zetaVariableDetector_eq_unweightedPrimitiveNegativeDirichletMass
#print axioms exists_zeta_variable_unweightedIntegral_parameters
#print axioms exists_zeta_gallagher_rawDensity_parameters
#print axioms exists_zeta_gallagher_rawDensity_globalProduct_parameters
#print axioms exists_zeta_gallagher_logFreeDensity_power_bound
#print axioms exists_zeta_logFreeDensity_power_bound

end

end Erdos381
