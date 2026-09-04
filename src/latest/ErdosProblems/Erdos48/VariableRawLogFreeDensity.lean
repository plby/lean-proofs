/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableSelectedZeroBandMass
import ErdosProblems.Erdos48.RawLogFreeDensity
import ErdosProblems.Erdos48.GallagherUnweightedSelection

/-!
# Raw variable-order log-free zero density

The detector is normalized by its factorial lower bound before the hybrid
large sieve is applied.  This is the cancellation which keeps the final
density exponent linear in `eta`.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

noncomputable def variableDetectorNormalization
    (eta : ℝ) (J j : ℕ) : ℝ :=
  ((578 : ℝ) ^ J / 2) * (2 * eta) ^ j /
    ((j - 1).factorial : ℝ)

noncomputable def variableNormalizedDetectorCoefficient
    (eta : ℝ) (J j n : ℕ) : ℂ :=
  (variableDetectorNormalization eta J j : ℂ) *
    (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)

theorem variableDetectorNormalization_nonneg
    {eta : ℝ} (heta : 0 ≤ eta) (J j : ℕ) :
    0 ≤ variableDetectorNormalization eta J j := by
  unfold variableDetectorNormalization
  positivity

theorem variable_normalized_polynomial_eq_smul
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) (eta : ℝ) (J j N : ℕ) (u : ℝ) :
    (∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) N,
        variableNormalizedDetectorCoefficient eta J j n * chi n *
          Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))) =
      (variableDetectorNormalization eta J j : ℂ) *
        variableBandZeroDetectorPolynomial chi E eta j N u := by
  classical
  unfold variableNormalizedDetectorCoefficient
    variableBandZeroDetectorPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem primitiveNegativeDirichletMass_real_mul
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) :
    primitiveNegativeDirichletMass Q s (fun n ↦ (a : ℂ) * c n) t =
      a ^ 2 * primitiveNegativeDirichletMass Q s c t := by
  classical
  unfold primitiveNegativeDirichletMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hchar :
      (∑ psi : primitiveCharacters q,
        ‖∑ n ∈ s, ((a : ℂ) * c n) * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
        a ^ 2 * ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s, c n * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    calc
      (∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s, ((a : ℂ) * c n) * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
        ∑ psi : primitiveCharacters q,
          a ^ 2 *
            ‖∑ n ∈ s, c n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro psi hpsi
        have hsum :
            (∑ n ∈ s, ((a : ℂ) * c n) * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
              (a : ℂ) *
                ∑ n ∈ s, c n * psi.1 n *
                  Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
        ring
      _ = a ^ 2 *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ s, c n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [hchar]
  ring

theorem primitiveNegativeDirichletMass_variableNormalized
    (Q : ℕ) (s : Finset ℕ) (eta : ℝ) (J j : ℕ) (t : ℝ)
    (heta : 0 ≤ eta) :
    primitiveNegativeDirichletMass Q s
        (variableNormalizedDetectorCoefficient eta J j) t =
      variableDetectorNormalization eta J j ^ 2 *
        primitiveNegativeDirichletMass Q s
          (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t := by
  change primitiveNegativeDirichletMass Q s
      (fun n ↦ (variableDetectorNormalization eta J j : ℂ) *
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t = _
  exact primitiveNegativeDirichletMass_real_mul Q s
      (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ))
      (variableDetectorNormalization eta J j) t
      (variableDetectorNormalization_nonneg heta J j)

theorem intervalIntegral_variableNormalizedDetector_eq
    (Q Y N T : ℕ) (eta : ℝ) (J j : ℕ) (heta : 0 ≤ eta) :
    (∫ u in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (variableNormalizedDetectorCoefficient eta J j) u) =
      variableDetectorNormalization eta J j ^ 2 *
        ∫ u in (0 : ℝ)..(T : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            (fun n ↦
              (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
  simp_rw [primitiveNegativeDirichletMass_variableNormalized Q
    (Finset.Ioc Y N) eta J j _ heta]
  rw [intervalIntegral.integral_const_mul]

/-- One order term in the variable-order detector density estimate. -/
noncomputable def variableRawLogFreeDensityTerm
    (T E N J j : ℕ) (eta : ℝ) : ℝ :=
  variableDetectorNormalization eta J j ^ 2 *
    ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
      ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
        (2 * ((j - 1) + 1))) *
      (((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^
        (-(2 * eta))))

/-- The complete variable-order detector-density inequality.  Unlike the
fixed-order predecessor, this applies at every logarithmic height. -/
theorem exists_variable_raw_and_unweightedIntegral_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          ((primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                variableRawLogFreeDensityTerm T E N J j eta) ∧
          ((primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                  unweightedPrimitiveNegativeDirichletMass Q
                    (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
                    (variableNormalizedDetectorCoefficient eta J j) u) := by
  obtain ⟨κ, D, hκ, hD, hselection⟩ :=
    exists_variable_detected_zero_selection
  obtain ⟨A, hA, hcoverBound⟩ :=
    exists_highZeroRectangleMass_cover_bound
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro Q T hQ eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
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
  let Klocal : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
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
  have hexists (q : ℕ) (psi : primitiveCharacters q) :
      ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
        q ∈ Finset.Ioc 1 Q →
          (∀ t ∈ S, 0 ≤ t ∧ t ≤ T) ∧
          (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
            2 * delta * eta < dist x y) ∧
          (∀ t ∈ S, L ≤ order t ∧ order t ≤ J) ∧
          (∀ t ∈ S, ∀ u : ℝ, |u - t| ≤ delta * eta →
            (1 / 16 : ℝ) ≤
              ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
                c (order t) n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) ∧
          ((primitiveHighZeroMassAt q psi eta T : ℕ) : ℝ) ≤
            (S.card : ℝ) * Klocal := by
    by_cases hqMem : q ∈ Finset.Ioc 1 Q
    · have hqData := Finset.mem_Ioc.mp hqMem
      have hq1 : 1 < q := hqData.1
      have hqQ : q ≤ Q := hqData.2
      let : NeZero q := ⟨by omega⟩
      obtain ⟨S, order, hSsub, hsep, hcover, horder⟩ :=
        hselection Q T hQ eta heta heta8 q hq1 hqQ psi.1 psi.2
      refine ⟨S, order, fun _ ↦ ⟨?_, hsep, ?_, ?_, ?_⟩⟩
      · intro t ht
        have htOrd := hSsub ht
        obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht0, htT⟩ :=
          (mem_highZeroOrdinates_iff hq1 psi.1 psi.2 heta1
            (show (0 : ℝ) ≤ T by positivity) t).mp htOrd
        exact ⟨ht0, htT⟩
      · intro t ht
        exact ⟨(horder t ht).1, (horder t ht).2.1⟩
      · intro t ht u hu
        have hlarge := (horder t ht).2.2.2.2 u hu
        let j := order t
        let f : ℝ := ((j - 1).factorial : ℝ)
        let G : ℝ := (578 : ℝ) ^ J / 2
        have hf : 0 < f := by
          dsimp [f]
          exact_mod_cast Nat.factorial_pos (j - 1)
        have hscaled : f / 16 <
            G * (2 * eta) ^ j *
              ‖variableBandZeroDetectorPolynomial psi.1 E eta j N u‖ := by
          simpa only [j, f, G] using hlarge.1
        have hdiv := div_lt_div_of_pos_right hscaled hf
        have hnormScale :
            ‖(variableDetectorNormalization eta J j : ℂ) *
                variableBandZeroDetectorPolynomial psi.1 E eta j N u‖ =
              variableDetectorNormalization eta J j *
                ‖variableBandZeroDetectorPolynomial psi.1 E eta j N u‖ := by
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg
              (variableDetectorNormalization_nonneg heta.le J j)]
        apply le_of_lt
        calc
          (1 / 16 : ℝ) = (f / 16) / f := by field_simp
          _ < (G * (2 * eta) ^ j *
                ‖variableBandZeroDetectorPolynomial psi.1 E eta j N u‖) /
              f := hdiv
          _ = variableDetectorNormalization eta J j *
                ‖variableBandZeroDetectorPolynomial psi.1 E eta j N u‖ := by
            dsimp [variableDetectorNormalization, G, f]
            ring
          _ = ‖(variableDetectorNormalization eta J j : ℂ) *
                variableBandZeroDetectorPolynomial psi.1 E eta j N u‖ :=
            hnormScale.symm
          _ = ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
                c (order t) n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
            rw [variable_normalized_polynomial_eq_smul]
      · have hinside : (0 : ℝ) < (q : ℝ) * ((T : ℝ) + 2) := by
          positivity
        have hlogle : Real.log ((q : ℝ) * ((T : ℝ) + 2)) ≤
            Real.log B := by
          apply Real.log_le_log hinside
          dsimp [B]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (by positivity)
        have hlogq : eta * Real.log ((q : ℝ) * ((T : ℝ) + 2)) ≤
            eta * Real.log B :=
          mul_le_mul_of_nonneg_left hlogle heta.le
        have hmass := hcoverBound q hq1 psi.1 psi.2 eta (T : ℝ)
          (eta * Real.log B) delta heta heta1 (by positivity)
          hdelta.le hdelta1 hlogq S hSsub hcover
        simpa only [primitiveHighZeroMassAt, dif_pos hq1, Klocal] using hmass
    · exact ⟨∅, fun _ ↦ L, fun h ↦ (hqMem h).elim⟩
  let S : ∀ q : ℕ, primitiveCharacters q → Finset ℝ :=
    fun q psi ↦ Classical.choose (hexists q psi)
  let order : ∀ q : ℕ, primitiveCharacters q → ℝ → ℕ :=
    fun q psi ↦ Classical.choose (Classical.choose_spec (hexists q psi))
  have hchosen (q : ℕ) (psi : primitiveCharacters q) :
      q ∈ Finset.Ioc 1 Q →
        (∀ t ∈ S q psi, 0 ≤ t ∧ t ≤ T) ∧
        (∀ x ∈ S q psi, ∀ y ∈ S q psi, x ≠ y →
          2 * delta * eta < dist x y) ∧
        (∀ t ∈ S q psi, L ≤ order q psi t ∧ order q psi t ≤ J) ∧
        (∀ t ∈ S q psi, ∀ u : ℝ, |u - t| ≤ delta * eta →
          (1 / 16 : ℝ) ≤
            ‖∑ n ∈ Finset.Ioc (Y (order q psi t)) N,
              c (order q psi t) n * psi.1 n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) ∧
        ((primitiveHighZeroMassAt q psi eta T : ℕ) : ℝ) ≤
          ((S q psi).card : ℝ) * Klocal := by
    exact Classical.choose_spec (Classical.choose_spec (hexists q psi))
  have hselected := sum_selectedOrdinates_card_mul_le_variablePrimitiveMass
    Q Y c N T L J eta delta (1 / 16 : ℝ)
      heta heta1 hdelta hdelta1 (by norm_num) S order
      (fun q hq psi ↦ (hchosen q psi hq).1)
      (fun q hq psi ↦ (hchosen q psi hq).2.1)
      (fun q hq psi ↦ (hchosen q psi hq).2.2.1)
      (fun q hq psi ↦ (hchosen q psi hq).2.2.2.1)
  have hselectedUnweighted :=
    sum_selectedOrdinates_card_mul_le_variableUnweightedPrimitiveMass
      Q Y c N T L J eta delta (1 / 16 : ℝ)
        heta heta1 hdelta hdelta1 (by norm_num) S order
        (fun q hq psi ↦ (hchosen q psi hq).1)
        (fun q hq psi ↦ (hchosen q psi hq).2.1)
        (fun q hq psi ↦ (hchosen q psi hq).2.2.1)
        (fun q hq psi ↦ (hchosen q psi hq).2.2.2.1)
  let totalCard : ℝ :=
    ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ((S q psi).card : ℝ)
  have hmass : (primitiveHighZeroMass Q eta T : ℝ) ≤
      totalCard * Klocal := by
    unfold primitiveHighZeroMass
    push_cast
    calc
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (primitiveHighZeroMassAt q psi eta T : ℝ)) ≤
          ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
            ((S q psi).card : ℝ) * Klocal := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro psi hpsi
        exact (hchosen q psi hq).2.2.2.2
      _ = totalCard * Klocal := by
        dsimp [totalCard]
        simp_rw [Finset.sum_mul]
  let c₀ : ℝ := (delta * eta) * (1 / 16 : ℝ) ^ 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hmassSelected :
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
                (c j) u := by
    calc
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
          (totalCard * Klocal) * c₀ :=
        mul_le_mul_of_nonneg_right hmass hc₀
      _ = Klocal * (totalCard * c₀) := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
                (c j) u := by
        apply mul_le_mul_of_nonneg_left _ hKlocal
        simpa only [totalCard, c₀, mul_assoc] using hselected
  have hmassSelectedUnweighted :
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              unweightedPrimitiveNegativeDirichletMass Q
                (Finset.Ioc (Y j) N) (c j) u := by
    calc
      (primitiveHighZeroMass Q eta T : ℝ) * c₀ ≤
          (totalCard * Klocal) * c₀ :=
        mul_le_mul_of_nonneg_right hmass hc₀
      _ = Klocal * (totalCard * c₀) := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              unweightedPrimitiveNegativeDirichletMass Q
                (Finset.Ioc (Y j) N) (c j) u := by
        apply mul_le_mul_of_nonneg_left _ hKlocal
        simpa only [totalCard, c₀, mul_assoc] using hselectedUnweighted
  have hintegrals :
      (∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
              (c j) u) ≤
        ∑ j ∈ Finset.Icc L J,
          variableRawLogFreeDensityTerm T E N J j eta := by
    apply Finset.sum_le_sum
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hYcompare : zeroDetectorLowerCutoff B ≤ Y j := by
      dsimp [Y]
      exact zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hYone : 1 ≤ Y j := by
      exact (show 1 ≤ zeroDetectorLowerCutoff B by
        unfold zeroDetectorLowerCutoff
        have : 0 < 2 ^ zeroDetectorLowerLog B := pow_pos (by omega) _
        omega).trans hYcompare
    have hhybrid : 2 * ((T + 1) + 1) * Q ^ 2 ≤ Y j := by
      have hbase := (detectorLowerCutoff_hybrid_bound Q T hQ).trans hYcompare
      simpa only [Nat.add_assoc, mul_assoc] using hbase
    have hweighted := intervalIntegral_weightedDetectorBand_hybrid_le
      Q (Y j) N (T + 1) (j - 1) (by omega) hYone hhybrid eta heta.le
    calc
      (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
            (c j) u) =
        variableDetectorNormalization eta J j ^ 2 *
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
              (fun n ↦
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
          simpa only [c] using
            intervalIntegral_variableNormalizedDetector_eq
              Q (Y j) N (T + 1) eta J j heta.le
      _ ≤ variableDetectorNormalization eta J j ^ 2 *
          ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
            ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
              (2 * ((j - 1) + 1))) *
            (((Y j : ℝ) / 2) ^ (-(2 * eta)))) :=
        mul_le_mul_of_nonneg_left hweighted (sq_nonneg _)
      _ = variableRawLogFreeDensityTerm T E N J j eta := by
        rfl
  constructor
  · calc
      (primitiveHighZeroMass Q eta T : ℝ) *
            (delta * eta) * (1 / 16 : ℝ) ^ 2 =
          (primitiveHighZeroMass Q eta T : ℝ) * c₀ := by
        dsimp [c₀]
        ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
                (c j) u := hmassSelected
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            variableRawLogFreeDensityTerm T E N J j eta :=
        mul_le_mul_of_nonneg_left hintegrals hKlocal
      _ = _ := by rfl
  · calc
      (primitiveHighZeroMass Q eta T : ℝ) *
            (delta * eta) * (1 / 16 : ℝ) ^ 2 =
          (primitiveHighZeroMass Q eta T : ℝ) * c₀ := by
        dsimp [c₀]
        ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              unweightedPrimitiveNegativeDirichletMass Q
                (Finset.Ioc (Y j) N) (c j) u := hmassSelectedUnweighted
      _ = _ := by rfl

/-- The original weighted raw-density interface, retained for the existing
envelope and power-bound developments. -/
theorem exists_variable_raw_logFreeDensity_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                variableRawLogFreeDensityTerm T E N J j eta := by
  obtain ⟨κ, D, A, hκ, hD, hA, hboth⟩ :=
    exists_variable_raw_and_unweightedIntegral_parameters
  exact ⟨κ, D, A, hκ, hD, hA, fun Q T hQ eta heta heta8 ↦
    (hboth Q T hQ eta heta heta8).1⟩

/-- The same zero-selection construction aggregated with the unweighted
primitive-character mass required by Gallagher's amplifier. -/
theorem exists_variable_unweightedIntegral_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                  unweightedPrimitiveNegativeDirichletMass Q
                    (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
                    (variableNormalizedDetectorCoefficient eta J j) u := by
  obtain ⟨κ, D, A, hκ, hD, hA, hboth⟩ :=
    exists_variable_raw_and_unweightedIntegral_parameters
  exact ⟨κ, D, A, hκ, hD, hA, fun Q T hQ eta heta heta8 ↦
    (hboth Q T hQ eta heta heta8).2⟩

end

end Erdos48
