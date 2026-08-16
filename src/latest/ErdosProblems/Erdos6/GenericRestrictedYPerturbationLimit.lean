import ErdosProblems.Erdos6.GenericRestrictedYEnvelopeLimit
import BoundedGaps.Maynard.ConcreteS2ReciprocalGMeanLimit
import BoundedGaps.Maynard.MaynardS2ReciprocalGSquarefreeFunction

/-!
# Summed restricted-Y perturbation is negligible
-/

namespace Erdos6.Maynard

open Filter
open scoped BigOperators

noncomputable section

def tupleCoordinateOneReciprocalGMass
    (H : Finset ℕ) (R D : ℕ) (m : H) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R
      (primorial D)).filter (fun r => r m = 1),
    1 / |∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)|

def tupleOffFaceReciprocalGMass
    {H : Finset ℕ} (R D : ℕ) (m : H) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R (primorial D),
    ∏ h : tupleOffFace H m,
      BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
        (primorial D) (u h)

theorem tupleReciprocalG_extension_eq_offFace
    {H : Finset ℕ} {R D : ℕ} (m : H)
    {u : tupleOffFace H m → ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R (primorial D)) :
    1 / |∏ h : H, (BoundedGaps.Maynard.maynardS2G
        (tupleOffFaceExtension m u h) : ℝ)| =
      ∏ h : tupleOffFace H m,
        BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
          (primorial D) (u h) := by
  have hrOff := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu
  have hrFull : BoundedGaps.Maynard.IsMaynardDivisorTuple H R
      (primorial D) (tupleOffFaceExtension m u) :=
    (isMaynardDivisorTuple_extension_iff R (primorial D) m u).mpr hrOff
  have hgFull :=
    BoundedGaps.Maynard.maynardS2G_divisorTupleProduct_eq_prod hrFull
  have hgOff :=
    BoundedGaps.Maynard.maynardS2G_divisorTupleProduct_eq_prod hrOff
  have hprod : (∏ h : H, (BoundedGaps.Maynard.maynardS2G
      (tupleOffFaceExtension m u h) : ℝ)) =
      ∏ h : tupleOffFace H m,
        (BoundedGaps.Maynard.maynardS2G (u h) : ℝ) := by
    calc
      _ = (BoundedGaps.Maynard.maynardS2G
          (BoundedGaps.Maynard.divisorTupleProduct H
            (tupleOffFaceExtension m u)) : ℝ) := by
        exact_mod_cast hgFull.symm
      _ = (BoundedGaps.Maynard.maynardS2G
          (BoundedGaps.Maynard.divisorTupleProduct
            (tupleOffFace H m) u) : ℝ) := by
        rw [divisorTupleProduct_extension]
      _ = _ := by exact_mod_cast hgOff
  have hfactor : ∀ h : tupleOffFace H m,
      BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
          (primorial D) (u h) =
        1 / (BoundedGaps.Maynard.maynardS2G (u h) : ℝ) := by
    intro h
    exact BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime
      (hrOff.coordinate_squarefree h) (hrOff.coordinate_coprime_W h)
  have hprod0 : 0 ≤ ∏ h : tupleOffFace H m,
      (BoundedGaps.Maynard.maynardS2G (u h) : ℝ) :=
    by
      apply Finset.prod_nonneg
      intro h hh
      exact_mod_cast Nat.zero_le (BoundedGaps.Maynard.maynardS2G (u h))
  rw [hprod, abs_of_nonneg hprod0]
  rw [show (∏ h : tupleOffFace H m,
      BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
        (primorial D) (u h)) =
      ∏ h : tupleOffFace H m,
        (1 / (BoundedGaps.Maynard.maynardS2G (u h) : ℝ)) by
      apply Finset.prod_congr rfl
      intro h hh
      exact hfactor h,
    Finset.prod_div_distrib]
  simp

theorem tupleCoordinateOneReciprocalGMass_eq_offFace
    (H : Finset ℕ) (R D : ℕ) (m : H) :
    tupleCoordinateOneReciprocalGMass H R D m =
      tupleOffFaceReciprocalGMass R D m := by
  unfold tupleCoordinateOneReciprocalGMass tupleOffFaceReciprocalGMass
  rw [sum_coordinateOneSupport_eq_offFace]
  apply Finset.sum_congr rfl
  intro u hu
  exact tupleReciprocalG_extension_eq_offFace m hu

theorem tupleReciprocalGSquarefreeAF_nonneg (W n : ℕ) :
    0 ≤ BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W n := by
  by_cases hn : Squarefree n
  · by_cases hcop : Nat.Coprime n W
    · rw [BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime
        hn hcop]
      positivity
    · by_cases hn0 : n = 0
      · subst n
        simp
      · obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
        have hpMem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn0
        unfold BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
        rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
        rw [BoundedGaps.Maynard.maynardS2ReciprocalGWeightAF,
          ArithmeticFunction.prodPrimeFactors_apply hn0]
        have hz : ∏ q ∈ n.primeFactors,
            (if q ∣ W then 0 else (1 : ℝ) / ((q - 2 : ℕ) : ℝ)) = 0 := by
          apply Finset.prod_eq_zero hpMem
          simp [hpW]
        rw [hz]
        simp
  · unfold BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
    rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
    have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn
    simp [hmu]

theorem tupleReciprocalGSquarefreeCoordinateSupport_sum_eq_mean
    (W Q : ℕ) :
    (∑ n ∈ BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport W Q,
      BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W n) =
      BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean W Q := by
  unfold BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
  apply Finset.sum_subset
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hnFull hnNot
    by_cases hsq : Squarefree n
    · by_cases hcop : Nat.Coprime n W
      · exact False.elim (hnNot
          (Finset.mem_filter.mpr ⟨hnFull, hsq, hcop⟩))
      · by_cases hn0 : n = 0
        · subst n
          simp
        · obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
          have hpMem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn0
          unfold BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
          rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
          rw [BoundedGaps.Maynard.maynardS2ReciprocalGWeightAF,
            ArithmeticFunction.prodPrimeFactors_apply hn0]
          have hz : ∏ q ∈ n.primeFactors,
              (if q ∣ W then 0 else (1 : ℝ) / ((q - 2 : ℕ) : ℝ)) = 0 := by
            apply Finset.prod_eq_zero hpMem
            simp [hpW]
          rw [hz]
          simp
    · unfold BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
      have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hmu]

theorem tupleOffFaceReciprocalGMass_le_box
    {H : Finset ℕ} (R D : ℕ) (m : H) :
    tupleOffFaceReciprocalGMass R D m ≤
      ∏ _h : tupleOffFace H m,
        BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
          (primorial D) R := by
  let K := tupleOffFace H m
  let W := primorial D
  let Q := fun _ : K => R
  let box := BoundedGaps.Maynard.squarefreeCoprimeTupleBox K W Q
  have hsubset : BoundedGaps.Maynard.maynardDivisorTupleSupport K R W ⊆
      box := by
    intro u hu
    change u ∈ BoundedGaps.Maynard.squarefreeCoprimeTupleBox K W Q
    rw [BoundedGaps.Maynard.squarefreeCoprimeTupleBox,
      Fintype.mem_piFinset]
    intro h
    apply Finset.mem_filter.mpr
    have hs := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu
    have hb := (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp
      hs.mem_maynardDivisorTupleBox) h
    exact ⟨Finset.mem_Icc.mpr ⟨hb.1, hb.2.le⟩,
      hs.coordinate_squarefree h, hs.coordinate_coprime_W h⟩
  let f : (K → ℕ) → ℝ := fun u =>
    ∏ h : K, BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W (u h)
  have hsum : (∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport K R W,
      f u) ≤ ∑ u ∈ box, f u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro u hu hnot
    dsimp [f]
    exact Finset.prod_nonneg fun h hh =>
      tupleReciprocalGSquarefreeAF_nonneg W (u h)
  unfold tupleOffFaceReciprocalGMass
  calc
    _ ≤ ∑ u ∈ box, ∏ h : K,
        BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W (u h) := by
      simpa [K, W, f] using hsum
    _ = ∏ h : K, ∑ n ∈
        BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport W R,
        BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W n := by
      change (∑ u ∈ BoundedGaps.Maynard.squarefreeCoprimeTupleBox K W Q,
        ∏ h : K,
          BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W (u h)) = _
      exact (Finset.prod_univ_sum
        (fun _ : K => BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport W R)
        (fun _ : K => fun n =>
          BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeAF W n)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h hh
      exact tupleReciprocalGSquarefreeCoordinateSupport_sum_eq_mean W R

theorem tupleCoordinateOneSquarePerturbation_eq_envelope_mul_mass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) :
    tupleCoordinateOneSquarePerturbation H alpha N m =
      tupleCoordinateOneSquarePerturbationEnvelope H
          (maynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m 1 *
        tupleCoordinateOneReciprocalGMass H (maynardRadius alpha N)
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m := by
  unfold tupleCoordinateOneSquarePerturbation
    tupleCoordinateOneReciprocalGMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem tendsto_normalizedTupleCoordinateOneSquarePerturbation_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) (m : H) :
    Tendsto (fun N : ℕ =>
      tupleCoordinateOneSquarePerturbation H alpha N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N))
      atTop (nhds 0) := by
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R : ℕ → ℕ := fun N => maynardRadius alpha N
  let L : ℕ → ℝ := fun N => Real.log (R N)
  let S : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries (D N)
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
      (primorial (D N)) (R N)
  let k := Fintype.card (tupleOffFace H m)
  have hmean : Tendsto (fun N : ℕ => M N / Q N)
      atTop (nhds 1) := by
    simpa [M, Q, S, L, D, R, maynardRadius,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one
        halpha
  have hmeanPow : Tendsto (fun N : ℕ => M N ^ k / Q N ^ k)
      atTop (nhds 1) := by
    simpa [div_pow] using hmean.pow k
  have hboxLe : ∀ᶠ N : ℕ in atTop, M N ^ k / Q N ^ k ≤ 2 := by
    filter_upwards [hmeanPow.eventually
      (Metric.ball_mem_nhds (1 : ℝ) one_pos)] with N hN
    have hd : |M N ^ k / Q N ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self (M N ^ k / Q N ^ k - 1)]
  have hL := BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hQpos : ∀ᶠ N : ℕ in atTop, 0 < Q N := by
    filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLN
    exact mul_pos (BoundedGaps.Maynard.preSieveSingularSeries_pos _) hLN
  have hmassLe : ∀ᶠ N : ℕ in atTop,
      tupleCoordinateOneReciprocalGMass H (R N) (D N) m /
        tupleNaturalScale (tupleOffFace H m) alpha N ≤ 2 := by
    filter_upwards [hboxLe, hQpos] with N hbox hQN
    rw [tupleCoordinateOneReciprocalGMass_eq_offFace]
    have hb := tupleOffFaceReciprocalGMass_le_box (R N) (D N) m
    have hscale : tupleNaturalScale (tupleOffFace H m) alpha N = Q N ^ k := by
      rfl
    rw [hscale]
    exact (div_le_div_of_nonneg_right hb (pow_nonneg hQN.le _)).trans (by
      simpa [M, k] using hbox)
  have hmass0 : ∀ᶠ N : ℕ in atTop,
      0 ≤ tupleCoordinateOneReciprocalGMass H (R N) (D N) m := by
    filter_upwards [] with N
    unfold tupleCoordinateOneReciprocalGMass
    exact Finset.sum_nonneg fun r hr => div_nonneg (by norm_num) (abs_nonneg _)
  have hscalePos := eventually_tupleNaturalScale_pos
    (H := tupleOffFace H m) halpha
  have henv :=
    tendsto_tupleCoordinateOneSquarePerturbationEnvelope_div_squareScale_zero
      (H := H) halpha m
  have hupper : Tendsto (fun N : ℕ =>
      2 * |tupleCoordinateOneSquarePerturbationEnvelope H (R N) (D N) m 1 /
        (S N ^ 2 * L N ^ 2)|) atTop (nhds 0) := by
    have ha := henv.abs
    simpa [R, D, S, L, maynardRadius] using ha.const_mul 2
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hupper
  filter_upwards [hmassLe, hmass0, hscalePos, hQpos] with
      N hmass hmassN hscale hQN
  have hmassRatio0 : 0 ≤ tupleCoordinateOneReciprocalGMass H (R N) (D N) m /
      tupleNaturalScale (tupleOffFace H m) alpha N :=
    div_nonneg hmassN hscale.le
  rw [tupleCoordinateOneSquarePerturbation_eq_envelope_mul_mass]
  have hid :
      tupleCoordinateOneSquarePerturbationEnvelope H (R N) (D N) m 1 *
          tupleCoordinateOneReciprocalGMass H (R N) (D N) m /
        (S N ^ 2 * L N ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N) =
      (tupleCoordinateOneSquarePerturbationEnvelope H (R N) (D N) m 1 /
          (S N ^ 2 * L N ^ 2)) *
        (tupleCoordinateOneReciprocalGMass H (R N) (D N) m /
          tupleNaturalScale (tupleOffFace H m) alpha N) := by
    field_simp [hscale.ne', hQN.ne']
  rw [show BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (maynardRadius alpha N) ^ 2 = S N ^ 2 * L N ^ 2 by rfl,
      hid, abs_mul]
  rw [abs_of_nonneg hmassRatio0]
  change |tupleCoordinateOneSquarePerturbationEnvelope H (R N) (D N) m 1 /
        (S N ^ 2 * L N ^ 2)| *
      (tupleCoordinateOneReciprocalGMass H (R N) (D N) m /
        tupleNaturalScale (tupleOffFace H m) alpha N) ≤
    2 * |tupleCoordinateOneSquarePerturbationEnvelope H (R N) (D N) m 1 /
      (S N ^ 2 * L N ^ 2)|
  have hmul := mul_le_mul_of_nonneg_left hmass
    (abs_nonneg (tupleCoordinateOneSquarePerturbationEnvelope H
      (R N) (D N) m 1 / (S N ^ 2 * L N ^ 2)))
  nlinarith

end

end Erdos6.Maynard
