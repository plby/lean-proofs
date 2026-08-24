import ErdosProblems.Erdos587.PolynomialDenseBoxes

/-!
Transfer polynomial-count coefficient filling to an ordinary proper GAP.
The coefficient cropping and generator-excursion estimates are unchanged;
the resulting cardinality loss is polynomial in reciprocal density at
every fixed rank.
-/

open Erdos587.GeneralizedAP
open scoped Pointwise

namespace Erdos587.CFP

def denseProperFactor (D d : ℕ) : ℕ :=
  nvDenseFactor D d * (((denseBoxCount D d + 1) * (d + 1)) ^ d)

theorem denseProperFactor_pos {D d : ℕ} (hD : 0 < D) : 0 < denseProperFactor D d := by
  unfold denseProperFactor
  exact Nat.mul_pos (nvDenseFactor_pos hD) (by positivity)

theorem denseProperFactor_le {D : ℕ} (hD : 0 < D) (d : ℕ) :
    denseProperFactor D d ≤ (4 * (256 * d + 1) * (d + 1)) ^ d * D ^ (5 * d) := by
  have hone : 1 ≤ D ^ 4 := pow_pos hD 4
  have hcount : denseBoxCount D d + 1 ≤ (256 * d + 1) * D ^ 4 := by
    calc
      denseBoxCount D d + 1 ≤ 256 * d * D ^ 4 + D ^ 4 :=
        Nat.add_le_add (denseBoxCount_le hD d) hone
      _ = (256 * d + 1) * D ^ 4 := by ring
  rw [denseProperFactor, nvDenseFactor_eq_pow, ← mul_pow]
  calc
    (4 * D * ((denseBoxCount D d + 1) * (d + 1))) ^ d ≤
        (4 * D * (((256 * d + 1) * D ^ 4) * (d + 1))) ^ d :=
      Nat.pow_le_pow_left
        (Nat.mul_le_mul_left (4 * D) (Nat.mul_le_mul_right (d + 1) hcount)) d
    _ = ((4 * (256 * d + 1) * (d + 1)) * D ^ 5) ^ d := by
      congr 1
      ring
    _ = (4 * (256 * d + 1) * (d + 1)) ^ d * D ^ (5 * d) := by
      rw [mul_pow, ← pow_mul]

def PolynomialDenseProperOutput (Q : GeneralizedAP) (D : ℕ)
    (Xs : List (Finset ℤ)) (R : GeneralizedAP) : Prop :=
  R.rank = Q.rank ∧ R.Proper ∧
  R.StepsCoordinatewiseMultiples Q ∧
  R.NondegenerateStepMultipliersBoundedBy Q Xs.length ∧
  R.SideLengthsBoundedBy Q Xs.length ∧
  R.carrier ⊆ nvFinsetListSum Xs ∧
  Q.boxCard ≤ denseProperFactor D Q.rank * R.carrier.card

theorem exists_large_proper_GAP_of_dense_summands
    (Q : GeneralizedAP) (D : ℕ) (hD : 0 < D) (hQproper : Q.Proper)
    (Xs : List (Finset ℤ)) (hlen : Xs.length = denseBoxCount D Q.rank)
    (hXs : ∀ X ∈ Xs, X ⊆ Q.carrier)
    (hdense : ∀ X ∈ Xs, Q.boxCard ≤ D * X.card) :
    ∃ R : GeneralizedAP, PolynomialDenseProperOutput Q D Xs R := by
  let Cs := Xs.map Q.pullbackCoeffs
  have hCsLen : Cs.length = denseBoxCount D Q.rank := by
    simpa [Cs] using hlen
  have hCsSub : ∀ C ∈ Cs, C ⊆ nvCoordBox Q.length := by
    intro C hC
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hC
    exact Q.pullbackCoeffs_subset_coordBox X
  have hCsDense : ∀ C ∈ Cs, (nvCoordBox Q.length).card ≤ D * C.card := by
    intro C hC
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hC
    rw [card_nvCoordBox, Q.card_pullbackCoeffs hQproper (hXs X hX)]
    exact hdense X hX
  obtain ⟨P, hPproper, hPaxis, hPsub, hPcard⟩ :=
    exists_large_coordinate_GAP_of_dense_summands D hD Q.length Cs hCsLen hCsSub hCsDense
  let t := Xs.length
  let C := (t + 1) * (Q.rank + 1)
  let Pt := P.truncate C
  let R := Q.pushCoeffGAP t Pt
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hPtproper : Pt.Proper := P.proper_truncate C hPproper
  have hPtaxis : Pt.AxisAligned := P.axisAligned_truncate C hPaxis
  have hRproper : R.Proper :=
    Q.proper_pushCoeffGAP_truncate t P Cs hQproper
      (by simp [Cs, t]) hCsSub hPproper hPsub
  have hRsteps : R.StepsCoordinatewiseMultiples Q := by
    intro i j hij
    change ∃ a : ℤ, (Q.pushCoeffGAP t Pt).step i = a * Q.step j
    have hidx : i = j := Fin.ext hij
    subst i
    exact ⟨Pt.step j j, Q.pushCoeffGAP_step_eq_of_axisAligned t Pt hPtaxis j⟩
  have hRside : R.SideLengthsBoundedBy Q Xs.length := by
    intro i j hij
    change P.length i / C ≤ Xs.length * Q.length j
    have hidx : i = j := Fin.ext hij
    subst i
    by_cases hz : P.length j = 0
    · simp [hz]
    have hpos : 0 < P.length j := Nat.pos_of_ne_zero hz
    have hdiag : P.step j j ≠ 0 :=
      P.diagonal_ne_zero_of_axisAligned hPproper hPaxis j hpos
    have habs : (1 : ℤ) ≤ |P.step j j| := Int.one_le_abs hdiag
    have hlenAbs : (P.length j : ℤ) ≤ |(P.length j : ℤ) * P.step j j| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ P.length j by positivity)]
      nlinarith
    have hexc := nvFullGAP_generator_excursion_le P
      (show Cs.length = Xs.length by simp [Cs]) hCsSub hPsub j j
    have hside : P.length j ≤ Xs.length * Q.length j := by
      exact_mod_cast hlenAbs.trans hexc
    exact (Nat.div_le_self _ _).trans hside
  have hRstepBound : R.NondegenerateStepMultipliersBoundedBy Q Xs.length := by
    intro i j hij hilen
    have hidx : i = j := Fin.ext hij
    subst i
    refine ⟨Pt.step j j, Q.pushCoeffGAP_step_eq_of_axisAligned t Pt hPtaxis j, ?_⟩
    change |((P.length j / C : ℕ) : ℤ) * P.step j j| ≤
      ((Xs.length * Q.length j : ℕ) : ℤ)
    have hfactor : |((P.length j / C : ℕ) : ℤ) * P.step j j| ≤
        |(P.length j : ℤ) * P.step j j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg
        (show (0 : ℤ) ≤ ((P.length j / C : ℕ) : ℤ) by positivity),
        abs_of_nonneg (show (0 : ℤ) ≤ P.length j by positivity)]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.div_le_self (P.length j) C) (abs_nonneg (P.step j j))
    exact hfactor.trans (nvFullGAP_generator_excursion_le P
      (show Cs.length = Xs.length by simp [Cs]) hCsSub hPsub j j)
  refine ⟨R, rfl, hRproper, hRsteps, hRstepBound, hRside, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := R.mem_carrier_iff.mp hz
    change (Q.pushCoeffGAP t Pt).eval x ∈ nvFinsetListSum Xs
    rw [Q.eval_pushCoeffGAP t Pt]
    apply Q.eval_nvFinsetListSum_pullbackCoeffs Xs
    apply hPsub
    apply P.carrier_truncate_subset C
    exact NVFullGAP.mem_carrier_iff.mpr
      ⟨Q.pushParamCoeff t Pt x, Q.pushParamCoeff_mem t Pt x, rfl⟩
  · have hbox : Q.boxCard = (nvCoordBox Q.length).card := by simp [boxCard, card_nvCoordBox]
    have hcard : R.carrier.card = Pt.carrier.card := by
      rw [R.card_carrier_of_proper hRproper, NVFullGAP.card_carrier_of_proper Pt hPtproper]
      rfl
    rw [hbox, hcard]
    calc
      (nvCoordBox Q.length).card ≤ nvDenseFactor D Q.rank * P.carrier.card := hPcard
      _ ≤ nvDenseFactor D Q.rank * (C ^ Q.rank * Pt.carrier.card) :=
        Nat.mul_le_mul_left _ (P.card_carrier_le_pow_mul_card_truncate C hCpos hPproper)
      _ = denseProperFactor D Q.rank * Pt.carrier.card := by
        simp only [denseProperFactor, C, t, hlen]
        ring

end Erdos587.CFP
