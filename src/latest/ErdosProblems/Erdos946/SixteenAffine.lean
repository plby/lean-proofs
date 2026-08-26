/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineCore
import ErdosProblems.Erdos946.AffineSieve

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

private lemma prime_dvd_common_of_dvd_fourfold
    {p a b c d : ℕ} (hp : p.Prime) (ha : a ∣ b) (hc : c ∣ d)
    (hdiv : p ∣ a * b * c * d) : p ∣ b * d := by
  rcases hp.dvd_mul.mp hdiv with habc | hd
  · rcases hp.dvd_mul.mp habc with hab | hc'
    · rcases hp.dvd_mul.mp hab with ha' | hb
      · exact dvd_mul_of_dvd_left (ha'.trans ha) _
      · exact dvd_mul_of_dvd_left hb _
    · exact dvd_mul_of_dvd_right (hc'.trans hc) _
  · exact dvd_mul_of_dvd_right hd _

private lemma dvd_fivefold_of_dvd_second
    {x a b c d e : ℕ} (h : x ∣ b) : x ∣ a * b * c * d * e := by
  rcases h with ⟨k, rfl⟩
  refine ⟨a * k * c * d * e, ?_⟩
  ac_rfl

private lemma fourfold_middle_swap (a b c d : ℕ) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  ac_rfl

private lemma fourfold_left_rotate (a b c d : ℕ) :
    (a * b) * (c * d) = (b * c) * (a * d) := by
  ac_rfl

private lemma cross_add_one_expand_left (a b c d : ℕ) :
    a * b * c * d + a * c = (a * c) * (b * d + 1) := by
  ring

private lemma cross_add_one_expand_right (a b c d : ℕ) :
    (b * c) * (a * d + 1) = a * b * c * d + b * c := by
  ring

private lemma quotient_cross_rearrange (a b d : ℕ) :
    a * (b * d) = b * (a * d) := by
  ac_rfl

private lemma mul_affine_add_one_expand (a b C : ℕ) :
    a * (b * C + 1) = (a * b) * C + a := by
  ring

private lemma mul_affine_successor_contract (a b C : ℕ) :
    (b * a) * C + (b + 1) = b * (a * C + 1) + 1 := by
  ring

private lemma mul_sq_coprime_prime_of_not_dvd_mul
    {p M R : ℕ} (hp : p.Prime) (hcore : ¬p ∣ M * R) :
    (M * R ^ 2).Coprime p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hpM | hpR2
  · exact hcore (dvd_mul_of_dvd_left hpM R)
  · exact hcore (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hpR2) M)


/-- Every prime appearing in a slope is already present in the common
fixed core. -/
lemma prime_dvd_commonCore16_of_dvd_affineSlope16 {p : ℕ} (hp : p.Prime)
    (i : Fin 16) (hdiv : p ∣ affineSlope16 i) :
    p ∣ keyCommonMultiplier16 * affinePower16Product := by
  apply prime_dvd_common_of_dvd_fourfold hp
    (keyNumber16_dvd_commonMultiplier i)
    (Nat.div_dvd_of_dvd (keyPower16_dvd_affinePower16Product i))
  rw [affineSlope16_factorization] at hdiv
  exact hdiv

lemma affineSlope16_coprime_of_not_dvd_commonCore16 {p : ℕ} (hp : p.Prime)
    (hn : ¬p ∣ keyCommonMultiplier16 * affinePower16Product) (i : Fin 16) :
    (affineSlope16 i).Coprime p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  exact fun h ↦ hn (prime_dvd_commonCore16_of_dvd_affineSlope16 hp i h)

/-- The explicit sixteen-form family has no fixed prime divisor. -/
lemma affineForm16s_admissible :
    AffineSieve.Admissible affineSlope16 affineConstant16 := by
  intro p hp
  by_cases hpcore : p ∣ keyCommonMultiplier16 * affinePower16Product
  · refine ⟨0, hp.pos, ?_⟩
    intro i
    simp only [mul_zero, zero_add]
    have hc : (affineConstant16 i).Coprime p :=
      Nat.Coprime.of_dvd_right hpcore (affineConstant16_coprime_commonCore16 i)
    exact hp.coprime_iff_not_dvd.mp hc.symm
  · have hslope : ∀ i : Fin 16, (affineSlope16 i).Coprime p :=
      affineSlope16_coprime_of_not_dvd_commonCore16 hp hpcore
    have hpgt : 16 < p := by
      by_contra hnlt
      have hple : p ≤ 16 := by omega
      have hpfac : p ∣ Nat.factorial 16 := hp.dvd_factorial.mpr hple
      have hpcommon : p ∣ keyCommonMultiplier16 := by
        rw [keyCommonMultiplier16]
        exact dvd_mul_of_dvd_left hpfac _
      exact hpcore (dvd_mul_of_dvd_left hpcommon _)
    have hcard :
        (AffineSieve.affineResidues affineSlope16 affineConstant16 p).card <
          (Finset.range p).card := by
      rw [Finset.card_range]
      change AffineSieve.localNu affineSlope16 affineConstant16 p < p
      exact (AffineSieve.localNu_le_card hp hslope).trans_lt (by simpa using hpgt)
    obtain ⟨r, hrange, hrnot⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨r, Finset.mem_range.mp hrange, ?_⟩
    intro i hdiv
    apply hrnot
    rw [AffineSieve.mem_affineResidues]
    refine ⟨Finset.mem_range.mp hrange, ?_⟩
    exact (AffineSieve.prime_dvd_affineProduct_iff hp).mpr ⟨i, hdiv⟩

lemma affineForm16_gt_parameter (i : Fin 16) (t : ℕ) : t < affineForm16 i t := by
  have hcoefficient : 0 < keyCongruence16Coefficient i := by
    rw [keyCongruence16Coefficient]
    exact mul_pos ((keyNumber16_gt_one i).trans' Nat.zero_lt_one)
      keyCommonMultiplier16_pos
  have hslope : 0 < keyCongruence16Coefficient i * affinePower16Cofactor i *
      affinePower16Product := by
    apply mul_pos
    · apply mul_pos
      · exact hcoefficient
      · exact affinePower16Cofactor_pos i
    · exact affinePower16Product_pos
  have hmul : t ≤
      (keyCongruence16Coefficient i * affinePower16Cofactor i *
        affinePower16Product) * t := by
    exact Nat.le_mul_of_pos_left t hslope
  rw [affineForm16]
  have hconstant := affineConstant16_pos i
  omega

/-- Every quotient of a key integer by a pairwise gcd is coprime to every
corresponding affine form.  This is why all key integers were included in
the common multiplier. -/
lemma keyGcdQuotient_coprime_affineForm16 (i j : Fin 16) (t : ℕ) :
    (keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)).Coprime
      (affineForm16 j t) := by
  let x := keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)
  have hxA : x ∣ keyCommonMultiplier16 :=
    keyGcdQuotient_dvd_commonMultiplier i j
  have hmultiple : x ∣
      keyNumber16 j * keyCommonMultiplier16 * affineCRT16Parameter := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hxA (keyNumber16 j)) _
  have hconstProd : keyPower16 j * affineConstant16 j ≡ 1 [MOD x] := by
    rw [keyPower16_mul_affineConstant16, keyCongruence16Coefficient]
    exact Nat.add_modEq_right_iff.mpr hmultiple
  have hconst : (affineConstant16 j).Coprime x := by
    apply Nat.coprime_of_mul_modEq_one (keyPower16 j)
    simpa [mul_comm] using hconstProd
  have hslope : x ∣
      keyCongruence16Coefficient j * affinePower16Cofactor j *
        affinePower16Product * t := by
    rw [keyCongruence16Coefficient]
    exact dvd_fivefold_of_dvd_second hxA
  rw [affineForm16]
  exact ((Nat.add_coprime_iff_right hslope).mpr hconst).symm

lemma keyNumber16_ne_of_ne (i j : Fin 16) (hij : i ≠ j) :
    keyNumber16 i ≠ keyNumber16 j := by
  exact SixteenKey.keyNumber16_injective.ne hij

lemma keyNumber16_sub_eq_gcd {i j : Fin 16}
    (hji : keyNumber16 j < keyNumber16 i) :
    keyNumber16 i - keyNumber16 j = (keyNumber16 i).gcd (keyNumber16 j) := by
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  rw [SixteenKey.keyNumber16_gcd_eq_distance hij,
    SixteenKey.keyDistance16_eq_numberDistance]
  simp [Nat.not_le_of_gt hji]

private lemma affine_cross_scaled {p : ℕ} (i j : Fin 16)
    (hcross : affineSlope16 i * affineConstant16 j ≡
      affineSlope16 j * affineConstant16 i [MOD p]) :
    (keyPower16 i * affineSlope16 i) *
        (keyPower16 j * affineConstant16 j) ≡
      (keyPower16 j * affineSlope16 j) *
        (keyPower16 i * affineConstant16 i) [MOD p] := by
  calc
    (keyPower16 i * affineSlope16 i) *
        (keyPower16 j * affineConstant16 j) =
        (keyPower16 i * keyPower16 j) *
          (affineSlope16 i * affineConstant16 j) := by
            exact fourfold_middle_swap _ _ _ _
    _ ≡ (keyPower16 i * keyPower16 j) *
          (affineSlope16 j * affineConstant16 i) [MOD p] :=
        hcross.mul_left _
    _ = (keyPower16 j * affineSlope16 j) *
        (keyPower16 i * affineConstant16 i) := by
          exact fourfold_left_rotate _ _ _ _

private lemma affine_cross_expanded {p : ℕ} (i j : Fin 16)
    (hcross : affineSlope16 i * affineConstant16 j ≡
      affineSlope16 j * affineConstant16 i [MOD p]) :
    (keyNumber16 i *
        (keyCommonMultiplier16 * affinePower16Product ^ 2)) *
          (keyNumber16 j *
            (keyCommonMultiplier16 * affineCRT16Parameter) + 1) ≡
      (keyNumber16 j *
        (keyCommonMultiplier16 * affinePower16Product ^ 2)) *
          (keyNumber16 i *
            (keyCommonMultiplier16 * affineCRT16Parameter) + 1) [MOD p] := by
  simpa only [keyPower16_mul_affineSlope16,
    keyPower16_mul_affineConstant16_common] using
      (affine_cross_scaled i j hcross)

private lemma coefficient_modEq_of_cross {p a b C D : ℕ}
    (hcross : (a * C) * (b * D + 1) ≡
      (b * C) * (a * D + 1) [MOD p]) :
    a * C ≡ b * C [MOD p] := by
  apply Nat.ModEq.add_left_cancel' (a * b * C * D)
  calc
    a * b * C * D + a * C = (a * C) * (b * D + 1) := by
      exact cross_add_one_expand_left _ _ _ _
    _ ≡ (b * C) * (a * D + 1) [MOD p] := hcross
    _ = a * b * C * D + b * C := by
      exact cross_add_one_expand_right _ _ _ _

private lemma commonSlopeCore_coprime_prime {p : ℕ} (hp : p.Prime)
    (hpcore : ¬p ∣ keyCommonMultiplier16 * affinePower16Product) :
    (keyCommonMultiplier16 * affinePower16Product ^ 2).Coprime p := by
  exact mul_sq_coprime_prime_of_not_dvd_mul hp hpcore

private lemma keyNumber_modEq_of_affine_cross {p : ℕ} (hp : p.Prime)
    (hpcore : ¬p ∣ keyCommonMultiplier16 * affinePower16Product)
    (i j : Fin 16)
    (hcross : affineSlope16 i * affineConstant16 j ≡
      affineSlope16 j * affineConstant16 i [MOD p]) :
    keyNumber16 i ≡ keyNumber16 j [MOD p] := by
  have hcoefficient := coefficient_modEq_of_cross
    (affine_cross_expanded i j hcross)
  exact hcoefficient.cancel_right_of_coprime
    (commonSlopeCore_coprime_prime hp hpcore).symm.gcd_eq_one

private lemma prime_dvd_commonMultiplier_of_key_modEq {p : ℕ}
    (i j : Fin 16) (hij : i ≠ j)
    (hnumber : keyNumber16 i ≡ keyNumber16 j [MOD p]) :
    p ∣ keyCommonMultiplier16 := by
  have hne := keyNumber16_ne_of_ne i j hij
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hpdiff : p ∣ keyNumber16 j - keyNumber16 i := hnumber.dvd'
    rw [keyNumber16_sub_eq_gcd hijlt] at hpdiff
    exact hpdiff.trans (Nat.gcd_dvd_left _ _ |>.trans
      (keyNumber16_dvd_commonMultiplier j))
  · have hpdiff : p ∣ keyNumber16 i - keyNumber16 j := hnumber.symm.dvd'
    rw [keyNumber16_sub_eq_gcd hjilt] at hpdiff
    exact hpdiff.trans (Nat.gcd_dvd_left _ _ |>.trans
      (keyNumber16_dvd_commonMultiplier i))

/-- Outside the fixed common core, two distinct forms have different roots
modulo every prime.  This is the determinant condition in Pinner's
hypothesis: after multiplying by the two attached powers, the determinant
collapses to the common slope times `keyNumber16 i - keyNumber16 j`. -/
lemma affine_cross_not_modEq_of_not_dvd_commonCore16 {p : ℕ} (hp : p.Prime)
    (hpcore : ¬p ∣ keyCommonMultiplier16 * affinePower16Product)
    (i j : Fin 16) (hij : i ≠ j) :
    ¬affineSlope16 i * affineConstant16 j ≡
      affineSlope16 j * affineConstant16 i [MOD p] := by
  intro hcross
  have hnumber := keyNumber_modEq_of_affine_cross hp hpcore i j hcross
  have hpcommon := prime_dvd_commonMultiplier_of_key_modEq i j hij hnumber
  exact hpcore (dvd_mul_of_dvd_left hpcommon affinePower16Product)

/-- The local density of the explicit family is exactly sixteen away from
the finite common core. -/
lemma affineForms16_localNu_eq_sixteen {p : ℕ} (hp : p.Prime)
    (hpcore : ¬p ∣ keyCommonMultiplier16 * affinePower16Product) :
    AffineSieve.localNu affineSlope16 affineConstant16 p = 16 := by
  simpa using AffineSieve.localNu_eq_card hp
    (affineSlope16_coprime_of_not_dvd_commonCore16 hp hpcore)
    (affine_cross_not_modEq_of_not_dvd_commonCore16 hp hpcore)

/-- The two ordered forms differ by exactly one after multiplication by the
quotients occurring in the key identity. -/
lemma affineForm16_pair_identity {i j : Fin 16}
    (hji : keyNumber16 j < keyNumber16 i) (t : ℕ) :
    (keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)) *
          keyPower16 j * affineForm16 j t =
      (keyNumber16 j / (keyNumber16 i).gcd (keyNumber16 j)) *
          keyPower16 i * affineForm16 i t + 1 := by
  let d := (keyNumber16 i).gcd (keyNumber16 j)
  let C := keyCommonMultiplier16 * affinePower16Product ^ 2 * t +
    keyCommonMultiplier16 * affineCRT16Parameter
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by
    exact (keyNumber16_gt_one i).trans' Nat.zero_lt_one)
  have hdi : d ∣ keyNumber16 i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ keyNumber16 j := Nat.gcd_dvd_right _ _
  have hsub : keyNumber16 i = keyNumber16 j + d := by
    have h := keyNumber16_sub_eq_gcd hji
    dsimp [d]
    omega
  have hquot : keyNumber16 i / d = keyNumber16 j / d + 1 := by
    apply Nat.mul_right_cancel hdpos
    rw [Nat.add_mul, Nat.div_mul_cancel hdi, Nat.div_mul_cancel hdj]
    simpa using hsub
  have hcross :
      (keyNumber16 i / d) * keyNumber16 j =
        (keyNumber16 j / d) * keyNumber16 i := by
    calc
      (keyNumber16 i / d) * keyNumber16 j =
      (keyNumber16 i / d) * ((keyNumber16 j / d) * d) := by
            rw [Nat.div_mul_cancel hdj]
      _ = (keyNumber16 j / d) * ((keyNumber16 i / d) * d) := by
            exact quotient_cross_rearrange _ _ _
      _ = (keyNumber16 j / d) * keyNumber16 i := by
            rw [Nat.div_mul_cancel hdi]
  change (keyNumber16 i / d) * keyPower16 j * affineForm16 j t =
    (keyNumber16 j / d) * keyPower16 i * affineForm16 i t + 1
  have hleft :
      (keyNumber16 i / d) * keyPower16 j * affineForm16 j t =
        (keyNumber16 i / d) * (keyNumber16 j * C + 1) := by
    rw [mul_assoc, keyPower16_mul_affineForm16]
  have hright :
      (keyNumber16 j / d) * keyPower16 i * affineForm16 i t =
        (keyNumber16 j / d) * (keyNumber16 i * C + 1) := by
    rw [mul_assoc, keyPower16_mul_affineForm16]
  rw [hleft, hright]
  change (keyNumber16 i / d) * (keyNumber16 j * C + 1) =
    (keyNumber16 j / d) * (keyNumber16 i * C + 1) + 1
  calc
    (keyNumber16 i / d) * (keyNumber16 j * C + 1) =
        ((keyNumber16 i / d) * keyNumber16 j) * C +
          keyNumber16 i / d := by
            exact mul_affine_add_one_expand _ _ _
    _ = ((keyNumber16 j / d) * keyNumber16 i) * C +
          (keyNumber16 j / d + 1) := by rw [hcross, hquot]
    _ = (keyNumber16 j / d) * (keyNumber16 i * C + 1) + 1 := by
          exact mul_affine_successor_contract _ _ _

lemma keyGcdQuotient_coprime_keyPower16 (i j k : Fin 16) :
    (keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)).Coprime
      (keyPower16 k) := by
  apply Nat.Coprime.of_dvd
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (keyNumber16 i) (keyNumber16 j)))
    dvd_rfl
  exact (keyPower16_coprime_keyNumber16 k i).symm

/-- For an ordered pair, the two sides of the consecutive identity have
equal divisor counts whenever the corresponding affine forms do. -/
lemma affineForm16_pair_tau_eq {i j : Fin 16} (hij : i ≠ j)
    (t : ℕ) (htau : σ 0 (affineForm16 i t) = σ 0 (affineForm16 j t)) :
    σ 0 ((keyNumber16 j / (keyNumber16 i).gcd (keyNumber16 j)) *
          keyPower16 i * affineForm16 i t) =
      σ 0 ((keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)) *
          keyPower16 j * affineForm16 j t) := by
  let d := (keyNumber16 i).gcd (keyNumber16 j)
  have hyPower : (keyNumber16 j / d).Coprime (keyPower16 i) := by
    have h := keyGcdQuotient_coprime_keyPower16 j i i
    simpa [d, Nat.gcd_comm] using h
  have hxPower : (keyNumber16 i / d).Coprime (keyPower16 j) := by
    exact keyGcdQuotient_coprime_keyPower16 i j j
  have hyForm : (keyNumber16 j / d).Coprime (affineForm16 i t) := by
    have h := keyGcdQuotient_coprime_affineForm16 j i t
    simpa [d, Nat.gcd_comm] using h
  have hxForm : (keyNumber16 i / d).Coprime (affineForm16 j t) := by
    exact keyGcdQuotient_coprime_affineForm16 i j t
  have hyOuter : (keyNumber16 j / d).Coprime
      (keyPower16 i * affineForm16 i t) := hyPower.mul_right hyForm
  have hxOuter : (keyNumber16 i / d).Coprime
      (keyPower16 j * affineForm16 j t) := hxPower.mul_right hxForm
  have hkey := keyNumber16_sigma_balance i j hij
  change σ 0 ((keyNumber16 j / d) * keyPower16 i * affineForm16 i t) =
    σ 0 ((keyNumber16 i / d) * keyPower16 j * affineForm16 j t)
  calc
    σ 0 ((keyNumber16 j / d) * keyPower16 i * affineForm16 i t) =
        σ 0 (keyNumber16 j / d) *
          (σ 0 (keyPower16 i) * σ 0 (affineForm16 i t)) := by
            rw [mul_assoc,
              ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
                hyOuter,
              ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
                (affineForm16_coprime_keyPower16 i t).symm]
    _ = (σ 0 (keyNumber16 i) * σ 0 (keyNumber16 j / d)) *
          σ 0 (affineForm16 i t) := by
            rw [sigma_zero_keyPower16]
            ring
    _ = (σ 0 (keyNumber16 j) * σ 0 (keyNumber16 i / d)) *
          σ 0 (affineForm16 i t) := by
            simpa [d] using congrArg (fun z => z * σ 0 (affineForm16 i t)) hkey
    _ = σ 0 (keyNumber16 i / d) *
          (σ 0 (keyPower16 j) * σ 0 (affineForm16 j t)) := by
            rw [sigma_zero_keyPower16, ← htau]
            ring
    _ = σ 0 ((keyNumber16 i / d) * keyPower16 j * affineForm16 j t) := by
            rw [mul_assoc,
              ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
                hxOuter,
              ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
                (affineForm16_coprime_keyPower16 j t).symm]

/- The explicit affine family has the algebraic solution-producing
property required by the sieve handoff. -/

end Erdos946.SixteenAffine
