import ErdosProblems.Erdos946.SixteenKeyCertificate

open scoped ArithmeticFunction.sigma BigOperators

namespace Erdos946.SixteenKey


lemma keyPairFactor16_pairwise :
    ((Finset.univ : Finset KeyPair16) : Set KeyPair16).Pairwise
      (fun ij kl ↦
        (keyPairFactor16 ij.1.1 ij.1.2).Coprime
          (keyPairFactor16 kl.1.1 kl.1.2)) := by
  intro ij _hi kl _hk hne
  have hrank : keyPairRank16 ij.1.1 ij.1.2 ij.2 ≠
      keyPairRank16 kl.1.1 kl.1.2 kl.2 :=
    keyPairRank16_injective.ne hne
  rw [keyPairFactor16, dif_pos ij.2, keyPairFactor16, dif_pos kl.2]
  exact keyPairFactorTable16_pairwise (Finset.mem_univ _)
    (Finset.mem_univ _) hrank

def keyPairProduct16 : ℕ :=
  ∏ ij : KeyPair16, keyPairFactor16 ij.1.1 ij.1.2

lemma keyPairFactor16_dvd_product (ij : KeyPair16) :
    keyPairFactor16 ij.1.1 ij.1.2 ∣ keyPairProduct16 :=
  Finset.dvd_prod_of_mem (f := fun kl : KeyPair16 ↦
    keyPairFactor16 kl.1.1 kl.1.2) (Finset.mem_univ ij)

lemma keySmallModulus16_coprime_pairProduct :
    keySmallModulus16.Coprime keyPairProduct16 := by
  unfold keyPairProduct16
  apply Nat.Coprime.prod_right
  intro ij _hij
  exact keySmallModulus16_coprime_pairFactor ij

lemma keyAuxProduct16_coprime_pairProduct :
    keyAuxProduct16.Coprime keyPairProduct16 := by
  unfold keyPairProduct16
  apply Nat.Coprime.prod_right
  intro ij _hij
  exact keyAuxProduct16_coprime_pairFactor ij



lemma keyCRTModulusAt16_ne_zero (i : KeyCRTIndex16) :
    keyCRTModulusAt16 i ≠ 0 := by
  rcases i with i | ij
  · fin_cases i
    · simpa [keyCRTModulusAt16] using Nat.ne_of_gt keySmallModulus16_pos
    · simpa [keyCRTModulusAt16] using Nat.ne_of_gt keyAuxProduct16_pos
  · have := keyPairFactor16_pos
        (show ij.1.1 ≠ ij.1.2 by exact Fin.ne_of_lt ij.2)
    simp [keyCRTModulusAt16, Nat.ne_of_gt this]

lemma keyCRTModulusAt16_pairwise_coprime :
    ((Finset.univ : Finset KeyCRTIndex16) : Set KeyCRTIndex16).Pairwise
      (fun i j ↦ (keyCRTModulusAt16 i).Coprime
        (keyCRTModulusAt16 j)) := by
  intro i _hi j _hj hij
  rcases i with i | ij <;> rcases j with j | kl
  · fin_cases i <;> fin_cases j <;> simp_all [keyCRTModulusAt16]
    · exact keySmallModulus16_coprime_auxProduct
    · exact keySmallModulus16_coprime_auxProduct.symm
  · fin_cases i
    · apply Nat.Coprime.pow_right
      exact keySmallModulus16_coprime_pairProduct.of_dvd_right
        (keyPairFactor16_dvd_product kl)
    · apply Nat.Coprime.pow_right
      exact keyAuxProduct16_coprime_pairProduct.of_dvd_right
        (keyPairFactor16_dvd_product kl)
  · fin_cases j
    · apply Nat.Coprime.pow_left
      exact keySmallModulus16_coprime_pairProduct.symm.of_dvd_left
        (keyPairFactor16_dvd_product ij)
    · apply Nat.Coprime.pow_left
      exact keyAuxProduct16_coprime_pairProduct.symm.of_dvd_left
        (keyPairFactor16_dvd_product ij)
  · exact Nat.Coprime.pow 2 2
      (keyPairFactor16_pairwise (Finset.mem_univ ij)
        (Finset.mem_univ kl) (by simpa using hij))

noncomputable def keyCRTBase16 : ℕ :=
  Nat.chineseRemainderOfFinset keyCRTResidueAt16 keyCRTModulusAt16
    Finset.univ
    (by intro i _; exact keyCRTModulusAt16_ne_zero i)
    keyCRTModulusAt16_pairwise_coprime

noncomputable def keyCRTProduct16 : ℕ :=
  ∏ i : KeyCRTIndex16, keyCRTModulusAt16 i

noncomputable def keyCRTParameter16 : ℕ :=
  keyCRTBase16 + keyCRTProduct16

noncomputable def keyNumber16 (i : Fin 16) : ℕ :=
  keyCRTParameter16 + keyDelta16 i

lemma keyCRTBase16_modEq (i : KeyCRTIndex16) :
    keyCRTBase16 ≡ keyCRTResidueAt16 i [MOD keyCRTModulusAt16 i] := by
  exact (Nat.chineseRemainderOfFinset keyCRTResidueAt16 keyCRTModulusAt16
    Finset.univ
    (by intro j _; exact keyCRTModulusAt16_ne_zero j)
    keyCRTModulusAt16_pairwise_coprime).prop i (Finset.mem_univ i)

lemma keyCRTParameter16_modEq (i : KeyCRTIndex16) :
    keyCRTParameter16 ≡ keyCRTResidueAt16 i [MOD keyCRTModulusAt16 i] := by
  have hdiv : keyCRTModulusAt16 i ∣ keyCRTProduct16 :=
    Finset.dvd_prod_of_mem (f := keyCRTModulusAt16) (Finset.mem_univ i)
  exact (keyCRTBase16_modEq i).add (Nat.modEq_zero_iff_dvd.mpr hdiv)


lemma keyNumber16_modEq_smallPart (i : Fin 16) :
    keyNumber16 i ≡ keySmallPart16 i [MOD keySmallModulus16] := by
  have h := (keyCRTParameter16_modEq (Sum.inl (0 : Fin 2))).add_right
    (keyDelta16 i)
  exact h.trans (keyDelta16_small_spec i)

lemma keyNumber16_modEq_pairFactor (ij : KeyPair16) :
    keyNumber16 ij.1.1 ≡ keyPairFactor16 ij.1.1 ij.1.2 *
      keyPairMultiplier16 ij.1.1 ij.1.2
      [MOD keyPairFactor16 ij.1.1 ij.1.2 ^ 2] := by
  have h := (keyCRTParameter16_modEq (Sum.inr ij)).add_right
    (keyDelta16 ij.1.1)
  exact h.trans (keyPairResidue16_spec ij)

lemma keyNumber16_modEq_aux (i j : Fin 16) :
    keyNumber16 i ≡ 1 + keyDelta16 i [MOD keyAuxPrime16 j] := by
  have hdiv : keyAuxPrime16 j ∣ keyAuxProduct16 :=
    Finset.dvd_prod_of_mem (f := keyAuxPrime16) (Finset.mem_univ j)
  exact ((keyCRTParameter16_modEq (Sum.inl (1 : Fin 2))).of_dvd hdiv).add_right
    (keyDelta16 i)
lemma keyNumber16_injective : Function.Injective keyNumber16 := by
  intro i j h
  unfold keyNumber16 at h
  exact keyDelta16_injective (Nat.add_left_cancel h)

lemma keyNumber16_modEq_distance (i j : Fin 16) :
    keyNumber16 i ≡ keyNumber16 j [MOD keyDistance16 i j] := by
  have hdelta : keyDelta16 i ≡ keyDelta16 j [MOD keyDistance16 i j] := by
    unfold keyDistance16
    split
    next h => exact (Nat.modEq_sub h).symm
    next h => exact Nat.modEq_sub (Nat.le_of_not_ge h)
  simpa only [keyNumber16] using hdelta.add_left keyCRTParameter16

lemma keyDistance16_eq_numberDistance (i j : Fin 16) :
    keyDistance16 i j =
      if keyNumber16 i ≤ keyNumber16 j then
        keyNumber16 j - keyNumber16 i
      else keyNumber16 i - keyNumber16 j := by
  simp only [keyDistance16, keyNumber16, Nat.add_le_add_iff_left,
    Nat.add_sub_add_left]


lemma keyCRTProduct16_pos : 0 < keyCRTProduct16 := by
  rw [keyCRTProduct16]
  exact Finset.prod_pos fun k _hk ↦
    Nat.pos_of_ne_zero (keyCRTModulusAt16_ne_zero k)

lemma keyNumber16_pos (i : Fin 16) : 0 < keyNumber16 i := by
  simp only [keyNumber16, keyCRTParameter16]
  exact Nat.add_pos_left (Nat.add_pos_right _ keyCRTProduct16_pos) _

lemma keyNumber16_gt_one (i : Fin 16) : 1 < keyNumber16 i := by
  have hmod := keyNumber16_modEq_smallPart i
  have hdvd : keySmallPart16 i ∣ keyNumber16 i := by
    exact (hmod.dvd_iff (keySmallPart16_dvd_smallModulus i)).mpr
      (dvd_refl _)
  have hs : 1 < keySmallPart16 i := keySmallPart16_gt_one i
  exact hs.trans_le (Nat.le_of_dvd (keyNumber16_pos i) hdvd)

lemma keyPrime16_pow_exponent_dvd_smallPart (i k : Fin 16) :
    keyPrime16 k ^ keyExponent16 i k ∣ keySmallPart16 i := by
  exact Finset.dvd_prod_of_mem
    (f := fun j : Fin 16 ↦ keyPrime16 j ^ keyExponent16 i j)
    (Finset.mem_univ k)



lemma keyPairFactor16_comm (i j : Fin 16) :
    keyPairFactor16 i j = keyPairFactor16 j i := by
  unfold keyPairFactor16
  by_cases hij : i.1 < j.1
  · simp [hij, hij.asymm]
  by_cases hji : j.1 < i.1
  · simp [hij, hji]
  have hval : i.1 = j.1 := Nat.le_antisymm (Nat.le_of_not_gt hji)
    (Nat.le_of_not_gt hij)
  have heq : i = j := Fin.ext hval
  simp [heq]

lemma keySmallGcd16_dvd_keyNumber_left (i j : Fin 16) :
    keySmallGcd16 i j ∣ keyNumber16 i := by
  exact ((keyNumber16_modEq_smallPart i).dvd_iff
    ((Nat.gcd_dvd_left _ _).trans (keySmallPart16_dvd_smallModulus i))).mpr
      (Nat.gcd_dvd_left _ _)

lemma keySmallGcd16_dvd_keyNumber_right (i j : Fin 16) :
    keySmallGcd16 i j ∣ keyNumber16 j := by
  exact ((keyNumber16_modEq_smallPart j).dvd_iff
    ((Nat.gcd_dvd_right _ _).trans (keySmallPart16_dvd_smallModulus j))).mpr
      (Nat.gcd_dvd_right _ _)

lemma keyPairFactor16_dvd_keyNumber_left {i j : Fin 16} (hij : i ≠ j) :
    keyPairFactor16 i j ∣ keyNumber16 i := by
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · let ij : KeyPair16 := ⟨(i, j), hij'⟩
    dsimp [ij] at *
    exact ((keyNumber16_modEq_pairFactor ⟨(i, j), hij'⟩).dvd_iff
      (by simp [pow_two])).mpr (dvd_mul_right _ _)
  · let ji : KeyPair16 := ⟨(j, i), hji'⟩
    rw [keyPairFactor16_comm i j]
    have hmodji := keyNumber16_modEq_pairFactor ji
    dsimp [ji] at hmodji
    have hright : keyPairFactor16 j i ∣ keyNumber16 j :=
      (hmodji.dvd_iff (by simp [pow_two])).mpr (dvd_mul_right _ _)
    have hdist : keyPairFactor16 j i ∣ keyDistance16 i j := by
      rw [keyDistance16_factorization i j hij]
      rw [keyPairFactor16_comm i j]
      exact dvd_mul_left _ _
    have hmod := (keyNumber16_modEq_distance i j).of_dvd hdist
    exact (hmod.dvd_iff (dvd_refl _)).mpr hright

lemma keyPairFactor16_dvd_keyNumber_right {i j : Fin 16} (hij : i ≠ j) :
    keyPairFactor16 i j ∣ keyNumber16 j := by
  have h := keyPairFactor16_dvd_keyNumber_left (Ne.symm hij)
  simpa only [keyPairFactor16_comm] using h

lemma keyDistance16_dvd_keyNumber_left {i j : Fin 16} (hij : i ≠ j) :
    keyDistance16 i j ∣ keyNumber16 i := by
  rw [keyDistance16_factorization i j hij]
  have hcop : (keySmallGcd16 i j).Coprime (keyPairFactor16 i j) :=
    (keyPairFactor16_coprime_smallPart i j).symm.of_dvd_left
      (Nat.gcd_dvd_left _ _)
  exact hcop.mul_dvd_of_dvd_of_dvd
    (keySmallGcd16_dvd_keyNumber_left i j)
    (keyPairFactor16_dvd_keyNumber_left hij)

lemma keyDistance16_dvd_keyNumber_right {i j : Fin 16} (hij : i ≠ j) :
    keyDistance16 i j ∣ keyNumber16 j := by
  rw [keyDistance16_factorization i j hij]
  have hcop : (keySmallGcd16 i j).Coprime (keyPairFactor16 i j) :=
    (keyPairFactor16_coprime_smallPart i j).symm.of_dvd_left
      (Nat.gcd_dvd_left _ _)
  exact hcop.mul_dvd_of_dvd_of_dvd
    (keySmallGcd16_dvd_keyNumber_right i j)
    (keyPairFactor16_dvd_keyNumber_right hij)

lemma keyNumber16_gcd_eq_distance {i j : Fin 16} (hij : i ≠ j) :
    (keyNumber16 i).gcd (keyNumber16 j) = keyDistance16 i j := by
  apply Nat.dvd_antisymm
  · have hdiff : (keyNumber16 i).gcd (keyNumber16 j) ∣ keyDistance16 i j := by
      rw [keyDistance16_eq_numberDistance]
      split
      · exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      · exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    exact hdiff
  · exact Nat.dvd_gcd (keyDistance16_dvd_keyNumber_left hij)
      (keyDistance16_dvd_keyNumber_right hij)


noncomputable def keyRemainder16 (i j : Fin 16) : ℕ :=
  keyNumber16 i / (keySmallPart16 i * keyPairFactor16 i j)

lemma keyNumber16_factorization {i j : Fin 16} (hij : i ≠ j) :
    keyNumber16 i = keySmallPart16 i * keyPairFactor16 i j *
      keyRemainder16 i j := by
  symm
  exact Nat.mul_div_cancel' <|
    (keyPairFactor16_coprime_smallPart i j).symm.mul_dvd_of_dvd_of_dvd
      (((keyNumber16_modEq_smallPart i).dvd_iff
        (keySmallPart16_dvd_smallModulus i)).mpr (dvd_refl _))
      (keyPairFactor16_dvd_keyNumber_left hij)

lemma keySmallPart16_coprime_remainder {i j : Fin 16} (hij : i ≠ j) :
    (keySmallPart16 i).Coprime (keyRemainder16 i j) := by
  rw [keySmallPart16]
  apply Nat.Coprime.prod_left
  intro k _hk
  apply Nat.Coprime.pow_left
  rw [(keyPrime16_prime k).coprime_iff_not_dvd]
  intro hpU
  have hfac := keyNumber16_factorization hij
  have hpowKey : keyPrime16 k ^ (keyExponent16 i k + 1) ∣
      keyNumber16 i := by
    rw [hfac]
    have hmul := Nat.mul_dvd_mul
      (keyPrime16_pow_exponent_dvd_smallPart i k)
      (dvd_mul_of_dvd_right hpU (keyPairFactor16 i j))
    simpa [pow_succ, mul_assoc] using hmul
  have hmod : keyNumber16 i ≡ keySmallPart16 i
      [MOD keyPrime16 k ^ (keyExponent16 i k + 1)] :=
    (keyNumber16_modEq_smallPart i).of_dvd
      (keyPrime16_pow_succ_exponent_dvd_modulus i k)
  have hzero : keyNumber16 i ≡ 0
      [MOD keyPrime16 k ^ (keyExponent16 i k + 1)] :=
    Nat.modEq_zero_iff_dvd.mpr hpowKey
  exact keyPrime16_pow_succ_exponent_not_dvd_smallPart i k
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hzero))

lemma keyPairFactor16_coprime_remainder {i j : Fin 16} (hij : i ≠ j) :
    (keyPairFactor16 i j).Coprime (keyRemainder16 i j) := by
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · let ij : KeyPair16 := ⟨(i, j), hij'⟩
    have hfac := keyNumber16_factorization hij
    have hmod := keyNumber16_modEq_pairFactor ij
    dsimp [ij] at hmod
    rw [hfac, show keySmallPart16 i * keyPairFactor16 i j *
        keyRemainder16 i j = keyPairFactor16 i j *
          (keySmallPart16 i * keyRemainder16 i j) by ring,
      pow_two] at hmod
    have hmod' : keyPairFactor16 i j *
          (keySmallPart16 i * keyRemainder16 i j) ≡
        keyPairFactor16 i j * keyPairMultiplier16 i j
          [MOD keyPairFactor16 i j * keyPairFactor16 i j] := by
      simpa using hmod
    have hq : keySmallPart16 i * keyRemainder16 i j ≡
        keyPairMultiplier16 i j
        [MOD keyPairFactor16 i j] :=
      Nat.ModEq.mul_left_cancel'
        (Nat.ne_of_gt (keyPairFactor16_pos hij)) hmod'
    have hcop : (keyPairFactor16 i j).Coprime
        (keySmallPart16 i * keyRemainder16 i j) := by
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, hq.gcd_eq]
      exact (keyPairFactor16_coprime_multiplier i j hij).symm
    exact hcop.of_dvd_right (dvd_mul_left _ _)
  · have hsymm : keyPairFactor16 i j = keyPairFactor16 j i := by
      exact keyPairFactor16_comm i j
    rw [hsymm]
    have hdiv : keyRemainder16 i j ∣ keyNumber16 i /
        keyPairFactor16 j i := by
      have hfac := keyNumber16_factorization hij
      have heq : keyNumber16 i / keyPairFactor16 j i =
          keySmallPart16 i * keyRemainder16 i j := by
        rw [hfac, hsymm]
        rw [show keySmallPart16 i * keyPairFactor16 j i *
            keyRemainder16 i j = keyPairFactor16 j i *
              (keySmallPart16 i * keyRemainder16 i j) by ring,
          Nat.mul_div_right _ (keyPairFactor16_pos (Ne.symm hij))]
      rw [heq]
      exact dvd_mul_left _ _
    let ji : KeyPair16 := ⟨(j, i), hji'⟩
    have hmod := keyNumber16_modEq_pairFactor ji
    dsimp [ji] at hmod
    have hfacj := keyNumber16_factorization (Ne.symm hij)
    rw [hfacj, show keySmallPart16 j * keyPairFactor16 j i *
        keyRemainder16 j i = keyPairFactor16 j i *
          (keySmallPart16 j * keyRemainder16 j i) by ring,
      pow_two] at hmod
    have hmod' : keyPairFactor16 j i *
          (keySmallPart16 j * keyRemainder16 j i) ≡
        keyPairFactor16 j i * keyPairMultiplier16 j i
          [MOD keyPairFactor16 j i * keyPairFactor16 j i] := by
      simpa using hmod
    have hq : keySmallPart16 j * keyRemainder16 j i ≡
        keyPairMultiplier16 j i
        [MOD keyPairFactor16 j i] :=
      Nat.ModEq.mul_left_cancel'
        (Nat.ne_of_gt (keyPairFactor16_pos (Ne.symm hij))) hmod'
    have hquotj : keyNumber16 j / keyPairFactor16 j i =
        keySmallPart16 j * keyRemainder16 j i := by
      rw [hfacj]
      rw [show keySmallPart16 j * keyPairFactor16 j i *
          keyRemainder16 j i = keyPairFactor16 j i *
            (keySmallPart16 j * keyRemainder16 j i) by ring,
        Nat.mul_div_right _ (keyPairFactor16_pos (Ne.symm hij))]
    have hcopj : (keyPairFactor16 j i).Coprime
        (keyNumber16 j / keyPairFactor16 j i) := by
      rw [hquotj]
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, hq.gcd_eq]
      exact (keyPairFactor16_coprime_multiplier j i (Ne.symm hij)).symm
    have hdist : keyNumber16 i / keyPairFactor16 j i =
        keyNumber16 j / keyPairFactor16 j i + keySmallGcd16 i j := by
      have hdji : keyDelta16 j < keyDelta16 i := keyDelta16_strictMono hji'
      have hnum : keyNumber16 i = keyNumber16 j + keyDistance16 i j := by
        simp only [keyNumber16, keyDistance16, if_neg (not_le_of_gt hdji)]
        omega
      have hdfac : keyDistance16 i j =
          keySmallGcd16 i j * keyPairFactor16 j i := by
        rw [keyDistance16_factorization i j hij, keyPairFactor16_comm i j]
      rw [hnum, hdfac, Nat.add_mul_div_right _ _
        (keyPairFactor16_pos (Ne.symm hij))]
    have hcopi : (keyPairFactor16 j i).Coprime
        (keyNumber16 i / keyPairFactor16 j i) := by
      rw [hdist]
      have hqj : keyNumber16 j / keyPairFactor16 j i ≡
          keyPairMultiplier16 j i
          [MOD keyPairFactor16 j i] := by
        rw [hquotj]
        exact hq
      have hsum := hqj.add_right (keySmallGcd16 i j)
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, hsum.gcd_eq]
      simpa [keySmallGcd16, Nat.gcd_comm] using
        keyPairFactor16_coprime_multiplier_add_gcd j i (Ne.symm hij)
    exact hcopi.of_dvd_right hdiv


private lemma keyPrimePowerFamily16_pairwise (e : Fin 16 → ℕ) :
    ((Finset.univ : Finset (Fin 16)) : Set (Fin 16)).Pairwise
      (fun i j ↦ (keyPrime16 i ^ e i).Coprime
        (keyPrime16 j ^ e j)) := by
  intro i _hi j _hj hij
  exact Nat.coprime_pow_primes (e i) (e j) (keyPrime16_prime i)
    (keyPrime16_prime j) (keyPrime16_injective.ne hij)

private lemma sigma_zero_keyPrimeProduct16 (e : Fin 16 → ℕ) :
    σ 0 (∏ k : Fin 16, keyPrime16 k ^ e k) =
      ∏ k : Fin 16, (e k + 1) := by
  have h := ArithmeticFunction.IsMultiplicative.map_prod
    (f := σ 0) (fun k : Fin 16 ↦ keyPrime16 k ^ e k)
    ArithmeticFunction.isMultiplicative_sigma Finset.univ
    (keyPrimePowerFamily16_pairwise e)
  simpa [ArithmeticFunction.sigma_zero_apply_prime_pow, keyPrime16_prime]
    using h

private lemma sigma_zero_smallPart16 (i : Fin 16) :
    σ 0 (keySmallPart16 i) =
      ∏ k : Fin 16, (keyExponent16 i k + 1) := by
  unfold keySmallPart16
  exact sigma_zero_keyPrimeProduct16 (keyExponent16 i)

private lemma sigma_zero_smallPart16_div_gcd (i j : Fin 16) :
    σ 0 (keySmallPart16 i / keySmallGcd16 i j) =
      ∏ k : Fin 16, (keyQuotientExponent16 i j k + 1) := by
  rw [keySmallPart16_div_gcd_factorization]
  exact sigma_zero_keyPrimeProduct16 (keyQuotientExponent16 i j)

private lemma sigma_zero_smallPart16_div_gcd_swap (i j : Fin 16) :
    σ 0 (keySmallPart16 i / keySmallGcd16 j i) =
      ∏ k : Fin 16, (keyQuotientExponent16 i j k + 1) := by
  rw [show keySmallGcd16 j i = keySmallGcd16 i j by
    simp [keySmallGcd16, Nat.gcd_comm]]
  exact sigma_zero_smallPart16_div_gcd i j

private lemma sigma_zero_smallPart16_balance (i j : Fin 16) :
    σ 0 (keySmallPart16 i) *
        σ 0 (keySmallPart16 j / keySmallGcd16 i j) =
      σ 0 (keySmallPart16 j) *
        σ 0 (keySmallPart16 i / keySmallGcd16 i j) := by
  rw [sigma_zero_smallPart16 i, sigma_zero_smallPart16_div_gcd_swap j i,
    sigma_zero_smallPart16 j, sigma_zero_smallPart16_div_gcd i j]
  exact keyExponent16_balance i j

private lemma mul_mul_div_mul_eq_div_mul
    (a f u g : ℕ) (hga : g ∣ a) (hg : 0 < g) (hf : 0 < f) :
    a * f * u / (g * f) = a / g * u := by
  rcases hga with ⟨q, rfl⟩
  calc
    g * q * f * u / (g * f) = (g * f) * (q * u) / (g * f) := by
      congr 1
      ring
    _ = q * u := Nat.mul_div_right _ (Nat.mul_pos hg hf)
    _ = (g * q) / g * u := by rw [Nat.mul_div_right _ hg]

private lemma sigma_zero_balance_of_factorizations16
    (ps pt f u v xs yt a b d : ℕ)
    (ha : a = ps * f * u) (hb : b = pt * f * v)
    (hadiv : a / d = xs * u) (hbdiv : b / d = yt * v)
    (hpsf : ps.Coprime f) (hpsu : ps.Coprime u) (hfu : f.Coprime u)
    (hptf : pt.Coprime f) (hptv : pt.Coprime v) (hfv : f.Coprime v)
    (hxsu : xs.Coprime u) (hytv : yt.Coprime v)
    (hsmall : σ 0 ps * σ 0 yt = σ 0 pt * σ 0 xs) :
    σ 0 a * σ 0 (b / d) = σ 0 b * σ 0 (a / d) := by
  have hpsfu : (ps * f).Coprime u := hpsu.mul_left hfu
  have hptfv : (pt * f).Coprime v := hptv.mul_left hfv
  rw [hadiv, hbdiv, ha, hb]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpsfu,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpsf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hptfv,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hptf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hxsu,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hytv]
  calc
    σ 0 ps * σ 0 f * σ 0 u * (σ 0 yt * σ 0 v) =
        (σ 0 ps * σ 0 yt) * (σ 0 f * σ 0 u * σ 0 v) := by ring
    _ = (σ 0 pt * σ 0 xs) * (σ 0 f * σ 0 u * σ 0 v) := by rw [hsmall]
    _ = σ 0 pt * σ 0 f * σ 0 v * (σ 0 xs * σ 0 u) := by ring

/-- The divisor-ratio identity in Heath--Brown's key lemma. -/
theorem keyNumber16_sigma_balance (i j : Fin 16) (hij : i ≠ j) :
    σ 0 (keyNumber16 i) *
        σ 0 (keyNumber16 j / (keyNumber16 i).gcd (keyNumber16 j)) =
      σ 0 (keyNumber16 j) *
        σ 0 (keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j)) := by
  rw [keyNumber16_gcd_eq_distance hij, keyDistance16_factorization i j hij]
  let g := keySmallGcd16 i j
  let f := keyPairFactor16 i j
  let u := keyRemainder16 i j
  let v := keyRemainder16 j i
  apply sigma_zero_balance_of_factorizations16
      (keySmallPart16 i) (keySmallPart16 j) f u v
      (keySmallPart16 i / g) (keySmallPart16 j / g)
  · simpa [f, u] using keyNumber16_factorization hij
  · have hsymm : keyPairFactor16 j i = keyPairFactor16 i j := by
      exact keyPairFactor16_comm j i
    simpa [f, v, hsymm] using keyNumber16_factorization (Ne.symm hij)
  · rw [keyNumber16_factorization hij]
    simpa [g, f, u] using mul_mul_div_mul_eq_div_mul
      (keySmallPart16 i) (keyPairFactor16 i j) (keyRemainder16 i j)
      (keySmallGcd16 i j) (Nat.gcd_dvd_left _ _)
      (Nat.gcd_pos_of_pos_left _ (keySmallPart16_pos i))
      (keyPairFactor16_pos hij)
  · have hsymm : keyPairFactor16 j i = keyPairFactor16 i j := by
      exact keyPairFactor16_comm j i
    rw [keyNumber16_factorization (Ne.symm hij), hsymm]
    simpa [g, f, v] using mul_mul_div_mul_eq_div_mul
      (keySmallPart16 j) (keyPairFactor16 i j) (keyRemainder16 j i)
      (keySmallGcd16 i j) (Nat.gcd_dvd_right _ _)
      (Nat.gcd_pos_of_pos_left _ (keySmallPart16_pos i))
      (keyPairFactor16_pos hij)
  · exact (keyPairFactor16_coprime_smallPart i j).symm
  · exact keySmallPart16_coprime_remainder hij
  · exact keyPairFactor16_coprime_remainder hij
  · have hsymm : keyPairFactor16 j i = keyPairFactor16 i j := by
      exact keyPairFactor16_comm j i
    simpa [hsymm] using (keyPairFactor16_coprime_smallPart j i).symm
  · exact keySmallPart16_coprime_remainder (Ne.symm hij)
  · have hsymm : keyPairFactor16 j i = keyPairFactor16 i j := by
      exact keyPairFactor16_comm j i
    simpa [hsymm] using keyPairFactor16_coprime_remainder (Ne.symm hij)
  · exact (keySmallPart16_coprime_remainder hij).of_dvd_left
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  · exact (keySmallPart16_coprime_remainder (Ne.symm hij)).of_dvd_left
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
  · exact sigma_zero_smallPart16_balance i j



lemma keyAuxPrime16_coprime_keyNumber (i j : Fin 16) :
    (keyAuxPrime16 i).Coprime (keyNumber16 j) := by
  rw [(keyAuxPrime16_prime i).coprime_iff_not_dvd]
  intro hdiv
  have hmod := keyNumber16_modEq_aux j i
  have hz : keyNumber16 j ≡ 0 [MOD keyAuxPrime16 i] :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  have : keyAuxPrime16 i ∣ 1 + keyDelta16 j :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hz)
  exact keyAuxPrime16_not_dvd_delta i j this

end Erdos946.SixteenKey
