/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.TupleCertificateCounting

/-!
# Divisor switching for the large-component error

This file formalizes the elementary geometric step in BNPZ Proposition 6.2.
If the distinguished component `eᵢ` of a near-top divisor is large, replace
it by the complementary divisor `bᵢ` in the residual `(n-i)/gᵢ`.  If `D` is
the product of all other components, then `bᵢ < D` and the new CRT modulus is
`D*bᵢ`, rather than `D*eᵢ`.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverDivisorTuple

/-- Product of all tuple components except the distinguished coordinate. -/
def otherValue {D : CoverFactorization n k} (E : CoverDivisorTuple D)
    (i : Fin k) : ℕ :=
  ∏ j ∈ (Finset.univ.erase i), E.factor j

theorem factor_mul_otherValue {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (i : Fin k) :
    E.factor i * E.otherValue i = E.value := by
  exact Finset.mul_prod_erase Finset.univ E.factor (Finset.mem_univ i)

theorem otherValue_pos {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (hpos : ∀ j : Fin k, 0 < E.factor j)
    (i : Fin k) : 0 < E.otherValue i := by
  exact Finset.prod_pos fun j _ => hpos j

end CoverDivisorTuple

namespace CoverBPZ

/-- Complementary divisor in the residual factor at coordinate `i`. -/
noncomputable def switchedComplement {B K n : ℕ} (S : BPZSection6Input B K)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (i : Fin S.k) : ℕ :=
  ((n - i.val) / (S.toCoverFactorization hn hprog).g i.val) / E.factor i

/-- Exact factorization of the distinguished residual after switching. -/
theorem factor_mul_switchedComplement {B K n : ℕ}
    (S : BPZSection6Input B K) (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (i : Fin S.k) :
    E.factor i * switchedComplement S hn hprog E i =
      (n - i.val) / (S.toCoverFactorization hn hprog).g i.val := by
  exact Nat.mul_div_cancel' (E.divides i)

/-- The exact divisor-switching inequalities.  They are stated without
rounding or real powers: `(large+1)D ≤ X` is the discrete form of
`D ≤ X/large`, and `b < D` is the key saving in the switched modulus. -/
theorem largeError_switching_data
    {B K X z large n : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hnError : n ∈ RefinedLargeErrors S X z large) :
    ∃ (hn : S.k < n)
      (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
      (i : Fin S.k)
      (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
      (b D : ℕ),
      D = E.otherValue i ∧
      E.factor i * D = E.value ∧
      E.factor i * b =
        (n - i.val) /
          (S.toCoverFactorization hn hprog).g i.val ∧
      n < B * E.value ∧ E.value ≤ n ∧
      0 < b ∧ b < D ∧ (large + 1) * D ≤ X := by
  classical
  have hnData := hnError
  rw [RefinedLargeErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨⟨hnIoc, hn, hnRefined⟩, hrough⟩, hnLarge⟩ := hnData
  have hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α :=
    refinement_progression_implies_public S hnRefined
  obtain ⟨hn', hprog', d, E, hnd, hdn, hvalue, i, hiLarge⟩ := hnLarge
  let D := E.otherValue i
  let b := switchedComplement S hn' hprog' E i
  have hePos : 0 < E.factor i := lt_of_le_of_lt (Nat.zero_le large) hiLarge
  have hresPos : 0 <
      (n - i.val) / (S.toCoverFactorization hn' hprog').g i.val := by
    have htermPos : 0 < n - i.val := Nat.sub_pos_of_lt (i.isLt.trans hn')
    have hgPos : 0 < (S.toCoverFactorization hn' hprog').g i.val :=
      hB.trans_le (S.coverQuotient_ge_B hn' hprog' i.isLt)
    have hgLe : (S.toCoverFactorization hn' hprog').g i.val ≤ n - i.val :=
      Nat.le_of_dvd htermPos
        ((S.toCoverFactorization hn' hprog').divides_term i.val i.isLt)
    exact Nat.div_pos hgLe hgPos
  have hbPos : 0 < b := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hresPos (E.divides i)
    · exact hePos
  have hED : E.factor i * D = E.value := E.factor_mul_otherValue i
  have hEDleX : E.factor i * D ≤ X := by
    rw [hED, hvalue]
    exact hdn.trans (Finset.mem_Ioc.mp hnIoc).2
  have hlargeD : (large + 1) * D ≤ X := by
    exact (Nat.mul_le_mul_right D (Nat.add_one_le_iff.mpr hiLarge)).trans hEDleX
  have heb : E.factor i * b =
      (n - i.val) / (S.toCoverFactorization hn' hprog').g i.val :=
    factor_mul_switchedComplement S hn' hprog' E i
  have hresLe :
      (n - i.val) / (S.toCoverFactorization hn' hprog').g i.val ≤ n / B :=
    S.coverQuotient_le_div hB hn' hprog' i.isLt
  have hBebLe : B * (E.factor i * b) ≤ n := by
    calc
      B * (E.factor i * b) = B *
          ((n - i.val) / (S.toCoverFactorization hn' hprog').g i.val) := by
            rw [heb]
      _ ≤ B * (n / B) := Nat.mul_le_mul_left B hresLe
      _ ≤ n := Nat.mul_div_le n B
  have hnLtBED : n < B * (E.factor i * D) := by
    rw [hED, hvalue]
    exact hnd
  have hbDmul : (B * E.factor i) * b < (B * E.factor i) * D := by
    calc
      (B * E.factor i) * b = B * (E.factor i * b) := by ac_rfl
      _ ≤ n := hBebLe
      _ < B * (E.factor i * D) := hnLtBED
      _ = (B * E.factor i) * D := by ac_rfl
  have hbD : b < D := by
    exact (Nat.mul_lt_mul_left (Nat.mul_pos hB hePos)).mp hbDmul
  refine ⟨hn', hprog', i, E, b, D, rfl, hED, heb,
    ?_, ?_, hbPos, hbD, hlargeD⟩
  · rw [hvalue]
    exact hnd
  · rw [hvalue]
    exact hdn

/-- In a sufficiently long dyadic interval the switched complementary
factor lies in a fixed-width multiplicative interval depending on `D`.
This is the fixed-`B` version of the localization in BNPZ Section 7.2; it
avoids introducing a second dyadic partition because `B` is frozen. -/
theorem largeError_switching_interval_data
    {B K X z large n : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hXwide : 6 * S.k ≤ X)
    (hnError : n ∈ RefinedLargeErrors S X z large) :
    ∃ (hn : S.k < n)
      (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
      (i : Fin S.k)
      (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
      (b D : ℕ),
      D = E.otherValue i ∧
      E.factor i * D = E.value ∧
      E.factor i * b =
        (n - i.val) /
          (S.toCoverFactorization hn hprog).g i.val ∧
      n < B * E.value ∧ E.value ≤ n ∧
      0 < b ∧ b < D ∧ (large + 1) * D ≤ X ∧
      D < 3 * S.g i * b ∧ b * S.g i < 2 * B * D := by
  classical
  obtain ⟨hn, hprog, i, E, b, D, hD, hED, heb,
      hnear, hvalueN, hbPos, hbD, hlargeD⟩ :=
    largeError_switching_data S hB hnError
  have hnData := hnError
  rw [RefinedLargeErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨⟨hnIoc, _hn, _hnRefined⟩, _hrough⟩, _hnLarge⟩ := hnData
  have hnX : n ≤ X := (Finset.mem_Ioc.mp hnIoc).2
  have hXpos : 0 < X := by have := S.hk3; omega
  have hgEq :
      (S.toCoverFactorization hn hprog).g i.val = S.g i := by
    exact S.gNat_eq i.isLt
  have hgPos : 0 < S.g i := S.g_pos i
  have hresEq : S.g i * (E.factor i * b) = n - i.val := by
    rw [← hgEq, heb]
    exact Nat.mul_div_cancel'
      ((S.toCoverFactorization hn hprog).divides_term i.val i.isLt)
  have hXlower : X < 3 * (n - i.val) := by
    have hnHalf := (Finset.mem_Ioc.mp hnIoc).1
    have hi := i.isLt
    omega
  have hDPos : 0 < D := hbPos.trans hbD
  have hlowerScaled : X * D < (3 * S.g i * b) * X := by
    calc
      X * D < (3 * (n - i.val)) * D :=
        (Nat.mul_lt_mul_right hDPos).2 hXlower
      _ = (3 * S.g i * b) * E.value := by
        rw [← hED, ← hresEq]
        ac_rfl
      _ ≤ (3 * S.g i * b) * n :=
        Nat.mul_le_mul_left _ hvalueN
      _ ≤ (3 * S.g i * b) * X :=
        Nat.mul_le_mul_left _ hnX
  have hlower : D < 3 * S.g i * b := by
    apply (Nat.mul_lt_mul_left hXpos).mp
    simpa [Nat.mul_comm] using hlowerScaled
  have hXtwoN : X < 2 * n := by
    have hnHalf := (Finset.mem_Ioc.mp hnIoc).1
    omega
  have hbgPos : 0 < b * S.g i := Nat.mul_pos hbPos hgPos
  have hupperScaled : X * (b * S.g i) < X * (2 * B * D) := by
    calc
      X * (b * S.g i) < (2 * n) * (b * S.g i) :=
        (Nat.mul_lt_mul_right hbgPos).2 hXtwoN
      _ < (2 * (B * E.value)) * (b * S.g i) := by
        exact (Nat.mul_lt_mul_right hbgPos).2
          ((Nat.mul_lt_mul_left (show 0 < 2 by omega)).2 hnear)
      _ = (2 * B * D) * (n - i.val) := by
        rw [← hED, ← hresEq]
        ac_rfl
      _ ≤ (2 * B * D) * X :=
        Nat.mul_le_mul_left _ ((Nat.sub_le n i.val).trans hnX)
      _ = X * (2 * B * D) := Nat.mul_comm _ _
  have hupper : b * S.g i < 2 * B * D :=
    (Nat.mul_lt_mul_left hXpos).mp hupperScaled
  exact ⟨hn, hprog, i, E, b, D, hD, hED, heb,
    hnear, hvalueN, hbPos, hbD, hlargeD, hlower, hupper⟩

end CoverBPZ

namespace TupleCertificate

/-- Product of every certificate coordinate except `i`. -/
def otherValue (C : TupleCertificate k X) (i : Fin k) : ℕ :=
  ∏ j ∈ (Finset.univ.erase i), C.factor j

theorem factor_mul_otherValue (C : TupleCertificate k X) (i : Fin k) :
    C.factor i * C.otherValue i = C.value := by
  exact Finset.mul_prod_erase Finset.univ C.factor (Finset.mem_univ i)

end TupleCertificate

namespace CoverBPZ

/-- Finite switched certificates used after replacing a large component by
its complementary divisor. -/
noncomputable def SwitchedLargeTupleCertificates {B K : ℕ}
    (S : BPZSection6Input B K) (X z large : ℕ) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact Finset.univ.filter fun C =>
    (∃ i : Fin S.k,
        C.val.factor i < C.val.otherValue i ∧
        (large + 1) * C.val.otherValue i ≤ X ∧
        C.val.otherValue i < 3 * S.g i * C.val.factor i ∧
        C.val.factor i * S.g i < 2 * B * C.val.otherValue i) ∧
      ∀ j : Fin S.k, IsZRough z (C.val.factor j)

theorem mem_switchedLargeTupleCertificates_iff {B K X z large : ℕ}
    {S : BPZSection6Input B K} {C : RefinedTupleCertificate S X} :
    C ∈ SwitchedLargeTupleCertificates S X z large ↔
      (∃ i : Fin S.k,
          C.val.factor i < C.val.otherValue i ∧
          (large + 1) * C.val.otherValue i ≤ X ∧
          C.val.otherValue i < 3 * S.g i * C.val.factor i ∧
          C.val.factor i * S.g i < 2 * B * C.val.otherValue i) ∧
        ∀ j : Fin S.k, IsZRough z (C.val.factor j) := by
  classical
  rw [SwitchedLargeTupleCertificates, Finset.mem_filter]
  simp

theorem switchedCertificate_factor_le_div {B K X z large : ℕ}
    {S : BPZSection6Input B K} {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (j : Fin S.k) : C.val.factor j ≤ X / (large + 1) := by
  obtain ⟨⟨i, hiLt, hiScale, _hiLower, _hiUpper⟩, _hRough⟩ :=
    mem_switchedLargeTupleCertificates_iff.mp hC
  have hOtherPos : 0 < C.val.otherValue i := by
    exact Finset.prod_pos fun a _ => C.val.positive a
  have hfactorOther : C.val.factor j ≤ C.val.otherValue i := by
    by_cases hji : j = i
    · subst j
      exact hiLt.le
    · apply Nat.le_of_dvd hOtherPos
      unfold TupleCertificate.otherValue
      exact Finset.dvd_prod_of_mem C.val.factor
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact hfactorOther.trans
    ((Nat.le_div_iff_mul_le (Nat.succ_pos large)).2
      (by simpa [Nat.mul_comm] using hiScale))

theorem switchedCertificate_factor_rough {B K X z large : ℕ}
    {S : BPZSection6Input B K} {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (j : Fin S.k) : IsZRough z (C.val.factor j) :=
  (mem_switchedLargeTupleCertificates_iff.mp hC).2 j

/-- Product-sensitive bound for a switched modulus: its value is at most the
square of the complementary product cutoff. -/
theorem switchedCertificate_value_le_square_div
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large) :
    C.val.value ≤ (X / (large + 1)) ^ 2 := by
  obtain ⟨⟨i, hiLt, hiScale, _hiLower, _hiUpper⟩, _hRough⟩ :=
    mem_switchedLargeTupleCertificates_iff.mp hC
  have hDle : C.val.otherValue i ≤ X / (large + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos large)).2
    simpa [Nat.mul_comm] using hiScale
  rw [← C.val.factor_mul_otherValue i]
  calc
    C.val.factor i * C.val.otherValue i ≤
        C.val.otherValue i * C.val.otherValue i :=
      Nat.mul_le_mul_right _ hiLt.le
    _ ≤ (X / (large + 1)) * (X / (large + 1)) :=
      Nat.mul_le_mul hDle hDle
    _ = (X / (large + 1)) ^ 2 := by simp [pow_two]

/-- Crude but power-saving endpoint count: every coordinate of a switched
certificate is at most `X/(large+1)`. -/
theorem card_switchedLargeTupleCertificates_le {B K X large : ℕ}
    (S : BPZSection6Input B K) (z : ℕ) :
    (SwitchedLargeTupleCertificates S X z large).card ≤
      (X / (large + 1) + 1) ^ S.k := by
  classical
  let T := SwitchedLargeTupleCertificates S X z large
  let A := {C : RefinedTupleCertificate S X // C ∈ T}
  have hfactorBound (C : A) (j : Fin S.k) :
      C.val.val.factor j ≤ X / (large + 1) := by
    exact switchedCertificate_factor_le_div C.property j
  let encode : A → (Fin S.k → Fin (X / (large + 1) + 1)) :=
    fun C j => ⟨C.val.val.factor j, by
      have := hfactorBound C j
      omega⟩
  have hencode : Function.Injective encode := by
    intro C₁ C₂ h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext j
    apply Fin.ext
    have hj := congrArg Fin.val (congrFun h j)
    simpa [encode, TupleCertificate.factor] using hj
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [A, T, Fintype.card_coe, Fintype.card_fun,
    Fintype.card_fin] using hcard

/-- The divisor switch puts every large error into an explicit CRT class
whose modulus uses the short complementary divisor.  The scale hypothesis is
the exact integer condition ensuring that the switched product is below the
left endpoint of the dyadic interval. -/
theorem refinedLargeErrors_subset_switchedCertificateClasses
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2) :
    RefinedLargeErrors S X z large ⊆
      (SwitchedLargeTupleCertificates S X z large).biUnion
        (fun C => C.classIoc (X / 2) X) := by
  classical
  intro n hnError
  have hnData := hnError
  rw [RefinedLargeErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨⟨hnIoc, hn, hnRefined⟩, hrough⟩, _hnLarge⟩ := hnData
  obtain ⟨hn', hprog', i, E, b, D, hD, hED, heb,
      _hnear, _hvalueN, hbPos, hbD, hlargeD, hbLower, hbUpper⟩ :=
    largeError_switching_interval_data S hB hXwide hnError
  have hpos : ∀ j : Fin S.k, 0 < E.factor j := by
    intro j
    have hfactorDvd : E.factor j ∣ n.choose S.k :=
      (E.divides j).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn' hprog') j.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd (Nat.choose_pos hn'.le)
  have hfactorLe : ∀ j : Fin S.k, E.factor j ≤ X := by
    intro j
    have hfactorTerm : E.factor j ∣ n - j.val :=
      (E.divides j).trans
        (coverQuotient_dvd_term (S.toCoverFactorization hn' hprog') j.isLt)
    have htermPos : 0 < n - j.val := Nat.sub_pos_of_lt (j.isLt.trans hn')
    exact (Nat.le_of_dvd htermPos hfactorTerm).trans
      ((Nat.sub_le n j.val).trans (Finset.mem_Ioc.mp hnIoc).2)
  have hDleX : D ≤ X := by
    calc
      D ≤ (large + 1) * D := by
        simpa [Nat.one_mul] using
          Nat.mul_le_mul_right D (Nat.succ_le_succ (Nat.zero_le large))
      _ ≤ X := hlargeD
  have hbLeX : b ≤ X := hbD.le.trans hDleX
  have hbDivResidual : b ∣
      (n - i.val) / (S.toCoverFactorization hn' hprog').g i.val := by
    exact ⟨E.factor i, by simpa [Nat.mul_comm] using heb.symm⟩
  let f : Fin S.k → Fin (X + 1) := fun j =>
    if hji : j = i then ⟨b, by omega⟩
    else ⟨E.factor j, by have := hfactorLe j; omega⟩
  have hfPos : ∀ j : Fin S.k, 0 < (f j).val := by
    intro j
    by_cases hji : j = i
    · simp [f, hji, hbPos]
    · simp [f, hji, hpos j]
  have hfPairwise : ∀ a c : Fin S.k, a ≠ c →
      Nat.Coprime (f a).val (f c).val := by
    intro a c hac
    by_cases hai : a = i
    · subst a
      have hci : c ≠ i := fun h => hac h.symm
      simp only [f, ↓reduceDIte, hci, Fin.val_mk]
      exact Nat.Coprime.of_dvd_right (E.divides c)
        (Nat.Coprime.of_dvd_left hbDivResidual
          (S.coverQuotients_pairwise_coprime hn' hprog'
            i i.isLt c c.isLt (fun h => hci (Fin.ext h).symm)))
    · by_cases hci : c = i
      · subst c
        simp only [f, hai, ↓reduceDIte, Fin.val_mk]
        exact (Nat.Coprime.of_dvd_right (E.divides a)
          (Nat.Coprime.of_dvd_left hbDivResidual
            (S.coverQuotients_pairwise_coprime hn' hprog'
              i i.isLt a a.isLt (fun h => hai (Fin.ext h).symm)))).symm
      · simp only [f, hai, hci]
        exact Nat.Coprime.of_dvd_right (E.divides c)
          (Nat.Coprime.of_dvd_left (E.divides a)
            (S.coverQuotients_pairwise_coprime hn' hprog'
              a a.isLt c c.isLt (fun h => hac (Fin.ext h))))
  let C₀ : TupleCertificate S.k X := ⟨f, hfPos, hfPairwise⟩
  have hCfactor : C₀.factor i = b := by simp [C₀, f, TupleCertificate.factor]
  have hCother : C₀.otherValue i = D := by
    rw [hD]
    unfold TupleCertificate.otherValue CoverDivisorTuple.otherValue
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [C₀, f, TupleCertificate.factor, hji]
  have hCvalue : C₀.value = b * D := by
    rw [← C₀.factor_mul_otherValue i, hCfactor, hCother]
  have hdivFactor : ∀ j : Fin S.k, C₀.factor j ∣
      (n - j.val) / (S.toCoverFactorization hn' hprog').g j.val := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [hCfactor] using hbDivResidual
    · change (f j).val ∣
        (n - j.val) / (S.toCoverFactorization hn' hprog').g j.val
      simpa [f, hji] using E.divides j
  have hCchoose : C₀.value ∣ n.choose S.k := by
    change (∏ j : Fin S.k, C₀.factor j) ∣ n.choose S.k
    rw [choose_eq_prod_coverQuotients (S.toCoverFactorization hn' hprog'),
      ← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_dvd_prod_of_dvd C₀.factor
      (fun j : Fin S.k =>
        (n - j.val) / (S.toCoverFactorization hn' hprog').g j.val)
      (by intro j _; exact hdivFactor j)
  have hcop : Nat.Coprime (refinementModulus S) C₀.value :=
    coprime_refinementModulus_of_dvd_choose_of_rough
      S hz hrough hCchoose
  let C : RefinedTupleCertificate S X := ⟨C₀, hcop⟩
  have hDleDiv : D ≤ X / (large + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos large)).2
    simpa [Nat.mul_comm] using hlargeD
  have hCvalueLtHalf : C₀.value < X / 2 := by
    rw [hCvalue]
    calc
      b * D < D * D := (Nat.mul_lt_mul_right (hbPos.trans hbD)).2 hbD
      _ ≤ (X / (large + 1)) * (X / (large + 1)) :=
        Nat.mul_le_mul hDleDiv hDleDiv
      _ = (X / (large + 1)) ^ 2 := by simp [pow_two]
      _ ≤ X / 2 := hscale
  have hCvalueLeN : C₀.value ≤ n :=
    hCvalueLtHalf.le.trans (Finset.mem_Ioc.mp hnIoc).1.le
  rw [Finset.mem_biUnion]
  refine ⟨C, ?_, ?_⟩
  · rw [SwitchedLargeTupleCertificates, Finset.mem_filter]
    refine ⟨Finset.mem_univ C, ⟨i, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [C, hCfactor, hCother] using hbD
    · simpa [C, hCother] using hlargeD
    · simpa [C, hCfactor, hCother] using hbLower
    · simpa [C, hCfactor, hCother] using hbUpper
    · intro j p hp hpz hpd
      exact hrough p hp hpz
        (hpd.trans ((hdivFactor j).trans
          (coverQuotient_dvd_choose
            (S.toCoverFactorization hn' hprog') j.isLt)))
  · apply (RefinedTupleCertificate.mem_classIoc_iff C).mpr
    refine ⟨hnIoc,
      (refinement_progression_dvd_iff_modEq S).mp hnRefined, ?_⟩
    apply C₀.ambient_modEq_crtResidue hn'.le hCvalueLeN
    intro j
    exact (hdivFactor j).trans
      (coverQuotient_dvd_term (S.toCoverFactorization hn' hprog') j.isLt)

/-- Reciprocal-modulus union bound after divisor switching. -/
theorem refinedLargeErrors_card_le_switchedCertificateSum
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        (((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * C.val.value : ℕ) + 2) := by
  let T := SwitchedLargeTupleCertificates S X z large
  have hsubset : RefinedLargeErrors S X z large ⊆
      T.biUnion (fun C => C.classIoc (X / 2) X) := by
    simpa [T] using
      (refinedLargeErrors_subset_switchedCertificateClasses
        (X := X) (large := large) S hB hz hXwide hscale)
  have hcardNat := Finset.card_le_card hsubset
  have hunionNat :
      (T.biUnion fun C => C.classIoc (X / 2) X).card ≤
        ∑ C ∈ T, (C.classIoc (X / 2) X).card :=
    Finset.card_biUnion_le
  have hleft : ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ∑ C ∈ T, ((C.classIoc (X / 2) X).card : ℝ) := by
    exact_mod_cast hcardNat.trans hunionNat
  refine hleft.trans (Finset.sum_le_sum fun C hC => ?_)
  exact C.card_classIoc_le (Nat.div_le_self X 2)

/-- The same bound with the interval-counting endpoint error separated from
the reciprocal switched-modulus main sum. -/
theorem refinedLargeErrors_card_le_switchedMain_add_endpoint
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
          (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
            (1 : ℝ) / C.val.value) +
        2 * ((X / (large + 1) + 1) ^ S.k : ℕ) := by
  let T := SwitchedLargeTupleCertificates S X z large
  change ((RefinedLargeErrors S X z large).card : ℝ) ≤
    (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
        (∑ C ∈ T, (1 : ℝ) / C.val.value) +
      2 * ((X / (large + 1) + 1) ^ S.k : ℕ)
  have hbase := refinedLargeErrors_card_le_switchedCertificateSum
    (X := X) (large := large) S hB hz hXwide hscale
  have hrewrite :
      (∑ C ∈ T,
          (((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * C.val.value : ℕ) + 2)) =
        (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
            (∑ C ∈ T, (1 : ℝ) / C.val.value) +
          2 * (T.card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro C hC
      have hm : (refinementModulus S : ℝ) ≠ 0 := by
        exact_mod_cast (refinementModulus_pos S).ne'
      have hd : (C.val.value : ℝ) ≠ 0 := by
        exact_mod_cast C.val.value_pos.ne'
      push_cast
      field_simp
    · simp [mul_comm]
  rw [show SwitchedLargeTupleCertificates S X z large = T from rfl] at hbase
  rw [hrewrite] at hbase
  have hcardNat := card_switchedLargeTupleCertificates_le
    (X := X) (large := large) S z
  have hcardReal : (T.card : ℝ) ≤
      ((X / (large + 1) + 1) ^ S.k : ℕ) := by
    exact_mod_cast hcardNat
  have hendpoint : 2 * (T.card : ℝ) ≤
      2 * ((X / (large + 1) + 1) ^ S.k : ℕ) := by
    nlinarith
  exact hbase.trans (add_le_add_right hendpoint _)

end CoverBPZ

end Erdos387
