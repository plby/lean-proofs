/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedDivisorCongruence

/-!
# Finite tuple certificates for divisor-error counting

The analytic union bounds must be indexed independently of the candidate
`n`.  A `TupleCertificate k X` is a positive pairwise-coprime `k`-tuple of
integers at most `X`, together with its product and canonical CRT residue.
-/

namespace Erdos387

open scoped BigOperators

/-- Finite positive pairwise-coprime factor vectors bounded by `X`. -/
def TupleCertificate (k X : ℕ) :=
  {f : Fin k → Fin (X + 1) //
    (∀ i, 0 < (f i).val) ∧
      ∀ i j, i ≠ j → Nat.Coprime (f i).val (f j).val}

noncomputable instance tupleCertificateFintype (k X : ℕ) :
    Fintype (TupleCertificate k X) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

namespace TupleCertificate

def factor (C : TupleCertificate k X) (i : Fin k) : ℕ :=
  (C.val i).val

theorem positive (C : TupleCertificate k X) (i : Fin k) :
    0 < C.factor i := C.property.1 i

theorem pairwise (C : TupleCertificate k X) (i j : Fin k) (hij : i ≠ j) :
    Nat.Coprime (C.factor i) (C.factor j) :=
  C.property.2 i j hij

theorem factor_le (C : TupleCertificate k X) (i : Fin k) :
    C.factor i ≤ X := by
  change (C.val i).val ≤ X
  have hi := (C.val i).isLt
  omega

def value (C : TupleCertificate k X) : ℕ :=
  ∏ i, C.factor i

theorem value_pos (C : TupleCertificate k X) : 0 < C.value := by
  exact Finset.prod_pos fun i _ => C.positive i

noncomputable def crtResidue (C : TupleCertificate k X) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun i : Fin k => i.val) C.factor Finset.univ
    (by intro i _; exact (C.positive i).ne')
    (by intro i _ j _ hij; exact C.pairwise i j hij)

theorem crtResidue_mod_factor (C : TupleCertificate k X) (i : Fin k) :
    C.crtResidue ≡ i.val [MOD C.factor i] := by
  exact (Nat.chineseRemainderOfFinset
    (fun i : Fin k => i.val) C.factor Finset.univ
    (by intro j _; exact (C.positive j).ne')
    (by intro a _ b _ hab; exact C.pairwise a b hab)).prop
      i (Finset.mem_univ i)

theorem crtResidue_lt_value (C : TupleCertificate k X) :
    C.crtResidue < C.value := by
  unfold crtResidue value
  exact Nat.chineseRemainderOfFinset_lt_prod
    (a := fun i : Fin k => i.val) (s := C.factor) (t := Finset.univ)
    (by intro i _; exact (C.positive i).ne')
    (by intro i _ j _ hij; exact C.pairwise i j hij)

/-- If every tuple factor divides its corresponding shift, the ambient
integer lies in the tuple's CRT class modulo their product. -/
theorem ambient_modEq_crtResidue (C : TupleCertificate k X)
    {n : ℕ} (hkn : k ≤ n) (hvalue : C.value ≤ n)
    (hdiv : ∀ i : Fin k, C.factor i ∣ n - i.val) :
    n ≡ C.crtResidue [MOD C.value] := by
  have hresLe : C.crtResidue ≤ n :=
    C.crtResidue_lt_value.le.trans hvalue
  have hfactorDvd : ∀ i : Fin k, C.factor i ∣ n - C.crtResidue := by
    intro i
    have hiLe : i.val ≤ n := (Nat.le_of_lt i.isLt).trans hkn
    have hiModN : i.val ≡ n [MOD C.factor i] :=
      (Nat.modEq_iff_dvd' hiLe).mpr (hdiv i)
    have hresModN : C.crtResidue ≡ n [MOD C.factor i] :=
      (C.crtResidue_mod_factor i).trans hiModN
    exact (Nat.modEq_iff_dvd' hresLe).mp hresModN
  have hprodDvd : C.value ∣ n - C.crtResidue := by
    change (∏ i : Fin k, C.factor i) ∣ n - C.crtResidue
    exact CoprimeCoverDivisorTuple.finset_prod_dvd_of_pairwise_coprime_nat
      Finset.univ C.factor (n - C.crtResidue)
      (by intro i _ j _ hij; exact C.pairwise i j hij)
      (by intro i _; exact hfactorDvd i)
  exact ((Nat.modEq_iff_dvd' hresLe).mpr hprodDvd).symm

end TupleCertificate

/-- Tuple certificates whose value is coprime to the refined progression
modulus. -/
def RefinedTupleCertificate {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X : ℕ) :=
  {C : TupleCertificate S.k X //
    Nat.Coprime (CoverBPZ.refinementModulus S) C.value}

noncomputable instance refinedTupleCertificateFintype {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X : ℕ) :
    Fintype (RefinedTupleCertificate S X) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

namespace RefinedTupleCertificate

noncomputable def classIoc {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (L U : ℕ) : Finset ℕ :=
  simultaneousClassIoc L U (CoverBPZ.refinementModulus S) C.val.value
    (CoverBPZ.refinementResidue S) C.val.crtResidue C.property

theorem mem_classIoc_iff {B K X L U n : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) :
    n ∈ C.classIoc L U ↔
      n ∈ Finset.Ioc L U ∧
      n ≡ CoverBPZ.refinementResidue S
        [MOD CoverBPZ.refinementModulus S] ∧
      n ≡ C.val.crtResidue [MOD C.val.value] := by
  exact mem_simultaneousClassIoc_iff C.property
    (CoverBPZ.refinementModulus_pos S) C.val.value_pos

theorem card_classIoc_le {B K X L U : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hLU : L ≤ U) :
    ((C.classIoc L U).card : ℝ) ≤
      ((U - L : ℕ) : ℝ) /
        (CoverBPZ.refinementModulus S * C.val.value : ℕ) + 2 := by
  exact card_refinedSimultaneousClassIoc_le S hLU
    C.val.value_pos C.property

end RefinedTupleCertificate

namespace CoverBPZ

/-- The finite independent parameter space for large-component errors. -/
noncomputable def RefinedLargeTupleCertificates {B K : ℕ}
    (S : BPZSection6Input B K) (X large : ℕ) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact Finset.univ.filter fun C =>
    C.val.value ≤ X ∧ ∃ i : Fin S.k, large < C.val.factor i

/-- Every refined large-component error lies in the congruence class of one
certificate in the finite independent parameter space. -/
theorem refinedLargeErrors_subset_certificateClasses
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hz : 2 * S.k ≤ z) :
    RefinedLargeErrors S X z large ⊆
      (RefinedLargeTupleCertificates S X large).biUnion
        (fun C => C.classIoc (X / 2) X) := by
  classical
  intro n hnError
  rw [RefinedLargeErrors, Finset.mem_filter] at hnError
  obtain ⟨hnS, hnLarge⟩ := hnError
  have hnData := hnS
  rw [RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨hnIoc, hn, hnRefined⟩, hrough⟩ := hnData
  obtain ⟨hn', hprog', d, E₀, hnd, hdn, hvalue, hlarge⟩ := hnLarge
  have hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α :=
    refinement_progression_implies_public S hnRefined
  have hpos : ∀ i : Fin S.k, 0 < E₀.factor i := by
    intro i
    have hfactorDvd : E₀.factor i ∣ n.choose S.k :=
      (E₀.divides i).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn' hprog') i.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd (Nat.choose_pos hn.le)
  have hfactorLe : ∀ i : Fin S.k, E₀.factor i ≤ X := by
    intro i
    have hfactorTerm : E₀.factor i ∣ n - i.val :=
      (E₀.divides i).trans
        (coverQuotient_dvd_term (S.toCoverFactorization hn' hprog') i.isLt)
    have htermPos : 0 < n - i.val :=
      Nat.sub_pos_of_lt (i.isLt.trans hn)
    exact (Nat.le_of_dvd htermPos hfactorTerm).trans
      ((Nat.sub_le n i.val).trans (Finset.mem_Ioc.mp hnIoc).2)
  have hpair : ∀ i j : Fin S.k, i ≠ j →
      Nat.Coprime (E₀.factor i) (E₀.factor j) := by
    intro i j hij
    exact Nat.Coprime.of_dvd_right (E₀.divides j)
      (Nat.Coprime.of_dvd_left (E₀.divides i)
        (S.coverQuotients_pairwise_coprime hn' hprog'
          i i.isLt j j.isLt (fun h => hij (Fin.ext h))))
  let f : Fin S.k → Fin (X + 1) := fun i =>
    ⟨E₀.factor i, by have := hfactorLe i; omega⟩
  let C₀ : TupleCertificate S.k X :=
    ⟨f, (by intro i; exact hpos i), (by intro i j hij; exact hpair i j hij)⟩
  have hCvalue : C₀.value = d := by
    change E₀.value = d
    exact hvalue
  have hdChoose : d ∣ n.choose S.k := by
    rw [← hCvalue]
    change (∏ i : Fin S.k, E₀.factor i) ∣ n.choose S.k
    rw [choose_eq_prod_coverQuotients (S.toCoverFactorization hn' hprog'),
      ← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_dvd_prod_of_dvd E₀.factor
      (fun i : Fin S.k =>
        (n - i.val) / (S.toCoverFactorization hn' hprog').g i.val)
      (by intro i _; exact E₀.divides i)
  have hcop : Nat.Coprime (refinementModulus S) C₀.value := by
    rw [hCvalue]
    exact coprime_refinementModulus_of_dvd_choose_of_rough
      S hz hrough hdChoose
  let C : RefinedTupleCertificate S X := ⟨C₀, hcop⟩
  rw [Finset.mem_biUnion]
  refine ⟨C, ?_, ?_⟩
  · rw [RefinedLargeTupleCertificates, Finset.mem_filter]
    refine ⟨Finset.mem_univ C, ?_, ?_⟩
    · rw [hCvalue]
      exact hdn.trans (Finset.mem_Ioc.mp hnIoc).2
    · obtain ⟨i, hi⟩ := hlarge
      exact ⟨i, hi⟩
  · apply (RefinedTupleCertificate.mem_classIoc_iff C).mpr
    refine ⟨hnIoc,
      (refinement_progression_dvd_iff_modEq S).mp hnRefined, ?_⟩
    apply C₀.ambient_modEq_crtResidue hn.le
    · rw [hCvalue]
      exact hdn
    · intro i
      change E₀.factor i ∣ n - i.val
      exact (E₀.divides i).trans
        (coverQuotient_dvd_term (S.toCoverFactorization hn' hprog') i.isLt)

/-- Exact reciprocal-modulus union bound reducing Proposition 6.2 to the
arithmetic sum over independent large tuple certificates. -/
theorem refinedLargeErrors_card_le_certificateSum
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hz : 2 * S.k ≤ z) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ∑ C ∈ RefinedLargeTupleCertificates S X large,
        (((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * C.val.value : ℕ) + 2) := by
  let T := RefinedLargeTupleCertificates S X large
  have hsubset : RefinedLargeErrors S X z large ⊆
      T.biUnion (fun C => C.classIoc (X / 2) X) := by
    simpa [T] using
      (refinedLargeErrors_subset_certificateClasses
        (X := X) (large := large) S hz)
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

end CoverBPZ

end Erdos387
