/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.MvPolynomial
import ErdosProblems.Erdos407.GeneralizedWronskian

namespace Erdos407.PolynomialHeights

open scoped BigOperators

noncomputable section

/-! ## Projective coefficient height -/

/-- The logarithmic projective height of the coefficient vector of a
multivariate polynomial.  The `Finsupp` height is by definition the height
of the finite tuple indexed by the support, so this also totalizes the zero
polynomial to height zero. -/
def projectiveCoeffHeight {ι : Type*} (P : MvPolynomial ι ℚ) : ℝ :=
  Height.logHeight (fun J : P.support ↦ MvPolynomial.coeff J P)

@[simp] theorem projectiveCoeffHeight_zero {ι : Type*} :
    projectiveCoeffHeight (0 : MvPolynomial ι ℚ) = 0 := by
  simp [projectiveCoeffHeight]

theorem projectiveCoeffHeight_nonneg {ι : Type*}
    (P : MvPolynomial ι ℚ) : 0 ≤ projectiveCoeffHeight P := by
  classical
  exact Height.logHeight_nonneg _

/-- The coefficient tuple indexed by the (finite) support. -/
abbrev coeffTuple {ι : Type*} (P : MvPolynomial ι ℚ) :
    P.support → ℚ := fun J ↦ MvPolynomial.coeff J P

theorem coeffTuple_ne_zero {ι : Type*} {P : MvPolynomial ι ℚ}
    (hP : P ≠ 0) : coeffTuple P ≠ 0 := by
  obtain ⟨J, hJ⟩ := MvPolynomial.support_nonempty.mpr hP
  exact Function.ne_iff.mpr ⟨⟨J, hJ⟩, MvPolynomial.mem_support_iff.mp hJ⟩

theorem projectiveCoeffHeight_eq_logHeight_coeffTuple {ι : Type*}
    (P : MvPolynomial ι ℚ) :
    projectiveCoeffHeight P = Height.logHeight (coeffTuple P) := by
  rfl

/-- Projective coefficient height is invariant under nonzero rational
scaling. -/
theorem projectiveCoeffHeight_smul {ι : Type*} (P : MvPolynomial ι ℚ)
    {a : ℚ} (ha : a ≠ 0) :
    projectiveCoeffHeight (a • P) = projectiveCoeffHeight P := by
  classical
  have hsupp : (a • P).support = P.support :=
    MvPolynomial.support_smul_eq ha P
  unfold projectiveCoeffHeight
  rw [hsupp]
  change Height.logHeight (a • coeffTuple P) = Height.logHeight (coeffTuple P)
  exact Height.logHeight_smul_eq_logHeight _ ha

/-- Injectively renaming variables does not change projective coefficient
height. -/
theorem projectiveCoeffHeight_rename_of_injective {ι κ : Type*}
    (P : MvPolynomial ι ℚ) (f : ι → κ) (hf : Function.Injective f) :
    projectiveCoeffHeight (MvPolynomial.rename f P) =
      projectiveCoeffHeight P := by
  classical
  let g : (ι →₀ ℕ) → (κ →₀ ℕ) := Finsupp.mapDomain f
  have hg : Function.Injective g := Finsupp.mapDomain_injective hf
  have hsupp : (MvPolynomial.rename f P).support =
      P.support.image g := MvPolynomial.support_rename_of_injective hf
  let eFun : P.support → (MvPolynomial.rename f P).support := fun J ↦
    ⟨g J.1, by rw [hsupp]; exact Finset.mem_image.mpr ⟨J.1, J.2, rfl⟩⟩
  have heinj : Function.Injective eFun := by
    intro J K h
    apply Subtype.ext
    apply hg
    exact Subtype.ext_iff.mp h
  have hesurj : Function.Surjective eFun := by
    intro L
    have hLimage : L.1 ∈ P.support.image g := by
      rw [← hsupp]
      exact L.2
    obtain ⟨J, hJ, hJL⟩ := Finset.mem_image.mp hLimage
    refine ⟨⟨J, hJ⟩, ?_⟩
    apply Subtype.ext
    simpa [eFun] using hJL
  let e : P.support ≃ (MvPolynomial.rename f P).support :=
    Equiv.ofBijective eFun ⟨heinj, hesurj⟩
  calc
    projectiveCoeffHeight (MvPolynomial.rename f P) =
        Height.logHeight (coeffTuple (MvPolynomial.rename f P) ∘ e) := by
      rw [projectiveCoeffHeight_eq_logHeight_coeffTuple,
        Height.logHeight_comp_equiv]
    _ = projectiveCoeffHeight P := by
      rw [projectiveCoeffHeight_eq_logHeight_coeffTuple]
      congr 1
      funext J
      exact MvPolynomial.coeff_rename_mapDomain f hf P J.1

/-- Projective coefficient height cannot increase when one keeps a subset
of the coefficient coordinates unchanged.  This is the common core of
coefficient extraction, setting selected variables to zero, and taking a
monomial slice. -/
theorem projectiveCoeffHeight_le_of_coeff_subvector {ι : Type*}
    {P Q : MvPolynomial ι ℚ}
    (hsupp : Q.support ⊆ P.support)
    (hcoeff : ∀ J ∈ Q.support,
      MvPolynomial.coeff J Q = MvPolynomial.coeff J P) :
    projectiveCoeffHeight Q ≤ projectiveCoeffHeight P := by
  classical
  let f : Q.support → P.support := fun J ↦ ⟨J.1, hsupp J.2⟩
  have h := Height.logHeight_comp_le f (coeffTuple P)
  simpa only [← projectiveCoeffHeight_eq_logHeight_coeffTuple] using
    (show Height.logHeight (coeffTuple Q) ≤ Height.logHeight (coeffTuple P) from by
      convert h using 1
      congr 1
      funext J
      exact hcoeff J J.2)

/-- A diagonal coefficient transformation is bounded by the height of its
multiplier tuple.  This is the height-theoretic core used for divided
derivatives after reindexing their support. -/
theorem projectiveCoeffHeight_le_of_diagonal {ι : Type*}
    {P Q : MvPolynomial ι ℚ} (c : P.support → ℚ)
    (hsupp : Q.support ⊆ P.support)
    (hcoeff : ∀ J : Q.support,
      MvPolynomial.coeff J Q = c ⟨J, hsupp J.2⟩ *
        MvPolynomial.coeff J P) :
    projectiveCoeffHeight Q ≤
      projectiveCoeffHeight P + Height.logHeight c := by
  classical
  let f : Q.support → P.support := fun J ↦ ⟨J.1, hsupp J.2⟩
  have hPcomp := Height.logHeight_comp_le f (coeffTuple P)
  have hccomp := Height.logHeight_comp_le f c
  have hmul := Height.logHeight_mul_le (coeffTuple P ∘ f) (c ∘ f)
  have heq : coeffTuple Q = (coeffTuple P ∘ f) * (c ∘ f) := by
    funext J
    calc
      coeffTuple Q J = c (f J) * coeffTuple P (f J) := hcoeff J
      _ = coeffTuple P (f J) * c (f J) := mul_comm _ _
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple Q,
    projectiveCoeffHeight_eq_logHeight_coeffTuple P, heq]
  linarith

/-- A diagonal coefficient transformation after an arbitrary reindexing of
the nonzero coefficients.  Injectivity is not required: restricting or
repeating coordinates can only decrease projective height. -/
theorem projectiveCoeffHeight_le_of_reindex_diagonal {ι κ : Type*}
    {P : MvPolynomial ι ℚ} {Q : MvPolynomial κ ℚ}
    (f : Q.support → P.support) (c : Q.support → ℚ)
    (hcoeff : ∀ J : Q.support,
      MvPolynomial.coeff J Q = c J * MvPolynomial.coeff (f J) P) :
    projectiveCoeffHeight Q ≤
      projectiveCoeffHeight P + Height.logHeight c := by
  classical
  have hPcomp := Height.logHeight_comp_le f (coeffTuple P)
  have hmul := Height.logHeight_mul_le (coeffTuple P ∘ f) c
  have heq : coeffTuple Q = (coeffTuple P ∘ f) * c := by
    funext J
    calc
      coeffTuple Q J = c J * coeffTuple P (f J) := hcoeff J
      _ = coeffTuple P (f J) * c J := mul_comm _ _
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple Q,
    projectiveCoeffHeight_eq_logHeight_coeffTuple P, heq]
  linarith

/-- A tuple of nonnegative rational integers bounded by `B` has projective
height at most `log B`.  Appending the coordinate `1` makes the representing
integer tuple primitive, which avoids any coprimality hypothesis. -/
theorem logHeight_natCast_le_log {κ : Type*} [Fintype κ]
    (a : κ → ℕ) (B : ℕ) (hB : 0 < B) (ha : ∀ j, a j ≤ B) :
    Height.logHeight (fun j ↦ (a j : ℚ)) ≤ Real.log B := by
  classical
  let x : κ ⊕ Unit → ℤ := Sum.elim (fun j ↦ (a j : ℤ)) (fun _ ↦ 1)
  let y : κ ⊕ Unit → ℚ := ((↑) : ℤ → ℚ) ∘ x
  let f : κ → κ ⊕ Unit := Sum.inl
  have hrestrict := Height.logHeight_comp_le f y
  have hcomp : y ∘ f = fun j ↦ (a j : ℚ) := by
    funext j
    simp [x, y, f]
  rw [hcomp] at hrestrict
  have hgcd : Finset.univ.gcd x = 1 := by
    have hdvd : Finset.univ.gcd x ∣ (1 : ℤ) := by
      simpa [x] using
        (Finset.gcd_dvd (s := (Finset.univ : Finset (κ ⊕ Unit)))
          (f := x) (b := Sum.inr ()) (Finset.mem_univ _))
    rw [← Finset.normalize_gcd, normalize_eq_one]
    exact isUnit_iff_dvd_one.mpr hdvd
  have hmax : (⨆ j, |x j|) ≤ (B : ℤ) := by
    apply ciSup_le
    intro j
    cases j with
    | inl j => simpa [x] using ha j
    | inr u => simp [x]; omega
  have hmaxpos : (0 : ℤ) < ⨆ j, |x j| := by
    have hone : (1 : ℤ) ≤ ⨆ j, |x j| :=
      Finite.le_ciSup_of_le (Sum.inr ()) (by simp [x])
    omega
  have hy := Rat.logHeight_eq_max_abs_of_gcd_eq_one (x := x) hgcd
  rw [show ((↑) : ℤ → ℚ) ∘ x = y from rfl] at hy
  calc
    Height.logHeight (fun j ↦ (a j : ℚ)) ≤ Height.logHeight y := hrestrict
    _ = Real.log (((⨆ j, |x j|) : ℤ) : ℝ) := hy
    _ ≤ Real.log B := by
      apply Real.log_le_log
      · exact_mod_cast hmaxpos
      · exact_mod_cast hmax

/-- Signed integral version of `logHeight_natCast_le_log`. -/
theorem logHeight_intCast_le_log {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (B : ℕ) (hB : 0 < B) (ha : ∀ j, (a j).natAbs ≤ B) :
    Height.logHeight (fun j ↦ (a j : ℚ)) ≤ Real.log B := by
  classical
  let x : κ ⊕ Unit → ℤ := Sum.elim a (fun _ ↦ 1)
  let y : κ ⊕ Unit → ℚ := ((↑) : ℤ → ℚ) ∘ x
  let f : κ → κ ⊕ Unit := Sum.inl
  have hrestrict := Height.logHeight_comp_le f y
  have hcomp : y ∘ f = fun j ↦ (a j : ℚ) := by
    funext j
    simp [x, y, f]
  rw [hcomp] at hrestrict
  have hgcd : Finset.univ.gcd x = 1 := by
    have hdvd : Finset.univ.gcd x ∣ (1 : ℤ) := by
      simpa [x] using
        (Finset.gcd_dvd (s := (Finset.univ : Finset (κ ⊕ Unit)))
          (f := x) (b := Sum.inr ()) (Finset.mem_univ _))
    rw [← Finset.normalize_gcd, normalize_eq_one]
    exact isUnit_iff_dvd_one.mpr hdvd
  have hmax : (⨆ j, |x j|) ≤ (B : ℤ) := by
    apply ciSup_le
    intro j
    cases j with
    | inl j =>
        change |a j| ≤ (B : ℤ)
        rw [Int.abs_eq_natAbs]
        exact_mod_cast ha j
    | inr u => simp [x]; omega
  have hmaxpos : (0 : ℤ) < ⨆ j, |x j| := by
    have hone : (1 : ℤ) ≤ ⨆ j, |x j| :=
      Finite.le_ciSup_of_le (Sum.inr ()) (by simp [x])
    omega
  have hy := Rat.logHeight_eq_max_abs_of_gcd_eq_one (x := x) hgcd
  rw [show ((↑) : ℤ → ℚ) ∘ x = y from rfl] at hy
  calc
    Height.logHeight (fun j ↦ (a j : ℚ)) ≤ Height.logHeight y := hrestrict
    _ = Real.log (((⨆ j, |x j|) : ℤ) : ℝ) := hy
    _ ≤ Real.log B := by
      apply Real.log_le_log
      · exact_mod_cast hmaxpos
      · exact_mod_cast hmax

/-! ## Rational point and linear-factor heights -/

/-- Logarithmic projective height of the rational point `[x : 1]`. -/
def rationalPointHeight (x : ℚ) : ℝ := Height.logHeight ![x, 1]

theorem rationalPointHeight_eq_logHeight₁ (x : ℚ) :
    rationalPointHeight x = Height.logHeight₁ x := by
  simpa [rationalPointHeight] using (Height.logHeight₁_eq_logHeight x).symm

theorem rationalPointHeight_eq_log_max (x : ℚ) :
    rationalPointHeight x = Real.log ((max x.num.natAbs x.den : ℕ) : ℝ) := by
  rw [rationalPointHeight_eq_logHeight₁, Rat.logHeight₁_eq_log_max]

/-! ## Exact products in disjoint variable sets -/

/-- The exponent obtained by joining exponents on two disjoint variable
sets. -/
def disjointJoin {ι κ : Type*} (z : (ι →₀ ℕ) × (κ →₀ ℕ)) :
    ι ⊕ κ →₀ ℕ :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm z

/-- The coefficient-tensor polynomial on a disjoint union of variable sets. -/
def disjointTensorProduct {ι κ : Type*} (P : MvPolynomial ι ℚ)
    (Q : MvPolynomial κ ℚ) : MvPolynomial (ι ⊕ κ) ℚ := by
  classical
  exact ∑ z : P.support × Q.support,
    MvPolynomial.monomial (disjointJoin (z.1.1, z.2.1))
      (MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q)

/-- Coefficients of the disjoint tensor product are literal products, with
no convolution or cancellation. -/
theorem coeff_disjointTensorProduct {ι κ : Type*}
    (P : MvPolynomial ι ℚ) (Q : MvPolynomial κ ℚ)
    (L : ι ⊕ κ →₀ ℕ) :
    MvPolynomial.coeff L (disjointTensorProduct P Q) =
      MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp L).1 P *
        MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp L).2 Q := by
  classical
  let E : (ι ⊕ κ →₀ ℕ) ≃ ((ι →₀ ℕ) × (κ →₀ ℕ)) :=
    Finsupp.sumFinsuppEquivProdFinsupp
  let J := (E L).1
  let K := (E L).2
  have hjoinJK : disjointJoin (J, K) = L := by
    change E.symm (E L) = L
    exact E.symm_apply_apply L
  have split_of_join (A : ι →₀ ℕ) (B : κ →₀ ℕ)
      (h : disjointJoin (A, B) = L) : A = J ∧ B = K := by
    change E.symm (A, B) = L at h
    have h' := congrArg E h
    rw [E.apply_symm_apply] at h'
    exact Prod.ext_iff.mp h'
  by_cases hJ : J ∈ P.support
  · by_cases hK : K ∈ Q.support
    · let z₀ : P.support × Q.support := ⟨⟨J, hJ⟩, ⟨K, hK⟩⟩
      unfold disjointTensorProduct
      rw [MvPolynomial.coeff_sum, Fintype.sum_eq_single z₀]
      · simp only [MvPolynomial.coeff_monomial]
        rw [if_pos (by simpa [z₀] using hjoinJK)]
      · intro z hz
        simp only [MvPolynomial.coeff_monomial]
        rw [if_neg]
        intro hjoin
        have hsplit := split_of_join z.1.1 z.2.1 hjoin
        apply hz
        apply Prod.ext <;> apply Subtype.ext
        · exact hsplit.1
        · exact hsplit.2
    · have hKcoeff : MvPolynomial.coeff K Q = 0 :=
        MvPolynomial.notMem_support_iff.mp hK
      rw [hKcoeff, mul_zero]
      unfold disjointTensorProduct
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro z _
      simp only [MvPolynomial.coeff_monomial]
      rw [if_neg]
      intro hjoin
      have hzK : z.2.1 = K := (split_of_join z.1.1 z.2.1 hjoin).2
      exact hK (hzK ▸ z.2.2)
  · have hJcoeff : MvPolynomial.coeff J P = 0 :=
      MvPolynomial.notMem_support_iff.mp hJ
    rw [hJcoeff, zero_mul]
    unfold disjointTensorProduct
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro z _
    simp only [MvPolynomial.coeff_monomial]
    rw [if_neg]
    intro hjoin
    have hzJ : z.1.1 = J := (split_of_join z.1.1 z.2.1 hjoin).1
    exact hJ (hzJ ▸ z.1.2)

/-- The explicit tensor polynomial is the ordinary product after injectively
renaming the factors into the two summands of the variable type. -/
theorem disjointTensorProduct_eq_mul_rename {ι κ : Type*}
    (P : MvPolynomial ι ℚ) (Q : MvPolynomial κ ℚ) :
    disjointTensorProduct P Q =
      MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q := by
  classical
  have hrenameP : MvPolynomial.rename (Sum.inl : ι → ι ⊕ κ) P =
      ∑ J ∈ P.support,
        MvPolynomial.monomial
          (Finsupp.mapDomain (Sum.inl : ι → ι ⊕ κ) J)
          (MvPolynomial.coeff J P) := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
    simp only [map_sum, MvPolynomial.rename_monomial]
  have hrenameQ : MvPolynomial.rename (Sum.inr : κ → ι ⊕ κ) Q =
      ∑ K ∈ Q.support,
        MvPolynomial.monomial
          (Finsupp.mapDomain (Sum.inr : κ → ι ⊕ κ) K)
          (MvPolynomial.coeff K Q) := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff Q]
    simp only [map_sum, MvPolynomial.rename_monomial]
  rw [hrenameP, hrenameQ]
  simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul]
  unfold disjointTensorProduct
  rw [Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_subtype P.support (fun _ ↦ Iff.rfl)
    (fun J ↦ ∑ K : Q.support,
      MvPolynomial.monomial (disjointJoin (J, K.1))
        (MvPolynomial.coeff J P * MvPolynomial.coeff K.1 Q))]
  have hinner (J : ι →₀ ℕ) :
      (∑ K : Q.support,
        MvPolynomial.monomial (disjointJoin (J, K.1))
          (MvPolynomial.coeff J P * MvPolynomial.coeff K.1 Q)) =
      ∑ K ∈ Q.support,
        MvPolynomial.monomial (disjointJoin (J, K))
          (MvPolynomial.coeff J P * MvPolynomial.coeff K Q) := by
    simpa only [] using
      (Finset.sum_subtype Q.support (fun _ ↦ Iff.rfl)
        (fun K ↦ MvPolynomial.monomial (disjointJoin (J, K))
          (MvPolynomial.coeff J P * MvPolynomial.coeff K Q))).symm
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K hK
  apply Finset.sum_congr rfl
  intro J hJ
  congr 2
  apply Finsupp.sumFinsuppEquivProdFinsupp.injective
  apply Prod.ext
  · ext x
    change J x =
      Finsupp.mapDomain (Sum.inl : ι → ι ⊕ κ) J (Sum.inl x) +
        Finsupp.mapDomain (Sum.inr : κ → ι ⊕ κ) K (Sum.inl x)
    rw [Finsupp.mapDomain_apply Sum.inl_injective]
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · simp
  · ext x
    change K x =
      Finsupp.mapDomain (Sum.inl : ι → ι ⊕ κ) J (Sum.inr x) +
        Finsupp.mapDomain (Sum.inr : κ → ι ⊕ κ) K (Sum.inr x)
    rw [Finsupp.mapDomain_apply Sum.inr_injective]
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · simp

private noncomputable def multiplicationMatrix {ι : Type*} (P Q : MvPolynomial ι ℚ) :
    (P * Q).support × (P.support × Q.support) → ℚ :=
  by
    classical
    exact fun z ↦ if z.2.1.1 + z.2.2.1 = z.1.1 then 1 else 0

private def coefficientTensor {ι κ : Type*} (P : MvPolynomial ι ℚ)
    (Q : MvPolynomial κ ℚ) :
    P.support × Q.support → ℚ :=
  fun z ↦ MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q

private theorem coeff_mul_eq_matrix_sum {ι : Type*}
    (P Q : MvPolynomial ι ℚ) (J : (P * Q).support) :
    MvPolynomial.coeff J (P * Q) =
      ∑ z : P.support × Q.support,
        multiplicationMatrix P Q (J, z) * coefficientTensor P Q z := by
  classical
  unfold MvPolynomial.coeff
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, coefficientTensor, multiplicationMatrix, one_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_subtype (AddMonoidAlgebra.coeff P).support (fun _ ↦ Iff.rfl)]
  simp_rw [Finset.sum_subtype (AddMonoidAlgebra.coeff Q).support (fun _ ↦ Iff.rfl)]
  rw [Fintype.sum_prod_type]
  rfl

private theorem logHeight_multiplicationMatrix {ι : Type*}
    {P Q : MvPolynomial ι ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Height.logHeight (multiplicationMatrix P Q) = 0 := by
  classical
  rw [Height.logHeight_eq_logHeight_restrict_support]
  have hone :
      (fun z : Function.support (multiplicationMatrix P Q) ↦
        multiplicationMatrix P Q z) = 1 := by
    funext z
    have hz := z.property
    simp only [Function.mem_support, ne_eq, multiplicationMatrix] at hz ⊢
    split_ifs at hz ⊢ <;> simp_all
  rw [hone, Height.logHeight_one]

private theorem logHeight_coefficientTensor {ι κ : Type*}
    {P : MvPolynomial ι ℚ} {Q : MvPolynomial κ ℚ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Height.logHeight (coefficientTensor P Q) =
      projectiveCoeffHeight P + projectiveCoeffHeight Q := by
  change Height.logHeight (fun z : P.support × Q.support ↦
    MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q) = _
  simpa only [projectiveCoeffHeight_eq_logHeight_coeffTuple] using
    Height.logHeight_fun_mul_eq (coeffTuple_ne_zero hP) (coeffTuple_ne_zero hQ)

/-- Exact additivity for the explicit product in disjoint variable sets. -/
theorem projectiveCoeffHeight_disjointTensorProduct {ι κ : Type*}
    {P : MvPolynomial ι ℚ} {Q : MvPolynomial κ ℚ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    projectiveCoeffHeight (disjointTensorProduct P Q) =
      projectiveCoeffHeight P + projectiveCoeffHeight Q := by
  classical
  let D := disjointTensorProduct P Q
  let E : (ι ⊕ κ →₀ ℕ) ≃ ((ι →₀ ℕ) × (κ →₀ ℕ)) :=
    Finsupp.sumFinsuppEquivProdFinsupp
  let eFun : P.support × Q.support → D.support := fun z ↦
    ⟨E.symm (z.1.1, z.2.1), by
      rw [MvPolynomial.mem_support_iff]
      change MvPolynomial.coeff (E.symm (z.1.1, z.2.1))
        (disjointTensorProduct P Q) ≠ 0
      rw [coeff_disjointTensorProduct]
      change MvPolynomial.coeff (E (E.symm (z.1.1, z.2.1))).1 P *
        MvPolynomial.coeff (E (E.symm (z.1.1, z.2.1))).2 Q ≠ 0
      rw [E.apply_symm_apply]
      exact mul_ne_zero (MvPolynomial.mem_support_iff.mp z.1.2)
        (MvPolynomial.mem_support_iff.mp z.2.2)⟩
  have heinj : Function.Injective eFun := by
    intro z w h
    have hval := Subtype.ext_iff.mp h
    change E.symm (z.1.1, z.2.1) = E.symm (w.1.1, w.2.1) at hval
    have hpair := E.symm.injective hval
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair
  have hesurj : Function.Surjective eFun := by
    intro L
    have hcoeff := MvPolynomial.mem_support_iff.mp L.2
    change MvPolynomial.coeff L.1 (disjointTensorProduct P Q) ≠ 0 at hcoeff
    rw [coeff_disjointTensorProduct] at hcoeff
    have hleft : MvPolynomial.coeff (E L.1).1 P ≠ 0 :=
      left_ne_zero_of_mul hcoeff
    have hright : MvPolynomial.coeff (E L.1).2 Q ≠ 0 :=
      right_ne_zero_of_mul hcoeff
    let z : P.support × Q.support :=
      ⟨⟨(E L.1).1, MvPolynomial.mem_support_iff.mpr hleft⟩,
        ⟨(E L.1).2, MvPolynomial.mem_support_iff.mpr hright⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change E.symm (E L.1) = L.1
    exact E.symm_apply_apply L.1
  let e : P.support × Q.support ≃ D.support :=
    Equiv.ofBijective eFun ⟨heinj, hesurj⟩
  calc
    projectiveCoeffHeight D = Height.logHeight (coeffTuple D ∘ e) := by
      rw [projectiveCoeffHeight_eq_logHeight_coeffTuple,
        Height.logHeight_comp_equiv]
    _ = Height.logHeight (coefficientTensor P Q) := by
      congr 1
      funext z
      change MvPolynomial.coeff (E.symm (z.1.1, z.2.1))
        (disjointTensorProduct P Q) = _
      rw [coeff_disjointTensorProduct]
      change MvPolynomial.coeff (E (E.symm (z.1.1, z.2.1))).1 P *
        MvPolynomial.coeff (E (E.symm (z.1.1, z.2.1))).2 Q = _
      rw [E.apply_symm_apply]
      rfl
    _ = projectiveCoeffHeight P + projectiveCoeffHeight Q :=
      logHeight_coefficientTensor hP hQ

/-- GLR Remark 2.12 over `ℚ`: products in disjoint variable sets have
exactly additive projective coefficient height. -/
theorem projectiveCoeffHeight_mul_rename_disjoint {ι κ : Type*}
    {P : MvPolynomial ι ℚ} {Q : MvPolynomial κ ℚ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    projectiveCoeffHeight
        (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q) =
      projectiveCoeffHeight P + projectiveCoeffHeight Q := by
  rw [← disjointTensorProduct_eq_mul_rename]
  exact projectiveCoeffHeight_disjointTensorProduct hP hQ

/-- The disjoint-variable height identity transported along any two
injective maps with disjoint images. -/
theorem projectiveCoeffHeight_mul_rename_disjoint_of_maps
    {ι κ τ : Type*} {P : MvPolynomial ι ℚ} {Q : MvPolynomial κ ℚ}
    (f : ι → τ) (g : κ → τ) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ i j, f i ≠ g j)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    projectiveCoeffHeight (MvPolynomial.rename f P * MvPolynomial.rename g Q) =
      projectiveCoeffHeight P + projectiveCoeffHeight Q := by
  let e : ι ⊕ κ → τ := Sum.elim f g
  have he : Function.Injective e := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (hf hxy)
        | inr j => exact False.elim (hfg i j hxy)
    | inr i =>
        cases y with
        | inl j => exact False.elim (hfg j i hxy.symm)
        | inr j => exact congrArg Sum.inr (hg hxy)
  have hrename :
      MvPolynomial.rename e
          (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q) =
        MvPolynomial.rename f P * MvPolynomial.rename g Q := by
    rw [map_mul]
    congr 1
    · rw [MvPolynomial.rename_rename]
      rfl
    · rw [MvPolynomial.rename_rename]
      rfl
  calc
    projectiveCoeffHeight (MvPolynomial.rename f P * MvPolynomial.rename g Q) =
        projectiveCoeffHeight (MvPolynomial.rename e
          (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q)) :=
      congrArg projectiveCoeffHeight hrename.symm
    _ = projectiveCoeffHeight
        (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q) :=
      projectiveCoeffHeight_rename_of_injective _ e he
    _ = projectiveCoeffHeight P + projectiveCoeffHeight Q :=
      projectiveCoeffHeight_mul_rename_disjoint hP hQ

private theorem finSuccEquiv_rename_succ {m : ℕ}
    (A : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.finSuccEquiv ℚ m (MvPolynomial.rename Fin.succ A) =
      Polynomial.C A := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add A B hA hB => simp [hA, hB]
  | mul_X A i hA => simp [hA, MvPolynomial.finSuccEquiv_X_succ]

private theorem finSuccEquiv_rename_zero_unique_symm {m : ℕ}
    (q : Polynomial ℚ) :
    MvPolynomial.finSuccEquiv ℚ m
        (MvPolynomial.rename (fun _ : Fin 1 ↦ (0 : Fin (m + 1)))
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q)) =
      q.map MvPolynomial.C := by
  let T : Polynomial ℚ →+* Polynomial (MvPolynomial (Fin m) ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ m).toRingEquiv.toRingHom.comp
      ((MvPolynomial.rename
        (fun _ : Fin 1 ↦ (0 : Fin (m + 1)))).toRingHom.comp
          (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm.toRingEquiv.toRingHom)
  have hT : T = Polynomial.mapRingHom MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [T, MvPolynomial.uniqueAlgEquiv,
        MvPolynomial.finSuccEquiv_apply]
    · simp [T, MvPolynomial.uniqueAlgEquiv,
        MvPolynomial.finSuccEquiv_X_zero]
  exact DFunLike.congr_fun hT q

/-- Splitting off variable zero by `finSuccEquiv` realizes a product of a
left multivariate factor and a right univariate factor as a product in
disjoint variable sets. -/
theorem finSuccEquiv_symm_C_mul_map_eq {m : ℕ}
    (A : MvPolynomial (Fin m) ℚ) (q : Polynomial ℚ) :
    (MvPolynomial.finSuccEquiv ℚ m).symm
        (Polynomial.C A * q.map MvPolynomial.C) =
      MvPolynomial.rename Fin.succ A *
        MvPolynomial.rename (fun _ : Fin 1 ↦ (0 : Fin (m + 1)))
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, finSuccEquiv_rename_succ,
    finSuccEquiv_rename_zero_unique_symm]

/-- Exact projective-height additivity for the left/right factorization
transported through `finSuccEquiv`. -/
theorem projectiveCoeffHeight_finSuccEquiv_symm_C_mul_map {m : ℕ}
    {A : MvPolynomial (Fin m) ℚ} {q : Polynomial ℚ}
    (hA : A ≠ 0) (hq : q ≠ 0) :
    projectiveCoeffHeight ((MvPolynomial.finSuccEquiv ℚ m).symm
        (Polynomial.C A * q.map MvPolynomial.C)) =
      projectiveCoeffHeight A +
        projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) := by
  have hqmv : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q ≠ 0 := by
    intro hz
    apply hq
    apply (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm.injective
    simpa using hz
  rw [finSuccEquiv_symm_C_mul_map_eq]
  exact projectiveCoeffHeight_mul_rename_disjoint_of_maps
    Fin.succ (fun _ : Fin 1 ↦ (0 : Fin (m + 1)))
    (@Fin.succ_injective m) (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun i _ ↦ Fin.succ_ne_zero i) hA hqmv

/-- Each nonzero factor in a `finSuccEquiv` left/right factorization has
height at most the height of the original multivariate polynomial. -/
theorem projectiveCoeffHeight_factors_le_of_finSuccEquiv_eq {m : ℕ}
    {V : MvPolynomial (Fin (m + 1)) ℚ}
    {A : MvPolynomial (Fin m) ℚ} {q : Polynomial ℚ}
    (hA : A ≠ 0) (hq : q ≠ 0)
    (hfactor : MvPolynomial.finSuccEquiv ℚ m V =
      Polynomial.C A * q.map MvPolynomial.C) :
    projectiveCoeffHeight A ≤ projectiveCoeffHeight V ∧
      projectiveCoeffHeight ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) ≤
        projectiveCoeffHeight V := by
  have hV : V = (MvPolynomial.finSuccEquiv ℚ m).symm
      (Polynomial.C A * q.map MvPolynomial.C) := by
    apply (MvPolynomial.finSuccEquiv ℚ m).injective
    rw [hfactor, AlgEquiv.apply_symm_apply]
  rw [hV, projectiveCoeffHeight_finSuccEquiv_symm_C_mul_map hA hq]
  constructor
  · exact le_add_of_nonneg_right (projectiveCoeffHeight_nonneg _)
  · exact le_add_of_nonneg_left (projectiveCoeffHeight_nonneg _)

/-- A coefficient-convolution height bound.  The loss is the logarithm of
the number of pairs of input monomials; degree bounds turn this into the
usual elementary GLR `log 2` loss. -/
theorem projectiveCoeffHeight_mul_le_support {ι : Type*}
    {P Q : MvPolynomial ι ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    projectiveCoeffHeight (P * Q) ≤
      Real.log (Nat.card P.support * Nat.card Q.support) +
        projectiveCoeffHeight P + projectiveCoeffHeight Q := by
  classical
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple]
  have hlin := Height.logHeight_linearMap_apply_le
    (multiplicationMatrix P Q) (coefficientTensor P Q)
  simp only [← coeff_mul_eq_matrix_sum] at hlin
  rw [logHeight_multiplicationMatrix hP hQ,
    logHeight_coefficientTensor hP hQ] at hlin
  norm_num [NumberField.totalWeight_eq_finrank] at hlin
  let eP : P.support ≃ {J // MvPolynomial.coeff J P ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ ↦ MvPolynomial.mem_support_iff)
  let eQ : Q.support ≃ {J // MvPolynomial.coeff J Q ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ ↦ MvPolynomial.mem_support_iff)
  have hcardP : Nat.card P.support =
      Nat.card {J // MvPolynomial.coeff J P ≠ 0} := Nat.card_congr eP
  have hcardQ : Nat.card Q.support =
      Nat.card {J // MvPolynomial.coeff J Q ≠ 0} := Nat.card_congr eQ
  convert hlin using 1 <;> simp only [hcardP, hcardQ, add_assoc]

/-! ## Heights of finite sums -/

/-- The disjoint union of all nonzero coefficient coordinates in a finite
family of polynomials. -/
abbrev FamilyCoeffIndex {α ι : Type*} (s : Finset α)
    (F : α → MvPolynomial ι ℚ) :=
  Σ i : {i // i ∈ s}, (F i.1).support

/-- The joint coefficient vector of a finite family.  Unlike the separate
projective heights, this records the relative scaling between summands. -/
def familyCoeffTuple {α ι : Type*} (s : Finset α)
    (F : α → MvPolynomial ι ℚ) : FamilyCoeffIndex s F → ℚ :=
  fun z ↦ MvPolynomial.coeff z.2 (F z.1.1)

private noncomputable def sumMatrix {α ι : Type*} (s : Finset α)
    (F : α → MvPolynomial ι ℚ) :
    (∑ i ∈ s, F i).support × FamilyCoeffIndex s F → ℚ := by
  classical
  exact fun z ↦ if z.2.2.1 = z.1.1 then 1 else 0

private theorem coeff_sum_eq_matrix_sum {α ι : Type*} (s : Finset α)
    (F : α → MvPolynomial ι ℚ) (J : (∑ i ∈ s, F i).support) :
    MvPolynomial.coeff J (∑ i ∈ s, F i) =
      ∑ z : FamilyCoeffIndex s F,
        sumMatrix s F (J, z) * familyCoeffTuple s F z := by
  classical
  rw [MvPolynomial.coeff_sum, Fintype.sum_sigma]
  unfold sumMatrix familyCoeffTuple
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_subtype s (fun _ ↦ Iff.rfl)]
  apply Fintype.sum_congr
  intro i
  calc
    MvPolynomial.coeff J (F i) =
        ∑ K ∈ (F i).support,
          if K = J.1 then MvPolynomial.coeff K (F i) else 0 := by
      symm
      rw [Finset.sum_ite_eq']
      by_cases hJ : J.1 ∈ (F i).support
      · simp [hJ]
      · simp [hJ, MvPolynomial.notMem_support_iff.mp hJ]
    _ = ∑ K : (F i).support,
          if K.1 = J.1 then MvPolynomial.coeff K.1 (F i) else 0 :=
      Finset.sum_subtype (F i).support (fun _ ↦ Iff.rfl) _
    _ = _ := by rfl

private theorem logHeight_sumMatrix {α ι : Type*} (s : Finset α)
    (F : α → MvPolynomial ι ℚ) : Height.logHeight (sumMatrix s F) = 0 := by
  classical
  rw [Height.logHeight_eq_logHeight_restrict_support]
  have hone :
      (fun z : Function.support (sumMatrix s F) ↦ sumMatrix s F z) = 1 := by
    funext z
    have hz := z.property
    simp only [Function.mem_support, ne_eq, sumMatrix] at hz ⊢
    split_ifs at hz ⊢ <;> simp_all
  rw [hone, Height.logHeight_one]

/-- Height of a finite polynomial sum, in terms of the joint coefficient
vector.  The joint height is necessary: separate projective heights forget
the relative rational scaling of the summands. -/
theorem projectiveCoeffHeight_finsetSum_le_joint {α ι : Type*}
    (s : Finset α) (F : α → MvPolynomial ι ℚ) :
    projectiveCoeffHeight (∑ i ∈ s, F i) ≤
      Real.log (Nat.card (FamilyCoeffIndex s F)) +
        Height.logHeight (familyCoeffTuple s F) := by
  classical
  unfold projectiveCoeffHeight
  have hlin := Height.logHeight_linearMap_apply_le
    (sumMatrix s F) (familyCoeffTuple s F)
  simp only [← coeff_sum_eq_matrix_sum] at hlin
  rw [logHeight_sumMatrix] at hlin
  norm_num [NumberField.totalWeight_eq_finrank] at hlin
  have hsupport : {z // familyCoeffTuple s F z ≠ 0} ≃
      FamilyCoeffIndex s F :=
    { toFun := fun z ↦ z.1
      invFun := fun z ↦ ⟨z, by
        exact MvPolynomial.mem_support_iff.mp z.2.2⟩
      left_inv := fun z ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  have hcard : Nat.card {z // familyCoeffTuple s F z ≠ 0} =
      Nat.card (FamilyCoeffIndex s F) := Nat.card_congr hsupport
  have hfamilycard : Nat.card (FamilyCoeffIndex s F) =
      ∑ i : {i // i ∈ s}, (F i.1).support.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hfamilycard]
  have hcast : ((∑ i : {i // i ∈ s}, (F i.1).support.card : ℕ) : ℝ) =
      ∑ i : {i // i ∈ s}, ((F i.1).support.card : ℝ) := by
    norm_cast
  rw [hcast]
  simpa [hcard, zero_add, add_assoc] using hlin

/-- A reusable shared-scaling bound.  If every coefficient of `V` is the
evaluation at the coefficient vector of `P` of a homogeneous form of degree
`N`, then `h(V)` is bounded by `N * h(P)` plus the explicit height constant
of that family of forms.  This is the direct interface for determinant
coefficient forms. -/
theorem projectiveCoeffHeight_le_of_homogeneous_coefficientMap
    {ι κ : Type*} {P : MvPolynomial ι ℚ} {V : MvPolynomial κ ℚ}
    {N : ℕ} (A : V.support → MvPolynomial P.support ℚ)
    (hhom : ∀ J : V.support, (A J).IsHomogeneous N)
    (hcoeff : ∀ J : V.support, MvPolynomial.coeff J V =
      MvPolynomial.eval (coeffTuple P) (A J)) :
    projectiveCoeffHeight V ≤
      Real.log (max (Height.mulHeightBound A) 1) +
        N * projectiveCoeffHeight P := by
  have h := Height.logHeight_eval_le hhom (coeffTuple P)
  have heq : (fun J ↦ MvPolynomial.eval (coeffTuple P) (A J)) =
      coeffTuple V := by
    funext J
    exact (hcoeff J).symm
  rw [heq] at h
  simpa only [projectiveCoeffHeight_eq_logHeight_coeffTuple] using h

/-- A Leibniz summand of a polynomial matrix determinant. -/
def determinantSummand {n ι : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι ℚ)) (σ : Equiv.Perm n) :
    MvPolynomial ι ℚ :=
  Equiv.Perm.sign σ • ∏ i, A (σ i) i

/-- Determinant height in terms of the joint coefficient vector of its
Leibniz summands.  This retains the relative scaling which separate
projective heights necessarily discard. -/
theorem projectiveCoeffHeight_det_le_joint {n ι : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι ℚ)) :
    projectiveCoeffHeight (Matrix.det A) ≤
      Real.log (Nat.card
        (FamilyCoeffIndex (Finset.univ : Finset (Equiv.Perm n))
          (determinantSummand A))) +
      Height.logHeight
        (familyCoeffTuple (Finset.univ : Finset (Equiv.Perm n))
          (determinantSummand A)) := by
  have h := projectiveCoeffHeight_finsetSum_le_joint
    (Finset.univ : Finset (Equiv.Perm n)) (determinantSummand A)
  simpa [determinantSummand, Matrix.det_apply] using h

/-! ## Degree-specialized product bound -/

/-- Every occurring monomial is componentwise bounded by `d`. -/
def HasPartialDegreeAtMost {ι : Type*} (P : MvPolynomial ι ℚ)
    (d : ι → ℕ) : Prop :=
  ∀ J ∈ P.support, ∀ i, J i ≤ d i

theorem hasPartialDegreeAtMost_iff_degreeOf_le {ι : Type*}
    {P : MvPolynomial ι ℚ} {d : ι → ℕ} :
    HasPartialDegreeAtMost P d ↔ ∀ i, MvPolynomial.degreeOf i P ≤ d i := by
  constructor
  · intro h i
    exact MvPolynomial.degreeOf_le_iff.mpr (fun J hJ ↦ h J hJ i)
  · intro h J hJ i
    exact MvPolynomial.degreeOf_le_iff.mp (h i) J hJ

theorem HasPartialDegreeAtMost.zero {ι : Type*} (d : ι → ℕ) :
    HasPartialDegreeAtMost (0 : MvPolynomial ι ℚ) d := by
  intro J hJ
  simp at hJ

theorem HasPartialDegreeAtMost.smul {S ι : Type*} [SMulZeroClass S ℚ]
    {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hP : HasPartialDegreeAtMost P d) (a : S) :
    HasPartialDegreeAtMost (a • P) d := by
  intro J hJ i
  exact hP J (MvPolynomial.support_smul hJ) i

theorem HasPartialDegreeAtMost.add {ι : Type*}
    {P Q : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hP : HasPartialDegreeAtMost P d)
    (hQ : HasPartialDegreeAtMost Q d) :
    HasPartialDegreeAtMost (P + Q) d := by
  rw [hasPartialDegreeAtMost_iff_degreeOf_le] at hP hQ ⊢
  intro i
  exact (MvPolynomial.degreeOf_add_le i P Q).trans
    (max_le (hP i) (hQ i))

theorem HasPartialDegreeAtMost.mul {ι : Type*}
    {P Q : MvPolynomial ι ℚ} {d e : ι → ℕ}
    (hP : HasPartialDegreeAtMost P d)
    (hQ : HasPartialDegreeAtMost Q e) :
    HasPartialDegreeAtMost (P * Q) (fun i ↦ d i + e i) := by
  rw [hasPartialDegreeAtMost_iff_degreeOf_le] at hP hQ ⊢
  intro i
  exact (MvPolynomial.degreeOf_mul_le i P Q).trans
    (Nat.add_le_add (hP i) (hQ i))

theorem HasPartialDegreeAtMost.finsetSum {α ι : Type*}
    (s : Finset α) (f : α → MvPolynomial ι ℚ) (d : ι → ℕ)
    (hf : ∀ a ∈ s, HasPartialDegreeAtMost (f a) d) :
    HasPartialDegreeAtMost (s.sum f) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasPartialDegreeAtMost.zero d
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)))

theorem HasPartialDegreeAtMost.finsetProd {α ι : Type*}
    (s : Finset α) (f : α → MvPolynomial ι ℚ) (d : ι → ℕ)
    (hf : ∀ a ∈ s, HasPartialDegreeAtMost (f a) d) :
    HasPartialDegreeAtMost (s.prod f) (fun i ↦ s.card * d i) := by
  rw [hasPartialDegreeAtMost_iff_degreeOf_le]
  intro i
  calc
    MvPolynomial.degreeOf i (s.prod f) ≤
        ∑ a ∈ s, MvPolynomial.degreeOf i (f a) := by
      simpa using MvPolynomial.degreeOf_prod_le i s f
    _ ≤ ∑ _a ∈ s, d i := by
      exact Finset.sum_le_sum fun a ha ↦
        hasPartialDegreeAtMost_iff_degreeOf_le.mp (hf a ha) i
    _ = s.card * d i := by simp

/-- If every entry of a square polynomial matrix has partial degrees bounded
by `d`, its determinant has partial degrees bounded by `card n * d`. -/
theorem HasPartialDegreeAtMost.det {n ι : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι ℚ)) (d : ι → ℕ)
    (hA : ∀ a b, HasPartialDegreeAtMost (A a b) d) :
    HasPartialDegreeAtMost A.det (fun i ↦ Nat.card n * d i) := by
  rw [Matrix.det_apply]
  apply HasPartialDegreeAtMost.finsetSum
  intro σ _
  apply HasPartialDegreeAtMost.smul
  have hprod := HasPartialDegreeAtMost.finsetProd
    (Finset.univ : Finset n) (fun b ↦ A (σ b) b) d
      (fun b _ ↦ hA (σ b) b)
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hprod

/-! ## Multivariate Hasse derivatives -/

/-- The integral binomial multiplier occurring in a multivariate divided
derivative. -/
def hasseMultiplier {ι : Type*} (I J : ι →₀ ℕ) : ℕ :=
  ∏ i ∈ I.support, Nat.choose (J i) (I i)

/-- The multivariate Hasse (divided) derivative.  Its coefficient at `K` is
`prod_i choose (K_i + I_i) I_i` times the coefficient of `P` at `K + I`.
The finite sum is taken over a support image only to exhibit finite support. -/
def hasseDerivative {ι : Type*} (I : ι →₀ ℕ) (P : MvPolynomial ι ℚ) :
    MvPolynomial ι ℚ := by
  classical
  exact ∑ K ∈ P.support.image (fun J ↦ J - I),
    MvPolynomial.monomial K
      ((hasseMultiplier I (K + I) : ℕ) * MvPolynomial.coeff (K + I) P)

@[simp] theorem coeff_hasseDerivative {ι : Type*} (I K : ι →₀ ℕ)
    (P : MvPolynomial ι ℚ) :
    MvPolynomial.coeff K (hasseDerivative I P) =
      (hasseMultiplier I (K + I) : ℕ) * MvPolynomial.coeff (K + I) P := by
  classical
  by_cases hKP : K + I ∈ P.support
  · have hmem : K ∈ P.support.image (fun J ↦ J - I) := by
      apply Finset.mem_image.mpr
      refine ⟨K + I, hKP, ?_⟩
      ext i
      simp
    unfold hasseDerivative
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    simp [hmem]
  · have hcoeff : MvPolynomial.coeff (K + I) P = 0 :=
      MvPolynomial.notMem_support_iff.mp hKP
    unfold hasseDerivative
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    simp [hcoeff]

/-- The first Hasse derivative is the usual partial derivative. -/
@[simp] theorem hasseDerivative_single_one {ι : Type*} (i : ι)
    (P : MvPolynomial ι ℚ) :
    hasseDerivative (Finsupp.single i 1) P = MvPolynomial.pderiv i P := by
  classical
  apply MvPolynomial.ext
  intro K
  rw [coeff_hasseDerivative, MvPolynomial.coeff_pderiv]
  have hm : hasseMultiplier (Finsupp.single i 1)
      (K + Finsupp.single i 1) = K i + 1 := by
    simp [hasseMultiplier]
  rw [hm]
  push_cast
  ring

/-- Hasse differentiation preserves any componentwise upper degree bound. -/
theorem HasPartialDegreeAtMost.hasseDerivative {ι : Type*}
    {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) (I : ι →₀ ℕ) :
    HasPartialDegreeAtMost (hasseDerivative I P) d := by
  intro K hK i
  have hshift : K + I ∈ P.support := by
    rw [MvPolynomial.mem_support_iff]
    intro hz
    have hnz := MvPolynomial.mem_support_iff.mp hK
    rw [coeff_hasseDerivative, hz, mul_zero] at hnz
    exact hnz rfl
  calc
    K i ≤ (K + I) i := by simp only [Finsupp.add_apply]; omega
    _ ≤ d i := hdeg (K + I) hshift i

private theorem hasseMultiplier_le_two_pow_sum {ι : Type*} [Fintype ι]
    {I J : ι →₀ ℕ} {d : ι → ℕ} (hJ : ∀ i, J i ≤ d i) :
    hasseMultiplier I J ≤ 2 ^ (∑ i, d i) := by
  classical
  calc
    hasseMultiplier I J ≤ ∏ i ∈ I.support, 2 ^ J i := by
      unfold hasseMultiplier
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ Nat.choose_le_two_pow _ _)
    _ ≤ ∏ i ∈ I.support, 2 ^ d i := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ Nat.pow_le_pow_right (by omega) (hJ i))
    _ = 2 ^ (∑ i ∈ I.support, d i) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 2 ^ (∑ i, d i) := by
      apply Nat.pow_le_pow_right (by omega)
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ I.support)

/-- Rational specialization of GLR Lemma 2.22: a multivariate divided
derivative loses at most `(sum d_i) * log 2` in projective coefficient
height. -/
theorem projectiveCoeffHeight_hasseDerivative_le {ι : Type*} [Fintype ι]
    {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) (I : ι →₀ ℕ) :
    projectiveCoeffHeight (hasseDerivative I P) ≤
      projectiveCoeffHeight P + (∑ i, d i : ℝ) * Real.log 2 := by
  classical
  let D := hasseDerivative I P
  let shift : D.support → P.support := fun K ↦
    ⟨K.1 + I, by
      rw [MvPolynomial.mem_support_iff]
      intro hz
      have hK := MvPolynomial.mem_support_iff.mp K.2
      rw [coeff_hasseDerivative, hz, mul_zero] at hK
      exact hK rfl⟩
  let c : D.support → ℚ := fun K ↦ hasseMultiplier I (K.1 + I)
  have hdiag : projectiveCoeffHeight D ≤
      projectiveCoeffHeight P + Height.logHeight c := by
    apply projectiveCoeffHeight_le_of_reindex_diagonal shift c
    intro K
    rw [coeff_hasseDerivative]
  have hc : Height.logHeight c ≤ Real.log (2 ^ (∑ i, d i)) := by
    have hc' := logHeight_natCast_le_log
      (fun K : D.support ↦ hasseMultiplier I (K.1 + I))
      (2 ^ (∑ i, d i)) (by positivity) (by
        intro K
        apply hasseMultiplier_le_two_pow_sum
        intro i
        exact hdeg (shift K).1 (shift K).2 i)
    simpa [c] using hc'
  have hlog : Real.log (2 ^ (∑ i, d i)) =
      (∑ i, d i : ℝ) * Real.log 2 := by
    have hcast : ((∑ i, d i : ℕ) : ℝ) = ∑ i, (d i : ℝ) := by
      norm_cast
    rw [Real.log_pow, hcast]
  dsimp [D] at hdiag ⊢
  rw [hlog] at hc
  linarith

/-- Ordinary first-partial-derivative specialization of the Hasse bound. -/
theorem projectiveCoeffHeight_pderiv_le {ι : Type*} [Fintype ι]
    {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) (i : ι) :
    projectiveCoeffHeight (MvPolynomial.pderiv i P) ≤
      projectiveCoeffHeight P + (∑ j, d j : ℝ) * Real.log 2 := by
  simpa using projectiveCoeffHeight_hasseDerivative_le hdeg
    (Finsupp.single i 1)

/-- A mixed derivative obtained by two Hasse differentiations has the
`2 * (sum d_i) * log 2` loss used in the determinant estimate. -/
theorem projectiveCoeffHeight_hasseDerivative_hasseDerivative_le
    {ι : Type*} [Fintype ι] {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) (I J : ι →₀ ℕ) :
    projectiveCoeffHeight (hasseDerivative I (hasseDerivative J P)) ≤
      projectiveCoeffHeight P +
        2 * (∑ i, (d i : ℝ)) * Real.log 2 := by
  have houter := projectiveCoeffHeight_hasseDerivative_le
    (hdeg.hasseDerivative J) I
  have hinner := projectiveCoeffHeight_hasseDerivative_le hdeg J
  linarith

theorem support_natCard_le_degreeBox {ι : Type*} [Fintype ι]
    {P : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) :
    Nat.card P.support ≤ ∏ i, (d i + 1) := by
  classical
  let f : P.support → (i : ι) → Fin (d i + 1) := fun J i ↦
    ⟨J.1 i, Nat.lt_succ_of_le (hdeg J.1 J.2 i)⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact Fin.mk.inj (congrFun hAB i)
  calc
    Nat.card P.support ≤ Nat.card ((i : ι) → Fin (d i + 1)) :=
      Nat.card_le_card_of_injective f hf
    _ = ∏ i, (d i + 1) := by
      rw [Nat.card_eq_fintype_card]
      simp

private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

theorem degreeBox_le_two_pow_sum {ι : Type*} [Fintype ι]
    (d : ι → ℕ) :
    (∏ i, (d i + 1)) ≤ 2 ^ (∑ i, d i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ succ_le_two_pow (d i)

/-- Binary GLR product estimate in a direct rational specialization.  The
constant is the elementary support-box bound `2 * (sum d_i) * log 2`. -/
theorem projectiveCoeffHeight_mul_le_of_partialDegree {ι : Type*} [Fintype ι]
    {P Q : MvPolynomial ι ℚ} {d : ι → ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdegP : HasPartialDegreeAtMost P d)
    (hdegQ : HasPartialDegreeAtMost Q d) :
    projectiveCoeffHeight (P * Q) ≤
      projectiveCoeffHeight P + projectiveCoeffHeight Q +
        (2 * (∑ i, d i) : ℝ) * Real.log 2 := by
  let D : ℕ := ∑ i, d i
  have hcardP : Nat.card P.support ≤ 2 ^ D :=
    (support_natCard_le_degreeBox hdegP).trans (degreeBox_le_two_pow_sum d)
  have hcardQ : Nat.card Q.support ≤ 2 ^ D :=
    (support_natCard_le_degreeBox hdegQ).trans (degreeBox_le_two_pow_sum d)
  have hcard : Nat.card P.support * Nat.card Q.support ≤ 2 ^ (D + D) := by
    calc
      Nat.card P.support * Nat.card Q.support ≤ 2 ^ D * 2 ^ D :=
        Nat.mul_le_mul hcardP hcardQ
      _ = 2 ^ (D + D) := (pow_add 2 D D).symm
  have hPcard : 0 < Nat.card P.support := by
    obtain ⟨J, hJ⟩ := MvPolynomial.support_nonempty.mpr hP
    exact Nat.card_pos_iff.mpr ⟨⟨J, hJ⟩, inferInstance⟩
  have hQcard : 0 < Nat.card Q.support := by
    obtain ⟨J, hJ⟩ := MvPolynomial.support_nonempty.mpr hQ
    exact Nat.card_pos_iff.mpr ⟨⟨J, hJ⟩, inferInstance⟩
  have hreal :
      (Nat.card P.support * Nat.card Q.support : ℝ) ≤
        ((2 ^ (D + D) : ℕ) : ℝ) := by exact_mod_cast hcard
  have hlog :
      Real.log (Nat.card P.support * Nat.card Q.support) ≤
        (2 * D : ℝ) * Real.log 2 := by
    calc
      Real.log (Nat.card P.support * Nat.card Q.support) ≤
          Real.log (((2 ^ (D + D) : ℕ) : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · simpa only [Nat.cast_mul] using hreal
      _ = (2 * D : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        push_cast
        ring
  have hmul := projectiveCoeffHeight_mul_le_support hP hQ
  dsimp [D] at hlog ⊢
  linarith

/-! ## Shared-source determinant bound -/

open Erdos407.GeneralizedWronskian

/-- Turn a multi-index represented as a function on a finite type into a
finitely supported function. -/
def multiIndexFinsupp {n : ℕ} (u : MultiIndex n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm u

/-- The mixed Hasse index belonging to row `a` and column `b`: the column
order is placed in coordinate zero and the row multi-index in the remaining
coordinates. -/
def mixedHasseIndex {m k : ℕ} (μ : Fin k → MultiIndex m)
    (a b : Fin k) : Fin (m + 1) →₀ ℕ :=
  multiIndexFinsupp (Fin.cases b.1 (μ a))

/-- A support-indexed presentation of the Hasse derivative.  This version is
tailored to expanding a determinant as one linear map on a tensor power of
the original coefficient vector. -/
def supportHasseDerivative {ι : Type*} (I : ι →₀ ℕ)
    (P : MvPolynomial ι ℚ) : MvPolynomial ι ℚ := by
  classical
  exact ∑ J : P.support,
    MvPolynomial.monomial (J.1 - I)
      ((hasseMultiplier I J.1 : ℚ) * MvPolynomial.coeff J.1 P)

private theorem hasseMultiplier_eq_prod_univ {ι : Type*} [Fintype ι]
    (I J : ι →₀ ℕ) :
    hasseMultiplier I J = ∏ i, Nat.choose (J i) (I i) := by
  classical
  unfold hasseMultiplier
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hIi : I i = 0 := by
    simpa only [Finsupp.mem_support_iff, not_not] using hi
  simp [hIi]

private theorem hasseMultiplier_mul_sub {n : ℕ} (I J : Fin n →₀ ℕ)
    (i : Fin n) :
    hasseMultiplier I J * (J i - I i) =
      (I i + 1) * hasseMultiplier (I + Finsupp.single i 1) J := by
  classical
  rw [hasseMultiplier_eq_prod_univ, hasseMultiplier_eq_prod_univ]
  let f : Fin n → ℕ := fun x ↦ Nat.choose (J x) (I x)
  have hupdate :
      (fun x : Fin n ↦ Nat.choose (J x)
        ((I + Finsupp.single i 1 : Fin n →₀ ℕ) x)) =
        Function.update f i (Nat.choose (J i) (I i + 1)) := by
    funext x
    by_cases hxi : x = i
    · subst x
      simp [f]
    · simp [f, Finsupp.single_apply, hxi]
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  change
    (Nat.choose (J i) (I i) * ∏ x ∈ Finset.univ.erase i, f x) *
        (J i - I i) =
      (I i + 1) *
        (Nat.choose (J i) (I i + 1) * ∏ x ∈ Finset.univ.erase i, f x)
  have hc := Nat.choose_succ_right_eq (J i) (I i)
  calc
    (Nat.choose (J i) (I i) * ∏ x ∈ Finset.univ.erase i, f x) *
        (J i - I i) =
        (Nat.choose (J i) (I i) * (J i - I i)) *
          ∏ x ∈ Finset.univ.erase i, f x := by ring
    _ = (Nat.choose (J i) (I i + 1) * (I i + 1)) *
          ∏ x ∈ Finset.univ.erase i, f x := by rw [hc]
    _ = _ := by ring

private theorem supportHasseDerivative_add_single {n : ℕ}
    (I : Fin n →₀ ℕ) (i : Fin n) (P : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.pderiv i (supportHasseDerivative I P) =
      (I i + 1 : ℚ) •
        supportHasseDerivative (I + Finsupp.single i 1) P := by
  classical
  unfold supportHasseDerivative
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [MvPolynomial.pderiv_monomial]
  have hexp :
      J.1 - I - Finsupp.single i 1 =
        J.1 - (I + Finsupp.single i 1) := by
    ext x
    by_cases h : x = i
    · subst x
      simp
      omega
    · simp [Finsupp.single_apply, h]
  rw [hexp]
  have hmult := hasseMultiplier_mul_sub I J.1 i
  rw [MvPolynomial.smul_monomial]
  congr 1
  have hmultQ :
      (hasseMultiplier I J.1 : ℚ) * ((J.1 i - I i : ℕ) : ℚ) =
        (I i + 1 : ℚ) * hasseMultiplier (I + Finsupp.single i 1) J.1 := by
    have := congrArg (fun t : ℕ ↦ (t : ℚ)) hmult
    push_cast at this
    exact this
  rw [smul_eq_mul]
  change
    (hasseMultiplier I J.1 : ℚ) * MvPolynomial.coeff J.1 P *
        ((J.1 i - I i : ℕ) : ℚ) =
      (I i + 1 : ℚ) *
        ((hasseMultiplier (I + Finsupp.single i 1) J.1 : ℚ) *
          MvPolynomial.coeff J.1 P)
  rw [mul_assoc (hasseMultiplier I J.1 : ℚ), mul_comm
    (MvPolynomial.coeff J.1 P), ← mul_assoc, hmultQ]
  ring

@[simp] private theorem supportHasseDerivative_zero {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) :
    supportHasseDerivative (0 : Fin n →₀ ℕ) P = P := by
  classical
  apply MvPolynomial.ext
  intro K
  unfold supportHasseDerivative
  simp [hasseMultiplier]
  have hs :
      (∑ J ∈ P.support.attach,
        MvPolynomial.monomial J.1 (MvPolynomial.coeff J.1 P)) =
      ∑ J ∈ P.support,
        MvPolynomial.monomial J (MvPolynomial.coeff J P) :=
    Finset.sum_attach P.support
      (fun J ↦ MvPolynomial.monomial J (MvPolynomial.coeff J P))
  rw [hs, MvPolynomial.support_sum_monomial_coeff]

private theorem pderiv_comm_local {n : ℕ} (i j : Fin n)
    (Q : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j Q) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i Q) := by
  ext d
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_apply, hij, hji, add_comm, add_left_comm, mul_comm]
    ring

private theorem multiDerivative_update_succ_local {n : ℕ} (i : Fin n)
    (u : MultiIndex n) (Q : MvPolynomial (Fin n) ℚ) :
    multiDerivative (Function.update u i (u i + 1)) Q =
      MvPolynomial.pderiv i (multiDerivative u Q) := by
  have hcomm (j : Fin n) : Function.Commute (MvPolynomial.pderiv i)
      (MvPolynomial.pderiv j) := fun Q ↦ pderiv_comm_local i j Q
  have hfold_eq : ∀ (l : List (Fin n)), i ∉ l →
      ∀ Q : MvPolynomial (Fin n) ℚ,
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update u i (u i + 1)) j] R) Q =
          l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R) Q := by
    intro l hil
    induction l with
    | nil => intro Q; rfl
    | cons j l ih =>
        intro Q
        have hji : j ≠ i := by simpa using fun h ↦ hil (by simp [h])
        have hil' : i ∉ l := fun h ↦ hil (by simp [h])
        simp only [List.foldl_cons]
        rw [show Function.update u i (u i + 1) j = u j by simp [hji]]
        exact ih hil' _
  have hthrough : ∀ (l : List (Fin n)) (Q : MvPolynomial (Fin n) ℚ),
      MvPolynomial.pderiv i
          (l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R) Q) =
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R)
          (MvPolynomial.pderiv i Q) := by
    intro l
    induction l with
    | nil => intro Q; rfl
    | cons j l ih =>
        intro Q
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        exact (hcomm j).iterate_right (u j) Q
  have hlist : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      ∀ Q : MvPolynomial (Fin n) ℚ,
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update u i (u i + 1)) j] R) Q =
          l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R)
            (MvPolynomial.pderiv i Q) := by
    intro l hnodup hi
    induction l with
    | nil => simp at hi
    | cons j l ih =>
        intro Q
        simp only [List.foldl_cons]
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          rw [Function.iterate_succ_apply]
          exact hfold_eq l hnodup.notMem _
        · have hil : i ∈ l := by simpa [Ne.symm hji] using hi
          have hnodupl : l.Nodup := hnodup.tail
          rw [show Function.update u i (u i + 1) j = u j by simp [hji]]
          rw [ih hnodupl hil]
          congr 1
          exact (hcomm j).iterate_right (u j) Q
  unfold multiDerivative
  calc
    Finset.univ.toList.foldl
        (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update u i (u i + 1)) j] R) Q =
      Finset.univ.toList.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R)
        (MvPolynomial.pderiv i Q) :=
          hlist _ (Finset.nodup_toList _) (by simp) Q
    _ = MvPolynomial.pderiv i
        (Finset.univ.toList.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[u j] R) Q) :=
      (hthrough _ Q).symm

private theorem totalOrder_update_succ_local {n : ℕ} (i : Fin n)
    (u : MultiIndex n) :
    totalOrder (Function.update u i (u i + 1)) = totalOrder u + 1 := by
  rw [totalOrder, totalOrder, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.add_sum_erase Finset.univ u (Finset.mem_univ i)]
  omega

/-- Ordinary mixed differentiation is a nonzero scalar multiple of the
support-indexed Hasse derivative.  The scalar is the product of the relevant
factorials; only its nonvanishing is needed for projective height. -/
theorem exists_multiDerivative_eq_smul_supportHasse {n : ℕ}
    (u : MultiIndex n) (P : MvPolynomial (Fin n) ℚ) :
    ∃ c : ℚ, c ≠ 0 ∧
      multiDerivative u P = c • supportHasseDerivative (multiIndexFinsupp u) P := by
  generalize hN : totalOrder u = N
  induction N using Nat.strong_induction_on generalizing u with
  | h N ih =>
      by_cases huzero : u = fun _ ↦ 0
      · subst u
        refine ⟨1, one_ne_zero, ?_⟩
        have hz : multiIndexFinsupp (fun _ : Fin n ↦ 0) = 0 := by
          apply Finsupp.ext
          intro i
          change 0 = 0
          rfl
        rw [multiDerivative_zero_index, hz, supportHasseDerivative_zero,
          one_smul]
      · have hex : ∃ i : Fin n, 0 < u i := by
          by_contra h
          push Not at h
          apply huzero
          funext i
          exact Nat.eq_zero_of_le_zero (h i)
        obtain ⟨i, hi⟩ := hex
        let v : MultiIndex n := Function.update u i (u i - 1)
        have hvi : v i + 1 = u i := by
          simp [v, Nat.sub_add_cancel hi]
        have hupdate : Function.update v i (v i + 1) = u := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [hvi]
          · simp [v, hji]
        have horder : totalOrder v + 1 = N := by
          rw [← totalOrder_update_succ_local i v, hupdate, hN]
        have hlt : totalOrder v < N := by omega
        obtain ⟨c, hc, hv⟩ := ih (totalOrder v) hlt v rfl
        have hindex :
            multiIndexFinsupp (Function.update v i (v i + 1)) =
              multiIndexFinsupp v + Finsupp.single i 1 := by
          apply Finsupp.ext
          intro j
          change Function.update v i (v i + 1) j =
            v j + Finsupp.single i 1 j
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
        refine ⟨c * (v i + 1 : ℚ), mul_ne_zero hc (by positivity), ?_⟩
        calc
          multiDerivative u P =
              MvPolynomial.pderiv i (multiDerivative v P) := by
            rw [← hupdate, multiDerivative_update_succ_local]
          _ = MvPolynomial.pderiv i
              (c • supportHasseDerivative (multiIndexFinsupp v) P) := by
            rw [hv]
          _ = c • MvPolynomial.pderiv i
              (supportHasseDerivative (multiIndexFinsupp v) P) :=
            (MvPolynomial.pderiv i).map_smul c _
          _ = c • ((multiIndexFinsupp v i + 1 : ℚ) •
              supportHasseDerivative
                (multiIndexFinsupp v + Finsupp.single i 1) P) := by
            rw [supportHasseDerivative_add_single]
          _ = (c * (v i + 1 : ℚ)) •
              supportHasseDerivative
                (multiIndexFinsupp v + Finsupp.single i 1) P := by
            change c • ((v i + 1 : ℚ) • _) = _
            rw [smul_smul]
          _ = (c * (v i + 1 : ℚ)) •
              supportHasseDerivative (multiIndexFinsupp u) P := by
            rw [← hupdate, hindex]

/-- Product of the coordinate factorials of a multi-index. -/
def multiIndexFactorial {n : ℕ} (u : MultiIndex n) : ℕ :=
  ∏ i, (u i).factorial

private theorem multiIndexFactorial_update_succ {n : ℕ}
    (u : MultiIndex n) (i : Fin n) :
    multiIndexFactorial (Function.update u i (u i + 1)) =
      (u i + 1) * multiIndexFactorial u := by
  classical
  unfold multiIndexFactorial
  let f : Fin n → ℕ := fun j ↦ (u j).factorial
  have hupdate :
      (fun j : Fin n ↦ (Function.update u i (u i + 1) j).factorial) =
        Function.update f i (u i + 1).factorial := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [f]
    · simp [f, hji]
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, Nat.factorial_succ]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  dsimp [f]
  ring

/-- Exact ordinary/Hasse comparison. -/
theorem multiDerivative_eq_factorial_smul_supportHasse {n : ℕ}
    (u : MultiIndex n) (P : MvPolynomial (Fin n) ℚ) :
    multiDerivative u P =
      (multiIndexFactorial u : ℚ) •
        supportHasseDerivative (multiIndexFinsupp u) P := by
  generalize hN : totalOrder u = N
  induction N using Nat.strong_induction_on generalizing u with
  | h N ih =>
      by_cases huzero : u = fun _ ↦ 0
      · subst u
        have hz : multiIndexFinsupp (fun _ : Fin n ↦ 0) = 0 := by
          apply Finsupp.ext
          intro i
          change 0 = 0
          rfl
        rw [multiDerivative_zero_index, hz, supportHasseDerivative_zero]
        simp [multiIndexFactorial]
      · have hex : ∃ i : Fin n, 0 < u i := by
          by_contra h
          push Not at h
          apply huzero
          funext i
          exact Nat.eq_zero_of_le_zero (h i)
        obtain ⟨i, hi⟩ := hex
        let v : MultiIndex n := Function.update u i (u i - 1)
        have hvi : v i + 1 = u i := by
          simp [v, Nat.sub_add_cancel hi]
        have hupdate : Function.update v i (v i + 1) = u := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [hvi]
          · simp [v, hji]
        have horder : totalOrder v + 1 = N := by
          rw [← totalOrder_update_succ_local i v, hupdate, hN]
        have hlt : totalOrder v < N := by omega
        have hv := ih (totalOrder v) hlt v rfl
        have hindex :
            multiIndexFinsupp (Function.update v i (v i + 1)) =
              multiIndexFinsupp v + Finsupp.single i 1 := by
          apply Finsupp.ext
          intro j
          change Function.update v i (v i + 1) j =
            v j + Finsupp.single i 1 j
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
        have hfac : multiIndexFactorial u =
            (v i + 1) * multiIndexFactorial v := by
          rw [← hupdate, multiIndexFactorial_update_succ]
        calc
          multiDerivative u P =
              MvPolynomial.pderiv i (multiDerivative v P) := by
            rw [← hupdate, multiDerivative_update_succ_local]
          _ = MvPolynomial.pderiv i
              ((multiIndexFactorial v : ℚ) •
                supportHasseDerivative (multiIndexFinsupp v) P) := by
            rw [hv]
          _ = (multiIndexFactorial v : ℚ) •
              MvPolynomial.pderiv i
                (supportHasseDerivative (multiIndexFinsupp v) P) :=
            (MvPolynomial.pderiv i).map_smul _ _
          _ = (multiIndexFactorial v : ℚ) •
              ((v i + 1 : ℚ) • supportHasseDerivative
                (multiIndexFinsupp v + Finsupp.single i 1) P) := by
            change _ = _ • ((multiIndexFinsupp v i + 1 : ℚ) • _)
            rw [supportHasseDerivative_add_single]
          _ = (multiIndexFactorial u : ℚ) •
              supportHasseDerivative (multiIndexFinsupp u) P := by
            rw [smul_smul, hfac, ← hupdate, hindex]
            push_cast
            ring

private theorem multiDerivative_pderiv_local {n : ℕ} (u : MultiIndex n)
    (i : Fin n) (P : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.pderiv i (multiDerivative u P) =
      multiDerivative u (MvPolynomial.pderiv i P) := by
  have hcomm (j : Fin n) : Function.Commute (MvPolynomial.pderiv i)
      (MvPolynomial.pderiv j) := fun Q ↦ pderiv_comm_local i j Q
  unfold multiDerivative
  generalize (Finset.univ.toList : List (Fin n)) = l
  induction l generalizing P with
  | nil => rfl
  | cons j l ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      exact (hcomm j).iterate_right (u j) P

private theorem mixedDerivative_eq_fullMultiDerivative {m k : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℚ) (μ : Fin k → MultiIndex m)
    (a b : Fin k) :
    multiDerivative (liftMultiIndex (μ a))
        ((MvPolynomial.pderiv 0)^[b.1] P) =
      multiDerivative (Fin.cases b.1 (μ a)) P := by
  induction b.1 with
  | zero => rfl
  | succ q ih =>
      let wq : MultiIndex (m + 1) := Fin.cases q (μ a)
      have hfun : (Fin.cases (q + 1) (μ a) : MultiIndex (m + 1)) =
          Function.update wq 0 (wq 0 + 1) := by
        funext j
        refine Fin.cases ?_ (fun t ↦ ?_) j
        · simp [wq]
        · simp [wq, Function.update_of_ne (Fin.succ_ne_zero t).symm]
      calc
        multiDerivative (liftMultiIndex (μ a))
            ((MvPolynomial.pderiv 0)^[q + 1] P) =
            multiDerivative (liftMultiIndex (μ a))
              (MvPolynomial.pderiv 0 ((MvPolynomial.pderiv 0)^[q] P)) := by
                rw [Function.iterate_succ_apply']
        _ = MvPolynomial.pderiv 0
            (multiDerivative (liftMultiIndex (μ a))
              ((MvPolynomial.pderiv 0)^[q] P)) :=
              (multiDerivative_pderiv_local _ _ _).symm
        _ = MvPolynomial.pderiv 0
            (multiDerivative (Fin.cases q (μ a)) P) := by rw [ih]
        _ = multiDerivative (Fin.cases (q + 1) (μ a)) P := by
          rw [hfun]
          change MvPolynomial.pderiv 0 (multiDerivative wq P) = _
          rw [multiDerivative_update_succ_local]

private theorem multiIndexFactorial_finCases {m : ℕ} (q : ℕ)
    (u : MultiIndex m) :
    multiIndexFactorial (Fin.cases q u) =
      q.factorial * multiIndexFactorial u := by
  unfold multiIndexFactorial
  rw [Fin.prod_univ_succ]
  rfl

private theorem prod_monomial {α ι : Type*} [Fintype α]
    (e : α → ι →₀ ℕ) (c : α → ℚ) :
    (∏ i, MvPolynomial.monomial (e i) (c i)) =
      MvPolynomial.monomial (∑ i, e i) (∏ i, c i) := by
  classical
  have h (s : Finset α) :
      (∏ i ∈ s, MvPolynomial.monomial (e i) (c i)) =
        MvPolynomial.monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          Finset.prod_insert ha, ih, MvPolynomial.monomial_mul]
  simpa using h Finset.univ

/-- The matrix of Hasse derivatives that differs from the ordinary mixed
derivative matrix only by row and column factorials. -/
def mixedSupportHasseMatrix {m k : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℚ) (μ : Fin k → MultiIndex m) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin (m + 1)) ℚ) :=
  fun a b ↦ supportHasseDerivative (mixedHasseIndex μ a b) P

/-- Every entry of the ordinary mixed-derivative matrix is the corresponding
Hasse entry scaled by a product of a row factor and a column factor. -/
theorem mixedDerivativeMatrix_entry_eq_smul {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ}
    (S : SeparationData m P) (μ : Fin S.k → MultiIndex m)
    (a b : Fin S.k) :
    mixedDerivativeMatrix S μ a b =
      ((multiIndexFactorial (μ a) : ℚ) * (b.1.factorial : ℚ)) •
        mixedSupportHasseMatrix P μ a b := by
  rw [mixedDerivativeMatrix, mixedSupportHasseMatrix,
    mixedDerivative_eq_fullMultiDerivative]
  rw [multiDerivative_eq_factorial_smul_supportHasse,
    multiIndexFactorial_finCases]
  congr 1
  · push_cast
    ring

/-- The determinant of the ordinary mixed-derivative matrix is the Hasse
determinant scaled by the products of its row and column factorials. -/
theorem mixedDerivativeMatrix_det_eq_smul {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ}
    (S : SeparationData m P) (μ : Fin S.k → MultiIndex m) :
    (mixedDerivativeMatrix S μ).det =
      ((∏ a, (multiIndexFactorial (μ a) : ℚ)) *
        ∏ b : Fin S.k, (b.1.factorial : ℚ)) •
          (mixedSupportHasseMatrix P μ).det := by
  classical
  let H := mixedSupportHasseMatrix P μ
  let row : Fin S.k → MvPolynomial (Fin (m + 1)) ℚ :=
    fun a ↦ MvPolynomial.C (multiIndexFactorial (μ a) : ℚ)
  let col : Fin S.k → MvPolynomial (Fin (m + 1)) ℚ :=
    fun b ↦ MvPolynomial.C (b.1.factorial : ℚ)
  have hmatrix : mixedDerivativeMatrix S μ =
      Matrix.of (fun a b ↦ col b * (row a * H a b)) := by
    funext a b
    change mixedDerivativeMatrix S μ a b = col b * (row a * H a b)
    rw [mixedDerivativeMatrix_entry_eq_smul]
    simp only [row, col, H, MvPolynomial.smul_eq_C_mul]
    rw [map_mul]
    ring
  calc
    (mixedDerivativeMatrix S μ).det =
        (Matrix.of (fun a b ↦ col b * (row a * H a b))).det :=
      congrArg Matrix.det hmatrix
    _ = (∏ b, col b) *
        (Matrix.of (fun a b ↦ row a * H a b)).det :=
      Matrix.det_mul_row col _
    _ = (∏ b, col b) * ((∏ a, row a) * H.det) := by
      rw [Matrix.det_mul_column row H]
    _ = ((∏ a, (multiIndexFactorial (μ a) : ℚ)) *
        ∏ b : Fin S.k, (b.1.factorial : ℚ)) •
          (mixedSupportHasseMatrix P μ).det := by
      simp only [row, col, H, map_prod, map_mul,
        MvPolynomial.smul_eq_C_mul]
      ring

/-- Ordinary and Hasse mixed-derivative determinants have the same
projective coefficient height. -/
theorem projectiveCoeffHeight_mixedDerivativeMatrix_det_eq {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ}
    (S : SeparationData m P) (μ : Fin S.k → MultiIndex m) :
    projectiveCoeffHeight (mixedDerivativeMatrix S μ).det =
      projectiveCoeffHeight (mixedSupportHasseMatrix P μ).det := by
  rw [mixedDerivativeMatrix_det_eq_smul]
  apply projectiveCoeffHeight_smul
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro a _
    have hfac : 0 < multiIndexFactorial (μ a) := by
      unfold multiIndexFactorial
      apply Finset.prod_pos
      intro i _
      exact Nat.factorial_pos (μ a i)
    exact_mod_cast hfac.ne'
  · apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact_mod_cast Nat.factorial_ne_zero b.1

/-- The generalized-Wronskian determinant inherits the componentwise degree
box `k * d` from its source polynomial. -/
theorem HasPartialDegreeAtMost.mixedDerivativeMatrix_det {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} {d : Fin (m + 1) → ℕ}
    (S : SeparationData m P) (hdeg : HasPartialDegreeAtMost P d)
    (μ : Fin S.k → MultiIndex m) :
    HasPartialDegreeAtMost (mixedDerivativeMatrix S μ).det
      (fun i ↦ S.k * d i) := by
  have hpderiv (i : Fin (m + 1))
      {Q : MvPolynomial (Fin (m + 1)) ℚ}
      (hQ : HasPartialDegreeAtMost Q d) :
      HasPartialDegreeAtMost (MvPolynomial.pderiv i Q) d := by
    rw [← hasseDerivative_single_one]
    exact hQ.hasseDerivative (Finsupp.single i 1)
  have hiter (i : Fin (m + 1)) (q : ℕ)
      {Q : MvPolynomial (Fin (m + 1)) ℚ}
      (hQ : HasPartialDegreeAtMost Q d) :
      HasPartialDegreeAtMost ((MvPolynomial.pderiv i)^[q] Q) d := by
    induction q with
    | zero => simpa
    | succ q ih =>
        rw [Function.iterate_succ_apply']
        exact hpderiv i ih
  have hmulti (u : MultiIndex (m + 1))
      {Q : MvPolynomial (Fin (m + 1)) ℚ}
      (hQ : HasPartialDegreeAtMost Q d) :
      HasPartialDegreeAtMost (multiDerivative u Q) d := by
    unfold multiDerivative
    generalize (Finset.univ.toList : List (Fin (m + 1))) = l
    induction l generalizing Q with
    | nil => simpa
    | cons i l ih =>
        simp only [List.foldl_cons]
        exact ih (hiter i (u i) hQ)
  have hentry (a b : Fin S.k) :
      HasPartialDegreeAtMost (mixedDerivativeMatrix S μ a b) d := by
    unfold mixedDerivativeMatrix
    exact hmulti _ (hiter 0 b.1 hdeg)
  simpa only [Nat.card_fin] using
    HasPartialDegreeAtMost.det (mixedDerivativeMatrix S μ) d hentry

/-- The degree-`k` tensor of the coefficient vector of `P`. -/
def coefficientPower {ι : Type*} (P : MvPolynomial ι ℚ) (k : ℕ) :
    (Fin k → P.support) → ℚ :=
  fun u ↦ ∏ i, MvPolynomial.coeff (u i).1 P

theorem logHeight_coefficientPower {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (k : ℕ) :
    Height.logHeight (coefficientPower P k) =
      (k : ℝ) * projectiveCoeffHeight P := by
  have hx : ∀ _ : Fin k, coeffTuple P ≠ 0 := fun _ ↦ coeffTuple_ne_zero hP
  have h := Height.logHeight_fun_prod_eq hx
  change Height.logHeight (coefficientPower P k) = _ at h
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple]
  simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using h

/-- The integer matrix expressing every coefficient of the Hasse
determinant as a linear combination of degree-`k` coefficient tensors. -/
def mixedHasseDeterminantMatrix {m k : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℚ) (μ : Fin k → MultiIndex m) :
    ((Fin (m + 1) →₀ ℕ) × (Fin k → P.support)) → ℤ := by
  classical
  exact fun z ↦ ∑ σ : Equiv.Perm (Fin k),
    if (∑ b, ((z.2 b).1 - mixedHasseIndex μ (σ b) b)) = z.1 then
      (Equiv.Perm.sign σ : ℤ) *
        ∏ b, hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1
    else 0

private theorem coeff_mixedSupportHasseMatrix_det {m k : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℚ) (μ : Fin k → MultiIndex m)
    (J : Fin (m + 1) →₀ ℕ) :
    MvPolynomial.coeff J (mixedSupportHasseMatrix P μ).det =
      ∑ u : Fin k → P.support,
        (mixedHasseDeterminantMatrix P μ (J, u) : ℚ) * coefficientPower P k u := by
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  simp_rw [mixedSupportHasseMatrix, supportHasseDerivative]
  simp_rw [← Finset.sum_prod_piFinset (Finset.univ : Finset P.support)]
  simp only [Fintype.piFinset_univ, prod_monomial]
  simp_rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  simp_rw [Finset.smul_sum]
  change (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))),
      ∑ u ∈ (Finset.univ : Finset (Fin k → P.support)), _) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  unfold mixedHasseDeterminantMatrix coefficientPower
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with h
  · rw [Finset.prod_mul_distrib]
    simp only [Units.smul_def]
    push_cast
    ring
  · simp

private theorem mixedHasseDeterminantMatrix_natAbs_le {m k : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} {d : Fin (m + 1) → ℕ}
    (hdeg : HasPartialDegreeAtMost P d) (μ : Fin k → MultiIndex m)
    (z : (Fin (m + 1) →₀ ℕ) × (Fin k → P.support)) :
    (mixedHasseDeterminantMatrix P μ z).natAbs ≤
      Nat.factorial k * 2 ^ (k * ∑ i, d i) := by
  classical
  let D := ∑ i, d i
  have hmult (σ : Equiv.Perm (Fin k)) (b : Fin k) :
      hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1 ≤ 2 ^ D := by
    apply hasseMultiplier_le_two_pow_sum
    intro i
    exact hdeg (z.2 b).1 (z.2 b).2 i
  have hprod (σ : Equiv.Perm (Fin k)) :
      (∏ b, hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1) ≤
        2 ^ (k * D) := by
    calc
      (∏ b, hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1) ≤
          ∏ _b : Fin k, 2 ^ D := by
        exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun b _ ↦ hmult σ b)
      _ = (2 ^ D) ^ k := by simp
      _ = 2 ^ (k * D) := by rw [← pow_mul, Nat.mul_comm D k]
  unfold mixedHasseDeterminantMatrix
  calc
    (∑ σ : Equiv.Perm (Fin k),
        if (∑ b, ((z.2 b).1 - mixedHasseIndex μ (σ b) b)) = z.1 then
          (Equiv.Perm.sign σ : ℤ) *
            ∏ b, hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1
        else 0).natAbs ≤
        ∑ σ : Equiv.Perm (Fin k),
          (if (∑ b, ((z.2 b).1 - mixedHasseIndex μ (σ b) b)) = z.1 then
            (Equiv.Perm.sign σ : ℤ) *
              ∏ b, hasseMultiplier (mixedHasseIndex μ (σ b) b) (z.2 b).1
          else 0).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), 2 ^ (k * D) := by
      apply Finset.sum_le_sum
      intro σ _
      split_ifs
      · rw [Int.natAbs_mul, Int.natAbs_natCast]
        have hsign : ((Equiv.Perm.sign σ : ℤ)).natAbs = 1 :=
          Int.natAbs_of_isUnit (Units.isUnit _)
        rw [hsign, one_mul]
        exact hprod σ
      · simp
    _ = Nat.factorial k * 2 ^ (k * D) := by
      simp [Fintype.card_perm]
    _ = Nat.factorial k * 2 ^ (k * ∑ i, d i) := by rfl

/-- The numeric shared-source bound for a determinant of mixed Hasse
derivatives.  The first copy of `k * sum d` bounds the integral Hasse
multipliers; the second bounds the tensor support. -/
theorem projectiveCoeffHeight_mixedSupportHasseMatrix_det_le {m k : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} {d : Fin (m + 1) → ℕ}
    (hP : P ≠ 0) (hdeg : HasPartialDegreeAtMost P d)
    (μ : Fin k → MultiIndex m) :
    projectiveCoeffHeight (mixedSupportHasseMatrix P μ).det ≤
      Real.log (Nat.factorial k) + k * projectiveCoeffHeight P +
        (2 * k * (∑ i, d i) : ℝ) * Real.log 2 := by
  classical
  let D : ℕ := ∑ i, d i
  let V := (mixedSupportHasseMatrix P μ).det
  let A : V.support × (Fin k → P.support) → ℚ := fun z ↦
    (mixedHasseDeterminantMatrix P μ (z.1.1, z.2) : ℚ)
  have hA : Height.logHeight A ≤
      Real.log (Nat.factorial k * 2 ^ (k * D)) := by
    have h := logHeight_intCast_le_log
      (fun z : V.support × (Fin k → P.support) ↦
        mixedHasseDeterminantMatrix P μ (z.1.1, z.2))
      (Nat.factorial k * 2 ^ (k * D)) (by positivity) (by
        intro z
        exact mixedHasseDeterminantMatrix_natAbs_le hdeg μ (z.1.1, z.2))
    simpa only [A, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hlin := Height.logHeight_linearMap_apply_le A (coefficientPower P k)
  have heq :
      (fun J : V.support ↦ ∑ u, A (J, u) * coefficientPower P k u) =
        coeffTuple V := by
    funext J
    exact (coeff_mixedSupportHasseMatrix_det P μ J.1).symm
  rw [heq, logHeight_coefficientPower hP k] at hlin
  norm_num [NumberField.totalWeight_eq_finrank] at hlin
  let eP : P.support ≃ {J // MvPolynomial.coeff J P ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ ↦ MvPolynomial.mem_support_iff)
  let ePow : (Fin k → P.support) ≃
      (Fin k → {J // MvPolynomial.coeff J P ≠ 0}) :=
    Equiv.piCongrRight (fun _ ↦ eP)
  have hcardEq : Nat.card (Fin k → P.support) =
      Nat.card (Fin k → {J // MvPolynomial.coeff J P ≠ 0}) :=
    Nat.card_congr ePow
  rw [← hcardEq] at hlin
  have hsupport : Nat.card P.support ≤ 2 ^ D := by
    exact (support_natCard_le_degreeBox hdeg).trans
      (degreeBox_le_two_pow_sum d)
  have hcard : Nat.card (Fin k → P.support) ≤ 2 ^ (k * D) := by
    rw [Nat.card_fun, Nat.card_fin]
    calc
      Nat.card P.support ^ k ≤ (2 ^ D) ^ k :=
        Nat.pow_le_pow_left hsupport k
      _ = 2 ^ (k * D) := by rw [← pow_mul, Nat.mul_comm D k]
  have hcardpos : 0 < Nat.card (Fin k → P.support) := by
    obtain ⟨J, hJ⟩ := MvPolynomial.support_nonempty.mpr hP
    let j₀ : P.support := ⟨J, hJ⟩
    apply Nat.card_pos_iff.mpr
    exact ⟨⟨fun _ ↦ j₀⟩, inferInstance⟩
  have hlogcard : Real.log (Nat.card (Fin k → P.support)) ≤
      (k * D : ℝ) * Real.log 2 := by
    calc
      Real.log (Nat.card (Fin k → P.support)) ≤
          Real.log ((2 ^ (k * D) : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hcardpos
        · exact_mod_cast hcard
      _ = (k * D : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        push_cast
        ring
  have hlogA : Real.log (Nat.factorial k * 2 ^ (k * D)) =
      Real.log (Nat.factorial k) + (k * D : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlogA] at hA
  change projectiveCoeffHeight V ≤ _
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple]
  dsimp [D] at hA hlin hlogcard ⊢
  linarith

/-- The shared-source numeric height bound for the determinant of the ordinary
mixed-derivative matrix used by the generalized Wronskian construction. -/
theorem projectiveCoeffHeight_mixedDerivativeMatrix_det_le {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} {d : Fin (m + 1) → ℕ}
    (S : SeparationData m P) (hP : P ≠ 0)
    (hdeg : HasPartialDegreeAtMost P d)
    (μ : Fin S.k → MultiIndex m) :
    projectiveCoeffHeight (mixedDerivativeMatrix S μ).det ≤
      Real.log (Nat.factorial S.k) + S.k * projectiveCoeffHeight P +
        (2 * S.k * (∑ i, d i) : ℝ) * Real.log 2 := by
  rw [projectiveCoeffHeight_mixedDerivativeMatrix_det_eq]
  exact projectiveCoeffHeight_mixedSupportHasseMatrix_det_le hP hdeg μ

end
end Erdos407.PolynomialHeights
