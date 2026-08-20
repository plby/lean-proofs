/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RothIndex
import ErdosProblems.Erdos407.GeneralizedWronskian
import ErdosProblems.Erdos407.PolynomialHeights
import ErdosProblems.Erdos407.MahlerHeightBridge

/-!
# The quantitative binary Roth lemma over `ℚ`

This file uses scalar variables for the dehomogenized form of GLR Lemma 3.9.
The definitions in `RothIndex` use one block of variables for each point.  The
first section records the (definitionally harmless) bridge between these two
presentations.
-/

namespace Erdos407.BinaryRoth

open scoped BigOperators

noncomputable section

/-! ## The affine presentation of Roth's index -/

/-- A scalar multi-index, one entry for each affine variable. -/
abbrev AffineMultiIndex (m : ℕ) := Fin m →₀ ℕ

/-- The normalized weight of a scalar multi-index. -/
def affineWeight {m : ℕ} (r : Fin m → ℕ) (J : AffineMultiIndex m) : ℚ :=
  ∑ j : Fin m, (J j : ℚ) / (r j : ℚ)

/-- The finite set of normalized weights occurring after translating by
`β`. -/
def affineIndexWeights {m : ℕ} (P : MvPolynomial (Fin m) ℚ)
    (r : Fin m → ℕ) (β : Fin m → ℚ) : Finset ℚ :=
  (RothIndex.translate β P).support.image (affineWeight r)

/-- Roth's normalized index in dehomogenized scalar variables. -/
def affineIndex {m : ℕ} (P : MvPolynomial (Fin m) ℚ)
    (r : Fin m → ℕ) (β : Fin m → ℚ) : ℚ :=
  if h : (affineIndexWeights P r β).Nonempty then
    (affineIndexWeights P r β).min' h
  else 0

/-- A nonzero translated coefficient realizing the affine index. -/
theorem exists_hasseCoeff_weight_eq_affineIndex {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) :
    ∃ J : AffineMultiIndex m,
      RothIndex.hasseCoeff P β J ≠ 0 ∧ affineWeight r J = affineIndex P r β := by
  have hsupp : (RothIndex.translate β P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (RothIndex.translate_ne_zero hP)
  have hw : (affineIndexWeights P r β).Nonempty := hsupp.image _
  have hmin : (affineIndexWeights P r β).min' hw ∈
      affineIndexWeights P r β := Finset.min'_mem _ _
  obtain ⟨J, hJ, hJweight⟩ := Finset.mem_image.mp hmin
  refine ⟨J, MvPolynomial.mem_support_iff.mp hJ, ?_⟩
  rw [affineIndex, dif_pos hw]
  exact hJweight

/-- The affine index is no larger than the weight of any nonzero translated
coefficient. -/
theorem affineIndex_le_weight {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) (J : AffineMultiIndex m)
    (hJ : RothIndex.hasseCoeff P β J ≠ 0) :
    affineIndex P r β ≤ affineWeight r J := by
  have hsupp : (RothIndex.translate β P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (RothIndex.translate_ne_zero hP)
  have hw : (affineIndexWeights P r β).Nonempty := hsupp.image _
  rw [affineIndex, dif_pos hw]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨J, MvPolynomial.mem_support_iff.mpr hJ, rfl⟩

/-- Every normalized weight is nonnegative when all normalizing degrees are
positive. -/
theorem affineWeight_nonneg {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ j, 0 < r j) (J : AffineMultiIndex m) :
    0 ≤ affineWeight r J := by
  unfold affineWeight
  exact Finset.sum_nonneg fun j _ ↦ div_nonneg (by positivity) (by positivity)

/-- A nonzero polynomial has nonnegative affine index. -/
theorem affineIndex_nonneg {m : ℕ} {P : MvPolynomial (Fin m) ℚ}
    (hP : P ≠ 0) {r : Fin m → ℕ} (hr : ∀ j, 0 < r j)
    (β : Fin m → ℚ) : 0 ≤ affineIndex P r β := by
  obtain ⟨J, -, hJ⟩ := exists_hasseCoeff_weight_eq_affineIndex hP r β
  rw [← hJ]
  exact affineWeight_nonneg hr J

/-! ## Elementary index calculus -/

@[simp] theorem translate_zero_poly {m : ℕ} (β : Fin m → ℚ) :
    RothIndex.translate β (0 : MvPolynomial (Fin m) ℚ) = 0 := by
  simpa using RothIndex.translate_C β (0 : ℚ)

@[simp] theorem translate_one_poly {m : ℕ} (β : Fin m → ℚ) :
    RothIndex.translate β (1 : MvPolynomial (Fin m) ℚ) = 1 := by
  simpa using RothIndex.translate_C β (1 : ℚ)

/-- Translating the origin commutes with an ordinary partial derivative. -/
theorem translate_pderiv {m : ℕ} (β : Fin m → ℚ) (i : Fin m)
    (P : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate β (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv i (RothIndex.translate β P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      rw [map_add, RothIndex.translate_add, RothIndex.translate_add,
        map_add, hP, hQ]
  | mul_X P j hP =>
      rw [MvPolynomial.pderiv_mul, RothIndex.translate_add,
        RothIndex.translate_mul, RothIndex.translate_mul,
        RothIndex.translate_mul, MvPolynomial.pderiv_mul,
        RothIndex.translate_X, hP]
      simp [RothIndex.translate_X, Pi.single_apply]
      split_ifs <;> simp

theorem affineWeight_add_single {m : ℕ} (r : Fin m → ℕ)
    (J : AffineMultiIndex m) (i : Fin m) :
    affineWeight r (J + Finsupp.single i 1) =
      affineWeight r J + 1 / (r i : ℚ) := by
  classical
  unfold affineWeight
  calc
    ∑ j, ((((J + Finsupp.single i 1 : AffineMultiIndex m)) j : ℕ) : ℚ) /
        (r j : ℚ) =
        ∑ j, ((J j : ℚ) / (r j : ℚ) +
          (((Finsupp.single i 1) j : ℕ) : ℚ) / (r j : ℚ)) := by
            apply Finset.sum_congr rfl
            intro j _
            change (((J j + (Finsupp.single i 1) j : ℕ) : ℚ) /
              (r j : ℚ)) = _
            rw [Nat.cast_add, add_div]
    _ = (∑ j, (J j : ℚ) / (r j : ℚ)) +
        ∑ j, (((Finsupp.single i 1) j : ℕ) : ℚ) / (r j : ℚ) :=
      Finset.sum_add_distrib
    _ = (∑ j, (J j : ℚ) / (r j : ℚ)) + 1 / (r i : ℚ) := by
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp

theorem affineWeight_add {m : ℕ} (r : Fin m → ℕ)
    (J K : AffineMultiIndex m) :
    affineWeight r (J + K) = affineWeight r J + affineWeight r K := by
  unfold affineWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change ((((J + K : AffineMultiIndex m)) j : ℕ) : ℚ) / (r j : ℚ) = _
  rw [Finsupp.add_apply, Nat.cast_add, add_div]

/-- The index of a nonzero sum is at least the smaller index of its two
nonzero summands. -/
theorem min_affineIndex_le_add {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPQ : P + Q ≠ 0) (r : Fin m → ℕ) (β : Fin m → ℚ) :
    min (affineIndex P r β) (affineIndex Q r β) ≤
      affineIndex (P + Q) r β := by
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hPQ r β
  rw [RothIndex.hasseCoeff, RothIndex.translate_add,
    MvPolynomial.coeff_add] at hJ
  have hcases :
      MvPolynomial.coeff J (RothIndex.translate β P) ≠ 0 ∨
        MvPolynomial.coeff J (RothIndex.translate β Q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hJ (by rw [h.1, h.2, add_zero])
  rw [← hweight]
  rcases hcases with hJP | hJQ
  · exact (min_le_left _ _).trans
      (affineIndex_le_weight hP r β J hJP)
  · exact (min_le_right _ _).trans
      (affineIndex_le_weight hQ r β J hJQ)

/-- The index is superadditive under multiplication.  Equality will only be
needed below for factors in disjoint sets of variables. -/
theorem affineIndex_add_le_mul {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) :
    affineIndex P r β + affineIndex Q r β ≤
      affineIndex (P * Q) r β := by
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hPQ r β
  have hJsupp : J ∈
      (RothIndex.translate β P * RothIndex.translate β Q).support := by
    rw [← RothIndex.translate_mul]
    exact MvPolynomial.mem_support_iff.mpr hJ
  have hsum := MvPolynomial.support_mul
    (RothIndex.translate β P) (RothIndex.translate β Q) hJsupp
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.mem_add.mp hsum
  have hAcoeff : RothIndex.hasseCoeff P β A ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hA
  have hBcoeff : RothIndex.hasseCoeff Q β B ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hB
  calc
    affineIndex P r β + affineIndex Q r β ≤
        affineWeight r A + affineWeight r B :=
      add_le_add (affineIndex_le_weight hP r β A hAcoeff)
        (affineIndex_le_weight hQ r β B hBcoeff)
    _ = affineWeight r (A + B) := (affineWeight_add r A B).symm
    _ = affineWeight r J := by rw [hAB]
    _ = affineIndex (P * Q) r β := hweight

@[simp] theorem affineIndex_one {m : ℕ} (r : Fin m → ℕ)
    (β : Fin m → ℚ) :
    affineIndex (1 : MvPolynomial (Fin m) ℚ) r β = 0 := by
  classical
  unfold affineIndex affineIndexWeights
  simp [affineWeight]

theorem translate_smul {m : ℕ} (a : ℚ) (β : Fin m → ℚ)
    (P : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate β (a • P) = a • RothIndex.translate β P := by
  simpa [← MvPolynomial.C_mul'] using
    RothIndex.translate_mul β (MvPolynomial.C a) P

/-- Multiplication by a nonzero scalar does not change the index. -/
theorem affineIndex_smul {m : ℕ} {a : ℚ} (ha : a ≠ 0)
    (P : MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ) (β : Fin m → ℚ) :
    affineIndex (a • P) r β = affineIndex P r β := by
  have hweights : affineIndexWeights (a • P) r β =
      affineIndexWeights P r β := by
    unfold affineIndexWeights
    rw [translate_smul, MvPolynomial.support_smul_eq ha]
  unfold affineIndex
  rw [hweights]

/-- A uniform lower bound for the indices of the nonzero summands is also a
lower bound for the index of a nonzero finite sum. -/
theorem le_affineIndex_finsetSum {m : ℕ} {I : Type*}
    (s : Finset I) (F : I → MvPolynomial (Fin m) ℚ)
    (r : Fin m → ℕ) (β : Fin m → ℚ) (B : ℚ)
    (hsum : ∑ i ∈ s, F i ≠ 0)
    (hF : ∀ i ∈ s, F i ≠ 0 → B ≤ affineIndex (F i) r β) :
    B ≤ affineIndex (∑ i ∈ s, F i) r β := by
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hsum r β
  have hex : ∃ i ∈ s,
      MvPolynomial.coeff J (RothIndex.translate β (F i)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hJ
    rw [RothIndex.hasseCoeff]
    simp only [RothIndex.translate, map_sum, MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero fun i hi ↦ h i hi
  obtain ⟨i, hi, hJi⟩ := hex
  have hFi : F i ≠ 0 := by
    intro hz
    rw [hz, translate_zero_poly, MvPolynomial.coeff_zero] at hJi
    exact hJi rfl
  calc
    B ≤ affineIndex (F i) r β := hF i hi hFi
    _ ≤ affineWeight r J := affineIndex_le_weight hFi r β J hJi
    _ = affineIndex (∑ i ∈ s, F i) r β := hweight

/-- Finite products inherit superadditivity of the affine index. -/
theorem finsetSum_affineIndex_le_prod {m : ℕ} {I : Type*}
    (s : Finset I) (F : I → MvPolynomial (Fin m) ℚ)
    (hF : ∀ i ∈ s, F i ≠ 0) (r : Fin m → ℕ) (β : Fin m → ℚ) :
    ∑ i ∈ s, affineIndex (F i) r β ≤
      affineIndex (∏ i ∈ s, F i) r β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have ih' : ∑ j ∈ s, affineIndex (F j) r β ≤
          affineIndex (∏ j ∈ s, F j) r β :=
        ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))
      have hprod : ∏ j ∈ s, F j ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j hj ↦
          hF j (Finset.mem_insert_of_mem hj)
      have hmul : affineIndex (F i) r β +
          affineIndex (∏ j ∈ s, F j) r β ≤
          affineIndex (F i * ∏ j ∈ s, F j) r β :=
        affineIndex_add_le_mul
          (hF i (Finset.mem_insert_self i s)) hprod r β
      linarith

/-- Determinant form of the index inequality.  A column-dependent lower
bound for every nonzero matrix entry adds over the columns. -/
theorem sum_le_affineIndex_det {m k : ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ))
    (hdet : A.det ≠ 0) (r : Fin m → ℕ) (β : Fin m → ℚ)
    (B : Fin k → ℚ)
    (hA : ∀ i j, A i j ≠ 0 → B j ≤ affineIndex (A i j) r β) :
    ∑ j, B j ≤ affineIndex A.det r β := by
  classical
  let c : Equiv.Perm (Fin k) → ℚ := fun σ ↦
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ)
  let F : Equiv.Perm (Fin k) → MvPolynomial (Fin m) ℚ := fun σ ↦
    c σ • ∏ i, A (σ i) i
  have hc (σ : Equiv.Perm (Fin k)) : c σ ≠ 0 := by
    unfold c
    exact_mod_cast Units.ne_zero (Equiv.Perm.sign σ)
  have hdet_sum : A.det = ∑ σ, F σ := by
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _
    unfold F c
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h]
  have hsum : ∑ σ, F σ ≠ 0 := by
    rw [← hdet_sum]
    exact hdet
  rw [hdet_sum]
  apply le_affineIndex_finsetSum Finset.univ F r β (∑ j, B j) hsum
  intro σ _ hFσ
  have hprod : ∏ i, A (σ i) i ≠ 0 := by
    intro hp
    apply hFσ
    simp [F, hp]
  have hentry (i : Fin k) : A (σ i) i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  calc
    ∑ j, B j ≤ ∑ j, affineIndex (A (σ j) j) r β := by
      exact Finset.sum_le_sum fun j _ ↦ hA (σ j) j (hentry j)
    _ ≤ affineIndex (∏ j, A (σ j) j) r β := by
      simpa using finsetSum_affineIndex_le_prod Finset.univ
        (fun j ↦ A (σ j) j) (fun j _ ↦ hentry j) r β
    _ = affineIndex (F σ) r β := by
      exact (affineIndex_smul (hc σ) (∏ j, A (σ j) j) r β).symm

/-- Applying one partial derivative can lower the normalized index by at
most the reciprocal degree of that variable. -/
theorem affineIndex_sub_reciprocal_le_pderiv {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) (i : Fin m)
    (hD : MvPolynomial.pderiv i P ≠ 0) :
    affineIndex P r β - 1 / (r i : ℚ) ≤
      affineIndex (MvPolynomial.pderiv i P) r β := by
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hD r β
  have hcoeff : RothIndex.hasseCoeff P β
      (J + Finsupp.single i 1) ≠ 0 := by
    rw [RothIndex.hasseCoeff, translate_pderiv,
      MvPolynomial.coeff_pderiv] at hJ
    exact left_ne_zero_of_mul hJ
  have hle := affineIndex_le_weight hP r β
    (J + Finsupp.single i 1) hcoeff
  rw [affineWeight_add_single] at hle
  rw [← hweight]
  linarith

/-- Repeating a partial derivative `n` times loses at most `n / rᵢ` from
the normalized affine index. -/
theorem affineIndex_sub_iterateLoss_le {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) (i : Fin m) (n : ℕ)
    (hD : (MvPolynomial.pderiv i)^[n] P ≠ 0) :
    affineIndex P r β - (n : ℚ) / (r i : ℚ) ≤
      affineIndex ((MvPolynomial.pderiv i)^[n] P) r β := by
  induction n with
  | zero => simpa using le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at hD ⊢
      have hprev : (MvPolynomial.pderiv i)^[n] P ≠ 0 := by
        intro hz
        apply hD
        rw [hz]
        simp
      have hfirst := ih hprev
      have hlast := affineIndex_sub_reciprocal_le_pderiv hprev r β i hD
      push_cast
      ring_nf at hfirst hlast ⊢
      linarith

private theorem derivativeFold_zero {m : ℕ}
    (μ : GeneralizedWronskian.MultiIndex m) (l : List (Fin m)) :
    l.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[μ i] Q)
        (0 : MvPolynomial (Fin m) ℚ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      have hz : (MvPolynomial.pderiv i)^[μ i]
          (0 : MvPolynomial (Fin m) ℚ) = 0 := by
        induction μ i with
        | zero => rfl
        | succ n hn => simp [Function.iterate_succ_apply', hn]
      simpa [hz] using ih

private theorem affineIndex_sub_derivativeFoldLoss_le {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ)
    (μ : GeneralizedWronskian.MultiIndex m) (l : List (Fin m))
    (hD : l.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[μ i] Q) P ≠ 0) :
    affineIndex P r β - (l.map fun i ↦ (μ i : ℚ) / (r i : ℚ)).sum ≤
      affineIndex
        (l.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[μ i] Q) P) r β := by
  induction l generalizing P with
  | nil => simpa using le_rfl
  | cons i l ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hD ⊢
      have hfirst : (MvPolynomial.pderiv i)^[μ i] P ≠ 0 := by
        intro hz
        apply hD
        rw [hz, derivativeFold_zero]
      have hhead := affineIndex_sub_iterateLoss_le hP r β i (μ i) hfirst
      have htail := ih hfirst hD
      linarith

/-- A mixed partial derivative loses at most the sum of the normalized
orders of differentiation. -/
theorem affineIndex_sub_multiDerivativeLoss_le {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ)
    (μ : GeneralizedWronskian.MultiIndex m)
    (hD : GeneralizedWronskian.multiDerivative μ P ≠ 0) :
    affineIndex P r β - ∑ i, (μ i : ℚ) / (r i : ℚ) ≤
      affineIndex (GeneralizedWronskian.multiDerivative μ P) r β := by
  unfold GeneralizedWronskian.multiDerivative at hD ⊢
  have h := affineIndex_sub_derivativeFoldLoss_le hP r β μ
    Finset.univ.toList hD
  simpa using h

/-- The combined loss from differentiating first `n` times in one variable
and then by a multi-index. -/
theorem affineIndex_sub_iterate_multiDerivativeLoss_le {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) (z : Fin m) (n : ℕ)
    (μ : GeneralizedWronskian.MultiIndex m)
    (hD : GeneralizedWronskian.multiDerivative μ
      ((MvPolynomial.pderiv z)^[n] P) ≠ 0) :
    affineIndex P r β - (n : ℚ) / (r z : ℚ) -
        ∑ i, (μ i : ℚ) / (r i : ℚ) ≤
      affineIndex (GeneralizedWronskian.multiDerivative μ
        ((MvPolynomial.pderiv z)^[n] P)) r β := by
  have hiter : (MvPolynomial.pderiv z)^[n] P ≠ 0 := by
    intro hz
    apply hD
    rw [hz, GeneralizedWronskian.multiDerivative_zero]
  have hfirst := affineIndex_sub_iterateLoss_le hP r β z n hiter
  have hlast := affineIndex_sub_multiDerivativeLoss_le hiter r β μ hD
  linarith

private theorem iterate_pderiv_ne_zero_of_coeff {m : ℕ}
    (i : Fin m) (Q : MvPolynomial (Fin m) ℚ) (J : Fin m →₀ ℕ)
    (hJ : MvPolynomial.coeff J Q ≠ 0) :
    (MvPolynomial.pderiv i)^[J i] Q ≠ 0 := by
  generalize hn : J i = n
  induction n generalizing J Q with
  | zero =>
      simp only [Function.iterate_zero, id_eq]
      intro hQ
      apply hJ
      rw [hQ, MvPolynomial.coeff_zero]
  | succ n ih =>
      let K : Fin m →₀ ℕ := J - Finsupp.single i 1
      have hKi : K i = n := by
        simp [K, hn]
      have hKadd : K + Finsupp.single i 1 = J := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [K, hn]
        · simp [K, hji]
      have hKcoeff : MvPolynomial.coeff K (MvPolynomial.pderiv i Q) ≠ 0 := by
        rw [MvPolynomial.coeff_pderiv, hKadd]
        exact mul_ne_zero hJ (by positivity)
      rw [Function.iterate_succ_apply]
      exact ih (MvPolynomial.pderiv i Q) K hKcoeff hKi

private theorem degreeOf_pderiv_lt_of_ne_zero {m : ℕ} (i : Fin m)
    {P : MvPolynomial (Fin m) ℚ} (hD : MvPolynomial.pderiv i P ≠ 0) :
    MvPolynomial.degreeOf i (MvPolynomial.pderiv i P) <
      MvPolynomial.degreeOf i P := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hD
  have hdcoeff : MvPolynomial.coeff d (MvPolynomial.pderiv i P) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hc : MvPolynomial.coeff (d + Finsupp.single i 1) P ≠ 0 := by
    intro hz
    apply hdcoeff
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hs : d + Finsupp.single i 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hc
  have hpos : 0 < MvPolynomial.degreeOf i P := by
    have hmono := MvPolynomial.monomial_le_degreeOf i hs
    have : 0 < (d + Finsupp.single i 1 : Fin m →₀ ℕ) i := by simp
    omega
  apply (MvPolynomial.degreeOf_lt_iff hpos).mpr
  intro e he
  have hecoeff : MvPolynomial.coeff e (MvPolynomial.pderiv i P) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have hec : MvPolynomial.coeff (e + Finsupp.single i 1) P ≠ 0 := by
    intro hz
    apply hecoeff
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hes : e + Finsupp.single i 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hec
  have hmono := MvPolynomial.monomial_le_degreeOf i hes
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hmono
  exact Nat.lt_of_succ_le hmono

private theorem iterate_le_degreeOf_of_ne_zero {m : ℕ} (i : Fin m)
    (P : MvPolynomial (Fin m) ℚ) (n : ℕ)
    (hD : (MvPolynomial.pderiv i)^[n] P ≠ 0) :
    n ≤ MvPolynomial.degreeOf i P := by
  induction n generalizing P with
  | zero => omega
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hD
      have hfirst : MvPolynomial.pderiv i P ≠ 0 := by
        intro hz
        apply hD
        rw [hz]
        simp
      have hn := ih (MvPolynomial.pderiv i P) hD
      have hlt := degreeOf_pderiv_lt_of_ne_zero i hfirst
      omega

private theorem translate_iterate_pderiv {m : ℕ} (β : Fin m → ℚ)
    (i : Fin m) (n : ℕ) (P : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate β ((MvPolynomial.pderiv i)^[n] P) =
      (MvPolynomial.pderiv i)^[n] (RothIndex.translate β P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        translate_pderiv, ih]

private theorem support_exponent_le_degreeOf_of_translate {m : ℕ}
    (P : MvPolynomial (Fin m) ℚ) (β : Fin m → ℚ)
    (J : Fin m →₀ ℕ) (hJ : RothIndex.hasseCoeff P β J ≠ 0)
    (i : Fin m) :
    J i ≤ MvPolynomial.degreeOf i P := by
  have hiterT : (MvPolynomial.pderiv i)^[J i]
      (RothIndex.translate β P) ≠ 0 :=
    iterate_pderiv_ne_zero_of_coeff i _ J hJ
  have hiter : (MvPolynomial.pderiv i)^[J i] P ≠ 0 := by
    intro hz
    apply hiterT
    rw [← translate_iterate_pderiv, hz, translate_zero_poly]
  exact iterate_le_degreeOf_of_ne_zero i P (J i) hiter

/-- Partial degree bounds imply the universal estimate `Ind(P) ≤ m`. -/
theorem affineIndex_le_card {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (β : Fin m → ℚ)
    (hdegree : ∀ i, MvPolynomial.degreeOf i P ≤ r i) :
    affineIndex P r β ≤ (m : ℚ) := by
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hP r β
  rw [← hweight, affineWeight]
  calc
    (∑ i, (J i : ℚ) / (r i : ℚ)) ≤ ∑ _i : Fin m, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_one (by exact_mod_cast hr i : (0 : ℚ) < (r i : ℚ))).2
      exact_mod_cast (support_exponent_le_degreeOf_of_translate P β J hJ i).trans
        (hdegree i)
    _ = (m : ℚ) := by simp

/-! ## Reindexing invariance -/

theorem affineWeight_mapDomain_equiv {m : ℕ} (e : Equiv.Perm (Fin m))
    (r : Fin m → ℕ) (J : AffineMultiIndex m) :
    affineWeight (r ∘ e.symm) (Finsupp.mapDomain e J) = affineWeight r J := by
  unfold affineWeight
  rw [← Equiv.sum_comp e (fun j ↦
    (((Finsupp.mapDomain e J) j : ℕ) : ℚ) / ((r ∘ e.symm) j : ℚ))]
  simp [Finsupp.mapDomain_apply e.injective]

theorem translate_rename_equiv {m : ℕ} (e : Equiv.Perm (Fin m))
    (β : Fin m → ℚ) (P : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate (β ∘ e.symm) (MvPolynomial.rename e P) =
      MvPolynomial.rename e (RothIndex.translate β P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [RothIndex.translate]
  | add P Q hP hQ =>
      rw [map_add, RothIndex.translate_add, RothIndex.translate_add,
        map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.rename_X, RothIndex.translate_mul,
        RothIndex.translate_X, RothIndex.translate_mul,
        RothIndex.translate_X, map_mul, map_add, MvPolynomial.rename_C, hP]
      simp [Function.comp_apply]

theorem affineIndexWeights_rename_equiv {m : ℕ} (e : Equiv.Perm (Fin m))
    (P : MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ) (β : Fin m → ℚ) :
    affineIndexWeights (MvPolynomial.rename e P) (r ∘ e.symm) (β ∘ e.symm) =
      affineIndexWeights P r β := by
  classical
  unfold affineIndexWeights
  rw [translate_rename_equiv,
    MvPolynomial.support_rename_of_injective e.injective]
  ext q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨K, ⟨J, hJ, rfl⟩, rfl⟩
    exact ⟨J, hJ, (affineWeight_mapDomain_equiv e r J).symm⟩
  · rintro ⟨J, hJ, rfl⟩
    exact ⟨Finsupp.mapDomain e J, ⟨J, hJ, rfl⟩,
      affineWeight_mapDomain_equiv e r J⟩

theorem affineIndex_rename_equiv {m : ℕ} (e : Equiv.Perm (Fin m))
    (P : MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ) (β : Fin m → ℚ) :
    affineIndex (MvPolynomial.rename e P) (r ∘ e.symm) (β ∘ e.symm) =
      affineIndex P r β := by
  unfold affineIndex
  rw [affineIndexWeights_rename_equiv]

/-! ## The one-variable presentation -/

/-- The canonical identification of a one-variable multivariate polynomial
with an ordinary polynomial. -/
def finOnePolynomial : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)

@[simp] theorem finOnePolynomial_C (a : ℚ) :
    finOnePolynomial (MvPolynomial.C a) = Polynomial.C a := by
  simp [finOnePolynomial]

@[simp] theorem finOnePolynomial_X_zero :
    finOnePolynomial (MvPolynomial.X (0 : Fin 1)) = Polynomial.X := by
  simp [finOnePolynomial]

theorem finOnePolynomial_translate (β : Fin 1 → ℚ)
    (P : MvPolynomial (Fin 1) ℚ) :
    finOnePolynomial (RothIndex.translate β P) =
      (finOnePolynomial P).comp (Polynomial.X + Polynomial.C (β 0)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [RothIndex.translate]
  | add P Q hP hQ => simp [RothIndex.translate_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      simp [RothIndex.translate_mul, hP]

theorem finOnePolynomial_coeff (P : MvPolynomial (Fin 1) ℚ)
    (J : Fin 1 →₀ ℕ) :
    (finOnePolynomial P).coeff (J 0) = MvPolynomial.coeff J P := by
  rw [finOnePolynomial, MvPolynomial.coeff_uniqueAlgEquiv]
  exact congrArg (fun K ↦ MvPolynomial.coeff K P)
    (by simpa using (Finsupp.unique_single J).symm)

theorem rootMultiplicity_eq_natTrailingDegree_translate
    (p : Polynomial ℚ) (hp : p ≠ 0) (a : ℚ) :
    p.rootMultiplicity a =
      (p.comp (Polynomial.X + Polynomial.C a)).natTrailingDegree := by
  let t := p.comp (Polynomial.X + Polynomial.C a)
  have ht : t ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hle (n : ℕ) : n ≤ p.rootMultiplicity a ↔ n ≤ t.rootMultiplicity 0 := by
    rw [Polynomial.le_rootMultiplicity_iff hp,
      Polynomial.le_rootMultiplicity_iff ht, map_zero, sub_zero]
    exact Polynomial.X_sub_C_pow_dvd_iff
  rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact le_antisymm ((hle _).mp le_rfl) ((hle _).mpr le_rfl)

/-- In one variable, the affine index is the usual root multiplicity divided
by the normalizing degree. -/
theorem affineIndex_fin_one_eq_rootMultiplicity_div
    {P : MvPolynomial (Fin 1) ℚ} (hP : P ≠ 0)
    (r : Fin 1 → ℕ) (hr : 0 < r 0) (β : Fin 1 → ℚ) :
    affineIndex P r β =
      ((finOnePolynomial P).rootMultiplicity (β 0) : ℚ) / (r 0 : ℚ) := by
  let p := finOnePolynomial P
  let t := p.comp (Polynomial.X + Polynomial.C (β 0))
  have hp : p ≠ 0 := (finOnePolynomial : _ ≃ₐ[ℚ] _).injective.ne hP
  have ht : t ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hroot : p.rootMultiplicity (β 0) = t.natTrailingDegree :=
    rootMultiplicity_eq_natTrailingDegree_translate p hp (β 0)
  obtain ⟨J, hJ, hweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hP r β
  have hcoeffJ : t.coeff (J 0) ≠ 0 := by
    dsimp [t, p]
    rw [← finOnePolynomial_translate]
    exact finOnePolynomial_coeff _ J ▸ hJ
  have htrail_le : t.natTrailingDegree ≤ J 0 := by
    apply le_of_not_gt
    intro hlt
    exact hcoeffJ (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt)
  have hlower : ((t.natTrailingDegree : ℕ) : ℚ) / (r 0 : ℚ) ≤
      affineIndex P r β := by
    rw [← hweight, affineWeight]
    simp only [Fin.sum_univ_one]
    exact div_le_div_of_nonneg_right (by exact_mod_cast htrail_le) (by positivity)
  let K : Fin 1 →₀ ℕ := Finsupp.single 0 t.natTrailingDegree
  have hKcoeff : RothIndex.hasseCoeff P β K ≠ 0 := by
    rw [RothIndex.hasseCoeff, ← finOnePolynomial_coeff,
      finOnePolynomial_translate]
    simpa [K, t, p] using Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr ht
  have hupper := affineIndex_le_weight hP r β K hKcoeff
  have hKweight : affineWeight r K =
      (t.natTrailingDegree : ℚ) / (r 0 : ℚ) := by
    simp [affineWeight, K]
  rw [hKweight] at hupper
  rw [hroot]
  exact le_antisymm hupper hlower

/-! ## Separating the distinguished variable -/

def liftLeft {m : ℕ} (A : MvPolynomial (Fin m) ℚ) :
    MvPolynomial (Fin (m + 1)) ℚ :=
  (MvPolynomial.finSuccEquiv ℚ m).symm (Polynomial.C A)

def liftRight {m : ℕ} (q : Polynomial ℚ) :
    MvPolynomial (Fin (m + 1)) ℚ :=
  (MvPolynomial.finSuccEquiv ℚ m).symm (q.map MvPolynomial.C)

@[simp] theorem finSuccEquiv_liftLeft {m : ℕ}
    (A : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.finSuccEquiv ℚ m (liftLeft A) = Polynomial.C A := by
  simp [liftLeft]

@[simp] theorem finSuccEquiv_liftRight {m : ℕ} (q : Polynomial ℚ) :
    MvPolynomial.finSuccEquiv ℚ m (liftRight q) = q.map MvPolynomial.C := by
  simp [liftRight]

@[simp] theorem liftLeft_C {m : ℕ} (a : ℚ) :
    liftLeft (m := m) (MvPolynomial.C a) = MvPolynomial.C a := by
  change (MvPolynomial.finSuccEquiv ℚ m).symm
    (Polynomial.C (MvPolynomial.C a)) = MvPolynomial.C a
  simpa using DFunLike.congr_fun
    (MvPolynomial.finSuccEquiv_comp_C_eq_C m) a

@[simp] theorem liftLeft_add {m : ℕ} (A B : MvPolynomial (Fin m) ℚ) :
    liftLeft (A + B) = liftLeft A + liftLeft B := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  simp

@[simp] theorem liftLeft_mul_X {m : ℕ} (A : MvPolynomial (Fin m) ℚ)
    (i : Fin m) : liftLeft (A * MvPolynomial.X i) =
      liftLeft A * MvPolynomial.X i.succ := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  rw [map_mul, finSuccEquiv_liftLeft,
    MvPolynomial.finSuccEquiv_X_succ]
  simp

@[simp] theorem liftLeft_mul {m : ℕ} (A B : MvPolynomial (Fin m) ℚ) :
    liftLeft (A * B) = liftLeft A * liftLeft B := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  simp only [finSuccEquiv_liftLeft, map_mul]

@[simp] theorem liftLeft_X {m : ℕ} (i : Fin m) :
    liftLeft (MvPolynomial.X i) =
      (MvPolynomial.X i.succ : MvPolynomial (Fin (m + 1)) ℚ) := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  rw [finSuccEquiv_liftLeft, MvPolynomial.finSuccEquiv_X_succ]

@[simp] theorem liftRight_C {m : ℕ} (a : ℚ) :
    liftRight (m := m) (Polynomial.C a) = MvPolynomial.C a := by
  unfold liftRight
  rw [Polynomial.map_C]
  change (MvPolynomial.finSuccEquiv ℚ m).symm
    (Polynomial.C (MvPolynomial.C a)) = MvPolynomial.C a
  simpa using DFunLike.congr_fun
    (MvPolynomial.finSuccEquiv_comp_C_eq_C m) a

@[simp] theorem liftRight_add {m : ℕ} (p q : Polynomial ℚ) :
    liftRight (m := m) (p + q) = liftRight (m := m) p + liftRight q := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  simp

@[simp] theorem liftRight_mul {m : ℕ} (p q : Polynomial ℚ) :
    liftRight (m := m) (p * q) = liftRight (m := m) p * liftRight q := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  simp

@[simp] theorem liftRight_mul_X {m : ℕ} (q : Polynomial ℚ) :
    liftRight (m := m) (q * Polynomial.X) =
      liftRight (m := m) q * MvPolynomial.X 0 := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  rw [map_mul, finSuccEquiv_liftRight,
    MvPolynomial.finSuccEquiv_X_zero]
  simp

@[simp] theorem liftRight_X {m : ℕ} :
    liftRight (m := m) Polynomial.X =
      (MvPolynomial.X 0 : MvPolynomial (Fin (m + 1)) ℚ) := by
  apply (MvPolynomial.finSuccEquiv ℚ m).injective
  rw [finSuccEquiv_liftRight, Polynomial.map_X,
    MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem liftRight_pow {m : ℕ} (q : Polynomial ℚ) (n : ℕ) :
    liftRight (m := m) (q ^ n) = liftRight (m := m) q ^ n := by
  induction n with
  | zero =>
      apply (MvPolynomial.finSuccEquiv ℚ m).injective
      simp
  | succ n ih => rw [pow_succ, liftRight_mul, ih, pow_succ]

theorem translate_liftLeft {m : ℕ} (β : Fin (m + 1) → ℚ)
    (A : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate β (liftLeft A) =
      liftLeft (RothIndex.translate (fun i ↦ β i.succ) A) := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [RothIndex.translate]
  | add A B hA hB => simp [RothIndex.translate_add, hA, hB]
  | mul_X A i hA => simp [RothIndex.translate_mul, hA]

private theorem translate_pow {ι : Type*} (β : ι → ℚ)
    (A : MvPolynomial ι ℚ) (n : ℕ) :
    RothIndex.translate β (A ^ n) = RothIndex.translate β A ^ n := by
  induction n with
  | zero => simp [RothIndex.translate]
  | succ n ih => simp [pow_succ, RothIndex.translate_mul, ih]

theorem translate_liftRight {m : ℕ} (β : Fin (m + 1) → ℚ)
    (q : Polynomial ℚ) :
    RothIndex.translate β (liftRight q) =
      liftRight (q.comp (Polynomial.X + Polynomial.C (β 0))) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [RothIndex.translate_add, hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [liftRight_mul, liftRight_C, liftRight_pow,
        RothIndex.translate_mul, RothIndex.translate_C, translate_pow,
        liftRight_X, RothIndex.translate_X, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_pow_comp,
        liftRight_mul, liftRight_C, liftRight_pow, liftRight_add,
        liftRight_X, liftRight_C]

theorem finSuccEquiv_lift_mul {m : ℕ}
    (A : MvPolynomial (Fin m) ℚ) (q : Polynomial ℚ) :
    MvPolynomial.finSuccEquiv ℚ m (liftLeft A * liftRight q) =
      Polynomial.C A * q.map MvPolynomial.C := by simp

theorem affineWeight_cons {m : ℕ} (r : Fin (m + 1) → ℕ)
    (n : ℕ) (J : Fin m →₀ ℕ) :
    affineWeight r (Finsupp.cons n J) =
      (n : ℚ) / (r 0 : ℚ) + affineWeight (fun i ↦ r i.succ) J := by
  unfold affineWeight
  rw [Fin.sum_univ_succ]
  simp

/-- The index of a product in the distinguished variable and the remaining
variables is at most the sum of the two separate indices.  Together with
`affineIndex_add_le_mul`, this is the disjoint-variable additivity used in
the Wronskian induction. -/
theorem affineIndex_liftLeft_mul_liftRight_le {m : ℕ}
    {A : MvPolynomial (Fin m) ℚ} (hA : A ≠ 0)
    {q : Polynomial ℚ} (hq : q ≠ 0)
    (r : Fin (m + 1) → ℕ) (β : Fin (m + 1) → ℚ) :
    affineIndex (liftLeft A * liftRight q) r β ≤
      affineIndex A (fun i ↦ r i.succ) (fun i ↦ β i.succ) +
        (q.rootMultiplicity (β 0) : ℚ) / (r 0 : ℚ) := by
  let t := q.comp (Polynomial.X + Polynomial.C (β 0))
  have ht : t ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hq
  let n := t.natTrailingDegree
  obtain ⟨J, hJ, hweightJ⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hA
      (fun i ↦ r i.succ) (fun i ↦ β i.succ)
  let K : Fin (m + 1) →₀ ℕ := Finsupp.cons n J
  have hn : t.coeff n ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr ht
  have hK : RothIndex.hasseCoeff (liftLeft A * liftRight q) β K ≠ 0 := by
    rw [RothIndex.hasseCoeff, RothIndex.translate_mul,
      translate_liftLeft, translate_liftRight]
    change MvPolynomial.coeff (Finsupp.cons n J)
      (liftLeft (RothIndex.translate (fun i ↦ β i.succ) A) * liftRight t) ≠ 0
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff J _ n, map_mul,
      finSuccEquiv_liftLeft, finSuccEquiv_liftRight,
      Polynomial.coeff_C_mul, Polynomial.coeff_map]
    rw [mul_comm, MvPolynomial.coeff_C_mul]
    exact mul_ne_zero hn hJ
  have hleft : liftLeft A ≠ 0 := by
    intro hz
    have hz' := congrArg (MvPolynomial.finSuccEquiv ℚ m) hz
    simp only [finSuccEquiv_liftLeft, map_zero, Polynomial.C_eq_zero] at hz'
    exact hA hz'
  have hright : liftRight (m := m) q ≠ 0 := by
    intro hz
    have hz' := congrArg (MvPolynomial.finSuccEquiv ℚ m) hz
    simp only [finSuccEquiv_liftRight, map_zero] at hz'
    exact ((Polynomial.map_ne_zero_iff
      (MvPolynomial.C_injective (σ := Fin m) (R := ℚ))).mpr hq) hz'
  have hupper := affineIndex_le_weight (mul_ne_zero hleft hright) r β K hK
  rw [affineWeight_cons, hweightJ] at hupper
  have hroot := rootMultiplicity_eq_natTrailingDegree_translate q hq (β 0)
  change q.rootMultiplicity (β 0) = n at hroot
  rw [hroot]
  simpa [add_comm] using hupper

private theorem finOnePolynomial_natDegree_le
    {P : MvPolynomial (Fin 1) ℚ} {r : ℕ}
    (hdegree : MvPolynomial.degreeOf 0 P ≤ r) :
    (finOnePolynomial P).natDegree ≤ r := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  let J : Fin 1 →₀ ℕ := Finsupp.single 0 N
  have hJ0 : J 0 = N := by simp [J]
  rw [← hJ0, finOnePolynomial_coeff P J]
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  have hJN := MvPolynomial.degreeOf_le_iff.mp hdegree J hmem
  simp [J] at hJN
  omega

/-- The one-variable base case of the quantitative Roth lemma. -/
theorem rothLemmaOne
    {P : MvPolynomial (Fin 1) ℚ} (hP : P ≠ 0)
    (r : Fin 1 → ℕ) (hr : 0 < r 0) (β : Fin 1 → ℚ)
    {η : ℝ} (hη : 0 < η)
    (hdegree : MvPolynomial.degreeOf 0 P ≤ r 0)
    (hheight : PolynomialHeights.projectiveCoeffHeight P +
        2 * (r 0 : ℝ) ≤
      η * (r 0 : ℝ) * Height.logHeight₁ (β 0)) :
    (affineIndex P r β : ℝ) ≤ 2 * η := by
  have hdeg := finOnePolynomial_natDegree_le hdegree
  have hmahler :=
    MahlerHeightBridge.uniqueAlgEquiv_rootMultiplicity_mul_logHeight₁_le
      hP (β 0) hdeg
  change ((finOnePolynomial P).rootMultiplicity (β 0) : ℝ) *
      Height.logHeight₁ (β 0) ≤
    PolynomialHeights.projectiveCoeffHeight P + (r 0 : ℝ) at hmahler
  have hrR : (0 : ℝ) < (r 0 : ℝ) := by exact_mod_cast hr
  have hpoly0 : 0 ≤ PolynomialHeights.projectiveCoeffHeight P :=
    PolynomialHeights.projectiveCoeffHeight_nonneg P
  have hbeta : 0 < Height.logHeight₁ (β 0) := by
    have hprod : 0 < η * (r 0 : ℝ) * Height.logHeight₁ (β 0) := by
      calc
        0 < PolynomialHeights.projectiveCoeffHeight P + 2 * (r 0 : ℝ) := by
          positivity
        _ ≤ _ := hheight
    have hb0 := Height.zero_le_logHeight₁ (β 0)
    apply lt_of_le_of_ne hb0
    intro heq
    rw [← heq, mul_zero] at hprod
    exact (lt_irrefl 0) hprod
  have hmult :
      ((finOnePolynomial P).rootMultiplicity (β 0) : ℝ) ≤
        η * (r 0 : ℝ) := by
    nlinarith
  have hdiv :
      ((finOnePolynomial P).rootMultiplicity (β 0) : ℝ) /
          (r 0 : ℝ) ≤ η :=
    (div_le_iff₀ hrR).2 hmult
  have hindex := affineIndex_fin_one_eq_rootMultiplicity_div hP r hr β
  have hindexR : (affineIndex P r β : ℝ) =
      ((finOnePolynomial P).rootMultiplicity (β 0) : ℝ) / (r 0 : ℝ) := by
    rw [hindex]
    simp only [Rat.cast_div, Rat.cast_natCast]
  rw [hindexR]
  linarith

/-- Replacing all normalizing degrees by a common lower bound bounds a
multi-index loss by its total order divided by that lower bound. -/
theorem multiDerivativeLoss_le_totalOrder_div {m q s : ℕ}
    (r : Fin m → ℕ) (hs : 0 < s) (hsr : ∀ i, s ≤ r i)
    (μ : GeneralizedWronskian.MultiIndex m)
    (hμ : GeneralizedWronskian.totalOrder μ ≤ q) :
    (∑ i, (μ i : ℚ) / (r i : ℚ)) ≤ (q : ℚ) / (s : ℚ) := by
  have hsQ : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  calc
    (∑ i, (μ i : ℚ) / (r i : ℚ)) ≤
        ∑ i, (μ i : ℚ) / (s : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div_of_nonneg_left (by positivity)
        hsQ (by exact_mod_cast hsr i)
    _ = ((∑ i, μ i : ℕ) : ℚ) / (s : ℚ) := by
      rw [← Finset.sum_div]
      norm_cast
    _ ≤ (q : ℚ) / (s : ℚ) := by
      apply div_le_div_of_nonneg_right _ hsQ.le
      change (∑ i, μ i) ≤ q at hμ
      exact_mod_cast hμ

/-- GLR's determinant-index inequality before estimating the finite sum.
If every row multi-index has normalized order at most `δ`, the Wronskian
determinant controls the sum of the truncated column losses. -/
theorem sum_max_sub_le_affineIndex_derivativeDet {m k : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (β : Fin m → ℚ)
    (z : Fin m) (μ : Fin k → GeneralizedWronskian.MultiIndex m)
    (δ : ℚ)
    (hμ : ∀ a, (∑ i, (μ a i : ℚ) / (r i : ℚ)) ≤ δ)
    (hdet : Matrix.det (fun a b : Fin k ↦
      GeneralizedWronskian.multiDerivative (μ a)
        ((MvPolynomial.pderiv z)^[(b : ℕ)] P)) ≠ 0) :
    ∑ b : Fin k,
        max (affineIndex P r β - δ - (b : ℚ) / (r z : ℚ)) 0 ≤
      affineIndex (Matrix.det (fun a b : Fin k ↦
        GeneralizedWronskian.multiDerivative (μ a)
          ((MvPolynomial.pderiv z)^[(b : ℕ)] P))) r β := by
  let A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ) :=
    fun a b ↦ GeneralizedWronskian.multiDerivative (μ a)
      ((MvPolynomial.pderiv z)^[(b : ℕ)] P)
  let B : Fin k → ℚ := fun b ↦
    max (affineIndex P r β - δ - (b : ℚ) / (r z : ℚ)) 0
  apply sum_le_affineIndex_det A hdet r β B
  intro a b hab
  apply max_le
  · have hentry := affineIndex_sub_iterate_multiDerivativeLoss_le
      hP r β z (b : ℕ) (μ a) hab
    have hμa := hμ a
    dsimp [A, B]
    linarith
  · exact affineIndex_nonneg hab hr β

/-- The form of the determinant-index estimate used in GLR (3.11): the
uniform row loss is moved outside the truncated column sum. -/
theorem sum_max_le_affineIndex_derivativeDet_add_loss {m k : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (β : Fin m → ℚ)
    (z : Fin m) (μ : Fin k → GeneralizedWronskian.MultiIndex m)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hμ : ∀ a, (∑ i, (μ a i : ℚ) / (r i : ℚ)) ≤ δ)
    (hdet : Matrix.det (fun a b : Fin k ↦
      GeneralizedWronskian.multiDerivative (μ a)
        ((MvPolynomial.pderiv z)^[(b : ℕ)] P)) ≠ 0) :
    (∑ b : Fin k,
        max (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0) ≤
      affineIndex (Matrix.det (fun a b : Fin k ↦
        GeneralizedWronskian.multiDerivative (μ a)
          ((MvPolynomial.pderiv z)^[(b : ℕ)] P))) r β + (k : ℚ) * δ := by
  let A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ) :=
    fun a b ↦ GeneralizedWronskian.multiDerivative (μ a)
      ((MvPolynomial.pderiv z)^[(b : ℕ)] P)
  let B : Fin k → ℚ := fun b ↦
    max (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0 - δ
  have hsum : ∑ b, B b ≤ affineIndex A.det r β := by
    apply sum_le_affineIndex_det A hdet r β B
    intro a b hab
    have hentry := affineIndex_sub_iterate_multiDerivativeLoss_le
      hP r β z (b : ℕ) (μ a) hab
    have hμa := hμ a
    have hentry0 := affineIndex_nonneg hab hr β
    dsimp [A, B]
    rcases le_total
        (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0 with hnonpos | hnonneg
    · rw [max_eq_right hnonpos]
      linarith
    · rw [max_eq_left hnonneg]
      linarith
  dsimp [B] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  exact sub_le_iff_le_add.mp hsum

/-! ## The numerical lower bound in the Wronskian argument -/

private theorem sum_fin_val_real (k : ℕ) :
    (∑ j : Fin k, (j.1 : ℝ)) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      have hcast : (∑ i : Fin k, (i.castSucc.1 : ℝ)) =
          (k : ℝ) * ((k : ℝ) - 1) / 2 := by simpa using ih
      rw [hcast]
      simp only [Fin.val_last]
      push_cast
      ring

/-- The elementary truncated-arithmetic-progression estimate used in GLR
(3.11).  It is stated over `ℝ` so it can be applied directly after casting
the rational affine index. -/
theorem sum_max_sub_div_lower {m k r : ℕ} {x : ℝ}
    (hm : 2 ≤ m) (hk0 : 0 < k) (hr : 0 < r) (hk : k ≤ r + 1)
    (hx0 : 0 ≤ x) (hxm : x ≤ m) :
    (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) ≤
      ∑ j : Fin k, max (x - (j.1 : ℝ) / (r : ℝ)) 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < m := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkpred : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0.ne')]
    norm_num
  by_cases hlarge : ((k - 1 : ℕ) : ℝ) / (r : ℝ) < x
  · have hterm (j : Fin k) :
        max (x - (j.1 : ℝ) / (r : ℝ)) 0 =
          x - (j.1 : ℝ) / (r : ℝ) := by
      rw [max_eq_left]
      have hj : (j.1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_sub_one_of_lt j.isLt)
      have hjdiv : (j.1 : ℝ) / (r : ℝ) ≤
          ((k - 1 : ℕ) : ℝ) / (r : ℝ) := by
        exact div_le_div_of_nonneg_right hj hrR.le
      linarith
    rw [show (∑ j : Fin k, max (x - (j.1 : ℝ) / (r : ℝ)) 0) =
        ∑ j : Fin k, (x - (j.1 : ℝ) / (r : ℝ)) by
      apply Finset.sum_congr rfl
      intro j _
      exact hterm j]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Finset.sum_div, sum_fin_val_real]
    have hthreshold : ((k : ℝ) - 1) / (r : ℝ) < x := by
      simpa only [hkpred] using hlarge
    have hhalf :
        (k : ℝ) * ((k : ℝ) - 1) / (2 * (r : ℝ)) <
          (k : ℝ) * x / 2 := by
      calc
        (k : ℝ) * ((k : ℝ) - 1) / (2 * (r : ℝ)) =
            (k : ℝ) / 2 * (((k : ℝ) - 1) / (r : ℝ)) := by ring
        _ < (k : ℝ) / 2 * x := by
          exact mul_lt_mul_of_pos_left hthreshold (by positivity)
        _ = (k : ℝ) * x / 2 := by ring
    have hxdiv : x ^ 2 / (m : ℝ) ≤ x := by
      apply (div_le_iff₀ hmR).2
      nlinarith
    have hgoal : (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) ≤
        (k : ℝ) * x / 2 := by
      calc
        (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) =
            (k : ℝ) / 2 * (x ^ 2 / (m : ℝ)) := by ring
        _ ≤ (k : ℝ) / 2 * x :=
          mul_le_mul_of_nonneg_left hxdiv (by positivity)
        _ = (k : ℝ) * x / 2 := by ring
    have heqsum : k • x -
        ((k : ℝ) * ((k : ℝ) - 1) / 2) / (r : ℝ) =
        (k : ℝ) * x -
          (k : ℝ) * ((k : ℝ) - 1) / (2 * (r : ℝ)) := by
      simp only [nsmul_eq_mul]
      ring
    rw [heqsum]
    linarith
  · have hsmall : x ≤ ((k - 1 : ℕ) : ℝ) / (r : ℝ) := le_of_not_gt hlarge
    let N : ℕ := ⌊(r : ℝ) * x⌋₊
    have hy0 : 0 ≤ (r : ℝ) * x := mul_nonneg hrR.le hx0
    have hNy : (N : ℝ) ≤ (r : ℝ) * x := Nat.floor_le hy0
    have hyN : (r : ℝ) * x < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hyk : (r : ℝ) * x ≤ ((k - 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using (le_div_iff₀ hrR).mp hsmall
    have hNk : N < k := by
      have hpredlt : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.sub_one_lt hk0.ne'
      exact_mod_cast lt_of_le_of_lt (hNy.trans hyk) hpredlt
    have hsub : Finset.range (N + 1) ⊆ Finset.range k :=
      Finset.range_mono (Nat.succ_le_iff.mpr hNk)
    have hpartial :
        (∑ i ∈ Finset.range (N + 1),
          max (x - (i : ℝ) / (r : ℝ)) 0) ≤
        ∑ i ∈ Finset.range k,
          max (x - (i : ℝ) / (r : ℝ)) 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi hni
      exact le_max_right _ _
    have hterm (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
        max (x - (i : ℝ) / (r : ℝ)) 0 =
          x - (i : ℝ) / (r : ℝ) := by
      rw [max_eq_left]
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiy : (i : ℝ) ≤ (r : ℝ) * x := by
        exact (by exact_mod_cast hiN : (i : ℝ) ≤ (N : ℝ)).trans hNy
      exact sub_nonneg.mpr ((div_le_iff₀ hrR).2 (by simpa [mul_comm] using hiy))
    have hpartialeq :
        (∑ i ∈ Finset.range (N + 1),
          max (x - (i : ℝ) / (r : ℝ)) 0) =
        (N + 1 : ℝ) * x -
          (N : ℝ) * ((N : ℝ) + 1) / (2 * (r : ℝ)) := by
      calc
        (∑ i ∈ Finset.range (N + 1),
          max (x - (i : ℝ) / (r : ℝ)) 0) =
            ∑ i ∈ Finset.range (N + 1),
              (x - (i : ℝ) / (r : ℝ)) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hterm i hi
        _ = (N + 1 : ℝ) * x -
            (N : ℝ) * ((N : ℝ) + 1) / (2 * (r : ℝ)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const,
                Finset.card_range, ← Finset.sum_div]
              have hsum : (∑ i ∈ Finset.range (N + 1), (i : ℝ)) =
                  (N + 1 : ℝ) * ((N + 1 : ℝ) - 1) / 2 := by
                rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ)) (N + 1)]
                simpa only [Nat.cast_add, Nat.cast_one] using sum_fin_val_real (N + 1)
              rw [hsum]
              ring
    have htri : (r : ℝ) * x ^ 2 / 2 ≤
        (N + 1 : ℝ) * x -
          (N : ℝ) * ((N : ℝ) + 1) / (2 * (r : ℝ)) := by
      have heqleft : (r : ℝ) * x ^ 2 / 2 =
          ((r : ℝ) ^ 2 * x ^ 2 / 2) / (r : ℝ) := by field_simp
      have heqright : (N + 1 : ℝ) * x -
          (N : ℝ) * ((N : ℝ) + 1) / (2 * (r : ℝ)) =
          (((N : ℝ) + 1) * (r : ℝ) * x -
            (N : ℝ) * ((N : ℝ) + 1) / 2) / (r : ℝ) := by field_simp
      rw [heqleft, heqright]
      apply (div_le_div_iff_of_pos_right hrR).2
      have hN0 : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg ((r : ℝ) * x - (N : ℝ)),
        mul_nonneg hN0 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    have hk2r : (k : ℝ) ≤ 2 * (r : ℝ) := by
      have : k ≤ 2 * r := by omega
      exact_mod_cast this
    have hkm : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hsquare : 0 ≤ x ^ 2 := sq_nonneg x
    have hfinal : (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) ≤
        (r : ℝ) * x ^ 2 / 2 := by
      have hcoef : (k : ℝ) / (2 * (m : ℝ)) ≤ (r : ℝ) / 2 := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))
          (by positivity : (0 : ℝ) < 2)).2
        nlinarith
      calc
        (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) =
            ((k : ℝ) / (2 * (m : ℝ))) * x ^ 2 := by ring
        _ ≤ ((r : ℝ) / 2) * x ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hsquare
        _ = (r : ℝ) * x ^ 2 / 2 := by ring
    calc
      (k : ℝ) * x ^ 2 / (2 * (m : ℝ)) ≤ (r : ℝ) * x ^ 2 / 2 := hfinal
      _ ≤ ∑ i ∈ Finset.range (N + 1),
          max (x - (i : ℝ) / (r : ℝ)) 0 := by simpa [hpartialeq] using htri
      _ ≤ ∑ i ∈ Finset.range k,
          max (x - (i : ℝ) / (r : ℝ)) 0 := hpartial
      _ = ∑ j : Fin k, max (x - (j.1 : ℝ) / (r : ℝ)) 0 := by
        exact (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦ max (x - (i : ℝ) / (r : ℝ)) 0) k).symm

/-- The completed index-theoretic part of GLR (3.11).  The remaining
Wronskian argument only has to provide a nonzero determinant, the row-order
bound `δ`, and an upper bound for the determinant's index. -/
theorem sq_affineIndex_le_derivativeDet_add_loss {m k : ℕ}
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (β : Fin m → ℚ)
    (z : Fin m) (μ : Fin k → GeneralizedWronskian.MultiIndex m)
    (hm : 2 ≤ m) (hk0 : 0 < k) (hk : k ≤ r z + 1)
    (hindex : (affineIndex P r β : ℝ) ≤ m)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hμ : ∀ a, (∑ i, (μ a i : ℚ) / (r i : ℚ)) ≤ δ)
    (hdet : Matrix.det (fun a b : Fin k ↦
      GeneralizedWronskian.multiDerivative (μ a)
        ((MvPolynomial.pderiv z)^[(b : ℕ)] P)) ≠ 0) :
    (k : ℝ) * (affineIndex P r β : ℝ) ^ 2 / (2 * (m : ℝ)) ≤
      (affineIndex (Matrix.det (fun a b : Fin k ↦
        GeneralizedWronskian.multiDerivative (μ a)
          ((MvPolynomial.pderiv z)^[(b : ℕ)] P))) r β : ℝ) +
        (k : ℝ) * (δ : ℝ) := by
  have hx0Q : 0 ≤ affineIndex P r β := affineIndex_nonneg hP hr β
  have hx0 : (0 : ℝ) ≤ (affineIndex P r β : ℝ) := by exact_mod_cast hx0Q
  have hlower := sum_max_sub_div_lower hm hk0 (hr z) hk hx0 hindex
  have hupperQ := sum_max_le_affineIndex_derivativeDet_add_loss
    hP r hr β z μ δ hδ hμ hdet
  have hupperR :
      (∑ b : Fin k,
          max ((affineIndex P r β : ℝ) - (b : ℝ) / (r z : ℝ)) 0) ≤
        (affineIndex (Matrix.det (fun a b : Fin k ↦
          GeneralizedWronskian.multiDerivative (μ a)
            ((MvPolynomial.pderiv z)^[(b : ℕ)] P))) r β : ℝ) +
          (k : ℝ) * (δ : ℝ) := by
    have hcast :
        ((∑ b : Fin k,
          max (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0 : ℚ) : ℝ) ≤
        ((affineIndex (Matrix.det (fun a b : Fin k ↦
          GeneralizedWronskian.multiDerivative (μ a)
            ((MvPolynomial.pderiv z)^[(b : ℕ)] P))) r β +
          (k : ℚ) * δ : ℚ) : ℝ) := Rat.cast_le.mpr hupperQ
    have hsumcast :
        ((∑ b : Fin k,
          max (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0 : ℚ) : ℝ) =
        ∑ b : Fin k,
          ((max (affineIndex P r β - (b : ℚ) / (r z : ℚ)) 0 : ℚ) : ℝ) := by
      exact map_sum (Rat.castHom ℝ) _ Finset.univ
    rw [hsumcast] at hcast
    simpa only [Rat.cast_max, Rat.cast_sub, Rat.cast_div,
      Rat.cast_zero, Rat.cast_natCast, Rat.cast_add, Rat.cast_mul] using hcast
  exact hlower.trans hupperR

/-- Embed a scalar variable as the unique variable in its block. -/
def toUnaryBlock {m : ℕ} (j : Fin m) : RothIndex.BlockVar m 0 := (j, 0)

theorem toUnaryBlock_injective {m : ℕ} :
    Function.Injective (@toUnaryBlock m) := by
  intro i j hij
  exact congrArg Prod.fst hij

/-- Regard an affine polynomial as a block polynomial with one variable in
each block. -/
def blockify {m : ℕ} (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial (RothIndex.BlockVar m 0) ℚ :=
  MvPolynomial.rename toUnaryBlock P

/-- Regard an affine point as a point in one-dimensional blocks. -/
def blockPoint {m : ℕ} (β : Fin m → ℚ) : RothIndex.MultiPoint m 0 :=
  fun j _ ↦ β j

@[simp] theorem flattenPoint_blockPoint {m : ℕ} (β : Fin m → ℚ)
    (x : RothIndex.BlockVar m 0) :
    RothIndex.flattenPoint (blockPoint β) x = β x.1 := by
  rfl

@[simp] theorem blockOrder_mapDomain_toUnaryBlock {m : ℕ}
    (J : AffineMultiIndex m) (j : Fin m) :
    RothIndex.blockOrder (Finsupp.mapDomain toUnaryBlock J) j = J j := by
  simp only [RothIndex.blockOrder, Fin.sum_univ_one]
  exact Finsupp.mapDomain_apply toUnaryBlock_injective J j

@[simp] theorem normalizedWeight_mapDomain_toUnaryBlock {m : ℕ}
    (r : Fin m → ℕ) (J : AffineMultiIndex m) :
    RothIndex.normalizedWeight r (Finsupp.mapDomain toUnaryBlock J) =
      affineWeight r J := by
  simp [RothIndex.normalizedWeight, affineWeight]

/-- Translation commutes with inserting the unique variable in every block. -/
theorem translate_blockify {m : ℕ} (β : Fin m → ℚ)
    (P : MvPolynomial (Fin m) ℚ) :
    RothIndex.translate (RothIndex.flattenPoint (blockPoint β)) (blockify P) =
      blockify (RothIndex.translate β P) := by
  unfold RothIndex.translate blockify
  change MvPolynomial.bind₁
      (fun x ↦ MvPolynomial.X x + MvPolynomial.C (β x.1))
        (MvPolynomial.rename toUnaryBlock P) =
    MvPolynomial.rename toUnaryBlock
      (MvPolynomial.bind₁
        (fun i ↦ MvPolynomial.X i + MvPolynomial.C (β i)) P)
  rw [MvPolynomial.bind₁_rename, MvPolynomial.rename_bind₁]
  apply congrArg (fun f : Fin m → MvPolynomial (RothIndex.BlockVar m 0) ℚ ↦
    MvPolynomial.bind₁ f P)
  funext i
  simp [toUnaryBlock]

theorem indexWeights_blockify {m : ℕ} (P : MvPolynomial (Fin m) ℚ)
    (r : Fin m → ℕ) (β : Fin m → ℚ) :
    RothIndex.indexWeights (blockify P) r (blockPoint β) =
      affineIndexWeights P r β := by
  classical
  unfold RothIndex.indexWeights affineIndexWeights
  rw [translate_blockify, blockify,
    MvPolynomial.support_rename_of_injective toUnaryBlock_injective]
  ext q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨K, ⟨J, hJ, rfl⟩, rfl⟩
    exact ⟨J, hJ, (normalizedWeight_mapDomain_toUnaryBlock r J).symm⟩
  · rintro ⟨J, hJ, rfl⟩
    exact ⟨Finsupp.mapDomain toUnaryBlock J, ⟨J, hJ, rfl⟩,
      normalizedWeight_mapDomain_toUnaryBlock r J⟩

/-- The affine index is exactly the existing block index after inserting one
variable in every block. -/
theorem normalizedIndex_blockify {m : ℕ} (P : MvPolynomial (Fin m) ℚ)
    (r : Fin m → ℕ) (β : Fin m → ℚ) :
    RothIndex.normalizedIndex (blockify P) r (blockPoint β) =
      affineIndex P r β := by
  unfold RothIndex.normalizedIndex affineIndex
  rw [indexWeights_blockify]

end

end Erdos407.BinaryRoth
