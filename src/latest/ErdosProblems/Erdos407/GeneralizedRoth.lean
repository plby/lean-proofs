/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RothIndex
import ErdosProblems.Erdos407.PolynomialHeights
import ErdosProblems.Erdos407.BinaryRoth
import ErdosProblems.Erdos407.BinaryRothTerminal

/-!
# Rational coordinates for the generalized Roth lemma

For each nonzero rational linear form we make a canonical choice of a
nonzero coefficient.  The associated triangular linear change of variables
turns that form into one distinguished variable.  Consequently the index in
powers of the forms is the least normalized exponent of the distinguished
variables, and extracting a coefficient of least weight gives the divided
derivative whose restriction to the product of kernels is nonzero.
-/

namespace Erdos407.GeneralizedRoth

open scoped BigOperators

noncomputable section

/-- A rational linear form on projective `n`-space. -/
abbrev RatLinearForm (n : ℕ) := Fin (n + 1) → ℚ

/-- A family of one rational linear form in each of `m` variable blocks. -/
abbrev FormFamily (m n : ℕ) := Fin m → RatLinearForm n

/-- The polynomial represented by the `j`th linear form. -/
def formPolynomial {m n : ℕ} (M : FormFamily m n) (j : Fin m) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  ∑ k : Fin (n + 1),
    MvPolynomial.C (M j k) * MvPolynomial.X (j, k)

/-- A canonical coordinate on which a nonzero form has nonzero coefficient. -/
def pivotIndex {n : ℕ} (M : RatLinearForm n) (hM : M ≠ 0) : Fin (n + 1) :=
  Classical.choose (Function.ne_iff.mp hM)

theorem pivotIndex_coeff_ne_zero {n : ℕ} (M : RatLinearForm n) (hM : M ≠ 0) :
    M (pivotIndex M hM) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp hM)

/-! ## A binary coordinate retaining height -/

/-- The usual logarithmic projective height of the coefficient vector of a
rational linear form. -/
def formHeight {n : ℕ} (M : RatLinearForm n) : ℝ :=
  Height.logHeight M

private def pairRatio {n : ℕ} (M : RatLinearForm n) (p : Fin (n + 1))
    (a : Fin (n + 1)) : Fin 2 → ℚ :=
  ![1, M a / M p]

private def pickCoordinate {n : ℕ} (i : Fin (n + 1)) :
    (a : Fin (n + 1)) → Fin 2 :=
  fun a ↦ if a = i then 1 else 0

private theorem prod_pairRatio_pick {n : ℕ} (M : RatLinearForm n)
    (p i : Fin (n + 1)) :
    (∏ a, pairRatio M p a (pickCoordinate i a)) = M i / M p := by
  classical
  rw [Fintype.prod_eq_single i]
  · simp [pairRatio, pickCoordinate]
  · intro b hbi
    simp [pairRatio, pickCoordinate, hbi]

/-- The height of a rational projective point is at most the sum of the
heights of all binary coordinate pairs containing one fixed nonzero
coordinate.  This is the product-formula estimate used in GLR Lemma 4.21. -/
theorem formHeight_le_sum_binaryHeights {n : ℕ} (M : RatLinearForm n)
    (p : Fin (n + 1)) (hp : M p ≠ 0) :
    formHeight M ≤
      ∑ a : Fin (n + 1), Height.logHeight ![M p, M a] := by
  let x : (a : Fin (n + 1)) → Fin 2 → ℚ := fun a ↦ pairRatio M p a
  have hx : ∀ a, x a ≠ 0 := by
    intro a h
    have := congrFun h 0
    simp [x, pairRatio] at this
  have hcomp := Height.logHeight_comp_le (pickCoordinate (n := n))
    (fun I : (a : Fin (n + 1)) → Fin 2 ↦ ∏ a, x a (I a))
  have hleft :
      Height.logHeight (fun i ↦ M i / M p) ≤
        Height.logHeight
          (fun I : (a : Fin (n + 1)) → Fin 2 ↦ ∏ a, x a (I a)) := by
    calc
      _ = Height.logHeight
          ((fun I : (a : Fin (n + 1)) → Fin 2 ↦ ∏ a, x a (I a)) ∘
            pickCoordinate) := by
        congr 1
        funext i
        exact (prod_pairRatio_pick M p i).symm
      _ ≤ _ := hcomp
  rw [Height.logHeight_fun_prod_eq hx] at hleft
  have hscale :
      Height.logHeight (fun i ↦ M i / M p) = formHeight M := by
    have hi : (M p)⁻¹ ≠ 0 := inv_ne_zero hp
    have hs := Height.logHeight_smul_eq_logHeight M hi
    unfold formHeight
    rw [← hs]
    congr
    funext i
    simp [div_eq_mul_inv, mul_comm]
  rw [hscale] at hleft
  apply hleft.trans_eq
  apply Finset.sum_congr rfl
  intro a ha
  have hi : (M p)⁻¹ ≠ 0 := inv_ne_zero hp
  have hs := Height.logHeight_smul_eq_logHeight
    (![M p, M a] : Fin 2 → ℚ) hi
  rw [← hs]
  congr
  funext k
  fin_cases k <;> simp [x, pairRatio, div_eq_mul_inv, mul_comm, hp]

/-- In positive projective dimension, some binary coordinate pair containing
a prescribed nonzero coordinate retains at least `1 / n` of the form
height. -/
theorem exists_large_binary_coordinate {n : ℕ} (hn : 0 < n)
    (M : RatLinearForm n) (p : Fin (n + 1)) (hp : M p ≠ 0) :
    ∃ q : Fin (n + 1), q ≠ p ∧
      formHeight M ≤
        (n : ℝ) * Height.logHeight ![M p, M q] := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.erase p
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hc : s.card = 0 := by simp [hzero]
    have : s.card = n := by simp [s]
    omega
  obtain ⟨q, hqs, hqmax⟩ :=
    Finset.exists_max_image s
      (fun a ↦ Height.logHeight ![M p, M a]) hs
  refine ⟨q, (Finset.mem_erase.mp hqs).1, ?_⟩
  have hsum := formHeight_le_sum_binaryHeights M p hp
  have hpp : Height.logHeight ![M p, M p] = 0 := by
    have hi : (M p)⁻¹ ≠ 0 := inv_ne_zero hp
    have hscale := Height.logHeight_smul_eq_logHeight
      (![M p, M p] : Fin 2 → ℚ) hi
    rw [← hscale]
    convert Height.logHeight_one (K := ℚ) (ι := Fin 2) using 2 <;>
      ext i <;> fin_cases i <;> simp [hp]
  have huniv :
      (∑ a : Fin (n + 1), Height.logHeight ![M p, M a]) =
        ∑ a ∈ s, Height.logHeight ![M p, M a] := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    simp only [s, hpp, add_zero]
  rw [huniv] at hsum
  have hbound := Finset.sum_le_card_nsmul s
    (fun a ↦ Height.logHeight ![M p, M a])
    (Height.logHeight ![M p, M q]) hqmax
  have hcard : s.card = n := by simp [s]
  rw [hcard, nsmul_eq_mul] at hbound
  exact hsum.trans hbound

/-- A canonical choice of the second coordinate in the binary reduction. -/
def secondaryIndex {n : ℕ} (hn : 0 < n) (M : RatLinearForm n)
    (hM : M ≠ 0) : Fin (n + 1) :=
  Classical.choose
    (exists_large_binary_coordinate hn M (pivotIndex M hM)
      (pivotIndex_coeff_ne_zero M hM))

theorem secondaryIndex_ne_pivot {n : ℕ} (hn : 0 < n)
    (M : RatLinearForm n) (hM : M ≠ 0) :
    secondaryIndex hn M hM ≠ pivotIndex M hM :=
  (Classical.choose_spec
    (exists_large_binary_coordinate hn M (pivotIndex M hM)
      (pivotIndex_coeff_ne_zero M hM))).1

theorem formHeight_le_binaryHeight {n : ℕ} (hn : 0 < n)
    (M : RatLinearForm n) (hM : M ≠ 0) :
    formHeight M ≤ (n : ℝ) * Height.logHeight
      ![M (pivotIndex M hM), M (secondaryIndex hn M hM)] :=
  (Classical.choose_spec
    (exists_large_binary_coordinate hn M (pivotIndex M hM)
      (pivotIndex_coeff_ne_zero M hM))).2

/-- The affine zero of the selected binary form after setting the secondary
homogeneous coordinate to one. -/
def binaryRoot {n : ℕ} (hn : 0 < n) (M : RatLinearForm n)
    (hM : M ≠ 0) : ℚ :=
  -M (secondaryIndex hn M hM) / M (pivotIndex M hM)

/-- The height of the selected binary coefficient pair is the ordinary
height of its affine zero. -/
theorem logHeight_binaryRoot {n : ℕ} (hn : 0 < n)
    (M : RatLinearForm n) (hM : M ≠ 0) :
    Height.logHeight₁ (binaryRoot hn M hM) =
      Height.logHeight
        ![M (pivotIndex M hM), M (secondaryIndex hn M hM)] := by
  rw [binaryRoot, neg_div, Height.logHeight₁_neg,
    Height.logHeight₁_div_eq_logHeight]
  exact Height.logHeight_swap _ _

/-! ## Lowest-power specialization -/

/-- The least exponent of `X i` occurring in a polynomial, totalized to zero
for the zero polynomial. -/
def variableOrder {ι : Type*} (P : MvPolynomial ι ℚ) (i : ι) : ℕ :=
  if h : (P.support.image fun e ↦ e i).Nonempty then
    (P.support.image fun e ↦ e i).min' h
  else 0

/-- Remove the largest common power of `X i` and then set `X i = 0`.
Equivalently, retain precisely the terms of lowest `X i`-exponent and remove
that exponent.  This is the one-coordinate specialization used repeatedly in
the binary reduction of GLR Lemma 4.21. -/
def initialSlice {ι : Type*} (P : MvPolynomial ι ℚ) (i : ι) :
    MvPolynomial ι ℚ :=
  (P.divMonomial (Finsupp.single i (variableOrder P i))).modMonomial
    (Finsupp.single i 1)

theorem exists_support_variableOrder {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (i : ι) :
    ∃ e ∈ P.support, e i = variableOrder P i := by
  have hs := MvPolynomial.support_nonempty.mpr hP
  have hi : (P.support.image fun e ↦ e i).Nonempty := hs.image _
  have hmem := Finset.min'_mem _ hi
  obtain ⟨e, he, hei⟩ := Finset.mem_image.mp hmem
  refine ⟨e, he, ?_⟩
  rw [variableOrder, dif_pos hi]
  exact hei

private theorem single_add_sub_eq {ι : Type*} (e : ι →₀ ℕ) (i : ι)
    {a : ℕ} (ha : e i = a) :
    Finsupp.single i a + (e - Finsupp.single i a) = e := by
  apply Finsupp.ext
  intro k
  by_cases hki : k = i
  · subst k
    simp [ha]
  · simp [hki]

theorem coeff_initialSlice_of_minimal {ι : Type*}
    (P : MvPolynomial ι ℚ) (i : ι) {e : ι →₀ ℕ}
    (he : e i = variableOrder P i) :
    MvPolynomial.coeff (e - Finsupp.single i (variableOrder P i))
        (initialSlice P i) = MvPolynomial.coeff e P := by
  classical
  let K := e - Finsupp.single i (variableOrder P i)
  have hKi : K i = 0 := by simp [K, he]
  have hnle : ¬ Finsupp.single i 1 ≤ K := by
    intro h
    have := h i
    simp [hKi] at this
  rw [initialSlice, MvPolynomial.coeff_modMonomial_of_not_le _ hnle,
    MvPolynomial.coeff_divMonomial]
  exact congrArg (fun z ↦ MvPolynomial.coeff z P)
    (single_add_sub_eq e i he)

theorem initialSlice_ne_zero {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (i : ι) :
    initialSlice P i ≠ 0 := by
  obtain ⟨e, heP, he⟩ := exists_support_variableOrder hP i
  intro hz
  have hc := coeff_initialSlice_of_minimal P i he
  rw [hz, MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp heP) hc.symm

theorem support_initialSlice_apply_eq_zero {ι : Type*}
    (P : MvPolynomial ι ℚ) (i : ι) {K : ι →₀ ℕ}
    (hK : K ∈ (initialSlice P i).support) : K i = 0 := by
  by_contra hi
  have hle : Finsupp.single i 1 ≤ K := by
    simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
  have hc := MvPolynomial.coeff_modMonomial_of_le
    (P.divMonomial (Finsupp.single i (variableOrder P i))) hle
  exact (MvPolynomial.mem_support_iff.mp hK) hc

private theorem modMonomial_single_add {ι : Type*}
    (P Q : MvPolynomial ι ℚ) (i : ι) :
    (P + Q).modMonomial (Finsupp.single i 1) =
      P.modMonomial (Finsupp.single i 1) +
        Q.modMonomial (Finsupp.single i 1) := by
  classical
  ext K
  by_cases hle : Finsupp.single i 1 ≤ K
  · simp [MvPolynomial.coeff_modMonomial_of_le _ hle]
  · simp [MvPolynomial.coeff_modMonomial_of_not_le _ hle]

private theorem modMonomial_single_mul_X_of_ne {ι : Type*}
    (P : MvPolynomial ι ℚ) {i k : ι} (hki : k ≠ i) :
    (P * MvPolynomial.X k).modMonomial (Finsupp.single i 1) =
      P.modMonomial (Finsupp.single i 1) * MvPolynomial.X k := by
  classical
  ext K
  by_cases hk : k ∈ K.support
  · have hsub_i : ((K - Finsupp.single k 1) : ι →₀ ℕ) i = K i := by
      change K i - (Finsupp.single k 1) i = K i
      simp [hki]
    by_cases hle : Finsupp.single i 1 ≤ K
    · have hle' : Finsupp.single i 1 ≤ K - Finsupp.single k 1 := by
        rw [Finsupp.single_le_iff, hsub_i]
        simpa [Finsupp.single_le_iff] using hle
      rw [MvPolynomial.coeff_modMonomial_of_le _ hle,
        MvPolynomial.coeff_mul_X', if_pos hk,
        MvPolynomial.coeff_modMonomial_of_le _ hle']
    · have hnle' : ¬ Finsupp.single i 1 ≤ K - Finsupp.single k 1 := by
        rw [Finsupp.single_le_iff, hsub_i]
        simpa [Finsupp.single_le_iff] using hle
      rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle,
        MvPolynomial.coeff_mul_X', if_pos hk,
        MvPolynomial.coeff_mul_X', if_pos hk,
        MvPolynomial.coeff_modMonomial_of_not_le _ hnle']
  · by_cases hle : Finsupp.single i 1 ≤ K
    · rw [MvPolynomial.coeff_modMonomial_of_le _ hle,
        MvPolynomial.coeff_mul_X', if_neg hk]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle,
        MvPolynomial.coeff_mul_X', if_neg hk,
        MvPolynomial.coeff_mul_X', if_neg hk]

/-- Substitute zero for one variable. -/
def setVariableZero {ι : Type*} (P : MvPolynomial ι ℚ) (i : ι) :
    MvPolynomial ι ℚ := by
  classical
  exact MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k ↦ if k = i then 0 else MvPolynomial.X k) P

/-- Substituting zero for one variable agrees with remainder modulo that
variable. -/
theorem setVariableZero_eq_modMonomial {ι : Type*}
    (P : MvPolynomial ι ℚ) (i : ι) :
    setVariableZero P i = P.modMonomial (Finsupp.single i 1) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      ext K
      by_cases hle : Finsupp.single i 1 ≤ K
      · have hK : K ≠ 0 := by
          intro hz
          subst K
          simpa using hle
        have hK' : 0 ≠ K := Ne.symm hK
        simp [setVariableZero,
          MvPolynomial.coeff_modMonomial_of_le _ hle, hK']
      · simp only [setVariableZero, MvPolynomial.eval₂Hom_C]
        rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle]
  | add P Q hP hQ =>
      calc
        setVariableZero (P + Q) i =
            setVariableZero P i + setVariableZero Q i := by
          simp [setVariableZero]
        _ = P.modMonomial (Finsupp.single i 1) +
            Q.modMonomial (Finsupp.single i 1) := congrArg₂ (· + ·) hP hQ
        _ = (P + Q).modMonomial (Finsupp.single i 1) :=
          (modMonomial_single_add P Q i).symm
  | mul_X P k hP =>
      by_cases hki : k = i
      · subst k
        simp only [setVariableZero, map_mul, MvPolynomial.eval₂Hom_X', if_pos,
          mul_zero, MvPolynomial.mul_X_modMonomial]
      · simp only [setVariableZero, map_mul, MvPolynomial.eval₂Hom_X', if_neg hki]
        change setVariableZero P i * MvPolynomial.X k = _
        rw [hP, modMonomial_single_mul_X_of_ne P hki]

/-- The sum of the non-pivot terms of a linear form. -/
def offPivotPolynomial {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (j : Fin m) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  ∑ k ∈ Finset.univ.erase (pivotIndex (M j) (hM j)),
    MvPolynomial.C (M j k) * MvPolynomial.X (j, k)

/-- Express an original variable in coordinates whose pivot coordinate is
the value of the corresponding form. -/
def toFormCoordinateVar {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (i : RothIndex.BlockVar m n) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  if _hi : i.2 = pivotIndex (M i.1) (hM i.1) then
    MvPolynomial.C (M i.1 i.2)⁻¹ *
      (MvPolynomial.X i - offPivotPolynomial M hM i.1)
  else MvPolynomial.X i

/-- Send the distinguished coordinate back to its linear form. -/
def fromFormCoordinateVar {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (i : RothIndex.BlockVar m n) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  if i.2 = pivotIndex (M i.1) (hM i.1) then
    formPolynomial M i.1
  else MvPolynomial.X i

/-- Rewrite a polynomial in form-adapted coordinates. -/
def toFormCoordinates {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (toFormCoordinateVar M hM) P

/-- The inverse substitution from form-adapted coordinates. -/
def fromFormCoordinates {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM) P

private theorem formPolynomial_eq_pivot_add_off {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0) (j : Fin m) :
    formPolynomial M j =
      MvPolynomial.C (M j (pivotIndex (M j) (hM j))) *
        MvPolynomial.X (j, pivotIndex (M j) (hM j)) +
      offPivotPolynomial M hM j := by
  classical
  rw [formPolynomial, offPivotPolynomial,
    ← Finset.add_sum_erase Finset.univ
      (fun k : Fin (n + 1) ↦
        MvPolynomial.C (M j k) * MvPolynomial.X (j, k))
      (Finset.mem_univ (pivotIndex (M j) (hM j)))]

theorem from_toFormCoordinateVar {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (i : RothIndex.BlockVar m n) :
    MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM)
        (toFormCoordinateVar M hM i) = MvPolynomial.X i := by
  classical
  rcases i with ⟨j, k⟩
  by_cases hi : k = pivotIndex (M j) (hM j)
  · subst k
    rw [toFormCoordinateVar, dif_pos rfl]
    simp only [map_mul, map_sub, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', fromFormCoordinateVar, if_pos]
    have hp := pivotIndex_coeff_ne_zero (M j) (hM j)
    have hoff :
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM)
          (offPivotPolynomial M hM j) = offPivotPolynomial M hM j := by
      unfold offPivotPolynomial
      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X']
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mem_erase] at hl
      simp [fromFormCoordinateVar, hl.1]
    rw [hoff, formPolynomial_eq_pivot_add_off M hM j]
    simp only [add_sub_cancel_right, ← mul_assoc, ← map_mul]
    rw [inv_mul_cancel₀ hp]
    simp
  · simp [toFormCoordinateVar, hi, fromFormCoordinateVar]

/-- The two triangular substitutions are inverse in the direction needed
for injectivity. -/
theorem from_toFormCoordinates {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    fromFormCoordinates M hM (toFormCoordinates M hM P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [fromFormCoordinates, toFormCoordinates]
  | add P Q hP hQ =>
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM)
          (MvPolynomial.eval₂Hom MvPolynomial.C (toFormCoordinateVar M hM) P) = P at hP
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM)
          (MvPolynomial.eval₂Hom MvPolynomial.C (toFormCoordinateVar M hM) Q) = Q at hQ
      simp only [fromFormCoordinates, toFormCoordinates, map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVar M hM)
          (MvPolynomial.eval₂Hom MvPolynomial.C (toFormCoordinateVar M hM) P) = P at hP
      simp only [fromFormCoordinates, toFormCoordinates, map_mul,
        MvPolynomial.eval₂Hom_X']
      rw [hP, from_toFormCoordinateVar]

theorem toFormCoordinates_ne_zero {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (hP : P ≠ 0) : toFormCoordinates M hM P ≠ 0 := by
  intro hzero
  apply hP
  have := congrArg (fromFormCoordinates M hM) hzero
  rw [from_toFormCoordinates] at this
  simpa [fromFormCoordinates] using this

/-! The reduction to two coordinates must retain the same pivot while the
other coefficients of a form are successively set to zero.  The following
variants therefore take an explicit nonzero pivot instead of recomputing the
canonical one after every specialization. -/

def offPivotPolynomialAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (j : Fin m) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  ∑ k ∈ Finset.univ.erase (p j),
    MvPolynomial.C (M j k) * MvPolynomial.X (j, k)

def toFormCoordinateVarAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (i : RothIndex.BlockVar m n) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  if _hi : i.2 = p i.1 then
    MvPolynomial.C (M i.1 i.2)⁻¹ *
      (MvPolynomial.X i - offPivotPolynomialAt M p i.1)
  else MvPolynomial.X i

def fromFormCoordinateVarAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (i : RothIndex.BlockVar m n) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  if i.2 = p i.1 then formPolynomial M i.1 else MvPolynomial.X i

def toFormCoordinatesAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (toFormCoordinateVarAt M p) P

def fromFormCoordinatesAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p) P

private theorem formPolynomial_eq_pivot_add_offAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1)) (j : Fin m) :
    formPolynomial M j =
      MvPolynomial.C (M j (p j)) * MvPolynomial.X (j, p j) +
        offPivotPolynomialAt M p j := by
  classical
  rw [formPolynomial, offPivotPolynomialAt,
    ← Finset.add_sum_erase Finset.univ
      (fun k : Fin (n + 1) ↦
        MvPolynomial.C (M j k) * MvPolynomial.X (j, k))
      (Finset.mem_univ (p j))]

theorem from_toFormCoordinateVarAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (hp : ∀ j, M j (p j) ≠ 0)
    (i : RothIndex.BlockVar m n) :
    MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p)
        (toFormCoordinateVarAt M p i) = MvPolynomial.X i := by
  classical
  rcases i with ⟨j, k⟩
  by_cases hi : k = p j
  · subst k
    rw [toFormCoordinateVarAt, dif_pos rfl]
    simp only [map_mul, map_sub, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', fromFormCoordinateVarAt, if_pos]
    have hoff :
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p)
          (offPivotPolynomialAt M p j) =
            offPivotPolynomialAt M p j := by
      unfold offPivotPolynomialAt
      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X']
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mem_erase] at hl
      simp [fromFormCoordinateVarAt, hl.1]
    rw [hoff, formPolynomial_eq_pivot_add_offAt M p j]
    simp only [add_sub_cancel_right, ← mul_assoc, ← map_mul]
    rw [inv_mul_cancel₀ (hp j)]
    simp
  · simp [toFormCoordinateVarAt, hi, fromFormCoordinateVarAt]

theorem from_toFormCoordinatesAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (hp : ∀ j, M j (p j) ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    fromFormCoordinatesAt M p (toFormCoordinatesAt M p P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [fromFormCoordinatesAt, toFormCoordinatesAt]
  | add P Q hP hQ =>
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p)
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (toFormCoordinateVarAt M p) P) = P at hP
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p)
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (toFormCoordinateVarAt M p) Q) = Q at hQ
      simp only [fromFormCoordinatesAt, toFormCoordinatesAt, map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      change
        MvPolynomial.eval₂Hom MvPolynomial.C (fromFormCoordinateVarAt M p)
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (toFormCoordinateVarAt M p) P) = P at hP
      simp only [fromFormCoordinatesAt, toFormCoordinatesAt, map_mul,
        MvPolynomial.eval₂Hom_X']
      rw [hP, from_toFormCoordinateVarAt M p hp]

theorem toFormCoordinatesAt_ne_zero {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    toFormCoordinatesAt M p P ≠ 0 := by
  intro hzero
  apply hP
  have := congrArg (fromFormCoordinatesAt M p) hzero
  rw [from_toFormCoordinatesAt M p hp] at this
  simpa [fromFormCoordinatesAt] using this

theorem toFormCoordinates_eq_at_canonical {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    toFormCoordinates M hM P =
    toFormCoordinatesAt M (fun j ↦ pivotIndex (M j) (hM j)) P := by
  rfl

/-- Set one coefficient of one form to zero. -/
def zeroFormCoefficient {m n : ℕ} (M : FormFamily m n)
    (i : RothIndex.BlockVar m n) : FormFamily m n :=
  fun j k ↦ if (j, k) = i then 0 else M j k

@[simp] theorem zeroFormCoefficient_apply_self {m n : ℕ}
    (M : FormFamily m n) (i : RothIndex.BlockVar m n) :
    zeroFormCoefficient M i i.1 i.2 = 0 := by
  simp [zeroFormCoefficient]

theorem zeroFormCoefficient_apply_of_ne {m n : ℕ}
    (M : FormFamily m n) (i : RothIndex.BlockVar m n)
    {j : Fin m} {k : Fin (n + 1)} (h : (j, k) ≠ i) :
    zeroFormCoefficient M i j k = M j k := by
  simp [zeroFormCoefficient, h]

theorem zeroFormCoefficient_pivot_ne_zero {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0) (i : RothIndex.BlockVar m n)
    (hi : i.2 ≠ p i.1) : ∀ j, zeroFormCoefficient M i j (p j) ≠ 0 := by
  intro j
  rw [zeroFormCoefficient_apply_of_ne]
  · exact hp j
  · intro h
    cases h
    exact hi rfl

theorem setVariableZero_offPivotPolynomialAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (i : RothIndex.BlockVar m n) (hi : i.2 ≠ p i.1) (j : Fin m) :
    setVariableZero (offPivotPolynomialAt M p j) i =
      offPivotPolynomialAt (zeroFormCoefficient M i) p j := by
  classical
  unfold offPivotPolynomialAt setVariableZero
  simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : (j, k) = i
  · subst i
    simp [zeroFormCoefficient]
  · simp [zeroFormCoefficient, hki]

@[simp] theorem setVariableZero_C {ι : Type*} (c : ℚ) (i : ι) :
    setVariableZero (MvPolynomial.C c) i = MvPolynomial.C c := by
  simp [setVariableZero]

@[simp] theorem setVariableZero_X {ι : Type*} [DecidableEq ι] (v i : ι) :
    setVariableZero (MvPolynomial.X v) i =
      if v = i then 0 else MvPolynomial.X v := by
  simp [setVariableZero]

@[simp] theorem setVariableZero_add {ι : Type*}
    (P Q : MvPolynomial ι ℚ) (i : ι) :
    setVariableZero (P + Q) i = setVariableZero P i + setVariableZero Q i := by
  simp [setVariableZero]

@[simp] theorem setVariableZero_sub {ι : Type*}
    (P Q : MvPolynomial ι ℚ) (i : ι) :
    setVariableZero (P - Q) i = setVariableZero P i - setVariableZero Q i := by
  simp [setVariableZero]

@[simp] theorem setVariableZero_mul {ι : Type*}
    (P Q : MvPolynomial ι ℚ) (i : ι) :
    setVariableZero (P * Q) i = setVariableZero P i * setVariableZero Q i := by
  simp [setVariableZero]

theorem setVariableZero_toFormCoordinateVarAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (i v : RothIndex.BlockVar m n) (hi : i.2 ≠ p i.1) :
    setVariableZero (toFormCoordinateVarAt M p v) i =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (toFormCoordinateVarAt (zeroFormCoefficient M i) p)
        (setVariableZero (MvPolynomial.X v) i) := by
  classical
  rcases i with ⟨a, b⟩
  rcases v with ⟨j, k⟩
  by_cases hv : (j, k) = (a, b)
  · cases hv
    simp [setVariableZero, toFormCoordinateVarAt, hi]
  · by_cases hk : k = p j
    · subst k
      have hv' : (j, p j) ≠ (a, b) := hv
      rw [toFormCoordinateVarAt, dif_pos rfl]
      rw [setVariableZero_mul, setVariableZero_sub, setVariableZero_C,
        setVariableZero_X, if_neg hv']
      rw [setVariableZero_offPivotPolynomialAt M p (a, b) hi j]
      have hpv : zeroFormCoefficient M (a, b) j (p j) = M j (p j) :=
        zeroFormCoefficient_apply_of_ne M (a, b) hv'
      simp [hv', toFormCoordinateVarAt, hpv]
    · simp [setVariableZero, toFormCoordinateVarAt, hk, hv]

/-- Fixed-pivot form coordinates commute with setting a nonpivot variable and
the corresponding form coefficient to zero. -/
theorem setVariableZero_toFormCoordinatesAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (i : RothIndex.BlockVar m n) (hi : i.2 ≠ p i.1) :
    setVariableZero (toFormCoordinatesAt M p P) i =
      toFormCoordinatesAt (zeroFormCoefficient M i) p
        (setVariableZero P i) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [setVariableZero, toFormCoordinatesAt]
  | add P Q hP hQ =>
      rw [toFormCoordinatesAt, map_add, setVariableZero_add,
        toFormCoordinatesAt, setVariableZero_add, map_add]
      change setVariableZero (toFormCoordinatesAt M p P) i +
        setVariableZero (toFormCoordinatesAt M p Q) i = _
      rw [hP, hQ]
      rfl
  | mul_X P v hP =>
      simp only [toFormCoordinatesAt, map_mul, MvPolynomial.eval₂Hom_X',
        setVariableZero_mul]
      change setVariableZero (toFormCoordinatesAt M p P) i *
          setVariableZero (toFormCoordinateVarAt M p v) i =
        toFormCoordinatesAt (zeroFormCoefficient M i) p
            (setVariableZero P i) *
          MvPolynomial.eval₂Hom MvPolynomial.C
            (toFormCoordinateVarAt (zeroFormCoefficient M i) p)
            (setVariableZero (MvPolynomial.X v) i)
      rw [hP, setVariableZero_toFormCoordinateVarAt M p i v hi]

theorem variableOrder_le_support {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (i : ι)
    {e : ι →₀ ℕ} (he : e ∈ P.support) : variableOrder P i ≤ e i := by
  have hs := MvPolynomial.support_nonempty.mpr hP
  have hi : (P.support.image fun e ↦ e i).Nonempty := hs.image _
  rw [variableOrder, dif_pos hi]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem modMonomial_variableOrder_eq_zero {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (i : ι) :
    P.modMonomial (Finsupp.single i (variableOrder P i)) = 0 := by
  classical
  ext K
  by_cases hle : Finsupp.single i (variableOrder P i) ≤ K
  · rw [MvPolynomial.coeff_modMonomial_of_le _ hle,
      MvPolynomial.coeff_zero]
  · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle,
      MvPolynomial.coeff_zero]
    by_contra hcoeff
    have hK : K ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    apply hle
    rw [Finsupp.single_le_iff]
    exact variableOrder_le_support hP i hK

theorem factor_variableOrder {ι : Type*}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) (i : ι) :
    MvPolynomial.monomial (Finsupp.single i (variableOrder P i)) 1 *
        P.divMonomial (Finsupp.single i (variableOrder P i)) = P := by
  have h := MvPolynomial.divMonomial_add_modMonomial P
    (Finsupp.single i (variableOrder P i))
  rw [modMonomial_variableOrder_eq_zero hP i, add_zero] at h
  exact h

theorem toFormCoordinatesAt_factor_variableOrder {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (i : RothIndex.BlockVar m n) (hi : i.2 ≠ p i.1) :
    MvPolynomial.monomial (Finsupp.single i (variableOrder P i)) 1 *
        toFormCoordinatesAt M p
          (P.divMonomial (Finsupp.single i (variableOrder P i))) =
      toFormCoordinatesAt M p P := by
  let s := Finsupp.single i (variableOrder P i)
  have hsmap : toFormCoordinatesAt M p (MvPolynomial.monomial s 1) =
      MvPolynomial.monomial s 1 := by
    classical
    unfold s
    rw [← MvPolynomial.X_pow_eq_monomial]
    simp [toFormCoordinatesAt, toFormCoordinateVarAt, hi]
  rw [← hsmap]
  simp only [toFormCoordinatesAt]
  rw [← map_mul, factor_variableOrder hP i]

/-- Changing to fixed-pivot form coordinates after a lowest-power
specialization is the same as first changing coordinates and then setting
the corresponding tangential variable to zero. -/
theorem toFormCoordinatesAt_initialSlice {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (i : RothIndex.BlockVar m n) (hi : i.2 ≠ p i.1) :
    toFormCoordinatesAt (zeroFormCoefficient M i) p (initialSlice P i) =
      setVariableZero
        (toFormCoordinatesAt M p
          (P.divMonomial (Finsupp.single i (variableOrder P i)))) i := by
  rw [initialSlice, ← setVariableZero_eq_modMonomial,
    setVariableZero_toFormCoordinatesAt M p _ i hi]

theorem support_modMonomial_single_apply_eq_zero {ι : Type*}
    (P : MvPolynomial ι ℚ) (i : ι) {K : ι →₀ ℕ}
    (hK : K ∈ (P.modMonomial (Finsupp.single i 1)).support) :
    K i = 0 := by
  by_contra hi
  have hle : Finsupp.single i 1 ≤ K := by
    simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
  have hc := MvPolynomial.coeff_modMonomial_of_le P hle
  exact (MvPolynomial.mem_support_iff.mp hK) hc

/-! ## Index along a product of hyperplanes -/

/-- One normal divided-derivative order in each block. -/
abbrev FormNormalOrder (m : ℕ) := Fin m → ℕ

/-- The normalized weight of normal divided-derivative orders. -/
def formNormalWeight {m : ℕ} (d : Fin m → ℕ)
    (I : FormNormalOrder m) : ℚ :=
  ∑ j : Fin m, (I j : ℚ) / (d j : ℚ)

/-- The exponent of an adapted monomial in the coordinate represented by
the form in each block. -/
def formNormalOrderOfExponent {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (e : RothIndex.MultiIndex m n) :
    FormNormalOrder m :=
  fun j ↦ e (j, pivotIndex (M j) (hM j))

/-- The normal orders occurring after changing to form-adapted coordinates. -/
def formRestrictionOrders {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    Finset (FormNormalOrder m) :=
  (toFormCoordinates M hM P).support.image
    (formNormalOrderOfExponent M hM)

/-- The normalized weights of the occurring normal orders. -/
def formRestrictionWeights {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : Finset ℚ :=
  (formRestrictionOrders M hM P).image (formNormalWeight d)

/-- The normalized index of `P` along the product of the hyperplanes
`M j = 0`.  Equivalently, it is the least normalized normal derivative order
whose restriction to that product is nonzero. -/
def formIndex {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : ℚ :=
  if h : (formRestrictionWeights M hM P d).Nonempty then
    (formRestrictionWeights M hM P d).min' h
  else 0

/-- Normal orders and index computed using a specified nonzero pivot in each
block.  This has the same value as `formIndex`; the explicit-pivot version is
stable under the coefficient specializations used in the binary reduction. -/
def formNormalOrderOfExponentAt {m n : ℕ}
    (p : Fin m → Fin (n + 1)) (e : RothIndex.MultiIndex m n) :
    FormNormalOrder m :=
  fun j ↦ e (j, p j)

def formRestrictionOrdersAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    Finset (FormNormalOrder m) :=
  (toFormCoordinatesAt M p P).support.image (formNormalOrderOfExponentAt p)

def formRestrictionWeightsAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : Finset ℚ :=
  (formRestrictionOrdersAt M p P).image (formNormalWeight d)

def formIndexAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : ℚ :=
  if h : (formRestrictionWeightsAt M p P d).Nonempty then
    (formRestrictionWeightsAt M p P d).min' h
  else 0

theorem formIndex_eq_at_canonical {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) (d : Fin m → ℕ) :
    formIndex M hM P d =
      formIndexAt M (fun j ↦ pivotIndex (M j) (hM j)) P d := by
  rfl

theorem formRestrictionOrdersAt_nonempty {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    (formRestrictionOrdersAt M p P).Nonempty := by
  exact (MvPolynomial.support_nonempty.mpr
    (toFormCoordinatesAt_ne_zero M p hp hP)).image _

theorem formRestrictionWeightsAt_nonempty {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    (formRestrictionWeightsAt M p P d).Nonempty :=
  (formRestrictionOrdersAt_nonempty M p hp hP).image _

theorem exists_formNormalOrderAt_weight_eq_index {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    ∃ e ∈ (toFormCoordinatesAt M p P).support,
      formNormalWeight d (formNormalOrderOfExponentAt p e) =
        formIndexAt M p P d := by
  have hw := formRestrictionWeightsAt_nonempty M p hp hP d
  have hmin : (formRestrictionWeightsAt M p P d).min' hw ∈
      formRestrictionWeightsAt M p P d := Finset.min'_mem _ _
  obtain ⟨I, hI, hweight⟩ := Finset.mem_image.mp hmin
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hI
  refine ⟨e, he, ?_⟩
  rw [formIndexAt, dif_pos hw]
  exact hweight

theorem formIndexAt_le_weight {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {e : RothIndex.MultiIndex m n}
    (he : e ∈ (toFormCoordinatesAt M p P).support) :
    formIndexAt M p P d ≤
      formNormalWeight d (formNormalOrderOfExponentAt p e) := by
  have hw := formRestrictionWeightsAt_nonempty M p hp hP d
  rw [formIndexAt, dif_pos hw]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨e, he, rfl⟩, rfl⟩

/-- Lowest-power specialization in a nonpivot variable cannot decrease the
form index.  This is the precise monotonicity needed to pass from all
projective coordinates to the selected binary coordinates. -/
theorem formIndexAt_le_initialSlice {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (i : RothIndex.BlockVar m n)
    (hi : i.2 ≠ p i.1) :
    formIndexAt M p P d ≤
      formIndexAt (zeroFormCoefficient M i) p (initialSlice P i) d := by
  let P' := initialSlice P i
  let M' := zeroFormCoefficient M i
  have hP' : P' ≠ 0 := initialSlice_ne_zero hP i
  have hp' : ∀ j, M' j (p j) ≠ 0 :=
    zeroFormCoefficient_pivot_ne_zero M p hp i hi
  obtain ⟨K, hK, hKw⟩ :=
    exists_formNormalOrderAt_weight_eq_index M' p hp' hP' d
  let R := P.divMonomial (Finsupp.single i (variableOrder P i))
  have hcomm : toFormCoordinatesAt M' p P' =
      setVariableZero (toFormCoordinatesAt M p R) i := by
    exact toFormCoordinatesAt_initialSlice M p P i hi
  have hKzero : K i = 0 := by
    rw [hcomm, setVariableZero_eq_modMonomial] at hK
    exact support_modMonomial_single_apply_eq_zero
      (toFormCoordinatesAt M p R) i hK
  have hKQ : K ∈ (toFormCoordinatesAt M p R).support := by
    rw [hcomm, setVariableZero_eq_modMonomial] at hK
    rw [MvPolynomial.mem_support_iff] at hK ⊢
    have hnle : ¬ Finsupp.single i 1 ≤ K := by
      intro h
      have := h i
      simp [hKzero] at this
    rwa [MvPolynomial.coeff_modMonomial_of_not_le _ hnle] at hK
  let s := Finsupp.single i (variableOrder P i)
  have hSK : s + K ∈ (toFormCoordinatesAt M p P).support := by
    rw [← toFormCoordinatesAt_factor_variableOrder M p hP i hi,
      MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul]
    simpa [s] using MvPolynomial.mem_support_iff.mp hKQ
  have hnormal : formNormalOrderOfExponentAt p (s + K) =
      formNormalOrderOfExponentAt p K := by
    funext j
    have hj : (j, p j) ≠ i := by
      intro h
      cases h
      exact hi rfl
    simp [formNormalOrderOfExponentAt, s, hj]
  have hle := formIndexAt_le_weight M p hp hP d hSK
  rw [hnormal, hKw] at hle
  exact hle

/-! ## Iterated specialization -/

/-- Successively retain the lowest-power slice in the listed variables. -/
def specializePolynomial {m n : ℕ}
    (L : List (RothIndex.BlockVar m n))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  L.foldl initialSlice P

/-- Set the corresponding coefficients of all forms to zero. -/
def specializeForms {m n : ℕ}
    (L : List (RothIndex.BlockVar m n)) (M : FormFamily m n) :
    FormFamily m n :=
  L.foldl zeroFormCoefficient M

@[simp] theorem specializePolynomial_nil {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    specializePolynomial [] P = P := rfl

@[simp] theorem specializeForms_nil {m n : ℕ} (M : FormFamily m n) :
    specializeForms [] M = M := rfl

@[simp] theorem specializePolynomial_cons {m n : ℕ}
    (i : RothIndex.BlockVar m n) (L : List (RothIndex.BlockVar m n))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    specializePolynomial (i :: L) P =
      specializePolynomial L (initialSlice P i) := by
  simp [specializePolynomial]

@[simp] theorem specializeForms_cons {m n : ℕ}
    (i : RothIndex.BlockVar m n) (L : List (RothIndex.BlockVar m n))
    (M : FormFamily m n) :
    specializeForms (i :: L) M =
      specializeForms L (zeroFormCoefficient M i) := by
  simp [specializeForms]

theorem specializePolynomial_ne_zero {m n : ℕ}
    (L : List (RothIndex.BlockVar m n))
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    specializePolynomial L P ≠ 0 := by
  induction L generalizing P with
  | nil => exact hP
  | cons i L ih =>
      rw [specializePolynomial_cons]
      exact ih (initialSlice_ne_zero hP i)

theorem specializeForms_pivot_ne_zero {m n : ℕ}
    (L : List (RothIndex.BlockVar m n)) (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (hp : ∀ j, M j (p j) ≠ 0)
    (hL : ∀ i ∈ L, i.2 ≠ p i.1) :
    ∀ j, specializeForms L M j (p j) ≠ 0 := by
  induction L generalizing M with
  | nil => exact hp
  | cons i L ih =>
      rw [specializeForms_cons]
      apply ih (M := zeroFormCoefficient M i)
        (zeroFormCoefficient_pivot_ne_zero M p hp i (hL i (by simp)))
      intro k hk
      exact hL k (by simp [hk])

/-- Iterating lowest-power specialization over any list of nonpivot variables
cannot decrease the form index. -/
theorem formIndexAt_le_specialize {m n : ℕ}
    (L : List (RothIndex.BlockVar m n))
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (hL : ∀ i ∈ L, i.2 ≠ p i.1) :
    formIndexAt M p P d ≤
      formIndexAt (specializeForms L M) p (specializePolynomial L P) d := by
  induction L generalizing M P with
  | nil => simp
  | cons i L ih =>
      rw [specializeForms_cons, specializePolynomial_cons]
      apply le_trans (formIndexAt_le_initialSlice M p hp hP d i
        (hL i (by simp)))
      apply ih
      · exact zeroFormCoefficient_pivot_ne_zero M p hp i (hL i (by simp))
      · exact initialSlice_ne_zero hP i
      · intro k hk
        exact hL k (by simp [hk])

/-- All variables other than the chosen pivot and secondary coordinate in
each block. -/
def discardedVariables {m n : ℕ} (p q : Fin m → Fin (n + 1)) :
    List (RothIndex.BlockVar m n) :=
  (Finset.univ.filter fun i ↦ i.2 ≠ p i.1 ∧ i.2 ≠ q i.1).toList

theorem mem_discardedVariables_iff {m n : ℕ}
    (p q : Fin m → Fin (n + 1)) (i : RothIndex.BlockVar m n) :
    i ∈ discardedVariables p q ↔
      i.2 ≠ p i.1 ∧ i.2 ≠ q i.1 := by
  simp [discardedVariables]

theorem specializeForms_apply {m n : ℕ}
    (L : List (RothIndex.BlockVar m n)) (M : FormFamily m n)
    (j : Fin m) (k : Fin (n + 1)) :
    specializeForms L M j k = if (j, k) ∈ L then 0 else M j k := by
  induction L generalizing M with
  | nil => simp
  | cons i L ih =>
      rw [specializeForms_cons, ih]
      by_cases hmem : (j, k) ∈ L
      · simp [hmem]
      · simp [hmem, zeroFormCoefficient]

theorem support_initialSlice_zero_of_support_zero {ι : Type*}
    (P : MvPolynomial ι ℚ) (i k : ι)
    (hzero : ∀ e ∈ P.support, e k = 0)
    {K : ι →₀ ℕ} (hK : K ∈ (initialSlice P i).support) : K k = 0 := by
  by_cases hki : k = i
  · subst k
    exact support_initialSlice_apply_eq_zero P i hK
  · have hKi : K i = 0 := support_initialSlice_apply_eq_zero P i hK
    have hnle : ¬ Finsupp.single i 1 ≤ K := by
      intro h
      have := h i
      simp [hKi] at this
    have hcoeff : MvPolynomial.coeff
        (Finsupp.single i (variableOrder P i) + K) P ≠ 0 := by
      have h := MvPolynomial.mem_support_iff.mp hK
      rw [initialSlice, MvPolynomial.coeff_modMonomial_of_not_le _ hnle,
        MvPolynomial.coeff_divMonomial] at h
      exact h
    have hsupp : Finsupp.single i (variableOrder P i) + K ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hz := hzero _ hsupp
    simpa [hki] using hz

/-- Every variable which has been specialized away has exponent zero in all
remaining monomials. -/
theorem support_specializePolynomial_zero_of_mem {m n : ℕ}
    (L : List (RothIndex.BlockVar m n))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {i : RothIndex.BlockVar m n} (hi : i ∈ L)
    {K : RothIndex.MultiIndex m n}
    (hK : K ∈ (specializePolynomial L P).support) : K i = 0 := by
  have preserve : ∀ (T : List (RothIndex.BlockVar m n))
      (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ),
      (∀ e ∈ Q.support, e i = 0) →
      ∀ {e}, e ∈ (specializePolynomial T Q).support → e i = 0 := by
    intro T
    induction T with
    | nil => simpa
    | cons a T ih =>
        intro Q hzero e he
        rw [specializePolynomial_cons] at he
        apply ih (initialSlice Q a)
        · intro f hf
          exact support_initialSlice_zero_of_support_zero Q a i hzero hf
        · exact he
  obtain ⟨A, T, rfl⟩ := List.append_of_mem hi
  rw [specializePolynomial, List.foldl_append] at hK
  change K ∈ (specializePolynomial T
    (initialSlice (specializePolynomial A P) i)).support at hK
  apply preserve T (initialSlice (specializePolynomial A P) i)
  · intro e he
    exact support_initialSlice_apply_eq_zero _ i he
  · exact hK

/-! ## Homogeneity through binary specialization -/

/-- All occurring monomials have the same total degree in each block.  This
weaker form of multihomogeneity is stable under taking lowest-power slices,
even though the resulting block degrees need not be the original `d`. -/
def HasConstantBlockOrders {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) : Prop :=
  ∀ ⦃e f : RothIndex.MultiIndex m n⦄, e ∈ P.support →
    f ∈ P.support → ∀ j : Fin m,
      RothIndex.blockOrder e j = RothIndex.blockOrder f j

theorem hasConstantBlockOrders_of_isMultiHomogeneous {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d) :
    HasConstantBlockOrders P := by
  intro e f he hf j
  rw [hP.of_mem_support he j, hP.of_mem_support hf j]

theorem blockOrder_add {m n : ℕ} (e f : RothIndex.MultiIndex m n)
    (j : Fin m) :
    RothIndex.blockOrder (e + f) j =
      RothIndex.blockOrder e j + RothIndex.blockOrder f j := by
  simp [RothIndex.blockOrder, Finset.sum_add_distrib]

/-- Every monomial of a lowest-power slice lifts, after restoring the common
power, to a monomial of the original polynomial. -/
theorem add_variableOrder_mem_support {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (i : RothIndex.BlockVar m n) {K : RothIndex.MultiIndex m n}
    (hK : K ∈ (initialSlice P i).support) :
    Finsupp.single i (variableOrder P i) + K ∈ P.support := by
  have hKi : K i = 0 := support_initialSlice_apply_eq_zero P i hK
  have hnle : ¬ Finsupp.single i 1 ≤ K := by
    intro h
    have := h i
    simp [hKi] at this
  rw [MvPolynomial.mem_support_iff] at hK ⊢
  rw [initialSlice, MvPolynomial.coeff_modMonomial_of_not_le _ hnle,
    MvPolynomial.coeff_divMonomial] at hK
  exact hK

theorem coeff_initialSlice_of_support {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (i : RothIndex.BlockVar m n) {K : RothIndex.MultiIndex m n}
    (hK : K ∈ (initialSlice P i).support) :
    MvPolynomial.coeff K (initialSlice P i) =
      MvPolynomial.coeff
        (Finsupp.single i (variableOrder P i) + K) P := by
  have hKi : K i = 0 := support_initialSlice_apply_eq_zero P i hK
  have hnle : ¬ Finsupp.single i 1 ≤ K := by
    intro h
    have := h i
    simp [hKi] at this
  rw [initialSlice, MvPolynomial.coeff_modMonomial_of_not_le _ hnle,
    MvPolynomial.coeff_divMonomial]

theorem le_add_variableOrder {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (i : RothIndex.BlockVar m n) (K : RothIndex.MultiIndex m n) :
    K ≤ Finsupp.single i (variableOrder P i) + K := by
  intro a
  simp only [Finsupp.add_apply]
  exact Nat.le_add_left _ _

theorem HasConstantBlockOrders.initialSlice {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (hP : HasConstantBlockOrders P) (i : RothIndex.BlockVar m n) :
    HasConstantBlockOrders (initialSlice P i) := by
  intro e f he hf j
  have he' := add_variableOrder_mem_support P i he
  have hf' := add_variableOrder_mem_support P i hf
  have hord := hP he' hf' j
  rw [blockOrder_add, blockOrder_add] at hord
  exact Nat.add_left_cancel hord

theorem HasConstantBlockOrders.specializePolynomial {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (hP : HasConstantBlockOrders P)
    (L : List (RothIndex.BlockVar m n)) :
    HasConstantBlockOrders (specializePolynomial L P) := by
  induction L generalizing P with
  | nil => exact hP
  | cons i L ih =>
      rw [specializePolynomial_cons]
      exact ih (hP.initialSlice i)

/-- Every coefficient surviving a sequence of lowest-power slices is an
unchanged coefficient of a componentwise larger monomial of the original
polynomial. -/
theorem exists_support_coeff_eq_of_specializePolynomial {m n : ℕ}
    (L : List (RothIndex.BlockVar m n))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {K : RothIndex.MultiIndex m n}
    (hK : K ∈ (specializePolynomial L P).support) :
    ∃ e ∈ P.support,
      MvPolynomial.coeff K (specializePolynomial L P) =
        MvPolynomial.coeff e P ∧ K ≤ e := by
  induction L generalizing P with
  | nil =>
      exact ⟨K, hK, rfl, le_rfl⟩
  | cons i L ih =>
      rw [specializePolynomial_cons] at hK
      obtain ⟨e, he, hcoeff, hKe⟩ := ih (initialSlice P i) hK
      let e' := Finsupp.single i (variableOrder P i) + e
      have he' : e' ∈ P.support := add_variableOrder_mem_support P i he
      refine ⟨e', he', ?_, hKe.trans ?_⟩
      · rw [specializePolynomial_cons, hcoeff]
        exact coeff_initialSlice_of_support P i he
      · exact le_add_variableOrder P i e

/-! ## Dehomogenizing a binary specialization -/

/-- Retain the exponent of the chosen affine coordinate in each block. -/
def affineExponentAt {m n : ℕ} (p : Fin m → Fin (n + 1))
    (e : RothIndex.MultiIndex m n) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ e (j, p j))

@[simp] theorem affineExponentAt_apply {m n : ℕ}
    (p : Fin m → Fin (n + 1)) (e : RothIndex.MultiIndex m n)
    (j : Fin m) : affineExponentAt p e j = e (j, p j) := by
  simp [affineExponentAt]

/-- Dehomogenize a polynomial supported on two chosen coordinates in every
block by setting the second coordinate to one.  The sum-over-support
definition makes the coefficient reindexing explicit. -/
def affineSpecialization {m n : ℕ} (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (Fin m) ℚ :=
  ∑ e ∈ P.support,
    MvPolynomial.monomial (affineExponentAt p e) (MvPolynomial.coeff e P)

/-- Set every non-affine homogeneous coordinate to one. -/
def dehomogenizeAt {m n : ℕ} (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (Fin m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ if i.2 = p i.1 then MvPolynomial.X i.1 else 1) P

theorem dehomogenizeAt_monomial {m n : ℕ}
    (p : Fin m → Fin (n + 1)) (e : RothIndex.MultiIndex m n) (c : ℚ) :
    dehomogenizeAt p (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (affineExponentAt p e) c := by
  classical
  rw [dehomogenizeAt, MvPolynomial.eval₂Hom_monomial,
    MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.prod_eq_single (p j)]
    · simp [affineExponentAt]
    · intro k hk hkp
      simp [hkp]
    · simp
  · intro j
    simp
  · intro i
    simp

theorem dehomogenizeAt_eq_affineSpecialization {m n : ℕ}
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    dehomogenizeAt p P = affineSpecialization p P := by
  classical
  conv_lhs => rw [P.as_sum]
  unfold dehomogenizeAt
  rw [map_sum]
  unfold affineSpecialization
  apply Finset.sum_congr rfl
  intro e he
  exact dehomogenizeAt_monomial p e _

/-- The affine substitution induced by the fixed-pivot form coordinates. -/
def affineFormSubstitutionAt {m n : ℕ} (M : FormFamily m n)
    (p : Fin m → Fin (n + 1)) (j : Fin m) :
    MvPolynomial (Fin m) ℚ :=
  MvPolynomial.C (M j (p j))⁻¹ *
    (MvPolynomial.X j -
      MvPolynomial.C (∑ k ∈ Finset.univ.erase (p j), M j k))

theorem dehomogenizeAt_toFormCoordinateVarAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (i : RothIndex.BlockVar m n) :
    dehomogenizeAt p (toFormCoordinateVarAt M p i) =
      MvPolynomial.eval₂Hom MvPolynomial.C (affineFormSubstitutionAt M p)
        (dehomogenizeAt p (MvPolynomial.X i)) := by
  rcases i with ⟨j, k⟩
  by_cases hk : k = p j
  · subst k
    simp only [dehomogenizeAt, MvPolynomial.eval₂Hom_X', Prod.fst,
      Prod.snd, if_pos rfl]
    rw [toFormCoordinateVarAt, dif_pos rfl, map_mul, map_sub,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', if_pos rfl]
    rw [show MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : RothIndex.BlockVar m n ↦
            if i.2 = p i.1 then MvPolynomial.X i.1 else 1)
          (offPivotPolynomialAt M p j) =
        MvPolynomial.C (∑ l ∈ Finset.univ.erase (p j), M j l) by
      unfold offPivotPolynomialAt
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hlp := (Finset.mem_erase.mp hl).1
      simp [hlp]]
    simp [affineFormSubstitutionAt]
  · simp [dehomogenizeAt, toFormCoordinateVarAt, hk]

/-- Changing to form coordinates and then dehomogenizing is the affine
substitution obtained by solving each form for its pivot coordinate. -/
theorem dehomogenizeAt_toFormCoordinatesAt {m n : ℕ}
    (M : FormFamily m n) (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    dehomogenizeAt p (toFormCoordinatesAt M p P) =
      MvPolynomial.eval₂Hom MvPolynomial.C (affineFormSubstitutionAt M p)
        (dehomogenizeAt p P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dehomogenizeAt, toFormCoordinatesAt]
  | add P Q hP hQ =>
      simpa only [toFormCoordinatesAt, map_add, dehomogenizeAt] using
        congrArg₂ (fun A B ↦ A + B) hP hQ
  | mul_X P i hP =>
      simpa only [toFormCoordinatesAt, map_mul,
        MvPolynomial.eval₂Hom_X', dehomogenizeAt] using
        congrArg₂ (fun A B ↦ A * B) hP
          (dehomogenizeAt_toFormCoordinateVarAt M p i)

/-! ## Nonzero diagonal scaling -/

def scaleVariables {m : ℕ} (a : Fin m → ℚ)
    (P : MvPolynomial (Fin m) ℚ) : MvPolynomial (Fin m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j ↦ MvPolynomial.C (a j) * MvPolynomial.X j) P

def scaleFactor {m : ℕ} (a : Fin m → ℚ) (e : Fin m →₀ ℕ) : ℚ :=
  e.prod fun j k ↦ a j ^ k

theorem scaleVariables_monomial {m : ℕ} (a : Fin m → ℚ)
    (e : Fin m →₀ ℕ) (c : ℚ) :
    scaleVariables a (MvPolynomial.monomial e c) =
      MvPolynomial.monomial e (scaleFactor a e * c) := by
  rw [scaleVariables, MvPolynomial.eval₂Hom_monomial,
    MvPolynomial.monomial_eq]
  simp only [mul_pow, map_mul, MvPolynomial.C_pow]
  rw [Finsupp.prod_mul]
  simp [scaleFactor, MvPolynomial.monomial_eq]
  ring

theorem coeff_scaleVariables {m : ℕ} (a : Fin m → ℚ)
    (P : MvPolynomial (Fin m) ℚ) (J : Fin m →₀ ℕ) :
    MvPolynomial.coeff J (scaleVariables a P) =
      scaleFactor a J * MvPolynomial.coeff J P := by
  classical
  conv_lhs => rw [P.as_sum]
  unfold scaleVariables
  rw [map_sum, MvPolynomial.coeff_sum]
  by_cases hJ : J ∈ P.support
  · rw [Finset.sum_eq_single J]
    · rw [show MvPolynomial.eval₂Hom MvPolynomial.C
            (fun j ↦ MvPolynomial.C (a j) * MvPolynomial.X j)
            (MvPolynomial.monomial J (MvPolynomial.coeff J P)) =
          MvPolynomial.monomial J
            (scaleFactor a J * MvPolynomial.coeff J P) by
        exact scaleVariables_monomial a J _]
      simp
    · intro K hK hKJ
      rw [show MvPolynomial.eval₂Hom MvPolynomial.C
            (fun j ↦ MvPolynomial.C (a j) * MvPolynomial.X j)
            (MvPolynomial.monomial K (MvPolynomial.coeff K P)) =
          MvPolynomial.monomial K
            (scaleFactor a K * MvPolynomial.coeff K P) by
        exact scaleVariables_monomial a K _]
      simp [hKJ]
    · exact fun h ↦ (h hJ).elim
  · have hc : MvPolynomial.coeff J P = 0 := by
      by_contra hc
      exact hJ (MvPolynomial.mem_support_iff.mpr hc)
    rw [hc, mul_zero]
    apply Finset.sum_eq_zero
    intro K hK
    rw [show MvPolynomial.eval₂Hom MvPolynomial.C
          (fun j ↦ MvPolynomial.C (a j) * MvPolynomial.X j)
          (MvPolynomial.monomial K (MvPolynomial.coeff K P)) =
        MvPolynomial.monomial K
          (scaleFactor a K * MvPolynomial.coeff K P) by
      exact scaleVariables_monomial a K _]
    simp [show K ≠ J by intro h; subst K; exact hJ hK]

theorem scaleFactor_ne_zero {m : ℕ} {a : Fin m → ℚ}
    (ha : ∀ j, a j ≠ 0) (e : Fin m →₀ ℕ) : scaleFactor a e ≠ 0 := by
  rw [scaleFactor, Finsupp.prod_ne_zero_iff]
  intro j hj
  exact pow_ne_zero _ (ha j)

theorem support_scaleVariables {m : ℕ} {a : Fin m → ℚ}
    (ha : ∀ j, a j ≠ 0) (P : MvPolynomial (Fin m) ℚ) :
    (scaleVariables a P).support = P.support := by
  ext J
  simp only [MvPolynomial.mem_support_iff, coeff_scaleVariables]
  exact mul_ne_zero_iff_left (scaleFactor_ne_zero ha J)

theorem scaleVariables_translate {m : ℕ} (a β : Fin m → ℚ)
    (P : MvPolynomial (Fin m) ℚ) :
    scaleVariables a (RothIndex.translate β P) =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun j ↦ MvPolynomial.C (a j) * MvPolynomial.X j +
          MvPolynomial.C (β j)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scaleVariables]
  | add P Q hP hQ =>
      rw [RothIndex.translate_add]
      simpa only [scaleVariables, map_add] using
        congrArg₂ (fun A B ↦ A + B) hP hQ
  | mul_X P j hP =>
      rw [RothIndex.translate_mul, RothIndex.translate_X]
      have hv : scaleVariables a
          (MvPolynomial.X j + MvPolynomial.C (β j)) =
          MvPolynomial.C (a j) * MvPolynomial.X j +
            MvPolynomial.C (β j) := by
        simp [scaleVariables]
      simpa only [scaleVariables, map_mul, MvPolynomial.eval₂Hom_X'] using
        congrArg₂ (fun A B ↦ A * B) hP hv

theorem offPivotSum_specializeForms_discarded {m n : ℕ}
    (M : FormFamily m n) (p q : Fin m → Fin (n + 1))
    (hpq : ∀ j, q j ≠ p j) (j : Fin m) :
    (∑ k ∈ Finset.univ.erase (p j),
      specializeForms (discardedVariables p q) M j k) = M j (q j) := by
  rw [Finset.sum_eq_single (q j)]
  · rw [specializeForms_apply]
    simp [mem_discardedVariables_iff, hpq j]
  · intro k hk hkq
    have hkp : k ≠ p j := (Finset.mem_erase.mp hk).1
    rw [specializeForms_apply]
    simp [mem_discardedVariables_iff, hkp, hkq]
  · simp [hpq j]

/-- The binary form root for specified pivot and secondary coordinates. -/
def binaryRootAt {m n : ℕ} (M : FormFamily m n)
    (p q : Fin m → Fin (n + 1)) : Fin m → ℚ :=
  fun j ↦ -M j (q j) / M j (p j)

def binarySpecializedPolynomial {m n : ℕ}
    (p q : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :=
  specializePolynomial (discardedVariables p q) P

def binarySpecializedForms {m n : ℕ}
    (p q : Fin m → Fin (n + 1)) (M : FormFamily m n) :=
  specializeForms (discardedVariables p q) M

def affineBinarySpecialization {m n : ℕ}
    (p q : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :=
  affineSpecialization p (binarySpecializedPolynomial p q P)

/-- The adapted binary polynomial dehomogenizes to the raw affine binary
specialization translated to the form root and scaled by nonzero pivot
coefficients. -/
theorem dehomogenize_binary_toForm_eq_scale_translate {m n : ℕ}
    (M : FormFamily m n) (p q : Fin m → Fin (n + 1))
    (hpq : ∀ j, q j ≠ p j)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    dehomogenizeAt p
        (toFormCoordinatesAt (binarySpecializedForms p q M) p
          (binarySpecializedPolynomial p q P)) =
      scaleVariables (fun j ↦ (M j (p j))⁻¹)
        (RothIndex.translate (binaryRootAt M p q)
          (affineBinarySpecialization p q P)) := by
  rw [dehomogenizeAt_toFormCoordinatesAt,
    dehomogenizeAt_eq_affineSpecialization, scaleVariables_translate]
  unfold affineBinarySpecialization
  apply congrArg (fun f : Fin m → MvPolynomial (Fin m) ℚ ↦
    MvPolynomial.eval₂Hom MvPolynomial.C f
      (affineSpecialization p (binarySpecializedPolynomial p q P)))
  funext j
  rw [affineFormSubstitutionAt]
  change MvPolynomial.C
        (binarySpecializedForms p q M j (p j))⁻¹ *
      (MvPolynomial.X j - MvPolynomial.C
        (∑ k ∈ Finset.univ.erase (p j),
          binarySpecializedForms p q M j k)) = _
  have hpN : binarySpecializedForms p q M j (p j) = M j (p j) := by
    rw [binarySpecializedForms, specializeForms_apply]
    simp [mem_discardedVariables_iff]
  have hsum :
      (∑ k ∈ Finset.univ.erase (p j),
        binarySpecializedForms p q M j k) = M j (q j) := by
    exact offPivotSum_specializeForms_discarded M p q hpq j
  rw [hpN, hsum]
  simp only [binaryRootAt, div_eq_mul_inv, map_neg, map_mul]
  ring

def selectedPivot {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) : Fin m → Fin (n + 1) :=
  fun j ↦ pivotIndex (M j) (hM j)

def selectedSecondary {m n : ℕ} (hn : 0 < n) (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) : Fin m → Fin (n + 1) :=
  fun j ↦ secondaryIndex hn (M j) (hM j)

def selectedAffinePolynomial {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (Fin m) ℚ :=
  affineBinarySpecialization (selectedPivot M hM)
    (selectedSecondary hn M hM) P

def selectedRoots {m n : ℕ} (hn : 0 < n) (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) : Fin m → ℚ :=
  fun j ↦ binaryRoot hn (M j) (hM j)

/-- On a polynomial whose support uses only `p` and `q`, constant block
orders ensure that dehomogenization is injective on the support. -/
theorem affineExponentAt_injOn_binarySupport {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (p q : Fin m → Fin (n + 1)) (hpq : ∀ j, q j ≠ p j)
    (hbinary : ∀ {e}, e ∈ P.support → ∀ i,
      i.2 ≠ p i.1 → i.2 ≠ q i.1 → e i = 0)
    (horders : HasConstantBlockOrders P) :
    Set.InjOn (affineExponentAt p) P.support := by
  intro e he f hf hef
  apply Finsupp.ext
  intro i
  rcases i with ⟨j, k⟩
  by_cases hkp : k = p j
  · subst k
    have := DFunLike.congr_fun hef j
    simpa using this
  by_cases hkq : k = q j
  · subst k
    have htotal := horders he hf j
    unfold RothIndex.blockOrder at htotal
    have hrest :
        (∑ a ∈ (Finset.univ.erase (q j)), e (j, a)) =
          ∑ a ∈ (Finset.univ.erase (q j)), f (j, a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haq : a ≠ q j := (Finset.mem_erase.mp ha).1
      by_cases hap : a = p j
      · subst a
        have := DFunLike.congr_fun hef j
        simpa using this
      · rw [hbinary he (j, a) hap haq, hbinary hf (j, a) hap haq]
    have heq :
        e (j, q j) + ∑ a ∈ (Finset.univ.erase (q j)), e (j, a) =
          f (j, q j) + ∑ a ∈ (Finset.univ.erase (q j)), f (j, a) := by
      calc
        e (j, q j) + ∑ a ∈ (Finset.univ.erase (q j)), e (j, a) =
            ∑ a, e (j, a) := by
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (q j))]
              ac_rfl
        _ = ∑ a, f (j, a) := htotal
        _ = f (j, q j) +
            ∑ a ∈ (Finset.univ.erase (q j)), f (j, a) := by
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (q j))]
              ac_rfl
    rw [hrest] at heq
    exact Nat.add_right_cancel heq
  · rw [hbinary he (j, k) hkp hkq, hbinary hf (j, k) hkp hkq]

theorem affineExponentAt_injOn_specializePolynomial {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (p q : Fin m → Fin (n + 1)) (hpq : ∀ j, q j ≠ p j)
    (horders : HasConstantBlockOrders P) :
    Set.InjOn (affineExponentAt p)
      (specializePolynomial (discardedVariables p q) P).support := by
  apply affineExponentAt_injOn_binarySupport p q hpq
  · intro e he i hip hiq
    apply support_specializePolynomial_zero_of_mem
      (discardedVariables p q) P
    · exact (mem_discardedVariables_iff p q i).2 ⟨hip, hiq⟩
    · exact he
  · exact horders.specializePolynomial _

theorem coeff_affineSpecialization {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (p : Fin m → Fin (n + 1))
    (hinj : Set.InjOn (affineExponentAt p) P.support)
    {e : RothIndex.MultiIndex m n} (he : e ∈ P.support) :
    MvPolynomial.coeff (affineExponentAt p e) (affineSpecialization p P) =
      MvPolynomial.coeff e P := by
  classical
  unfold affineSpecialization
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hne : affineExponentAt p f ≠ affineExponentAt p e := by
      intro haf
      exact hfe (hinj hf he haf)
    simp [hne]
  · exact fun h ↦ (h he).elim

theorem support_affineSpecialization {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    (p : Fin m → Fin (n + 1))
    (hinj : Set.InjOn (affineExponentAt p) P.support) :
    (affineSpecialization p P).support =
      P.support.image (affineExponentAt p) := by
  classical
  ext J
  constructor
  · intro hJ
    have hc : MvPolynomial.coeff J (affineSpecialization p P) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hJ
    have hex : ∃ e ∈ P.support, affineExponentAt p e = J := by
      by_contra h
      push Not at h
      apply hc
      unfold affineSpecialization
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro e he
      simp [h e he]
    obtain ⟨e, he, rfl⟩ := hex
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · intro hJ
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hJ
    rw [MvPolynomial.mem_support_iff,
      coeff_affineSpecialization p hinj he]
    exact MvPolynomial.mem_support_iff.mp he

theorem exists_support_affineExponentAt_of_mem_affineSpecialization {m n : ℕ}
    (p : Fin m → Fin (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {J : Fin m →₀ ℕ} (hJ : J ∈ (affineSpecialization p P).support) :
    ∃ e ∈ P.support, affineExponentAt p e = J := by
  have hc : MvPolynomial.coeff J (affineSpecialization p P) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hJ
  by_contra h
  push Not at h
  apply hc
  unfold affineSpecialization
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro e he
  simp [h e he]

theorem affineSpecialization_ne_zero {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (p : Fin m → Fin (n + 1))
    (hinj : Set.InjOn (affineExponentAt p) P.support) :
    affineSpecialization p P ≠ 0 := by
  have hs : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  apply MvPolynomial.support_nonempty.mp
  rw [support_affineSpecialization p hinj]
  exact hs.image _

theorem degreeOf_affineSpecialization_le {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d)
    (p : Fin m → Fin (n + 1))
    (hinj : Set.InjOn (affineExponentAt p) P.support) (j : Fin m) :
    (affineSpecialization p P).degreeOf j ≤ d j := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro J hJ
  rw [support_affineSpecialization p hinj] at hJ
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hJ
  rw [affineExponentAt_apply]
  calc
    e (j, p j) ≤ RothIndex.blockOrder e j := by
      unfold RothIndex.blockOrder
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun k : Fin (n + 1) ↦ e (j, k))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (p j))
    _ = d j := hP.of_mem_support he j

theorem exists_original_coeff_eq_affineSpecialization_specialize {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (p q : Fin m → Fin (n + 1)) (hpq : ∀ j, q j ≠ p j)
    (horders : HasConstantBlockOrders P) {J : Fin m →₀ ℕ}
    (hJ : J ∈ (affineSpecialization p
      (specializePolynomial (discardedVariables p q) P)).support) :
    ∃ e ∈ P.support,
      MvPolynomial.coeff J (affineSpecialization p
        (specializePolynomial (discardedVariables p q) P)) =
        MvPolynomial.coeff e P := by
  let S := specializePolynomial (discardedVariables p q) P
  have hinj : Set.InjOn (affineExponentAt p) S.support :=
    affineExponentAt_injOn_specializePolynomial P p q hpq horders
  rw [support_affineSpecialization p hinj] at hJ
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨e, he, hcoeff, -⟩ :=
    exists_support_coeff_eq_of_specializePolynomial
      (discardedVariables p q) P hK
  refine ⟨e, he, ?_⟩
  rw [coeff_affineSpecialization p hinj hK, hcoeff]

/-- Lowest-slice specialization and dehomogenization only select and reindex
coefficients, so their projective coefficient height cannot increase. -/
theorem projectiveCoeffHeight_affineSpecialization_specialize_le {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (p q : Fin m → Fin (n + 1)) (hpq : ∀ j, q j ≠ p j)
    (horders : HasConstantBlockOrders P) :
    PolynomialHeights.projectiveCoeffHeight
      (affineSpecialization p
        (specializePolynomial (discardedVariables p q) P)) ≤
      PolynomialHeights.projectiveCoeffHeight P := by
  let Q := affineSpecialization p
    (specializePolynomial (discardedVariables p q) P)
  have hex : ∀ J : Q.support, ∃ e : P.support,
      MvPolynomial.coeff J Q = MvPolynomial.coeff e P := by
    intro J
    obtain ⟨e, he, hc⟩ :=
      exists_original_coeff_eq_affineSpecialization_specialize
        P p q hpq horders J.2
    exact ⟨⟨e, he⟩, hc⟩
  let f : Q.support → P.support := fun J ↦ Classical.choose (hex J)
  let c : Q.support → ℚ := fun _ ↦ 1
  have hc : ∀ J : Q.support,
      MvPolynomial.coeff J Q = c J * MvPolynomial.coeff (f J) P := by
    intro J
    simp only [c, one_mul]
    exact Classical.choose_spec (hex J)
  have h := PolynomialHeights.projectiveCoeffHeight_le_of_reindex_diagonal
    f c hc
  have hc0 : Height.logHeight c = 0 := Height.logHeight_one
  rw [hc0, add_zero] at h
  exact h

theorem degreeOf_affineSpecialization_specialize_le {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d)
    (p q : Fin m → Fin (n + 1)) (hpq : ∀ j, q j ≠ p j)
    (j : Fin m) :
    (affineSpecialization p
      (specializePolynomial (discardedVariables p q) P)).degreeOf j ≤ d j := by
  let S := specializePolynomial (discardedVariables p q) P
  have horders := hasConstantBlockOrders_of_isMultiHomogeneous hP
  have hinj : Set.InjOn (affineExponentAt p) S.support :=
    affineExponentAt_injOn_specializePolynomial P p q hpq horders
  rw [MvPolynomial.degreeOf_le_iff]
  intro J hJ
  rw [support_affineSpecialization p hinj] at hJ
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨e, he, -, hKe⟩ :=
    exists_support_coeff_eq_of_specializePolynomial
      (discardedVariables p q) P hK
  rw [affineExponentAt_apply]
  calc
    K (j, p j) ≤ e (j, p j) := hKe (j, p j)
    _ ≤ RothIndex.blockOrder e j := by
      unfold RothIndex.blockOrder
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun k : Fin (n + 1) ↦ e (j, k))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (p j))
    _ = d j := hP.of_mem_support he j

/-! ## The completed algebraic binary reduction -/

theorem formIndexAt_le_affineIndex_binarySpecialization {m n : ℕ}
    (M : FormFamily m n) (p q : Fin m → Fin (n + 1))
    (hpq : ∀ j, q j ≠ p j) (hp : ∀ j, M j (p j) ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (horders : HasConstantBlockOrders P) (d : Fin m → ℕ) :
    formIndexAt M p P d ≤
      BinaryRoth.affineIndex (affineBinarySpecialization p q P) d
        (binaryRootAt M p q) := by
  let L := discardedVariables p q
  let S := binarySpecializedPolynomial p q P
  let N := binarySpecializedForms p q M
  let A := affineBinarySpecialization p q P
  let β := binaryRootAt M p q
  have hL : ∀ i ∈ L, i.2 ≠ p i.1 := by
    intro i hi
    exact (mem_discardedVariables_iff p q i).mp hi |>.1
  have hmono : formIndexAt M p P d ≤ formIndexAt N p S d :=
    formIndexAt_le_specialize L M p hp hP d hL
  apply hmono.trans
  have hS : S ≠ 0 := specializePolynomial_ne_zero L hP
  have hpN : ∀ j, N j (p j) ≠ 0 :=
    specializeForms_pivot_ne_zero L M p hp hL
  have hinj : Set.InjOn (affineExponentAt p) S.support :=
    affineExponentAt_injOn_specializePolynomial P p q hpq horders
  have hA : A ≠ 0 := affineSpecialization_ne_zero hS p hinj
  obtain ⟨J, hJcoeff, hJweight⟩ :=
    BinaryRoth.exists_hasseCoeff_weight_eq_affineIndex hA d β
  have hJtrans : J ∈ (RothIndex.translate β A).support :=
    MvPolynomial.mem_support_iff.mpr hJcoeff
  have hscale : ∀ j, (M j (p j))⁻¹ ≠ 0 :=
    fun j ↦ inv_ne_zero (hp j)
  have hJscale : J ∈
      (scaleVariables (fun j ↦ (M j (p j))⁻¹)
        (RothIndex.translate β A)).support := by
    rw [support_scaleVariables hscale]
    exact hJtrans
  have hadapt := dehomogenize_binary_toForm_eq_scale_translate M p q hpq P
  have hJdehom : J ∈
      (affineSpecialization p (toFormCoordinatesAt N p S)).support := by
    rw [← dehomogenizeAt_eq_affineSpecialization, hadapt]
    exact hJscale
  obtain ⟨e, he, heJ⟩ :=
    exists_support_affineExponentAt_of_mem_affineSpecialization
      p (toFormCoordinatesAt N p S) hJdehom
  have hle := formIndexAt_le_weight N p hpN hS d he
  rw [← hJweight]
  calc
    formIndexAt N p S d ≤
        formNormalWeight d (formNormalOrderOfExponentAt p e) := hle
    _ = BinaryRoth.affineWeight d J := by
      unfold formNormalWeight BinaryRoth.affineWeight
      apply Finset.sum_congr rfl
      intro j hj
      rw [show formNormalOrderOfExponentAt p e j = J j by
        rw [formNormalOrderOfExponentAt, ← heJ, affineExponentAt_apply]]

/-- Canonical binary reduction of the form index. -/
theorem formIndex_le_selectedAffineIndex {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d) :
    formIndex M hM P d ≤
      BinaryRoth.affineIndex (selectedAffinePolynomial hn M hM P) d
        (selectedRoots hn M hM) := by
  rw [formIndex_eq_at_canonical]
  exact formIndexAt_le_affineIndex_binarySpecialization M
    (selectedPivot M hM) (selectedSecondary hn M hM)
    (fun j ↦ secondaryIndex_ne_pivot hn (M j) (hM j))
    (fun j ↦ pivotIndex_coeff_ne_zero (M j) (hM j)) hP
    (hasConstantBlockOrders_of_isMultiHomogeneous hhom) d

theorem selectedAffinePolynomial_ne_zero {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d) :
    selectedAffinePolynomial hn M hM P ≠ 0 := by
  let p := selectedPivot M hM
  let q := selectedSecondary hn M hM
  let S := binarySpecializedPolynomial p q P
  have hpq : ∀ j, q j ≠ p j := fun j ↦
    secondaryIndex_ne_pivot hn (M j) (hM j)
  have hS : S ≠ 0 := specializePolynomial_ne_zero _ hP
  have hinj : Set.InjOn (affineExponentAt p) S.support :=
    affineExponentAt_injOn_specializePolynomial P p q hpq
      (hasConstantBlockOrders_of_isMultiHomogeneous hhom)
  exact affineSpecialization_ne_zero hS p hinj

theorem degreeOf_selectedAffinePolynomial_le {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d)
    (j : Fin m) :
    (selectedAffinePolynomial hn M hM P).degreeOf j ≤ d j :=
  degreeOf_affineSpecialization_specialize_le hhom
    (selectedPivot M hM) (selectedSecondary hn M hM)
    (fun j ↦ secondaryIndex_ne_pivot hn (M j) (hM j)) j

/-- The elementary bound by the number of blocks.  It supplies the large
root branch of the generalized Roth lemma without any height argument. -/
theorem formIndex_le_card {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hd : ∀ j, 0 < d j)
    (hhom : RothIndex.IsMultiHomogeneous P d) :
    formIndex M hM P d ≤ (m : ℚ) := by
  apply (formIndex_le_selectedAffineIndex hn M hM hP hhom).trans
  exact BinaryRoth.affineIndex_le_card
    (selectedAffinePolynomial_ne_zero hn M hM hP hhom)
    d hd (selectedRoots hn M hM)
    (degreeOf_selectedAffinePolynomial_le hn M hM hhom)

theorem projectiveCoeffHeight_selectedAffinePolynomial_le {m n : ℕ}
    (hn : 0 < n) (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d) :
    PolynomialHeights.projectiveCoeffHeight
        (selectedAffinePolynomial hn M hM P) ≤
      PolynomialHeights.projectiveCoeffHeight P :=
  projectiveCoeffHeight_affineSpecialization_specialize_le P
    (selectedPivot M hM) (selectedSecondary hn M hM)
    (fun j ↦ secondaryIndex_ne_pivot hn (M j) (hM j))
    (hasConstantBlockOrders_of_isMultiHomogeneous hhom)

theorem formHeight_le_selectedRootHeight {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0) (j : Fin m) :
    formHeight (M j) ≤
      (n : ℝ) * Height.logHeight₁ (selectedRoots hn M hM j) := by
  rw [selectedRoots, logHeight_binaryRoot]
  exact formHeight_le_binaryHeight hn (M j) (hM j)

theorem finUnivNonempty {m : ℕ} (hm : 0 < m) :
    (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- The GLR height hypothesis descends to exactly the height hypothesis for
the selected affine polynomial in the classical Roth lemma. -/
theorem selectedAffine_height_hypothesis {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hheight : ∀ j,
      (n : ℝ) * sigma⁻¹ *
          (PolynomialHeights.projectiveCoeffHeight P +
            4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ)) ≤
        (d j : ℝ) * formHeight (M j)) :
    PolynomialHeights.projectiveCoeffHeight
          (selectedAffinePolynomial hn M hM P) +
        2 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ) ≤
      sigma * Finset.univ.inf' (finUnivNonempty hm)
        (fun j ↦ (d j : ℝ) *
          Height.logHeight₁ (selectedRoots hn M hM j)) := by
  have hAle := projectiveCoeffHeight_selectedAffinePolynomial_le
    hn M hM P hhom
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall :
      PolynomialHeights.projectiveCoeffHeight
          (selectedAffinePolynomial hn M hM P) +
        2 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ) ≤
      PolynomialHeights.projectiveCoeffHeight P +
        4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (d ⟨0, hm⟩ : ℝ) := by positivity
    have hmR : (0 : ℝ) ≤ m := by positivity
    nlinarith
  apply hsmall.trans
  have hinf : sigma⁻¹ *
      (PolynomialHeights.projectiveCoeffHeight P +
        4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ)) ≤
      Finset.univ.inf' (finUnivNonempty hm)
        (fun j ↦ (d j : ℝ) *
          Height.logHeight₁ (selectedRoots hn M hM j)) := by
    apply (Finset.le_inf'_iff (finUnivNonempty hm) _).2
    intro j hj
    have hroot := formHeight_le_selectedRootHeight hn M hM j
    have hh := hheight j
    have hdnonneg : (0 : ℝ) ≤ (d j : ℝ) := by positivity
    have hscaledRoot :
        (d j : ℝ) * formHeight (M j) ≤
          (n : ℝ) * ((d j : ℝ) *
            Height.logHeight₁ (selectedRoots hn M hM j)) := by
      calc
        (d j : ℝ) * formHeight (M j) ≤
            (d j : ℝ) * ((n : ℝ) *
              Height.logHeight₁ (selectedRoots hn M hM j)) :=
          mul_le_mul_of_nonneg_left hroot hdnonneg
        _ = (n : ℝ) * ((d j : ℝ) *
            Height.logHeight₁ (selectedRoots hn M hM j)) := by ring
    nlinarith [hh.trans hscaledRoot]
  have hmul := mul_le_mul_of_nonneg_left hinf hsigma.le
  calc
    PolynomialHeights.projectiveCoeffHeight P +
        4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ) =
      sigma * (sigma⁻¹ *
        (PolynomialHeights.projectiveCoeffHeight P +
          4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hsigma.ne', one_mul]
    _ ≤ sigma * Finset.univ.inf' (finUnivNonempty hm)
        (fun j ↦ (d j : ℝ) *
          Height.logHeight₁ (selectedRoots hn M hM j)) := hmul

/-- Pointwise form of `selectedAffine_height_hypothesis`, convenient for
versions of the classical Roth lemma whose height premise is not packaged as
a finite infimum. -/
theorem selectedAffine_height_hypothesis_pointwise {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hheight : ∀ j,
      (n : ℝ) * sigma⁻¹ *
          (PolynomialHeights.projectiveCoeffHeight P +
            4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ)) ≤
        (d j : ℝ) * formHeight (M j))
    (j : Fin m) :
    PolynomialHeights.projectiveCoeffHeight
          (selectedAffinePolynomial hn M hM P) +
        2 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ) ≤
      sigma * ((d j : ℝ) *
        Height.logHeight₁ (selectedRoots hn M hM j)) := by
  have hinf := selectedAffine_height_hypothesis hm hn M hM P hhom
    hsigma hheight
  exact hinf.trans (mul_le_mul_of_nonneg_left
    (Finset.inf'_le _ (Finset.mem_univ j)) hsigma.le)

/-- The real `2^(m-1)`-st root occurring in GLR Lemma 4.21. -/
def rothRoot (m : ℕ) (sigma : ℝ) : ℝ :=
  Real.rpow sigma (((2 ^ (m - 1) : ℕ) : ℝ)⁻¹)

theorem rothRoot_pos {m : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < rothRoot m sigma :=
  Real.rpow_pos_of_pos hsigma _

theorem rothRoot_pow {m : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) :
    rothRoot m sigma ^ (2 ^ (m - 1)) = sigma := by
  exact Real.rpow_inv_natCast_pow hsigma.le (pow_ne_zero _ (by norm_num))

/-- When the Roth root is at least one half, the elementary degree bound is
already stronger than the quantitative Roth conclusion.  This isolates the
large-root branch from the height argument used in the small-root branch. -/
theorem formIndex_cast_le_large_rothRoot {m n : ℕ} (hn : 0 < n)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hd : ∀ j, 0 < d j)
    (hhom : RothIndex.IsMultiHomogeneous P d) {sigma : ℝ}
    (hhalf : (1 : ℝ) / 2 ≤ rothRoot m sigma) :
    (formIndex M hM P d : ℝ) ≤
      2 * (m : ℝ) * rothRoot m sigma := by
  have hcardQ := formIndex_le_card hn M hM hP hd hhom
  have hcardR : (formIndex M hM P d : ℝ) ≤ (m : ℝ) :=
    Rat.cast_le.mpr hcardQ
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  nlinarith

/-- Generalized Roth lemma over `ℚ`, in the form of GLR Lemma 4.21.

The polynomial is multihomogeneous of block degrees `d`, and `M j` is a
nonzero rational linear form in the `j`th block.  Under the descending degree
ratio and height hypotheses, its normalized index in the powers of the forms
is at most `2 m σ^(1/2^(m-1))`. -/
theorem generalizedRothLemma {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (hd : ∀ j, 0 < d j)
    (hhom : RothIndex.IsMultiHomogeneous P d)
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {sigma : ℝ} (hsigma : 0 < sigma) (_hsigmaHalf : sigma ≤ 1 / 2)
    (hratio : ∀ j : Fin (m - 1),
      (d ⟨j.val + 1, by omega⟩ : ℝ) /
        (d ⟨j.val, by omega⟩ : ℝ) ≤ sigma)
    (hheight : ∀ j,
      (n : ℝ) * sigma⁻¹ *
          (PolynomialHeights.projectiveCoeffHeight P +
            4 * (m : ℝ) * (d ⟨0, hm⟩ : ℝ)) ≤
        (d j : ℝ) * formHeight (M j)) :
    (formIndex M hM P d : ℝ) ≤
      2 * (m : ℝ) * rothRoot m sigma := by
  let eta := rothRoot m sigma
  by_cases heta : eta ≤ 1 / 2
  · have hformQ := formIndex_le_selectedAffineIndex hn M hM hP hhom
    have hformR : (formIndex M hM P d : ℝ) ≤
        (BinaryRoth.affineIndex (selectedAffinePolynomial hn M hM P) d
          (selectedRoots hn M hM) : ℝ) := Rat.cast_le.mpr hformQ
    apply hformR.trans
    apply BinaryRoth.rothLemma hm
      (selectedAffinePolynomial_ne_zero hn M hM hP hhom) d hd
      (selectedRoots hn M hM) (rothRoot_pos hsigma) heta
      (degreeOf_selectedAffinePolynomial_le hn M hM hhom)
    · intro j
      have hj := hratio j
      rw [rothRoot_pow hsigma]
      exact hj
    · intro j
      have hj := selectedAffine_height_hypothesis_pointwise hm hn M hM P
        hhom hsigma hheight j
      rw [rothRoot_pow hsigma]
      simpa only [mul_assoc] using hj
  · apply formIndex_cast_le_large_rothRoot hn M hM hP hd hhom
    exact (lt_of_not_ge heta).le

theorem formRestrictionOrders_nonempty {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    (formRestrictionOrders M hM P).Nonempty := by
  exact (MvPolynomial.support_nonempty.mpr
    (toFormCoordinates_ne_zero M hM hP)).image _

theorem formRestrictionWeights_nonempty {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    (formRestrictionWeights M hM P d).Nonempty :=
  (formRestrictionOrders_nonempty M hM hP).image _

/-- The form index is attained by the normal order of an actual monomial in
the adapted polynomial. -/
theorem exists_formNormalOrder_weight_eq_index {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    ∃ e ∈ (toFormCoordinates M hM P).support,
      formNormalWeight d (formNormalOrderOfExponent M hM e) =
        formIndex M hM P d := by
  have hw := formRestrictionWeights_nonempty M hM hP d
  have hmin : (formRestrictionWeights M hM P d).min' hw ∈
      formRestrictionWeights M hM P d := Finset.min'_mem _ _
  obtain ⟨I, hI, hweight⟩ := Finset.mem_image.mp hmin
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hI
  refine ⟨e, he, ?_⟩
  rw [formIndex, dif_pos hw]
  exact hweight

/-- The form index is no larger than the normalized normal order of any
occurring adapted monomial. -/
theorem formIndex_le_weight {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {e : RothIndex.MultiIndex m n}
    (he : e ∈ (toFormCoordinates M hM P).support) :
    formIndex M hM P d ≤
      formNormalWeight d (formNormalOrderOfExponent M hM e) := by
  have hw := formRestrictionWeights_nonempty M hM hP d
  rw [formIndex, dif_pos hw]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨e, he, rfl⟩, rfl⟩

end

end Erdos407.GeneralizedRoth
