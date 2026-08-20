/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos407.BinaryRoth

/-!
# Terminal induction for the quantitative binary Roth lemma

This module isolates the final Wronskian induction from the foundational
index, height, and generalized-Wronskian developments in `BinaryRoth`.
-/

namespace Erdos407.BinaryRoth

open scoped BigOperators

noncomputable section

private theorem two_mul_le_two_pow {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n; norm_num
      · rw [pow_succ]
        have ihn := ih (Nat.one_le_iff_ne_zero.mpr hn0)
        omega

private theorem four_mul_le_two_pow_two_pow {n : ℕ} (hn : 1 ≤ n) :
    4 * n ≤ 2 ^ (2 ^ n) := by
  by_cases hn1 : n = 1
  · subst n; norm_num
  have hexp : 2 * n ≤ 2 ^ n := two_mul_le_two_pow hn
  have hpow : 2 ^ (2 * n) ≤ 2 ^ (2 ^ n) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hbasic := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hfour : 4 * n ≤ 2 * n ^ 2 + 1 := by
    have hn2 : 2 ≤ n := by omega
    nlinarith
  exact hfour.trans (hbasic.trans hpow)

theorem nat_mul_pow_two_pow_le_quarter {n : ℕ} (hn : 1 ≤ n)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    (n : ℝ) * η ^ (2 ^ n) ≤ 1 / 4 := by
  have hpbase : η ^ (2 ^ n) ≤ (1 / 2 : ℝ) ^ (2 ^ n) :=
    pow_le_pow_left₀ hη0 hη _
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpbase hn0
  have hnat := four_mul_le_two_pow_two_pow hn
  have hnatR : (4 : ℝ) * n ≤ (2 : ℝ) ^ (2 ^ n) := by exact_mod_cast hnat
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n) := by positivity
  calc
    (n : ℝ) * η ^ (2 ^ n) ≤
        (n : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) := hmul
    _ = (n : ℝ) / ((2 : ℝ) ^ (2 ^ n)) := by
      rw [one_div, inv_pow]
      ring
    _ ≤ 1 / 4 := by
      rw [div_le_iff₀ hden]
      nlinarith

theorem sum_degrees_le_five_fourths {n : ℕ} (hn : 1 ≤ n)
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hratio : ∀ j : Fin n,
      (r j.castSucc : ℝ) / (r j.succ : ℝ) ≤ η ^ (2 ^ n)) :
    (∑ i, (r i : ℝ)) ≤ (5 / 4 : ℝ) * r (Fin.last n) := by
  let q := η ^ (2 ^ n)
  have hq0 : 0 ≤ q := pow_nonneg hη0 _
  have hqquarter : (n : ℝ) * q ≤ 1 / 4 :=
    nat_mul_pow_two_pow_le_quarter hn hη0 hη
  have hqone : q ≤ 1 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hadj (j : Fin n) : (r j.castSucc : ℝ) ≤ r j.succ := by
    have hden : (0 : ℝ) < r j.succ := by exact_mod_cast hr j.succ
    have hscaled := (div_le_iff₀ hden).mp (hratio j)
    have hrj : (0 : ℝ) ≤ r j.succ := hden.le
    nlinarith
  have hmono : Monotone (fun i : Fin (n + 1) ↦ (r i : ℝ)) :=
    Fin.monotone_iff_le_succ.mpr hadj
  rw [Fin.sum_univ_castSucc]
  have hfirst : (∑ i : Fin n, (r i.castSucc : ℝ)) ≤
      ∑ _i : Fin n, q * (r (Fin.last n) : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    have hden : (0 : ℝ) < r i.succ := by exact_mod_cast hr i.succ
    have hscaled := (div_le_iff₀ hden).mp (hratio i)
    have hlast : (r i.succ : ℝ) ≤ r (Fin.last n) :=
      hmono (Fin.le_last _)
    exact hscaled.trans (mul_le_mul_of_nonneg_left hlast hq0)
  calc
    (∑ i : Fin n, (r i.castSucc : ℝ)) + r (Fin.last n) ≤
        (∑ _i : Fin n, q * (r (Fin.last n) : ℝ)) + r (Fin.last n) :=
      add_le_add hfirst le_rfl
    _ = ((n : ℝ) * q + 1) * r (Fin.last n) := by simp; ring
    _ ≤ (5 / 4 : ℝ) * r (Fin.last n) := by
      have hrlast : (0 : ℝ) ≤ r (Fin.last n) := by positivity
      nlinarith

theorem log_factorial_le_mul_pred {k : ℕ} (hk : 0 < k) :
    Real.log (Nat.factorial k) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
  have hfac := Nat.factorial_le_pow k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpowR : (Nat.factorial k : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast hfac
  calc
    Real.log (Nat.factorial k) ≤ Real.log ((k : ℝ) ^ k) := by
      exact Real.log_le_log (by positivity) hpowR
    _ = (k : ℝ) * Real.log k := by rw [Real.log_pow]
    _ ≤ (k : ℝ) * ((k : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hkR) hkR.le

theorem hasPartialDegreeAtMost_iterate_pderiv {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} {d : Fin m → ℕ}
    (hP : PolynomialHeights.HasPartialDegreeAtMost P d)
    (i : Fin m) (n : ℕ) :
    PolynomialHeights.HasPartialDegreeAtMost
      ((MvPolynomial.pderiv i)^[n] P) d := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa using ih.hasseDerivative (Finsupp.single i 1)

theorem hasPartialDegreeAtMost_multiDerivative {m : ℕ}
    {P : MvPolynomial (Fin m) ℚ} {d : Fin m → ℕ}
    (hP : PolynomialHeights.HasPartialDegreeAtMost P d)
    (μ : GeneralizedWronskian.MultiIndex m) :
    PolynomialHeights.HasPartialDegreeAtMost
      (GeneralizedWronskian.multiDerivative μ P) d := by
  unfold GeneralizedWronskian.multiDerivative
  generalize (Finset.univ.toList : List (Fin m)) = l
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih =>
      simp only [List.foldl_cons]
      apply ih
      exact hasPartialDegreeAtMost_iterate_pderiv hP i (μ i)

theorem hasPartialDegreeAtMost_det {m k : ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ))
    (d : Fin m → ℕ)
    (hA : ∀ a b, PolynomialHeights.HasPartialDegreeAtMost (A a b) d) :
    PolynomialHeights.HasPartialDegreeAtMost A.det (fun i ↦ k * d i) := by
  rw [PolynomialHeights.HasPartialDegreeAtMost]
  intro J hJ i
  apply (MvPolynomial.degreeOf_le_iff.mp ?_ J hJ)
  rw [Matrix.det_apply]
  calc
    MvPolynomial.degreeOf i
        (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ j, A (σ j) j) ≤
        Finset.univ.sup (fun σ : Equiv.Perm (Fin k) ↦
          MvPolynomial.degreeOf i (Equiv.Perm.sign σ • ∏ j, A (σ j) j)) := by
      simpa using MvPolynomial.degreeOf_sum_le i Finset.univ
        (fun σ : Equiv.Perm (Fin k) ↦ Equiv.Perm.sign σ • ∏ j, A (σ j) j)
    _ ≤ k * d i := by
      apply Finset.sup_le
      intro σ hσ
      have hprod : MvPolynomial.degreeOf i (∏ j, A (σ j) j) ≤ k * d i := by
        calc
          MvPolynomial.degreeOf i (∏ j, A (σ j) j) ≤
              ∑ j : Fin k, MvPolynomial.degreeOf i (A (σ j) j) := by
            simpa using MvPolynomial.degreeOf_prod_le i Finset.univ
              (fun j : Fin k ↦ A (σ j) j)
          _ ≤ ∑ _j : Fin k, d i := by
            apply Finset.sum_le_sum
            intro j hj
            exact MvPolynomial.degreeOf_le_iff.mpr
              (fun J hJ ↦ hA (σ j) j J hJ i)
          _ = k * d i := by simp [mul_comm]
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro L hL
      apply MvPolynomial.degreeOf_le_iff.mp hprod L
      exact MvPolynomial.support_smul hL

theorem factor_degree_bounds {m k : ℕ}
    {V : MvPolynomial (Fin (m + 1)) ℚ}
    {A : MvPolynomial (Fin m) ℚ} (hA : A ≠ 0)
    {q : Polynomial ℚ} (hq : q ≠ 0)
    (r : Fin (m + 1) → ℕ)
    (hVdeg : PolynomialHeights.HasPartialDegreeAtMost V
      (fun i ↦ k * r i))
    (hfactor : MvPolynomial.finSuccEquiv ℚ m V =
      Polynomial.C A * q.map MvPolynomial.C) :
    q.natDegree ≤ k * r 0 ∧
      ∀ i, MvPolynomial.degreeOf i A ≤ k * r i.succ := by
  have hmapq : q.map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (MvPolynomial.C_injective (σ := Fin m) (R := ℚ))).mpr hq
  have hCA : Polynomial.C A ≠ 0 := Polynomial.C_ne_zero.mpr hA
  have hnat : (MvPolynomial.finSuccEquiv ℚ m V).natDegree = q.natDegree := by
    rw [hfactor, Polynomial.natDegree_mul hCA hmapq,
      Polynomial.natDegree_C, zero_add, Polynomial.natDegree_map]
  have hVdegree (i : Fin (m + 1)) :
      MvPolynomial.degreeOf i V ≤ k * r i :=
    MvPolynomial.degreeOf_le_iff.mpr (fun J hJ ↦ hVdeg J hJ i)
  constructor
  · rw [← hnat, MvPolynomial.natDegree_finSuccEquiv]
    exact hVdegree 0
  · intro i
    let n := q.natDegree
    have hn : q.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    have hcoeff : (MvPolynomial.finSuccEquiv ℚ m V).coeff n =
        A * MvPolynomial.C (q.coeff n) := by
      rw [hfactor, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    calc
      MvPolynomial.degreeOf i A =
          MvPolynomial.degreeOf i (MvPolynomial.C (q.coeff n) * A) := by
        symm
        exact MvPolynomial.degreeOf_C_mul i _
          (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
      _ = MvPolynomial.degreeOf i ((MvPolynomial.finSuccEquiv ℚ m V).coeff n) := by
        rw [hcoeff, mul_comm]
      _ ≤ MvPolynomial.degreeOf i.succ V :=
        MvPolynomial.degreeOf_coeff_finSuccEquiv V i n
      _ ≤ k * r i.succ := hVdegree i.succ

theorem affineWeight_mul_degrees {m k : ℕ} (hk : 0 < k)
    (r : Fin m → ℕ) (J : AffineMultiIndex m) :
    (k : ℚ) * affineWeight (fun i ↦ k * r i) J = affineWeight r J := by
  unfold affineWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hri : r i = 0
  · simp [hri]
  · push_cast
    field_simp

theorem affineIndex_mul_degrees {m k : ℕ} (hk : 0 < k)
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (β : Fin m → ℚ) :
    (k : ℚ) * affineIndex P (fun i ↦ k * r i) β = affineIndex P r β := by
  obtain ⟨J, hJ, hJweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hP (fun i ↦ k * r i) β
  obtain ⟨K, hK, hKweight⟩ :=
    exists_hasseCoeff_weight_eq_affineIndex hP r β
  have hle1 := affineIndex_le_weight hP r β J hJ
  have hle2 := affineIndex_le_weight hP (fun i ↦ k * r i) β K hK
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  rw [← affineWeight_mul_degrees hk r J, hJweight] at hle1
  have hscaleK := affineWeight_mul_degrees hk r K
  rw [hKweight] at hscaleK
  nlinarith

def splitEquiv (m : ℕ) : Fin m ⊕ Fin 1 ≃ Fin (m + 1) :=
  (Equiv.sumComm (Fin m) (Fin 1)).trans
    (finSumFinEquiv.trans (finCongr (Nat.one_add m)))

@[simp] theorem splitEquiv_inl {m : ℕ} (i : Fin m) :
    splitEquiv m (Sum.inl i) = i.succ := by
  apply Fin.ext
  simp [splitEquiv, finSumFinEquiv]

@[simp] theorem splitEquiv_inr {m : ℕ} (i : Fin 1) :
    splitEquiv m (Sum.inr i) = 0 := by
  apply Fin.ext
  simp [splitEquiv, finSumFinEquiv]

theorem rename_splitEquiv_inl {m : ℕ} (A : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.rename (splitEquiv m) (MvPolynomial.rename Sum.inl A) =
      liftLeft A := by
  induction A using MvPolynomial.induction_on with
  | C a => simp
  | add A B hA hB => simp [hA, hB]
  | mul_X A i hA => simp [hA]

theorem rename_splitEquiv_inr {m : ℕ} (q : MvPolynomial (Fin 1) ℚ) :
    MvPolynomial.rename (splitEquiv m) (MvPolynomial.rename Sum.inr q) =
      liftRight (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add A B hA hB => simp [hA, hB]
  | mul_X A i hA =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [hA]

theorem projectiveCoeffHeight_lift_mul {m : ℕ}
    {A : MvPolynomial (Fin m) ℚ} (hA : A ≠ 0)
    {q : Polynomial ℚ} (hq : q ≠ 0) :
    PolynomialHeights.projectiveCoeffHeight (liftLeft A * liftRight q) =
      PolynomialHeights.projectiveCoeffHeight A +
        PolynomialHeights.projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) := by
  let Q : MvPolynomial (Fin 1) ℚ :=
    (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q
  have hQeq : MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) Q = q :=
    (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).apply_symm_apply q
  have hQ : Q ≠ 0 := by
    intro hz
    apply hq
    rw [← hQeq, hz]
    simp
  have hdis := PolynomialHeights.projectiveCoeffHeight_mul_rename_disjoint hA hQ
  have hren := PolynomialHeights.projectiveCoeffHeight_rename_of_injective
    (MvPolynomial.rename Sum.inl A * MvPolynomial.rename Sum.inr Q)
    (splitEquiv m) (splitEquiv m).injective
  rw [map_mul, rename_splitEquiv_inl, rename_splitEquiv_inr] at hren
  rw [hQeq] at hren
  rw [hren, hdis]

theorem degrees_monotone_of_ratio {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hratio : ∀ j : Fin n,
      (r j.castSucc : ℝ) / (r j.succ : ℝ) ≤ η ^ (2 ^ n)) :
    Monotone (fun i : Fin (n + 1) ↦ (r i : ℝ)) := by
  have hq0 : 0 ≤ η ^ (2 ^ n) := pow_nonneg hη0.le _
  have hq1 : η ^ (2 ^ n) ≤ 1 := by
    apply pow_le_one₀ hη0.le
    linarith
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  have hden : (0 : ℝ) < r j.succ := by exact_mod_cast hr j.succ
  have h := (div_le_iff₀ hden).mp (hratio j)
  nlinarith [mul_le_mul_of_nonneg_right hq1 hden.le]

theorem qpar_le_eta_sq {n : ℕ} {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 2) :
    η ^ (2 ^ (n + 1)) ≤ η ^ 2 := by
  apply pow_le_pow_of_le_one hη0.le (by linarith)
  rw [pow_succ]
  have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  omega

theorem terminal_mainLower {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℚ} (hP : P ≠ 0)
    (S : GeneralizedWronskian.SeparationData (n + 1) P)
    (r : Fin (n + 2) → ℕ) (hr : ∀ i, 0 < r i)
    (β : Fin (n + 2) → ℚ) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 2)
    (hratio : ∀ j : Fin (n + 1),
      (r j.castSucc : ℝ) / (r j.succ : ℝ) ≤ η ^ (2 ^ (n + 1)))
    (hdegree : ∀ i, MvPolynomial.degreeOf i P ≤ r i)
    (μ : Fin S.k → GeneralizedWronskian.MultiIndex (n + 1))
    (hμ : ∀ a, GeneralizedWronskian.totalOrder (μ a) ≤ a.1)
    (hk0 : 0 < S.k) (hk : S.k ≤ r 0 + 1)
    (hV : (GeneralizedWronskian.mixedDerivativeMatrix S μ).det ≠ 0) :
    (S.k : ℝ) * (affineIndex P r β : ℝ) ^ 2 /
          (2 * ((n + 2 : ℕ) : ℝ)) ≤
      (affineIndex (GeneralizedWronskian.mixedDerivativeMatrix S μ).det
          r β : ℝ) +
        (S.k : ℝ) * η ^ (2 ^ (n + 1)) := by
  let q : ℝ := η ^ (2 ^ (n + 1))
  let s : ℕ := r (1 : Fin (n + 2))
  let δ : ℚ := (r 0 : ℚ) / (s : ℚ)
  have hq0 : 0 ≤ q := pow_nonneg hη0.le _
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact pow_le_one₀ hη0.le (by linarith)
  have hmono : Monotone (fun i : Fin (n + 2) ↦ (r i : ℝ)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    have hden : (0 : ℝ) < r j.succ := by exact_mod_cast hr j.succ
    have h := (div_le_iff₀ hden).mp (hratio j)
    dsimp [q] at hq0 hq1
    nlinarith [mul_le_mul_of_nonneg_right hq1 hden.le]
  have hs : 0 < s := hr 1
  have hsr : ∀ i : Fin (n + 1), s ≤ r i.succ := by
    intro i
    have hle : (1 : Fin (n + 2)) ≤ i.succ := by
      apply Fin.mk_le_mk.mpr
      simp
    have hc := hmono hle
    change r 1 ≤ r i.succ
    have hc' : (r 1 : ℝ) ≤ (r i.succ : ℝ) := hc
    exact_mod_cast hc'
  have horder (a : Fin S.k) : GeneralizedWronskian.totalOrder (μ a) ≤ r 0 :=
    (hμ a).trans (by omega)
  have hlossTail (a : Fin S.k) :
      (∑ i, (μ a i : ℚ) / (r i.succ : ℚ)) ≤ δ :=
    multiDerivativeLoss_le_totalOrder_div
      (fun i ↦ r i.succ) hs hsr (μ a) (horder a)
  have hloss (a : Fin S.k) :
      (∑ i, (GeneralizedWronskian.liftMultiIndex (μ a) i : ℚ) /
        (r i : ℚ)) ≤ δ := by
    rw [Fin.sum_univ_succ]
    simpa [GeneralizedWronskian.liftMultiIndex] using hlossTail a
  have hδ0 : 0 ≤ δ := div_nonneg (by positivity) (by positivity)
  have hindexQ := affineIndex_le_card hP r hr β hdegree
  have hindexR : (affineIndex P r β : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast hindexQ
  have hV' : Matrix.det (fun a b : Fin S.k ↦
      GeneralizedWronskian.multiDerivative
        (GeneralizedWronskian.liftMultiIndex (μ a))
          ((MvPolynomial.pderiv 0)^[(b : ℕ)] P)) ≠ 0 := by
    change (GeneralizedWronskian.mixedDerivativeMatrix S μ).det ≠ 0
    exact hV
  have hmain := sq_affineIndex_le_derivativeDet_add_loss
    hP r hr β (0 : Fin (n + 2))
      (fun a ↦ GeneralizedWronskian.liftMultiIndex (μ a))
      (by omega : 2 ≤ n + 2) hk0 hk hindexR δ hδ0 hloss hV'
  have hδq : (δ : ℝ) ≤ q := by
    have hfirst := hratio (0 : Fin (n + 1))
    change (r 0 : ℝ) / (r 1 : ℝ) ≤ q at hfirst
    simpa [δ, s, Rat.cast_div, Rat.cast_natCast] using hfirst
  calc
    (S.k : ℝ) * (affineIndex P r β : ℝ) ^ 2 /
          (2 * ((n + 2 : ℕ) : ℝ)) ≤
        (affineIndex (GeneralizedWronskian.mixedDerivativeMatrix S μ).det
          r β : ℝ) + (S.k : ℝ) * (δ : ℝ) := by
      change _ ≤ (affineIndex (Matrix.det (fun a b : Fin S.k ↦
        GeneralizedWronskian.multiDerivative
          (GeneralizedWronskian.liftMultiIndex (μ a))
            ((MvPolynomial.pderiv 0)^[(b : ℕ)] P))) r β : ℝ) + _
      exact hmain
    _ ≤ (affineIndex (GeneralizedWronskian.mixedDerivativeMatrix S μ).det
          r β : ℝ) + (S.k : ℝ) * q := by gcongr
    _ = _ := rfl

theorem determinant_height_numeric {n k : ℕ} (hn : 1 ≤ n)
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hratio : ∀ j : Fin n,
      (r j.castSucc : ℝ) / (r j.succ : ℝ) ≤ η ^ (2 ^ n))
    (hk0 : 0 < k) (hk : k ≤ r 0 + 1)
    {H hV : ℝ}
    (hdet : hV ≤ Real.log (Nat.factorial k) + k * H +
      (2 * k * (∑ i, r i) : ℝ) * Real.log 2) :
    hV ≤ (k : ℝ) * (H + 2 * (r (Fin.last n) : ℝ)) := by
  let q : ℝ := η ^ (2 ^ n)
  have hη0' : 0 ≤ η := hη0.le
  have hq0 : 0 ≤ q := pow_nonneg hη0' _
  have hnq : (n : ℝ) * q ≤ 1 / 4 :=
    nat_mul_pow_two_pow_le_quarter hn hη0' hη
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqquarter : q ≤ 1 / 4 := by nlinarith
  have hqone : q ≤ 1 := by linarith
  have hadj (j : Fin n) : (r j.castSucc : ℝ) ≤ r j.succ := by
    have hden : (0 : ℝ) < r j.succ := by exact_mod_cast hr j.succ
    have hs := (div_le_iff₀ hden).mp (hratio j)
    nlinarith [mul_le_mul_of_nonneg_right hqone hden.le]
  have hmono : Monotone (fun i : Fin (n + 1) ↦ (r i : ℝ)) :=
    Fin.monotone_iff_le_succ.mpr hadj
  let j0 : Fin n := ⟨0, hn⟩
  have hr0q : (r 0 : ℝ) ≤ q * r (Fin.last n) := by
    have hden : (0 : ℝ) < r j0.succ := by exact_mod_cast hr j0.succ
    have hs := (div_le_iff₀ hden).mp (hratio j0)
    have hlast : (r j0.succ : ℝ) ≤ r (Fin.last n) :=
      hmono (Fin.le_last _)
    exact hs.trans (mul_le_mul_of_nonneg_left hlast hq0)
  have hr0quarter : (r 0 : ℝ) ≤ (1 / 4 : ℝ) * r (Fin.last n) := by
    exact hr0q.trans (mul_le_mul_of_nonneg_right hqquarter (by positivity))
  have hkpred : k - 1 ≤ r 0 := by omega
  have hkpredR : (k : ℝ) - 1 ≤ r 0 := by
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0.ne')]
      norm_num
    rw [← hcast]
    exact_mod_cast hkpred
  have hlogfac : Real.log (Nat.factorial k) ≤
      (k : ℝ) * ((1 / 4 : ℝ) * r (Fin.last n)) := by
    calc
      Real.log (Nat.factorial k) ≤ (k : ℝ) * ((k : ℝ) - 1) :=
        log_factorial_le_mul_pred hk0
      _ ≤ (k : ℝ) * (r 0 : ℝ) :=
        mul_le_mul_of_nonneg_left hkpredR (by positivity)
      _ ≤ (k : ℝ) * ((1 / 4 : ℝ) * r (Fin.last n)) :=
        mul_le_mul_of_nonneg_left hr0quarter (by positivity)
  have hsum := sum_degrees_le_five_fourths hn r hr hη0' hη hratio
  have hlogtwo : Real.log 2 ≤ 7 / 10 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hsum0 : (0 : ℝ) ≤ ∑ i, (r i : ℝ) := by positivity
  have hsumcast : ((∑ i, r i : ℕ) : ℝ) = ∑ i, (r i : ℝ) := by simp
  have hderiv :
      (2 * k * (∑ i, r i) : ℝ) * Real.log 2 ≤
        (7 / 4 : ℝ) * k * r (Fin.last n) := by
    calc
      (2 * k * (∑ i, r i) : ℝ) * Real.log 2 ≤
          (2 * k * (∑ i, r i) : ℝ) * (7 / 10) :=
        mul_le_mul_of_nonneg_left hlogtwo (by positivity)
      _ ≤ (2 * k * ((5 / 4 : ℝ) * r (Fin.last n))) * (7 / 10) := by
        rw [hsumcast]
        gcongr
      _ = (7 / 4 : ℝ) * k * r (Fin.last n) := by ring
  calc
    hV ≤ Real.log (Nat.factorial k) + k * H +
        (2 * k * (∑ i, r i) : ℝ) * Real.log 2 := hdet
    _ ≤ (k : ℝ) * ((1 / 4 : ℝ) * r (Fin.last n)) + k * H +
        (7 / 4 : ℝ) * k * r (Fin.last n) := by linarith
    _ = (k : ℝ) * (H + 2 * (r (Fin.last n) : ℝ)) := by ring

def MixedDetHeightBound : Prop :=
  ∀ {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℚ}
    (S : GeneralizedWronskian.SeparationData n P)
    (d : Fin (n + 1) → ℕ)
    (hP : P ≠ 0) (hdeg : PolynomialHeights.HasPartialDegreeAtMost P d)
    (μ : Fin S.k → GeneralizedWronskian.MultiIndex n),
    PolynomialHeights.projectiveCoeffHeight
        (GeneralizedWronskian.mixedDerivativeMatrix S μ).det ≤
      Real.log (Nat.factorial S.k) + S.k *
        PolynomialHeights.projectiveCoeffHeight P +
        (2 * S.k * (∑ i, d i) : ℝ) * Real.log 2

theorem rothLemmaAscending_of_detHeight (hDet : MixedDetHeightBound) :
    ∀ n : ℕ,
      ∀ {P : MvPolynomial (Fin (n + 1)) ℚ}, P ≠ 0 →
      ∀ (r : Fin (n + 1) → ℕ), (∀ i, 0 < r i) →
      ∀ (β : Fin (n + 1) → ℚ) {η : ℝ}, 0 < η → η ≤ 1 / 2 →
      (∀ i, MvPolynomial.degreeOf i P ≤ r i) →
      (∀ j : Fin n,
        (r j.castSucc : ℝ) / (r j.succ : ℝ) ≤ η ^ (2 ^ n)) →
      (∀ i, PolynomialHeights.projectiveCoeffHeight P +
          2 * (n + 1 : ℝ) * (r (Fin.last n) : ℝ) ≤
        η ^ (2 ^ n) * (r i : ℝ) * Height.logHeight₁ (β i)) →
      (affineIndex P r β : ℝ) ≤ 2 * (n + 1 : ℝ) * η := by
  intro n
  induction n with
  | zero =>
      intro P hP r hr β η hη hηhalf hdegree hratio hheight
      have hheight0 := hheight 0
      norm_num at hheight0
      have h := rothLemmaOne hP r (hr 0) β hη (hdegree 0) hheight0
      norm_num at h ⊢
      exact h
  | succ n ih =>
      intro P hP r hr β η hη hηhalf hdegree hratio hheight
      let S := Classical.choice (GeneralizedWronskian.exists_separationData P)
      have hk0 : 0 < S.k := by
        by_contra hkn
        have hkz : S.k = 0 := Nat.eq_zero_of_not_pos hkn
        have hrecon := S.reconstruct
        have hsumzero :
            (∑ i : Fin S.k, (S.right i).map MvPolynomial.C *
              Polynomial.C (S.left i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have := i.isLt
          omega
        rw [hsumzero] at hrecon
        apply hP
        apply (MvPolynomial.finSuccEquiv ℚ (n + 1)).injective
        simpa using hrecon
      obtain ⟨μ, hμ, hV, hfactor⟩ :=
        GeneralizedWronskian.SeparationData.exists_mixedDerivativeMatrix_ne_zero S
      let V := (GeneralizedWronskian.mixedDerivativeMatrix S μ).det
      let A := GeneralizedWronskian.generalizedWronskian μ S.left
      let q := GeneralizedWronskian.univariateWronskian S.right
      have hq : q ≠ 0 :=
        GeneralizedWronskian.univariateWronskian_ne_zero_of_linearIndependent
          S.right_linearIndependent
      have hA : A ≠ 0 := by
        intro hAz
        have hf := hfactor
        change MvPolynomial.finSuccEquiv ℚ (n + 1) V =
          Polynomial.C A * q.map MvPolynomial.C at hf
        simp only [hAz, map_zero, zero_mul] at hf
        apply hV
        apply (MvPolynomial.finSuccEquiv ℚ (n + 1)).injective
        simpa [V] using hf
      have hPdeg : PolynomialHeights.HasPartialDegreeAtMost P r := by
        intro J hJ i
        exact MvPolynomial.degreeOf_le_iff.mp (hdegree i) J hJ
      have hVdeg : PolynomialHeights.HasPartialDegreeAtMost V
          (fun i ↦ S.k * r i) := by
        apply hasPartialDegreeAtMost_det
        intro a b
        apply hasPartialDegreeAtMost_multiDerivative
        exact hasPartialDegreeAtMost_iterate_pderiv hPdeg 0 b.1
      have hfactor' : MvPolynomial.finSuccEquiv ℚ (n + 1) V =
          Polynomial.C A * q.map MvPolynomial.C := hfactor
      obtain ⟨hqdeg, hAdeg⟩ := factor_degree_bounds hA hq r hVdeg hfactor'
      have hk : S.k ≤ r 0 + 1 := by
        calc
          S.k ≤ (MvPolynomial.finSuccEquiv ℚ (n + 1) P).natDegree + 1 := S.rank_le
          _ = MvPolynomial.degreeOf 0 P + 1 := by
            rw [MvPolynomial.natDegree_finSuccEquiv]
          _ ≤ r 0 + 1 := Nat.add_le_add_right (hdegree 0) 1
      have hVheightRaw := hDet S r hP hPdeg μ
      have hVheight : PolynomialHeights.projectiveCoeffHeight V ≤
          (S.k : ℝ) * (PolynomialHeights.projectiveCoeffHeight P +
            2 * (r (Fin.last (n + 1)) : ℝ)) := by
        exact determinant_height_numeric (Nat.succ_le_succ (Nat.zero_le n))
          r hr hη hηhalf hratio hk0 hk hVheightRaw
      have hVprod : V = liftLeft A * liftRight q := by
        apply (MvPolynomial.finSuccEquiv ℚ (n + 1)).injective
        rw [hfactor', finSuccEquiv_lift_mul]
      have hheightEq : PolynomialHeights.projectiveCoeffHeight V =
          PolynomialHeights.projectiveCoeffHeight A +
            PolynomialHeights.projectiveCoeffHeight
              ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) := by
        rw [hVprod]
        exact projectiveCoeffHeight_lift_mul hA hq
      have hAheight : PolynomialHeights.projectiveCoeffHeight A ≤
          PolynomialHeights.projectiveCoeffHeight V := by
        rw [hheightEq]
        exact le_add_of_nonneg_right
          (PolynomialHeights.projectiveCoeffHeight_nonneg _)
      have hqheight : PolynomialHeights.projectiveCoeffHeight
            ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) ≤
          PolynomialHeights.projectiveCoeffHeight V := by
        rw [hheightEq]
        exact le_add_of_nonneg_left
          (PolynomialHeights.projectiveCoeffHeight_nonneg _)
      let qpar : ℝ := η ^ (2 ^ (n + 1))
      have hqpar0 : 0 < qpar := pow_pos hη _
      have hrightHeight :
          PolynomialHeights.projectiveCoeffHeight
              ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) +
              2 * (S.k * r 0 : ℝ) ≤
            qpar * (S.k * r 0 : ℝ) * Height.logHeight₁ (β 0) := by
        have hbig := hheight (0 : Fin (n + 2))
        norm_num only [Nat.cast_add, Nat.cast_one] at hbig
        have hkR : (0 : ℝ) ≤ S.k := by positivity
        have hlast0 : (0 : ℝ) ≤ r (Fin.last (n + 1)) := by positivity
        dsimp [qpar] at hbig ⊢
        calc
          _ ≤ (S.k : ℝ) *
              (PolynomialHeights.projectiveCoeffHeight P +
                2 * (r (Fin.last (n + 1)) : ℝ)) +
                2 * (S.k * r 0 : ℝ) := by linarith
          _ = (S.k : ℝ) *
              (PolynomialHeights.projectiveCoeffHeight P +
                2 * r (Fin.last (n + 1)) + 2 * r 0) := by ring
          _ ≤ (S.k : ℝ) *
              (PolynomialHeights.projectiveCoeffHeight P +
                2 * (n + 2 : ℝ) * r (Fin.last (n + 1))) := by
                  apply mul_le_mul_of_nonneg_left _ hkR
                  have hr0last : (r 0 : ℝ) ≤ r (Fin.last (n + 1)) :=
                    degrees_monotone_of_ratio r hr hη hηhalf hratio
                      (Fin.le_last _)
                  have hn0 : (0 : ℝ) ≤ n := by positivity
                  have hrlast0 : (0 : ℝ) ≤ r (Fin.last (n + 1)) := by positivity
                  nlinarith
          _ ≤ (S.k : ℝ) *
              (qpar * (r 0 : ℝ) * Height.logHeight₁ (β 0)) := by
                have hbig' : PolynomialHeights.projectiveCoeffHeight P +
                    2 * (n + 2 : ℝ) * r (Fin.last (n + 1)) ≤
                    qpar * (r 0 : ℝ) * Height.logHeight₁ (β 0) := by
                  dsimp [qpar]
                  convert hbig using 1 <;> ring
                have hm := mul_le_mul_of_nonneg_left hbig' hkR
                dsimp [qpar]
                simpa [qpar] using hm
          _ = _ := by ring
      let rq : Fin 1 → ℕ := fun _ ↦ S.k * r 0
      let βq : Fin 1 → ℚ := fun _ ↦ β 0
      have hrq : 0 < rq 0 := by
        simp only [rq]
        exact Nat.mul_pos hk0 (hr 0)
      have hqmv : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q ≠ 0 := by
        intro hz
        apply hq
        rw [← (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).apply_symm_apply q, hz]
        simp
      have hmahler := MahlerHeightBridge.rootMultiplicity_mul_logHeight₁_le
        hq (β 0) hqdeg
      norm_num only [Nat.cast_mul] at hmahler
      have hr0R : (0 : ℝ) < r 0 := by exact_mod_cast hr 0
      have hbeta0 : 0 < Height.logHeight₁ (β 0) := by
        have hkrpos : (0 : ℝ) < (S.k * r 0 : ℕ) := by
          exact_mod_cast Nat.mul_pos hk0 (hr 0)
        norm_num only [Nat.cast_mul] at hkrpos
        have hh0 := PolynomialHeights.projectiveCoeffHeight_nonneg
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q)
        have hpos : 0 < qpar * (S.k * r 0 : ℝ) *
            Height.logHeight₁ (β 0) := by
          calc
            0 < PolynomialHeights.projectiveCoeffHeight
                ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm q) +
                2 * (S.k * r 0 : ℝ) := by nlinarith
            _ ≤ _ := hrightHeight
        have hz := Height.zero_le_logHeight₁ (β 0)
        rcases hz.eq_or_lt with hz | hz
        · rw [← hz, mul_zero] at hpos
          exact (lt_irrefl 0 hpos).elim
        · exact hz
      have hroot : (q.rootMultiplicity (β 0) : ℝ) ≤
          qpar * (S.k * r 0 : ℝ) := by
        nlinarith
      have hrightIndex : (q.rootMultiplicity (β 0) : ℝ) / (r 0 : ℝ) ≤
          (S.k : ℝ) * qpar := by
        calc
          (q.rootMultiplicity (β 0) : ℝ) / (r 0 : ℝ) ≤
              (qpar * ((S.k : ℝ) * r 0)) / r 0 :=
            div_le_div_of_nonneg_right hroot hr0R.le
          _ = (S.k : ℝ) * qpar := by field_simp
      -- The left factor satisfies the same hypotheses in one fewer variable,
      -- with parameter `η²` and all degrees multiplied by the separation rank.
      have hleftIndex :
          (affineIndex A (fun i ↦ r i.succ) (fun i ↦ β i.succ) : ℝ) ≤
            2 * (S.k : ℝ) * (n + 1 : ℝ) * η ^ 2 := by
        let rA : Fin (n + 1) → ℕ := fun i ↦ S.k * r i.succ
        let βA : Fin (n + 1) → ℚ := fun i ↦ β i.succ
        have hrA : ∀ i, 0 < rA i := fun i ↦ by
          exact Nat.mul_pos hk0 (hr i.succ)
        have hηsq0 : 0 < η ^ 2 := sq_pos_of_pos hη
        have hηsqhalf : η ^ 2 ≤ 1 / 2 := by nlinarith [sq_nonneg (η - 1 / 2)]
        have hpow : (η ^ 2) ^ (2 ^ n) = qpar := by
          dsimp [qpar]
          calc
            (η ^ 2) ^ (2 ^ n) = η ^ (2 * 2 ^ n) := by rw [pow_mul]
            _ = η ^ (2 ^ (n + 1)) := by
              rw [pow_succ]
              congr 1
              omega
        have hratioA : ∀ j : Fin n,
            (rA j.castSucc : ℝ) / (rA j.succ : ℝ) ≤
              (η ^ 2) ^ (2 ^ n) := by
          intro j
          have hidx1 : (j.castSucc : Fin (n + 1)).succ =
              (j.succ : Fin (n + 1)).castSucc := by
            apply Fin.ext
            simp
          have horig := hratio (j.succ : Fin (n + 1))
          have hkRpos : (0 : ℝ) < S.k := by exact_mod_cast hk0
          dsimp [rA]
          norm_num only [Nat.cast_mul]
          rw [hidx1, hpow]
          calc
            (S.k : ℝ) * r j.succ.castSucc /
                ((S.k : ℝ) * r j.succ.succ) =
                (r j.succ.castSucc : ℝ) / r j.succ.succ := by field_simp
            _ ≤ qpar := horig
        have hheightA : ∀ i,
            PolynomialHeights.projectiveCoeffHeight A +
                2 * (n + 1 : ℝ) * (rA (Fin.last n) : ℝ) ≤
              (η ^ 2) ^ (2 ^ n) * (rA i : ℝ) *
                Height.logHeight₁ (βA i) := by
          intro i
          have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
            apply Fin.ext
            simp
          have hbig := hheight i.succ
          norm_num only [Nat.cast_add, Nat.cast_one] at hbig
          have hkR : (0 : ℝ) ≤ S.k := by positivity
          dsimp [rA, βA]
          norm_num only [Nat.cast_mul]
          rw [hpow]
          calc
            PolynomialHeights.projectiveCoeffHeight A +
                2 * (n + 1 : ℝ) * ((S.k : ℝ) * r (Fin.last (n + 1))) ≤
                (S.k : ℝ) *
                    (PolynomialHeights.projectiveCoeffHeight P +
                      2 * r (Fin.last (n + 1))) +
                  2 * (n + 1 : ℝ) *
                    ((S.k : ℝ) * r (Fin.last (n + 1))) := by linarith
            _ = (S.k : ℝ) *
                (PolynomialHeights.projectiveCoeffHeight P +
                  2 * (n + 2 : ℝ) * r (Fin.last (n + 1))) := by ring
            _ ≤ (S.k : ℝ) *
                (qpar * (r i.succ : ℝ) * Height.logHeight₁ (β i.succ)) := by
              apply mul_le_mul_of_nonneg_left _ hkR
              rw [show (n + 2 : ℝ) = (n : ℝ) + 1 + 1 by
                push_cast; ring]
              dsimp [qpar]
              exact hbig
            _ = qpar * ((S.k : ℝ) * r i.succ) *
                Height.logHeight₁ (β i.succ) := by ring
        have hih := ih hA rA hrA βA hηsq0 hηsqhalf
          (by intro i; simpa [rA] using hAdeg i) hratioA hheightA
        have hscale := affineIndex_mul_degrees hk0 hA
          (fun i ↦ r i.succ) (fun i ↦ β i.succ)
        have hscaleR : (S.k : ℝ) *
              (affineIndex A rA βA : ℝ) =
            (affineIndex A (fun i ↦ r i.succ) (fun i ↦ β i.succ) : ℝ) := by
          have hc := congrArg (fun x : ℚ ↦ (x : ℝ)) hscale
          simpa only [Rat.cast_mul, Rat.cast_natCast, rA, βA] using hc
        rw [← hscaleR]
        have hm := mul_le_mul_of_nonneg_left hih (by positivity : (0 : ℝ) ≤ S.k)
        nlinarith
      have hVindex : (affineIndex V r β : ℝ) ≤
          (S.k : ℝ) * qpar + 2 * (S.k : ℝ) * (n + 1 : ℝ) * η ^ 2 := by
        have hs := affineIndex_liftLeft_mul_liftRight_le hA hq r β
        have hsR : (affineIndex V r β : ℝ) ≤
            (affineIndex A (fun i ↦ r i.succ) (fun i ↦ β i.succ) : ℝ) +
              (q.rootMultiplicity (β 0) : ℝ) / (r 0 : ℝ) := by
                rw [hVprod]
                have hsCast :
                    ((affineIndex (liftLeft A * liftRight q) r β : ℚ) : ℝ) ≤
                      ((affineIndex A (fun i ↦ r i.succ)
                        (fun i ↦ β i.succ) +
                        (q.rootMultiplicity (β 0) : ℚ) / (r 0 : ℚ) : ℚ) : ℝ) :=
                  Rat.cast_le.mpr hs
                norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast] at hsCast
                exact hsCast
        linarith
      have hmainLower : (S.k : ℝ) * (affineIndex P r β : ℝ) ^ 2 /
            (2 * (n + 2 : ℝ)) ≤
          (affineIndex V r β : ℝ) + (S.k : ℝ) * qpar := by
        have hm := terminal_mainLower hP S r hr β hη hηhalf hratio
          hdegree μ hμ hk0 hk hV
        simpa [V, qpar] using hm
      have hqpar_eta2 : qpar ≤ η ^ 2 := by
        exact qpar_le_eta_sq hη hηhalf
      have hI0 : (0 : ℝ) ≤ (affineIndex P r β : ℝ) := by
        exact_mod_cast affineIndex_nonneg hP hr β
      have hkRpos : (0 : ℝ) < S.k := by exact_mod_cast hk0
      have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
      have hsq : (affineIndex P r β : ℝ) ^ 2 ≤
          (2 * (n + 2 : ℝ) * η) ^ 2 := by
        have h := hmainLower.trans (by
          calc
            (affineIndex V r β : ℝ) + (S.k : ℝ) * qpar ≤
                2 * (S.k : ℝ) * qpar +
                  2 * (S.k : ℝ) * (n + 1 : ℝ) * η ^ 2 := by linarith
            _ ≤ 2 * (S.k : ℝ) * (n + 2 : ℝ) * η ^ 2 := by
              nlinarith)
        have hden : (0 : ℝ) < 2 * (n + 2 : ℝ) := by positivity
        have hmul := (div_le_iff₀ hden).mp h
        nlinarith
      have hbound0 : 0 ≤ 2 * (n + 2 : ℝ) * η := by positivity
      have hfinal : (affineIndex P r β : ℝ) ≤ 2 * (n + 2 : ℝ) * η := by
        exact (sq_le_sq₀ hI0 hbound0).mp hsq
      convert hfinal using 1 <;> push_cast <;> ring

theorem rothLemma_of_detHeight (hDet : MixedDetHeightBound)
    {m : ℕ} (hm : 0 < m)
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ j, 0 < r j) (β : Fin m → ℚ)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hdegree : ∀ j, MvPolynomial.degreeOf j P ≤ r j)
    (hratio : ∀ j : Fin (m - 1),
      (r ⟨j.val + 1, by omega⟩ : ℝ) /
        (r ⟨j.val, by omega⟩ : ℝ) ≤ η ^ (2 ^ (m - 1)))
    (hheight : ∀ j, PolynomialHeights.projectiveCoeffHeight P +
        2 * (m : ℝ) * (r ⟨0, hm⟩ : ℝ) ≤
      η ^ (2 ^ (m - 1)) * (r j : ℝ) * Height.logHeight₁ (β j)) :
    (affineIndex P r β : ℝ) ≤ 2 * (m : ℝ) * η := by
  cases m with
  | zero => omega
  | succ n =>
      let e : Equiv.Perm (Fin (n + 1)) := Fin.revPerm
      let P' : MvPolynomial (Fin (n + 1)) ℚ := MvPolynomial.rename e P
      let r' : Fin (n + 1) → ℕ := r ∘ e.symm
      let β' : Fin (n + 1) → ℚ := β ∘ e.symm
      have hP' : P' ≠ 0 := by
        dsimp [P']
        exact (MvPolynomial.rename_injective e e.injective).ne hP
      have hr' : ∀ j, 0 < r' j := fun j ↦ hr (e.symm j)
      have hdegree' : ∀ j, MvPolynomial.degreeOf j P' ≤ r' j := by
        intro j
        have hd := hdegree (e.symm j)
        have he := MvPolynomial.degreeOf_rename_of_injective
          (p := P) e.injective (e.symm j)
        simpa [P', r'] using he.trans_le hd
      have hratio' : ∀ j : Fin n,
          (r' j.castSucc : ℝ) / (r' j.succ : ℝ) ≤ η ^ (2 ^ n) := by
        intro j
        have hrev1 : e.symm j.castSucc = (j.rev).succ := by
          apply Fin.ext
          simp only [e, Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev,
            Fin.coe_castSucc, Fin.val_succ]
          omega
        have hrev2 : e.symm j.succ = (j.rev).castSucc := by
          apply Fin.ext
          simp only [e, Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev,
            Fin.val_succ, Fin.coe_castSucc]
          omega
        let t : Fin (n + 1 - 1) := ⟨j.rev.val, by omega⟩
        have ho := hratio t
        have hnum : (⟨t.val + 1, by omega⟩ : Fin (n + 1)) = j.rev.succ := by
          apply Fin.ext
          rfl
        have hden : (⟨t.val, by omega⟩ : Fin (n + 1)) = j.rev.castSucc := by
          apply Fin.ext
          rfl
        rw [hnum, hden] at ho
        norm_num only [Nat.add_sub_cancel] at ho
        simpa [r', hrev1, hrev2] using ho
      have hheight' : ∀ j, PolynomialHeights.projectiveCoeffHeight P' +
            2 * (n + 1 : ℝ) * (r' (Fin.last n) : ℝ) ≤
          η ^ (2 ^ n) * (r' j : ℝ) * Height.logHeight₁ (β' j) := by
        intro j
        have hheightj := hheight (e.symm j)
        have hheightP : PolynomialHeights.projectiveCoeffHeight P' =
            PolynomialHeights.projectiveCoeffHeight P :=
          PolynomialHeights.projectiveCoeffHeight_rename_of_injective
            P e e.injective
        have hlast : e.symm (Fin.last n) = (0 : Fin (n + 1)) := by
          apply Fin.ext
          simp [e, Fin.revPerm_apply, Fin.rev]
        simpa [P', r', β', hheightP, hlast] using hheightj
      have h := rothLemmaAscending_of_detHeight hDet n hP' r' hr' β'
        hη hηhalf hdegree' hratio' hheight'
      have hindex := affineIndex_rename_equiv e P r β
      have hindexR : (affineIndex P' r' β' : ℝ) =
          (affineIndex P r β : ℝ) := by
        exact_mod_cast hindex
      rw [hindexR] at h
      norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
      exact h

theorem mixedDetHeightBound : MixedDetHeightBound := by
  intro n P S d hP hdeg μ
  exact PolynomialHeights.projectiveCoeffHeight_mixedDerivativeMatrix_det_le
    S hP hdeg μ

theorem rothLemma
    {m : ℕ} (hm : 0 < m)
    {P : MvPolynomial (Fin m) ℚ} (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ j, 0 < r j) (β : Fin m → ℚ)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hdegree : ∀ j, MvPolynomial.degreeOf j P ≤ r j)
    (hratio : ∀ j : Fin (m - 1),
      (r ⟨j.val + 1, by omega⟩ : ℝ) /
        (r ⟨j.val, by omega⟩ : ℝ) ≤ η ^ (2 ^ (m - 1)))
    (hheight : ∀ j, PolynomialHeights.projectiveCoeffHeight P +
        2 * (m : ℝ) * (r ⟨0, hm⟩ : ℝ) ≤
      η ^ (2 ^ (m - 1)) * (r j : ℝ) * Height.logHeight₁ (β j)) :
    (affineIndex P r β : ℝ) ≤ 2 * (m : ℝ) * η :=
  rothLemma_of_detHeight mixedDetHeightBound hm hP r hr β hη hηhalf
    hdegree hratio hheight

#print axioms rothLemma

end
end Erdos407.BinaryRoth
