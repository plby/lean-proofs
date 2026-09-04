import ErdosProblems.Erdos95.Algebraic
import ErdosProblems.Erdos95.Geometry

open scoped BigOperators

namespace Erdos95.Hilbert

open Erdos95.Algebraic Erdos95.ES

noncomputable def exactSumEquiv (n : ℕ) :
    {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} ≃
      ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag n) where
  toFun d := ⟨d.1, by
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨d.2, Finset.subset_univ _⟩⟩
  invFun d := ⟨d.1, (Finset.mem_finsuppAntidiag'.mp d.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance exactSumFintype (n : ℕ) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} :=
  Fintype.ofEquiv _ (exactSumEquiv n).symm

noncomputable instance exactSumFintypeDep {T : ℕ} (n : {n : ℕ // n ≤ T}) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
  exactSumFintype n.1

lemma card_exactSum (n : ℕ) :
    Fintype.card {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} =
      Nat.multichoose 3 n := by
  classical
  rw [Fintype.card_congr (exactSumEquiv n)]
  simp only [Fintype.card_coe]
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

def boundedNatEquiv (T : ℕ) : {n : ℕ // n ≤ T} ≃ Fin (T + 1) where
  toFun n := ⟨n.1, by omega⟩
  invFun n := ⟨n.1, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedNatFintype (T : ℕ) :
    Fintype {n : ℕ // n ≤ T} :=
  Fintype.ofEquiv (Fin (T + 1)) (boundedNatEquiv T).symm

noncomputable def boundedSumEquiv (T : ℕ) :
    (Σ n : {n : ℕ // n ≤ T},
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) ≃
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} :=
  Equiv.sigmaSubtypeFiberEquivSubtype
    (fun d : Fin 3 →₀ ℕ => d.sum (fun _ e => e))
    (fun d => by rfl)

noncomputable instance boundedSumFintype (T : ℕ) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} :=
  by
    letI (n : {n : ℕ // n ≤ T}) :
        Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
      exactSumFintype n.1
    letI : Fintype (Σ n : {n : ℕ // n ≤ T},
        {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) :=
      @Sigma.instFintype _ _ (fun n => exactSumFintype n.1) inferInstance
    exact Fintype.ofEquiv _ (boundedSumEquiv T)

lemma card_boundedSum (T : ℕ) :
    Fintype.card {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} =
      (T + 3).choose 3 := by
  classical
  let (n : {n : ℕ // n ≤ T}) :
      Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
    exactSumFintype n.1
  let : Fintype (Σ n : {n : ℕ // n ≤ T},
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) :=
    @Sigma.instFintype _ _ (fun n => exactSumFintype n.1) inferInstance
  rw [← Fintype.card_congr (boundedSumEquiv T)]
  rw [Fintype.card_sigma]
  simp_rw [card_exactSum]
  rw [← Finset.sum_subtype (Finset.range (T + 1)) (by intro x; simp)]
  simpa [Nat.add_comm] using Nat.sum_range_multichoose T 3

lemma finrank_restrictTotalDegree_fin_three (T : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ T) =
      (T + 3).choose 3 := by
  let : Fintype {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ T} :=
    boundedSumFintype T
  unfold MvPolynomial.restrictTotalDegree
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ T})]
  exact card_boundedSum T

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
noncomputable abbrev DegreeLE (T : ℕ) :=
  MvPolynomial.restrictTotalDegree (Fin 3) ℝ T

noncomputable def mulDegreeLE (Q : Poly3) (a T : ℕ)
    (hQ : Q.totalDegree = a) (ha : a ≤ T) : DegreeLE (T - a) →ₗ[ℝ] DegreeLE T where
  toFun A := ⟨Q * A.1, by
    rw [MvPolynomial.mem_restrictTotalDegree]
    refine (MvPolynomial.totalDegree_mul Q A.1).trans ?_
    have hA := (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - a) A.1).mp A.2
    rw [hQ]
    omega⟩
  map_add' A B := by ext; simp [mul_add]
  map_smul' r A := by ext; simp [mul_smul_comm]

lemma mulDegreeLE_injective {Q : Poly3} {a T : ℕ}
    (hQ0 : Q ≠ 0) (hQ : Q.totalDegree = a) (ha : a ≤ T) :
    Function.Injective (mulDegreeLE Q a T hQ ha) := by
  intro A B h
  apply Subtype.ext
  apply mul_left_cancel₀ hQ0
  exact congrArg Subtype.val h

lemma finrank_range_mulDegreeLE {Q : Poly3} {a T : ℕ}
    (hQ0 : Q ≠ 0) (hQ : Q.totalDegree = a) (ha : a ≤ T) :
    Module.finrank ℝ (LinearMap.range (mulDegreeLE Q a T hQ ha)) =
      (T - a + 3).choose 3 := by
  rw [← (LinearEquiv.ofInjective (mulDegreeLE Q a T hQ ha)
    (mulDegreeLE_injective hQ0 hQ ha)).finrank_eq]
  exact finrank_restrictTotalDegree_fin_three (T - a)

lemma range_mulDegreeLE_inf {Q R : Poly3} {a b T : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ T) :
    LinearMap.range (mulDegreeLE Q a T hQa (by omega)) ⊓
        LinearMap.range (mulDegreeLE R b T hRb (by omega)) =
      LinearMap.range (mulDegreeLE (Q * R) (a + b) T
        (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT) := by
  ext Z
  constructor
  · rintro ⟨⟨A, hAZ⟩, ⟨B, hBZ⟩⟩
    have heq : Q * A.1 = R * B.1 := by
      have := congrArg Subtype.val (hAZ.trans hBZ.symm)
      exact this
    have hQdvd : Q ∣ R * B.1 := ⟨A.1, heq.symm⟩
    have hQprime : Prime Q :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hQirr
    have hQdvdB : Q ∣ B.1 :=
      (hQprime.dvd_mul.mp hQdvd).resolve_left hQnotR
    obtain ⟨C, hBC⟩ := hQdvdB
    have hAC : A.1 = R * C := by
      apply mul_left_cancel₀ hQ0
      calc
        Q * A.1 = R * B.1 := heq
        _ = R * (Q * C) := by rw [hBC]
        _ = Q * (R * C) := by ring
    have hCdeg : C.totalDegree ≤ T - (a + b) := by
      by_cases hC0 : C = 0
      · simp [hC0]
      · have hBdeg :=
          (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - b) B.1).mp B.2
        rw [hBC, MvPolynomial.totalDegree_mul_of_isDomain hQ0 hC0, hQa] at hBdeg
        omega
    refine ⟨⟨C, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
      (T - (a + b)) C).mpr hCdeg⟩, ?_⟩
    apply Subtype.ext
    change (Q * R) * C = Z.1
    calc
      (Q * R) * C = Q * (R * C) := by ring
      _ = Q * A.1 := by rw [← hAC]
      _ = Z.1 := congrArg Subtype.val hAZ
  · rintro ⟨C, hCZ⟩
    have hCdeg :=
      (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - (a + b)) C.1).mp C.2
    have hRCdeg : (R * C.1).totalDegree ≤ T - a := by
      refine (MvPolynomial.totalDegree_mul R C.1).trans ?_
      rw [hRb]
      omega
    have hQCdeg : (Q * C.1).totalDegree ≤ T - b := by
      refine (MvPolynomial.totalDegree_mul Q C.1).trans ?_
      rw [hQa]
      omega
    constructor
    · refine ⟨⟨R * C.1, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
        (T - a) (R * C.1)).mpr hRCdeg⟩, ?_⟩
      apply Subtype.ext
      change Q * (R * C.1) = Z.1
      calc
        Q * (R * C.1) = (Q * R) * C.1 := by ring
        _ = Z.1 := congrArg Subtype.val hCZ
    · refine ⟨⟨Q * C.1, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
        (T - b) (Q * C.1)).mpr hQCdeg⟩, ?_⟩
      apply Subtype.ext
      change R * (Q * C.1) = Z.1
      calc
        R * (Q * C.1) = (Q * R) * C.1 := by ring
        _ = Z.1 := congrArg Subtype.val hCZ

lemma six_mul_choose_add_three (n : ℕ) :
    6 * (n + 3).choose 3 = (n + 1) * (n + 2) * (n + 3) := by
  have h3 := Nat.choose_succ_right_eq (n + 3) 2
  have h2 := Nat.choose_succ_right_eq (n + 3) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h3 h2
  have hm2 : n + 3 - 2 = n + 1 := by omega
  have hm1 : n + 3 - 1 = n + 2 := by omega
  rw [hm2] at h3
  rw [hm1] at h2
  nlinarith

lemma choose_cross_bound {a b T : ℕ} (hT : a + b ≤ T) :
    (T + 3).choose 3 + (T - (a + b) + 3).choose 3 ≤
      (T - a + 3).choose 3 + (T - b + 3).choose 3 + a * b * (T + 2) := by
  have h0 := six_mul_choose_add_three T
  have hab := six_mul_choose_add_three (T - (a + b))
  have ha := six_mul_choose_add_three (T - a)
  have hb := six_mul_choose_add_three (T - b)
  have hTa : T - a + a = T := by omega
  have hTb : T - b + b = T := by omega
  have hTab : T - (a + b) + (a + b) = T := by omega
  have hrelA : T - a = T - (a + b) + b := by omega
  have hrelB : T - b = T - (a + b) + a := by omega
  let x := T - (a + b)
  have hx : T - (a + b) = x := rfl
  have hTx : T = x + a + b := by dsimp [x]; omega
  have hAx : T - a = x + b := by dsimp [x]; omega
  have hBx : T - b = x + a := by dsimp [x]; omega
  have hcross :
      6 * ((T + 3).choose 3 + (T - (a + b) + 3).choose 3) +
          3 * a * b * (a + b) =
        6 * ((T - a + 3).choose 3 + (T - b + 3).choose 3) +
          6 * (a * b * (T + 2)) := by
    simp only [Nat.mul_add]
    rw [h0, hab, ha, hb]
    rw [hAx, hBx, hx, hTx]
    ring
  omega

lemma finrank_quotient_principalParts_le {Q R : Poly3} {a b T : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ T) :
    Module.finrank ℝ
        (DegreeLE T ⧸
          (LinearMap.range (mulDegreeLE Q a T hQa (by omega)) ⊔
            LinearMap.range (mulDegreeLE R b T hRb (by omega)))) ≤
      a * b * (T + 2) := by
  let SQ : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE Q a T hQa (by omega))
  let SR : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE R b T hRb (by omega))
  have hquot := (SQ ⊔ SR).finrank_quotient_add_finrank
  have hsup := SQ.finrank_sup_add_finrank_inf_eq SR
  have hQrank : Module.finrank ℝ SQ = (T - a + 3).choose 3 := by
    dsimp [SQ]
    exact finrank_range_mulDegreeLE hQ0 hQa (by omega)
  have hRrank : Module.finrank ℝ SR = (T - b + 3).choose 3 := by
    dsimp [SR]
    exact finrank_range_mulDegreeLE hR0 hRb (by omega)
  have hIrank : Module.finrank ℝ ↥(SQ ⊓ SR) =
      (T - (a + b) + 3).choose 3 := by
    rw [show SQ ⊓ SR =
        LinearMap.range (mulDegreeLE (Q * R) (a + b) T
          (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT) by
      dsimp [SQ, SR]
      exact range_mulDegreeLE_inf hQ0 hR0 hQirr hQnotR hQa hRb hT]
    exact finrank_range_mulDegreeLE (mul_ne_zero hQ0 hR0)
      (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT
  have hVrank : Module.finrank ℝ (DegreeLE T) = (T + 3).choose 3 :=
    finrank_restrictTotalDegree_fin_three T
  have hcross := choose_cross_bound hT
  rw [hQrank, hRrank, hIrank] at hsup
  rw [hVrank] at hquot
  dsimp [SQ, SR] at hquot hsup ⊢
  omega

lemma finrank_quotient_ge_of_diagonal
    {I : Type*} [Fintype I] [DecidableEq I] {s T : ℕ}
    (U : Submodule ℝ (DegreeLE T))
    (F : I × Fin (s + 1) → DegreeLE T)
    (φ : I → DegreeLE T →ₗ[ℝ] Polynomial ℝ)
    (d : I → Polynomial ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hF : ∀ j i k, φ j (F (i, k)) =
      if i = j then d j * Polynomial.X ^ (k : ℕ) else 0)
    (hU : ∀ j G, G ∈ U → φ j G = 0) :
    Fintype.card I * (s + 1) ≤
      Module.finrank ℝ (DegreeLE T ⧸ U) := by
  let b : I × Fin (s + 1) → DegreeLE T ⧸ U :=
    fun z => U.mkQ (F z)
  have hb : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc z
    have hsumQ : U.mkQ (∑ w, c w • F w) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hc
    have hmem : (∑ w, c w • F w) ∈ U := by
      rw [← Submodule.Quotient.mk_eq_zero U]
      change U.mkQ (∑ w, c w • F w) = 0
      exact hsumQ
    have hz := hU z.1 (∑ w, c w • F w) hmem
    rw [map_sum] at hz
    simp only [map_smul] at hz
    rw [Fintype.sum_prod_type] at hz
    have hz' : ∑ k : Fin (s + 1),
        c (z.1, k) • (d z.1 * Polynomial.X ^ (k : ℕ)) = 0 := by
      simpa [hF] using hz
    have hfactor : d z.1 *
        (∑ k : Fin (s + 1),
          Polynomial.C (c (z.1, k)) * Polynomial.X ^ (k : ℕ)) = 0 := by
      rw [Finset.mul_sum]
      simpa only [Polynomial.smul_eq_C_mul, mul_assoc, mul_comm,
        mul_left_comm] using hz'
    have hpoly : (∑ k : Fin (s + 1),
        Polynomial.C (c (z.1, k)) * Polynomial.X ^ (k : ℕ)) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (hd z.1)
    have hcoeff := congrArg (Polynomial.lcoeff ℝ (z.2 : ℕ)) hpoly
    simp only [map_sum, Polynomial.C_mul_X_pow_eq_monomial, map_zero,
      Polynomial.lcoeff_apply] at hcoeff
    have hrewrite :
        (∑ b : Fin (s + 1),
          ((Polynomial.monomial (b : ℕ)) (c (z.1, b))).coeff z.2) =
        ∑ b : Fin (s + 1), if (b : ℕ) = (z.2 : ℕ) then c (z.1, b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Polynomial.coeff_monomial
    rw [hrewrite] at hcoeff
    have hsum :
        (∑ b : Fin (s + 1),
          if (b : ℕ) = (z.2 : ℕ) then c (z.1, b) else 0) = c z := by
      calc
        _ = (if (z.2 : ℕ) = (z.2 : ℕ) then c (z.1, z.2) else 0) := by
          apply Finset.sum_eq_single z.2
          · intro b hb hne
            have hval : (b : ℕ) ≠ (z.2 : ℕ) := fun e => hne (Fin.ext e)
            simp [hval]
          · simp
        _ = c z := by simp
    rw [hsum] at hcoeff
    exact hcoeff
  have hcard := hb.fintype_card_le_finrank
  simpa [b, Fintype.card_prod, Fintype.card_fin] using hcard

noncomputable def lineEquation (p q : PlanePoint) (k : Fin 2) : Poly3 :=
  MvPolynomial.X k.castSucc -
    MvPolynomial.C (linePoint p q 0 k.castSucc) -
      MvPolynomial.C (lineDirection p q k.castSucc) * MvPolynomial.X 2

lemma eval_lineEquation_on_line (p q r s : PlanePoint) (k : Fin 2) (t : ℝ) :
    MvPolynomial.eval (linePoint p q t) (lineEquation r s k) =
      linePoint p q t k.castSucc - linePoint r s t k.castSucc := by
  fin_cases k <;> simp [lineEquation, linePoint, lineDirection] <;> ring

lemma lineContained_lineEquation (p q : PlanePoint) (k : Fin 2) :
    LineContained (lineEquation p q k) (linePoint p q 0) (lineDirection p q) := by
  rw [lineContained_iff]
  intro t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, eval_lineEquation_on_line]
  ring

lemma exists_lineEquation_not_contained
    {p q r s : PlanePoint} (hne : (p, q) ≠ (r, s)) :
    ∃ k : Fin 2,
      ¬ LineContained (lineEquation r s k) (linePoint p q 0) (lineDirection p q) := by
  by_contra h
  push Not at h
  have heq (t : ℝ) : linePoint p q t = linePoint r s t := by
    funext i
    fin_cases i
    · have hz := (lineContained_iff (lineEquation r s 0)
        (linePoint p q 0) (lineDirection p q)).mp (h 0) t
      have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
          linePoint p q t := by
        funext j
        fin_cases j <;> simp [linePoint, lineDirection] <;> ring
      rw [hpoint, eval_lineEquation_on_line] at hz
      exact sub_eq_zero.mp hz
    · have hz := (lineContained_iff (lineEquation r s 1)
        (linePoint p q 0) (lineDirection p q)).mp (h 1) t
      have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
          linePoint p q t := by
        funext j
        fin_cases j <;> simp [linePoint, lineDirection] <;> ring
      rw [hpoint, eval_lineEquation_on_line] at hz
      exact sub_eq_zero.mp hz
    · simp [linePoint]
  exact hne (Prod.ext
    (eq_of_linePoint_eq_at_two (by norm_num : (0 : ℝ) ≠ 1) (heq 0) (heq 1)).1
    (eq_of_linePoint_eq_at_two (by norm_num : (0 : ℝ) ≠ 1) (heq 0) (heq 1)).2)

lemma totalDegree_lineEquation_le (p q : PlanePoint) (k : Fin 2) :
    (lineEquation p q k).totalDegree ≤ 1 := by
  unfold lineEquation
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp
    · simp
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

section Separators

variable {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)

noncomputable def separatorCoordinate (i j : I) : Fin 2 :=
  if h : i = j then 0 else
    Classical.choose (exists_lineEquation_not_contained (hinj.ne h))

noncomputable def lineSeparator (i j : I) : Poly3 :=
  lineEquation (idx j).1 (idx j).2 (separatorCoordinate idx hinj i j)

lemma lineContained_lineSeparator (i j : I) :
    LineContained (lineSeparator idx hinj i j)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) :=
  lineContained_lineEquation _ _ _

lemma not_lineContained_lineSeparator {i j : I} (hij : i ≠ j) :
    ¬ LineContained (lineSeparator idx hinj i j)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2) := by
  unfold lineSeparator separatorCoordinate
  simp only [dif_neg hij]
  exact Classical.choose_spec
    (exists_lineEquation_not_contained (hinj.ne hij))

lemma totalDegree_lineSeparator_le (i j : I) :
    (lineSeparator idx hinj i j).totalDegree ≤ 1 :=
  totalDegree_lineEquation_le _ _ _

noncomputable def lineIsolator (i : I) : Poly3 :=
  ∏ j ∈ (Finset.univ.erase i), lineSeparator idx hinj i j

lemma totalDegree_lineIsolator_le (i : I) :
    (lineIsolator idx hinj i).totalDegree ≤ Fintype.card I - 1 := by
  unfold lineIsolator
  calc
    (∏ j ∈ Finset.univ.erase i, lineSeparator idx hinj i j).totalDegree ≤
        ∑ j ∈ Finset.univ.erase i,
          (lineSeparator idx hinj i j).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact totalDegree_lineSeparator_le idx hinj i j
    _ = Fintype.card I - 1 := by simp

lemma lineRestriction_lineIsolator_ne_zero (i : I) :
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2) ≠ 0 := by
  unfold lineIsolator lineRestriction
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact not_lineContained_lineSeparator idx hinj hji.symm

lemma lineRestriction_lineIsolator_eq_zero {i j : I} (hij : i ≠ j) :
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) = 0 := by
  unfold lineIsolator lineRestriction
  rw [map_prod]
  apply Finset.prod_eq_zero (i := j)
  · exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
  · exact lineContained_lineSeparator idx hinj i j

end Separators

noncomputable def lineRestrictionLinear (T : ℕ) (x v : Fin 3 → ℝ) :
    DegreeLE T →ₗ[ℝ] Polynomial ℝ :=
  (MvPolynomial.aeval
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))).toLinearMap.comp
      (MvPolynomial.restrictTotalDegree (Fin 3) ℝ T).subtype

lemma lineRestrictionLinear_apply (T : ℕ) (x v : Fin 3 → ℝ) (F : DegreeLE T) :
    lineRestrictionLinear T x v F = lineRestriction F.1 x v := by
  simp [lineRestrictionLinear, lineRestriction, MvPolynomial.aeval_def]

lemma lineRestriction_X_two (p q : PlanePoint) :
    lineRestriction (MvPolynomial.X 2 : Poly3)
      (linePoint p q 0) (lineDirection p q) = Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [eval_lineRestriction]
  simp [linePoint, lineDirection]

noncomputable def isolatorPower
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    (s : ℕ) (z : I × Fin (s + 1)) : DegreeLE (Fintype.card I - 1 + s) :=
  ⟨lineIsolator idx hinj z.1 * MvPolynomial.X 2 ^ (z.2 : ℕ), by
    rw [MvPolynomial.mem_restrictTotalDegree]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hH := totalDegree_lineIsolator_le idx hinj z.1
    rw [MvPolynomial.totalDegree_X_pow]
    have hk : (z.2 : ℕ) ≤ s := by omega
    omega⟩

lemma line_family_quotient_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q R : Poly3} {a b s : ℕ}
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ Fintype.card I - 1 + s)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hRlines : ∀ i, LineContained R
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2)) :
    Fintype.card I * (s + 1) ≤
      Module.finrank ℝ
        (DegreeLE (Fintype.card I - 1 + s) ⧸
          (LinearMap.range (mulDegreeLE Q a (Fintype.card I - 1 + s)
              hQa (by omega)) ⊔
            LinearMap.range (mulDegreeLE R b (Fintype.card I - 1 + s)
              hRb (by omega)))) := by
  let T := Fintype.card I - 1 + s
  let U : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE Q a T hQa (by dsimp [T]; omega)) ⊔
      LinearMap.range (mulDegreeLE R b T hRb (by dsimp [T]; omega))
  let φ : I → DegreeLE T →ₗ[ℝ] Polynomial ℝ := fun i =>
    lineRestrictionLinear T (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2)
  let d : I → Polynomial ℝ := fun i =>
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2)
  have hd : ∀ i, d i ≠ 0 := lineRestriction_lineIsolator_ne_zero idx hinj
  have hF : ∀ j i k, φ j (isolatorPower idx hinj s (i, k)) =
      if i = j then d j * Polynomial.X ^ (k : ℕ) else 0 := by
    intro j i k
    dsimp [φ]
    rw [lineRestrictionLinear_apply]
    change lineRestriction
      (lineIsolator idx hinj i * MvPolynomial.X 2 ^ (k : ℕ))
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = _
    rw [lineRestriction_mul]
    have hpow : lineRestriction (MvPolynomial.X 2 ^ (k : ℕ) : Poly3)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = Polynomial.X ^ (k : ℕ) := by
      unfold lineRestriction
      rw [map_pow]
      exact congrArg (fun F : Polynomial ℝ => F ^ (k : ℕ))
        (lineRestriction_X_two (idx j).1 (idx j).2)
    rw [hpow]
    by_cases hij : i = j
    · subst i
      simp [d]
    · rw [lineRestriction_lineIsolator_eq_zero idx hinj hij]
      simp [hij]
  have hU : ∀ j G, G ∈ U → φ j G = 0 := by
    intro j G hG
    rcases Submodule.mem_sup.mp hG with ⟨Y, hY, Z, hZ, rfl⟩
    rw [map_add]
    have hY0 : φ j Y = 0 := by
      obtain ⟨A, hA⟩ := hY
      rw [← hA]
      dsimp [φ]
      rw [lineRestrictionLinear_apply]
      change lineRestriction (Q * A.1)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = 0
      rw [lineRestriction_mul, hQlines j, zero_mul]
    have hZ0 : φ j Z = 0 := by
      obtain ⟨B, hB⟩ := hZ
      rw [← hB]
      dsimp [φ]
      rw [lineRestrictionLinear_apply]
      change lineRestriction (R * B.1)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = 0
      rw [lineRestriction_mul, hRlines j, zero_mul]
    rw [hY0, hZ0, add_zero]
  have hlow := finrank_quotient_ge_of_diagonal U
    (isolatorPower idx hinj s) φ d hd hF hU
  simpa [T, U] using hlow

/-- A finite family of distinct normalized Elekes--Sharir lines contained in
two coprime surfaces is uniformly bounded in terms of their degrees.  The
constant is deliberately coarse; only its independence of the line family is
used in the incidence argument. -/
lemma card_le_of_lines_in_two_surfaces
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q R : Poly3} {a b : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hRlines : ∀ i, LineContained R
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2)) :
    Fintype.card I ≤ a * b * (2 * (a * b) + a + b + 2) := by
  let m := Fintype.card I
  let s := 2 * (a * b) + a + b + 1
  let T := m - 1 + s
  by_cases hm0 : m = 0
  · simp [m, hm0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hT : a + b ≤ T := by
    dsimp [T, s]
    omega
  have hlo := line_family_quotient_lower idx hinj hQa hRb hT hQlines hRlines
  have hup := finrank_quotient_principalParts_le hQ0 hR0 hQirr hQnotR
    hQa hRb hT
  have hbound : m * (s + 1) ≤ a * b * (T + 2) := by
    exact hlo.trans hup
  have hmone : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
  dsimp [m, s, T] at hbound ⊢
  have hleft : 2 * (a * b) + a + b + 1 + 1 =
      2 * (a * b) + a + b + 2 := by omega
  have hright : Fintype.card I - 1 + (2 * (a * b) + a + b + 1) + 2 =
      Fintype.card I + (2 * (a * b) + a + b + 2) := by
    dsimp [m] at hmpos
    omega
  rw [hleft, hright] at hbound
  have hL : Fintype.card I * (2 * (a * b) + a + b + 2) =
      Fintype.card I * (a * b) +
        Fintype.card I * (a * b + a + b + 2) := by ring
  have hR : a * b * (Fintype.card I + (2 * (a * b) + a + b + 2)) =
      Fintype.card I * (a * b) +
        a * b * (2 * (a * b) + a + b + 2) := by ring
  rw [hL, hR] at hbound
  have hmid : Fintype.card I * (a * b + a + b + 2) ≤
      a * b * (2 * (a * b) + a + b + 2) := by omega
  calc
    Fintype.card I = Fintype.card I * 1 := by omega
    _ ≤ Fintype.card I * (a * b + a + b + 2) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ a * b * (2 * (a * b) + a + b + 2) := hmid

end Erdos95.Hilbert
