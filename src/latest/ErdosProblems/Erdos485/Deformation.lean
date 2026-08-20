import ErdosProblems.Erdos485.Normalization
import ErdosProblems.Erdos485.Dirichlet
import ErdosProblems.Erdos485.Bivariate

/-!
# The Dirichlet deformation in Schinzel's proof

This file implements the passage from a primitively normalized square to the
small bivariate polynomial used in the squarefree-gap argument.
-/

namespace Erdos485

open Polynomial
open scoped BigOperators

noncomputable section

/-- The `j`-th interior position in a list of length `t`. -/
def middleIndex {t : ℕ} (ht : 2 ≤ t) (j : Fin (t - 2)) : Fin t :=
  ⟨j.1 + 1, by omega⟩

theorem middleIndex_ne_zero {t : ℕ} (ht : 2 ≤ t) (j : Fin (t - 2)) :
    middleIndex ht j ≠ ⟨0, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  simp [middleIndex] at this

theorem middleIndex_ne_last {t : ℕ} (ht : 3 ≤ t) (j : Fin (t - 2)) :
    middleIndex (by omega : 2 ≤ t) j ≠ ⟨t - 1, by omega⟩ := by
  intro h
  have hj := j.2
  have := congrArg Fin.val h
  simp [middleIndex] at this
  omega

/-- The first exponent of a primitive normalized square is zero. -/
def PrimitiveNormalization.firstSqIndex {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) : Fin (N.poly ^ 2).support.card :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 3) N.three_le_sq_support⟩

def PrimitiveNormalization.lastSqIndex {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) : Fin (N.poly ^ 2).support.card :=
  ⟨(N.poly ^ 2).support.card - 1,
    Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 3) N.three_le_sq_support) (by decide)⟩

theorem PrimitiveNormalization.sqExponent_zero {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    N.sqExponent N.firstSqIndex = 0 := by
  let S := (N.poly ^ 2).support
  have hzero : 0 ∈ S := by
    rw [Polynomial.mem_support_iff]
    simpa [S, pow_two] using pow_ne_zero 2 N.coeff_zero_ne
  rw [PrimitiveNormalization.sqExponent]
  unfold PrimitiveNormalization.firstSqIndex
  rw [Finset.orderEmbOfFin_zero rfl
    (lt_of_lt_of_le (by decide : 0 < 3) N.three_le_sq_support)]
  exact Nat.eq_zero_of_le_zero (Finset.min'_le S 0 hzero)

/-- The final exponent of a primitive normalized square is its natural degree. -/
theorem PrimitiveNormalization.sqExponent_last {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    N.sqExponent N.lastSqIndex =
      (N.poly ^ 2).natDegree := by
  have hsq : N.poly ^ 2 ≠ 0 := by
    intro h
    have : (N.poly ^ 2).coeff 0 = 0 := by simp [h]
    have hn : (N.poly ^ 2).coeff 0 ≠ 0 := by
      simpa [pow_two] using pow_ne_zero 2 N.coeff_zero_ne
    exact hn this
  rw [PrimitiveNormalization.sqExponent]
  unfold PrimitiveNormalization.lastSqIndex
  rw [Finset.orderEmbOfFin_last rfl
    (lt_of_lt_of_le (by decide : 0 < 3) N.three_le_sq_support)]
  exact (Polynomial.natDegree_eq_support_max' hsq).symm

/-- Data produced by the nontrivial branch of the Dirichlet deformation. -/
structure Deformation {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) where
  q : ℕ
  q_pos : 1 ≤ q
  q_le : q ≤ 8 ^ ((N.poly ^ 2).support.card - 2)
  p : Fin (N.poly ^ 2).support.card → ℕ
  p_zero : p N.firstSqIndex = 0
  p_last : p N.lastSqIndex = q
  residual : Fin (N.poly ^ 2).support.card → ℤ
  residual_eq : ∀ j, residual j =
    (q : ℤ) * N.sqExponent j - ((N.poly ^ 2).natDegree : ℤ) * p j
  residual_zero : residual N.firstSqIndex = 0
  residual_last : residual N.lastSqIndex = 0
  residual_abs_lt : ∀ j, (8 : ℝ) * |(residual j : ℝ)| < (N.poly ^ 2).natDegree
  some_residual_ne : ∃ j, residual j ≠ 0
  shift : ℤ
  shift_le : ∀ j, shift ≤ residual j
  shift_mem : ∃ j, shift = residual j
  shift_nonpos : shift ≤ 0
  zExponent : Fin (N.poly ^ 2).support.card → ℕ
  zExponent_eq : ∀ j, zExponent j = Int.toNat (residual j - shift)
  pair_injective : Function.Injective (fun j ↦ (p j, zExponent j))
  F : BiPolynomial K
  F_eq : F = ∑ j, biMonomial (p j) (zExponent j)
    ((N.poly ^ 2).coeff (N.sqExponent j))
  exponentPairs_eq : exponentPairs F =
    Finset.univ.image (fun j ↦ (p j, zExponent j))
  card_exponentPairs : (exponentPairs F).card = (N.poly ^ 2).support.card
  four_mul_zExponent_lt : ∀ j, 4 * zExponent j < (N.poly ^ 2).natDegree
  zDegreeLT : ZDegreeLT (N.poly ^ 2).natDegree F
  coeff_y_zero_ne : biCoeff F 0 (zExponent N.firstSqIndex) ≠ 0
  coeff_z_zero_ne : ∃ a, biCoeff F a 0 ≠ 0
  specialize_eq : specialize (N.poly ^ 2).natDegree F =
    (N.poly.comp (X ^ q)) ^ 2 * X ^ Int.toNat (-shift)

/-- Extend data on the interior indices by prescribed endpoint values. -/
def extendInterior {t : ℕ} (ht : 3 ≤ t) (left right : ℕ)
    (u : Fin (t - 2) → ℕ) (j : Fin t) : ℕ :=
  if j.1 = 0 then left
  else if j.1 = t - 1 then right
  else u ⟨(j.1 - 1) % (t - 2), Nat.mod_lt _ (by omega)⟩

@[simp] theorem extendInterior_first {t : ℕ} (ht : 3 ≤ t) (left right : ℕ)
    (u : Fin (t - 2) → ℕ) :
    extendInterior ht left right u ⟨0, by omega⟩ = left := by
  simp [extendInterior]

@[simp] theorem extendInterior_last {t : ℕ} (ht : 3 ≤ t) (left right : ℕ)
    (u : Fin (t - 2) → ℕ) :
    extendInterior ht left right u ⟨t - 1, by omega⟩ = right := by
  have hne : t - 1 ≠ 0 := by omega
  simp [extendInterior, hne]

@[simp] theorem extendInterior_middle {t : ℕ} (ht : 3 ≤ t) (left right : ℕ)
    (u : Fin (t - 2) → ℕ) (i : Fin (t - 2)) :
    extendInterior ht left right u (middleIndex (by omega) i) = u i := by
  have h0 : i.1 + 1 ≠ 0 := by omega
  have hlast : i.1 + 1 ≠ t - 1 := by
    have hi := i.2
    omega
  simp only [extendInterior, middleIndex, h0, hlast, if_false]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.2]

/-- The simultaneous approximation, including its two exact endpoints. -/
structure DirichletData {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) where
  q : ℕ
  q_pos : 1 ≤ q
  q_le : q ≤ 8 ^ ((N.poly ^ 2).support.card - 2)
  p : Fin (N.poly ^ 2).support.card → ℕ
  p_zero : p N.firstSqIndex = 0
  p_last : p N.lastSqIndex = q
  residual : Fin (N.poly ^ 2).support.card → ℤ
  residual_eq : ∀ j, residual j =
    (q : ℤ) * N.sqExponent j - ((N.poly ^ 2).natDegree : ℤ) * p j
  residual_zero : residual N.firstSqIndex = 0
  residual_last : residual N.lastSqIndex = 0
  residual_abs_lt : ∀ j, (8 : ℝ) * |(residual j : ℝ)| < (N.poly ^ 2).natDegree

theorem PrimitiveNormalization.natDegree_sq_pos {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) : 0 < (N.poly ^ 2).natDegree := by
  by_contra h
  have hdeg : (N.poly ^ 2).natDegree = 0 := by omega
  have hsub : (N.poly ^ 2).support ⊆ {0} := by
    intro i hi
    have := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    simp only [hdeg, Finset.mem_singleton]
    omega
  have := Finset.card_le_card hsub
  simp at this
  have hthree := N.three_le_sq_support
  omega

/-- Dirichlet's box lemma applied to the interior normalized exponents. -/
theorem exists_dirichletData {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P)
    (ht : 4 ≤ (N.poly ^ 2).support.card) : Nonempty (DirichletData N) := by
  classical
  let t := (N.poly ^ 2).support.card
  let n := (N.poly ^ 2).natDegree
  have ht3 : 3 ≤ t := by omega
  have hn : 0 < n := N.natDegree_sq_pos
  let alpha : Fin (t - 2) → ℝ := fun i ↦
    (N.sqExponent (middleIndex (by omega) i) : ℝ) / n
  have halpha : ∀ i, 0 < alpha i ∧ alpha i < 1 := by
    intro i
    have hfirst : N.firstSqIndex < middleIndex (by omega) i := by
      apply Fin.mk_lt_mk.mpr
      simp [PrimitiveNormalization.firstSqIndex, middleIndex]
    have hlast : middleIndex (by omega) i < N.lastSqIndex := by
      apply Fin.mk_lt_mk.mpr
      change i.1 + 1 < t - 1
      have hi := i.2
      omega
    have hpos : 0 < N.sqExponent (middleIndex (by omega) i) := by
      rw [← N.sqExponent_zero]
      exact N.sqExponent.strictMono hfirst
    have hlt : N.sqExponent (middleIndex (by omega) i) < n := by
      change N.sqExponent (middleIndex (by omega) i) < (N.poly ^ 2).natDegree
      rw [← N.sqExponent_last]
      exact N.sqExponent.strictMono hlast
    constructor
    · exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast hn)
    · rw [div_lt_one (by exact_mod_cast hn)]
      exact_mod_cast hlt
  obtain ⟨q, pInt, hqpos, hqle, happ, hpInt⟩ :=
    finite_simultaneous_dirichlet (m := t - 2) (Q := 8) (by omega) (by omega)
      alpha halpha
  let pMid : Fin (t - 2) → ℕ := fun i ↦ Int.toNat (pInt i)
  have hpMid_cast : ∀ i, (pMid i : ℤ) = pInt i := by
    intro i
    exact Int.toNat_of_nonneg (hpInt i).1
  let p : Fin t → ℕ := extendInterior ht3 0 q pMid
  let residual : Fin t → ℤ := fun j ↦
    (q : ℤ) * N.sqExponent j - (n : ℤ) * p j
  have hpzero : p N.firstSqIndex = 0 := by
    have hi : N.firstSqIndex = (⟨0, by omega⟩ : Fin t) := by
      apply Fin.ext
      rfl
    rw [hi]
    exact extendInterior_first ht3 0 q pMid
  have hplast : p N.lastSqIndex = q := by
    have hi : N.lastSqIndex = (⟨t - 1, by omega⟩ : Fin t) := by
      apply Fin.ext
      rfl
    rw [hi]
    exact extendInterior_last ht3 0 q pMid
  have hrzero : residual N.firstSqIndex = 0 := by
    simp [residual, hpzero, N.sqExponent_zero]
  have hrlast : residual N.lastSqIndex = 0 := by
    dsimp [residual]
    rw [hplast, N.sqExponent_last]
    dsimp [n]
    push_cast
    ring
  have hrabs : ∀ j, (8 : ℝ) * |(residual j : ℝ)| < n := by
    intro j
    by_cases h0 : j.1 = 0
    · have hj : j = N.firstSqIndex := by
        apply Fin.ext
        simpa [PrimitiveNormalization.firstSqIndex]
      rw [hj, hrzero]
      norm_num
      exact_mod_cast hn
    by_cases hlast : j.1 = t - 1
    · have hj : j = N.lastSqIndex := by
        apply Fin.ext
        simpa [PrimitiveNormalization.lastSqIndex]
      rw [hj, hrlast]
      norm_num
      exact_mod_cast hn
    · let i : Fin (t - 2) := ⟨j.1 - 1, by omega⟩
      have hj : j = middleIndex (by omega) i := by
        apply Fin.ext
        simp [i, middleIndex]
        omega
      have hpj : p j = pMid i := by
        rw [hj]
        exact extendInterior_middle ht3 0 q pMid i
      have happrox := happ i
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hrewrite :
          alpha i - (pInt i : ℝ) / q =
            ((residual j : ℤ) : ℝ) / ((n : ℝ) * q) := by
        simp only [alpha, residual, hpMid_cast]
        rw [hpj, hpMid_cast, hj]
        push_cast
        field_simp
      rw [hrewrite] at happrox
      rw [abs_div, abs_of_pos (mul_pos hnR hqR)] at happrox
      have hscaled := (div_lt_iff₀ (mul_pos hnR hqR)).mp happrox
      have hrhs :
          (1 : ℝ) / ((8 : ℕ) * q) * (n * q) = n / 8 := by
        push_cast
        field_simp
        <;> ring
      rw [hrhs] at hscaled
      nlinarith
  exact ⟨{
    q := q
    q_pos := hqpos
    q_le := by simpa [t] using hqle
    p := p
    p_zero := hpzero
    p_last := hplast
    residual := residual
    residual_eq := by intro j; rfl
    residual_zero := hrzero
    residual_last := hrlast
    residual_abs_lt := by simpa [n] using hrabs }⟩

/-- If every residual vanishes, primitivity forces the top exponent to divide
the Dirichlet denominator, giving Schinzel's elementary branch. -/
theorem DirichletData.small_bound_of_all_residual_zero
    {K : Type*} [Field K] [CharZero K] {P : K[X]}
    {N : PrimitiveNormalization P} (D : DirichletData N)
    (hall : ∀ j, D.residual j = 0) :
    N.poly.support.card ≤
      1 + 8 ^ ((N.poly ^ 2).support.card - 2) / 2 := by
  classical
  let n := (N.poly ^ 2).natDegree
  have hdiv_each : ∀ e ∈ (N.poly ^ 2).support, n ∣ D.q * e := by
    intro e he
    have herange : e ∈ Set.range N.sqExponent := by
      rw [N.sqExponent_range]
      exact he
    obtain ⟨j, rfl⟩ := herange
    have hr := D.residual_eq j
    rw [hall j] at hr
    have heqI : (D.q : ℤ) * N.sqExponent j =
        (n : ℤ) * D.p j := by
      dsimp [n]
      omega
    have heqN : D.q * N.sqExponent j = n * D.p j := by
      exact_mod_cast heqI
    exact ⟨D.p j, heqN⟩
  have hdivg : n ∣ (N.poly ^ 2).support.gcd (fun e ↦ D.q * e) :=
    Finset.dvd_gcd hdiv_each
  have hnq : n ∣ D.q := by
    rw [Finset.gcd_mul_left] at hdivg
    have hgcd : (N.poly ^ 2).support.gcd (fun e ↦ e) = 1 := by
      change (N.poly ^ 2).support.gcd id = 1
      exact N.primitive_sq_support
    rw [hgcd] at hdivg
    simpa using hdivg
  have hnleq : n ≤ D.q := Nat.le_of_dvd D.q_pos hnq
  have hsupp_le : N.poly.support.card ≤ N.poly.natDegree + 1 := by
    have hc : N.poly.support.card ≤ (Finset.range (N.poly.natDegree + 1)).card := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp he))
    simpa using hc
  have hdeg : n = 2 * N.poly.natDegree := N.natDegree_sq
  have hhalf : N.poly.natDegree ≤ D.q / 2 := by
    omega
  exact hsupp_le.trans (by
    have := D.q_le
    omega)

theorem biCoeff_finset_sum {K I : Type*} [Semiring K] [DecidableEq I]
    (s : Finset I) (H : I → BiPolynomial K) (a b : ℕ) :
    biCoeff (∑ i ∈ s, H i) a b = ∑ i ∈ s, biCoeff (H i) a b := by
  simp [biCoeff]

theorem exponentPairs_sum_biMonomial {K I : Type*} [Semiring K]
    [Fintype I] [DecidableEq I] (a b : I → ℕ) (c : I → K)
    (hc : ∀ i, c i ≠ 0) (hinj : Function.Injective (fun i ↦ (a i, b i))) :
    exponentPairs (∑ i, biMonomial (a i) (b i) (c i)) =
      Finset.univ.image (fun i ↦ (a i, b i)) := by
  classical
  ext ab
  rw [Finset.mem_image]
  rw [mem_exponentPairs_iff]
  rw [show (∑ i, biMonomial (a i) (b i) (c i)) =
      ∑ i ∈ Finset.univ, biMonomial (a i) (b i) (c i) by simp]
  rw [biCoeff_finset_sum]
  constructor
  · intro h
    obtain ⟨i, hi, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hp : ab = (a i, b i) := by
      by_contra hp
      have : biCoeff (biMonomial (a i) (b i) (c i)) ab.1 ab.2 = 0 := by
        rw [biCoeff_biMonomial]
        have hpair : ¬ (ab.1 = a i ∧ ab.2 = b i) := by
          intro hpair
          exact hp (Prod.ext hpair.1 hpair.2)
        simp [hpair]
      exact hterm this
    exact ⟨i, hi, hp.symm⟩
  · rintro ⟨i, -, rfl⟩
    rw [Finset.sum_eq_single i]
    · simpa using hc i
    · intro j _ hji
      rw [biCoeff_biMonomial]
      split
      · rename_i hpair
        exfalso
        apply hji
        apply hinj
        exact Prod.ext hpair.1.symm hpair.2.symm
      · rfl
    · simp

theorem sum_monomial_sqExponent {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    (∑ j, monomial (N.sqExponent j)
      ((N.poly ^ 2).coeff (N.sqExponent j))) = N.poly ^ 2 := by
  classical
  have hmap : Finset.univ.map N.sqExponent.toEmbedding = (N.poly ^ 2).support :=
    Finset.map_orderEmbOfFin_univ _ rfl
  calc
    (∑ j, monomial (N.sqExponent j)
      ((N.poly ^ 2).coeff (N.sqExponent j))) =
        ∑ j ∈ Finset.univ, monomial (N.sqExponent j)
          ((N.poly ^ 2).coeff (N.sqExponent j)) := by simp
    _ = ∑ e ∈ Finset.univ.map N.sqExponent.toEmbedding,
        monomial e ((N.poly ^ 2).coeff e) := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ e ∈ (N.poly ^ 2).support,
        monomial e ((N.poly ^ 2).coeff e) := by rw [hmap]
    _ = (N.poly ^ 2).sum (fun e c ↦ monomial e c) := by
      rw [Polynomial.sum_def]
    _ = N.poly ^ 2 := Polynomial.sum_monomial_eq _

theorem comp_X_pow_eq_sum_sqExponent {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) (q : ℕ) :
    (N.poly ^ 2).comp (X ^ q) =
      ∑ j, monomial (q * N.sqExponent j)
        ((N.poly ^ 2).coeff (N.sqExponent j)) := by
  classical
  calc
    (N.poly ^ 2).comp (X ^ q) =
        (∑ j, monomial (N.sqExponent j)
          ((N.poly ^ 2).coeff (N.sqExponent j))).comp (X ^ q) := by
      rw [sum_monomial_sqExponent]
    _ = ∑ j, (monomial (N.sqExponent j)
          ((N.poly ^ 2).coeff (N.sqExponent j))).comp (X ^ q) := by
      rw [Polynomial.sum_comp]
    _ = ∑ j, monomial (q * N.sqExponent j)
          ((N.poly ^ 2).coeff (N.sqExponent j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial]

/-- A nonzero residual produces the shifted ordinary bivariate deformation. -/
theorem DirichletData.toDeformation_of_some_residual_ne
    {K : Type*} [Field K] [CharZero K] {P : K[X]}
    {N : PrimitiveNormalization P} (D : DirichletData N)
    (hsome : ∃ j, D.residual j ≠ 0) : Nonempty (Deformation N) := by
  classical
  let R : Finset ℤ := Finset.univ.image D.residual
  have hR : R.Nonempty := by
    refine ⟨D.residual N.firstSqIndex, ?_⟩
    simp [R]
  let shift : ℤ := R.min' hR
  have hshift_le : ∀ j, shift ≤ D.residual j := by
    intro j
    apply Finset.min'_le
    simp [R]
  have hshift_mem : ∃ j, shift = D.residual j := by
    have hm : shift ∈ R := Finset.min'_mem R hR
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, hj.symm⟩
  have hshift_nonpos : shift ≤ 0 := by
    simpa [D.residual_zero] using hshift_le N.firstSqIndex
  let zExponent : Fin (N.poly ^ 2).support.card → ℕ := fun j ↦
    Int.toNat (D.residual j - shift)
  have hzcast : ∀ j, (zExponent j : ℤ) = D.residual j - shift := by
    intro j
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (hshift_le j))
  have hpairinj : Function.Injective (fun j ↦ (D.p j, zExponent j)) := by
    intro i j hij
    have hp : D.p i = D.p j := congrArg Prod.fst hij
    have hz : zExponent i = zExponent j := congrArg Prod.snd hij
    have hr : D.residual i = D.residual j := by
      have hzI : (zExponent i : ℤ) = zExponent j := by exact_mod_cast hz
      rw [hzcast i, hzcast j] at hzI
      omega
    have heqI : (D.q : ℤ) * N.sqExponent i =
        (D.q : ℤ) * N.sqExponent j := by
      rw [D.residual_eq i, D.residual_eq j] at hr
      rw [hp] at hr
      omega
    have heqN : D.q * N.sqExponent i = D.q * N.sqExponent j := by
      exact_mod_cast heqI
    apply N.sqExponent.injective
    exact Nat.eq_of_mul_eq_mul_left D.q_pos heqN
  let F : BiPolynomial K :=
    ∑ j, biMonomial (D.p j) (zExponent j)
      ((N.poly ^ 2).coeff (N.sqExponent j))
  have hc : ∀ j, (N.poly ^ 2).coeff (N.sqExponent j) ≠ 0 := by
    intro j
    exact Polynomial.mem_support_iff.mp (N.sqExponent_mem j)
  have hFpair : exponentPairs F =
      Finset.univ.image (fun j ↦ (D.p j, zExponent j)) := by
    exact exponentPairs_sum_biMonomial D.p zExponent _ hc hpairinj
  have hzquarter : ∀ j, 4 * zExponent j < (N.poly ^ 2).natDegree := by
    intro j
    obtain ⟨k, hk⟩ := hshift_mem
    have hjabs := D.residual_abs_lt j
    have hkabs := D.residual_abs_lt k
    have hshift : shift = D.residual k := hk
    have hzR : (zExponent j : ℝ) =
        (D.residual j : ℝ) - (shift : ℝ) := by
      exact_mod_cast hzcast j
    have hjle : (D.residual j : ℝ) ≤ |(D.residual j : ℝ)| := le_abs_self _
    have hkle : -(D.residual k : ℝ) ≤ |(D.residual k : ℝ)| := neg_le_abs _
    have hzreal : (4 : ℝ) * zExponent j < (N.poly ^ 2).natDegree := by
      rw [hzR, hshift]
      nlinarith
    exact_mod_cast hzreal
  have hZdeg : ZDegreeLT (N.poly ^ 2).natDegree F := by
    intro a ha
    have hca : F.coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
    have hlead : (F.coeff a).coeff (F.coeff a).natDegree ≠ 0 :=
      by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hca
    have hab : (a, (F.coeff a).natDegree) ∈ exponentPairs F := by
      rw [mem_exponentPairs_iff]
      exact hlead
    rw [hFpair] at hab
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hab
    have hb : (F.coeff a).natDegree = zExponent j := (congrArg Prod.snd hj).symm
    rw [hb]
    exact (show zExponent j ≤ 4 * zExponent j by omega).trans_lt (hzquarter j)
  have hcoeff_y : biCoeff F 0 (zExponent N.firstSqIndex) ≠ 0 := by
    apply (mem_exponentPairs_iff F 0 (zExponent N.firstSqIndex)).mp
    rw [hFpair]
    refine Finset.mem_image.mpr ⟨N.firstSqIndex, Finset.mem_univ _, ?_⟩
    simp [D.p_zero]
  have hcoeff_z : ∃ a, biCoeff F a 0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hshift_mem
    have hzk : zExponent k = 0 := by
      have hzI : (zExponent k : ℤ) = 0 := by
        rw [hzcast, ← hk]
        ring
      exact_mod_cast hzI
    refine ⟨D.p k, ?_⟩
    apply (mem_exponentPairs_iff F (D.p k) 0).mp
    rw [hFpair]
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
    simp [hzk]
  have hshiftNat : (Int.toNat (-shift) : ℤ) = -shift :=
    Int.toNat_of_nonneg (neg_nonneg.mpr hshift_nonpos)
  have hweight : ∀ j,
      (N.poly ^ 2).natDegree * D.p j + zExponent j =
        D.q * N.sqExponent j + Int.toNat (-shift) := by
    intro j
    have hInt : ((N.poly ^ 2).natDegree : ℤ) * D.p j + zExponent j =
        (D.q : ℤ) * N.sqExponent j + Int.toNat (-shift) := by
      rw [hzcast, hshiftNat, D.residual_eq]
      ring
    exact_mod_cast hInt
  have hFspec : specialize (N.poly ^ 2).natDegree F =
      ∑ j, monomial (D.q * N.sqExponent j + Int.toNat (-shift))
        ((N.poly ^ 2).coeff (N.sqExponent j)) := by
    dsimp [F]
    change (evalRingHom (X ^ (N.poly ^ 2).natDegree))
      (∑ j, biMonomial (D.p j) (zExponent j)
        ((N.poly ^ 2).coeff (N.sqExponent j))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs := specialize_biMonomial (K := K) (N.poly ^ 2).natDegree
      (D.p j) (zExponent j) ((N.poly ^ 2).coeff (N.sqExponent j))
    change (evalRingHom (X ^ (N.poly ^ 2).natDegree))
      (biMonomial (D.p j) (zExponent j)
        ((N.poly ^ 2).coeff (N.sqExponent j))) = _ at hs
    rw [hs]
    rw [hweight]
  have hsqcomp : (N.poly.comp (X ^ D.q)) ^ 2 =
      ∑ j, monomial (D.q * N.sqExponent j)
        ((N.poly ^ 2).coeff (N.sqExponent j)) := by
    rw [show (N.poly.comp (X ^ D.q)) ^ 2 =
      (N.poly ^ 2).comp (X ^ D.q) by simp [pow_two, Polynomial.mul_comp]]
    exact comp_X_pow_eq_sum_sqExponent N D.q
  have hspec : specialize (N.poly ^ 2).natDegree F =
      (N.poly.comp (X ^ D.q)) ^ 2 * X ^ Int.toNat (-shift) := by
    rw [hFspec, hsqcomp, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [monomial_mul_X_pow]
  exact ⟨{
    q := D.q
    q_pos := D.q_pos
    q_le := D.q_le
    p := D.p
    p_zero := D.p_zero
    p_last := D.p_last
    residual := D.residual
    residual_eq := D.residual_eq
    residual_zero := D.residual_zero
    residual_last := D.residual_last
    residual_abs_lt := D.residual_abs_lt
    some_residual_ne := hsome
    shift := shift
    shift_le := hshift_le
    shift_mem := hshift_mem
    shift_nonpos := hshift_nonpos
    zExponent := zExponent
    zExponent_eq := by intro j; rfl
    pair_injective := hpairinj
    F := F
    F_eq := rfl
    exponentPairs_eq := hFpair
    card_exponentPairs := by
      rw [hFpair, Finset.card_image_of_injective _ hpairinj]
      simp
    four_mul_zExponent_lt := hzquarter
    zDegreeLT := hZdeg
    coeff_y_zero_ne := hcoeff_y
    coeff_z_zero_ne := hcoeff_z
    specialize_eq := hspec }⟩

/-- The complete Dirichlet-deformation alternative for a normalized square. -/
theorem primitiveNormalization_deformation
    {K : Type*} [Field K] [CharZero K] {P : K[X]}
    (N : PrimitiveNormalization P)
    (ht : 4 ≤ (N.poly ^ 2).support.card) :
    N.poly.support.card ≤
        1 + 8 ^ ((N.poly ^ 2).support.card - 2) / 2 ∨
      Nonempty (Deformation N) := by
  obtain ⟨D⟩ := exists_dirichletData N ht
  by_cases hall : ∀ j, D.residual j = 0
  · exact Or.inl (D.small_bound_of_all_residual_zero hall)
  · push_neg at hall
    exact Or.inr (D.toDeformation_of_some_residual_ne hall)

end

end Erdos485
