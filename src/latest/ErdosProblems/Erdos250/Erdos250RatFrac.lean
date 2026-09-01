import Mathlib

open scoped BigOperators

noncomputable section

namespace DoublePartialFraction

open Polynomial

variable {K ι : Type*} [Field K] [DecidableEq ι]

def lin (r : ι → K) (i : ι) : K[X] := X - C (r i)

def rest (s : Finset ι) (r : ι → K) (i : ι) : K[X] :=
  ∏ k ∈ s.erase i, (lin r k) ^ 2

def den (s : Finset ι) (r : ι → K) : K[X] :=
  ∏ k ∈ s, (lin r k) ^ 2

def B (s : Finset ι) (r : ι → K) (P : K[X]) (i : ι) : K :=
  P.eval (r i) / (rest s r i).eval (r i)

def A (s : Finset ι) (r : ι → K) (P : K[X]) (i : ι) : K :=
  (P.derivative.eval (r i) - B s r P i * (rest s r i).derivative.eval (r i)) /
    (rest s r i).eval (r i)

def numerator (s : Finset ι) (r : ι → K) (P : K[X]) : K[X] :=
  ∑ i ∈ s, (C (A s r P i) * lin r i + C (B s r P i)) * rest s r i

omit [DecidableEq ι] in
@[simp] lemma eval_lin (r : ι → K) (i : ι) (x : K) :
    (lin r i).eval x = x - r i := by simp [lin]

omit [DecidableEq ι] in
@[simp] lemma derivative_lin (r : ι → K) (i : ι) :
    (lin r i).derivative = 1 := by simp [lin]

lemma rest_eval_ne_zero {s : Finset ι} {r : ι → K}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (rest s r i).eval (r i) ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  apply pow_ne_zero
  exact sub_ne_zero.mpr fun h ↦
    (Finset.ne_of_mem_erase hk).symm (hr hi (Finset.mem_of_mem_erase hk) h)

lemma rest_eval_eq_zero {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s r k).eval (r i) = 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hi⟩)
  simp

lemma sq_dvd_rest {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (lin r i) ^ 2 ∣ rest s r k := by
  exact Finset.dvd_prod_of_mem (fun j ↦ (lin r j) ^ 2)
    (Finset.mem_erase.mpr ⟨hik, hi⟩)

lemma eval_derivative_eq_zero_of_sq_dvd {p : K[X]} {x : K}
    (h : (X - C x) ^ 2 ∣ p) : p.derivative.eval x = 0 := by
  rcases h with ⟨q, rfl⟩
  simp [derivative_mul, derivative_pow]

lemma rest_derivative_eval_eq_zero {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s r k).derivative.eval (r i) = 0 := by
  apply eval_derivative_eq_zero_of_sq_dvd
  simpa [lin] using sq_dvd_rest (r := r) hi hik

lemma numerator_eval {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s r P).eval (r i) = P.eval (r i) := by
  rw [numerator, eval_finsetSum]
  simp_rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_lin]
  rw [Finset.sum_eq_single i]
  · simp [B, rest_eval_ne_zero hr hi]
  · intro k hk hki
    rw [rest_eval_eq_zero hi hki.symm, mul_zero]
  · exact fun h ↦ (h hi).elim

lemma numerator_derivative_eval {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s r P).derivative.eval (r i) = P.derivative.eval (r i) := by
  rw [numerator, derivative_sum, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      mul_one, zero_add, eval_add, eval_mul, eval_C, eval_lin]
    simp [A, rest_eval_ne_zero hr hi]
  · intro k hk hki
    simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      mul_one, zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [rest_eval_eq_zero hi hki.symm, rest_derivative_eval_eq_zero hi hki.symm]
    ring
  · exact fun h ↦ (h hi).elim

lemma sq_dvd_of_eval_derivative_eq_zero {p : K[X]} {x : K}
    (h0 : p.eval x = 0) (h1 : p.derivative.eval x = 0) :
    (X - C x) ^ 2 ∣ p := by
  have hlin : X - C x ∣ p := (dvd_iff_isRoot).mpr h0
  rcases hlin with ⟨q, hq⟩
  subst p
  have hq0 : q.eval x = 0 := by
    simpa [derivative_mul] using h1
  rcases (dvd_iff_isRoot).mpr hq0 with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [hu]
  ring

lemma den_dvd_sub_numerator {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) : den s r ∣ P - numerator s r P := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply IsCoprime.pow
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hr hi hj h)).isUnit
  · intro i hi
    apply sq_dvd_of_eval_derivative_eq_zero
    · simp [numerator_eval hr hi]
    · simp [numerator_derivative_eval hr hi]

lemma natDegree_rest {s : Finset ι} {r : ι → K} {i : ι} :
    (rest s r i).natDegree = 2 * (s.erase i).card := by
  rw [rest, Polynomial.natDegree_prod_of_monic]
  · simp [lin, Nat.mul_comm]
  · intro k hk
    exact (Polynomial.monic_X_sub_C (r k)).pow 2

omit [DecidableEq ι] in
lemma natDegree_den {s : Finset ι} {r : ι → K} :
    (den s r).natDegree = 2 * s.card := by
  classical
  rw [den, Polynomial.natDegree_prod_of_monic]
  · simp [lin, Nat.mul_comm]
  · intro k hk
    exact (Polynomial.monic_X_sub_C (r k)).pow 2

lemma natDegree_numerator_lt {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) : (numerator s r P).natDegree < 2 * s.card := by
  have hterm : ∀ i ∈ s,
      ((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).natDegree ≤
        2 * s.card - 1 := by
    intro i hi
    have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
    have hlin : (C (A s r P i) * lin r i + C (B s r P i)).natDegree ≤ 1 := by
      have hmul : (C (A s r P i) * lin r i).natDegree ≤ 1 :=
        (Polynomial.natDegree_mul_le).trans (by simp [lin])
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
    calc
      _ ≤ (C (A s r P i) * lin r i + C (B s r P i)).natDegree +
          (rest s r i).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 * (s.card - 1) := by rw [natDegree_rest, herase]; omega
      _ ≤ 2 * s.card - 1 := by omega
  have hsum : (numerator s r P).natDegree ≤ 2 * s.card - 1 := by
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
  exact hsum.trans_lt (Nat.sub_lt (by positivity) (by omega))

theorem polynomial_identity {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) :
    P = numerator s r P := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt (den_dvd_sub_numerator hr)
  rw [natDegree_den]
  exact (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt hP (natDegree_numerator_lt hs))

lemma den_eq_mul_rest {s : Finset ι} {r : ι → K} {i : ι} (hi : i ∈ s) :
    den s r = (lin r i) ^ 2 * rest s r i := by
  rw [den, rest, Finset.mul_prod_erase s (fun k ↦ (lin r k) ^ 2) hi]

lemma rest_eval_ne_zero_at {s : Finset ι} {r : ι → K} {i : ι} {t : K}
    (ht : ∀ k ∈ s, t ≠ r k) : (rest s r i).eval t ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  exact pow_ne_zero 2 (sub_ne_zero.mpr (ht k (Finset.mem_of_mem_erase hk)))

theorem partial_fraction {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) (t : K)
    (ht : ∀ i ∈ s, t ≠ r i) :
    P.eval t / (den s r).eval t =
      ∑ i ∈ s, (A s r P i / (t - r i) + B s r P i / (t - r i) ^ 2) := by
  calc
    P.eval t / (den s r).eval t =
        (numerator s r P).eval t / (den s r).eval t := by
          exact congrArg (fun Q : K[X] ↦ Q.eval t / (den s r).eval t)
            (polynomial_identity hs hr hP)
    _ = ∑ i ∈ s, (A s r P i / (t - r i) + B s r P i / (t - r i) ^ 2) := by
      rw [numerator, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [den_eq_mul_rest hi]
      simp only [eval_mul, eval_pow, eval_add, eval_C, eval_lin]
      field_simp [ht i hi, rest_eval_ne_zero_at ht]

namespace Scaled

def lin (c r : ι → K) (i : ι) : K[X] :=
  C (c i) * DoublePartialFraction.lin r i

def rest (s : Finset ι) (c r : ι → K) (i : ι) : K[X] :=
  ∏ k ∈ s.erase i, (lin c r k) ^ 2

def den (s : Finset ι) (c r : ι → K) : K[X] :=
  ∏ k ∈ s, (lin c r k) ^ 2

def V (s : Finset ι) (c r : ι → K) (P : K[X]) (i : ι) : K :=
  P.eval (r i) / (rest s c r i).eval (r i)

def U (s : Finset ι) (c r : ι → K) (P : K[X]) (i : ι) : K :=
  (P.derivative.eval (r i) - V s c r P i * (rest s c r i).derivative.eval (r i)) /
    (c i * (rest s c r i).eval (r i))

def numerator (s : Finset ι) (c r : ι → K) (P : K[X]) : K[X] :=
  ∑ i ∈ s, (C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i

omit [DecidableEq ι] in
@[simp] lemma eval_lin (c r : ι → K) (i : ι) (x : K) :
    (lin c r i).eval x = c i * (x - r i) := by simp [lin]

omit [DecidableEq ι] in
@[simp] lemma derivative_lin (c r : ι → K) (i : ι) :
    (lin c r i).derivative = C (c i) := by simp [lin]

lemma rest_eval_ne_zero {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (rest s c r i).eval (r i) ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  apply pow_ne_zero
  apply mul_ne_zero (hc k (Finset.mem_of_mem_erase hk))
  exact sub_ne_zero.mpr fun h ↦
    (Finset.ne_of_mem_erase hk).symm (hr hi (Finset.mem_of_mem_erase hk) h)

lemma rest_eval_eq_zero {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s c r k).eval (r i) = 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hi⟩)
  simp

lemma root_sq_dvd_rest {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (X - C (r i)) ^ 2 ∣ rest s c r k := by
  apply dvd_trans (b := (lin c r i) ^ 2)
  · refine ⟨C (c i) ^ 2, ?_⟩
    simp [lin, DoublePartialFraction.lin]
    ring
  · exact Finset.dvd_prod_of_mem (fun j ↦ (lin c r j) ^ 2)
      (Finset.mem_erase.mpr ⟨hik, hi⟩)

lemma rest_derivative_eval_eq_zero {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s c r k).derivative.eval (r i) = 0 :=
  eval_derivative_eq_zero_of_sq_dvd (root_sq_dvd_rest hi hik)

lemma numerator_eval {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s c r P).eval (r i) = P.eval (r i) := by
  rw [numerator, eval_finsetSum]
  simp_rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_lin]
  rw [Finset.sum_eq_single i]
  · simp [V, rest_eval_ne_zero hc hr hi]
  · intro k hk hki
    rw [rest_eval_eq_zero hi hki.symm, mul_zero]
  · exact fun h ↦ (h hi).elim

lemma numerator_derivative_eval {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s c r P).derivative.eval (r i) = P.derivative.eval (r i) := by
  rw [numerator, derivative_sum, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [U]
    field_simp [rest_eval_ne_zero hc hr hi, hc i hi]
    simp
    ring
  · intro k hk hki
    simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [rest_eval_eq_zero hi hki.symm, rest_derivative_eval_eq_zero hi hki.symm]
    ring
  · exact fun h ↦ (h hi).elim

lemma root_den_dvd_sub_numerator {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) :
    DoublePartialFraction.den s r ∣ P - numerator s c r P := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply IsCoprime.pow
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hr hi hj h)).isUnit
  · intro i hi
    apply sq_dvd_of_eval_derivative_eq_zero
    · simp [numerator_eval hc hr hi]
    · simp [numerator_derivative_eval hc hr hi]

lemma natDegree_rest_le {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) {i : ι} :
    (rest s c r i).natDegree ≤ 2 * (s.erase i).card := by
  calc
    _ ≤ ∑ k ∈ s.erase i, ((lin c r k) ^ 2).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = ∑ _k ∈ s.erase i, 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.natDegree_pow]
      have hck : c k ≠ 0 := hc k (Finset.mem_of_mem_erase hk)
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul hck]
    _ = 2 * (s.erase i).card := by simp [Nat.mul_comm]

lemma natDegree_numerator_lt {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) :
    (numerator s c r P).natDegree < 2 * s.card := by
  have hterm : ∀ i ∈ s,
      ((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).natDegree ≤
        2 * s.card - 1 := by
    intro i hi
    have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
    have hsline : (lin c r i).natDegree = 1 := by
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul (hc i hi)]
    have hlin : (C (U s c r P i) * lin c r i + C (V s c r P i)).natDegree ≤ 1 := by
      have hmul : (C (U s c r P i) * lin c r i).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_mul_le).trans (by simp [hsline])
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
    calc
      _ ≤ (C (U s c r P i) * lin c r i + C (V s c r P i)).natDegree +
          (rest s c r i).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 * (s.card - 1) := by
        exact Nat.add_le_add hlin ((natDegree_rest_le hc).trans_eq (by rw [herase]))
      _ ≤ 2 * s.card - 1 := by omega
  have hsum : (numerator s c r P).natDegree ≤ 2 * s.card - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
  exact hsum.trans_lt (Nat.sub_lt (by positivity) (by omega))

theorem polynomial_identity {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) :
    P = numerator s c r P := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt (root_den_dvd_sub_numerator hc hr)
  rw [DoublePartialFraction.natDegree_den]
  exact (Polynomial.natDegree_sub_le _ _).trans_lt
    (max_lt hP (natDegree_numerator_lt hs hc))

lemma den_eq_mul_rest {s : Finset ι} {c r : ι → K} {i : ι} (hi : i ∈ s) :
    den s c r = (lin c r i) ^ 2 * rest s c r i := by
  rw [den, rest, Finset.mul_prod_erase s (fun k ↦ (lin c r k) ^ 2) hi]

lemma rest_eval_ne_zero_at {s : Finset ι} {c r : ι → K} {i : ι} {t : K}
    (hc : ∀ k ∈ s, c k ≠ 0) (ht : ∀ k ∈ s, t ≠ r k) :
    (rest s c r i).eval t ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  exact pow_ne_zero 2 (mul_ne_zero (hc k (Finset.mem_of_mem_erase hk))
    (sub_ne_zero.mpr (ht k (Finset.mem_of_mem_erase hk))))

theorem partial_fraction {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) (t : K)
    (ht : ∀ i ∈ s, t ≠ r i) :
    P.eval t / (den s c r).eval t =
      ∑ i ∈ s, (U s c r P i / (lin c r i).eval t + V s c r P i / ((lin c r i).eval t) ^ 2) := by
  calc
    P.eval t / (den s c r).eval t =
        (numerator s c r P).eval t / (den s c r).eval t := by
          exact congrArg (fun Q : K[X] ↦ Q.eval t / (den s c r).eval t)
            (polynomial_identity hs hc hr hP)
    _ = ∑ i ∈ s, (U s c r P i / (lin c r i).eval t +
          V s c r P i / ((lin c r i).eval t) ^ 2) := by
      rw [numerator, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [den_eq_mul_rest hi]
      simp only [eval_mul, eval_pow, eval_add, eval_C]
      field_simp [eval_lin, hc i hi, ht i hi, rest_eval_ne_zero_at hc ht]

end Scaled

namespace Scaled

lemma natDegree_rest_eq {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (i : ι) :
    (rest s c r i).natDegree = 2 * (s.erase i).card := by
  rw [rest, Polynomial.natDegree_prod]
  · calc
      ∑ j ∈ s.erase i, (lin c r j ^ 2).natDegree =
          ∑ _j ∈ s.erase i, 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Polynomial.natDegree_pow]
        have hcj : c j ≠ 0 := hc j (Finset.mem_of_mem_erase hj)
        simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul hcj]
      _ = 2 * (s.erase i).card := by simp [Nat.mul_comm]
  · intro j hj
    apply pow_ne_zero
    apply mul_ne_zero
    · simp [hc j (Finset.mem_of_mem_erase hj)]
    · exact Polynomial.X_sub_C_ne_zero (r j)

lemma leadingCoeff_rest {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (i : ι) :
    (rest s c r i).leadingCoeff = ∏ j ∈ s.erase i, (c j) ^ 2 := by
  rw [rest, Polynomial.leadingCoeff_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.leadingCoeff_pow]
  have hcj : c j ≠ 0 := hc j (Finset.mem_of_mem_erase hj)
  simp [lin, DoublePartialFraction.lin, Polynomial.leadingCoeff_mul]

lemma coeff_affine_mul_rest_top {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) {i : ι} (hi : i ∈ s) :
    (((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
      (2 * s.card - 1)) =
      U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 := by
  have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
  have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  have hdeg : (rest s c r i).natDegree = 2 * (s.card - 1) := by
    rw [natDegree_rest_eq hc, herase]
  have htop : 2 * s.card - 1 = 1 + 2 * (s.card - 1) := by omega
  rw [htop, Polynomial.coeff_mul_add_eq_of_natDegree_le]
  · rw [← hdeg, Polynomial.coeff_natDegree, leadingCoeff_rest hc]
    simp [lin, DoublePartialFraction.lin]
  · have hlin : (lin c r i).natDegree = 1 := by
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul (hc i hi)]
    have hmul : (C (U s c r P i) * lin c r i).natDegree ≤ 1 :=
      Polynomial.natDegree_mul_le.trans (by simp [hlin])
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
  · exact hdeg.le

/-- In a scaled double-pole basis `c i * (X - r i)`, degree gap two forces
the weighted simple-pole cancellation `Σ U_i / c_i = 0`. -/
theorem sum_U_div_scale_eq_zero {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card - 1) :
    ∑ i ∈ s, U s c r P i / c i = 0 := by
  have hP' : P.natDegree < 2 * s.card := hP.trans_le (Nat.sub_le _ _)
  have hid := polynomial_identity hs hc hr hP'
  have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff (2 * s.card - 1)) hid
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hP] at hcoeff
  change 0 = (∑ i ∈ s,
    (C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
      (2 * s.card - 1) at hcoeff
  rw [finsetSum_coeff] at hcoeff
  have hweighted :
      ∑ i ∈ s, U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 = 0 := by
    calc
      _ = ∑ i ∈ s,
          ((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
            (2 * s.card - 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [coeff_affine_mul_rest_top hc hi]
      _ = 0 := hcoeff.symm
  let Ctot : K := ∏ i ∈ s, (c i) ^ 2
  have hCtot : Ctot ≠ 0 := by
    dsimp [Ctot]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero 2 (hc i hi)
  apply mul_left_cancel₀ hCtot
  rw [mul_zero, Finset.mul_sum]
  calc
    ∑ i ∈ s, Ctot * (U s c r P i / c i) =
        ∑ i ∈ s, U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show Ctot = c i ^ 2 * ∏ j ∈ s.erase i, (c j) ^ 2 by
        exact (Finset.mul_prod_erase s (fun j ↦ c j ^ 2) hi).symm]
      field_simp [hc i hi]
    _ = 0 := hweighted

end Scaled

lemma rest_monic (s : Finset ι) (r : ι → K) (i : ι) :
    (rest s r i).Monic := by
  rw [rest]
  exact monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C (r j)).pow 2

lemma coeff_affine_mul_rest_top {s : Finset ι} {r : ι → K} {P : K[X]}
    {i : ι} (hi : i ∈ s) :
    (((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
      (2 * s.card - 1)) = A s r P i := by
  have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
  have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  have hdeg : (rest s r i).natDegree = 2 * (s.card - 1) := by
    rw [natDegree_rest, herase]
  have htop : 2 * s.card - 1 = 1 + 2 * (s.card - 1) := by omega
  rw [htop, coeff_mul_add_eq_of_natDegree_le]
  · rw [← hdeg, coeff_natDegree, (rest_monic s r i).leadingCoeff]
    simp [lin]
  · have hmul : (C (A s r P i) * lin r i).natDegree ≤ 1 :=
      (natDegree_mul_le).trans (by simp [lin])
    exact (natDegree_add_le _ _).trans (max_le hmul (by simp))
  · exact hdeg.le

/-- The sum of the simple-pole coefficients vanishes when the rational
function has a gap of at least two between denominator and numerator degree. -/
theorem sum_A_eq_zero {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card - 1) :
    ∑ i ∈ s, A s r P i = 0 := by
  have hP' : P.natDegree < 2 * s.card := hP.trans_le (Nat.sub_le _ _)
  have hid := polynomial_identity hs hr hP'
  have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff (2 * s.card - 1)) hid
  rw [coeff_eq_zero_of_natDegree_lt hP] at hcoeff
  change 0 = (∑ i ∈ s,
    (C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
      (2 * s.card - 1) at hcoeff
  rw [finsetSum_coeff] at hcoeff
  calc
    ∑ i ∈ s, A s r P i = ∑ i ∈ s,
        ((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
          (2 * s.card - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [coeff_affine_mul_rest_top hi]
    _ = 0 := hcoeff.symm

namespace OldRational

def root (j : ℕ) : ℚ := (2 : ℚ) ^ (j + 1)

def scale (j : ℕ) : ℚ := -(root j)⁻¹

def numeratorFactor (n j : ℕ) : ℚ[X] :=
  1 - C ((2 : ℚ) ^ (n - 1 - j)) * X

def P (n : ℕ) : ℚ[X] :=
  X ^ n * ∏ j ∈ Finset.range n, numeratorFactor n j

def poleFactor (j : ℕ) : ℚ[X] := Scaled.lin scale root j

def D (n : ℕ) : ℚ[X] := Scaled.den (Finset.range (n + 1)) scale root

def G (n j : ℕ) : ℚ[X] := Scaled.rest (Finset.range (n + 1)) scale root j

/-- The coefficient of the double pole `j`. -/
def vCoeff (n j : ℕ) : ℚ :=
  Scaled.V (Finset.range (n + 1)) scale root (P n) j

/-- The coefficient of the simple pole `j`.  Since `scale j = -1 / root j`,
this is `-root j` times the derivative at `root j` of `(poleFactor j)^2 R`. -/
def uCoeff (n j : ℕ) : ℚ :=
  Scaled.U (Finset.range (n + 1)) scale root (P n) j

def R (n : ℕ) (T : ℚ) : ℚ := (P n).eval T / (D n).eval T

lemma root_ne_zero (j : ℕ) : root j ≠ 0 := by
  norm_num [root]

lemma scale_ne_zero (j : ℕ) : scale j ≠ 0 := by
  simp [scale, root_ne_zero]

lemma root_injective : Function.Injective root := by
  intro i j h
  have he : i + 1 = j + 1 :=
    (pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) h
  omega

lemma root_injOn (n : ℕ) : Set.InjOn root (Finset.range (n + 1)) :=
  root_injective.injOn

lemma scale_mul_root (j : ℕ) : scale j * root j = -1 := by
  rw [scale]
  field_simp [root_ne_zero]

lemma poleFactor_eval (j : ℕ) (T : ℚ) :
    (poleFactor j).eval T = 1 - T / root j := by
  rw [poleFactor, Scaled.eval_lin]
  rw [scale]
  field_simp [root_ne_zero]
  ring

lemma P_eval (n : ℕ) (T : ℚ) :
    (P n).eval T = T ^ n *
      ∏ j ∈ Finset.range n, (1 - (2 : ℚ) ^ (n - 1 - j) * T) := by
  rw [P, eval_mul, eval_pow, eval_X, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [numeratorFactor]

lemma D_eval (n : ℕ) (T : ℚ) :
    (D n).eval T = ∏ j ∈ Finset.range (n + 1), (1 - T / root j) ^ 2 := by
  rw [D, Scaled.den, eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [eval_pow]
  change (poleFactor j).eval T ^ 2 = _
  rw [poleFactor_eval]

lemma R_eq_products (n : ℕ) (T : ℚ) :
    R n T = T ^ n *
      (∏ j ∈ Finset.range n, (1 - (2 : ℚ) ^ (n - 1 - j) * T)) *
      (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℚ) ^ (j + 1))⁻¹ ^ 2) := by
  rw [R, P_eval, D_eval]
  simp only [root]
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [inv_pow]

lemma natDegree_numeratorFactor_le (n j : ℕ) :
    (numeratorFactor n j).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

lemma natDegree_P_lt (n : ℕ) :
    (P n).natDegree < 2 * (Finset.range (n + 1)).card := by
  have hprod : (∏ j ∈ Finset.range n, numeratorFactor n j).natDegree ≤ n := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (numeratorFactor n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact natDegree_numeratorFactor_le n j
      _ = n := by simp
  rw [P]
  refine Polynomial.natDegree_mul_le.trans_lt ?_
  simp only [Polynomial.natDegree_pow, natDegree_X]
  simp only [Finset.card_range]
  omega

lemma natDegree_P_lt_gap (n : ℕ) :
    (P n).natDegree < 2 * (Finset.range (n + 1)).card - 1 := by
  have hprod : (∏ j ∈ Finset.range n, numeratorFactor n j).natDegree ≤ n := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (numeratorFactor n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact natDegree_numeratorFactor_le n j
      _ = n := by simp
  rw [P]
  refine Polynomial.natDegree_mul_le.trans_lt ?_
  simp only [Polynomial.natDegree_pow, natDegree_X, Finset.card_range]
  omega

/-- Degree gap at infinity cancels the simple-pole part. -/
theorem sum_root_mul_uCoeff_eq_zero (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), root j * uCoeff n j = 0 := by
  have h := Scaled.sum_U_div_scale_eq_zero
    (K := ℚ) (s := Finset.range (n + 1)) (c := scale) (r := root) (P := P n)
    (by simp) (fun j _hj ↦ scale_ne_zero j) (root_injOn n) (natDegree_P_lt_gap n)
  change ∑ j ∈ Finset.range (n + 1), uCoeff n j / scale j = 0 at h
  have hneg := congrArg Neg.neg h
  simpa [scale, root_ne_zero, div_eq_mul_inv, mul_comm] using hneg

lemma G_eval_ne_zero {n j : ℕ} (hj : j < n + 1) :
    (G n j).eval (root j) ≠ 0 := by
  exact Scaled.rest_eval_ne_zero
    (fun k _hk ↦ scale_ne_zero k) (root_injOn n) (Finset.mem_range.mpr hj)

lemma vCoeff_eq_eval (n j : ℕ) :
    vCoeff n j = (P n).eval (root j) / (G n j).eval (root j) := rfl

lemma G_eval_products (n k : ℕ) :
    (G n k).eval (root k) =
      ∏ j ∈ (Finset.range (n + 1)).erase k,
        (1 - root k / root j) ^ 2 := by
  rw [G, Scaled.rest, eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [eval_pow]
  change (poleFactor j).eval (root k) ^ 2 = _
  rw [poleFactor_eval]

lemma vCoeff_eq_products (n k : ℕ) :
    vCoeff n k =
      ((root k) ^ n *
        ∏ i ∈ Finset.range n,
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) /
        (∏ j ∈ (Finset.range (n + 1)).erase k,
          (1 - root k / root j) ^ 2) := by
  rw [vCoeff_eq_eval, P_eval, G_eval_products]

lemma P_eval_root_ne_zero {n k : ℕ} : (P n).eval (root k) ≠ 0 := by
  rw [P_eval]
  apply mul_ne_zero (pow_ne_zero _ (root_ne_zero k))
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  rw [root, ← pow_add]
  have he : 0 < (n - 1 - i) + (k + 1) := by omega
  exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) he.ne'))

/-- The logarithmic derivative which appears in the simple-pole coefficient. -/
def rawLogDeriv (n k : ℕ) : ℚ :=
  root k * ((P n).derivative.eval (root k) / (P n).eval (root k) -
    (G n k).derivative.eval (root k) / (G n k).eval (root k))

lemma eval_derivative_mul_div (A B : ℚ[X]) (x : ℚ)
    (hA : A.eval x ≠ 0) (hB : B.eval x ≠ 0) :
    (A * B).derivative.eval x / (A * B).eval x =
      A.derivative.eval x / A.eval x + B.derivative.eval x / B.eval x := by
  simp only [derivative_mul, eval_add, eval_mul]
  field_simp

lemma eval_derivative_prod_div {s : Finset ℕ} (f : ℕ → ℚ[X]) (x : ℚ)
    (hf : ∀ i ∈ s, (f i).eval x ≠ 0) :
    (∏ i ∈ s, f i).derivative.eval x / (∏ i ∈ s, f i).eval x =
      ∑ i ∈ s, (f i).derivative.eval x / (f i).eval x := by
  rw [derivative_prod_finset, eval_finsetSum, eval_prod, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_mul, eval_prod]
  rw [← Finset.mul_prod_erase s (fun j ↦ (f j).eval x) hi]
  have hrest : ∏ j ∈ s.erase i, (f j).eval x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hf j (Finset.mem_of_mem_erase hj)
  field_simp [hf i hi, hrest]

lemma numeratorFactor_eval_root_ne_zero {n k i : ℕ} (_hi : i < n) :
    (numeratorFactor n i).eval (root k) ≠ 0 := by
  simp only [numeratorFactor, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  rw [root, ← pow_add]
  have he : 0 < (n - 1 - i) + (k + 1) := by omega
  exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) he.ne'))

lemma logDeriv_P (n k : ℕ) :
    (P n).derivative.eval (root k) / (P n).eval (root k) =
      (n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) := by
  rw [P, eval_derivative_mul_div]
  · congr 1
    · by_cases hn : n = 0
      · simp [hn]
      · simp only [derivative_pow, derivative_X, eval_mul, eval_C, eval_pow, eval_X,
          mul_one]
        field_simp [root_ne_zero]
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    · rw [eval_derivative_prod_div (fun i ↦ numeratorFactor n i) (root k)
          (fun i hi ↦ numeratorFactor_eval_root_ne_zero (Finset.mem_range.mp hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [numeratorFactor]
      simp [derivative_mul, derivative_pow]
  · simpa using pow_ne_zero n (root_ne_zero k)
  · rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i hi ↦
      numeratorFactor_eval_root_ne_zero (Finset.mem_range.mp hi)

lemma poleFactor_eval_root_ne_zero {n k j : ℕ}
    (hj : j ∈ (Finset.range (n + 1)).erase k) :
    (poleFactor j).eval (root k) ≠ 0 := by
  rw [poleFactor_eval]
  apply sub_ne_zero.mpr
  intro h
  have hroot : root k = root j := by
    apply (div_eq_one_iff_eq (root_ne_zero j)).mp
    linarith
  exact (Finset.ne_of_mem_erase hj).symm (root_injective hroot)

lemma logDeriv_G (n k : ℕ) :
    (G n k).derivative.eval (root k) / (G n k).eval (root k) =
      ∑ j ∈ (Finset.range (n + 1)).erase k,
        (2 * scale j) / (1 - root k / root j) := by
  rw [G, Scaled.rest,
    eval_derivative_prod_div (fun j ↦ Scaled.lin scale root j ^ 2) (root k)
      (fun j hj ↦ by
        rw [eval_pow]
        change (poleFactor j).eval (root k) ^ 2 ≠ 0
        exact pow_ne_zero 2 (poleFactor_eval_root_ne_zero hj))]
  apply Finset.sum_congr rfl
  intro j hj
  change (poleFactor j ^ 2).derivative.eval (root k) /
      (poleFactor j ^ 2).eval (root k) = _
  rw [eval_pow, poleFactor_eval]
  simp only [derivative_pow, Nat.cast_ofNat, eval_mul, eval_C]
  have hpderiv : (poleFactor j).derivative = C (scale j) := by
    exact Scaled.derivative_lin scale root j
  rw [hpderiv, eval_C]
  norm_num [poleFactor_eval]
  change (2 * (1 - root k / root j) * scale j) /
      (1 - root k / root j) ^ 2 = _
  field_simp [poleFactor_eval_root_ne_zero hj]

lemma rawLogDeriv_eq_index_sums (n k : ℕ) :
    rawLogDeriv n k =
      root k * ((n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) -
        ∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := by
  rw [rawLogDeriv, logDeriv_P, logDeriv_G]

def oddFactorQ (d : ℕ) : ℚ := (2 : ℚ) ^ d - 1

lemma oddFactorQ_ne_zero {d : ℕ} (hd : 1 ≤ d) : oddFactorQ d ≠ 0 := by
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))

lemma numerator_log_term (n k i : ℕ) (hi : i < n) :
    root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
      (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
      (2 : ℚ) ^ (n + k - i) / oddFactorQ (n + k - i) := by
  have he : (n - 1 - i) + (k + 1) = n + k - i := by omega
  have hd : 1 ≤ n + k - i := by omega
  have hmul : root k * (2 : ℚ) ^ (n - 1 - i) = (2 : ℚ) ^ (n + k - i) := by
    rw [root, ← pow_add]
    congr 1
    omega
  have hone : 1 - (2 : ℚ) ^ (n + k - i) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))
  have hodd : -1 + (2 : ℚ) ^ (n + k - i) ≠ 0 := by
    intro h
    apply hone
    linarith
  calc
    root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
        (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
        (root k * (-(2 : ℚ) ^ (n - 1 - i))) /
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k) := by ring
    _ = (-(2 : ℚ) ^ (n + k - i)) / (1 - (2 : ℚ) ^ (n + k - i)) := by
      rw [mul_neg, hmul]
      rw [show (2 : ℚ) ^ (n - 1 - i) * root k = (2 : ℚ) ^ (n + k - i) by
        rw [mul_comm, hmul]]
    _ = (2 : ℚ) ^ (n + k - i) / oddFactorQ (n + k - i) := by
      simp only [oddFactorQ]
      rw [show 1 - (2 : ℚ) ^ (n + k - i) =
        -((2 : ℚ) ^ (n + k - i) - 1) by ring]
      rw [neg_div_neg_eq]

lemma lower_pole_log_term (k j : ℕ) (hj : j < k) :
    root k * ((2 * scale j) / (1 - root k / root j)) =
      2 * (2 : ℚ) ^ (k - j) / oddFactorQ (k - j) := by
  have hd : 1 ≤ k - j := by omega
  have he : (j + 1) + (k - j) = k + 1 := by omega
  have hroot : root k = root j * (2 : ℚ) ^ (k - j) := by
    simp only [root, ← pow_add, he]
  have hratio : root k / root j = (2 : ℚ) ^ (k - j) := by
    rw [hroot]
    field_simp [root_ne_zero j]
  have hscale : root k * (2 * scale j) = -2 * (2 : ℚ) ^ (k - j) := by
    rw [scale, hroot]
    field_simp [root_ne_zero j]
  have hone : 1 - (2 : ℚ) ^ (k - j) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))
  have hodd : -1 + (2 : ℚ) ^ (k - j) ≠ 0 := by
    intro h
    apply hone
    linarith
  calc
    root k * ((2 * scale j) / (1 - root k / root j)) =
        (root k * (2 * scale j)) / (1 - root k / root j) := by ring
    _ = (-2 * (2 : ℚ) ^ (k - j)) / (1 - (2 : ℚ) ^ (k - j)) := by
      rw [hscale, hratio]
    _ = 2 * (2 : ℚ) ^ (k - j) / oddFactorQ (k - j) := by
      simp only [oddFactorQ]
      rw [show -2 * (2 : ℚ) ^ (k - j) =
        -(2 * (2 : ℚ) ^ (k - j)) by ring]
      rw [show 1 - (2 : ℚ) ^ (k - j) =
        -((2 : ℚ) ^ (k - j) - 1) by ring]
      rw [neg_div_neg_eq]

lemma upper_pole_log_term (k j : ℕ) (hj : k < j) :
    root k * ((2 * scale j) / (1 - root k / root j)) =
      -2 / oddFactorQ (j - k) := by
  have hd : 1 ≤ j - k := by omega
  have he : (k + 1) + (j - k) = j + 1 := by omega
  have hroot : root j = root k * (2 : ℚ) ^ (j - k) := by
    simp only [root, ← pow_add, he]
  have hratio : root k / root j = 1 / (2 : ℚ) ^ (j - k) := by
    rw [hroot]
    field_simp [root_ne_zero k]
  have hscale : root k * (2 * scale j) = -2 / (2 : ℚ) ^ (j - k) := by
    rw [scale, hroot]
    field_simp [root_ne_zero k]
  have hone : (2 : ℚ) ^ (j - k) - 1 ≠ 0 := oddFactorQ_ne_zero hd
  calc
    root k * ((2 * scale j) / (1 - root k / root j)) =
        (root k * (2 * scale j)) / (1 - root k / root j) := by ring
    _ = (-2 / (2 : ℚ) ^ (j - k)) /
        (1 - 1 / (2 : ℚ) ^ (j - k)) := by rw [hscale, hratio]
    _ = -2 / oddFactorQ (j - k) := by
      simp only [oddFactorQ]
      field_simp [hone]

lemma sum_range_reverse (n k : ℕ) (F : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, F (n + k - i) =
      ∑ d ∈ Finset.Icc (k + 1) (n + k), F d := by
  apply Finset.sum_bij (fun i _hi ↦ n + k - i)
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_range] at hi₁ hi₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨n + k - d, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

lemma sum_range_reverse_from_one (k : ℕ) (F : ℕ → ℚ) :
    ∑ j ∈ Finset.range k, F (k - j) =
      ∑ d ∈ Finset.Icc 1 k, F d := by
  simpa using sum_range_reverse k 0 F

lemma sum_Icc_sub (n k : ℕ) (hkn : k ≤ n) (F : ℕ → ℚ) :
    ∑ j ∈ Finset.Icc (k + 1) n, F (j - k) =
      ∑ d ∈ Finset.Icc 1 (n - k), F d := by
  apply Finset.sum_bij (fun j _hj ↦ j - k)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_Icc] at hj₁ hj₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d + k, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

def targetLogDeriv (n k : ℕ) : ℚ :=
  n +
    ∑ d ∈ Finset.Icc (k + 1) (n + k),
      (2 : ℚ) ^ d / oddFactorQ d -
    2 * ∑ d ∈ Finset.Icc 1 k,
      (2 : ℚ) ^ d / oddFactorQ d +
    2 * ∑ d ∈ Finset.Icc 1 (n - k),
      (1 : ℚ) / oddFactorQ d

theorem rawLogDeriv_eq_targetLogDeriv (n k : ℕ) (hkn : k ≤ n) :
    rawLogDeriv n k = targetLogDeriv n k := by
  let high : ℕ → ℚ := fun d ↦ (2 : ℚ) ^ d / oddFactorQ d
  let low : ℕ → ℚ := fun d ↦ (1 : ℚ) / oddFactorQ d
  have hnterm : root k * ((n : ℚ) / root k) = n := by
    field_simp [root_ne_zero]
  have hPsum :
      root k * (∑ i ∈ Finset.range n,
        (-(2 : ℚ) ^ (n - 1 - i)) /
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
        ∑ d ∈ Finset.Icc (k + 1) (n + k), high d := by
    calc
      _ = ∑ i ∈ Finset.range n,
          root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) := by
              rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range n, high (n + k - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact numerator_log_term n k i (Finset.mem_range.mp hi)
      _ = ∑ d ∈ Finset.Icc (k + 1) (n + k), high d :=
              sum_range_reverse n k high
  have herase : (Finset.range (n + 1)).erase k =
      Finset.range k ∪ Finset.Icc (k + 1) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdis : Disjoint (Finset.range k) (Finset.Icc (k + 1) n) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Finset.mem_range] at hj₁
    simp only [Finset.mem_Icc] at hj₂
    omega
  have hpoles :
      root k * (∑ j ∈ (Finset.range (n + 1)).erase k,
        (2 * scale j) / (1 - root k / root j)) =
        2 * (∑ d ∈ Finset.Icc 1 k, high d) -
        2 * (∑ d ∈ Finset.Icc 1 (n - k), low d) := by
    calc
      _ = root k * ((∑ j ∈ Finset.range k,
            (2 * scale j) / (1 - root k / root j)) +
          (∑ j ∈ Finset.Icc (k + 1) n,
            (2 * scale j) / (1 - root k / root j))) := by
              rw [herase, Finset.sum_union hdis]
      _ = (∑ j ∈ Finset.range k,
            root k * ((2 * scale j) / (1 - root k / root j))) +
          (∑ j ∈ Finset.Icc (k + 1) n,
            root k * ((2 * scale j) / (1 - root k / root j))) := by
              rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ = (∑ j ∈ Finset.range k, 2 * high (k - j)) +
          (∑ j ∈ Finset.Icc (k + 1) n, -2 * low (j - k)) := by
              apply congrArg₂ (· + ·)
              · apply Finset.sum_congr rfl
                intro j hj
                simpa [high, mul_div_assoc] using
                  lower_pole_log_term k j (Finset.mem_range.mp hj)
              · apply Finset.sum_congr rfl
                intro j hj
                have hj' : k < j := by
                  exact Nat.lt_of_succ_le (Finset.mem_Icc.mp hj).1
                simpa [low, div_eq_mul_inv] using upper_pole_log_term k j hj'
      _ = (∑ d ∈ Finset.Icc 1 k, 2 * high d) +
          (∑ d ∈ Finset.Icc 1 (n - k), -2 * low d) := by
              rw [sum_range_reverse_from_one k (fun d ↦ 2 * high d)]
              rw [sum_Icc_sub n k hkn (fun d ↦ -2 * low d)]
      _ = 2 * (∑ d ∈ Finset.Icc 1 k, high d) -
          2 * (∑ d ∈ Finset.Icc 1 (n - k), low d) := by
              rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg]
              congr 1
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro d hd
              ring
  calc
    rawLogDeriv n k = root k * ((n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) -
        ∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := rawLogDeriv_eq_index_sums n k
    _ = root k * ((n : ℚ) / root k) +
        root k * (∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) -
        root k * (∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := by ring
    _ = (n : ℚ) +
        (∑ d ∈ Finset.Icc (k + 1) (n + k), high d) -
        (2 * (∑ d ∈ Finset.Icc 1 k, high d) -
          2 * (∑ d ∈ Finset.Icc 1 (n - k), low d)) := by
            rw [hnterm, hPsum, hpoles]
    _ = targetLogDeriv n k := by
      simp only [targetLogDeriv, high, low]
      ring

lemma uCoeff_eq_eval_derivative (n j : ℕ) :
    uCoeff n j = -root j *
      ((P n).derivative.eval (root j) -
        vCoeff n j * (G n j).derivative.eval (root j)) /
        (G n j).eval (root j) := by
  rw [uCoeff, Scaled.U, vCoeff, G]
  rw [scale]
  field_simp [root_ne_zero]

lemma uCoeff_eq_neg_vCoeff_mul_rawLogDeriv {n k : ℕ} (hk : k < n + 1) :
    uCoeff n k = -vCoeff n k * rawLogDeriv n k := by
  rw [uCoeff_eq_eval_derivative, rawLogDeriv, vCoeff_eq_eval]
  field_simp [P_eval_root_ne_zero (n := n) (k := k), G_eval_ne_zero hk]

theorem partial_fraction (n : ℕ) (T : ℚ)
    (hT : ∀ j < n + 1, T ≠ root j) :
    R n T = ∑ j ∈ Finset.range (n + 1),
      (uCoeff n j / (1 - T / root j) + vCoeff n j / (1 - T / root j) ^ 2) := by
  rw [R]
  have h := Scaled.partial_fraction (K := ℚ)
      (s := Finset.range (n + 1)) (c := scale) (r := root) (P := P n)
      (by simp) (fun j _hj ↦ scale_ne_zero j) (root_injOn n) (natDegree_P_lt n) T
      (fun j hj ↦ hT j (Finset.mem_range.mp hj))
  change (P n).eval T /
      (Scaled.den (Finset.range (n + 1)) scale root).eval T = _
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  change Scaled.U (Finset.range (n + 1)) scale root (P n) j /
      (poleFactor j).eval T +
      Scaled.V (Finset.range (n + 1)) scale root (P n) j /
        ((poleFactor j).eval T) ^ 2 = _
  rw [poleFactor_eval]
  rfl

/-- The same rational function with real coefficients, in exactly the product form
used by the analytic q-Apéry development. -/
def Rreal (n : ℕ) (T : ℝ) : ℝ :=
  T ^ n *
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * T)) *
    (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)

lemma cast_root (j : ℕ) : ((root j : ℚ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
  simp [root]

lemma cast_R (n : ℕ) (T : ℚ) : ((R n T : ℚ) : ℝ) = Rreal n (T : ℝ) := by
  rw [R_eq_products, Rreal]
  push_cast
  norm_num

theorem partial_fraction_real (n : ℕ) (T : ℚ)
    (hT : ∀ j < n + 1, T ≠ root j) :
    Rreal n (T : ℝ) = ∑ j ∈ Finset.range (n + 1),
      (((uCoeff n j : ℚ) : ℝ) / (1 - (T : ℝ) / (2 : ℝ) ^ (j + 1)) +
        ((vCoeff n j : ℚ) : ℝ) / (1 - (T : ℝ) / (2 : ℝ) ^ (j + 1)) ^ 2) := by
  rw [← cast_R]
  rw [partial_fraction n T hT]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [cast_root]

end OldRational

end DoublePartialFraction
