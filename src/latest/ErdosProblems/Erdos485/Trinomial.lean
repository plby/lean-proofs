import ErdosProblems.Erdos485.Normalization

/-!
# The normalized trinomial base case for Erdős problem 485

This file formalizes the root-uniqueness argument in Schinzel's proof.  A
polynomial whose square has support `{0,u,n}` with `gcd u n = 1` has only one
distinct root.  Hajós' multiplicity bound then forces that root to be simple,
so the polynomial is a binomial.
-/

namespace Erdos485

open Polynomial

noncomputable section

section AlgebraicallyClosed

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The algebraically closed form of Schinzel's trinomial base case. -/
theorem card_support_eq_two_of_sq_support_eq_three_of_primitive
    {f : K[X]} (hf0 : f.coeff 0 ≠ 0) (hftwo : 2 ≤ f.support.card)
    (hthree : (f ^ 2).support.card = 3)
    (hprimitive : (f ^ 2).support.gcd id = 1) :
    f.support.card = 2 := by
  classical
  let q : K[X] := f ^ 2
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q, pow_two] using mul_ne_zero hf0 hf0
  have hq : q ≠ 0 := fun h ↦ hq0 (by simp [h])
  have hqcard : q.support.card = 3 := by simpa [q] using hthree
  let e : Fin 3 ↪o ℕ := q.support.orderEmbOfFin hqcard
  let i0 : Fin 3 := ⟨0, by omega⟩
  let i1 : Fin 3 := ⟨1, by omega⟩
  let i2 : Fin 3 := ⟨2, by omega⟩
  let u : ℕ := e i1
  let n : ℕ := e i2
  have hi01 : i0 < i1 := by simp [i0, i1]
  have hi12 : i1 < i2 := by simp [i1, i2]
  have he01 : e i0 < e i1 := e.lt_iff_lt.mpr hi01
  have he12 : e i1 < e i2 := e.lt_iff_lt.mpr hi12
  have hsupp : q.support = {e i0, u, n} := by
    rw [← q.support.image_orderEmbOfFin_univ hqcard]
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [e, i0, i1, i2, u, n]
    · intro hk
      rcases hk with hk | hk | hk
      · exact ⟨i0, by simpa [e] using hk.symm⟩
      · exact ⟨i1, by simpa [e, u] using hk.symm⟩
      · exact ⟨i2, by simpa [e, n] using hk.symm⟩
  have he0 : e i0 = 0 := by
    have hz : 0 ∈ q.support := Polynomial.mem_support_iff.mpr hq0
    rw [hsupp] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · exact hz.symm
    · have : e i0 < 0 := by simpa [u, hz] using he01
      omega
    · have h02 : e i0 < e i2 := he01.trans he12
      have : e i0 < 0 := by simpa [n, hz] using h02
      omega
  have hu_pos : 0 < u := by
    simpa [u, he0] using he01
  have hun : u < n := by simpa [u, n] using he12
  have hnq : n = q.natDegree := by
    have hnd : q.natDegree ∈ q.support := q.natDegree_mem_support_of_nonzero hq
    rw [hsupp] at hnd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnd
    rcases hnd with hnd | hnd | hnd
    · have hqdeg : 0 < q.natDegree := by
        have hfdeg : 0 < f.natDegree := by
          by_contra hfdeg
          have hfdeg0 : f.natDegree = 0 := by omega
          have hcard : f.support.card ≤ 1 := by
            exact (Polynomial.card_supp_le_succ_natDegree f).trans (by omega)
          omega
        simp only [q, Polynomial.natDegree_pow]
        omega
      rw [he0] at hnd
      omega
    · have hnmem : n ∈ q.support := by rw [hsupp]; simp
      have hnle : n ≤ q.natDegree :=
        q.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hnmem)
      have humem : u ∈ q.support := by rw [hsupp]; simp
      have hule : u ≤ q.natDegree :=
        q.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp humem)
      omega
    · exact hnd.symm
  have hcoprime : u.Coprime n := by
    have hp : q.support.gcd id = 1 := by simpa [q] using hprimitive
    rw [hsupp, he0] at hp
    exact Nat.coprime_iff_gcd_eq_one.mpr (by
      simpa [gcd_eq_nat_gcd] using hp)
  let c0 : K := q.coeff 0
  let cu : K := q.coeff u
  let cn : K := q.coeff n
  have hcu : cu ≠ 0 := by
    exact Polynomial.mem_support_iff.mp (by rw [hsupp]; simp)
  have hcn : cn ≠ 0 := by
    exact Polynomial.mem_support_iff.mp (by rw [hsupp]; simp)
  have hqform : q = C c0 + C cu * X ^ u + C cn * X ^ n := by
    rw [q.as_sum_support_C_mul_X_pow, hsupp, he0]
    have h0 : 0 ∉ ({u, n} : Finset ℕ) := by
      simp [hu_pos.ne, (hu_pos.trans hun).ne]
    have hu : u ∉ ({n} : Finset ℕ) := by simp [hun.ne]
    rw [Finset.sum_insert h0, Finset.sum_insert hu, Finset.sum_singleton]
    simp [c0, cu, cn]
    ring
  have hf : f ≠ 0 := fun h ↦ hf0 (by simp [h])
  have hfdeg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf]
    exact_mod_cast (show f.natDegree ≠ 0 by
      intro h
      have hcard : f.support.card ≤ 1 := by
        exact (Polynomial.card_supp_le_succ_natDegree f).trans (by omega)
      omega)
  obtain ⟨a, haRoot⟩ := IsAlgClosed.exists_root f hfdeg
  have haeval : f.eval a = 0 := Polynomial.IsRoot.def.mp haRoot
  have ha : a ≠ 0 := by
    intro ha
    subst a
    apply hf0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact haeval
  have hroot_unique : ∀ b, f.IsRoot b → b = a := by
    intro b hbRoot
    have hbeval : f.eval b = 0 := Polynomial.IsRoot.def.mp hbRoot
    have hb : b ≠ 0 := by
      intro hb
      subst b
      apply hf0
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hbeval
    have hqa : q.eval a = 0 := by simp [q, haeval]
    have hqb : q.eval b = 0 := by simp [q, hbeval]
    have hqda : q.derivative.eval a = 0 := by
      simp [q, pow_two, haeval]
    have hqdb : q.derivative.eval b = 0 := by
      simp [q, pow_two, hbeval]
    have hqa' : c0 + cu * a ^ u + cn * a ^ n = 0 := by
      simpa [hqform] using hqa
    have hqb' : c0 + cu * b ^ u + cn * b ^ n = 0 := by
      simpa [hqform] using hqb
    have hqda' :
        cu * ((u : K) * a ^ (u - 1)) + cn * ((n : K) * a ^ (n - 1)) = 0 := by
      simpa [hqform, Polynomial.derivative_X_pow] using hqda
    have hqdb' :
        cu * ((u : K) * b ^ (u - 1)) + cn * ((n : K) * b ^ (n - 1)) = 0 := by
      simpa [hqform, Polynomial.derivative_X_pow] using hqdb
    have hpow (x : K) {k : ℕ} (hk : 0 < k) : x * x ^ (k - 1) = x ^ k := by
      calc
        x * x ^ (k - 1) = x ^ (k - 1) * x := mul_comm _ _
        _ = x ^ ((k - 1) + 1) := (pow_succ x (k - 1)).symm
        _ = x ^ k := by rw [Nat.sub_add_cancel hk]
    have hn_pos : 0 < n := hu_pos.trans hun
    have hea : (u : K) * cu * a ^ u + (n : K) * cn * a ^ n = 0 := by
      calc
        (u : K) * cu * a ^ u + (n : K) * cn * a ^ n =
            a * (cu * ((u : K) * a ^ (u - 1)) +
              cn * ((n : K) * a ^ (n - 1))) := by
                rw [← hpow a hu_pos, ← hpow a hn_pos]
                ring
        _ = 0 := by rw [hqda']; simp
    have heb : (u : K) * cu * b ^ u + (n : K) * cn * b ^ n = 0 := by
      calc
        (u : K) * cu * b ^ u + (n : K) * cn * b ^ n =
            b * (cu * ((u : K) * b ^ (u - 1)) +
              cn * ((n : K) * b ^ (n - 1))) := by
                rw [← hpow b hu_pos, ← hpow b hn_pos]
                ring
        _ = 0 := by rw [hqdb']; simp
    have hsum : cu * (a ^ u - b ^ u) + cn * (a ^ n - b ^ n) = 0 := by
      linear_combination hqa' - hqb'
    have hweighted :
        (u : K) * cu * (a ^ u - b ^ u) +
          (n : K) * cn * (a ^ n - b ^ n) = 0 := by
      linear_combination hea - heb
    have hcoef : ((n : K) - (u : K)) ≠ 0 := by
      exact sub_ne_zero.mpr (Nat.cast_injective.ne hun.ne')
    have haupow : a ^ u = b ^ u := by
      have hz : ((n : K) - (u : K)) * (cu * (a ^ u - b ^ u)) = 0 := by
        linear_combination (n : K) * hsum - hweighted
      have hz' : cu * (a ^ u - b ^ u) = 0 :=
        (mul_eq_zero.mp hz).resolve_left hcoef
      have : a ^ u - b ^ u = 0 := (mul_eq_zero.mp hz').resolve_left hcu
      exact sub_eq_zero.mp this
    have hanpow : a ^ n = b ^ n := by
      have hz : ((n : K) - (u : K)) * (cn * (a ^ n - b ^ n)) = 0 := by
        linear_combination hweighted - (u : K) * hsum
      have hz' : cn * (a ^ n - b ^ n) = 0 :=
        (mul_eq_zero.mp hz).resolve_left hcoef
      have : a ^ n - b ^ n = 0 := (mul_eq_zero.mp hz').resolve_left hcn
      exact sub_eq_zero.mp this
    let r : K := a / b
    have hru : r ^ u = 1 := by
      dsimp [r]
      rw [div_pow, haupow, div_self (pow_ne_zero _ hb)]
    have hrn : r ^ n = 1 := by
      dsimp [r]
      rw [div_pow, hanpow, div_self (pow_ne_zero _ hb)]
    have hr : r = 1 := (pow_eq_one_iff_of_coprime hcoprime).mp ⟨hru, hrn⟩
    have hab : a = b := (div_eq_one_iff_eq hb).mp (by simpa [r] using hr)
    exact hab.symm
  have hmult : f.rootMultiplicity a = f.natDegree := by
    rw [← Polynomial.count_roots]
    have hcount : f.roots.count a = f.roots.card := by
      apply Multiset.count_eq_card.mpr
      intro b hbmem
      exact (hroot_unique b ((Polynomial.mem_roots hf).mp hbmem)).symm
    rw [hcount, IsAlgClosed.card_roots_eq_natDegree]
  have hqmult : q.rootMultiplicity a = 2 * f.natDegree := by
    dsimp [q]
    rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hf hf), hmult]
    omega
  have hhajos := hajos_rootMultiplicity_lt_support_card hq ha
  rw [hqmult, hqcard] at hhajos
  have hfdeg_le : f.natDegree ≤ 1 := by omega
  apply Nat.le_antisymm
  · exact (Polynomial.card_supp_le_succ_natDegree f).trans (by omega)
  · exact hftwo

/-- In the primitive normalization over an algebraically closed field, a
three-term square has a binomial square root. -/
theorem PrimitiveNormalization.card_support_eq_two_of_card_sq_support_eq_three
    {P : K[X]} (N : PrimitiveNormalization P)
    (hthree : (N.poly ^ 2).support.card = 3) :
    N.poly.support.card = 2 :=
  card_support_eq_two_of_sq_support_eq_three_of_primitive
    N.coeff_zero_ne N.two_le_support hthree N.primitive_sq_support

end AlgebraicallyClosed

section General

variable {K : Type*} [Field K] [CharZero K]

/-- The normalized trinomial base case over an arbitrary characteristic-zero
field, obtained by passing to the algebraic closure. -/
theorem primitive_trinomial_support_card_eq_two
    {P : K[X]} (N : PrimitiveNormalization P)
    (_hN : 2 ≤ N.poly.support.card)
    (hthree : (N.poly ^ 2).support.card = 3) :
    N.poly.support.card = 2 := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hι : Function.Injective ι := RingHom.injective ι
  let Q : (AlgebraicClosure K)[X] := N.poly.map ι
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h
    apply N.coeff_zero_ne
    apply hι
    simpa [Q, ι] using h
  have hQsupport : Q.support = N.poly.support := by
    exact Polynomial.support_map_of_injective N.poly hι
  have hQtwo : 2 ≤ Q.support.card := by rw [hQsupport]; exact N.two_le_support
  have hQsqSupport : (Q ^ 2).support = (N.poly ^ 2).support := by
    rw [show Q ^ 2 = (N.poly ^ 2).map ι by simp [Q, Polynomial.map_pow],
      Polynomial.support_map_of_injective (N.poly ^ 2) hι]
  have hQthree : (Q ^ 2).support.card = 3 := by rw [hQsqSupport]; exact hthree
  have hQprimitive : (Q ^ 2).support.gcd id = 1 := by
    rw [hQsqSupport]
    exact N.primitive_sq_support
  have hQcard : Q.support.card = 2 :=
    card_support_eq_two_of_sq_support_eq_three_of_primitive
      hQ0 hQtwo hQthree hQprimitive
  rwa [hQsupport] at hQcard

/-- Alias matching the structure-oriented naming used by normalization. -/
theorem PrimitiveNormalization.card_support_eq_two_of_card_sq_support_eq_three_general
    {P : K[X]} (N : PrimitiveNormalization P)
    (hthree : (N.poly ^ 2).support.card = 3) :
    N.poly.support.card = 2 :=
  primitive_trinomial_support_card_eq_two N N.two_le_support hthree

end General

end

end Erdos485
