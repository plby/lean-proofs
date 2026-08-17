/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos372.Erdos372AffineExcess

/-!
# Erdős Problem 372

Let `P n` be the largest prime factor of `n`, with `P 1 = 1`.  We prove that
there are infinitely many `n` for which

`P n > P (n + 1) > P (n + 2)`.

The elementary conversion is due to Sungjin Kim.  Its analytic input is the
Maynard--Tao theorem for a finite admissible family of affine linear forms.
The latter is derived from the proved Bombieri--Vinogradov and prime number
theorems in the bundled `BoundedGaps` development.
-/

namespace Erdos372

open scoped BigOperators

/-- The largest prime factor of `n`, or `1` when `n` has no prime factors. -/
def P (n : ℕ) : ℕ := n.primeFactors.max.getD 1

lemma P_pos (n : ℕ) : 0 < P n := by
  rcases n with (_ | _ | n) <;> simp_all +arith +decide [P]
  rcases h : Finset.max ((n + 2).primeFactors) with (_ | _ | p) <;>
    simp_all +arith +decide
  exact absurd (Finset.mem_of_max h) (by norm_num)

lemma P_prime {p : ℕ} (hp : p.Prime) : P p = p := by
  unfold P
  rw [hp.primeFactors]
  rfl

/-- If `p` is prime and the positive cofactor is smaller than `p`, then `p`
is the largest prime factor of their product. -/
lemma P_mul_prime_eq (a p : ℕ) (ha : 0 < a) (hp : p.Prime) (hap : a < p) :
    P (a * p) = p := by
  have hmax : ∀ q ∈ (a * p).primeFactors, q ≤ p := by
    norm_num [Nat.primeFactors_mul, hp.ne_zero, ha.ne']
    rintro q (⟨hqPrime, hqa⟩ | ⟨hqPrime, hqp⟩)
    · exact (Nat.le_of_dvd ha hqa).trans hap.le
    · exact Nat.le_of_dvd hp.pos hqp
  have hMaxEq : (a * p).primeFactors.max = p := by
    refine le_antisymm
      (Finset.sup_le fun q hq => WithBot.coe_le_coe.mpr (hmax q hq)) ?_
    exact Finset.le_max (Nat.mem_primeFactors.mpr ⟨hp, by aesop⟩)
  unfold P
  aesop

/-- A convenient criterion for bounding the largest prime factor. -/
lemma P_lt_of_primeFactors_lt {n p : ℕ} (hp : 1 < p)
    (h : ∀ q ∈ n.primeFactors, q < p) : P n < p := by
  unfold P
  cases hmax : n.primeFactors.max with
  | bot =>
      change 1 < p
      exact hp
  | coe q =>
      change q < p
      exact h q (Finset.mem_of_max hmax)

/-- If `n = a*b` and both positive factors are below `p`, then every prime
factor of `n` is below `p`. -/
lemma P_mul_lt {a b p : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hap : a < p) (hbp : b < p) : P (a * b) < p := by
  apply P_lt_of_primeFactors_lt (lt_of_le_of_lt ha hap)
  rw [Nat.primeFactors_mul ha.ne' hb.ne']
  intro q hq
  rcases Finset.mem_union.mp hq with hqa | hqb
  · exact (Nat.le_of_mem_primeFactors hqa).trans_lt hap
  · exact (Nat.le_of_mem_primeFactors hqb).trans_lt hbp

/-- There are arbitrarily large parameters at which two members of the
positive affine family `A i * r + 1` are prime. -/
def InfinitelyOftenTwoPrimeAffine {ι : Type*} [Fintype ι]
    (A : ι → ℕ) : Prop :=
  ∀ R : ℕ, ∃ r : ℕ, R < r ∧
    ∃ i j : ι, i ≠ j ∧ (A i * r + 1).Prime ∧ (A j * r + 1).Prime

/-- A finite coefficient family with Kim's pairwise divisibility property. -/
structure KimFamily (k : ℕ) where
  coeff : Fin k → ℕ
  coeff_pos : ∀ i, 0 < coeff i
  coeff_injective : Function.Injective coeff
  sub_dvd_left : ∀ i j, coeff i < coeff j → coeff j - coeff i ∣ coeff i

namespace KimFamily

/-- Prepending the product of all old coefficients and translating the old
family by that product preserves Kim's divisibility property. -/
def extend {k : ℕ} (K : KimFamily k) : KimFamily (k + 1) := by
  let L := ∏ i, K.coeff i
  have hL : 0 < L := Finset.prod_pos fun i _ => K.coeff_pos i
  have hcoeffDvd (i : Fin k) : K.coeff i ∣ L := by
    exact Finset.dvd_prod_of_mem K.coeff (Finset.mem_univ i)
  let B : Fin (k + 1) → ℕ :=
    Fin.cases L (fun i => L + K.coeff i)
  refine
    { coeff := B
      coeff_pos := ?_
      coeff_injective := ?_
      sub_dvd_left := ?_ }
  · intro i
    refine Fin.cases hL (fun j => ?_) i
    dsimp only [B, Fin.cases_succ]
    positivity
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
      dsimp only [B, Fin.cases_zero, Fin.cases_succ] at h
      exfalso
      have := K.coeff_pos j
      omega
    · intro j
      refine Fin.cases (fun h => ?_) (fun j h => ?_) j
      · dsimp only [B, Fin.cases_zero, Fin.cases_succ] at h
        exfalso
        have := K.coeff_pos i
        omega
      · apply congrArg Fin.succ
        apply K.coeff_injective
        dsimp only [B, Fin.cases_succ] at h
        omega
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j _ => ?_) j
      dsimp only [B, Fin.cases_zero, Fin.cases_succ]
      simpa only [Nat.add_sub_cancel_left] using hcoeffDvd j
    · intro j
      refine Fin.cases (fun h => ?_) (fun j h => ?_) j
      · dsimp only [B, Fin.cases_zero, Fin.cases_succ] at h
        have := K.coeff_pos i
        omega
      · dsimp only [B, Fin.cases_succ] at h ⊢
        have hij : K.coeff i < K.coeff j := by omega
        have hdvdAi := K.sub_dvd_left i j hij
        have hdvdL := hdvdAi.trans (hcoeffDvd i)
        simpa only [Nat.add_sub_add_left] using hdvdL.add hdvdAi

/-- Kim families of every finite cardinality. -/
def canonical : (k : ℕ) → KimFamily k
  | 0 =>
      { coeff := Fin.elim0
        coeff_pos := fun i => Fin.elim0 i
        coeff_injective := fun i => Fin.elim0 i
        sub_dvd_left := fun i => Fin.elim0 i }
  | k + 1 => (canonical k).extend

/-- A common multiple of every pair modulus needed in Kim's factorization. -/
def modulus {k : ℕ} (K : KimFamily k) : ℕ :=
  ∏ ij : Fin k × Fin k,
    (K.coeff ij.2 / (K.coeff ij.2 - K.coeff ij.1) + 1)

lemma modulus_pos {k : ℕ} (K : KimFamily k) : 0 < K.modulus := by
  unfold modulus
  apply Finset.prod_pos
  intro ij _
  exact Nat.succ_pos _

lemma pair_modulus_dvd {k : ℕ} (K : KimFamily k) (i j : Fin k) :
    K.coeff j / (K.coeff j - K.coeff i) + 1 ∣ K.modulus := by
  unfold modulus
  exact Finset.dvd_prod_of_mem
    (fun ij : Fin k × Fin k =>
      K.coeff ij.2 / (K.coeff ij.2 - K.coeff ij.1) + 1)
    (Finset.mem_univ (i, j))

end KimFamily

/-- Kim's elementary conversion, expressed after writing two coefficients as
`c*d` and `(c+1)*d`.  The modulus divisibility makes `n+2` split into two
factors smaller than the middle prime. -/
lemma descending_at_of_two_affine_primes
    (c d M r : ℕ) (hc : 0 < c) (hM : 0 < M) (hr : 0 < r)
    (hMdiv : c + 2 ∣ M)
    (hp : (c * d * M * r + 1).Prime)
    (hq : ((c + 1) * d * M * r + 1).Prime)
    (hlarge : c + 2 < c * d * M * r + 1) :
    let p := c * d * M * r + 1
    let q := (c + 1) * d * M * r + 1
    let n := c * q
    P n > P (n + 1) ∧ P (n + 1) > P (n + 2) := by
  dsimp only
  let p := c * d * M * r + 1
  let q := (c + 1) * d * M * r + 1
  have hp' : p.Prime := by simpa [p] using hp
  have hq' : q.Prime := by simpa [q] using hq
  have hd : 0 < d := by
    by_contra hd
    have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    simp at hlarge
  have hpq : p < q := by
    dsimp only [p, q]
    nlinarith [Nat.mul_pos (Nat.mul_pos hd hM) hr]
  have hcq : c < q := (by omega : c < p).trans hpq
  have hcp : c + 1 < p := by
    dsimp only [p] at hlarge ⊢
    omega
  have hPn : P (c * q) = q := P_mul_prime_eq c q hc hq' hcq
  have hnext : c * q + 1 = (c + 1) * p := by
    dsimp only [p, q]
    ring
  have hPn1 : P (c * q + 1) = p := by
    rw [hnext]
    exact P_mul_prime_eq (c + 1) p (by omega) hp' hcp
  obtain ⟨k, hk⟩ := hMdiv
  have hkPos : 0 < k := by
    by_contra hkZero
    have : k = 0 := Nat.eq_zero_of_not_pos hkZero
    subst k
    simp at hk
    omega
  let e := c * (c + 1) * d * k * r + 1
  have hfactor : c * q + 2 = (c + 2) * e := by
    dsimp only [q, e]
    rw [hk]
    ring
  have hePos : 0 < e := by positivity
  have hep : e < p := by
    have hx : 0 < c * d * k * r := by positivity
    dsimp only [e, p]
    rw [hk]
    nlinarith
  have hPn2 : P (c * q + 2) < p := by
    rw [hfactor]
    exact P_mul_lt (by omega) hePos
      (by simpa [p] using hlarge) hep
  rw [hPn, hPn1]
  exact ⟨hpq, hPn2⟩

/-- The pairwise divisibility property rewrites an ordered pair of Kim
coefficients as `c*d,(c+1)*d`, so the preceding conversion applies. -/
lemma descending_at_of_ordered_kim_pair {k : ℕ} (K : KimFamily k)
    (i j : Fin k) (hij : K.coeff i < K.coeff j) (r : ℕ)
    (hr : 0 < r)
    (hp : (K.coeff i * K.modulus * r + 1).Prime)
    (hq : (K.coeff j * K.modulus * r + 1).Prime)
    (hlarge : K.coeff j + 2 < K.coeff i * K.modulus * r + 1) :
    ∃ c : ℕ, 0 < c ∧
      P (c * (K.coeff j * K.modulus * r + 1)) >
        P (c * (K.coeff j * K.modulus * r + 1) + 1) ∧
      P (c * (K.coeff j * K.modulus * r + 1) + 1) >
        P (c * (K.coeff j * K.modulus * r + 1) + 2) := by
  let d := K.coeff j - K.coeff i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  obtain ⟨c, hcEq⟩ := K.sub_dvd_left i j hij
  have hc : 0 < c := by
    by_contra hcZero
    have : c = 0 := Nat.eq_zero_of_not_pos hcZero
    subst c
    simp at hcEq
    exact (K.coeff_pos i).ne' hcEq
  have hi : K.coeff i = c * d := by
    rw [mul_comm]
    exact hcEq
  have hj : K.coeff j = (c + 1) * d := by
    have hsum : K.coeff i + d = K.coeff j := by
      dsimp only [d]
      omega
    rw [hi] at hsum
    nlinarith
  have hpairDiv : c + 2 ∣ K.modulus := by
    have h := K.pair_modulus_dvd i j
    rw [show K.coeff j - K.coeff i = d by rfl, hj] at h
    simpa [hd.ne'] using h
  have hlarge' : c + 2 < c * d * K.modulus * r + 1 := by
    rw [← hi]
    have hcLe : c ≤ K.coeff j := by
      have hmul : c + 1 ≤ (c + 1) * d :=
        Nat.le_mul_of_pos_right _ hd
      omega
    omega
  refine ⟨c, hc, ?_⟩
  simpa [← hi, ← hj] using
    descending_at_of_two_affine_primes c d K.modulus r hc
      K.modulus_pos hr hpairDiv (by simpa [← hi] using hp)
      (by simpa [← hj] using hq) hlarge'

/-- Once the affine Maynard--Tao theorem is available for the canonical
105-form family, Kim's elementary construction gives Erdős Problem 372. -/
theorem erdos_372_of_affine_maynard_family {k : ℕ} (K : KimFamily k)
    (hMaynard :
      InfinitelyOftenTwoPrimeAffine
        (fun i : Fin k => K.coeff i * K.modulus)) :
    Set.Infinite
      {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} := by
  let M := K.modulus
  let L := ∏ i, K.coeff i
  have hL : 0 < L := Finset.prod_pos fun i _ => K.coeff_pos i
  have hcoeffLeL (i : Fin k) : K.coeff i ≤ L := by
    exact Nat.le_of_dvd hL
      (Finset.dvd_prod_of_mem K.coeff (Finset.mem_univ i))
  rw [Set.infinite_iff_exists_gt]
  intro T
  obtain ⟨r, hrBound, i, j, hij, hpi, hpj⟩ := hMaynard (T + L + 2)
  have hr : 0 < r := by omega
  have hcoeffNe : K.coeff i ≠ K.coeff j := by
    intro h
    exact hij (K.coeff_injective h)
  have handle : ∀ a b : Fin k, K.coeff a < K.coeff b →
      (K.coeff a * M * r + 1).Prime →
      (K.coeff b * M * r + 1).Prime →
      ∃ n : ℕ, n ∈ {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} ∧
        T < n := by
    intro a b hab hpa hpb
    have hMb : 0 < M := K.modulus_pos
    have hbr : r < K.coeff b * M * r + 1 := by
      have hprod : 0 < K.coeff b * M := Nat.mul_pos (K.coeff_pos b) hMb
      nlinarith
    have hbLarge : K.coeff b + 2 < K.coeff a * M * r + 1 := by
      have haLe : K.coeff a ≤ L := hcoeffLeL a
      have hbLe : K.coeff b ≤ L := hcoeffLeL b
      have hra : K.coeff a + 2 < r := by omega
      have hprod : 0 < K.coeff a * M := Nat.mul_pos (K.coeff_pos a) hMb
      have hrp : r < K.coeff a * M * r + 1 := by nlinarith
      omega
    obtain ⟨c, hc, hn⟩ := descending_at_of_ordered_kim_pair K a b hab r hr
      hpa hpb hbLarge
    refine ⟨c * (K.coeff b * M * r + 1), hn, ?_⟩
    have hqle : K.coeff b * M * r + 1 ≤
        c * (K.coeff b * M * r + 1) := by
      exact Nat.le_mul_of_pos_left _ hc
    exact (by omega : T < r).trans_le (hbr.le.trans hqle)
  rcases lt_or_gt_of_ne hcoeffNe with hlt | hgt
  · apply handle i j hlt
    · simpa [M] using hpi
    · simpa [M] using hpj
  · apply handle j i hgt
    · simpa [M] using hpj
    · simpa [M] using hpi

/-- The fixed 105-form version of the Kim conversion. -/
theorem erdos_372_of_affine_maynard
    (hMaynard :
      InfinitelyOftenTwoPrimeAffine
        (fun i : Fin 105 =>
          (KimFamily.canonical 105).coeff i *
            (KimFamily.canonical 105).modulus)) :
    Set.Infinite
      {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} :=
  erdos_372_of_affine_maynard_family (KimFamily.canonical 105) hMaynard

/-- Erdős Problem 372: the largest prime factors of three consecutive
integers are strictly decreasing infinitely often. -/
theorem erdos_372 :
    Set.Infinite
      {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} := by
  let K := KimFamily.canonical Erdos6.Maynard.largeK
  let e := Erdos6.Maynard.largeTupleIndexEquiv
  let A : Erdos6.Maynard.largePowerTuple → ℕ :=
    fun h => K.coeff (e h) * K.modulus
  have hApos : ∀ h, 0 < A h := by
    intro h
    exact Nat.mul_pos (K.coeff_pos (e h)) K.modulus_pos
  have hAinj : Function.Injective A := by
    intro a b hab
    apply e.injective
    apply K.coeff_injective
    exact Nat.eq_of_mul_eq_mul_right K.modulus_pos hab
  have hraw :=
    AffineMaynard.infinitelyOften_two_prime_affine_forms_largePowerTuple
      A hApos hAinj
  have hMaynard : InfinitelyOftenTwoPrimeAffine
      (fun i : Fin Erdos6.Maynard.largeK => K.coeff i * K.modulus) := by
    intro R
    obtain ⟨n, hn, i, j, hij, hpi, hpj⟩ := hraw R
    refine ⟨n, hn, e i, e j, ?_, ?_, ?_⟩
    · intro heq
      exact hij (e.injective heq)
    · simpa [A] using hpi
    · simpa [A] using hpj
  exact erdos_372_of_affine_maynard_family K hMaynard

#print axioms erdos_372

end Erdos372
