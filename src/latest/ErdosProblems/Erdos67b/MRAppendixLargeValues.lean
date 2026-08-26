import ErdosProblems.Erdos67b.MRMeanSquareProof
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Permutation

/-!
# The prime-polynomial large-values mechanism in Appendix A

This file formalizes the finite combinatorial heart of Lemma 8 in
Matomäki--Radziwiłł, *Multiplicative functions in short intervals*, which is
also the large-values input used in Appendix A.3 of
Matomäki--Radziwiłł--Tao, *An averaged form of Chowla's conjecture*.

If a Dirichlet polynomial supported on primes is raised to the `k`-th
power, its coefficient at `n` is a sum over ordered prime `k`-tuples with
product `n`.  Unique factorization implies that every such fiber has at
most `k!` elements.  Cauchy--Schwarz then bounds the coefficient square
mass by `k!` times the `k`-th power of the original square mass.  Combining
this with the already proved continuous Montgomery--Vaughan theorem gives
an unconditional high-moment estimate.

There is no analytic proposition or mean-value assumption in this file.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

/-- Product of the entries of a finite tuple. -/
def tupleProduct {k : ℕ} (v : Fin k → ℕ) : ℕ :=
  ∏ i, v i

/-- Product of coefficients along a finite tuple. -/
def tupleCoefficient {k : ℕ} (a : ℕ → ℂ) (v : Fin k → ℕ) : ℂ :=
  ∏ i, a (v i)

/-- Ordered `k`-tuples drawn from a finite set `P`. -/
abbrev TupleFrom (P : Finset ℕ) (k : ℕ) := Fin k → {p // p ∈ P}

/-- Product of a tuple whose entries lie in `P`. -/
def tupleFromProduct {P : Finset ℕ} {k : ℕ} (v : TupleFrom P k) : ℕ :=
  tupleProduct fun i ↦ (v i : ℕ)

/-- Product of coefficients along a tuple whose entries lie in `P`. -/
def tupleFromCoefficient {P : Finset ℕ} {k : ℕ}
    (a : ℕ → ℂ) (v : TupleFrom P k) : ℂ :=
  tupleCoefficient a fun i ↦ (v i : ℕ)

/-- The fiber of ordered tuples having a prescribed product. -/
def primeTupleProductFiber (P : Finset ℕ) (k n : ℕ) :
    Finset (TupleFrom P k) :=
  Finset.univ.filter fun v ↦ tupleFromProduct v = n

@[simp]
theorem mem_primeTupleProductFiber {P : Finset ℕ} {k n : ℕ}
    {v : TupleFrom P k} :
    v ∈ primeTupleProductFiber P k n ↔ tupleFromProduct v = n := by
  simp [primeTupleProductFiber]

/-- The coefficient of the `k`-th power after grouping prime tuples by
their product. -/
def primePowerCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (k n : ℕ) : ℂ :=
  ∑ v ∈ primeTupleProductFiber P k n, tupleFromCoefficient a v

theorem tupleFromProduct_pos
    {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) {k : ℕ}
    (v : TupleFrom P k) :
    0 < tupleFromProduct v := by
  unfold tupleFromProduct tupleProduct
  exact Finset.prod_pos fun i hi ↦ hP (v i) (v i).property

theorem tupleFromProduct_le_pow
    {P : Finset ℕ} {N k : ℕ} (hPN : ∀ p ∈ P, p ≤ N)
    (v : TupleFrom P k) :
    tupleFromProduct v ≤ N ^ k := by
  unfold tupleFromProduct tupleProduct
  calc
    ∏ i : Fin k, (v i : ℕ) ≤ ∏ _i : Fin k, N := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ hPN (v i) (v i).property)
    _ = N ^ k := by simp

/-- Unique factorization bounds an ordered prime-product fiber by `k!`.

Repeated primes cause no problem: every tuple in a nonempty fiber is a
permutation of one fixed tuple.  Mapping tuples to their `List.ofFn` lists
embeds the fiber in the (possibly duplicate-containing) list of all
permutations, whose length is exactly `k!`. -/
theorem card_primeTupleProductFiber_le_factorial
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k n : ℕ) :
    (primeTupleProductFiber P k n).card ≤ k.factorial := by
  classical
  by_cases hnonempty : (primeTupleProductFiber P k n).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    simp
  let v : TupleFrom P k := hnonempty.choose
  have hv : v ∈ primeTupleProductFiber P k n := hnonempty.choose_spec
  let toList : TupleFrom P k → List ℕ :=
    fun w ↦ List.ofFn fun i ↦ (w i : ℕ)
  have htoList : Function.Injective toList := by
    intro w z hwz
    apply funext
    intro i
    apply Subtype.ext
    exact congrFun (List.ofFn_injective (by simpa [toList] using hwz)) i
  rw [← Finset.card_image_of_injective
    (primeTupleProductFiber P k n) htoList]
  calc
    (Finset.image toList (primeTupleProductFiber P k n)).card ≤
        (toList v).permutations.toFinset.card := by
      apply Finset.card_le_card
      intro l hl
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hl
      rw [List.mem_toFinset, List.mem_permutations]
      apply perm_of_prod_eq_prod
      · rw [show (toList w).prod = tupleFromProduct w by
            exact List.prod_ofFn,
          show (toList v).prod = tupleFromProduct v by
            exact List.prod_ofFn]
        exact (mem_primeTupleProductFiber.mp hw).trans
          (mem_primeTupleProductFiber.mp hv).symm
      · intro p hp
        simp only [toList, List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        exact (hP (w i) (w i).property).prime
      · intro p hp
        simp only [toList, List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        exact (hP (v i) (v i).property).prime
    _ ≤ (toList v).permutations.length :=
      List.toFinset_card_le (toList v).permutations
    _ = k.factorial := by simp [toList, List.length_permutations]

/-- Cauchy--Schwarz on one product fiber, with unique factorization
supplying the factor `k!`. -/
theorem normSq_primePowerCoefficient_le_factorial_mul
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ → ℂ) (k n : ℕ) :
    Complex.normSq (primePowerCoefficient P a k n) ≤
      (k.factorial : ℝ) *
        ∑ v ∈ primeTupleProductFiber P k n,
          Complex.normSq (tupleFromCoefficient a v) := by
  classical
  unfold primePowerCoefficient
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ v ∈ primeTupleProductFiber P k n, tupleFromCoefficient a v‖ ^ 2 ≤
        ((primeTupleProductFiber P k n).card : ℝ) *
          ∑ v ∈ primeTupleProductFiber P k n,
            ‖tupleFromCoefficient a v‖ ^ 2 := by
      calc
        _ ≤ (∑ v ∈ primeTupleProductFiber P k n,
            ‖tupleFromCoefficient a v‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ _ := sq_sum_le_card_mul_sum_sq
    _ ≤ (k.factorial : ℝ) *
          ∑ v ∈ primeTupleProductFiber P k n,
            ‖tupleFromCoefficient a v‖ ^ 2 := by
      gcongr
      exact_mod_cast card_primeTupleProductFiber_le_factorial hP k n
    _ = (k.factorial : ℝ) *
        ∑ v ∈ primeTupleProductFiber P k n,
          Complex.normSq (tupleFromCoefficient a v) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- Square mass of the grouped coefficients of a prime polynomial power.
This is the `k!` coefficient estimate in the proof of the prime-polynomial
large-values lemma. -/
theorem sum_normSq_primePowerCoefficient_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (N ^ k),
        Complex.normSq (primePowerCoefficient P a k n)) ≤
      (k.factorial : ℝ) *
        (∑ p ∈ P, Complex.normSq (a p)) ^ k := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp ↦ (hP p hp).pos
  calc
    (∑ n ∈ Finset.Icc 1 (N ^ k),
        Complex.normSq (primePowerCoefficient P a k n)) ≤
        ∑ n ∈ Finset.Icc 1 (N ^ k),
          (k.factorial : ℝ) *
            ∑ v ∈ primeTupleProductFiber P k n,
              Complex.normSq (tupleFromCoefficient a v) := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_primePowerCoefficient_le_factorial_mul hP a k n
    _ = (k.factorial : ℝ) *
        ∑ n ∈ Finset.Icc 1 (N ^ k),
          ∑ v ∈ primeTupleProductFiber P k n,
            Complex.normSq (tupleFromCoefficient a v) := by
      rw [Finset.mul_sum]
    _ = (k.factorial : ℝ) *
        ∑ v : TupleFrom P k,
          Complex.normSq (tupleFromCoefficient a v) := by
      congr 1
      simpa only [primeTupleProductFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (TupleFrom P k)))
          (t := Finset.Icc 1 (N ^ k))
          (g := tupleFromProduct)
          (fun v hv ↦ Finset.mem_Icc.mpr
            ⟨tupleFromProduct_pos hPpos v, tupleFromProduct_le_pow hPN v⟩)
          (fun v ↦ Complex.normSq (tupleFromCoefficient a v)))
    _ = (k.factorial : ℝ) *
        (∑ p ∈ P, Complex.normSq (a p)) ^ k := by
      congr 1
      rw [show (∑ p ∈ P, Complex.normSq (a p)) =
          ∑ p : {p // p ∈ P}, Complex.normSq (a p) by
        exact Finset.sum_subtype P (fun _ ↦ Iff.rfl)
          (fun p ↦ Complex.normSq (a p)),
        Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [tupleFromCoefficient, tupleCoefficient,
        Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

/-! ## The power identity for logarithmic Dirichlet polynomials -/

theorem logarithmicPhase_eq_archimedeanTwist
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    logarithmicPhase n t = archimedeanTwist t n := by
  rw [logarithmicPhase, archimedeanTwist,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem logarithmicPhase_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    logarithmicPhase (m * n) t =
      logarithmicPhase m t * logarithmicPhase n t := by
  rw [logarithmicPhase_eq_archimedeanTwist (Nat.mul_pos hm hn),
    logarithmicPhase_eq_archimedeanTwist hm,
    logarithmicPhase_eq_archimedeanTwist hn]
  unfold archimedeanTwist
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg
    (Nat.cast_nonneg m) (Nat.cast_nonneg n) _

theorem logarithmicPhase_tupleFromProduct
    {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p)
    {k : ℕ} (v : TupleFrom P k) (t : ℝ) :
    logarithmicPhase (tupleFromProduct v) t =
      ∏ i, logarithmicPhase (v i) t := by
  classical
  unfold tupleFromProduct tupleProduct
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [logarithmicPhase]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        logarithmicPhase_mul]
      · rw [ih]
      · exact hP (v i) (v i).property
      · exact Finset.prod_pos fun j hj ↦ hP (v j) (v j).property

/-- The logarithmic polynomial obtained after grouping the `k`-fold
expansion by the product of the prime tuple. -/
def groupedPrimePowerPolynomial (P : Finset ℕ) (a : ℕ → ℂ)
    (k N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N ^ k),
    primePowerCoefficient P a k n * logarithmicPhase n t

/-- Exact power identity: raising a prime-supported logarithmic polynomial
to the `k`-th power and grouping ordered tuples by their product gives
`groupedPrimePowerPolynomial`. -/
theorem logarithmicDirichletPolynomial_pow_eq_groupedPrimePowerPolynomial
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) (t : ℝ) :
    logarithmicDirichletPolynomial P a t ^ k =
      groupedPrimePowerPolynomial P a k N t := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp ↦ (hP p hp).pos
  unfold logarithmicDirichletPolynomial groupedPrimePowerPolynomial
  rw [show (∑ n ∈ P, a n * logarithmicPhase n t) =
      ∑ n : {n // n ∈ P}, a n * logarithmicPhase n t by
        exact Finset.sum_subtype P (fun _ ↦ Iff.rfl)
          (fun n ↦ a n * logarithmicPhase n t),
    Fintype.sum_pow]
  calc
    (∑ v : TupleFrom P k,
        ∏ i, (a (v i) * logarithmicPhase (v i) t)) =
        ∑ v : TupleFrom P k,
          tupleFromCoefficient a v *
            logarithmicPhase (tupleFromProduct v) t := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.prod_mul_distrib,
        logarithmicPhase_tupleFromProduct hPpos]
      rfl
    _ = ∑ n ∈ Finset.Icc 1 (N ^ k),
        ∑ v ∈ primeTupleProductFiber P k n,
          tupleFromCoefficient a v *
            logarithmicPhase (tupleFromProduct v) t := by
      symm
      simpa only [primeTupleProductFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (TupleFrom P k)))
          (t := Finset.Icc 1 (N ^ k))
          (g := tupleFromProduct)
          (fun v hv ↦ Finset.mem_Icc.mpr
            ⟨tupleFromProduct_pos hPpos v, tupleFromProduct_le_pow hPN v⟩)
          (fun v ↦ tupleFromCoefficient a v *
            logarithmicPhase (tupleFromProduct v) t))
    _ = ∑ n ∈ Finset.Icc 1 (N ^ k),
        primePowerCoefficient P a k n * logarithmicPhase n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primePowerCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mem_primeTupleProductFiber.mp hv]

/-! ## The continuous high-moment estimate -/

theorem realExponentialPhase_mul_log_eq_logarithmicPhase
    (n : ℕ) (t : ℝ) :
    realExponentialPhase (t * Real.log n) = logarithmicPhase n t := by
  rfl

/-- Reindex the positive integers `1, ..., M` by `Fin M`. -/
theorem sum_Icc_one_eq_sum_fin
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, f n) = ∑ j : Fin M, f (j.1 + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ f (j + 1)) M]
  symm
  apply Finset.sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    exact Finset.mem_Icc.mpr
      ⟨by omega, by simpa using Finset.mem_range.mp hj⟩
  · intro i hi j hj hij
    omega
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    rfl

/-- The grouped polynomial is the finite-frequency polynomial indexed by
the positive integers at most `N^k`.  The index `j : Fin (N^k)` represents
the positive integer `j+1`, so no zero frequency is introduced. -/
theorem groupedPrimePowerPolynomial_eq_finiteFrequencyPolynomial
    (P : Finset ℕ) (a : ℕ → ℂ) (k N : ℕ) (t : ℝ) :
    groupedPrimePowerPolynomial P a k N t =
      finiteFrequencyPolynomial
        (fun n : Fin (N ^ k) ↦ Real.log (n.1 + 1))
        (fun n ↦ primePowerCoefficient P a k (n.1 + 1)) t := by
  classical
  unfold groupedPrimePowerPolynomial finiteFrequencyPolynomial
  rw [sum_Icc_one_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← realExponentialPhase_mul_log_eq_logarithmicPhase]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Montgomery--Vaughan applied to the coefficients obtained by grouping
the `k`-fold prime-tuple expansion.  This is the analytic half of the
prime-polynomial high-moment method. -/
theorem norm_groupedPrimePowerPolynomial_intervalIntegral_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (groupedPrimePowerPolynomial P a k N t) *
          groupedPrimePowerPolynomial P a k N t‖ ≤
      (2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) *
          (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
  classical
  let M : ℕ := N ^ k
  have hM : 0 < M := pow_pos hN k
  let freq : Fin M → ℝ := fun n ↦ Real.log (n.1 + 1)
  let coeff : Fin M → ℂ :=
    fun n ↦ primePowerCoefficient P a k (n.1 + 1)
  have hdelta : (0 : ℝ) < (M : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hM)
  have hsep : ∀ r s, r ≠ s →
      (M : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    have hne : r.1 + 1 ≠ s.1 + 1 := by
      intro hrsval
      apply hrs
      apply Fin.ext
      omega
    simpa only [freq, Nat.cast_add, Nat.cast_one] using
      (inv_nat_le_abs_log_sub_log
        (m := r.1 + 1) (n := s.1 + 1) (N := M)
        (by omega) (by omega)
        (Nat.succ_le_iff.mpr r.2) (Nat.succ_le_iff.mpr s.2) hne)
  have hmean := norm_finiteFrequencyPolynomial_intervalIntegral_le
    freq coeff hT hdelta hsep
  have hfactor : 0 ≤ 2 * T + 2 * Real.pi * (M : ℝ) := by
    positivity
  calc
    ‖∫ t in -T..T,
        conj (groupedPrimePowerPolynomial P a k N t) *
          groupedPrimePowerPolynomial P a k N t‖ ≤
        (2 * T + 2 * Real.pi * (M : ℝ)) *
          ∑ n : Fin M,
            Complex.normSq (primePowerCoefficient P a k (n.1 + 1)) := by
      simp_rw [groupedPrimePowerPolynomial_eq_finiteFrequencyPolynomial]
      simpa only [M, freq, coeff, inv_inv, Complex.normSq_eq_norm_sq] using hmean
    _ = (2 * T + 2 * Real.pi * (M : ℝ)) *
          ∑ n ∈ Finset.Icc 1 M,
            Complex.normSq (primePowerCoefficient P a k n) := by
      congr 1
      exact (sum_Icc_one_eq_sum_fin
        (fun n ↦ Complex.normSq (primePowerCoefficient P a k n)) M).symm
    _ ≤ (2 * T + 2 * Real.pi * (M : ℝ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      simpa only [M] using sum_normSq_primePowerCoefficient_le hP hPN a
    _ = (2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
      rfl

/-- Unconditional `2k`-th mean-value estimate for a logarithmic
Dirichlet polynomial supported on primes.  The `k!` is the exact
unique-factorization multiplicity loss from the ordered tuple expansion.
This is the continuous analogue of Matomäki--Radziwiłł's Lemma 8. -/
theorem norm_primePolynomial_highMoment_intervalIntegral_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial P a t ^ k) *
          logarithmicDirichletPolynomial P a t ^ k‖ ≤
      (2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) *
          (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
  simpa only [logarithmicDirichletPolynomial_pow_eq_groupedPrimePowerPolynomial
    hP hPN] using
      norm_groupedPrimePowerPolynomial_intervalIntegral_le hP hN hPN a hT

theorem conj_pow_mul_pow_eq_ofReal_norm_pow
    (z : ℂ) (k : ℕ) :
    conj (z ^ k) * z ^ k = ((‖z‖ ^ (2 * k) : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self]
  congr 1
  rw [Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
  congr 1
  omega

/-- Real-valued form of the continuous prime-polynomial high-moment
bound.  This is the form needed for Chebyshev's inequality. -/
theorem primePolynomial_highMoment_intervalIntegral_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        ‖logarithmicDirichletPolynomial P a t‖ ^ (2 * k)) ≤
      (2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) *
          (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
  let F : ℝ → ℂ := fun t ↦ logarithmicDirichletPolynomial P a t
  let moment : ℝ → ℝ := fun t ↦ ‖F t‖ ^ (2 * k)
  have hcomplex := norm_primePolynomial_highMoment_intervalIntegral_le
    (k := k) hP hN hPN a hT
  have hident :
      (∫ t in -T..T, conj (F t ^ k) * F t ^ k) =
        (∫ t in -T..T, ((moment t : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact conj_pow_mul_pow_eq_ofReal_norm_pow (F t) k
  have hmoment_nonneg : 0 ≤ ∫ t in -T..T, moment t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact pow_nonneg (norm_nonneg _) _
  calc
    (∫ t in -T..T,
        ‖logarithmicDirichletPolynomial P a t‖ ^ (2 * k)) =
        ‖((∫ t in -T..T, moment t) : ℂ)‖ := by
      change (∫ t in -T..T, moment t) =
        ‖∫ t in -T..T, ((moment t : ℝ) : ℂ)‖
      rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hmoment_nonneg]
    _ = ‖∫ t in -T..T, conj (F t ^ k) * F t ^ k‖ := by
      rw [← hident]
    _ ≤ (2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ P, Complex.normSq (a p)) ^ k) := by
      simpa only [F] using hcomplex

/-- Continuous prime-polynomial large-values estimate.  The measure is
Lebesgue measure restricted to `(-T,T]`; endpoint choices are immaterial,
but this one agrees exactly with `intervalIntegral.integral_of_le`.

This is the Chebyshev conclusion of Matomäki--Radziwiłł's prime
polynomial Lemma 8.  In particular, it is unconditional and retains
arbitrary complex coefficients (including zeros). -/
theorem primePolynomial_largeValues_measure_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hPN : ∀ p ∈ P, p ≤ N) (a : ℕ → ℂ)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (-T) T)).real
        {t | V ≤ ‖logarithmicDirichletPolynomial P a t‖} ≤
      ((2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ P, Complex.normSq (a p)) ^ k)) /
        V ^ (2 * k) := by
  let moment : ℝ → ℝ := fun t ↦
    ‖logarithmicDirichletPolynomial P a t‖ ^ (2 * k)
  have hcontinuous : Continuous moment := by
    unfold moment logarithmicDirichletPolynomial logarithmicPhase
    fun_prop
  have hintegrable : MeasureTheory.Integrable moment
      ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioc (-T) T)) :=
    hcontinuous.integrableOn_Ioc
  have hnonneg : 0 ≤ᵐ[(MeasureTheory.MeasureSpace.volume :
      MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (-T) T)] moment :=
    Filter.Eventually.of_forall fun t ↦ pow_nonneg (norm_nonneg _) _
  have hset :
      {t | V ^ (2 * k) ≤ moment t} =
        {t | V ≤ ‖logarithmicDirichletPolynomial P a t‖} := by
    ext t
    exact pow_le_pow_iff_left₀ hV.le (norm_nonneg _)
      (by omega : 2 * k ≠ 0)
  have hchebyshev :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      hnonneg hintegrable (V ^ (2 * k))
  rw [hset] at hchebyshev
  have hintegral :
      ∫ t, moment t ∂((MeasureTheory.MeasureSpace.volume :
        MeasureTheory.Measure ℝ).restrict
        (Set.Ioc (-T) T)) =
        ∫ t in -T..T, moment t := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  rw [hintegral] at hchebyshev
  apply (le_div_iff₀ (pow_pos hV (2 * k))).2
  simpa only [mul_comm] using hchebyshev.trans
    (primePolynomial_highMoment_intervalIntegral_le hP hN hPN a hT)

/-! ## Weighted prime-polynomial specialization -/

/-- Coefficients `g(p) / p^sigma` occurring after Perron and Ramaré
factorization.  The definition is meaningful at every natural number and
therefore also handles character twists which vanish at conductor primes. -/
def weightedPrimeCoefficient (g : ℕ → ℂ) (sigma : ℝ) (p : ℕ) : ℂ :=
  g p * Complex.ofReal ((p : ℝ) ^ (-sigma))

theorem normSq_weightedPrimeCoefficient_le
    {g : ℕ → ℂ} (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    (sigma : ℝ) {p : ℕ} (hp : 0 < p) :
    Complex.normSq (weightedPrimeCoefficient g sigma p) ≤
      ((p : ℝ) ^ (-sigma)) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  unfold weightedPrimeCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hweight : 0 ≤ (p : ℝ) ^ (-sigma) :=
    Real.rpow_nonneg (by positivity) _
  apply (sq_le_sq₀
    (mul_nonneg (norm_nonneg (g p)) hweight) hweight).2
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hg p hp) hweight

/-- Large-values estimate in the exact weighted form used for a
one-bounded multiplicative function.  No unit-norm hypothesis is present:
zeros from Dirichlet characters are retained without a conductor patch. -/
theorem weightedPrimePolynomial_largeValues_measure_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hPN : ∀ p ∈ P, p ≤ N)
    {g : ℕ → ℂ} (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    (sigma : ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (-T) T)).real
        {t | V ≤ ‖logarithmicDirichletPolynomial P
          (weightedPrimeCoefficient g sigma) t‖} ≤
      ((2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ P, ((p : ℝ) ^ (-sigma)) ^ 2) ^ k)) /
        V ^ (2 * k) := by
  have hbase := primePolynomial_largeValues_measure_le
    hP hN hk hPN (weightedPrimeCoefficient g sigma) hT hV
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hV.le (2 * k))
  have hmass :
      (∑ p ∈ P, Complex.normSq (weightedPrimeCoefficient g sigma p)) ≤
        ∑ p ∈ P, ((p : ℝ) ^ (-sigma)) ^ 2 := by
    apply Finset.sum_le_sum
    intro p hp
    exact normSq_weightedPrimeCoefficient_le hg sigma (hP p hp).pos
  have hfactor : 0 ≤ 2 * T + 2 * Real.pi * (N ^ k : ℕ) := by
    positivity
  apply mul_le_mul_of_nonneg_left _ hfactor
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀
      (Finset.sum_nonneg fun p hp ↦ Complex.normSq_nonneg _) hmass k)
  positivity

/-- Elementary square-mass bound for a prime block lying above `P0`.
At the Perron line `sigma = 1`, this is the estimate
`sum_{p in P} 1/p^2 <= #P/P0^2`. -/
theorem sum_inv_sq_le_card_div_sq
    {P : Finset ℕ} {P0 : ℕ} (hP0 : 0 < P0)
    (hlo : ∀ p ∈ P, P0 ≤ p) :
    (∑ p ∈ P, ((p : ℝ)⁻¹) ^ 2) ≤
      (P.card : ℝ) / (P0 : ℝ) ^ 2 := by
  calc
    (∑ p ∈ P, ((p : ℝ)⁻¹) ^ 2) ≤
        ∑ _p ∈ P, (((P0 : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      apply pow_le_pow_left₀ (inv_nonneg.mpr (by positivity))
      exact inv_anti₀ (by exact_mod_cast hP0)
        (by exact_mod_cast hlo p hp)
    _ = (P.card : ℝ) / (P0 : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [inv_pow, div_eq_mul_inv]

/-- Source-ready Perron-line specialization.  For primes in `[P0,N]`,
the large-value measure depends only on the block cardinality and its
lower endpoint.  This is the explicit form used when `k` is chosen near
`log T / log P0`. -/
theorem perronPrimeBlock_largeValues_measure_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {P0 N k : ℕ} (hP0 : 0 < P0) (hN : 0 < N) (hk : 0 < k)
    (hlo : ∀ p ∈ P, P0 ≤ p) (hPN : ∀ p ∈ P, p ≤ N)
    {g : ℕ → ℂ} (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (-T) T)).real
        {t | V ≤ ‖logarithmicDirichletPolynomial P
          (weightedPrimeCoefficient g 1) t‖} ≤
      ((2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            ((P.card : ℝ) / (P0 : ℝ) ^ 2) ^ k)) /
        V ^ (2 * k) := by
  have hbase := weightedPrimePolynomial_largeValues_measure_le
    hP hN hk hPN hg 1 hT hV
  simp only [Real.rpow_neg_one] at hbase
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hV.le (2 * k))
  have hmass := sum_inv_sq_le_card_div_sq hP0 hlo
  have hfactor : 0 ≤ 2 * T + 2 * Real.pi * (N ^ k : ℕ) := by
    positivity
  apply mul_le_mul_of_nonneg_left _ hfactor
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀
      (Finset.sum_nonneg fun p hp ↦ sq_nonneg _) hmass k)
  positivity

/-- The preceding estimate specialized to the actual prime blocks in the
corrected Ramaré identity.  This theorem can be applied directly to the
main branch of
`typicalModulatedShortSum_eq_multiplicative_ramare_cofactors`; no complete
multiplicativity or unit-norm assumption is required. -/
theorem ramarePrimeBlock_largeValues_measure_le
    (I : ℕ × ℕ) (hlo : 0 < I.1) (hhi : 0 < I.2)
    {k : ℕ} (hk : 0 < k)
    {g : ℕ → ℂ} (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioc (-T) T)).real
        {t | V ≤ ‖logarithmicDirichletPolynomial (primesInBlock I)
          (weightedPrimeCoefficient g 1) t‖} ≤
      ((2 * T + 2 * Real.pi * (I.2 ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (((primesInBlock I).card : ℝ) / (I.1 : ℝ) ^ 2) ^ k)) /
        V ^ (2 * k) := by
  apply perronPrimeBlock_largeValues_measure_le
    (P := primesInBlock I)
    (P0 := I.1) (N := I.2) (k := k)
    (fun p hp ↦ (mem_primesInBlock.mp hp).1)
    hlo hhi hk
  · intro p hp
    exact (mem_primesInBlock.mp hp).2.1
  · intro p hp
    exact (mem_primesInBlock.mp hp).2.2
  · exact hg
  · exact hT
  · exact hV

end

end Erdos67b
