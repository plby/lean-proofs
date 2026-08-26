import Mathlib.NumberTheory.Bertrand
import Mathlib

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The arithmetic skeleton for Erdős Problem 486

This file formalizes the elementary number-theoretic construction in the
arithmetic-skeleton lemma of the proposed solution.  Rational inequalities
are stated after cross multiplication, so every quantitative assertion lives
in `ℕ`.
-/

open scoped BigOperators

namespace Erdos486

/-- The even parameter `k = 2 * floor (sqrt j / 8)` from the paper. -/
def skeletonK (j : ℕ) : ℕ :=
  2 * (Nat.sqrt j / 8)

/-- The paper's central family, written without integer subtraction:
`|S.card - k / 2| ≤ sqrt k`. -/
def SkeletonCentralFamily (k : ℕ) :=
  {S : Finset (Fin k) //
    k / 2 ≤ S.card + Nat.sqrt k ∧ S.card ≤ k / 2 + Nat.sqrt k}

/-- Membership in the integer interval `[11Q/10, 19Q/10]`, with both
inequalities cross multiplied. -/
def InSkeletonInterval (Q m : ℕ) : Prop :=
  11 * Q ≤ 10 * m ∧ 10 * m ≤ 19 * Q

/-- A prime selected from the Bertrand interval belonging to `i`. -/
noncomputable def skeletonPrime (k : ℕ) (i : Fin k) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul (4 ^ (k + i.val + 1)) (by positivity))

theorem skeletonPrime_spec (k : ℕ) (i : Fin k) :
    (skeletonPrime k i).Prime ∧
      4 ^ (k + i.val + 1) < skeletonPrime k i ∧
      skeletonPrime k i ≤ 2 * 4 ^ (k + i.val + 1) := by
  exact Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (4 ^ (k + i.val + 1)) (by positivity))

theorem skeletonPrime_lt_two_mul (k : ℕ) (i : Fin k) :
    skeletonPrime k i < 2 * 4 ^ (k + i.val + 1) := by
  let n := 4 ^ (k + i.val + 1)
  have hnFour : 4 ≤ n := by
    have hexp : 1 ≤ k + i.val + 1 := by omega
    simpa [n] using Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hexp
  have hpPrime : (skeletonPrime k i).Prime := (skeletonPrime_spec k i).1
  have hnlt : n < skeletonPrime k i := (skeletonPrime_spec k i).2.1
  have hple : skeletonPrime k i ≤ 2 * n := (skeletonPrime_spec k i).2.2
  apply lt_of_le_of_ne hple
  intro hEq
  have hnDvd : n ∣ skeletonPrime k i := by
    refine ⟨2, ?_⟩
    omega
  rcases (Nat.dvd_prime hpPrime).mp hnDvd with hnOne | hnEq
  · omega
  · omega

theorem skeletonPrime_strictMono (k : ℕ) : StrictMono (skeletonPrime k) := by
  intro i i' hii'
  have hi := (skeletonPrime_spec k i).2.2
  have hi' := (skeletonPrime_spec k i').2.1
  have hexp : k + i.val + 1 + 1 ≤ k + i'.val + 1 := by
    omega
  have hpow : 2 * 4 ^ (k + i.val + 1) < 4 ^ (k + i.val + 1 + 1) := by
    calc
      2 * 4 ^ (k + i.val + 1) < 4 ^ (k + i.val + 1) * 4 := by
        nlinarith [show 0 < 4 ^ (k + i.val + 1) by positivity]
      _ = 4 ^ (k + i.val + 1 + 1) := (pow_succ _ _).symm
  have hmono : 4 ^ (k + i.val + 1 + 1) ≤ 4 ^ (k + i'.val + 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact hi.trans_lt (hpow.trans_le hmono |>.trans hi')

theorem skeletonPrime_injective (k : ℕ) : Function.Injective (skeletonPrime k) :=
  (skeletonPrime_strictMono k).injective

/-- The exact exponent sum used in the paper's product estimate. -/
theorem skeleton_exponent_sum (k : ℕ) :
    (∑ i : Fin k, (2 * (k + i.val + 1) + 1)) = 3 * k ^ 2 + 2 * k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ 2 * (k + 1 + i + 1) + 1)]
      simp_rw [show ∀ i : ℕ,
        2 * (k + 1 + i + 1) + 1 = (2 * (k + 1) + 3) + 2 * i by omega]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsum := Finset.sum_range_id_mul_two (k + 1)
      simp only [Nat.add_sub_cancel] at hsum
      nlinarith

/-- The product `P` of the selected Bertrand primes. -/
noncomputable def skeletonProduct (k : ℕ) : ℕ :=
  ∏ i : Fin k, skeletonPrime k i

theorem skeletonPrime_le_twoPow (k : ℕ) (i : Fin k) :
    skeletonPrime k i ≤ 2 ^ (2 * (k + i.val + 1) + 1) := by
  calc
    skeletonPrime k i ≤ 2 * 4 ^ (k + i.val + 1) := (skeletonPrime_spec k i).2.2
    _ = 2 ^ (2 * (k + i.val + 1) + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_add]
      simp [mul_comm]

/-- The paper's exact product estimate `P ≤ 2^(3k²+2k)`. -/
theorem skeletonProduct_le (k : ℕ) :
    skeletonProduct k ≤ 2 ^ (3 * k ^ 2 + 2 * k) := by
  have hprod :
      skeletonProduct k ≤ ∏ i : Fin k, 2 ^ (2 * (k + i.val + 1) + 1) := by
    unfold skeletonProduct
    exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      fun i _ ↦ skeletonPrime_le_twoPow k i
  have hpow :
      (∏ i : Fin k, 2 ^ (2 * (k + i.val + 1) + 1)) =
        2 ^ (∑ i : Fin k, (2 * (k + i.val + 1) + 1)) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin k))
        (fun i : Fin k ↦ 2 * (k + i.val + 1) + 1) 2)
  rw [hpow, skeleton_exponent_sum] at hprod
  exact hprod

/-- The squared version `P² ≤ 2^(6k²+4k)` of the paper's product estimate. -/
theorem skeletonProduct_sq_le (k : ℕ) :
    skeletonProduct k ^ 2 ≤ 2 ^ (6 * k ^ 2 + 4 * k) := by
  have h := Nat.pow_le_pow_left (skeletonProduct_le k) 2
  calc
    skeletonProduct k ^ 2 ≤ (2 ^ (3 * k ^ 2 + 2 * k)) ^ 2 := h
    _ = 2 ^ (6 * k ^ 2 + 4 * k) := by
      rw [← pow_mul]
      congr 2
      omega

theorem skeletonK_even (j : ℕ) : Even (skeletonK j) := by
  exact ⟨Nat.sqrt j / 8, by simp [skeletonK, two_mul]⟩

theorem four_mul_skeletonK_le_sqrt (j : ℕ) :
    4 * skeletonK j ≤ Nat.sqrt j := by
  have h := Nat.div_mul_le_self (Nat.sqrt j) 8
  calc
    4 * skeletonK j = (Nat.sqrt j / 8) * 8 := by
      simp only [skeletonK]
      ring
    _ ≤ Nat.sqrt j := h

theorem skeletonK_ge_two {j : ℕ} (hj : 64 ≤ j) : 2 ≤ skeletonK j := by
  have hsqrt : 8 ≤ Nat.sqrt j := by
    have hsqrt64 : Nat.sqrt 64 = 8 := by norm_num
    rw [← hsqrt64]
    exact Nat.sqrt_le_sqrt hj
  have hdiv : 1 ≤ Nat.sqrt j / 8 := (Nat.le_div_iff_mul_le (by norm_num)).2 hsqrt
  simp only [skeletonK]
  omega

/-- For the explicit cutoff `j ≥ 64`, the exponent in the squared product
bound, plus the five bits needed to dominate the factor `20`, is at most
`j`. -/
theorem skeleton_exponent_sq_add_five_le {j : ℕ} (hj : 64 ≤ j) :
    6 * skeletonK j ^ 2 + 4 * skeletonK j + 5 ≤ j := by
  let k := skeletonK j
  have hk : 2 ≤ k := skeletonK_ge_two hj
  have hfour : 4 * k ≤ Nat.sqrt j := four_mul_skeletonK_le_sqrt j
  have hsqrt := Nat.sqrt_le j
  dsimp only [k] at hk hfour ⊢
  nlinarith

/-- The quantitative smallness needed by the construction, entirely in
cross-multiplied natural-number form: `20 P² ≤ Q`. -/
theorem twenty_mul_skeletonProduct_sq_le (j : ℕ) (hj : 64 ≤ j) :
    20 * skeletonProduct (skeletonK j) ^ 2 ≤ 2 ^ j := by
  let k := skeletonK j
  have hP : skeletonProduct k ^ 2 ≤ 2 ^ (6 * k ^ 2 + 4 * k) :=
    skeletonProduct_sq_le k
  have hexp : 6 * k ^ 2 + 4 * k + 5 ≤ j := by
    simpa [k] using skeleton_exponent_sq_add_five_le hj
  calc
    20 * skeletonProduct k ^ 2 ≤ 2 ^ 5 * 2 ^ (6 * k ^ 2 + 4 * k) :=
      Nat.mul_le_mul (by norm_num) hP
    _ = 2 ^ (6 * k ^ 2 + 4 * k + 5) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hexp

/-- A positive representative in the progression `d * (1 + Pℤ)`.  This is
the floor-based analogue of the paper's closest representative. -/
def progressionApprox (Q P d : ℕ) : ℕ :=
  d * (1 + P * (Q / (d * P)))

theorem progressionApprox_pos {Q P d : ℕ} (hd : 0 < d) :
    0 < progressionApprox Q P d := by
  simp only [progressionApprox]
  positivity

theorem progressionApprox_le_add_sq {Q P d : ℕ} (hP : 0 < P) (hdP : d ≤ P) :
    progressionApprox Q P d ≤ Q + P ^ 2 := by
  have hdiv := Nat.div_mul_le_self Q (d * P)
  have hPsq : P ≤ P ^ 2 := by
    nlinarith
  calc
    progressionApprox Q P d = d + (Q / (d * P)) * (d * P) := by
      simp only [progressionApprox]
      ring
    _ ≤ d + Q := Nat.add_le_add_left hdiv d
    _ ≤ Q + P ^ 2 := by omega

theorem le_progressionApprox_add_sq {Q P d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (hdP : d ≤ P) :
    Q ≤ progressionApprox Q P d + P ^ 2 := by
  have hden : 0 < d * P := Nat.mul_pos hd hP
  have hdiv : Q < d * P * (Q / (d * P) + 1) := Nat.lt_mul_div_succ Q hden
  have hdp : d * P ≤ P ^ 2 := by
    nlinarith
  rw [progressionApprox]
  nlinarith

/-- If `20P² ≤ Q`, the floor-based progression representative lies in the
paper's window `[19Q/20, 21Q/20]`, stated by cross multiplication. -/
theorem progressionApprox_bounds {Q P d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (hdP : d ≤ P) (hsmall : 20 * P ^ 2 ≤ Q) :
    19 * Q ≤ 20 * progressionApprox Q P d ∧
      20 * progressionApprox Q P d ≤ 21 * Q := by
  have hlower := le_progressionApprox_add_sq (Q := Q) hP hd hdP
  have hupper := progressionApprox_le_add_sq (Q := Q) hP hdP
  constructor <;> nlinarith

/-- The product `d_S` of the selected primes indexed by `S`. -/
noncomputable def skeletonSubsetProduct (k : ℕ) (S : Finset (Fin k)) : ℕ :=
  ∏ i ∈ S, skeletonPrime k i

theorem skeletonSubsetProduct_pos (k : ℕ) (S : Finset (Fin k)) :
    0 < skeletonSubsetProduct k S := by
  unfold skeletonSubsetProduct
  exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos

theorem skeletonSubsetProduct_dvd_product (k : ℕ) (S : Finset (Fin k)) :
    skeletonSubsetProduct k S ∣ skeletonProduct k := by
  simpa [skeletonSubsetProduct, skeletonProduct] using
    (Finset.prod_dvd_prod_of_subset S (Finset.univ : Finset (Fin k))
      (skeletonPrime k) S.subset_univ)

theorem skeletonSubsetProduct_le_product (k : ℕ) (S : Finset (Fin k)) :
    skeletonSubsetProduct k S ≤ skeletonProduct k := by
  exact Nat.le_of_dvd (by
    unfold skeletonProduct
    exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos)
    (skeletonSubsetProduct_dvd_product k S)

/-- The modulus attached to a subset.  It is constructed for every subset;
the final theorem restricts it to the paper's central family. -/
noncomputable def skeletonModulus (j : ℕ) (S : Finset (Fin (skeletonK j))) : ℕ :=
  progressionApprox (2 ^ j) (skeletonProduct (skeletonK j))
    (skeletonSubsetProduct (skeletonK j) S)

theorem skeletonProduct_pos (k : ℕ) : 0 < skeletonProduct k := by
  unfold skeletonProduct
  exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos

theorem skeletonPrime_dvd_product (k : ℕ) (i : Fin k) :
    skeletonPrime k i ∣ skeletonProduct k := by
  unfold skeletonProduct
  exact Finset.dvd_prod_of_mem (skeletonPrime k) (Finset.mem_univ i)

/-- A selected prime divides a subset product exactly when its index belongs
to that subset. -/
theorem skeletonPrime_dvd_subsetProduct_iff (k : ℕ) (S : Finset (Fin k))
    (i : Fin k) : skeletonPrime k i ∣ skeletonSubsetProduct k S ↔ i ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [skeletonSubsetProduct, (skeletonPrime_spec k i).1.not_dvd_one]
  | @insert a S ha ih =>
      rw [show skeletonSubsetProduct k (insert a S) =
          skeletonPrime k a * skeletonSubsetProduct k S by
        simp [skeletonSubsetProduct, ha]]
      rw [(skeletonPrime_spec k i).1.dvd_mul,
        Nat.prime_dvd_prime_iff_eq (skeletonPrime_spec k i).1
          (skeletonPrime_spec k a).1, ih]
      constructor
      · rintro (hpEq | hiS)
        · exact Finset.mem_insert.mpr (Or.inl ((skeletonPrime_injective k) hpEq))
        · exact Finset.mem_insert.mpr (Or.inr hiS)
      · intro hi
        rcases Finset.mem_insert.mp hi with hiEq | hiS
        · exact Or.inl (congrArg (skeletonPrime k) hiEq)
        · exact Or.inr hiS

theorem skeletonPrime_not_dvd_progressionFactor
    (Q k d : ℕ) (i : Fin k) :
    ¬skeletonPrime k i ∣
      1 + skeletonProduct k * (Q / (d * skeletonProduct k)) := by
  intro hdiv
  have hterm : skeletonPrime k i ∣
      skeletonProduct k * (Q / (d * skeletonProduct k)) :=
    (skeletonPrime_dvd_product k i).mul_right _
  have hone : skeletonPrime k i ∣ 1 :=
    (Nat.dvd_add_iff_right hterm).mpr (by simpa [Nat.add_comm] using hdiv)
  exact (skeletonPrime_spec k i).1.not_dvd_one hone

/-- The divisibility encoding asserted in the paper: the `i`th selected
prime divides `q_S` exactly when `i ∈ S`. -/
theorem skeletonPrime_dvd_modulus_iff (j : ℕ)
    (S : Finset (Fin (skeletonK j))) (i : Fin (skeletonK j)) :
    skeletonPrime (skeletonK j) i ∣ skeletonModulus j S ↔ i ∈ S := by
  let k := skeletonK j
  let P := skeletonProduct k
  let d := skeletonSubsetProduct k S
  have hprime := (skeletonPrime_spec k i).1
  change skeletonPrime k i ∣
      d * (1 + P * (2 ^ j / (d * P))) ↔ i ∈ S
  constructor
  · intro hdiv
    rcases hprime.dvd_mul.mp hdiv with hd | hfactor
    · exact (skeletonPrime_dvd_subsetProduct_iff k S i).mp hd
    · exact (skeletonPrime_not_dvd_progressionFactor (2 ^ j) k d i hfactor).elim
  · intro hiS
    exact ((skeletonPrime_dvd_subsetProduct_iff k S i).mpr hiS).mul_right _

theorem skeletonModulus_pos (j : ℕ) (S : Finset (Fin (skeletonK j))) :
    0 < skeletonModulus j S := by
  exact progressionApprox_pos (skeletonSubsetProduct_pos (skeletonK j) S)

/-- The cross-multiplied window bounds for every subset (and hence for every
member of the central family). -/
theorem skeletonModulus_bounds (j : ℕ) (hj : 64 ≤ j)
    (S : Finset (Fin (skeletonK j))) :
    19 * 2 ^ j ≤ 20 * skeletonModulus j S ∧
      20 * skeletonModulus j S ≤ 21 * 2 ^ j := by
  apply progressionApprox_bounds
  · exact skeletonProduct_pos (skeletonK j)
  · exact skeletonSubsetProduct_pos (skeletonK j) S
  · exact skeletonSubsetProduct_le_product (skeletonK j) S
  · exact twenty_mul_skeletonProduct_sq_le j hj

/-- Distinct subsets receive distinct moduli. -/
theorem skeletonModulus_injective (j : ℕ) : Function.Injective (skeletonModulus j) := by
  intro S T hST
  ext i
  rw [← skeletonPrime_dvd_modulus_iff j S i,
    ← skeletonPrime_dvd_modulus_iff j T i, hST]

/-- The paper's interval containment follows formally from the
cross-multiplied modulus window. -/
theorem inSkeletonInterval_between_modulus {Q q m : ℕ} (hQ : 0 < Q)
    (hqLower : 19 * Q ≤ 20 * q) (hqUpper : 20 * q ≤ 21 * Q)
    (hm : InSkeletonInterval Q m) : q < m ∧ m ≤ 2 * q := by
  unfold InSkeletonInterval at hm
  omega

/-- Any two integers in `[11Q/10,19Q/10]` are less than `q` apart whenever
`19Q/20 ≤ q`.  This is the diameter assertion in natural-number form. -/
theorem inSkeletonInterval_dist_lt_modulus {Q q m n : ℕ} (hQ : 0 < Q)
    (hqLower : 19 * Q ≤ 20 * q)
    (hm : InSkeletonInterval Q m) (hn : InSkeletonInterval Q n) :
    Nat.dist m n < q := by
  unfold InSkeletonInterval at hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    omega

/-- All conclusions of the paper's arithmetic-skeleton lemma, including the
quantitative estimates used in its proof.  Here `Q` is definitionally `2^j`
and `k` is definitionally `skeletonK j`. -/
structure ArithmeticSkeleton (j : ℕ) where
  p : Fin (skeletonK j) → ℕ
  q : SkeletonCentralFamily (skeletonK j) → ℕ
  k_even : Even (skeletonK j)
  k_pos : 0 < skeletonK j
  p_prime : ∀ i, (p i).Prime
  p_lower : ∀ i, 4 ^ (skeletonK j + i.val + 1) < p i
  p_upper : ∀ i, p i < 2 * 4 ^ (skeletonK j + i.val + 1)
  p_injective : Function.Injective p
  product_bound :
    (∏ i, p i) ≤ 2 ^ (3 * skeletonK j ^ 2 + 2 * skeletonK j)
  product_square_small : 20 * (∏ i, p i) ^ 2 ≤ 2 ^ j
  q_pos : ∀ S, 0 < q S
  q_lower : ∀ S, 19 * 2 ^ j ≤ 20 * q S
  q_upper : ∀ S, 20 * q S ≤ 21 * 2 ^ j
  prime_dvd_q_iff : ∀ S i, p i ∣ q S ↔ i ∈ S.1
  q_injective : Function.Injective q
  interval_subset : ∀ S m, InSkeletonInterval (2 ^ j) m → q S < m ∧ m ≤ 2 * q S
  interval_diameter : ∀ S m n, InSkeletonInterval (2 ^ j) m →
    InSkeletonInterval (2 ^ j) n → Nat.dist m n < q S

/-- A complete arithmetic skeleton exists for every `j ≥ 64`.  This explicit
cutoff is stronger than the paper's qualitative “for all sufficiently large
integers `j`.” -/
theorem arithmetic_skeleton (j : ℕ) (hj : 64 ≤ j) :
    Nonempty (ArithmeticSkeleton j) := by
  let q : SkeletonCentralFamily (skeletonK j) → ℕ :=
    fun S ↦ skeletonModulus j S.1
  refine ⟨{
    p := skeletonPrime (skeletonK j)
    q := q
    k_even := skeletonK_even j
    k_pos := lt_of_lt_of_le (by norm_num) (skeletonK_ge_two hj)
    p_prime := fun i ↦ (skeletonPrime_spec (skeletonK j) i).1
    p_lower := fun i ↦ (skeletonPrime_spec (skeletonK j) i).2.1
    p_upper := fun i ↦ skeletonPrime_lt_two_mul (skeletonK j) i
    p_injective := skeletonPrime_injective (skeletonK j)
    product_bound := by
      simpa only [skeletonProduct] using skeletonProduct_le (skeletonK j)
    product_square_small := by
      simpa only [skeletonProduct] using twenty_mul_skeletonProduct_sq_le j hj
    q_pos := fun S ↦ by
      simpa only [q] using skeletonModulus_pos j S.1
    q_lower := fun S ↦ by
      simpa only [q] using (skeletonModulus_bounds j hj S.1).1
    q_upper := fun S ↦ by
      simpa only [q] using (skeletonModulus_bounds j hj S.1).2
    prime_dvd_q_iff := fun S i ↦ by
      simpa only [q] using skeletonPrime_dvd_modulus_iff j S.1 i
    q_injective := by
      intro S T hST
      apply Subtype.ext
      apply skeletonModulus_injective j
      simpa only [q] using hST
    interval_subset := fun S m hm ↦ by
      have hbounds := skeletonModulus_bounds j hj S.1
      simpa only [q] using
        (inSkeletonInterval_between_modulus (Q := 2 ^ j)
          (q := skeletonModulus j S.1) (by positivity) hbounds.1 hbounds.2 hm)
    interval_diameter := fun S m n hm hn ↦ by
      have hlower := (skeletonModulus_bounds j hj S.1).1
      simpa only [q] using
        (inSkeletonInterval_dist_lt_modulus (Q := 2 ^ j)
          (q := skeletonModulus j S.1) (by positivity) hlower hm hn)
  }⟩

/-- The literal filter formulation of “for all sufficiently large `j`.” -/
theorem arithmetic_skeleton_eventually :
    ∀ᶠ j : ℕ in Filter.atTop, Nonempty (ArithmeticSkeleton j) := by
  filter_upwards [Filter.eventually_ge_atTop (64 : ℕ)] with j hj
  exact arithmetic_skeleton j hj

end Erdos486
