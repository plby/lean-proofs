/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: exact arithmetic core of the positive-density family

This file formalizes only the elementary, exact part of the proposed
positive-density proof.  It defines the four linear branches and the
quadratic family, proves all six linear identities and the product identity,
certifies strict growth, records the fixed-prime congruences, and checks the
finite top-digit residue tables.

It also gives the exact bridge to the statement of Erdős 730: an infinite
set of good parameters in this family maps injectively into the upstream set
of unequal pairs with equal central-binomial prime support.

No analytic density estimate, Kummer theorem, Mertens theorem, or prime
number theorem in arithmetic progressions is asserted here.
-/

namespace Erdos730
namespace FullDensityCore

/-! ## The family -/

/-- The fixed modulus factor `3 * 41 * 43`. -/
def T : ℕ := 3 * 41 * 43

/-- The `P` branch. -/
def P (x : ℕ) : ℕ := 42 * T * x + 11

/-- The `Q` branch. -/
def Q (x : ℕ) : ℕ := 72 * T * x + 13

/-- The `R` branch. -/
def R (x : ℕ) : ℕ := 28 * T * x + 5

/-- The `S` branch. -/
def S (x : ℕ) : ℕ := 72 * T * x + 19

/-- The consecutive-pair parameter used in the density argument. -/
def n (x : ℕ) : ℕ := P x * Q x - 1

theorem T_eq : T = 5289 := by
  norm_num [T]

theorem branch_expansions (x : ℕ) :
    P x = 222138 * x + 11 ∧
    Q x = 380808 * x + 13 ∧
    R x = 148092 * x + 5 ∧
    S x = 380808 * x + 19 := by
  norm_num [P, Q, R, S, T]

/-- The exact quadratic polynomial, including the subtraction by one. -/
theorem n_expansion (x : ℕ) :
    n x = 84591927504 * x ^ 2 + 7076682 * x + 142 := by
  unfold n
  have hprod :
      P x * Q x = 84591927504 * x ^ 2 + 7076682 * x + 143 := by
    simp only [P, Q, T]
    ring
  rw [hprod]
  omega

/-! ## Exact branch identities -/

theorem product_identity (x : ℕ) :
    2 * (P x * Q x) = 3 * (R x * S x) + 1 := by
  simp only [P, Q, R, S, T]
  ring

theorem identity_PQ (x : ℕ) : 12 * P x = 7 * Q x + 41 := by
  simp only [P, Q, T]
  ring

theorem identity_RS (x : ℕ) : 18 * R x + 43 = 7 * S x := by
  simp only [R, S, T]
  ring

theorem identity_PS (x : ℕ) : 12 * P x + 1 = 7 * S x := by
  simp only [P, S, T]
  ring

theorem identity_QR (x : ℕ) : 7 * Q x = 18 * R x + 1 := by
  simp only [Q, R, T]
  ring

theorem identity_PR (x : ℕ) : 2 * P x = 3 * R x + 7 := by
  simp only [P, R, T]
  ring

theorem identity_QS (x : ℕ) : S x = Q x + 6 := by
  simp only [Q, S]

theorem n_add_one (x : ℕ) : n x + 1 = P x * Q x := by
  have hpos : 0 < P x * Q x := by
    simp only [P, Q, T]
    positivity
  simp only [n]
  omega

theorem two_n_add_one (x : ℕ) : 2 * n x + 1 = 3 * (R x * S x) := by
  have hprod := product_identity x
  have hn := n_add_one x
  omega

/-! ## Positivity and strict growth -/

theorem branches_positive (x : ℕ) :
    0 < P x ∧ 0 < Q x ∧ 0 < R x ∧ 0 < S x := by
  simp only [P, Q, R, S, T]
  omega

theorem P_strictMono : StrictMono P := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [P, T]
  omega

theorem Q_strictMono : StrictMono Q := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [Q, T]
  omega

theorem R_strictMono : StrictMono R := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [R, T]
  omega

theorem S_strictMono : StrictMono S := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [S, T]
  omega

theorem n_strictMono : StrictMono n := by
  apply strictMono_nat_of_lt_succ
  intro x
  rw [n_expansion, n_expansion]
  nlinarith

/-! ## Exact bridge to the upstream Erdős 730 statement -/

/-- This is the set `S` in `FormalConjectures/ErdosProblems/730.lean`. -/
abbrev PairSet : Set (ℕ × ℕ) :=
  {z | z.1 < z.2 ∧
    z.1.centralBinom.primeFactors = z.2.centralBinom.primeFactors}

/-- The consecutive pair produced by a parameter. -/
def familyPair (x : ℕ) : ℕ × ℕ := (n x, n x + 1)

/-- A paper-family parameter, starting at `1`, whose consecutive pair has
equal prime support. -/
def GoodParameter (x : ℕ) : Prop :=
  1 ≤ x ∧
    (n x).centralBinom.primeFactors =
      (n x + 1).centralBinom.primeFactors

def GoodParameters : Set ℕ := {x | GoodParameter x}

theorem familyPair_mem_pairSet {x : ℕ} (hx : GoodParameter x) :
    familyPair x ∈ PairSet := by
  exact ⟨Nat.lt_succ_self _, hx.2⟩

theorem familyPair_mapsTo_pairSet :
    Set.MapsTo familyPair GoodParameters PairSet := by
  intro x hx
  exact familyPair_mem_pairSet hx

theorem familyPair_injective : Function.Injective familyPair := by
  intro x y hxy
  have hnxy : n x = n y := congrArg Prod.fst hxy
  exact n_strictMono.injective hnxy

theorem familyPair_injOn_good : Set.InjOn familyPair GoodParameters :=
  fun _ _ _ _ h => familyPair_injective h

/-- The exact final set-theoretic intake bridge.  Any proof that the good
parameter set is infinite therefore proves the upstream Erdős 730 set is
infinite. -/
theorem pairSet_infinite_of_goodParameters_infinite
    (hgood : GoodParameters.Infinite) : PairSet.Infinite := by
  have himage : (familyPair '' GoodParameters).Infinite :=
    Set.Infinite.image familyPair_injOn_good hgood
  exact himage.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact familyPair_mem_pairSet hx)

/-! ## Fixed-prime congruences -/

theorem branch_mod_41 (x : ℕ) :
    P x % 41 = 11 ∧ Q x % 41 = 13 ∧
    R x % 41 = 5 ∧ S x % 41 = 19 := by
  simp only [P, Q, R, S, T]
  omega

theorem branch_mod_43 (x : ℕ) :
    P x % 43 = 11 ∧ Q x % 43 = 13 ∧
    R x % 43 = 5 ∧ S x % 43 = 19 := by
  simp only [P, Q, R, S, T]
  omega

theorem fixed_primes_do_not_divide_branches (x : ℕ) :
    (¬41 ∣ P x ∧ ¬41 ∣ Q x ∧ ¬41 ∣ R x ∧ ¬41 ∣ S x) ∧
    (¬43 ∣ P x ∧ ¬43 ∣ Q x ∧ ¬43 ∣ R x ∧ ¬43 ∣ S x) := by
  rcases branch_mod_41 x with ⟨hP41, hQ41, hR41, hS41⟩
  rcases branch_mod_43 x with ⟨hP43, hQ43, hR43, hS43⟩
  simp only [Nat.dvd_iff_mod_eq_zero, hP41, hQ41, hR41, hS41,
    hP43, hQ43, hR43, hS43]
  norm_num

theorem branch_mod_3 (x : ℕ) :
    P x % 3 = 2 ∧ Q x % 3 = 1 ∧
    R x % 3 = 2 ∧ S x % 3 = 1 := by
  simp only [P, Q, R, S, T]
  omega

theorem branch_mod_7_fixed (x : ℕ) : P x % 7 = 4 ∧ R x % 7 = 5 := by
  simp only [P, R, T]
  omega

theorem Q_S_odd_and_one_mod_three (x : ℕ) :
    Q x % 2 = 1 ∧ S x % 2 = 1 ∧
    Q x % 3 = 1 ∧ S x % 3 = 1 := by
  simp only [Q, S, T]
  omega

/-! ## Pairwise coprimality of the four branches -/

lemma coprime_of_gcd_dvd_coprime
    {a b c : ℕ} (hac : Nat.Coprime a c) (hdiv : Nat.gcd a b ∣ c) :
    Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply (Nat.coprime_self _).mp
  exact Nat.Coprime.of_dvd (Nat.gcd_dvd_left a b) hdiv hac

theorem P_Q_coprime (x : ℕ) : Nat.Coprime (P x) (Q x) := by
  let g := Nat.gcd (P x) (Q x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgQ : g ∣ Q x := Nat.gcd_dvd_right _ _
  have h12P : g ∣ 12 * P x := dvd_mul_of_dvd_right hgP 12
  have h7Q : g ∣ 7 * Q x := dvd_mul_of_dvd_right hgQ 7
  have hdiff : 12 * P x - 7 * Q x = 41 := by
    have hid := identity_PQ x
    omega
  have hgdiff : g ∣ 12 * P x - 7 * Q x := Nat.dvd_sub h12P h7Q
  rw [hdiff] at hgdiff
  have hnot : ¬41 ∣ P x := (fixed_primes_do_not_divide_branches x).1.1
  have hcop : Nat.Coprime (P x) 41 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 41)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem R_S_coprime (x : ℕ) : Nat.Coprime (R x) (S x) := by
  let g := Nat.gcd (R x) (S x)
  have hgR : g ∣ R x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have h18R : g ∣ 18 * R x := dvd_mul_of_dvd_right hgR 18
  have h7S : g ∣ 7 * S x := dvd_mul_of_dvd_right hgS 7
  have hdiff : 7 * S x - 18 * R x = 43 := by
    have hid := identity_RS x
    omega
  have hgdiff : g ∣ 7 * S x - 18 * R x := Nat.dvd_sub h7S h18R
  rw [hdiff] at hgdiff
  have hnot : ¬43 ∣ R x := (fixed_primes_do_not_divide_branches x).2.2.2.1
  have hcop : Nat.Coprime (R x) 43 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 43)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem P_S_coprime (x : ℕ) : Nat.Coprime (P x) (S x) := by
  let g := Nat.gcd (P x) (S x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have h12P : g ∣ 12 * P x := dvd_mul_of_dvd_right hgP 12
  have h7S : g ∣ 7 * S x := dvd_mul_of_dvd_right hgS 7
  have hdiff : 7 * S x - 12 * P x = 1 := by
    have hid := identity_PS x
    omega
  have hgdiff : g ∣ 7 * S x - 12 * P x := Nat.dvd_sub h7S h12P
  rw [hdiff] at hgdiff
  rw [Nat.coprime_iff_gcd_eq_one]
  exact Nat.dvd_one.mp hgdiff

theorem Q_R_coprime (x : ℕ) : Nat.Coprime (Q x) (R x) := by
  let g := Nat.gcd (Q x) (R x)
  have hgQ : g ∣ Q x := Nat.gcd_dvd_left _ _
  have hgR : g ∣ R x := Nat.gcd_dvd_right _ _
  have h7Q : g ∣ 7 * Q x := dvd_mul_of_dvd_right hgQ 7
  have h18R : g ∣ 18 * R x := dvd_mul_of_dvd_right hgR 18
  have hdiff : 7 * Q x - 18 * R x = 1 := by
    have hid := identity_QR x
    omega
  have hgdiff : g ∣ 7 * Q x - 18 * R x := Nat.dvd_sub h7Q h18R
  rw [hdiff] at hgdiff
  rw [Nat.coprime_iff_gcd_eq_one]
  exact Nat.dvd_one.mp hgdiff

theorem P_R_coprime (x : ℕ) : Nat.Coprime (P x) (R x) := by
  let g := Nat.gcd (P x) (R x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgR : g ∣ R x := Nat.gcd_dvd_right _ _
  have h2P : g ∣ 2 * P x := dvd_mul_of_dvd_right hgP 2
  have h3R : g ∣ 3 * R x := dvd_mul_of_dvd_right hgR 3
  have hdiff : 2 * P x - 3 * R x = 7 := by
    have hid := identity_PR x
    omega
  have hgdiff : g ∣ 2 * P x - 3 * R x := Nat.dvd_sub h2P h3R
  rw [hdiff] at hgdiff
  have hPmod := (branch_mod_7_fixed x).1
  have hnot : ¬7 ∣ P x := by
    rw [Nat.dvd_iff_mod_eq_zero, hPmod]
    norm_num
  have hcop : Nat.Coprime (P x) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem Q_S_coprime (x : ℕ) : Nat.Coprime (Q x) (S x) := by
  let g := Nat.gcd (Q x) (S x)
  have hgQ : g ∣ Q x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have hdiff : S x - Q x = 6 := by
    have hid := identity_QS x
    omega
  have hgdiff : g ∣ S x - Q x := Nat.dvd_sub hgS hgQ
  rw [hdiff] at hgdiff
  rcases Q_S_odd_and_one_mod_three x with ⟨hQ2, _hS2, hQ3, _hS3⟩
  have hnot2 : ¬2 ∣ Q x := by
    rw [Nat.dvd_iff_mod_eq_zero, hQ2]
    norm_num
  have hnot3 : ¬3 ∣ Q x := by
    rw [Nat.dvd_iff_mod_eq_zero, hQ3]
    norm_num
  have hQ2cop : Nat.Coprime (Q x) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnot2).symm
  have hQ3cop : Nat.Coprime (Q x) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot3).symm
  have hQ6cop : Nat.Coprime (Q x) 6 := by
    exact hQ2cop.mul_right hQ3cop
  exact coprime_of_gcd_dvd_coprime hQ6cop hgdiff

theorem branches_pairwise_coprime (x : ℕ) :
    Nat.Coprime (P x) (Q x) ∧ Nat.Coprime (P x) (R x) ∧
    Nat.Coprime (P x) (S x) ∧ Nat.Coprime (Q x) (R x) ∧
    Nat.Coprime (Q x) (S x) ∧ Nat.Coprime (R x) (S x) := by
  exact ⟨P_Q_coprime x, P_R_coprime x, P_S_coprime x,
    Q_R_coprime x, Q_S_coprime x, R_S_coprime x⟩

/-! ## Finite residue tables used by the top-range classification -/

def unitsMod (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun c => Nat.Coprime c m)

def PAllowedResidues : Finset ℕ :=
  (unitsMod 7).filter (fun c => 12 * c ^ 2 % 7 = 3)

def RAllowedResidues : Finset ℕ :=
  (unitsMod 14).filter (fun c => 54 * c ^ 2 % 14 = 6)

theorem P_unit_residue_table : unitsMod 7 = {1, 2, 3, 4, 5, 6} := by
  decide

theorem P_allowed_residue_table : PAllowedResidues = {3, 4} := by
  decide

theorem R_unit_residue_table : unitsMod 14 = {1, 3, 5, 9, 11, 13} := by
  decide

theorem R_allowed_residue_table : RAllowedResidues = {5, 9} := by
  decide

theorem allowed_residue_card_certificate :
    (unitsMod 7).card = 6 ∧ PAllowedResidues.card = 2 ∧
    (unitsMod 14).card = 6 ∧ RAllowedResidues.card = 2 := by
  rw [P_unit_residue_table, P_allowed_residue_table,
    R_unit_residue_table, R_allowed_residue_table]
  norm_num

theorem P_top_residue_iff (c : Fin 7) :
    12 * c.val ^ 2 % 7 = 3 ↔ c.val = 3 ∨ c.val = 4 := by
  exact (by decide : ∀ z : Fin 7,
    12 * z.val ^ 2 % 7 = 3 ↔ z.val = 3 ∨ z.val = 4) c

theorem R_top_residue_iff (c : Fin 14) (hc : Nat.Coprime c.val 14) :
    54 * c.val ^ 2 % 14 = 6 ↔ c.val = 5 ∨ c.val = 9 := by
  exact (by decide : ∀ z : Fin 14, Nat.Coprime z.val 14 →
    (54 * z.val ^ 2 % 14 = 6 ↔ z.val = 5 ∨ z.val = 9)) c hc

/-! ## Cleared top-digit inequalities -/

/-- Cleared `P`-branch top-digit classification.  The residue numerator is
the lower-half digit exactly in the residue case `r=3`. -/
theorem P_top_digit_classification
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 3 ∨ r = 5 ∨ r = 6)
    (heq : 7 * d + 41 * c = r * p) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 3) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- The `Q`-branch top digit is strictly above the lower half. -/
theorem Q_top_digit_large
    {p c d : ℕ} (hp : 130 * c < p)
    (heq : 12 * d = 7 * p + 41 * c) :
    p < 2 * d := by
  omega

/-- Cleared `R`-branch top-digit classification. -/
theorem R_top_digit_classification
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 6 ∨ r = 10 ∨ r = 12)
    (heq : 14 * d + 7 = r * p + 129 * c) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 6) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- The `S`-branch top digit lies strictly between `p/2` and `p`. -/
theorem S_top_digit_large
    {p c d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (heq : 12 * d + 43 * c + 6 = 7 * p) :
    p < 2 * d ∧ d < p := by
  omega

/-! ## Exact modulus-size certificates -/

theorem switching_moduli : 42 * T = 222138 ∧ 28 * T = 148092 := by
  norm_num [T]

theorem switching_modulus_factorizations :
    42 * T = 2 * 3 ^ 2 * 7 * 41 * 43 ∧
    28 * T = 2 ^ 2 * 3 * 7 * 41 * 43 := by
  norm_num [T]

/-- Exact Euler-totient values of the two divisor-switching moduli. -/
theorem switching_modulus_totients :
    Nat.totient (42 * T) = 60480 ∧
    Nat.totient (28 * T) = 40320 := by
  rw [T_eq]
  constructor
  · rw [show 42 * 5289 = 2 * 9 * 7 * 41 * 43 by norm_num]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9 * 7 * 41) 43)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9 * 7) 41)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9) 7)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime 2 9)]
    rw [show 9 = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num)]
    norm_num [Nat.totient_prime]
  · rw [show 28 * 5289 = 4 * 3 * 7 * 41 * 43 by norm_num]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3 * 7 * 41) 43)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3 * 7) 41)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3) 7)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime 4 3)]
    rw [show 4 = 2 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num)]
    norm_num [Nat.totient_prime]

theorem switching_allowed_class_count_certificate :
    Nat.totient (42 * T) / 3 = 20160 ∧
    Nat.totient (28 * T) / 3 = 13440 := by
  rw [switching_modulus_totients.1, switching_modulus_totients.2]
  norm_num

/-- Numeric certificate for the `1/3` class fraction after the CRT
equal-fiber argument (the CRT argument itself is analytic-paper intake, not
hidden in this arithmetic theorem). -/
theorem switching_class_count_arithmetic :
    3 * 20160 = 60480 ∧ 3 * 13440 = 40320 := by
  norm_num

#print axioms T_eq
#print axioms branch_expansions
#print axioms n_expansion
#print axioms product_identity
#print axioms identity_PQ
#print axioms identity_RS
#print axioms identity_PS
#print axioms identity_QR
#print axioms identity_PR
#print axioms identity_QS
#print axioms n_add_one
#print axioms two_n_add_one
#print axioms n_strictMono
#print axioms familyPair_mem_pairSet
#print axioms familyPair_mapsTo_pairSet
#print axioms familyPair_injective
#print axioms pairSet_infinite_of_goodParameters_infinite
#print axioms fixed_primes_do_not_divide_branches
#print axioms branch_mod_3
#print axioms branch_mod_7_fixed
#print axioms P_Q_coprime
#print axioms P_R_coprime
#print axioms P_S_coprime
#print axioms Q_R_coprime
#print axioms Q_S_coprime
#print axioms R_S_coprime
#print axioms branches_pairwise_coprime
#print axioms allowed_residue_card_certificate
#print axioms P_top_residue_iff
#print axioms R_top_residue_iff
#print axioms P_top_digit_classification
#print axioms Q_top_digit_large
#print axioms R_top_digit_classification
#print axioms S_top_digit_large
#print axioms switching_modulus_factorizations
#print axioms switching_modulus_totients
#print axioms switching_allowed_class_count_certificate
#print axioms switching_class_count_arithmetic

end FullDensityCore
end Erdos730
