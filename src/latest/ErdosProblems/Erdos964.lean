/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

Formalizes original paper:
- [Eb25] S. Eberhard, Ratios of consecutive values of the divisor function. arXiv:2505.00727 (2025).
-/

/-
We prove that the sequence of ratios of consecutive values of the divisor function,
$\tau(n+1)/\tau(n)$, is everywhere dense in $(0, \infty)$, assuming the
Goldston-Graham-Pintz-Yildirim theorem (GPY). The proof proceeds by showing that every positive
rational number is a value taken by this sequence (in fact, infinitely often). This is achieved by
constructing specific configurations of prime factors for $n$ and $n+1$ using the GPY theorem to
ensure their existence. Finally, since the positive rationals are dense in the positive reals, the
result follows.
-/

import Mathlib

namespace Erdos964

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

/-
The divisor function tau(n) counts the number of divisors of n.
-/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-
E2(C) is the set of products of two distinct primes both greater than C.
-/
def E2 (C : ℕ) : Set ℕ :=
  { n | ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ p1 ≠ p2 ∧ C < p1 ∧ C < p2 ∧ n = p1 * p2 }

/-
L_i(x) = a_i * x + 1
-/
def L (a : ℕ) (x : ℕ) : ℕ := a * x + 1

/-
The set of ratios of consecutive values of the divisor function.
-/
def divisor_ratios : Set ℚ :=
  { q | ∃ n : ℕ, n > 0 ∧ q = (tau (n + 1) : ℚ) / (tau n : ℚ) }

/-
The statement of the Goldston-Graham-Pintz-Yildirim theorem (Corollary 2.1 in the paper).
-/
def GoldstonGrahamPintzYildirimStatement : Prop :=
  ∀ (a r : Fin 3 → ℕ),
    (∀ i, 0 < a i) → (∀ i, 0 < r i) →
    (∀ i, (r i).Coprime (a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (if a i > a j then a i - a j else a j - a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (r j)) →
    ∀ C : ℕ,
      ∃ i j, i < j ∧ {x : ℕ | r i ∣ L (a i) x ∧ r j ∣ L (a j) x ∧
        (L (a i) x) / r i ∈ E2 C ∧ (L (a j) x) / r j ∈ E2 C}.Infinite

/-
R is the set of values attained infinitely many times by the sequence d(n+1)/d(n).
-/
def R_set : Set ℚ := {q | {n | (tau (n + 1) : ℚ) / (tau n : ℚ) = q}.Infinite}

/-
Define the sequence a_i = (a, a+1, a+2).
-/
def a_seq (a : ℕ) : Fin 3 → ℕ := ![a, a + 1, a + 2]

/-
Identities relating L_i(x) and a_i.
a2 * L1 - a1 * L2 = 1
a3 * L2 - a2 * L3 = 1
a3/2 * L1 - a1/2 * L3 = 1
-/
lemma identities (a : ℕ) (x : ℕ) :
  let a_vec := a_seq a
  (a_vec 1 * L (a_vec 0) x = a_vec 0 * L (a_vec 1) x + 1) ∧
  (a_vec 2 * L (a_vec 1) x = a_vec 1 * L (a_vec 2) x + 1) ∧
  (a_vec 2 * L (a_vec 0) x / 2 = a_vec 0 * L (a_vec 2) x / 2 + 1) := by
    unfold a_seq L;
    simp +zetaDelta at *;
    grind

/-
Define the function f(x,y) = (x+1)(y+1)/(x+y+1).
-/
def f_rat (x y : ℕ) : ℚ := ((x + 1) * (y + 1) : ℚ) / (x + y + 1 : ℚ)

/-
If L1/r1 and L2/r2 are in E2(C), then d(n+1)/d(n) = d(a2 r1)/d(a1 r2).
Proof sketch:
1. Use `identities` to show `n+1 = a_seq a 1 * L (a_seq a 0) x`.
2. Let `E0 = L (a_seq a 0) x / r 0` and `E1 = L (a_seq a 1) x / r 1`.
3. Then `n+1 = a_seq a 1 * r 0 * E0` and `n = a_seq a 0 * r 1 * E1`.
4. Since `E0, E1 \in E2(C)`, their prime factors are $> C$.
5. The prime factors of `a_seq a 1 * r 0` and `a_seq a 0 * r 1` are $\le C$ by `hC`.
6. Thus `gcd(a_seq a 1 * r 0, E0) = 1` and `gcd(a_seq a 0 * r 1, E1) = 1`.
7. By multiplicativity of `tau`, `tau(n+1) = tau(a_seq a 1 * r 0) * tau(E0)` and `tau(n) = tau(a_seq a 0 * r 1) * tau(E1)`.
8. Since `E0, E1 \in E2(C)`, `tau(E0) = tau(E1) = 4`.
9. The result follows.
-/
lemma ratio_lemma_12 (a : ℕ) (r : Fin 3 → ℕ) (C : ℕ) (x : ℕ)
  (hr : ∀ i, 0 < r i)
  (hC : ∀ p, p.Prime → p ∣ (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) → p ≤ C)
  (h1 : r 0 ∣ L (a_seq a 0) x)
  (h2 : r 1 ∣ L (a_seq a 1) x)
  (hE1 : L (a_seq a 0) x / r 0 ∈ E2 C)
  (hE2 : L (a_seq a 1) x / r 1 ∈ E2 C) :
  let n := a_seq a 0 * L (a_seq a 1) x
  (tau (n + 1) : ℚ) / (tau n : ℚ) = (tau (a_seq a 1 * r 0) : ℚ) / (tau (a_seq a 0 * r 1) : ℚ) := by
    -- By multiplicativity of `tau`, `tau(n+1) = tau(a_seq a 1 * r 0) * tau(E0 �)`� and `tau(n) = tau(a_seq a 0 * r 1) * tau(E1)`.
    have h_tau_mul : let n := a_seq a 0 * L (a_seq a 1) x;
      tau (n + 1) = tau (a_seq a 1 * r 0) * tau (L (a_seq a 0) x / r 0) ∧
      tau n = tau (a_seq a 0 * r 1) * tau (L (a_seq a 1) x / r 1) := by
        constructor;
        · -- By definition of $E2$, we know that $L (a_seq a 0) x / r 0$ is in $E2 C$, so its prime factors are greater than $C$.
          have h_coprime : Nat.gcd (a_seq a 1 * r 0) (L (a_seq a 0) x / r 0) = 1 := by
            -- Since $L (a_seq a 0) x / r 0 \in E2(C)$, its prime factors are greater than $C$.
            have h_prime_factors_E2 : ∀ p, Nat.Prime p → p ∣ (L (a_seq a 0) x / r 0) → p > C := by
              intro p pp dp; rcases hE1 with ⟨ p1, p2, hp1, hp2, hne, hC1, hC2, he ⟩ ; simp_all +decide ;
              simp_all +decide [ Nat.Prime.dvd_mul ];
              rcases dp with ( dp | dp ) <;> have := Nat.prime_dvd_prime_iff_eq pp hp1 <;> have := Nat.prime_dvd_prime_iff_eq pp hp2 <;> aesop;
            refine' Nat.coprime_of_dvd' _;
            intro k hk hk' hk''; specialize h_prime_factors_E2 k hk hk''; specialize hC k hk; simp_all +decide [ Nat.Prime.dvd_mul ] ;
            grind;
          -- By definition of $L$, we know that $n + 1 = a_seq a 1 * r 0 * (L (a_seq a 0) x / r 0)$.
          have hL1 : a_seq a 0 * L (a_seq a 1) x + 1 = a_seq a 1 * r 0 * (L (a_seq a 0) x / r 0) := by
            obtain ⟨ k, hk ⟩ := h1;
            unfold L at *; simp_all +decide [ mul_comm, mul_assoc, mul_left_comm ] ;
            unfold a_seq at *; norm_num at *; nlinarith;
          unfold tau;
          rw [ hL1, Nat.divisors_mul ];
          rw [ ← Nat.divisors_mul ];
          exact Nat.Coprime.card_divisors_mul h_coprime;
        · -- By multiplicativity of `tau`, we have `tau(n) = tau(a_seq a 0 * r 1) * tau(L (a_seq a 1) x / r 1)`.
          have h_tau_mul : ∀ {m n : ℕ}, Nat.gcd m n = 1 → tau (m * n) = tau m * tau n := by
            unfold tau;
            exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
          rw [ ← h_tau_mul, Nat.mul_assoc, Nat.mul_div_cancel' h2 ];
          -- Since $p1$ and $p2$ are primes greater than $C$, and $a_seq a 0$ and $r 1$ are products of primes ≤ $C$, their gcd must be 1.
          have h_coprime : ∀ p : ℕ, Nat.Prime p → p ∣ a_seq a 0 * r 1 → p ≤ C := by
            intro p pp dp; specialize hC p pp; simp_all +decide [ mul_assoc, Nat.Prime.dvd_mul ] ;
            exact hC <| by rcases dp with ( dp | dp ) <;> [ exact Or.inl dp; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl dp ] ;
          obtain ⟨ p1, p2, hp1, hp2, hne, hlt1, hlt2, hn ⟩ := hE2;
          rw [ hn, Nat.gcd_comm ];
          exact Nat.Coprime.mul_left ( hp1.coprime_iff_not_dvd.mpr fun h => by linarith [ h_coprime p1 hp1 h ] ) ( hp2.coprime_iff_not_dvd.mpr fun h => by linarith [ h_coprime p2 hp2 h ] );
    -- Since `E0, E1 \in E2(C)`, `tau(E0) = tau(E1) = 4`.
    have h_tau_E2 : ∀ E ∈ E2 C, tau E = 4 := by
      intro E hE;
      -- Since $E \in E2(C)$, we have $E = p1 * p2$ for some distinct primes $ �p�1$ and $p2$ greater than $C$.
      obtain ⟨p1, p2, hp1, hp2, hneq, hgt⟩ := hE
      have h_divisors : Nat.divisors E = {1, p1, p2, p1 * p2} := by
        rw [ hgt.2.2, Nat.divisors_mul, hp1.divisors, hp2.divisors ];
        simpa [ Finset.ext_iff, Finset.mem_mul ] using by tauto;
      rcases p1 with ( _ | _ | p1 ) <;> rcases p2 with ( _ | _ | p2 ) <;> simp_all +decide;
      unfold tau; simp +decide [h_divisors] ;
      grind;
    simp_all +decide [ mul_div_mul_right ]

/-
The three values that R is guaranteed to contain.
-/
def val1 (a : ℕ) (r : Fin 3 → ℕ) : ℚ := (tau (a_seq a 1 * r 0) : ℚ) / (tau (a_seq a 0 * r 1) : ℚ)
def val2 (a : ℕ) (r : Fin 3 → ℕ) : ℚ := (tau (a_seq a 2 * r 1) : ℚ) / (tau (a_seq a 1 * r 2) : ℚ)
def val3 (a : ℕ) (r : Fin 3 → ℕ) : ℚ := (tau (a_seq a 2 / 2 * r 0) : ℚ) / (tau (a_seq a 0 / 2 * r 2) : ℚ)

/-
Analogous to ratio_lemma_12 but for indices 1 and 2.
If L2/r2 and L3/r3 are in E2(C), then d(n+1)/d(n) = d(a3 r2)/d(a2 r3).
-/
lemma ratio_lemma_23 (a : ℕ) (r : Fin 3 → ℕ) (C : ℕ) (x : ℕ)
  (hr : ∀ i, 0 < r i)
  (hC : ∀ p, p.Prime → p ∣ (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) → p ≤ C)
  (h1 : r 1 ∣ L (a_seq a 1) x)
  (h2 : r 2 ∣ L (a_seq a 2) x)
  (hE1 : L (a_seq a 1) x / r 1 ∈ E2 C)
  (hE2 : L (a_seq a 2) x / r 2 ∈ E2 C) :
  let n := a_seq a 1 * L (a_seq a 2) x
  (tau (n + 1) : ℚ) / (tau n : ℚ) = (tau (a_seq a 2 * r 1) : ℚ) / (tau (a_seq a 1 * r 2) : ℚ) := by
    -- Using the identity and properties of the divisor function, we can simplify the expression.
    have h_simp : (tau (a_seq a 2 * r 1 * (L (a_seq a 1) x / r 1)) : ℚ) / (tau (a_seq a 1 * r 2 * (L (a_seq a 2) x / r 2)) : ℚ) = (tau (a_seq a 2 * r 1) : ℚ) / (tau (a_seq a 1 * r 2) : ℚ) := by
      -- Since $E0$ and $E1$ are in $E2(C)$, we have $\tau(E0) = \tau(E1) = 4$.
      obtain ⟨p1, p2, hp1, hp2, hneq, hE0⟩ := hE1
      obtain ⟨q1, q2, hq1, hq2, hneq', hE1⟩ := hE2
      have h_tau_E0 : tau ((L (a_seq a 1) x) / r 1) = 4 := by
        -- Since $p1$ and $p2$ are distinct primes, the number of divisors of $p1 * p2$ is $(1 + 1)(1 + 1) = 4$.
        have h_divisors : Nat.divisors (p1 * p2) = {1, p1, p2, p1 * p2} := by
          rw [ Nat.divisors_mul, hp1.divisors, hp2.divisors ];
          simpa [ Finset.ext_iff, Finset.mem_mul ] using by tauto;
        rcases p1 with ( _ | _ | p1 ) <;> rcases p2 with ( _ | _ | p2 ) <;> simp_all +decide;
        unfold tau; simp +decide [h_divisors] ;
        grind
      have h_tau_E1 : tau ((L (a_seq a 2) x) / r 2) = 4 := by
        -- Since $q1$ and $q2$ are distinct primes, the divisors of $q1 * q2$ are $1, q1, q2, q1 * q2$.
        have h_divisors : Nat.divisors (q1 * q2) = {1, q1, q2, q1 * q2} := by
          rw [ Nat.divisors_mul, hq1.divisors, hq2.divisors ];
          simpa [ Finset.ext_iff, Finset.mem_mul ] using by tauto;
        rcases q1 with ( _ | _ | q1 ) <;> rcases q2 with ( _ | _ | q2 ) <;> simp_all +decide;
        unfold tau; simp +decide [h_divisors] ;
        grind;
      -- Since $a_seq a 2 * r 1$ and $a_seq a 1 * r 2$ are coprime to $E0$ and $E1$ respectively, we can apply the multiplicativity of the divisor function.
      have h_coprime : Nat.gcd (a_seq a 2 * r 1) ((L (a_seq a 1) x) / r 1) = 1 ∧ Nat.gcd (a_seq a 1 * r 2) ((L (a_seq a 2) x) / r 2) = 1 := by
        constructor <;> refine' Nat.coprime_of_dvd' _;
        · intro k hk hk1 hk2; have := Nat.dvd_trans hk2 ( show L ( a_seq a 1 ) x / r 1 ∣ L ( a_seq a 1 ) x from Nat.div_dvd_of_dvd h1 ) ; simp_all +decide [ Nat.Prime.dvd_mul ] ;
          contrapose! hC;
          exact ⟨ k, hk, by aesop, by rcases hk2 with ( hk2 | hk2 ) <;> have := Nat.prime_dvd_prime_iff_eq hk hp1 <;> have := Nat.prime_dvd_prime_iff_eq hk hp2 <;> aesop ⟩;
        · intro k hk hk1 hk2; have := Nat.Prime.dvd_mul hk |>.1 hk1; simp_all +decide [ Nat.Prime.dvd_mul ] ;
          rcases this with ( hk | hk ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
          · grind;
          · grind;
      -- Apply the multiplicativity of the divisor function.
      have h_mul : ∀ {m n : ℕ}, Nat.gcd m n = 1 → tau (m * n) = tau m * tau n := by
        intros m n h_coprime
        unfold tau;
        exact Nat.Coprime.card_divisors_mul h_coprime;
      rw [ h_mul h_coprime.1, h_mul h_coprime.2, h_tau_E0, h_tau_E1 ] ; ring_nf;
      field_simp;
      rw [ Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ ( by norm_num ) ];
    convert h_simp using 3;
    · rw [ Nat.mul_assoc, Nat.mul_div_cancel' h1 ];
      unfold L a_seq; ring_nf;
      exact congr_arg _ ( by erw [ show ( ![a, 1 + a, 2 + a] : Fin 3 → ℕ ) 1 = 1 + a by rfl ] ; erw [ show ( ![a, 1 + a, 2 + a] : Fin 3 → ℕ ) 2 = 2 + a by rfl ] ; ring );
    · rw [ mul_assoc, Nat.mul_div_cancel' h2 ]

/-
Algebraic identity for ratio_lemma_13: n + 1 = (a3 * r1 / 2) * (L1 / r1).
This follows from the identity a3/2 * L1 - a1/2 * L3 = 1.
Multiplying by 2: a3 * L1 - a1 * L3 = 2.
So a1 * L3 + 2 = a3 * L1.
Dividing by 2: a1 * L3 / 2 + 1 = a3 * L1 / 2.
LHS is n + 1.
RHS is a3 * r1 * (L1/r1) / 2 = (a3 * r1 / 2) * (L1/r1) since a3 * r1 is even (a3 is even).
-/
lemma ratio_lemma_13_algebra (a : ℕ) (r : Fin 3 → ℕ) (x : ℕ)
  (ha : Even a)
  (hr : ∀ i, 0 < r i)
  (h1 : r 0 ∣ L (a_seq a 0) x) :
  let n := (a_seq a 0) * L (a_seq a 2) x / 2
  n + 1 = (a_seq a 2 * r 0 / 2) * (L (a_seq a 0) x / r 0) := by
    obtain ⟨ k, hk ⟩ := h1;
    unfold a_seq L at *;
    obtain ⟨ m, rfl ⟩ := ha; simp_all +decide ; ring_nf;
    norm_num [ show m * 2 + m * x * 4 + m ^ 2 * x * 4 = 2 * ( m + m * x * 2 + m ^ 2 * x * 2 ) by ring, show m * r 0 * 2 + r 0 * 2 = 2 * ( m * r 0 + r 0 ) by ring ];
    nlinarith [ hr 0 ]

/-
Analogous to ratio_lemma_12 but for indices 1 and 3 (0 and 2 in 0-indexing).
If L1/r1 and L3/r3 are in E2(C), then d(n+1)/d(n) = d(a3 r1 / 2)/d(a1 r3 / 2).
Note: n = a1 L3 / 2.
Identity used: a3/2 * L1 - a1/2 * L3 = 1.
So n+1 = a3/2 * L1.
n = a1/2 * L3.
Then substitute L1 = r1 * E1, L3 = r3 * E3.
n+1 = a3/2 * r1 * E1.
n = a1/2 * r3 * E3.
Then use multiplicativity and tau(E)=4.
-/
lemma ratio_lemma_13 (a : ℕ) (r : Fin 3 → ℕ) (C : ℕ) (x : ℕ)
  (ha : Even a)
  (hr : ∀ i, 0 < r i)
  (hC : ∀ p, p.Prime → p ∣ (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) → p ≤ C)
  (h1 : r 0 ∣ L (a_seq a 0) x)
  (h3 : r 2 ∣ L (a_seq a 2) x)
  (hE1 : L (a_seq a 0) x / r 0 ∈ E2 C)
  (hE3 : L (a_seq a 2) x / r 2 ∈ E2 C) :
  let n := (a_seq a 0) * L (a_seq a 2) x / 2
  (tau (n + 1) : ℚ) / (tau n : ℚ) = (tau ((a_seq a 2) * r 0 / 2) : ℚ) / (tau ((a_seq a 0) * r 2 / 2) : ℚ) := by
    -- By multiplicativity of `tau`, we have `tau(n+1) = tau(a_seq a 2 * r 0 / 2 �)� * tau(E1)` and `tau(n) = tau(a_seq a 0 * r 2 / 2) * tau(E3)`.
    have h_tau_mult : (tau (a_seq a 0 * L (a_seq a 2) x / 2 + 1) : ℚ) = (tau (a_seq a 2 * r 0 / 2) : ℚ) * (tau (L (a_seq a 0) x / r 0) : ℚ) ∧ (tau (a_seq a 0 * L (a_seq a 2) x / 2) : ℚ) = (tau (a_seq a 0 * r 2 / 2) : ℚ) * (tau (L (a_seq a 2) x / r 2) : ℚ) := by
      constructor <;> norm_cast;
      · -- Let's simplify the expression for $n + 1$.
        have h_n1 : a_seq a 0 * L (a_seq a 2) x / 2 + 1 = (a_seq a 2 * r 0 / 2) * (L (a_seq a 0) x / r 0) := by
          convert ratio_lemma_13_algebra a r x ha hr h1 using 1;
        -- Since $a_seq a 2 * r 0 / 2$ and $L (a_seq a 0) x / r 0$ are coprime, we can apply the multiplicativity of $\tau$.
        have h_coprime : Nat.gcd (a_seq a 2 * r 0 / 2) (L (a_seq a 0) x / r 0) = 1 := by
          obtain ⟨ p1, p2, hp1, hp2, hne, hC1, hC2, h ⟩ := hE1;
          refine' Nat.Coprime.symm ( h.symm ▸ Nat.Coprime.mul_left _ _ );
          · refine' hp1.coprime_iff_not_dvd.mpr _;
            intro H;
            -- Since $p1$ divides $a_seq a 2 * r 0 / 2$, it must also divide $a_seq a 2 * r 0$.
            have h_div : p1 ∣ a_seq a 2 * r 0 := by
              convert H.mul_left 2 using 1;
              rw [ Nat.mul_div_cancel' ];
              exact dvd_mul_of_dvd_left ( even_iff_two_dvd.mp ( by unfold a_seq; simp +arith +decide [ *, parity_simps ] ) ) _;
            contrapose! hC1;
            exact hC p1 hp1 ( dvd_trans h_div ( by exact ⟨ a_seq a 0 * a_seq a 1 * r 1 * r 2, by ring ⟩ ) );
          · refine' hp2.coprime_iff_not_dvd.mpr _;
            intro H;
            -- Since $p2$ divides $a_seq a 2 * r 0 / 2$, it must also divide $a_seq a 2 * r 0$.
            have h_div : p2 ∣ a_seq a 2 * r 0 := by
              convert H.mul_left 2 using 1;
              rw [ Nat.mul_div_cancel' ];
              exact dvd_mul_of_dvd_left ( even_iff_two_dvd.mp ( by unfold a_seq; simp +decide [ *, parity_simps ] ) ) _;
            contrapose! hC2;
            exact hC p2 hp2 ( dvd_trans h_div ( by exact ⟨ a_seq a 0 * a_seq a 1 * r 1 * r 2, by ring! ⟩ ) );
        rw [ h_n1 ];
        unfold tau;
        exact Nat.Coprime.card_divisors_mul h_coprime;
      · -- Since $a_seq a 0 * r 2 / 2$ and $L (a_seq a 2) x / r 2$ are coprime, we can apply the multiplicativity of the divisor function.
        have h_coprime : Nat.gcd (a_seq a 0 * r 2 / 2) (L (a_seq a 2) x / r 2) = 1 := by
          -- Since $E3 \in E2(C)$, its prime factors are greater than $C$. By $hC$, any prime factor of $a_seq a 0 * r 2$ must be $\leq C$. Therefore, $E3 �$� and $a_seq a 0 * r 2$ share no common prime factors, implying they are coprime.
          have h_coprime : ∀ p, Nat.Prime p → p ∣ a_seq a 0 * r 2 → p ≤ C := by
            intro p pp dp; specialize hC p pp; simp_all +decide [ mul_assoc, Nat.Prime.dvd_mul ] ;
            exact hC <| by aesop;
          obtain ⟨ p1, p2, hp1, hp2, hne, hC1, hC2, h ⟩ := hE3;
          refine' Nat.Coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd _ ) _;
          · exact dvd_mul_of_dvd_left ( even_iff_two_dvd.mp ( by unfold a_seq; aesop ) ) _;
          · rw [ h ];
            exact Nat.Coprime.mul_right ( Nat.Coprime.symm <| hp1.coprime_iff_not_dvd.mpr fun h => by linarith [ h_coprime p1 hp1 h ] ) ( Nat.Coprime.symm <| hp2.coprime_iff_not_dvd.mpr fun h => by linarith [ h_coprime p2 hp2 h ] );
        -- Apply the multiplicativity of the divisor function.
        have h_mul : ∀ {m n : ℕ}, Nat.gcd m n = 1 → tau (m * n) = tau m * tau n := by
          unfold tau;
          exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
        convert h_mul h_coprime using 1;
        rw [ Nat.div_mul_div_comm ( show 2 ∣ a_seq a 0 * r 2 from dvd_mul_of_dvd_left ( even_iff_two_dvd.mp <| by unfold a_seq; simp +decide [ *, parity_simps ] ) _ ) h3 ];
        rw [ ← Nat.mul_div_mul_right _ _ ( hr 2 ) ] ; ring_nf;
    -- Since `L (a_seq a 0) x / r 0` and `L (a_seq a 2) x / r 2` are in `E2(C)`, their prime factors are $> C$.
    have h_tau_E2 : ∀ {n : ℕ}, n ∈ E2 C → (tau n : ℚ) = 4 := by
      intro n hn
      obtain ⟨p1, p2, hp1, hp2, hneq, hgt⟩ := hn
      have h_divisors : Nat.divisors (p1 * p2) = {1, p1, p2, p1 * p2} := by
        rw [ Nat.divisors_mul, hp1.divisors, hp2.divisors ];
        simpa [ Finset.ext_iff, Finset.mem_mul ] using by tauto;
      simp_all +decide [ tau ];
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ hp1.ne_zero, hp2.ne_zero, hp1.ne_one, hp2.ne_one, hneq ];
      exact ⟨ Ne.symm hp1.ne_one, Ne.symm hp2.ne_one, Nat.ne_of_lt ( one_lt_mul'' hp1.one_lt hp2.one_lt ) ⟩;
    grind

/-
Under the conditions of the GPY theorem, R contains one of the three specified values.
Proof sketch:
1. Let `P = a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2`.
2. Let `C` be the maximum prime factor of `P` (or 1 if P=0/1).
3. Apply `hGPY` with `a_seq a`, `r`, and `C`.
   - Verify hypotheses of `hGPY`:
     - `a_seq a i > 0`: since `a > 0`.
     - `r i > 0`: given.
     - `(r i).Coprime (a_seq a i)`: given.
     - `(r i).Coprime (a_seq a i - a_seq a j)`:
       - Differences are `|1|, |2|, |1|`.
       - `r i` are odd, so coprime to 1 and 2.
     - `(r i).Coprime (r j)`: given.
4. Obtain `i, j` with `i < j` and infinite set of `x`.
5. Cases on `(i, j)`:
   - `(0, 1)`: Use `ratio_lemma_12`. The ratio is `val1`.
   - `(1, 2)`: Use `ratio_lemma_23`. The ratio is `val2`.
   - `(0, 2)`: Use `ratio_lemma_13`. The ratio is `val3`.
6. In each case, the set of `n` is infinite because the set of `x` is infinite and the map `x -> n` is injective (linear).
   - `n` depends on `x` linearly: `n = a_seq a 0 * (a_seq a 1 * x + 1)` etc.
   - Since `a_seq a i > 0`, the map is injective.
   - Image of infinite set under injective map is infinite.
7. Thus the ratio is in `R_set`.
-/
lemma R_contains_one_of_three (hGPY : GoldstonGrahamPintzYildirimStatement)
  (a : ℕ) (r : Fin 3 → ℕ)
  (ha : Even a) (ha_pos : 0 < a)
  (hr : ∀ i, 0 < r i)
  (hr_odd : ∀ i, Odd (r i))
  (hr_coprime : ∀ i j, i ≠ j → (r i).Coprime (r j))
  (hra : ∀ i, (r i).Coprime (a_seq a i)) :
  val1 a r ∈ R_set ∨ val2 a r ∈ R_set ∨ val3 a r ∈ R_set := by
    -- By the properties of the Goldston-Graham-Pintz-Yildirim theorem, we can find such `i` and `j`.
    obtain ⟨i, j, hij, h_inf⟩ := hGPY (a_seq a) r
      (fun i => by fin_cases i <;> [ exact ha_pos; exact Nat.succ_pos _; exact Nat.succ_pos _ ])
      hr hra
      (fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp_all +decide [ Fin.forall_fin_succ ]
        all_goals unfold a_seq; simp +decide [*])
      hr_coprime
      (Nat.findGreatest (fun p => p.Prime ∧ p ∣ a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2))
    -- We'll use the fact that if the set of $x$ is infinite, then the set of corresponding $n$ values is also infinite.
    have h_infinite_n : Set.Infinite {n : ℕ | ∃ x : ℕ, r i ∣ L (a_seq a i) x ∧ r j ∣ L (a_seq a j) x ∧ L (a_seq a i) x / r i ∈ E2 (Nat.findGreatest (fun p => p.Prime ∧ p ∣ a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2)) ∧ L (a_seq a j) x / r j ∈ E2 (Nat.findGreatest (fun p => p.Prime ∧ p ∣ a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2)) ∧ n = if i = 0 ∧ j = 1 then a_seq a 0 * L (a_seq a 1) x else if i = 1 ∧ j = 2 then a_seq a 1 * L (a_seq a 2) x else (a_seq a 0) * L (a_seq a 2) x / 2} := by
      intro H;
      apply h_inf;
      refine' Set.Finite.subset ( H.preimage _ ) _;
      use fun x => if i = 0 ∧ j = 1 then a_seq a 0 * L ( a_seq a 1 ) x else if i = 1 ∧ j = 2 then a_seq a 1 * L ( a_seq a 2 ) x else a_seq a 0 * L ( a_seq a 2 ) x / 2;
      · intro x hx y hy; simp +decide [ Fin.forall_fin_succ ] at *;
        fin_cases i <;> fin_cases j <;> simp +decide at hij;
        · simp +decide [ L, a_seq ];
          aesop;
        · simp +decide [L] at *;
          intro h; rw [ Nat.div_eq_iff_eq_mul_left zero_lt_two ] at h; simp_all +decide [ Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm ] ;
          · rw [ Nat.mul_div_cancel' ] at h;
            · simp_all +decide [ a_seq ];
              exact h.resolve_right ha_pos.ne';
            · exact dvd_mul_of_dvd_left ( even_iff_two_dvd.mp ( by unfold a_seq; simp +decide [ ha, parity_simps ] ) ) _;
          · exact dvd_mul_of_dvd_left ( even_iff_two_dvd.mp ( by unfold a_seq; simp +decide [ ha, parity_simps ] ) ) _;
        · simp +decide [L, a_seq] at *;
      · exact fun x hx => ⟨ x, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, rfl ⟩;
    -- By the properties of the Goldston-Graham-Pintz-Yildirim theorem, we can find such `i` and `j` and use them to show that one of the three values is in `R_set`.
    have h_ratio : ∀ x : ℕ, (r i ∣ L (a_seq a i) x ∧ r j ∣ L (a_seq a j) x ∧ L (a_seq a i) x / r i ∈ E2 (Nat.findGreatest (fun p => p.Prime ∧ p ∣ a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2)) ∧ L (a_seq a j) x / r j ∈ E2 (Nat.findGreatest (fun p => p.Prime ∧ p ∣ a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2))) → (tau ((if i = 0 ∧ j = 1 then a_seq a 0 * L (a_seq a 1) x else if i = 1 ∧ j = 2 then a_seq a 1 * L (a_seq a 2) x else (a_seq a 0) * L (a_seq a 2) x / 2) + 1) : ℚ) / (tau (if i = 0 ∧ j = 1 then a_seq a 0 * L (a_seq a 1) x else if i = 1 ∧ j = 2 then a_seq a 1 * L (a_seq a 2) x else (a_seq a 0) * L (a_seq a 2) x / 2) : ℚ) = if i = 0 ∧ j = 1 then val1 a r else if i = 1 ∧ j = 2 then val2 a r else val3 a r := by
      fin_cases i <;> fin_cases j <;> simp +decide at hij;
      · intro x hx;
        convert ratio_lemma_12 a r _ x hr _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 using 1;
        intro p pp dp; refine' Nat.le_findGreatest _ _ <;> norm_num at *;
        · exact Nat.le_of_dvd ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ) ( hr 0 ) ) ( hr 1 ) ) ( hr 2 ) ) dp;
        · grind;
      · simp +zetaDelta at *;
        intro x hx1 hx2 hx3 hx4; exact (by
        convert ratio_lemma_13 a r _ x ha hr _ hx1 hx2 hx3 hx4 using 1;
        · unfold val3; ring_nf;
          rw [ Nat.mul_comm ( a_seq a 2 / 2 ), Nat.mul_comm ( a_seq a 0 / 2 ) ] ; rw [ Nat.mul_div_assoc _ ( even_iff_two_dvd.mp ( by unfold a_seq; simp +decide [ *, parity_simps ] ) ), Nat.mul_div_assoc _ ( even_iff_two_dvd.mp ( by unfold a_seq; simp +decide [ *, parity_simps ] ) ) ] ;
        · intro p pp dp; refine' Nat.le_findGreatest _ _;
          · exact Nat.le_of_dvd ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop ) ) ) ( hr 0 ) ) ( hr 1 ) ) ( hr 2 ) ) dp;
          · exact And.symm ⟨dp, pp⟩ );
      · intro x hx;
        convert ratio_lemma_23 a r _ x hr _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 using 1;
        intro p pp dp; refine' Nat.le_findGreatest _ _;
        · exact Nat.le_of_dvd ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop_cat ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop_cat ) ) ) ( Nat.pos_of_ne_zero ( by unfold a_seq; aesop_cat ) ) ) ( Nat.pos_of_ne_zero ( by linarith [ hr 0 ] ) ) ) ( Nat.pos_of_ne_zero ( by linarith [ hr 1 ] ) ) ) ( Nat.pos_of_ne_zero ( by linarith [ hr 2 ] ) ) ) dp;
        · exact And.symm ⟨dp, pp⟩;
    contrapose! h_infinite_n;
    simp_all +decide [ R_set ];
    refine Set.Finite.subset ( h_infinite_n.1.union ( h_infinite_n.2.1.union h_infinite_n.2.2 ) ) ?_;
    rintro n ⟨ x, hx₁, hx₂, hx₃, hx₄, rfl ⟩ ; specialize h_ratio x; aesop;

/-
By modifying r_i to r'_i = r_i * p_i^(e_i-1), we can show that R contains one of the modified values.
The modified values are obtained by multiplying the original values by e_i/e_j.
This corresponds to the step in the paper where they deduce that R contains one of the three expressions involving e_i.
-/
lemma R_contains_modified_values (hGPY : GoldstonGrahamPintzYildirimStatement)
  (a : ℕ) (r : Fin 3 → ℕ) (p : Fin 3 → ℕ) (e : Fin 3 → ℕ)
  (ha : Even a) (ha_pos : 0 < a)
  (hr : ∀ i, 0 < r i)
  (hr_odd : ∀ i, Odd (r i))
  (hr_coprime : ∀ i j, i ≠ j → (r i).Coprime (r j))
  (hra : ∀ i, (r i).Coprime (a_seq a i))
  (hp_prime : ∀ i, (p i).Prime)
  (hp_distinct : ∀ i j, i ≠ j → p i ≠ p j)
  (hp_coprime_a : ∀ i j, (p i).Coprime (a_seq a j))
  (hp_coprime_r : ∀ i j, (p i).Coprime (r j))
  (he_pos : ∀ i, 0 < e i) :
  let v1 := (tau (a_seq a 1 * r 0) * e 0 : ℚ) / (tau (a_seq a 0 * r 1) * e 1 : ℚ)
  let v2 := (tau (a_seq a 2 * r 1) * e 1 : ℚ) / (tau (a_seq a 1 * r 2) * e 2 : ℚ)
  let v3 := (tau (a_seq a 2 / 2 * r 0) * e 0 : ℚ) / (tau (a_seq a 0 / 2 * r 2) * e 2 : ℚ)
  v1 ∈ R_set ∨ v2 ∈ R_set ∨ v3 ∈ R_set := by
    convert R_contains_one_of_three hGPY a ( fun i => r i * p i ^ ( e i - 1 ) ) ha ha_pos ( fun i => mul_pos ( hr i ) ( pow_pos ( Nat.Prime.pos ( hp_prime i ) ) _ ) ) ( fun i => ?_ ) ( fun i j hij => ?_ ) ( fun i => ?_ ) using 1;
    · -- Apply the multiplicative property of the divisor function.
      have h_mul : ∀ {m n : ℕ}, Nat.Coprime m n → tau (m * n) = tau m * tau n := by
        unfold tau;
        exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
      -- Apply the multiplicative property of the divisor function to each term in the ratio.
      have h1 : tau (a_seq a 1 * (r 0 * p 0 ^ (e 0 - 1))) = tau (a_seq a 1 * r 0) * tau (p 0 ^ (e 0 - 1)) := by
        rw [ ← h_mul ];
        · rw [ mul_assoc ];
        · refine' Nat.Coprime.mul_left _ _;
          · exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm ( hp_coprime_a 0 1 ) );
          · exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm ( hp_coprime_r 0 0 ) )
      have h2 : tau (a_seq a 0 * (r 1 * p 1 ^ (e 1 - 1))) = tau (a_seq a 0 * r 1) * tau (p 1 ^ (e 1 - 1)) := by
        rw [ ← h_mul ];
        · rw [ mul_assoc ];
        · refine' Nat.Coprime.mul_left _ _;
          · exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm ( hp_coprime_a _ _ ) );
          · exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm ( hp_coprime_r _ _ ) );
      -- Apply the formula for the number of divisors of a prime power.
      have h_divisors_prime_power : ∀ {p : ℕ} (hp : Nat.Prime p) {k : ℕ}, tau (p ^ k) = k + 1 := by
        intro p hp k; rw [ tau ] ; simp +decide [ Nat.divisors_prime_pow hp ] ;
      unfold val1; aesop;
    · unfold val2 val3; simp +decide [*] ;
      -- By definition of tau, we know that tau(n * p^k) = (k + 1) * tau(n) for any prime p and integer k.
      have h_tau_mul : ∀ n k p : ℕ, Nat.Prime p → Nat.Coprime n p → tau (n * p ^ k) = (k + 1) * tau n := by
        intros n k p hp hcoprime
        have h_tau_mul : (Nat.divisors (n * p ^ k)).card = (Nat.divisors n).card * (Nat.divisors (p ^ k)).card := by
          have h_tau_mul : ∀ {m n : ℕ}, Nat.Coprime m n → (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
            exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
          exact h_tau_mul <| hcoprime.pow_right _;
        simp_all +decide [ Nat.divisors_prime_pow, mul_comm ];
        exact h_tau_mul;
      have h_tau_mul : tau (a_seq a 2 * (r 1 * p 1 ^ (e 1 - 1))) = (e 1 - 1 + 1) * tau (a_seq a 2 * r 1) ∧ tau (a_seq a 1 * (r 2 * p 2 ^ (e 2 - 1))) = (e 2 - 1 + 1) * tau (a_seq a 1 * r 2) ∧ tau (a_seq a 2 / 2 * (r 0 * p 0 ^ (e 0 - 1))) = (e 0 - 1 + 1) * tau (a_seq a 2 / 2 * r 0) ∧ tau (a_seq a 0 / 2 * (r 2 * p 2 ^ (e 2 - 1))) = (e 2 - 1 + 1) * tau (a_seq a 0 / 2 * r 2) := by
        refine' ⟨ _, _, _, _ ⟩;
        · convert h_tau_mul ( a_seq a 2 * r 1 ) ( e 1 - 1 ) ( p 1 ) ( hp_prime 1 ) _ using 1;
          · rw [ mul_assoc ];
          · exact Nat.Coprime.mul_left ( hp_coprime_a _ _ |> Nat.Coprime.symm ) ( hp_coprime_r _ _ |> Nat.Coprime.symm );
        · convert h_tau_mul ( a_seq a 1 * r 2 ) ( e 2 - 1 ) ( p 2 ) ( hp_prime 2 ) _ using 1;
          · rw [ mul_assoc ];
          · exact Nat.Coprime.mul_left ( hp_coprime_a 2 1 |> Nat.Coprime.symm ) ( hp_coprime_r 2 2 |> Nat.Coprime.symm );
        · convert h_tau_mul ( a_seq a 2 / 2 * r 0 ) ( e 0 - 1 ) ( p 0 ) ( hp_prime 0 ) _ using 1;
          · ring_nf;
          · simp_all +decide [Nat.coprime_mul_iff_right, Nat.Coprime, Nat.gcd_comm];
            exact Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd <| even_iff_two_dvd.mp <| by unfold a_seq; simp +arith +decide [ *, parity_simps ] ) ( hp_coprime_a 0 2 );
        · convert h_tau_mul ( a_seq a 0 / 2 * r 2 ) ( e 2 - 1 ) ( p 2 ) ( hp_prime 2 ) _ using 1;
          · ring_nf;
          · simp_all +decide [Nat.coprime_mul_iff_right, Nat.Coprime, Nat.gcd_comm];
            refine' Nat.Coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd _ ) _;
            · exact even_iff_two_dvd.mp ha;
            · exact Nat.Coprime.symm ( hp_coprime_a 2 0 );
      simp_all +decide [ Nat.sub_add_cancel ( he_pos _ ) ];
      ring_nf;
    · simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
      norm_num [ Nat.mul_mod, Nat.pow_mod, hr_odd i, Nat.Prime.eq_two_or_odd ( hp_prime i ) |> Or.resolve_left <| ?_ ];
      cases Nat.Prime.eq_two_or_odd ( hp_prime i ) <;> simp_all +decide;
      specialize hp_coprime_a i 0 ; simp_all +decide;
      unfold a_seq at hp_coprime_a; simp_all +decide [Nat.odd_iff] ;
    · apply_rules [ Nat.Coprime.mul_left, Nat.Coprime.mul_right ];
      · exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm ( hp_coprime_r _ _ ) );
      · exact Nat.Coprime.pow_left _ ( hp_coprime_r i j );
      · exact Nat.coprime_pow_primes _ _ ( hp_prime _ ) ( hp_prime _ ) ( hp_distinct _ _ hij );
    · exact Nat.Coprime.mul_left ( hra i ) ( Nat.Coprime.pow_left _ ( hp_coprime_a i i ) )

/-
With specific choices of e_i, the three values become equal to the target value.
Corrected target: (d1 * d3 * d6) / (d2 * d4 * d5).
Proof is just algebraic simplification.
Note: d_i are positive integers (since arguments are positive), so we can divide by them in Q.
Arguments are positive:
a > 0, so a_seq a i > 0.
r i > 0.
a is even, so a/2 > 0 (since a >= 2).
So all arguments to tau are positive, so tau >= 1, so d_i >= 1.
So denominators are non-zero.
-/
lemma equal_values_lemma (a : ℕ) (r : Fin 3 → ℕ)
  (ha_pos : 0 < a)
  (hr : ∀ i, 0 < r i) :
  let d1 := tau (a_seq a 1 * r 0)
  let d2 := tau (a_seq a 0 * r 1)
  let d3 := tau (a_seq a 2 * r 1)
  let d4 := tau (a_seq a 1 * r 2)
  let d5 := tau (a_seq a 2 / 2 * r 0)
  let d6 := tau (a_seq a 0 / 2 * r 2)
  let e0 := d1 * d3 * d6 ^ 2
  let e1 := d1 * d4 * d5 * d6
  let e2 := d2 * d4 * d5 ^ 2
  let target := (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ)
  (d1 * e0 : ℚ) / (d2 * e1 : ℚ) = target ∧
  (d3 * e1 : ℚ) / (d4 * e2 : ℚ) = target ∧
  (d5 * e0 : ℚ) / (d6 * e2 : ℚ) = target := by
    grind

/-
Definitions for the construction of a and r, and the target value V.
-/
def construct_a (data_p : List (ℕ × ℕ × ℕ)) (data_q : List (ℕ × ℕ × ℕ)) : ℕ :=
  4 * (data_p.map (fun (p, x, _) => p ^ x)).prod * (data_q.map (fun (q, u, _) => q ^ u)).prod

def construct_r (data_p : List (ℕ × ℕ × ℕ)) (data_q : List (ℕ × ℕ × ℕ)) : Fin 3 → ℕ :=
  ![1, (data_p.map (fun (p, _, y) => p ^ y)).prod, (data_q.map (fun (q, _, v) => q ^ v)).prod]

def target_val (data_p : List (ℕ × ℕ × ℕ)) (data_q : List (ℕ × ℕ × ℕ)) : ℚ :=
  4/3 * (data_p.map (fun (_, x, y) => f_rat x y)).prod * (data_q.map (fun (_, u, v) => 1 / f_rat u v)).prod

/-
G_gen is the set of values f(x,y) for x,y >= 1.
-/
def G_gen : Set ℚ := {q | ∃ x y : ℕ, x ≥ 1 ∧ y ≥ 1 ∧ q = f_rat x y}

/-
G is the subgroup of Q^x generated by the values in G_gen (viewed as units).
-/
def G_subgroup : Subgroup ℚˣ := Subgroup.closure { u : ℚˣ | (u : ℚ) ∈ G_gen }

/-
G is the subgroup of Q^x generated by the values in G_gen (viewed as units).
-/
def G_subgroup_def : Subgroup ℚˣ := Subgroup.closure { u : ℚˣ | (u : ℚ) ∈ G_gen }

/-
G contains every prime number p.
-/
lemma G_contains_primes : ∀ p (hp : Nat.Prime p), (Units.mk0 (p : ℚ) (by norm_cast; exact hp.ne_zero)) ∈ G_subgroup_def := by
  intro p hp
  have h_unit : (p : ℚ) ∈ G_gen := by
    rcases p with ( _ | _ | p ) <;> norm_num [ G_gen ] at *;
    use 2 * p + 3, by linarith, 2 * p + 2, by linarith;
    unfold f_rat; rw [ eq_div_iff ] <;> norm_cast ; linarith;
  generalize_proofs at *;
  exact Subgroup.subset_closure ( by aesop )

/-
G contains all positive integers.
Proof sketch:
1. Every positive integer n can be written as a product of primes.
2. G contains all primes (by G_contains_primes).
3. G is a subgroup, so it contains products of its elements.
4. Therefore G contains all positive integers.
-/
lemma G_contains_nat (n : ℕ) (hn : 0 < n) : Units.mk0 (n : ℚ) (by norm_cast; linarith) ∈ G_subgroup_def := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn_one : n = 1;
  · aesop;
  · -- Since n is not 1, it must � have� a prime factor p. By the induction hypothesis, the product of the other factors (which is less than n) is in G.
    obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ n := by
      exact Nat.exists_prime_and_dvd hn_one;
    -- Since p divides n, � we� can write n as p * m for some m. By the induction hypothesis, m is in G.
    obtain ⟨m, rfl⟩ : ∃ m, n = p * m := hp_div
    have hm : Units.mk0 (m : ℚ) (by norm_cast; exact Nat.ne_of_gt (Nat.pos_of_ne_zero (by
    grind))) ∈ G_subgroup_def := by
      exact ih m ( by nlinarith [ hp_prime.two_le ] ) ( Nat.pos_of_ne_zero ( by aesop ) )
    generalize_proofs at *;
    convert Subgroup.mul_mem _ ( G_contains_primes p hp_prime ) hm using 1 ; aesop

/-
G contains all positive rationals.
Proof sketch:
1. Every positive rational q can be written as a product of primes and their inverses.
2. G contains all primes (by G_contains_primes).
3. G is a subgroup, so it contains products and inverses of its elements.
4. Therefore G contains all positive rationals.
-/
lemma G_is_everything (q : ℚ) (hq : 0 < q) : Units.mk0 q (ne_of_gt hq) ∈ G_subgroup_def := by
  have := G_contains_nat q.num.natAbs ( Nat.pos_of_ne_zero ( by aesop ) );
  convert Subgroup.mul_mem _ this ( Subgroup.inv_mem _ ( G_contains_nat q.den ( Nat.pos_of_ne_zero ( by aesop ) ) ) ) using 1 ; norm_num [ abs_of_pos, hq ];
  simp +decide [Units.ext_iff];
  exact q.num_div_den.symm

/-
G contains all positive rationals.
Proof sketch:
1. Every positive rational q can be written as num/den.
2. num and den are positive integers, so they are in G (by G_contains_nat).
3. G is a subgroup, so it contains inverses. So 1/den is in G.
4. G is a subgroup, so it contains products. So num * (1/den) = q is in G.
-/
lemma G_is_everything_pos_rat (q : ℚ) (hq : 0 < q) : Units.mk0 q (ne_of_gt hq) ∈ G_subgroup_def := by
  exact G_is_everything q hq

/-
There exist 3 distinct primes coprime to n (for n != 0).
-/
lemma exists_three_primes (n : ℕ) (hn : n ≠ 0) : ∃ p : Fin 3 → ℕ, (∀ i, (p i).Prime) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ (∀ i, (p i).Coprime n) := by
  -- Since there are infinitely many primes, we can choose three distinct primes that are coprime to n.
  have h_inf_primes : Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Coprime p n} := by
    exact Nat.infinite_setOf_prime.diff ( Set.finite_le_nat n ) |> Set.Infinite.mono fun p hp => ⟨ hp.1, Nat.Prime.coprime_iff_not_dvd hp.1 |>.2 fun h => hp.2 <| Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) h ⟩;
  have := h_inf_primes.exists_subset_card_eq 3; rcases this with ⟨ s, hs ⟩ ; rcases Finset.card_eq_three.mp hs.2 with ⟨ p, q, r, hp, hq, hr ⟩ ; use fun i => if i = 0 then p else if i = 1 then q else r; simp_all +decide [ Fin.forall_fin_succ ] ;
  grind

/-
Every positive rational number `q` can be represented in the form `target_val data_p data_q` for some lists `data_p` and `data_q`.
-/
lemma exists_representation (q : ℚ) (hq : 0 < q) :
  ∃ data_p data_q : List (ℕ × ℕ × ℕ), q = target_val data_p data_q := by
    -- By Lemma 25, there exist lists `data_p` and `data_q` such that `q = target_val data_p data_q`.
    have h_exists_lists : ∃ data_p data_q : List (ℕ × ℕ × ℕ), q = (4 / 3 : ℚ) * (data_p.map (fun (p, x, y) => f_rat x y)).prod * (data_q.map (fun (q, u, v) => 1 / f_rat u v)).prod := by
      have h_existsLists : ∀ q : ℚ, 0 < q → ∃ data_p data_q : List ℚ, q = (4 / 3 : ℚ) * (data_p.prod) * (data_q.prod)⁻¹ ∧ (∀ x ∈ data_p, ∃ x' y' : ℕ, x' ≥ 1 ∧ y' ≥ 1 ∧ x = f_rat x' y') ∧ (∀ x ∈ data_q, ∃ u' v' : ℕ, u' ≥ 1 ∧ v' ≥ 1 ∧ x = f_rat u' v') := by
        intro q hq
        obtain ⟨data_p, data_q, h_prod⟩ : ∃ data_p data_q : List ℚ, q = (4 / 3 : ℚ) * (data_p.prod) * (data_q.prod)⁻¹ ∧ (∀ x ∈ data_p, x ∈ G_gen) ∧ (∀ x ∈ data_q, x ∈ G_gen) := by
          have h_prod : ∀ x ∈ G_subgroup_def, ∃ data_p data_q : List ℚ, (x : ℚ) = (data_p.prod) * (data_q.prod)⁻¹ ∧ (∀ y ∈ data_p, y ∈ G_gen) ∧ (∀ y ∈ data_q, y ∈ G_gen) := by
            intro x hx
            induction' hx using Subgroup.closure_induction with x hx ihx
            all_goals generalize_proofs at *;
            · exact ⟨ [ x ], [ ], by aesop ⟩;
            · exact ⟨ [ ], [ ], by norm_num, by norm_num, by norm_num ⟩;
            · rename_i hx hy ihx hyx; obtain ⟨ data_p, data_q, h₁, h₂, h₃ ⟩ := ihx; obtain ⟨ data_p', data_q', h₄, h₅, h₆ ⟩ := hyx; use data_p ++ data_p', data_q ++ data_q'; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
              exact ⟨ fun y hy => hy.elim ( fun hy => h₂ y hy ) fun hy => h₅ y hy, fun y hy => hy.elim ( fun hy => h₃ y hy ) fun hy => h₆ y hy ⟩
            · rename_i hx ih; obtain ⟨ data_p, data_q, h₁, h₂, h₃ ⟩ := ih; use data_q, data_p; aesop;
          field_simp;
          obtain ⟨ data_p, data_q, h₁, h₂, h₃ ⟩ := h_prod ( Units.mk0 ( q * 3 / 4 ) ( by positivity ) ) ( by simpa using G_is_everything_pos_rat ( q * 3 / 4 ) ( by positivity ) );
          exact ⟨ data_p, data_q, by norm_num [ Units.ext_iff ] at h₁; linear_combination h₁ * 4, h₂, h₃ ⟩;
        exact ⟨ data_p, data_q, h_prod.1, fun x hx => by obtain ⟨ x', y', hx', hy', rfl ⟩ := h_prod.2.1 x hx; exact ⟨ x', y', hx', hy', rfl ⟩, fun x hx => by obtain ⟨ x', y', hx', hy', rfl ⟩ := h_prod.2.2 x hx; exact ⟨ x', y', hx', hy', rfl ⟩ ⟩;
      obtain ⟨ data_p, data_q, h₁, h₂, h₃ ⟩ := h_existsLists q hq;
      -- Convert the lists `data_p` and `data_q` to lists of triples `(p, x, y)` and `(q, u, v)` respectively.
      obtain ⟨data_p_triples, hdata_p_triples⟩ : ∃ data_p_triples : List (ℕ × ℕ × ℕ), data_p = List.map (fun (p, x, y) => f_rat x y) data_p_triples := by
        choose! x' y' hx' hy' hxy' using h₂;
        use List.map (fun x => (0, x' x, y' x)) data_p;
        exact List.ext_get ( by simp +decide ) ( by simp +contextual [ ← hxy' ] )
      obtain ⟨data_q_triples, hdata_q_triples⟩ : ∃ data_q_triples : List (ℕ × ℕ × ℕ), data_q = List.map (fun (q, u, v) => f_rat u v) data_q_triples := by
        have hdata_q_triples : ∀ x ∈ data_q, ∃ u' v' : ℕ, u' ≥ 1 ∧ v' ≥ 1 ∧ x = f_rat u' v' := by
          assumption;
        choose! u' v' hu' hv' hx using hdata_q_triples;
        use data_q.map (fun x => (0, u' x, v' x));
        exact List.ext_get ( by simp +decide ) ( by simp +decide [ ← hx ] );
      use data_p_triples, data_q_triples; simp_all +decide ;
      exact Or.inl ( by rw [ List.prod_inv ] ; exact congr_arg _ ( List.ext_get ( by aesop ) ( by aesop ) ) );
    exact h_exists_lists

/-
For any positive rational `q`, there exist lists `data_p` and `data_q` representing `q` such that the associated primes are distinct odd primes.
-/
lemma exists_representation_odd_primes (q : ℚ) (hq : 0 < q) :
  ∃ data_p data_q : List (ℕ × ℕ × ℕ),
    q = target_val data_p data_q ∧
    (∀ i, Odd (construct_r data_p data_q i)) ∧
    (∀ p, p ∈ (data_p.map (fun (x : ℕ × ℕ × ℕ) => x.1)) ++ (data_q.map (fun (x : ℕ × ℕ × ℕ) => x.1)) → p.Prime) ∧
    (data_p.map (fun (x : ℕ × ℕ × ℕ) => x.1) ++ data_q.map (fun (x : ℕ × ℕ × ℕ) => x.1)).Pairwise (· ≠ ·) := by
      obtain ⟨ data_p, data_q, h ⟩ := exists_representation q hq;
      -- Choose `n_p + n_q` distinct odd primes. For example, the first `n_p + n_q` primes starting from 3.
      obtain ⟨ps, hps⟩ : ∃ ps : List ℕ, ps.length = data_p.length + data_q.length ∧ (∀ p ∈ ps, Nat.Prime p ∧ p > 2) ∧ List.Pairwise (fun x1 x2 => x1 ≠ x2) ps := by
        exact ⟨ List.map ( fun i => Nat.nth Nat.Prime ( i + 2 ) ) ( List.range ( List.length data_p + List.length data_q ) ), by simp +decide, fun p hp => by
          have := List.mem_map.mp hp; obtain ⟨ i, hi, rfl ⟩ := this; exact ⟨ Nat.prime_nth_prime _, Nat.lt_of_le_of_lt ( Nat.Prime.two_le <| Nat.prime_nth_prime _ ) <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| Nat.lt_succ_self _ ⟩ ;, by
          norm_num [ List.pairwise_iff_get ];
          exact fun i j hij => fun h => hij.ne <| Fin.ext <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; aesop; ⟩;
      refine' ⟨ List.zipWith ( fun p x => ( p, x.2.1, x.2.2 ) ) ( List.take data_p.length ps ) data_p, List.zipWith ( fun p x => ( p, x.2.1, x.2.2 ) ) ( List.drop data_p.length ps ) data_q, _, _, _, _ ⟩ <;> simp_all +decide [ List.pairwise_append ];
      · unfold target_val;
        congr! 2;
        · refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
        · refine' List.ext_get _ _ <;> aesop;
      · unfold construct_r; simp +decide [ Fin.forall_fin_succ ] ;
        -- Since the primes in `ps` are all odd, their powers are also odd.
        have h_odd_primes : ∀ p ∈ ps, Odd p := by
          exact fun p hp => Nat.Prime.odd_of_ne_two ( hps.2.1 p hp |>.1 ) ( ne_of_gt ( hps.2.1 p hp |>.2 ) );
        have h_odd_powers : ∀ {l : List ℕ}, (∀ p ∈ l, Odd p) → Odd (List.prod l) := by
          intro l hl; induction l <;> simp_all +decide [Nat.odd_iff] ;
        refine' ⟨ h_odd_powers _, h_odd_powers _ ⟩;
        · intro p hp; rw [ List.mem_iff_get ] at hp; obtain ⟨ i, hi ⟩ := hp; simp_all +decide ;
          exact hi ▸ Odd.pow ( h_odd_primes _ ( by simp ) );
        · intro p hp; rw [ List.mem_iff_get ] at hp; obtain ⟨ i, hi ⟩ := hp; simp_all +decide ;
          exact hi ▸ Odd.pow ( h_odd_primes _ ( by simp ) );
      · intro p hp; rcases hp with ( hp | hp ) <;> rw [ List.mem_iff_get ] at hp <;> aesop;
      · simp_all +decide [ List.pairwise_iff_get ];
        refine' ⟨ _, _, _ ⟩;
        · intro i j hij; specialize hps; have := hps.2.2 ⟨ i, by
            exact lt_of_lt_of_le i.2 ( by simp +decide [ hps.1 ] ) ⟩ ⟨ j, by
            exact lt_of_lt_of_le j.2 ( by simp [ hps.1 ] ) ⟩ hij; aesop;
        · intro i j hij; convert hps.2.2 ⟨ data_p.length + i, by
            linarith [ Fin.is_lt i, Fin.is_lt j, show ( i : ℕ ) < List.length data_q from by simpa [ hps.1 ] using i.2, show ( j : ℕ ) < List.length data_q from by simpa [ hps.1 ] using j.2 ] ⟩ ⟨ data_p.length + j, by
            grind ⟩ ( by simpa [ Fin.ext_iff ] using hij ) using 1;
        · intro a ha b hb; rw [ List.mem_iff_get ] at ha hb; obtain ⟨ i, hi ⟩ := ha; obtain ⟨ j, hj ⟩ := hb; simp_all +decide ;
          refine' hi ▸ hj ▸ hps.2.2 ⟨ i, by
            exact lt_of_lt_of_le i.2 ( by simp +decide [ hps.1 ] ) ⟩ ⟨ data_p.length + j, by
            grind ⟩ ( by
            exact Nat.lt_of_lt_of_le i.2 ( by simp ) )

/-
The constructed values `a` and `r` satisfy `a > 0`, `a` is even, and `r i > 0`.
-/
lemma construct_basic_properties (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p) :
  let a := construct_a data_p data_q
  let r := construct_r data_p data_q
  0 < a ∧ Even a ∧ (∀ i, 0 < r i) := by
    unfold construct_a construct_r; simp_all +decide [ Fin.forall_fin_succ ] ;
    exact ⟨ ⟨ fun x y z t h1 h2 => by subst h2; exact pow_pos ( Nat.Prime.pos ( hp_prime _ <| Or.inl ⟨ _, _, h1 ⟩ ) ) _, fun x y z t h1 h2 => by subst h2; exact pow_pos ( Nat.Prime.pos ( hp_prime _ <| Or.inr ⟨ _, _, h1 ⟩ ) ) _ ⟩, by simp +decide [ Nat.even_mul ], fun x y z t h1 h2 => by subst h2; exact pow_pos ( Nat.Prime.pos ( hp_prime _ <| Or.inl ⟨ _, _, h1 ⟩ ) ) _, fun x y z t h1 h2 => by subst h2; exact pow_pos ( Nat.Prime.pos ( hp_prime _ <| Or.inr ⟨ _, _, h1 ⟩ ) ) _ ⟩

/-
The function `f_rat` is symmetric in its arguments.
-/
lemma f_rat_symm (x y : ℕ) : f_rat x y = f_rat y x := by
  unfold f_rat; ring;

/-
Helper definitions for components of `a` and `r`.
-/
def P_val (data_p : List (ℕ × ℕ × ℕ)) : ℕ := (data_p.map (fun (p, x, _) => p ^ x)).prod
def Q_val (data_q : List (ℕ × ℕ × ℕ)) : ℕ := (data_q.map (fun (q, u, _) => q ^ u)).prod
def R1_val (data_p : List (ℕ × ℕ × ℕ)) : ℕ := (data_p.map (fun (p, _, y) => p ^ y)).prod
def R2_val (data_q : List (ℕ × ℕ × ℕ)) : ℕ := (data_q.map (fun (q, _, v) => q ^ v)).prod

/-
There exists a representation of `q` where all exponents `x, y` (and `u, v`) are positive.
-/
lemma exists_representation_clean (q : ℚ) (hq : 0 < q) :
  ∃ data_p data_q : List (ℕ × ℕ × ℕ),
    q = target_val data_p data_q ∧
    (∀ i, Odd (construct_r data_p data_q i)) ∧
    (∀ p, p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)) → p.Prime) ∧
    (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·) ∧
    (∀ t ∈ data_p, 0 < t.2.1 ∧ 0 < t.2.2) ∧
    (∀ t ∈ data_q, 0 < t.2.1 ∧ 0 < t.2.2) := by
      -- By cleaning the lists data_p and data_q, we ensure that all exponents are positive.
      obtain ⟨data_p, data_q, hq_eq, hr_odd, hp_prime, hp_distinct⟩ := exists_representation_odd_primes q hq;
      use data_p.filter (fun t => 0 < t.2.1 ∧ 0 < t.2.2), data_q.filter (fun t => 0 < t.2.1 ∧ 0 < t.2.2);
      unfold target_val construct_r at *; simp_all +decide ;
      refine' ⟨ _, _, _, _ ⟩;
      · -- By definition of `f_rat`, we know that `f_rat x y = 1` if `x = 0` or `y = 0`.
        have h_f_rat_zero : ∀ x y : ℕ, x = 0 ∨ y = 0 → f_rat x y = 1 := by
          rintro x y ( rfl | rfl ) <;> unfold f_rat <;> norm_num
          · exact show ((y : ℚ) + 1) ≠ 0 from by positivity
          · exact show ((x : ℚ) + 1) ≠ 0 from by positivity
        have h_filter : ∀ (l : List (ℕ × ℕ × ℕ)), (List.map (fun x => f_rat x.2.1 x.2.2) l).prod = (List.map (fun x => f_rat x.2.1 x.2.2) (List.filter (fun t => 0 < t.2.1 ∧ 0 < t.2.2) l)).prod := by
          intro l; induction l <;> simp_all +decide [ List.filter_cons ] ;
          by_cases h : 0 < ‹ℕ × ℕ × ℕ›.2.1 <;> aesop;
        have h_filter_inv : ∀ (l : List (ℕ × ℕ × ℕ)), (List.map (fun x => (f_rat x.2.1 x.2.2)⁻¹) l).prod = (List.map (fun x => (f_rat x.2.1 x.2.2)⁻¹) (List.filter (fun t => 0 < t.2.1 ∧ 0 < t.2.2) l)).prod := by
          intro l; induction l <;> simp +decide [ * ] ;
          by_cases h : 0 < ‹ℕ × ℕ × ℕ›.2.1 <;> by_cases h' : 0 < ‹ℕ × ℕ × ℕ›.2.2 <;> simp +decide [ h, h' ];
          · grind;
          · specialize h_f_rat_zero 0 ‹ℕ × ℕ × ℕ›.2.2 ; aesop;
          · rw [ h_f_rat_zero _ _ ( Or.inl ( by linarith ) ), inv_one, one_mul ];
        simp +zetaDelta at *;
        rw [ h_filter, h_filter_inv ];
      · simp_all +decide [Fin.forall_fin_succ];
        have h_filter_odd : ∀ {l : List (ℕ × ℕ × ℕ)}, (∀ p ∈ l, Nat.Prime p.1) → Odd (List.prod (List.map (fun x => x.1 ^ x.2.2) l)) → Odd (List.prod (List.map (fun x => x.1 ^ x.2.2) (List.filter (fun t => decide (0 < t.2.1) && decide (0 < t.2.2)) l))) := by
          intros l hl_prime hl_odd; induction l <;> simp_all +decide [Nat.odd_iff, Nat.mul_mod,
            Nat.pow_mod] ;
          cases Nat.Prime.eq_two_or_odd hl_prime.1 <;> simp_all +decide [ Nat.pow_mod ];
          · cases h : ‹ℕ × ℕ × ℕ›.2.2 <;> simp_all +decide;
          · by_cases h : 0 < ( ‹ℕ × ℕ × ℕ›.2.1 ) <;> by_cases h' : 0 < ( ‹ℕ × ℕ × ℕ›.2.2 ) <;> simp_all +decide [ Nat.pow_mod, Nat.mul_mod ];
        grind;
      · grind;
      · simp_all +decide [ List.pairwise_append, List.pairwise_map ];
        exact ⟨ List.Pairwise.filter _ hp_distinct.1, List.Pairwise.filter _ hp_distinct.2.1, fun a x x_1 hx hx' hx'' b y y_1 hy hy' hy'' => hp_distinct.2.2 a x x_1 hx b y y_1 hy ⟩

/-
The number 2 is in the subgroup G.
-/
lemma two_in_G : Units.mk0 (2 : ℚ) (by norm_num) ∈ G_subgroup_def := by
  -- By definition of $G$, we know that $2 \in G$.
  apply G_contains_nat; norm_num

/-
The divisor function of the product of P and R1 is the product of (x+y+1).
-/
lemma tau_P_mul_R1 (data_p : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_p.map (·.1), Nat.Prime p)
  (hd : (data_p.map (·.1)).Pairwise (· ≠ ·)) :
  tau (P_val data_p * R1_val data_p) = (data_p.map (fun (_, x, y) => x + y + 1)).prod := by
    -- By definition of `tau`, we know that `tau(n)` is the number of divisors of `n`. Since `P_val data_p * R1_val data_p` is a product of powers of distinct primes, its number of divisors is the product of the number of divisors of each prime power.
    have h_divisors : tau ((List.map (fun (d : ℕ × ℕ × ℕ) => d.1 ^ (d.2.1 + d.2.2)) data_p).prod) = (List.map (fun d => d.2.1 + d.2.2 + 1) data_p).prod := by
      induction data_p <;> simp_all +decide [ List.prod_cons, List.map ];
      -- Apply the multiplicativity of the divisor function.
      have h_mult : ∀ {a b : ℕ}, Nat.Coprime a b → (Nat.divisors (a * b)).card = (Nat.divisors a).card * (Nat.divisors b).card := by
        exact fun {a b} a_1 ↦ Nat.Coprime.card_divisors_mul a_1;
      -- Apply the multiplicativity of the divisor function to the product of prime powers.
      have h_prod : ∀ {l : List (ℕ × ℕ × ℕ)}, (∀ d ∈ l, Nat.Prime d.1) → (List.Pairwise (fun x1 x2 => ¬x1.1 = x2.1) l) → (Nat.divisors ((List.map (fun d => d.1 ^ (d.2.1 + d.2.2)) l).prod)).card = (List.map (fun d => d.2.1 + d.2.2 + 1) l).prod := by
        intros l hl_prime hl_pairwise; induction l <;> simp_all +decide [ List.prod_cons, List.map ] ;
        rw [ h_mult ];
        · simp_all +decide [ Nat.divisors_prime_pow ];
          induction ‹List ( ℕ × ℕ × ℕ ) › <;> simp_all +decide [ List.prod_cons, List.map ];
          rw [ h_mult ];
          · rw [ Nat.divisors_prime_pow ( hl_prime.2 _ _ _ ( Or.inl rfl ) ) ] ; aesop;
          · have h_coprime : ∀ {l : List (ℕ × ℕ × ℕ)}, (∀ d ∈ l, Nat.Prime d.1) → (List.Pairwise (fun x1 x2 => ¬x1.1 = x2.1) l) → ∀ {p : ℕ}, Nat.Prime p → (∀ d ∈ l, d.1 ≠ p) → Nat.Coprime (p ^ (‹ℕ × ℕ × ℕ›.2.1 + ‹ℕ × ℕ × ℕ›.2.2)) (List.prod (List.map (fun d => d.1 ^ (d.2.1 + d.2.2)) l)) := by
              intros l hl_prime hl_pairwise p hp hne; induction l <;> simp_all +decide [Nat.coprime_mul_iff_right] ;
              exact ⟨ Nat.Coprime.pow _ _ <| hp.coprime_iff_not_dvd.mpr fun h => hne.1 <| by have := Nat.prime_dvd_prime_iff_eq hp hl_prime.1; tauto, by assumption ⟩;
            exact h_coprime ( fun d hd => hl_prime.2 _ _ _ <| Or.inr hd ) hl_pairwise.2.2 ( hl_prime.2 _ _ _ <| Or.inl rfl ) fun d hd => by aesop;
        · induction ‹List ( ℕ × ℕ × ℕ ) › <;> simp_all +decide [Nat.coprime_mul_iff_right];
          rename_i k hk ih;
          exact ⟨ Nat.coprime_pow_primes _ _ hl_prime.1 ( hl_prime.2 _ _ _ ( Or.inl rfl ) ) ( by aesop ), ih ( fun a a_1 b hab => hl_prime.2 _ _ _ ( Or.inr hab ) ) ( fun a a_1 b hab => hl_pairwise.1 _ _ _ ( Or.inr hab ) ) ⟩;
      convert h_prod _ _ using 1;
      any_goals exact List.cons ‹_› ‹_›;
      · unfold tau; aesop;
      · simp +decide;
      · aesop;
      · simp_all +decide [ List.pairwise_cons ];
        exact ⟨ hd.1, by simpa [ List.pairwise_map ] using hd.2 ⟩;
    convert h_divisors using 3;
    unfold P_val R1_val; simp +decide [pow_add, List.prod_map_mul] ;

/-
The divisor function of P is the product of (x+1).
-/
lemma tau_P (data_p : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_p.map (·.1), Nat.Prime p)
  (hd : (data_p.map (·.1)).Pairwise (· ≠ ·)) :
  tau (P_val data_p) = (data_p.map (fun (_, x, _) => x + 1)).prod := by
    induction' data_p using List.reverseRecOn with data_p ih;
    · rfl;
    · -- Since $P_val$ and $ih.1 ^ ih.2.1$ are coprime, we can apply the multiplicativity of the divisor function.
      have h_coprime : Nat.gcd (P_val data_p) (ih.1 ^ ih.2.1) = 1 := by
        -- Since the primes in data_p are distinct and ih.1 is a prime not in data_p, their product P_val is coprime with ih.1^ih.2.1.
        have h_coprime : ∀ p ∈ data_p.map (fun x => x.1), Nat.gcd p ih.1 = 1 := by
          simp_all +decide [ List.pairwise_append ];
          exact fun p x y h => by have := Nat.coprime_primes ( hp p ( Or.inl ⟨ x, y, h ⟩ ) ) ( hp ih.1 ( Or.inr rfl ) ) ; aesop;
        have h_coprime : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.gcd p ih.1 = 1) → Nat.gcd (List.prod l) (ih.1 ^ ih.2.1) = 1 := by
          intros l hl; induction l <;> simp_all +decide [Nat.coprime_mul_iff_left] ;
          exact ⟨ Nat.Coprime.pow_right _ hl.1, by assumption ⟩;
        convert h_coprime _;
        simp +zetaDelta at *;
        exact fun p x y z h1 h2 => h2 ▸ Nat.Coprime.pow_left _ ( h_coprime _ _ _ h1 );
      -- Apply the multiplicativity of the divisor function.
      have h_divisors_mul : ∀ {m n : ℕ}, Nat.gcd m n = 1 → (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
        exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
      convert h_divisors_mul h_coprime using 1;
      · unfold P_val; aesop;
      · simp_all +decide [ Nat.divisors_prime_pow ];
        exact Eq.symm ( by rename_i h; exact h <| List.pairwise_append.mp hd |>.1 )

/-
The divisor function of R1 is the product of (y+1).
-/
lemma tau_R1 (data_p : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_p.map (·.1), Nat.Prime p)
  (hd : (data_p.map (·.1)).Pairwise (· ≠ ·)) :
  tau (R1_val data_p) = (data_p.map (fun (_, _, y) => y + 1)).prod := by
    convert tau_P _ _ using 1;
    rotate_left;
    exact data_p.map fun x => ( x.1, x.2.2, x.2.1 );
    · aesop;
    · unfold P_val R1_val; aesop;

/-
If a prime p divides R2, it divides a.
-/
lemma prime_dvd_R2_imp_dvd_a (data_p data_q : List (ℕ × ℕ × ℕ))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2)
  (p : ℕ) (hp : Nat.Prime p) (h : p ∣ R2_val data_q) :
  p ∣ construct_a data_p data_q := by
    -- Since $p$ divides some $q_i$, and $q_i$ is a prime factor of $R2_val data_q$, it follows that $p$ divides $Q_val data_q$.
    have h_div_Q : p ∣ Q_val data_q := by
      -- Since $p$ divides $R2_val data_q$, and $R2_val data_q$ is the product of $q^v$ for each $(q, u, v)$ in $data_q$, it follows that $p$ divides some $q^v$.
      obtain ⟨q, v, hq, hv⟩ : ∃ q v, (q, v) ∈ data_q.map (fun (q, u, v) => (q, v)) ∧ p ∣ q ^ v := by
        haveI := Fact.mk hp; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
        unfold R2_val at h; simp_all +decide [ZMod.natCast_eq_zero_iff] ;
        grind;
      obtain ⟨t, ht⟩ : ∃ t ∈ data_q, t.1 = q ∧ t.2.2 = v := by
        rw [ List.mem_map ] at hq; obtain ⟨ t, ht, rfl, rfl ⟩ := hq; exact ⟨ t, ht, rfl, rfl ⟩ ;
      have h_div_q : p ∣ t.1 ^ t.2.1 := by
        exact dvd_pow ( by simpa [ ht.2 ] using hp.dvd_of_dvd_pow hv ) ( by linarith [ h_pos t ( List.mem_append_right _ ht.1 ) ] );
      exact dvd_trans h_div_q ( by exact List.dvd_prod ( List.mem_map.mpr ⟨ t, ht.1, by aesop ⟩ ) );
    exact dvd_trans h_div_Q ( by exact dvd_mul_of_dvd_right ( by aesop ) _ )

/-
a+1 and R2 are coprime.
-/
lemma coprime_a_plus_one_R2 (data_p data_q : List (ℕ × ℕ × ℕ))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r2 := R2_val data_q
  (a + 1).Coprime r2 := by
    refine' Nat.coprime_of_dvd' _;
    intros k hk hk_div_a hk_div_r2
    have hk_div_a_plus_one : k ∣ construct_a data_p data_q + 1 := hk_div_a
    have hk_div_a : k ∣ construct_a data_p data_q := by
      apply prime_dvd_R2_imp_dvd_a data_p data_q h_pos k hk hk_div_r2;
    simpa using Nat.dvd_sub hk_div_a_plus_one hk_div_a

/-
If a prime p divides R1, it divides a.
-/
lemma prime_dvd_R1_imp_dvd_a (data_p data_q : List (ℕ × ℕ × ℕ))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2)
  (p : ℕ) (hp : Nat.Prime p) (h : p ∣ R1_val data_p) :
  p ∣ construct_a data_p data_q := by
    -- Since p divides R1_val, and R1_val is a product of primes raised to some powers, p must be one of those primes. Therefore, p divides P_val.
    have h_div_P : p ∣ P_val data_p := by
      unfold P_val R1_val at *;
      haveI := Fact.mk hp; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
      grind;
    exact dvd_trans h_div_P ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( by aesop ) _ ) _ )

/-
a+2 and R1 are coprime.
-/
lemma coprime_a_plus_two_R1 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  (a + 2).Coprime r1 := by
    refine' Nat.coprime_of_dvd' _;
    -- If a prime p divides R1, it must divide a (by prime_dvd_R1_imp_dvd_a). But p also divides a+2, so p divides (a+2) - a = 2. Since p is odd, this is impossible. Therefore, p can't divide both a+2 and R1, so their gcd must be 1.
    intros p hp_prime hp_div_a2 hp_div_r1
    have hp_div_2 : p ∣ 2 := by
      have hp_div_a : p ∣ construct_a data_p data_q := by
        apply prime_dvd_R1_imp_dvd_a data_p data_q h_pos p hp_prime hp_div_r1;
      simpa using Nat.dvd_sub hp_div_a2 hp_div_a;
    have := Nat.le_of_dvd ( by decide ) hp_div_2; interval_cases p <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
    unfold R1_val at hp_div_r1; simp_all +decide [Nat.even_iff] ;
    -- Since all primes in data_p are odd, each term in the product is odd. The product of odd numbers is odd.
    have h_odd_prod : ∀ x ∈ List.map (fun x => x.1 ^ x.2.2) data_p, Odd x := by
      simp +zetaDelta at *;
      exact fun x y z t h1 h2 => h2 ▸ Odd.pow ( hp_odd _ ( Or.inl ⟨ _, _, h1 ⟩ ) );
    have h_odd_prod : ∀ {l : List ℕ}, (∀ x ∈ l, Odd x) → Odd (List.prod l) := by
      intros l hl; induction l <;> simp_all +decide [Nat.odd_iff] ;
    exact absurd ( h_odd_prod ‹_› ) ( by simp +decide [ Nat.even_iff, hp_div_r1 ] )

/-
a/2+1 and R1 are coprime.
-/
lemma coprime_a_div_two_plus_one_R1 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  (a / 2 + 1).Coprime r1 := by
    refine' Nat.Coprime.symm <| Nat.coprime_of_dvd' _;
    intro k hk hk' hk''; have := Nat.dvd_sub hk'' ( Nat.dvd_div_of_mul_dvd ( show 2 * k ∣ construct_a data_p data_q from ?_ ) ) ; simp_all +decide ;
    refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
    · -- Since $k$ divides $R1_val$, and $R1_val$ is a product of primes from $data_p$, each of which is odd by $hp_odd$, $k$ must be one of those primes.
      have hk_prime : ∃ p ∈ data_p.map (fun x => x.1), k ∣ p := by
        have hk_prime : k ∣ (data_p.map (fun (p, _, y) => p ^ y)).prod := by
          exact hk';
        haveI := Fact.mk hk; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
        grind +ring;
      obtain ⟨ p, hp₁, hp₂ ⟩ := hk_prime; have := Nat.prime_dvd_prime_iff_eq hk ( hp_prime p ( by aesop ) ) ; aesop;
    · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _;
    · convert prime_dvd_R1_imp_dvd_a data_p data_q h_pos k hk hk' using 1

/-
Q_val is odd.
-/
lemma odd_Q_val (data_q : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ data_q.map (fun x => x.1), Odd p) :
  Odd (Q_val data_q) := by
    induction data_q <;> simp_all +decide [ parity_simps ];
    exact Odd.mul ( hp_odd.1.pow ) ‹_›

/-
Q is coprime to P*R1.
-/
lemma coprime_Q_P_mul_R1 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  (Q_val data_q).Coprime (P_val data_p * R1_val data_p) := by
    have h_coprime : ∀ p ∈ data_q.map (fun x => x.1), ∀ q ∈ data_p.map (fun x => x.1) ++ data_p.map (fun x => x.1), p ≠ q := by
      grind;
    have h_coprime : ∀ p ∈ data_q.map (fun x => x.1), Nat.Coprime p (P_val data_p * R1_val data_p) := by
      intros p hp
      have h_coprime_p : ∀ q ∈ data_p.map (fun x => x.1) ++ data_p.map (fun x => x.1), p ≠ q := by
        exact h_coprime p hp;
      have h_coprime_p : ∀ q ∈ data_p.map (fun x => x.1) ++ data_p.map (fun x => x.1), Nat.Coprime p q := by
        intros q hq; exact Nat.Coprime.symm ( hp_prime q ( by aesop ) |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| fun h => h_coprime_p q hq <| by have := Nat.prime_dvd_prime_iff_eq ( hp_prime q ( by aesop ) ) ( hp_prime p ( by aesop ) ) ; tauto ) ;
      have h_coprime_p : Nat.Coprime p (List.prod (List.map (fun (p, x, y) => p ^ x) data_p)) ∧ Nat.Coprime p (List.prod (List.map (fun (p, x, y) => p ^ y) data_p)) := by
        have h_coprime_p : ∀ {l : List ℕ}, (∀ q ∈ l, Nat.Coprime p q) → Nat.Coprime p (List.prod l) := by
          intros l hl; induction l <;> simp_all +decide [Nat.coprime_mul_iff_right] ;
          grind;
        exact ⟨ h_coprime_p fun q hq => by rcases List.mem_map.mp hq with ⟨ x, hx, rfl ⟩ ; exact Nat.Coprime.pow_right _ <| by aesop, h_coprime_p fun q hq => by rcases List.mem_map.mp hq with ⟨ x, hx, rfl ⟩ ; exact Nat.Coprime.pow_right _ <| by aesop ⟩;
      exact Nat.Coprime.mul_right h_coprime_p.1 h_coprime_p.2;
    have h_coprime_prod : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.Coprime p (P_val data_p * R1_val data_p)) → Nat.Coprime (List.prod l) (P_val data_p * R1_val data_p) := by
      exact fun {l} a ↦ (fun {l} {k} ↦ Nat.coprime_list_prod_left_iff.mpr) a;
    convert h_coprime_prod fun p hp => ?_;
    rw [ List.mem_map ] at hp; obtain ⟨ q, hq, rfl ⟩ := hp; exact Nat.Coprime.pow_left _ ( h_coprime _ <| by aesop ) ;

/-
P is coprime to Q*R2.
-/
lemma coprime_P_Q_mul_R2 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  (P_val data_p).Coprime (Q_val data_q * R2_val data_q) := by
    -- Since `data_p` and `data_q` have distinct primes, `P_val` and `Q_val * R2_val` are coprime.
    have h_coprime : ∀ (p : ℕ), Nat.Prime p → p ∣ P_val data_p → ¬(p ∣ Q_val data_q * R2_val data_q) := by
      intros p hp hp_div_P hp_div_QR2
      have hp_in_data_p : p ∈ List.map (fun x => x.1) data_p := by
        have hp_in_data_p : p ∣ (data_p.map (fun (p, x, _) => p ^ x)).prod := by
          exact hp_div_P;
        haveI := Fact.mk hp; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
        obtain ⟨ a, b, ⟨ x, hx ⟩, ha, hb ⟩ := hp_in_data_p; rw [ ZMod.natCast_eq_zero_iff ] at ha; rw [ Nat.prime_dvd_prime_iff_eq ] at ha <;> aesop;
      have hp_not_in_data_q : p ∉ List.map (fun x => x.1) data_q := by
        grind +ring
      have hp_not_div_QR2 : ¬(p ∣ Q_val data_q) := by
        have hp_not_div_QR2 : ∀ q ∈ List.map (fun x => x.1) data_q, ¬(p ∣ q) := by
          intro q hq hq_div_p; have := List.pairwise_append.mp hp_distinct; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
        haveI := Fact.mk hp; simp_all +decide [← ZMod.natCast_eq_zero_iff] ;
        unfold Q_val; simp_all +decide ;
        exact fun x y z h₁ h₂ => False.elim <| hp_not_div_QR2 x y z h₁ h₂
      have hp_not_div_QR2' : ¬(p ∣ R2_val data_q) := by
        have hp_not_div_R2 : ∀ q ∈ data_q.map (fun x => x.1), ¬(p ∣ q) := by
          intro q hq hq_div_p; have := Nat.prime_dvd_prime_iff_eq hp ( hp_prime q ( List.mem_append_right _ hq ) ) ; aesop;
        simp_all +decide [ R2_val, Nat.Prime.dvd_iff_not_coprime hp ];
        have hp_not_div_R2 : ∀ {l : List ℕ}, (∀ q ∈ l, Nat.gcd p q = 1) → Nat.gcd p (List.prod l) = 1 := by
          intros l hl; induction l <;> simp_all +decide [Nat.coprime_mul_iff_right] ;
          tauto;
        exact hp_not_div_R2 fun q hq => by obtain ⟨ x, hx, rfl ⟩ := List.mem_map.mp hq; exact Nat.Coprime.pow_right _ ( by aesop ) ;
      have hp_not_div_QR2'' : ¬(p ∣ Q_val data_q * R2_val data_q) := by
        exact Nat.Prime.not_dvd_mul hp hp_not_div_QR2 hp_not_div_QR2'
      exact hp_not_div_QR2'' hp_div_QR2;
    exact Nat.coprime_of_dvd <| by tauto;

/-
P*R1 is odd.
-/
lemma odd_P_mul_R1 (data_p : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ data_p.map (fun x => x.1), Odd p) :
  Odd (P_val data_p * R1_val data_p) := by
    unfold P_val R1_val; induction data_p <;> simp_all +decide [ parity_simps ] ;
    grind

/-
tau(a * R1) = 3 * tau(Q) * tau(P * R1).
-/
lemma tau_a_mul_R1 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  tau (a * r1) = 3 * tau (Q_val data_q) * tau (P_val data_p * r1) := by
    -- We show pairwise coprimality of `4`, `Q_val`, and `P_val * r1`.
    have h_coprime : Nat.Coprime 4 (Q_val data_q) ∧ Nat.Coprime 4 (P_val data_p * R1_val data_p) ∧ Nat.Coprime (Q_val data_q) (P_val data_p * R1_val data_p) := by
      have h_coprime : Nat.Coprime 4 (Q_val data_q) ∧ Nat.Coprime 4 (P_val data_p * R1_val data_p) := by
        have h_coprime : Odd (Q_val data_q) ∧ Odd (P_val data_p * R1_val data_p) := by
          exact ⟨ odd_Q_val data_q fun p hp => hp_odd p <| List.mem_append_right _ hp, odd_P_mul_R1 data_p fun p hp => hp_odd p <| List.mem_append_left _ hp ⟩;
        exact ⟨ Nat.Coprime.pow_left 2 ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using h_coprime.1 ), Nat.Coprime.pow_left 2 ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using h_coprime.2 ) ⟩
      exact ⟨h_coprime.left, h_coprime.right, by
        apply coprime_Q_P_mul_R1;
        · assumption;
        · assumption⟩;
    -- By multiplicativity of `tau`:
    have h_tau_mul : ∀ {m n : ℕ}, Nat.Coprime m n → tau (m * n) = tau m * tau n := by
      unfold tau;
      exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
    convert h_tau_mul ( show Nat.Coprime ( 4 * Q_val data_q ) ( P_val data_p * R1_val data_p ) from ?_ ) using 1;
    · unfold construct_a P_val R1_val Q_val; ring_nf;
    · rw [ h_tau_mul h_coprime.1 ];
      rfl;
    · exact Nat.Coprime.mul_left h_coprime.2.1 h_coprime.2.2

/-
P_val is odd.
-/
lemma odd_P_val (data_p : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ data_p.map (fun x => x.1), Odd p) :
  Odd (P_val data_p) := by
    induction data_p <;> simp_all +decide [Nat.odd_iff];
    unfold P_val; simp +decide [ *, Nat.mul_mod ] ;
    norm_num [ Nat.pow_mod, hp_odd.1 ] ; aesop;

/-
R2_val is odd.
-/
lemma odd_R2_val (data_q : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ data_q.map (fun x => x.1), Odd p) :
  Odd (R2_val data_q) := by
    induction data_q <;> simp_all +decide;
    exact Odd.mul ( hp_odd.1.pow ) ‹_›

/-
tau(a * R1) = 3 * tau(Q) * tau(P * R1).
-/
lemma tau_a_mul_R1_eq (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  tau (a * r1) = 3 * tau (Q_val data_q) * tau (P_val data_p * r1) := by
    convert tau_a_mul_R1 data_p data_q hp_prime hp_odd hp_distinct using 1

/-
tau(a/2 * R2) = 2 * tau(P) * tau(Q * R2).
-/
lemma tau_a_div_two_mul_R2 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  let a := construct_a data_p data_q
  let r2 := R2_val data_q
  tau (a / 2 * r2) = 2 * tau (P_val data_p) * tau (Q_val data_q * r2) := by
    -- By multiplicativity of tau, we can split the product into three parts: tau(2), tau(P_val), and tau(Q_val * r2).
    have h_mul : let a := construct_a data_p data_q; let r2 := R2_val data_q; tau (2 * P_val data_p * (Q_val data_q * r2)) = tau 2 * tau (P_val data_p) * tau (Q_val data_q * r2) := by
      have h_coprime : Nat.Coprime 2 (P_val data_p) ∧ Nat.Coprime 2 (Q_val data_q * R2_val data_q) ∧ Nat.Coprime (P_val data_p) (Q_val data_q * R2_val data_q) := by
        refine' ⟨ Nat.prime_two.coprime_iff_not_dvd.mpr _, Nat.prime_two.coprime_iff_not_dvd.mpr _, _ ⟩;
        · have h_odd_P_val : Odd (P_val data_p) := by
            apply odd_P_val; intro p hp; specialize hp_odd p; aesop;
          simpa [ ← even_iff_two_dvd ] using h_odd_P_val;
        · simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
          exact ⟨ odd_Q_val data_q fun p hp => hp_odd p <| by aesop, odd_R2_val data_q fun p hp => hp_odd p <| by aesop ⟩;
        · convert coprime_P_Q_mul_R2 data_p data_q hp_prime hp_distinct using 1
      generalize_proofs at *; (
      -- Apply the multiplicativity of tau.
      have h_mul : ∀ {m n : ℕ}, Nat.Coprime m n → tau (m * n) = tau m * tau n := by
        unfold tau;
        exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a
      generalize_proofs at *; (
      field_simp;
      rw [ h_mul, h_mul ] <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
      tauto));
    field_simp;
    convert h_mul using 1;
    unfold construct_a P_val Q_val R2_val; ring_nf;
    rw [ show ( List.map ( fun x => x.1 ^ x.2.1 ) data_p |> List.prod ) * ( List.map ( fun x => x.1 ^ x.2.1 ) data_q |> List.prod ) * 4 / 2 = ( List.map ( fun x => x.1 ^ x.2.1 ) data_p |> List.prod ) * ( List.map ( fun x => x.1 ^ x.2.1 ) data_q |> List.prod ) * 2 by rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; ring ] ; ring_nf;

/-
tau(Q) is product of (u+1).
-/
lemma tau_Q (data_q : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_q.map (·.1), Nat.Prime p)
  (hd : (data_q.map (·.1)).Pairwise (· ≠ ·)) :
  tau (Q_val data_q) = (data_q.map (fun (_, u, _) => u + 1)).prod := by
    convert tau_P data_q ?_ ?_ using 1;
    · assumption;
    · assumption

/-
tau(R2) is product of (v+1).
-/
lemma tau_R2 (data_q : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_q.map (·.1), Nat.Prime p)
  (hd : (data_q.map (·.1)).Pairwise (· ≠ ·)) :
  tau (R2_val data_q) = (data_q.map (fun (_, _, v) => v + 1)).prod := by
    convert tau_P using 1;
    constructor;
    · exact fun a data_p hp hd ↦ tau_P data_p hp hd;
    · intro h;
      convert h ( data_q.map fun x => ( x.1, x.2.2, x.2.1 ) ) _ _ using 1;
      · unfold P_val R2_val; aesop;
      · simp +decide [ List.map_map ];
        exact congr_arg _ ( List.map_congr_left fun x hx => by rfl );
      · aesop;
      · simpa using hd

/-
tau(Q*R2) is product of (u+v+1).
-/
lemma tau_Q_mul_R2 (data_q : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_q.map (·.1), Nat.Prime p)
  (hd : (data_q.map (·.1)).Pairwise (· ≠ ·)) :
  tau (Q_val data_q * R2_val data_q) = (data_q.map (fun (_, u, v) => u + v + 1)).prod := by
    -- Applying the lemma `tau_P_mul_R1` to `data_q`.
    have := tau_P_mul_R1 data_q hp hd; (
    exact this)

/-
a/2+1 is odd.
-/
lemma odd_a_div_two_plus_one (data_p data_q : List (ℕ × ℕ × ℕ)) :
  Odd (construct_a data_p data_q / 2 + 1) := by
    unfold construct_a; simp +decide [parity_simps] ;
    exact even_iff_two_dvd.mpr ( Nat.dvd_div_of_mul_dvd ( dvd_mul_of_dvd_left ( by exact dvd_mul_of_dvd_left ( by decide ) _ ) _ ) )

/-
tau(a+2) = 2 * tau(a/2+1).
-/
lemma tau_a_plus_two (data_p data_q : List (ℕ × ℕ × ℕ)) :
  tau (construct_a data_p data_q + 2) = 2 * tau (construct_a data_p data_q / 2 + 1) := by
    -- By definition of $a$, we know that $a + 2 = 2(a/2 + 1)$.
    have h_eq : construct_a data_p data_q + 2 = 2 * (construct_a data_p data_q / 2 + 1) := by
      unfold construct_a; ring_nf;
      grind;
    -- Since `construct_a / 2 + 1` is odd, it is coprime to 2.
    have h_coprime : Nat.Coprime (construct_a data_p data_q / 2 + 1) 2 := by
      rw [ Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec ];
      rw [ Nat.add_mod, Nat.mod_eq_zero_of_dvd ( Nat.dvd_div_of_mul_dvd _ ) ] ; norm_num;
      unfold construct_a; norm_num [ Nat.mul_mod, Nat.dvd_iff_mod_eq_zero ] ;
    -- Since `tau` is multiplicative and `2` and `construct_a / 2 + 1` are coprime, we have `tau(2 * (construct_a / 2 + 1)) = tau(2) * tau(construct_a / 2 + 1)`.
    have h_mul : ∀ {m n : ℕ}, Nat.Coprime m n → tau (m * n) = tau m * tau n := by
      unfold tau;
      exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
    rw [ h_eq, mul_comm, h_mul h_coprime, tau ];
    rw [ mul_comm, show tau 2 = 2 by rfl ]

/-
tau((a+2)*r1) = 2 * tau(a/2+1) * tau(r1).
-/
lemma d3_eq (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  tau ((a + 2) * r1) = 2 * tau (a / 2 + 1) * tau r1 := by
    -- By Lemma 25, `a+2` and `r1` are coprime.
    have h_coprime : let a := construct_a data_p data_q; let r1 := R1_val data_p; (a + 2).Coprime r1 := by
      apply coprime_a_plus_two_R1;
      · assumption;
      · assumption;
    -- By Lemma 26, `tau((a+2)*r1) = tau(a+2) * tau(r1)`.
    have h_tau_mul : let a := construct_a data_p data_q; let r1 := R1_val data_p; tau ((a + 2) * r1) = tau (a + 2) * tau r1 := by
      unfold tau;
      exact
        let a := construct_a data_p data_q;
        let r1 := R1_val data_p;
        Nat.Coprime.card_divisors_mul h_coprime;
    exact h_tau_mul.trans ( congr_arg₂ _ ( tau_a_plus_two data_p data_q ) rfl )

/-
tau((a+1)*r2) = tau(a+1) * tau(r2).
-/
lemma d4_eq (data_p data_q : List (ℕ × ℕ × ℕ))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r2 := R2_val data_q
  tau ((a + 1) * r2) = tau (a + 1) * tau r2 := by
    -- Apply the multiplicativity of the divisor function.
    have h_divisors_mul : ∀ {m n : ℕ}, Nat.gcd m n = 1 → (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
      exact fun {m n} a ↦ Nat.Coprime.card_divisors_mul a;
    apply h_divisors_mul;
    convert coprime_a_plus_one_R2 data_p data_q h_pos using 1

/-
(tau(P) * tau(R1)) / tau(P * R1) = \prod f_rat(x, y).
-/
lemma prod_f_rat_eq (data_p : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_p.map (·.1), Nat.Prime p)
  (hd : (data_p.map (·.1)).Pairwise (· ≠ ·)) :
  (tau (P_val data_p) * tau (R1_val data_p) : ℚ) / tau (P_val data_p * R1_val data_p) = (data_p.map (fun (_, x, y) => f_rat x y)).prod := by
    rw [ tau_P data_p hp hd, tau_R1 data_p hp hd, tau_P_mul_R1 data_p hp hd ];
    unfold f_rat; simp +decide ;
    induction data_p <;> simp +decide [ *, Function.comp ];
    grind

/-
(tau(Q * R2)) / (tau(Q) * tau(R2)) = \prod (1 / f_rat(u, v)).
-/
lemma prod_inv_f_rat_eq (data_q : List (ℕ × ℕ × ℕ))
  (hp : ∀ p ∈ data_q.map (·.1), Nat.Prime p)
  (hd : (data_q.map (·.1)).Pairwise (· ≠ ·)) :
  (tau (Q_val data_q * R2_val data_q) : ℚ) / (tau (Q_val data_q) * tau (R2_val data_q)) = (data_q.map (fun (_, u, v) => 1 / f_rat u v)).prod := by
    -- Apply the definition of `f_rat` to rewrite the right-hand side.
    simp [f_rat];
    rw [ tau_Q_mul_R2, tau_Q, tau_R2 ];
    all_goals try assumption;
    induction data_q <;> simp +decide [ *, mul_assoc, mul_div_mul_comm ];
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, List.prod_map_mul ]

/-
The target value identity holds.
-/
lemma target_eq_target_val (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r := construct_r data_p data_q
  let d1 := tau (a_seq a 1 * r 0)
  let d2 := tau (a_seq a 0 * r 1)
  let d3 := tau (a_seq a 2 * r 1)
  let d4 := tau (a_seq a 1 * r 2)
  let d5 := tau (a_seq a 2 / 2 * r 0)
  let d6 := tau (a_seq a 0 / 2 * r 2)
  (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ) = target_val data_p data_q := by
    set a := construct_a data_p data_q
    set r := construct_r data_p data_q
    set d1 := tau (a_seq a 1 * r 0)
    set d2 := tau (a_seq a 0 * r 1)
    set d3 := tau (a_seq a 2 * r 1)
    set d4 := tau (a_seq a 1 * r 2)
    set d5 := tau (a_seq a 2 / 2 * r 0)
    set d6 := tau (a_seq a 0 / 2 * r 2);
    -- By definition of $d_i$, we know that $d1 = \tau(a+1)$, $d2 = \tau(a \cdot r1)$, $d3 = \tau((a+2) \cdot r1)$, $d4 = \tau((a+1) \cdot r2)$, $d5 = \tau(a/2 + 1)$, and $d6 = \tau(a/2 \cdot r2)$.
    have hd1 : d1 = tau (a + 1) := by
      simp +zetaDelta at *;
      unfold construct_r; simp +decide [ a_seq ] ;
    have hd2 : d2 = tau (a * R1_val data_p) := by
      exact congr_arg _ ( by rfl ) ;
    have hd3 : d3 = tau ((a + 2) * R1_val data_p) := by
      exact rfl
    have hd4 : d4 = tau ((a + 1) * R2_val data_q) := by
      exact congr_arg _ ( by rfl )
    have hd5 : d5 = tau (a / 2 + 1) := by
      simp +zetaDelta at *;
      unfold a_seq construct_r; norm_num;
      erw [ Nat.add_div ] <;> norm_num;
      unfold construct_a; norm_num [ Nat.add_mod, Nat.mul_mod ] ;
    have hd6 : d6 = tau (a / 2 * R2_val data_q) := by
      exact rfl;
    -- Substitute the expressions for $d_i$ into the ratio.
    have h_ratio : (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5) = (4 / 3) * ((tau (P_val data_p) * tau (R1_val data_p) : ℚ) / tau (P_val data_p * R1_val data_p)) * ((tau (Q_val data_q * R2_val data_q) : ℚ) / (tau (Q_val data_q) * tau (R2_val data_q))) := by
      rw [hd1, hd2, hd3, hd4, hd5, hd6];
      have h_subst : tau (a * R1_val data_p) = 3 * tau (Q_val data_q) * tau (P_val data_p * R1_val data_p) ∧ tau ((a + 2) * R1_val data_p) = 2 * tau (a / 2 + 1) * tau (R1_val data_p) ∧ tau ((a + 1) * R2_val data_q) = tau (a + 1) * tau (R2_val data_q) ∧ tau (a / 2 * R2_val data_q) = 2 * tau (P_val data_p) * tau (Q_val data_q * R2_val data_q) := by
        apply_rules [ And.intro, tau_a_mul_R1_eq, d3_eq, d4_eq, tau_a_div_two_mul_R2 ];
      rw [ h_subst.1, h_subst.2.1, h_subst.2.2.1, h_subst.2.2.2 ] ; push_cast ; ring_nf;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < tau ( 1 + a ) from Finset.card_pos.mpr ⟨ 1, by aesop_cat ⟩ ), ne_of_gt ( show 0 < tau ( 1 + a / 2 ) from Finset.card_pos.mpr ⟨ 1, by aesop_cat ⟩ ) ];
    convert h_ratio using 1;
    rw [ prod_f_rat_eq, prod_inv_f_rat_eq ];
    · exact rfl;
    · exact fun p hp => hp_prime p <| List.mem_append_right _ hp;
    · exact hp_distinct.sublist ( by simp +decide );
    · exact fun p hp => hp_prime p <| List.mem_append_left _ hp;
    · exact List.pairwise_append.mp hp_distinct |>.1

/-
If a prime divides R1, it is in the list of primes.
-/
lemma prime_dvd_R1_imp_mem (data_p : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ data_p.map (fun x => x.1), Nat.Prime p)
  (p : ℕ) (hp : Nat.Prime p) (h : p ∣ R1_val data_p) :
  p ∈ data_p.map (fun x => x.1) := by
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, R1_val ] ;
    obtain ⟨ a, b, c, h₁, h₂, h₃ ⟩ := h; rw [ ZMod.natCast_eq_zero_iff ] at h₂; have := Nat.prime_dvd_prime_iff_eq hp ( hp_prime _ _ _ h₁ ) ; aesop;

/-
There exist 3 distinct primes coprime to all elements of a_seq and r.
-/
lemma suitable_primes_exist (a : ℕ) (r : Fin 3 → ℕ)
  (ha : 0 < a) (hr : ∀ i, 0 < r i) :
  ∃ p : Fin 3 → ℕ,
    (∀ i, (p i).Prime) ∧
    (∀ i j, i ≠ j → p i ≠ p j) ∧
    (∀ i j, (p i).Coprime (a_seq a j)) ∧
    (∀ i j, (p i).Coprime (r j)) := by
      -- By `exists_three_primes`, there exist 3 distinct primes coprime to $P$.
      obtain ⟨p, hp_prime, hp_distinct, hp_coprime⟩ : ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ (∀ i, Nat.Coprime (p i) (a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2)) := by
        have := exists_three_primes ( a_seq a 0 * a_seq a 1 * a_seq a 2 * r 0 * r 1 * r 2 ) ?_;
        · exact this;
        · simp +decide [ *, a_seq ];
          exact ⟨ ⟨ ⟨ ha.ne', ne_of_gt ( hr 0 ) ⟩, ne_of_gt ( hr 1 ) ⟩, ne_of_gt ( hr 2 ) ⟩;
      refine' ⟨ p, hp_prime, hp_distinct, _, _ ⟩ <;> simp_all +decide [Nat.coprime_mul_iff_right];
      · intro i j; specialize hp_coprime i; fin_cases j <;> tauto;
      · exact fun i j => by fin_cases j <;> simp_all +decide [ Nat.Coprime ] ;

/-
r1 is coprime to a+1.
-/
lemma r1_coprime_a_plus_one (data_p data_q : List (ℕ × ℕ × ℕ))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r1 := R1_val data_p
  r1.Coprime (a + 1) := by
    -- Let `p` be a prime factor of `r1`.
    by_contra h_not_coprime
    obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ R1_val data_p ∧ p ∣ construct_a data_p data_q + 1 := by
      exact Nat.Prime.not_coprime_iff_dvd.mp h_not_coprime;
    -- Since `p` divides `R1_val data_p`, it must also divide `construct_a data_p data_q`.
    have hp_div_a : p ∣ construct_a data_p data_q := by
      apply prime_dvd_R1_imp_dvd_a data_p data_q h_pos p hp_prime hp_div.left;
    simp_all +decide [ Nat.dvd_add_right ]

/-
If a prime p divides R2_val, it is in the list of primes of data_q.
-/
lemma prime_dvd_R2_imp_mem (data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ data_q.map (fun x => x.1), Nat.Prime p)
  (p : ℕ) (hp : Nat.Prime p) (h : p ∣ R2_val data_q) :
  p ∈ data_q.map (fun x => x.1) := by
    exact prime_dvd_R1_imp_mem data_q hp_prime p hp h

/-
R1_val and R2_val are coprime.
-/
lemma coprime_R1_R2 (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  (R1_val data_p).Coprime (R2_val data_q) := by
    apply_mod_cast Nat.coprime_of_dvd';
    intro k hk_prime hk_div_R1 hk_div_R2
    have hk_mem_data_p : k ∈ data_p.map (fun x => x.1) := by
      apply prime_dvd_R1_imp_mem data_p (by
      exact fun p hp => hp_prime p <| List.mem_append_left _ hp) k hk_prime hk_div_R1
    have hk_mem_data_q : k ∈ data_q.map (fun x => x.1) := by
      apply prime_dvd_R2_imp_mem data_q (fun p hp => hp_prime p (List.mem_append_right _ hp)) k hk_prime hk_div_R2
    have hk_ne : k ≠ k := by
      grind
    exact absurd hk_ne (by simp)

/-
The values in construct_r are pairwise coprime.
-/
lemma r_values_pairwise_coprime (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·)) :
  let r := construct_r data_p data_q
  ∀ i j, i ≠ j → (r i).Coprime (r j) := by
    have h_coprime : Nat.Coprime (R1_val data_p) (R2_val data_q) := by
      apply coprime_R1_R2;
      · grind +ring;
      · assumption;
    unfold construct_r; simp_all +decide [ Fin.forall_fin_succ ] ;
    exact ⟨ h_coprime, h_coprime.symm ⟩

/-
r2 is coprime to a+2.
-/
lemma r2_coprime_a_plus_two (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2) :
  let a := construct_a data_p data_q
  let r2 := R2_val data_q
  r2.Coprime (a + 2) := by
    refine' Nat.coprime_of_dvd' _;
    intro k hk hk' hk''; have := Nat.dvd_sub hk'' ( prime_dvd_R2_imp_dvd_a data_p data_q h_pos k hk hk' ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    contrapose! hk'; simp_all +decide ;
    exact Nat.odd_iff.mp ( odd_R2_val data_q fun p hp => hp_odd p <| by aesop ) |> fun h => h.symm ▸ rfl;

/-
If data_p and data_q satisfy the conditions, then target_val data_p data_q is in R_set.
-/
lemma target_val_in_R_set (hGPY : GoldstonGrahamPintzYildirimStatement)
  (data_p data_q : List (ℕ × ℕ × ℕ))
  (hp_prime : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Nat.Prime p)
  (hp_odd : ∀ p ∈ (data_p.map (fun x => x.1)) ++ (data_q.map (fun x => x.1)), Odd p)
  (hp_distinct : (data_p.map (fun x => x.1) ++ data_q.map (fun x => x.1)).Pairwise (· ≠ ·))
  (h_pos : ∀ t ∈ data_p ++ data_q, 0 < t.2.1 ∧ 0 < t.2.2)
  (hr_odd : ∀ i, Odd (construct_r data_p data_q i)) :
  target_val data_p data_q ∈ R_set := by
    have hr_coprime : ∀ i j, i ≠ j → (construct_r data_p data_q i).Coprime (construct_r data_p data_q j) := by
      apply r_values_pairwise_coprime data_p data_q hp_prime hp_distinct;
    have ha_pos : 0 < construct_a data_p data_q := by
      exact Nat.mul_pos ( Nat.mul_pos ( by decide ) ( List.prod_pos <| by intros p hp; obtain ⟨ x, hx, rfl ⟩ := List.mem_map.mp hp; exact pow_pos ( Nat.Prime.pos <| hp_prime _ <| by aesop ) _ ) ) ( List.prod_pos <| by intros p hp; obtain ⟨ x, hx, rfl ⟩ := List.mem_map.mp hp; exact pow_pos ( Nat.Prime.pos <| hp_prime _ <| by aesop ) _ ) ;
    have ha_even : Even (construct_a data_p data_q) := by
      exact even_iff_two_dvd.mpr ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _ )
    have hr_gt_one : ∀ i, 0 < construct_r data_p data_q i := by
      grind
    have hra_coprime : ∀ i, (construct_r data_p data_q i).Coprime (a_seq (construct_a data_p data_q) i) := by
      intro i
      fin_cases i <;> simp [construct_r, a_seq];
      · convert r1_coprime_a_plus_one data_p data_q h_pos using 1;
      · convert r2_coprime_a_plus_two data_p data_q hp_odd h_pos using 1
    have hp_exists : ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ (∀ i j, Nat.Coprime (p i) (a_seq (construct_a data_p data_q) j)) ∧ (∀ i j, Nat.Coprime (p i) (construct_r data_p data_q j)) := by
      apply suitable_primes_exist; assumption; exact hr_gt_one;
    obtain ⟨p, hp_prime, hp_distinct, hp_coprime_a, hp_coprime_r⟩ := hp_exists
    generalize_proofs at *; (
    have hR : ∃ v1 v2 v3, v1 ∈ R_set ∧ v2 ∈ R_set ∧ v3 ∈ R_set ∧
      let d1 := tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 0)
      let d2 := tau (a_seq (construct_a data_p data_q) 0 * construct_r data_p data_q 1)
      let d3 := tau (a_seq (construct_a data_p data_q) 2 * construct_r data_p data_q 1)
      let d4 := tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 2)
      let d5 := tau (a_seq (construct_a data_p data_q) 2 / 2 * construct_r data_p data_q 0)
      let d6 := tau (a_seq (construct_a data_p data_q) 0 / 2 * construct_r data_p data_q 2)
      v1 = (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ) ∧
      v2 = (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ) ∧
      v3 = (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ) := by
        have := R_contains_modified_values hGPY (construct_a data_p data_q) (construct_r data_p data_q) p (fun i => (if i = 0 then tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 0) * tau (a_seq (construct_a data_p data_q) 2 * construct_r data_p data_q 1) * tau (a_seq (construct_a data_p data_q) 0 / 2 * construct_r data_p data_q 2) ^ 2 else if i = 1 then tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 0) * tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 2) * tau (a_seq (construct_a data_p data_q) 2 / 2 * construct_r data_p data_q 0) * tau (a_seq (construct_a data_p data_q) 0 / 2 * construct_r data_p data_q 2) else tau (a_seq (construct_a data_p data_q) 0 * construct_r data_p data_q 1) * tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 2) * tau (a_seq (construct_a data_p data_q) 2 / 2 * construct_r data_p data_q 0) ^ 2)) ha_even ha_pos hr_gt_one hr_odd hr_coprime hra_coprime hp_prime hp_distinct hp_coprime_a hp_coprime_r (by
        have htau_pos {n : ℕ} (hn : n ≠ 0) : 0 < tau n := by
          unfold tau
          exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
        have ha_half_pos : 0 < construct_a data_p data_q / 2 := by
          exact Nat.div_pos (Nat.le_of_dvd ha_pos (even_iff_two_dvd.mp ha_even)) zero_lt_two
        have ha_two_half_pos : 0 < a_seq (construct_a data_p data_q) 2 / 2 := by
          exact Nat.div_pos (by simp [a_seq]) zero_lt_two
        have hd1_pos : 0 < tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 0) := by
          apply htau_pos
          exact Nat.mul_ne_zero (by simp [a_seq]) (ne_of_gt (hr_gt_one 0))
        have hd2_pos : 0 < tau (a_seq (construct_a data_p data_q) 0 * construct_r data_p data_q 1) := by
          apply htau_pos
          exact Nat.mul_ne_zero (by simpa [a_seq] using ne_of_gt ha_pos) (ne_of_gt (hr_gt_one 1))
        have hd3_pos : 0 < tau (a_seq (construct_a data_p data_q) 2 * construct_r data_p data_q 1) := by
          apply htau_pos
          exact Nat.mul_ne_zero (by simp [a_seq]) (ne_of_gt (hr_gt_one 1))
        have hd4_pos : 0 < tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 2) := by
          apply htau_pos
          exact Nat.mul_ne_zero (by simp [a_seq]) (ne_of_gt (hr_gt_one 2))
        have hd5_pos : 0 < tau (a_seq (construct_a data_p data_q) 2 / 2 * construct_r data_p data_q 0) := by
          apply htau_pos
          exact Nat.mul_ne_zero (ne_of_gt ha_two_half_pos) (ne_of_gt (hr_gt_one 0))
        have hd6_pos : 0 < tau (a_seq (construct_a data_p data_q) 0 / 2 * construct_r data_p data_q 2) := by
          apply htau_pos
          exact Nat.mul_ne_zero (by simpa [a_seq] using ne_of_gt ha_half_pos) (ne_of_gt (hr_gt_one 2))
        intro i
        fin_cases i <;> simp
        · exact ⟨⟨hd1_pos, hd3_pos⟩, pow_pos hd6_pos 2⟩
        · exact ⟨⟨⟨hd1_pos, hd4_pos⟩, hd5_pos⟩, hd6_pos⟩
        · exact ⟨⟨hd2_pos, hd4_pos⟩, pow_pos hd5_pos 2⟩) ; simp_all +decide [ Fin.forall_fin_succ ] ; (
        grind)
    generalize_proofs at *; (
    have h_target : let d1 := tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 0)
      let d2 := tau (a_seq (construct_a data_p data_q) 0 * construct_r data_p data_q 1)
      let d3 := tau (a_seq (construct_a data_p data_q) 2 * construct_r data_p data_q 1)
      let d4 := tau (a_seq (construct_a data_p data_q) 1 * construct_r data_p data_q 2)
      let d5 := tau (a_seq (construct_a data_p data_q) 2 / 2 * construct_r data_p data_q 0)
      let d6 := tau (a_seq (construct_a data_p data_q) 0 / 2 * construct_r data_p data_q 2)
      (d1 * d3 * d6 : ℚ) / (d2 * d4 * d5 : ℚ) = target_val data_p data_q := by
        apply target_eq_target_val; assumption; assumption; assumption; assumption
    generalize_proofs at *; (
    grind)))

/-
R_set contains all positive rationals.
-/
lemma R_set_contains_pos_rationals (q : ℚ) (hq : 0 < q) (hGPY : GoldstonGrahamPintzYildirimStatement) : q ∈ R_set := by
  -- Use `exists_representation_clean` to get `data_p`, `data_q` such that `q = target_val data_p data_q`.
  obtain ⟨data_p, data_q, hq_eq, hr_odd, hp_prime, hp_distinct, h_pos⟩ := exists_representation_clean q hq;
  -- Apply the lemma `target_val_in_R_set` to conclude that `q` is in `R_set`.
  apply hq_eq ▸ target_val_in_R_set hGPY data_p data_q hp_prime (by
  intro p hp
  have hp_prime : Nat.Prime p := hp_prime p hp
  have hp_odd : Odd p := by
    have hp_odd : Odd (R1_val data_p) ∧ Odd (R2_val data_q) := by
      exact ⟨ hr_odd 1, hr_odd 2 ⟩;
    by_cases hp_p : p ∈ data_p.map (fun x => x.1) <;> by_cases hp_q : p ∈ data_q.map (fun x => x.1) <;> simp_all +decide;
    · have := hp_distinct; simp_all +decide [ List.pairwise_append ] ;
      grind;
    · have hp_div_R1 : p ∣ R1_val data_p := by
        exact dvd_trans ( dvd_pow_self _ ( ne_of_gt ( h_pos.1 _ _ _ hp_p.choose_spec.choose_spec |>.2 ) ) ) ( List.dvd_prod ( List.mem_map.mpr ⟨ _, hp_p.choose_spec.choose_spec, rfl ⟩ ) ) ;
      exact hp_odd.1.of_dvd_nat hp_div_R1;
    · obtain ⟨ a, b, h ⟩ := hp_q; specialize hp_odd; replace hp_odd := hp_odd.2.of_dvd_nat ( show p ∣ R2_val data_q from ?_ ) ; simp_all +decide ;
      exact dvd_trans ( dvd_pow_self _ ( by linarith [ h_pos.2 _ _ _ h ] ) ) ( List.dvd_prod ( List.mem_map.mpr ⟨ _, h, rfl ⟩ ) )
  exact hp_odd) hp_distinct (by
  grind) hr_odd

/-
R_set is a subset of divisor_ratios.
-/
lemma R_set_subset_divisor_ratios : R_set ⊆ divisor_ratios := by
  -- Let $q$ be an element of $R_set$. By definition, the set $\{n \mid \frac{\tau(n+1)}{\tau(n)} = q\}$ is infinite.
  intro q hq
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, 0 < n ∧ (tau (n + 1) : ℚ) / (tau n : ℚ) = q := by
    have := hq.exists_gt 0;
    tauto;
  -- By definition of divisor_ratios, we need to show that there exists a natural number m such that m > 0 and (tau (m + 1) : ℚ) / (tau m : ℚ) = q.
  use n;
  grind

/-
divisor_ratios contains all positive rationals.
-/
lemma divisor_ratios_contains_all_pos_rats (hGPY : GoldstonGrahamPintzYildirimStatement) :
  { q : ℚ | 0 < q } ⊆ divisor_ratios := by
    -- By combining the results from R_set_contains_pos_rationals and R_set_subset_divisor_ratios, we can conclude that divisor_ratios contains all positive rationals.
    intros q hq
    have hq_in_R_set : q ∈ R_set := R_set_contains_pos_rationals q hq hGPY
    exact R_set_subset_divisor_ratios hq_in_R_set

/-
The set of positive rationals is dense in the set of positive real numbers.
-/
lemma pos_rats_dense_in_pos_reals : Set.Ioi (0 : ℝ) ⊆ closure (Set.image (fun q : ℚ => (q : ℝ)) {q : ℚ | 0 < q}) := by
  intro x hx_pos
  obtain ⟨q_n, hq_n⟩ : ∃ q_n : ℕ → ℚ, (∀ n, 0 < q_n n) ∧ Filter.Tendsto (fun n => (q_n n : ℝ)) Filter.atTop (nhds x) := by
    have h_seq : ∀ ε > 0, ∃ q : ℚ, 0 < q ∧ |q - x| < ε := by
      intro ε ε_pos; have := exists_rat_btwn ( show x < x + ε by linarith ) ; rcases this with ⟨ q, hq₁, hq₂ ⟩ ; exact ⟨ q, by exact_mod_cast ( by linarith [ hx_pos.out ] : ( 0 : ℝ ) < q ), abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩ ;
    generalize_proofs at *; (
    exact ⟨ fun n => Classical.choose ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1, tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩);
  exact mem_closure_of_tendsto hq_n.2 ( Filter.Eventually.of_forall fun n => Set.mem_image_of_mem _ ( hq_n.1 n ) )

/-
The set of divisor ratios is dense in (0, \infty).
-/
theorem ErdosProblem964 (hGPY : GoldstonGrahamPintzYildirimStatement) :
  Set.Ioi (0 : ℝ) ⊆ closure (Set.image (fun q : ℚ => (q : ℝ)) divisor_ratios) := by
    have h_image_subset : Set.image (fun q : ℚ => (q : ℝ)) {q : ℚ | 0 < q} ⊆ Set.image (fun q : ℚ => (q : ℝ)) divisor_ratios :=
      Set.image_mono ( divisor_ratios_contains_all_pos_rats hGPY );
    exact Set.Subset.trans ( pos_rats_dense_in_pos_reals ) ( closure_mono h_image_subset )

-- #print axioms ErdosProblem964
-- 'Erdos964.ErdosProblem964' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos964
