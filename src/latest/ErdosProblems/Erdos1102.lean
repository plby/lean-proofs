/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1102.
https://www.erdosproblems.com/forum/thread/1102

Informal authors:
- Wouter van Doorn
- Terence Tao

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/1102#post-4415
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem1102PropertyP.lean
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem1102PropertyQDensity.lean
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem1102PropertyOverP.lean
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem1102PropertyQFastGrowing.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1102.lean
-/
/-
We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many
  $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that
  $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$
  such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_\infty$ if there exist infinitely many positive
  integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in
  A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao
and I managed to prove tight bounds on the possible densities of sequences with
one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree
properties of their translates. arXiv:2512.01087 (2025).

Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof
of the following theorem is formalized in the Lean file below:

Any sequence with property $P$ has density $0$. On the other hand, the decay
rate of this density can be arbitrarily slow.

At the very end you can find the (relevant parts of the) statement of Erdős
Problem #1102 taken from the Formal Conjectures project by Google DeepMind,
which we also prove.

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1102.lean

-/

import Mathlib

namespace Erdos1102


open Squarefree Set Order Filter Topology

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A set A has natural density d if the proportion of elements in A up to n tends to d as n goes to infinity.
-/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds d)

/-
A set A has property P if for every n, the set of a in A such that n+a is squarefree is finite.
-/
def PropertyP (A : Set ℕ) : Prop := ∀ n, ({a ∈ A | Squarefree (n + a)}).Finite

/-
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
Definition of W_r = (p_1 ... p_r)^2.
-/
def W (r : ℕ) : ℕ := (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i)^2

/-
Definition of the sequence l_r for the construction in Theorem 1(ii). l_0 = 0, and l_{r+1} is the smallest integer > l_r such that f(j) >= W_{r+1} for all j >= l_{r+1}.
-/
def l_seq (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : ℕ → ℕ :=
  Nat.rec 0 (fun r lr => Nat.find (by
  exact Filter.eventually_atTop.mp ( hf.eventually_ge_atTop ( W ( r + 1 ) ) ) |> fun ⟨ n, hn ⟩ ↦ ⟨ n + lr + 1, by linarith, fun j hj ↦ hn j ( by linarith ) ⟩ : ∃ n, n > lr ∧ ∀ j ≥ n, f j ≥ W (r + 1)))

/-
Definition of k(j) for the construction in Theorem 1(ii). k(j) is the largest r such that l_r <= j.
-/
def k_func (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) : ℕ :=
  ((Finset.range (j + 1)).filter (fun r => l_seq f hf r ≤ j)).max' (by
  exact ⟨ 0, by simp +decide [ l_seq ] ⟩)

/-
Definition of the sequence a_j for the construction in Theorem 1(ii). a_j = j for j <= l_1. For j > l_1, a_j is the smallest integer > a_{j-1} such that a_j + r is divisible by p_r^2 for all 1 <= r <= k(j).
-/
def a_seq (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : ℕ → ℕ :=
  Nat.rec 0 (fun j aj =>
    if j + 1 ≤ l_seq f hf 1 then j + 1
    else Nat.find (by
    -- By the Chinese Remainder Theorem, there exists an x such that x ≡ -r (mod p_r^2) for each r in the given range.
    obtain ⟨x, hx⟩ : ∃ x, ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), x ≡ -r [ZMOD (Nat.nth Nat.Prime (r - 1))^2] := by
      -- Apply the Chinese Remainder Theorem to find such an $x$.
      have h_crt : ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), ∃ x, x ≡ -r [ZMOD (Nat.nth Nat.Prime (r - 1)^2)] ∧ ∀ s ∈ Finset.Icc 1 (k_func f hf (j + 1)), s ≠ r → x ≡ 0 [ZMOD (Nat.nth Nat.Prime (s - 1)^2)] := by
        -- For each $r$, let $y_r$ be the multiplicative inverse of $\prod_{s \neq r} p_s^2$ modulo $p_r^2$.
        intros r hr
        obtain ⟨y_r, hy_r⟩ : ∃ y_r : ℤ, y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2) ≡ 1 [ZMOD (Nat.nth Nat.Prime (r - 1))^2] := by
          have h_coprime : Nat.gcd (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2) ((Nat.nth Nat.Prime (r - 1))^2) = 1 := by
            refine' Nat.Coprime.prod_left _;
            simp +contextual [Nat.Prime.coprime_iff_not_dvd];
            intro i hi₁ hi₂ hi₃; rw [ Nat.Prime.dvd_iff_eq ] <;> norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
            exact fun h => hi₃ <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; cases r <;> cases i <;> aesop;
          have := Nat.gcd_eq_gcd_ab ( ∏ s ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) \ { r }, Nat.nth Nat.Prime ( s - 1 ) ^ 2 ) ( Nat.nth Nat.Prime ( r - 1 ) ^ 2 );
          exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by push_cast at *; linarith ⟩ ⟩;
        use -↑r * y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2);
        exact ⟨ by simpa [ mul_assoc ] using hy_r.mul_left _, fun s hs hs' => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ⟩;
      choose! x hx₁ hx₂ using h_crt;
      use ∑ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), x r;
      intro r hr; simp_all +decide only [Int.ModEq];
      rw [ Finset.sum_int_mod, Finset.sum_eq_single r ] <;> aesop;
    -- Let $M = \prod_{r=1}^{k(j+1)} p_r^2$.
    set M := ∏ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (Nat.nth Nat.Prime (r - 1)^2) with hM_def;
    -- Let $y$ be a positive integer such that $y \equiv x \pmod{M}$ and $y > aj$.
    obtain ⟨y, hy⟩ : ∃ y, y > aj ∧ y ≡ x [ZMOD ↑M] := by
      use Int.toNat ( x % M + M * ( aj + 1 ) );
      norm_num [ Int.ModEq ];
      exact ⟨ by nlinarith [ Int.emod_nonneg x ( show ( M : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ), Int.emod_lt_of_pos x ( show ( M : ℤ ) > 0 from mod_cast Finset.prod_pos fun i hi => pow_pos ( Nat.Prime.pos <| by aesop ) 2 ) ], by rw [ max_eq_left ( by nlinarith [ Int.emod_nonneg x ( show ( M : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ), Int.emod_lt_of_pos x ( show ( M : ℤ ) > 0 from mod_cast Finset.prod_pos fun i hi => pow_pos ( Nat.Prime.pos <| by aesop ) 2 ) ] ) ] ; simp +decide [Int.add_emod] ⟩;
    refine' ⟨ y, hy.1, fun r hr => _ ⟩;
    rw [ ← Int.natCast_inj ] ; simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ];
    convert dvd_add ( dvd_trans ( Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr hr ) ) hy.2 ) ( hx r hr.1 hr.2 ) using 1 ; ring : ∃ x, x > aj ∧ ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (x + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0))

/-
The set A constructed from the sequence a_j.
-/
def A_constructed (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set ℕ :=
  {n | ∃ j ≥ 1, n = a_seq f hf j}

/-
Lemma: W(k(j)) <= f(j).
-/
lemma W_k_le_f (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (hf_pos : ∀ n, 1 ≤ f n) (j : ℕ) :
  W (k_func f hf j) ≤ f j := by
    -- By definition of $l_seq$, we know that for all $m \geq l_seq f hf (k_func f hf j)$, $f(m) \geq W (k_func f hf j)$.
    have h_l_seq : ∀ m ≥ l_seq f hf (k_func f hf j), f m ≥ W (k_func f hf j) := by
      have h_l_seq : ∀ r, ∀ m ≥ l_seq f hf r, f m ≥ W r := by
        intros r m hm
        induction' r with r ih generalizing m;
        · exact hf_pos m;
        · exact Nat.find_spec ( _ : ∃ n, n > l_seq f hf r ∧ ∀ j ≥ n, f j ≥ W ( r + 1 ) ) |>.2 m hm;
      exact h_l_seq _;
    have := Finset.max'_mem ( Finset.filter ( fun r => l_seq f hf r ≤ j ) ( Finset.range ( j + 1 ) ) ) ⟨ k_func f hf j, by
      exact Finset.max'_mem _ _ ⟩ ; aesop;

/-
k(j) is a monotonic function of j.
-/
lemma k_func_mono (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : Monotone (k_func f hf) := by
  intro j k hjk;
  refine' Finset.le_max' _ _ _;
  have h_range : k_func f hf j ∈ Finset.filter (fun r => l_seq f hf r ≤ j) (Finset.range (j + 1)) := by
    convert Finset.max'_mem _ _;
  grind

/-
Lemma: a_{j+1} <= a_j + W(k(j+1)).
-/
lemma a_seq_step_le (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) :
  a_seq f hf (j + 1) ≤ a_seq f hf j + W (k_func f hf (j + 1)) := by
    -- By the Chinese Remainder Theorem, there exists a solution $y$ to the system of congruences.
    obtain ⟨y, hy⟩ : ∃ y, y > a_seq f hf j ∧ ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (y + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
      -- By the Chinese Remainder Theorem, there exists a solution $y$ to the system of congruences $y \equiv -r \pmod{p_r^2}$ for $r = 1, 2, \ldots, k(j+1)$.
      obtain ⟨y, hy⟩ : ∃ y, ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), y ≡ -r [ZMOD (Nat.nth Nat.Prime (r - 1))^2] := by
        have h_crt : ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), ∃ y, y ≡ -r [ZMOD (Nat.nth Nat.Prime (r - 1))^2] ∧ ∀ s ∈ Finset.Icc 1 (k_func f hf (j + 1)), s ≠ r → y ≡ 0 [ZMOD (Nat.nth Nat.Prime (s - 1))^2] := by
          -- For each $r$, let $y_r$ be the multiplicative inverse of $\prod_{s \neq r} p_s^2$ modulo $p_r^2$.
          intros r hr
          obtain ⟨y_r, hy_r⟩ : ∃ y_r : ℤ, y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2) ≡ 1 [ZMOD (Nat.nth Nat.Prime (r - 1))^2] := by
            have h_coprime : Nat.gcd (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2) ((Nat.nth Nat.Prime (r - 1))^2) = 1 := by
              refine' Nat.Coprime.prod_left _;
              simp +contextual [Nat.Prime.coprime_iff_not_dvd];
              intro i hi₁ hi₂ hi₃; rw [ Nat.prime_dvd_prime_iff_eq ] <;> norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
              exact fun h => hi₃ <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; cases i <;> cases r <;> aesop;
            have := Nat.gcd_eq_gcd_ab ( ∏ s ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) \ { r }, Nat.nth Nat.Prime ( s - 1 ) ^ 2 ) ( Nat.nth Nat.Prime ( r - 1 ) ^ 2 );
            exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by push_cast at *; linarith ⟩ ⟩;
          use -r * y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2);
          exact ⟨ by simpa [ mul_assoc ] using hy_r.mul_left _, fun s hs hs' => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ⟩;
        choose! y hy₁ hy₂ using h_crt;
        use ∑ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), y r;
        intro r hr; simp_all +decide only [Int.ModEq];
        rw [ Finset.sum_int_mod, Finset.sum_eq_single r ] <;> aesop;
      -- Let $y$ be a solution to the system of congruences.
      obtain ⟨y, hy⟩ : ∃ y : ℕ, ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (y + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
        use Int.toNat ( y % ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), ( Nat.nth Nat.Prime ( r - 1 ) ) ^ 2 );
        intro r hr; rw [ ← Int.natCast_inj ] ; simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( show ( ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), Nat.nth Nat.Prime ( r - 1 ) ^ 2 : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) ] ;
        rw [ Int.dvd_iff_emod_eq_zero ] ; simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ( show r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) from Finset.mem_Icc.mpr hr ), Int.add_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
      use y + (a_seq f hf j + 1) * (∏ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (Nat.nth Nat.Prime (r - 1))^2);
      exact ⟨ by nlinarith [ show 0 < ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), Nat.nth Nat.Prime ( r - 1 ) ^ 2 from Finset.prod_pos fun x hx => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ], fun r hr => by simpa [ Nat.add_mod, Nat.mul_mod, Finset.prod_eq_prod_diff_singleton_mul hr ] using hy r hr ⟩;
    -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $(a_j, a_j + W(k(j+1))]$ that satisfies the congruences.
    obtain ⟨z, hz⟩ : ∃ z ∈ Set.Ioo (a_seq f hf j) (a_seq f hf j + W (k_func f hf (j + 1)) + 1), ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (z + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
      -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $(a_j, a_j + W(k(j+1))]$ that satisfies the congruences. Let $z = y - m \cdot W(k(j+1))$ for some integer $m$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, a_seq f hf j < y - m * W (k_func f hf (j + 1)) ∧ y - m * W (k_func f hf (j + 1)) < a_seq f hf j + W (k_func f hf (j + 1)) + 1 := by
        refine' ⟨ ( y - ( a_seq f hf j + 1 ) ) / W ( k_func f hf ( j + 1 ) ), _, _ ⟩;
        · rw [ Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le ];
          · linarith [ Nat.div_mul_le_self ( y - ( a_seq f hf j + 1 ) ) ( W ( k_func f hf ( j + 1 ) ) ), Nat.sub_add_cancel ( by linarith : a_seq f hf j + 1 ≤ y ) ];
          · exact le_trans ( Nat.div_mul_le_self _ _ ) ( Nat.sub_le _ _ ) |> le_trans <| by linarith;
        · rw [ tsub_lt_iff_left ];
          · linarith [ Nat.div_add_mod ( y - ( a_seq f hf j + 1 ) ) ( W ( k_func f hf ( j + 1 ) ) ), Nat.mod_lt ( y - ( a_seq f hf j + 1 ) ) ( show W ( k_func f hf ( j + 1 ) ) > 0 from pow_pos ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) ) 2 ), Nat.sub_add_cancel ( by linarith : a_seq f hf j + 1 ≤ y ) ];
          · exact le_trans ( Nat.div_mul_le_self _ _ ) ( Nat.sub_le_of_le_add <| by linarith );
      refine' ⟨ y - m * W ( k_func f hf ( j + 1 ) ), ⟨ hm.1, hm.2 ⟩, fun r hr => _ ⟩;
      rw [ ← Nat.dvd_iff_mod_eq_zero ] at *;
      convert Nat.dvd_sub ( Nat.dvd_of_mod_eq_zero ( hy.2 r hr ) ) ( dvd_mul_of_dvd_right ( show Nat.nth Nat.Prime ( r - 1 ) ^ 2 ∣ W ( k_func f hf ( j + 1 ) ) from _ ) m ) using 1;
      · grind;
      · exact dvd_trans ( by norm_num ) ( pow_dvd_pow_of_dvd ( Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr ( show r - 1 < k_func f hf ( j + 1 ) from Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.mem_Icc.mp hr |>.1 ) ) ) ( Finset.mem_Icc.mp hr |>.2 ) ) ) ) 2 );
    by_cases h_case : j + 1 ≤ l_seq f hf 1;
    · rcases j with ( _ | j ) <;> simp_all +decide [ a_seq ];
      · exact Nat.one_le_iff_ne_zero.mpr ( by erw [ show W ( k_func f hf 1 ) = ( ∏ i ∈ Finset.range ( k_func f hf 1 ), Nat.nth Nat.Prime i ) ^ 2 from rfl ] ; exact pow_ne_zero _ <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop );
      · grind;
    · simp +zetaDelta at *;
      exact Nat.le_of_lt_succ <| by { rw [ show a_seq f hf ( j + 1 ) = Nat.find ( show ∃ x, x > a_seq f hf j ∧ ∀ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), ( x + r ) % Nat.nth Nat.Prime ( r - 1 ) ^ 2 = 0 from ⟨ z, hz.1.1, fun r hr => hz.2 r ( Finset.mem_Icc.mp hr |>.1 ) ( Finset.mem_Icc.mp hr |>.2 ) ⟩ ) from if_neg <| by aesop ] ; exact Nat.lt_of_le_of_lt ( Nat.find_min' _ ⟨ hz.1.1, fun r hr => hz.2 r ( Finset.mem_Icc.mp hr |>.1 ) ( Finset.mem_Icc.mp hr |>.2 ) ⟩ ) ( by linarith ) }

/-
W(k(j)) <= f(j).
-/
lemma W_k_le_f_proved (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (hf_pos : ∀ n, 1 ≤ f n) (j : ℕ) :
  W (k_func f hf j) ≤ f j := by
    convert W_k_le_f f hf hf_pos j using 1

/-
For j > l_1, a_j satisfies the congruence conditions a_j = -r mod p_r^2 for r <= k(j).
-/
lemma a_seq_congruence (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) (hj : j > l_seq f hf 1) :
  ∀ r ∈ Finset.Icc 1 (k_func f hf j), (a_seq f hf j + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
    induction' j with j ih <;> simp_all +decide [ a_seq ];
    grind

/-
W(k(j)) <= f(j).
-/
lemma W_k_le_f_proof (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (hf_pos : ∀ n, 1 ≤ f n) (j : ℕ) :
  W (k_func f hf j) ≤ f j := by
    -- Apply the lemma W_k_le_f_proved with the given hypotheses.
    apply W_k_le_f_proved f hf hf_pos j

/-
W is a monotonic function.
-/
lemma W_mono : Monotone W := by
  -- The product of primes is monotone because each prime is greater than or equal to the previous one.
  have h_prod_mono : ∀ k m : ℕ, k ≤ m → (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) ≤ (∏ i ∈ Finset.range m, Nat.nth Nat.Prime i) := by
    intro k m hkm; rw [ ← Finset.prod_sdiff ( Finset.range_mono hkm ) ] ;
    exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => Nat.zero_le _ ) ( Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.Prime.ne_zero <| by aesop );
  exact fun k m hkm => Nat.pow_le_pow_left ( h_prod_mono k m hkm ) 2

/-
k(j) tends to infinity as j tends to infinity.
-/
lemma k_func_tendsto_atTop (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  Filter.Tendsto (k_func f hf) Filter.atTop Filter.atTop := by
    -- Since $l_seq$ is strictly increasing, $k_func$ is unbounded.
    have hk_unbounded : ∀ M, ∃ j, k_func f hf j ≥ M := by
      intro M
      obtain ⟨j, hj⟩ : ∃ j, l_seq f hf (M + 1) ≤ j := by
        use l_seq f hf (M + 1);
      refine' ⟨ j, _ ⟩
      generalize_proofs at *; (
      exact Finset.le_max' ( Finset.filter ( fun r => l_seq f hf r ≤ j ) ( Finset.range ( j + 1 ) ) ) ( M + 1 ) ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ show M + 1 ≤ j from hj.trans' ( show l_seq f hf ( M + 1 ) ≥ M + 1 from Nat.recOn ( M + 1 ) ( by norm_num ) fun r hr => Nat.find_spec ( _ : ∃ n, n > l_seq f hf r ∧ ∀ j ≥ n, f j ≥ W ( r + 1 ) ) |>.1.trans_le' <| by linarith ) ] ), hj ⟩ ) |> le_trans ( by norm_num ) ;);
    exact Filter.tendsto_atTop_atTop.mpr fun M => by obtain ⟨ j, hj ⟩ := hk_unbounded M; exact ⟨ j, fun n hn => le_trans hj ( k_func_mono f hf hn ) ⟩ ;

/-
a_j <= j * W(k(j)) for all j >= 1.
-/
lemma a_seq_upper_bound (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  ∀ j ≥ 1, a_seq f hf j ≤ j * W (k_func f hf j) := by
    intro j hj_ge_1
    induction' j, hj_ge_1 using Nat.le_induction with j ih;
    · -- For the base case $j = 1$, we have $a_1 = 1$.
      simp [a_seq];
      split_ifs <;> norm_num [ W ];
      · exact Nat.one_le_pow _ _ ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) );
      · unfold l_seq at * ; aesop;
    · -- By Lemma a_seq_step_le, we have $a_{j+1} \leq a_j + W(k(j+1))$.
      have h_step : a_seq f hf (j + 1) ≤ a_seq f hf j + W (k_func f hf (j + 1)) := by
        exact a_seq_step_le f hf j;
      nlinarith [ show W ( k_func f hf j ) ≤ W ( k_func f hf ( j + 1 ) ) from W_mono <| k_func_mono f hf <| Nat.le_succ _ ]

/-
The constructed sequence A has Property P (restricted to n >= 1).
-/
def PropertyP_positive (A : Set ℕ) : Prop := ∀ n, n ≥ 1 → ({a ∈ A | Squarefree (n + a)}).Finite

lemma A_constructed_PropertyP_positive (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  PropertyP_positive (A_constructed f hf) := by
    -- For any fixed $n \geq 1$, there exists $J$ such that for all $j \geq J$, $k(j) \geq n$.
    have h_J : ∀ n ≥ 1, ∃ J, ∀ j ≥ J, k_func f hf j ≥ n := by
      exact fun n hn => Filter.eventually_atTop.mp ( k_func_tendsto_atTop f hf |> Filter.Tendsto.eventually_ge_atTop <| n );
    -- For such $j$, by $a_seq_congruence$, $(a_j + n)$ is divisible by $p_{n-1}^2$.
    have h_div : ∀ n ≥ 1, ∃ J, ∀ j ≥ J, (a_seq f hf j + n) % (Nat.nth Nat.Prime (n - 1))^2 = 0 := by
      intros n hn
      obtain ⟨J, hJ⟩ := h_J n hn
      use max J (l_seq f hf 1 + 1) + 1
      intro j hj
      have hk : k_func f hf j ≥ n := by
        exact hJ j ( by linarith [ Nat.le_max_left J ( l_seq f hf 1 + 1 ) ] )
      have h_cong : (a_seq f hf j + n) % (Nat.nth Nat.Prime (n - 1))^2 = 0 := by
        convert a_seq_congruence f hf j ( by linarith [ Nat.le_max_left J ( l_seq f hf 1 + 1 ), Nat.le_max_right J ( l_seq f hf 1 + 1 ) ] ) n ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) using 1
      exact h_cong;
    -- Thus, {a in A | Squarefree (n + a)} is contained in {a_1, ..., a_{J-1}}, which is finite.
    intros n hn
    obtain ⟨J, hJ⟩ := h_div n hn
    have h_finite : {a ∈ A_constructed f hf | Squarefree (n + a)} ⊆ Finset.image (fun j => a_seq f hf j) (Finset.Icc 1 (J - 1)) := by
      intro a ha; obtain ⟨ j, hj₁, rfl ⟩ := ha.1; rcases lt_or_ge j J with hj₂ | hj₂ <;> simp_all +decide ;
      · exact ⟨ j, ⟨ hj₁, Nat.le_sub_one_of_lt hj₂ ⟩, rfl ⟩;
      · have := Nat.dvd_of_mod_eq_zero ( hJ j hj₂ ) ; simp_all +decide [Nat.squarefree_iff_prime_squarefree] ;
        exact False.elim <| ha.2 ( Nat.nth Nat.Prime ( n - 1 ) ) ( Nat.prime_nth_prime _ ) <| by simpa only [ sq, add_comm ] using this;
    exact Set.Finite.subset ( Finset.finite_toSet _ ) h_finite

/-
a_seq is strictly monotonic.
-/
lemma a_seq_strict_mono (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  StrictMono (a_seq f hf) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n;
    -- By definition of $a_seq$, we have $a_{j+1} > a_j$ for all $j$.
    have h_a_seq_strict_mono : ∀ j, a_seq f hf (j + 1) > a_seq f hf j := by
      intro j;
      -- By definition of $a_seq$, we have $a_seq f hf (j + 1) > a_seq f hf j$ because $a_seq f hf (j + 1)$ is the smallest integer greater than $a_seq f hf j$ that satisfies the congruence conditions.
      have h_a_seq_gt : ∀ j, a_seq f hf (j + 1) > a_seq f hf j := by
        intro j;
        refine' Nat.lt_of_not_ge fun h => _;
        induction' j with j ih <;> simp_all +decide [ a_seq ];
        · split_ifs at h ; simp_all +decide [ l_seq ];
        · grind;
      exact h_a_seq_gt j;
    exact h_a_seq_strict_mono n

/-
The cardinality of the set S_r of residues modulo W_r not divisible by the square of the first r primes is the product of (p_i^2 - 1).
-/
def S_r (r : ℕ) : Finset ℕ := (Finset.Icc 1 (W r)).filter (fun s => ∀ i ∈ Finset.range r, ¬ (Nat.nth Nat.Prime i)^2 ∣ s)

lemma card_S_r (r : ℕ) : (S_r r).card = ∏ i ∈ Finset.range r, ((Nat.nth Nat.Prime i)^2 - 1) := by
  -- By the Chinese Remainder Theorem, the number of solutions modulo $W_r$ is the product of the number of solutions modulo each $p_i^2$.
  have h_crt : ∀ (rs : Finset ℕ), (Finset.filter (fun x => ∀ i ∈ rs, ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.Icc 1 (Finset.prod rs (fun i => Nat.nth Nat.Prime i ^ 2)))).card = ∏ i ∈ rs, (Nat.nth Nat.Prime i ^ 2 - 1) := by
    intro rs
    have h_crt : ∀ (rs : Finset ℕ), (Finset.filter (fun x => ∀ i ∈ rs, ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.Icc 1 (Finset.prod rs (fun i => Nat.nth Nat.Prime i ^ 2)))).card = Finset.card (Finset.filter (fun x => ∀ i ∈ rs, ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.Ico 0 (Finset.prod rs (fun i => Nat.nth Nat.Prime i ^ 2)))) := by
      intro rs; rw [ Finset.card_filter, Finset.card_filter ] ; rw [ Finset.sum_Ico_eq_sum_range ] ;
      erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, Finset.sum_range_succ' ] ; ring_nf;
      rw [ Finset.card_filter, Finset.card_filter ];
      conv_rhs => rw [ ← Nat.sub_add_cancel ( show 1 ≤ ∏ x ∈ rs, Nat.nth Nat.Prime x ^ 2 from Finset.prod_pos fun _ _ => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ), Finset.sum_range_succ' ] ; simp +decide [ add_comm 1 ] ;
      rw [ ← Nat.sub_add_cancel ( show 1 ≤ ∏ x ∈ rs, Nat.nth Nat.Prime x ^ 2 from Finset.prod_pos fun _ _ => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ), Finset.sum_range_succ ] ; simp +decide [add_comm
            1] ; ring_nf;
      split_ifs <;> simp_all +decide;
      rename_i h₁ h₂; obtain ⟨ x, hx ⟩ := h₂; specialize h₁ x hx; simp_all +decide [Finset.prod_eq_prod_diff_singleton_mul
            hx] ;
      exact h₁ ( by rw [ add_tsub_cancel_of_le ( Nat.one_le_iff_ne_zero.mpr <| mul_ne_zero ( Finset.prod_ne_zero_iff.mpr fun y hy => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) <| pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) ] ; norm_num );
    induction' rs using Finset.induction with i rs hi ih;
    · norm_num;
    · have h_crt_step : Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)))) = Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2))) * Finset.card (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2))) := by
        have h_crt_step : Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)))) = Finset.card (Finset.image (fun x => (x % Nat.nth Nat.Prime i ^ 2, x % ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)) (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2))))) := by
          rw [ Finset.card_image_of_injOn ];
          intros x hx y hy hxy;
          have h_crt_step : x ≡ y [MOD Nat.nth Nat.Prime i ^ 2] ∧ x ≡ y [MOD ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2] := by
            aesop;
          have h_crt_step : x ≡ y [MOD (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)] := by
            rw [ Nat.modEq_and_modEq_iff_modEq_mul ] at h_crt_step ; aesop;
            refine' Nat.Coprime.prod_right fun j hj => _;
            simp +decide [Nat.Prime.coprime_iff_not_dvd, Nat.prime_dvd_prime_iff_eq];
            exact fun h => hi <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; aesop;
          exact Nat.mod_eq_of_lt ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ▸ Nat.mod_eq_of_lt ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hy |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ▸ h_crt_step;
        rw [ h_crt_step, show ( Finset.image ( fun x => ( x % Nat.nth Nat.Prime i ^ 2, x % ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) ( Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.filter ( fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x ) ( Finset.Ico 0 ( Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) ) ) ) = Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.Ico 0 ( Nat.nth Nat.Prime i ^ 2 ) ) ×ˢ Finset.filter ( fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x ) ( Finset.Ico 0 ( ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) from ?_ ];
        · exact Finset.card_product _ _;
        · ext ⟨x, y⟩; simp [Finset.mem_image];
          constructor;
          · rintro ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl, rfl ⟩;
            exact ⟨ ⟨ Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime i ) ) 2 ), by simpa [ Nat.dvd_iff_mod_eq_zero ] using ha₃ ⟩, Nat.mod_lt _ ( Finset.prod_pos fun j hj => pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime j ) ) 2 ), fun j hj => by simpa [ Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ ( Finset.dvd_prod_of_mem _ hj ) ] using ha₂ j hj ⟩;
          · intro hxy
            obtain ⟨a, ha⟩ : ∃ a, a ≡ x [MOD Nat.nth Nat.Prime i ^ 2] ∧ a ≡ y [MOD ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2] ∧ a < Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 := by
              have h_crt : Nat.gcd (Nat.nth Nat.Prime i ^ 2) (∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2) = 1 := by
                simp +decide [Nat.coprime_prod_right_iff, Nat.Prime.coprime_iff_not_dvd];
                intro j hj; rw [ Nat.prime_dvd_prime_iff_eq ] <;> norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
                exact fun h => hi <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; aesop;
              have := Nat.chineseRemainder h_crt x y;
              exact ⟨ this.val % ( Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2, Nat.mod_lt _ ( Nat.mul_pos ( pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime i ) ) 2 ) ( Finset.prod_pos fun j hj => pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime j ) ) 2 ) ) ⟩;
            use a;
            simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ];
            exact ⟨ fun j hj => by rw [ ← Nat.mod_mod_of_dvd a ( show Nat.nth Nat.Prime j ^ 2 ∣ ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 from Finset.dvd_prod_of_mem _ hj ) ] ; simp_all +decide [ Nat.mod_eq_of_lt ], Nat.mod_eq_of_lt hxy.1.1, Nat.mod_eq_of_lt hxy.2.1 ⟩;
      simp_all +decide [ Finset.prod_insert hi ];
      convert h_crt_step using 1;
      · convert h_crt ( Insert.insert i rs ) using 2 ; simp +decide [Finset.prod_insert hi];
        ext; simp +decide [ Finset.prod_insert hi, Finset.mem_filter, Finset.mem_range ] ; aesop;
      · rw [ show Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.range ( Nat.nth Nat.Prime i ^ 2 ) ) = Finset.range ( Nat.nth Nat.Prime i ^ 2 ) \ { 0 } from ?_, Finset.card_sdiff ] <;> norm_num;
        · rw [ Finset.inter_eq_left.mpr ] <;> norm_num;
          exact pow_pos ( Nat.Prime.pos ( by aesop ) ) _;
        · ext ( _ | x ) <;> simp +decide [ Nat.dvd_iff_mod_eq_zero ];
          exact fun h => by rw [ Nat.mod_eq_of_lt h ] ; norm_num;
  convert h_crt ( Finset.range r ) using 2;
  unfold S_r;
  unfold W; norm_num [ Finset.prod_pow ] ;

/-
The density of S_r in [1, W_r] tends to 6/pi^2 as r tends to infinity.
-/
lemma density_S_r_tendsto : Filter.Tendsto (fun r => ((S_r r).card : ℝ) / W r) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  -- The density is $\prod_{i < r} (1 - 1/p_i^2)$.
  have h_density : Filter.Tendsto (fun r => (∏ i ∈ Finset.range r, (1 - 1 / (Nat.nth Nat.Prime i : ℝ) ^ 2))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    -- Recognize that the product $\prod_{i=1}^\infty (1 - 1/p_i^2)$ converges to $1/\zeta(2)$, where $\zeta(2) = \pi^2/6$.
    have h_zeta : Filter.Tendsto (fun r => (∏ i ∈ Finset.range r, (1 - 1 / (Nat.nth Nat.Prime i : ℝ) ^ 2))) Filter.atTop (nhds (1 / (∑' n : ℕ, (1 / (n : ℝ) ^ 2)))) := by
      -- Apply the Euler product formula to the Riemann zeta function.
      have h_euler : ∏' p : Nat.Primes, (1 - (1 : ℝ) / p^2)⁻¹ = ∑' n : ℕ, (1 : ℝ) / n^2 := by
        have := @EulerProduct.eulerProduct_hasProd;
        specialize @this ℝ _ ( fun n => ( n : ℝ ) ⁻¹ ^ 2 ) _ _ _ _ <;> norm_num at *;
        · intro m n h; ring;
        · convert this.tprod_eq using 1;
          refine' tprod_congr fun p => _;
          ring_nf;
          norm_num [ pow_mul' ];
          rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ] ; norm_num;
      have h_prod_conv : Filter.Tendsto (fun r => (∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹)) Filter.atTop (nhds (∏' p : Nat.Primes, (1 - (1 : ℝ) / p^2)⁻¹)) := by
        have h_abs_conv : Summable (fun p : Nat.Primes => Real.log ((1 - (1 : ℝ) / p^2)⁻¹)) := by
          have h_abs_conv : Summable (fun p : Nat.Primes => (1 : ℝ) / p^2) := by
            exact Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _;
          have h_abs_conv : ∀ p : Nat.Primes, Real.log ((1 - (1 : ℝ) / p^2)⁻¹) ≤ 2 * (1 : ℝ) / p^2 := by
            intro p; rw [ Real.log_inv ] ; ring_nf; norm_num;
            nlinarith only [ Real.log_inv ( 1 - ( p ^ 2 : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show 0 < 1 - ( p ^ 2 : ℝ ) ⁻¹ by exact sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ) ), inv_mul_cancel₀ ( show ( 1 - ( p ^ 2 : ℝ ) ⁻¹ ) ≠ 0 by exact ne_of_gt ( sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ) ), inv_pos.mpr ( show 0 < ( p ^ 2 : ℝ ) by exact sq_pos_of_pos ( Nat.cast_pos.mpr p.2.pos ) ), inv_mul_cancel₀ ( show ( p ^ 2 : ℝ ) ≠ 0 by exact pow_ne_zero 2 ( Nat.cast_ne_zero.mpr p.2.ne_zero ) ), show ( p ^ 2 : ℝ ) ≥ 4 by exact_mod_cast Nat.pow_le_pow_left p.2.two_le 2 ];
          exact Summable.of_nonneg_of_le ( fun p => Real.log_nonneg <| by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le p.2, one_div_mul_cancel <| show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr p.2.ne_zero ] ) ( fun p => h_abs_conv p ) <| by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using Summable.mul_left 2 ‹Summable fun p : Nat.Primes => ( 1 : ℝ ) / p ^ 2›;
        have h_exp_conv : Filter.Tendsto (fun r => Real.exp (∑ i ∈ Finset.range r, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹))) Filter.atTop (nhds (Real.exp (∑' p : Nat.Primes, Real.log ((1 - (1 : ℝ) / p^2)⁻¹)))) := by
          refine' Real.continuous_exp.continuousAt.tendsto.comp _;
          have h_exp_conv : Filter.Tendsto (fun r => ∑ i ∈ Finset.range r, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹)) Filter.atTop (nhds (∑' p : ℕ, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime p)^2)⁻¹))) := by
            refine' ( Summable.hasSum _ ) |> HasSum.tendsto_sum_nat;
            convert h_abs_conv.comp_injective ( show Function.Injective ( fun i : ℕ => ⟨ Nat.nth Nat.Prime i, Nat.prime_nth_prime i ⟩ : ℕ → Nat.Primes ) from fun i j hij => by simpa using Nat.nth_injective ( Nat.infinite_setOf_prime ) <| Subtype.ext_iff.mp hij ) using 1;
          convert h_exp_conv using 1;
          rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun p : ℕ => ⟨ Nat.nth Nat.Prime p, Nat.prime_nth_prime p ⟩ ) ⟨ fun p => ?_, fun p => ?_ ⟩ ) ];
          all_goals norm_num [ Nat.nth_injective ];
          · exact fun q h => Nat.nth_injective ( Nat.infinite_setOf_prime ) <| by injection h;
          · use Nat.count ( Nat.Prime ) p.val;
            exact Subtype.ext <| Nat.nth_count p.2;
        convert h_exp_conv using 2;
        · rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( inv_pos.mpr <| sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ) two_ne_zero ) ];
        · have h_exp_conv : ∀ {f : Nat.Primes → ℝ}, (∀ p : Nat.Primes, 0 < f p) → Summable (fun p : Nat.Primes => Real.log (f p)) → ∏' p : Nat.Primes, f p = Real.exp (∑' p : Nat.Primes, Real.log (f p)) := by
            exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1);
          exact h_exp_conv ( fun p => inv_pos.mpr <| sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) h_abs_conv;
      convert h_prod_conv.inv₀ _ using 1;
      · norm_num [ Finset.prod_inv_distrib ];
      · aesop;
      · exact h_euler.symm ▸ by exact ne_of_gt ( by exact lt_of_lt_of_le ( by positivity ) ( Summable.le_tsum ( by exact Real.summable_one_div_nat_pow.2 one_lt_two ) 1 ( by intros; positivity ) ) ) ;
    convert h_zeta using 2 ; have := hasSum_zeta_two ; have := this.tsum_eq ; norm_num at * ; aesop;
  convert h_density using 2 ; norm_num [ card_S_r, W ];
  rw [ ← Finset.prod_pow ] ; rw [ ← Finset.prod_div_distrib ] ; exact Finset.prod_congr rfl fun _ _ => by rw [ Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ] ; norm_num ; ring_nf ; norm_num [ Nat.Prime.ne_zero <| Nat.prime_nth_prime ‹_› ] ;

/-
T_finset is the set of integers n in [1, N] such that n is congruent to some element of S_r modulo W_r.
-/
def T_finset (N r : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => (if n % W r = 0 then W r else n % W r) ∈ S_r r)

/-
Elements in T_finset are not divisible by the square of any of the first r primes.
-/
lemma T_finset_squarefree_prop (N r : ℕ) (n : ℕ) (hn : n ∈ T_finset N r) :
    ∀ i ∈ Finset.range r, ¬ (Nat.nth Nat.Prime i)^2 ∣ n := by
      intro i hi;
      -- By definition of $T_{\text{finset}}$, if $n \in T_{\text{finset}}(N, r)$, then $n \pmod{W_r} \in S_r$.
      have h_mod : (if n % W r = 0 then W r else n % W r) ∈ S_r r := by
        exact Finset.mem_filter.mp hn |>.2;
      -- By definition of $S_r$, if $n \pmod{W_r} \in S_r$, then $n \pmod{W_r}$ is not divisible by $p_i^2$ for any $i < r$.
      have h_not_div : ¬(Nat.nth Nat.Prime i)^2 ∣ (if n % W r = 0 then W r else n % W r) := by
        unfold S_r at h_mod; aesop;
      split_ifs at h_not_div <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      · contrapose! h_not_div;
        exact Nat.mod_eq_zero_of_dvd <| dvd_trans ( by norm_num ) <| pow_dvd_pow_of_dvd ( Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi ) 2;
      · rwa [ Nat.mod_mod_of_dvd _ ( show Nat.nth Nat.Prime i ^ 2 ∣ W r from dvd_trans ( pow_dvd_pow_of_dvd ( Nat.dvd_of_mod_eq_zero <| by rw [ Nat.mod_eq_zero_of_dvd ] ; exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr hi ) ) _ ) ( dvd_refl _ ) ) ] at h_not_div

/-
If an element in T_finset is not squarefree, it must be divisible by the square of a prime greater than or equal to the r-th prime.
-/
lemma non_squarefree_in_T_implies_large_prime_sq_dvd (N r : ℕ) (n : ℕ) (hn : n ∈ T_finset N r) (hns : ¬ Squarefree n) :
    ∃ p, Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r ∧ p^2 ∣ n := by
      obtain ⟨ p, hp_prime, hp_div ⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n := by
        rw [ Nat.squarefree_iff_prime_squarefree ] at hns;
        simpa [ sq ] using hns;
      by_cases hp_lt : p < Nat.nth Nat.Prime r;
      · obtain ⟨ i, hi ⟩ : ∃ i < r, p = Nat.nth Nat.Prime i := by
          refine' ⟨ Nat.count ( Nat.Prime ) p, _, _ ⟩;
          · contrapose! hp_lt;
            rw [ Nat.nth_eq_sInf ];
            refine' Nat.sInf_le ⟨ hp_prime, _ ⟩;
            intro k hk; exact Nat.nth_lt_of_lt_count <| by linarith;
          · rw [ Nat.nth_count ] ; aesop;
        have := T_finset_squarefree_prop N r n hn i ( Finset.mem_range.mpr hi.1 ) ; aesop;
      · exact ⟨ p, hp_prime, le_of_not_gt hp_lt, hp_div ⟩

/-
For any c > 0, there exists an r such that the number of non-squarefree elements in T_finset(N, r) is at most c * N for all N.
-/
lemma card_non_squarefree_in_T_bound (c : ℝ) (hc : c > 0) :
    ∃ r, ∀ N, ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ c * N := by
      -- By the properties of the Möbius function and the definition of $T_finset$, we can bound the number of non-squarefree elements in $T_finset(N, r)$.
      have h_bound : ∀ r N : ℕ, ((Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card : ℝ) ≤ N * (∑' p : ℕ, if (Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r) then (1 / (p : ℝ)^2) else 0) := by
        intros r N
        have h_non_squarefree_bound : ((Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N), (N / p^2 : ℝ) := by
          have h_non_squarefree_bound : ((Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N), ((Finset.filter (fun n => p^2 ∣ n) (T_finset N r)).card : ℝ) := by
            have h_non_squarefree_bound : ((Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N), ((Finset.filter (fun n => p^2 ∣ n) (T_finset N r)).card : ℝ) := by
              have h_non_squarefree_bound : ∀ n ∈ T_finset N r, ¬Squarefree n → ∃ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N), p^2 ∣ n := by
                intros n hn hns
                obtain ⟨p, hp_prime, hp_ge, hp_sq⟩ : ∃ p, Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r ∧ p^2 ∣ n := by
                  exact non_squarefree_in_T_implies_large_prime_sq_dvd N r n hn hns;
                norm_num +zetaDelta at *;
                exact ⟨ p, ⟨ ⟨ hp_ge, by nlinarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hn ( by unfold T_finset; aesop ) ) ) hp_sq, show n ≤ N from Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ] ⟩, hp_prime ⟩, hp_sq ⟩
              have h_non_squarefree_bound : (Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card ≤ Finset.card (Finset.biUnion (Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N)) (fun p => Finset.filter (fun n => p^2 ∣ n) (T_finset N r))) := by
                exact Finset.card_le_card fun x hx => by aesop;
              exact_mod_cast h_non_squarefree_bound.trans ( Finset.card_biUnion_le );
            convert h_non_squarefree_bound using 1;
          refine le_trans h_non_squarefree_bound <| Finset.sum_le_sum fun p hp => ?_;
          -- The number of multiples of $p^2$ in $[1, N]$ is at most $N / p^2$.
          have h_multiples_bound : ((Finset.filter (fun n => p^2 ∣ n) (Finset.Icc 1 N)).card : ℝ) ≤ N / p^2 := by
            have h_multiples_bound : ((Finset.filter (fun n => p^2 ∣ n) (Finset.Icc 1 N)).card : ℝ) ≤ Finset.card (Finset.image (fun n => p^2 * n) (Finset.Icc 1 (N / p^2))) := by
              exact_mod_cast Finset.card_mono fun x hx => Finset.mem_image.mpr ⟨ x / p ^ 2, Finset.mem_Icc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) ) ( pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ), Nat.div_le_div_right ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ⟩, Nat.mul_div_cancel' ( Finset.mem_filter.mp hx |>.2 ) ⟩;
            exact h_multiples_bound.trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) hxy ] ; simpa using Nat.cast_div_le .. |> le_trans <| by norm_num );
          exact le_trans ( mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.filter_subset _ _ ) h_multiples_bound;
        refine le_trans h_non_squarefree_bound ?_;
        rw [ ← tsum_mul_left ];
        refine' le_trans _ ( Summable.sum_le_tsum ( Finset.Icc ( Nat.nth Nat.Prime r ) N ) ( fun _ _ => by positivity ) _ );
        · rw [ Finset.sum_filter ] ; exact Finset.sum_le_sum fun x hx => by aesop;
        · exact Summable.mul_left _ <| Summable.of_nonneg_of_le ( fun x => by positivity ) ( fun x => by aesop ) <| Real.summable_one_div_nat_pow.2 one_lt_two;
      -- Since $\sum_{p \ge p_r} \frac{1}{p^2}$ converges, the tail sum tends to 0.
      have h_tail_zero : Filter.Tendsto (fun r => ∑' p : ℕ, if (Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r) then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds 0) := by
        have h_tail_zero : Filter.Tendsto (fun r => ∑' p : ℕ, if (Nat.Prime p ∧ p ≥ r) then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds 0) := by
          convert tendsto_sum_nat_add fun p => ( if Nat.Prime p then ( p ^ 2 : ℝ ) ⁻¹ else 0 ) using 1;
          ext r; rw [ ← Summable.sum_add_tsum_nat_add r ] ; norm_num [ add_comm, add_left_comm, add_assoc ] ;
          · exact Finset.sum_eq_zero fun x hx => if_neg <| not_and_of_not_right _ <| by linarith [ Finset.mem_range.mp hx ] ;
          · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
        exact h_tail_zero.comp <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) |> StrictMono.tendsto_atTop;
      have := h_tail_zero.eventually ( gt_mem_nhds hc ) ; obtain ⟨ r, hr ⟩ := this.exists; exact ⟨ r, fun N => by nlinarith [ h_bound r N ] ⟩ ;

/-
There exists a residue class l modulo W_r such that the number of elements in A congruent to l modulo W_r is large.
-/
def A_l (A : Set ℕ) (N r l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 2 * W r)).filter (fun a => a ∈ A ∧ a % W r = l)

lemma exists_l_large_A_l (A : Set ℕ) (N r : ℕ) (δ : ℝ) (hr : W r > 0)
    (h_card : ((Finset.Icc 1 (N - 2 * W r)).filter (fun a => a ∈ A)).card > δ * N / 2) :
    ∃ l < W r, ((A_l A N r l).card : ℝ) > δ * N / (2 * W r) := by
      contrapose! h_card;
      -- The set $A \cap [1, N - 2W_r]$ is partitioned into $W_r$ sets $A_l$ based on the residue modulo $W_r$.
      have h_partition : (Finset.filter (fun a => a ∈ A) (Finset.Icc 1 (N - 2 * W r))).card = ∑ l ∈ Finset.range (W r), (A_l A N r l).card := by
        rw [ ← Finset.card_biUnion ];
        · congr with x ; simp +decide [ A_l ];
          exact fun _ _ _ => Nat.mod_lt _ hr;
        · intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left, A_l ] ;
      convert Finset.sum_le_sum fun i hi => h_card i ( Finset.mem_range.mp hi ) using 1;
      · exact_mod_cast h_partition;
      · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hr.ne' ]

/-
The translate of A_l by W_r + s - l is contained in T_finset.
-/
def translate_set (A : Set ℕ) (N r l s : ℕ) : Finset ℕ :=
  (A_l A N r l).image (fun a => W r + s - l + a)

lemma translates_subset_T (A : Set ℕ) (N r l : ℕ) (s : ℕ)
    (hs : s ∈ S_r r) (hl : l < W r) :
    translate_set A N r l s ⊆ T_finset N r := by
      intro x hx;
      obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx;
      -- Since $a \equiv l \pmod{W_r}$, we have $W_r + s - l + a \equiv s \pmod{W_r}$.
      have h_mod : (W r + s - l + a) % W r = s % W r := by
        have h_mod : a % W r = l % W r := by
          unfold A_l at ha; aesop;
        simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show l ≤ W r + s from by linarith ) ];
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      -- Since $s \in S_r$, we have $s \in [1, W_r]$ and $s$ satisfies the condition. Thus, $W_r + s - l + a \in T_finset N r$.
      have h_range : 1 ≤ W r + s - l + a ∧ W r + s - l + a ≤ N := by
        have h_bounds : 1 ≤ a ∧ a ≤ N - 2 * W r := by
          unfold A_l at ha; aesop;
        have h_bounds_s : s ≤ W r := by
          exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hs |>.1 ) |>.2;
        omega;
      have h_range : (if (W r + s - l + a) % W r = 0 then W r else (W r + s - l + a) % W r) ∈ S_r r := by
        split_ifs <;> simp_all +decide;
        · rw [ eq_comm, ← Nat.dvd_iff_mod_eq_zero ] at h_mod;
          contrapose! h_mod; simp_all +decide [ S_r ] ;
          exact Nat.not_dvd_of_pos_of_lt hs.1.1 ( lt_of_le_of_ne hs.1.2 ( by aesop ) );
        · convert hs using 1;
          exact Nat.mod_eq_of_lt ( show s < W r from lt_of_le_of_ne ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hs |>.1 ) |>.2 ) fun con => by aesop );
      exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ‹_›, h_range ⟩

/-
The translates of A_l by different shifts s1 and s2 are disjoint.
-/
lemma translates_disjoint (A : Set ℕ) (N r l : ℕ) (s1 s2 : ℕ)
    (hs1 : s1 ∈ S_r r) (hs2 : s2 ∈ S_r r) (hneq : s1 ≠ s2) :
    Disjoint (translate_set A N r l s1) (translate_set A N r l s2) := by
      unfold S_r at *; simp_all +decide [ Finset.disjoint_left ] ;
      intros x hx1 hx2; unfold translate_set at *; simp_all +decide ;
      obtain ⟨ a, ha, rfl ⟩ := hx1; obtain ⟨ b, hb, hb' ⟩ := hx2; simp_all +decide [ A_l ] ;
      -- Since $a \equiv b \equiv l \pmod{W_r}$, we have $s1 \equiv s2 \pmod{W_r}$.
      have h_mod : s1 % W r = s2 % W r := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
        have h_mod : (W r + s2 - l + b : ℤ) ≡ (W r + s1 - l + a : ℤ) [ZMOD W r] := by
          norm_cast;
          rw [ Int.subNatNat_of_le, Int.subNatNat_of_le ] <;> norm_cast;
          · rw [hb'];
          · exact ha.2.2 ▸ Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) ) |> le_trans <| by linarith;
          · exact ha.2.2 ▸ Nat.le_of_lt ( Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop ) ) ) |> le_trans <| by linarith;
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        rw [ ← Nat.mod_add_div a ( W r ), ← Nat.mod_add_div b ( W r ) ] at *; simp_all +decide ;
      have := Nat.modEq_iff_dvd.mp h_mod.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      obtain ⟨ k, hk ⟩ := this; exact hneq <| by nlinarith [ show k = 0 by nlinarith ] ;

/-
The cardinality of a translate of A_l is equal to the cardinality of A_l.
-/
lemma card_translate_set (A : Set ℕ) (N r l s : ℕ) :
    (translate_set A N r l s).card = (A_l A N r l).card := by
      -- The function $a \mapsto W_r + s - l + a$ is injective, so the cardinality of the image is equal to the cardinality of the domain.
      have h_inj : Function.Injective (fun a => W r + s - l + a) := by
        exact add_right_injective _;
      exact Finset.card_image_of_injective _ h_inj

/-
Under certain conditions, there exists a shift s in S_r such that the translate of A_l by s contains many squarefree numbers.
-/
lemma exists_s_many_squarefree (A : Set ℕ) (N r l : ℕ) (δ : ℝ)
    (h_card_Al : ((A_l A N r l).card : ℝ) > δ * N / (2 * W r))
    (h_Sr_large : ((S_r r).card : ℝ) > (W r : ℝ) / 2)
    (h_non_sq : ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ (δ / 8) * N)
    (hl : l < W r)
    (hWr_pos : W r > 0) :
    ∃ s ∈ S_r r, ((translate_set A N r l s).filter Squarefree).card > (δ * N) / (8 * (S_r r).card) := by
      -- Let $U = \bigcup_{s \in S_r} \text{translate\_set}(s)$.
      set U := Finset.biUnion (S_r r) (fun s => translate_set A N r l s) with hU_def;
      -- Since translates are disjoint, $|U| = |S_r| |A_l|$.
      have hU_card : (U.card : ℝ) = (S_r r).card * (A_l A N r l).card := by
        rw [ Finset.card_biUnion ];
        · simp +decide [ card_translate_set ];
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => Finset.disjoint_left.mp ( translates_disjoint A N r l x y ( by aesop ) ( by aesop ) hxy ) hz₁ hz₂;
      -- Number of squarefree in $U$ is $|U| - |U \cap \text{non-sq}| \ge |U| - |T \cap \text{non-sq}| > \delta N / 4 - \delta N / 8 = \delta N / 8$.
      have h_squarefree_U : ((U.filter Squarefree).card : ℝ) > δ * N / 8 := by
        have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≥ (U.card : ℝ) - ((T_finset N r).filter (fun n => ¬ Squarefree n)).card := by
          have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≥ (U.card : ℝ) - ((U.filter (fun n => ¬ Squarefree n)).card : ℝ) := by
            rw [ show ( Finset.filter Squarefree U ) = U \ ( Finset.filter ( fun n => ¬Squarefree n ) U ) by ext; aesop, Finset.card_sdiff ] ; norm_num;
            rw [ Nat.cast_sub ] <;> norm_num [ Finset.filter_inter ] ; exact Finset.card_le_card fun x hx => by aesop;
          refine le_trans ?_ h_squarefree_U;
          gcongr;
          exact Finset.biUnion_subset.mpr fun s hs => translates_subset_T A N r l s hs ( by aesop );
        rw [ gt_iff_lt, div_lt_iff₀ ] at * <;> nlinarith [ show ( W r : ℝ ) > 0 by positivity ];
      contrapose! h_squarefree_U;
      have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≤ ∑ s ∈ S_r r, ((translate_set A N r l s).filter Squarefree).card := by
        rw [ Finset.filter_biUnion ];
        exact_mod_cast Finset.card_biUnion_le;
      simp +zetaDelta at *;
      refine le_trans h_squarefree_U <| le_trans ( Finset.sum_le_sum ‹_› ) ?_;
      norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ne_of_gt ( show 0 < ( S_r r |> Finset.card : ℝ ) from lt_of_le_of_lt ( by positivity ) h_Sr_large ) ]

/-
If for arbitrarily large N there is a shift n in a finite set S such that the number of squarefree translates is proportional to N, then there is a shift n in S for which there are infinitely many squarefree translates.
-/
lemma infinite_squarefree_of_frequent_dense_shifts (A : Set ℕ) (S : Finset ℕ) (c : ℝ) (hc : c > 0)
    (h_inf : ∀ k, ∃ N ≥ k, ∃ n ∈ S, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N) :
    ∃ n ∈ S, ({a ∈ A | Squarefree (n + a)}).Infinite := by
      by_contra h_contra;
      -- Since $S$ is finite, by the infinite pigeonhole principle, there exists an $n \in S$ such that for infinitely many $N$, the count is $> c N$.
      obtain ⟨n, hnS, hn_inf⟩ : ∃ n ∈ S, Set.Infinite {N | ∃ N' ≥ N, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N'))) > c * N'} := by
        by_cases h_finite : ∀ n ∈ S, Set.Finite {N | ∃ N' ≥ N, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N'))) > c * N'};
        · exact absurd ( Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet S ) h_finite ) fun x hx => by aesop ) ( Set.infinite_univ.mono fun x _ => by obtain ⟨ N, hN₁, n, hn₁, hn₂ ⟩ := h_inf x; exact ⟨ n, hn₁, N, hN₁, hn₂ ⟩ );
        · aesop;
      -- Since the set of a in A such that n + a is squarefree is finite, there exists some maximum element M in this set.
      obtain ⟨M, hM⟩ : ∃ M, ∀ a ∈ {a | a ∈ A ∧ Squarefree (n + a)}, a ≤ M := by
        exact Set.Finite.bddAbove <| Classical.not_not.1 fun h => h_contra ⟨ n, hnS, h ⟩;
      -- For any $N > M$, the number of elements in $A$ up to $N$ that are squarefree when added to $n$ is at most $M$.
      have h_card_le_M : ∀ N > M, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N))) ≤ M := by
        exact fun N hN => le_trans ( Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, hM x <| Finset.mem_filter.mp hx |>.2 ⟩ ) ( by simp );
      -- Choose $N$ large enough such that $cN > M$.
      obtain ⟨N, hN⟩ : ∃ N, N > M ∧ c * N > M := by
        exact ⟨ ⌊M / c⌋₊ + M + 1, by linarith, by push_cast; nlinarith [ Nat.lt_floor_add_one ( M / c ), mul_div_cancel₀ ( M : ℝ ) hc.ne' ] ⟩;
      obtain ⟨ N', hN'₁, hN'₂ ⟩ := hn_inf.exists_gt N;
      obtain ⟨ N'', hN''₁, hN''₂ ⟩ := hN'₁;
      exact hN''₂.not_ge ( le_trans ( Nat.cast_le.mpr ( h_card_le_M N'' ( by linarith ) ) ) ( by nlinarith [ show ( N'' : ℝ ) ≥ N by norm_cast; linarith ] ) )

/-
For a given N, if A has large intersection with [1, N-2W_r], then there exists a shift n in S_shifts(r) such that n+A has many squarefree elements in [1, N].
-/
def S_shifts (r : ℕ) : Finset ℕ :=
  (Finset.product (Finset.range (W r)) (S_r r)).image (fun p => W r + p.2 - p.1)

lemma exists_good_shift_for_N (A : Set ℕ) (N r : ℕ) (δ : ℝ)
    (hr : W r > 0)
    (h_Sr_large : ((S_r r).card : ℝ) > (W r : ℝ) / 2)
    (h_non_sq : ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ (δ / 8) * N)
    (h_card : ((Finset.Icc 1 (N - 2 * W r)).filter (fun a => a ∈ A)).card > δ * N / 2) :
    ∃ n ∈ S_shifts r, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > (δ * N) / (8 * (S_r r).card) := by
      -- By `exists_l_large_A_l`, there exists $l < W_r$ such that $|A_l| > \delta N / (2 W_r)$.
      obtain ⟨l, hl₁, hl₂⟩ : ∃ l < W r, ((A_l A N r l).card : ℝ) > δ * N / (2 * W r) := by
        exact exists_l_large_A_l A N r δ hr h_card;
      -- By `exists_s_many_squarefree`, there exists $s \in S_r$ such that the translate of $A_l$ by $n = W_r + s - l$ has $> \delta N / (8 |S_r|)$ squarefree elements.
      obtain ⟨s, hs₁, hs₂⟩ : ∃ s ∈ S_r r, ((translate_set A N r l s).filter Squarefree).card > δ * N / (8 * (S_r r).card) := by
        apply exists_s_many_squarefree;
        all_goals norm_cast at *;
      refine' ⟨ W r + s - l, _, _ ⟩ <;> simp_all +decide [ S_shifts ];
      · exact ⟨ l, s, ⟨ hl₁, hs₁ ⟩, rfl ⟩;
      · refine' hs₂.trans_le ( mod_cast _ );
        refine' le_trans ( Finset.card_le_card <| show Finset.filter Squarefree ( translate_set A N r l s ) ⊆ Finset.image ( fun a => W r + s - l + a ) ( Finset.filter ( fun a => a ∈ A ∧ Squarefree ( W r + s - l + a ) ) ( Finset.Icc 1 ( N - 2 * W r ) ) ) from _ ) _;
        · simp +decide [ Finset.subset_iff, translate_set ];
          unfold A_l; aesop;
        · rw [ Finset.card_image_of_injective _ fun x y hxy => by linarith [ Nat.sub_add_cancel ( show l ≤ W r + s from by linarith ) ] ] ; gcongr ; aesop;

/-
If the upper density of A is delta > 0, then for any constant C and any k, there exists N >= k such that the number of elements of A in [1, N-C] is greater than (delta/2) * N.
-/
lemma exists_large_N_with_density (A : Set ℕ) (δ : ℝ) (hδ : upperDensity A = δ) (hδ_pos : δ > 0) (C : ℕ) :
    ∀ k, ∃ N ≥ k, ((Finset.Icc 1 (N - C)).filter (fun a => a ∈ A)).card > (δ / 2) * N := by
      have h_upper_density : ∀ ε > 0, ∃ k, ∀ N ≥ k, ∃ n ≥ N, ((Finset.Icc 1 n).filter (fun a => a ∈ A)).card ≥ (δ - ε) * n := by
        intro ε hε_pos
        have h_upper_density : ∀ ε > 0, ∃ k, ∀ N ≥ k, ∃ n ≥ N, ((Finset.Icc 1 n).filter (fun a => a ∈ A)).card / (n : ℝ) ≥ δ - ε := by
          intro ε hε_pos
          have h_lim_sup : Filter.limsup (fun n => ((Finset.Icc 1 n).filter (fun a => a ∈ A)).card / (n : ℝ)) Filter.atTop = δ := by
            convert hδ using 1;
            unfold upperDensity;
            norm_num [ Set.ncard_eq_toFinset_card' ]
          contrapose! h_lim_sup;
          refine' ne_of_lt ( lt_of_le_of_lt ( csInf_le _ _ ) _ );
          exact δ - ε;
          · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN N le_rfl ) ⟩;
          · exact Filter.eventually_atTop.mpr ( by obtain ⟨ N, hN₁, hN₂ ⟩ := h_lim_sup 0; exact ⟨ N, fun n hn => le_of_lt ( hN₂ n hn ) ⟩ );
          · linarith;
        exact Exists.elim ( h_upper_density ε hε_pos ) fun k hk => ⟨ k + 1, fun N hN => by obtain ⟨ n, hn₁, hn₂ ⟩ := hk N ( by linarith ) ; exact ⟨ n, hn₁, by rw [ ge_iff_le, le_div_iff₀ ( Nat.cast_pos.mpr <| by linarith ) ] at hn₂; linarith ⟩ ⟩ ;
      intro k
      obtain ⟨k', hk'⟩ : ∃ k', ∀ N ≥ k', ∃ n ≥ N, ((Finset.Icc 1 n).filter (fun a => a ∈ A)).card ≥ (δ - δ / 4) * n := h_upper_density (δ / 4) (by linarith);
      obtain ⟨ n, hn₁, hn₂ ⟩ := hk' ( k' + k + 4 * C + 1 ) ( by linarith );
      refine' ⟨ n + C, by linarith, _ ⟩ ; norm_num at *;
      nlinarith [ show ( n : ℝ ) ≥ k' + k + 4 * C + 1 by norm_cast ]

/-
For any delta > 0, there exists an r such that the density of S_r is > 1/2 and the number of non-squarefree elements in T(N, r) is small (<= delta/8 * N).
-/
lemma exists_suitable_r (δ : ℝ) (hδ : δ > 0) :
    ∃ r, ((S_r r).card : ℝ) > (W r : ℝ) / 2 ∧ ∀ N, ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ (δ / 8) * N := by
      -- Since the product of (1 - 1/p^2) for the first r primes is greater than 1/2 for any r, we can choose r=0.
      have h_density : ∀ r, ((S_r r).card : ℝ) > (W r : ℝ) / 2 := by
        intro r
        have h_prod : ∏ i ∈ Finset.range r, (1 - 1 / (Nat.nth Nat.Prime i : ℝ) ^ 2) > 1 / 2 := by
          have h_prod_gt_half : Filter.Tendsto (fun r => ∏ i ∈ Finset.range r, (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
            have := density_S_r_tendsto;
            convert this using 2;
            rw [ show ( S_r _ : Finset ℕ ).card = ∏ i ∈ Finset.range _, ( ( Nat.nth Nat.Prime i ) ^ 2 - 1 ) from ?_, show ( W _ : ℕ ) = ∏ i ∈ Finset.range _, ( Nat.nth Nat.Prime i ) ^ 2 from ?_ ];
            any_goals exact ‹ℕ›;
            · norm_num [ Nat.cast_sub ( Nat.one_le_pow _ _ ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) ) ) ];
              rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ] ; intros ; rw [ inv_eq_one_div, sub_div, div_self ] ; norm_cast ; exact pow_ne_zero _ <| Nat.Prime.ne_zero <| by aesop;
            · unfold W; norm_num [ Finset.prod_pow ] ;
            · (expose_names; exact card_S_r x);
          have h_prod_gt_half : ∀ r, ∏ i ∈ Finset.range r, (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) ≥ 6 / Real.pi ^ 2 := by
            intro r
            have h_prod_gt_half : ∀ r, ∏ i ∈ Finset.range r, (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) ≥ ∏ i ∈ Finset.range (r + 1), (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) := by
              norm_num [ Finset.prod_range_succ ];
              exact fun r => mul_le_of_le_one_right ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ) <| sub_le_self _ <| inv_nonneg.2 <| sq_nonneg _;
            exact le_of_tendsto ‹_› ( Filter.eventually_atTop.mpr ⟨ r, fun n hn => by induction hn <;> [ tauto; linarith [ h_prod_gt_half ‹_› ] ] ⟩ );
          refine' lt_of_lt_of_le _ ( h_prod_gt_half r );
          rw [ div_lt_div_iff₀ ] <;> nlinarith only [ Real.pi_gt_three, show Real.pi < 3.4 by pi_upper_bound [ 7 / 5 ] ];
        -- By definition of $S_r$, we know that $|S_r| = W_r \prod_{i=1}^r (1 - 1/p_i^2)$.
        have h_card_S_r : (S_r r).card = (W r : ℝ) * ∏ i ∈ Finset.range r, (1 - 1 / (Nat.nth Nat.Prime i : ℝ) ^ 2) := by
          have h_card_S_r : (S_r r).card = ∏ i ∈ Finset.range r, ((Nat.nth Nat.Prime i)^2 - 1) := by
            exact card_S_r r;
          simp_all +decide;
          rw [ Finset.prod_congr rfl fun _ _ => Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ] ; norm_num [ Finset.prod_mul_distrib, W ];
          rw [ ← Finset.prod_pow ] ; rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_congr rfl fun _ _ => by nlinarith only [ mul_inv_cancel₀ ( show ( Nat.nth Nat.Prime ‹_› : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop ) ] ;
        nlinarith [ show ( W r : ℝ ) > 0 from mod_cast pow_pos ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) ) 2 ];
      exact Exists.elim ( card_non_squarefree_in_T_bound ( δ / 8 ) ( by positivity ) ) fun r hr => ⟨ r, h_density r, hr ⟩

/-
If A has positive upper density, then there exists a finite set of shifts (S_shifts r) and a constant c > 0 such that for arbitrarily large N, one of the shifts produces more than c*N squarefree translates.
-/
lemma frequent_dense_shifts_of_positive_density (A : Set ℕ) (h_density : upperDensity A > 0) :
    ∃ r, ∃ c : ℝ, c > 0 ∧ ∀ k, ∃ N ≥ k, ∃ n ∈ S_shifts r, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N := by
      obtain ⟨r, hr⟩ : ∃ r : ℕ, ((S_r r).card : ℝ) > (W r : ℝ) / 2 ∧ ∀ N : ℕ, ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ (upperDensity A / 8) * N := by
        exact exists_suitable_r (upperDensity A) h_density;
      refine' ⟨ r, upperDensity A / ( 8 * ( S_r r |> Finset.card ) ), _, fun k => _ ⟩;
      · exact div_pos h_density ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ 1, by
          refine' Finset.mem_filter.mpr ⟨ _, _ ⟩ <;> norm_num [ W ];
          · exact Nat.one_le_pow _ _ ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) );
          · exact fun i hi => Nat.Prime.ne_one <| Nat.prime_nth_prime i ⟩ ) ) );
      · obtain ⟨ N, hN₁, hN₂ ⟩ := exists_large_N_with_density A ( upperDensity A ) rfl h_density ( 2 * W r ) k;
        have := exists_good_shift_for_N A N r ( upperDensity A ) ?_ ?_ ?_ ?_ <;> norm_num at *;
        · exact ⟨ N, hN₁, this.choose, this.choose_spec.1, by convert this.choose_spec.2 using 1; ring ⟩;
        · exact pow_pos ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) ) _;
        · exact hr.1;
        · exact hr.2 N;
        · linarith

/-
If a strictly increasing sequence A has natural density 0, then A(j)/j tends to infinity.
-/
lemma tendsto_div_of_density_zero (A : ℕ → ℕ) (h_inc : StrictMono A) (h_dens : HasNaturalDensity (Set.range A) 0) : Filter.Tendsto (fun j => (A j : ℝ) / j) Filter.atTop Filter.atTop := by
  -- Since $A$ is strictly increasing, $A(j) \ge j$. The number of elements of $S$ in $[1, x]$ is approximately $A^{-1}(x)$. Specifically, $|S \cap [1, A(j)]| = j+1$ (assuming $A(0) \ge 1$, or similar).
  have h_card : ∀ j : ℕ, j ≥ 1 → ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ j := by
    intros j hj
    have h_range : Set.range A ∩ Set.Icc 1 (A j) ⊇ Finset.image A (Finset.Icc 1 j) := by
      simp +decide [ Set.subset_def ];
      exact fun x y hy₁ hy₂ hx => ⟨ ⟨ y, hx ⟩, hx ▸ Nat.one_le_iff_ne_zero.mpr ( by linarith [ h_inc <| show 0 < y from hy₁ ] ), hx ▸ h_inc.monotone hy₂ ⟩;
    refine' mod_cast le_trans _ ( Set.ncard_le_ncard h_range );
    rw [ Set.ncard_coe_finset, Finset.card_image_of_injective _ h_inc.injective ] ; aesop;
  -- This implies $A(j) / (j+1) \to \infty$, so $A(j) / j \to \infty$.
  have h_lim : Filter.Tendsto (fun j : ℕ => ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) / (A j)) Filter.atTop (nhds 0) := by
    exact h_dens.comp h_inc.tendsto_atTop;
  -- Since $|S \cap [1, A(j)]| \ge j$, we have $j / A(j) \le |S \cap [1, A(j)]| / A(j)$.
  have h_le : ∀ j : ℕ, j ≥ 1 → (j : ℝ) / (A j) ≤ ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) / (A j) := by
    bound;
  -- Since $j / A(j) \le |S \cap [1, A(j)]| / A(j)$ and $|S \cap [1, A(j)]| / A(j) \to 0$, it follows that $j / A(j) \to 0$.
  have h_j_div_A_j_zero : Filter.Tendsto (fun j : ℕ => (j : ℝ) / (A j)) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun j hj => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_le j hj ⟩ ) h_lim;
  have h_j_div_A_j_zero : Filter.Tendsto (fun j : ℕ => (A j : ℝ) / j) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun j : ℕ => (j : ℝ) / (A j)) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [ tendsto_nhdsWithin_iff ];
      exact ⟨ h_j_div_A_j_zero, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by simpa using div_pos ( Nat.cast_pos.mpr hn ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by linarith [ h_inc hn ] ) ) ) ⟩ ⟩
    have : Filter.Tendsto (fun j : ℕ => ((j : ℝ) / (A j))⁻¹) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.inv_tendsto_nhdsGT_zero this;
    aesop;
  convert h_j_div_A_j_zero using 1

/-
If a set A has property P, then it has natural density 0.
-/
theorem Theorem1_i (A : Set ℕ) (hA : PropertyP A) : HasNaturalDensity A 0 := by
  -- Apply the lemma frequent_dense_shifts_of_positive_density to get the existence of r and c, then use infinite_squarefree_of_frequent_dense_shifts to get the contradiction.
  by_contra h_contra
  obtain ⟨r, c, hc_pos, h_freq⟩ : ∃ r, ∃ c : ℝ, c > 0 ∧ ∀ k, ∃ N ≥ k, ∃ n ∈ S_shifts r, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N := by
    convert frequent_dense_shifts_of_positive_density A _;
    unfold upperDensity;
    refine' lt_of_not_ge fun h => h_contra _;
    refine' tendsto_order.2 ⟨ _, _ ⟩;
    · exact fun x hx => Filter.Eventually.of_forall fun n => hx.trans_le <| by positivity;
    · rw [ Filter.limsup_eq ] at h;
      rw [ Real.sInf_le_iff ] at h;
      · exact fun ε hε => by obtain ⟨ x, hx₁, hx₂ ⟩ := h ε hε; filter_upwards [ hx₁ ] with n hn; linarith;
      · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ n, hn ⟩ ; exact le_trans ( by positivity ) ( hn _ le_rfl ) ⟩;
      · exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by norm_num [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩ ⟩;
  obtain ⟨n, hn⟩ : ∃ n ∈ S_shifts r, ({a ∈ A | Squarefree (n + a)}).Infinite := by
    apply infinite_squarefree_of_frequent_dense_shifts A (S_shifts r) c hc_pos h_freq;
  exact hn.2 ( Set.Finite.subset ( hA n |> Set.Finite.union <| Set.finite_singleton 0 ) fun x hx => by cases x <;> aesop )

/-
Theorem 1(ii): For any function f that goes to infinity, a sequence A with
Property P exists that satisfies the growth condition a_j/j <= f(j).
-/
theorem Theorem1_ii (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (hf_pos : ∀ n, 1 ≤ f n) :
    PropertyP_positive (A_constructed f hf) ∧ ∀ j ≥ 1, (a_seq f hf j : ℝ) / j ≤ f j := by
      refine' ⟨ A_constructed_PropertyP_positive f hf, fun j hj => _ ⟩;
      -- By combining the results from a_seq_upper_bound and W_k_le_f_proof, we get the desired inequality.
      have h_combined : a_seq f hf j ≤ j * f j := by
        refine' le_trans ( a_seq_upper_bound f hf j hj ) _;
        exact Nat.mul_le_mul_left _ ( W_k_le_f_proof f hf hf_pos j );
      rw [ div_le_iff₀ ] <;> norm_cast ; linarith

/-
Definition of HasPropertyP as written down by the Formal Conjectures project of Google DeepMind.
-/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n ≥ 1, {a ∈ A | Squarefree (n + a)}.Finite

/-
Statements from the Formal Conjectures project of Google DeepMind concerning Property P.
-/
theorem erdos_1102.density_zero_of_P
    (A : ℕ → ℕ)
    (h_inc : StrictMono A)
    (hP : HasPropertyP (range A)) :
    Tendsto (fun j => (A j / j : ℝ)) atTop atTop := by
  convert tendsto_div_of_density_zero A h_inc _;
  -- Since the range of A is a subset of the set of numbers that are not squarefree, and squarefree numbers have density 0, the range of A must also have density 0.
  apply Classical.byContradiction
  intro h_nonzero_density;
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, upperDensity (Set.range A) = δ := by
    refine' ⟨ _, _, rfl ⟩;
    contrapose! h_nonzero_density;
    refine' tendsto_order.2 ⟨ _, _ ⟩;
    · exact fun x hx => Filter.Eventually.of_forall fun n => hx.trans_le <| by positivity;
    · intro a ha; have := h_nonzero_density; simp_all +decide [ upperDensity ] ;
      rw [ Filter.limsup_eq ] at h_nonzero_density;
      simp +zetaDelta at *;
      exact Exists.elim ( show ∃ x, x ∈ { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → ( Set.range A ∩ Set.Icc 1 b |> Set.ncard : ℝ ) / b ≤ a } ∧ x < a from exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → ( Set.range A ∩ Set.Icc 1 b |> Set.ncard : ℝ ) / b ≤ a }.Nonempty from ⟨ _, ⟨ 0, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩ ⟩ ) <| lt_of_le_of_lt h_nonzero_density ha ) fun x hx => ⟨ hx.1.choose, fun n hn => lt_of_le_of_lt ( hx.1.choose_spec n hn ) hx.2 ⟩;
  have := frequent_dense_shifts_of_positive_density ( Set.range A ) ( by linarith );
  obtain ⟨ r, c, hc_pos, hc ⟩ := this;
  obtain ⟨ n, hn ⟩ := infinite_squarefree_of_frequent_dense_shifts ( Set.range A ) ( S_shifts r ) c hc_pos hc;
  exact hn.2 ( Set.Finite.subset ( hP n ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hn.1 ( by
    simp +decide [ S_shifts ];
    exact fun x y hx hy => Nat.sub_ne_zero_of_lt ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hy |>.1 ) ] ) ) ) ) ) fun x hx => by aesop )

theorem erdos_1102.exists_sequence_with_P
    (f : ℕ → ℕ) (h_inf : Tendsto f atTop atTop)
    (h_pos : ∀ n, f n ≠ 0) :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    HasPropertyP (range A) ∧
    ∀ j : ℕ, (A j : ℝ) / j ≤ f j := by
  refine' ⟨ fun j => a_seq f h_inf j, _, _, _ ⟩;
  · exact a_seq_strict_mono f h_inf;
  · intro n hn;
    have h_finite : ∀ n ≥ 1, {a ∈ Set.range (a_seq f h_inf) | Squarefree (n + a)}.Finite := by
      convert A_constructed_PropertyP_positive f h_inf using 1;
      constructor <;> intro h n hn <;> simp_all +decide [ PropertyP_positive, A_constructed ];
      · exact Set.Finite.subset ( h n hn ) fun x hx => by obtain ⟨ ⟨ j, hj₁, rfl ⟩, hx' ⟩ := hx; exact ⟨ ⟨ j, rfl ⟩, hx' ⟩ ;
      · refine Set.Finite.subset ( h n hn |> Set.Finite.union <| Set.finite_singleton ( a_seq f h_inf 0 ) ) ?_;
        intro a ha; cases' ha with ha₁ ha₂; cases' ha₁ with j hj; cases' j with j <;> aesop;
    exact h_finite n hn;
  · intro j; by_cases hj : 1 ≤ j <;> simp_all +decide ;
    field_simp;
    exact_mod_cast le_trans ( a_seq_upper_bound f h_inf j hj ) ( mul_le_mul_of_nonneg_left ( W_k_le_f f h_inf ( fun n => Nat.pos_of_ne_zero ( h_pos n ) ) j ) ( Nat.cast_nonneg _ ) )

#print axioms erdos_1102.exists_sequence_with_P
-- 'Erdos1102.erdos_1102.exists_sequence_with_P' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end

end Erdos1102
