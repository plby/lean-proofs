/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
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

-- The concatenated generated proof sections need these focused linter
-- suppressions and resource budgets while avoiding broad linter disables.
set_option linter.style.setOption false
set_option linter.style.cases false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.flexible false
set_option linter.style.longLine false

set_option maxHeartbeats 50000000

namespace Erdos1102


open Squarefree Set Order Filter Topology


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

-- The generated density-P construction needs extended heartbeat, recursion,


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
            refine Nat.Coprime.prod_left ?_
            simp +contextual [Nat.Prime.coprime_iff_not_dvd]
            intro i hi₁ hi₂ hi₃
            rw [ Nat.Prime.dvd_iff_eq ]
            all_goals
              norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ]
            exact fun h => hi₃ <| by
              have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h
              cases r
              all_goals
                cases i
              all_goals
                aesop
          have := Nat.gcd_eq_gcd_ab ( ∏ s ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) \ { r }, Nat.nth Nat.Prime ( s - 1 ) ^ 2 ) ( Nat.nth Nat.Prime ( r - 1 ) ^ 2 )
          exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by
            push_cast at *
            linarith ⟩ ⟩
        use -↑r * y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2)
        exact ⟨ by simpa [ mul_assoc ] using hy_r.mul_left _, fun s hs hs' => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ⟩
      choose! x hx₁ hx₂ using h_crt
      use ∑ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), x r
      intro r hr
      simp_all +decide only [Int.ModEq]
      rw [ Finset.sum_int_mod, Finset.sum_eq_single r ]
      all_goals
        aesop
    -- Let $M = \prod_{r=1}^{k(j+1)} p_r^2$.
    set M := ∏ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (Nat.nth Nat.Prime (r - 1)^2) with hM_def
    -- Let $y$ be a positive integer such that $y \equiv x \pmod{M}$ and $y > aj$.
    obtain ⟨y, hy⟩ : ∃ y, y > aj ∧ y ≡ x [ZMOD ↑M] := by
      use Int.toNat ( x % M + M * ( aj + 1 ) )
      norm_num [ Int.ModEq ]
      exact ⟨ by nlinarith [ Int.emod_nonneg x ( show ( M : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ), Int.emod_lt_of_pos x ( show ( M : ℤ ) > 0 from mod_cast Finset.prod_pos fun i hi => pow_pos ( Nat.Prime.pos <| by aesop ) 2 ) ], by rw [ max_eq_left ( by nlinarith [ Int.emod_nonneg x ( show ( M : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ), Int.emod_lt_of_pos x ( show ( M : ℤ ) > 0 from mod_cast Finset.prod_pos fun i hi => pow_pos ( Nat.Prime.pos <| by aesop ) 2 ) ] ) ] ; simp +decide [Int.add_emod] ⟩
    refine ⟨ y, hy.1, fun r hr => ?_ ⟩
    rw [ ← Int.natCast_inj ]
    simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ]
    convert dvd_add ( dvd_trans ( Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr hr ) ) hy.2 ) ( hx r hr.1 hr.2 ) using 1
    ring : ∃ x, x > aj ∧ ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (x + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0))

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
        induction r generalizing m with
        | zero =>
          exact hf_pos m
        | succ r ih =>
          exact Nat.find_spec ( _ : ∃ n, n > l_seq f hf r ∧ ∀ j ≥ n, f j ≥ W ( r + 1 ) ) |>.2 m hm
      exact h_l_seq _
    have := Finset.max'_mem ( Finset.filter ( fun r => l_seq f hf r ≤ j ) ( Finset.range ( j + 1 ) ) ) ⟨ k_func f hf j, by
      exact Finset.max'_mem _ _ ⟩ ; aesop

/-
k(j) is a monotonic function of j.
-/
lemma k_func_mono (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : Monotone (k_func f hf) := by
  intro j k hjk
  refine Finset.le_max'
    ((Finset.range (k + 1)).filter (fun r => l_seq f hf r ≤ k))
    (k_func f hf j) ?_
  have h_range : k_func f hf j ∈ Finset.filter (fun r => l_seq f hf r ≤ j) (Finset.range (j + 1)) := by
    unfold k_func
    exact Finset.max'_mem _ _
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp h_range).1)) hjk)),
    le_trans (Finset.mem_filter.mp h_range).2 hjk⟩

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
              refine Nat.Coprime.prod_left ?_
              simp +contextual [Nat.Prime.coprime_iff_not_dvd]
              intro i hi₁ hi₂ hi₃
              rw [ Nat.prime_dvd_prime_iff_eq ]
              all_goals
                norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ]
              exact fun h => hi₃ <| by
                have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h
                cases i
                all_goals
                  cases r
                all_goals
                  aesop
            have := Nat.gcd_eq_gcd_ab ( ∏ s ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) \ { r }, Nat.nth Nat.Prime ( s - 1 ) ^ 2 ) ( Nat.nth Nat.Prime ( r - 1 ) ^ 2 )
            exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by
              push_cast at *
              linarith ⟩ ⟩
          use -r * y_r * (∏ s ∈ Finset.Icc 1 (k_func f hf (j + 1)) \ {r}, (Nat.nth Nat.Prime (s - 1))^2)
          exact ⟨ by simpa [ mul_assoc ] using hy_r.mul_left _, fun s hs hs' => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ⟩
        choose! y hy₁ hy₂ using h_crt
        use ∑ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), y r
        intro r hr
        simp_all +decide only [Int.ModEq]
        rw [ Finset.sum_int_mod, Finset.sum_eq_single r ]
        all_goals
          aesop
      -- Let $y$ be a solution to the system of congruences.
      obtain ⟨y, hy⟩ : ∃ y : ℕ, ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (y + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
        use Int.toNat ( y % ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), ( Nat.nth Nat.Prime ( r - 1 ) ) ^ 2 )
        intro r hr
        rw [ ← Int.natCast_inj ]
        simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( show ( ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), Nat.nth Nat.Prime ( r - 1 ) ^ 2 : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) ]
        rw [ Int.dvd_iff_emod_eq_zero ]
        simp_all +decide [ Finset.prod_eq_prod_sdiff_singleton_mul ( show r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ) from Finset.mem_Icc.mpr hr ), Int.add_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero ]
      use y + (a_seq f hf j + 1) * (∏ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (Nat.nth Nat.Prime (r - 1))^2)
      exact ⟨ by nlinarith [ show 0 < ∏ r ∈ Finset.Icc 1 ( k_func f hf ( j + 1 ) ), Nat.nth Nat.Prime ( r - 1 ) ^ 2 from Finset.prod_pos fun x hx => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ], fun r hr => by simpa [ Nat.add_mod, Nat.mul_mod, Finset.prod_eq_prod_sdiff_singleton_mul hr ] using hy r hr ⟩
    -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $(a_j, a_j + W(k(j+1))]$ that satisfies the congruences.
    obtain ⟨z, hz⟩ : ∃ z ∈ Set.Ioo (a_seq f hf j) (a_seq f hf j + W (k_func f hf (j + 1)) + 1), ∀ r ∈ Finset.Icc 1 (k_func f hf (j + 1)), (z + r) % (Nat.nth Nat.Prime (r - 1))^2 = 0 := by
      -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $(a_j, a_j + W(k(j+1))]$ that satisfies the congruences. Let $z = y - m \cdot W(k(j+1))$ for some integer $m$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, a_seq f hf j < y - m * W (k_func f hf (j + 1)) ∧ y - m * W (k_func f hf (j + 1)) < a_seq f hf j + W (k_func f hf (j + 1)) + 1 := by
        refine ⟨ ( y - ( a_seq f hf j + 1 ) ) / W ( k_func f hf ( j + 1 ) ), ?_, ?_ ⟩
        · rw [ Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le ]
          · linarith [ Nat.div_mul_le_self ( y - ( a_seq f hf j + 1 ) ) ( W ( k_func f hf ( j + 1 ) ) ), Nat.sub_add_cancel ( by linarith : a_seq f hf j + 1 ≤ y ) ]
          · exact le_trans ( Nat.div_mul_le_self _ _ ) ( Nat.sub_le _ _ ) |> le_trans <| by linarith
        · rw [ tsub_lt_iff_left ]
          · linarith [ Nat.div_add_mod ( y - ( a_seq f hf j + 1 ) ) ( W ( k_func f hf ( j + 1 ) ) ), Nat.mod_lt ( y - ( a_seq f hf j + 1 ) ) ( show W ( k_func f hf ( j + 1 ) ) > 0 from pow_pos ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) ) 2 ), Nat.sub_add_cancel ( by linarith : a_seq f hf j + 1 ≤ y ) ]
          · exact le_trans ( Nat.div_mul_le_self _ _ ) ( Nat.sub_le_of_le_add <| by linarith )
      refine ⟨ y - m * W ( k_func f hf ( j + 1 ) ), ⟨ hm.1, hm.2 ⟩, fun r hr => ?_ ⟩
      rw [ ← Nat.dvd_iff_mod_eq_zero ] at *
      convert Nat.dvd_sub ( Nat.dvd_of_mod_eq_zero ( hy.2 r hr ) ) ( dvd_mul_of_dvd_right ( show Nat.nth Nat.Prime ( r - 1 ) ^ 2 ∣ W ( k_func f hf ( j + 1 ) ) from _ ) m ) using 1
      · grind
      · exact dvd_trans ( by norm_num ) ( pow_dvd_pow_of_dvd ( Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr ( show r - 1 < k_func f hf ( j + 1 ) from Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.mem_Icc.mp hr |>.1 ) ) ) ( Finset.mem_Icc.mp hr |>.2 ) ) ) ) 2 )
    by_cases h_case : j + 1 ≤ l_seq f hf 1
    · rcases j with ( _ | j )
      all_goals
        simp_all +decide [ a_seq ]
      · exact Nat.one_le_iff_ne_zero.mpr ( by erw [ show W ( k_func f hf 1 ) = ( ∏ i ∈ Finset.range ( k_func f hf 1 ), Nat.nth Nat.Prime i ) ^ 2 from rfl ] ; exact pow_ne_zero _ <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop )
      · grind
    · simp +zetaDelta at *
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
    induction j with
    | zero =>
      simp_all +decide
    | succ j ih =>
      simp_all +decide [ a_seq ]
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
    intro k m hkm
    rw [ ← Finset.prod_sdiff ( Finset.range_mono hkm ) ]
    exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => Nat.zero_le _ ) ( Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.Prime.ne_zero <| by aesop )
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
        use l_seq f hf (M + 1)
      refine ⟨ j, ?_ ⟩
      generalize_proofs at *
      (
      exact Finset.le_max' ( Finset.filter ( fun r => l_seq f hf r ≤ j ) ( Finset.range ( j + 1 ) ) ) ( M + 1 ) ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ show M + 1 ≤ j from hj.trans' ( show l_seq f hf ( M + 1 ) ≥ M + 1 from Nat.recOn ( M + 1 ) ( by norm_num ) fun r hr => Nat.find_spec ( _ : ∃ n, n > l_seq f hf r ∧ ∀ j ≥ n, f j ≥ W ( r + 1 ) ) |>.1.trans_le' <| by linarith ) ] ), hj ⟩ ) |> le_trans ( by norm_num ) ;)
    exact Filter.tendsto_atTop_atTop.mpr fun M => by
      obtain ⟨ j, hj ⟩ := hk_unbounded M
      exact ⟨ j, fun n hn => le_trans hj ( k_func_mono f hf hn ) ⟩

/-
a_j <= j * W(k(j)) for all j >= 1.
-/
lemma a_seq_upper_bound (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  ∀ j ≥ 1, a_seq f hf j ≤ j * W (k_func f hf j) := by
    intro j hj_ge_1
    induction j, hj_ge_1 using Nat.le_induction with
    | base =>
      -- For the base case $j = 1$, we have $a_1 = 1$.
      simp [a_seq]
      split_ifs
      all_goals
        norm_num [ W ]
      · exact Nat.one_le_pow _ _ ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) )
      · unfold l_seq at *
        aesop
    | succ j hj ih =>
      -- By Lemma a_seq_step_le, we have $a_{j+1} \leq a_j + W(k(j+1))$.
      have h_step : a_seq f hf (j + 1) ≤ a_seq f hf j + W (k_func f hf (j + 1)) := by
        exact a_seq_step_le f hf j
      nlinarith [ show W ( k_func f hf j ) ≤ W ( k_func f hf ( j + 1 ) ) from W_mono <| k_func_mono f hf <| Nat.le_succ _ ]

/-
The constructed sequence A has Property P (restricted to n >= 1).
-/
def PropertyP_positive (A : Set ℕ) : Prop := ∀ n, n ≥ 1 → ({a ∈ A | Squarefree (n + a)}).Finite

lemma A_constructed_PropertyP_positive (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  PropertyP_positive (A_constructed f hf) := by
    -- For any fixed $n \geq 1$, there exists $J$ such that for all $j \geq J$, $k(j) \geq n$.
    have h_J : ∀ n ≥ 1, ∃ J, ∀ j ≥ J, k_func f hf j ≥ n := by
      exact fun n hn => Filter.eventually_atTop.mp ( k_func_tendsto_atTop f hf |> Filter.Tendsto.eventually_ge_atTop <| n )
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
      exact h_cong
    -- Thus, {a in A | Squarefree (n + a)} is contained in {a_1, ..., a_{J-1}}, which is finite.
    intros n hn
    obtain ⟨J, hJ⟩ := h_div n hn
    have h_finite : {a ∈ A_constructed f hf | Squarefree (n + a)} ⊆ Finset.image (fun j => a_seq f hf j) (Finset.Icc 1 (J - 1)) := by
      intro a ha
      obtain ⟨ j, hj₁, rfl ⟩ := ha.1
      rcases lt_or_ge j J with hj₂ | hj₂
      all_goals
        simp_all +decide
      · exact ⟨ j, ⟨ hj₁, Nat.le_sub_one_of_lt hj₂ ⟩, rfl ⟩
      · have := Nat.dvd_of_mod_eq_zero ( hJ j hj₂ )
        simp_all +decide [Nat.squarefree_iff_prime_squarefree]
        exact False.elim <| ha.2 ( Nat.nth Nat.Prime ( n - 1 ) ) ( Nat.prime_nth_prime _ ) <| by simpa only [ sq, add_comm ] using this
    exact Set.Finite.subset ( Finset.finite_toSet _ ) h_finite

/-
a_seq is strictly monotonic.
-/
lemma a_seq_strict_mono (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
  StrictMono (a_seq f hf) := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    -- By definition of $a_seq$, we have $a_{j+1} > a_j$ for all $j$.
    have h_a_seq_strict_mono : ∀ j, a_seq f hf (j + 1) > a_seq f hf j := by
      intro j
      -- By definition of $a_seq$, we have $a_seq f hf (j + 1) > a_seq f hf j$ because $a_seq f hf (j + 1)$ is the smallest integer greater than $a_seq f hf j$ that satisfies the congruence conditions.
      have h_a_seq_gt : ∀ j, a_seq f hf (j + 1) > a_seq f hf j := by
        intro j
        refine Nat.lt_of_not_ge fun h => ?_
        induction j with
        | zero =>
          simp_all +decide [ a_seq ]
          split_ifs at h
          simp_all +decide [ l_seq ]
        | succ j ih =>
          simp_all +decide [ a_seq ]
          grind
      exact h_a_seq_gt j
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
      intro rs
      rw [ Finset.card_filter, Finset.card_filter ]
      rw [ Finset.sum_Ico_eq_sum_range ]
      erw [ Finset.sum_Ico_eq_sum_range ]
      norm_num [ add_comm, Finset.sum_range_succ' ]
      ring_nf
      rw [ Finset.card_filter, Finset.card_filter ]
      conv_rhs =>
        rw [ ← Nat.sub_add_cancel ( show 1 ≤ ∏ x ∈ rs, Nat.nth Nat.Prime x ^ 2 from Finset.prod_pos fun _ _ => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ), Finset.sum_range_succ' ]
        simp +decide [ add_comm 1 ]
      rw [ ← Nat.sub_add_cancel ( show 1 ≤ ∏ x ∈ rs, Nat.nth Nat.Prime x ^ 2 from Finset.prod_pos fun _ _ => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ), Finset.sum_range_succ ]
      simp +decide [add_comm
            1]
      ring_nf
      split_ifs
      all_goals
        simp_all +decide
      rename_i h₁ h₂
      obtain ⟨ x, hx ⟩ := h₂
      specialize h₁ x hx
      simp_all +decide [Finset.prod_eq_prod_sdiff_singleton_mul
            hx]
      exact h₁ ( by rw [ add_tsub_cancel_of_le ( Nat.one_le_iff_ne_zero.mpr <| mul_ne_zero ( Finset.prod_ne_zero_iff.mpr fun y hy => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) <| pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ) ] ; norm_num )
    induction rs using Finset.induction with
    | empty =>
      norm_num
    | insert i rs hi ih =>
      have h_crt_step : Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)))) = Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2))) * Finset.card (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2))) := by
        have h_crt_step : Finset.card (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)))) = Finset.card (Finset.image (fun x => (x % Nat.nth Nat.Prime i ^ 2, x % ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)) (Finset.filter (fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x) (Finset.filter (fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x) (Finset.Ico 0 (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2))))) := by
          rw [ Finset.card_image_of_injOn ]
          intros x hx y hy hxy
          have h_crt_step : x ≡ y [MOD Nat.nth Nat.Prime i ^ 2] ∧ x ≡ y [MOD ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2] := by
            aesop
          have h_crt_step : x ≡ y [MOD (Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2)] := by
            rw [ Nat.modEq_and_modEq_iff_modEq_mul ] at h_crt_step
            · aesop
            · refine Nat.Coprime.prod_right fun j hj => ?_
              simp +decide [Nat.Prime.coprime_iff_not_dvd, Nat.prime_dvd_prime_iff_eq]
              exact fun h => hi <| by
                have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h
                aesop
          exact Nat.mod_eq_of_lt ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ▸ Nat.mod_eq_of_lt ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hy |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ▸ h_crt_step
        rw [ h_crt_step, show ( Finset.image ( fun x => ( x % Nat.nth Nat.Prime i ^ 2, x % ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) ( Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.filter ( fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x ) ( Finset.Ico 0 ( Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) ) ) ) = Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.Ico 0 ( Nat.nth Nat.Prime i ^ 2 ) ) ×ˢ Finset.filter ( fun x => ∀ j ∈ rs, ¬Nat.nth Nat.Prime j ^ 2 ∣ x ) ( Finset.Ico 0 ( ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ) ) from ?_ ]
        · exact Finset.card_product _ _
        · ext ⟨x, y⟩
          simp [Finset.mem_image]
          constructor
          · rintro ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl, rfl ⟩
            exact ⟨ ⟨ Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime i ) ) 2 ), by simpa [ Nat.dvd_iff_mod_eq_zero ] using ha₃ ⟩, Nat.mod_lt _ ( Finset.prod_pos fun j hj => pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime j ) ) 2 ), fun j hj => by simpa [ Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ ( Finset.dvd_prod_of_mem _ hj ) ] using ha₂ j hj ⟩
          · intro hxy
            obtain ⟨a, ha⟩ : ∃ a, a ≡ x [MOD Nat.nth Nat.Prime i ^ 2] ∧ a ≡ y [MOD ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2] ∧ a < Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 := by
              have h_crt : Nat.gcd (Nat.nth Nat.Prime i ^ 2) (∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2) = 1 := by
                simp +decide [Nat.coprime_prod_right_iff, Nat.Prime.coprime_iff_not_dvd]
                intro j hj
                rw [ Nat.prime_dvd_prime_iff_eq ]
                all_goals
                  norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ]
                exact fun h => hi <| by
                  have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h
                  aesop
              have := Nat.chineseRemainder h_crt x y
              exact ⟨ this.val % ( Nat.nth Nat.Prime i ^ 2 * ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2, Nat.mod_lt _ ( Nat.mul_pos ( pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime i ) ) 2 ) ( Finset.prod_pos fun j hj => pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime j ) ) 2 ) ) ⟩
            use a
            simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ]
            exact ⟨ fun j hj => by rw [ ← Nat.mod_mod_of_dvd a ( show Nat.nth Nat.Prime j ^ 2 ∣ ∏ j ∈ rs, Nat.nth Nat.Prime j ^ 2 from Finset.dvd_prod_of_mem _ hj ) ] ; simp_all +decide [ Nat.mod_eq_of_lt ], Nat.mod_eq_of_lt hxy.1.1, Nat.mod_eq_of_lt hxy.2.1 ⟩
      simp_all +decide [ Finset.prod_insert hi ]
      convert h_crt_step using 1
      · convert h_crt ( Insert.insert i rs ) using 2
        · simp +decide [Finset.prod_insert hi]
        · ext
          simp +decide [ Finset.prod_insert hi, Finset.mem_filter, Finset.mem_range ]
          aesop
      · rw [ show Finset.filter ( fun x => ¬Nat.nth Nat.Prime i ^ 2 ∣ x ) ( Finset.range ( Nat.nth Nat.Prime i ^ 2 ) ) = Finset.range ( Nat.nth Nat.Prime i ^ 2 ) \ { 0 } from ?_, Finset.card_sdiff ] <;> norm_num
        · rw [ Finset.inter_eq_left.mpr ]
          all_goals
            norm_num
          exact pow_pos ( Nat.Prime.pos ( by aesop ) ) _
        · ext ( _ | x ) <;> simp +decide [ Nat.dvd_iff_mod_eq_zero ]
          exact fun h => by
            rw [ Nat.mod_eq_of_lt h ]
            norm_num
  convert h_crt ( Finset.range r ) using 2
  unfold S_r
  unfold W
  norm_num [ Finset.prod_pow ]

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
        have := @EulerProduct.eulerProduct_hasProd
        specialize @this ℝ _ ( fun n => ( n : ℝ ) ⁻¹ ^ 2 ) _ _ _ _ <;> norm_num at *
        · intro m n h
          ring
        · convert this.tprod_eq using 1
          refine tprod_congr fun p => ?_
          ring_nf
          norm_num [ pow_mul' ]
          rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ]
          norm_num
      have h_prod_conv : Filter.Tendsto (fun r => (∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹)) Filter.atTop (nhds (∏' p : Nat.Primes, (1 - (1 : ℝ) / p^2)⁻¹)) := by
        have h_abs_conv : Summable (fun p : Nat.Primes => Real.log ((1 - (1 : ℝ) / p^2)⁻¹)) := by
          have h_abs_conv : Summable (fun p : Nat.Primes => (1 : ℝ) / p^2) := by
            exact Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _
          have h_abs_conv : ∀ p : Nat.Primes, Real.log ((1 - (1 : ℝ) / p^2)⁻¹) ≤ 2 * (1 : ℝ) / p^2 := by
            intro p
            rw [ Real.log_inv ]
            ring_nf
            norm_num
            nlinarith only [ Real.log_inv ( 1 - ( p ^ 2 : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show 0 < 1 - ( p ^ 2 : ℝ ) ⁻¹ by exact sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ) ), inv_mul_cancel₀ ( show ( 1 - ( p ^ 2 : ℝ ) ⁻¹ ) ≠ 0 by exact ne_of_gt ( sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) ) ) ), inv_pos.mpr ( show 0 < ( p ^ 2 : ℝ ) by exact sq_pos_of_pos ( Nat.cast_pos.mpr p.2.pos ) ), inv_mul_cancel₀ ( show ( p ^ 2 : ℝ ) ≠ 0 by exact pow_ne_zero 2 ( Nat.cast_ne_zero.mpr p.2.ne_zero ) ), show ( p ^ 2 : ℝ ) ≥ 4 by exact_mod_cast Nat.pow_le_pow_left p.2.two_le 2 ]
          exact Summable.of_nonneg_of_le ( fun p => Real.log_nonneg <| by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le p.2, one_div_mul_cancel <| show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr p.2.ne_zero ] ) ( fun p => h_abs_conv p ) <| by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using Summable.mul_left 2 ‹Summable fun p : Nat.Primes => ( 1 : ℝ ) / p ^ 2›
        have h_exp_conv : Filter.Tendsto (fun r => Real.exp (∑ i ∈ Finset.range r, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹))) Filter.atTop (nhds (Real.exp (∑' p : Nat.Primes, Real.log ((1 - (1 : ℝ) / p^2)⁻¹)))) := by
          refine Real.continuous_exp.continuousAt.tendsto.comp ?_
          have h_exp_conv : Filter.Tendsto (fun r => ∑ i ∈ Finset.range r, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime i)^2)⁻¹)) Filter.atTop (nhds (∑' p : ℕ, Real.log ((1 - (1 : ℝ) / (Nat.nth Nat.Prime p)^2)⁻¹))) := by
            refine ( Summable.hasSum ?_ ) |> HasSum.tendsto_sum_nat
            simpa [Function.comp_def] using
              h_abs_conv.comp_injective
                (show Function.Injective
                    (fun i : ℕ => ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩ : ℕ → Nat.Primes) from
                  fun i j hij => by
                    simpa using Nat.nth_injective (Nat.infinite_setOf_prime) <|
                      Subtype.ext_iff.mp hij)
          convert h_exp_conv using 1
          rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun p : ℕ => ⟨ Nat.nth Nat.Prime p, Nat.prime_nth_prime p ⟩ ) ⟨ fun p => ?_, fun p => ?_ ⟩ ) ]
          all_goals norm_num [ Nat.nth_injective ]
          · exact fun q h => Nat.nth_injective ( Nat.infinite_setOf_prime ) <| by injection h
          · use Nat.count ( Nat.Prime ) p.val
            exact Subtype.ext <| Nat.nth_count p.2
        convert h_exp_conv using 2
        · rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( inv_pos.mpr <| sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ) two_ne_zero ) ]
        · have h_exp_conv : ∀ {f : Nat.Primes → ℝ}, (∀ p : Nat.Primes, 0 < f p) → Summable (fun p : Nat.Primes => Real.log (f p)) → ∏' p : Nat.Primes, f p = Real.exp (∑' p : Nat.Primes, Real.log (f p)) := by
            exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
          exact h_exp_conv ( fun p => inv_pos.mpr <| sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast p.2.one_lt ) two_ne_zero ) h_abs_conv
      convert h_prod_conv.inv₀ _ using 1
      · norm_num [ Finset.prod_inv_distrib ]
      · aesop
      · exact h_euler.symm ▸ by exact ne_of_gt ( by exact lt_of_lt_of_le ( by positivity ) ( Summable.le_tsum ( by exact Real.summable_one_div_nat_pow.2 one_lt_two ) 1 ( by intros; positivity ) ) )
    convert h_zeta using 2
    have := hasSum_zeta_two
    have := this.tsum_eq
    norm_num at *
    aesop
  convert h_density using 2
  norm_num [ card_S_r, W ]
  rw [ ← Finset.prod_pow ]
  rw [ ← Finset.prod_div_distrib ]
  exact Finset.prod_congr rfl fun _ _ => by
    rw [ Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ]
    all_goals
      norm_num
    all_goals
      ring_nf
    all_goals
      norm_num [ Nat.Prime.ne_zero <| Nat.prime_nth_prime ‹_› ]

/-
T_finset is the set of integers n in [1, N] such that n is congruent to some element of S_r modulo W_r.
-/
def T_finset (N r : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => (if n % W r = 0 then W r else n % W r) ∈ S_r r)

/-
Elements in T_finset are not divisible by the square of any of the first r primes.
-/
lemma T_finset_squarefree_prop (N r : ℕ) (n : ℕ) (hn : n ∈ T_finset N r) :
    ∀ i ∈ Finset.range r, ¬ (Nat.nth Nat.Prime i)^2 ∣ n := by
      intro i hi
      -- By definition of $T_{\text{finset}}$, if $n \in T_{\text{finset}}(N, r)$, then $n \pmod{W_r} \in S_r$.
      have h_mod : (if n % W r = 0 then W r else n % W r) ∈ S_r r := by
        exact Finset.mem_filter.mp hn |>.2
      -- By definition of $S_r$, if $n \pmod{W_r} \in S_r$, then $n \pmod{W_r}$ is not divisible by $p_i^2$ for any $i < r$.
      have h_not_div : ¬(Nat.nth Nat.Prime i)^2 ∣ (if n % W r = 0 then W r else n % W r) := by
        unfold S_r at h_mod
        aesop
      split_ifs at h_not_div
      all_goals
        simp_all +decide [ Nat.dvd_iff_mod_eq_zero ]
      · contrapose! h_not_div
        exact Nat.mod_eq_zero_of_dvd <| dvd_trans ( by norm_num ) <| pow_dvd_pow_of_dvd ( Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi ) 2
      · rwa [ Nat.mod_mod_of_dvd _ ( show Nat.nth Nat.Prime i ^ 2 ∣ W r from dvd_trans ( pow_dvd_pow_of_dvd ( Nat.dvd_of_mod_eq_zero <| by rw [ Nat.mod_eq_zero_of_dvd ] ; exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr hi ) ) _ ) ( dvd_refl _ ) ) ] at h_not_div

/-
If an element in T_finset is not squarefree, it must be divisible by the square of a prime greater than or equal to the r-th prime.
-/
lemma non_squarefree_in_T_implies_large_prime_sq_dvd (N r : ℕ) (n : ℕ) (hn : n ∈ T_finset N r) (hns : ¬ Squarefree n) :
    ∃ p, Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r ∧ p^2 ∣ n := by
      obtain ⟨ p, hp_prime, hp_div ⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n := by
        rw [ Nat.squarefree_iff_prime_squarefree ] at hns
        simpa [ sq ] using hns
      by_cases hp_lt : p < Nat.nth Nat.Prime r
      · obtain ⟨ i, hi ⟩ : ∃ i < r, p = Nat.nth Nat.Prime i := by
          refine ⟨ Nat.count ( Nat.Prime ) p, ?_, ?_ ⟩
          · contrapose! hp_lt
            rw [ Nat.nth_eq_sInf ]
            refine Nat.sInf_le ⟨ hp_prime, ?_ ⟩
            intro k hk
            exact Nat.nth_lt_of_lt_count <| by linarith
          · rw [ Nat.nth_count ]
            aesop
        have := T_finset_squarefree_prop N r n hn i ( Finset.mem_range.mpr hi.1 )
        aesop
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
                  exact non_squarefree_in_T_implies_large_prime_sq_dvd N r n hn hns
                norm_num +zetaDelta at *
                exact ⟨ p, ⟨ ⟨ hp_ge, by nlinarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hn ( by unfold T_finset; aesop ) ) ) hp_sq, show n ≤ N from Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ] ⟩, hp_prime ⟩, hp_sq ⟩
              have h_non_squarefree_bound : (Finset.filter (fun n => ¬Squarefree n) (T_finset N r)).card ≤ Finset.card (Finset.biUnion (Finset.filter Nat.Prime (Finset.Icc (Nat.nth Nat.Prime r) N)) (fun p => Finset.filter (fun n => p^2 ∣ n) (T_finset N r))) := by
                exact Finset.card_le_card fun x hx => by aesop
              exact_mod_cast h_non_squarefree_bound.trans ( Finset.card_biUnion_le )
            convert h_non_squarefree_bound using 1
          refine le_trans h_non_squarefree_bound <| Finset.sum_le_sum fun p hp => ?_
          -- The number of multiples of $p^2$ in $[1, N]$ is at most $N / p^2$.
          have h_multiples_bound : ((Finset.filter (fun n => p^2 ∣ n) (Finset.Icc 1 N)).card : ℝ) ≤ N / p^2 := by
            have h_multiples_bound : ((Finset.filter (fun n => p^2 ∣ n) (Finset.Icc 1 N)).card : ℝ) ≤ Finset.card (Finset.image (fun n => p^2 * n) (Finset.Icc 1 (N / p^2))) := by
              exact_mod_cast Finset.card_mono fun x hx => Finset.mem_image.mpr ⟨ x / p ^ 2, Finset.mem_Icc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) ) ( pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ), Nat.div_le_div_right ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ⟩, Nat.mul_div_cancel' ( Finset.mem_filter.mp hx |>.2 ) ⟩
            exact h_multiples_bound.trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) hxy ] ; simpa using Nat.cast_div_le .. |> le_trans <| by norm_num )
          exact le_trans ( mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.filter_subset _ _ ) h_multiples_bound
        refine le_trans h_non_squarefree_bound ?_
        rw [ ← tsum_mul_left ]
        refine le_trans ?_ ( Summable.sum_le_tsum ( Finset.Icc ( Nat.nth Nat.Prime r ) N ) ( fun _ _ => by positivity ) ?_ )
        · rw [ Finset.sum_filter ]
          exact Finset.sum_le_sum fun x hx => by aesop
        · exact Summable.mul_left _ <| Summable.of_nonneg_of_le ( fun x => by positivity ) ( fun x => by aesop ) <| Real.summable_one_div_nat_pow.2 one_lt_two
      -- Since $\sum_{p \ge p_r} \frac{1}{p^2}$ converges, the tail sum tends to 0.
      have h_tail_zero : Filter.Tendsto (fun r => ∑' p : ℕ, if (Nat.Prime p ∧ p ≥ Nat.nth Nat.Prime r) then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds 0) := by
        have h_tail_zero : Filter.Tendsto (fun r => ∑' p : ℕ, if (Nat.Prime p ∧ p ≥ r) then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds 0) := by
          convert tendsto_sum_nat_add fun p => ( if Nat.Prime p then ( p ^ 2 : ℝ ) ⁻¹ else 0 ) using 1
          ext r
          rw [ ← Summable.sum_add_tsum_nat_add r ]
          focus
            norm_num [ add_comm, add_left_comm, add_assoc ]
          · exact Finset.sum_eq_zero fun x hx => if_neg <| not_and_of_not_right _ <| by linarith [ Finset.mem_range.mp hx ]
          · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
        exact h_tail_zero.comp <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) |> StrictMono.tendsto_atTop
      have := h_tail_zero.eventually ( gt_mem_nhds hc )
      obtain ⟨ r, hr ⟩ := this.exists
      exact ⟨ r, fun N => by nlinarith [ h_bound r N ] ⟩

/-
There exists a residue class l modulo W_r such that the number of elements in A congruent to l modulo W_r is large.
-/
def A_l (A : Set ℕ) (N r l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 2 * W r)).filter (fun a => a ∈ A ∧ a % W r = l)

lemma exists_l_large_A_l (A : Set ℕ) (N r : ℕ) (δ : ℝ) (hr : W r > 0)
    (h_card : ((Finset.Icc 1 (N - 2 * W r)).filter (fun a => a ∈ A)).card > δ * N / 2) :
    ∃ l < W r, ((A_l A N r l).card : ℝ) > δ * N / (2 * W r) := by
      contrapose! h_card
      -- The set $A \cap [1, N - 2W_r]$ is partitioned into $W_r$ sets $A_l$ based on the residue modulo $W_r$.
      have h_partition : (Finset.filter (fun a => a ∈ A) (Finset.Icc 1 (N - 2 * W r))).card = ∑ l ∈ Finset.range (W r), (A_l A N r l).card := by
        rw [ ← Finset.card_biUnion ]
        · congr with x
          simp +decide [ A_l ]
          exact fun _ _ _ => Nat.mod_lt _ hr
        · intro x hx y hy hxy
          simp_all +decide [ Finset.disjoint_left, A_l ]
      convert Finset.sum_le_sum fun i hi => h_card i ( Finset.mem_range.mp hi ) using 1
      · exact_mod_cast h_partition
      · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hr.ne' ]

/-
The translate of A_l by W_r + s - l is contained in T_finset.
-/
def translate_set (A : Set ℕ) (N r l s : ℕ) : Finset ℕ :=
  (A_l A N r l).image (fun a => W r + s - l + a)

lemma translates_subset_T (A : Set ℕ) (N r l : ℕ) (s : ℕ)
    (hs : s ∈ S_r r) (hl : l < W r) :
    translate_set A N r l s ⊆ T_finset N r := by
      intro x hx
      obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx
      -- Since $a \equiv l \pmod{W_r}$, we have $W_r + s - l + a \equiv s \pmod{W_r}$.
      have h_mod : (W r + s - l + a) % W r = s % W r := by
        have h_mod : a % W r = l % W r := by
          unfold A_l at ha
          aesop
        simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show l ≤ W r + s from by linarith ) ]
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
      -- Since $s \in S_r$, we have $s \in [1, W_r]$ and $s$ satisfies the condition. Thus, $W_r + s - l + a \in T_finset N r$.
      have h_range : 1 ≤ W r + s - l + a ∧ W r + s - l + a ≤ N := by
        have h_bounds : 1 ≤ a ∧ a ≤ N - 2 * W r := by
          unfold A_l at ha
          aesop
        have h_bounds_s : s ≤ W r := by
          exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hs |>.1 ) |>.2
        omega
      have h_range : (if (W r + s - l + a) % W r = 0 then W r else (W r + s - l + a) % W r) ∈ S_r r := by
        split_ifs
        all_goals
          simp_all +decide
        · rw [ eq_comm, ← Nat.dvd_iff_mod_eq_zero ] at h_mod
          contrapose! h_mod
          simp_all +decide [ S_r ]
          exact Nat.not_dvd_of_pos_of_lt hs.1.1 ( lt_of_le_of_ne hs.1.2 ( by aesop ) )
        · convert hs using 1
          exact Nat.mod_eq_of_lt ( show s < W r from lt_of_le_of_ne ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hs |>.1 ) |>.2 ) fun con => by aesop )
      exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ‹_›, h_range ⟩

/-
The translates of A_l by different shifts s1 and s2 are disjoint.
-/
lemma translates_disjoint (A : Set ℕ) (N r l : ℕ) (s1 s2 : ℕ)
    (hs1 : s1 ∈ S_r r) (hs2 : s2 ∈ S_r r) (hneq : s1 ≠ s2) :
    Disjoint (translate_set A N r l s1) (translate_set A N r l s2) := by
      unfold S_r at *
      simp_all +decide [ Finset.disjoint_left ]
      intros x hx1 hx2
      unfold translate_set at *
      simp_all +decide
      obtain ⟨ a, ha, rfl ⟩ := hx1
      obtain ⟨ b, hb, hb' ⟩ := hx2
      simp_all +decide [ A_l ]
      -- Since $a \equiv b \equiv l \pmod{W_r}$, we have $s1 \equiv s2 \pmod{W_r}$.
      have h_mod : s1 % W r = s2 % W r := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
        have h_mod : (W r + s2 - l + b : ℤ) ≡ (W r + s1 - l + a : ℤ) [ZMOD W r] := by
          norm_cast
          rw [ Int.subNatNat_of_le, Int.subNatNat_of_le ]
          all_goals
            norm_cast
          · rw [hb']
          · exact ha.2.2 ▸ Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) ) |> le_trans <| by linarith
          · exact ha.2.2 ▸ Nat.le_of_lt ( Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop ) ) ) |> le_trans <| by linarith
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ]
        rw [ ← Nat.mod_add_div a ( W r ), ← Nat.mod_add_div b ( W r ) ] at *
        simp_all +decide
      have := Nat.modEq_iff_dvd.mp h_mod.symm
      simp_all +decide [ Nat.dvd_iff_mod_eq_zero ]
      obtain ⟨ k, hk ⟩ := this
      exact hneq <| by nlinarith [ show k = 0 by nlinarith ]

/-
The cardinality of a translate of A_l is equal to the cardinality of A_l.
-/
lemma card_translate_set (A : Set ℕ) (N r l s : ℕ) :
    (translate_set A N r l s).card = (A_l A N r l).card := by
      -- The function $a \mapsto W_r + s - l + a$ is injective, so the cardinality of the image is equal to the cardinality of the domain.
      have h_inj : Function.Injective (fun a => W r + s - l + a) := by
        exact add_right_injective _
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
      set U := Finset.biUnion (S_r r) (fun s => translate_set A N r l s) with hU_def
      -- Since translates are disjoint, $|U| = |S_r| |A_l|$.
      have hU_card : (U.card : ℝ) = (S_r r).card * (A_l A N r l).card := by
        rw [ Finset.card_biUnion ]
        · simp +decide [ card_translate_set ]
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => Finset.disjoint_left.mp ( translates_disjoint A N r l x y ( by aesop ) ( by aesop ) hxy ) hz₁ hz₂
      -- Number of squarefree in $U$ is $|U| - |U \cap \text{non-sq}| \ge |U| - |T \cap \text{non-sq}| > \delta N / 4 - \delta N / 8 = \delta N / 8$.
      have h_squarefree_U : ((U.filter Squarefree).card : ℝ) > δ * N / 8 := by
        have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≥ (U.card : ℝ) - ((T_finset N r).filter (fun n => ¬ Squarefree n)).card := by
          have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≥ (U.card : ℝ) - ((U.filter (fun n => ¬ Squarefree n)).card : ℝ) := by
            rw [
              show ( Finset.filter Squarefree U ) = U \ ( Finset.filter ( fun n => ¬Squarefree n ) U ) by
                ext
                aesop,
              Finset.card_sdiff
            ]
            norm_num
            rw [ Nat.cast_sub ] <;> norm_num [ Finset.filter_inter ] ; exact Finset.card_le_card fun x hx => by aesop
          refine le_trans ?_ h_squarefree_U
          gcongr
          exact Finset.biUnion_subset.mpr fun s hs => translates_subset_T A N r l s hs ( by aesop )
        rw [ gt_iff_lt, div_lt_iff₀ ] at *
        all_goals
          nlinarith [ show ( W r : ℝ ) > 0 by positivity ]
      contrapose! h_squarefree_U
      have h_squarefree_U : ((U.filter Squarefree).card : ℝ) ≤ ∑ s ∈ S_r r, ((translate_set A N r l s).filter Squarefree).card := by
        rw [ Finset.filter_biUnion ]
        exact_mod_cast Finset.card_biUnion_le
      simp +zetaDelta at *
      refine le_trans h_squarefree_U <| le_trans ( Finset.sum_le_sum ‹_› ) ?_
      norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ne_of_gt ( show 0 < ( S_r r |> Finset.card : ℝ ) from lt_of_le_of_lt ( by positivity ) h_Sr_large ) ]

/-
If for arbitrarily large N there is a shift n in a finite set S such that the number of squarefree translates is proportional to N, then there is a shift n in S for which there are infinitely many squarefree translates.
-/
lemma infinite_squarefree_of_frequent_dense_shifts (A : Set ℕ) (S : Finset ℕ) (c : ℝ) (hc : c > 0)
    (h_inf : ∀ k, ∃ N ≥ k, ∃ n ∈ S, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N) :
    ∃ n ∈ S, ({a ∈ A | Squarefree (n + a)}).Infinite := by
      by_contra h_contra
      -- Since $S$ is finite, by the infinite pigeonhole principle, there exists an $n \in S$ such that for infinitely many $N$, the count is $> c N$.
      obtain ⟨n, hnS, hn_inf⟩ : ∃ n ∈ S, Set.Infinite {N | ∃ N' ≥ N, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N'))) > c * N'} := by
        by_cases h_finite : ∀ n ∈ S, Set.Finite {N | ∃ N' ≥ N, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N'))) > c * N'}
        · exact absurd ( Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet S ) h_finite ) fun x hx => by aesop ) ( Set.infinite_univ.mono fun x _ => by obtain ⟨ N, hN₁, n, hn₁, hn₂ ⟩ := h_inf x; exact ⟨ n, hn₁, N, hN₁, hn₂ ⟩ )
        · aesop
      -- Since the set of a in A such that n + a is squarefree is finite, there exists some maximum element M in this set.
      obtain ⟨M, hM⟩ : ∃ M, ∀ a ∈ {a | a ∈ A ∧ Squarefree (n + a)}, a ≤ M := by
        exact Set.Finite.bddAbove <| Classical.not_not.1 fun h => h_contra ⟨ n, hnS, h ⟩
      -- For any $N > M$, the number of elements in $A$ up to $N$ that are squarefree when added to $n$ is at most $M$.
      have h_card_le_M : ∀ N > M, (Finset.card (Finset.filter (fun a => a ∈ A ∧ Squarefree (n + a)) (Finset.Icc 1 N))) ≤ M := by
        exact fun N hN => le_trans ( Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, hM x <| Finset.mem_filter.mp hx |>.2 ⟩ ) ( by simp )
      -- Choose $N$ large enough such that $cN > M$.
      obtain ⟨N, hN⟩ : ∃ N, N > M ∧ c * N > M := by
        exact ⟨ ⌊M / c⌋₊ + M + 1, by linarith, by
          push_cast
          nlinarith [ Nat.lt_floor_add_one ( M / c ), mul_div_cancel₀ ( M : ℝ ) hc.ne' ] ⟩
      obtain ⟨ N', hN'₁, hN'₂ ⟩ := hn_inf.exists_gt N
      obtain ⟨ N'', hN''₁, hN''₂ ⟩ := hN'₁
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
        exact exists_l_large_A_l A N r δ hr h_card
      -- By `exists_s_many_squarefree`, there exists $s \in S_r$ such that the translate of $A_l$ by $n = W_r + s - l$ has $> \delta N / (8 |S_r|)$ squarefree elements.
      obtain ⟨s, hs₁, hs₂⟩ : ∃ s ∈ S_r r, ((translate_set A N r l s).filter Squarefree).card > δ * N / (8 * (S_r r).card) := by
        apply exists_s_many_squarefree
        all_goals norm_cast at *
      refine ⟨ W r + s - l, ?_, ?_ ⟩ <;> simp_all +decide [ S_shifts ]
      · exact ⟨ l, s, ⟨ hl₁, hs₁ ⟩, rfl ⟩
      · refine hs₂.trans_le ( mod_cast ?_ )
        refine le_trans ( Finset.card_le_card <| show Finset.filter Squarefree ( translate_set A N r l s ) ⊆ Finset.image ( fun a => W r + s - l + a ) ( Finset.filter ( fun a => a ∈ A ∧ Squarefree ( W r + s - l + a ) ) ( Finset.Icc 1 ( N - 2 * W r ) ) ) from ?_ ) ?_
        · simp +decide [ Finset.subset_iff, translate_set ]
          unfold A_l
          aesop
        · rw [ Finset.card_image_of_injective _ fun x y hxy => by linarith [ Nat.sub_add_cancel ( show l ≤ W r + s from by linarith ) ] ] ; gcongr ; aesop

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
            convert hδ using 1
            unfold upperDensity
            norm_num [ Set.ncard_eq_toFinset_card' ]
          contrapose! h_lim_sup
          refine ne_of_lt ( lt_of_le_of_lt
            (b := δ - ε)
            ( csInf_le (a := δ - ε) ?_ ?_ ) ?_ )
          · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN N le_rfl ) ⟩
          · exact Filter.eventually_atTop.mpr ( by obtain ⟨ N, hN₁, hN₂ ⟩ := h_lim_sup 0; exact ⟨ N, fun n hn => le_of_lt ( hN₂ n hn ) ⟩ )
          · linarith
        exact Exists.elim ( h_upper_density ε hε_pos ) fun k hk => ⟨ k + 1, fun N hN => by obtain ⟨ n, hn₁, hn₂ ⟩ := hk N ( by linarith ) ; exact ⟨ n, hn₁, by rw [ ge_iff_le, le_div_iff₀ ( Nat.cast_pos.mpr <| by linarith ) ] at hn₂; linarith ⟩ ⟩
      intro k
      obtain ⟨k', hk'⟩ : ∃ k', ∀ N ≥ k', ∃ n ≥ N, ((Finset.Icc 1 n).filter (fun a => a ∈ A)).card ≥ (δ - δ / 4) * n := h_upper_density (δ / 4) (by linarith)
      obtain ⟨ n, hn₁, hn₂ ⟩ := hk' ( k' + k + 4 * C + 1 ) ( by linarith )
      refine ⟨ n + C, by linarith, ?_ ⟩ ; norm_num at *
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
            have := density_S_r_tendsto
            convert this using 2
            rw [ show ( S_r _ : Finset ℕ ).card = ∏ i ∈ Finset.range _, ( ( Nat.nth Nat.Prime i ) ^ 2 - 1 ) from ?_, show ( W _ : ℕ ) = ∏ i ∈ Finset.range _, ( Nat.nth Nat.Prime i ) ^ 2 from ?_ ]
            any_goals exact ‹ℕ›
            · norm_num [ Nat.cast_sub ( Nat.one_le_pow _ _ ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) ) ) ]
              rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ]
              intros
              rw [ inv_eq_one_div, sub_div, div_self ]
              norm_cast
              exact pow_ne_zero _ <| Nat.Prime.ne_zero <| by aesop
            · unfold W
              norm_num [ Finset.prod_pow ]
            · (expose_names; exact card_S_r x)
          have h_prod_gt_half : ∀ r, ∏ i ∈ Finset.range r, (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) ≥ 6 / Real.pi ^ 2 := by
            intro r
            have h_prod_gt_half : ∀ r, ∏ i ∈ Finset.range r, (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) ≥ ∏ i ∈ Finset.range (r + 1), (1 - 1 / ((Nat.nth Nat.Prime i : ℝ) ^ 2)) := by
              norm_num [ Finset.prod_range_succ ]
              exact fun r => mul_le_of_le_one_right ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ) <| sub_le_self _ <| inv_nonneg.2 <| sq_nonneg _
            exact le_of_tendsto ‹_› ( Filter.eventually_atTop.mpr ⟨ r, fun n hn => by induction hn <;> [ tauto; linarith [ h_prod_gt_half ‹_› ] ] ⟩ )
          refine lt_of_lt_of_le ?_ ( h_prod_gt_half r )
          rw [ div_lt_div_iff₀ ]
          all_goals
            nlinarith only [ Real.pi_gt_three, show Real.pi < 3.4 by pi_upper_bound [ 7 / 5 ] ]
        -- By definition of $S_r$, we know that $|S_r| = W_r \prod_{i=1}^r (1 - 1/p_i^2)$.
        have h_card_S_r : (S_r r).card = (W r : ℝ) * ∏ i ∈ Finset.range r, (1 - 1 / (Nat.nth Nat.Prime i : ℝ) ^ 2) := by
          have h_card_S_r : (S_r r).card = ∏ i ∈ Finset.range r, ((Nat.nth Nat.Prime i)^2 - 1) := by
            exact card_S_r r
          simp_all +decide
          rw [ Finset.prod_congr rfl fun _ _ => Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| by aesop ] ; norm_num [ Finset.prod_mul_distrib, W ]
          rw [ ← Finset.prod_pow ]
          rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_congr rfl fun _ _ => by nlinarith only [ mul_inv_cancel₀ ( show ( Nat.nth Nat.Prime ‹_› : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop ) ]
        nlinarith [ show ( W r : ℝ ) > 0 from mod_cast pow_pos ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) ) 2 ]
      exact Exists.elim ( card_non_squarefree_in_T_bound ( δ / 8 ) ( by positivity ) ) fun r hr => ⟨ r, h_density r, hr ⟩

/-
If A has positive upper density, then there exists a finite set of shifts (S_shifts r) and a constant c > 0 such that for arbitrarily large N, one of the shifts produces more than c*N squarefree translates.
-/
lemma frequent_dense_shifts_of_positive_density (A : Set ℕ) (h_density : upperDensity A > 0) :
    ∃ r, ∃ c : ℝ, c > 0 ∧ ∀ k, ∃ N ≥ k, ∃ n ∈ S_shifts r, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N := by
      obtain ⟨r, hr⟩ : ∃ r : ℕ, ((S_r r).card : ℝ) > (W r : ℝ) / 2 ∧ ∀ N : ℕ, ((T_finset N r).filter (fun n => ¬ Squarefree n)).card ≤ (upperDensity A / 8) * N := by
        exact exists_suitable_r (upperDensity A) h_density
      refine ⟨ r, upperDensity A / ( 8 * ( S_r r |> Finset.card ) ), ?_, fun k => ?_ ⟩
      · exact div_pos h_density ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ 1, by
          refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩ <;> norm_num [ W ]
          · exact Nat.one_le_pow _ _ ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) )
          · exact fun i hi => Nat.Prime.ne_one <| Nat.prime_nth_prime i ⟩ ) ) )
      · obtain ⟨ N, hN₁, hN₂ ⟩ := exists_large_N_with_density A ( upperDensity A ) rfl h_density ( 2 * W r ) k
        have := exists_good_shift_for_N A N r ( upperDensity A ) ?_ ?_ ?_ ?_ <;> norm_num at *
        · exact ⟨ N, hN₁, this.choose, this.choose_spec.1, by convert this.choose_spec.2 using 1; ring ⟩
        · exact pow_pos ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) ) _
        · exact hr.1
        · exact hr.2 N
        · linarith

/-
If a strictly increasing sequence A has natural density 0, then A(j)/j tends to infinity.
-/
lemma tendsto_div_of_density_zero (A : ℕ → ℕ) (h_inc : StrictMono A) (h_dens : HasNaturalDensity (Set.range A) 0) : Filter.Tendsto (fun j => (A j : ℝ) / j) Filter.atTop Filter.atTop := by
  -- Since $A$ is strictly increasing, $A(j) \ge j$. The number of elements of $S$ in $[1, x]$ is approximately $A^{-1}(x)$. Specifically, $|S \cap [1, A(j)]| = j+1$ (assuming $A(0) \ge 1$, or similar).
  have h_card : ∀ j : ℕ, j ≥ 1 → ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ j := by
    intros j hj
    have h_range : Set.range A ∩ Set.Icc 1 (A j) ⊇ Finset.image A (Finset.Icc 1 j) := by
      simp +decide [ Set.subset_def ]
      exact fun x y hy₁ hy₂ hx => ⟨ ⟨ y, hx ⟩, hx ▸ Nat.one_le_iff_ne_zero.mpr ( by linarith [ h_inc <| show 0 < y from hy₁ ] ), hx ▸ h_inc.monotone hy₂ ⟩
    refine mod_cast le_trans ?_ ( Set.ncard_le_ncard h_range )
    rw [ Set.ncard_coe_finset, Finset.card_image_of_injective _ h_inc.injective ]
    aesop
  -- This implies $A(j) / (j+1) \to \infty$, so $A(j) / j \to \infty$.
  have h_lim : Filter.Tendsto (fun j : ℕ => ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) / (A j)) Filter.atTop (nhds 0) := by
    exact h_dens.comp h_inc.tendsto_atTop
  -- Since $|S \cap [1, A(j)]| \ge j$, we have $j / A(j) \le |S \cap [1, A(j)]| / A(j)$.
  have h_le : ∀ j : ℕ, j ≥ 1 → (j : ℝ) / (A j) ≤ ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) / (A j) := by
    bound
  -- Since $j / A(j) \le |S \cap [1, A(j)]| / A(j)$ and $|S \cap [1, A(j)]| / A(j) \to 0$, it follows that $j / A(j) \to 0$.
  have h_j_div_A_j_zero : Filter.Tendsto (fun j : ℕ => (j : ℝ) / (A j)) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun j hj => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_le j hj ⟩ ) h_lim
  have h_j_div_A_j_zero : Filter.Tendsto (fun j : ℕ => (A j : ℝ) / j) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun j : ℕ => (j : ℝ) / (A j)) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [ tendsto_nhdsWithin_iff ]
      exact ⟨ h_j_div_A_j_zero, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by simpa using div_pos ( Nat.cast_pos.mpr hn ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by linarith [ h_inc hn ] ) ) ) ⟩ ⟩
    have : Filter.Tendsto (fun j : ℕ => ((j : ℝ) / (A j))⁻¹) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.inv_tendsto_nhdsGT_zero this
    aesop
  convert h_j_div_A_j_zero using 1

/-
If a set A has property P, then it has natural density 0.
-/
theorem Theorem1_i (A : Set ℕ) (hA : PropertyP A) : HasNaturalDensity A 0 := by
  -- Apply the lemma frequent_dense_shifts_of_positive_density to get the existence of r and c, then use infinite_squarefree_of_frequent_dense_shifts to get the contradiction.
  by_contra h_contra
  obtain ⟨r, c, hc_pos, h_freq⟩ : ∃ r, ∃ c : ℝ, c > 0 ∧ ∀ k, ∃ N ≥ k, ∃ n ∈ S_shifts r, ((Finset.Icc 1 N).filter (fun a => a ∈ A ∧ Squarefree (n + a))).card > c * N := by
    convert frequent_dense_shifts_of_positive_density A _
    unfold upperDensity
    refine lt_of_not_ge fun h => h_contra ?_
    refine tendsto_order.2 ⟨ ?_, ?_ ⟩
    · exact fun x hx => Filter.Eventually.of_forall fun n => hx.trans_le <| by positivity
    · rw [ Filter.limsup_eq ] at h
      rw [ Real.sInf_le_iff ] at h
      · exact fun ε hε => by
          obtain ⟨ x, hx₁, hx₂ ⟩ := h ε hε
          filter_upwards [ hx₁ ] with n hn
          linarith
      · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ n, hn ⟩ ; exact le_trans ( by positivity ) ( hn _ le_rfl ) ⟩
      · exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by norm_num [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩ ⟩
  obtain ⟨n, hn⟩ : ∃ n ∈ S_shifts r, ({a ∈ A | Squarefree (n + a)}).Infinite := by
    apply infinite_squarefree_of_frequent_dense_shifts A (S_shifts r) c hc_pos h_freq
  exact hn.2 ( Set.Finite.subset ( hA n |> Set.Finite.union <| Set.finite_singleton 0 ) fun x hx => by cases x <;> aesop )

/-
Theorem 1(ii): For any function f that goes to infinity, a sequence A with
Property P exists that satisfies the growth condition a_j/j <= f(j).
-/
theorem Theorem1_ii (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (hf_pos : ∀ n, 1 ≤ f n) :
    PropertyP_positive (A_constructed f hf) ∧ ∀ j ≥ 1, (a_seq f hf j : ℝ) / j ≤ f j := by
      refine ⟨ A_constructed_PropertyP_positive f hf, fun j hj => ?_ ⟩
      -- By combining the results from a_seq_upper_bound and W_k_le_f_proof, we get the desired inequality.
      have h_combined : a_seq f hf j ≤ j * f j := by
        refine le_trans ( a_seq_upper_bound f hf j hj ) ?_
        exact Nat.mul_le_mul_left _ ( W_k_le_f_proof f hf hf_pos j )
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
  convert tendsto_div_of_density_zero A h_inc _
  -- Since the range of A is a subset of the set of numbers that are not squarefree, and squarefree numbers have density 0, the range of A must also have density 0.
  apply Classical.byContradiction
  intro h_nonzero_density
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, upperDensity (Set.range A) = δ := by
    refine ⟨ upperDensity (Set.range A), ?_, rfl ⟩
    contrapose! h_nonzero_density
    refine tendsto_order.2 ⟨ ?_, ?_ ⟩
    · exact fun x hx => Filter.Eventually.of_forall fun n => hx.trans_le <| by positivity
    · intro a ha
      have := h_nonzero_density
      simp_all +decide [ upperDensity ]
      rw [ Filter.limsup_eq ] at h_nonzero_density
      simp +zetaDelta at *
      exact Exists.elim ( show ∃ x, x ∈ { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → ( Set.range A ∩ Set.Icc 1 b |> Set.ncard : ℝ ) / b ≤ a } ∧ x < a from exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → ( Set.range A ∩ Set.Icc 1 b |> Set.ncard : ℝ ) / b ≤ a }.Nonempty from ⟨ _, ⟨ 0, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩ ⟩ ) <| lt_of_le_of_lt h_nonzero_density ha ) fun x hx => ⟨ hx.1.choose, fun n hn => lt_of_le_of_lt ( hx.1.choose_spec n hn ) hx.2 ⟩
  have := frequent_dense_shifts_of_positive_density ( Set.range A ) ( by linarith )
  obtain ⟨ r, c, hc_pos, hc ⟩ := this
  obtain ⟨ n, hn ⟩ := infinite_squarefree_of_frequent_dense_shifts ( Set.range A ) ( S_shifts r ) c hc_pos hc
  exact hn.2 ( Set.Finite.subset ( hP n ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hn.1 ( by
    simp +decide [ S_shifts ]
    exact fun x y hx hy => Nat.sub_ne_zero_of_lt ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hy |>.1 ) ] ) ) ) ) ) fun x hx => by aesop )

theorem erdos_1102.exists_sequence_with_P
    (f : ℕ → ℕ) (h_inf : Tendsto f atTop atTop)
    (h_pos : ∀ n, f n ≠ 0) :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    HasPropertyP (range A) ∧
    ∀ j : ℕ, (A j : ℝ) / j ≤ f j := by
  refine ⟨ fun j => a_seq f h_inf j, ?_, ?_, ?_ ⟩
  · exact a_seq_strict_mono f h_inf
  · intro n hn
    have h_finite : ∀ n ≥ 1, {a ∈ Set.range (a_seq f h_inf) | Squarefree (n + a)}.Finite := by
      convert A_constructed_PropertyP_positive f h_inf using 1
      constructor
      all_goals
        intro h n hn
      all_goals
        simp_all +decide [ PropertyP_positive, A_constructed ]
      · exact Set.Finite.subset ( h n hn ) fun x hx => by
          obtain ⟨ ⟨ j, hj₁, rfl ⟩, hx' ⟩ := hx
          exact ⟨ ⟨ j, rfl ⟩, hx' ⟩
      · refine Set.Finite.subset ( h n hn |> Set.Finite.union <| Set.finite_singleton ( a_seq f h_inf 0 ) ) ?_
        intro a ha
        cases' ha with ha₁ ha₂; cases' ha₁ with j hj; cases' j with j <;> aesop
    exact h_finite n hn
  · intro j
    by_cases hj : 1 ≤ j <;> simp_all +decide
    field_simp
    exact_mod_cast le_trans ( a_seq_upper_bound f h_inf j hj ) ( mul_le_mul_of_nonneg_left ( W_k_le_f f h_inf ( fun n => Nat.pos_of_ne_zero ( h_pos n ) ) j ) ( Nat.cast_nonneg _ ) )

#print axioms erdos_1102.exists_sequence_with_P
-- 'Erdos1102.erdos_1102.exists_sequence_with_P' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end

end Erdos1102

/- ---------------------------------------------------------------------------- -/
/- Concatenated from ErdosProblem1102PropertyQDensity.lean -/
namespace Erdos1102b


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

Any sequence with property $Q$ has upper density at most $6/\pi^2$. On the other
hand, sequences with property $Q$ exist which have natural density equal to
$6/\pi^2$.

At the very end you can find the (relevant parts of the) statement of Erdős
Problem #1102 taken from the Formal Conjectures project by Google DeepMind,
which we also prove.

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1102.lean

-/


open Squarefree Set Order Filter Topology


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable



noncomputable section

/-
SF is the set of squarefree numbers.
-/
def SF : Set ℕ := {n | Squarefree n}

/-
A set A has property Q if for infinitely many n, n+a is squarefree for all a in A with a < n.
-/
def PropertyQ (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, a < n → Squarefree (n + a)}).Infinite

/-
A set A is admissible if for every prime p, there is a residue class mod p^2 that A avoids.
-/
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b

/-
Every set with property Q is admissible.
-/
theorem PropertyQ_implies_Admissible (A : Set ℕ) (h : PropertyQ A) : Admissible A := by
  intro p hp
  obtain ⟨S, hS_inf, hS⟩ : ∃ S : Set ℕ, S.Infinite ∧ ∀ n ∈ S, ∀ a ∈ A, a < n → ¬(n + a) % p^2 = 0 := by
    refine ⟨ {n | ∀ a ∈ A, a < n → Squarefree (n + a)}, h, fun n hn a ha ha' => ?_ ⟩
    intro H
    have := hn a ha ha'
    rw [ ← Nat.dvd_iff_mod_eq_zero ] at H
    have := this.squarefree_of_dvd H
    simp_all +decide [ sq, Nat.squarefree_mul_iff ]
  -- By the pigeonhole principle, since there are infinitely many $n$ in $S$ and only finitely many residue classes mod $p^2$, there must be a residue class $b$ such that $b_n = b$ for infinitely many $n$.
  obtain ⟨b, hb⟩ : ∃ b < p^2, Set.Infinite {n ∈ S | n % p^2 = b} := by
    by_contra h_contra
    exact hS_inf <| Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_lt_nat <| p ^ 2 ) fun i hi => Set.not_infinite.mp fun hi' => h_contra ⟨ i, hi, hi' ⟩ ) fun x hx => by
      have := Nat.mod_lt x ( pow_pos hp.pos 2 )
      aesop
  use ( p^2 - b % p^2 ) % p^2
  refine ⟨ Nat.mod_lt (p ^ 2 - b % p ^ 2) ( pow_pos hp.pos 2 ), fun a ha ha' => ?_ ⟩
  -- Since there are infinitely many $n \in S$ such that $n \equiv b \pmod{p^2}$, we can choose $n$ large enough so that $n > a$.
  obtain ⟨n, hnS, hn_gt⟩ : ∃ n ∈ S, n > a ∧ n % p^2 = b := by
    exact Exists.elim ( hb.2.exists_gt a ) fun n hn => ⟨ n, hn.1.1, hn.2, hn.1.2 ⟩
  specialize hS n hnS a ha hn_gt.1
  simp_all +decide [ Nat.add_mod ]
  simp_all +decide [ Nat.add_sub_of_le ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ]

/-
Property Q is downwardly monotone.
-/
lemma PropertyQ_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyQ B) : PropertyQ A := by
  contrapose! hB
  unfold PropertyQ at *
  simp +zetaDelta at *
  refine Set.Finite.subset ( hB.union ( Set.finite_singleton 0 ) ) ?_
  intro n
  aesop

/-
A set A has natural density d if the proportion of elements in A up to n tends to d as n goes to infinity.
-/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds d)

/-
The sum of mu(d) for d such that d^2 divides n is 1 if n is squarefree and 0 otherwise.
-/
lemma sum_moebius_sq_dvd_eq_indicator (n : ℕ) (hn : n > 0) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), ArithmeticFunction.moebius d = if Squarefree n then 1 else 0 := by
      -- Let $k$ be the product of the primes dividing $n$.
      set k := ∏ p ∈ Nat.primeFactors n, p ^ (Nat.factorization n p / 2) with hk_def
      -- If $n$ is not squarefree, then $k > 1$.
      by_cases h_squarefree : Squarefree n
      · -- If $n$ is squarefree, then the only divisor $d$ such that $d^2 \mid n$ is $d = 1$.
        have h_divisors : ∀ d ∈ Finset.Icc 1 n, d^2 ∣ n → d = 1 := by
          exact fun d hd hdn => by
            have := h_squarefree.squarefree_of_dvd hdn
            rw [ sq, Nat.squarefree_mul_iff ] at this
            aesop
        rw [ Finset.sum_eq_single 1 ]
        all_goals
          norm_num [ h_squarefree ]
        · exact fun b hb₁ hb₂ hb₃ hb₄ => False.elim <| hb₄ <| h_divisors b ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ ) hb₃
        · linarith
      · -- If $n$ is not squarefree, then $k > 1$ and the sum becomes $\sum_{d \mid k} \mu(d)$.
        have h_sum_divisors : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d)) = (∑ d ∈ Nat.divisors k, (ArithmeticFunction.moebius d)) := by
          have h_sum_divisors : Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n) = Nat.divisors k := by
            ext d
            constructor
            all_goals
              intro hd
            all_goals
              simp_all +decide
            · -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $2 \cdot \text{exponent}(p \text  {  in } d) \leq \text{exponent}(p \text{ in } n)$.
              have h_exp : ∀ p ∈ Nat.primeFactors d, 2 * (Nat.factorization d p) ≤ Nat.factorization n p := by
                intro p hp
                have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hd.2
                aesop
              -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $d.factorization p \leq (Nat.factorization n p) / 2$.
              have h_exp_le : ∀ p ∈ Nat.primeFactors d, d.factorization p ≤ (Nat.factorization n p) / 2 := by
                exact fun p hp => by
                  rw [ Nat.le_div_iff_mul_le zero_lt_two ]
                  linarith [ h_exp p hp ]
              refine ⟨ ?_, Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero (n.factorization p / 2) <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ⟩
              conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : d ≠ 0 ) ]
              rw [ ← Finset.prod_sdiff <| show d.primeFactors ⊆ n.primeFactors from Nat.primeFactors_mono ( dvd_of_mul_left_dvd hd.2 ) <| by aesop ]
              exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p ( h_exp_le p hp ) ) _
            · refine ⟨ ⟨ Nat.pos_of_dvd_of_pos hd.1 ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) (n.factorization p / 2) ), Nat.le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) (n.factorization p / 2) ) hd.1 ) ?_ ⟩, ?_ ⟩
              · conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self hn.ne' ]
                exact Finset.prod_le_prod' fun p hp => pow_le_pow_right₀ ( Nat.pos_of_mem_primeFactors hp ) ( Nat.div_le_self _ _ )
              · refine dvd_trans ( pow_dvd_pow_of_dvd hd.1 2 ) ?_
                conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self hn.ne' ]
                rw [ ← Finset.prod_pow ]
                exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => by
                  rw [ ← pow_mul ]
                  exact pow_dvd_pow _ ( Nat.div_mul_le_self _ _ )
          congr
        -- Since $k > 1$, we can apply the property of the Möbius function that $\sum_{d \mid k} \mu(d ( )  = 0$.
        have h_moebius_sum : ∀ {m : ℕ}, 1 < m → (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = 0 := by
          intros m hm_gt_one
          have h_moebius_sum : (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
            exact Eq.symm ArithmeticFunction.coe_mul_zeta_apply
          simp_all +decide [ ArithmeticFunction.moebius_mul_coe_zeta ]
          exact if_neg hm_gt_one.ne'
        rw [ if_neg h_squarefree, h_sum_divisors, h_moebius_sum ]
        contrapose! h_squarefree
        -- If $k \leq 1$, then for all primes $p$ dividing $n$, we have $p^{Nat.factorization n p / 2} \leq 1$, which implies $Nat.factorization n p / 2 = 0$, hence $Nat.factorization n p < 2$.
        have h_factorization : ∀ p ∈ Nat.primeFactors n, Nat.factorization n p < 2 := by
          exact fun p hp => Nat.lt_succ_of_le ( Nat.le_of_not_lt fun h => h_squarefree.not_gt <| lt_of_lt_of_le ( by exact one_lt_pow₀ ( Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) <| Nat.ne_of_gt <| Nat.div_pos ( by linarith ) zero_lt_two ) <| Nat.le_of_dvd ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos <| Nat.prime_of_mem_primeFactors hq ) _ ) <| Finset.dvd_prod_of_mem _ hp )
        rw [ Nat.squarefree_iff_prime_squarefree ]
        intro p pp dp
        specialize h_factorization p
        simp_all +decide [← sq]
        exact absurd ( h_factorization ( dvd_of_mul_left_dvd dp ) hn.ne' ) ( by have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 dp; aesop )

/-
The number of squarefree integers up to N is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
-/
lemma sum_squarefree_indicator_eq_sum_moebius_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (N / d ^ 2 : ℤ) := by
      -- We'll use the fact that if the condition holds for all $n \leq N$, then the sums are equal.
      have h_sum_eq : ∀ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0) := by
        intro n hn
        have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 (Nat.sqrt N)), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
          have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
            convert sum_moebius_sq_dvd_eq_indicator n ( Finset.mem_Icc.mp hn |>.1 ) using 1
          rw [ ← h_sum, Finset.sum_subset ]
          · simp +contextual [ Finset.subset_iff ]
            exact fun x hx₁ hx₂ hx₃ => Nat.le_of_dvd ( Finset.mem_Icc.mp hn |>.1 ) ( dvd_of_mul_left_dvd hx₃ )
          · simp +zetaDelta at *
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( Nat.le_sqrt.mpr <| by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃
        simp_all +decide [ Finset.sum_ite ]
      -- By interchanging the order of summation, we can rewrite the right-hand side of the equation.
      have h_interchange : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0))) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (∑ n ∈ Finset.Icc 1 N, (if d^2 ∣ n then 1 else 0))) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ]
      convert h_interchange using 1
      · exact Finset.sum_congr rfl h_sum_eq
      · refine Finset.sum_congr rfl fun x hx => ?_
        simp +zetaDelta at *
        rw [
          show Finset.filter ( fun y => x ^ 2 ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x ^ 2 * y ) ( Finset.Icc 1 ( N / x ^ 2 ) ) from ?_,
          Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( pow_ne_zero 2 ( by linarith : x ≠ 0 ) ) h
        ]
        focus
          norm_num
        -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro y
        simp
        exact ⟨ fun h => ⟨ y / x ^ 2, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( pow_pos ( by linarith ) 2 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ pow_pos ( by linarith : 0 < x ) 2 ], by nlinarith [ Nat.div_mul_le_self N ( x ^ 2 ) ] ⟩, by norm_num ⟩ ⟩

/-
The partial sums of mu(d)/d^2 converge to 6/pi^2.
-/
lemma sum_moebius_div_sq_tendsto : Filter.Tendsto (fun k => ∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ) / d ^ 2) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  -- We know that $\sum_{d=1}^{\infty} \frac{\mu(d)}{d^2} = \frac{1}{\zeta(2)}$.
  have h_sum : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ) = 1 / (Real.pi ^ 2 / 6) := by
    -- By definition of $L(2, \mu)$, we know that $L(2, \mu) = \sum_{d=1}^{\infty} \frac{\mu(d)}{d^2}$.
    have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (riemannZeta 2)⁻¹ := by
      have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) := by
        norm_num [ LSeries ]
        convert Complex.ofReal_tsum _
        norm_num [ LSeries.term ]
        aesop
      have h_L2_mu : (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) * (riemannZeta 2) = 1 := by
        convert ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius _ using 1
        focus
          rw [ mul_comm ]
        focus
          rw [ ArithmeticFunction.LSeries_zeta_eq_riemannZeta ]
        · norm_num
        · norm_num
      exact eq_inv_of_mul_eq_one_left <| by aesop
    -- We know that $\zeta(2) = \frac{\pi^2}{6}$.
    have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := by
      exact riemannZeta_two
    simp_all +decide [ Complex.ext_iff, sq ]
    norm_cast
  convert h_sum ▸ Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 2 <;> norm_num [ Finset.sum_Ico_eq_sub ]
  · erw [ Finset.sum_Ico_eq_sub _ _ ]
    all_goals
      norm_num
  · exact ( by contrapose! h_sum; erw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity )

/-
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
The number of integers in an interval of length L that are congruent to a modulo m is L/m + O(1).
-/
lemma card_filter_modEq_Icc (u L a m : ℕ) (hm : m > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S := I.filter (fun x => x ≡ a [MOD m])
  abs ((S.card : ℝ) - (L : ℝ) / m) ≤ 2 := by
    refine abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩
    · refine le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_le_card <| show Finset.filter ( fun x => x ≡ a [MOD m] ) ( Finset.Icc u ( u + L - 1 ) ) ⊆ Finset.image ( fun k => m * k + a % m ) ( Finset.Icc ( u / m ) ( ( u + L - 1 ) / m ) ) from ?_ ) ((L : ℝ) / m) ) ?_
      · intro x hx
        simp_all +decide [ Nat.ModEq ]
        exact ⟨ x / m, ⟨ Nat.div_le_div_right hx.1.1, Nat.div_le_div_right hx.1.2 ⟩, by linarith [ Nat.mod_add_div x m ] ⟩
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by nlinarith [ Nat.mod_lt a hm ] ] ; norm_num
        rcases L with ( _ | L )
        all_goals
          norm_num [ Nat.succ_div ]
        ·
          exact lt_add_of_pos_of_le zero_lt_two ( Nat.div_le_div_right ( Nat.pred_le _ ) )
        · field_simp
          exact mod_cast by nlinarith [ Nat.div_mul_le_self ( u + L ) m, Nat.div_add_mod ( u + L ) m, Nat.mod_lt ( u + L ) hm, Nat.div_mul_le_self u m, Nat.div_add_mod u m, Nat.mod_lt u hm, Nat.sub_add_cancel ( show u / m ≤ ( u + L ) / m + 1 from Nat.le_succ_of_le ( Nat.div_le_div_right ( by linarith ) ) ) ]
    · -- The set of integers in [u, u+L-1] that are congruent to a modulo m forms an arithmetic progression with common difference m.
      have h_arith_prog : Finset.filter (fun x => x ≡ a [MOD m]) (Finset.Icc u (u + L - 1)) ⊇ Finset.image (fun k => u + ((a + m - u % m) % m) + k * m) (Finset.range (L / m)) := by
        intro x hxaesop
        norm_num +zetaDelta at *
        rcases hxaesop with ⟨ k, hk₁, rfl ⟩
        exact ⟨ ⟨ by nlinarith [ Nat.zero_le ( ( a + m - u % m ) % m ) ], Nat.le_sub_one_of_lt ( by nlinarith [ Nat.div_mul_le_self L m, Nat.zero_le ( ( a + m - u % m ) % m ), Nat.mod_lt ( a + m - u % m ) hm ] ) ⟩, by simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ( show u % m ≤ a + m from by linarith [ Nat.mod_lt u hm ] ) ] ⟩
      have := Finset.card_mono h_arith_prog
      simp_all +decide [ Finset.card_image_of_injective, Function.Injective, hm.ne' ]
      rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_add_mod L m, Nat.mod_lt L hm ]

/-
The number of integers in an interval of length L satisfying two coprime modular constraints is L/(Wq) + O(1).
-/
lemma card_intersect_bound (u L W q b c : ℕ) (hWq : Nat.Coprime W q) (hW : W > 0) (hq : q > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q])
  abs ((S_intersect.card : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
    -- By the Chinese Remainder Theorem, there exists a unique solution modulo $Wq$ to the system of congruences $n \equiv b \pmod{W}$ and $n \equiv c \pmod{q}$.
    obtain ⟨a, ha⟩ : ∃ a, a ≡ b [MOD W] ∧ a ≡ c [MOD q] ∧ a < W * q := by
      have := Nat.chineseRemainder hWq b c
      exact ⟨ this.val % ( W * q ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.2, Nat.mod_lt _ ( Nat.mul_pos hW hq ) ⟩
    -- The set of integers in $I$ that are congruent to $a$ modulo $Wq$ is exactly the set of integers in $I$ that satisfy both congruences.
    have h_set_eq : {n ∈ Finset.Icc u (u + L - 1) | n ≡ b [MOD W] ∧ n ≡ c [MOD q]} = {n ∈ Finset.Icc u (u + L - 1) | n ≡ a [MOD (W * q)]} := by
      ext n
      simp_all +decide
      intro _ _
      rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ]
      focus
        simp_all +decide [ Nat.ModEq ]
      assumption
    convert card_filter_modEq_Icc u L a ( W * q ) ( mul_pos hW hq ) using 1
    aesop

/-
Lemma freq: Let b mod W, c mod q be congruence classes with W coprime to q, and let I be an interval of length L >= W. Then, if n is drawn uniformly at random from those elements of b mod W that lie in I, the probability that n lies in c mod q is O(1/q + W/L).
-/
lemma lemma_freq :
  ∃ C : ℝ, C > 0 ∧ ∀ (W q : ℕ) (b c : ℕ) (u L : ℕ),
    Nat.Coprime W q → L ≥ W →
    let I := Finset.Icc u (u + L - 1)
    let S := I.filter (fun n => n ≡ b [MOD W])
    let N_S := S.card
    let N_intersect := (S.filter (fun n => n ≡ c [MOD q])).card
    N_S > 0 →
    (N_intersect : ℝ) / N_S ≤ C * (1 / (q : ℝ) + (W : ℝ) / L) := by
      refine ⟨ 4, by norm_num, fun W q b c u L hWq hL hS => ?_ ⟩
      -- Let's consider the two cases: $L \geq 4W$ and $W \leq L < 4W$.
      by_cases h_case : L ≥ 4 * W
      · -- Using the bounds from card_filter_modEq_Icc and card_intersect_bound, we have:
        have h_bound : (Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card ≤ (L : ℝ) / (W * q) + 2 ∧ (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card ≥ (L : ℝ) / W - 2 := by
          have h_bounds : abs ((Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card - (L : ℝ) / (W * q)) ≤ 2 ∧ abs ((Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card - (L : ℝ) / W) ≤ 2 := by
            apply And.intro
            · by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ Nat.Coprime ]
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · convert card_intersect_bound u L W q b c hWq ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) using 1
                simp +decide only [Finset.filter_filter]
            · by_cases hW : W = 0 <;> simp_all +decide [ Nat.ModEq ]
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · simpa [Nat.ModEq] using card_filter_modEq_Icc u L b W ( Nat.pos_of_ne_zero hW )
          exact ⟨ by linarith [ abs_le.mp h_bounds.1 ], by linarith [ abs_le.mp h_bounds.2 ] ⟩
        by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ division_def ]
        · exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_bound.1 ) ( by positivity ) ) ( by rw [ ← div_eq_mul_inv ] ; rw [ div_le_iff₀ ] <;> norm_cast <;> linarith [ Finset.card_pos.mpr hS ] )
        · norm_num [ Nat.modEq_iff_dvd ] at *
          field_simp
          rw [ div_le_iff₀ ] <;> norm_cast at * <;> cases L <;> norm_num at * ; nlinarith
        · rw [ ← div_eq_mul_inv, div_le_iff₀ ]
          · field_simp at *
            rw [ add_div', mul_div_assoc' ] <;> try norm_cast ; linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ]
            rw [ div_mul_eq_mul_div, le_div_iff₀ ]
            all_goals
              norm_cast at *
            all_goals
              try linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ]
            nlinarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq, mul_pos ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) ]
          · exact Nat.cast_pos.mpr ( Finset.card_pos.mpr hS )
      · refine le_trans ( div_le_one_of_le₀ ?_ ?_ ) ?_
        · exact_mod_cast Finset.card_mono <| Finset.filter_subset _ _
        · positivity
        · rcases q with ( _ | _ | q )
          all_goals
            norm_num at *
          · rw [ mul_div, le_div_iff₀ ]
            all_goals
              norm_cast
            all_goals
              linarith [ show L > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ]
          · exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_right <| by positivity ) zero_le_four )
          · field_simp
            rw [ add_div', mul_div_assoc', le_div_iff₀ ]
            all_goals
              norm_cast
            all_goals
              nlinarith

/-
If A is a subset of a periodic set B with period M, then the upper density of A is at most the density of B in one period.
-/
lemma density_of_subset_periodic (A B : Set ℕ) (M : ℕ) (hM : M > 0) (hB_per : ∀ n, n ∈ B ↔ n + M ∈ B) (hsub : A ⊆ B) :
  upperDensity A ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) / M := by
    field_simp
    refine le_trans ( mul_le_mul_of_nonneg_right ( show upperDensity A ≤ upperDensity ( B ) from ?_ ) ( Nat.cast_nonneg M ) ) ?_
    · apply_rules [ Filter.limsup_le_limsup ]
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_div_of_nonneg_right ( mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ hsub ) <| Nat.cast_nonneg _
      · refine ⟨ 0, fun x hx => ?_ ⟩
        norm_num at *
        exact le_trans ( by positivity ) ( hx.choose_spec _ le_rfl ) |> le_trans <| by norm_num
      · use 1
        norm_num [ Filter.IsBoundedUnder ]
        exact ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩
    · -- Since B is periodic with period M, its natural density exists and is equal to the density in one period, which is |B ∩ [1, M]| / M.
      have hB_nat_density : HasNaturalDensity B ((B ∩ Set.Icc 1 M).ncard / M : ℝ) := by
        -- Since B is periodic with period M, the number of elements of B in [1, N] is approximately (N/M) times the number of elements of B in [1, M].
        have hB_card : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) + M := by
          intro N
          have hB_card : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ)) + M := by
            have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≤ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro k
              have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                intro k
                have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                  intro k
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)) ⊆ (fun n => n + k * M) '' (B ∩ Set.Icc 1 M) := by
                    intro n hn
                    use n - k * M
                    norm_num at *
                    constructor
                    · have hB_card_period : ∀ k : ℕ, ∀ n ∈ B, n ≥ k * M + 1 → n - k * M ∈ B := by
                        intro k n hn hn'
                        induction k generalizing n with
                        | zero =>
                          norm_num at *
                          assumption
                        | succ k ih =>
                          norm_num at *
                          convert ih ( n - M ) ( by rw [ hB_per ] ; exact by rw [ Nat.sub_add_cancel ( by nlinarith ) ] ; exact hn ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ n ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf
                      exact ⟨ hB_card_period k n hn.1 hn.2.1, Nat.sub_pos_of_lt hn.2.1, by linarith ⟩
                    · rw [ Nat.sub_add_cancel ( by linarith ) ]
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard ≤ ((fun n => n + k * M) '' (B ∩ Set.Icc 1 M)).ncard := by
                    apply_rules [ Set.ncard_le_ncard ]
                    exact Set.Finite.image _ ( Set.finite_iff_bddAbove.mpr ⟨ M, fun x hx => hx.2.2 ⟩ )
                  rw [ Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ] at hB_card_period ; exact_mod_cast hB_card_period
                exact hB_card_period k
              induction k with
              | zero =>
                norm_num [ Set.ncard_eq_toFinset_card' ]
              | succ k ih =>
                have hB_card_period : ((B ∩ Set.Icc 1 ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) + ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) := by
                  norm_cast
                  convert Set.ncard_union_le _ _ using 2
                  ext
                  norm_num
                  ring_nf
                  grind
                grind
            have hB_card_bound : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 ((N / M + 1) * M)).ncard : ℝ) := by
              fapply Nat.cast_le.mpr
              apply Set.ncard_le_ncard
              · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc_right ( by nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM ] ) )
              · exact Set.finite_iff_bddAbove.mpr ⟨ _, fun x hx => hx.2.2 ⟩
            refine le_trans hB_card_bound <| le_trans ( hB_card_period _ ) ?_
            field_simp
            norm_cast
            nlinarith [ Nat.div_mul_le_self N M, show ( B ∩ Set.Icc 1 M ).ncard ≤ M from le_trans ( Set.ncard_le_ncard ( show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from fun x hx => hx.2 ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ]
          convert hB_card using 1
        have hB_card_lower : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) - M := by
          intro N
          have hB_card_lower_step : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≥ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
            intro k
            have hB_card_lower_step : ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) = ∑ i ∈ Finset.range k, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) := by
              induction k with
              | zero =>
                norm_num [ Set.ncard_eq_toFinset_card' ]
              | succ k ih =>
                rw [ Finset.sum_range_succ, ← ih ]
                rw_mod_cast [ ← Set.ncard_union_eq ]
                · congr with x
                  norm_num
                  ring_nf
                  grind
                · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₁.2, Set.mem_Icc.mp hx₂.2 ]
            -- Since B is periodic with period M, the number of elements of B in [i*M+1, (i+1)*M] is the same as the number of elements of B in [1, M].
            have hB_card_lower_step_periodic : ∀ i : ℕ, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) = ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro i
              have hB_card_lower_step_periodic : (B ∩ Set.Icc (i * M + 1) ((i + 1) * M)) = (fun x => x + i * M) '' (B ∩ Set.Icc 1 M) := by
                ext x
                simp [Set.mem_image]
                constructor
                · intro hx
                  use x - i * M
                  simp
                  refine ⟨ ⟨ ?_, ?_, ?_ ⟩, Nat.sub_add_cancel ( by linarith ) ⟩
                  · induction i generalizing x with
                    | zero =>
                      norm_num at *
                      tauto
                    | succ i ih =>
                      norm_num at *
                      convert ih ( x - M ) ( by rw [ hB_per ] ; exact by convert hx.1 using 1; rw [ Nat.sub_add_cancel ( by nlinarith ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf
                  · exact Nat.sub_pos_of_lt hx.2.1
                  · linarith
                · rintro ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩
                  exact ⟨ by exact Nat.recOn i ( by simpa using hy₁ ) fun n ihn => by simpa [ Nat.succ_mul, ← add_assoc ] using hB_per _ |>.1 ihn, by nlinarith, by nlinarith ⟩
              rw [ hB_card_lower_step_periodic, Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ]
            simp_all +singlePass [ mul_comm ]
          have hB_card_lower_step : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ ((B ∩ Set.Icc 1 ((N / M) * M)).ncard : ℝ) := by
            gcongr
            · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2.2 ⟩
            · exact Nat.div_mul_le_self _ _
          refine le_trans ?_ hB_card_lower_step
          refine le_trans ?_ ( ‹∀ k : ℕ, ( B ∩ Set.Icc 1 ( k * M ) |> Set.ncard : ℝ ) ≥ k * ( B ∩ Set.Icc 1 M |> Set.ncard : ℝ ) › ( N / M ) )
          field_simp
          rw [ sub_le_iff_le_add ]
          norm_cast ; nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM, show ( B ∩ Set.Icc 1 M |> Set.ncard ) ≤ M from le_trans ( Set.ncard_le_ncard <| show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ]
        refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
        refine squeeze_zero_norm' (a := fun n : ℕ => ( M : ℝ ) / n + ( M : ℝ ) / n) ?_ ?_
        · norm_num +zetaDelta at *
          refine ⟨ M + 1, fun n hn => abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩ ⟩ <;> ring_nf at * <;> norm_num at *
          · field_simp
            rw [ div_add', div_le_div_iff_of_pos_right ] <;> try norm_num ; linarith
            have := hB_card n
            rw [ ← @Nat.cast_le ℝ ] at *
            push_cast at *
            nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 n ).ncard : ℝ ), inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 M ).ncard : ℝ ) ]
          · have := hB_card_lower n
            have := hB_card n
            nlinarith [ inv_pos.mpr ( by norm_cast; linarith : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( M : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) + M ≤ n ) ]
        · simpa [div_eq_mul_inv] using Filter.Tendsto.add ( tendsto_const_nhds.mul (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from tendsto_inv_atTop_nhds_zero_nat) ) ( tendsto_const_nhds.mul (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from tendsto_inv_atTop_nhds_zero_nat) )
      unfold upperDensity HasNaturalDensity at *
      rw [ hB_nat_density.limsup_eq ]
      norm_num [ hM.ne' ]

/-
The product of (1 - 1/p^2) over primes p < k tends to 6/pi^2 as k goes to infinity.
-/
lemma prod_primes_inv_sq_tendsto : Filter.Tendsto (fun k => ∏ p ∈ Finset.filter Nat.Prime (Finset.range k), (1 - 1/(p:ℝ)^2)) Filter.atTop (nhds (6 / Real.pi^2)) := by
  -- The product over primes of (1 - 1/p^2) is the inverse of the sum over integers of 1/n^2 (Euler product). Since sum 1/n^2 = pi^2/6, the product is 6/pi^2.
  have h_euler_product : ∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = 6 / Real.pi^2 := by
    have h_euler_product : (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) = (∑' n : ℕ, 1 / (n^2 : ℝ))⁻¹ := by
      -- Apply the Euler product formula to the Riemann zeta function.
      have h_euler_product : ∀ s : ℝ, 1 < s → (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^s)⁻¹ else 1) = (∑' n : ℕ, (1 / (n : ℝ)^s)) := by
        intro s hs
        have := @EulerProduct.eulerProduct_hasProd
        specialize @this ℝ _ ( fun n => ( n : ℝ ) ⁻¹ ^ s ) _ _ _ _ <;> norm_num at *
        · intro m n hmn
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), mul_comm ]
        · exact Summable.abs <| by simpa [ Real.inv_rpow ] using Real.summable_nat_rpow_inv.2 hs
        · convert HasProd.tprod_eq ( this ( by rw [ Real.zero_rpow ( by positivity ) ] ) ) using 1
          · convert ( tprod_subtype _ _ ) |> Eq.symm using 1
            any_goals exact { p : ℕ | Nat.Prime p }
            any_goals try infer_instance
            rotate_right
            focus
              use fun p => 1 / ( 1 - 1 / ( p : ℝ ) ^ s )
            · simp +decide [ Set.mulIndicator ]
            · refine tprod_congr fun p => ?_
              rw [ one_div, ← tsum_geometric_of_lt_one ( by positivity ) ]
              · norm_num [ Real.inv_rpow ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ]
                norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_comm ]
              · exact div_lt_self zero_lt_one ( Real.one_lt_rpow ( mod_cast p.2.one_lt ) ( by positivity ) )
          · norm_num [ Real.inv_rpow ]
      convert congr_arg ( fun x : ℝ => x⁻¹ ) ( h_euler_product 2 ( by norm_num ) ) using 1
      · have h_prod_inv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p)⁻¹ = ∏' p, (f p)⁻¹ := by
          intros f hf_pos hf_summable
          have h_prod_inv : (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
            exact Eq.symm (Real.rexp_tsum_eq_tprod hf_pos hf_summable)
          have h_prod_inv' : (∏' p, (f p)⁻¹) = Real.exp (∑' p, Real.log ((f p)⁻¹)) := by
            have h_prod_inv' : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
              exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
            exact h_prod_inv' ( fun p => inv_pos.mpr ( hf_pos p ) ) ( by simpa [ Real.log_inv ] using hf_summable.neg ) ▸ by simp +decide
          simp_all +decide [Real.log_inv]
          rw [ ← Real.exp_neg, tsum_neg ]
        rw [ h_prod_inv ]
        · exact tprod_congr fun p => by split_ifs <;> norm_num
        · intro p
          split_ifs
          all_goals
            norm_num
          exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt ‹_› ) two_ne_zero
        · have h_sum_log : Summable (fun p : ℕ => if Nat.Prime p then Real.log (1 - 1 / (p : ℝ)^2)⁻¹ else 0) := by
            have h_log_bound : ∀ p : ℕ, Nat.Prime p → Real.log (1 - 1 / (p : ℝ)^2)⁻¹ ≤ 2 / (p : ℝ)^2 := by
              intro p hp
              rw [ Real.log_inv ]
              ring_nf
              nlinarith only [ Real.log_inv ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show 0 < 1 - ( p : ℝ ) ⁻¹ ^ 2 by exact sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), inv_mul_cancel₀ ( show ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ) ≠ 0 by exact ne_of_gt ( sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), show ( p : ℝ ) ⁻¹ ^ 2 ≤ 1 / 4 by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( inv_anti₀ ( by norm_num ) ( Nat.cast_le.mpr hp.two_le ) ) 2 ) ( by norm_num ) ]
            refine Summable.of_nonneg_of_le ( fun p => ?_ ) ( fun p => ?_ ) ( Real.summable_nat_pow_inv.2 one_lt_two |> Summable.mul_left 2 )
            · split_ifs <;> first | positivity | exact Real.log_nonneg <| by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ‹_›, one_div_mul_cancel <| show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero ‹_› ]
            · aesop
          exact h_sum_log.congr fun p => by split_ifs <;> simp +decide [ * ]
      · norm_cast
    field_simp
    rw [ h_euler_product, inv_mul_eq_div, div_eq_iff ] <;> first | positivity | have := hasSum_zeta_two; have := this.tsum_eq; norm_num at * ; nlinarith [ Real.pi_gt_three ]
  generalize_proofs at *
  (
  rw [ ← h_euler_product ]
  have h_euler_product : Filter.Tendsto (fun k => ∏ p ∈ Finset.range k, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) Filter.atTop (nhds (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) := by
    have h_abs_conv : Summable (fun p : ℕ => |Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)|) := by
      have h_log_conv : Summable (fun p : ℕ => |Real.log (1 - 1 / (p : ℝ)^2)|) := by
        -- We'll use the fact that |log(1 - x)| ≤ 2x for x in [0, 1/2].
        have h_log_bound : ∀ p : ℕ, p ≥ 2 → |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
          intros p hp
          have h_log_bound : |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
            have h_log_bound_aux : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → |Real.log (1 - x)| ≤ 2 * x := by
              intros x hx
              rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ]
              nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]
            exact h_log_bound_aux _ ⟨ by positivity, by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith ⟩
          generalize_proofs at *
          (
          exact h_log_bound)
        generalize_proofs at *
        (
        rw [ ← summable_nat_add_iff 2 ]
        exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_log_bound _ ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two ))
      generalize_proofs at *
      (
      exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => by split_ifs <;> norm_num ) h_log_conv)
    have h_exp_conv : Filter.Tendsto (fun k => Real.exp (∑ p ∈ Finset.range k, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) Filter.atTop (nhds (Real.exp (∑' p : ℕ, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp <| h_abs_conv.of_abs.hasSum.tendsto_sum_nat
    generalize_proofs at *
    (
    convert h_exp_conv using 2
    · rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by assumption ) two_ne_zero ) ]
    · have h_exp_conv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → ∏' p, f p = Real.exp (∑' p, Real.log (f p)) := by
        exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
      generalize_proofs at *
      (
      exact h_exp_conv ( fun p => by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt ‹_› ) two_ne_zero ) <| h_abs_conv.of_abs;))
  generalize_proofs at *
  (
  convert h_euler_product using 2
  simp +decide [ Finset.prod_ite ]))

/-
If A is admissible, then for any C, A is contained in a periodic set B whose density is the product of (1 - 1/p^2) for primes p <= C.
-/
lemma admissible_subset_periodic (A : Set ℕ) (h : Admissible A) (C : ℕ) :
  ∃ B : Set ℕ, A ⊆ B ∧
  (∃ M > 0, (∀ n, n ∈ B ↔ n + M ∈ B) ∧
   ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (1 - 1/(p:ℝ)^2)) := by
     -- For each prime p, let b_p be a residue class mod p^2 that A avoids.
     obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ p, Nat.Prime p → ∀ a ∈ A, ¬(a ≡ b p [MOD p^2]) := by
       have h_choose_residues : ∀ p, Nat.Prime p → ∃ b_p, ∀ a ∈ A, ¬(a ≡ b_p [MOD p^2]) := by
         intro p hp
         have h_residue : ∃ b_p ∈ Finset.range (p^2), ∀ a ∈ A, ¬(a ≡ b_p [MOD p^2]) := by
           have := h p hp
           exact ⟨ this.choose, Finset.mem_range.mpr this.choose_spec.1, fun a ha => fun h => this.choose_spec.2 a ha <| h.symm ▸ Nat.mod_eq_of_lt this.choose_spec.1 ⟩
         aesop
       choose! b hb using h_choose_residues
       tauto
     refine ⟨ { n | ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] }, ?_, ?_ ⟩
     · aesop_cat
     · refine ⟨ ∏ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), p ^ 2, Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2, ?_, ?_ ⟩
       ·
         simp +decide [ Nat.ModEq ]
         intro n
         constructor
         all_goals
           intros h p hp hp'
         all_goals
           specialize h p hp hp'
         all_goals
           simp_all +decide [ Finset.prod_eq_prod_sdiff_singleton_mul <| show p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ) from Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, hp' ⟩, Nat.add_mod ]
       · -- The number of integers in [1, M] that are not congruent to b_p modulo p^2 for any prime p <= C is given by the Euler's totient function of M.
         have h_card : (Finset.filter (fun n => ∀ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), ¬n ≡ b p [MOD p^2]) (Finset.Icc 1 (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), p^2))).card = (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (p^2 - 1)) := by
           have h_card : Finset.card (Finset.filter (fun n => ∀ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), ¬(n ≡ b p [MOD p^2])) (Finset.range (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), p^2))) = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (p^2 - 1) := by
             have h_card : ∀ (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) → Finset.card (Finset.filter (fun n => ∀ p ∈ ps, ¬(n ≡ b p [MOD p^2])) (Finset.range (∏ p ∈ ps, p^2))) = ∏ p ∈ ps, (p^2 - 1) := by
               intro ps hps
               induction ps using Finset.induction with
               | empty =>
                 norm_num +zetaDelta at *
               | insert p ps hps ih =>
                 have h_card_insert : Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2]) ∧ ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (p^2 * ∏ q ∈ ps, q^2))) = (p^2 - 1) * Finset.card (Finset.filter (fun n => ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (∏ q ∈ ps, q^2))) := by
                   have h_card_insert : Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2]) ∧ ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (p^2 * ∏ q ∈ ps, q^2))) = Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2])) (Finset.range (p^2))) * Finset.card (Finset.filter (fun n => ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (∏ q ∈ ps, q^2))) := by
                     rw [ ← Finset.card_product ]
                     refine Finset.card_bij ( fun n hn => ( n % p ^ 2, n % ∏ q ∈ ps, q ^ 2 ) ) ?_ ?_ ?_
                     · simp +contextual
                       exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self _ _ ) ) ) 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using ha₂ ⟩, Nat.mod_lt _ ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hps q ( Finset.mem_insert_of_mem hq ) ) ) 2 ), fun q hq => by simpa [ Nat.ModEq, Nat.mod_mod, Finset.prod_eq_prod_sdiff_singleton_mul hq ] using ha₃ q hq ⟩
                     · simp +zetaDelta at *
                       intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ ha₇ ha₈
                       -- Since $a₁ \equiv a₂ \pmod{p^2}$ and $a₁ \equiv a₂ \pmod{\prod_{q \in ps} q^2}$, and $p^2$ and $\prod_{q \in ps} q^2$ are coprime, we have $a₁ \equiv a₂ \pmod{p^2 \prod_{q \in ps} q^2}$.
                       have h_cong : a₁ ≡ a₂ [MOD p^2 * ∏ q ∈ ps, q^2] := by
                         rw [ Nat.modEq_iff_dvd ] at *
                         convert Int.coe_lcm_dvd ( Nat.modEq_iff_dvd.mp ha₇ ) ( Nat.modEq_iff_dvd.mp ha₈ ) using 1
                         norm_cast
                         rw [ Nat.Coprime.lcm_eq_mul ]
                         exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hps.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ ps› <| by have := Nat.prime_dvd_prime_iff_eq hps.1 ( hps.2 q hq ) ; aesop
                       exact Nat.mod_eq_of_lt ha₁ ▸ Nat.mod_eq_of_lt ha₄ ▸ h_cong
                     · simp +zetaDelta at *
                       intro a b_1 ha hb_1 hb_2 hb_3
                       obtain ⟨a_5, ha_5⟩ : ∃ a_5, a_5 ≡ a [MOD p^2] ∧ a_5 ≡ b_1 [MOD ∏ q ∈ ps, q^2] ∧ a_5 < p^2 * ∏ q ∈ ps, q^2 := by
                         have h_crt : Nat.gcd (p^2) (∏ q ∈ ps, q^2) = 1 := by
                           exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hps.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ ps› <| by have := Nat.prime_dvd_prime_iff_eq hps.1 ( hps.2 q hq ) ; aesop
                         have := Nat.chineseRemainder h_crt a b_1
                         exact ⟨ this.val % ( p ^ 2 * ∏ q ∈ ps, q ^ 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2, Nat.mod_lt _ ( Nat.mul_pos ( pow_pos hps.1.pos 2 ) ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hps.2 q hq ) ) 2 ) ) ⟩
                       use a_5
                       simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ]
                       intro q hq
                       specialize hb_3 q hq
                       rw [ ← Nat.mod_mod_of_dvd a_5 ( show q ^ 2 ∣ ∏ q ∈ ps, q ^ 2 from Finset.dvd_prod_of_mem _ hq ) ]
                       aesop
                   rw [ h_card_insert, show Finset.filter ( fun n => ¬n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) = Finset.range ( p ^ 2 ) \ Finset.image ( fun n => n ) ( Finset.filter ( fun n => n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) ) from ?_, Finset.card_sdiff ] <;> norm_num
                   · rw [ show Finset.filter ( fun n => n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) ∩ Finset.range ( p ^ 2 ) = { b p % ( p ^ 2 ) } from ?_ ]
                     focus
                       norm_num
                     ext
                     simp [Nat.ModEq]
                     exact ⟨ fun h => by linarith [ Nat.mod_eq_of_lt h.1.1 ], fun h => ⟨ ⟨ by linarith [ Nat.mod_lt ( b p ) ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self p ps ) ) ) 2 ) ], by simp +decide [ h ] ⟩, by linarith [ Nat.mod_lt ( b p ) ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self p ps ) ) ) 2 ) ] ⟩ ⟩
                   · grind
                 simp_all +decide [Finset.prod_insert]
             exact h_card _ fun p hp => Finset.mem_filter.mp hp |>.2
           rw [ ← h_card ]
           refine Finset.card_bij ( fun x hx => if x = ∏ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), p ^ 2 then 0 else x ) ?_ ?_ ?_
           · simp +zetaDelta at *
             intro a ha₁ ha₂ ha₃
             split_ifs
             all_goals
               simp_all +decide [ Nat.ModEq ]
             · exact ⟨ fun p hp₁ hp₂ => pow_pos hp₂.pos _, fun p hp₁ hp₂ => Ne.symm <| by specialize ha₃ p hp₁ hp₂; rw [ Nat.mod_eq_zero_of_dvd <| Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, hp₂ ⟩ ] at ha₃; aesop ⟩
             · exact lt_of_le_of_ne ha₂ ‹_›
           · grind
           · simp +zetaDelta at *
             intro n hn hn'
             use if n = 0 then ∏ p ∈ Finset.range ( C + 1 ) with Nat.Prime p, p ^ 2 else n
             split_ifs
             all_goals
               simp_all +decide
             · refine ⟨ Finset.prod_pos fun p hp => hn p ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ( Finset.mem_filter.mp hp |>.2 ), fun p hp hp' => ?_ ⟩
               simp_all +decide [ Nat.ModEq, Finset.prod_eq_prod_sdiff_singleton_mul <| Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le hp, hp' ⟩ ]
             · exact ⟨ Nat.pos_of_ne_zero ‹_›, hn.le ⟩
         rw [ show ( { n | ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] } ∩ Set.Icc 1 ( ∏ p ∈ Finset.range ( C + 1 ) with Nat.Prime p, p ^ 2 ) ).ncard = ( Finset.filter ( fun n => ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] ) ( Finset.Icc 1 ( ∏ p ∈ Finset.range ( C + 1 ) with Nat.Prime p, p ^ 2 ) ) ).card from ?_ ]
         · rw [ h_card, Nat.cast_prod ]
           rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| Finset.mem_filter.mp hx |>.2 ]
           norm_num
           rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ]
           intros
           rw [ sub_div, inv_eq_one_div, div_self ]
           aesop
         · rw [ ← Set.ncard_coe_finset ]
           congr
           ext
           aesop

/-
If A is admissible, its upper density is at most the product of (1 - 1/p^2) for primes p <= C.
-/
lemma admissible_upper_bound_C (A : Set ℕ) (h : Admissible A) (C : ℕ) :
  upperDensity A ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (1 - 1/(p:ℝ)^2) := by
    obtain ⟨ B, hB₁, hB₂ ⟩ := admissible_subset_periodic A h C
    obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hB₂
    exact hM₃ ▸ density_of_subset_periodic A B M hM₁ hM₂ hB₁

/-
Every admissible set has upper density at most 6/pi^2.
-/
theorem Admissible_implies_upperDensity_le_6_div_pi_sq (A : Set ℕ) (h : Admissible A) :
  upperDensity A ≤ 6 / Real.pi^2 := by
    convert le_of_tendsto_of_tendsto' tendsto_const_nhds ( prod_primes_inv_sq_tendsto ) ( fun k => ?_ ) using 1
    have := admissible_upper_bound_C A h ( k - 1 )
    rcases k with ( _ | k )
    all_goals
      aesop

/-
The product of $p^2$ for all primes $p \le n^2$.
-/
def W_sq (n : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n^2 + 1)), p^2

/-
If $n'$ is a multiple of $W = \prod_{p \le n^2} p^2$ and $a \le n$ is squarefree, then if $n'+a$ is not squarefree, it must be divisible by the square of a prime $p > n^2$.
-/
lemma key_construction_i_deterministic (n : ℕ) (n' : ℕ) (a : ℕ)
    (hW : W_sq n ∣ n')
    (ha : a ∈ Finset.Icc 1 n)
    (ha_sf : a ∈ SF)
    (h_not_sf : n' + a ∉ SF) :
    ∃ p, Nat.Prime p ∧ p > n^2 ∧ p^2 ∣ (n' + a) := by
      -- Let $p$ be a prime such that $p^2 \mid n' + a$.
      obtain ⟨p, hp_prime, hp_sq⟩ : ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n' + a := by
        contrapose! h_not_sf
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => by simpa [ sq ] using h_not_sf p hp
      by_cases hp_le : p ≤ n^2
      · -- Since $p \leq n^2$, we have $p^2 \mid W_sq n$.
        have hp_sq_div_W_sq : p^2 ∣ W_sq n := by
          exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by nlinarith ), hp_prime ⟩ )
        simp_all +decide [ Nat.dvd_add_right, dvd_trans hp_sq_div_W_sq hW ]
        exact absurd ( ha_sf.squarefree_of_dvd hp_sq ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop )
      · exact ⟨ p, hp_prime, not_le.mp hp_le, hp_sq ⟩

/-
The set of multiples of W in [x/2, x].
-/
def candidates (x W : ℕ) : Finset ℕ := (Finset.Icc (x / 2) x).filter (fun n => W ∣ n)

/-
$W$ is positive.
-/
lemma W_sq_pos (n : ℕ) : W_sq n > 0 := by
  exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2

/-
If $x/2 \ge W$, then there is a multiple of $W$ in $[x/2, x]$.
-/
lemma candidates_card_pos (x W : ℕ) (hW : W > 0) (hx : x / 2 ≥ W) : (candidates x W).card > 0 := by
  -- Since $W \leq x/2$, there exists some multiple of $W$ in the interval $[x/2, x]$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, W * k ∈ Finset.Icc (x / 2) x := by
    exact ⟨ x / 2 / W + 1, Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x / 2 ) W, Nat.mod_lt ( x / 2 ) hW ], by linarith [ Nat.div_mul_le_self ( x / 2 ) W, Nat.div_mul_le_self x 2 ] ⟩ ⟩
  exact Finset.card_pos.mpr ⟨ W * k, Finset.mem_filter.mpr ⟨ hk, dvd_mul_right _ _ ⟩ ⟩

/-
The set of candidates $n'$ such that $n' + a$ is divisible by $p^2$.
-/
def bad_candidates (x W a p : ℕ) : Finset ℕ :=
  (candidates x W).filter (fun n' => p^2 ∣ (n' + a))

/-
The fraction of candidates $n'$ such that $p^2 \mid n' + a$ is bounded by $O(1/p^2 + W/x)$.
-/
lemma bad_candidates_prob_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (a : ℕ) (p : ℕ),
    n > 0 → p > n^2 → Nat.Prime p → x / 2 ≥ W_sq n →
    ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
      obtain ⟨ C, hC_pos, hC ⟩ := lemma_freq
      use C, hC_pos
      intro n x a p hn hp hp_prime hx
      have h_filter_bounds : (bad_candidates x (W_sq n) a p).card ≤ C * ((candidates x (W_sq n)).card : ℝ) * ((1 / (p : ℝ)^2) + ((W_sq n : ℝ) / (x / 2))) := by
        by_cases h : ( candidates x ( W_sq n ) |> Finset.card ) = 0 <;> simp_all +decide [ mul_assoc ]
        · unfold bad_candidates
          aesop
        · have := hC ( W_sq n ) ( p ^ 2 ) 0 ( -a % ( p ^ 2 ) |> Int.toNat ) ( x / 2 ) ( x - x / 2 + 1 ) ?_ ?_ ?_ <;> norm_num at *
          · rw [ div_le_iff₀ ] at this
            · refine le_trans ?_ ( this.trans ?_ )
              · refine mod_cast Finset.card_le_card ?_
                simp +decide [ Finset.subset_iff ]
                simp +contextual [Nat.ModEq]
                simp +contextual [ bad_candidates, candidates ]
                intro k hk₁ hk₂ hk₃ hk₄
                rw [ Nat.mod_eq_zero_of_dvd hk₃ ]
                norm_num [ ← Int.natCast_inj, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( pow_ne_zero 2 ( Nat.cast_ne_zero.mpr hp_prime.ne_zero ) ) ) ]
                exact ⟨ by omega, Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hk₄ ⟩
              · rw [ mul_right_comm ]
                rw [ mul_assoc ]
                gcongr
                · simp +contextual [ Finset.subset_iff, candidates ]
                  exact fun n hn₁ hn₂ hn₃ => ⟨ by omega, Nat.dvd_of_mod_eq_zero hn₃ ⟩
                · exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hx ( by exact not_le_of_gt ( Nat.pos_of_ne_zero ( by exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 ( Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ) ) ) ) zero_lt_two
                · rw [ div_le_iff₀ ] <;> norm_cast ; omega
            · simp_all +decide [ Finset.ext_iff, candidates ]
              exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ h.choose_spec ], by linarith [ h.choose_spec, Nat.sub_add_cancel ( show x / 2 ≤ x from Nat.div_le_self _ _ ) ] ⟩, Nat.modEq_zero_iff_dvd.mpr h.choose_spec.2.2 ⟩ ⟩
          · refine Nat.Coprime.prod_left fun q hq => ?_
            exact Nat.Coprime.pow_left 2 ( Nat.Coprime.symm <| hp_prime.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos <| Finset.mem_filter.mp hq |>.2 ) <| by nlinarith [ Finset.mem_range.mp <| Finset.mem_filter.mp hq |>.1 ] )
          · omega
          · contrapose! h
            simp_all +decide [ candidates ]
            exact fun y hy₁ hy₂ => fun hy₃ => h hy₁ ( by omega ) <| Nat.modEq_zero_iff_dvd.mpr hy₃
      norm_num at *
      (
      exact div_le_of_le_mul₀ ( Nat.cast_nonneg _ ) ( by positivity ) ( by linarith ))

/-
The set of candidates $n'$ that fail condition (i), i.e., there exists $a \le n$ and $p > n^2$ such that $p^2 \mid n' + a$.
-/
def bad_candidates_i (n x : ℕ) : Finset ℕ :=
  Finset.biUnion (Finset.Icc 1 n) (fun a =>
    Finset.biUnion ((Finset.Ioc (n^2) (Nat.sqrt (2 * x))).filter Nat.Prime) (fun p =>
      bad_candidates x (W_sq n) a p))

/-
The fraction of candidates failing condition (i) is $O(1/n + n W/\sqrt{x})$.
-/
lemma bad_candidates_i_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ),
    n > 0 → x / 2 ≥ W_sq n →
    ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (n : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨ C, hC₀, hC ⟩ := bad_candidates_prob_bound
      refine ⟨ C * 4, by positivity, fun n x hn hx => ?_ ⟩
      -- Apply the bound from `hC` to each term in the sum.
      have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2)) * n + C * (W_sq n : ℝ) / (x / 2) * n * (Nat.sqrt (2 * x)) := by
        have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
          have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ ((Finset.Ioc (n^2) (Nat.sqrt (2 * x))).filter Nat.Prime), ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card := by
            have h_sum : ((bad_candidates_i n x).card : ℝ) ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n ^ 2) (Nat.sqrt (2 * x))), ((bad_candidates x (W_sq n) a p).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun a ha => Finset.card_biUnion_le )
            simpa only [ ← Finset.sum_div _ _ _ ] using div_le_div_of_nonneg_right h_sum <| Nat.cast_nonneg _
          exact h_sum_bound.trans ( Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => hC n x a p hn ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) hx )
        simp_all +decide [Finset.sum_add_distrib, mul_add, mul_comm, mul_left_comm,
          Finset.mul_sum _ _ _]
        refine le_trans h_sum_bound ?_
        norm_num [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ]
        gcongr
        exact le_trans ( Finset.card_filter_le _ _ ) ( by simp )
      -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$.
      have h_sum_p_inv_sq : ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2) ≤ 2 / (n : ℝ)^2 := by
        -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$ because there are at most $\sqrt{2x}$ terms and each term is at most $1/(n^2)^2$.
        have h_sum_p_inv_sq : ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ⟩ ) fun _ _ _ => by positivity
        -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$ because there are at most $\sqrt{2x}$ terms and each term is at most $1/(n^2)^2$. We can bound the sum by comparing it to a telescoping series.
        have h_telescope : ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) := by
          gcongr
          rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( ↑‹ℕ› : ℝ ) ≥ 2 by norm_cast; nlinarith [ Finset.mem_Icc.mp ‹_› ], sq ( ( ↑‹ℕ› : ℝ ) - 1 ) ]
        -- The sum of a telescoping series is bounded by the difference of the first and last terms.
        have h_telescope_sum : ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) ≤ 1 / (n^2 : ℝ) := by
          erw [ Finset.sum_Ico_eq_sum_range ]
          -- The sum of a telescoping series is bounded by the difference of the first and last terms, which is $1/n^2$.
          have h_telescope_sum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / (n^2 + k : ℝ) - 1 / (n^2 + k + 1 : ℝ)) = 1 / (n^2 : ℝ) - 1 / (n^2 + m : ℝ) := by
            exact fun m => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring
          convert le_trans
              (le_of_eq (h_telescope_sum (Nat.sqrt (2 * x) + 1 - (n ^ 2 + 1))))
              (sub_le_self _ (by positivity)) using 1
          all_goals
            first
            | rfl
            | apply Finset.sum_congr rfl
              intro k hk
              have h₁ :
                  ((Nat.cast (n ^ 2 + 1 + k) : ℝ) - (1 : ℝ)) =
                    ((Nat.cast (n ^ 2) : ℝ) + (Nat.cast k : ℝ)) := by
                norm_num [Nat.cast_add, Nat.cast_pow]
                ring
              have h₂ :
                  (Nat.cast (n ^ 2 + 1 + k) : ℝ) =
                    ((Nat.cast (n ^ 2) : ℝ) + (Nat.cast k : ℝ) + 1) := by
                norm_num [Nat.cast_add, Nat.cast_pow]
                ring
              rw [h₁, h₂]
              norm_num [Nat.cast_pow]
        exact h_sum_p_inv_sq.trans <| h_telescope.trans <| h_telescope_sum.trans <| by rw [ div_le_div_iff_of_pos_right ] <;> norm_cast ; nlinarith
      -- The sum over $p$ of $W/x$ is at most $\sqrt{2x} \cdot W/x = O(W/\sqrt{x})$.
      have h_sum_p_W_div_x : (W_sq n : ℝ) / (x / 2) * n * (Nat.sqrt (2 * x)) ≤ 4 * (W_sq n : ℝ) * n / (Nat.sqrt x) := by
        rcases x with ( _ | _ | x )
        all_goals
          norm_num at *
        · exact absurd hx <| ne_of_gt <| W_sq_pos n
        · field_simp
          norm_cast
          nlinarith only [ show 0 ≤ W_sq n * ( x + 1 + 1 ) by positivity, show ( 2 * ( x + 1 + 1 ) ).sqrt * ( x + 1 + 1 ).sqrt ≤ ( x + 1 + 1 ) * 2 by nlinarith only [ Nat.sqrt_le ( 2 * ( x + 1 + 1 ) ), Nat.sqrt_le ( x + 1 + 1 ) ] ]
      refine le_trans h_sum_bound ?_
      field_simp
      refine le_trans ( mul_le_mul_of_nonneg_left ( add_le_add h_sum_p_inv_sq ( show ( W_sq n : ℝ ) * 2 * Nat.sqrt ( 2 * x ) / x ≤ ( W_sq n : ℝ ) * 2 * Nat.sqrt ( 2 * x ) / x from le_rfl ) ) ( sq_nonneg _ ) ) ?_
      rw [ mul_add, mul_div_cancel₀ ]
      all_goals
        norm_num [ hn.ne' ]
      ring_nf at *
      nlinarith [ show ( n : ℝ ) ^ 2 ≥ 1 by exact_mod_cast Nat.one_le_pow _ _ hn ]

/-
Definitions for part (ii):
`I_R_eps` is the interval $(R, (1+\epsilon)R]$.
`relevant_primes` are primes $p$ with $\max(n^2, \sqrt{R}) < p \le \sqrt{2x}$.
`bad_a_ii` are $a \in \SF \cap I_R$ such that $n'+a$ is divisible by $p^2$ for some relevant prime.
`bad_candidates_ii_R` are candidates $n'$ where the number of bad $a$ is large ($> \epsilon^2 R$).
-/
def I_R_eps (R : ℕ) (ε : ℝ) : Finset ℕ := Finset.Ioc R (Nat.floor ((1 + ε) * R))

def relevant_primes (n R x : ℕ) : Finset ℕ :=
  (Finset.Ioc (max (n^2) (Nat.sqrt R)) (Nat.sqrt (2 * x))).filter Nat.Prime

def bad_a_ii (n' R x n : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p^2 ∣ n' + a)

def bad_candidates_ii_R (R x n : ℕ) (ε : ℝ) (W : ℕ) : Finset ℕ :=
  (candidates x W).filter (fun n' => (bad_a_ii n' R x n ε).card > ε^2 * R)

/-
The sum of `bad_a_ii` sizes is bounded by the sum of `bad_candidates` sizes.
-/
lemma sum_bad_a_ii_le_sum_bad_candidates (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ) :
  ∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≤
  ∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0 := by
    rw [ Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun p hp => ?_ ]
    rotate_left
    focus
      use fun a p => if a ∈ SF then ∑ n' ∈ candidates x ( W_sq n ), if p ^ 2 ∣ n' + a then 1 else 0 else 0
    · unfold bad_candidates
      aesop
    · rw [ Finset.sum_comm ]
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      rotate_right
      focus
        use fun n' => ∑ a ∈ I_R_eps R ε, if a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p ^ 2 ∣ n' + a then 1 else 0
      · rw [ Finset.sum_comm ]
        gcongr
        split_ifs
        all_goals
          simp_all +decide
        norm_cast
        exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le )
      · unfold bad_a_ii
        aesop

/-
The expected number of bad $a$'s is bounded by the sum over relevant primes.
-/
lemma sum_bad_a_ii_bound_explicit :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
      by_contra h
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ (n : ℕ) (x : ℕ) (a : ℕ) (p : ℕ),
        n > 0 → p > n^2 → Nat.Prime p → x / 2 ≥ W_sq n →
        ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
          -- Apply the lemma bad_candidates_prob_bound to obtain the constant C.
          apply bad_candidates_prob_bound
      refine h ⟨ C, hC_pos, ?_ ⟩
      intros n x R ε hn hx hR hx' hε_pos
      have h_sum : (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) ≤ ∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) * (candidates x (W_sq n)).card else 0 := by
        refine le_trans
          (b := ∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x,
            if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0)
          ?_ ( Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => ?_ )
        focus
          convert sum_bad_a_ii_le_sum_bad_candidates n x R ε using 1
        split_ifs
        all_goals
          norm_num
        have := hC n x a p hn ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1.trans_le' <| le_max_left _ _ ) ( Finset.mem_filter.mp hp |>.2 ) hx
        rw [ div_le_iff₀ ] at this <;> norm_num at *
        focus
          linarith
        exact Finset.card_pos.mp ( candidates_card_pos x ( W_sq n ) ( W_sq_pos n ) ( by linarith [ Nat.div_mul_le_self x 2 ] ) )
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      · positivity
      · exact mul_nonneg ( mul_nonneg hC_pos.le ( Nat.cast_nonneg _ ) ) ( Finset.sum_nonneg fun _ _ => by positivity )
      · refine le_trans h_sum ?_
        norm_num [ Finset.sum_ite, Finset.mul_sum _ _ _, Finset.sum_mul ]
        refine Finset.sum_le_sum fun p hp => ?_
        refine le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le (I_R_eps R ε) (fun x => x ∈ SF) ) <| by positivity ) ?_ ; ring_nf ; norm_num

/-
The sum of $1/p^2$ for relevant primes is $O(1/\sqrt{R})$.
-/
lemma sum_inv_sq_relevant_primes_bound_R :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
    ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / (Nat.sqrt R : ℝ) := by
      use 2
      norm_num +zetaDelta at *
      intros n x R hn hx hR hxR
      have h_sum_bound : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ 2 / (Nat.sqrt R : ℝ) := by
        have h_sum_bound : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) := by
          gcongr
          rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( ↑‹ℕ› : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp ‹_›, Nat.sqrt_pos.mpr ( show 0 < R by linarith ) ] ]
        -- The series $\sum_{p=\sqrt{R}+1}^{\sqrt{2x}} \left(\frac{1}{p-1} - \frac{1}{p}\right)$ is a telescoping series.
        have h_telescoping : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) = 1 / (Nat.sqrt R : ℝ) - 1 / (Nat.sqrt (2 * x) : ℝ) := by
          erw [ Finset.sum_Ico_eq_sum_range ]
          convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring_nf
          rw [ Nat.cast_sub ( Nat.sqrt_le_sqrt ( by linarith ) ) ]
          ring
        exact h_sum_bound.trans <| h_telescoping.symm ▸ by exact le_trans ( sub_le_self _ <| by positivity ) <| by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.sqrt_pos.mpr <| show 0 < R by linarith ]
      refine le_trans ?_ h_sum_bound
      norm_num [ relevant_primes ]
      exact Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.le_max_right ( n ^ 2 ) ( Nat.sqrt R ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.le_max_right ( n ^ 2 ) ( Nat.sqrt R ) ] ⟩ ) fun _ _ _ => by positivity

/-
The conclusion of Proposition Key: n' satisfies properties (i) and (ii).
-/
def PropositionKey_conclusion (n n' : ℕ) (ε C : ℝ) : Prop :=
  (∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF) ∧
  (∀ R : ℕ, n ≤ R → R ≤ n' →
    let numerator := ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∈ SF)).card
    (numerator : ℝ) / R ≥ 6 / Real.pi^2 - C * ε)

/-
The set of bad a in the interval is contained in the union of bad a due to small primes, large primes, and very large primes.
-/
def bad_in_interval (n' : ℕ) (R : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ n' + a ∉ SF)

def small_primes (n R : ℕ) : Finset ℕ :=
  (Finset.Ioc (n^2) (Nat.sqrt R)).filter Nat.Prime

def bad_small (n' R : ℕ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => ∃ p ∈ small_primes n R, p^2 ∣ n' + a)

def bad_large (n' R x : ℕ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p^2 ∣ n' + a)

def bad_very_large (n' R x : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => ∃ p, Nat.Prime p ∧ p > Nat.sqrt (2 * x) ∧ p^2 ∣ n' + a)

lemma bad_in_interval_subset (n' R x n : ℕ) (ε : ℝ) (hW : W_sq n ∣ n') :
  bad_in_interval n' R ε ⊆ bad_small n' R ε n ∪ bad_large n' R x ε n ∪ bad_very_large n' R x ε := by
    intro a ha
    obtain ⟨ha_sqf, p, hp_prime, hp_sq_div⟩ : a ∈ SF ∧ ∃ p, Nat.Prime p ∧ p^2 ∣ n' + a ∧ p > n^2 := by
      obtain ⟨ha_sqf, ha_not_sqf⟩ : a ∈ SF ∧ n' + a ∉ SF := by
        unfold bad_in_interval at ha
        aesop
      obtain ⟨p, hp_prime, hp_sq_div⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n' + a := by
        contrapose! ha_not_sqf
        generalize_proofs at *
        (
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => by
          simpa [ sq ] using ha_not_sqf p hp
          )
      generalize_proofs at *
      (
      refine ⟨ ha_sqf, p, hp_prime, hp_sq_div, ?_ ⟩
      generalize_proofs at *
      (
      by_contra h_contra
      generalize_proofs at *
      (
      have h_div_a : p^2 ∣ a := by
        have h_div_a : p^2 ∣ n' := by
          exact dvd_trans ( by exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by nlinarith [ hp_prime.two_le ] ), hp_prime ⟩ ) ) hW
        generalize_proofs at *
        (
        simpa using Nat.dvd_sub hp_sq_div h_div_a)
      generalize_proofs at *
      (
      exact absurd ( ha_sqf.squarefree_of_dvd h_div_a ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop )))))
    generalize_proofs at *
    (
    by_cases hp_le_sqrt_R : p ≤ Nat.sqrt R <;> by_cases hp_le_sqrt_2x : p ≤ Nat.sqrt (2 * x) <;> simp_all +decide [ bad_small, bad_large, bad_very_large ]
    · exact Or.inl ⟨ by unfold bad_in_interval at ha; aesop, p, by unfold small_primes; aesop ⟩
    · exact Or.inr <| Or.inr <| ⟨ by unfold bad_in_interval at ha; aesop, p, hp_prime, hp_le_sqrt_2x, hp_sq_div.1 ⟩
    · right
      left
      exact ⟨ by
        exact Finset.mem_Ioc.mpr ⟨ Finset.mem_Ioc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_Ioc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩, p, by
        unfold relevant_primes
        aesop
        , hp_sq_div.1 ⟩
    · exact Or.inr <| Or.inr <| ⟨ by unfold bad_in_interval at ha; aesop, p, hp_prime, hp_le_sqrt_2x, hp_sq_div.1 ⟩)

/-
The sum of 1/k^2 for k > n is at most 1/n.
-/
lemma sum_inv_sq_tail_bound (n : ℕ) (hn : n > 0) :
  ∑' k : ℕ, (if k > n then 1 / (k : ℝ)^2 else 0) ≤ 1 / (n : ℝ) := by
    -- We compare the sum to an integral and use the fact that the integral of $1/x^2$ is $1/x$.
    have h_integral_comparison : ∀ n : ℕ, (n > 0) → (∑' k : ℕ, if k > n then (1 : ℝ) / k^2 else 0) ≤ ∑' k : ℕ, (1 : ℝ) / ((k + n) * (k + n + 1)) := by
      -- By shifting the index of summation, we can rewrite the sum as starting from $k = 1$ to infinity.
      have h_shift : ∀ (n : ℕ) (hn : n > 0), (∑' k : ℕ, if k > n then (1 : ℝ) / k^2 else 0) = (∑' k : ℕ, (1 : ℝ) / (k + n + 1)^2) := by
        intro n hn
        rw [ ← Summable.sum_add_tsum_nat_add n.succ ]
        focus
          norm_num [ add_assoc, add_left_comm, add_comm ]
        · exact Finset.sum_eq_zero fun x hx => if_neg <| by linarith [ Finset.mem_range.mp hx ]
        · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
      intro n hn
      rw [ h_shift n hn ]
      refine Summable.tsum_le_tsum ?_ ?_ ?_
      · exact fun k => by
          gcongr
          nlinarith
      · exact_mod_cast summable_nat_add_iff ( n + 1 ) |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two
      · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith ) ( summable_nat_add_iff n |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two )
    -- The series $\sum_{k=n+1}^\infty \frac{1}{k(k-1)}$ is a telescoping series.
    have h_telescoping : ∀ (N : ℕ), (∑ k ∈ Finset.range N, (1 : ℝ) / ((k + n) * (k + n + 1))) = (1 : ℝ) / n - (1 : ℝ) / (N + n) := by
      intro N
      induction N
      all_goals
        simp_all +decide [ Finset.sum_range_succ ]
      -- Combine and simplify the terms on the left-hand side.
      field_simp
      ring
    -- By the properties of the telescoping series, we can conclude that the sum of the series is bounded above by $1/n$.
    have h_sum_bound : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (1 : ℝ) / ((k + n) * (k + n + 1)))) Filter.atTop (nhds ((1 : ℝ) / n)) := by
      simpa only [ h_telescoping ] using by simpa using tendsto_const_nhds.sub ( (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from tendsto_inv_atTop_nhds_zero_nat).comp ( Filter.tendsto_add_atTop_nat n ) )
    exact le_trans ( h_integral_comparison n hn ) ( le_of_tendsto_of_tendsto' ( by exact ( Summable.hasSum ( by exact by { by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_sum_bound ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h } ) |> HasSum.tendsto_sum_nat ) ) h_sum_bound fun N => by aesop )

/-
The number of multiples of k in the interval (a, b] is at most (b-a)/k + 1.
-/
lemma count_multiples_in_interval (a b k : ℕ) (hk : k > 0) :
  ((Finset.Ioc a b).filter (fun x => k ∣ x)).card ≤ (b - a) / k + 1 := by
    -- The multiples of $k$ in the interval $(a, b]$ are given by $k * (a / k + 1), k * (a / k + 2), \ldots, k * (b / k)$.
    have h_multiples : Finset.filter (fun x => k ∣ x) (Finset.Ioc a b) ⊆ Finset.image (fun m => k * m) (Finset.Icc (a / k + 1) (b / k)) := by
      intro x hx
      simp +zetaDelta at *
      exact ⟨ x / k, ⟨ Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_mul_cancel hx.2 ] ), Nat.div_le_div_right hx.1.2 ⟩, by rw [ mul_comm, Nat.div_mul_cancel hx.2 ] ⟩
    refine le_trans ( Finset.card_le_card h_multiples ) ?_
    refine le_trans (b := ( b / k ) - ( a / k )) ?_ ?_
    · exact Finset.card_image_le.trans ( by simp +arith +decide )
    · rw [ Nat.sub_le_iff_le_add ]
      rw [ Nat.div_le_iff_le_mul_add_pred hk ]
      cases le_total b a
      all_goals
        simp_all +decide [ Nat.div_eq_of_lt ]
      · nlinarith [ Nat.div_add_mod a k, Nat.mod_lt a hk, Nat.sub_add_cancel hk ]
      · linarith [ Nat.div_add_mod ( b - a ) k, Nat.mod_lt ( b - a ) hk, Nat.sub_add_cancel ‹_›, Nat.div_add_mod a k, Nat.mod_lt a hk, Nat.sub_add_cancel hk ]

/-
The cardinality of bad_small is bounded by the sum over small primes p of (|I|/p^2 + 1).
-/
lemma bad_small_card_bound_sum (n' R : ℕ) (ε : ℝ) (n : ℕ) :
  ((bad_small n' R ε n).card : ℝ) ≤
  ∑ p ∈ small_primes n R, (((I_R_eps R ε).card : ℝ) / p^2 + 1) := by
    -- For each small prime $p$, the set $S_p = \{a \in I_{R,\epsilon} : p^2 \mid n' + a\}$ is in one-to-one correspondence with the set of multiples of $p^2$ in the interval $n' + I_{R,\epsilon}$.
    have h_card_S_p (p : ℕ) (hp : p ∈ small_primes n R) : ((I_R_eps R ε).filter (fun a => p^2 ∣ n' + a)).card ≤ ((I_R_eps R ε).card : ℝ) / (p : ℝ)^2 + 1 := by
      have h_multiples : ((Finset.Ioc (n' + R) (n' + Nat.floor ((1 + ε) * R))).filter (fun x => p^2 ∣ x)).card ≤ (Nat.floor ((1 + ε) * R) - R) / p^2 + 1 := by
        convert count_multiples_in_interval ( n' + R ) ( n' + ⌊ ( 1 + ε ) * R⌋₊ ) ( p ^ 2 ) _ using 1
        · rw [ Nat.add_sub_add_left ]
        · exact pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
      have h_multiples : ((Finset.Ioc R (Nat.floor ((1 + ε) * R))).filter (fun a => p^2 ∣ n' + a)).card ≤ ((Finset.Ioc (n' + R) (n' + Nat.floor ((1 + ε) * R))).filter (fun x => p^2 ∣ x)).card := by
        rw [ ← Finset.card_image_of_injective _ ( add_right_injective n' ) ]
        exact Finset.card_le_card fun x hx => by aesop
      refine le_trans ( Nat.cast_le.mpr <| h_multiples.trans ‹_› ) ?_
      norm_num [ I_R_eps ]
      exact Nat.cast_div_le .. |> le_trans <| by norm_num
    refine le_trans ?_ ( Finset.sum_le_sum h_card_S_p )
    norm_cast
    convert Finset.card_biUnion_le
    all_goals try infer_instance
    unfold bad_small
    ext
    aesop

/-
The sum of 1/p^2 over small primes is at most 1/n^2.
-/
lemma sum_inv_sq_small_primes_bound (n R : ℕ) (hn : n > 0) :
  ∑ p ∈ small_primes n R, (1 / (p : ℝ)^2) ≤ 1 / (n^2 : ℝ) := by
    -- The sum is over primes $p \in (n^2, \sqrt{R}]$.
    -- This is bounded by the sum over all integers $k \in (n^2, \sqrt{R}]$.
    have h_sum_bound : ∑ p ∈ small_primes n R, (1 / (p : ℝ)^2) ≤ ∑' k : ℕ, (if k > n^2 then 1 / (k : ℝ)^2 else 0) := by
      refine le_trans ?_ ( Summable.sum_le_tsum ?_ ?_ ?_ )
      any_goals exact Finset.filter ( fun p => Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ Nat.sqrt R ) ( Finset.Ioc ( n ^ 2 ) ( Nat.sqrt R ) )
      · simp +decide [ Finset.sum_ite ]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        simp +decide [ Finset.subset_iff ]
        unfold small_primes
        aesop
      · exact fun _ _ => by positivity
      · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
    generalize_proofs at *
    (
    exact h_sum_bound.trans ( sum_inv_sq_tail_bound _ ( by positivity ) ) |> le_trans <| by norm_num;)

/-
The number of bad a due to small primes is bounded by 2 * epsilon^2 * R.
-/
lemma bad_small_bound :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ R : ℕ, R ≥ n →
  ∀ n' : ℕ,
  ((bad_small n' R ε n).card : ℝ) ≤ C * ε^2 * R := by
    use 2
    refine ⟨ by norm_num, fun ε hε_pos hε_lt_one => ⟨ ⌈ε⁻¹ ^ 4⌉₊ + 1, fun n hn R hR n' => ?_ ⟩ ⟩
    -- By `bad_small_card_bound_sum`, the cardinality is bounded by $|I_{R,\epsilon}| \sum_{p \in small} \frac{1}{p^2} + |small|$.
    have h_card_bound : ((bad_small n' R ε n).card : ℝ) ≤ (I_R_eps R ε).card * (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) + (small_primes n R).card := by
      refine le_trans ( bad_small_card_bound_sum n' R ε n ) ?_
      norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib ]
    -- Use the bounds on the sum of 1/p^2 and the cardinality of small_primes.
    have h_sum_bound : (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) ≤ ε := by
      have h_sum_bound : (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) ≤ 1 / (n^2 : ℝ) := by
        convert sum_inv_sq_small_primes_bound n R ( by linarith ) using 1
      refine le_trans h_sum_bound ?_
      rw [ div_le_iff₀ ]
      all_goals
        nlinarith [ show ( n : ℝ ) ≥ ⌈ε⁻¹ ^ 4⌉₊ + 1 by exact_mod_cast hn, Nat.le_ceil ( ε⁻¹ ^ 4 ), inv_pos.2 hε_pos, mul_inv_cancel₀ ( ne_of_gt hε_pos ), pow_pos ( inv_pos.2 hε_pos ) 2, pow_pos ( inv_pos.2 hε_pos ) 3, pow_pos ( inv_pos.2 hε_pos ) 4 ]
    have h_card_small_bound : (small_primes n R).card ≤ Real.sqrt R := by
      have h_card_small_bound : (small_primes n R).card ≤ Nat.sqrt R := by
        exact le_trans ( Finset.card_le_card ( show small_primes n R ⊆ Finset.Icc 1 ( Nat.sqrt R ) from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩ ) ) ( by simp )
      exact le_trans ( Nat.cast_le.mpr h_card_small_bound ) ( Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ ) )
    -- Use the bound on the cardinality of I_R_eps.
    have h_card_I_R_eps_bound : ((I_R_eps R ε).card : ℝ) ≤ ε * R := by
      unfold I_R_eps
      norm_num [ Nat.floor_le ]
      rw [ Nat.cast_sub ]
      all_goals
        norm_num
      · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by linarith )
      · exact Nat.le_floor <| by nlinarith
    -- Use the bound on the square root of R.
    have h_sqrt_R_bound : Real.sqrt R ≤ ε^2 * R := by
      rw [ Real.sqrt_le_left ]
      all_goals
        ring_nf
      · have h_sqrt_R_bound : (ε⁻¹ ^ 4 : ℝ) ≤ R := by
          exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith )
        rw [ inv_pow, inv_eq_one_div, div_le_iff₀ ] at h_sqrt_R_bound
        all_goals
          nlinarith [ pow_pos hε_pos 4 ]
      · positivity
    nlinarith [ show 0 ≤ ε * R by positivity ]

/-
If n' + max(a) <= 2x, then bad_very_large is empty.
-/
lemma bad_very_large_empty (n' R x : ℕ) (ε : ℝ) (h : n' + Nat.floor ((1 + ε) * R) ≤ 2 * x) :
  bad_very_large n' R x ε = ∅ := by
    -- Assume there exists $a \in \text{bad\_very\_large}$.
    by_contra h_nonempty
    obtain ⟨a, ha⟩ : ∃ a ∈ I_R_eps R ε, ∃ p, Nat.Prime p ∧ p > Nat.sqrt (2 * x) ∧ p^2 ∣ n' + a := by
      unfold bad_very_large at h_nonempty
      aesop
    -- Since $a \in I_R_eps$, we have $a \leq \lfloor (1+\epsilon)R \rfloor$.
    have ha_le : a ≤ Nat.floor ((1 + ε) * R) := by
      exact Finset.mem_Ioc.mp ha.1 |>.2
    obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ha.2
    nlinarith [ Nat.sqrt_lt.mp hp₂, Nat.le_of_dvd ( by linarith [ Finset.mem_Ioc.mp ha.1 ] ) hp₃ ]

/-
The tail sum of mu(d)/d^2 for d > k is bounded by 1/k.
-/
lemma sum_moebius_div_sq_tail_bound (k : ℕ) (hk : k > 0) :
  abs (∑' d : ℕ, (if d > k then (ArithmeticFunction.moebius d : ℝ) / d ^ 2 else 0)) ≤ 1 / (k : ℝ) := by
    -- By Lemma `sum_inv_sq_tail_bound`, we know that $\sum_{d > k} \frac{1}{d^2} \le \frac{1}{k}$.
    have h_sum_inv_sq_tail_bound : (∑' (d : ℕ), if k < d then (1 : ℝ) / d ^ 2 else 0) ≤ 1 / (k : ℝ) := by
      exact sum_inv_sq_tail_bound k hk
    refine le_trans
      (b := ‖∑' d : ℕ, (if d > k then (ArithmeticFunction.moebius d : ℝ) / d ^ 2 else 0)‖)
      ( le_of_eq <| ?_ ) ?_
    · rw [ ← Real.norm_eq_abs ]
    refine le_trans
      (b := ∑' d : ℕ, ‖if d > k then (ArithmeticFunction.moebius d : ℝ) / d ^ 2 else 0‖)
      ( norm_tsum_le_tsum_norm ?_ ) ?_
    · refine Summable.of_nonneg_of_le ( fun i => norm_nonneg (if i > k then (ArithmeticFunction.moebius i : ℝ) / i ^ 2 else 0) ) ( fun i => ?_ ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
      split_ifs
      all_goals
        norm_num [ ArithmeticFunction.moebius ]
      split_ifs
      all_goals
        norm_num
    · refine (Summable.tsum_le_tsum ?_ ?_ ?_).trans h_sum_inv_sq_tail_bound
      · intro i
        split_ifs
        all_goals
          norm_num [ ArithmeticFunction.moebius ]
        split_ifs
        all_goals
          norm_num
      · refine Summable.of_nonneg_of_le ( fun i => ?_ ) ( fun i => ?_ ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
        · positivity
        · split_ifs
          all_goals
            norm_num [ ArithmeticFunction.moebius ]
          split_ifs
          all_goals
            norm_num
      · exact Summable.of_nonneg_of_le ( fun d => by positivity ) ( fun d => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )

/-
The difference between the sum of mu(d) * floor(n/d^2) and n * sum(mu(d)/d^2) is at most sqrt(n).
-/
lemma sum_moebius_floor_approx (n : ℕ) :
  abs ((∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ)) -
       n * ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) / d^2) ≤ Nat.sqrt n := by
         -- The absolute value of each term in the sum is bounded by 1.
         have h_abs_term : ∀ d ∈ Finset.Icc 1 (Nat.sqrt n), |(ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ) - n * (ArithmeticFunction.moebius d : ℝ) / d^2| ≤ 1 := by
           intro d hd
           rw [ mul_div_right_comm ]
           simp +decide [ abs_le ]
           norm_num [ ArithmeticFunction.moebius ]
           split_ifs
           all_goals
             norm_num
           constructor
           all_goals
             by_cases h : Even ( ArithmeticFunction.cardFactors d )
           all_goals
             simp_all +decide
           · rw [ div_le_iff₀ ]
             all_goals
               norm_cast
             all_goals
               nlinarith [ Nat.div_add_mod n ( d ^ 2 ), Nat.mod_lt n ( pow_pos ( by linarith : 0 < d ) 2 ) ]
           · exact le_add_of_nonneg_of_le zero_le_one ( by rw [ le_div_iff₀ ( by norm_cast; nlinarith ) ] ; norm_cast; nlinarith [ Nat.div_mul_le_self n ( d ^ 2 ) ] )
           · rw [ add_div', le_div_iff₀ ]
             all_goals
               norm_cast
             all_goals
               nlinarith [ Nat.div_mul_le_self n ( d ^ 2 ), Nat.pos_of_ne_zero ( show d ^ 2 ≠ 0 by nlinarith ) ]
           · rw [ div_le_iff₀ ]
             all_goals
               norm_cast
             all_goals
               nlinarith [ Nat.div_add_mod n ( d ^ 2 ), Nat.mod_lt n ( pow_pos ( by linarith : 0 < d ) 2 ) ]
         simpa [ Finset.mul_sum _ _ _, mul_div_assoc ] using le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum h_abs_term ) |> le_trans <| by norm_num

/-
The infinite sum of mu(d)/d^2 is equal to 6/pi^2.
-/
lemma sum_moebius_div_sq_tsum_eq :
  ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 = 6 / Real.pi^2 := by
    -- The series is absolutely convergent, so the infinite sum is the same as the limit of the partial sums.
    have h_abs_conv : Summable (fun d : ℕ => |(ArithmeticFunction.moebius d : ℝ) / d^2|) := by
      norm_num [ abs_div, ArithmeticFunction.moebius ]
      exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by split_ifs <;> norm_num ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
    refine tendsto_nhds_unique ?_ ( sum_moebius_div_sq_tendsto )
    convert h_abs_conv.of_abs.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1
    exact funext fun n => by erw [ Function.comp_apply, Finset.sum_Ico_eq_sub _ ] <;> norm_num

/-
The difference between the partial sum of mu(d)/d^2 and 6/pi^2 is at most 1/k.
-/
lemma partial_sum_diff_bound (k : ℕ) (hk : k > 0) :
  abs ((∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ) / d^2) - 6 / Real.pi^2) ≤ 1 / (k : ℝ) := by
    convert sum_moebius_div_sq_tail_bound k hk using 1
    have h_tsum_eq : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 = 6 / Real.pi^2 := by
      exact sum_moebius_div_sq_tsum_eq
    have h_sum_split : ∑' d : ℕ, (if d > k then (ArithmeticFunction.moebius d : ℝ) / d^2 else 0) = ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 - ∑' d : ℕ, (if d ≤ k then (ArithmeticFunction.moebius d : ℝ) / d^2 else 0) := by
      rw [ ← Summable.tsum_sub ]
      · congr
        ext d
        split_ifs <;> linarith
      · exact ( by contrapose! h_tsum_eq; erw [ tsum_eq_zero_of_not_summable h_tsum_eq ] ; positivity )
      · rw [ ← summable_nat_add_iff ( k + 1 ) ]
        exact ⟨ _, hasSum_single 0 fun n hn => if_neg <| by linarith ⟩
    rw [ h_sum_split, h_tsum_eq, ← Summable.sum_add_tsum_nat_add k.succ ]
    · rw [ ← abs_neg ]
      rw [ ← h_tsum_eq ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]
      rw [ Finset.sum_congr rfl fun i hi => if_pos <| by linarith [ Finset.mem_range.mp hi ] ]
      rw [ tsum_congr fun i => if_neg ( by linarith ) ] ; norm_num
    · refine summable_of_ne_finset_zero (s := Finset.range ( k + 1 )) ?_
      exact fun b hb => if_neg fun h => hb <| Finset.mem_range_succ_iff.mpr h

/-
The difference between n times the partial sum of mu(d)/d^2 and n times 6/pi^2 is at most 3 * sqrt(n).
-/
lemma bound_diff_partial_sum_limit (n : ℕ) (hn : n > 0) :
  abs ((n : ℝ) * (∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) / d^2) - (n : ℝ) * (6 / Real.pi^2)) ≤ 3 * (Nat.sqrt n : ℝ) := by
    have := partial_sum_diff_bound ( Nat.sqrt n ) ?_ <;> norm_num at *
    · rw [ ← mul_sub, abs_mul, abs_of_nonneg ( by positivity ) ]
      refine le_trans ( mul_le_mul_of_nonneg_left this <| Nat.cast_nonneg _ ) ?_
      rw [ ← div_eq_mul_inv, div_le_iff₀ ]
      all_goals
        norm_cast
      all_goals
        nlinarith [ Nat.lt_succ_sqrt n ]
    · positivity

/-
The number of squarefree integers up to n is 6/pi^2 * n + O(sqrt(n)).
-/
lemma SF_count_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
  abs (((Finset.Icc 1 n).filter (fun x => x ∈ SF)).card - (6 / Real.pi^2) * n) ≤ C * Nat.sqrt n := by
    use 4
    use by norm_num
    -- Apply the bounds from the previous lemmas to conclude the proof.
    intros n hn
    have h_sum_floor : abs ((∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ)) - (n : ℝ) * (6 / Real.pi^2)) ≤ 4 * (Nat.sqrt n : ℝ) := by
      convert le_trans ( abs_sub_le _ _ _ ) _ using 1
      · exact Real.instIsOrderedAddMonoid
      · exact ( n : ℝ ) * ∑ d ∈ Finset.Icc 1 ( Nat.sqrt n ), ( ArithmeticFunction.moebius d : ℝ ) / d ^ 2
      refine le_trans
        (b := (n.sqrt : ℝ) + 3 * (n.sqrt : ℝ))
        ( add_le_add
          ((sum_moebius_floor_approx n).trans (le_rfl : (n.sqrt : ℝ) ≤ n.sqrt))
          ((bound_diff_partial_sum_limit n hn).trans (le_rfl : (3 * (n.sqrt : ℝ)) ≤ 3 * n.sqrt)) )
        ?_
      linarith
    convert h_sum_floor using 2
    convert congr_arg ( fun x : ℤ => ( x : ℝ ) - 6 / Real.pi ^ 2 * n ) ( sum_squarefree_indicator_eq_sum_moebius_floor n ) using 1
    · norm_num [ SF ]
    · norm_num [ mul_comm ]
      exact rfl

/-
Definitions for the geometric progression and the good candidate property.
-/
noncomputable def max_k (n x : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor (Real.log ((x : ℝ) / n) / Real.log (1 + ε))

/-
Recursive definition of geometric progression to avoid gaps.
-/
noncomputable def geometric_R_rec (n : ℕ) (ε : ℝ) : ℕ → ℕ
| 0 => n
| k + 1 => Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ))

def geometric_points (n x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (max_k n x ε + 5)).image (geometric_R_rec n ε)

/-
Definition of GeometricGood using the recursive geometric progression.
-/
def GeometricGood_rec (n n' : ℕ) (x : ℕ) (ε : ℝ) : Prop :=
  n' ∈ candidates x (W_sq n) ∧
  n' ∉ bad_candidates_i n x ∧
  ∀ k ∈ Finset.range (max_k n x ε + 5), n' ∉ bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)

/-
The set of bad elements up to R.
-/
def bad_upto (n' R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∉ SF)

/-
The sum of the terms in the recursive geometric progression up to $m$ is bounded by $O(1/\epsilon)$ times the $m$-th term.
-/
lemma geometric_sum_bound :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ m : ℕ,
  ∑ k ∈ Finset.range m, (geometric_R_rec n ε k : ℝ) ≤ C * (1/ε) * (geometric_R_rec n ε m : ℝ) := by
    use 2
    norm_num +zetaDelta at *
    intro ε hε₁ hε₂
    -- For sufficiently large $n$, the floor function does not affect the growth rate of the sequence.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ k, geometric_R_rec n ε (k + 1) ≥ (1 + ε / 2) * geometric_R_rec n ε k := by
      use Nat.ceil (2 / ε) + 1
      intro n hn k
      have h_floor : ∀ x : ℕ, x ≥ Nat.ceil (2 / ε) + 1 → Nat.floor ((1 + ε) * x) ≥ (1 + ε / 2) * x := by
        intro x hx
        nlinarith [ Nat.le_ceil ( 2 / ε ), Nat.lt_floor_add_one ( ( 1 + ε ) * x ), mul_div_cancel₀ 2 hε₁.ne', show ( x : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast hx ]
      have h_ge : geometric_R_rec n ε k ≥ Nat.ceil (2 / ε) + 1 := by
        induction k with
        | zero =>
          simpa [geometric_R_rec] using hn
        | succ k ih =>
          have hstep := h_floor (geometric_R_rec n ε k) ih
          have ih' : (geometric_R_rec n ε k : ℝ) ≥ Nat.ceil (2 / ε) + 1 := by
            exact_mod_cast ih
          have : (geometric_R_rec n ε (k + 1) : ℝ) ≥ Nat.ceil (2 / ε) + 1 := by
            simp [geometric_R_rec] at hstep ⊢
            nlinarith [hstep, hε₁]
          exact_mod_cast this
      simpa [geometric_R_rec] using h_floor (geometric_R_rec n ε k) h_ge
    use N₀ + 1
    intro n hn m
    induction m with
    | zero =>
      norm_num [ Finset.sum_range_succ ] at *
      positivity
    | succ m ih =>
      norm_num [ Finset.sum_range_succ ] at *
      nlinarith [ inv_pos.2 hε₁, mul_inv_cancel₀ hε₁.ne', hN₀ n ( by linarith ) m ]

/-
The set of bad elements up to $R$ is contained in the union of bad elements in the intervals of the geometric progression, provided the progression covers $R$ and the initial segment is good.
-/
lemma bad_upto_subset (n : ℕ) (n' : ℕ) (R : ℕ) (ε : ℝ) (m : ℕ)
  (h_cover : R ≤ geometric_R_rec n ε m)
  (h_good_i : ∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF) :
  bad_upto n' R ⊆ Finset.biUnion (Finset.range m) (fun k => bad_in_interval n' (geometric_R_rec n ε k) ε) := by
    intros a ha
    obtain ⟨k, hk⟩ : ∃ k < m, a ∈ Finset.Ioc (geometric_R_rec n ε k) (geometric_R_rec n ε (k + 1)) := by
      have h_seq : a ≤ geometric_R_rec n ε m := by
        exact le_trans ( Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ) h_cover
      generalize_proofs at *
      by_cases h_cases : a ≤ geometric_R_rec n ε 0
      · contrapose! h_good_i
        unfold bad_upto at ha
        aesop
      · have h_seq : ∃ k ≤ m, a ≤ geometric_R_rec n ε k ∧ ∀ j < k, a > geometric_R_rec n ε j := by
          have h_seq : ∃ k ≤ m, a ≤ geometric_R_rec n ε k := by
            exact ⟨ m, le_rfl, h_seq ⟩
          generalize_proofs at *
          exact ⟨ Nat.find h_seq, Nat.find_spec h_seq |>.1, Nat.find_spec h_seq |>.2, fun j hj => not_le.mp fun h => Nat.find_min h_seq hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_seq |>.1 ), h ⟩ ⟩
        generalize_proofs at *
        obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_seq
        use k - 1; rcases k <;> aesop
    simp_all +decide [ bad_upto, bad_in_interval ]
    refine ⟨ k, hk.1, ?_ ⟩
    unfold I_R_eps
    aesop

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    have h_good_candidates : ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_in_interval n' R ε).card : ℝ) ≤ C * ε^2 * R := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_small n' R ε n).card : ℝ) ≤ C₁ * ε^2 * R := by
        obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n → ∀ n' : ℕ, ((bad_small n' R ε n).card : ℝ) ≤ C₁ * ε^2 * R := by
          exact bad_small_bound
        exact ⟨ C₁, hC₁.1, fun ε hε₁ hε₂ => by obtain ⟨ N₀, hN₀ ⟩ := hC₁.2 ε hε₁ hε₂; exact ⟨ N₀, fun n hn => ⟨ n, fun x hx => fun n' hn' R hR hR' => hN₀ n hn R ( by
          obtain ⟨ k, hk ⟩ := Finset.mem_image.mp hR
          -- By definition of `geometric_R_rec`, we know that `geometric_R_rec n ε k ≥ n` for all `k`.
          have h_geometric_R_rec_ge_n : ∀ k, geometric_R_rec n ε k ≥ n := by
            intro k
            induction k with
            | zero =>
              norm_num [ geometric_R_rec ]
            | succ k ih =>
              norm_num [ geometric_R_rec ]
              exact Nat.le_floor <| by nlinarith [ show ( geometric_R_rec n ε k : ℝ ) ≥ n by exact_mod_cast ih ]
          linarith [ h_geometric_R_rec_ge_n k ] ) n' ⟩ ⟩ ⟩
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_large n' R x ε n).card : ℝ) ≤ ε^2 * R := by
        use 1
        norm_num
        intros ε hε₁ hε₂
        use 1
        intro n hn
        use 1
        intro x hx n' hn' R hR hR'
        have := hn'.2.2 ( Finset.mem_image.mp hR |> Classical.choose ) ?_ <;> simp_all +decide [ GeometricGood_rec ]
        · contrapose! this
          refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩ <;> norm_num [ bad_candidates_ii_R ]
          · exact hn'.1
          · have := Classical.choose_spec ( Finset.mem_image.mp hR )
            aesop
        · have := Classical.choose_spec ( Finset.mem_image.mp hR )
          aesop
      have h_bad_very_large : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → bad_very_large n' R x ε = ∅ := by
        intros ε hε_pos hε_lt_1
        use 1
        intro n hn
        use 1
        intro x hx n' hn' R hR hR_le
        apply bad_very_large_empty
        exact hR_le
      refine ⟨ C₁ + 1, by linarith, fun ε hε₁ hε₂ => ?_ ⟩
      obtain ⟨ N₀₁, hN₀₁ ⟩ := hC₁.2 ε hε₁ hε₂
      obtain ⟨ N₀₂, hN₀₂ ⟩ := hC₂.2 ε hε₁ hε₂
      obtain ⟨ N₀₃, hN₀₃ ⟩ := h_bad_very_large ε hε₁ hε₂
      use max N₀₁ (max N₀₂ N₀₃)
      intros n hn
      obtain ⟨ x₀₁, hx₀₁ ⟩ := hN₀₁ n (by linarith [Nat.le_max_left N₀₁ (max N₀₂ N₀₃)])
      obtain ⟨ x₀₂, hx₀₂ ⟩ := hN₀₂ n (by linarith [Nat.le_max_right N₀₁ (max N₀₂ N₀₃), Nat.le_max_left N₀₂ N₀₃])
      obtain ⟨ x₀₃, hx₀₃ ⟩ := hN₀₃ n (by linarith [Nat.le_max_right N₀₁ (max N₀₂ N₀₃), Nat.le_max_right N₀₂ N₀₃])
      use max x₀₁ (max x₀₂ x₀₃)
      intros x hx n' hn' R hR hR'
      have h_bad_in_interval_subset : bad_in_interval n' R ε ⊆ bad_small n' R ε n ∪ bad_large n' R x ε n ∪ bad_very_large n' R x ε := by
        apply bad_in_interval_subset
        exact hn'.1 |> fun h => Finset.mem_filter.mp h |>.2
      have h_bad_in_interval_card : ((bad_in_interval n' R ε).card : ℝ) ≤ ((bad_small n' R ε n).card : ℝ) + ((bad_large n' R x ε n).card : ℝ) + ((bad_very_large n' R x ε).card : ℝ) := by
        exact_mod_cast le_trans ( Finset.card_le_card h_bad_in_interval_subset ) ( Finset.card_union_le _ _ |> le_trans <| add_le_add_left ( Finset.card_union_le _ _ ) _ )
      rw [ hx₀₃ x ( by linarith [ Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₂ x₀₃ ] ) n' hn' R hR hR' ] at h_bad_in_interval_card
      norm_num at *
      nlinarith [ hx₀₁ x ( by linarith [ Nat.le_max_left x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ) ] ) n' hn' R hR hR', hx₀₂ x ( by linarith [ Nat.le_max_left x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_left x₀₂ x₀₃, Nat.le_max_right x₀₂ x₀₃ ] ) n' hn' R hR hR' ]
    obtain ⟨ C, hC₀, hC ⟩ := h_good_candidates
    use C, hC₀
    intros ε hε₁ hε₂
    obtain ⟨ N₀, hN₀ ⟩ := hC ε hε₁ hε₂
    use N₀
    intros n hn
    obtain ⟨ x₀, hx₀ ⟩ := hN₀ n hn
    use x₀
    intros x hx n' hn' k hk
    specialize hx₀ x hx n' hn'
    simp_all +decide [ geometric_points ]

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v2 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    -- Apply the bound from `bad_in_interval_bound_rec`.
    apply bad_in_interval_bound_rec

/-
Lower bound for the recursive geometric progression: $R_k \ge (1+\epsilon)^k (n - 1/\epsilon)$.
-/
lemma geometric_R_rec_lower_bound_explicit (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  (geometric_R_rec n ε k : ℝ) ≥ (1 + ε)^k * (n - 1/ε) := by
    -- Define the auxiliary sequence $a_k = R_k (1+\epsilon)^{-k}$.
    set a : ℕ → ℝ := fun k => (geometric_R_rec n ε k : ℝ) / (1 + ε)^k
    -- Then $a_{k+1} (1+\epsilon)^{k+1} > (1+\epsilon) a_k (1+\epsilon)^k - 1$.
    have ha_recurrence : ∀ k, a (k + 1) > a k - (1 + ε)⁻¹ ^ (k + 1) := by
      intro k
      simp [a]
      rw [ show geometric_R_rec n ε ( k + 1 ) = Nat.floor ( ( 1 + ε ) * ( geometric_R_rec n ε k : ℝ ) ) by rfl ] ; rw [ div_sub', div_lt_div_iff₀ ] <;> try positivity
      nlinarith [ Nat.lt_floor_add_one ( ( 1 + ε ) * ( geometric_R_rec n ε k : ℝ ) ), pow_pos ( by linarith : 0 < 1 + ε ) k, pow_succ' ( 1 + ε ) k, mul_inv_cancel_left₀ ( by positivity : ( 1 + ε ) ^ ( k + 1 ) ≠ 0 ) ( ( 1 + ε ) ^ k ) ]
    -- Summing this inequality:
    have ha_sum : ∀ k, a k ≥ n - ∑ j ∈ Finset.range k, (1 + ε)⁻¹ ^ (j + 1) := by
      intro k
      induction k with
      | zero =>
        norm_num [ Finset.sum_range_succ ] at *
        aesop
      | succ k ih =>
        norm_num [ Finset.sum_range_succ ] at *
        linarith [ ha_recurrence k ]
    -- The sum is bounded by $\sum_{j=1}^\infty (1+\epsilon)^{-j} = 1/\epsilon$.
    have ha_sum_bound : ∀ k, ∑ j ∈ Finset.range k, (1 + ε)⁻¹ ^ (j + 1) ≤ 1 / ε := by
      intro k
      have := geom_sum_mul ( ( 1 + ε ) ⁻¹ ) k
      simp_all +decide [pow_succ', mul_comm]
      rw [ ← Finset.mul_sum _ _ _ ]
      nlinarith [ inv_pos.mpr hε, inv_pos.mpr ( show 0 < 1 + ε by linarith ), mul_inv_cancel₀ ( show ( 1 + ε ) ≠ 0 by linarith ), mul_inv_cancel₀ ( show ( ε : ℝ ) ≠ 0 by linarith ), pow_pos ( show 0 < 1 + ε by linarith ) k, inv_pos.mpr ( show 0 < ( 1 + ε ) ^ k by positivity ), mul_inv_cancel₀ ( show ( ( 1 + ε ) ^ k : ℝ ) ≠ 0 by positivity ) ]
    have := ha_sum k
    rw [ ge_iff_le ] at this
    rw [ le_div_iff₀ ( by positivity ) ] at this
    nlinarith [ ha_sum_bound k, pow_pos ( by positivity : 0 < ( 1 + ε ) ) k ]

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v3 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    convert bad_in_interval_bound_rec_v2 using 1

/-
The recursive geometric progression eventually exceeds $x$.
-/
lemma geometric_covers_x :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ x : ℕ, x ≥ n →
  geometric_R_rec n ε (max_k n x ε + 4) ≥ x := by
    intros ε hε_pos hε_lt_one
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x ≥ n, (1 + ε)^(max_k n x ε + 3) * (n - 1/ε) ≥ x := by
      -- By definition of $max_k$, we know that $(1 + ε)^{max_k n x ε} \geq (x / n) / (1 + ε)$.
      have h_max_k : ∀ n x : ℕ, n ≥ 1 → x ≥ n → (1 + ε)^(max_k n x ε) ≥ (x / n) / (1 + ε) := by
        intros n x hn hx
        have h_max_k : max_k n x ε ≥ Real.log ((x : ℝ) / n) / Real.log (1 + ε) - 1 := by
          exact le_of_lt ( Nat.sub_one_lt_floor _ )
        have h_exp : (1 + ε)^(max_k n x ε) ≥ Real.exp (Real.log ((x : ℝ) / n) - Real.log (1 + ε)) := by
          rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ]
          exact Real.exp_le_exp.mpr ( by nlinarith [ Real.log_pos ( show 1 + ε > 1 by linarith ), mul_div_cancel₀ ( Real.log ( x / n ) ) ( ne_of_gt ( Real.log_pos ( show 1 + ε > 1 by linarith ) ) ) ] )
        rw [ Real.exp_sub, Real.exp_log ( by exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Nat.cast_pos.mpr ( by linarith ) ) ), Real.exp_log ( by linarith ) ] at h_exp
        aesop
      -- Choose $N₀$ such that for all $n \geq N₀$, we have $(n - 1/ε) \geq n / (1 + ε)$.
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, (n - 1/ε : ℝ) ≥ n / (1 + ε) := by
        simp +zetaDelta at *
        exact ⟨ ⌈ε⁻¹ * ( 1 + ε ) / ε⌉₊ + 1, fun n hn => by rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( 1 + ε ) / ε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * ( 1 + ε ) / ε⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ ( ε⁻¹ * ( 1 + ε ) ) hε_pos.ne', mul_inv_cancel₀ hε_pos.ne' ] ⟩
      refine ⟨ N₀ + 1, fun n hn x hx => ?_ ⟩ ; specialize hN₀ n ( by linarith ) ; specialize h_max_k n x ( by linarith ) ( by linarith ) ; simp_all +decide [ pow_add ]
      rw [ div_div, div_le_iff₀ ] at *
      all_goals
        try positivity
      · nlinarith [ pow_pos ( by linarith : 0 < 1 + ε ) 2, pow_pos ( by linarith : 0 < 1 + ε ) 3, mul_le_mul_of_nonneg_left hN₀ ( show 0 ≤ ( 1 + ε ) ^ max_k n x ε by positivity ) ]
      · exact mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( by linarith )
    use N₀
    intros n hn x hx
    specialize hN₀ n hn x hx
    simp_all +decide [ pow_succ, mul_assoc ]
    have h_geometric_R_rec_lower_bound : (geometric_R_rec n ε (max_k n x ε + 4) : ℝ) ≥ (1 + ε)^(max_k n x ε + 4) * (n - 1/ε) := by
      exact geometric_R_rec_lower_bound_explicit n ε ( max_k n x ε + 4 ) hε_pos |> le_trans ( by norm_num )
    exact_mod_cast hN₀.trans ( h_geometric_R_rec_lower_bound.trans' ( by ring_nf; nlinarith ) )

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v4 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    convert bad_in_interval_bound_rec_v3 using 1

/-
The expected number of bad $a$'s is bounded by a function involving $1/\sqrt{R}$.
-/
lemma expected_bad_a_bound_R :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      have := sum_bad_a_ii_bound_explicit
      obtain ⟨ C, hC₀, hC ⟩ := this
      -- Use the bound on the sum of 1/p^2 for relevant primes.
      have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
        ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) ≤ C * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ)) := by
          have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
            ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / (Nat.sqrt R : ℝ) := by
              obtain ⟨ C, hC₀, hC ⟩ := sum_inv_sq_relevant_primes_bound_R
              exact ⟨ C, hC₀, hC ⟩
          have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
            ∑ p ∈ relevant_primes n R x, (W_sq n : ℝ) / (x / 2) ≤ C * (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ) := by
              use 2 * Real.sqrt 2 + 1
              refine ⟨ by positivity, fun n x R hn hx hR hx' => ?_ ⟩
              -- The number of relevant primes is at most $\sqrt{2x}$.
              have h_num_primes : (relevant_primes n R x).card ≤ Nat.sqrt (2 * x) := by
                refine le_trans ( Finset.card_le_card (t := Finset.Icc 1 ( Nat.sqrt ( 2 * x ) )) ?_ ) ?_
                · exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩
                · norm_num
              by_cases hx : x = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ]
              field_simp
              refine le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr h_num_primes ) <| Nat.cast_nonneg (W_sq n) ) zero_le_two ) <| Nat.cast_nonneg (Nat.sqrt x) ) ?_
              -- By simplifying, we can see that the inequality holds.
              have h_simplify : 2 * Nat.sqrt (x * 2) * Nat.sqrt x ≤ x * n * (2 * Real.sqrt 2 + 1) := by
                have h_simplify : 2 * Nat.sqrt (x * 2) * Nat.sqrt x ≤ x * (2 * Real.sqrt 2 + 1) := by
                  have h_sqrt : Nat.sqrt (x * 2) ≤ Real.sqrt (x * 2) ∧ Nat.sqrt x ≤ Real.sqrt x := by
                    exact ⟨ Real.le_sqrt_of_sq_le <| by exact_mod_cast Nat.sqrt_le' _, Real.le_sqrt_of_sq_le <| by exact_mod_cast Nat.sqrt_le' _ ⟩
                  norm_num at *
                  nlinarith [ Real.sqrt_nonneg x, Real.sqrt_nonneg 2, Real.sq_sqrt ( Nat.cast_nonneg x ), Real.sq_sqrt zero_le_two, show ( x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hx ), show ( Nat.sqrt x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( Nat.pos_of_ne_zero hx ) ) ]
                exact h_simplify.trans ( mul_le_mul_of_nonneg_right ( le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( mod_cast hn ) ) ( by positivity ) )
              nlinarith [ show 0 ≤ ( W_sq n : ℝ ) by positivity ]
          obtain ⟨ C₁, hC₁₀, hC₁ ⟩ := ‹∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ∑ p ∈ relevant_primes n R x, 1 / ( p : ℝ ) ^ 2 ≤ C / ( R.sqrt : ℝ ) ›
          obtain ⟨ C₂, hC₂₀, hC₂ ⟩ := h_sum_bound
          use max C₁ C₂ + 1
          simp
          refine ⟨ by positivity, fun n x R hn hx₁ hx₂ hx₃ => ?_ ⟩ ; simp_all +decide [ Finset.sum_add_distrib ]
          refine le_trans ( add_le_add ( hC₁ n x R hn hx₁ hx₂ hx₃ ) ( hC₂ n x R hn hx₁ hx₂ hx₃ ) ) ?_
          ring_nf
          nlinarith [ show 0 ≤ ( R.sqrt : ℝ ) ⁻¹ by positivity, show 0 ≤ ( x.sqrt : ℝ ) ⁻¹ by positivity, show 0 ≤ ( W_sq n : ℝ ) * n * ( x.sqrt : ℝ ) ⁻¹ by positivity, le_max_left C₁ C₂, le_max_right C₁ C₂ ]
      obtain ⟨ C', hC'₀, hC' ⟩ := h_sum_bound
      exact ⟨ C * C', mul_pos hC₀ hC'₀, fun n x R ε hn hx hR hx' hε => le_trans ( hC n x R ε hn hx hR hx' hε ) ( by convert mul_le_mul_of_nonneg_left ( hC' n x R hn hx hR hx' ) ( mul_nonneg hC₀.le ( Nat.cast_nonneg ( I_R_eps R ε |> Finset.card ) ) ) using 1 ; ring ) ⟩

/-
The probability that a candidate is bad for a given R is bounded by a function of R, n, x, and epsilon.
-/
lemma prob_bad_candidates_ii_R_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
    C / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      -- By Lemma `expected_bad_a_bound_R`, we have that the expected number of bad $a$'s is bounded by a function involving $1/\sqrt{R}$.
      obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, C > 0 ∧ ∀ (n x R : ℕ) (ε : ℝ), n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 → ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card) ≤ C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
        exact expected_bad_a_bound_R
      -- By Markov's inequality, the fraction of bad candidates is at most the expected number of bad $a$'s divided by $\epsilon^2 R$.
      have h_markov : ∀ (n x R : ℕ) (ε : ℝ), n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 → ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card) / (ε^2 * R) := by
        intros n x R ε hn hx hR hx' hε_pos
        have h_markov : ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) * (ε^2 * R) ≤ (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) := by
          have h_markov : ∀ n' ∈ bad_candidates_ii_R R x n ε (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≥ ε^2 * R := by
            intros n' hn'_bad
            have h_card : (bad_a_ii n' R x n ε).card > ε^2 * R := by
              exact_mod_cast Finset.mem_filter.mp hn'_bad |>.2
            exact le_of_lt h_card
          have h_markov : ∑ n' ∈ bad_candidates_ii_R R x n ε (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≥ (bad_candidates_ii_R R x n ε (W_sq n)).card * (ε^2 * R) := by
            simpa using Finset.sum_le_sum h_markov
          exact h_markov.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _ )
        rw [ div_right_comm ]
        gcongr
        rwa [ le_div_iff₀ ( mul_pos ( sq_pos_of_pos hε_pos ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ]
      refine ⟨ C, hC_pos, fun n x R ε hn hx hR hx' hε => le_trans ( h_markov n x R ε hn hx hR hx' hε ) ?_ ⟩
      convert div_le_div_of_nonneg_right ( hC n x R ε hn hx hR hx' hε ) ( by positivity : 0 ≤ ε ^ 2 * R ) using 1 ; ring

/-
The number of integers in $(R, (1+\epsilon)R]$ is at most $\epsilon R + 1$.
-/
lemma card_I_R_eps_le (R : ℕ) (ε : ℝ) (hR : R > 0) (hε : ε > 0) :
  ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
    unfold I_R_eps
    norm_num [ Finset.card_map, Finset.card_range ]
    rw [ Nat.cast_sub ]
    all_goals
      norm_num
    · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by linarith )
    · exact Nat.le_floor <| by nlinarith

/-
If R is very large, there are no bad candidates of type ii.
-/
lemma bad_candidates_ii_R_empty_of_large_R (n x R : ℕ) (ε : ℝ) (W : ℕ)
    (hR : R > 2 * x) (hε : ε > 0) :
    bad_candidates_ii_R R x n ε W = ∅ := by
      ext n'
      simp [bad_candidates_ii_R]
      intro hn'
      have h_empty : bad_a_ii n' R x n ε = ∅ := by
        ext a
        simp [bad_a_ii, relevant_primes]
        exact fun ha₁ ha₂ p hp₁ hp₂ hp₃ hp₄ => by nlinarith [ Nat.sqrt_lt.mp hp₂, Nat.sqrt_le ( 2 * x ) ]
      aesop

/-
The recursive geometric progression grows at least exponentially with rate 1 + epsilon/2.
-/
lemma geometric_R_rec_lower_bound (n k : ℕ) (ε : ℝ)
      (hε : 0 < ε) (hε1 : ε < 1) (hn : n > 2 / ε) :
      (geometric_R_rec n ε k : ℝ) ≥ (1 + ε / 2) ^ k * n := by
        induction k with
        | zero =>
          norm_num [ *, pow_succ', mul_assoc ] at *
          exact Nat.le_refl n
        | succ k ih =>
          norm_num [ *, pow_succ', mul_assoc ] at *
          -- By definition of geometric_R_rec, we have geometric_R_rec n ε (k + 1) = floor((1 + ε) * geometric_R_rec n ε k).
          have h_geometric_R_rec_succ : geometric_R_rec n ε (k + 1) = Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ)) := by
            exact rfl
          rw [ h_geometric_R_rec_succ ]
          refine le_trans ?_ ( Nat.sub_one_lt_floor ((1 + ε) * (geometric_R_rec n ε k : ℝ)) |> le_of_lt )
          rw [ div_lt_iff₀ ] at hn
          all_goals
            nlinarith [ pow_le_pow_right₀ ( by linarith : ( 1 + ε / 2 ) ≥ 1 ) ( show k ≥ 0 by linarith ) ]

/-
The sum of the inverse square roots of the geometric progression is bounded by $O(1/(\epsilon \sqrt{n}))$.
-/
lemma sum_inv_sqrt_R_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∀ n : ℕ, n > 2 / ε →
  ∀ m : ℕ,
  ∑ k ∈ Finset.range m, 1 / Real.sqrt (geometric_R_rec n ε k) ≤ C / (ε * Real.sqrt n) := by
    -- We use the lower bound on $R_k$ to bound the sum.
    have h_sum_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ, (n : ℝ) > 2 / ε → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / Real.sqrt ((1 + ε / 2) ^ k * n : ℝ)) ≤ C / (ε * Real.sqrt n) := by
      -- We can sum the geometric series $\sum_{k=0}^{m-1} (1 + \epsilon / 2)^{-k/2}$ and show it is bounded by $C / \epsilon$.
      have h_geo_series_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 + ε / 2 : ℝ) ^ (-k / 2 : ℝ) ≤ C / ε := by
        -- The sum of a geometric series with ratio $r < 1$ is $\frac{1}{1-r}$. Here, $r = \frac{1}{\sqrt{1+\epsilon/2}}$.
        have h_geo_series_sum : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 + ε / 2 : ℝ) ^ (-k / 2 : ℝ) ≤ 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) := by
          intros ε hε₁ hε₂ m
          have h_geo_series_sum : ∑ k ∈ Finset.range m, (1 / Real.sqrt (1 + ε / 2)) ^ k ≤ 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) := by
            rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < 1 / Real.sqrt ( 1 + ε / 2 ) by positivity, show 1 / Real.sqrt ( 1 + ε / 2 ) < 1 by rw [ div_lt_one ( by positivity ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ), pow_pos ( show 0 < 1 / Real.sqrt ( 1 + ε / 2 ) by positivity ) m, geom_sum_mul ( 1 / Real.sqrt ( 1 + ε / 2 ) ) m ]
          convert h_geo_series_sum using 2 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity : 0 ≤ 1 + ε / 2 ) ] ; ring_nf
          rw [ ← Real.rpow_natCast, ← Real.rpow_neg ( by positivity ), ← Real.rpow_mul ( by positivity ) ]
          ring_nf
        -- We need to show that $1 / (1 - 1 / \sqrt{1 + \epsilon / 2}) \leq C / \epsilon$ for some $C > 0$.
        have h_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) ≤ C / ε := by
          use 8, by norm_num, fun ε hε₁ hε₂ => ?_
          field_simp
          rw [ div_le_iff₀ ]
          all_goals
            nlinarith [ sq_nonneg ( Real.sqrt ( ( 2 + ε ) / 2 ) - 1 ), Real.sqrt_nonneg ( ( 2 + ε ) / 2 ), Real.mul_self_sqrt ( show 0 ≤ ( 2 + ε ) / 2 by positivity ) ]
        exact ⟨ h_bound.choose, h_bound.choose_spec.1, fun ε hε₁ hε₂ m => le_trans ( h_geo_series_sum ε hε₁ hε₂ m ) ( h_bound.choose_spec.2 ε hε₁ hε₂ ) ⟩
      obtain ⟨ C, hC₀, hC ⟩ := h_geo_series_bound
      use C, hC₀
      intros ε hε₀ hε₁ n hn m
      convert mul_le_mul_of_nonneg_right ( hC ε hε₀ hε₁ m ) ( inv_nonneg.mpr ( Real.sqrt_nonneg n ) ) using 1
      focus
        rfl
      focus
        norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity : ( 0 :ℝ ) ≤ 1 + ε / 2 ) ]
      focus
        first | rfl | ring_nf
      · rw [ Finset.sum_mul _ _ _ ]
        refine Finset.sum_congr rfl fun _ _ => ?_ ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf; norm_num [ ← Real.sqrt_eq_rpow ] ; ring_nf
        exact Or.inl ( by rw [ ← Real.rpow_neg ( by positivity ) ] ; ring_nf )
      · ring
    obtain ⟨ C, hC₀, hC ⟩ := h_sum_bound
    refine ⟨ C, hC₀, fun ε hε₁ hε₂ n hn m => le_trans ?_ ( hC ε hε₁ hε₂ n hn m ) ⟩
    gcongr
    · exact Real.sqrt_pos.mpr ( mul_pos ( pow_pos ( by positivity ) _ ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hn; linarith [ div_pos zero_lt_two hε₁ ] ) ) ) )
    · exact geometric_R_rec_lower_bound n _ ε hε₁ hε₂ hn

/-
The fraction of candidates failing condition (i) is less than 1/3 for sufficiently large n and x.
-/
lemma bad_candidates_i_fraction_bound :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card < 1/3 := by
    obtain ⟨ C, hC₀, hC ⟩ := bad_candidates_i_bound
    use ⌈C * 6⌉₊ + 1
    intro n hn
    -- Choose $x₀$ such that $C W n / \sqrt{x₀} < 1/6$ and $x₀/2 \ge W$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, ∀ x ≥ x₀, C * (W_sq n * n / (Nat.sqrt x : ℝ)) < 1 / 6 ∧ x / 2 ≥ W_sq n := by
      have hx₀ : Filter.Tendsto (fun x : ℕ => C * (W_sq n * n / (Nat.sqrt x : ℝ))) Filter.atTop (nhds 0) := by
        have hsqrt_inv : Filter.Tendsto (fun x : ℕ => ((Nat.sqrt x : ℝ)⁻¹)) Filter.atTop (nhds 0) := by
          exact (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from
            tendsto_inv_atTop_nhds_zero_nat).comp <|
              Filter.tendsto_atTop_atTop.mpr fun x =>
                ⟨x ^ 2, fun y hy => by nlinarith [Nat.lt_succ_sqrt' y]⟩
        have hmul : Filter.Tendsto
            (fun x : ℕ => C * ((W_sq n * n : ℝ) * (Nat.sqrt x : ℝ)⁻¹))
            Filter.atTop (nhds 0) := by
          have hinner : Filter.Tendsto
              (fun x : ℕ => (W_sq n * n : ℝ) * (Nat.sqrt x : ℝ)⁻¹)
              Filter.atTop (nhds 0) := by
            simpa using
              ((show Filter.Tendsto (fun _ : ℕ => (W_sq n * n : ℝ)) Filter.atTop
                  (nhds (W_sq n * n : ℝ)) from tendsto_const_nhds).mul hsqrt_inv)
          simpa using (show Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) from
              tendsto_const_nhds).mul hinner
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
      exact Filter.eventually_atTop.mp ( hx₀.eventually ( gt_mem_nhds <| by norm_num ) ) |> fun ⟨ x₀, hx₀ ⟩ ↦ ⟨ x₀ + 2 * W_sq n, fun x hx ↦ ⟨ hx₀ x <| by linarith, by omega ⟩ ⟩
    use x₀
    intros x hx
    specialize hC n x ( by linarith ) ( hx₀ x hx |>.2 )
    specialize hx₀ x hx
    norm_num at *
    nlinarith [ Nat.le_ceil ( C * 6 ), show ( n : ℝ ) ≥ ⌈C * 6⌉₊ + 1 by exact_mod_cast hn, inv_mul_cancel₀ ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ) ]

/-
The term involving the number of steps and the bound for large primes tends to 0 as x goes to infinity.
-/
lemma term_2_tendsto_zero (n : ℕ) (ε : ℝ) (hε : ε > 0) :
  Filter.Tendsto (fun x => ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) Filter.atTop (nhds 0) := by
    by_cases hn : n = 0
    · aesop
    · -- We'll use the fact that `max_k` grows logarithmically with `x`.
      have h_max_k_log : Filter.Tendsto (fun x => (max_k n x ε : ℝ) / Real.sqrt x) Filter.atTop (nhds 0) := by
        have h_max_k_log : Filter.Tendsto (fun x => (Real.log ((x : ℝ) / n) / Real.log (1 + ε)) / Real.sqrt x) Filter.atTop (nhds 0) := by
          -- We can factor out the constant $1 / \log(1 + \epsilon)$ and use the fact that $\frac{\log x}{\sqrt{x}}$ tends to $0$ as $x$ tends to infinity.
          have h_log_sqrt : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
            -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{2 \log y}{y}$.
            suffices h_log_y : Filter.Tendsto (fun y => 2 * Real.log y / y) Filter.atTop (nhds 0) by
              have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ )
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring )
            -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [div_eq_mul_inv, mul_assoc, mul_comm] )
            norm_num +zetaDelta at *
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ mul_assoc ] using Filter.Tendsto.neg ( tendsto_const_nhds.mul ( Real.continuous_mul_log.tendsto 0 ) ) )
          have h_log_sqrt : Filter.Tendsto (fun x => (Real.log x - Real.log n) / Real.sqrt x) Filter.atTop (nhds 0) := by
            have h_const : Filter.Tendsto (fun x : ℝ => Real.log n / Real.sqrt x) Filter.atTop (nhds 0) := by
              exact tendsto_const_nhds.div_atTop
                (Filter.tendsto_atTop_atTop.mpr fun y =>
                  ⟨y ^ 2, fun x hx => Real.le_sqrt_of_sq_le <| by nlinarith⟩)
            simpa [sub_div] using h_log_sqrt.sub h_const
          convert h_log_sqrt.div_const ( Real.log ( 1 + ε ) ) |> Filter.Tendsto.congr' _ using 2
          · ring
          · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring
        refine squeeze_zero_norm' ?_ ( h_max_k_log.comp tendsto_natCast_atTop_atTop )
        simp +zetaDelta at *
        refine ⟨ n + 1, fun x hx => ?_ ⟩
        rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ]
        gcongr
        exact Nat.floor_le ( div_nonneg ( Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; norm_cast ; linarith ) <| Real.log_nonneg <| by linarith )
      -- We can factor out the constant term $(W_sq n * n)$ and use the fact that $(max_k n x ε : ℝ) / \sqrt{x}$ tends to $0$.
      have h_factor : Filter.Tendsto (fun x => ((max_k n x ε : ℝ) + 5) / Real.sqrt x) Filter.atTop (nhds 0) := by
        have h_five : Filter.Tendsto (fun x : ℕ => (5 : ℝ) / Real.sqrt x) Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop
            (Filter.tendsto_atTop_atTop.mpr fun y =>
              ⟨Nat.ceil (y ^ 2), fun x hx =>
                Real.le_sqrt_of_sq_le <| by
                  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hx)⟩)
        simpa [add_div] using h_max_k_log.add h_five
      convert h_factor.const_mul ( W_sq n * n : ℝ ) using 2 <;> ring

/-
The probability of a bad candidate for a given R is bounded by a simplified expression involving 1/sqrt(R) and W*n/sqrt(x).
-/
lemma prob_bad_candidates_ii_R_bound_simplified :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R → R ≤ x →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    obtain ⟨ C, hC₀, hC ⟩ := prob_bad_candidates_ii_R_bound
    refine ⟨ 6 * C, by positivity, fun ε hε₁ hε₂ => ⟨ ⌈2 / ε⌉₊ + 1, fun n hn x hx R hR₁ hR₂ => le_trans ( hC n x R ε ( by linarith [ Nat.le_ceil ( 2 / ε ), div_pos zero_lt_two hε₁ ] ) hx hR₁ hR₂ hε₁ ) ?_ ⟩ ⟩
    -- Using the bound $|I_R|/R \le \epsilon + 1/R$ and the fact that $R \ge n \ge 1$, we get $|I_R|/R \le 1.5 \epsilon$.
    have h_I_R_bound : ((I_R_eps R ε).card : ℝ) / R ≤ 1.5 * ε := by
      have h_I_R_bound : ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
        convert card_I_R_eps_le R ε ( by linarith [ show n > 0 from by linarith ] ) hε₁ using 1
      rw [ div_le_iff₀ ]
      all_goals
        norm_num
      all_goals
        nlinarith [ show ( R : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast by linarith, Nat.le_ceil ( 2 / ε ), mul_div_cancel₀ 2 hε₁.ne' ]
    -- Using the bound $1/\sqrt{R}_{nat} \le 2/\sqrt{R}_{real}$ and similarly for $x$, we get the desired inequality.
    have h_sqrt_bound : (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ)) ≤ 2 * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
      have h_sqrt_bound : (1 / (Nat.sqrt R : ℝ)) ≤ 2 / Real.sqrt R ∧ (1 / (Nat.sqrt x : ℝ)) ≤ 2 / Real.sqrt x := by
        constructor
        all_goals
          rw [ div_le_div_iff₀ ]
        all_goals
          norm_num
        any_goals nlinarith [ Nat.lt_succ_sqrt x, Nat.lt_succ_sqrt R ]
        · rw [ Real.sqrt_le_left ]
          all_goals
            norm_cast
          all_goals
            nlinarith only [ Nat.lt_succ_sqrt R ]
        · rw [ Real.sqrt_le_left ]
          all_goals
            norm_cast
          all_goals
            nlinarith only [ Nat.lt_succ_sqrt x ]
      ring_nf at *
      nlinarith [ show 0 ≤ ( W_sq n : ℝ ) * n by positivity ]
    refine le_trans ( mul_le_mul ( by simpa only [ mul_div_assoc ] using mul_le_mul_of_nonneg_left h_I_R_bound <| by positivity ) h_sqrt_bound ( by positivity ) <| by positivity ) ?_ ; ring_nf ; norm_num [ hε₁.ne', hε₂.ne' ]
    norm_num [ sq, mul_assoc, hε₁.ne' ]
    ring_nf
    gcongr
    all_goals
      norm_num

/-
The set of relevant primes for R is a subset of the set of relevant primes for x if R >= x.
-/
lemma relevant_primes_subset (n R x : ℕ) (h : R ≥ x) :
  relevant_primes n R x ⊆ relevant_primes n x x := by
    -- Since $R \geq x$, we have $\sqrt{R} \geq \sqrt{x}$. Therefore, $\max(n^2, \sqrt{R}) \geq \max(n^2, \sqrt{x})$.
    have h_max : max (n^2) (Nat.sqrt R) ≥ max (n^2) (Nat.sqrt x) := by
      exact max_le_max le_rfl ( Nat.sqrt_le_sqrt h )
    exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ⟩, Finset.mem_filter.mp hp |>.2 ⟩

/-
The bound on the sum of relevant primes holds for the case x < R <= 2x.
-/
lemma sum_relevant_primes_bound_case_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x →
    ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) ≤
    C * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
      -- By Lemma `sum_inv_sq_relevant_primes_bound_R`, we have that the sum of `1/p^2` over relevant primes is bounded by `C / sqrt(x)`.
      have sum_relevant_primes_bound_R : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / Real.sqrt x := by
        -- Since $x < R$, `relevant_primes n R x` is a subset of `relevant_primes n x x` (by `relevant_primes_subset`).
        have h_subset : ∀ n x R : ℕ, x < R → relevant_primes n R x ⊆ relevant_primes n x x := by
          intros n x R hR
          exact relevant_primes_subset n R x hR.le
        have h_sum_bound : ∃ C : ℝ, C > 0 ∧ ∀ n x : ℕ, n > 0 → x / 2 ≥ W_sq n → ∑ p ∈ relevant_primes n x x, (1 / (p : ℝ)^2) ≤ C / Real.sqrt x := by
          obtain ⟨ C, hC₀, hC ⟩ := sum_inv_sq_relevant_primes_bound_R
          refine ⟨ C * 2, mul_pos hC₀ zero_lt_two, fun n x hn hx => ?_ ⟩
          by_cases hx_ge_n : x ≥ n
          · refine le_trans ( hC n x x hn hx hx_ge_n le_rfl ) ?_
            rw [ div_le_div_iff₀ ]
            · rw [ mul_assoc ]
              gcongr
              exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith [ Nat.lt_succ_sqrt x ] ⟩
            · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) )
            · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) )
          · rw [ show relevant_primes n x x = ∅ from _ ]
            · norm_num
              positivity
            · generalize_proofs at *
              (
              ext p
              simp [relevant_primes]
              exact fun h₁ h₂ h₃ => absurd h₃ ( by rw [ Nat.le_sqrt ] ; nlinarith [ Nat.sqrt_le x ] ))
        exact ⟨ h_sum_bound.choose, h_sum_bound.choose_spec.1, fun n x R hn hx hR hR' => le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( h_subset n x R hR ) fun _ _ _ => by positivity ) ( h_sum_bound.choose_spec.2 n x hn hx ) ⟩
      -- By Lemma `count_multiples_in_interval`, we have that the number of relevant primes is at most `sqrt(2x)`.
      have relevant_primes_card_bound_R : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → (relevant_primes n R x).card ≤ C / 2 * (n : ℝ) * Real.sqrt x := by
        -- Since the number of relevant primes is at most sqrt(2x), we can bound it by 2*sqrt(x).
        have relevant_primes_card_bound_R : ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → (relevant_primes n R x).card ≤ 2 * Real.sqrt x := by
          intros n x R hn hx hx' hx''
          refine le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| show relevant_primes n R x ⊆ Finset.Icc 1 ( Nat.sqrt ( 2 * x ) ) from ?_ ) ?_
          · exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2, Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩
          · norm_num +zetaDelta at *
            nlinarith only [ Real.sqrt_nonneg x, Real.sq_sqrt ( Nat.cast_nonneg x ), show ( Nat.sqrt ( 2 * x ) : ℝ ) ^ 2 ≤ 2 * x by norm_cast; linarith [ Nat.sqrt_le ( 2 * x ) ] ]
        exact ⟨ 4, by norm_num, fun n x R hn hx hx' hx'' => le_trans ( relevant_primes_card_bound_R n x R hn hx hx' hx'' ) ( by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg x ] ) ⟩
      obtain ⟨ C₁, hC₁_pos, hC₁ ⟩ := sum_relevant_primes_bound_R
      obtain ⟨ C₂, hC₂_pos, hC₂ ⟩ := relevant_primes_card_bound_R
      refine ⟨ 8 * ( C₁ + C₂ + 1 ), by positivity, fun n x R hn hx hx' hx'' => ?_ ⟩ ; specialize hC₁ n x R hn hx hx' hx'' ; specialize hC₂ n x R hn hx hx' hx'' ; simp_all +decide [ Finset.sum_add_distrib ]
      refine le_trans ( add_le_add hC₁ ( mul_le_mul_of_nonneg_right hC₂ <| by positivity ) ) ?_
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_left <| by positivity ) <| by positivity )
      field_simp
      rw [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ]
      rw [ div_le_div_iff_of_pos_right ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) ]
      ring_nf
      by_cases hx : x = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
      nlinarith [ show ( n : ℝ ) * W_sq n ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( mod_cast hn ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ), show ( n : ℝ ) * W_sq n ≥ 0 by positivity ]

/-
The expected number of bad a's for R in (x, 2x] is bounded.
-/
lemma expected_bad_a_bound_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨ C, hC ⟩ := sum_relevant_primes_bound_case_mid
      -- Apply the bound from `sum_bad_a_ii_le_sum_bad_candidates` and `bad_candidates_prob_bound`.
      have h_bound : ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
          (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
          (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card := by
            intros n x R ε hn hx hxR hR ε_pos
            have h_sum_bound : (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) ≤ (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) := by
              convert sum_bad_a_ii_le_sum_bad_candidates _ _ _ _ using 1
            gcongr
      obtain ⟨ C', hC' ⟩ := bad_candidates_prob_bound
      refine ⟨ C' * C, mul_pos hC'.1 hC.1, fun n x R ε hn hx hR hR' hε => le_trans ( h_bound n x R ε hn hx hR hR' hε ) ?_ ⟩
      -- Apply the bound from `bad_candidates_prob_bound` to each term in the sum.
      have h_term_bound : ∀ a ∈ I_R_eps R ε, ∀ p ∈ relevant_primes n R x, (if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card ≤ C' * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
        intros a ha p hp
        by_cases haSF : a ∈ SF
        · rw [ if_pos haSF ]
          apply hC'.right n x a p hn (by
          exact Finset.mem_filter.mp hp |>.2 |> fun h => by
            exact lt_of_le_of_lt ( Nat.le_max_left _ _ ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 )
            ) (by
          exact Finset.mem_filter.mp hp |>.2) hx
        · simp [haSF]
          exact mul_nonneg hC'.1.le ( add_nonneg ( inv_nonneg.2 ( sq_nonneg _ ) ) ( div_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) )
      have h_sum_bound : (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card ≤ C' * (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
        simp +decide only [Finset.mul_sum _ _ _]
        simpa only [ Finset.sum_div _ _ _ ] using Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => h_term_bound a ha p hp
      refine le_trans h_sum_bound ?_
      simp_all +decide [mul_assoc]
      rw [ mul_left_comm ]
      gcongr
      refine le_trans ( hC.2 n x R hn hx hR hR' ) ?_
      gcongr
      · linarith
      · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) )
      · exact Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ )
      · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) )
      · exact Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ )

/-
Markov's inequality for finite sets with integer-valued functions.
-/
lemma markov_bound {α : Type*} (S : Finset α) (f : α → ℕ) (C : ℝ) (hC : C > 0) :
  ((S.filter (fun x => (f x : ℝ) > C)).card : ℝ) ≤ (∑ x ∈ S, (f x : ℝ)) / C := by
    rw [ le_div_iff₀' hC ]
    rw [ Finset.card_filter ]
    push_cast [ Finset.mul_sum _ _ _ ]
    exact Finset.sum_le_sum fun x _ => by split_ifs <;> linarith

/-
The probability of a bad candidate for R in (x, 2x] is bounded.
-/
lemma prob_bad_candidates_ii_R_bound_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
    ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
    C / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 → ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤ C₁ * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x))) := by
        exact expected_bad_a_bound_mid
      refine ⟨ C₁, hC₁.1, fun n x R ε hn hx hx' hx'' hε => ?_ ⟩
      have h_markov : ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) ≤ (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (ε^2 * R) := by
        apply markov_bound
        exact mul_pos ( sq_pos_of_pos hε ) ( Nat.cast_pos.mpr ( by linarith ) )
      refine le_trans ( div_le_div_of_nonneg_right h_markov <| Nat.cast_nonneg _ ) ?_
      convert mul_le_mul_of_nonneg_right ( hC₁.2 n x R ε hn hx hx' hx'' hε ) ( by positivity : 0 ≤ ( ε ^ 2 * R : ℝ ) ⁻¹ ) using 1
      · ring
      · ring

/-
For large enough n, the ratio |I_R|/R is bounded by 2*epsilon.
-/
lemma card_I_R_eps_ratio_bound :
  ∀ ε : ℝ, 0 < ε →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n →
  ((I_R_eps R ε).card : ℝ) / R ≤ 2 * ε := by
    intro ε hε_pos
    use Nat.ceil (1 / ε) + 1
    intro n hn R hR
    have h_card_I_R_eps : ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
      have := card_I_R_eps_le R ε ( by linarith ) hε_pos
      aesop
    rw [ div_le_iff₀ ]
    all_goals
      nlinarith [ show ( R : ℝ ) ≥ ⌈1 / ε⌉₊ + 1 by exact_mod_cast hn.trans hR, Nat.le_ceil ( 1 / ε ), one_div_mul_cancel hε_pos.ne' ]

/-
Simplified bound for the probability of a bad candidate for x < R <= 2x.
-/
lemma prob_bad_candidates_ii_R_bound_mid_simplified :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R → x < R → R ≤ 2 * x →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 → ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ C₁ / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      exact prob_bad_candidates_ii_R_bound_mid
    generalize_proofs at *
    (
    obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n → ((I_R_eps R ε).card : ℝ) / R ≤ C₂ * ε := by
      exact ⟨ 2, by norm_num, fun ε hε => by obtain ⟨ N₀, hN₀ ⟩ := card_I_R_eps_ratio_bound ε hε; exact ⟨ N₀, fun n hn R hR => by linarith [ hN₀ n hn R hR ] ⟩ ⟩
    generalize_proofs at *
    (
    refine ⟨ 2 * C₁ * C₂, mul_pos ( mul_pos two_pos hC₁.1 ) hC₂.1, fun ε hε₁ hε₂ => ?_ ⟩ ; obtain ⟨ N₀, hN₀ ⟩ := hC₂.2 ε hε₁ ; use Max.max N₀ 1 ; intros n hn x hx R hn' hx' hx'' ; by_cases hn'' : n = 0 <;> simp_all +decide [ division_def ]
    refine le_trans ( hC₁.2 n x R ε ( Nat.pos_of_ne_zero hn'' ) hx hx' hx'' hε₁ ) ?_
    -- Apply the bounds from hC₁ and hC₂ to simplify the expression.
    have h_simp : C₁ * (ε^2)⁻¹ * (C₂ * ε) * ((R.sqrt : ℝ)⁻¹ + (W_sq n : ℝ) * n * (x.sqrt : ℝ)⁻¹) ≤ 2 * C₁ * C₂ * ε⁻¹ * ((Real.sqrt R)⁻¹ + (W_sq n : ℝ) * n * (Real.sqrt x)⁻¹) := by
      field_simp
      rw [ mul_assoc ]
      rw [ mul_assoc, mul_assoc ]
      gcongr
      · linarith [ hC₁.1 ]
      · linarith [ hC₂.1 ]
      · rw [ mul_add ]
        gcongr <;> norm_num [ Nat.sqrt_le ]
        focus
          ring_nf
        · rw [ inv_le_comm₀ ]
          all_goals
            norm_num
          · nlinarith only [ show ( R : ℝ ) ≥ 1 by norm_cast; linarith, Real.mul_self_sqrt ( Nat.cast_nonneg R ), show ( R.sqrt : ℝ ) ≥ 1 by exact_mod_cast Nat.sqrt_pos.mpr ( by linarith ), show ( R : ℝ ) ≤ ( R.sqrt + 1 ) ^ 2 by norm_cast; linarith [ Nat.lt_succ_sqrt R ] ]
          · exact Nat.sqrt_pos.mpr ( by linarith )
          · linarith [ Nat.pos_of_ne_zero hn'' ]
        · rw [ mul_div, div_le_div_iff₀ ]
          all_goals
            norm_num
          · nlinarith only [ show ( W_sq n : ℝ ) * n ≥ 0 by positivity, show ( Real.sqrt x : ℝ ) ≤ x.sqrt + 1 by rw [ Real.sqrt_le_left ] <;> norm_cast <;> linarith [ Nat.lt_succ_sqrt x ], show ( x.sqrt : ℝ ) ≥ 1 by exact_mod_cast Nat.sqrt_pos.mpr ( by linarith ) ]
          · exact Nat.sqrt_pos.mpr ( by linarith )
          · linarith [ Nat.pos_of_ne_zero hn'' ]
    generalize_proofs at *
    (
    refine le_trans ?_ h_simp
    generalize_proofs at *
    (
    convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hN₀ n hn.1 R hn' ) ( show 0 ≤ C₁ * ( ε ^ 2 ) ⁻¹ by exact mul_nonneg hC₁.1.le ( inv_nonneg.2 ( sq_nonneg ε ) ) ) ) ( show 0 ≤ ( R.sqrt : ℝ ) ⁻¹ + W_sq n * n * ( x.sqrt : ℝ ) ⁻¹ by positivity ) using 1 ; ring!;))))

/-
There exists a constant C such that the probability of a bad candidate is bounded by $C/\epsilon * (1/\sqrt{R} + W n / \sqrt{x})$ for all $R \ge n$.
-/
lemma prob_bad_candidates_ii_R_bound_combined :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    -- By combining the results from lemmas `prob_bad_candidates_ii_R_bound_simplified` and `prob_bad_candidates_ii_R_bound_mid_simplified`, we can construct the desired constant `C`.
    obtain ⟨C1, hC1⟩ := prob_bad_candidates_ii_R_bound_simplified
    obtain ⟨C2, hC2⟩ := prob_bad_candidates_ii_R_bound_mid_simplified
    use Max.max C1 C2 + 1
    refine ⟨ by linarith [ le_max_left C1 C2, le_max_right C1 C2 ], fun ε hε₁ hε₂ => ?_ ⟩
    obtain ⟨ N₀₁, hN₀₁ ⟩ := hC1.2 ε hε₁ hε₂
    obtain ⟨ N₀₂, hN₀₂ ⟩ := hC2.2 ε hε₁ hε₂
    use Max.max N₀₁ N₀₂ + 1
    intro n hn x hx R hR
    by_cases hR' : R ≤ 2 * x
    · by_cases hR'' : R ≤ x
      · exact le_trans ( hN₀₁ n ( by linarith [ Nat.le_max_left N₀₁ N₀₂ ] ) x hx R hR hR'' ) ( mul_le_mul_of_nonneg_right ( by rw [ div_le_div_iff_of_pos_right hε₁ ] ; linarith [ le_max_left C1 C2, le_max_right C1 C2 ] ) ( by positivity ) )
      · refine le_trans ( hN₀₂ n ( by linarith [ le_max_left N₀₁ N₀₂, le_max_right N₀₁ N₀₂ ] ) x hx R hR ( by linarith ) hR' ) ?_
        gcongr
        linarith [ le_max_right C1 C2 ]
    · rw [ bad_candidates_ii_R_empty_of_large_R ]
      all_goals
        norm_num
      · exact mul_nonneg ( div_nonneg ( add_nonneg ( le_max_of_le_left hC1.1.le ) zero_le_one ) hε₁.le ) ( add_nonneg ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) ) ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Real.sqrt_nonneg _ ) ) )
      · linarith
      · exact hε₁

/-
The total failure probability is the sum of the failure probabilities for each R in the geometric progression.
-/
def total_failure_prob (n x : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (max_k n x ε + 5),
    ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card

/-
The total failure probability is less than 1/6 for sufficiently large n and x.
-/
lemma total_failure_prob_bound :
  ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  total_failure_prob n x ε < 1/6 := by
    intro ε hε_pos hε_lt_1
    obtain ⟨C₁, hC₁_pos, hC₁_bound⟩ := prob_bad_candidates_ii_R_bound_combined
    obtain ⟨C₂, hC₂_pos, hC₂_sum⟩ := sum_inv_sqrt_R_bound
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, (C₁ / ε * ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) < 1 / 12 := by
      -- By Lemma term_2_tendsto_zero, the term tends to zero as x goes to infinity. So, for any fixed n, we can choose x₀ large enough so that the term is less than 1/12.
      have h_term_zero : ∀ n : ℕ, Filter.Tendsto (fun x : ℕ => (C₁ / ε) * ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) Filter.atTop (nhds 0) := by
        intro n
        have := term_2_tendsto_zero n ε hε_pos
        simpa using this.const_mul _
      exact ⟨ 0, fun n hn => by rcases Metric.tendsto_atTop.mp ( h_term_zero n ) ( 1 / 12 ) ( by norm_num ) with ⟨ x₀, hx₀ ⟩ ; exact ⟨ x₀, fun x hx => by linarith [ abs_lt.mp ( hx₀ x hx ) ] ⟩ ⟩
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ x : ℕ, x / 2 ≥ W_sq n → (∑ k ∈ Finset.range (max_k n x ε + 5), (C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k)))) ≤ (C₁ / ε^2 * C₂ / Real.sqrt n) := by
      use Nat.ceil (2 / ε) + 1
      intro n hn x hx
      specialize hC₂_sum ε hε_pos hε_lt_1 n ( Nat.lt_of_ceil_lt hn ) ( max_k n x ε + 5 )
      simp_all +decide [mul_assoc,
        mul_comm, mul_left_comm, div_eq_mul_inv]
      convert mul_le_mul_of_nonneg_left hC₂_sum ( show 0 ≤ C₁ * ε⁻¹ by positivity ) using 1 <;> first | rfl | ring_nf
      rw [ Finset.mul_sum _ _ _ ]
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, (C₁ / ε^2 * C₂ / Real.sqrt n) < 1 / 12 := by
      have h_lim : Filter.Tendsto (fun n : ℕ => C₁ / ε^2 * C₂ / Real.sqrt n) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( by simpa [Real.sqrt_eq_rpow, Function.comp_def] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop )
      simpa using h_lim.eventually ( gt_mem_nhds <| by norm_num )
    obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ x : ℕ, x / 2 ≥ W_sq n → ∀ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k) + (W_sq n : ℝ) * n / Real.sqrt x) := by
      obtain ⟨ N₃, hN₃ ⟩ := hC₁_bound ε hε_pos hε_lt_1
      use N₃ + 1
      intros n hn x hx k hk
      have h_geometric_R_rec_ge_n : ∀ k, geometric_R_rec n ε k ≥ n := by
        intro k
        induction k with
        | zero =>
          exact Nat.le_refl n
        | succ k ih =>
          exact Nat.le_floor <| by
            nlinarith [show (geometric_R_rec n ε k : ℝ) ≥ n by exact_mod_cast ih]
      exact hN₃ n (by linarith) x hx (geometric_R_rec n ε k) (h_geometric_R_rec_ge_n k)
    use Max.max N₀ ( Max.max N₁ ( Max.max N₂ N₃ ) )
    intro n hn
    obtain ⟨x₀, hx₀⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
    use Max.max x₀ (W_sq n * 2)
    intros x hx
    have h_sum_bound : ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ k ∈ Finset.range (max_k n x ε + 5), C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k) + (W_sq n : ℝ) * n / Real.sqrt x) := by
      exact Finset.sum_le_sum fun k hk => hN₃ n ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) hn ) x ( by linarith [ Nat.div_add_mod x 2, Nat.mod_lt x two_pos, le_max_right x₀ ( W_sq n * 2 ) ] ) k hk
    simp_all +decide [ Finset.sum_add_distrib, mul_add ]
    exact lt_of_le_of_lt h_sum_bound ( by have := hN₁ n hn.2.1 x ( by omega ) ; have := hN₂ n hn.2.2.1; have := hx₀ x hx.1; norm_num at *; linarith )

/-
For sufficiently large n and x, there exists a candidate n' that satisfies the GeometricGood_rec property.
-/
lemma exists_GeometricGood_rec :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∃ n', GeometricGood_rec n n' x ε := by
    intro ε hε_pos hε_lt_1
    obtain ⟨N₀₁, hN₀₁⟩ : ∃ N₀₁ : ℕ, ∀ n ≥ N₀₁, ∃ x₀₁ : ℕ, ∀ x ≥ x₀₁, ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card < 1/3 := by
      exact bad_candidates_i_fraction_bound

    obtain ⟨N₀₂, hN₀₂⟩ : ∃ N₀₂ : ℕ, ∀ n ≥ N₀₂, ∃ x₀₂ : ℕ, ∀ x ≥ x₀₂, total_failure_prob n x ε < 1/6 := by
      exact total_failure_prob_bound ε hε_pos hε_lt_1
    obtain ⟨N₀₃, hN₀₃⟩ : ∃ N₀₃ : ℕ, ∀ n ≥ N₀₃, ∃ x₀₃ : ℕ, ∀ x ≥ x₀₃, (candidates x (W_sq n)).card > 0 := by
      use 1
      intro n hn
      use 2 * W_sq n + 1
      intro x hx
      have h_candidates_nonempty : ∃ n' ∈ Finset.Icc (x / 2 + 1) x, W_sq n ∣ n' := by
        use W_sq n * ((x / 2) / W_sq n + 1)
        norm_num +zetaDelta at *
        exact ⟨ by linarith [ Nat.div_add_mod ( x / 2 ) ( W_sq n ), Nat.mod_lt ( x / 2 ) ( show W_sq n > 0 from Nat.pos_of_ne_zero ( by exact mt Finset.prod_eq_zero_iff.mp ( by intros h; cases h; aesop ) ) ) ], by linarith [ Nat.div_mul_le_self ( x / 2 ) ( W_sq n ), Nat.div_mul_le_self x 2, Nat.div_add_mod x 2, Nat.mod_lt x two_pos ] ⟩
      exact Finset.card_pos.mpr ⟨ h_candidates_nonempty.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp h_candidates_nonempty.choose_spec.1 ], by linarith [ Finset.mem_Icc.mp h_candidates_nonempty.choose_spec.1 ] ⟩, h_candidates_nonempty.choose_spec.2 ⟩ ⟩
    use Max.max N₀₁ ( Max.max N₀₂ N₀₃ ) + 1
    intros n hn
    obtain ⟨ x₀₁, hx₀₁ ⟩ := hN₀₁ n ( by linarith [ le_max_left N₀₁ ( max N₀₂ N₀₃ ) ] )
    obtain ⟨ x₀₂, hx₀₂ ⟩ := hN₀₂ n ( by linarith [ le_max_right N₀₁ ( max N₀₂ N₀₃ ), le_max_left N₀₂ N₀₃ ] )
    obtain ⟨ x₀₃, hx₀₃ ⟩ := hN₀₃ n ( by linarith [ le_max_right N₀₁ ( max N₀₂ N₀₃ ), le_max_right N₀₂ N₀₃ ] )
    use Max.max x₀₁ ( Max.max x₀₂ x₀₃ ) + 1
    intros x hx
    specialize hx₀₁ x ( by linarith [ le_max_left x₀₁ ( Max.max x₀₂ x₀₃ ) ] )
    specialize hx₀₂ x ( by linarith [ le_max_right x₀₁ ( Max.max x₀₂ x₀₃ ), le_max_left x₀₂ x₀₃ ] )
    specialize hx₀₃ x ( by linarith [ le_max_right x₀₁ ( Max.max x₀₂ x₀₃ ), le_max_right x₀₂ x₀₃ ] )
    norm_num at *
    have h_exists_good : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card < 1 := by
      linarith!
    have h_exists_good : ∃ n' ∈ candidates x (W_sq n), n' ∉ bad_candidates_i n x ∧ ∀ k ∈ Finset.range (max_k n x ε + 5), n' ∉ bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n) := by
      have h_sum : ((bad_candidates_i n x).card : ℝ) + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) < (candidates x (W_sq n)).card := by
        rw [ ← Finset.sum_div _ _ _ ] at *
        rwa [ ← add_div, div_lt_one ( Nat.cast_pos.mpr <| Finset.card_pos.mpr hx₀₃ ) ] at h_exists_good
      contrapose! h_sum
      have h_sum : (candidates x (W_sq n)).card ≤ (bad_candidates_i n x).card + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℕ) := by
        have h_union : candidates x (W_sq n) ⊆ bad_candidates_i n x ∪ Finset.biUnion (Finset.range (max_k n x ε + 5)) (fun k => bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)) := by
          intro n' hn'
          specialize h_sum n' hn'
          by_cases h : n' ∈ bad_candidates_i n x <;> aesop
        exact le_trans ( Finset.card_le_card h_union ) ( Finset.card_union_le _ _ ) |> le_trans <| add_le_add_right ( Finset.card_biUnion_le ) _
      exact_mod_cast h_sum
    exact h_exists_good

/-
If a set has good density at R1, and R is close to R1 (within factor 1+epsilon), then it has good density at R.
-/
lemma density_interpolation_lemma (S : Set ℕ) (R1 R2 R : ℕ) (ε C : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hR1 : R1 > 0)
    (hR2 : R2 ≤ (1 + ε) * R1)
    (hR : R1 ≤ R ∧ R ≤ R2)
    (h_dens : ((S ∩ Finset.Icc 1 R1).ncard : ℝ) / R1 ≥ 6 / Real.pi^2 - C * ε) :
    ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - (C + 1) * ε := by
      -- Using the density bound for $R_1$, this is $\ge (6/\pi^2 - C\epsilon) \frac{R_1}{R}$.
      have h_dens_R : (S ∩ (Finset.Icc 1 R)).ncard / (R : ℝ) ≥ (6 / Real.pi ^ 2 - C * ε) * (R1 / R : ℝ) := by
        refine le_trans ( mul_le_mul_of_nonneg_right h_dens <| by positivity ) ?_
        rw [ div_mul_div_cancel₀ ( by positivity ) ]
        gcongr
        · exact Set.Finite.subset ( Finset.finite_toSet ( Finset.Icc 1 R ) ) fun x hx => hx.2
        · linarith
      -- Since $R \le R_2 \le (1+\epsilon)R_1$, we have $\frac{R_1}{R} \ge \frac{1}{1+\epsilon} \ge 1 - \epsilon$.
      have h_frac_R1_R : (R1 : ℝ) / R ≥ 1 - ε := by
        rw [ ge_iff_le, le_div_iff₀ ] <;> nlinarith [ show ( R1 : ℝ ) ≥ 1 by norm_cast, show ( R : ℝ ) ≥ R1 by norm_cast; linarith, show ( R2 : ℝ ) ≥ R by norm_cast; linarith ]
      contrapose! h_dens
      refine lt_of_le_of_lt (b := 1) ?_ ( lt_sub_iff_add_lt'.mpr ?_ )
      · exact div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp [ Set.ncard_eq_toFinset_card' ] ) <| by positivity
      · nlinarith [ show ( R1 : ℝ ) / R ≤ 1 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ]

/-
If n' is a good candidate, then n' + a is squarefree for all squarefree a <= n.
-/
lemma GeometricGood_rec_implies_condition_i (n n' x : ℕ) (ε : ℝ)
  (hgood : GeometricGood_rec n n' x ε) :
  ∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF := by
    -- Since $n'$ is not in bad_candidates_i, for all $a \in [1, n]$, if $a$ is squarefree, then $n' + a$ must be squarefree.
    have h_not_bad_i : n' ∉ bad_candidates_i n x := by
      exact hgood.2.1
    contrapose! h_not_bad_i
    obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h_not_bad_i
    have := hgood.1
    obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ : ∃ p, Nat.Prime p ∧ p > n^2 ∧ p^2 ∣ n' + a := by
      apply key_construction_i_deterministic
      · unfold candidates at this
        aesop
      · assumption
      · assumption
      · exact ha₃
    simp_all +decide [ candidates, bad_candidates_i ]
    refine ⟨ a, ha₁, p, ⟨ ⟨ hp₂, ?_ ⟩, hp₁ ⟩, ?_ ⟩
    · rw [ Nat.le_sqrt ]
      nlinarith [ show hp₃ > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ]
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, this.2 ⟩, by aesop ⟩

/-
The terms of the recursive geometric progression are always positive if n > 0 and epsilon > 0.
-/
lemma geometric_R_rec_pos (n : ℕ) (ε : ℝ) (k : ℕ) (hn : n > 0) (hε : 0 < ε) :
  geometric_R_rec n ε k > 0 := by
    induction k with
    | zero =>
      exact hn
    | succ k ih =>
      exact Nat.floor_pos.mpr ( by nlinarith [ ( by norm_cast : ( 0 :ℝ ) < n ), show ( geometric_R_rec n ε k : ℝ ) ≥ 1 from Nat.one_le_cast.mpr ih ] )

/-
The recursive geometric progression grows at most by a factor of (1 + epsilon) at each step.
-/
lemma geometric_R_rec_growth (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  (geometric_R_rec n ε (k + 1) : ℝ) ≤ (1 + ε) * geometric_R_rec n ε k := by
    exact Nat.floor_le ( by positivity )

/-
If the density is good at R_k, it is good at any R in [R_k, R_{k+1}] (with a slightly worse constant).
-/
lemma density_interpolation_geometric (n : ℕ) (ε : ℝ) (k : ℕ) (R : ℕ) (C : ℝ) (S : Set ℕ)
  (hε : 0 < ε) (hε1 : ε < 1)
  (hn : n > 0)
  (h_range : geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1))
  (h_dens : ((S ∩ Finset.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) / (geometric_R_rec n ε k) ≥ 6 / Real.pi^2 - C * ε) :
  ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - (C + 1) * ε := by
    apply density_interpolation_lemma S (geometric_R_rec n ε k) (geometric_R_rec n ε (k + 1)) R ε C hε hε1 (geometric_R_rec_pos n ε k hn hε) (geometric_R_rec_growth n ε k hε) h_range h_dens

/-
The recursive geometric progression is non-decreasing.
-/
lemma geometric_R_rec_monotone
  (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  geometric_R_rec n ε k ≤ geometric_R_rec n ε (k + 1) := by
  -- unfold the recursive definition at k+1
  change geometric_R_rec n ε k
      ≤ Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ))

  -- it suffices to prove the real inequality before applying floor
  apply Nat.le_floor

  have h_mul :
      (geometric_R_rec n ε k : ℝ)
        ≤ (1 + ε) * (geometric_R_rec n ε k : ℝ) := by
    have h₁ : (1 : ℝ) ≤ 1 + ε := by
      have : (0 : ℝ) ≤ ε := le_of_lt hε
      linarith
    have h₂ : (0 : ℝ) ≤ (geometric_R_rec n ε k : ℝ) := by
      exact_mod_cast Nat.zero_le _
    -- multiply inequality 1 ≤ 1+ε by a nonnegative number
    simpa [one_mul] using mul_le_mul_of_nonneg_right h₁ h₂

  simpa using h_mul

/-
If n' is a GeometricGood candidate, then the number of bad elements up to R_k is bounded by C * epsilon * R_k, provided R_k <= n'.
-/
lemma bad_upto_bound_rec :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ≤ max_k n x ε + 5,
  geometric_R_rec n ε k ≤ n' →
  ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) ≤ C * ε * (geometric_R_rec n ε k) := by
    -- Let $C_{interval}$ be the constant from `bad_in_interval_bound_rec`.
    obtain ⟨C_interval, hC_interval_pos, hC_interval⟩ := bad_in_interval_bound_rec_v4
    -- Let $C_{sum}$ be the constant from `geometric_sum_bound`.
    obtain ⟨C_sum, hC_sum_pos, hC_sum⟩ := geometric_sum_bound
    use C_interval * C_sum
    refine ⟨ mul_pos hC_interval_pos hC_sum_pos, ?_ ⟩
    intro ε hε hε1
    obtain ⟨N₀, hN₀⟩ := hC_interval ε hε hε1
    obtain ⟨N₀', hN₀'⟩ := hC_sum ε hε hε1
    use max N₀ N₀' + 1
    intro n hn
    obtain ⟨x₀, hx₀⟩ := hN₀ n (by linarith [Nat.le_max_left N₀ N₀'])
    use max x₀ (2 * n) + 1
    intro x hx n' hn' k hk hk_le_n'
    have h_sum : ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) ≤ ∑ j ∈ Finset.range k, ((bad_in_interval n' (geometric_R_rec n ε j) ε).card : ℝ) := by
      have h_sum : bad_upto n' (geometric_R_rec n ε k) ⊆ Finset.biUnion (Finset.range k) (fun j => bad_in_interval n' (geometric_R_rec n ε j) ε) := by
        apply bad_upto_subset
        · grind
        · exact GeometricGood_rec_implies_condition_i n n' x ε hn' |> fun h => by simpa using h
      exact_mod_cast le_trans ( Finset.card_le_card h_sum ) ( Finset.card_biUnion_le )
    refine le_trans h_sum ?_
    refine le_trans ( Finset.sum_le_sum fun i hi => hx₀ x ( by linarith [ Nat.le_max_left x₀ ( 2 * n ) ] ) n' hn' i ( Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp hi ] ) ) ?_ ) ?_
    · have h_bound : n' ≤ x := by
        exact hn'.1 |> fun h => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp h |>.1 ) ]
      have h_bound : ⌊(1 + ε) * (geometric_R_rec n ε i : ℝ)⌋₊ ≤ x := by
        have h_bound : geometric_R_rec n ε (i + 1) ≤ x := by
          have h_bound : geometric_R_rec n ε (i + 1) ≤ geometric_R_rec n ε k := by
            have h_bound : ∀ j, i + 1 ≤ j → j ≤ k → geometric_R_rec n ε (i + 1) ≤ geometric_R_rec n ε j := by
              intros j hj₁ hj₂
              induction j, hj₁ using Nat.le_induction with
              | base =>
                grind
              | succ j hj ih =>
                exact le_trans ( ih ( Nat.le_of_succ_le hj₂ ) ) ( geometric_R_rec_monotone n ε j hε )
            exact h_bound k ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hi ] )
          linarith
        simpa [geometric_R_rec] using h_bound
      linarith
    · convert mul_le_mul_of_nonneg_left ( hN₀' n ( by linarith [ Nat.le_max_right N₀ N₀' ] ) k ) ( show 0 ≤ C_interval * ε ^ 2 by positivity ) using 1
      focus
        ring_nf
      · rw [ Finset.mul_sum _ _ _ ]
      · grind

/-
For any epsilon, for sufficiently large R, the density of squarefree numbers up to R is at least 6/pi^2 - epsilon.
-/
lemma SF_density_lower_bound :
  ∀ ε : ℝ, 0 < ε →
  ∃ N₀ : ℕ, ∀ R ≥ N₀,
  ((Finset.Icc 1 R).filter (fun x => x ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - ε := by
    intro ε hε_pos
    have h_density : ∃ C : ℝ, C > 0 ∧ ∀ R : ℕ, R > 0 → abs (((Finset.Icc 1 R).filter (fun x => x ∈ SF)).card - (6 / Real.pi^2) * R) ≤ C * Real.sqrt R := by
      have := SF_count_bound
      exact ⟨ this.choose, this.choose_spec.1, fun R hR => le_trans ( this.choose_spec.2 R hR ) ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ ) ) this.choose_spec.1.le ) ⟩
    obtain ⟨ C, hC₀, hC ⟩ := h_density
    use ⌈ ( C / ε ) ^ 2⌉₊ + 1; intro R hR; rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> norm_num at * <;> try nlinarith
    have := hC R ( by linarith )
    rw [ abs_le ] at this
    nlinarith [ show ( R : ℝ ) ≥ ⌈ ( C / ε ) ^ 2⌉₊ + 1 by exact_mod_cast hR, Nat.le_ceil ( ( C / ε ) ^ 2 ), Real.sqrt_nonneg R, Real.sq_sqrt <| Nat.cast_nonneg R, mul_div_cancel₀ C hε_pos.ne.symm, pow_two_nonneg ( Real.sqrt R - C / ε ), Real.mul_self_sqrt <| Nat.cast_nonneg R ]

/-
If n' is a GeometricGood candidate, then the density of good elements at each point in the geometric progression is close to 6/pi^2.
-/
lemma GeometricGood_rec_implies_density_at_points_strong :
  ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ≤ max_k n x ε + 5,
  let R := geometric_R_rec n ε k
  R ≤ n' →
  let S := {a | a ∈ SF ∧ n' + a ∈ SF}
  ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - C * ε := by
    obtain ⟨C₁, hC₁⟩ := bad_upto_bound_rec
    field_simp
    refine ⟨ 6 + C₁, by linarith, fun ε hε₁ hε₂ => ?_ ⟩
    obtain ⟨ N₀, hN₀ ⟩ := SF_density_lower_bound ( ε / 2 ) ( half_pos hε₁ )
    obtain ⟨ N₁, hN₁ ⟩ := hC₁.2 ε hε₁ hε₂
    use Max.max N₀ N₁ + 1
    intro n hn
    obtain ⟨ x₀, hx₀ ⟩ := hN₁ n ( by linarith [ le_max_right N₀ N₁ ] )
    use x₀
    intros x hx n' hn' k hk hk'
    specialize hx₀ x hx n' hn' k hk hk'
    specialize hN₀ ( geometric_R_rec n ε k ) ( by
      -- By definition of $geometric_R_rec$, we know that $geometric_R_rec n ε k \geq n$ for all $k$.
      have h_geometric_R_rec_ge_n : ∀ k, geometric_R_rec n ε k ≥ n := by
        intro k
        induction k with
        | zero =>
          norm_num [ *, geometric_R_rec ]
        | succ k ih =>
          norm_num [ *, geometric_R_rec ]
          exact Nat.le_floor <| by nlinarith [ show ( geometric_R_rec n ε k : ℝ ) ≥ n by exact_mod_cast ih ]
      linarith [ h_geometric_R_rec_ge_n k, le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ; norm_num at *
    -- The number of good elements is at least the number of squarefree elements minus the number of bad elements.
    have h_good_elements : (({a | a ∈ SF ∧ n' + a ∈ SF} ∩ Set.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) ≥ ((Finset.Icc 1 (geometric_R_rec n ε k)).filter (fun x => x ∈ SF)).card - ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) := by
      rw [ ← Set.ncard_coe_finset ]
      rw [ show { a | a ∈ SF ∧ n' + a ∈ SF } ∩ Set.Icc 1 ( geometric_R_rec n ε k ) = ( Finset.filter ( fun x => x ∈ SF ) ( Finset.Icc 1 ( geometric_R_rec n ε k ) ) ) \ ( bad_upto n' ( geometric_R_rec n ε k ) ) from ?_ ]
      · rw [ Set.ncard_coe_finset, Set.ncard_coe_finset ]
        rw [ Finset.card_sdiff ]
        norm_num
        rw [ Nat.cast_sub ]
        · linarith [ show ( Finset.card ( bad_upto n' ( geometric_R_rec n ε k ) ∩ Finset.filter ( fun x => x ∈ SF ) ( Finset.Icc 1 ( geometric_R_rec n ε k ) ) ) : ℝ ) ≤ Finset.card ( bad_upto n' ( geometric_R_rec n ε k ) ) from mod_cast Finset.card_mono <| Finset.inter_subset_left ]
        · exact Finset.card_le_card fun x hx => by aesop
      · ext
        simp [bad_upto]
        grind
    -- Substitute the lower bound for the number of good elements into the inequality.
    have h_subst : 6 / Real.pi^2 ≤ (({a | a ∈ SF ∧ n' + a ∈ SF} ∩ Set.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) / (geometric_R_rec n ε k) + C₁ * ε + ε / 2 := by
      refine le_trans hN₀ ?_
      norm_num +zetaDelta at *
      rw [ div_add', div_le_div_iff_of_pos_right ]
      all_goals
        nlinarith [ show ( geometric_R_rec n ε k : ℝ ) > 0 from Nat.cast_pos.mpr ( geometric_R_rec_pos n ε k ( by linarith [ le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ( by linarith [ le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ) ]
    field_simp
    rw [ div_le_iff₀ ] at h_subst
    all_goals
      nlinarith [ Real.pi_gt_three, pow_pos Real.pi_pos 2 ]

/-
If n' is a GeometricGood candidate, then condition (ii) of the Key Proposition holds.
-/
lemma GeometricGood_rec_implies_condition_ii :
  ∃ C_ii : ℝ, C_ii > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ R : ℕ, n ≤ R → R ≤ n' →
  let numerator := ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∈ SF)).card
  (numerator : ℝ) / R ≥ 6 / Real.pi^2 - C_ii * ε := by
    -- Set C_ii = C + 1.
    obtain ⟨C, hC_pos, hC⟩ := GeometricGood_rec_implies_density_at_points_strong
    refine ⟨ C + 1, ?_, ?_ ⟩ <;> try linarith
    intro ε hε₁ hε₂
    obtain ⟨N₀, hN₀⟩ := hC ε hε₁ hε₂
    obtain ⟨N₀', hN₀'⟩ := geometric_covers_x ε hε₁ hε₂
    use max N₀ N₀' + 1
    intro n hn
    obtain ⟨ x₀, hx₀ ⟩ := hN₀ n ( by linarith [ le_max_left N₀ N₀' ] )
    use x₀ + n + 1
    intro x hx n' hn' R hR₁ hR₂
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k ≤ max_k n x ε + 5, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
      have h_exists_k : ∃ k ≤ max_k n x ε + 4, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
        have h_exists_k : ∃ k ≤ max_k n x ε + 4, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
          have h_exists_k : ∃ k ≤ max_k n x ε + 4, R ≤ geometric_R_rec n ε (k + 1) := by
            have h_exists_k : R ≤ geometric_R_rec n ε (max_k n x ε + 4) := by
              have hR_le_x : R ≤ x := by
                exact le_trans hR₂ ( hn'.1 |> fun h => Finset.mem_Icc.mp ( Finset.mem_filter.mp h |>.1 ) |> fun h => h.2 )
              exact le_trans hR_le_x ( hN₀' n ( by linarith [ Nat.le_max_right N₀ N₀' ] ) x ( by linarith ) )
            exact ⟨ max_k n x ε + 3, by linarith, h_exists_k ⟩
          contrapose! h_exists_k
          intro k hk
          induction k with
          | zero =>
            norm_num at *
            exact h_exists_k 0 bot_le ( by exact Nat.le_trans ( by exact Nat.le_refl _ ) hR₁ )
          | succ k ih =>
            norm_num at *
            exact h_exists_k _ ( by linarith ) ( by linarith [ ih ( by linarith ) ] )
        exact h_exists_k
      exact ⟨ h_exists_k.choose, Nat.le_succ_of_le h_exists_k.choose_spec.1, h_exists_k.choose_spec.2.1, h_exists_k.choose_spec.2.2 ⟩
    have := hx₀ x ( by linarith ) n' hn' k hk₁ ( by linarith )
    convert density_interpolation_geometric n ε k R C { a | a ∈ SF ∧ n' + a ∈ SF } hε₁ hε₂ ( by linarith [ Nat.le_max_left N₀ N₀', Nat.le_max_right N₀ N₀' ] ) ⟨ hk₂.1, hk₂.2 ⟩ this using 1
    rw [ ← Set.ncard_coe_finset ]
    congr
    ext
    aesop

/-
If n' is a GeometricGood candidate, then it satisfies the conclusion of the Key Proposition.
-/
lemma GeometricGood_implies_PropositionKey :
  ∃ C_key : ℝ, C_key > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  PropositionKey_conclusion n n' ε C_key := by
    -- Let's choose C_key from GeometricGood_rec_implies_condition_ii.
    obtain ⟨C_ii, hC_ii_pos, hC_ii⟩ := GeometricGood_rec_implies_condition_ii
    use C_ii
    exact ⟨ hC_ii_pos, fun ε hε₁ hε₂ => by obtain ⟨ N₀, hN₀ ⟩ := hC_ii ε hε₁ hε₂; exact ⟨ N₀, fun n hn => by obtain ⟨ x₀, hx₀ ⟩ := hN₀ n hn; exact ⟨ x₀, fun x hx n' hn' => ⟨ by simpa using GeometricGood_rec_implies_condition_i n n' x ε hn', hx₀ x hx n' hn' ⟩ ⟩ ⟩ ⟩

/-
Key Proposition: For any epsilon and sufficiently large n, there exist arbitrarily large n' satisfying properties (i) and (ii).
-/
theorem PropositionKey :
  ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ M : ℕ, ∃ n' ≥ M, PropositionKey_conclusion n n' ε C := by
    obtain ⟨C_key, hC_key_pos, hC_key⟩ := GeometricGood_implies_PropositionKey
    use C_key
    -- By combining the results from hC_key and exists_GeometricGood_rec, we can conclude the proof.
    have h_combined : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀, ∀ n ≥ N₀, ∃ x₀, ∀ x ≥ x₀, ∃ n', GeometricGood_rec n n' x ε ∧ n' ≥ x / 2 := by
      intro ε hε_pos hε_lt_1
      obtain ⟨N₀, hN₀⟩ := exists_GeometricGood_rec ε hε_pos hε_lt_1
      use N₀ + 1
      intro n hn
      obtain ⟨x₀, hx₀⟩ := hN₀ n (by linarith)
      use x₀ + 2 * W_sq n + 1
      intro x hx
      obtain ⟨n', hn'⟩ := hx₀ x (by linarith)
      exact ⟨ n', hn', Nat.le_of_not_lt fun h => by have := hn'.1; unfold candidates at this; norm_num at this; omega ⟩
    refine ⟨ hC_key_pos, fun ε hε₁ hε₂ => ?_ ⟩
    obtain ⟨ N₀, hN₀ ⟩ := h_combined ε hε₁ hε₂
    obtain ⟨ N₁, hN₁ ⟩ := hC_key ε hε₁ hε₂
    use Max.max N₀ N₁
    intros n hn M
    obtain ⟨ x₀, hx₀ ⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
    obtain ⟨ x₁, hx₁ ⟩ := hN₁ n (le_trans (le_max_right _ _) hn)
    obtain ⟨ n', hn'₁, hn'₂ ⟩ := hx₀ ( 2 * M + x₁ + x₀ + 1 ) ( by linarith )
    exact ⟨ n', by omega, hx₁ _ ( by omega ) _ hn'₁ ⟩

/-
The set A is the union of sets of squarefree numbers a in (n_k, n_{k+1}] such that n_{k+1} + a is squarefree.
-/
def constructed_A (n : ℕ → ℕ) : Set ℕ :=
  ⋃ k, { a | a ∈ Set.Ioc (n k) (n (k+1)) ∧ a ∈ SF ∧ n (k+1) + a ∈ SF }

/-
The sequence n_k satisfies the properties required for the construction of A.
-/
def SequenceProperties (n : ℕ → ℕ) (C : ℝ) : Prop :=
  (∀ k ≥ 1, n k < n (k+1)) ∧
  (∀ k ≥ 1, ∀ a ∈ Finset.Icc 1 (n k), a ∈ SF → n (k+1) + a ∈ SF) ∧
  (∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k+1) →
    ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n (k+1) + a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k) ∧
  (∀ k ≥ 1, n (k+1) ≥ (k+1) * n k)

/-
C_seq is the constant from PropositionKey. N_seq is the threshold function from PropositionKey.
-/
noncomputable def C_seq : ℝ := Classical.choose PropositionKey

lemma C_seq_pos : C_seq > 0 := (Classical.choose_spec PropositionKey).1

noncomputable def N_seq (ε : ℝ) : ℕ :=
  if h : 0 < ε ∧ ε < 1 then
    Classical.choose ((Classical.choose_spec PropositionKey).2 ε h.1 h.2)
  else 0

/-
epsilon_seq k is 1/(k+1). It is between 0 and 1 for k >= 1.
-/
noncomputable def epsilon_seq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma epsilon_seq_valid (k : ℕ) (hk : k ≥ 1) : 0 < epsilon_seq k ∧ epsilon_seq k < 1 := by
  exact ⟨ by rw [ epsilon_seq ] ; exact one_div_pos.mpr ( by positivity ), by rw [ epsilon_seq ] ; exact div_lt_self zero_lt_one ( by norm_cast; linarith ) ⟩

/-
N_seq satisfies the property that for any n >= N_seq(epsilon), and any M, there exists n' >= M satisfying the Key Proposition conclusion.
-/
lemma N_seq_spec (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
  ∀ n ≥ N_seq ε, ∀ M : ℕ, ∃ n' ≥ M, PropositionKey_conclusion n n' ε C_seq :=
  by
    simp [N_seq, hε, hε1]
    exact Classical.choose_spec ((Classical.choose_spec PropositionKey).2 ε hε hε1)

/-
n_seq is the sequence of natural numbers constructed to satisfy the properties.
-/
noncomputable def next_val (n : ℕ) (k : ℕ) : ℕ :=
  let ε := epsilon_seq k
  let M := max ((k + 1) * n) (N_seq (epsilon_seq (k + 1)))
  if h : n ≥ N_seq ε ∧ 0 < ε ∧ ε < 1 then
    Classical.choose (N_seq_spec ε h.2.1 h.2.2 n h.1 M)
  else
    M + 1

noncomputable def n_seq : ℕ → ℕ
| 0 => 1
| 1 => N_seq (epsilon_seq 1) + 1
| (k + 2) => next_val (n_seq (k + 1)) (k + 1)

/-
The terms of n_seq are positive.
-/
lemma n_seq_pos (k : ℕ) : n_seq k > 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with ( _ | _ | k )
    all_goals
      norm_num [ n_seq ]
    unfold next_val
    simp +zetaDelta at *
    split_ifs
    all_goals
      norm_num [ ih ]
    have := Classical.choose_spec ( N_seq_spec ( epsilon_seq ( k + 1 ) ) ( by linarith ) ( by linarith ) ( n_seq ( k + 1 ) ) ( by linarith ) ( max ( ( k + 1 + 1 ) * n_seq ( k + 1 ) ) ( N_seq ( epsilon_seq ( k + 1 + 1 ) ) ) ) )
    grind

/-
n_seq grows at least factorially (or rather, n_{k+1} >= (k+1) n_k).
-/
lemma n_seq_growth (k : ℕ) : n_seq (k + 1) ≥ (k + 1) * n_seq k := by
  -- By definition of $next\_val$, we know that $n\_seq (k + 1) \geq (k + 1) * n\_seq k$.
  have h_next : ∀ n k, n > 0 → next_val n k ≥ (k + 1) * n := by
    unfold next_val
    norm_num +zetaDelta at *
    intro n k hn
    split_ifs
    · have := Classical.choose_spec ( N_seq_spec ( epsilon_seq k ) ( by tauto ) ( by tauto ) n ( by tauto ) ( max ( ( k + 1 ) * n ) ( N_seq ( epsilon_seq ( k + 1 ) ) ) ) )
      aesop
    · exact Nat.le_succ_of_le ( Nat.le_max_left _ _ )
  induction k with
  | zero =>
    exact Nat.le_add_left _ _
  | succ k ih =>
    exact h_next _ _ ( n_seq_pos _ )

/-
n_seq k is large enough to satisfy the threshold for epsilon_seq k.
-/
lemma n_seq_large (k : ℕ) (hk : k ≥ 1) : n_seq k ≥ N_seq (epsilon_seq k) := by
  rcases k with ( _ | _ | k )
  all_goals
    simp_all +decide [ epsilon_seq ]
  · unfold n_seq
    norm_num
    unfold epsilon_seq
    norm_num
  · rw [ show n_seq ( k + 2 ) = next_val ( n_seq ( k + 1 ) ) ( k + 1 ) from rfl ]
    unfold next_val
    unfold epsilon_seq
    norm_num
    split_ifs
    all_goals
      norm_num at *
    · have := Classical.choose_spec ( N_seq_spec ( ( k + 1 + 1 : ℝ ) ⁻¹ ) ( by positivity ) ( by rw [ inv_eq_one_div, div_lt_iff₀ ] <;> linarith ) ( n_seq ( k + 1 ) ) ( by linarith ) ( Max.max ( ( k + 1 + 1 ) * n_seq ( k + 1 ) ) ( N_seq ( ( k + 1 + 1 + 1 : ℝ ) ⁻¹ ) ) ) ) ; aesop
    · exact Nat.le_succ_of_le ( Nat.le_max_right _ _ )

/-
n_seq (k+1) satisfies the Key Proposition conclusion with respect to n_seq k and epsilon_seq k.
-/
lemma n_seq_prop_key (k : ℕ) (hk : k ≥ 1) :
  PropositionKey_conclusion (n_seq k) (n_seq (k + 1)) (epsilon_seq k) C_seq := by
    by_cases h : n_seq (k + 1) = next_val (n_seq k) k
    · rw [h]
      unfold next_val
      simp +zetaDelta at *
      split_ifs
      · exact Classical.choose_spec ( N_seq_spec ( epsilon_seq k ) ( by linarith ) ( by linarith ) ( n_seq k ) ( by linarith ) ( max ( ( k + 1 ) * n_seq k ) ( N_seq ( epsilon_seq ( k + 1 ) ) ) ) ) |> fun h => by aesop
      · exact False.elim <| ‹¬ ( N_seq ( epsilon_seq k ) ≤ n_seq k ∧ 0 < epsilon_seq k ∧ epsilon_seq k < 1 ) › ⟨ n_seq_large k hk, epsilon_seq_valid k hk |>.1, epsilon_seq_valid k hk |>.2 ⟩
    · rcases k with ( _ | _ | k )
      all_goals
        tauto

/-
There exists a sequence n_k and a constant C satisfying the SequenceProperties.
-/
lemma exists_sequence :
  ∃ n : ℕ → ℕ, ∃ C : ℝ, SequenceProperties n C := by
    use n_seq, C_seq
    constructor
    · intro k hk
      have := n_seq_growth k
      have := n_seq_growth ( k + 1 )
      norm_num at *
      nlinarith [ n_seq_pos k, n_seq_pos ( k + 1 ) ]
    · refine ⟨ ?_, ?_, ?_ ⟩
      · intro k hk a ha ha'
        have := n_seq_prop_key k hk
        unfold PropositionKey_conclusion at this
        aesop
      · intro k hk R hR₁ hR₂
        have := n_seq_prop_key k hk
        refine le_trans ?_ ( this.2 R hR₁ hR₂ )
        unfold epsilon_seq
        gcongr
        norm_num
        exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( by linarith ) ) ( by exact le_of_lt ( C_seq_pos ) )
      · exact fun k a => n_seq_growth k

/-
The constructed set A is a subset of the squarefree numbers.
-/
lemma constructed_A_subset_SF (n : ℕ → ℕ) : constructed_A n ⊆ SF := by
  intro x hx
  rw [constructed_A] at hx
  simp at hx
  obtain ⟨k, hk⟩ := hx
  exact hk.2.1

/-
n_lower is the sequence, C_lower is the constant, and A_lower is the set constructed from them.
-/
noncomputable def n_lower : ℕ → ℕ := Classical.choose exists_sequence

noncomputable def C_lower : ℝ := Classical.choose (Classical.choose_spec exists_sequence)

lemma n_lower_properties : SequenceProperties n_lower C_lower :=
  Classical.choose_spec (Classical.choose_spec exists_sequence)

noncomputable def A_lower : Set ℕ := constructed_A n_lower

/-
The set A_lower has property Q.
-/
lemma A_lower_property_Q : PropertyQ A_lower := by
  -- By definition of $A_lower$, we know that for any $a \in A_lower$ with $a < n$ (where $n = n_lower (k+1)$), $n + a$ is squarefree.
  have h_A_lower_Q : ∀ k ≥ 1, ∀ a ∈ A_lower, a < n_lower (k + 1) → n_lower (k + 1) + a ∈ SF := by
    intro k hk a ha hlt
    obtain ⟨j, hj⟩ : ∃ j < k + 1, a ∈ Set.Ioc (n_lower j) (n_lower (j + 1)) ∧ a ∈ SF ∧ n_lower (j + 1) + a ∈ SF := by
      obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp ha
      refine ⟨ j, ?_, hj ⟩
      contrapose! hlt
      -- Since $n_lower$ is strictly increasing, we have $n_lower (k + 1) \leq n_lower j$ for $j \geq k + 1$.
      have h_inc : ∀ j k, j ≥ k + 1 → n_lower (k + 1) ≤ n_lower j := by
        intros j k hjk
        induction j, hjk using Nat.le_induction with
        | base =>
          norm_num +zetaDelta at *
        | succ j hj ih =>
          have := n_lower_properties.1 j ( by linarith [ Nat.succ_le_iff.mp hj ] )
          linarith!
      exact le_trans ( h_inc _ _ hlt ) hj.1.1.le
    by_cases hjk : j = k
    · aesop
    · -- Since $j < k$, we have $a \leq n_lower (j + 1) \leq n_lower k$.
      have h_le : a ≤ n_lower k := by
        have h_le : ∀ m ≥ j + 1, n_lower m ≥ n_lower (j + 1) := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base =>
            norm_num +zetaDelta at *
          | succ m hm ih =>
            exact le_trans ‹_› ( n_lower_properties.1 _ ( by linarith [ Nat.succ_le_iff.mp hm ] ) |> le_of_lt )
        exact le_trans hj.2.1.2 ( h_le k ( Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.le_of_lt_succ hj.1 ) hjk ) ) )
      have := n_lower_properties.2.1 k hk
      exact this a ( Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero ( by aesop ), h_le ⟩ ) hj.2.2.1
  -- Since $n_lower$ is strictly increasing, there are infinitely many $n_lower (k + 1)$.
  have h_inf : Set.Infinite {n | ∃ k ≥ 1, n = n_lower (k + 1)} := by
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    use n_lower (a + 2)
    refine ⟨ ⟨ a + 1, by linarith, rfl ⟩, ?_ ⟩
    have h_seq_growth : ∀ k ≥ 1, n_lower (k + 1) ≥ (k + 1) * n_lower k := by
      exact fun k hk => n_lower_properties.2.2.2 k hk
    induction a with
    | zero =>
      nlinarith! [ h_seq_growth 1 le_rfl, n_lower_properties.1 1 le_rfl ]
    | succ a ih =>
      nlinarith [ h_seq_growth ( a + 2 ) ( by linarith ), n_seq_pos ( a + 2 ) ]
  refine h_inf.mono ?_
  aesop

/-
Inequality for the cardinality of A_lower intersection [1, R].
-/
lemma A_lower_card_ineq (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) ≥
  ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n_lower (k + 1) + a ∈ SF)).card -
  ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card -
  n_lower (k - 1) := by
    rw [ Set.ncard_eq_toFinset_card _ ]
    norm_num [ Set.setOf_and ]
    ring_nf
    -- Let's simplify the goal using the definitions of $A_lower$ and $SF$.
    have h_simp : Finset.filter (fun a => a ∈ SF ∧ n_lower (1 + k) + a ∈ SF) (Finset.Icc 1 R) ⊆ Finset.filter (fun a => a ∈ A_lower) (Finset.Icc 1 R) ∪ Finset.filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF) (Finset.Icc 1 (n_lower k)) ∪ Finset.Icc 1 (n_lower (k - 1)) := by
      intro a ha
      by_cases ha1 : a ≤ n_lower k <;> by_cases ha2 : a ≤ n_lower (k - 1) <;> simp_all +decide [ add_comm 1 k ]
      · by_contra h_contra
        rcases k with ( _ | _ | k )
        all_goals
          simp_all +decide
        exact h_contra.1 <| Set.mem_iUnion.2 ⟨ k + 1, by aesop ⟩
      · left
        exact Set.mem_iUnion.mpr ⟨ k, ⟨ ⟨ by linarith, by linarith ⟩, ha.2.1, ha.2.2 ⟩ ⟩
    exact_mod_cast le_trans ( Finset.card_le_card h_simp ) ( by exact le_trans ( Finset.card_union_le _ _ ) ( by exact le_trans ( add_le_add_left ( Finset.card_union_le _ _ ) _ ) ( by norm_num; linarith ) ) )

/-
Bound on the number of squarefree integers a <= n_k such that n_k + a is not squarefree.
-/
lemma bad_set_bound (k : ℕ) (hk : k ≥ 2) :
  ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card ≤
  C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) := by
    have := Classical.choose_spec SF_count_bound
    have := n_lower_properties.2.2.1 ( k - 1 ) ( Nat.le_sub_one_of_lt hk )
    rcases k with ( _ | _ | k )
    all_goals
      norm_num at *
    have := this ( n_lower ( k + 1 + 1 ) ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] ) ; rw [ div_add', le_div_iff₀ ] at this <;> norm_num at *
    · have := ‹0 < Classical.choose SF_count_bound ∧ ∀ n : ℕ, 0 < n → |↑{x ∈ Finset.Icc 1 n | x ∈ SF}.card - 6 / Real.pi ^ 2 * ↑n| ≤ Classical.choose SF_count_bound * ↑n.sqrt›.2 ( n_lower ( k + 1 + 1 ) ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] )
      rw [ abs_le ] at this
      norm_num at *
      rw [
        show ( Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∉ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ) = Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) \ Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) by
          ext
          aesop
      ]
      rw [ Finset.card_sdiff ]
      rw [ Nat.cast_sub ]
      · rw [
          show ( Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ∩ Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ) = Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) by
            ext
            aesop
        ]
        norm_num
        nlinarith [ Real.sqrt_nonneg ( n_lower ( k + 1 + 1 ) : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( n_lower ( k + 1 + 1 ) ) ), show ( Nat.sqrt ( n_lower ( k + 1 + 1 ) ) : ℝ ) ≤ Real.sqrt ( n_lower ( k + 1 + 1 ) ) from Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ ) ]
      · exact Finset.card_mono <| Finset.inter_subset_right
    · exact Nat.pos_of_ne_zero ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] )
    · exact ne_of_gt ( Nat.pos_of_ne_zero ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ), n_lower_properties.2.2.2 ( k + 1 ) ( by linarith ) ] ) )

/-
Explicit lower bound for the density of A_lower in the interval [1, R].
-/
lemma A_lower_density_lower_bound_explicit (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥
  6 / Real.pi^2 - C_lower / k -
  (C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) + n_lower (k - 1)) / R := by
    have := n_lower_properties.2.2.1 k ( by linarith ) R hR1 hR2
    refine le_trans ( sub_le_sub_right this ((C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) + n_lower (k - 1)) / R) ) ?_
    have h_card_ineq : ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) ≥
      ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n_lower (k + 1) + a ∈ SF)).card -
      ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card -
      n_lower (k - 1) := by
        convert A_lower_card_ineq k hk R hR1 hR2 using 1
    have h_card_bound : ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card ≤
      C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) := by
        convert bad_set_bound k hk using 1
    rw [ ← sub_div ]
    gcongr
    linarith

/-
The sequence n_lower tends to infinity.
-/
lemma n_lower_tendsto_atTop : Filter.Tendsto n_lower Filter.atTop Filter.atTop := by
  -- By definition of $n_lower$, we know that it satisfies the properties of $SequenceProperties$.
  obtain ⟨C, hC⟩ := n_lower_properties
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro b
  use b + 1
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    norm_num at *
    exact Nat.recOn b ( by linarith! [ C 1 le_rfl, hC.2.2 1 le_rfl ] ) fun k ih => by linarith! [ C ( k + 1 ) ( by linarith ), hC.2.2 ( k + 1 ) ( by linarith ) ]
  | succ k hk ih =>
    norm_num at *
    linarith [ C k ( by linarith ), hC.2.2 k ( by linarith ) ]

/-
The ratio n_{k-1}/n_k tends to 0.
-/
lemma term4_tendsto_zero :
  Filter.Tendsto (fun k => (n_lower (k - 1) : ℝ) / n_lower k) Filter.atTop (nhds 0) := by
    -- By definition of $n_lower$, we know that $n_lower (k - 1) / n_lower k \leq 1 / k$ for all $k \geq 2$.
    have h_bound : ∀ k ≥ 2, (n_lower (k - 1) : ℝ) / n_lower k ≤ 1 / k := by
      intro k hk
      have h_bound : n_lower k ≥ k * n_lower (k - 1) := by
        rcases k with ( _ | _ | k )
        all_goals
          simp_all +decide
        exact n_lower_properties.2.2.2 _ ( by linarith ) |> le_trans ( by nlinarith )
      have h_ratio : (n_lower (k - 1) : ℝ) / n_lower k ≤ 1 / k := by
        field_simp
        exact div_le_one_of_le₀ ( mod_cast by linarith ) ( Nat.cast_nonneg _ )
      exact h_ratio
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun k hk => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound k hk ⟩ ) ( tendsto_one_div_atTop_nhds_zero_nat )

/-
The error terms in the density lower bound tend to 0 as k goes to infinity.
-/
lemma error_terms_tendsto_zero :
  Filter.Tendsto (fun (k : ℕ) => C_lower / (k : ℝ) + C_lower / ((k : ℝ) - 1) + (Classical.choose SF_count_bound) / Real.sqrt (n_lower k) + (n_lower (k - 1) : ℝ) / n_lower k) Filter.atTop (nhds 0) := by
    -- We'll use the fact that if the denominator grows faster than the numerator, the limit will tend to 0.
    have h_sqrt : Filter.Tendsto (fun k => Real.sqrt (n_lower k)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_atTop.mpr fun x => by
        rcases Filter.eventually_atTop.mp ( n_lower_tendsto_atTop.eventually_ge_atTop ( Nat.ceil ( x ^ 2 ) ) ) with ⟨ k, hk ⟩
        exact ⟨ k, fun n hn => Real.le_sqrt_of_sq_le <| by simpa using Nat.le_of_ceil_le <| hk n hn ⟩
    simpa [sub_eq_add_neg] using Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.div_atTop h_sqrt ) ) term4_tendsto_zero

/-
The error term tends to 0.
-/
noncomputable def error_term (k : ℕ) : ℝ :=
  C_lower / (k : ℝ) + C_lower / ((k : ℝ) - 1) + (Classical.choose SF_count_bound) / Real.sqrt (n_lower k) + (n_lower (k - 1) : ℝ) / n_lower k

lemma error_term_tendsto_zero : Filter.Tendsto error_term Filter.atTop (nhds 0) := by
  change Filter.Tendsto
    (fun k : ℕ => C_lower / (k : ℝ) + C_lower / ((k : ℝ) - 1) +
      (Classical.choose SF_count_bound) / Real.sqrt (n_lower k) +
      (n_lower (k - 1) : ℝ) / n_lower k) Filter.atTop (nhds 0)
  exact error_terms_tendsto_zero

/-
The lower density of a set A of natural numbers.
-/
def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
If the upper density is at most d and the lower density is at least d, then the set has natural density d.
-/
lemma natural_density_of_densities (A : Set ℕ) (d : ℝ)
    (h_upper : upperDensity A ≤ d)
    (h_lower : lowerDensity A ≥ d) :
    HasNaturalDensity A d := by
      refine tendsto_order.2 ⟨ ?_, ?_ ⟩
      · intro a' ha'
        contrapose! ha'
        simp_all +decide [ upperDensity, lowerDensity ]
        refine le_trans h_lower ?_
        refine csSup_le ?_ ?_ <;> norm_num
        · exact ⟨ 0, ⟨ 1, fun n hn => by positivity ⟩ ⟩
        · exact fun b x hx => by
            rw [Filter.frequently_atTop] at ha'
            obtain ⟨ y, hy₁, hy₂ ⟩ := ha' x
            linarith [ hx y hy₁ ]
      · unfold upperDensity lowerDensity at *
        rw [ Filter.limsup_eq ] at h_upper
        contrapose! h_upper
        refine lt_of_lt_of_le h_upper.choose_spec.1 ( le_csInf ?_ ?_ )
        · refine ⟨ 1, ?_ ⟩
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity
        · intro b hb
          exact le_of_not_gt fun h => h_upper.choose_spec.2 <| hb.mono fun n hn => by linarith [ h_upper.choose_spec.1 ]

/-
If the density in intervals [n_k, n_{k+1}] is bounded below by C - epsilon_k, and epsilon_k tends to 0, then the lower density is at least C.
-/
lemma lower_density_of_interval_bound (A : Set ℕ) (n : ℕ → ℕ) (C : ℝ) (ε : ℕ → ℝ)
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (h_bound : ∀ k, ∀ R, n k ≤ R → R ≤ n (k + 1) →
      ((A ∩ Set.Icc 1 R).ncard : ℝ) / R ≥ C - ε k)
    (h_lim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    lowerDensity A ≥ C := by
      -- By definition of lower density, we need to show that for any $d < C$, there exists an $N$ such that for all $n \geq N$, the density of $A$ up to $n$ is at least $d$.
      apply le_of_forall_lt_imp_le_of_dense
      intro d hd
      obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, ε k < C - d := by
        simpa using h_lim.eventually ( gt_mem_nhds <| by linarith )
      refine le_csSup ?_ ?_ <;> norm_num [ lowerDensity ]
      · exact ⟨ 1, by rintro x ⟨ k, hk ⟩ ; exact le_trans ( hk ( k + 1 ) ( by linarith ) ) ( div_le_one_of_le₀ ( mod_cast Nat.le_trans ( Set.ncard_le_ncard ( Set.inter_subset_right ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity ) ) ⟩
      · -- Choose $a = n_N$.
        use n N + 1
        intro b hb
        obtain ⟨k, hk⟩ : ∃ k ≥ N, n k ≤ b ∧ b ≤ n (k + 1) := by
          have h_exists_k : ∃ k ≥ N, n k ≤ b ∧ b < n (k + 1) := by
            have h_unbounded : ∀ M, ∃ k ≥ N, n k > M := by
              exact fun M => by
                rcases Filter.eventually_atTop.mp ( hn.eventually_gt_atTop M ) with ⟨ k, hk ⟩
                exact ⟨ _, le_max_left _ _, hk _ ( le_max_right _ _ ) ⟩
            contrapose! h_unbounded
            exact ⟨ b, fun x hx => Nat.le_induction ( by linarith ) h_unbounded x hx ⟩
          exact ⟨ h_exists_k.choose, h_exists_k.choose_spec.1, h_exists_k.choose_spec.2.1, h_exists_k.choose_spec.2.2.le ⟩
        linarith [ h_bound k b hk.2.1 hk.2.2, hN k hk.1 ]

/-
n_lower k is positive for k >= 2.
-/
lemma n_lower_pos_ge_2 (k : ℕ) (hk : k ≥ 2) : n_lower k > 0 := by
  induction k with
  | zero =>
    contradiction
  | succ k ih =>
    have := n_lower_properties.2.2.2 k
    rcases k with ( _ | _ | k )
    all_goals
      simp_all +decide
    · have := n_lower_properties.1 1
      norm_num at this
      linarith
    · grind

/-
If a sequence n_k grows fast enough and the density of SF in [1, R] is lower bounded by 6/pi^2 - C/k, then C >= 0.
-/
lemma density_contradiction_abstract (n : ℕ → ℕ) (C : ℝ)
  (h_growth : ∀ k ≥ 1, n (k+1) ≥ (k+1) * n k)
  (h_pos : ∀ k ≥ 1, n k > 0)
  (h_dens : ∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k+1) →
    ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k) :
  C ≥ 0 := by
    by_contra h_neg
    -- From `SF_count_bound`, we have $|\SF \cap [1, R]|/R \le 6/\pi^2 + C_{SF}/\sqrt{R}$.
    have h_bound : ∀ R : ℕ, R > 0 → ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≤ 6 / Real.pi^2 + (Classical.choose SF_count_bound) / Real.sqrt R := by
      intro R hR_pos
      have h_bound : ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card ≤ 6 / Real.pi^2 * R + (Classical.choose SF_count_bound) * Real.sqrt R := by
        have := Classical.choose_spec SF_count_bound
        exact le_trans ( show ( Finset.card ( Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 R ) ) : ℝ ) ≤ 6 / Real.pi ^ 2 * R + Classical.choose SF_count_bound * Nat.sqrt R by linarith [ abs_le.mp ( this.2 R ( Nat.cast_pos.mpr hR_pos ) ) ] ) ( add_le_add_right ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( by exact_mod_cast Nat.sqrt_le' _ ) ) ( by linarith ) ) _ )
      rw [ div_le_iff₀ ] <;> first | positivity | (convert h_bound using 1 <;> first | rfl | ring_nf; norm_num [ hR_pos.ne', Real.sqrt_div_self ])
      rw [ mul_assoc, ← Real.sqrt_div_self, div_mul_cancel₀ _ ( by positivity ) ]
    -- From `h_growth`, $n_{k+1}$ grows super-polynomially.
    have h_super_poly : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt (n (k + 1))) Filter.atTop (nhds 0) := by
      -- Since $n_{k+1} \geq (k+1)!$, we have $\sqrt{n_{k+1}} \geq \sqrt{(k+1)!}$.
      have h_sqrt_bound : ∀ k ≥ 1, Real.sqrt (n (k + 1)) ≥ Real.sqrt ((k + 1)!) := by
        intros k hk
        have h_factorial : n (k + 1) ≥ (k + 1)! := by
          induction hk
          all_goals
            simp_all +decide [ Nat.factorial_succ ]
          · nlinarith [ h_growth 1 le_rfl, h_pos 1 le_rfl ]
          · nlinarith [ h_growth ( ‹_› + 1 ) ( by linarith ) ]
        exact Real.sqrt_le_sqrt (Nat.cast_le.mpr h_factorial)
      -- Since $\sqrt{(k+1)!}$ grows faster than $k$, we have $\frac{k}{\sqrt{(k+1)!}} \to 0$ as $k \to \infty$.
      have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt ((k + 1)!)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\sqrt{(k+1)!}$ grows faster than $k$.
        have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt (k !)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\sqrt{k!}$ grows faster than $k$.
          have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ 2 / (k !)) Filter.atTop (nhds 0) := by
            refine squeeze_zero_norm' ?_ (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from tendsto_inv_atTop_nhds_zero_nat)
            norm_num +zetaDelta at *
            exact ⟨ 8, fun k hk => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> first | positivity | induction hk <;> norm_num [ Nat.factorial_succ ] at * ; nlinarith ⟩
          have := h_sqrt_factorial.sqrt
          simpa [ Real.sqrt_div ( sq_nonneg _ ), Real.sqrt_sq ( Nat.cast_nonneg _ ) ] using this
        exact squeeze_zero ( fun k => by positivity ) ( fun k => by gcongr ; linarith ) h_sqrt_factorial
      refine squeeze_zero_norm' ?_ h_sqrt_factorial
      filter_upwards [ Filter.eventually_ge_atTop 1 ] with k hk using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( h_sqrt_bound k hk )
    -- From `h_dens`, we have $6/\pi^2 + D/k \le 6/\pi^2 + C_{SF}/\sqrt{n_{k+1}}$.
    have h_ineq : ∀ k : ℕ, k ≥ 1 → 6 / Real.pi^2 + (-C) / (k : ℝ) ≤ 6 / Real.pi^2 + (Classical.choose SF_count_bound) / Real.sqrt (n (k + 1)) := by
      intro k hk
      specialize h_dens k hk ( n ( k + 1 ) ) ( by nlinarith [ h_growth k hk, h_pos k hk ] ) le_rfl
      specialize h_bound ( n ( k + 1 ) ) ( by nlinarith [ h_growth k hk, h_pos k hk ] )
      ring_nf at *
      linarith
    -- From `h_ineq`, we have $-C/k \le C_{SF}/\sqrt{n_{k+1}}$.
    have h_ineq_simplified : ∀ k : ℕ, k ≥ 1 → -C ≤ (Classical.choose SF_count_bound) * (k : ℝ) / Real.sqrt (n (k + 1)) := by
      intro k hk
      specialize h_ineq k hk
      ring_nf at h_ineq ⊢
      nlinarith [ inv_pos.mpr ( by positivity : 0 < ( k : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ) ]
    exact absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds ( by simpa [ mul_div_assoc ] using h_super_poly.const_mul ( Classical.choose SF_count_bound ) ) ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => h_ineq_simplified k hk ⟩ ) ) ( by norm_num; linarith )

/-
C_lower is non-negative.
-/
lemma C_lower_nonneg : C_lower ≥ 0 := by
  by_contra h_neg_C_lower
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, ∃ C : ℝ, SequenceProperties n C ∧ C < 0 := by
    exact ⟨ n_lower, C_lower, n_lower_properties, lt_of_not_ge h_neg_C_lower ⟩
  obtain ⟨ C, hC₁, hC₂ ⟩ := hn
  have h_density : ∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k + 1) → ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k := by
    intros k hk R hR1 hR2
    have h_density : ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n (k + 1) + a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k := by
      exact hC₁.2.2.1 k hk R hR1 hR2
    refine le_trans h_density ?_
    gcongr
    simp +decide only [Finset.mem_Icc] at *
    tauto
  have := density_contradiction_abstract n C ( fun k hk => hC₁.2.2.2 k hk ) ( fun k hk => ?_ ) h_density
  · linarith
  · rcases k with ( _ | _ | k )
    all_goals
      simp_all +decide [ SequenceProperties ]
    · have := h_density 1 le_rfl ( n 1 ) le_rfl ( by linarith [ hC₁.1 1 le_rfl ] )
      norm_num at this
      exact Nat.pos_of_ne_zero fun h => by
        norm_num [ h ] at this
        nlinarith [ Real.pi_gt_three, mul_div_cancel₀ ( 6 : ℝ ) ( pow_ne_zero 2 Real.pi_ne_zero ) ]
    · linarith [ hC₁.1 ( k + 1 ) ( by linarith ), hC₁.1 ( k + 2 ) ( by linarith ) ]

/-
For R in [n_k, n_{k+1}], the density of A_lower in [1, R] is at least 6/pi^2 - error_term k.
-/
lemma A_lower_density_bound_k (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - error_term k := by
    -- By Lemma `A_lower_density_lower_bound_explicit`, we have the inequality:
    have h_density : ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - C_lower / (k : ℝ) - (C_lower / ((k : ℝ) - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) + n_lower (k - 1)) / (n_lower k : ℝ) := by
      have := A_lower_density_lower_bound_explicit k hk R hR1 hR2
      refine le_trans ?_ this
      gcongr
      · exact add_nonneg ( add_nonneg ( mul_nonneg ( div_nonneg ( by linarith [ show 0 ≤ C_lower by exact le_of_not_gt fun h => by have := C_lower_nonneg; linarith ] ) ( by linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( Classical.choose_spec SF_count_bound |>.1.le ) ( Real.sqrt_nonneg _ ) ) ) ( Nat.cast_nonneg _ )
      · exact Nat.cast_pos.mpr ( n_lower_pos_ge_2 k hk )
    convert h_density using 1
    unfold error_term
    ring_nf
    norm_num [ ne_of_gt ( show 0 < n_lower k from n_lower_pos_ge_2 k hk ) ]
    rw [ mul_assoc, ← Real.sqrt_div_self ]
    ring

/-
The lower density of A_lower is at least 6/pi^2.
-/
lemma A_lower_lowerDensity : lowerDensity A_lower ≥ 6 / Real.pi^2 := by
  -- Apply the lower_density_of_interval_bound lemma with the sequence n'_k = n_{k+2} and error term ε'_k = error_term (k+2).
  apply lower_density_of_interval_bound A_lower (fun k => n_lower (k + 2)) (6 / Real.pi^2) (fun k => error_term (k + 2)) (by
  exact n_lower_tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 2 )) (by
  intros k R hk₁ hk₂
  convert A_lower_density_bound_k ( k + 2 ) ( by linarith ) R hk₁ hk₂ using 1
  norm_num [ Set.ncard_eq_toFinset_card' ]) (by
  exact error_term_tendsto_zero.comp ( Filter.tendsto_add_atTop_nat 2 ))

/-
Every sequence with property Q has upper density at most 6/pi^2.
-/
theorem TheoremQ_upper (A : Set ℕ) (h : PropertyQ A) : upperDensity A ≤ 6 / Real.pi^2 := by
  -- Apply the lemma that states if A is admissible, then its upper density is at most 6/π².
  apply Admissible_implies_upperDensity_le_6_div_pi_sq A (PropertyQ_implies_Admissible A h)

/-
There exists a subset of SF with property Q and natural density 6/pi^2.
-/
theorem TheoremQ_lower : ∃ A : Set ℕ, A ⊆ SF ∧ PropertyQ A ∧ HasNaturalDensity A (6 / Real.pi^2) := by
  use A_lower
  refine ⟨constructed_A_subset_SF n_lower, A_lower_property_Q, ?_⟩
  apply natural_density_of_densities
  · exact TheoremQ_upper A_lower A_lower_property_Q
  · exact A_lower_lowerDensity

#print axioms TheoremQ_upper
-- 'Erdos1102b.TheoremQ_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms TheoremQ_lower
-- 'Erdos1102b.TheoremQ_lower' depends on axioms: [propext, Classical.choice, Quot.sound]

/-
Definition of HasPropertyQ as written down by the Formal Conjectures project of Google DeepMind.
-/
def HasPropertyQ (A : Set ℕ) : Prop :=
  {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}.Infinite

/-
Statements from the Formal Conjectures project of Google DeepMind concerning Property Q.
-/
theorem erdos_1102.upper_density_Q
    (A : ℕ → ℕ) (h_inc : StrictMono A)
    (hQ : HasPropertyQ (range A)) :
    limsup (fun j : ℕ  ↦ (j / A j : ℝ)) atTop ≤ 6 / Real.pi^2 := by
  have h_upper_density : Filter.limsup (fun j => ((Set.range A ∩ Set.Icc 1 j).ncard : ℝ) / j) Filter.atTop ≤ 6 / Real.pi^2 := by
    simpa [upperDensity] using TheoremQ_upper ( Set.range A ) hQ
  -- Since $A$ is strictly monotone, the number of elements in $\text{range}(A)$ up to $j$ is at most $j$.
  have h_card_le_j : ∀ j, ((Set.range A ∩ Set.Icc 1 j).ncard : ℝ) ≤ j := by
    intro j
    exact_mod_cast le_trans ( Set.ncard_le_ncard ( show Set.range A ∩ Set.Icc 1 j ⊆ Set.Icc 1 j from fun x hx => hx.2 ) ) ( by simp [ Set.ncard_eq_toFinset_card' ] )
  -- Since $A$ is strictly monotone, the number of elements in $\text{range}(A)$ up to $j$ is at least $j / A_j$.
  have h_card_ge_j_div_Aj : ∀ j, ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ j := by
    intros j
    have h_card_ge_j_div_Aj : ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ Finset.card (Finset.image A (Finset.Icc 1 j)) := by
      rw [ ← Set.ncard_coe_finset ]
      gcongr
      · exact Set.finite_iff_bddAbove.mpr ⟨ A j, fun x hx => hx.2.2 ⟩
      · exact fun x hx => by
          obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
          exact ⟨ Set.mem_range_self _, ⟨ Nat.one_le_iff_ne_zero.mpr <| by linarith [ h_inc <| show 0 < y from Finset.mem_Icc.mp hy |>.1 ], h_inc.monotone <| Finset.mem_Icc.mp hy |>.2 ⟩ ⟩
    rw [ Finset.card_image_of_injective _ h_inc.injective ] at h_card_ge_j_div_Aj
    aesop
  refine le_trans ?_ h_upper_density
  refine le_csInf ?_ ?_ <;> norm_num +zetaDelta at *
  · exact ⟨ 1, ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast h_card_le_j n ) ( Nat.cast_nonneg _ ) ⟩ ⟩
  · intro b x hx
    refine csInf_le ?_ ?_ <;> norm_num +zetaDelta at *
    · exact ⟨ 0, by rintro a ⟨ k, hk ⟩ ; exact le_trans ( by positivity ) ( hk _ le_rfl ) ⟩
    · use x + 1
      -- By combining the results from hx and h_card_ge_j_div_Aj, we can conclude the proof.
      intros b_1 hb_1
      have h_ratio : (b_1 : ℝ) / (A b_1 : ℝ) ≤ (Set.range A ∩ Set.Icc 1 (A b_1)).ncard / (A b_1 : ℝ) := by
        gcongr
        aesop
      grind

theorem erdos_1102.lower_density_Q_exists :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    (∀ j, Squarefree (A j)) ∧
    HasPropertyQ (range A) ∧
    Tendsto (fun j : ℕ  ↦ (j / A j : ℝ)) atTop (𝓝 (6 / Real.pi^2)) := by
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, A ⊆ SF ∧ PropertyQ A ∧ HasNaturalDensity A (6 / Real.pi^2) := by
    -- Apply the theorem that states there exists a subset of SF with property Q and natural density 6/pi^2.
    apply TheoremQ_lower
  -- Let's choose any enumeration of the set A.
  obtain ⟨A_enum, hA_enum⟩ : ∃ A_enum : ℕ → ℕ, StrictMono A_enum ∧ Set.range A_enum = A := by
    have h_enum : A.Infinite := by
      -- Since $A$ has property $Q$, it must be infinite. Otherwise, the set $\{n \mid \forall a \in A, a < n \rightarrow \text{Squarefree}(n + a)\}$ would be finite, contradicting property $Q$.
      by_contra h_finite
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, n ∉ A := by
        exact Set.finite_iff_bddAbove.mp ( Classical.not_not.mp h_finite ) |> fun ⟨ N, hN ⟩ => ⟨ N + 1, fun n hn h => not_lt_of_ge ( hN h ) hn ⟩
      have h_contra : Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds 0) := by
        have h_contra : ∀ n ≥ N, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ (A ∩ Set.Icc 1 N).ncard := by
          intros n hn
          exact_mod_cast Set.ncard_le_ncard ( show A ∩ Set.Icc 1 n ⊆ A ∩ Set.Icc 1 N from fun x hx => ⟨ hx.1, ⟨ hx.2.1, by linarith [ hx.2.2, show x ≤ N from le_of_not_gt fun hx' => hN x ( by linarith [ hx.2.1, hx.2.2 ] ) hx.1 ] ⟩ ⟩ )
        exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ N, fun n hn => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_contra n hn ) ( Nat.cast_nonneg _ ) ⟩ ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop )
      exact absurd ( tendsto_nhds_unique h_contra hA.2.2 ) ( by positivity )
    use fun n => Nat.nth A n
    exact ⟨ Nat.nth_strictMono h_enum, Set.ext fun x => ⟨ fun hx => by obtain ⟨ n, rfl ⟩ := hx; exact Nat.nth_mem_of_infinite h_enum _, fun hx => ⟨ Nat.count A x, Nat.nth_count hx ⟩ ⟩ ⟩
  have h_density : Filter.Tendsto (fun j : ℕ => ((Set.range A_enum ∩ Set.Icc 1 (A_enum j)).ncard : ℝ) / (A_enum j : ℝ)) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    have h_density : Filter.Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
      exact hA.2.2
    convert h_density.comp ( show Filter.Tendsto ( fun j => A_enum j ) Filter.atTop Filter.atTop from ?_ ) using 2
    · aesop
    · exact hA_enum.1.tendsto_atTop
  have h_card : ∀ j, ((Set.range A_enum ∩ Set.Icc 1 (A_enum j)).ncard : ℝ) = j + 1 := by
    intro j
    rw [ show ( Set.range A_enum ∩ Set.Icc 1 ( A_enum j ) ) = Set.image A_enum ( Finset.Icc 0 j ) from ?_ ]
    · rw [ Set.ncard_image_of_injective _ hA_enum.1.injective ]
      simp +decide [ Set.ncard_eq_toFinset_card' ]
    · -- To prove equality of sets, we show each set is a subset of the other.
      apply Set.ext
      intro x
      simp [Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro ⟨ ⟨ y, rfl ⟩, hy₁, hy₂ ⟩
        exact ⟨ y, hA_enum.1.le_iff_le.mp hy₂, rfl ⟩
      · rintro ⟨ k, hk₁, rfl ⟩
        exact ⟨ ⟨ k, rfl ⟩, Nat.pos_of_ne_zero fun h => by have := hA.1 ( hA_enum.2.subset <| Set.mem_range_self k ) ; simp_all +decide [ SF ], hA_enum.1.monotone hk₁ ⟩
  have h_card : Filter.Tendsto (fun j : ℕ => ((j + 1 : ℝ) / (A_enum j : ℝ))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    simpa only [ h_card ] using h_density
  have h_card : Filter.Tendsto (fun j : ℕ => ((j : ℝ) / (A_enum j : ℝ))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    convert h_card.sub ( show Filter.Tendsto ( fun j : ℕ => ( 1 : ℝ ) / ( A_enum j : ℝ ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp hA_enum.1.tendsto_atTop ) using 2 <;> ring
  use A_enum
  aesop

#print axioms erdos_1102.upper_density_Q
-- 'Erdos1102b.erdos_1102.upper_density_Q' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms erdos_1102.lower_density_Q_exists
-- 'Erdos1102b.erdos_1102.lower_density_Q_exists' depends on axioms: [propext,
-- Classical.choice, Quot.sound]

end
end Erdos1102b

/- ---------------------------------------------------------------------------- -/
/- Concatenated from ErdosProblem1102PropertyOverP.lean -/
namespace Erdos1102c


/-
We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

Any sequence with property $\overline{P}$ or $\overline{P}_infty$ has density strictly smaller than $6/\pi^2$. On the other hand, for every $\epsilon > 0$ there exists a sequence with property $\overline{P}$ (which therefore has property $\overline{P}_infty$ as well) with lower density larger than $6/\pi^2 - \epsilon$.

-/


open Squarefree Set Order Filter Topology


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable



noncomputable section

/-
SF is the set of squarefree numbers.
-/
def SF : Set ℕ := {n | Squarefree n}

/-
A set A has property P_bar if for infinitely many n, n+a is squarefree for all a in A.
-/
def PropertyP_bar (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, Squarefree (n + a)}).Infinite

/-
A set A has property P_bar_infty if for infinitely many n, n+a is squarefree for all but finitely many a in A.
-/
def PropertyP_bar_infty (A : Set ℕ) : Prop := ({n | ({a ∈ A | ¬Squarefree (n + a)}).Finite}).Infinite

/-
A set A is admissible if for every prime p, there is a residue class mod p^2 that A avoids.
-/
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b

/-
A set A is almost admissible if for every prime p, there is a residue class mod p^2 that contains only finitely many elements of A.
-/
def AlmostAdmissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ({a ∈ A | a % p^2 = b}).Finite

/-
Every set with property P_bar has property P_bar_infty.
-/
theorem P_bar_implies_P_bar_infty (A : Set ℕ) (h : PropertyP_bar A) : PropertyP_bar_infty A := by
  -- By definition of PropertyP_bar, there are infinitely many n such that for all a in A, n+a is squarefree.
  have h_inf : {n | ∀ a ∈ A, Squarefree (n + a)}.Infinite := by
    exact h
  exact h_inf.mono fun n hn => Set.Finite.subset ( Set.finite_singleton 0 ) fun x hx => by aesop

/-
Every admissible set is almost admissible.
-/
theorem Admissible_implies_AlmostAdmissible (A : Set ℕ) (h : Admissible A) : AlmostAdmissible A := by
  -- By definition of admissible, for every prime $p$, there exists a residue class $b \pmod{p^2}$ such that no element of $A$ is congruent to $b \pmod{p^2}$.
  intro p hp
  obtain ⟨b, hb₁, hb₂⟩ := h p hp
  use b
  simp [hb₁]
  exact Set.finite_empty.subset fun x hx => hb₂ x hx.1 hx.2

/-
Every set with property P_bar_infty is almost admissible.
-/
theorem PropertyP_bar_infty_implies_AlmostAdmissible (A : Set ℕ) (h : PropertyP_bar_infty A) : AlmostAdmissible A := by
  intro p hp
  -- Fix a prime $p$.
  by_cases h_finite : ∀ b < p ^ 2, Set.Infinite {a ∈ A | a % p ^ 2 = b}
  · -- If for every $b < p^2$, the set $\{a \in A \mid a \equiv b \pmod{p^2}\}$ is infinite, then for any $n$, the set $\{a \in A \mid n + a \text{ is not squarefree}\}$ is infinite.
    have h_inf_not_squarefree : ∀ n, Set.Infinite {a ∈ A | ¬Squarefree (n + a)} := by
      intro n
      have h_inf_not_squarefree : Set.Infinite {a ∈ A | (n + a) % p ^ 2 = 0} := by
        have h_inf_not_squarefree : Set.Infinite {a ∈ A | a % p ^ 2 = (p ^ 2 - n % p ^ 2) % p ^ 2} := by
          exact h_finite _ ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) )
        refine h_inf_not_squarefree.mono ?_
        simp +contextual [ Nat.add_mod ]
        exact fun a ha ha' => by simp +decide [ Nat.add_sub_of_le ( Nat.mod_lt n ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ]
      refine h_inf_not_squarefree.mono ?_
      intro a ha
      obtain ⟨ ha₁, ha₂ ⟩ := ha
      rw [ ← Nat.dvd_iff_mod_eq_zero ] at ha₂
      obtain ⟨ k, hk ⟩ := ha₂
      simp_all +decide [ Nat.squarefree_mul_iff ]
      simp_all +decide [ sq, Nat.squarefree_mul_iff ]
      aesop
    contrapose! h_inf_not_squarefree
    exact Exists.elim ( h.nonempty ) fun n hn => ⟨ n, by simpa using hn ⟩
  · aesop

/-
Property P_bar_infty is unaffected by finite modifications of the set.
-/
theorem PropertyP_bar_infty_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : PropertyP_bar_infty A ↔ PropertyP_bar_infty B := by
  constructor
  all_goals
    intro h'
  all_goals
    unfold PropertyP_bar_infty at *
  · refine Set.Infinite.mono ?_ h'
    intro n hn
    have h_finite : {a ∈ B | ¬Squarefree (n + a)} ⊆ ({a ∈ A | ¬Squarefree (n + a)} ∪ (B \ A)) := by
      exact fun x hx => if hx' : x ∈ A then Or.inl ⟨ hx', hx.2 ⟩ else Or.inr ⟨ hx.1, hx' ⟩
    exact Set.Finite.subset ( hn.union h.2 ) h_finite
  · refine h'.sdiff ( h.1.union h.2 |> Set.Finite.image fun x => x ) |> fun h'' => h''.mono ?_
    intro n hn
    simp_all +decide
    refine Set.Finite.subset ( hn.1.union ( h.1.union h.2 ) ) ?_
    intro a ha
    by_cases ha' : a ∈ B <;> aesop

/-
AlmostAdmissible is unaffected by finite modifications of the set.
-/
theorem AlmostAdmissible_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : AlmostAdmissible A ↔ AlmostAdmissible B := by
  constructor
  · intro hA p hp
    obtain ⟨b, hb₁, hb₂⟩ := hA p hp
    use b
    exact ⟨ hb₁, Set.Finite.subset ( hb₂.union ( h.1.union h.2 ) ) fun x hx => by by_cases hx' : x ∈ A <;> aesop ⟩
  · -- For any prime $p$, choose $b$ such that $B \mod p^2 \neq b$. Since $A \mod p^2$ can differ from $B \mod p^2$ by at most a finite number of elements, we can adjust $b$ to avoid elements of $A$ that are congruent to $b$ modulo $p^2$.
    intro hB p hp
    obtain ⟨b, hb⟩ := hB p hp
    have h_finite_diff : ({a ∈ A | a % p^2 = b}).Finite := by
      exact Set.Finite.subset ( h.1.union hb.2 |> Set.Finite.union <| h.2 ) fun x hx => by by_cases hx' : x ∈ B <;> aesop
    exact ⟨ b, hb.1, h_finite_diff ⟩

/-
Property P_bar is downwardly monotone.
-/
lemma PropertyP_bar_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyP_bar B) : PropertyP_bar A := by
  exact Set.Infinite.mono ( fun n hn => by rintro a ha; exact hn a ( h ha ) ) hB

/-
Property P_bar_infty is downwardly monotone.
-/
lemma PropertyP_bar_infty_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyP_bar_infty B) : PropertyP_bar_infty A := by
  refine Set.Infinite.mono ?_ ( hB )
  exact fun n hn => Set.Finite.subset ( hn ) fun x hx => ⟨ h hx.1, hx.2 ⟩

/-
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
A set A has natural density d if the proportion of elements in A up to n tends to d as n goes to infinity.
-/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds d)

/-
The sum of mu(d) for d such that d^2 divides n is 1 if n is squarefree and 0 otherwise.
-/
lemma sum_moebius_sq_dvd_eq_indicator (n : ℕ) (hn : n > 0) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), ArithmeticFunction.moebius d = if Squarefree n then 1 else 0 := by
      -- Let $k$ be the product of the primes dividing $n$.
      set k := ∏ p ∈ Nat.primeFactors n, p ^ (Nat.factorization n p / 2) with hk_def
      -- If $n$ is not squarefree, then $k > 1$.
      by_cases h_squarefree : Squarefree n
      · -- If $n$ is squarefree, then the only divisor $d$ such that $d^2 \mid n$ is $d = 1$.
        have h_divisors : ∀ d ∈ Finset.Icc 1 n, d^2 ∣ n → d = 1 := by
          exact fun d hd hdn => by
            have := h_squarefree.squarefree_of_dvd hdn
            rw [ sq, Nat.squarefree_mul_iff ] at this
            aesop
        rw [ Finset.sum_eq_single 1 ]
        all_goals
          norm_num [ h_squarefree ]
        · exact fun b hb₁ hb₂ hb₃ hb₄ => False.elim <| hb₄ <| h_divisors b ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ ) hb₃
        · linarith
      · -- If $n$ is not squarefree, then $k > 1$ and the sum becomes $\sum_{d \mid k} \mu(d)$.
        have h_sum_divisors : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d)) = (∑ d ∈ Nat.divisors k, (ArithmeticFunction.moebius d)) := by
          have h_sum_divisors : Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n) = Nat.divisors k := by
            ext d
            constructor
            all_goals
              intro hd
            all_goals
              simp_all +decide
            · -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $2 \cdot \text{exponent}(p \text  {  in } d) \leq \text{exponent}(p \text{ in } n)$.
              have h_exp : ∀ p ∈ Nat.primeFactors d, 2 * (Nat.factorization d p) ≤ Nat.factorization n p := by
                intro p hp
                have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hd.2
                aesop
              -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $d.factorization p \leq (Nat.factorization n p) / 2$.
              have h_exp_le : ∀ p ∈ Nat.primeFactors d, d.factorization p ≤ (Nat.factorization n p) / 2 := by
                exact fun p hp => by
                  rw [ Nat.le_div_iff_mul_le zero_lt_two ]
                  linarith [ h_exp p hp ]
              refine ⟨ ?_, Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero (n.factorization p / 2) <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ⟩
              conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : d ≠ 0 ) ]
              rw [ ← Finset.prod_sdiff <| show d.primeFactors ⊆ n.primeFactors from Nat.primeFactors_mono ( dvd_of_mul_left_dvd hd.2 ) <| by aesop ]
              exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p ( h_exp_le p hp ) ) _
            · refine ⟨ ⟨ Nat.pos_of_dvd_of_pos hd.1 ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) (n.factorization p / 2) ), Nat.le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) (n.factorization p / 2) ) hd.1 ) ?_ ⟩, ?_ ⟩
              · conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self hn.ne' ]
                exact Finset.prod_le_prod' fun p hp => pow_le_pow_right₀ ( Nat.pos_of_mem_primeFactors hp ) ( Nat.div_le_self _ _ )
              · refine dvd_trans ( pow_dvd_pow_of_dvd hd.1 2 ) ?_
                conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self hn.ne' ]
                rw [ ← Finset.prod_pow ]
                exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => by
                  rw [ ← pow_mul ]
                  exact pow_dvd_pow _ ( Nat.div_mul_le_self _ _ )
          congr
        -- Since $k > 1$, we can apply the property of the Möbius function that $\sum_{d \mid k} \mu(d ( )  = 0$.
        have h_moebius_sum : ∀ {m : ℕ}, 1 < m → (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = 0 := by
          intros m hm_gt_one
          have h_moebius_sum : (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
            exact Eq.symm ArithmeticFunction.coe_mul_zeta_apply
          simp_all +decide [ ArithmeticFunction.moebius_mul_coe_zeta ]
          exact if_neg hm_gt_one.ne'
        rw [ if_neg h_squarefree, h_sum_divisors, h_moebius_sum ]
        contrapose! h_squarefree
        -- If $k \leq 1$, then for all primes $p$ dividing $n$, we have $p^{Nat.factorization n p / 2} \leq 1$, which implies $Nat.factorization n p / 2 = 0$, hence $Nat.factorization n p < 2$.
        have h_factorization : ∀ p ∈ Nat.primeFactors n, Nat.factorization n p < 2 := by
          exact fun p hp => Nat.lt_succ_of_le ( Nat.le_of_not_lt fun h => h_squarefree.not_gt <| lt_of_lt_of_le ( by exact one_lt_pow₀ ( Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) <| Nat.ne_of_gt <| Nat.div_pos ( by linarith ) zero_lt_two ) <| Nat.le_of_dvd ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos <| Nat.prime_of_mem_primeFactors hq ) _ ) <| Finset.dvd_prod_of_mem _ hp )
        rw [ Nat.squarefree_iff_prime_squarefree ]
        intro p pp dp
        specialize h_factorization p
        simp_all +decide [← sq]
        exact absurd ( h_factorization ( dvd_of_mul_left_dvd dp ) hn.ne' ) ( by have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 dp; aesop )

/-
The number of squarefree integers up to N is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
-/
lemma sum_squarefree_indicator_eq_sum_moebius_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (N / d ^ 2 : ℤ) := by
      -- We'll use the fact that if the condition holds for all $n \leq N$, then the sums are equal.
      have h_sum_eq : ∀ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0) := by
        intro n hn
        have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 (Nat.sqrt N)), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
          have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
            convert sum_moebius_sq_dvd_eq_indicator n ( Finset.mem_Icc.mp hn |>.1 ) using 1
          rw [ ← h_sum, Finset.sum_subset ]
          · simp +contextual [ Finset.subset_iff ]
            exact fun x hx₁ hx₂ hx₃ => Nat.le_of_dvd ( Finset.mem_Icc.mp hn |>.1 ) ( dvd_of_mul_left_dvd hx₃ )
          · simp +zetaDelta at *
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( Nat.le_sqrt.mpr <| by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃
        simp_all +decide [ Finset.sum_ite ]
      -- By interchanging the order of summation, we can rewrite the right-hand side of the equation.
      have h_interchange : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0))) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (∑ n ∈ Finset.Icc 1 N, (if d^2 ∣ n then 1 else 0))) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ]
      convert h_interchange using 1
      · exact Finset.sum_congr rfl h_sum_eq
      · refine Finset.sum_congr rfl fun x hx => ?_
        simp +zetaDelta at *
        rw [
          show Finset.filter ( fun y => x ^ 2 ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x ^ 2 * y ) ( Finset.Icc 1 ( N / x ^ 2 ) ) from ?_,
          Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( pow_ne_zero 2 ( by linarith : x ≠ 0 ) ) h
        ]
        focus
          norm_num
        -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro y
        simp
        exact ⟨ fun h => ⟨ y / x ^ 2, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( pow_pos ( by linarith ) 2 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ pow_pos ( by linarith : 0 < x ) 2 ], by nlinarith [ Nat.div_mul_le_self N ( x ^ 2 ) ] ⟩, by norm_num ⟩ ⟩

/-
The number of squarefree integers up to N is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
-/
lemma sum_squarefree_indicator_eq_sum_moebius_floor_v2 (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (N / d ^ 2 : ℤ) := by
      convert sum_squarefree_indicator_eq_sum_moebius_floor N using 1

/-
The partial sums of mu(d)/d^2 converge to 6/pi^2.
-/
lemma sum_moebius_div_sq_tendsto : Filter.Tendsto (fun k => ∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ) / d ^ 2) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  -- We know that $\sum_{d=1}^{\infty} \frac{\mu(d)}{d^2} = \frac{1}{\zeta(2)}$.
  have h_sum : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ) = 1 / (Real.pi ^ 2 / 6) := by
    -- By definition of $L(2, \mu)$, we know that $L(2, \mu) = \sum_{d=1}^{\infty} \frac{\mu(d)}{d^2}$.
    have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (riemannZeta 2)⁻¹ := by
      have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) := by
        norm_num [ LSeries ]
        convert Complex.ofReal_tsum _
        norm_num [ LSeries.term ]
        aesop
      have h_L2_mu : (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) * (riemannZeta 2) = 1 := by
        convert ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius _ using 1
        focus
          rw [ mul_comm ]
        focus
          rw [ ArithmeticFunction.LSeries_zeta_eq_riemannZeta ]
        · norm_num
        · norm_num
      exact eq_inv_of_mul_eq_one_left <| by aesop
    -- We know that $\zeta(2) = \frac{\pi^2}{6}$.
    have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := by
      exact riemannZeta_two
    simp_all +decide [ Complex.ext_iff, sq ]
    norm_cast
  convert h_sum ▸ Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 2 <;> norm_num [ Finset.sum_Ico_eq_sub ]
  · erw [ Finset.sum_Ico_eq_sub _ _ ]
    all_goals
      norm_num
  · exact ( by contrapose! h_sum; erw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity )

/-
The set of squarefree numbers has natural density 6/pi^2.
-/
theorem SF_density : HasNaturalDensity SF (6 / Real.pi ^ 2) := by
  -- We need to show that $\frac{1}{N} |SF \cap [1, N]| \to \frac{6}{\pi^2}$.
  suffices h_limit : Filter.Tendsto (fun N => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ)) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) by
    -- By definition of `SF`, we know that `|SF ∩ [1, N]|` is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
    have h_card : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℝ)) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ) - ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ)) := by
      intro N
      have h_card_eq : (∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℝ)) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ) - ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ)) := by
        have h_sum_eq : ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℤ) * (N / d ^ 2 : ℤ) := by
          convert sum_squarefree_indicator_eq_sum_moebius_floor_v2 N using 1
        -- Apply the equality of the integer and real sums to rewrite the left-hand side.
        have h_rewrite : (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℤ)) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ)) - (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ))) := by
          rw [ ← Finset.sum_sub_distrib ]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [ Int.fract ]
          ring_nf
          field_simp
          rw [ show ⌊ ( N : ℝ ) / x ^ 2⌋ = ((N / x ^ 2 : ℕ) : ℤ) from Int.floor_eq_iff.mpr ⟨ by rw [ le_div_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N ( x ^ 2 ) ], by rw [ div_lt_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_add_mod N ( x ^ 2 ), Nat.mod_lt N ( by nlinarith [ Finset.mem_Icc.mp hx ] : 0 < x ^ 2 ) ] ⟩ ]
          norm_cast
        convert h_rewrite using 1
        exact_mod_cast h_sum_eq
      convert h_card_eq using 1
    -- The second term is bounded by $\frac{1}{N} \sum_{d=1}^{\sqrt{N}} 1 = \frac{\lfloor \sqrt{N} \rfloor}{N} \le \frac{1}{\sqrt{N}}$, which tends to 0.
    have h_second_term : Filter.Tendsto (fun N => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)) / N) Filter.atTop (nhds 0) := by
      -- The absolute value of the second term is bounded by $\frac{1}{N} \sum_{d=1}^{\sqrt{N}} 1 = \frac{\lfloor \sqrt{N} \rfloor}{N} \le \frac{1}{\sqrt{N}}$, which tends to 0.
      have h_second_term_abs : ∀ N : ℕ, |(∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)) / N| ≤ (Nat.sqrt N : ℝ) / N := by
        intros N
        have h_abs : |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)| ≤ Nat.sqrt N := by
          refine le_trans
            ( Finset.abs_sum_le_sum_abs
              (fun d => (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ))
              (Finset.Icc 1 (Nat.sqrt N)) ) ?_
          refine le_trans
            (b := ∑ i ∈ Finset.Icc 1 (Nat.sqrt N), (1 : ℝ))
            ( Finset.sum_le_sum fun i hi => ?_ ) ?_
          · norm_num [ abs_mul, ArithmeticFunction.moebius ]
            split_ifs
            all_goals
              norm_num [ abs_mul, abs_of_nonneg, Int.fract_nonneg, Int.fract_lt_one ]
            exact Int.fract_lt_one _ |> le_of_lt
          · norm_num
        rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ N ) ]
        gcongr
      refine squeeze_zero_norm h_second_term_abs ?_
      refine squeeze_zero_norm' (a := fun n : ℕ => 1 / Real.sqrt (n : ℝ)) ?_ ?_
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, show ( n :ℝ ) ≥ 1 by exact_mod_cast hn, show ( Nat.sqrt n :ℝ ) ^ 2 ≤ n by exact_mod_cast Nat.sqrt_le' n ]
      · simpa using tendsto_inv_atTop_nhds_zero_nat.sqrt
    refine Filter.Tendsto.congr' ?_ ( by simpa using h_limit.sub h_second_term )
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN
    simp_all +decide [div_eq_mul_inv, mul_comm, Set.ncard_eq_toFinset_card']
    rw [
      show ( Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 N ) ) = Finset.filter ( fun x => Squarefree x ) ( Finset.Icc 1 N ) by
        ext
        aesop
    ]
    rw [ h_card ]
    ring_nf
  -- We'll use the fact that $\sum_{d=1}^{\sqrt{N}} \frac{\mu(d)}{d^2} \left\lfloor \frac{N}{d^2} \right\rfloor$ is approximately $\frac{6}{\pi^2} N$.
  have h_sum_approx : Filter.Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) / d ^ 2)) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    simpa [Function.comp_def] using
      sum_moebius_div_sq_tendsto.comp
        (Filter.tendsto_atTop_atTop.mpr fun b =>
          ⟨b ^ 2, fun a ha => by nlinarith [Nat.lt_succ_sqrt a]⟩)
  refine h_sum_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by simp +decide [div_eq_mul_inv,
    mul_assoc, mul_comm, Finset.mul_sum _ _ _, hN.ne'] )

/-
The number of integers in an interval of length L that are congruent to a modulo m is L/m + O(1).
-/
lemma card_filter_modEq_Icc (u L a m : ℕ) (hm : m > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S := I.filter (fun x => x ≡ a [MOD m])
  abs ((S.card : ℝ) - (L : ℝ) / m) ≤ 2 := by
    refine abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩
    · refine le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_le_card <| show Finset.filter ( fun x => x ≡ a [MOD m] ) ( Finset.Icc u ( u + L - 1 ) ) ⊆ Finset.image ( fun k => m * k + a % m ) ( Finset.Icc ( u / m ) ( ( u + L - 1 ) / m ) ) from ?_ ) ((L : ℝ) / m) ) ?_
      · intro x hx
        simp_all +decide [ Nat.ModEq ]
        exact ⟨ x / m, ⟨ Nat.div_le_div_right hx.1.1, Nat.div_le_div_right hx.1.2 ⟩, by linarith [ Nat.mod_add_div x m ] ⟩
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by nlinarith [ Nat.mod_lt a hm ] ] ; norm_num
        rcases L with ( _ | L )
        all_goals
          norm_num [ Nat.succ_div ]
        · calc (u - 1) / m ≤ u / m := Nat.div_le_div_right (Nat.sub_le u 1)
              _ < 2 + u / m := by omega
        · field_simp
          exact mod_cast by nlinarith [ Nat.div_mul_le_self ( u + L ) m, Nat.div_add_mod ( u + L ) m, Nat.mod_lt ( u + L ) hm, Nat.div_mul_le_self u m, Nat.div_add_mod u m, Nat.mod_lt u hm, Nat.sub_add_cancel ( show u / m ≤ ( u + L ) / m + 1 from Nat.le_succ_of_le ( Nat.div_le_div_right ( by linarith ) ) ) ]
    · -- The set of integers in [u, u+L-1] that are congruent to a modulo m forms an arithmetic progression with common difference m.
      have h_arith_prog : Finset.filter (fun x => x ≡ a [MOD m]) (Finset.Icc u (u + L - 1)) ⊇ Finset.image (fun k => u + ((a + m - u % m) % m) + k * m) (Finset.range (L / m)) := by
        intro x hxaesop
        norm_num +zetaDelta at *
        rcases hxaesop with ⟨ k, hk₁, rfl ⟩
        exact ⟨ ⟨ by nlinarith [ Nat.zero_le ( ( a + m - u % m ) % m ) ], Nat.le_sub_one_of_lt ( by nlinarith [ Nat.div_mul_le_self L m, Nat.zero_le ( ( a + m - u % m ) % m ), Nat.mod_lt ( a + m - u % m ) hm ] ) ⟩, by simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ( show u % m ≤ a + m from by linarith [ Nat.mod_lt u hm ] ) ] ⟩
      have := Finset.card_mono h_arith_prog
      simp_all +decide [ Finset.card_image_of_injective, Function.Injective, hm.ne' ]
      rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_add_mod L m, Nat.mod_lt L hm ]

/-
The number of integers in an interval of length L satisfying two coprime modular constraints is L/(Wq) + O(1).
-/
lemma card_intersect_bound (u L W q b c : ℕ) (hWq : Nat.Coprime W q) (hW : W > 0) (hq : q > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q])
  abs ((S_intersect.card : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
    -- By the Chinese Remainder Theorem, there exists a unique solution modulo $Wq$ to the system of congruences $n \equiv b \pmod{W}$ and $n \equiv c \pmod{q}$.
    obtain ⟨a, ha⟩ : ∃ a, a ≡ b [MOD W] ∧ a ≡ c [MOD q] ∧ a < W * q := by
      have := Nat.chineseRemainder hWq b c
      exact ⟨ this.val % ( W * q ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.2, Nat.mod_lt _ ( Nat.mul_pos hW hq ) ⟩
    -- The set of integers in $I$ that are congruent to $a$ modulo $Wq$ is exactly the set of integers in $I$ that satisfy both congruences.
    have h_set_eq : {n ∈ Finset.Icc u (u + L - 1) | n ≡ b [MOD W] ∧ n ≡ c [MOD q]} = {n ∈ Finset.Icc u (u + L - 1) | n ≡ a [MOD (W * q)]} := by
      ext n
      simp_all +decide
      intro _ _
      rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ]
      focus
        simp_all +decide [ Nat.ModEq ]
      assumption
    convert card_filter_modEq_Icc u L a ( W * q ) ( mul_pos hW hq ) using 1
    aesop

/-
If A is a subset of a periodic set B with period M, then the upper density of A is at most the density of B in one period.
-/
lemma density_of_subset_periodic (A B : Set ℕ) (M : ℕ) (hM : M > 0) (hB_per : ∀ n, n ∈ B ↔ n + M ∈ B) (hsub : A ⊆ B) :
  upperDensity A ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) / M := by
    field_simp
    refine le_trans ( mul_le_mul_of_nonneg_right ( show upperDensity A ≤ upperDensity ( B ) from ?_ ) ( Nat.cast_nonneg M ) ) ?_
    · apply_rules [ Filter.limsup_le_limsup ]
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_div_of_nonneg_right ( mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ hsub ) <| Nat.cast_nonneg _
      · refine ⟨ 0, fun x hx => ?_ ⟩
        norm_num at *
        exact le_trans ( by positivity ) ( hx.choose_spec _ le_rfl ) |> le_trans <| by norm_num
      · use 1
        norm_num [ Filter.IsBoundedUnder ]
        exact ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩
    · -- Since B is periodic with period M, its natural density exists and is equal to the density in one period, which is |B ∩ [1, M]| / M.
      have hB_nat_density : HasNaturalDensity B ((B ∩ Set.Icc 1 M).ncard / M : ℝ) := by
        -- Since B is periodic with period M, the number of elements of B in [1, N] is approximately (N/M) times the number of elements of B in [1, M].
        have hB_card : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) + M := by
          intro N
          have hB_card : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ)) + M := by
            have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≤ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro k
              have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                intro k
                have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                  intro k
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)) ⊆ (fun n => n + k * M) '' (B ∩ Set.Icc 1 M) := by
                    intro n hn
                    use n - k * M
                    norm_num at *
                    constructor
                    · have hB_card_period : ∀ k : ℕ, ∀ n ∈ B, n ≥ k * M + 1 → n - k * M ∈ B := by
                        intro k n hn hn'
                        induction k generalizing n with
                        | zero =>
                          norm_num at *
                          assumption
                        | succ k ih =>
                          norm_num at *
                          convert ih ( n - M ) ( by rw [ hB_per ] ; exact by rw [ Nat.sub_add_cancel ( by nlinarith ) ] ; exact hn ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ n ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf
                      exact ⟨ hB_card_period k n hn.1 hn.2.1, Nat.sub_pos_of_lt hn.2.1, by linarith ⟩
                    · rw [ Nat.sub_add_cancel ( by linarith ) ]
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard ≤ ((fun n => n + k * M) '' (B ∩ Set.Icc 1 M)).ncard := by
                    apply_rules [ Set.ncard_le_ncard ]
                    exact Set.Finite.image _ ( Set.finite_iff_bddAbove.mpr ⟨ M, fun x hx => hx.2.2 ⟩ )
                  rw [ Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ] at hB_card_period ; exact_mod_cast hB_card_period
                exact hB_card_period k
              induction k with
              | zero =>
                norm_num [ Set.ncard_eq_toFinset_card' ]
              | succ k ih =>
                have hB_card_period : ((B ∩ Set.Icc 1 ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) + ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) := by
                  norm_cast
                  convert Set.ncard_union_le _ _ using 2
                  ext
                  norm_num
                  ring_nf
                  grind
                grind
            have hB_card_bound : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 ((N / M + 1) * M)).ncard : ℝ) := by
              fapply Nat.cast_le.mpr
              apply Set.ncard_le_ncard
              · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc_right ( by nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM ] ) )
              · exact Set.finite_iff_bddAbove.mpr ⟨ _, fun x hx => hx.2.2 ⟩
            refine le_trans hB_card_bound <| le_trans ( hB_card_period _ ) ?_
            field_simp
            norm_cast
            nlinarith [ Nat.div_mul_le_self N M, show ( B ∩ Set.Icc 1 M ).ncard ≤ M from le_trans ( Set.ncard_le_ncard ( show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from fun x hx => hx.2 ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ]
          convert hB_card using 1
        have hB_card_lower : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) - M := by
          intro N
          have hB_card_lower_step : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≥ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
            intro k
            have hB_card_lower_step : ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) = ∑ i ∈ Finset.range k, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) := by
              induction k with
              | zero =>
                norm_num [ Set.ncard_eq_toFinset_card' ]
              | succ k ih =>
                rw [ Finset.sum_range_succ, ← ih ]
                rw_mod_cast [ ← Set.ncard_union_eq ]
                · congr with x
                  norm_num
                  ring_nf
                  grind
                · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₁.2, Set.mem_Icc.mp hx₂.2 ]
            -- Since B is periodic with period M, the number of elements of B in [i*M+1, (i+1)*M] is the same as the number of elements of B in [1, M].
            have hB_card_lower_step_periodic : ∀ i : ℕ, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) = ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro i
              have hB_card_lower_step_periodic : (B ∩ Set.Icc (i * M + 1) ((i + 1) * M)) = (fun x => x + i * M) '' (B ∩ Set.Icc 1 M) := by
                ext x
                simp [Set.mem_image]
                constructor
                · intro hx
                  use x - i * M
                  simp
                  refine ⟨ ⟨ ?_, ?_, ?_ ⟩, Nat.sub_add_cancel ( by linarith ) ⟩
                  · induction i generalizing x with
                    | zero =>
                      norm_num at *
                      tauto
                    | succ i ih =>
                      norm_num at *
                      convert ih ( x - M ) ( by rw [ hB_per ] ; exact by convert hx.1 using 1; rw [ Nat.sub_add_cancel ( by nlinarith ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf
                  · exact Nat.sub_pos_of_lt hx.2.1
                  · linarith
                · rintro ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩
                  exact ⟨ by exact Nat.recOn i ( by simpa using hy₁ ) fun n ihn => by simpa [ Nat.succ_mul, ← add_assoc ] using hB_per _ |>.1 ihn, by nlinarith, by nlinarith ⟩
              rw [ hB_card_lower_step_periodic, Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ]
            simp_all +singlePass [ mul_comm ]
          have hB_card_lower_step : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ ((B ∩ Set.Icc 1 ((N / M) * M)).ncard : ℝ) := by
            gcongr
            · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2.2 ⟩
            · exact Nat.div_mul_le_self _ _
          refine le_trans ?_ hB_card_lower_step
          refine le_trans ?_ ( ‹∀ k : ℕ, ( B ∩ Set.Icc 1 ( k * M ) |> Set.ncard : ℝ ) ≥ k * ( B ∩ Set.Icc 1 M |> Set.ncard : ℝ ) › ( N / M ) )
          field_simp
          rw [ sub_le_iff_le_add ]
          norm_cast ; nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM, show ( B ∩ Set.Icc 1 M |> Set.ncard ) ≤ M from le_trans ( Set.ncard_le_ncard <| show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ]
        refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
        refine squeeze_zero_norm' (a := fun n : ℕ => ( M : ℝ ) / n + ( M : ℝ ) / n) ?_ ?_
        · norm_num +zetaDelta at *
          refine ⟨ M + 1, fun n hn => abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩ ⟩ <;> ring_nf at * <;> norm_num at *
          · field_simp
            rw [ div_add', div_le_div_iff_of_pos_right ] <;> try norm_num ; linarith
            have := hB_card n
            rw [ ← @Nat.cast_le ℝ ] at *
            push_cast at *
            nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 n ).ncard : ℝ ), inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 M ).ncard : ℝ ) ]
          · have := hB_card_lower n
            have := hB_card n
            nlinarith [ inv_pos.mpr ( by norm_cast; linarith : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( M : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) + M ≤ n ) ]
        · simpa [div_eq_mul_inv] using Filter.Tendsto.add ( tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) ) ( tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) )
      unfold upperDensity HasNaturalDensity at *
      rw [ hB_nat_density.limsup_eq ]
      norm_num [ hM.ne' ]

/-
The product of (1 - 1/p^2) over primes p < k tends to 6/pi^2 as k goes to infinity.
-/
lemma prod_primes_inv_sq_tendsto : Filter.Tendsto (fun k => ∏ p ∈ Finset.filter Nat.Prime (Finset.range k), (1 - 1/(p:ℝ)^2)) Filter.atTop (nhds (6 / Real.pi^2)) := by
  -- The product over primes of (1 - 1/p^2) is the inverse of the sum over integers of 1/n^2 (Euler product). Since sum 1/n^2 = pi^2/6, the product is 6/pi^2.
  have h_euler_product : ∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = 6 / Real.pi^2 := by
    have h_euler_product : (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) = (∑' n : ℕ, 1 / (n^2 : ℝ))⁻¹ := by
      -- Apply the Euler product formula to the Riemann zeta function.
      have h_euler_product : ∀ s : ℝ, 1 < s → (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^s)⁻¹ else 1) = (∑' n : ℕ, (1 / (n : ℝ)^s)) := by
        intro s hs
        have := @EulerProduct.eulerProduct_hasProd
        specialize @this ℝ _ ( fun n => ( n : ℝ ) ⁻¹ ^ s ) _ _ _ _ <;> norm_num at *
        · intro m n hmn
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), mul_comm ]
        · exact Summable.abs <| by simpa [ Real.inv_rpow ] using Real.summable_nat_rpow_inv.2 hs
        · convert HasProd.tprod_eq ( this ( by rw [ Real.zero_rpow ( by positivity ) ] ) ) using 1
          · convert ( tprod_subtype _ _ ) |> Eq.symm using 1
            any_goals exact { p : ℕ | Nat.Prime p }
            any_goals try infer_instance
            rotate_right
            focus
              use fun p => 1 / ( 1 - 1 / ( p : ℝ ) ^ s )
            · simp +decide [ Set.mulIndicator ]
            · refine tprod_congr fun p => ?_
              rw [ one_div, ← tsum_geometric_of_lt_one ( by positivity ) ]
              · norm_num [ Real.inv_rpow ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ]
                norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_comm ]
              · exact div_lt_self zero_lt_one ( Real.one_lt_rpow ( mod_cast p.2.one_lt ) ( by positivity ) )
          · norm_num [ Real.inv_rpow ]
      convert congr_arg ( fun x : ℝ => x⁻¹ ) ( h_euler_product 2 ( by norm_num ) ) using 1
      · have h_prod_inv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p)⁻¹ = ∏' p, (f p)⁻¹ := by
          intros f hf_pos hf_summable
          have h_prod_inv : (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
            exact Eq.symm (Real.rexp_tsum_eq_tprod hf_pos hf_summable)
          have h_prod_inv' : (∏' p, (f p)⁻¹) = Real.exp (∑' p, Real.log ((f p)⁻¹)) := by
            have h_prod_inv' : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
              exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
            exact h_prod_inv' ( fun p => inv_pos.mpr ( hf_pos p ) ) ( by simpa [ Real.log_inv ] using hf_summable.neg ) ▸ by simp +decide
          simp_all +decide [Real.log_inv]
          rw [ ← Real.exp_neg, tsum_neg ]
        rw [ h_prod_inv ]
        · exact tprod_congr fun p => by split_ifs <;> norm_num
        · intro p
          split_ifs
          all_goals
            norm_num
          exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt ‹_› ) two_ne_zero
        · have h_sum_log : Summable (fun p : ℕ => if Nat.Prime p then Real.log (1 - 1 / (p : ℝ)^2)⁻¹ else 0) := by
            have h_log_bound : ∀ p : ℕ, Nat.Prime p → Real.log (1 - 1 / (p : ℝ)^2)⁻¹ ≤ 2 / (p : ℝ)^2 := by
              intro p hp
              rw [ Real.log_inv ]
              ring_nf
              nlinarith only [ Real.log_inv ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show 0 < 1 - ( p : ℝ ) ⁻¹ ^ 2 by exact sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), inv_mul_cancel₀ ( show ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ) ≠ 0 by exact ne_of_gt ( sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), show ( p : ℝ ) ⁻¹ ^ 2 ≤ 1 / 4 by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( inv_anti₀ ( by norm_num ) ( Nat.cast_le.mpr hp.two_le ) ) 2 ) ( by norm_num ) ]
            refine Summable.of_nonneg_of_le ( fun p => ?_ ) ( fun p => ?_ ) ( Real.summable_nat_pow_inv.2 one_lt_two |> Summable.mul_left 2 )
            · split_ifs <;> first | positivity | exact Real.log_nonneg <| by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ‹_›, one_div_mul_cancel <| show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero ‹_› ]
            · aesop
          exact h_sum_log.congr fun p => by split_ifs <;> simp +decide [ * ]
      · norm_cast
    field_simp
    rw [ h_euler_product, inv_mul_eq_div, div_eq_iff ] <;> first | positivity | have := hasSum_zeta_two; have := this.tsum_eq; norm_num at * ; nlinarith [ Real.pi_gt_three ]
  generalize_proofs at *
  (
  rw [ ← h_euler_product ]
  have h_euler_product : Filter.Tendsto (fun k => ∏ p ∈ Finset.range k, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) Filter.atTop (nhds (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) := by
    have h_abs_conv : Summable (fun p : ℕ => |Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)|) := by
      have h_log_conv : Summable (fun p : ℕ => |Real.log (1 - 1 / (p : ℝ)^2)|) := by
        -- We'll use the fact that |log(1 - x)| ≤ 2x for x in [0, 1/2].
        have h_log_bound : ∀ p : ℕ, p ≥ 2 → |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
          intros p hp
          have h_log_bound : |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
            have h_log_bound_aux : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → |Real.log (1 - x)| ≤ 2 * x := by
              intros x hx
              rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ]
              nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]
            exact h_log_bound_aux _ ⟨ by positivity, by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith ⟩
          generalize_proofs at *
          (
          exact h_log_bound)
        generalize_proofs at *
        (
        rw [ ← summable_nat_add_iff 2 ]
        exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_log_bound _ ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two ))
      generalize_proofs at *
      (
      exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => by split_ifs <;> norm_num ) h_log_conv)
    have h_exp_conv : Filter.Tendsto (fun k => Real.exp (∑ p ∈ Finset.range k, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) Filter.atTop (nhds (Real.exp (∑' p : ℕ, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp <| h_abs_conv.of_abs.hasSum.tendsto_sum_nat
    generalize_proofs at *
    (
    convert h_exp_conv using 2
    · rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by assumption ) two_ne_zero ) ]
    · have h_exp_conv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → ∏' p, f p = Real.exp (∑' p, Real.log (f p)) := by
        exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
      generalize_proofs at *
      (
      exact h_exp_conv ( fun p => by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt ‹_› ) two_ne_zero ) <| h_abs_conv.of_abs;))
  generalize_proofs at *
  (
  convert h_euler_product using 2
  simp +decide [ Finset.prod_ite ]))

/-
If A has property P_bar_infty, there exist n1 < n2 such that n1+a and n2+a are squarefree for all but finitely many a in A.
-/
lemma P_bar_infty_implies_pair (A : Set ℕ) (h : PropertyP_bar_infty A) :
    ∃ n₁ n₂, n₁ < n₂ ∧ ({a ∈ A | ¬(Squarefree (n₁ + a) ∧ Squarefree (n₂ + a))}).Finite := by
      rcases h.exists_gt 0 with ⟨ n₁, hn₁ ⟩
      obtain ⟨ n₂, hn₂ ⟩ := h.exists_gt n₁
      exact ⟨ n₁, n₂, hn₂.2, Set.Finite.subset ( hn₁.1.union hn₂.1 ) fun x hx => by by_cases h : Squarefree ( n₁ + x ) <;> aesop ⟩

/-
The upper density of a set is invariant under finite modifications.
-/
lemma upperDensity_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : upperDensity A = upperDensity B := by
  -- Since the difference between the two sets is finite, the proportion of elements in A and B up to n is the same for large n.
  have h_prop : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (((A ∩ Set.Icc 1 n).ncard : ℝ) / n - ((B ∩ Set.Icc 1 n).ncard : ℝ) / n) < ε := by
    -- Since the difference between the two sets is finite, the number of elements in A and B up to n is the same for large n.
    have h_card_diff : ∃ C : ℕ, ∀ n : ℕ, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 n).ncard : ℝ) + C ∧ ((B ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((A ∩ Set.Icc 1 n).ncard : ℝ) + C := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℕ, ∀ n : ℕ, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 n).ncard : ℝ) + C₁ := by
        use h.1.toFinset.card
        intro n
        have h_card_diff : (A ∩ Set.Icc 1 n).ncard ≤ (B ∩ Set.Icc 1 n).ncard + ((A \ B) ∩ Set.Icc 1 n).ncard := by
          have h_card_diff : (A ∩ Set.Icc 1 n) ⊆ (B ∩ Set.Icc 1 n) ∪ ((A \ B) ∩ Set.Icc 1 n) := by
            intro x hx
            by_cases hxB : x ∈ B <;> aesop
          exact le_trans ( Set.ncard_le_ncard h_card_diff ) ( Set.ncard_union_le _ _ )
        refine mod_cast h_card_diff.trans ( add_le_add_right ?_ (B ∩ Set.Icc 1 n).ncard )
        rw [ ← Set.ncard_coe_finset ]
        exact Set.ncard_le_ncard fun x hx => by aesop
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℕ, ∀ n : ℕ, ((B ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((A ∩ Set.Icc 1 n).ncard : ℝ) + C₂ := by
        use h.2.toFinset.card + 1
        intro n
        norm_cast
        simp +decide [ Set.ncard_eq_toFinset_card' ]
        have h_diff_card : Finset.filter (fun a => a ∈ B) (Finset.Icc 1 n) ⊆ Finset.filter (fun a => a ∈ A) (Finset.Icc 1 n) ∪ h.2.toFinset := by
          intro x hx
          by_cases hx' : x ∈ A <;> aesop
        exact le_trans ( Finset.card_le_card h_diff_card ) ( Finset.card_union_le _ _ ) |> le_trans <| by linarith
      use max C₁ C₂
      intro n
      exact ⟨by
      exact le_trans ( hC₁ n ) ( add_le_add_right ( mod_cast le_max_left _ _ ) _ ), by
        exact le_trans ( hC₂ n ) ( add_le_add_right ( mod_cast le_max_right _ _ ) _ )⟩
    intro ε hε
    obtain ⟨ C, hC ⟩ := h_card_diff
    use ⌈ε⁻¹ * ( C + 1 ) ⌉₊ + 1; intro n hn; rw [ abs_lt ] ; constructor <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( C + 1 ) ), mul_inv_cancel₀ hε.ne', show ( n : ℝ ) ≥ ⌈ε⁻¹ * ( C + 1 ) ⌉₊ + 1 by exact_mod_cast hn, hC n, div_mul_cancel₀ ( ( A ∩ Set.Icc 1 n |> Set.ncard : ℝ ) : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), div_mul_cancel₀ ( ( B ∩ Set.Icc 1 n |> Set.ncard : ℝ ) : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ]
  refine le_antisymm ?_ ?_ <;> rw [ upperDensity ]
  · refine le_csInf ?_ ?_
    · refine ⟨ 1, ?_ ⟩
      norm_num
      exact ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard ( show B ∩ Set.Icc 1 n ⊆ Set.Icc 1 n from Set.inter_subset_right ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity ) ⟩
    · intro b hb
      refine le_of_forall_pos_le_add fun ε ε_pos => ?_
      refine csInf_le ?_ ?_
      · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩
      · obtain ⟨ N, hN ⟩ := h_prop ε ε_pos
        obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hb
        rw [Set.mem_setOf_eq, Filter.eventually_map, Filter.eventually_atTop]
        exact ⟨ Max.max N M, fun n hn => by
          have hdiff := abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) )
          have hB_le := hM n ( le_trans ( le_max_right _ _ ) hn )
          simp at hB_le
          linarith ⟩
  · refine le_csInf ?_ ?_ <;> norm_num
    · exact ⟨ 1, ⟨ 1, fun n hn => by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ show Set.ncard ( A ∩ Set.Icc 1 n ) ≤ n by exact le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by norm_num [ Set.ncard_eq_toFinset_card' ] ] ⟩ ⟩
    · intro b x hx
      refine le_of_forall_pos_le_add fun ε ε_pos => ?_
      refine csInf_le ?_ ?_ <;> norm_num
      · exact ⟨ 0, by rintro _ ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩
      · obtain ⟨ N, hN ⟩ := h_prop ε ε_pos
        exact ⟨ Max.max x N, fun n hn => by linarith [ abs_lt.mp ( hN n ( le_trans ( le_max_right _ _ ) hn ) ), hx n ( le_trans ( le_max_left _ _ ) hn ) ] ⟩

/-
The density of a set defined by modular constraints modulo squares of distinct primes is the product of the local densities.
-/
lemma density_of_coprime_mod_sieve (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ S, R p ⊆ Finset.range (p^2)) :
    let M := ∏ p ∈ S, p^2
    let B := {n : ℕ | ∀ p ∈ S, n % p^2 ∈ R p}
    M > 0 ∧
    (∀ n, n ∈ B ↔ n + M ∈ B) ∧
    ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = ∏ p ∈ S, ((R p).card : ℝ) / p^2 := by
      refine ⟨ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) 2, ?_, ?_ ⟩
      · simp +zetaDelta at *
        intro n
        congr! 2
        simp +decide [ Nat.add_mod, Finset.prod_eq_prod_sdiff_singleton_mul <| Finset.mem_coe.mpr ‹_› ]
      · -- By the Chinese Remainder Theorem, the number of solutions modulo M is the product of the number of choices for each p.
        have h_crt : Finset.card (Finset.filter (fun n => ∀ p ∈ S, (n % p^2) ∈ R p) (Finset.range (∏ p ∈ S, p^2))) = ∏ p ∈ S, (Finset.card (R p)) := by
          induction S using Finset.induction with
          | empty =>
            norm_num
          | insert p S hS ih =>
            have h_crt : ∀ (a b : ℕ), Nat.Coprime a b → ∀ (A : Finset ℕ), A ⊆ Finset.range a → ∀ (B : Finset ℕ), B ⊆ Finset.range b → Finset.card (Finset.filter (fun n => n % a ∈ A ∧ n % b ∈ B) (Finset.range (a * b))) = Finset.card A * Finset.card B := by
              intros a b hab A hA B hB
              have h_crt : Finset.card (Finset.filter (fun n => n % a ∈ A ∧ n % b ∈ B) (Finset.range (a * b))) = Finset.card (Finset.product A B) := by
                refine Finset.card_bij ( fun n hn => ( n % a, n % b ) ) ?_ ?_ ?_
                · aesop
                · simp +zetaDelta at *
                  intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ ha₇ ha₈
                  -- Since $a$ and $b$ are coprime, by the Chinese Remainder Theorem, $a₁ \equiv a₂ \pmod{ab}$.
                  have h_crt : a₁ ≡ a₂ [MOD a] ∧ a₁ ≡ a₂ [MOD b] → a₁ ≡ a₂ [MOD (a * b)] := by
                    rw [ Nat.modEq_and_modEq_iff_modEq_mul ]
                    · aesop
                    · assumption
                  exact Nat.mod_eq_of_lt ha₁ ▸ Nat.mod_eq_of_lt ha₄ ▸ h_crt ⟨ ha₇, ha₈ ⟩
                · simp +zetaDelta at *
                  intro x y hx hy
                  -- By the Chinese Remainder Theorem, there exists a unique $z$ modulo $ab$ such that $z \equiv x \pmod{a}$ and $z \equiv y \pmod{b}$.
                  obtain ⟨z, hz⟩ : ∃ z, z < a * b ∧ z ≡ x [MOD a] ∧ z ≡ y [MOD b] := by
                    have := Nat.chineseRemainder hab x y
                    exact ⟨ this.val % ( a * b ), Nat.mod_lt _ ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2 ⟩
                  use z
                  have := hA hx
                  have := hB hy
                  simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ]
              exact h_crt.trans ( Finset.card_product _ _ )
            simp_all +decide [Finset.prod_insert]
            convert h_crt ( p ^ 2 ) ( ∏ p ∈ S, p ^ 2 ) _ ( R p ) hR.1 ( Finset.filter ( fun n => ∀ p ∈ S, n % p ^ 2 ∈ R p ) ( Finset.range ( ∏ p ∈ S, p ^ 2 ) ) ) _ using 1
            · congr! 2
              rename_i x hx_mem
              simp +decide
              intro hx
              refine ⟨ fun h => ?_, fun h => ?_ ⟩
              · refine ⟨ Nat.mod_lt x ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hS.2 q hq ) ) 2 ), fun q hq => ?_ ⟩
                simpa [ Nat.mod_mod_of_dvd x ( Finset.dvd_prod_of_mem (fun q : ℕ => q ^ 2) hq ) ] using h q hq
              · intro q hq
                simpa [ Nat.mod_mod_of_dvd x ( Finset.dvd_prod_of_mem (fun q : ℕ => q ^ 2) hq ) ] using h.2 q hq
            · rw [ ih ]
            · exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ S› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 q hq ) ; aesop
            · exact Finset.filter_subset _ _
        -- The set of integers in [1, M] satisfying the modular constraints is exactly the set of solutions modulo M.
        have h_eq : {n | ∀ p ∈ S, (n % p^2) ∈ R p} ∩ (Set.Icc 1 (∏ p ∈ S, p^2)) = Finset.image (fun n => if n = 0 then ∏ p ∈ S, p^2 else n) (Finset.filter (fun n => ∀ p ∈ S, (n % p^2) ∈ R p) (Finset.range (∏ p ∈ S, p^2))) := by
          ext
          simp +zetaDelta at *
          constructor
          all_goals
            intro h
          · use if ‹_› = ∏ p ∈ S, p ^ 2 then 0 else ‹_›
            split_ifs
            all_goals
              simp_all +decide
            · exact ⟨ fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) 2, fun p hp => by simpa [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ] using h.1 p hp ⟩
            · exact lt_of_le_of_ne h.2.2 ‹_›
          · rcases h with ⟨ x, hx, rfl ⟩ ; split_ifs <;> simp_all +decide
            · exact ⟨ fun p hp => by rw [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ] ; exact hx.2 p hp, Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) 2 ⟩
            · exact ⟨ Nat.pos_of_ne_zero ‹_›, hx.1.le ⟩
        rw [ h_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn ]
        · aesop
        · intro x hx y hy
          aesop

/-
For any K > C, the upper density of A is bounded by the product of (1 - 1/p^2) for p <= C and (1 - 2/p^2) for C < p <= K.
-/
lemma sieve_finite_bound (A : Set ℕ) (C K : ℕ) (hK : K > C)
    (h1 : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b)
    (h2 : ∀ p, Nat.Prime p → p > C → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ A, a % p^2 ≠ b1) ∧ (∀ a ∈ A, a % p^2 ≠ b2)) :
    upperDensity A ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (C + 1) K), (1 - 2 / (p : ℝ)^2)) := by
      obtain ⟨B, hB⟩ : ∃ B : Set ℕ, A ⊆ B ∧ (∃ M > 0, (∀ n, n ∈ B ↔ n + M ∈ B) ∧ ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 K), if p ≤ C then (1 - 1/(p:ℝ)^2) else (1 - 2/(p:ℝ)^2))) := by
        -- Let $S$ be the set of primes in $[1, K]$.
        set S := Finset.filter Nat.Prime (Finset.Icc 1 K) with hS_def
        -- For each $p \in S$, let $R(p) = \{x \in [0, p^2-1] \mid \exists a \in A, a \equiv x \pmod{p^2}\}$.
        obtain ⟨R, hR⟩ : ∃ R : ℕ → Finset ℕ, (∀ p ∈ S, R p ⊆ Finset.range (p^2)) ∧ (∀ p ∈ S, (R p).card = if p ≤ C then p^2 - 1 else p^2 - 2) ∧ A ⊆ {n : ℕ | ∀ p ∈ S, n % p^2 ∈ R p} := by
          choose! b hb₁ hb₂ using h1
          choose! b1 b2 hb3 hb4 hb5 hb6 hb7 using h2
          refine ⟨ fun p => if p ≤ C then Finset.range ( p ^ 2 ) \ { b p } else Finset.range ( p ^ 2 ) \ { b1 p, b2 p }, ?_, ?_, ?_ ⟩ <;> simp_all +decide
          · intro p hp₁ hp₂ hp₃
            split_ifs
            all_goals
              simp +decide [ Finset.sdiff_subset ]
          · intro p hp₁ hp₂ hp₃
            split_ifs
            all_goals
              simp_all +decide [ Finset.card_sdiff, Finset.card_singleton ]
          · intro a ha p hp₁ hp₂ hp₃
            split_ifs
            all_goals
              simp_all +decide [ Finset.mem_sdiff, Finset.mem_singleton ]
            · exact Nat.mod_lt _ ( by positivity )
            · exact Nat.mod_lt _ ( by positivity )
        refine ⟨ { n | ∀ p ∈ S, n % p ^ 2 ∈ R p }, hR.2.2, ∏ p ∈ S, p ^ 2, ?_, ?_, ?_ ⟩
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
        · simp +decide [ Nat.add_mod ]
          intro n
          refine forall₂_congr fun p hp => ?_
          simp +decide [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ]
        · convert density_of_coprime_mod_sieve S ( fun p hp => Finset.mem_filter.mp hp |>.2 ) R ( fun p hp => hR.1 p hp ) |> And.right |> And.right using 1
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [ hR.2.1 p hp ]
          split_ifs <;> norm_num [ Nat.cast_sub ( show 1 ≤ p ^ 2 from pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ), Nat.cast_sub ( show 2 ≤ p ^ 2 from by nlinarith only [ Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ]
          focus
            ring_nf
          · norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ]
          · rw [ sub_div, div_self ( by norm_cast; nlinarith only [ Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ]
      obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hB.2
      refine le_trans ( density_of_subset_periodic A B M hM₁ hM₂ hB.1 ) ?_
      convert hM₃.le using 1
      rw [ show ( Finset.filter Nat.Prime ( Finset.Icc 1 K ) ) = Finset.filter Nat.Prime ( Finset.Icc 1 C ) ∪ Finset.filter Nat.Prime ( Finset.Icc ( C + 1 ) K ) from ?_, Finset.prod_union ]
      · exact congrArg₂ _ ( Finset.prod_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ] ) ( Finset.prod_congr rfl fun x hx => by rw [ if_neg ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ] ) ] )
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ]
      · ext
        simp [Finset.mem_union, Finset.mem_filter]
        grind

/-
The infinite product of (1 - 2/p^2) for p > C is strictly less than the infinite product of (1 - 1/p^2) for p > C.
-/
lemma prod_inequality (C : ℕ) :
  (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) <
  (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
    have h_log_lt : Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) ∧ Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) := by
      constructor
      · -- We can bound the absolute value of the logarithm by the absolute value of the argument.
        have h_log_bound : ∀ p : ℕ, Nat.Prime p ∧ C < p → |Real.log (1 - 1 / (p : ℝ) ^ 2)| ≤ 2 / (p : ℝ) ^ 2 := by
          intro p hp
          have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 4 → |Real.log (1 - x)| ≤ 2 * x := by
            intro x hx
            rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ]
            nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]
          convert h_log_bound ( 1 / ( p : ℝ ) ^ 2 ) ⟨ by exact one_div_pos.mpr ( sq_pos_of_pos ( Nat.cast_pos.mpr hp.1.pos ) ), by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ hp.1.two_le ] ⟩ using 1 ; ring
        have h_summable : Summable (fun p : ℕ => 2 / (p : ℝ) ^ 2) := by
          exact Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two
        -- Apply the comparison test with the summable series ∑' p : ℕ, 2 / (p : ℝ) ^ 2.
        have h_comparison : Summable (fun p : ℕ => |if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ) ^ 2) else 0|) := by
          exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => by split_ifs <;> [ exact h_log_bound p ‹_›; exact by norm_num; positivity ] ) h_summable
        exact h_comparison.of_abs
      · -- The series $\sum_{p > C} \log(1 - 2/p^2)$ converges absolutely because $\log(1 - 2/p^2) \leq -2/p^2$ and $\sum_{p > C} 2/p^2$ converges.
        have h_abs_conv : Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then |Real.log (1 - 2 / (p : ℝ)^2)| else 0) := by
          -- We'll use the fact that |Real.log (1 - x)| ≤ 2x for x in [0, 1/2].
          have h_log_bound : ∀ p : ℕ, Nat.Prime p → C < p → |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 4 / (p : ℝ)^2 := by
            intros p hp hC
            have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → abs (Real.log (1 - x)) ≤ 2 * x := by
              intros x hx
              rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ]
              nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]
            convert h_log_bound ( 2 / ( p : ℝ ) ^ 2 ) ⟨ by exact div_pos zero_lt_two ( sq_pos_of_pos ( Nat.cast_pos.mpr hp.pos ) ), by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ hp.two_le ] ⟩ using 1 ; ring
          refine Summable.of_nonneg_of_le ( fun p => ?_ ) ( fun p => ?_ ) ( Summable.mul_left 4 <| Real.summable_nat_pow_inv.2 one_lt_two )
          · positivity
          · split_ifs <;> [ exact h_log_bound p ( by tauto ) ( by tauto ) ; exact by positivity ]
        exact Summable.of_norm <| h_abs_conv.congr fun p => by split_ifs <;> norm_num
    have h_exp_log_lt : (∏' p : ℕ, if Nat.Prime p ∧ C < p then (1 - 2 / (p : ℝ)^2) else 1) = Real.exp (∑' p : ℕ, if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) ∧ (∏' p : ℕ, if Nat.Prime p ∧ C < p then (1 - 1 / (p : ℝ)^2) else 1) = Real.exp (∑' p : ℕ, if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) := by
      constructor
      all_goals
        rw [ Real.exp_eq_exp_ℝ ]
      · have h_exp_log_lt : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
          exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
        convert h_exp_log_lt _ _ using 1
        · rw [ Real.exp_eq_exp_ℝ ]
          congr
          ext p
          aesop
        · intro p
          split_ifs
          all_goals
            norm_num
          rw [ div_lt_iff₀ ]
          all_goals
            norm_cast
          all_goals
            nlinarith [ Nat.Prime.two_le ( by tauto : Nat.Prime p ) ]
        · exact h_log_lt.2.congr fun p => by aesop
      · have h_exp_log_lt : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
          exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
        rw [ ← Real.exp_eq_exp_ℝ, h_exp_log_lt ]
        · exact congr_arg Real.exp ( tsum_congr fun p => by split_ifs <;> norm_num )
        · intro p
          split_ifs
          all_goals
            norm_num
          exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt ( by tauto ) ) two_ne_zero
        · exact h_log_lt.1.congr fun p => by split_ifs <;> norm_num
    -- Since there exists at least one prime $p > C$, we can find such a prime $p$.
    obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ C < p := by
      exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( C + 1 ) )
    have h_log_lt : ∑' p : ℕ, (if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) < ∑' p : ℕ, (if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) := by
      fapply Summable.tsum_lt_tsum
      · use p
      · intro n
        by_cases hn : Nat.Prime n ∧ C < n <;> simp +decide [ hn ]
        exact Real.log_le_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ hn.1.two_le ] ) <| sub_le_sub_left ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith only [ hn.1.two_le ] ) _
      · rw [ if_pos ⟨ hp_prime, hp_gt ⟩, if_pos ⟨ hp_prime, hp_gt ⟩ ]
        exact Real.log_lt_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ hp_prime.two_le ] ) <| sub_lt_sub_left ( by rw [ div_lt_div_iff_of_pos_right ] <;> norm_cast ; nlinarith only [ hp_prime.two_le ] ) _
      · exact h_log_lt.2
      · exact h_log_lt.1
    aesop

/-
If a set A avoids at least 1 residue class mod p^2 for all p, and at least 2 residue classes mod p^2 for all p > C, then its upper density is strictly less than 6/pi^2.
-/
lemma sieve_strict_bound (A : Set ℕ) (C : ℕ)
    (h1 : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b)
    (h2 : ∀ p, Nat.Prime p → p > C → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ A, a % p^2 ≠ b1) ∧ (∀ a ∈ A, a % p^2 ≠ b2)) :
    upperDensity A < 6 / Real.pi^2 := by
      have h_limit : Filter.Tendsto (fun K => (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (C + 1) K), (1 - 2 / (p : ℝ)^2))) Filter.atTop (nhds ((∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
        refine Filter.Tendsto.mul tendsto_const_nhds ?_
        have h_partial_prod : Filter.Tendsto (fun K => ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ p > C) (Finset.range (K + 1)), (1 - 2 / (p : ℝ)^2)) Filter.atTop (nhds (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)) := by
          have h_partial_prod : Filter.Tendsto (fun K => ∏ p ∈ Finset.range (K + 1), (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)) Filter.atTop (nhds (∏' p : ℕ, (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
            have h_limit : Multipliable (fun p : ℕ => if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) := by
              have h_abs_conv : Summable (fun p : ℕ => |Real.log (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)|) := by
                have h_prod_conv : Summable (fun p : ℕ => |Real.log (1 - 2 / (p : ℝ)^2)| * (if Nat.Prime p ∧ p > C then 1 else 0)) := by
                  have h_prod_conv : Summable (fun p : ℕ => |Real.log (1 - 2 / (p : ℝ)^2)|) := by
                    -- We'll use the fact that |log(1 - x)| ≤ 2x for x in [0, 1/2].
                    have h_log_bound : ∀ p : ℕ, p ≥ 2 → |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 4 / (p : ℝ)^2 := by
                      intros p hp
                      have h_log_bound : |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 2 / (p : ℝ)^2 / (1 - 2 / (p : ℝ)^2) := by
                        have h_log_bound : ∀ x : ℝ, 0 < x ∧ x < 1 → |Real.log (1 - x)| ≤ x / (1 - x) := by
                          intros x hx
                          rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ]
                          rw [ div_eq_mul_inv ]
                          nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]
                        exact h_log_bound _ ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith ⟩
                      refine le_trans h_log_bound ?_
                      rw [ div_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by norm_cast, show ( p : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith, div_mul_cancel₀ ( 2 : ℝ ) ( show ( p : ℝ ) ^ 2 ≠ 0 by positivity ) ]
                    exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => if hp : p ≥ 2 then h_log_bound p hp else by interval_cases p <;> norm_num ) ( Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two )
                  exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( abs_nonneg _ ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( abs_nonneg _ ) ( by aesop ) ) h_prod_conv
                convert h_prod_conv using 2
                aesop
              have h_abs_conv : Multipliable (fun p : ℕ => Real.exp (Real.log (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
                refine ⟨ ?_, ?_ ⟩
                · exact Real.exp ( ∑' p : ℕ, Real.log ( if Nat.Prime p ∧ p > C then 1 - 2 / ( p : ℝ ) ^ 2 else 1 ) )
                · convert h_abs_conv.of_abs.hasSum.exp using 1 <;>
                  first | rfl | infer_instance | (ext; simp only [Function.comp_apply, Real.exp_eq_exp_ℝ]) | simp +decide [ Real.exp_eq_exp_ℝ ]
              convert h_abs_conv using 1
              ext p
              split_ifs
              all_goals
                norm_num
              rw [ Real.exp_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.Prime.two_le ( by tauto : Nat.Prime p ) ] ) ]
            simpa [Function.comp_def] using
              h_limit.hasProd.tendsto_prod_nat.comp (Filter.tendsto_add_atTop_nat 1)
          convert h_partial_prod using 2
          simp +decide [ Finset.prod_ite ]
        convert h_partial_prod using 2
        congr! 1
        ext
        simp [Finset.mem_Icc]
        exact ⟨ fun h => ⟨ by linarith, h.2, by linarith ⟩, fun h => ⟨ ⟨ by linarith, by linarith ⟩, h.2.1 ⟩ ⟩
      have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) < 6 / Real.pi ^ 2 := by
        have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) < (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
          apply_rules [ mul_lt_mul_of_pos_left, prod_inequality ]
          exact Finset.prod_pos fun p hp => sub_pos_of_lt <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) two_ne_zero
        have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) = (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) := by
          have h_limit : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
            have h_split : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = (∏' p : ℕ, if Nat.Prime p ∧ p ≤ C then (1 - 1 / (p : ℝ)^2) else 1) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
              rw [ ← Multipliable.tprod_mul ]
              · congr with p
                by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ C <;> simp +decide [ hp, hp' ]
              · refine multipliable_of_ne_finset_one (s := Finset.range ( C + 1 )) ?_
                exact fun p hp => if_neg fun h => hp <| Finset.mem_range.mpr <| by linarith
              · have h_prod_conv : Summable (fun p : ℕ => if Nat.Prime p ∧ p > C then (1 / (p : ℝ)^2) else 0) := by
                  exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
                have h_prod_conv : Multipliable (fun p : ℕ => 1 - (if Nat.Prime p ∧ p > C then (1 / (p : ℝ)^2) else 0)) := by
                  refine multipliable_one_add_of_summable ?_
                  exact h_prod_conv.norm.congr fun n => by split_ifs <;> norm_num
                convert h_prod_conv using 2
                aesop
            convert h_split using 2
            rw [ tprod_eq_prod ]
            any_goals exact Finset.filter Nat.Prime ( Finset.Icc 1 C )
            · exact Finset.prod_congr rfl fun x hx => by aesop
            · aesop
          rw [h_limit]
        have h_limit : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = 6 / Real.pi ^ 2 := by
          convert tendsto_nhds_unique ( show Filter.Tendsto ( fun k => ∏ p ∈ Finset.filter Nat.Prime ( Finset.range k ), ( 1 - 1 / ( p : ℝ ) ^ 2 ) ) Filter.atTop ( nhds ( ∏' p : ℕ, if Nat.Prime p then ( 1 - 1 / ( p : ℝ ) ^ 2 ) else 1 ) ) from ?_ ) ( prod_primes_inv_sq_tendsto ) using 1
          have h_prod : Multipliable (fun p : ℕ => if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) := by
            have h_prod : Summable (fun p : ℕ => if Nat.Prime p then (1 / (p : ℝ)^2) else 0) := by
              exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
            have h_prod : Multipliable (fun p : ℕ => 1 - (if Nat.Prime p then (1 / (p : ℝ)^2) else 0)) := by
              refine multipliable_one_add_of_summable ?_
              exact h_prod.norm.congr fun _ => by split_ifs <;> norm_num
            convert h_prod using 2
            aesop
          convert h_prod.hasProd.tendsto_prod_nat using 1
          exact funext fun n => by rw [ Finset.prod_filter ]
        linarith
      refine lt_of_le_of_lt ?_ h_limit
      exact le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› ( Filter.eventually_atTop.mpr ⟨ C + 1, fun K hK => sieve_finite_bound A C K ( by linarith ) h1 h2 ⟩ )

open Finset Filter Asymptotics

/-! ## Chebyshev Prime Bounds -/

/-- The sum ∑_{p ≤ x, prime} log p over `Finset.range` equals `Chebyshev.theta x` for x ≥ 0. -/
lemma sum_log_primes_eq_theta (x : ℝ) (hx : 0 ≤ x) :
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x),
      Real.log (p : ℝ) = Chebyshev.theta x := by
  congr 1 with ( _ | p ) <;> simp +arith +decide [ Nat.prime_def_lt' ]
  exact fun h₁ h₂ h₃ => le_trans ( mod_cast Nat.succ_le_of_lt h₁ ) ( Nat.floor_le hx )

/-- The sum of log p for p ≤ x is O(x), proved from Chebyshev's upper bound. -/
lemma theta_bound_chebyshev :
    (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x)
      (Finset.range (Nat.floor x + 1)), Real.log p) =O[atTop] (fun x => x) := by
  refine Asymptotics.IsBigO.of_bound ( Real.log 4 ) ?_
  filter_upwards [ Filter.eventually_ge_atTop 0 ] with x hx using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| by aesop ) ] ; rw [ Real.norm_of_nonneg hx ] ; exact sum_log_primes_eq_theta x hx ▸ Chebyshev.theta_le_log4_mul_x hx

/-- The number of primes up to y, as a real, is O(y / log y). -/
lemma pi_le_const_mul_div_log :
    ∀ᶠ y : ℝ in atTop,
      ((Finset.filter Nat.Prime (Finset.range (Nat.floor y + 1))).card : ℝ) ≤
        (Real.log 4 + 1) * y / Real.log y := by
  filter_upwards [ Filter.eventually_gt_atTop 1, Chebyshev.eventually_primeCounting_le zero_lt_one ] with x hx₁ hx₂
  convert hx₂ using 1
  rw [ Nat.primeCounting ]
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ]

/-- Auxiliary: sum of primes up to y is O(y² / log y). -/
lemma sum_primes_le_y_bound :
    ∀ᶠ y : ℝ in atTop,
      (∑ p ∈ (Finset.range (Nat.floor y + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ y),
        (p : ℝ)) ≤ (Real.log 4 + 1) * y ^ 2 / Real.log y := by
  filter_upwards [ Filter.eventually_gt_atTop 1, pi_le_const_mul_div_log ] with y hy₁ hy₂
  refine le_trans ( Finset.sum_le_sum fun i hi => show ( i : ℝ ) ≤ y from ?_ ) ?_
  · aesop
  · convert mul_le_mul_of_nonneg_left hy₂ ( show 0 ≤ y by positivity ) using 1
    focus
      ring_nf
    · norm_num [ add_comm, mul_comm ]
      exact Or.inl ( congr_arg Finset.card <| Finset.filter_congr fun x hx => ⟨ fun hx' => hx'.1, fun hx' => ⟨ hx', by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp hx ) <| Nat.floor_le <| by positivity ⟩ ⟩ )
    · ring

/-
The sum of p/(log log p)² for p ≤ √(2x) is o(x).
-/
lemma error_term_small_chebyshev :
    (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x))
      (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)),
      (p : ℝ) / (Real.log (Real.log p))^2) =o[atTop] (fun x => x) := by
  -- Since $\frac{p}{(\ln \ln p)^2} \leq Cp$ for some constant $C$ and all sufficiently large primes $p$, we can bound the sum.
  have h_bound : ∃ C > 0, ∀ p : ℕ, Nat.Prime p → p ≥ 16 → (p : ℝ) / (Real.log (Real.log p))^2 ≤ C * p := by
    -- Since $\frac{1}{(\ln \ln p)^2}$ is bounded above by some constant $C$ for all $p \geq 16$, we can choose $C$ such that $\frac{1}{(\ln \ln p)^2} \leq C$.
    obtain ⟨C, hC⟩ : ∃ C > 0, ∀ p : ℕ, Nat.Prime p → p ≥ 16 → 1 / (Real.log (Real.log p))^2 ≤ C := by
      use 1 / (Real.log (Real.log 16))^2
      exact ⟨ one_div_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log 16 by rw [ Real.lt_log_iff_exp_lt ( by norm_num ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num ) ) ) ), fun p hp hp' => one_div_le_one_div_of_le ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log 16 by rw [ Real.lt_log_iff_exp_lt ( by norm_num ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num ) ) ) ) ( pow_le_pow_left₀ ( Real.log_nonneg ( show 1 ≤ Real.log 16 by rw [ Real.le_log_iff_exp_le ( by norm_num ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num ) ) ) ( Real.log_le_log ( Real.log_pos ( show 1 < 16 by norm_num ) ) ( Real.log_le_log ( by positivity ) ( by norm_cast ) ) ) _ ) ⟩
    exact ⟨ C, hC.1, fun p hp hp' => by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
          using mul_le_mul_of_nonneg_right ( hC.2 p hp hp' ) ( Nat.cast_nonneg p ) ⟩
  -- Using the bound, we can show that the sum is $O(x / \log x)$.
  have h_sum_bound : ∀ᶠ x : ℝ in atTop, (∑ p ∈ (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)), (p : ℝ) / (Real.log (Real.log p))^2) ≤ (Real.log 4 + 1) * (Real.sqrt (2 * x))^2 / Real.log (Real.sqrt (2 * x)) * h_bound.choose + (∑ p ∈ Finset.filter Nat.Prime (Finset.range 16), (p : ℝ) / (Real.log (Real.log p))^2) := by
    have h_sum_bound : ∀ᶠ x : ℝ in atTop, (∑ p ∈ (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ p ≥ 16), (p : ℝ) / (Real.log (Real.log p))^2) ≤ (Real.log 4 + 1) * (Real.sqrt (2 * x))^2 / Real.log (Real.sqrt (2 * x)) * h_bound.choose := by
      have h_sum_bound : ∀ᶠ x : ℝ in atTop, (∑ p ∈ (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ p ≥ 16), (p : ℝ)) ≤ (Real.log 4 + 1) * (Real.sqrt (2 * x))^2 / Real.log (Real.sqrt (2 * x)) := by
        have h_sum_bound : ∀ᶠ x : ℝ in atTop, (∑ p ∈ (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)), (p : ℝ)) ≤ (Real.log 4 + 1) * (Real.sqrt (2 * x))^2 / Real.log (Real.sqrt (2 * x)) := by
          have := sum_primes_le_y_bound
          exact this.filter_mono ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt ( 2 * x ) ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2 / 2, fun y hy => Real.le_sqrt_of_sq_le <| by linarith ⟩ )
        filter_upwards [ h_sum_bound ] with x hx using le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => by aesop ) fun _ _ _ => Nat.cast_nonneg _ ) hx
      filter_upwards [ h_sum_bound ] with x hx
      refine le_trans ?_ ( mul_le_mul_of_nonneg_right hx <| le_of_lt h_bound.choose_spec.1 )
      rw [ Finset.sum_mul _ _ _ ]
      exact Finset.sum_le_sum fun p hp => by simpa only [ mul_comm ] using h_bound.choose_spec.2 p ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hp |>.2.2.2 )
    filter_upwards [ h_sum_bound, Filter.eventually_gt_atTop 256 ] with x hx₁ hx₂
    rw [ show ( Finset.filter ( fun p : ℕ => Nat.Prime p ∧ ( p : ℝ ) ≤ Real.sqrt ( 2 * x ) ) ( Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 ) ) ) = Finset.filter ( fun p : ℕ => Nat.Prime p ∧ ( p : ℝ ) ≤ Real.sqrt ( 2 * x ) ∧ p ≥ 16 ) ( Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 ) ) ∪ Finset.filter ( fun p : ℕ => Nat.Prime p ∧ ( p : ℝ ) ≤ Real.sqrt ( 2 * x ) ∧ p < 16 ) ( Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 ) ) from ?_, Finset.sum_union ]
    · refine add_le_add hx₁ ?_
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg
        (t := Finset.filter Nat.Prime ( Finset.range 16 )) ?_ ?_ ) ?_
      · grind
      · exact fun _ _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ )
      · norm_num [ Finset.sum_filter, Finset.sum_range_succ ]
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith
    · grind
  -- Simplify the expression to show it is $o(x)$.
  have h_simplify : Filter.Tendsto (fun x : ℝ => ((Real.log 4 + 1) * (Real.sqrt (2 * x))^2 / Real.log (Real.sqrt (2 * x)) * h_bound.choose + (∑ p ∈ Finset.filter Nat.Prime (Finset.range 16), (p : ℝ) / (Real.log (Real.log p))^2)) / x) Filter.atTop (nhds 0) := by
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun x : ℝ => ((Real.log 4 + 1) * 2 * x / (Real.log (Real.sqrt (2 * x))) * h_bound.choose) / x) Filter.atTop (nhds 0) by
      have h_simplify : Filter.Tendsto (fun x : ℝ => ((Real.log 4 + 1) * 2 * x / (Real.log (Real.sqrt (2 * x))) * h_bound.choose) / x + (∑ p ∈ Finset.filter Nat.Prime (Finset.range 16), (p : ℝ) / (Real.log (Real.log p))^2) / x) Filter.atTop (nhds 0) := by
        simpa using h_simplify.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id )
      refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.sq_sqrt ( by positivity ) ] ; ring )
    -- Simplify the expression inside the limit further.
    suffices h_simplify' : Filter.Tendsto (fun x : ℝ => (Real.log 4 + 1) * 2 * h_bound.choose / Real.log (Real.sqrt (2 * x))) Filter.atTop (nhds 0) by
      refine h_simplify'.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ eq_div_iff hx.ne' ] ; ring )
    exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2 / 2, fun y hy => Real.le_sqrt_of_sq_le <| by linarith ⟩ )
  rw [ Asymptotics.isLittleO_iff_tendsto' ]
  · refine squeeze_zero_norm' ?_ h_simplify
    filter_upwards [ h_sum_bound, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) ) hx₂.le ) ] ; exact div_le_div_of_nonneg_right hx₁ hx₂.le
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
For n ≥ 3, 1/(n·(log n)²) ≤ 1/log(n-1) - 1/log(n).
-/
lemma inv_mul_log_sq_le_diff_inv_log (n : ℕ) (hn : 3 ≤ n) :
    1 / ((n : ℝ) * (Real.log n)^2) ≤ 1 / Real.log (n - 1 : ℝ) - 1 / Real.log n := by
  -- We'll use the Mean Value Theorem to show that $f(n) - f(n-1) \ge f'(n)$.
  have h_mean_value : ∃ c ∈ Set.Ioo (n - 1 : ℝ) n, deriv (fun x => -1 / Real.log x) c = ( (-1 / Real.log n) - (-1 / Real.log (n - 1)) ) / (n - (n - 1)) := by
    apply_rules [ exists_deriv_eq_slope ] <;> norm_num
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) )
    · exact DifferentiableOn.div ( differentiableOn_const _ ) ( DifferentiableOn.log differentiableOn_id fun x hx => by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] ) fun x hx => ne_of_gt <| Real.log_pos <| by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ]
  obtain ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ := h_mean_value
  -- Since $c < n$, we have $1 / (c * (Real.log c) ^ 2) \ge 1 / (n * (Real.log n) ^ 2)$.
  have h_deriv_ge : 1 / (c * (Real.log c) ^ 2) ≥ 1 / (n * (Real.log n) ^ 2) := by
    gcongr
    · exact mul_pos ( by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) )
    · exact Real.log_nonneg ( by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] )
    · linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ]
  norm_num [ show c ≠ 0 by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ], show Real.log c ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ], div_eq_mul_inv ] at * ; ring_nf at * ; linarith

/-
The series ∑_{n≥3} 1/(n·(log n)²) is summable (bounded by 1/log 2).
-/
lemma summable_inv_mul_log_sq :
    Summable (fun n : ℕ => if 3 ≤ n then 1 / ((n : ℝ) * (Real.log n)^2) else 0) := by
  refine summable_nat_add_iff 3 |>.1 ?_
  -- Apply the integral test to show that the series converges.
  have h_integral_test : Summable (fun n : ℕ => ∫ x in (n + 3 : ℝ)..((n + 4) : ℝ), 1 / (x * (Real.log x)^2)) := by
    -- Evaluate the integral $\int_{n+3}^{n+4} \frac{dx}{x (\ln x)^2}$.
    have h_integral_eval : ∀ n : ℕ, ∫ x in (n + 3 : ℝ).. (n + 4), (1 / (x * (Real.log x)^2)) = (1 / Real.log (n + 3)) - (1 / Real.log (n + 4)) := by
      intro n
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ]
      rotate_right
      · use fun x => -1 / Real.log x
      · ring_nf
      · intro x hx
        convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith ) using 1 <;> first | rfl | ring
      · apply_rules [ ContinuousOn.intervalIntegrable ]
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith
      -- The series $\sum_{n=3}^{\infty} \left( \frac{1}{\ln(n+3)} - \frac{1}{\ln(n+4)} \right)$ is a telescoping series.
    have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / Real.log (n + 3) - 1 / Real.log (n + 4)) = 1 / Real.log 3 - 1 / Real.log (N + 3) := by
      exact fun N => by
        induction N with
        | zero =>
          norm_num [ add_assoc, Finset.sum_range_succ ] at *
        | succ N ih =>
          norm_num [ add_assoc, Finset.sum_range_succ ] at *
          linear_combination ih
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ]
    · exact fun h => not_tendsto_atTop_of_tendsto_nhds ( by
        simpa only [ h_integral_eval, h_telescoping, Function.comp_apply ]
          using tendsto_const_nhds.sub
            (tendsto_const_nhds.div_atTop <|
              Real.tendsto_log_atTop.comp <|
                Filter.tendsto_atTop_add_const_right Filter.atTop (3 : ℝ)
                  tendsto_natCast_atTop_atTop) ) h
    · exact fun n => intervalIntegral.integral_nonneg ( by linarith ) fun x hx => one_div_nonneg.2 ( mul_nonneg ( by linarith [ hx.1 ] ) ( sq_nonneg _ ) )
  have h_integral_bound : ∀ n : ℕ, ∫ x in (n + 3 : ℝ)..((n + 4) : ℝ), 1 / (x * (Real.log x)^2) ≥ 1 / ((n + 4 : ℝ) * (Real.log (n + 4))^2) := by
    intro n
    have h_integral_bound : ∀ x ∈ Set.Icc (n + 3 : ℝ) (n + 4 : ℝ), 1 / (x * (Real.log x)^2) ≥ 1 / ((n + 4 : ℝ) * (Real.log (n + 4))^2) := by
      simp +zetaDelta at *
      bound
    refine le_trans ?_ ( intervalIntegral.integral_mono_on ?_ ?_ ?_ h_integral_bound ) <;> norm_num
    apply_rules [ ContinuousOn.intervalIntegrable ]
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) )
  exact summable_nat_add_iff 1 |>.1 <| h_integral_test.of_nonneg_of_le ( fun n => by positivity ) fun n => by exact_mod_cast h_integral_bound n

/-
Partial sums of 1/(n·(log n)²) are bounded by 1/log 2.
-/
lemma partial_sum_inv_mul_log_sq_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 3 N, 1 / ((n : ℝ) * (Real.log n)^2) ≤ 1 / Real.log 2 := by
  rcases lt_trichotomy N 2
  all_goals
    norm_num at *
  · interval_cases N <;> norm_num
    · positivity
    · positivity
  · -- For $N \geq 3$, we can use the telescoping series.
    have h_telescope : ∀ N : ℕ, 3 ≤ N → (∑ n ∈ Finset.Icc 3 N, (1 / ((n : ℝ) * (Real.log n)^2))) ≤ (1 / Real.log 2) - (1 / Real.log N) := by
        intro N hN
        induction N, Nat.succ_le_iff.mpr hN using Nat.le_induction with
        | base =>
          have := inv_mul_log_sq_le_diff_inv_log 3
          norm_num at *
          linarith
        | succ N hN ih =>
          erw [ Finset.sum_Ioc_succ_top ( by linarith ), add_comm ]
          have := inv_mul_log_sq_le_diff_inv_log ( N + 1 ) ( by linarith )
          norm_num at *
          linarith! [ ih hN ]
    rcases ‹N = 2 ∨ 2 < N› with ( rfl | hN )
    all_goals
      norm_num at *
    · positivity
    · exact le_trans ( h_telescope N hN ) ( sub_le_self _ ( inv_nonneg.2 ( Real.log_nonneg ( by norm_cast; linarith ) ) ) )

/-
The tail sum of 1/(p (log log p)²) for p > P tends to 0.
-/
lemma tail_sum_bound_chebyshev :
    Tendsto (fun P => ∑' p, if p > P ∧ Nat.Prime p then
      1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) atTop (nhds 0) := by
  by_cases h_summable : Summable (fun p : ℕ => if Nat.Prime p then (Real.log (Real.log p) ^ 2)⁻¹ * (p : ℝ)⁻¹ else 0)
  · convert tendsto_sum_nat_add fun n => if Nat.Prime ( n + 1 ) then ( Real.log ( Real.log ( n + 1 ) ) ^ 2 ) ⁻¹ * ( n + 1 : ℝ ) ⁻¹ else 0 using 1
    ext P
    rw [ ← Summable.sum_add_tsum_nat_add P.succ ]
    focus
      norm_num [ add_assoc, Nat.succ_eq_add_one ]
    · rw [ Finset.sum_eq_zero ]
      all_goals
        norm_num
      · grind
      · grind
    · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by split_ifs <;> first | positivity | aesop ) h_summable
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with P hP
    rw [ tsum_eq_zero_of_not_summable ]
    rw [ ← summable_nat_add_iff ( P + 1 ) ] at *
    grind

/-- There exists N₀ such that for N ≥ N₀, the number of primes ≤ N is at most
    (log 4 + 1) * N / log N. -/
lemma chebyshev_pi_bound_concrete :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ((Finset.filter Nat.Prime (Finset.range (N + 1))).card : ℝ) ≤
        (Real.log 4 + 1) * N / Real.log N := by
  set ε := (1 : ℝ)
  have hεpos : 0 < ε := by norm_num
  have := Chebyshev.eventually_primeCounting_le hεpos
  rw [ Filter.eventually_atTop ] at this
  rcases this with ⟨ N₀, hN₀ ⟩
  refine ⟨ ⌈N₀⌉₊ + 1, ?_ ⟩
  intro N hN
  have hceil : ⌈N₀⌉₊ ≤ N := by omega
  have hN₀N : N₀ ≤ (N : ℝ) := Nat.le_of_ceil_le hceil
  simpa [ε, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    using hN₀ (N : ℝ) hN₀N

/-- For k ≥ 8, log(k * log 2) ≥ (log k)/2. -/
lemma log_k_log2_ge_half_logk (k : ℕ) (hk : k ≥ 8) :
    Real.log ((k : ℝ) * Real.log 2) ≥ Real.log (k : ℝ) / 2 := by
  rw [ Real.log_mul ( by positivity ) ( by positivity ), ge_iff_le, div_le_iff₀' ]
  all_goals
    norm_num
  have h_log_k : Real.log k ≥ 3 * Real.log 2 := by
    rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_cast ; linarith
  have := Real.log_two_gt_d9
  norm_num at *
  nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]

/-- For n ≥ 2^k with k ≥ 8, log(log n) ≥ (log k)/2. -/
lemma loglog_lower_bound (n k : ℕ) (hk : k ≥ 8) (hn : n ≥ 2^k) :
    Real.log (Real.log (n : ℝ)) ≥ Real.log (k : ℝ) / 2 := by
  have h_log_log : Real.log (Real.log n) ≥ Real.log (k * Real.log 2) := by
    gcongr
    rw [ ← Real.log_pow ]
    gcongr
    norm_cast
  exact le_trans ( log_k_log2_ge_half_logk k hk ) h_log_log

/-- For p ≥ 2^k with k ≥ 8: 1/(p * (log log p)²) ≤ 4/(2^k * (log k)²). -/
lemma term_bound_in_block (p k : ℕ) (hk : k ≥ 8) (hp : p ≥ 2^k) :
    1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤
      4 / ((2:ℝ)^k * (Real.log k)^2) := by
  have h_log_log_p : Real.log (Real.log p) ≥ Real.log k / 2 := by
    exact loglog_lower_bound p k hk hp
  have h_subst : (p : ℝ) * (Real.log (Real.log p))^2 ≥ (2^k : ℝ) * ((Real.log k) / 2)^2 := by
    gcongr
    norm_cast
  rw [ div_le_div_iff₀ ]
  all_goals
    nlinarith [ show 0 < ( 2 : ℝ ) ^ k by positivity, show 0 < Real.log k ^ 2 by exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ]

/-- Bound the contribution from primes in a single dyadic block [2^k, 2^{k+1}). -/
lemma block_sum_bound (k : ℕ) (hk : k ≥ 8) (N₀ : ℕ)
    (hcheb : ∀ N : ℕ, N ≥ N₀ →
      ((Finset.filter Nat.Prime (Finset.range (N + 1))).card : ℝ) ≤
        (Real.log 4 + 1) * N / Real.log N)
    (hk_large : 2^(k+1) ≥ N₀) :
    ∑ p ∈ ((Finset.Ico (2^k) (2^(k+1))).filter Nat.Prime),
      1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤
        8 * (Real.log 4 + 1) / (Real.log 2 * k * (Real.log k)^2) := by
  have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ico (2^k) (2^(k+1))), 1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤ 4 / ((2 : ℝ)^k * (Real.log k)^2) := by
    intro p hp
    convert term_bound_in_block p k hk ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) using 1
  have h_prime_count : (Finset.filter Nat.Prime (Finset.Ico (2^k) (2^(k+1)))).card ≤ (Real.log 4 + 1) * 2^(k+1) / ((k+1) * Real.log 2) := by
    refine le_trans ?_ ( le_trans ( hcheb (2 ^ (k + 1)) hk_large ) ?_ )
    · exact_mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr <| by linarith [ Finset.mem_Ico.mp hx ]
    · norm_num [ Real.log_pow ]
  refine le_trans ( Finset.sum_le_sum h_term_bound ) ?_
  norm_num [ pow_succ' ] at *
  refine le_trans ( mul_le_mul_of_nonneg_right h_prime_count <| by positivity ) ?_
  field_simp
  exact div_le_div_of_nonneg_right ( by linarith ) ( sq_nonneg _ )

/-
The partial sums of the prime reciprocal loglog series are bounded.
-/
lemma prime_loglog_partial_sums_bounded :
    ∃ B : ℝ, ∀ N : ℕ,
      ∑ p ∈ (Finset.range N).filter (fun p => Nat.Prime p),
        1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤ B := by
  obtain ⟨ N₀, hN₀ ⟩ := chebyshev_pi_bound_concrete
  obtain ⟨ K₀, hK₀ ⟩ : ∃ K₀ : ℕ, K₀ ≥ 8 ∧ 2^(K₀+1) ≥ N₀ := by
    exact ⟨ N₀ + 8, by linarith, by linarith [ Nat.le_ceil ( Real.logb 2 N₀ ), show 2 ^ ( N₀ + 8 + 1 ) ≥ N₀ + 8 + 1 from Nat.recOn N₀ ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith ] ⟩
  have h_sum_bound : ∀ N : ℕ, (∑ p ∈ ((Finset.Ico (2^K₀) N).filter Nat.Prime), 1 / ((p : ℝ) * (Real.log (Real.log p))^2)) ≤ 8 * (Real.log 4 + 1) / (Real.log 2)^2 := by
    intro N
    have h_sum_bound : (∑ p ∈ ((Finset.Ico (2^K₀) N).filter Nat.Prime), 1 / ((p : ℝ) * (Real.log (Real.log p))^2)) ≤ ∑ k ∈ Finset.Ico K₀ (Nat.log 2 (N - 1) + 1), ∑ p ∈ ((Finset.Ico (2^k) (2^(k+1))).filter Nat.Prime), 1 / ((p : ℝ) * (Real.log (Real.log p))^2) := by
      rw [ ← Finset.sum_biUnion ]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro p hp
        simp_all +decide
        exact ⟨ Nat.log 2 p, ⟨ Nat.le_log_of_pow_le ( by norm_num ) hp.1.1, Nat.log_mono_right ( Nat.le_sub_one_of_lt hp.1.2 ) ⟩, Nat.pow_le_of_le_log ( by linarith [ Nat.Prime.one_lt hp.2 ] ) ( by linarith ), Nat.lt_pow_of_log_lt ( by norm_num ) ( by linarith ) ⟩
      · intros k hk l hl hkl
        simp_all +decide [ Finset.disjoint_left ]
        grind +suggestions
    refine le_trans h_sum_bound <| le_trans ( Finset.sum_le_sum fun k hk => block_sum_bound k ( by linarith [ Finset.mem_Ico.mp hk ] ) N₀ hN₀ <| by linarith [ Finset.mem_Ico.mp hk, Nat.pow_le_pow_right two_pos ( show k + 1 ≥ K₀ + 1 from by linarith [ Finset.mem_Ico.mp hk ] ) ] ) ?_
    have h_sum_bound : ∑ k ∈ Finset.Ico K₀ (Nat.log 2 (N - 1) + 1), (1 / ((k : ℝ) * (Real.log k)^2)) ≤ 1 / Real.log 2 := by
      have h_sum_bound : ∑ k ∈ Finset.Ico 3 (Nat.log 2 (N - 1) + 1), (1 / ((k : ℝ) * (Real.log k)^2)) ≤ 1 / Real.log 2 := by
        rw [show Finset.Ico 3 (Nat.log 2 (N - 1) + 1) =
            Finset.Icc 3 (Nat.log 2 (N - 1)) by
          ext k
          simp]
        exact partial_sum_inv_mul_log_sq_le ( Nat.log 2 ( N - 1 ) )
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Ico_subset_Ico ( by linarith ) le_rfl ) fun _ _ _ => by positivity ) h_sum_bound
    convert mul_le_mul_of_nonneg_left h_sum_bound ( show ( 0 : ℝ ) ≤ 8 * ( Real.log 4 + 1 ) / Real.log 2 by positivity ) using 1 <;> ring_nf
    simp +decide only [mul_assoc, sum_add_distrib, Finset.mul_sum _ _ _, sum_mul]
  use (∑ p ∈ ((Finset.range (2^K₀)).filter Nat.Prime), 1 / ((p : ℝ) * (Real.log (Real.log p))^2)) + 8 * (Real.log 4 + 1) / (Real.log 2)^2
  intro N
  specialize h_sum_bound N
  by_cases hN : N ≤ 2^K₀ <;> simp_all +decide [ Finset.sum_filter ]
  · exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hN ) fun _ _ _ => by positivity ) h_sum_bound
  · rw [ ← Finset.sum_range_add_sum_Ico _ hN.le ]
    linarith

/-
The sum of 1/(p * (log log p)²) over primes is summable.
-/
lemma prime_loglog_summable :
    Summable (fun n : ℕ => if Nat.Prime n then
      1 / ((n : ℝ) * (Real.log (Real.log n))^2) else 0) := by
  obtain ⟨ B, hB ⟩ := prime_loglog_partial_sums_bounded
  rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ]
  · exact fun h => absurd ( h.eventually_gt_atTop B ) fun h' => by
      obtain ⟨ N, hN ⟩ := h'.exists
      exact not_le_of_gt hN <| by simpa [ Finset.sum_filter ] using hB N
  · intro n
    split_ifs
    all_goals
      positivity

/-
The tail sum (with p > P condition) is summable for any P.
-/
theorem tail_summable_from_chebyshev (P : ℕ) :
    Summable (fun p : ℕ => if p > P ∧ Nat.Prime p then
      1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) := by
  refine .of_nonneg_of_le ( fun p => ?_ ) ( fun p => ?_ ) ( prime_loglog_summable )
  · positivity
  · split_ifs <;> norm_num
    focus
      aesop
    positivity

/-
The tail sum of 1/(p (log log p)^2) tends to 0 as P goes to infinity.
-/
lemma tail_sum_bound :
    Filter.Tendsto (fun P => ∑' p, if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) Filter.atTop (nhds 0) := by
      exact tail_sum_bound_chebyshev

/-
The sum of p/(log log p)^2 for p <= sqrt(2x) is o(x).
-/
lemma error_term_small :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) =o[Filter.atTop] (fun x => x) := by
    exact error_term_small_chebyshev

/-
Definitions for relevant primes, bound for a, relevant pairs, and the set S_x of multiples of W in the interval.
-/
def relevant_primes (P : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ p > P)

def a_bound (p : ℕ) : ℕ := Nat.floor ((p : ℝ) / (Real.log (Real.log p))^2)

def relevant_pairs (P : ℕ) (x : ℝ) : Finset (ℕ × ℕ) :=
  (relevant_primes P x).biUnion (fun p => (Finset.Icc 1 (a_bound p)).image (fun a => (p, a)))

def S_x (x : ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil (x/2)) (Nat.floor x)).filter (fun n => n % W = 0)

/-
Definitions for W_P (product of p^2 for p <= P) and the set of bad n for a specific pair (p, a).
-/
def W_P (P : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (P + 1)), p^2

def bad_n_for_pair (x : ℝ) (W : ℕ) (p a : ℕ) : Finset ℕ :=
  (S_x x W).filter (fun n => (n + a) % p^2 = 0)

/-
Length of the interval [ceil(x/2), floor(x)].
-/
def L_x (x : ℝ) : ℕ := Nat.floor x - Nat.ceil (x/2) + 1

/-
The number of bad n for a given pair (p, a) is at most L_x / (W p^2) + 2.
-/
lemma bad_n_for_pair_bound (x : ℝ) (W : ℕ) (p a : ℕ) (hW : W > 0) (hp : p > 0) (hWp : Nat.Coprime W (p^2)) :
  ((bad_n_for_pair x W p a).card : ℝ) ≤ (L_x x : ℝ) / (W * p^2) + 2 := by
    unfold bad_n_for_pair S_x L_x
    by_cases h : ⌊x⌋₊ ≥ ⌈x / 2⌉₊ <;> simp_all +decide
    · -- Apply the lemma about the number of solutions to the congruence $n \equiv 0 \pmod{W}$ and $n \equiv -a \pmod{p^2}$.
      have h_card : ((Finset.Icc ⌈x / 2⌉₊ ⌊x⌋₊).filter (fun n => n % W = 0 ∧ (n + a) % p ^ 2 = 0)).card ≤ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1 : ℝ) / (W * p ^ 2) + 2 := by
        have h_card : ∀ (u L : ℕ) (W q : ℕ) (b c : ℕ), Nat.Coprime W q → W > 0 → q > 0 → let I := Finset.Icc u (u + L - 1)
        let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q]); (S_intersect.card : ℝ) ≤ (L : ℝ) / (W * q) + 2 := by
          intros u L W q b c hWq hW hq
          have h_card : abs ((Finset.card (Finset.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q]) (Finset.Icc u (u + L - 1))) : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
            convert card_intersect_bound u L W q b c hWq hW hq using 1
          linarith [ abs_le.mp h_card ]
        convert h_card ⌈x / 2⌉₊ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1) W (p ^ 2) 0 (p ^ 2 - a % (p ^ 2)) _ _ _ using 1 <;> norm_num [ Nat.Coprime, Nat.gcd_comm ]
        · rw [ show ⌈x / 2⌉₊ + ( ⌊x⌋₊ - ⌈x / 2⌉₊ ) = ⌊x⌋₊ from add_tsub_cancel_of_le <| Nat.ceil_le.mpr <| by linarith ]
          congr! 2
          simp +decide [Nat.ModEq]
          intro hxW
          rw [ ← Nat.dvd_iff_mod_eq_zero ] at *
          simp_all +decide [←
              ZMod.natCast_eq_zero_iff]
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
          rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| by positivity ) ]
          simp +decide
          rw [ eq_neg_iff_add_eq_zero ]
        · rw [ Nat.cast_sub ( Nat.ceil_le.mpr ( by linarith ) ) ]
        · exact hWp
        · positivity
        · positivity
      simpa only [ Finset.filter_filter ] using h_card
    · rw [ Finset.Icc_eq_empty ]
      all_goals
        norm_num
      · positivity
      · linarith

/-
Definitions of sums S1 and S2, and a bound on the cardinality of S_x.
-/
def sum_S1 (P : ℕ) (x : ℝ) : ℝ := ∑ p ∈ relevant_primes P x, (a_bound p : ℝ) / p^2
def sum_S2 (P : ℕ) (x : ℝ) : ℝ := ∑ p ∈ relevant_primes P x, (a_bound p : ℝ)

lemma card_S_x_bound (x : ℝ) (W : ℕ) (hW : W > 0) :
  abs ((S_x x W).card - (L_x x : ℝ) / W) ≤ 2 := by
    -- Apply the lemma `card_filter_modEq_Icc` to the interval [ceil(x/2), floor(x)].
    have h_apply_lemma : let I := Finset.Icc (Nat.ceil (x / 2)) (Nat.floor x)
      let S := I.filter (fun n => n % W = 0)
      abs ((S.card : ℝ) - (L_x x : ℝ) / W) ≤ 2 := by
        by_cases hx : ⌈x / 2⌉₊ ≤ ⌊x⌋₊ <;> simp_all +decide [ L_x ]
        · convert card_filter_modEq_Icc ⌈x / 2⌉₊ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1) 0 W hW using 1
          simp +decide [ Nat.ModEq, Nat.mod_eq_of_lt hW ]
          rw [ Nat.add_sub_of_le ( Nat.ceil_le.mpr ( by linarith ) ) ]
          rw [ Nat.cast_sub ( Nat.ceil_le.mpr ( by linarith ) ) ]
        · rw [ Nat.sub_eq_zero_of_le ]
          all_goals
            norm_num
          · rw [ Finset.card_eq_zero.mpr ]
            all_goals
              norm_num
            · exact le_trans ( inv_le_one_of_one_le₀ <| mod_cast hW ) <| by norm_num
            · intros
              linarith [ Nat.floor_le ( show 0 ≤ x by linarith [ Nat.lt_floor_add_one x ] ), show ( ↑‹ℕ› : ℝ ) ≤ ⌊x⌋₊ by norm_cast ]
          · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( x / 2 ) ]
    simpa [S_x] using h_apply_lemma

/-
Bound for the term a_bound p / p^2.
-/
lemma a_bound_term_le (p : ℕ) (hp : p ≥ 3) :
  (a_bound p : ℝ) / p^2 ≤ 1 / ((p : ℝ) * (Real.log (Real.log p))^2) := by
    field_simp
    exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) )

/-
Definition of tail_val as the infinite sum of 1/(p (log log p)^2) for primes p > P.
-/
def tail_val (P : ℕ) : ℝ := ∑' p, if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0

/-
sum_S1 is bounded by the sum of the upper bounds of its terms.
-/
lemma sum_S1_le_sum_bound (P : ℕ) (x : ℝ) :
  sum_S1 P x ≤ ∑ p ∈ relevant_primes P x, 1 / ((p : ℝ) * (Real.log (Real.log p))^2) := by
    apply Finset.sum_le_sum
    intro p hp
    by_cases hp3 : p ≥ 3
    · convert a_bound_term_le p hp3 using 1
    · interval_cases p <;> norm_num [ a_bound ] at hp ⊢
      rw [ div_le_iff₀ ]
      all_goals
        norm_num
      exact Nat.floor_le ( by positivity ) |> le_trans <| by ring_nf; norm_num

structure SieveAssumptions where
  tail_summable : ∀ P : ℕ, Summable (fun p : ℕ => if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0)

/-
The tail series of 1/(p (log log p)^2) is summable.
-/
lemma tail_summable (assumps : SieveAssumptions) (P : ℕ) :
  Summable (fun p : ℕ => if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) := by
    exact assumps.tail_summable P

/-
The sum over relevant primes is bounded by the tail value.
-/
lemma sum_subset_le_tail (P : ℕ) (x : ℝ) (assumps : SieveAssumptions) :
  ∑ p ∈ relevant_primes P x, 1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤ tail_val P := by
    refine le_trans
      (b := ∑ p ∈ relevant_primes P x,
        if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0)
      ?_ ( Summable.sum_le_tsum (relevant_primes P x) ?_ ?_ )
    · refine Finset.sum_le_sum fun p hp => ?_
      unfold relevant_primes at hp
      aesop
    · intro i hi
      split_ifs
      all_goals
        positivity
    · exact tail_summable assumps P

/-
Sum S1 is bounded by the tail value.
-/
lemma sum_S1_le_tail (P : ℕ) (x : ℝ) (assumps : SieveAssumptions) : sum_S1 P x ≤ tail_val P := by
  refine le_trans ( sum_S1_le_sum_bound P x ) ( sum_subset_le_tail P x assumps )

/-
sum_S2 is o(x).
-/
lemma sum_S2_is_littleO (P : ℕ):
  (fun x => sum_S2 P x) =o[Filter.atTop] (fun x => x) := by
    -- By definition of `sum_S2`, we have `sum_S2 P x ≤ ∑ p ∈ relevant_primes P x, p / (Real.log (Real.log p))^2`.
    have h_sum_S2_le : ∀ x : ℝ, sum_S2 P x ≤ ∑ p ∈ relevant_primes P x, (p : ℝ) / (Real.log (Real.log p))^2 := by
      intro x
      refine Finset.sum_le_sum fun p hp => ?_
      exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) )
    -- The sum over relevant primes is bounded by the sum over all primes $p \le \sqrt{2x}$ by definition of `relevant_primes`.
    have h_relevant_primes_le_all_primes : ∀ x : ℝ, ∑ p ∈ relevant_primes P x, (p : ℝ) / (Real.log (Real.log p))^2 ≤ ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2 := by
      intros x
      simp [relevant_primes]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ )
      simp +contextual [ Finset.subset_iff ]
      exact fun p hp₁ hp₂ hp₃ => Nat.floor_le ( by positivity ) |> le_trans ( mod_cast hp₁ )
    -- By `error_term_small`, this larger sum is $o(x)$.
    have h_error_term_small : (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) =o[Filter.atTop] (fun x => x) := by
      convert error_term_small using 1
    rw [ Asymptotics.isLittleO_iff ] at *
    intro c hc
    filter_upwards [ h_error_term_small hc, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂
    rw [ Real.norm_of_nonneg ( show 0 ≤ sum_S2 P x from Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ]
    exact le_trans ( h_sum_S2_le x |> le_trans <| h_relevant_primes_le_all_primes x ) ( le_trans ( le_abs_self _ ) hx₁ )

/-
Bound on the total number of bad n.
-/
def bad_n_total (P : ℕ) (x : ℝ) (W : ℕ) : Finset ℕ :=
  (relevant_pairs P x).biUnion (fun ⟨p, a⟩ => bad_n_for_pair x W p a)

lemma bad_n_card_bound (P : ℕ) (x : ℝ) (W : ℕ) (hW : W > 0)
    (h_coprime : ∀ p ∈ relevant_primes P x, Nat.Coprime W (p^2)) :
  (bad_n_total P x W).card ≤ (L_x x : ℝ) / W * (sum_S1 P x) + 2 * (sum_S2 P x) := by
    -- The cardinality of the union is at most the sum of cardinalities.
    have h_union_card : ((bad_n_total P x W).card : ℝ) ≤ ∑ p ∈ (relevant_primes P x), ∑ a ∈ (Finset.Icc 1 (a_bound p)), ((bad_n_for_pair x W p a).card : ℝ) := by
      refine mod_cast le_trans ( Finset.card_biUnion_le ) ?_
      erw [ Finset.sum_biUnion ]
      · exact Finset.sum_le_sum fun p hp => by
          rw [ Finset.sum_image ]
          aesop
      · exact fun p hp q hq hpq => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hpq <| by aesop
    -- Using `bad_n_for_pair_bound`, each term is $\le L_x / (W p^2) + 2$.
    have h_term_bound : ∀ p ∈ relevant_primes P x, ∀ a ∈ Finset.Icc 1 (a_bound p), ((bad_n_for_pair x W p a).card : ℝ) ≤ (L_x x : ℝ) / (W * p^2) + 2 := by
      intros p hp a ha
      apply bad_n_for_pair_bound x W p a hW (by
      exact Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 )) (by
      exact h_coprime p hp)
    refine le_trans
      (h_union_card.trans
        (Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun a ha =>
          h_term_bound p hp a ha)) ?_
    rw [show (L_x x : ℝ) / W * sum_S1 P x + 2 * sum_S2 P x =
        ∑ i ∈ relevant_primes P x, ∑ i_1 ∈ Finset.Icc 1 (a_bound i),
          ((L_x x : ℝ) / (W * i ^ 2) + 2) by
      norm_num [ div_eq_mul_inv, mul_add, mul_assoc, mul_comm, mul_left_comm,
        Finset.mul_sum _ _ _, Finset.sum_add_distrib ]
      unfold sum_S1 sum_S2
      simp +decide [div_eq_mul_inv, mul_assoc, mul_comm,
        Finset.mul_sum _ _ _]]

/-
The lower density of a set A of natural numbers.
-/
def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
For sufficiently large P, and sufficiently large x (depending on P), the number of bad n is strictly less than the number of multiples of W_P in the interval.
-/
lemma large_P_bound_satisfied (assumps : SieveAssumptions) :
    ∃ P₀, ∀ P ≥ P₀, ∃ x₀, ∀ x ≥ x₀, (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card := by
      -- By Lemma~\ref{lem:tail_sum_bound}, we can find $P$ large enough such that the tail value (and thus sum_S1) is less than 0.5.
      obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, ∀ P ≥ P₀, tail_val P < 0.5 := by
        have h_tail_zero : Filter.Tendsto tail_val Filter.atTop (nhds 0) := by
          refine tail_sum_bound.congr' ?_
          filter_upwards with P
          unfold tail_val
          congr with p
        simpa using h_tail_zero.eventually ( gt_mem_nhds <| by norm_num )
      -- By Lemma~\ref{lem:sum_S2_is_littleO}, the term $2 * sum_S2$ is $o(x)$, while $L_x x / W$ is proportional to $x$. So $2 * sum_S2 / (L_x x / W)$ tends to 0.
      have h_term_zero : ∀ P ≥ P₀, Filter.Tendsto (fun x => 2 * sum_S2 P x / ((L_x x : ℝ) / W_P P)) Filter.atTop (nhds 0) := by
        intro P hP
        have h_term_zero : Filter.Tendsto (fun x => sum_S2 P x / x) Filter.atTop (nhds 0) := by
          have := sum_S2_is_littleO P
          exact this.tendsto_div_nhds_zero
        have h_term_zero : Filter.Tendsto (fun x => (L_x x : ℝ) / x) Filter.atTop (nhds 0.5) := by
          have h_floor_ceil : ∀ x : ℝ, x ≥ 2 → (Nat.floor x : ℝ) - Nat.ceil (x / 2) + 1 ≥ x / 2 - 2 ∧ (Nat.floor x : ℝ) - Nat.ceil (x / 2) + 1 ≤ x / 2 + 2 := by
            intro x hx
            constructor
            all_goals
              linarith [ Nat.floor_le ( show 0 ≤ x by linarith ), Nat.lt_floor_add_one x, Nat.le_ceil ( x / 2 ), Nat.ceil_lt_add_one ( show 0 ≤ x / 2 by linarith ) ]
          rw [ Metric.tendsto_nhds ]
          intro ε hε
          filter_upwards [ Filter.eventually_ge_atTop 2, Filter.eventually_gt_atTop ( 4 / ε ) ] with x hx₁ hx₂
          rw [ dist_eq_norm ]
          norm_num [ L_x ]
          rw [ Nat.cast_sub ( show ⌈x / 2⌉₊ ≤ ⌊x⌋₊ from Nat.ceil_le.mpr <| by linarith [ Nat.lt_floor_add_one x ] ) ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ h_floor_ceil x hx₁, mul_div_cancel₀ ( ( ⌊x⌋₊ - ⌈x / 2⌉₊ : ℝ ) + 1 ) ( by linarith : x ≠ 0 ), mul_div_cancel₀ ( 4 : ℝ ) hε.ne' ]
        have h_term_zero : Filter.Tendsto (fun x => 2 * sum_S2 P x / x * (x / (L_x x : ℝ)) * (W_P P : ℝ)) Filter.atTop (nhds 0) := by
          have h_term_zero : Filter.Tendsto (fun x => 2 * sum_S2 P x / x * (x / (L_x x : ℝ))) Filter.atTop (nhds 0) := by
            convert Filter.Tendsto.mul ( ‹Filter.Tendsto ( fun x : ℝ => sum_S2 P x / x ) Filter.atTop ( nhds 0 ) ›.const_mul 2 ) ( h_term_zero.inv₀ <| by norm_num ) using 2 <;> ring_nf ; norm_num
            ring
          simpa using h_term_zero.mul_const _
        refine h_term_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hx.ne' ] )
      -- By combining the results from h_term_zero and h_bad_n_card_bound, we can find such an x₀.
      have h_combined : ∀ P ≥ P₀, ∃ x₀ : ℝ, ∀ x ≥ x₀, (L_x x : ℝ) / W_P P * (tail_val P) + 2 * sum_S2 P x < (L_x x : ℝ) / W_P P - 2 := by
        intro P hP
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, 2 * sum_S2 P x / ((L_x x : ℝ) / W_P P) < 1 / 4 := by
          exact Filter.eventually_atTop.mp ( h_term_zero P hP |> fun h => h.eventually ( gt_mem_nhds <| by norm_num ) )
        -- Choose x₀ such that for all x ≥ x₀, (L_x x : ℝ) / W_P P > 8.
        obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x ≥ x₁, (L_x x : ℝ) / W_P P > 8 := by
          have hL_x_growth : Filter.Tendsto (fun x => (L_x x : ℝ)) Filter.atTop Filter.atTop := by
            refine tendsto_natCast_atTop_atTop.comp ?_
            refine Filter.tendsto_atTop_atTop.mpr ?_
            intro b
            use 2 * b + 2
            intro a ha
            unfold L_x
            exact Nat.le_succ_of_le ( Nat.le_sub_of_add_le <| Nat.le_floor <| by norm_num; linarith [ Nat.ceil_lt_add_one <| show 0 ≤ a / 2 by linarith ] )
          exact Filter.eventually_atTop.mp ( hL_x_growth.eventually_gt_atTop ( 8 * W_P P ) ) |> fun ⟨ x₁, hx₁ ⟩ ↦ ⟨ x₁, fun x hx ↦ by rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| Finset.prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) ] ; linarith [ hx₁ x hx ] ⟩
        exact ⟨ Max.max x₀ x₁, fun x hx => by have := hx₀ x ( le_trans ( le_max_left _ _ ) hx ) ; have := hx₁ x ( le_trans ( le_max_right _ _ ) hx ) ; rw [ div_lt_iff₀ ] at * <;> nlinarith [ hP₀ P hP ] ⟩
      use P₀
      intros P hP
      obtain ⟨x₀, hx₀⟩ := h_combined P hP
      use x₀ + 2
      intro x hx
      have h_card_bound : (bad_n_total P x (W_P P)).card ≤ (L_x x : ℝ) / W_P P * sum_S1 P x + 2 * sum_S2 P x := by
        apply_rules [ bad_n_card_bound ]
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
        · intros p hp
          have h_coprime : Nat.Coprime (∏ p ∈ Finset.filter Nat.Prime (Finset.range (P + 1)), p^2) (p^2) := by
            simp +zetaDelta at *
            exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.pow_left 2 <| Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Finset.mem_filter.mp hp |>.2.1 ) |>.2 fun h => by have := Nat.le_of_dvd ( Nat.pos_of_ne_zero <| by aesop ) h; linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hq |>.1 ), Finset.mem_filter.mp hp |>.2.2 ]
          exact h_coprime
      have h_card_S_x : (S_x x (W_P P)).card ≥ (L_x x : ℝ) / W_P P - 2 := by
        have := card_S_x_bound x ( W_P P ) ?_ <;> norm_num at *
        · linarith [ abs_le.mp this ]
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
      have h_final : (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card := by
        have h_final : (L_x x : ℝ) / W_P P * sum_S1 P x + 2 * sum_S2 P x < (L_x x : ℝ) / W_P P - 2 := by
          exact lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left ( sum_S1_le_tail P x assumps ) ( by positivity ) ) le_rfl ) ( hx₀ x ( by linarith ) )
        exact_mod_cast h_card_bound.trans_lt ( h_final.trans_le h_card_S_x )
      exact h_final

/-
For $p \ge 20$, if $a \le p / (\log \log p)^2$, then $a < p$.
-/
lemma a_lt_p (p : ℕ) (a : ℕ) (hp : p ≥ 20) (ha_bound : (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2) : a < p := by
  -- Since $p \geq 20$, we have $\log \log p > 1$, thus $(\log \log p)^2 > 1$.
  have h_log_log_p_gt_1 : 1 < (Real.log (Real.log p)) := by
    rw [ Real.lt_log_iff_exp_lt ( Real.log_pos <| by norm_cast; linarith ) ]
    rw [ Real.lt_log_iff_exp_lt ]
    all_goals
      norm_num
    all_goals
      try linarith
    have := Real.exp_one_lt_d9.le
    -- We'll use that $e^e < 16$ to conclude the proof.
    have h_exp_exp_lt_16 : Real.exp (Real.exp 1) < 16 := by
      rw [ ← Real.log_lt_log_iff ( by positivity ) ]
      all_goals
        norm_num
      rw [ show ( 16 : ℝ ) = ( 2 ^ 4 ) by norm_num, Real.log_pow ]
      norm_num
      exact lt_of_le_of_lt this ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith )
    exact h_exp_exp_lt_16.trans_le ( mod_cast by linarith )
  exact_mod_cast ( by rw [ le_div_iff₀ ( by positivity ) ] at ha_bound; nlinarith [ show ( p :ℝ ) ≥ 20 by norm_cast, show ( Real.log ( Real.log p ) ^ 2 :ℝ ) > 1 by exact one_lt_pow₀ h_log_log_p_gt_1 ( by norm_num ) ] : ( a :ℝ ) < p )

/-
If $p \le \sqrt{2x}$ and the bad condition holds, then $n$ is in `bad_n_total`.
-/
lemma bad_implies_mem_bad_n_total_of_le_sqrt
  (n : ℕ) (x : ℝ) (P : ℕ) (hn : n ∈ S_x x (W_P P)) (p : ℕ) (hp_prime : Nat.Prime p) (hp_gt : p > P) (hp_le : (p : ℝ) ≤ Real.sqrt (2 * x))
  (a : ℕ) (ha_pos : 1 ≤ a) (ha_bound : (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2) (h_div : (n + a) % p^2 = 0) :
  n ∈ bad_n_total P x (W_P P) := by

  -- Extract 0 ≤ 2 * x from hp_le
  have hx2 : 0 ≤ 2 * x := by
    by_contra hneg
    have hneg' : 2 * x ≤ 0 := le_of_lt (lt_of_not_ge hneg)
    have hsqrt : Real.sqrt (2 * x) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hneg'
    have hp_pos : (0 : ℝ) < p := by
      exact_mod_cast hp_prime.pos
    have : (p : ℝ) ≤ 0 := by
      simpa [hsqrt] using hp_le
    exact (not_le_of_gt hp_pos) this

  exact Finset.mem_biUnion.mpr
    ⟨ (p, a),
      Finset.mem_biUnion.mpr
        ⟨ p,
          Finset.mem_filter.mpr
            ⟨ Finset.mem_range.mpr
                (Nat.lt_succ_of_le
                  (Nat.le_floor <|
                    by
                      nlinarith [Real.mul_self_sqrt hx2])),
              hp_prime,
              hp_gt ⟩,
          Finset.mem_image.mpr
            ⟨ a,
              Finset.mem_Icc.mpr ⟨ ha_pos, Nat.le_floor ha_bound ⟩,
              rfl ⟩ ⟩,
      by
        unfold bad_n_for_pair
        aesop ⟩

/-
If n is in S_x, it satisfies condition (a).
-/
lemma lemma_condition_a_of_mem_Sx (P : ℕ) (x : ℝ) (n : ℕ)
    (hn_mem : n ∈ S_x x (W_P P)) :
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) := by
      intro p pp pP
      exact Nat.mod_eq_zero_of_dvd ( dvd_trans ( by exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), pp ⟩ ) |> fun h => dvd_trans ( by norm_num ) h ) ( Nat.dvd_of_mod_eq_zero <| Finset.mem_filter.mp hn_mem |>.2 ) )

/-
If n is not in bad_n_total, then for small p, condition (b) holds.
-/
lemma lemma_condition_b_small_p (P : ℕ) (x : ℝ) (n : ℕ)
    (hn_mem : n ∈ S_x x (W_P P))
    (hn_not_bad : n ∉ bad_n_total P x (W_P P)) :
    (∀ p, Nat.Prime p → p > P → (p : ℝ) ≤ Real.sqrt (2 * x) →
     ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
  intros p hp_prime hp_gt hp_le a ha_pos ha_bound h_div
  apply hn_not_bad
  apply bad_implies_mem_bad_n_total_of_le_sqrt n x P hn_mem p hp_prime hp_gt hp_le a ha_pos ha_bound h_div

/-
If n is in S_x and x is large enough, then for large p, condition (b) holds.
-/
lemma lemma_condition_b_large_p (P : ℕ) (x : ℝ) (n : ℕ)
    (hx : x ≥ 200)
    (hn_mem : n ∈ S_x x (W_P P)) :
    (∀ p, Nat.Prime p → p > P → (p : ℝ) > Real.sqrt (2 * x) →
     ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
       intros p hp_prime hp_gt hp_gt_sqrt a ha_pos ha_bound
       have h_n_lt_x : n < p^2 := by
         have h_n_lt_x : n ≤ x := by
           exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn_mem |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity
         exact_mod_cast ( by nlinarith [ Real.sqrt_nonneg ( 2 * x ), Real.mul_self_sqrt ( show 0 ≤ 2 * x by positivity ) ] : ( n : ℝ ) < p ^ 2 )
       have h_a_lt_p : a < p := by
         by_cases hp : p ≥ 20
         · exact a_lt_p p a hp ha_bound
         · interval_cases p <;> norm_num at *
           all_goals rw [ ← Real.sqrt_mul <| by positivity ] at hp_gt_sqrt; rw [ Real.sqrt_lt' <| by positivity ] at hp_gt_sqrt; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
       have h_n_a_lt_p_sq : n + a < p^2 := by
         have h_n_a_lt_p_sq : n ≤ x := by
           exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn_mem |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity
         exact_mod_cast ( by nlinarith [ Real.sqrt_nonneg ( 2 * x ), Real.mul_self_sqrt ( show 0 ≤ 2 * x by positivity ), show ( p : ℝ ) ≥ a + 1 by norm_cast ] : ( n : ℝ ) + a < p ^ 2 )
       exact (by
       rw [ Nat.mod_eq_of_lt ]
       all_goals
         linarith [ show n + a > 0 from by linarith ])

/-
If the number of bad n is less than the size of S_x, then there exists a good n satisfying conditions (a) and (b).
-/
lemma lemma_exists_good_n_if_card_lt (P : ℕ) (x : ℝ) (hx : x ≥ 200)
    (h_card : (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card) :
    ∃ n ∈ S_x x (W_P P),
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧
    (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
  have h_exists : ∃ n, n ∈ S_x x (W_P P) ∧ n ∉ bad_n_total P x (W_P P) := by
    by_contra h
    push Not at h
    have h_subset : S_x x (W_P P) ⊆ bad_n_total P x (W_P P) := fun n hn => h n hn
    have h_le : (S_x x (W_P P)).card ≤ (bad_n_total P x (W_P P)).card := Finset.card_le_card h_subset
    linarith
  obtain ⟨n, hn_mem, hn_not_bad⟩ := h_exists
  use n
  constructor
  · exact hn_mem
  · constructor
    · apply lemma_condition_a_of_mem_Sx
      assumption
    · intros p hp hp_gt a ha_pos ha_bound
      by_cases hp_le : (p : ℝ) ≤ Real.sqrt (2 * x)
      · apply lemma_condition_b_small_p P x n hn_mem hn_not_bad p hp hp_gt hp_le a ha_pos ha_bound
      · apply lemma_condition_b_large_p P x n hx hn_mem p hp hp_gt (lt_of_not_ge hp_le) a ha_pos ha_bound

/-
For any sufficiently large $P \ge 3$, there exist arbitrarily large natural numbers $n$ such that
(a) $n \equiv 0 \pmod{p^2}$ whenever $p \leq P$
and
(b) $n + a \not \equiv 0 \pmod{p^2}$ whenever $p>P$ and $1 \leq a \leq \frac{p}{(\log\log p)^2}$.
-/
lemma lemma_largeP (assumps : SieveAssumptions) :
    ∃ P₀ ≥ 3, ∀ P ≥ P₀, ∀ M : ℕ, ∃ n ≥ M,
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧
    (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
      obtain ⟨ P₀, hP₀ ⟩ := large_P_bound_satisfied assumps
      refine ⟨ P₀ + 3, by linarith, fun P hP M => ?_ ⟩
      obtain ⟨ x₀, hx₀ ⟩ := hP₀ P ( by linarith )
      -- Choose $x$ large enough such that $x \geq \max(x₀, \max(200, 2M))$.
      obtain ⟨ x, hx₁, hx₂ ⟩ : ∃ x : ℝ, x ≥ x₀ ∧ x ≥ 200 ∧ x ≥ 2 * M := by
        exact ⟨ Max.max x₀ ( Max.max 200 ( 2 * M ) ), le_max_left _ _, le_max_of_le_right ( le_max_left _ _ ), le_max_of_le_right ( le_max_right _ _ ) ⟩
      obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := lemma_exists_good_n_if_card_lt P x hx₂.1 ( hx₀ x hx₁ )
      exact ⟨ n, Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.ceil_le.mp <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn₁ |>.1 ) |>.1 ] }, hn₂, hn₃ ⟩

/-
There exists a strictly increasing sequence n_j satisfying the conditions (a) and (b) with respect to P_seq K j.
-/
def P_seq (K j : ℕ) : ℕ := Nat.floor ((K : ℝ) * Real.exp (Real.exp j))

/-
The set A defined by the sequence n has property P_bar.
-/
def A_seq (n : ℕ → ℕ) : Set ℕ := { a | ∀ j, Squarefree (n j + a) }

lemma PropertyP_bar_A_seq (n : ℕ → ℕ) (h_mono : StrictMono n) : PropertyP_bar (A_seq n) := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  have := h_mono.id_le ( a + 1 )
  aesop

/-
If p > P_seq K j, then j < log log p.
-/
lemma P_seq_growth (K j : ℕ) (hK : K ≥ 3) (p : ℕ) (hp : p > P_seq K j) :
    (j : ℝ) < Real.log (Real.log p) := by
      -- Since $p > P_seq K j$, we have $p > K \exp(\exp(j))$.
      have hp_gt_exp_exp_j : (p : ℝ) > (K : ℝ) * Real.exp (Real.exp j) := by
        contrapose! hp
        exact Nat.le_floor <| mod_cast hp
      -- Since $p > K \exp(\exp(j))$, we have $\log p > \log (K \exp(\exp(j))) = \log K + \exp(j)$.
      have h_log_p : Real.log p > Real.log K + Real.exp j := by
        simpa [ Real.log_mul ( by positivity : ( K : ℝ ) ≠ 0 ) ( by positivity : Real.exp ( Real.exp j ) ≠ 0 ) ] using Real.log_lt_log ( by positivity ) hp_gt_exp_exp_j
      rw [ Real.lt_log_iff_exp_lt ]
      · linarith [ Real.log_nonneg ( show ( K : ℝ ) ≥ 1 by norm_cast; linarith ) ]
      · exact lt_of_le_of_lt ( add_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( Real.exp_nonneg _ ) ) h_log_p

/-
If a <= x and a > p / (log log p)^2, then p <= 4 x (log log x)^2.
-/
def p_upper_bound (x : ℝ) : ℝ := 4 * x * (Real.log (Real.log x))^2

lemma p_bound_lemma_v2 (x : ℝ) (hx : x ≥ 100) (p : ℕ) (a : ℕ) (ha : a ≤ x)
    (h_ineq : (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2) :
    (p : ℝ) ≤ p_upper_bound x := by
      unfold p_upper_bound
      -- Assume $f(Y) > x$.
      have h_fY_gt_x : (4 * x * (Real.log (Real.log x))^2 : ℝ) / (Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)))^2 > x := by
        -- We'll use that $Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)) \leq Real.log (Real.log x) + Real.log 4$.
        have h_log_bound : Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)) ≤ Real.log (Real.log x) + Real.log 4 := by
          rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.log_pos <| by linarith ) ( by positivity ) ]
          gcongr
          · refine Real.log_pos ?_
            -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10$. Therefore, $\log (\log x) \geq \log (2 \log 10)$.
            have h_log_log_x_ge_log_2_log_10 : Real.log (Real.log x) ≥ Real.log (2 * Real.log 10) := by
              exact Real.log_le_log ( by positivity ) ( by rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> linarith )
            have h_log_log_x_sq_gt_1 : Real.log (2 * Real.log 10) > 1 := by
              rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ]
              · exact lt_of_le_of_lt ( Real.exp_one_lt_d9.le ) ( by have := Real.log_two_gt_d9; norm_num1 at *; rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.log_mul ] <;> norm_num ; have := Real.log_lt_log ( by norm_num ) ( by norm_num : ( 5 : ℝ ) > 2 ) ; norm_num at * ; linarith )
              · positivity
            nlinarith
          · rw [ Real.log_le_iff_le_exp ( by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ]
            rw [ Real.exp_mul, Real.exp_log ( by positivity ) ]
            -- We'll use that $Real.log (Real.log x) \leq Real.log x$ for $x \geq 100$.
            have h_log_bound : Real.log (Real.log x) ≤ Real.log x := by
              exact le_trans ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by linarith ) ) ) ( by linarith )
            -- We'll use that $Real.log x \leq x^{1/2}$ for $x \geq 100$.
            have h_log_sqrt : Real.log x ≤ x^(1/2 : ℝ) := by
              rw [ ← Real.sqrt_eq_rpow ]
              have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt x / 2 )
              rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this
              have := Real.log_two_lt_d9
              norm_num at *
              linarith
            refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) h_log_bound 2 ) <| by positivity ) ?_
            refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| by linarith ) h_log_sqrt 2 ) <| by positivity ) ?_ ; ring_nf ; norm_num
            rw [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ]
            all_goals
              nlinarith [ pow_le_pow_left₀ ( by positivity ) hx 3 ]
        -- Substitute the bound into the inequality.
        have h_subst : 4 * x * (Real.log (Real.log x))^2 / (Real.log (Real.log x) + Real.log 4)^2 > x := by
          -- We'll use that $Real.log (Real.log x) > Real.log 4$ for $x \geq 100$.
          have h_log_log_x_gt_log_4 : Real.log (Real.log x) > Real.log 4 := by
            gcongr
            rw [ Real.lt_log_iff_exp_lt ( by positivity ) ]
            have := Real.exp_one_lt_d9.le
            norm_num1 at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num; linarith )
          rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ show 0 < x by positivity, show 0 < Real.log ( Real.log x ) by exact Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith, show 0 < Real.log 4 by positivity, mul_lt_mul_of_pos_left h_log_log_x_gt_log_4 <| show 0 < x by positivity ]
        refine lt_of_lt_of_le h_subst ?_
        gcongr
        · refine sq_pos_of_pos ( Real.log_pos ?_ )
          rw [ Real.lt_log_iff_exp_lt ]
          · -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10 \approx 4.605$.
            have h_log_x : Real.log x ≥ 4 := by
              rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ]
              exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num ) ) hx
            exact lt_of_lt_of_le ( Real.exp_one_lt_d9.trans_le ( by norm_num ) ) ( mul_le_mul ( mul_le_mul_of_nonneg_left hx ( by norm_num ) ) ( pow_le_pow_left₀ ( by positivity ) ( show Real.log ( Real.log x ) ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) 2 ) ( by positivity ) ( by positivity ) )
          · exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) )
        · refine Real.log_nonneg ?_
          rw [ Real.le_log_iff_exp_le ( by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ]
          have h_exp_log : Real.log (Real.log x) ≥ 1 / 2 := by
            have h_log_bound : Real.log x ≥ 4 := by
              rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ]
              exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num ) ) hx
            exact le_trans ( Real.log_two_gt_d9.le.trans' <| by norm_num ) ( Real.log_le_log ( by norm_num ) <| show Real.log x ≥ 2 by linarith )
          have := Real.exp_one_lt_d9.le
          norm_num at *
          nlinarith [ Real.add_one_le_exp 1 ]
      -- If $p > Y$, then $f(p) \ge f(Y) > x$, since $f(t)$ is increasing for $t \ge 100$.
      have h_f_p_ge_f_Y : ∀ t₁ t₂ : ℝ, 100 ≤ t₁ → t₁ ≤ t₂ → (t₁ / (Real.log (Real.log t₁))^2 : ℝ) ≤ (t₂ / (Real.log (Real.log t₂))^2 : ℝ) := by
        -- To show that $f(t)$ is increasing for $t \geq 100$, we can compute its derivative and show that it is positive.
        have h_deriv_pos : ∀ t : ℝ, 100 ≤ t → deriv (fun t => t / (Real.log (Real.log t))^2) t > 0 := by
          intro t ht
          have h_deriv_pos : deriv (fun t => t / (Real.log (Real.log t))^2) t = (1 / (Real.log (Real.log t))^2) * (1 - 2 / (Real.log t * Real.log (Real.log t))) := by
            have ht_ne : t ≠ 0 := by linarith
            have hlog_ne : Real.log t ≠ 0 := by
              exact ne_of_gt <| Real.log_pos <| by linarith
            have hloglog_ne : Real.log (Real.log t) ≠ 0 := by
              exact ne_of_gt <| Real.log_pos <| show 1 < Real.log t by
                rw [Real.lt_log_iff_exp_lt]
                all_goals
                  linarith [Real.exp_one_lt_d9]
            convert HasDerivAt.deriv
              (HasDerivAt.div (hasDerivAt_id t)
                ((HasDerivAt.log (Real.hasDerivAt_log ht_ne) hlog_ne).pow 2)
                (pow_ne_zero 2 hloglog_ne)) using 1
            · rfl
            · change
                1 / Real.log (Real.log t) ^ 2 *
                    (1 - 2 / (Real.log t * Real.log (Real.log t))) =
                  (1 * Real.log (Real.log t) ^ 2 -
                        t * (2 * Real.log (Real.log t) ^ (2 - 1) *
                          (t⁻¹ / Real.log t))) /
                    (Real.log (Real.log t) ^ 2) ^ 2
              field_simp [ht_ne, hlog_ne, hloglog_ne]
              ring
          refine h_deriv_pos.symm ▸ mul_pos ( one_div_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log t from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ( sub_pos.mpr ?_ )
          rw [ div_lt_iff₀ ]
          all_goals
            norm_num
          · have h_log_log_t : Real.log t > 4 := by
              rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ( by positivity ) ]
              have := Real.exp_one_lt_d9.le
              norm_num1 at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num; linarith )
            nlinarith [ show 1 < Real.log ( Real.log t ) from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ]
          · exact mul_pos ( Real.log_pos ( by linarith ) ) ( Real.log_pos ( show 1 < Real.log t from by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) )
        intros t₁ t₂ ht₁ ht₂
        by_contra h_contra
        push Not at h_contra
        have := exists_deriv_eq_slope ( fun t => t / Real.log ( Real.log t ) ^ 2 ) ( show t₁ < t₂ from ht₂.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at this
        exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos t <| by linarith [ ht.1 ] ) ( by exact fun t ht => DifferentiableAt.differentiableWithinAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos t <| by linarith [ ht.1 ] ) ) ( by rintro ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ ; rw [ eq_div_iff ] at h₃ <;> nlinarith [ h_deriv_pos c <| by linarith ] )
      contrapose! h_ineq
      refine le_trans ?_ ( h_f_p_ge_f_Y _ _ ?_ h_ineq.le )
      · linarith
      · -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10$.
        have h_log_x_ge_2_log_10 : Real.log x ≥ 2 * Real.log 10 := by
          rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ]
          all_goals
            norm_num
          all_goals
            linarith
        -- Since $\log 10 \approx 2.3026$, we have $2 \log 10 \approx 4.6052$.
        have h_log_10_approx : Real.log 10 > 2 := by
          norm_num [ Real.lt_log_iff_exp_lt ]
          have := Real.exp_one_lt_d9.le
          norm_num1 at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ]
        nlinarith [ show 1 ≤ Real.log ( Real.log x ) from by rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ]

/-
The number of indices j such that P_j < p is at most log log p + 1.
-/
def relevant_indices (K p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun j => P_seq K j < p)

lemma card_relevant_indices_bound (K p : ℕ) (hK : K ≥ 3) (hp : p > K) :
    (relevant_indices K p).card ≤ Real.log (Real.log p) + 1 := by
      -- The set of relevant indices is a subset of {0, 1, ..., ⌊log log p⌋}.
      have h_subset : relevant_indices K p ⊆ Finset.range (Nat.floor (Real.log (Real.log p)) + 1) := by
        intro j hj
        have := P_seq_growth K j hK p ( Finset.mem_filter.mp hj |>.2 )
        exact Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor this.le ) )
      exact le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_subset ) <| by norm_num; linarith [ Nat.floor_le <| Real.log_nonneg <| show 1 ≤ Real.log p from by rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( p : ℝ ) ≥ 3 by norm_cast; linarith ] ]

/-
Definitions for the subset of [1, x] removed from A, and the bound on its size.
-/
def removed_subset (n : ℕ → ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun a => Squarefree a ∧ ∃ j, ¬ Squarefree (n j + a))

def bound_sum_term (x : ℝ) (p : ℕ) : ℝ := (Real.log (Real.log p) + 1) * (x / p^2 + 1)

def total_removed_bound (K : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), bound_sum_term x p

/-
The removed subset is contained in the union of bad_a_for_p over relevant primes.
-/
def relevant_primes_for_bound (K : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (p_upper_bound x) + 1)).filter (fun p => Nat.Prime p ∧ p > K)

def bad_a_for_p (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun a => ∃ j, P_seq K j < p ∧ (n j + a) % p^2 = 0)

/-
The number of bad a for a given p is bounded by the term in the sum.
-/
lemma card_bad_a_for_p_le (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (p : ℕ) (hK : K ≥ 3) (hp : p > K) (hx : x ≥ 0) :
  (bad_a_for_p n K x p).card ≤ bound_sum_term x p := by
    -- The set `bad_a_for_p` consists of $a \in [1, \lfloor x \rfloor]$ such that $a \pmod{p^2}$ belongs to the set of residues $R = \{ (-n_j) \pmod{p^2} \mid P_j < p \}$.
    set R := Finset.image (fun j => (-n j : ZMod (p^2))) (Finset.filter (fun j => P_seq K j < p) (Finset.range p)) with hR_def
    have hR_card : R.card ≤ Real.log (Real.log p) + 1 := by
      refine le_trans ( Nat.cast_le.mpr <| Finset.card_image_le ) ?_
      simpa [relevant_indices] using card_relevant_indices_bound K p hK hp
    -- For each residue $r \in R$, the number of $a \in [1, \lfloor x \rfloor]$ with $a \equiv r \pmod{p^2}$ is at most $\lfloor x \rfloor / p^2 + 1 \le x/p^2 + 1$.
    have h_residue_count : ∀ r ∈ R, ((Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])).card ≤ x / p^2 + 1 := by
      intros r hr
      have h_residue_count : ((Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])).card ≤ (Nat.floor x) / p^2 + 1 := by
        -- The set of integers in [1, floor(x)] that are congruent to r modulo p^2 is contained in the set {r + kp^2 | k = 0, 1, ..., floor(x)/p^2}.
        have h_subset : Finset.filter (fun a => a ≡ r.val [MOD p^2]) (Finset.Icc 1 (Nat.floor x)) ⊆ Finset.image (fun k => r.val + k * p^2) (Finset.range (Nat.floor x / p^2 + 1)) := by
          intro a ha
          simp_all +decide [ Nat.ModEq ]
          refine ⟨ a / p ^ 2, ?_, ?_ ⟩
          · exact Nat.div_le_div_right ha.1.2
          · linarith [ Nat.mod_add_div a ( p ^ 2 ), Nat.mod_eq_of_lt ( show r.val < p ^ 2 from by { haveI := Fact.mk ( show p ^ 2 > 1 from one_lt_pow₀ ( by linarith ) two_ne_zero ) ; exact ZMod.val_lt r } ) ]
        exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( by norm_num ) )
      refine le_trans ( Nat.cast_le.mpr h_residue_count ) ?_
      norm_num +zetaDelta at *
      rw [ le_div_iff₀ ( by norm_cast; nlinarith ) ]
      exact le_trans ( mod_cast Nat.div_mul_le_self _ _ ) ( Nat.floor_le hx )
    -- The set `bad_a_for_p` is a subset of the union of the sets of $a$ for each residue $r \in R$.
    have h_bad_subset_union : bad_a_for_p n K x p ⊆ Finset.biUnion R (fun r => (Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])) := by
      intro a ha
      obtain ⟨j, hj₁, hj₂⟩ : ∃ j, P_seq K j < p ∧ (n j + a) % p^2 = 0 := by
        unfold bad_a_for_p at ha
        aesop
      have h_residue : a ≡ (-n j : ZMod (p^2)).val [MOD p^2] := by
        simp_all +decide [ ← ZMod.val_natCast, Nat.ModEq ]
        simp_all +decide [ add_eq_zero_iff_eq_neg ]
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨j, by
        simp_all +decide [ P_seq ]
        contrapose! hj₁
        exact Nat.le_floor <| by nlinarith [ Real.add_one_le_exp j, Real.add_one_le_exp ( Real.exp j ), show ( p : ℝ ) ≤ j by norm_cast, show ( K : ℝ ) ≥ 3 by norm_cast ] ;, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by
      exact Nat.pos_of_ne_zero fun h => by
        have := Finset.mem_filter.mp ha
        aesop
        , by
        exact Finset.mem_filter.mp ha |>.1 |> Finset.mem_Icc.mp |>.2⟩, h_residue⟩⟩
    refine le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_bad_subset_union ) ?_
    refine le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) ?_
    push_cast [ bound_sum_term ]
    exact le_trans ( Finset.sum_le_sum h_residue_count ) ( by simpa [ mul_add ] using mul_le_mul_of_nonneg_right hR_card ( by positivity : 0 ≤ x / p ^ 2 + 1 ) )

/-
The total removed bound divided by x splits into two sums.
-/
def sum_part1 (K : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), (Real.log (Real.log p) + 1) / p^2

def sum_part2 (K : ℕ) (x : ℝ) : ℝ :=
  (1 / x) * ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), (Real.log (Real.log p) + 1)

lemma total_removed_bound_split (K : ℕ) (x : ℝ) (hx : x > 0) :
  total_removed_bound K x / x = sum_part1 K x + sum_part2 K x := by
    unfold total_removed_bound sum_part1 sum_part2
    rw [ div_eq_mul_inv, Finset.mul_sum _ _ _ ]
    rw [ Finset.sum_mul _ _ _ ]
    rw [ ← Finset.sum_add_distrib ]
    congr
    ext
    unfold bound_sum_term
    ring_nf
    simp +decide [ sq, mul_assoc, mul_comm x, hx.ne' ]

/-
Definition of the tail sum of the error term (log log p + 1) / p^2 for p > K.
-/
def tail_sum_loglog_sq (K : ℕ) : ℝ :=
  ∑' p, if p > K ∧ Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0

/-
The tail sum of (log log p + 1) / p^2 is summable.
-/
lemma tail_sum_loglog_sq_summable (K : ℕ) :
  Summable (fun p : ℕ => if p > K ∧ Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) := by
    have h_tail_sum_sq_summable : Summable (fun p : ℕ => if Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) := by
      -- We'll use the comparison test. Since \( \frac{\log \log p + 1}{p^2} \leq \frac{2 \log \log p}{p^2} \) for sufficiently large \( p \), and the series \( \sum_{p} \frac{\log \log p}{p^2} \) converges, it follows that \( \sum_{p} \frac{\log \log p + 1}{p^2} \) also converges.
      have h_comparison : Summable (fun p : ℕ => if Nat.Prime p then (Real.log (Real.log p)) / (p : ℝ)^2 else 0) := by
        have h_summable : Summable (fun p : ℕ => (Real.log (Real.log p)) / p^2) := by
          have h_log_log_bound : ∀ p : ℕ, p ≥ 3 → Real.log (Real.log p) ≤ p^(1/2 : ℝ) := by
            intro p hp
            have h_log_log_bound : Real.log (Real.log p) ≤ Real.sqrt p := by
              have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt p / Real.exp 1 by positivity )
              rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ), Real.log_exp ] at this
              nlinarith [ Real.add_one_le_exp 1, Real.sqrt_nonneg p, Real.sq_sqrt <| Nat.cast_nonneg p, mul_div_cancel₀ ( Real.sqrt p ) <| ne_of_gt <| Real.exp_pos 1, Real.log_le_sub_one_of_pos <| show 0 < Real.log p from Real.log_pos <| by norm_cast; linarith ]
            rwa [ Real.sqrt_eq_rpow ] at h_log_log_bound
          -- Using the bound $\log \log p \leq p^{1/2}$, we can show that $\frac{\log \log p}{p^2} \leq \frac{p^{1/2}}{p^2} = \frac{1}{p^{3/2}}$.
          have h_bound : ∀ p : ℕ, p ≥ 3 → (Real.log (Real.log p)) / p^2 ≤ 1 / p^(3/2 : ℝ) := by
            intro p hp
            convert div_le_div_of_nonneg_right ( h_log_log_bound p hp ) ( sq_nonneg _ ) using 1
            all_goals
              first
              | rfl
              | rw [ show ( p : ℝ ) ^ ( 3 / 2 : ℝ ) = p ^ ( 1 / 2 : ℝ ) * p by
                    rw [ ← Real.rpow_add_one ] <;> norm_num
                    linarith ]
                rw [ ← Real.sqrt_eq_rpow ]
                field_simp [show Real.sqrt (p : ℝ) ≠ 0 by positivity,
                  show (p : ℝ) ≠ 0 by positivity]
                rw [Real.sq_sqrt (Nat.cast_nonneg p)]
          rw [ ← summable_nat_add_iff 3 ]
          exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( Real.log_nonneg <| Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) <| sq_nonneg _ ) ( fun n => h_bound _ <| by linarith ) <| by simpa using summable_nat_add_iff 3 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by norm_num
        -- Since the original series is summable, and the new series is a subseries of it, the new series must also be summable.
        have h_subseries : Summable (fun p : ℕ => Real.log (Real.log p) / p^2) → Summable (fun p : ℕ => if Nat.Prime p then Real.log (Real.log p) / p^2 else 0) := by
          intro h_summable
          have h_subseries : Summable (fun p : ℕ => if Nat.Prime p then Real.log (Real.log p) / p^2 else 0) := by
            have h_abs : ∀ p : ℕ, abs ((if Nat.Prime p then Real.log (Real.log p) / p^2 else 0)) ≤ abs (Real.log (Real.log p) / p^2) := by
              intro p
              split_ifs
              all_goals
                norm_num
            -- Apply the comparison test with the original series.
            have h_comparison : Summable (fun p : ℕ => abs (Real.log (Real.log p) / p^2)) := by
              exact h_summable.abs
            -- Apply the comparison test with the original series to conclude that the subseries is summable.
            have h_comparison : Summable (fun p : ℕ => abs ((if Nat.Prime p then Real.log (Real.log p) / p^2 else 0))) := by
              exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) h_abs h_comparison
            exact h_comparison.of_abs
          convert h_subseries using 1
        exact h_subseries h_summable
      have h_comparison : Summable (fun p : ℕ => if Nat.Prime p then (1 : ℝ) / (p : ℝ)^2 else 0) := by
        exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
      convert h_comparison.add ‹Summable fun p : ℕ => if Nat.Prime p then Real.log ( Real.log p ) / p ^ 2 else 0› using 2
      ring_nf
      split_ifs
      all_goals
        ring
    rw [ ← summable_nat_add_iff ( K + 1 ) ] at *
    grind

/-
The partial sum `sum_part1` converges to the tail sum as x goes to infinity.
-/
lemma sum_part1_tendsto (K : ℕ) :
  Filter.Tendsto (fun x => sum_part1 K x) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
    -- By definition of `sum_part1` and `tail_sum_loglog_sq`, we can rewrite the limit expression.
    have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
      have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ p ≤ Nat.floor (p_upper_bound x) then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
        have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ p ≤ x then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
          have hpartial :
              Filter.Tendsto
                (fun x => ∑ p ∈ Finset.range (x + 1),
                  if p > K ∧ Nat.Prime p then
                    (Real.log (Real.log p) + 1) / (p : ℝ)^2
                  else 0)
                Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
            simpa [tail_sum_loglog_sq, Function.comp_def] using
              (tail_sum_loglog_sq_summable K).hasSum.tendsto_sum_nat.comp
                (Filter.tendsto_add_atTop_nat 1)
          refine hpartial.congr' ?_
          filter_upwards with x
          rw [tsum_eq_sum (s := Finset.range (x + 1))]
          · apply Finset.sum_congr rfl
            intro p hp
            have hpx : p ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
            by_cases hprime : Nat.Prime p
            · by_cases hK : K < p
              · simp [hprime, hK, hpx]
              · simp [hprime, hK]
            · simp [hprime]
          · intro p hp
            have hpx : ¬ p ≤ x := by
              simpa [Finset.mem_range, Nat.lt_succ_iff] using hp
            simp [hpx]
        generalize_proofs at *
        (
        refine h_tail_limit.comp ?_
        have h_p_upper_bound_inf : Filter.Tendsto (fun x : ℝ => 4 * x * (Real.log (Real.log x))^2) Filter.atTop Filter.atTop := by
          have h_p_upper_bound_inf : Filter.Tendsto (fun x : ℝ => x * (Real.log (Real.log x))^2) Filter.atTop Filter.atTop := by
            have h_log_log_sq_inf : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)^2) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) )
            exact Filter.tendsto_id.atTop_mul_atTop₀ h_log_log_sq_inf
          simpa only [ mul_assoc ] using h_p_upper_bound_inf.const_mul_atTop zero_lt_four
        exact tendsto_nat_floor_atTop.comp h_p_upper_bound_inf)
      refine h_tail_limit.congr' ?_
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx
      congr! 3
      rw [ Nat.le_floor_iff ( by exact mul_nonneg ( mul_nonneg zero_le_four ( by positivity ) ) ( sq_nonneg _ ) ) ]
    refine h_tail_limit.congr' ?_
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
    simp +decide [ sum_part1, p_upper_bound ]
    rw [ tsum_eq_sum ]
    · exact
        Eq.symm
          (Finset.sum_filter (fun a => Nat.Prime a ∧ K < a ∧ ↑a ≤ 4 * x * Real.log (Real.log x) ^ 2)
            fun a => (Real.log (Real.log ↑a) + 1) / ↑a ^ 2)
    · exact fun p hp => if_neg fun h => hp <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| by simpa using h.2.2

/-
The sum of log p for p <= x is O(x).
-/
lemma theta_bound :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) =O[Filter.atTop] (fun x => x) := by
    exact theta_bound_chebyshev

/-
The prime counting function pi(x) is O(x / log x).
-/
lemma pi_bound :
  (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ)) =O[Filter.atTop] (fun x => x / Real.log x) := by
    -- By definition of $pi(x)$, we know that $\pi(x) \leq \theta(x) / \log(\sqrt{x}) + \sqrt{x}$.
    have h_pi_le_theta : ∀ x : ℝ, x ≥ 100 → (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card ≤ (2 * (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p)) / Real.log x + Real.sqrt x := by
      intro x hx
      have h_pi_le_theta_step : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log (Real.sqrt x)) := by
        have h_pi_le_theta_step : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log (Real.sqrt x)) := by
          exact Finset.sum_le_sum fun p hp => Real.log_le_log ( Real.sqrt_pos.mpr <| by positivity ) <| by linarith [ Finset.mem_filter.mp hp ]
        exact h_pi_le_theta_step.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => by aesop ) fun _ _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop )
      -- The number of primes in the interval $(\sqrt{x}, x]$ is at least $\pi(x) - \pi(\sqrt{x})$.
      have h_prime_count : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), 1) ≥ (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card - (Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1))).card := by
        have h_prime_count : Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)) ⊇ Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1)) \ Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1)) := by
          simp +contextual [ Finset.subset_iff ]
          exact fun p hp₁ hp₂ hp₃ => ⟨ Nat.lt_of_floor_lt hp₃, Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hp₁ ) ⟩
        have := Finset.card_mono h_prime_count
        simp_all +decide [ Finset.card_sdiff ]
        exact this.trans ( add_le_add_right ( Finset.card_mono <| Finset.inter_subset_left ) _ )
      -- Since $\pi(\sqrt{x}) \leq \sqrt{x}$, we have $\pi(x) \leq \theta(x) / \log(\sqrt{x}) + \sqrt{x}$.
      have h_pi_le_theta_step2 : (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card ≤ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), 1) + Real.sqrt x := by
        have h_pi_le_theta_step2 : (Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1))).card ≤ Real.sqrt x := by
          refine le_trans ?_ ( Nat.floor_le <| Real.sqrt_nonneg x )
          exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter Nat.Prime ( Finset.range ( ⌊Real.sqrt x⌋₊ + 1 ) ) ⊆ Finset.Ico 2 ( ⌊Real.sqrt x⌋₊ + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2, Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) <| by simp +arith +decide
        norm_num at *
        exact le_trans ( Nat.cast_le.mpr h_prime_count ) ( by
          push_cast
          linarith )
      simp_all +decide [ Real.log_sqrt ( show 0 ≤ x by positivity ) ]
      exact le_trans h_pi_le_theta_step2 ( add_le_add_left ( by rw [ le_div_iff₀ ( show (0 : ℝ) < Real.log x from Real.log_pos ( by linarith ) ) ] ; linarith ) _ )
    -- From `theta_bound`, we know $\theta(x) = O(x)$.
    have h_theta_bound : (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) =O[Filter.atTop] (fun x => x) := by
      exact theta_bound
    -- Since $\sqrt{x} = o(x / \log x)$, we can conclude that $\pi(x) = O(x / \log x)$.
    have h_sqrt_o : (fun x => Real.sqrt x) =o[Filter.atTop] (fun x => x / Real.log x) := by
      -- We can simplify the expression $\frac{\sqrt{x} \cdot \log x}{x}$ to $\frac{\log x}{\sqrt{x}}$.
      suffices h_simplified : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) by
        rw [ Asymptotics.isLittleO_iff_tendsto' ]
        all_goals
          norm_num
        · grind
        · exact ⟨ 2, by rintro x hx ( rfl | rfl | rfl ) <;> norm_num at hx ⟩
      -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y => 2 * Real.log y / y) Filter.atTop (nhds 0) by
        have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ )
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring )
      -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
      suffices h_log_z : Filter.Tendsto (fun z => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [div_eq_mul_inv, mul_assoc, mul_comm] )
      norm_num
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 )
    -- By combining the results from h_pi_le_theta, h_theta_bound, and h_sqrt_o, we can conclude that the cardinality is O(x / log x).
    have h_card_O : (fun x => (2 * (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p)) / Real.log x) =O[Filter.atTop] (fun x => x / Real.log x) := by
      rw [ Asymptotics.isBigO_iff ] at *
      obtain ⟨ c, hc ⟩ := h_theta_bound
      use 2 * c
      filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂
      norm_num [ abs_div, abs_mul, abs_of_nonneg, Real.log_nonneg hx₂.le ] at *
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx₁ zero_le_two)
          (inv_nonneg.mpr (Real.log_nonneg hx₂.le))
    refine Asymptotics.IsBigO.trans ?_ ( h_card_O.add h_sqrt_o.isBigO )
    rw [ Asymptotics.isBigO_iff ]
    use 1
    filter_upwards [ Filter.eventually_ge_atTop 100 ] with x hx using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( add_nonneg ( div_nonneg ( mul_nonneg zero_le_two <| Finset.sum_nonneg fun _ _ => Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by aesop ) <| Real.log_nonneg <| by linarith ) <| Real.sqrt_nonneg _ ) ] ; linarith [ h_pi_le_theta x hx ]

/-
The sum of (log log p + 1) for p <= x is O(x log log x / log x).
-/
lemma sum_loglog_bound :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), (Real.log (Real.log p) + 1)) =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
    have h_sum_bound : (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ) * (Real.log (Real.log x) + 1)) =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
      have h_sum_bound : (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ)) =O[Filter.atTop] (fun x => x / Real.log x) := by
        exact pi_bound
      have h_mul_bound : (fun x => (Real.log (Real.log x) + 1)) =O[Filter.atTop] (fun x => Real.log (Real.log x)) := by
        norm_num [ Asymptotics.isBigO_iff ]
        exact ⟨ 2, Real.exp ( Real.exp 1 ), fun x hx => by rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log ( Real.log x ) ) <;> linarith [ show 1 ≤ Real.log ( Real.log x ) from by rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ] ; rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ] ⟩
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        h_sum_bound.mul h_mul_bound
    refine Asymptotics.IsBigO.trans ?_ h_sum_bound
    refine Asymptotics.isBigO_iff.mpr ?_
    refine ⟨ 1, Filter.eventually_atTop.mpr ⟨ 3, fun x hx => ?_ ⟩ ⟩
    norm_num
    refine le_trans
      ( Finset.abs_sum_le_sum_abs
        (fun i : ℕ => Real.log (Real.log (i : ℝ)) + 1)
        (Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1))) ) ?_
    refine le_trans
      (b := ∑ i ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)),
        |Real.log ( Real.log x ) + 1|)
      ( Finset.sum_le_sum fun i hi => ?_ ) ?_
    · rw [ abs_of_nonneg, abs_of_nonneg ]
      all_goals
        norm_num at *
      · exact Real.log_le_log ( Real.log_pos <| Nat.one_lt_cast.mpr hi.2.1.one_lt ) ( Real.log_le_log ( Nat.cast_pos.mpr hi.2.1.pos ) hi.2.2 )
      · exact add_nonneg ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) zero_le_one
      · by_cases hi' : i ≤ 2
        · interval_cases i <;> norm_num at *
          have := Real.log_two_gt_d9
          norm_num at *
          nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]
        · exact add_nonneg ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( i : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) zero_le_one
    · norm_num [ Finset.sum_filter ]
      exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_mono <| fun p hp => by aesop ) <| abs_nonneg _

/-
The ratio of log(p_upper_bound x) to log x tends to 1.
-/
lemma log_p_upper_bound_div_log_x_tendsto_one :
  Filter.Tendsto (fun x => Real.log (p_upper_bound x) / Real.log x) Filter.atTop (nhds 1) := by
    unfold p_upper_bound
    -- We can simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun x => (Real.log 4 + Real.log x + 2 * Real.log (Real.log (Real.log x))) / Real.log x) Filter.atTop (nhds 1) by
      refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring )
    -- We can use the fact that $\frac{\log(\log(\log(x)))}{\log(x)}$ tends to $0$ as $x$ tends to infinity.
    have h_log_log_log : Filter.Tendsto (fun x => Real.log (Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
      -- Let $y = \log x$, therefore the expression becomes $\frac{\log (\log y)}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y => Real.log (Real.log y) / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop )
      -- Let $z = \log y$, therefore the expression becomes $\frac{\log z}{e^z}$.
      suffices h_log_z : Filter.Tendsto (fun z => Real.log z / Real.exp z) Filter.atTop (nhds 0) by
        have := h_log_z.comp Real.tendsto_log_atTop
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] )
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      refine squeeze_zero_norm' ?_ this
      norm_num [ Real.exp_neg ]
      exact ⟨ 2, fun x hx => by rw [ ← div_eq_mul_inv ] ; gcongr ; rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith ) ) ] ; linarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < x ) ] ⟩
    have h_const : Filter.Tendsto (fun x : ℝ => Real.log 4 / Real.log x) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h_one : Filter.Tendsto (fun x : ℝ => Real.log x / Real.log x) Filter.atTop (nhds 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx
      exact (div_self (ne_of_gt (Real.log_pos hx))).symm
    have h_two :
        Filter.Tendsto
          (fun x : ℝ => 2 * (Real.log (Real.log (Real.log x)) / Real.log x))
          Filter.atTop (nhds 0) := by
      simpa using h_log_log_log.const_mul 2
    convert (h_const.add h_one).add h_two using 1
    · ext x
      ring
    · norm_num

/-
The limit of (log log x)^k / log x as x tends to infinity is 0.
-/
lemma log_log_pow_div_log_tendsto_zero (k : ℝ) :
  Filter.Tendsto (fun x => (Real.log (Real.log x))^k / Real.log x) Filter.atTop (nhds 0) := by
    -- Let $y = \log x$, so we deal with $\lim_{y \to \infty} \frac{(\log y)^k}{y}$.
    suffices h_log : Filter.Tendsto (fun y => (Real.log y) ^ k / y) Filter.atTop (nhds 0) by
      exact h_log.comp ( Real.tendsto_log_atTop )
    generalize_proofs at *
    (
    -- Let $z = \log y$, so we can rewrite the limit as $\lim_{z \to \infty} \frac{z^k}{e^z}$.
    suffices h_log : Filter.Tendsto (fun z => z ^ k / Real.exp z) Filter.atTop (nhds 0) by
      have := h_log.comp Real.tendsto_log_atTop
      generalize_proofs at *
      (
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] ))
    generalize_proofs at *
    (
    -- We can use the fact that the exponential function grows faster than any polynomial function.
    have h_exp_growth : Filter.Tendsto (fun z => z ^ k / Real.exp z) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun z => z ^ (⌈k⌉₊ : ℝ) / Real.exp z) Filter.atTop (nhds 0) := by
        simpa [ Real.exp_neg, div_eq_mul_inv ] using
          Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈k⌉₊ |> Filter.Tendsto.comp <| Filter.tendsto_id
      refine squeeze_zero_norm' ?_ this
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( by simpa using Real.rpow_le_rpow_of_exponent_le hx.le <| Nat.le_ceil k ) <| by positivity
    generalize_proofs at *
    (
    convert h_exp_growth using 1)))

/-
The asymptotic behavior of the term involving p_upper_bound.
-/
lemma p_upper_bound_term_asymptotics :
  (fun x => p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x) := by
    -- We can simplify the expression by dividing both sides by $x (\log \log x)^2$.
    suffices h_simplified : (fun x => Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => Real.log (Real.log x) / Real.log x) by
      have hpO : ( fun x => p_upper_bound x ) =O[Filter.atTop]
          ( fun x => x * ( Real.log ( Real.log x ) ) ^ 2 ) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨4, Filter.Eventually.of_forall fun x => ?_⟩
        simp [p_upper_bound, mul_assoc, mul_comm, mul_left_comm]
      simpa [div_eq_mul_inv, pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using
        h_simplified.mul hpO
    -- We know that $\log P(x) \sim \log x$ and $\log \log P(x) \sim \log \log x$.
    have h_log_P : Filter.Tendsto (fun x => Real.log (p_upper_bound x) / Real.log x) Filter.atTop (nhds 1) := by
      exact log_p_upper_bound_div_log_x_tendsto_one
    have h_log_log_P : Filter.Tendsto (fun x => Real.log (Real.log (p_upper_bound x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
      have h_log_log_P : Filter.Tendsto (fun x => Real.log (Real.log (p_upper_bound x) / Real.log x) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_log_P one_ne_zero ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) )
      have h_log_log_P : Filter.Tendsto (fun x => (Real.log (Real.log (p_upper_bound x) / Real.log x) + Real.log (Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
        simpa [ add_div ] using h_log_log_P.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ using by rw [ div_self <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ] )
      refine h_log_log_P.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, h_log_P.eventually ( lt_mem_nhds one_pos ) ] with x hx₁ hx₂ using by rw [ Real.log_div ( by aesop ) ( by linarith [ Real.log_pos hx₁ ] ) ] ; ring )
    have h_ratio : Filter.Tendsto (fun x => (Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) / (Real.log (Real.log x) / Real.log x)) Filter.atTop (nhds 1) := by
      convert h_log_log_P.mul ( h_log_P.inv₀ one_ne_zero ) using 2 <;> ring
    rw [ Asymptotics.isBigO_iff ]
    obtain ⟨ c, hc ⟩ := Metric.tendsto_atTop.mp h_ratio 1 zero_lt_one
    use 2
    filter_upwards [ Filter.eventually_ge_atTop c, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃; specialize hc x hx₁; rw [ Real.norm_eq_abs, Real.norm_eq_abs ] ; rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log ( Real.log ( p_upper_bound x ) ) / Real.log ( p_upper_bound x ) ) <;> cases abs_cases ( Real.log ( Real.log x ) / Real.log x ) <;> nlinarith [ abs_lt.mp hc, mul_div_cancel₀ ( Real.log ( Real.log ( p_upper_bound x ) ) / Real.log ( p_upper_bound x ) ) ( show ( Real.log ( Real.log x ) / Real.log x ) ≠ 0 from div_ne_zero ( ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith [ Real.add_one_le_exp 1 ] ) <| ne_of_gt <| Real.log_pos <| show 1 < x from by linarith [ Real.add_one_le_exp 1 ] ) ]

/-
p_upper_bound x tends to infinity as x tends to infinity.
-/
lemma p_upper_bound_tendsto_atTop : Filter.Tendsto p_upper_bound Filter.atTop Filter.atTop := by
  refine Filter.Tendsto.atTop_mul_atTop₀ ?_ ?_
  · exact Filter.tendsto_id.const_mul_atTop zero_lt_four
  · exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) )

/-
Definition of S_loglog(x) as the sum of (log log p + 1) for primes p <= x.
-/
def S_loglog (x : ℝ) : ℝ := ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), (Real.log (Real.log p) + 1)

/-
For any prime p, log(log p) + 1 is positive.
-/
lemma log_log_p_plus_one_pos (p : ℕ) (hp : Nat.Prime p) : Real.log (Real.log p) + 1 > 0 := by
  by_cases h₂ : p ≤ 2
  · interval_cases p <;> norm_num at *
    have := Real.log_two_gt_d9
    norm_num at *
    nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]
  · exact add_pos_of_nonneg_of_pos ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( p : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) zero_lt_one

/-
sum_part2 is bounded by (1/x) * S_loglog(p_upper_bound x).
-/
lemma sum_part2_le (K : ℕ) :
  ∀ᶠ x in Filter.atTop, sum_part2 K x ≤ (1/x) * S_loglog (p_upper_bound x) := by
    refine Filter.eventually_atTop.mpr ⟨ 800, fun x hx => ?_ ⟩
    unfold sum_part2 S_loglog
    gcongr
    · exact fun p hp₁ hp₂ => le_of_lt ( log_log_p_plus_one_pos p ( by aesop ) )
    · exact fun hp => hp.2

/-
S_loglog(x) is O(x log log x / log x).
-/
lemma S_loglog_is_BigO :
  S_loglog =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
  exact sum_loglog_bound

/-
sum_part2 is non-negative for large x.
-/
lemma sum_part2_nonneg (K : ℕ) : ∀ᶠ x in Filter.atTop, 0 ≤ sum_part2 K x := by
  refine Filter.eventually_atTop.mpr ⟨ 1, fun x hx => ?_ ⟩
  unfold sum_part2
  refine mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun p hp => ?_ )
  exact le_of_lt ( log_log_p_plus_one_pos p ( by aesop ) )

/-
The upper bound for sum_part2 has the correct asymptotic behavior.
-/
lemma bound_asymptotics :
  (fun x => (1/x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (Real.log (Real.log x))^3 / Real.log x) := by
    have h_sum_part2_le : (fun x => (1 / x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (1 / x) * (p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x))) := by
      have h_S_loglog_bound : S_loglog =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
        exact S_loglog_is_BigO
      apply_rules [ Asymptotics.IsBigO.mul, h_S_loglog_bound.comp_tendsto ]
      · exact Asymptotics.isBigO_refl _ _
      · exact Asymptotics.isBigO_refl _ _
      · exact p_upper_bound_tendsto_atTop
    refine h_sum_part2_le.trans ?_
    have h_sum_part2_le : (fun x => (p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) / x) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x * (1 / x)) := by
      have h_sum_part2_le : (fun x => p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x) := by
        exact p_upper_bound_term_asymptotics
      simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using h_sum_part2_le.mul ( Asymptotics.isBigO_refl ( fun x : ℝ => 1 / x ) Filter.atTop )
    have h_sum_part2_le' :
        (fun x => (1 / x) * (p_upper_bound x * Real.log (Real.log (p_upper_bound x)) /
          Real.log (p_upper_bound x))) =O[Filter.atTop]
          (fun x => x * (Real.log (Real.log x)) ^ 3 / Real.log x * (1 / x)) := by
      refine h_sum_part2_le.congr_left ?_
      intro x
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    refine h_sum_part2_le'.congr_right ?_
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]

/-
sum_part2 tends to 0 as x goes to infinity.
-/
lemma sum_part2_tendsto (K : ℕ):
  Filter.Tendsto (fun x => sum_part2 K x) Filter.atTop (nhds 0) := by
  have h1 : ∀ᶠ x in Filter.atTop, 0 ≤ sum_part2 K x := sum_part2_nonneg K
  have h2 : ∀ᶠ x in Filter.atTop, sum_part2 K x ≤ (1/x) * S_loglog (p_upper_bound x) := sum_part2_le K
  have h3 : (fun x => (1/x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (Real.log (Real.log x))^3 / Real.log x) := bound_asymptotics
  have h4 : Filter.Tendsto (fun x => (Real.log (Real.log x))^3 / Real.log x) Filter.atTop (nhds 0) := by
    convert log_log_pow_div_log_tendsto_zero 3 using 1
    norm_cast
  have h5 : Filter.Tendsto (fun x => (1/x) * S_loglog (p_upper_bound x)) Filter.atTop (nhds 0) := h3.trans_tendsto h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h5 h1 h2

/-
The density of the removed set converges to the tail sum.
-/
lemma total_removed_density (K : ℕ) :
  Filter.Tendsto (fun x => total_removed_bound K x / x) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
    rw [ Filter.tendsto_congr' ]
    focus
      convert Filter.Tendsto.add ( sum_part1_tendsto K ) ( sum_part2_tendsto K ) using 2
    · ring
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using total_removed_bound_split K x hx ▸ rfl

/-
The cardinality of A_seq intersected with [1, x] is at least the cardinality of SF intersected with [1, x] minus the cardinality of the removed subset.
-/
lemma card_A_seq_ge (n : ℕ → ℕ) (x : ℝ):
  ((A_seq n ∩ Set.Icc 1 (Nat.floor x)).ncard : ℝ) ≥ ((SF ∩ Set.Icc 1 (Nat.floor x)).ncard : ℝ) - (removed_subset n x).card := by
    rw [ ge_iff_le, sub_le_iff_le_add ]
    norm_cast
    rw [ ← Set.ncard_coe_finset ]
    have h_subset : (SF ∩ Set.Icc 1 ⌊x⌋₊) ⊆ (A_seq n ∩ Set.Icc 1 ⌊x⌋₊) ∪ (removed_subset n x) := by
      intro a ha
      -- If $a$ is in $A_seq n$, then it is in the first part of the union.
      by_cases ha_A : a ∈ A_seq n
      · exact Or.inl ⟨ ha_A, ha.2 ⟩
      · unfold A_seq removed_subset at *
        aesop
    exact le_trans ( Set.ncard_le_ncard h_subset ) ( Set.ncard_union_le _ _ )

/-
If f >= g - h eventually, and g -> Lg, h -> Lh, and f is bounded above, then liminf f >= Lg - Lh.
-/
lemma liminf_ge_limit_sub_limit {f g h : ℕ → ℝ} {Lg Lh : ℝ}
    (h_ge : ∀ᶠ n in Filter.atTop, f n ≥ g n - h n)
    (hg : Filter.Tendsto g Filter.atTop (nhds Lg))
    (hh : Filter.Tendsto h Filter.atTop (nhds Lh))
    (hf_bdd_above : Filter.IsBoundedUnder LE.le Filter.atTop f) :
    Filter.liminf f Filter.atTop ≥ Lg - Lh := by
      have h_liminf_ge : Filter.liminf (fun n => g n - h n) Filter.atTop ≤ Filter.liminf f Filter.atTop := by
        apply_rules [ Filter.liminf_le_liminf ]
        · exact Filter.Tendsto.isBoundedUnder_ge ( hg.sub hh )
        · exact Filter.IsBoundedUnder.isCoboundedUnder_ge hf_bdd_above
      refine le_trans ?_ h_liminf_ge
      rw [ Filter.Tendsto.liminf_eq ( hg.sub hh ) ]

/-
The sequence u_n converges to the expected limit.
-/
lemma u_tendsto (K : ℕ) :
  Filter.Tendsto (fun n : ℕ => ((SF ∩ Set.Icc 1 n).ncard : ℝ) / n - total_removed_bound K n / n) Filter.atTop (nhds (6 / Real.pi^2 - tail_sum_loglog_sq K)) := by
    have h_diff : Filter.Tendsto (fun n : ℕ => ((SF ∩ (Set.Icc 1 n)).ncard : ℝ) / n) Filter.atTop (nhds (6 / Real.pi^2)) := by
      have := @SF_density
      simpa [HasNaturalDensity] using this
    exact h_diff.sub ( total_removed_density K |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop )

/-
The tail sum of (log log p + 1) / p^2 for p > K tends to 0 as K goes to infinity.
-/
lemma tail_sum_loglog_sq_tendsto_zero : Filter.Tendsto tail_sum_loglog_sq Filter.atTop (nhds 0) := by
  convert tendsto_sum_nat_add fun n => ( Real.log ( Real.log ( n + 1 ) ) + 1 ) / ( n + 1 ) ^ 2 * ( if Nat.Prime ( n + 1 ) then 1 else 0 ) using 1
  ext
  rw [ Summable.tsum_eq_zero_add ]
  · norm_num
    · rw [ tail_sum_loglog_sq ]
      rw [ ← Summable.sum_add_tsum_nat_add ]
      rotate_left
      focus
        exact ‹_› + 1 + 1
      · convert tail_sum_loglog_sq_summable _ using 1
      · rw [ Finset.sum_eq_single ( ‹_› + 1 ) ] <;> norm_num
        focus
          ring_nf
        · grind +ring
        · intros
          omega
  · have h_summable : Summable (fun p : ℕ => (Real.log (Real.log p) + 1) / p^2 * (if Nat.Prime p then 1 else 0)) := by
      have := @tail_sum_loglog_sq_summable 0
      exact this.congr fun p => by cases p <;> aesop
    exact_mod_cast h_summable.comp_injective ( add_left_injective _ ) |> Summable.comp_injective <| add_left_injective _

/-
A sequence n is GoodSeqNat with respect to K if it is strictly increasing and satisfies the modular properties (a) and (b) with respect to P_seq K j, where a is a natural number.
-/
def GoodSeqNat (n : ℕ → ℕ) (K : ℕ) : Prop :=
  StrictMono n ∧
  (∀ j, ∀ p, Nat.Prime p → p ≤ P_seq K j → n j % p^2 = 0) ∧
  (∀ j, ∀ p, Nat.Prime p → p > P_seq K j → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n j + a) % p^2 ≠ 0)

lemma P_seq_ge_K (K j : ℕ) : P_seq K j ≥ K := by
  -- Since $K$ is a natural number, multiplying it by $e^{e^j}$ (which is greater than 1) will give a value that's at least $K$. Taking the floor of that value should still be at least $K$.
  have h_floor : (K : ℝ) * Real.exp (Real.exp j) ≥ K := by
    exact le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( Real.one_le_exp ( by positivity ) )
  exact Nat.le_floor h_floor

/-
Existence of GoodSeqNat given sufficiently large K.
-/
lemma exists_sequence_n_nat (K P₀ : ℕ) (hK : K ≥ P₀)
    (h_prop : ∀ P ≥ P₀, ∀ M, ∃ n ≥ M, (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧ (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0)) :
    ∃ n : ℕ → ℕ, GoodSeqNat n K := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ j, (∀ p : ℕ, Nat.Prime p → p ≤ P_seq K j → n j % p^2 = 0) ∧ (∀ p : ℕ, Nat.Prime p → P_seq K j < p → ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n j + a) % p^2 ≠ 0)) := by
        choose! f hf₁ hf₂ hf₃ using h_prop
        use fun j => Nat.recOn j ( f ( P_seq K 0 ) 0 ) fun j ih => f ( P_seq K ( j + 1 ) ) ( ih + 1 )
        refine ⟨ strictMono_nat_of_lt_succ fun j => ?_, fun j => ?_ ⟩
        · exact lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( hf₁ _ ( by linarith [ P_seq_ge_K K ( j + 1 ) ] ) _ )
        · cases j with
          | zero =>
            simp_all +decide
            refine ⟨
              fun p hp hp' => hf₂ (P_seq K 0)
                (le_trans hK (P_seq_ge_K K 0))
                0 p hp hp',
              fun p hp hp' a ha ha' => hf₃ (P_seq K 0)
                (le_trans hK (P_seq_ge_K K 0))
                0 p hp hp' a ha ha' ⟩
          | succ j =>
            simp_all +decide
            let m_j : ℕ := Nat.recOn (motive := fun _ => ℕ) j ( f ( P_seq K 0 ) 0 ) fun j ih => f ( P_seq K ( j + 1 ) ) ( ih + 1 )
            refine ⟨ fun p hp hp' => hf₂ (P_seq K (j + 1))
                (le_trans hK (P_seq_ge_K K (j + 1))) (m_j + 1) p hp hp',
              fun p hp hp' a ha ha' => hf₃ (P_seq K (j + 1))
                (le_trans hK (P_seq_ge_K K (j + 1))) (m_j + 1) p hp hp' a ha ha' ⟩
      exact ⟨ n, hn.1, fun j p hp hle => hn.2 j |>.1 p hp hle, fun j p hp hgt a ha₁ ha₂ => hn.2 j |>.2 p hp hgt a ha₁ ha₂ ⟩

lemma bad_prime_properties_nat (n : ℕ → ℕ) (K : ℕ) (h_good : GoodSeqNat n K) (j : ℕ) (a : ℕ)
    (ha_sf : Squarefree a) (h_not_sf : ¬ Squarefree (n j + a)) :
    ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a ∧ p > P_seq K j ∧ (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2 := by
      obtain ⟨ p, hp_prime, hp_sq, hp_div ⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a := by
        rw [ Nat.squarefree_iff_prime_squarefree ] at h_not_sf
        simpa [ sq ] using h_not_sf
      by_cases hp_le : p ≤ P_seq K j
      · have hp_div_n : p^2 ∣ n j := by
          exact h_good.2.1 j p hp_prime hp_le |> fun h => Nat.dvd_of_mod_eq_zero h
        have hp_div_a : p^2 ∣ a := by
          simpa [ ← hp_div ] using Nat.dvd_sub ( dvd_of_mul_right_eq _ hp_div.symm ) hp_div_n
        exact absurd ( ha_sf.squarefree_of_dvd hp_div_a ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop )
      · refine ⟨ p, hp_prime, hp_div.symm ▸ dvd_mul_right (p ^ 2) hp_sq, not_le.mp hp_le, ?_ ⟩
        have := h_good.2.2 j p hp_prime ( not_le.mp hp_le )
        exact not_le.mp fun h => this a ( Nat.pos_of_ne_zero fun ha => by subst ha; simp_all +decide ) h <| Nat.mod_eq_zero_of_dvd <| hp_div.symm ▸ dvd_mul_right _ _

/-
The removed subset is contained in the union of bad sets for relevant primes, using GoodSeqNat.
-/
lemma removed_subset_subset_union_nat (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (h_good : GoodSeqNat n K) (hx : x ≥ 100) :
  removed_subset n x ⊆ (relevant_primes_for_bound K x).biUnion (fun p => bad_a_for_p n K x p) := by
    -- Let $a \in removed\_subset\ n\ x$.
    intro a ha
    obtain ⟨j, hj⟩ := Finset.mem_filter.mp ha |>.2.2
    generalize_proofs at *
    (
    -- By `bad_prime_properties_nat`, there exists a prime $p$ such that $p^2 \mid n_j + a$, $p > P_{seq} K j$, and $a > p / (\log \log p)^2$.
    obtain ⟨p, hp_prime, hp_sq, hp_gt, ha_gt⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a ∧ p > P_seq K j ∧ (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2 := by
      apply bad_prime_properties_nat n K h_good j a (by
      exact Finset.mem_filter.mp ha |>.2.1) hj
    -- Since $a \le x$, we have $p / (\log \log p)^2 < x$.
    have hp_le : (p : ℝ) ≤ p_upper_bound x := by
      apply p_bound_lemma_v2 x hx p a (by
      exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;) (by
      exact ha_gt)
    generalize_proofs at *
    refine Finset.mem_biUnion.mpr ⟨ p, ?_, ?_ ⟩ <;> simp_all +decide
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor hp_le ) ), hp_prime, by linarith [ show K ≤ P_seq K j from Nat.le_floor <| by nlinarith [ Real.add_one_le_exp ( Real.exp j ), Real.add_one_le_exp j ] ] ⟩
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩, j, hp_gt, Nat.mod_eq_zero_of_dvd hp_sq ⟩)

/-
Bound on the size of the removed subset for GoodSeqNat.
-/
lemma removed_subset_card_le_nat (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (h_good : GoodSeqNat n K) (hx : x ≥ 100) (hK : K ≥ 3) :
  (removed_subset n x).card ≤ total_removed_bound K x := by
    unfold total_removed_bound
    rw [ show
      Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x)
        (Finset.range (⌊p_upper_bound x⌋₊ + 1)) =
      relevant_primes_for_bound K x by
        have hp_upper_nonneg : 0 ≤ p_upper_bound x := by
          unfold p_upper_bound
          nlinarith [sq_nonneg (Real.log (Real.log x))]
        ext p
        constructor
        · intro hp
          simp [relevant_primes_for_bound] at hp ⊢
          exact ⟨ hp.1, hp.2.1, hp.2.2.1 ⟩
        · intro hp
          simp [relevant_primes_for_bound] at hp ⊢
          exact ⟨ hp.1, hp.2.1, hp.2.2,
            le_trans (Nat.cast_le.mpr hp.1) (Nat.floor_le hp_upper_nonneg) ⟩ ]
    refine le_trans
      (b := ∑ p ∈ relevant_primes_for_bound K x,
        ((removed_subset n x ∩ bad_a_for_p n K x p).card : ℝ))
      ?_ ( Finset.sum_le_sum fun p hp => ?_ )
    · have h_card_le : (removed_subset n x).card ≤ (Finset.biUnion (relevant_primes_for_bound K x) (fun p => removed_subset n x ∩ bad_a_for_p n K x p)).card := by
        refine Finset.card_le_card ?_
        intro a ha
        have := removed_subset_subset_union_nat n K x h_good hx
        specialize this ha
        aesop
      refine le_trans ( Nat.cast_le.mpr h_card_le ) ?_
      exact_mod_cast (Finset.card_biUnion_le :
        (Finset.biUnion (relevant_primes_for_bound K x)
          (fun p => removed_subset n x ∩ bad_a_for_p n K x p)).card ≤
        ∑ p ∈ relevant_primes_for_bound K x,
          (removed_subset n x ∩ bad_a_for_p n K x p).card)
    · have hpK : p > K := by
        rw [ relevant_primes_for_bound ] at hp
        exact (Finset.mem_filter.mp hp).2.2
      refine le_trans ?_ ( card_bad_a_for_p_le n K x p hK hpK ( by linarith ) )
      exact_mod_cast Finset.card_le_card fun x hx => by aesop

/-
If n is a GoodSeqNat with respect to K, then the lower density of A_seq n is at least 6/pi^2 - tail_sum_loglog_sq K.
-/
lemma lowerDensity_A_seq_bound_nat (n : ℕ → ℕ) (K : ℕ) (hK : K ≥ 3) (h_good : GoodSeqNat n K) :
  lowerDensity (A_seq n) ≥ 6 / Real.pi^2 - tail_sum_loglog_sq K := by
    apply le_of_forall_gt_imp_ge_of_dense
    have := @liminf_ge_limit_sub_limit
    contrapose! this
    obtain ⟨ a, ha₁, ha₂ ⟩ := this
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    · use fun x => ( Set.ncard ( A_seq n ∩ Set.Icc 1 x ) : ℝ ) / x
    · use fun x => ( Set.ncard ( SF ∩ Set.Icc 1 x ) : ℝ ) / x - total_removed_bound K x / x
    · use fun x => 0
    · exact 6 / Real.pi ^ 2 - tail_sum_loglog_sq K
    · exact 0
    · filter_upwards [ Filter.eventually_gt_atTop 100 ] with x hx
      have := removed_subset_card_le_nat n K x h_good ( by norm_num; linarith ) ( by linarith )
      have := card_A_seq_ge n x
      norm_num [ Nat.floor_natCast ] at *
      rw [ ← add_div ]
      gcongr
      linarith
    · convert u_tendsto K using 1
    · exact tendsto_const_nhds
    · refine ⟨ ?_, ?_ ⟩
      · refine ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun x hx => ?_ ⟩ ⟩
        simp +zetaDelta at *
        exact div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard ( show A_seq n ∩ Set.Icc 1 x ⊆ Set.Icc 1 x from fun y hy => hy.2 ) ) ( by norm_num [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity )
      · simpa [lowerDensity] using lt_trans ha₁ ha₂
/-
If A has property P_bar_infty (in particular, if it has property P_bar), then its upper density is strictly less than 6/pi^2.
-/
theorem theorem_overp_i (A : Set ℕ) (h : PropertyP_bar_infty A) :
    upperDensity A < 6 / Real.pi^2 := by
      obtain ⟨ n₁, n₂, h₁, h₂ ⟩ := P_bar_infty_implies_pair A h
      -- By `upperDensity_finite_diff`, `upperDensity A = upperDensity A'`.
      have h_upperDensity_eq : upperDensity A = upperDensity {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)} := by
        apply upperDensity_finite_diff
        exact ⟨ h₂.subset fun x hx => by aesop, Set.finite_empty.subset fun x hx => by aesop ⟩
      -- Apply `sieve_strict_bound` to $A'$ with $C = n_2 - n_1$.
      have h_sieve : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b := by
        intro p hp
        use (p^2 - n₁ % p^2) % p^2
        refine ⟨ Nat.mod_lt (p ^ 2 - n₁ % p ^ 2) ( pow_pos hp.pos 2 ), fun a ha ha' => ?_ ⟩
        -- Since $a \equiv -n_1 \pmod{p^2}$, we have $n_1 + a \equiv 0 \pmod{p^2}$, which implies $p^2 \mid (n_1 + a)$.
        have h_div : p^2 ∣ (n₁ + a) := by
          rw [ Nat.dvd_iff_mod_eq_zero ]
          rw [ Nat.add_mod, ha' ]
          simp +decide [ Nat.add_sub_of_le ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ]
        exact absurd ( ha.2.1.squarefree_of_dvd h_div ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop )
      have h_sieve_strict : ∀ p, Nat.Prime p → p > n₂ - n₁ → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b1) ∧ (∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b2) := by
        intro p hp hp_gt
        use (p^2 - n₁ % p^2) % p^2, (p^2 - n₂ % p^2) % p^2
        refine ⟨ Nat.mod_lt (p ^ 2 - n₁ % p ^ 2) ( pow_pos hp.pos 2 ), Nat.mod_lt (p ^ 2 - n₂ % p ^ 2) ( pow_pos hp.pos 2 ), ?_, ?_, ?_ ⟩
        · intro h_mod_eq
          have h_div : p^2 ∣ (n₂ - n₁) := by
            have h_div : n₂ % p^2 = n₁ % p^2 := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
              rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ), Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] at h_mod_eq
              aesop
            rw [ ← Nat.mod_add_div n₂ ( p ^ 2 ), ← Nat.mod_add_div n₁ ( p ^ 2 ), h_div ]
            norm_num [ Nat.add_sub_add_left, ← mul_tsub ]
          nlinarith [ Nat.le_of_dvd ( Nat.sub_pos_of_lt h₁ ) h_div, Nat.sub_add_cancel h₁.le ]
        · intro a ha H
          have := Nat.mod_eq_of_lt ( show n₁ % p ^ 2 < p ^ 2 from Nat.mod_lt _ ( pow_pos hp.pos _ ) )
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
          -- Since $a \equiv -n₁ \pmod{p^2}$, we have $n₁ + a \equiv 0 \pmod{p^2}$, which contradicts the assumption that $n₁ + a$ is squarefree.
          have h_contradiction : p^2 ∣ (n₁ + a) := by
            rw [ ← ZMod.natCast_eq_zero_iff ]
            simp_all +decide [ Nat.cast_sub ( show n₁ % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ]
          have := ha.1.2.squarefree_of_dvd h_contradiction
          simp_all +decide [ sq, Nat.squarefree_mul_iff ]
        · intro a ha H
          have := Nat.mod_eq_of_lt ( show n₂ % p ^ 2 < p ^ 2 from Nat.mod_lt _ ( pow_pos hp.pos _ ) )
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]
          -- Since $a \equiv -n₂ \pmod{p^2}$, we have $n₂ + a \equiv 0 \pmod{p^2}$, which contradicts the assumption that $n₂ + a$ is squarefree.
          have h_contradiction : p^2 ∣ (n₂ + a) := by
            rw [ ← ZMod.natCast_eq_zero_iff ]
            simp_all +decide [ Nat.cast_sub ( show n₂ % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ]
          have := ha.2.2.squarefree_of_dvd h_contradiction
          simp_all +decide [ sq, Nat.squarefree_mul_iff ]
      exact h_upperDensity_eq.symm ▸ sieve_strict_bound _ _ h_sieve h_sieve_strict

/-
For any epsilon > 0, there exists a set A with property P_bar such that its
lower density is at least 6/pi^2 - epsilon, conditional on SieveAssumptions.
-/
theorem theorem_overp_ii_conditional (assumps : SieveAssumptions) :
    ∀ ε > 0, ∃ A : Set ℕ, PropertyP_bar A ∧ lowerDensity A ≥ 6 / Real.pi^2 - ε := by
      have := lemma_largeP assumps
      -- By `tail_sum_loglog_sq_tendsto_zero`, there exists $K_1$ such that for all $K \ge K_1$, `tail_sum_loglog_sq K < \epsilon`.
      have h_tail : ∀ ε > 0, ∃ K₁ : ℕ, ∀ K ≥ K₁, tail_sum_loglog_sq K < ε := by
        exact fun ε ε_pos => by
          rcases Metric.tendsto_atTop.mp ( tail_sum_loglog_sq_tendsto_zero ) ε ε_pos with ⟨ K₁, hK₁ ⟩
          exact ⟨ K₁, fun K hK => by linarith [ abs_lt.mp ( hK₁ K hK ) ] ⟩
      intro ε hε_pos
      obtain ⟨K₁, hK₁⟩ := h_tail ε hε_pos
      obtain ⟨P₀, hP₀_ge_3, hP₀⟩ := this
      set K := max K₁ (max P₀ 3) with hK_def
      obtain ⟨n, hn⟩ := exists_sequence_n_nat K P₀ (by
      exact le_max_of_le_right ( le_max_left _ _ )) hP₀
      generalize_proofs at *
      use A_seq n
      refine ⟨ ?_, ?_ ⟩
      · exact PropertyP_bar_A_seq n hn.1
      · refine le_trans ?_ ( lowerDensity_A_seq_bound_nat n K ?_ hn )
        · exact sub_le_sub_left ( le_of_lt ( hK₁ K ( le_max_left _ _ ) ) ) _
        · exact le_trans ( by linarith ) ( le_max_right _ _ ) |> le_trans ( le_max_right _ _ )

/-- Construction of SieveAssumptions from Chebyshev bounds. -/
theorem sieveAssumptionsFromChebyshev : SieveAssumptions :=
  ⟨tail_summable_from_chebyshev⟩

/-
For any ε > 0, there exists a set A with property P̄ whose lower density is at least 6/π² - ε.
-/
theorem theorem_overp_ii :
    ∀ ε > 0, ∃ A : Set ℕ, PropertyP_bar A ∧ lowerDensity A ≥ 6 / Real.pi^2 - ε :=
  theorem_overp_ii_conditional sieveAssumptionsFromChebyshev

#print axioms theorem_overp_i
-- 'Erdos1102c.theorem_overp_i' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms theorem_overp_ii
-- 'Erdos1102c.theorem_overp_ii' depends on axioms: [propext, Classical.choice, Quot.sound]

end
end Erdos1102c

/- ---------------------------------------------------------------------------- -/
/- Concatenated from ErdosProblem1102PropertyQFastGrowing.lean -/
namespace Erdos1102d


/-
We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_\infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Define a sequence to be admissible if if avoids at least one residue class modulo $p^2$ for every prime $p$. Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

There exists an absolute constant $C$ such that any admissible sequence $A = \{a_1 < a_2 < \cdots \}$ for which $a_j \ge \exp(C j/\log j)$ holds for infinitely many $j$, has property $Q$. In particular, the specific sequences $2^n \pm 1$ and $n! \pm 1$ all have property $Q$.

-/



open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable



noncomputable section

/-
A set A has property Q if for infinitely many n, n+a is squarefree for all a in A with a < n.
-/
def PropertyQ (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, a < n → Squarefree (n + a)}).Infinite

/-
A set A is admissible if for every prime p, there is a residue class mod p^2 that A avoids.
-/
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b

/-
Definitions of the sequences A1, A2, A3, A4 as sets of natural numbers.
-/
def A1 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j + 1}
def A2 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j - 1}
def A3 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = Nat.factorial j + 1}
def A4 : Set ℕ := {n | ∃ j : ℕ, j > 1 ∧ n = Nat.factorial j - 1}

/-
A set A satisfies the growth condition with constant C if a_j >= exp(C j / log j) for infinitely many j.
-/
def GrowthCondition (A : Set ℕ) (C : ℝ) : Prop :=
  ∃ᶠ j in Filter.atTop, (Nat.nth (· ∈ A) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j)

/-
The sequence A1 is admissible.
-/
lemma A1_admissible : Admissible A1 := by
  intro p hp
  by_cases h_cases : p = 2
  · use 0
    simp +decide [h_cases]
    rintro a ⟨ j, hj, rfl ⟩
    rcases j with ( _ | _ | j ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *
  · refine ⟨ 1, ?_, ?_ ⟩ <;> norm_num +zetaDelta at *
    · exact hp.one_lt
    · rintro a ⟨ j, hj₁, rfl ⟩
      intro H
      have := Nat.dvd_of_mod_eq_zero ( show ( 2 ^ j ) % p ^ 2 = 0 from Nat.mod_eq_zero_of_dvd <| ?_ )
      focus
        simp_all +decide
      · exact absurd ( hp.dvd_of_dvd_pow ( dvd_of_mul_left_dvd this ) ) ( by intro h; have := Nat.le_of_dvd ( by positivity ) h; interval_cases p <;> trivial )
      · exact ⟨ ( 2 ^ j + 1 ) / p ^ 2, by linarith [ Nat.mod_add_div ( 2 ^ j + 1 ) ( p ^ 2 ) ] ⟩

/-
The sequence A2 is admissible.
-/
lemma A2_admissible : Admissible A2 := by
  intro p hp
  by_cases h_cases : p = 2
  · use 2
    norm_num [ h_cases ]
    rintro a ⟨ j, hj₁, rfl ⟩
    rcases j with ( _ | _ | j ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *
    have : 4 ∣ 2^(j+2) := ⟨2^j, by ring⟩
    omega
  · use p^2 - 1
    refine ⟨ Nat.sub_lt ( pow_pos hp.pos 2 ) zero_lt_one, ?_ ⟩
    rintro a ⟨ j, hj, rfl ⟩
    intro h_mod
    have h_div : p^2 ∣ 2^j := by
      exact ⟨ ( 2 ^ j - 1 ) / p ^ 2 + 1, by linarith [ Nat.mod_add_div ( 2 ^ j - 1 ) ( p ^ 2 ), Nat.sub_add_cancel ( show 1 ≤ p ^ 2 from pow_pos hp.pos 2 ), Nat.sub_add_cancel ( show 1 ≤ 2 ^ j from Nat.one_le_pow _ _ ( by decide ) ) ] ⟩
    exact absurd ( hp.dvd_of_dvd_pow ( dvd_of_mul_left_dvd h_div ) ) ( by intro h; have := Nat.le_of_dvd ( by positivity ) h; interval_cases p <;> trivial )

/-
The sequence A3 is admissible.
-/
lemma A3_admissible : Admissible A3 := by
  intro p hp_prime
  by_cases hp_odd : p % 2 = 1
  · -- For odd primes p, the elements j! + 1 are congruent to 1 mod p^2 for all j >= 2p.
    have h_odd_primes : ∀ j ≥ 2 * p, (Nat.factorial j + 1) % p^2 = 1 := by
      intros j hj
      have h_factorial : p^2 ∣ Nat.factorial j := by
        have h_factorial : p^2 ∣ Nat.factorial (2 * p) := by
          have h_factorial : p^2 ∣ Nat.factorial p * Nat.factorial p := by
            simpa only [ sq ] using mul_dvd_mul ( Nat.dvd_factorial hp_prime.pos le_rfl ) ( Nat.dvd_factorial hp_prime.pos le_rfl )
          exact dvd_trans h_factorial ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by rw [ two_mul ] )
        exact dvd_trans h_factorial ( Nat.factorial_dvd_factorial hj )
      norm_num [ Nat.add_mod, Nat.mod_eq_zero_of_dvd h_factorial ]
      rw [ Nat.mod_eq_of_lt ( by nlinarith [ hp_prime.two_le ] ) ]
    -- Therefore, for odd primes p, A3 occupies at most 2p < p^2 residue classes modulo p^2 (the values for j < 2p, plus the value 1).
    have h_odd_primes_bound : Finset.card (Finset.image (fun j => (Nat.factorial j + 1) % p^2) (Finset.range (2 * p)) ∪ {1}) < p^2 := by
      refine lt_of_le_of_lt ( Finset.card_union_le
        (Finset.image (fun j => (Nat.factorial j + 1) % p^2) (Finset.range (2 * p)))
        {1} ) ?_
      exact lt_of_le_of_lt ( add_le_add ( Finset.card_image_le ) le_rfl ) ( by norm_num; nlinarith [ hp_prime.two_le, show p > 2 from lt_of_le_of_ne hp_prime.two_le ( Ne.symm <| by omega ) ] )
    -- Therefore, there exists a residue class modulo p^2 that A3 avoids.
    obtain ⟨b, hb⟩ : ∃ b < p^2, b ∉ Finset.image (fun j => (Nat.factorial j + 1) % p^2) (Finset.range (2 * p)) ∪ {1} := by
      contrapose! h_odd_primes_bound
      exact le_trans ( by norm_num ) ( Finset.card_le_card ( show Finset.range ( p ^ 2 ) ⊆ Finset.image ( fun j => ( j ! + 1 ) % p ^ 2 ) ( Finset.range ( 2 * p ) ) ∪ { 1 } from fun x hx => h_odd_primes_bound x ( Finset.mem_range.mp hx ) ) )
    use b
    simp_all +decide [ A3 ]
    grind +ring
  · cases hp_prime.eq_two_or_odd
    all_goals
      simp_all +decide
    use 0
    norm_num [ A3 ]
    intro a x hx ha
    subst ha
    have : (Nat.factorial x + 1) % 4 ≠ 0 := by
      rcases x with _ | _ | _ | _ | x
      · decide
      · decide
      · decide
      · decide
      · have heq : x + 1 + 1 + 1 + 1 = x + 4 := by omega
        rw [heq]
        have h4 : 4 ∣ Nat.factorial (x + 4) := dvd_trans (show 4 ∣ Nat.factorial 4 by norm_num) (Nat.factorial_dvd_factorial (by omega))
        omega
    exact this

/-
The sequence A4 is admissible.
-/
lemma A4_admissible : Admissible A4 := by
  intro p hp
  by_cases h_cases : p % 2 = 1
  · -- For odd primes p, the elements j! - 1 are congruent to -1 mod p^2 for all j >= 2p.
    have h_odd_primes : ∀ j ≥ 2 * p, (Nat.factorial j - 1) % p^2 = (p^2 - 1) % p^2 := by
      intro j hj
      have h_div : p^2 ∣ Nat.factorial j := by
        have h_div : p^2 ∣ Nat.factorial (2 * p) := by
          -- Since $p$ is prime and $p \geq 3$, we know that $p^2 \mid (2p)!$.
          have h_div : p^2 ∣ Nat.factorial p * Nat.factorial p := by
            simpa only [ sq ] using mul_dvd_mul ( Nat.dvd_factorial hp.pos le_rfl ) ( Nat.dvd_factorial hp.pos le_rfl )
          exact dvd_trans h_div ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by rw [ two_mul ] )
        exact dvd_trans h_div ( Nat.factorial_dvd_factorial hj )
      refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_
      obtain ⟨ k, hk ⟩ := h_div
      use k - 1
      rw [ Nat.cast_sub <| by nlinarith [ Nat.factorial_pos j, hp.two_le ], Nat.cast_sub <| by nlinarith [ hp.two_le ] ]
      push_cast
      linarith
    -- Thus, for odd p, A4 occupies at most 2p residue classes modulo p^2 (the values for j < 2p, plus the value -1).
    have h_odd_primes_classes : Finset.image (fun j => (Nat.factorial j - 1) % p^2) (Finset.range (2 * p)) ∪ {p^2 - 1} ⊂ Finset.range (p^2) := by
      refine ⟨ ?_, ?_ ⟩
      · exact Finset.union_subset ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Nat.mod_lt _ <| pow_pos hp.pos 2 ) ( Finset.singleton_subset_iff.mpr <| Finset.mem_range.mpr <| Nat.sub_lt ( pow_pos hp.pos 2 ) zero_lt_one )
      · intro h
        have := Finset.card_le_card h
        simp_all +decide [ Finset.subset_iff ]
        refine this.not_gt ( lt_of_le_of_lt ( Finset.card_insert_le (p ^ 2 - 1) (Finset.image (fun j => (Nat.factorial j - 1) % p^2) (Finset.range (2 * p))) ) ?_ )
        refine lt_of_le_of_lt ( Nat.add_le_add_right ( Finset.card_image_le ) 1 ) ?_
        norm_num
        rcases p with ( _ | _ | _ | p ) <;> norm_num at * ; nlinarith
    obtain ⟨ b, hb ⟩ := Finset.exists_of_ssubset h_odd_primes_classes
    use b
    simp +zetaDelta at *
    exact ⟨ hb.1, fun a ha => by rcases ha with ⟨ j, hj, rfl ⟩ ; exact fun h => hb.2.2 j ( not_le.mp fun h' => by have := h_odd_primes j h'; omega ) <| by simpa [ Nat.factorial_pos ] using h ⟩
  · cases hp.eq_two_or_odd
    all_goals
      simp_all +decide
    use 0
    norm_num
    intro a ha
    rcases ha with ⟨ j, hj, rfl ⟩
    have : (Nat.factorial j - 1) % 4 ≠ 0 := by
      rcases j with _ | _ | _ | _ | j
      · omega
      · omega
      · decide
      · decide
      · have heq : j + 1 + 1 + 1 + 1 = j + 4 := by omega
        rw [heq]
        have h4 : 4 ∣ Nat.factorial (j + 4) := dvd_trans (show 4 ∣ Nat.factorial 4 by norm_num) (Nat.factorial_dvd_factorial (by omega))
        have := Nat.factorial_pos (j + 4)
        omega
    exact this

/-
A1 is infinite.
-/
lemma A1_infinite : A1.Infinite := by
  exact Set.infinite_of_injective_forall_mem ( fun i j hij => by simpa using hij ) fun j => ⟨ j + 1, by linarith, rfl ⟩

/-
The n-th element of A1 is 2^(n+1) + 1.
-/
lemma A1_nth (n : ℕ) : Nat.nth (· ∈ A1) n = 2^(n + 1) + 1 := by
  induction n with
  | zero =>
    norm_num [ Nat.nth_zero, A1 ]
    exact le_antisymm ( Nat.sInf_le ⟨ 1, by norm_num, rfl ⟩ ) ( le_csInf ⟨ 3, ⟨ 1, by norm_num, rfl ⟩ ⟩ fun n hn => by obtain ⟨ j, hj, rfl ⟩ := hn; exact Nat.succ_le_succ ( Nat.succ_le_of_lt ( lt_of_lt_of_le ( by norm_num ) ( Nat.pow_le_pow_right ( by norm_num ) hj ) ) ) )
  | succ n ih =>
    rw [ Nat.nth_eq_sInf ]
    refine le_antisymm ?_ ?_
    · refine Nat.sInf_le ⟨ ?_, ?_ ⟩
      · exact ⟨ n + 1 + 1, by norm_num, rfl ⟩
      · intro k hk
        exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A1 }.Infinite from A1_infinite ) ( Nat.le_of_lt_succ hk ) ) ( by rw [ ih ] ; exact Nat.succ_lt_succ ( pow_lt_pow_right₀ ( by decide ) ( by linarith ) ) )
    · refine le_csInf ?_ ?_ <;> norm_num
      · refine ⟨ 2 ^ ( n + 2 ) + 1, ?_, ?_ ⟩
        · exact ⟨ n + 2, by norm_num, rfl ⟩
        · intro k hk
          exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A1 }.Infinite from A1_infinite ) ( hk ) ) ( by rw [ ih ] ; exact by linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) ( by linarith : n + 1 < n + 2 ) ] )
      · intro b hb h
        contrapose! h
        use n
        obtain ⟨ j, hj₁, hj₂ ⟩ := hb
        rcases j with ( _ | j )
        all_goals
          simp_all +decide [ pow_succ' ]
        rw [ ← pow_succ' ] at h
        exact le_of_not_gt fun h' => h.not_ge <| Nat.pow_le_pow_right ( by decide ) <| Nat.succ_le_of_lt <| Nat.lt_of_not_ge fun h'' => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h'' ]

/-
A2 is infinite.
-/
lemma A2_infinite : A2.Infinite := by
  -- The function $j \mapsto 2^j - 1$ is injective, and the domain $\{1, 2, \ldots\}$ is infinite.
  have h_inj : Function.Injective (fun j : ℕ => 2^(j + 1) - 1) := by
    exact fun a b h => by
      zify at h
      norm_num at h
      linarith
  exact Set.infinite_of_injective_forall_mem h_inj fun j => ⟨ j + 1, by norm_num, rfl ⟩

/-
The n-th element of A2 is 2^(n+1) - 1.
-/
lemma A2_nth (n : ℕ) : Nat.nth (· ∈ A2) n = 2^(n + 1) - 1 := by
  induction n with
  | zero =>
    norm_num [ Nat.succ_eq_add_one, Nat.nth_zero ]
    exact le_antisymm ( csInf_le ⟨ 0, fun x hx => by rcases hx with ⟨ j, hj, rfl ⟩ ; exact Nat.zero_le _ ⟩ ⟨ 1, by norm_num, by norm_num ⟩ ) ( le_csInf ⟨ 1, ⟨ 1, by norm_num, by norm_num ⟩ ⟩ fun x hx => by rcases hx with ⟨ j, hj, rfl ⟩ ; exact Nat.le_sub_one_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) )
  | succ n ih =>
    -- By definition of $A2$, we know that $2^{n+2} - 1$ is the smallest element in $A2$ greater than $2^{n+1} - 1$.
    have h_next : ∀ m ∈ A2, m > 2^(n+1) - 1 → m ≥ 2^(n+2) - 1 := by
      intros m hm hm_gt
      obtain ⟨j, hj⟩ : ∃ j : ℕ, m = 2^j - 1 ∧ j ≥ 1 := by
        cases hm
        aesop
      exact hj.1.symm ▸ Nat.sub_le_sub_right ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => hm_gt.not_ge <| by rw [ hj.1 ] ; exact Nat.sub_le_sub_right ( pow_le_pow_right₀ ( by decide ) h ) _ ) ) ) _
    rw [ Nat.nth_eq_sInf ]
    refine le_antisymm ?_ ?_
    · refine Nat.sInf_le ⟨ ?_, ?_ ⟩
      · exact ⟨ n + 2, by norm_num, rfl ⟩
      · intro k hk
        refine lt_of_le_of_lt ( Nat.nth_monotone ?_ ( Nat.le_of_lt_succ hk ) ) ?_
        · exact A2_infinite
        · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_pow _ _ ( by decide ) ) ] ; ring_nf; norm_num
    · refine le_csInf ?_ ?_
      · refine ⟨ 2 ^ ( n + 2 ) - 1, ?_, ?_ ⟩
        · exact ⟨ n + 2, by norm_num, rfl ⟩
        · intro k hk
          refine lt_of_le_of_lt ( Nat.nth_monotone ?_ ( Nat.le_of_lt_succ hk ) ) ?_
          · exact A2_infinite
          · rw [ ih ]
            rw [ tsub_lt_tsub_iff_right ( Nat.one_le_pow _ _ ( by decide ) ) ]
            ring_nf
            norm_num
      · exact fun x hx => h_next x hx.1 ( by linarith [ hx.2 n ( Nat.lt_succ_self n ) ] )

/-
A3 is infinite.
-/
lemma A3_infinite : A3.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  exact fun a => ⟨ _, ⟨ a + 1, Nat.succ_pos _, rfl ⟩, by linarith [ Nat.self_le_factorial ( a + 1 ) ] ⟩

/-
The n-th element of A3 is (n+1)! + 1.
-/
lemma A3_nth (n : ℕ) : Nat.nth (· ∈ A3) n = Nat.factorial (n + 1) + 1 := by
  induction n with
  | zero =>
    norm_num [ A3 ]
    rw [ Nat.nth_zero ]
    exact le_antisymm ( Nat.sInf_le ⟨ 1, by decide, rfl ⟩ ) ( le_csInf ⟨ 2, ⟨ 1, by decide, rfl ⟩ ⟩ fun n hn => by obtain ⟨ j, hj, rfl ⟩ := hn; linarith [ Nat.self_le_factorial j ] )
  | succ n ih =>
    -- The (n+1)-th element of A3 is the smallest element in A3 that is greater than (n+1)! + 1.
    have h_next : Nat.nth (fun x => x ∈ A3) (n + 1) = sInf {x ∈ A3 | x > (n + 1)! + 1} := by
      rw [ ← ih, Nat.nth_eq_sInf ]
      congr with x
      constructor
      all_goals
        intro h
      all_goals
        simp_all +decide
      · exact ih ▸ h.2 _ ( le_refl _ )
      · intro k hk
        exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A3 }.Infinite from by exact Set.infinite_of_forall_exists_gt fun m => ⟨ ( m + 1 ) ! + 1, ⟨ m + 1, by linarith, rfl ⟩, by linarith [ Nat.self_le_factorial ( m + 1 ) ] ⟩ ) ( hk ) ) ( lt_of_le_of_lt ( ih.le ) h.2 )
    rw [ h_next, IsLeast.csInf_eq ]
    constructor
    · exact ⟨ ⟨ n + 2, by norm_num, by norm_num [ Nat.factorial_succ ] ⟩, by gcongr ; linarith ⟩
    · rintro x ⟨ hx₁, hx₂ ⟩
      obtain ⟨ j, hj₁, rfl ⟩ := hx₁
      exact Nat.succ_le_succ ( Nat.factorial_le ( Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => hx₂.not_ge <| Nat.succ_le_succ <| Nat.factorial_le h ) ) )

/-
The sequence A1 satisfies the growth condition for any constant C.
-/
lemma A1_growth (C : ℝ) : GrowthCondition A1 C := by
  -- We need to show that for infinitely many j, a_j ≥ exp(C j / log j).
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (2^(j + 1) + 1 : ℝ) ≥ Real.exp (C * (j + 1) / Real.log (j + 1)) := by
    -- We want to show that for sufficiently large $j$, $\exp(j \log 2) \geq \exp(C j / \log j)$.
    have h_exp_growth : ∀ᶠ j in Filter.atTop, Real.exp ((j + 1) * Real.log 2) ≥ Real.exp (C * (j + 1) / Real.log (j + 1)) := by
      -- We can divide both sides by $(j + 1)$ (which is positive for $j \geq 1$) to get $C / \log (j + 1) \leq \log 2$.
      suffices h_div : ∀ᶠ j in Filter.atTop, C / Real.log (j + 1) ≤ Real.log 2 by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ using
          Real.exp_le_exp.mpr (by
            have hmul := mul_le_mul_of_nonneg_left hj₁
              (show 0 ≤ (j + 1 : ℝ) by positivity)
            calc
              C * (j + 1) / Real.log (j + 1)
                  = (j + 1 : ℝ) * (C / Real.log (j + 1)) := by
                    rw [div_eq_mul_inv]
                    ring
              _ ≤ (j + 1 : ℝ) * Real.log 2 := hmul
              _ = (j + 1) * Real.log 2 := by ring)
      have h_div : Filter.Tendsto (fun j : ℝ => C / Real.log (j + 1)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.atTop_add tendsto_const_nhds )
      exact h_div.eventually ( ge_mem_nhds <| by positivity )
    filter_upwards [ h_exp_growth ] with j hj using
      le_trans hj (by
        have hpow :
            Real.exp ((j + 1 : ℝ) * Real.log 2) = (2 : ℝ) ^ (j + 1) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring_nf
        rw [hpow]
        exact le_add_of_nonneg_right zero_le_one)
  rw [ Filter.eventually_atTop ] at *
  obtain ⟨ a, ha ⟩ := h_exp_growth
  -- By definition of $A1$, we know that $Nat.nth (· ∈ A1) n = 2^(n + 1) + 1$ for all $n$.
  have h_nth_A1 : ∀ n : ℕ, Nat.nth (· ∈ A1) n = 2^(n + 1) + 1 := by
    exact fun n => A1_nth n
  refine Filter.frequently_atTop.mpr fun n => ?_
  refine ⟨ n + ⌈a⌉₊ + 1, ?_, ?_ ⟩ <;> norm_num [ h_nth_A1 ]
  · linarith
  · exact_mod_cast ha ( n + ⌈a⌉₊ ) ( by linarith [ Nat.le_ceil a ] )

/-
The sequence A2 satisfies the growth condition for any constant C.
-/
lemma A2_growth (C : ℝ) : GrowthCondition A2 C := by
  -- We need to show that for infinitely many $j$, $a_j \geq \exp(Cj/\log j)$.
  suffices h_inf : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A2) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) by
    exact Filter.Eventually.frequently h_inf
  -- We'll use that $2^j - 1 \geq \exp(Cj / \log j)$ for sufficiently large $j$.
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (2 : ℝ) ^ j - 1 ≥ Real.exp (C * j / Real.log j) := by
    -- We'll use that exponential functions grow faster than polynomial functions.
    have h_exp_growth : Filter.Tendsto (fun j : ℝ => Real.exp (C * j / Real.log j) / 2^j) Filter.atTop (nhds 0) := by
      -- We can rewrite the limit expression using properties of exponents: $\frac{e^{C \cdot \frac{j}{\log j}}}{2^j} = e^{C \cdot \frac{j}{\log j} - j \log 2}$.
      suffices h_exp : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j - j * Real.log 2)) Filter.atTop (nhds 0) by
        convert h_exp using 2
        norm_num [ Real.rpow_def_of_pos, mul_comm, Real.exp_sub ]
      -- We can factor out $j$ in the exponent: $j \left( \frac{C}{\log j} - \log 2 \right)$.
      suffices h_factor : Filter.Tendsto (fun j => j * (C / Real.log j - Real.log 2)) Filter.atTop Filter.atBot by
        exact Real.tendsto_exp_atBot.comp ( h_factor.congr fun x => by ring )
      -- We can use the fact that $C / \log j - \log 2$ tends to $-\log 2$ as $j \to \infty$.
      have h_log : Filter.Tendsto (fun j : ℝ => C / Real.log j - Real.log 2) Filter.atTop (nhds (-Real.log 2)) := by
        exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num )
      apply_rules [ Filter.Tendsto.atTop_mul_neg, h_log ]
      · norm_num [ Real.log_pos ]
      · exact Filter.tendsto_id
    filter_upwards [ h_exp_growth.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ using by rw [ div_lt_iff₀ <| by positivity ] at hj₁; nlinarith [ Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hj₂.le ]
  have h_nth_A2 : ∀ j : ℕ, j > 0 → (Nat.nth (· ∈ A2) (j - 1) : ℝ) = (2 : ℝ) ^ j - 1 := by
    intro j hj
    have h_def : Nat.nth (· ∈ A2) (j - 1) = 2 ^ j - 1 := by
      convert A2_nth ( j - 1 ) using 1
      rw [ Nat.sub_add_cancel hj ]
    norm_num [ h_def ]
  filter_upwards [ Filter.eventually_gt_atTop 0, h_exp_growth.natCast_atTop ] with j hj₁ hj₂ using by simpa [ h_nth_A2 j hj₁ ] using hj₂

/-
The sequence A3 satisfies the growth condition for any constant C.
-/
lemma A3_growth (C : ℝ) : GrowthCondition A3 C := by
  -- We need to show that for infinitely many j, a_j ≥ exp(C j / log j).
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A3) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) := by
    -- We'll use that $j! \geq e^{j \log j - j}$ for all $j \geq 1$.
    have h_factorial_bound : ∀ j : ℕ, j ≥ 1 → (Nat.factorial j : ℝ) ≥ Real.exp (j * Real.log j - j) := by
      field_simp
      intro j hj
      rw [ mul_sub, mul_one, Real.exp_sub, Real.exp_nat_mul, Real.exp_log ( by positivity ) ]
      rw [ div_le_iff₀ ( Real.exp_pos _ ) ]
      rw [ ← div_le_iff₀' ( by positivity ) ] ; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ] ; exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) j ( fun _ _ => by positivity )
    -- By definition of $A3$, we have $Nat.nth (· ∈ A3) (j - 1) = Nat.factorial j + 1$.
    have h_nth_A3 : ∀ j : ℕ, j ≥ 1 → Nat.nth (· ∈ A3) (j - 1) = Nat.factorial j + 1 := by
      intro j hj
      convert A3_nth ( j - 1 ) using 1; rcases j with ( _ | j ) <;> aesop
    -- We'll use that $j \log j - j \geq C j / \log j$ for sufficiently large $j$.
    have h_log_bound : ∀ᶠ j in Filter.atTop, j * Real.log j - j ≥ C * j / Real.log j := by
      -- We can divide both sides by $j$ to get $\log j - 1 \geq \frac{C}{\log j}$.
      suffices h_div : ∀ᶠ j in Filter.atTop, Real.log j - 1 ≥ C / Real.log j by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ using by ring_nf at *; nlinarith
      filter_upwards [ Filter.eventually_gt_atTop ( Real.exp ( |C| + 1 ) ) ] with j hj using by rw [ ge_iff_le, div_le_iff₀ ] <;> cases abs_cases C <;> nlinarith [ Real.log_exp ( |C| + 1 ), Real.log_lt_log ( by positivity ) hj ]
    filter_upwards [ Filter.eventually_ge_atTop 1, h_log_bound.natCast_atTop ] with j hj₁ hj₂ using by simpa [ h_nth_A3 j hj₁ ] using le_add_of_le_of_nonneg ( le_trans ( Real.exp_le_exp.mpr <| by simpa using hj₂ ) ( h_factorial_bound j hj₁ ) ) zero_le_one
  exact h_exp_growth.frequently

/-
A4 is infinite.
-/
lemma A4_infinite : A4.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  exact fun n => ⟨ _, ⟨ n + 3, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by linarith [ Nat.self_le_factorial ( n + 3 ) ] ⟩

/-
The n-th element of A4 is (n+2)! - 1.
-/
lemma A4_nth (n : ℕ) : Nat.nth (· ∈ A4) n = Nat.factorial (n + 2) - 1 := by
  -- By definition of $A4$, we know that every element in $A4$ is of the form $j! - 1$ for some $j \geq 2$.
  have hA4_def : ∀ x, x ∈ A4 ↔ ∃ j ≥ 2, x = Nat.factorial j - 1 := by
    unfold A4
    aesop
  induction n with
  | zero =>
    simp_all +decide [ Nat.nth_zero ]
    exact le_antisymm ( Nat.sInf_le ⟨ 2, by decide, rfl ⟩ ) ( le_csInf ⟨ 1, ⟨ 2, by decide, rfl ⟩ ⟩ fun x hx => by obtain ⟨ j, hj, rfl ⟩ := hx; exact Nat.le_sub_one_of_lt ( by linarith [ Nat.self_le_factorial j ] ) )
  | succ n ih =>
    simp_all +decide
    rw [ Nat.nth_eq_sInf ]
    refine le_antisymm ?_ ?_
    · refine Nat.sInf_le ⟨ ⟨ n + 3, by linarith, rfl ⟩, fun k hk => ?_ ⟩
      refine lt_of_le_of_lt ( Nat.nth_monotone ?_ ( Nat.le_of_lt_succ hk ) ) ?_
      · exact Set.infinite_of_forall_exists_gt fun x => ⟨ (x + 2)! - 1, ⟨ x + 2, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by nlinarith [ Nat.self_le_factorial ( x + 2 ) ] ⟩
      · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; gcongr ; linarith
    · refine le_csInf ?_ ?_
      · refine ⟨ (n + 3)! - 1, ⟨ ⟨ n + 3, by linarith, rfl ⟩, fun k hk => ?_ ⟩ ⟩
        refine lt_of_le_of_lt ( Nat.nth_monotone ?_ ( Nat.le_of_lt_succ hk ) ) ?_
        · exact Set.infinite_of_forall_exists_gt fun x => ⟨ (x + 2)! - 1, ⟨ x + 2, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by nlinarith [ Nat.self_le_factorial ( x + 2 ) ] ⟩
        · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; gcongr ; linarith
      · intro b hb
        obtain ⟨ ⟨ j, hj₁, rfl ⟩, hb' ⟩ := hb
        have := hb' n
        simp_all +decide
        contrapose! this
        rw [ tsub_le_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| Nat.factorial_ne_zero _ ) ]
        exact Nat.factorial_le ( Nat.le_of_not_lt fun h => by linarith [ Nat.sub_add_cancel ( Nat.factorial_pos j ), Nat.factorial_le h ] )

/-
The number of integers in an interval of length L that are congruent to a modulo m is L/m + O(1).
-/
lemma card_filter_modEq_Icc (u L a m : ℕ) (hm : m > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S := I.filter (fun x => x ≡ a [MOD m])
  abs ((S.card : ℝ) - (L : ℝ) / m) ≤ 2 := by
    refine abs_sub_le_iff.mpr ⟨ ?_, ?_ ⟩
    · refine le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_le_card <| show Finset.filter ( fun x => x ≡ a [MOD m] ) ( Finset.Icc u ( u + L - 1 ) ) ⊆ Finset.image ( fun k => m * k + a % m ) ( Finset.Icc ( u / m ) ( ( u + L - 1 ) / m ) ) from ?_ ) ((L : ℝ) / m) ) ?_
      · intro x hx
        simp_all +decide [ Nat.ModEq ]
        exact ⟨ x / m, ⟨ Nat.div_le_div_right hx.1.1, Nat.div_le_div_right hx.1.2 ⟩, by linarith [ Nat.mod_add_div x m ] ⟩
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by nlinarith [ Nat.mod_lt a hm ] ] ; norm_num
        rcases L with ( _ | L )
        all_goals
          norm_num [ Nat.succ_div ]
        · calc (u - 1) / m ≤ u / m := Nat.div_le_div_right (Nat.sub_le u 1)
            _ < 2 + u / m := by omega
        · field_simp
          exact mod_cast by nlinarith [ Nat.div_mul_le_self ( u + L ) m, Nat.div_add_mod ( u + L ) m, Nat.mod_lt ( u + L ) hm, Nat.div_mul_le_self u m, Nat.div_add_mod u m, Nat.mod_lt u hm, Nat.sub_add_cancel ( show u / m ≤ ( u + L ) / m + 1 from Nat.le_succ_of_le ( Nat.div_le_div_right ( by linarith ) ) ) ]
    · -- The set of integers in [u, u+L-1] that are congruent to a modulo m forms an arithmetic progression with common difference m.
      have h_arith_prog : Finset.filter (fun x => x ≡ a [MOD m]) (Finset.Icc u (u + L - 1)) ⊇ Finset.image (fun k => u + ((a + m - u % m) % m) + k * m) (Finset.range (L / m)) := by
        intro x hxaesop
        norm_num +zetaDelta at *
        rcases hxaesop with ⟨ k, hk₁, rfl ⟩
        exact ⟨ ⟨ by nlinarith [ Nat.zero_le ( ( a + m - u % m ) % m ) ], Nat.le_sub_one_of_lt ( by nlinarith [ Nat.div_mul_le_self L m, Nat.zero_le ( ( a + m - u % m ) % m ), Nat.mod_lt ( a + m - u % m ) hm ] ) ⟩, by simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ( show u % m ≤ a + m from by linarith [ Nat.mod_lt u hm ] ) ] ⟩
      have := Finset.card_mono h_arith_prog
      simp_all +decide [ Finset.card_image_of_injective, Function.Injective, hm.ne' ]
      rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_add_mod L m, Nat.mod_lt L hm ]

/-
The number of integers in an interval of length L satisfying two coprime modular constraints is L/(Wq) + O(1).
-/
lemma card_intersect_bound (u L W q b c : ℕ) (hWq : Nat.Coprime W q) (hW : W > 0) (hq : q > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q])
  abs ((S_intersect.card : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
    -- By the Chinese Remainder Theorem, there exists a unique solution modulo $Wq$ to the system of congruences $n \equiv b \pmod{W}$ and $n \equiv c \pmod{q}$.
    obtain ⟨a, ha⟩ : ∃ a, a ≡ b [MOD W] ∧ a ≡ c [MOD q] ∧ a < W * q := by
      have := Nat.chineseRemainder hWq b c
      exact ⟨ this.val % ( W * q ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.2, Nat.mod_lt _ ( Nat.mul_pos hW hq ) ⟩
    -- The set of integers in $I$ that are congruent to $a$ modulo $Wq$ is exactly the set of integers in $I$ that satisfy both congruences.
    have h_set_eq : {n ∈ Finset.Icc u (u + L - 1) | n ≡ b [MOD W] ∧ n ≡ c [MOD q]} = {n ∈ Finset.Icc u (u + L - 1) | n ≡ a [MOD (W * q)]} := by
      ext n
      simp_all +decide
      intro _ _
      rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ]
      focus
        simp_all +decide [ Nat.ModEq ]
      assumption
    convert card_filter_modEq_Icc u L a ( W * q ) ( mul_pos hW hq ) using 1
    aesop

/-
Lemma freq: Let b mod W, c mod q be congruence classes with W coprime to q, and let I be an interval of length L >= W. Then, if n is drawn uniformly at random from those elements of b mod W that lie in I, the probability that n lies in c mod q is O(1/q + W/L).
-/
lemma lemma_freq :
  ∃ C : ℝ, C > 0 ∧ ∀ (W q : ℕ) (b c : ℕ) (u L : ℕ),
    Nat.Coprime W q → L ≥ W →
    let I := Finset.Icc u (u + L - 1)
    let S := I.filter (fun n => n ≡ b [MOD W])
    let N_S := S.card
    let N_intersect := (S.filter (fun n => n ≡ c [MOD q])).card
    N_S > 0 →
    (N_intersect : ℝ) / N_S ≤ C * (1 / (q : ℝ) + (W : ℝ) / L) := by
      refine ⟨ 4, by norm_num, fun W q b c u L hWq hL hS => ?_ ⟩
      -- Let's consider the two cases: $L \geq 4W$ and $W \leq L < 4W$.
      by_cases h_case : L ≥ 4 * W
      · -- Using the bounds from card_filter_modEq_Icc and card_intersect_bound, we have:
        have h_bound : (Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card ≤ (L : ℝ) / (W * q) + 2 ∧ (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card ≥ (L : ℝ) / W - 2 := by
          have h_bounds : abs ((Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card - (L : ℝ) / (W * q)) ≤ 2 ∧ abs ((Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card - (L : ℝ) / W) ≤ 2 := by
            apply And.intro
            · by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ Nat.Coprime ]
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · convert card_intersect_bound u L W q b c hWq ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) using 1
                simp +decide only [Finset.filter_filter]
            · by_cases hW : W = 0 <;> simp_all +decide [ Nat.ModEq ]
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num )
              · convert card_filter_modEq_Icc u L b W ( Nat.pos_of_ne_zero hW ) using 1
                have hfilter :
                    (Finset.filter (fun x => x % W = b % W) (Finset.Icc u (u + L - 1))) =
                      (Finset.filter (fun x => x ≡ b [MOD W]) (Finset.Icc u (u + L - 1))) := by
                  ext n
                  simp [Nat.ModEq]
                rw [hfilter]
          exact ⟨ by linarith [ abs_le.mp h_bounds.1 ], by linarith [ abs_le.mp h_bounds.2 ] ⟩
        by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ division_def ]
        · exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_bound.1 ) ( by positivity ) ) ( by rw [ ← div_eq_mul_inv ] ; rw [ div_le_iff₀ ] <;> norm_cast <;> linarith [ Finset.card_pos.mpr hS ] )
        · norm_num [ Nat.modEq_iff_dvd ] at *
          field_simp
          rw [ div_le_iff₀ ] <;> norm_cast at * <;> cases L <;> norm_num at * ; nlinarith
        · rw [ ← div_eq_mul_inv, div_le_iff₀ ]
          · field_simp at *
            rw [ add_div', mul_div_assoc' ] <;> try norm_cast ; linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ]
            rw [ div_mul_eq_mul_div, le_div_iff₀ ]
            all_goals
              norm_cast at *
            all_goals
              try linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ]
            nlinarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq, mul_pos ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) ]
          · exact Nat.cast_pos.mpr ( Finset.card_pos.mpr hS )
      · refine le_trans ( div_le_one_of_le₀ ?_ ?_ ) ?_
        · exact_mod_cast Finset.card_mono <| Finset.filter_subset _ _
        · positivity
        · rcases q with ( _ | _ | q )
          all_goals
            norm_num at *
          · rw [ mul_div, le_div_iff₀ ]
            all_goals
              norm_cast
            all_goals
              linarith [ show L > 0 from Nat.pos_of_ne_zero ( by omega ) ]
          · exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_right <| by positivity ) zero_le_four )
          · field_simp
            rw [ add_div', mul_div_assoc', le_div_iff₀ ]
            all_goals
              norm_cast
            all_goals
              nlinarith

/-
W_val(x) is the product of p^2 for all primes p <= 0.1 log x.
-/
def W_val (x : ℝ) : ℕ := ∏ p ∈ (Finset.range (Nat.floor (0.1 * Real.log x) + 1)).filter Nat.Prime, p^2

/-
For all x, W_val(x) <= x^0.4. Uses Chebyshev's bound θ(y) ≤ log(4) * y.
-/
lemma W_bound :
  ∀ᶠ x in Filter.atTop,
    (W_val x : ℝ) ≤ Real.exp (0.4 * Real.log x) := by
      -- Use Chebyshev's theta bound: $\theta(y) \leq \log(4) y$ (Chebyshev.theta_le_log4_mul_x).
      have theta_bound : ∀ y : ℝ, 0 ≤ y → (∑ p ∈ (Finset.range (Nat.floor y + 1)).filter Nat.Prime, Real.log p) ≤ Real.log 4 * y := by
        intro y hy
        convert Chebyshev.theta_le_log4_mul_x hy using 1
        refine Finset.sum_bij ( fun p hp => p ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ]
        exact fun a ha ha' => Nat.Prime.pos ha'
      -- Use the bound on $\theta(y)$ to bound $\log(W_val(x))$.
      have log_W_val_bound : ∀ᶠ x in Filter.atTop, Real.log (W_val x) ≤ 2 * Real.log 4 * (0.1 * Real.log x) := by
        -- By definition of $W_val$, we have $\log(W_val(x)) = \sum_{p \leq 0.1 \log x} 2 \log p$.
        have h_log_W_val_def : ∀ x, 1 < x → Real.log (W_val x) = ∑ p ∈ (Finset.range (Nat.floor (0.1 * Real.log x) + 1)).filter Nat.Prime, 2 * Real.log p := by
          intros x hx
          unfold W_val
          rw [ Nat.cast_prod ]
          rw [ Real.log_prod ]
          focus
            norm_num [ Finset.sum_mul _ _ _ ]
          aesop
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ h_log_W_val_def x hx ] ; simpa [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( theta_bound ( 0.1 * Real.log x ) ( by linarith [ Real.log_nonneg hx.le ] ) ) zero_le_two
      filter_upwards [ log_W_val_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂
      rw [ ← Real.log_le_iff_le_exp ( by exact Nat.cast_pos.mpr <| Finset.prod_pos fun p hp => pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) _ ) ]
      exact hx₁.trans ( by rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; norm_num; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos hx₂ ] )

/-
The tail sum of 1/p² over primes p ≥ x is O(1/(x * log x)).
-/
lemma tail_sum_inv_prime_sq_isBigO :
    (fun (x : ℝ) => ∑' (p : ℕ), if (p : ℝ) ≥ x ∧ Nat.Prime p then 1 / (p : ℝ)^2 else 0) =O[Filter.atTop]
    (fun (x : ℝ) => 1 / (x * Real.log x)) := by
  -- We want to show that the sum of 1/p² over primes p ≥ x is O(1/(x · log x)).
  -- This follows from the following lemma.
  have h_bound : ∃ C > 0, ∀ x : ℝ, x ≥ 4 → (∑' p : ℕ, if (Nat.Prime p) ∧ x ≤ (p : ℝ) then 1 / (p : ℝ) ^ 2 else 0) ≤ C / (x * Real.log x) := by
    have h_tail_bound : ∃ C > 0, ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → (∑ p ∈ Finset.Icc (Nat.ceil x) N, if Nat.Prime p then (1 / (p : ℝ)^2) else 0) ≤ C / (x * Real.log x) := by
      -- By Abel's summation formula, we have:
      have h_abel : ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → (∑ p ∈ Finset.Icc (Nat.ceil x) N, if Nat.Prime p then (1 / (p : ℝ)^2) else 0) ≤ (Nat.primeCounting N : ℝ) / N^2 + ∑ m ∈ Finset.Icc (Nat.ceil x) N, (Nat.primeCounting m : ℝ) * (1 / m^2 - 1 / (m + 1)^2) := by
        intros x hx N hN
        have h_sum_split : (∑ p ∈ Finset.Icc (Nat.ceil x) N, if Nat.Prime p then (1 / (p : ℝ)^2) else 0) ≤ (Nat.primeCounting N : ℝ) / N^2 + ∑ m ∈ Finset.Ico (Nat.ceil x) N, (Nat.primeCounting m : ℝ) * (1 / m^2 - 1 / (m + 1)^2) := by
          induction hN
          all_goals
            norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *
          · split_ifs
            all_goals
              norm_num [ Nat.primeCounting ]
            · rw [ inv_eq_one_div, div_le_div_iff_of_pos_right ]
              all_goals
                norm_cast
              all_goals
                norm_num [ Nat.primeCounting' ]
              · grind
              · exact pow_pos ( Nat.ceil_pos.mpr ( by positivity ) ) _
            · positivity
          · rename_i k hk ih
            erw [ Finset.sum_Ico_succ_top ( by linarith [ Nat.ceil_le.mpr hk ] ), Finset.sum_Ico_succ_top ( by linarith [ Nat.ceil_le.mpr hk ] ) ]
            rw [ Finset.sum_Ico_succ_top ( by linarith [ Nat.ceil_le.mpr hk ] ) ]
            rw [ show ( Nat.primeCounting ( k + 1 ) : ℝ ) = Nat.primeCounting k + if Nat.Prime ( k + 1 ) then 1 else 0 from ?_ ]
            · rw [ Finset.Icc_eq_cons_Ico ( Nat.ceil_le.mpr hk ), Finset.sum_cons ] at ih
              norm_num at *
              split_ifs at *
              all_goals
                ring_nf at *
              all_goals
                norm_num at *
              · linarith
              · grind +revert
              · linarith
              · grind
            · rw [ Nat.primeCounting, Nat.primeCounting ]
              rw [ Nat.primeCounting', Nat.count_succ ]
              aesop
        refine le_trans h_sum_split ?_
        norm_num [ Finset.sum_Ico_succ_top, hN ]
        exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Ico.mp hx |>.1, Finset.mem_Ico.mp hx |>.2.le ⟩ ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr <| inv_anti₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp ‹_›, Nat.ceil_pos.mpr ( show 0 < x by linarith ) ] ) <| by gcongr ; linarith )
      -- Using the bound on the prime counting function, we get:
      have h_prime_counting_bound : ∃ C > 0, ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → (∑ m ∈ Finset.Icc (Nat.ceil x) N, (Nat.primeCounting m : ℝ) * (1 / m^2 - 1 / (m + 1)^2)) ≤ C * (∑ m ∈ Finset.Icc (Nat.ceil x) N, (1 / (m * Real.log m) * (1 / m))) := by
        have h_prime_counting_bound : ∃ C > 0, ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → ∀ m ∈ Finset.Icc (Nat.ceil x) N, (Nat.primeCounting m : ℝ) ≤ C * (m / Real.log m) := by
          have h_prime_counting_bound : ∃ C > 0, ∀ m : ℕ, m ≥ 2 → (Nat.primeCounting m : ℝ) ≤ C * (m / Real.log m) := by
            have := @Chebyshev.eventually_primeCounting_le
            obtain ⟨ C, hC ⟩ := Filter.eventually_atTop.mp ( this zero_lt_one )
            refine ⟨ Max.max ( Real.log 4 + 1 ) ( ∑ m ∈ Finset.Icc 2 ( Nat.ceil C ), ( Nat.primeCounting m : ℝ ) * Real.log m / m ) + 1, by positivity, fun m hm => ?_ ⟩
            by_cases hm' : m ≤ Nat.ceil C
            · have := Finset.single_le_sum ( fun x ( hx : x ∈ Finset.Icc 2 ⌈C⌉₊ ) => show 0 ≤ ( Nat.primeCounting x : ℝ ) * Real.log x / x from div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) ) ) ( Nat.cast_nonneg _ ) ) ( Finset.mem_Icc.mpr ⟨ hm, hm' ⟩ )
              rw [ div_le_iff₀ ( by positivity ) ] at this
              rw [ mul_div, le_div_iff₀ ( Real.log_pos ( by norm_cast ) ) ]
              exact this.trans ( mul_le_mul_of_nonneg_right ( le_add_of_le_of_nonneg ( le_max_right _ _ ) zero_le_one ) ( Nat.cast_nonneg _ ) )
            · have := hC m ( Nat.le_of_ceil_le ( le_of_not_ge hm' ) )
              norm_num at *
              exact this.trans ( by rw [ mul_div_assoc ] ; exact mul_le_mul_of_nonneg_right ( by linarith [ le_max_left ( Real.log 4 + 1 ) ( ∑ m ∈ Finset.Icc 2 ⌈C⌉₊, ( m.primeCounting : ℝ ) * Real.log m / m ) ] ) ( by positivity ) )
          exact ⟨ h_prime_counting_bound.choose, h_prime_counting_bound.choose_spec.1, fun x hx N hN m hm => h_prime_counting_bound.choose_spec.2 m <| by linarith [ Finset.mem_Icc.mp hm, Nat.ceil_le.mp <| Finset.mem_Icc.mp hm |>.1, show ⌈x⌉₊ ≥ 4 by exact Nat.succ_le_of_lt <| Nat.lt_ceil.mpr <| by norm_num; linarith ] ⟩
        obtain ⟨ C, hC₀, hC ⟩ := h_prime_counting_bound
        refine ⟨ C * 3, mul_pos hC₀ zero_lt_three, fun x hx N hN => ?_ ⟩
        rw [ Finset.mul_sum _ _ _ ]
        refine Finset.sum_le_sum fun m hm => le_trans ( mul_le_mul_of_nonneg_right ( hC x hx N hN m hm ) <| sub_nonneg.mpr <| one_div_le_one_div_of_le ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hm, Nat.ceil_pos.mpr ( show 0 < x by linarith ) ] ) <| by gcongr ; linarith ) ?_
        rcases m with ( _ | _ | m )
        all_goals
          norm_num at *
        field_simp
        exact div_le_div_of_nonneg_right ( by ring_nf; nlinarith ) ( Real.log_nonneg ( by linarith ) )
      -- The sum $\sum_{m \geq x} \frac{1}{m^2 \log m}$ is bounded by $\frac{2}{x \log x}$.
      have h_sum_bound : ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → (∑ m ∈ Finset.Icc (Nat.ceil x) N, (1 / (m * Real.log m) * (1 / m))) ≤ 2 / (x * Real.log x) := by
        -- We'll use the fact that $\sum_{m \geq x} \frac{1}{m^2 \log m}$ is bounded by $\frac{2}{x \log x}$.
        intros x hx N hN
        have h_sum_bound : (∑ m ∈ Finset.Icc (Nat.ceil x) N, (1 / (m * Real.log m) * (1 / m))) ≤ (∑ m ∈ Finset.Icc (Nat.ceil x) N, (1 / (m - 1 : ℝ) - 1 / (m : ℝ)) / Real.log x) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rcases m with ( _ | _ | m )
          all_goals
            norm_num at *
          · linarith
          · linarith
          · field_simp
            rw [ div_le_div_iff₀ ]
            all_goals
              nlinarith [ Real.log_pos ( by linarith : 1 < x ), Real.log_le_log ( by linarith ) ( by linarith : x ≤ m + 1 + 1 ) ]
        -- The sum $\sum_{m \geq x} \frac{1}{m-1} - \frac{1}{m}$ telescopes to $\frac{1}{x-1} - \frac{1}{N}$.
        have h_telescope : (∑ m ∈ Finset.Icc (Nat.ceil x) N, (1 / (m - 1 : ℝ) - 1 / (m : ℝ))) = (1 / (Nat.ceil x - 1 : ℝ)) - (1 / (N : ℝ)) := by
          erw [ Finset.sum_Ico_eq_sum_range ]
          convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring_nf
          rw [ Nat.cast_sub ]
          all_goals
            push_cast
          all_goals
            linarith [ Nat.ceil_le_floor_add_one x ]
        -- Using the fact that $1 / (Nat.ceil x - 1) \leq 2 / x$ for $x \geq 4$, we get:
        have h_ceil_bound : 1 / (Nat.ceil x - 1 : ℝ) ≤ 2 / x := by
          rw [ div_le_div_iff₀ ] <;> nlinarith [ Nat.le_ceil x, show ( ⌈x⌉₊ : ℝ ) ≥ 4 by exact_mod_cast Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ]
        simp_all +decide [ ← Finset.sum_div _ _ _ ]
        exact h_sum_bound.trans ( by rw [ div_mul_eq_div_div ] ; exact div_le_div_of_nonneg_right ( by linarith [ inv_nonneg.2 ( show ( 0 : ℝ ) ≤ N by positivity ) ] ) ( Real.log_nonneg ( by linarith ) ) )
      obtain ⟨ C, hC₀, hC ⟩ := h_prime_counting_bound
      -- Using the bound on the prime counting function, we get $\frac{\pi(N)}{N^2} \leq \frac{C}{N \log N}$.
      have h_prime_counting_bound : ∃ C > 0, ∀ x : ℝ, x ≥ 4 → ∀ N : ℕ, N ≥ Nat.ceil x → (Nat.primeCounting N : ℝ) / N^2 ≤ C / (N * Real.log N) := by
        have h_prime_counting_bound : ∃ C > 0, ∀ N : ℕ, N ≥ 4 → (Nat.primeCounting N : ℝ) ≤ C * N / Real.log N := by
          have := @Chebyshev.eventually_primeCounting_le
          obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp ( this zero_lt_one )
          use Max.max ( Real.log 4 + 1 ) ( ∑ N ∈ Finset.Icc 4 ( Nat.floor M ), ( Nat.primeCounting N : ℝ ) * Real.log N / N )
          refine ⟨ lt_max_of_lt_left ( by positivity ), fun N hN => ?_ ⟩
          by_cases hN' : N ≤ Nat.floor M
          · rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ]
            refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( le_max_right (Real.log 4 + 1) (∑ N ∈ Finset.Icc 4 ( Nat.floor M ), ( Nat.primeCounting N : ℝ ) * Real.log N / N) ) ( Nat.cast_nonneg N ) )
            rw [ Finset.sum_mul _ _ _ ]
            refine le_trans ?_ ( Finset.single_le_sum ( fun i hi => by positivity ) ( Finset.mem_Icc.mpr ⟨ hN, hN' ⟩ ) )
            rw [ div_mul_cancel₀ _ ( by positivity ) ]
          · have := hM N ( Nat.lt_of_floor_lt ( not_le.mp hN' ) |> le_of_lt )
            simp_all +decide [ mul_div_assoc ]
            exact le_trans this ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) )
        obtain ⟨ C, hC₀, hC ⟩ := h_prime_counting_bound
        use C, hC₀
        intro x hx N hN
        rw [ div_le_iff₀ ]
        all_goals
          ring_nf at *
        all_goals
          norm_num at *
        · convert ‹∀ N : ℕ, 4 ≤ N → ( N.primeCounting : ℝ ) ≤ C * N * ( Real.log N ) ⁻¹› N ( by exact_mod_cast hx.trans hN ) using 1
          · rfl
          · have hN_ne : (N : ℝ) ≠ 0 := by
              have hN_pos : (0 : ℝ) < N := by linarith
              exact ne_of_gt hN_pos
            rw [sq]
            calc
              C * (↑N * ↑N) * (↑N)⁻¹ * (Real.log ↑N)⁻¹
                  = C * (↑N * (↑N * (↑N)⁻¹)) * (Real.log ↑N)⁻¹ := by
                    ring
              _ = C * ↑N * (Real.log ↑N)⁻¹ := by
                    rw [mul_inv_cancel₀ hN_ne, mul_one]
        · exact sq_pos_of_pos ( by linarith )
      obtain ⟨ D, hD₀, hD ⟩ := h_prime_counting_bound
      refine ⟨ D + C * 2, by positivity, fun x hx N hN => le_trans ( h_abel x hx N hN ) ?_ ⟩
      refine le_trans ( add_le_add ( hD x hx N hN ) ( hC x hx N hN ) ) ?_
      refine le_trans ( add_le_add ( show D / ( N * Real.log N ) ≤ D / ( x * Real.log x ) from ?_ ) ( mul_le_mul_of_nonneg_left ( h_sum_bound x hx N hN ) hC₀.le ) ) ?_
      · gcongr
        · exact mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) )
        · exact Real.log_nonneg ( by linarith )
        · exact le_trans ( Nat.le_ceil _ ) ( mod_cast hN )
        · exact le_trans ( Nat.le_ceil _ ) ( mod_cast hN )
      · ring_nf
        norm_num
    obtain ⟨ C, hC₀, hC ⟩ := h_tail_bound
    refine ⟨ C, hC₀, fun x hx => ?_ ⟩
    have h_tail_bound : Filter.Tendsto (fun N : ℕ => ∑ p ∈ Finset.Icc (Nat.ceil x) N, if Nat.Prime p then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds (∑' p : ℕ, if Nat.Prime p ∧ x ≤ (p : ℝ) then (1 / (p : ℝ)^2) else 0)) := by
      have h_tail_bound : Filter.Tendsto (fun N : ℕ => ∑ p ∈ Finset.range (N + 1), if Nat.Prime p ∧ x ≤ (p : ℝ) then (1 / (p : ℝ)^2) else 0) Filter.atTop (nhds (∑' p : ℕ, if Nat.Prime p ∧ x ≤ (p : ℝ) then (1 / (p : ℝ)^2) else 0)) := by
        refine ( Summable.hasSum ?_ ) |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1
        exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
      refine h_tail_bound.congr' ?_
      filter_upwards [ Filter.eventually_ge_atTop ⌈x⌉₊ ] with N hN
      rw [ ← Finset.sum_filter ]
      rw [ ← Finset.sum_filter ]
      congr 1 with ( _ | p ) <;> simp +arith +decide
      tauto
    exact le_of_tendsto h_tail_bound ( Filter.eventually_atTop.mpr ⟨ ⌈x⌉₊, fun N hN => hC x hx N hN ⟩ )
  norm_num [ Asymptotics.isBigO_iff ]
  simp_all +decide [ and_comm ]
  obtain ⟨ C, hC₀, hC ⟩ := h_bound
  use C, 4; intros x hx; rw [ abs_of_nonneg ( tsum_nonneg fun _ => by positivity ), abs_of_nonneg ( Real.log_nonneg <| by linarith ), abs_of_nonneg ( by linarith ) ] ; convert hC x hx using 1 ; ring

/-
The sum of 1/p^2 for primes p in (0.1 log x, sqrt(2x)] is O(1/(log x log log x)).
-/
lemma sum_inv_sq_part_O :
  (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), 1 / (p : ℝ)^2)
  =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
    -- The sum is bounded by the infinite sum $\sum_{p > 0.1 \log x} 1/p^2$.
    have h_sum_bound : ∀ x : ℝ, x ≥ 2 → (∑ p ∈ Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p ^ 2 : ℝ))) ≤ (∑' p : ℕ, if (p : ℝ) ≥ 0.1 * Real.log x ∧ Nat.Prime p then 1 / (p ^ 2 : ℝ) else 0) := by
      intro x hx
      have h_subset : Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)) ⊆ Finset.filter (fun p : ℕ => Nat.Prime p ∧ 0.1 * Real.log x ≤ p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)) := by
        exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hp |>.1, Finset.mem_filter.mp hp |>.2.2.2, le_of_lt ( Finset.mem_filter.mp hp |>.2.1 ) ⟩
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_subset fun _ _ _ => by positivity ) ?_
      refine le_trans ?_ ( Summable.sum_le_tsum ?_ ?_ ?_ )
      any_goals exact Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 )
      · rw [ Finset.sum_filter ]
        exact Finset.sum_le_sum fun _ _ => by aesop
      · exact fun _ _ => by positivity
      · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
    -- By Chebyshev, the tail sum starting at $y$ is $O(1/(y \log y))$.
    have h_tail_sum : (fun x : ℝ => ∑' p : ℕ, if (p : ℝ) ≥ 0.1 * Real.log x ∧ Nat.Prime p then 1 / (p ^ 2 : ℝ) else 0) =O[Filter.atTop] (fun x : ℝ => 1 / ((0.1 * Real.log x) * Real.log (0.1 * Real.log x))) := by
      simpa [Function.comp_def] using
        tail_sum_inv_prime_sq_isBigO.comp_tendsto
          (show Filter.Tendsto ( fun x : ℝ => 0.1 * Real.log x )
              Filter.atTop Filter.atTop from
            Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_log_atTop ) )
    -- Since $0.1 \log x$ is a constant multiple of $\log x$, we can simplify the expression.
    have h_simplify : (fun x : ℝ => 1 / ((0.1 * Real.log x) * Real.log (0.1 * Real.log x))) =O[Filter.atTop] (fun x : ℝ => 1 / ((Real.log x) * Real.log (Real.log x))) := by
      rw [ Asymptotics.isBigO_iff ]
      -- Since $\log(0.1 \log x) = \log \log x + \log 0.1$, we can simplify the expression.
      have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (0.1 * Real.log x) ≥ (1 / 2) * Real.log (Real.log x) := by
        have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (0.1 * Real.log x) ≥ Real.log (Real.log x) - Real.log 10 := by
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos hx ) ( ne_of_gt <| by norm_num ) ] ; ring_nf; norm_num
        have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (Real.log x) ≥ 2 * Real.log 10 := by
          have h_log_simplify : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop := by
            exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
          exact h_log_simplify.eventually_ge_atTop _
        filter_upwards [ ‹∀ᶠ x in Filter.atTop, Real.log ( 0.1 * Real.log x ) ≥ Real.log ( Real.log x ) - Real.log 10›, h_log_simplify ] with x hx₁ hx₂ using by linarith
      refine ⟨ 20, ?_ ⟩ ; filter_upwards [ h_log_simplify, Filter.eventually_gt_atTop 2, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ ; rw [ Real.norm_of_nonneg, Real.norm_of_nonneg ] <;> norm_num at *
      · rw [ inv_mul_eq_div, div_le_iff₀ ]
        · field_simp
          rw [ div_le_div_iff₀ ]
          all_goals
            ring_nf at *
          all_goals
            norm_num at *
          · nlinarith [ Real.log_pos ( show 1 < x by linarith ), Real.log_pos ( show 1 < Real.log x by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ]
          · exact Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ]
          · exact mul_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 1 ] ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )
        · exact lt_of_lt_of_le ( mul_pos ( by norm_num ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) hx₁
      · exact mul_nonneg ( inv_nonneg.2 ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) ( inv_nonneg.2 ( Real.log_nonneg ( show 1 ≤ x from by linarith [ Real.add_one_le_exp 1 ] ) ) )
      · exact mul_nonneg ( inv_nonneg.mpr ( le_trans ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) hx₁ ) ) ( mul_nonneg ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) ) ( by norm_num ) )
    refine Asymptotics.IsBigO.trans ?_ ( h_tail_sum.trans h_simplify )
    rw [ Asymptotics.isBigO_iff ]
    exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 2, fun x hx => by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( tsum_nonneg fun _ => by positivity ) ] ; simpa using h_sum_bound x hx ⟩ ⟩

/-
For sufficiently large x, the sum of W/x for primes p in (0.1 log x, sqrt(2x)] is at most 1 / (log x log log x).
-/
lemma sum_W_div_x_bound :
  ∀ᶠ x in Filter.atTop,
    (Finset.filter
        (fun (p : ℕ) =>
          0.1 * Real.log x < (p : ℝ)
          ∧ (p : ℝ) ≤ Real.sqrt (2 * x)
          ∧ Nat.Prime p)
        (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))
    ).card
      * ((W_val x : ℝ) / x)
    ≤ 1 / (Real.log x * Real.log (Real.log x)) := by
    -- Let's simplify the expression using the bounds we have.
    suffices h_simp : ∀ᶠ x in Filter.atTop, (Finset.card (Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))) : ℝ) ≤ Real.sqrt (2 * x) by
      -- By combining the results from h_simp and h_bound, we can conclude the proof.
      have h_final : ∀ᶠ x in Filter.atTop, Real.sqrt (2 * x) * (Real.exp (0.4 * Real.log x) / x) ≤ 1 / (Real.log x * Real.log (Real.log x)) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (2 * x) * (Real.exp (0.4 * Real.log x) / x) * (Real.log x * Real.log (Real.log x))) Filter.atTop (nhds 0) by
          filter_upwards [ h_simplify.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ hx₃ hx₄ using by rw [ le_div_iff₀ ( mul_pos ( Real.log_pos hx₂ ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ; linarith
        -- Simplify the expression inside the limit further.
        suffices h_simplify' : Filter.Tendsto (fun x : ℝ => Real.sqrt 2 * Real.exp (-0.1 * Real.log x) * (Real.log x * Real.log (Real.log x))) Filter.atTop (nhds 0) by
          refine h_simplify'.congr' ?_
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
          norm_num [ Real.exp_neg, Real.exp_log hx, hx.le ]
          ring_nf
          rw [ show x = ( Real.exp ( Real.log x ) ) by rw [ Real.exp_log hx ] ]
          norm_num [ Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, hx.ne' ]
          norm_num [ ← Real.exp_add ]
          ring_nf
          norm_num
        -- Let $y = \log x$, therefore the expression becomes $\sqrt{2} \cdot e^{-0.25y} \cdot y \cdot \log y$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.sqrt 2 * Real.exp (-0.1 * y) * y * Real.log y) Filter.atTop (nhds 0) by
          convert h_log.comp Real.tendsto_log_atTop using 2
          norm_num
          ring
        -- We can factor out $y$ and use the fact that $\exp(-0.25y) \cdot y \to 0$ as $y \to \infty$.
        suffices h_factor : Filter.Tendsto (fun y : ℝ => Real.exp (-0.1 * y) * y^2) Filter.atTop (nhds 0) by
          have h_log : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
            -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] )
            norm_num
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by
              have h := Real.continuous_mul_log.tendsto 0
              simpa [neg_mul] using h.neg )
          convert h_factor.const_mul ( Real.sqrt 2 ) |> Filter.Tendsto.mul <| h_log using 2 <;> ring_nf
          by_cases h : ‹ℝ› = 0 <;> simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, h ]
        -- Let $z = 0.1y$, therefore the expression becomes $\exp(-z) \cdot (10z)^2$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * (10 * z)^2) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < ( 0.1 : ℝ ) by norm_num ) ) using 2 ; norm_num ; ring
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
        convert this.const_mul 100 using 2 <;> ring
      filter_upwards [ h_simp, h_final, Filter.eventually_gt_atTop 1, W_bound ] with x hx₁ hx₂ hx₃ hx₄
      refine le_trans ?_ hx₂
      gcongr
    refine Filter.eventually_atTop.mpr ⟨ 4, fun x hx => ?_ ⟩
    norm_num [ Nat.floor_le ] at *
    refine le_trans ?_ ( Nat.floor_le <| by positivity )
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) x]
    exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun p : ℕ => 1 / 10 * Real.log x < ( p : ℝ ) ∧ ( p : ℝ ) ≤ Real.sqrt 2 * Real.sqrt x ∧ Nat.Prime p ) ( Finset.range ( ⌊Real.sqrt 2 * Real.sqrt x⌋₊ + 1 ) ) ⊆ Finset.Ico 1 ( ⌊Real.sqrt 2 * Real.sqrt x⌋₊ + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.pos <| by aesop, Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) <| by simp +arith +decide

/-
Define C_freq as the constant from lemma_freq.
-/
noncomputable def C_freq : ℝ := Classical.choose lemma_freq

lemma C_freq_pos : C_freq > 0 := (Classical.choose_spec lemma_freq).1

lemma C_freq_spec : ∀ (W q : ℕ) (b c : ℕ) (u L : ℕ),
    Nat.Coprime W q → L ≥ W →
    let I := Finset.Icc u (u + L - 1)
    let S := I.filter (fun n => n ≡ b [MOD W])
    let N_S := S.card
    let N_intersect := (S.filter (fun n => n ≡ c [MOD q])).card
    N_S > 0 →
    (N_intersect : ℝ) / N_S ≤ C_freq * (1 / (q : ℝ) + (W : ℝ) / L) := (Classical.choose_spec lemma_freq).2

/-
failure_prob_sum_2(x) is the sum of (1/p^2 + 2W/x) for primes p in (0.1 log x, sqrt(2x)].
-/
def failure_prob_sum_2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2 + 2 * (W_val x : ℝ) / x)

/-
failure_prob_sum_2(x) is O(1/(log x log log x)).
-/
lemma failure_prob_sum_2_bound_O :
  failure_prob_sum_2 =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
    have h_failure_prob_sum_2 : failure_prob_sum_2 =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
      have h_sum_inv_sq : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2)) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        convert sum_inv_sq_part_O using 1
      have h_sum_W_div_x : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (W_val x : ℝ) / x) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        have := sum_W_div_x_bound
        rw [ Asymptotics.isBigO_iff ]
        exact ⟨ 1, by filter_upwards [ this, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( one_div_nonneg.mpr <| mul_nonneg ( Real.log_nonneg <| by linarith ) <| Real.log_nonneg <| by exact Real.le_log_iff_exp_le ( by linarith ) |>.2 <| by linarith ) ] ; simpa using hx₁ ⟩
      have h_sum_W_div_x : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (2 * (W_val x : ℝ) / x)) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        refine (h_sum_W_div_x.const_mul_left 2).congr_left ?_
        intro x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p hp => by ring
      refine (h_sum_inv_sq.add h_sum_W_div_x).congr_left ?_
      intro x
      unfold failure_prob_sum_2
      rw [ ← Finset.sum_add_distrib ]
    exact h_failure_prob_sum_2

/-
For any admissible set A and real x, there exists an integer b such that for all prime factors p of W_val(x), A avoids the residue class b mod p^2.
-/
lemma admissible_to_b (A : Set ℕ) (hA : Admissible A) (W : ℕ) (hW : Squarefree W) :
    ∃ b, ∀ p, p ∣ W → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2 := by
      choose! b hb using hA
      -- By the Chinese Remainder Theorem, there exists a unique $b$ modulo $W$ such that $b \equiv b_p \pmod{p^2}$ for each prime $p$ dividing $W$.
      have h_crt : ∃ b₀ : ℕ, ∀ p : ℕ, p ∣ W → Nat.Prime p → b₀ ≡ b p [MOD p^2] := by
        have h_crt : ∀ p ∈ Nat.primeFactors W, ∃ x, x ≡ b p [MOD p^2] ∧ ∀ q ∈ Nat.primeFactors W, q ≠ p → x ≡ 0 [MOD q^2] := by
          -- For each prime $p$ dividing $W$, let $y_p$ be the multiplicative inverse of $\prod_{q \neq p} q^2$ modulo $p^2$.
          intros p hp
          obtain ⟨y_p, hy_p⟩ : ∃ y_p, y_p * (∏ q ∈ Nat.primeFactors W \ {p}, q^2) ≡ 1 [MOD p^2] := by
            have h_coprime : Nat.gcd (∏ q ∈ Nat.primeFactors W \ {p}, q^2) (p^2) = 1 := by
              simp_all +decide [Nat.coprime_prod_left_iff]
              exact fun q hq hq' hq'' => hq.coprime_iff_not_dvd.mpr fun h => hq'' <| Nat.prime_dvd_prime_iff_eq hq hp.1 |>.1 h
            have h1lt : 1 < p ^ 2 := one_lt_pow₀ ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) two_ne_zero
            obtain ⟨y, hy⟩ := Nat.exists_mul_mod_eq_one_of_coprime h_coprime h1lt
            exact ⟨y, by unfold Nat.ModEq; rw [Nat.mod_eq_of_lt h1lt, mul_comm]; exact hy.2⟩
          use y_p * (∏ q ∈ Nat.primeFactors W \ {p}, q^2) * b p
          exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩
        choose! x hx₁ hx₂ using h_crt
        use ∑ p ∈ Nat.primeFactors W, x p
        intro p hp hp'
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
        rw [ Finset.sum_eq_single p ]
        all_goals
          aesop
      exact ⟨ h_crt.choose, fun p hp hp' a ha => by have := hb p hp'; have := h_crt.choose_spec p hp hp'; simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ] ⟩

/-
For any admissible set A and real x, there exists an integer b such that for all prime factors p of W_val(x), A avoids the residue class b mod p^2.
-/
lemma admissible_to_b_W_val (A : Set ℕ) (hA : Admissible A) (x : ℝ) :
    ∃ b, ∀ p, p ∣ W_val x → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2 := by
      obtain ⟨W, hW⟩ : ∃ W : ℕ, Squarefree W ∧ ∀ p, p ∣ W_val x → Nat.Prime p → p ∣ W := by
        use ∏ p ∈ Nat.primeFactors ( W_val x ), p
        rw [ Nat.squarefree_iff_prime_squarefree ]
        constructor
        · intro p pp dp
          rw [ Finset.prod_eq_prod_sdiff_singleton_mul <| Nat.mem_primeFactors.mpr ⟨ pp, ?_, ?_ ⟩ ] at dp
          all_goals
            norm_num at *
          · rw [ Nat.mul_dvd_mul_iff_right pp.pos ] at dp
            simp_all +decide [ Nat.Prime.dvd_iff_not_coprime pp, Nat.coprime_prod_right_iff ]
            obtain ⟨ q, hq₁, hq₂, hq₃, hq₄, hq₅ ⟩ := dp
            have := Nat.coprime_primes pp hq₁
            aesop
          · exact dvd_trans ( dvd_of_mul_left_dvd dp ) ( Nat.prod_primeFactors_dvd _ )
          · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop
        · exact fun p hp hp' => Finset.dvd_prod_of_mem _ <| Nat.mem_primeFactors.mpr ⟨ hp', hp, by unfold W_val; exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ⟩
      obtain ⟨ b, hb ⟩ := admissible_to_b A hA W hW.1
      exact ⟨ b, fun p hp hp' a ha => hb p ( hW.2 p hp hp' ) hp' a ha ⟩

/-
The function 1 / (log x log log x) is decreasing for sufficiently large x.
-/
def bound_func (x : ℝ) : ℝ := 1 / (Real.log x * Real.log (Real.log x))

lemma bound_func_decreasing : ∀ᶠ x in Filter.atTop, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
  unfold bound_func
  filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx
  intro y hy
  gcongr
  any_goals nlinarith [ Real.add_one_le_exp 1, Real.log_exp 1, Real.log_lt_log ( by positivity ) hx ]
  · exact mul_pos ( Real.log_pos ( lt_trans ( by norm_num ) hx ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos 1 ] ) ] ; linarith [ Real.add_one_le_exp 1 ] )
  · exact Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] )

/-
There exists a constant C such that for sufficiently large j, if x >= exp(C j / log j), then j * C_freq * failure_prob_sum_2(x) < 1.
-/
lemma prob_condition_of_growth :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    ∀ x, x ≥ Real.exp (C * j / Real.log j) →
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      -- We know `failure_prob_sum_2` is $O(\text{bound\_func})$.
      have h_bound : ∃ K > 0, ∀ᶠ x in Filter.atTop, failure_prob_sum_2 x ≤ K * bound_func x := by
        obtain ⟨ K, hK ⟩ := Asymptotics.isBigO_iff.mp ( failure_prob_sum_2_bound_O )
        refine ⟨ Max.max K 1, by positivity, ?_ ⟩
        filter_upwards [ hK, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃
        refine le_trans ( le_abs_self (failure_prob_sum_2 x) ) ( le_trans hx₁ ?_ )
        rw [ Real.norm_of_nonneg ( one_div_nonneg.mpr ( mul_nonneg ( Real.log_nonneg hx₂.le ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) ) ]
        exact mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( one_div_nonneg.mpr ( mul_nonneg ( Real.log_nonneg hx₂.le ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) )
      -- Let $x_{min}(j) = \exp(C j / \log j)$.
      obtain ⟨K, hK_pos, hK_bound⟩ := h_bound
      obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, ∀ᶠ j in Filter.atTop, j * C_freq * (K * bound_func (Real.exp (C * j / Real.log j))) < 1 := by
        -- Choose $C$ such that $C > C_{freq} \cdot K$.
        obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, C > C_freq * K := by
          exact ⟨ Max.max ( C_freq * K + 1 ) 1, by positivity, by linarith [ le_max_left ( C_freq * K + 1 ) 1, le_max_right ( C_freq * K + 1 ) 1 ] ⟩
        -- For large $j$, $\log(C j / \log j) \approx \log j$.
        have h_log_approx : Filter.Tendsto (fun j => Real.log (C * j / Real.log j) / Real.log j) Filter.atTop (nhds 1) := by
          -- We can use the fact that $\log(Cj / \log j) = \log C + \log j - \log \log j$.
          suffices h_log_simplified : Filter.Tendsto (fun j => Real.log C / Real.log j + 1 - Real.log (Real.log j) / Real.log j) Filter.atTop (nhds 1) by
            refine h_log_simplified.congr' ?_
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with j hj
            have hj_pos : 0 < j := lt_trans zero_lt_one hj
            have hlogj_pos : 0 < Real.log j := Real.log_pos hj
            rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt hlogj_pos ),
              Real.log_mul ( by positivity ) ( by positivity ) ]
            field_simp [ ne_of_gt hlogj_pos ]
          -- We can use the fact that $\frac{\log \log j}{\log j} \to 0$ as $j \to \infty$.
          have h_log_log : Filter.Tendsto (fun j => Real.log (Real.log j) / Real.log j) Filter.atTop (nhds 0) := by
            simpa [Function.comp_def] using
              (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
          have h_logC : Filter.Tendsto (fun j : ℝ => Real.log C / Real.log j) Filter.atTop (nhds 0) := by
            exact tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
          simpa using (h_logC.add tendsto_const_nhds).sub h_log_log
        -- Using the approximation, we get $\text{bound\_func}(x_{min}(j)) \approx 1 / (C j)$.
        have h_bound_func_approx : Filter.Tendsto (fun j => j * bound_func (Real.exp (C * j / Real.log j))) Filter.atTop (nhds (1 / C)) := by
          have h_inv : Filter.Tendsto (fun j => (Real.log (C * j / Real.log j) / Real.log j)⁻¹) Filter.atTop (nhds 1) := by
            simpa using h_log_approx.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
          have h_inv' : Filter.Tendsto (fun j => Real.log j / Real.log (C * j / Real.log j)) Filter.atTop (nhds 1) := by
            refine h_inv.congr' ?_
            filter_upwards [Filter.eventually_gt_atTop 1] with j hj
            rw [inv_div]
          have h_scaled : Filter.Tendsto (fun j => (1 / C) * (Real.log j / Real.log (C * j / Real.log j))) Filter.atTop (nhds (1 / C)) := by
            simpa using h_inv'.const_mul (1 / C)
          refine h_scaled.congr' ?_
          filter_upwards [Filter.eventually_gt_atTop 1] with j hj
          have hj_pos : 0 < j := lt_trans zero_lt_one hj
          have hlogj_pos : 0 < Real.log j := Real.log_pos hj
          have hC_ne : C ≠ 0 := ne_of_gt hC_pos
          have hlogj_ne : Real.log j ≠ 0 := ne_of_gt hlogj_pos
          have hy_pos : 0 < C * j / Real.log j := by positivity
          unfold bound_func
          simp only [Real.log_exp]
          field_simp [hC_ne, hlogj_ne]
        have := h_bound_func_approx.const_mul ( C_freq * K )
        exact ⟨ C, hC_pos, by filter_upwards [ this.eventually ( gt_mem_nhds <| show C_freq * K * ( 1 / C ) < 1 by rw [ mul_one_div, div_lt_iff₀ ] <;> linarith ) ] with j hj using by linarith ⟩
      -- By combining the results from hK_bound and hC_bound, we can conclude the proof.
      have h_final : ∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp (C * j / Real.log j), failure_prob_sum_2 x ≤ K * bound_func (Real.exp (C * j / Real.log j)) := by
        have h_final : ∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp (C * j / Real.log j), failure_prob_sum_2 x ≤ K * bound_func x := by
          have h_final : ∀ᶠ j in Filter.atTop, Real.exp (C * j / Real.log j) ≥ Classical.choose (Filter.eventually_atTop.mp hK_bound) := by
            have h_final : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
              refine Real.tendsto_exp_atTop.comp ?_
              -- We can use the change of variables $u = \log j$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u => C * Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] )
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( Real.tendsto_exp_div_pow_atTop 1 )
            exact h_final.eventually_ge_atTop _
          filter_upwards [ h_final ] with j hj using fun x hx => Classical.choose_spec ( Filter.eventually_atTop.mp hK_bound ) x ( le_trans hj hx )
        have h_final : ∀ᶠ x in Filter.atTop, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
          apply bound_func_decreasing
        obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x ≥ x₀, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
          exact Filter.eventually_atTop.mp h_final
        have h_final : ∀ᶠ j in Filter.atTop, Real.exp (C * j / Real.log j) ≥ x₀ := by
          have h_final : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
            have h_exp_growth : Filter.Tendsto (fun j => C * j / Real.log j) Filter.atTop Filter.atTop := by
              have h_exp_growth : Filter.Tendsto (fun j => j / Real.log j) Filter.atTop Filter.atTop := by
                -- We can use the change of variables $u = \log j$ to transform the limit expression.
                suffices h_log : Filter.Tendsto (fun u => Real.exp u / u) Filter.atTop Filter.atTop by
                  have := h_log.comp Real.tendsto_log_atTop
                  exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] )
                simpa using Real.tendsto_exp_div_pow_atTop 1
              simpa only [ mul_div_assoc ] using h_exp_growth.const_mul_atTop hC_pos
            exact Real.tendsto_exp_atTop.comp h_exp_growth
          exact h_final.eventually_ge_atTop x₀
        filter_upwards [ h_final, ‹∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp ( C * j / Real.log j ), failure_prob_sum_2 x ≤ K * bound_func x› ] with j hj₁ hj₂ using fun x hx => le_trans ( hj₂ x hx ) ( mul_le_mul_of_nonneg_left ( hx₀ _ hj₁ _ hx ) hK_pos.le )
      use C, hC_pos
      filter_upwards [ hC_bound, h_final, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ hj₃ using fun x hx => lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( hj₂ x hx ) ( by exact mul_nonneg ( by positivity ) ( by exact le_of_lt ( show 0 < C_freq from C_freq_pos ) ) ) ) hj₁

/-
There exists a constant C such that for sufficiently large j, if x >= exp(C j / log j), then j * C_freq * failure_prob_sum_2(x) < 1.
-/
lemma prob_condition_of_growth_v2 :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    ∀ x, x ≥ Real.exp (C * j / Real.log j) →
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      apply_mod_cast prob_condition_of_growth

/-
For sufficiently large x, the length of the interval [ceil(x/2), floor(x)] is at least W_val(x).
-/
lemma length_condition :
  ∀ᶠ x in Filter.atTop, (Nat.floor x - Nat.ceil (x / 2) + 1 : ℝ) ≥ (W_val x : ℝ) := by
    -- For large x, we have x/2 - 1 ≥ x^0.4.
    have h_x_half_minus_one_ge_x_pow : ∀ᶠ x in Filter.atTop, (x / 2 - 1 : ℝ) ≥ Real.exp (0.4 * Real.log x) := by
      -- We can divide both sides by $x^{0.4}$ to get $x^{0.6}/2 - 1/x^{0.4} \geq 1$, which simplifies to $x^{0.6}/2 \geq 1 + 1/x^{0.4}$.
      suffices h_div : ∀ᶠ x in Filter.atTop, (x : ℝ) ^ (3 / 5 : ℝ) / 2 ≥ 1 + 1 / (x : ℝ) ^ (2 / 5 : ℝ) by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂
        rw [ show ( 3 / 5 : ℝ ) = 1 - 2 / 5 by norm_num, Real.rpow_sub ] at hx₁
        all_goals
          norm_num at *
        all_goals
          try linarith
        rw [ show ( 2 / 5 : ℝ ) * Real.log x = Real.log ( x ^ ( 2 / 5 : ℝ ) ) by rw [ Real.log_rpow ( by positivity ) ] ]
        rw [ Real.exp_log ( by positivity ) ]
        ring_nf at *
        nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( zero_lt_one.trans hx₂ ) ( 2 / 5 : ℝ ) ) ), Real.rpow_pos_of_pos ( zero_lt_one.trans hx₂ ) ( 2 / 5 : ℝ ) ]
      -- As $x$ tends to infinity, $x^{3/5}/2$ grows without bound, while $1 + 1/x^{2/5}$ tends to $1$.
      have h_bound : Filter.Tendsto (fun x : ℝ => x ^ (3 / 5 : ℝ) / 2 - 1 - 1 / x ^ (2 / 5 : ℝ)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_div_const ( by norm_num ) ( tendsto_rpow_atTop ( by norm_num ) ) ) tendsto_const_nhds ) ( Filter.Tendsto.neg ( tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by norm_num ) ) ) )
      filter_upwards [ h_bound.eventually_gt_atTop 0 ] with x hx using by linarith
    filter_upwards [ h_x_half_minus_one_ge_x_pow, W_bound, Filter.eventually_gt_atTop 2 ] with x hx₁ hx₂ hx₃
    linarith [ Nat.le_ceil ( x / 2 ), Nat.ceil_lt_add_one ( show 0 ≤ x / 2 by positivity ), Nat.lt_floor_add_one x ]

/-
If L >= x/2, then W/L <= 2W/x.
-/
lemma W_div_L_le (x L W : ℝ) (hx : x > 0) (hL : L ≥ x / 2) (hW : W ≥ 0) : W / L ≤ 2 * W / x := by
  rw [ div_le_div_iff₀ ]
  all_goals
    nlinarith

/-
If L >= x/2 and W = W_val(x), then the sum of (1/p^2 + W/L) is bounded by failure_prob_sum_2(x).
-/
lemma sum_bound_inequality (x : ℝ) (hx : x > 0) (L : ℝ) (hL : L ≥ x / 2) (W : ℝ) (hW_eq : W = W_val x) :
    let P := Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))
    ∑ p ∈ P, (1 / (p : ℝ)^2 + W / L) ≤ failure_prob_sum_2 x := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := W_div_L_le x L ( ↑ ( W_val x ) ) hx hL
      aesop

/-
Any interval of length at least m contains a number congruent to k modulo m.
-/
lemma exists_mod_in_interval (u L m k : ℕ) (hL : L ≥ m) (hm : m > 0) :
    ∃ n ∈ Finset.Icc u (u + L - 1), n ≡ k [MOD m] := by
      -- By the pigeonhole principle, since there are m consecutive integers and m possible residues modulo m, one of these integers must be congruent to k modulo m.
      have h_pigeonhole : ∃ n ∈ Finset.range m, (u + n) ≡ k [MOD m] := by
        use ( k + m - u % m ) % m
        norm_num [ Nat.ModEq, Nat.mod_lt _ hm ]
        simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show u % m ≤ k + m from le_trans ( Nat.le_of_lt <| Nat.mod_lt _ hm ) <| Nat.le_add_left _ _ ) ]
      exact ⟨ u + h_pigeonhole.choose, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_range.mp h_pigeonhole.choose_spec.1 ], Nat.le_sub_one_of_lt ( by linarith [ Finset.mem_range.mp h_pigeonhole.choose_spec.1 ] ) ⟩, h_pigeonhole.choose_spec.2 ⟩

/-
The set of candidate integers is non-empty if the interval length is at least W.
-/
def CandidateSet (x_nat : ℕ) (W : ℕ) (b : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ))).filter (fun n => (n + b) % W = 0)

lemma CandidateSet_nonempty (x_nat : ℕ) (W : ℕ) (b : ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0) :
    (CandidateSet x_nat W b).Nonempty := by
      convert exists_mod_in_interval ( Nat.ceil ( x_nat / 2 : ℝ ) ) ( Nat.floor ( x_nat : ℝ ) - Nat.ceil ( x_nat / 2 : ℝ ) + 1 ) W ( W - b % W ) ?_ ?_ using 1
      · unfold CandidateSet
        constructor
        all_goals
          intro h
        · obtain ⟨ n, hn ⟩ := h
          use n
          simp_all +decide [Nat.ModEq]
          refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_
          rw [ Int.ofNat_sub ( Nat.le_of_lt <| Nat.mod_lt _ hW ) ]
          norm_num
          obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp hn.2
          exact ⟨ k - ( b / W + 1 ), by linarith [ Nat.mod_add_div b W ] ⟩
        · obtain ⟨ n, hn₁, hn₂ ⟩ := h
          use n
          simp_all +decide [Nat.ModEq]
          simp +decide [ Nat.add_mod, hn₂ ]
          simp +decide [ Nat.add_comm, Nat.add_sub_of_le ( Nat.mod_lt b hW |> Nat.le_of_lt ) ]
      · convert hL using 1
      · assumption

/-
The set of integers n in the candidate set such that n+a is divisible by p^2.
-/
def BadSet (x_nat : ℕ) (W : ℕ) (b : ℕ) (a : ℕ) (p : ℕ) : Finset ℕ :=
  (CandidateSet x_nat W b).filter (fun n => (n + a) % p^2 = 0)

/-
The set of primes p such that 0.1 log x < p <= sqrt(2x).
-/
def PrimesInInterval (x : ℝ) : Finset ℕ :=
  Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))

/-
CandidateSet is the set of n in the interval congruent to -b mod W.
-/
lemma CandidateSet_eq_modEq (x_nat W b : ℕ) (hW : W > 0) :
    CandidateSet x_nat W b = (Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ))).filter (fun n => n ≡ (W - (b % W)) % W [MOD W]) := by
      ext n
      simp [CandidateSet]
      intro _ _
      rw [ Nat.ModEq ]
      simp +decide [← ZMod.val_natCast]
      cases W
      all_goals
        simp_all +decide [ ← eq_sub_iff_add_eq ]
      rw [ ← ZMod.natCast_eq_natCast_iff' ]
      aesop

lemma BadSet_card_bound (x_nat : ℕ) (W : ℕ) (b : ℕ) (a : ℕ) (p : ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0)
    (hp : Nat.Coprime W (p^2)) (hp_pos : p > 0) :
    let S := CandidateSet x_nat W b
    let B := BadSet x_nat W b a p
    let L_nat := Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1
    (B.card : ℝ) ≤ (S.card : ℝ) * C_freq * (1 / (p^2 : ℝ) + (W : ℝ) / (L_nat : ℝ)) := by
      let u := Nat.ceil ((x_nat : ℝ) / 2)
      let L := Nat.floor (x_nat : ℝ) - u + 1
      let I := Finset.Icc u (u + L - 1)
      let resW := (W - b % W) % W
      let resP := (p ^ 2 - a % p ^ 2) % p ^ 2
      let Smod := I.filter (fun n => n ≡ resW [MOD W])
      let Bmod := Smod.filter (fun n => n ≡ resP [MOD p ^ 2])
      have hu_le_floor : u ≤ Nat.floor (x_nat : ℝ) := by
        dsimp [u]
        rw [Nat.floor_natCast]
        exact Nat.ceil_le.mpr (by
          have hx_nonneg : (0 : ℝ) ≤ x_nat := by positivity
          nlinarith)
      have hu_le_x : u ≤ x_nat := by
        simpa [Nat.floor_natCast] using hu_le_floor
      have hL_cast : (L : ℝ) = (x_nat : ℝ) - (u : ℝ) + 1 := by
        dsimp [L]
        rw [Nat.floor_natCast, Nat.cast_add, Nat.cast_sub hu_le_x]
        norm_num
      have hI_right : u + L - 1 = Nat.floor (x_nat : ℝ) := by
        dsimp [L]
        omega
      have hS_eq : CandidateSet x_nat W b = Smod := by
        dsimp [Smod, I, resW]
        rw [hI_right]
        exact CandidateSet_eq_modEq x_nat W b hW
      have hbad_residue :
          ∀ n, (n + a) % p ^ 2 = 0 ↔ n ≡ resP [MOD p ^ 2] := by
        intro n
        dsimp [resP]
        have hm : 0 < p ^ 2 := pow_pos hp_pos 2
        change (n + a) % (p ^ 2) = 0 % (p ^ 2) ↔
          n ≡ (p ^ 2 - a % p ^ 2) % p ^ 2 [MOD p ^ 2]
        rw [← ZMod.natCast_eq_natCast_iff' (n + a) 0 (p ^ 2)]
        rw [← ZMod.natCast_eq_natCast_iff n
          ((p ^ 2 - a % p ^ 2) % p ^ 2) (p ^ 2)]
        have hres :
            ((((p ^ 2 - a % p ^ 2) % p ^ 2 : ℕ) : ZMod (p ^ 2))) =
              -(a : ZMod (p ^ 2)) := by
          rw [ZMod.natCast_mod]
          rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt a hm))]
          simp
        push_cast
        rw [hres, add_comm, add_eq_zero_iff_eq_neg]
        constructor
        · intro h
          rw [h]
          simp
        · intro h
          rw [h]
          simp
      have hB_eq : BadSet x_nat W b a p = Bmod := by
        dsimp [Bmod]
        rw [← hS_eq]
        ext n
        simp [BadSet, hbad_residue n]
      have hS_pos : 0 < Smod.card := by
        rw [← hS_eq]
        exact Finset.card_pos.mpr (CandidateSet_nonempty x_nat W b hL hW)
      have hfreq :
          (Bmod.card : ℝ) / Smod.card ≤
            C_freq * (1 / (p ^ 2 : ℝ) + (W : ℝ) / (L : ℝ)) := by
        simpa [I, Smod, Bmod, resW, resP] using
          C_freq_spec W (p ^ 2) resW resP u L hp
            (by simpa [L, u] using hL) hS_pos
      have hmul := mul_le_mul_of_nonneg_left hfreq (show 0 ≤ (Smod.card : ℝ) by positivity)
      have hleft :
          (Smod.card : ℝ) * ((Bmod.card : ℝ) / Smod.card) = (Bmod.card : ℝ) := by
        rw [mul_div_cancel₀]
        exact_mod_cast (ne_of_gt hS_pos)
      have hmain :
          (Bmod.card : ℝ) ≤
            (Smod.card : ℝ) * (C_freq * (1 / (p ^ 2 : ℝ) + (W : ℝ) / (L : ℝ))) := by
        simpa [hleft, mul_assoc] using hmul
      simpa [hS_eq, hB_eq, hL_cast, mul_assoc] using hmain
      /-
      convert C_freq_spec W ( p ^ 2 ) ( ( W - ( b % W ) ) % W ) ( ( p ^ 2 - ( a % p ^ 2 ) ) % p ^ 2 ) ( Nat.ceil ( ( x_nat : ℝ ) / 2 ) ) ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) _ _ using 1
      · constructor
        all_goals
          intro h
        · convert C_freq_spec W ( p ^ 2 ) ( ( W - b % W ) % W ) ( ( p ^ 2 - a % p ^ 2 ) % p ^ 2 ) ( Nat.ceil ( ( x_nat : ℝ ) / 2 ) ) ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) _ _ using 1
          · assumption
          · convert hL using 1
        · convert mul_le_mul_of_nonneg_left ( h ?_ ) ( Nat.cast_nonneg _ ) using 1
          any_goals exact Finset.card ( Finset.filter ( fun n => n ≡ ( W - b % W ) % W [MOD W] ) ( Finset.Icc ⌈ ( x_nat : ℝ ) / 2⌉₊ ( ⌈ ( x_nat : ℝ ) / 2⌉₊ + ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) - 1 ) ) )
          · rw [ mul_div_cancel₀ ]
            · congr! 2
              ext
              simp [BadSet, CandidateSet]
              simp +decide [Nat.ModEq, Nat.add_mod]
              constructor
              all_goals
                intro h
              all_goals
                simp_all +decide [← Nat.dvd_iff_mod_eq_zero]
              · constructor
                all_goals
                  rw [ Nat.ModEq.symm ]
                · rw [ Nat.modEq_iff_dvd ]
                  obtain ⟨ k, hk ⟩ := h.1.2
                  use k - ( b / W + 1 )
                  linarith [ Nat.div_add_mod b W, Nat.sub_add_cancel ( show b % W ≤ W from Nat.le_of_lt ( Nat.mod_lt _ hW ) ) ]
                · rw [ Nat.modEq_iff_dvd ]
                  rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| by positivity ) ]
                  push_cast
                  obtain ⟨ k, hk ⟩ := h.2
                  exact ⟨ k - ( a / p ^ 2 ) - 1, by linarith [ Nat.mod_add_div a ( p ^ 2 ) ] ⟩
              · exact ⟨ ⟨ b / W + 1, by linarith [ Nat.div_add_mod b W, Nat.sub_add_cancel ( show b % W ≤ W from Nat.le_of_lt ( Nat.mod_lt _ hW ) ) ] ⟩, ⟨ a / p ^ 2 + 1, by linarith [ Nat.div_add_mod a ( p ^ 2 ), Nat.sub_add_cancel ( show a % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt ( Nat.mod_lt _ ( pow_pos hp_pos 2 ) ) ) ] ⟩ ⟩
            · have := exists_mod_in_interval ⌈ ( x_nat : ℝ ) / 2⌉₊ ( x_nat - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) W ( ( W - b % W ) % W ) ?_ ?_ <;> aesop
          · rw [ ← mul_assoc, mul_comm ]
            rw [ mul_comm ]
            norm_num [CandidateSet_eq_modEq, hW]
          · refine Finset.card_pos.mpr ?_
            obtain ⟨ n, hn ⟩ := exists_mod_in_interval ⌈ ( x_nat : ℝ ) / 2⌉₊ ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) W ( ( W - b % W ) % W ) ( by linarith ) ( by linarith )
            use n
            aesop
      · assumption
      · exact hL
      -/

/-
The union of all bad sets for a in A and p in the relevant prime interval.
-/
def UnionBadSets (x_nat : ℕ) (W : ℕ) (b : ℕ) (A : Finset ℕ) : Finset ℕ :=
  Finset.biUnion A (fun a => Finset.biUnion (PrimesInInterval (x_nat : ℝ)) (fun p => BadSet x_nat W b a p))

/-
The size of the union of bad sets is bounded by the sum of the bounds.
-/
lemma UnionBadSets_card_bound (x_nat : ℕ) (W : ℕ) (b : ℕ) (A : Finset ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0)
    (hCoprime : ∀ p ∈ PrimesInInterval (x_nat : ℝ), Nat.Coprime W (p^2)) :
    let S := CandidateSet x_nat W b
    let U := UnionBadSets x_nat W b A
    let L_nat := Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1
    (U.card : ℝ) ≤ (S.card : ℝ) * C_freq * (A.card : ℝ) * ∑ p ∈ PrimesInInterval (x_nat : ℝ), (1 / (p^2 : ℝ) + (W : ℝ) / (L_nat : ℝ)) := by
      refine le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) ?_
      refine le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun a ha => Finset.card_biUnion_le ) ?_
      push_cast [ Finset.mul_sum _ _ _ ]
      rw [ Finset.sum_comm ]
      refine Finset.sum_le_sum fun p hp => ?_
      have := BadSet_card_bound x_nat W b
      convert Finset.sum_le_sum fun a ha => this a p hL hW ( hCoprime p hp ) ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.2.2 ) ) using 1
      norm_num
      ring

/-
W is coprime to p^2 for any p in the relevant interval.
-/
lemma W_coprime_primes (x_nat : ℕ) (W : ℕ) (hW : W = W_val x_nat) :
    ∀ p ∈ PrimesInInterval (x_nat : ℝ), Nat.Coprime W (p^2) := by
      unfold W_val at hW
      -- Since $p$ is a prime in the interval $(0.1 \log x, \sqrt{2x}]$, it is greater than any prime factor of $W$.
      intros p hp
      have h_gt : ∀ q ∈ Finset.range (Nat.floor (0.1 * Real.log x_nat) + 1), Nat.Prime q → q < p := by
        intro q hq hq'
        have := Finset.mem_filter.mp hp
        simp only [Finset.mem_range, PrimesInInterval, Finset.mem_filter] at *
        have h_floor_lt := (Nat.floor_lt (show (0 : ℝ) ≤ 0.1 * Real.log ↑x_nat by positivity) (n := p)).mpr this.2.1
        omega
      simp_all +decide [Nat.coprime_prod_left_iff]
      exact fun q hq hq' => Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( by unfold PrimesInInterval at hp; aesop ) |>.2 <| Nat.not_dvd_of_pos_of_lt hq'.pos <| h_gt q hq hq'

/-
The size of the union of bad sets is strictly less than the size of the candidate set.
-/
lemma UnionBadSets_card_lt_S_card (x_nat : ℕ) (hx : (x_nat : ℝ) ≥ 100) (W : ℕ) (hW : W = W_val x_nat) (b : ℕ) (A : Finset ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W)
    (h_prob : (A.card : ℝ) * C_freq * failure_prob_sum_2 x_nat < 1)
    (hS_pos : (CandidateSet x_nat W b).card > 0) :
    (UnionBadSets x_nat W b A).card < (CandidateSet x_nat W b).card := by
      have h_union_bad_sets_card_bound : (UnionBadSets x_nat W b A).card ≤ (CandidateSet x_nat W b).card * C_freq * (A.card : ℝ) * failure_prob_sum_2 x_nat := by
        refine le_trans ( UnionBadSets_card_bound x_nat W b A hL ?_ ?_ ) ?_
        · exact hW.symm ▸ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
        · exact fun p a => W_coprime_primes x_nat W hW p a
        · gcongr
          · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( C_freq_pos ) ) ) ( Nat.cast_nonneg _ )
          · have hL_real :
                ((⌊(x_nat : ℝ)⌋₊ - ⌈(x_nat : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) ≥
                  (x_nat : ℝ) / 2 := by
                norm_num [Nat.floor_natCast]
                linarith [Nat.ceil_lt_add_one (show 0 ≤ (x_nat : ℝ) / 2 by positivity)]
            have hsum :=
              sum_bound_inequality (x_nat : ℝ) (by linarith)
                ((⌊(x_nat : ℝ)⌋₊ - ⌈(x_nat : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ)
                hL_real (W : ℝ) (congrArg Nat.cast hW)
            simpa [PrimesInInterval, failure_prob_sum_2, Nat.floor_natCast] using hsum
      have hS_pos_real : (0 : ℝ) < (CandidateSet x_nat W b).card := by
        exact_mod_cast hS_pos
      have h_bound_lt :
          (CandidateSet x_nat W b).card * C_freq * (A.card : ℝ) *
              failure_prob_sum_2 x_nat <
            (CandidateSet x_nat W b).card := by
        calc
          (CandidateSet x_nat W b).card * C_freq * (A.card : ℝ) *
              failure_prob_sum_2 x_nat
              = (CandidateSet x_nat W b).card *
                  ((A.card : ℝ) * C_freq * failure_prob_sum_2 x_nat) := by
                    ring
          _ < (CandidateSet x_nat W b).card * 1 := by
                    exact mul_lt_mul_of_pos_left h_prob hS_pos_real
          _ = (CandidateSet x_nat W b).card := by ring
      exact_mod_cast lt_of_le_of_lt h_union_bad_sets_card_bound h_bound_lt

lemma exists_good_n_final (x_nat : ℕ) (hx : (x_nat : ℝ) ≥ 100) (W : ℕ) (hW : W = W_val x_nat) (b : ℕ) (A : Finset ℕ)
    (hA_subset : ∀ a ∈ A, a ≤ x_nat)
    (hA_admissible : ∀ p, p ∣ W → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W)
    (h_prob : (A.card : ℝ) * C_freq * failure_prob_sum_2 x_nat < 1) :
    ∃ n ∈ Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ)), (n + b) % W = 0 ∧ ∀ a ∈ A, Squarefree (n + a) := by
      obtain ⟨n, hn⟩ : ∃ n ∈ CandidateSet x_nat W b, n ∉ UnionBadSets x_nat W b A := by
        have h_card_lt_S_card : (UnionBadSets x_nat W b A).card < (CandidateSet x_nat W b).card := by
          apply UnionBadSets_card_lt_S_card x_nat hx W hW b A hL h_prob (by
          convert CandidateSet_nonempty x_nat W b hL _
          · exact Finset.card_pos
          · exact hW.symm ▸ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2)
        exact Finset.not_subset.mp fun h => h_card_lt_S_card.not_ge <| Finset.card_le_card h
      refine ⟨ n, ?_, ?_, ?_ ⟩ <;> simp_all +decide
      · unfold CandidateSet at hn
        aesop
      · unfold CandidateSet at hn
        aesop
      · intro a ha
        have h_not_div : ∀ p, Nat.Prime p → p^2 ∣ (n + a) → False := by
          intro p hp hp_div
          by_cases hp_le : p ≤ Nat.floor (0.1 * Real.log x_nat)
          · -- Since $p \leq \lfloor 0.1 \log x_nat \rfloor$, we have $p^2 \mid W$.
            have hp_sq_div_W : p^2 ∣ W_val x_nat := by
              refine Finset.dvd_prod_of_mem (fun p : ℕ => p ^ 2) ?_
              exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le hp_le ), hp ⟩
            -- Since $p^2 \mid W$, we have $n \equiv -b \pmod{p^2}$.
            have hn_mod_p2 : n ≡ -b [ZMOD p^2] := by
              have hn_mod_p2 : (n + b) % p^2 = 0 := by
                exact Nat.mod_eq_zero_of_dvd ( dvd_trans hp_sq_div_W ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hn.1 |>.2 ) ) )
              exact Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using Nat.dvd_of_mod_eq_zero hn_mod_p2
            have hn_mod_p2 : (n + a : ℤ) ≡ (a - b : ℤ) [ZMOD p^2] := by
              convert hn_mod_p2.add_right a using 1
              ring
            have hn_mod_p2 : (a - b : ℤ) ≡ 0 [ZMOD p^2] := by
              exact hn_mod_p2.symm.trans ( Int.modEq_zero_iff_dvd.mpr <| mod_cast hp_div )
            exact hA_admissible p ( dvd_trans ( dvd_pow_self _ two_ne_zero ) hp_sq_div_W ) hp a ha ( Nat.ModEq.symm <| Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hn_mod_p2.symm.dvd )
          · by_cases hp_ge : p ≤ Nat.floor (Real.sqrt (2 * x_nat))
            · contrapose! hn
              simp_all +decide [ CandidateSet, UnionBadSets, BadSet ]
              refine fun _ _ _ => ⟨ a, ha, p, ?_, ?_ ⟩ <;> norm_num [ PrimesInInterval ] at *
              · constructor
                · omega
                · exact ⟨Nat.lt_of_floor_lt hp_le, Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hp_ge ), hp⟩
              · exact Nat.mod_eq_zero_of_dvd hp_div
            · have h_contra : p^2 > 2 * x_nat := by
                exact_mod_cast ( by nlinarith only [ Nat.lt_floor_add_one ( Real.sqrt ( 2 * x_nat ) ), Real.sqrt_nonneg ( 2 * x_nat ), Real.mul_self_sqrt ( show 0 ≤ 2 * ( x_nat : ℝ ) by positivity ), show ( p : ℝ ) ≥ ⌊Real.sqrt ( 2 * x_nat ) ⌋₊ + 1 by exact_mod_cast not_le.mp hp_ge ] : ( p : ℝ ) ^ 2 > 2 * x_nat )
              have h_contra : n + a ≤ 2 * x_nat := by
                have h_contra : n ≤ x_nat := by
                  exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hn.1 |>.1 ) |>.2.trans ( Nat.floor_le_of_le ( by norm_num ) )
                linarith [ hA_subset a ha ]
              have h_contra : n + a = 0 := by
                exact Nat.eq_zero_of_dvd_of_lt hp_div ( by linarith )
              simp_all +decide [ CandidateSet ]
              exact hn.1.1.not_gt ( by positivity )
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => fun h => h_not_div p hp <| by simpa only [ sq ] using h

/-
If a set A satisfies the growth condition for a constant C, and C satisfies the probability condition, then A has Property Q.
-/
lemma sufficient_condition_for_Q  (A : Set ℕ) (hA_adm : Admissible A) (hA_inf : A.Infinite) (C : ℝ)
    (h_prob : ∀ᶠ j in Filter.atTop, ∀ x, x ≥ Real.exp (C * j / Real.log j) → (j : ℝ) * C_freq * failure_prob_sum_2 x < 1)
    (h_growth : GrowthCondition A C) : PropertyQ A := by
      obtain ⟨J, hJ⟩ : ∃ J : ℕ → ℕ, StrictMono J ∧ ∀ k, (Nat.nth (· ∈ A) (J k - 1) : ℝ) ≥ Real.exp (C * J k / Real.log (J k)) := by
        rw [ GrowthCondition ] at h_growth
        rw [ Filter.frequently_atTop' ] at h_growth
        exact ⟨ fun k => Nat.recOn k ( Nat.find ( h_growth 0 ) ) fun k ih => Nat.find ( h_growth ih ), strictMono_nat_of_lt_succ fun k => Nat.find_spec ( h_growth _ ) |>.1, fun k => Nat.recOn k ( Nat.find_spec ( h_growth 0 ) |>.2 ) fun k ih => Nat.find_spec ( h_growth _ ) |>.2 ⟩
      -- For sufficiently large k, apply exists_good_n_final to find n in [x/2, x] such that n+a is squarefree for all a in A with a < n.
      have h_exists_good_n : ∀ᶠ k in Filter.atTop, ∃ n ∈ Finset.Icc (Nat.ceil ((Nat.nth (· ∈ A) (J k - 1) : ℝ) / 2)) (Nat.floor (Nat.nth (· ∈ A) (J k - 1) : ℝ)), ∀ a ∈ A, a < n → Squarefree (n + a) := by
        have h_exists_good_n : ∀ᶠ k in Filter.atTop, (Nat.nth (· ∈ A) (J k - 1) : ℝ) ≥ 100 ∧ (J k : ℝ) * C_freq * failure_prob_sum_2 (Nat.nth (· ∈ A) (J k - 1)) < 1 ∧ (Nat.floor (Nat.nth (· ∈ A) (J k - 1) : ℝ) - Nat.ceil ((Nat.nth (· ∈ A) (J k - 1) : ℝ) / 2) + 1 : ℝ) ≥ W_val (Nat.nth (· ∈ A) (J k - 1)) := by
          have h_exists_good_n : ∀ᶠ k in Filter.atTop, (Nat.nth (· ∈ A) (J k - 1) : ℝ) ≥ 100 ∧ (J k : ℝ) * C_freq * failure_prob_sum_2 (Nat.nth (· ∈ A) (J k - 1)) < 1 := by
            have h_exists_good_n : ∀ᶠ k in Filter.atTop, (Nat.nth (· ∈ A) (J k - 1) : ℝ) ≥ 100 := by
              have h_exists_good_n : Filter.Tendsto (fun k => (Nat.nth (· ∈ A) (J k - 1) : ℝ)) Filter.atTop Filter.atTop := by
                refine tendsto_natCast_atTop_atTop.comp ( Nat.nth_strictMono hA_inf |> StrictMono.tendsto_atTop |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 1 |> Filter.Tendsto.comp <| hJ.1.tendsto_atTop )
              exact h_exists_good_n.eventually_ge_atTop 100
            filter_upwards [ h_exists_good_n, h_prob.natCast_atTop.filter_mono hJ.1.tendsto_atTop ] with k hk₁ hk₂ using ⟨ hk₁, hk₂ _ ( hJ.2 k ) ⟩
          have h_length_condition : ∀ᶠ x in Filter.atTop, (Nat.floor x - Nat.ceil (x / 2) + 1 : ℝ) ≥ W_val x := by
            convert length_condition using 1
          have h_length_condition : Filter.Tendsto (fun k => (Nat.nth (· ∈ A) (J k - 1) : ℝ)) Filter.atTop Filter.atTop := by
            refine tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_atTop.mpr ?_ )
            intro b
            use b + 1
            intro a ha
            refine le_trans ?_ ( Nat.le_nth ?_ )
            · exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ha ( hJ.1.id_le _ ) )
            · exact fun hf => False.elim <| hA_inf <| hf.subset fun x hx => hx
          filter_upwards [ h_exists_good_n, h_length_condition.eventually ‹_› ] with k hk₁ hk₂ using ⟨ hk₁.1, hk₁.2, hk₂ ⟩
        filter_upwards [ h_exists_good_n ] with k hk
        have := exists_good_n_final ( Nat.nth ( fun x => x ∈ A ) ( J k - 1 ) ) hk.1 ( W_val ( Nat.nth ( fun x => x ∈ A ) ( J k - 1 ) ) ) rfl ( Classical.choose ( admissible_to_b_W_val A hA_adm ( Nat.nth ( fun x => x ∈ A ) ( J k - 1 ) ) ) ) ( Finset.filter ( fun a => a < Nat.nth ( fun x => x ∈ A ) ( J k - 1 ) ) ( Finset.image ( fun n => Nat.nth ( fun x => x ∈ A ) n ) ( Finset.range ( J k ) ) ) ) ?_ ?_ ?_ ?_
        · obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := this
          refine ⟨ n, hn₁, fun a ha ha' => ?_ ⟩
          by_cases ha'' : a < Nat.nth (fun x => x ∈ A) (J k - 1)
          · have := Nat.nth_mem_of_infinite hA_inf ( Nat.count ( fun x => x ∈ A ) a )
            simp_all +decide
            convert hn₃ ( Nat.count ( fun x => x ∈ A ) a ) _ _ using 1
            · rw [ Nat.nth_count ]
              aesop
            · contrapose! ha''
              refine Nat.le_of_lt_succ ?_
              refine Nat.nth_lt_of_lt_count ?_
              grind
            · rw [ Nat.nth_count ]
              focus
                aesop
              assumption
          · simp +zetaDelta at *
            grind +splitImp
        · exact fun x hx => le_of_lt <| Finset.mem_filter.mp hx |>.2
        · intro p hp hp_prime a ha
          have := Classical.choose_spec ( admissible_to_b_W_val A hA_adm ( Nat.nth ( fun x => x ∈ A ) ( J k - 1 ) ) ) p hp hp_prime
          simp +zetaDelta at *
          exact this a ( by obtain ⟨ i, hi, rfl ⟩ := ha.1; exact Nat.nth_mem_of_infinite hA_inf _ )
        · norm_cast at *
          rw [ Int.subNatNat_of_le ] at hk <;> norm_cast at *
          focus
            aesop
          rw [ Nat.ceil_le ]
          rw [ Nat.floor_natCast ]
          linarith
        · refine lt_of_le_of_lt ?_ hk.2.1
          gcongr
          · exact Finset.sum_nonneg fun _ _ => add_nonneg ( one_div_nonneg.mpr ( sq_nonneg _ ) ) ( div_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) )
          · exact le_of_lt ( C_freq_pos )
          · exact le_trans ( Finset.card_filter_le _ _ ) ( Finset.card_image_le.trans ( by simp ) )
      have h_inf_good_n : Set.Infinite {n : ℕ | ∃ k, n ∈ Finset.Icc (Nat.ceil ((Nat.nth (· ∈ A) (J k - 1) : ℝ) / 2)) (Nat.floor (Nat.nth (· ∈ A) (J k - 1) : ℝ)) ∧ ∀ a ∈ A, a < n → Squarefree (n + a)} := by
        have h_inf_good_n : Filter.Tendsto (fun k => Nat.nth (· ∈ A) (J k - 1)) Filter.atTop Filter.atTop := by
          refine Filter.tendsto_atTop_atTop.mpr ?_
          intro b
          use b + 1
          intro a ha
          refine le_trans ?_ ( Nat.le_nth ?_ )
          · exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ha ( hJ.1.id_le _ ) )
          · exact fun hf => False.elim <| hA_inf <| hf.subset fun x hx => hx
        rw [ Filter.tendsto_atTop_atTop ] at h_inf_good_n
        rw [ Filter.eventually_atTop ] at h_exists_good_n
        obtain ⟨ a, ha ⟩ := h_exists_good_n
        refine Set.infinite_of_forall_exists_gt ?_
        intro b
        obtain ⟨ i, hi ⟩ := h_inf_good_n ( 2 * b + 2 )
        obtain ⟨ n, hn₁, hn₂ ⟩ := ha ( Max.max a i ) ( le_max_left _ _ )
        use n
        simp_all +decide [Nat.ceil_le]
        exact ⟨ ⟨ _, hn₁ ⟩, by rw [ div_le_iff₀ ] at hn₁ <;> norm_cast at * ; linarith [ hi ( Max.max a i ) ( le_max_right a i ) ] ⟩
      exact h_inf_good_n.mono fun n hn => by
        obtain ⟨ k, hk₁, hk₂ ⟩ := hn
        exact hk₂

/-
There is an absolute constant C such that, if A is an admissible sequence with a_j >= exp(C j / log j) for infinitely many j, then A has property Q.
-/
theorem Theorem_suff :
  ∃ C > 0, ∀ A : Set ℕ, Admissible A → A.Infinite → GrowthCondition A C → PropertyQ A := by
    -- Apply the lemma prob_condition_of_growth_v2 to obtain the constant C.
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ᶠ j in Filter.atTop, ∀ x, x ≥ Real.exp (C * j / Real.log j) → (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      exact prob_condition_of_growth_v2
    refine ⟨ C, hC_pos, ?_ ⟩
    intro A hA_adm hA_inf h_growth
    apply sufficient_condition_for_Q A hA_adm hA_inf C
    · exact hC
    · assumption

#print axioms Theorem_suff
-- 'Erdos1102d.Theorem_suff' depends on axioms: [propext, Classical.choice, Quot.sound]

/-
The sequence A1 has property Q.
-/
theorem A1_PropertyQ : PropertyQ A1 := by
  obtain ⟨C, _, hC⟩ := Theorem_suff
  exact hC A1 A1_admissible A1_infinite ( A1_growth C )

/-
The sequence A2 has property Q.
-/
theorem A2_PropertyQ : PropertyQ A2 := by
  -- By Theorem_suff, there exists a constant C > 0 such that any admissible infinite sequence satisfying the growth condition for C has Property Q.
  obtain ⟨C, _, hC⟩ := Theorem_suff
  exact hC _ A2_admissible A2_infinite ( A2_growth C )

/-
The sequence A3 has property Q.
-/
theorem A3_PropertyQ : PropertyQ A3 := by
  -- By Theorem_suff, there exists a constant C > 0 such that any admissible infinite sequence satisfying the growth condition for C has Property Q.
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ A : Set ℕ, Admissible A → A.Infinite → GrowthCondition A C → PropertyQ A := by
    exact Theorem_suff
  exact hC A3 A3_admissible A3_infinite ( A3_growth C )

/-
The sequence A4 has property Q.
-/
theorem A4_PropertyQ : PropertyQ A4 := by
  obtain ⟨C, hC_pos, hC⟩ := Theorem_suff
  apply hC A4 A4_admissible A4_infinite
  -- To show that A4 satisfies the growth condition with any constant C, we need to find infinitely many j such that the j-th element of A4 is at least exp(C*j/log j).
  have h_growth_A4 : ∀ C > 0, ∃ᶠ j in Filter.atTop, (Nat.nth (· ∈ A4) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) := by
    intro C hC_pos
    have h_growth_A4 : ∀ᶠ j in Filter.atTop, (Nat.factorial (j + 1) - 1 : ℝ) ≥ Real.exp (C * j / Real.log j) := by
      -- We'll use that $j!$ grows faster than any exponential function.
      have h_factorial_growth : Filter.Tendsto (fun j : ℕ => Real.exp (C * j / Real.log j) / (j ! : ℝ)) Filter.atTop (nhds 0) := by
        have h_factorial_growth : Filter.Tendsto (fun j : ℕ => Real.exp (C * j) / (j ! : ℝ)) Filter.atTop (nhds 0) := by
          have h_factorial_growth : Summable (fun j : ℕ => Real.exp (C * j) / (j ! : ℝ)) := by
            have := Real.summable_pow_div_factorial ( Real.exp C )
            simpa [ Real.exp_mul ] using this
          convert h_factorial_growth.tendsto_atTop_zero
        refine squeeze_zero_norm' ?_ h_factorial_growth
        exact Filter.eventually_atTop.mpr ⟨ 3, fun n hn => by
          rw [Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _))]
          exact div_le_div_of_nonneg_right (Real.exp_le_exp_of_le (div_le_self (by positivity) (Real.le_log_iff_exp_le (by positivity) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [show (n : ℝ) ≥ 3 by norm_cast]))) (Nat.cast_nonneg _) ⟩
      filter_upwards [ h_factorial_growth.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂
      rw [ div_lt_one ( by positivity ) ] at hj₁
      exact le_trans hj₁.le ( le_tsub_of_add_le_right <| mod_cast by nlinarith [ Nat.factorial_pos j, Nat.factorial_succ j ] )
    refine Filter.Eventually.frequently ?_
    filter_upwards [ h_growth_A4, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂
    rw [ A4_nth ]
    rw [ Nat.cast_sub <| Nat.factorial_pos _ ]
    cases j <;> simp [Nat.factorial] at * ; linarith
  exact h_growth_A4 C hC_pos

/-
All four sequences A1, A2, A3, A4 have property Q.
-/
theorem All_Sequences_PropertyQ : PropertyQ A1 ∧ PropertyQ A2 ∧ PropertyQ A3 ∧ PropertyQ A4 := by
  exact ⟨A1_PropertyQ, A2_PropertyQ, A3_PropertyQ, A4_PropertyQ⟩

#print axioms All_Sequences_PropertyQ
-- 'Erdos1102d.All_Sequences_PropertyQ' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end
end Erdos1102d
