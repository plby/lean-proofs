/-

This is a Lean formalization of a solution to Erdős Problem 370.
https://www.erdosproblems.com/370

The original human proof was found by: Stefan Steinerberger

https://www.erdosproblems.com/370

ChatGPT 5.1 Pro from OpenAI explained some proof of this result (not
necessarily the original human proof, instead prioritizing clarity).

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.

The proof is verified by Lean.  The exact version numbers below may be
necessary to type-check this proof.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

-/
import Mathlib

namespace Erdos370

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

#check Nat.minFac

#check Nat.Prime

#check Nat.divisors

#check Nat.primeFactors

def P (n : ℕ) : ℕ := (Nat.primeFactors n).max.getD 1

def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n
#check Real.sqrt

lemma lem_threeconsecutive (k : ℕ) (hk : 3 ≤ k) :
  let m := k.factorial + 3
  Composite (m - 1) ∧ Composite m ∧ Composite (m + 1) := by
    aesop;
    · exact ⟨ by linarith [ Nat.self_le_factorial k ], fun h => absurd ( h.eq_two_or_odd'.resolve_left <| by linarith [ Nat.self_le_factorial k ] ) <| by rw [ Nat.odd_iff ] ; exact by rw [ Nat.add_mod ] ; norm_num [ Nat.mod_eq_zero_of_dvd ( Nat.dvd_factorial ( by linarith ) ( by linarith : k ≥ 2 ) ) ] ⟩;
    · -- Since $k!$ is divisible by $3$ for $k \geq 3$, $k! + 3$ is also divisible by $3$.
      have h_div3 : 3 ∣ m := by
        exact Nat.dvd_add ( Nat.dvd_factorial ( by decide ) hk ) ( by decide );
      refine' ⟨ _, _ ⟩;
      · grind;
      · -- Since $m$ is divisible by $3$ and greater than $3$, it cannot be prime.
        have h_not_prime : 3 < m → ¬Nat.Prime m := by
          exact fun h => fun h' => by rw [ h'.dvd_iff_eq ] at h_div3 <;> linarith;
        exact h_not_prime ( by exact lt_add_of_pos_of_le ( Nat.factorial_pos _ ) ( by decide ) );
    · -- For $k \geq 3$, $k! + 4$ is even and greater than $2$, hence composite.
      have h_even : Even (k.factorial + 4) := by
        exact even_iff_two_dvd.mpr ( dvd_add ( Nat.dvd_factorial ( by linarith ) ( by linarith ) ) ( by decide ) );
      exact ⟨ by linarith [ Nat.self_le_factorial k ], by rintro h; exact absurd ( h.even_iff.mp h_even ) ( by linarith [ Nat.self_le_factorial k ] ) ⟩


#check Set.Infinite

lemma lem_construction (m : ℕ) (hm : m ≥ 3)
  (h1 : Composite (m - 1)) (h2 : Composite m) (h3 : Composite (m + 1)) :
  let n := m^2 - 1
  (P n : ℝ) < Real.sqrt n ∧ (P (n + 1) : ℝ) < Real.sqrt (n + 1) := by
    -- Let's first show that $P(n) < \sqrt{n}$.
    have hPn : (P (m ^ 2 - 1) : ℝ) < Real.sqrt (m ^ 2 - 1) := by
      -- Since $m-1$ and $m+1$ are composite, their largest prime factors are at most $(m-1)/2$ and $(m+1)/2$ respectively.
      have h_prime_factors : (P (m ^ 2 - 1) : ℝ) ≤ (m + 1) / 2 := by
        -- Since $m-1$ and $m+1$ are composite, write $m-1=(a)(b)$ and $m+1=(c)(d)$ with $a,b,c,d\ge 2$. Then every prime factor of $m-1$ and $m+1$ is at most $\frac{m-1}{2}$ and $\frac{m+1}{2}$, respectively.
        have h_factors : ∀ p, Nat.Prime p → p ∣ m - 1 → p ≤ (m - 1) / 2 := by
          rcases m with ( _ | _ | m ) <;> simp_all +decide;
          intro p pp dp; rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; rcases dp with ⟨ q, hq ⟩ ; rcases q with ( _ | _ | q ) <;> simp_all! +arith +decide [ Nat.prime_mul_iff ] ;
          · cases h1 ; aesop;
          · bound
        have h_factors' : ∀ p, Nat.Prime p → p ∣ m + 1 → p ≤ (m + 1) / 2 := by
          intro p pp dp; rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; rcases dp with ⟨ q, hq ⟩ ; rcases q with ( _ | _ | q ) <;> simp_all +arith +decide [ Nat.prime_mul_iff ] ;
          · cases h3 ; aesop;
          · nlinarith;
        -- Therefore, $P(n) = \max\{P(m-1), P(m+1)\} \leq \max\{\frac{m-1}{2}, \frac{m+1}{2}\} = \frac{m+1}{2}$.
        have h_P_n : (P (m^2 - 1)) ≤ max ((m - 1) / 2) ((m + 1) / 2) := by
          -- By definition of $P$, we know that $P(n) = \max\{p \mid n\}$.
          unfold P;
          -- Since $m^2 - 1 = (m - 1)(m + 1)$, the prime factors of $m^2 - 1$ are the union of the prime factors of $m - 1$ and $m + 1$.
          have h_prime_factors : (m ^ 2 - 1).primeFactors = (m - 1).primeFactors ∪ (m + 1).primeFactors := by
            rw [ show m ^ 2 - 1 = ( m - 1 ) * ( m + 1 ) by convert Nat.sq_sub_sq m 1 using 1; ring, Nat.primeFactors_mul ] <;> aesop;
            cases h_factors 2 Nat.prime_two;
          rcases x : Finset.max ( m ^ 2 - 1 |> Nat.primeFactors ) with ( _ | ⟨ p, hp ⟩ ) <;> aesop;
          · omega;
          · have := Finset.mem_of_max x; aesop;
        exact le_trans ( Nat.cast_le.mpr h_P_n ) ( by rw [ max_def_lt ] ; split_ifs <;> rw [ le_div_iff₀ ] <;> norm_cast <;> omega );
      exact lt_of_le_of_lt h_prime_factors <| Real.lt_sqrt_of_sq_lt <| by nlinarith [ show ( m : ℝ ) ≥ 3 by norm_cast ] ;
    refine' ⟨ hPn.trans_le _, _ ⟩;
    · rw [ Nat.cast_sub ] <;> norm_num ; nlinarith;
    · -- Since $n+1=m^{2}$, we have $P(n+1)=P(m^{2})=P(m)\le \frac{m}{2}<m=\sqrt{n+1}$.
      have hPn1 : (P (m ^ 2) : ℝ) < m := by
        unfold P; aesop;
        -- Since $m$ is composite, its largest prime factor is less than $m$.
        have hPm : (m.primeFactors.max.getD 1 : ℕ) < m := by
          -- Since $m$ is composite, its largest prime factor $P(m)$ is less than $m$. Use this fact.
          have hPm_lt_m : ∀ p ∈ m.primeFactors, p < m := by
            exact fun p hp => lt_of_le_of_ne ( Nat.le_of_mem_primeFactors hp ) fun con => h2.2 <| con ▸ Nat.prime_of_mem_primeFactors hp;
          have := Finset.max_of_nonempty ( Finset.nonempty_of_ne_empty ( by aesop_cat : m.primeFactors ≠ ∅ ) ) ; aesop;
          have := Finset.mem_of_max h; aesop;
        rw [ Nat.primeFactors_pow ] <;> aesop;
      rw [ Nat.sub_add_cancel ( by nlinarith ) ] ; aesop;
      rw [ Nat.cast_sub ] <;> norm_num ; nlinarith [ ( by norm_cast : ( 3 :ℝ ) ≤ m ), Real.sqrt_nonneg ( m^2 - 1 + 1 ), Real.mul_self_sqrt ( show 0 ≤ ( m^2 - 1 + 1 :ℝ ) by nlinarith [ ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) ];
      nlinarith


theorem infinitely_many_n : Set.Infinite { n : ℕ | (P n : ℝ) < Real.sqrt n ∧ (P (n + 1) : ℝ) < Real.sqrt (n + 1) } := by
  -- By lemma_threeconsecutive, for every $k \geq 3$, $n = (k! + 3)^2 - 1$ satisfies the conditions.
  have h_infinite : ∀ k : ℕ, 3 ≤ k → (let n := (Nat.factorial k + 3)^2 - 1;
    P n < Real.sqrt n ∧ P (n + 1) < Real.sqrt (n + 1)) := by
      intros k hk_ge_3
      apply lem_construction (Nat.factorial k + 3);
      · grind;
      · refine ⟨ ?_, ?_ ⟩;
        · exact lt_tsub_iff_left.mpr ( by linarith [ Nat.self_le_factorial k ] );
        · rw [ Nat.prime_def_lt' ];
          exact fun h => h.2 2 ( by decide ) ( lt_tsub_iff_left.mpr ( by linarith [ Nat.self_le_factorial k ] ) ) ( Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_eq_zero_of_dvd ( Nat.dvd_factorial ( by decide ) ( show k ≥ 2 by linarith ) ) ] ) );
      · -- Since $k \geq 3$, $k!$ is divisible by $3$, hence $k! + 3$ is also divisible by $3$.
        have h_div3 : 3 ∣ (Nat.factorial k + 3) := by
          field_simp;
          exact Nat.dvd_factorial ( by decide ) hk_ge_3;
        exact ⟨ by linarith [ Nat.self_le_factorial k ], by rintro H; have := Nat.prime_dvd_prime_iff_eq Nat.prime_three H; aesop ; linarith [ Nat.self_le_factorial k ] ⟩;
      · exact ⟨ by linarith [ Nat.self_le_factorial k ], by rw [ show k.factorial + 3 + 1 = 2 * ( k.factorial / 2 + 2 ) by linarith [ Nat.div_mul_cancel ( show 2 ∣ k.factorial from Nat.dvd_factorial ( by linarith ) ( by linarith ) ) ] ] ; exact Nat.not_prime_mul ( by linarith ) ( by linarith [ Nat.div_add_mod ( k.factorial ) 2, Nat.mod_lt ( k.factorial ) two_pos ] ) ⟩;
  rw [ Set.infinite_iff_exists_gt ];
  refine' fun a => ⟨ _, h_infinite ( a + 3 ) <| by linarith, lt_tsub_iff_right.mpr <| by nlinarith [ Nat.self_le_factorial ( a + 3 ) ] ⟩

noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}

theorem erdos_370 :
  { n | maxPrimeFac n < √n ∧ maxPrimeFac (n + 1) < √(n + 1) }.Infinite ↔ True := by
  refine iff_of_true ?_ trivial;
  -- Apply the fact that the set is infinite to conclude the proof.
  apply Set.Infinite.mono (by
  unfold P; aesop;
  · -- Since `Option.getD a.primeFactors.max 1` is the same as `a.maxPrimeFac`, we can rewrite the goal.
    convert a_1 using 1;
    unfold maxPrimeFac; aesop;
    -- Since the prime factors of a are finite, their maximum exists and is equal to the supremum.
    have h_max_prime_factors : ∀ {S : Finset ℕ}, S.Nonempty → sSup {p : ℕ | p ∈ S} = S.max.getD 1 := by
      intro S hS; rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> aesop;
      · have := Finset.le_max a_4; aesop;
        cases h : Finset.max S <;> aesop;
      · have := Finset.max_of_nonempty hS; aesop;
        exact ⟨ w_1, Finset.mem_of_max h, a_3 ⟩;
    by_cases ha : a.primeFactors.Nonempty <;> aesop;
    · -- Apply the lemma that states the supremum of a nonempty finite set is its maximum element.
      convert h_max_prime_factors (Finset.nonempty_of_ne_empty (by
      aesop : a.primeFactors ≠ ∅)) using 1
      generalize_proofs at *;
      exact congr_arg _ ( by ext; aesop );
    · interval_cases a <;> norm_num at *;
      · contradiction;
      · contradiction;
  · -- Since $a$ is composite, its maximum prime factor is less than $\sqrt{a}$.
    have h_max_prime_factor : ∀ {n : ℕ}, 1 < n → maxPrimeFac n = (Nat.primeFactors n).max.getD 1 := by
      unfold maxPrimeFac; aesop;
      -- The maximum element of a finite set is equal to its supremum.
      have h_max_eq_sup : ∀ {S : Finset ℕ}, S.Nonempty → (S.max.getD 1) = sSup S := by
        intros S hS_nonempty; exact (by
        -- The maximum element of a finite set is equal to its supremum by definition.
        have h_max_eq_sup : ∀ {S : Finset ℕ}, S.Nonempty → (S.max.getD 1) = sSup S := by
          intros S hS_nonempty
          have h_max : S.max = some (sSup S) := by
            exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| le_csSup ( Finset.bddAbove S ) hx ) ( Finset.le_sup ( f := WithBot.some ) <| show SupSet.sSup ( S : Set ℕ ) ∈ S from by exact ( IsCompact.sSup_mem ( show IsCompact ( S : Set ℕ ) from S.finite_toSet.isCompact ) <| by exact Set.nonempty_of_mem <| Finset.mem_coe.mpr hS_nonempty.choose_spec ) )
          exact h_max.symm ▸ rfl
        generalize_proofs at *;
        exact h_max_eq_sup hS_nonempty);
      rw [ h_max_eq_sup ];
      · congr with p ; aesop;
      · exact Finset.nonempty_of_ne_empty ( by aesop );
    rcases a with ( _ | _ | a ) <;> simp_all +arith +decide [ maxPrimeFac ]) (infinitely_many_n)

end

end Erdos370
