/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 370.
https://www.erdosproblems.com/forum/thread/370

Informal authors:
- Stefan Steinerberger
- ChatGPT 5.1 Pro

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos370.md
-/
import Mathlib

namespace Erdos370

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def P (n : ℕ) : ℕ := (Nat.primeFactors n).max.getD 1

def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

lemma lem_threeconsecutive (k : ℕ) (hk : 3 ≤ k) :
  let m := k.factorial + 3
  Composite (m - 1) ∧ Composite m ∧ Composite (m + 1) := by
  change Composite (k.factorial + 3 - 1) ∧ Composite (k.factorial + 3) ∧
    Composite (k.factorial + 3 + 1)
  dsimp [Composite]
  constructor
  · constructor
    · linarith [Nat.self_le_factorial k]
    · intro h
      have hne : k.factorial + 3 - 1 ≠ 2 := by
        have hkfac : 3 ≤ k.factorial := le_trans hk (Nat.self_le_factorial k)
        omega
      have hodd : Odd (k.factorial + 3 - 1) := h.eq_two_or_odd'.resolve_left hne
      rw [Nat.odd_iff] at hodd
      have hmod : (k.factorial + 3 - 1) % 2 = 0 := by
        rw [show k.factorial + 3 - 1 = k.factorial + 2 by omega]
        rw [Nat.add_mod]
        norm_num [Nat.mod_eq_zero_of_dvd
          (Nat.dvd_factorial (by linarith) (by linarith : k ≥ 2))]
      omega
  · constructor
    · -- Since $k!$ is divisible by $3$ for $k \geq 3$, $k! + 3$ is also divisible by $3$.
      have h_div3 : 3 ∣ k.factorial + 3 := by
        exact Nat.dvd_add (Nat.dvd_factorial (by decide) hk) (by decide)
      constructor
      · linarith [Nat.factorial_pos k]
      · -- Since $k! + 3$ is divisible by $3$ and greater than $3$, it cannot be prime.
        have h_not_prime : 3 < k.factorial + 3 → ¬Nat.Prime (k.factorial + 3) := by
          exact fun h => fun h' => by rw [h'.dvd_iff_eq] at h_div3 <;> linarith
        exact h_not_prime (by exact lt_add_of_pos_of_le (Nat.factorial_pos _) (by decide))
    · -- For $k \geq 3$, $k! + 4$ is even and greater than $2$, hence composite.
      have h_even : Even (k.factorial + 3 + 1) := by
        rw [show k.factorial + 3 + 1 = k.factorial + 4 by omega]
        exact even_iff_two_dvd.mpr
          (dvd_add (Nat.dvd_factorial (by linarith) (by linarith)) (by decide))
      exact
        ⟨by linarith [Nat.self_le_factorial k],
          by
            rintro h
            exact absurd (h.even_iff.mp h_even) (by linarith [Nat.self_le_factorial k])⟩


lemma lem_construction (m : ℕ) (hm : m ≥ 3)
  (h1 : Composite (m - 1)) (h2 : Composite m) (h3 : Composite (m + 1)) :
  let n := m^2 - 1
  (P n : ℝ) < Real.sqrt n ∧ (P (n + 1) : ℝ) < Real.sqrt (n + 1) := by
    -- Let's first show that $P(n) < \sqrt{n}$.
    have hPn : (P (m ^ 2 - 1) : ℝ) < Real.sqrt (m ^ 2 - 1) := by
      -- Since $m-1$ and $m+1$ are composite, their largest prime factors are at most $(m-1)/2$ and
      -- $(m+1)/2$ respectively.
      have h_prime_factors : (P (m ^ 2 - 1) : ℝ) ≤ (m + 1) / 2 := by
        -- Since $m-1$ and $m+1$ are composite, write $m-1=(a)(b)$ and $m+1=(c)(d)$ with $a,b,c,d\ge
        -- 2$. Then every prime factor of $m-1$ and $m+1$ is at most $\frac{m-1}{2}$ and
        -- $\frac{m+1}{2}$, respectively.
        have h_factors : ∀ p, Nat.Prime p → p ∣ m - 1 → p ≤ (m - 1) / 2 := by
          rcases m with (_ | _ | m) <;> simp_all +decide only [add_tsub_cancel_right]
          intro p pp dp
          rw [Nat.le_div_iff_mul_le zero_lt_two]
          rcases dp with ⟨q, hq⟩
          rcases q with (_ | _ | q) <;> simp_all! +arith +decide [Nat.prime_mul_iff]
          · cases h1
            subst hq
            simp_all only [Nat.reduceLeDiff]
          · bound
        have h_factors' : ∀ p, Nat.Prime p → p ∣ m + 1 → p ≤ (m + 1) / 2 := by
          intro p pp dp
          rw [Nat.le_div_iff_mul_le zero_lt_two]
          rcases dp with ⟨q, hq⟩
          rcases q with (_ | _ | q) <;> simp_all +arith +decide
          · cases h3
            subst hq
            simp_all only
          · nlinarith
        -- Therefore, $P(n) = \max\{P(m-1), P(m+1)\} \leq \max\{\frac{m-1}{2}, \frac{m+1}{2}\} =
        -- \frac{m+1}{2}$.
        have h_P_n : (P (m^2 - 1)) ≤ max ((m - 1) / 2) ((m + 1) / 2) := by
          -- By definition of $P$, we know that $P(n) = \max\{p \mid n\}$.
          unfold P
          -- Since $m^2 - 1 = (m - 1)(m + 1)$, the prime factors of $m^2 - 1$ are the union of the
          -- prime factors of $m - 1$ and $m + 1$.
          have h_prime_factors :
              (m ^ 2 - 1).primeFactors =
                (m - 1).primeFactors ∪ (m + 1).primeFactors := by
            rw [
              show m ^ 2 - 1 = (m - 1) * (m + 1) by
                convert Nat.sq_sub_sq m 1 using 1
                ring,
              Nat.primeFactors_mul
                (by
                  intro hzero
                  have htwo : 2 ∣ m - 1 := by
                    rw [hzero]
                    exact dvd_zero 2
                  have := h_factors 2 Nat.prime_two htwo
                  omega)
                (by omega),
            ]
          rcases x : Finset.max (m ^ 2 - 1 |> Nat.primeFactors) with _ | p
          · have hle : 1 ≤ (m + 1) / 2 := by
              rw [Nat.le_div_iff_mul_le zero_lt_two]
              omega
            simpa using le_trans hle (le_max_right ((m - 1) / 2) ((m + 1) / 2))
          · have hmem : p ∈ (m ^ 2 - 1).primeFactors := Finset.mem_of_max x
            rw [h_prime_factors] at hmem
            rcases Finset.mem_union.mp hmem with hp | hp
            · exact le_trans
                (h_factors p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
                (le_max_left ((m - 1) / 2) ((m + 1) / 2))
            · exact le_trans
                (h_factors' p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
                (le_max_right ((m - 1) / 2) ((m + 1) / 2))
        exact le_trans (Nat.cast_le.mpr h_P_n) (by
          rw [max_def_lt]
          split_ifs <;> rw [le_div_iff₀] <;> norm_cast <;> omega)
      exact lt_of_le_of_lt h_prime_factors <| Real.lt_sqrt_of_sq_lt <|
        by nlinarith [show (m : ℝ) ≥ 3 by norm_cast]
    refine ⟨hPn.trans_le ?_, ?_⟩
    · rw [Nat.cast_sub] <;> norm_num
      nlinarith
    · -- Since $n+1=m^{2}$, we have $P(n+1)=P(m^{2})=P(m)\le \frac{m}{2}<m=\sqrt{n+1}$.
      have hPn1 : (P (m ^ 2) : ℝ) < m := by
        unfold P
        -- Since $m$ is composite, its largest prime factor is less than $m$.
        have hPm : (m.primeFactors.max.getD 1 : ℕ) < m := by
          -- Since $m$ is composite, its largest prime factor $P(m)$ is less than $m$. Use this
          -- fact.
          have hPm_lt_m : ∀ p ∈ m.primeFactors, p < m := by
            exact fun p hp => lt_of_le_of_ne (Nat.le_of_mem_primeFactors hp) fun con => h2.2 <|
              con ▸ Nat.prime_of_mem_primeFactors hp
          obtain ⟨p, hpmax⟩ :=
            Finset.max_of_nonempty (s := m.primeFactors) (by simpa using h2.1)
          have hpmem : p ∈ m.primeFactors := Finset.mem_of_max hpmax
          simpa [hpmax] using hPm_lt_m p hpmem
        rw [Nat.primeFactors_pow]
        · simp_all only [ge_iff_le, Nat.cast_lt]
        · simp_all only [ge_iff_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      rw [Nat.sub_add_cancel (by nlinarith)]
      apply lt_of_lt_of_le hPn1
      rw [Nat.cast_sub]
      · norm_num
      · nlinarith

theorem infinitely_many_n : Set.Infinite { n : ℕ | (P n : ℝ) < Real.sqrt n ∧
  (P (n + 1) : ℝ) < Real.sqrt (n + 1) } := by
  -- Let's define the set S as the set of all natural numbers n for which the given conditions hold.
  set S := {n : ℕ | (P n : ℝ) < Real.sqrt n ∧ (P (n + 1) : ℝ) < Real.sqrt (n + 1)}
  -- We need to show that the set $S$ is infinite.
  have h_infinite : ∀ k ≥ 3, (k.factorial + 3)^2 - 1 ∈ S := by
    -- Let's choose any $k \geq 3$.
    intro k hk
    -- By Lemma lem_threeconsecutive, we know that $(k! + 3)^2 - 1$ satisfies the conditions.
    have h_lemma : let m := k.factorial + 3; Composite (m - 1) ∧ Composite m ∧ Composite (m + 1) :=
      by
      apply lem_threeconsecutive k hk
    -- Apply the lemma lem_construction with m = k! + 3.
    apply lem_construction (k.factorial + 3) (by linarith [Nat.self_le_factorial k])
      h_lemma.left h_lemma.right.left h_lemma.right.right
  exact Set.infinite_of_forall_exists_gt fun n => ⟨((n + 3) ! + 3) ^ 2 - 1,
    h_infinite _ (by linarith),
    lt_tsub_iff_left.mpr (by
      nlinarith [Nat.self_le_factorial (n + 3), Nat.factorial_pos (n + 3)])⟩



noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}

theorem erdos_370 :
  { n | maxPrimeFac n < √n ∧ maxPrimeFac (n + 1) < √(n + 1) }.Infinite ↔ True := by
  refine iff_of_true ?_ trivial
  have h_finset_sSup :
      ∀ {S : Finset ℕ}, S.Nonempty → (S.max.getD 1) = sSup (S : Set ℕ) := by
    intro S hS
    obtain ⟨p, hpmax⟩ := Finset.max_of_nonempty hS
    have hpmem : p ∈ S := Finset.mem_of_max hpmax
    apply le_antisymm
    · rw [hpmax]
      exact le_csSup (Finset.bddAbove S) (by simpa using hpmem)
    · rw [hpmax]
      exact csSup_le (Set.nonempty_of_mem (by simpa using hpmem)) (by
        intro q hq
        have hqS : q ∈ S := by simpa using hq
        have hqmax := Finset.le_max hqS
        rw [hpmax] at hqmax
        exact WithBot.coe_le_coe.mp hqmax)
  have h_max_prime_factor : ∀ {n : ℕ}, 1 < n → maxPrimeFac n = P n := by
    intro n hn
    have hnonempty : n.primeFactors.Nonempty := by simpa using hn
    unfold maxPrimeFac P
    rw [h_finset_sSup hnonempty]
    congr with p
    have hnzero : n ≠ 0 := by omega
    simp [Nat.mem_primeFactors_of_ne_zero hnzero]
  apply Set.Infinite.mono ?_ infinitely_many_n
  intro n hn
  rcases hn with ⟨hnP, hnP1⟩
  have hn_gt : 1 < n := by
    by_contra hnle
    rw [not_lt] at hnle
    have hn_small : n = 0 ∨ n = 1 := by omega
    rcases hn_small with rfl | rfl
    · have hP0 : P 0 = 1 := by
        unfold P
        simp only [Nat.primeFactors_zero, Finset.max_empty]
        rfl
      norm_num [hP0] at hnP
    · have hP1 : P 1 = 1 := by
        unfold P
        simp only [Nat.primeFactors_one, Finset.max_empty]
        rfl
      norm_num [hP1] at hnP
  have hn1_gt : 1 < n + 1 := by
    by_contra hnle
    rw [not_lt] at hnle
    have hn0 : n = 0 := by omega
    subst n
    have hP1 : P 1 = 1 := by
      unfold P
      simp only [Nat.primeFactors_one, Finset.max_empty]
      rfl
    norm_num [hP1] at hnP1
  constructor
  · simpa [h_max_prime_factor hn_gt] using hnP
  · simpa [h_max_prime_factor hn1_gt] using hnP1

#print axioms erdos_370
-- 'Erdos370.erdos_370' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos370
