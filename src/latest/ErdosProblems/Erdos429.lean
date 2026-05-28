/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 429.
https://www.erdosproblems.com/forum/thread/429

Informal authors:
- Desmond Weisenberg

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/429#post-3910
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem429.lean
- https://math.colgate.edu/~integers/y89/y89.pdf
-/
/-
We prove that for every function $f$ on the positive integers that goes to infinity, there exists an infinite set $B$ of positive integers omitting a residue class modulo every prime, whose counting function increases more slowly than $f$ does, and which has the property that for every integer $n$, the set $B+n$ contains a composite number. This formalization (which was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun)) follows the second proof in

D. Weisenberg, Sparse Admissible Sets and a Problem of Erdős and Graham. Integers (2024)

which can also be found here: https://math.colgate.edu/~integers/y89/y89.pdf.

This provides one solution to Erdős Problem #429 (https://www.erdosproblems.com/429), of which Weisenberg gives three more in the aforementioned paper.

-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 50000000
-- Several generated Diophantine-approximation estimates time out at the default heartbeat limit.
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Erdos429

/-
A set B is admissible if for every prime p there exists a residue class modulo p that is not represented by any element of B.
-/
def Admissible (B : Set ℕ) : Prop :=
  ∀ p, p.Prime → ∃ (a : ZMod p), ∀ b ∈ B, (b : ZMod p) ≠ a

/-
We can extend a finite set $B_0$ by an element $x$ that satisfies specified residue classes modulo a finite set of primes, while maintaining the density condition (provided $x$ is large enough).
-/
lemma sparse_extension_fixing (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (B₀ : Finset ℕ) (hB₀ : ∀ N, (B₀ ∩ Finset.Icc 1 N).card ≤ f N)
    (M : ℕ) (constraints : Finset ℕ) (h_primes : ∀ q ∈ constraints, Nat.Prime q)
    (target : ∀ q ∈ constraints, ZMod q) :
    ∃ x > M, (∀ q (hq : q ∈ constraints), (x : ZMod q) = target q hq) ∧
      ∀ N, ((B₀ ∪ {x}) ∩ Finset.Icc 1 N).card ≤ f N := by
  -- Let $c_q$ be the residue of $target(q)$ modulo $q$.
  set c : ℕ → ℕ := fun q => if hq : q ∈ constraints then (target q hq).val else 0
  -- By the Chinese Remainder Theorem, there exists an integer $x_0$ such that $x_0 \equiv c_q \pmod{q}$ for all $q \in \text{constraints}$.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, ∀ q (hq : q ∈ constraints), (x₀ : ZMod q) = c q := by
    -- By the Chinese Remainder Theorem, there exists an integer $x_0$ such that $x_0 \equiv c_q \pmod{q}$ for all $q \in \text{constraints}$ because the moduli $q$ are pairwise coprime.
    have h_crt : ∀ q ∈ constraints, ∃ x₀ : ℕ, x₀ ≡ c q [MOD q] ∧ ∀ r ∈ constraints, r ≠ q → x₀ ≡ 0 [MOD r] := by
      -- For each $q \in \text{constraints}$, let $y_q$ be the multiplicative inverse of $\prod_{r \in \text{constraints}, r \neq q} r$ modulo $q$.
      intros q hq
      obtain ⟨y_q, hy_q⟩ : ∃ y_q : ℕ, y_q * (∏ r ∈ constraints \ {q}, r) ≡ 1 [MOD q] := by
        have h_coprime : Nat.gcd (∏ r ∈ constraints \ {q}, r) q = 1 := by
          exact Nat.Coprime.prod_left fun r hr => Nat.coprime_comm.mp <| h_primes q hq |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h => by have := Nat.prime_dvd_prime_iff_eq ( h_primes q hq ) ( h_primes r <| Finset.mem_sdiff.mp hr |>.1 ) ; aesop
        obtain ⟨m, _hm_lt, hm⟩ :=
          Nat.exists_mul_mod_eq_one_of_coprime h_coprime
            (Nat.Prime.one_lt (h_primes q hq))
        exact ⟨m, by
          simpa [Nat.ModEq, Nat.mul_comm,
            Nat.mod_eq_of_lt (Nat.Prime.one_lt (h_primes q hq))] using hm⟩
      use y_q * (∏ r ∈ constraints \ {q}, r) * c q
      exact ⟨ by simpa using hy_q.mul_right _, fun r hr hrq => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩
    choose! x₀ hx₀₁ hx₀₂ using h_crt
    use ∑ q ∈ constraints, x₀ q; intro q hq; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
    rw [ Finset.sum_eq_single q ] <;> aesop
  -- Let $P = \prod_{q \in \text{constraints}} q$.
  set P := Finset.prod constraints (fun q => q) with hP_defP_def
  -- Let $x_k = x_0 + kP$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x₀ + k * P > M ∧ (∀ N, ((B₀ ∪ {x₀ + k * P}) ∩ Finset.Icc 1 N).card ≤ f N) := by
    -- Since $f(N) \to \infty$, there exists $N_0$ such that $f(N) \ge \lvert B_0 \rvert + 1$ for all $N \ge N_0$.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ N ≥ N₀, f N ≥ B₀.card + 1 := by
      exact Filter.eventually_atTop.mp ( hf.eventually_ge_atTop _ )
    -- Choose $k$ large enough such that $x = x₀ + kP > \max(M, N₀)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, x₀ + k * P > max M N₀ := by
      exact ⟨ Max.max M N₀ + 1, by nlinarith [ Nat.zero_le x₀, Nat.zero_le P, show P > 0 from Finset.prod_pos fun q hq => Nat.Prime.pos ( h_primes q hq ), le_max_left M N₀, le_max_right M N₀ ] ⟩
    refine' ⟨ k, lt_of_le_of_lt ( le_max_left _ _ ) hk, fun N => _ ⟩ ; by_cases hN : N < x₀ + k * P <;> simp_all +decide [ Finset.inter_comm ]
    refine' le_trans _ ( hN₀ N ( by linarith ) )
    exact le_trans ( Finset.card_le_card ( show Finset.Icc 1 N ∩ Insert.insert ( x₀ + k * ∏ q ∈ constraints, q ) B₀ ⊆ Insert.insert ( x₀ + k * ∏ q ∈ constraints, q ) B₀ from Finset.inter_subset_right ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by norm_num
  refine' ⟨ x₀ + k * P, hk.1, _, hk.2 ⟩
  intro q hq; specialize hx₀ q hq; simp_all +decide [Finset.prod_eq_prod_diff_singleton_mul hq]
  simp +zetaDelta at *
  simp +decide [hq]
  haveI := Fact.mk ( h_primes q hq ) ; simp +decide

/-
If a finite set $B$ has fewer elements than the modulus $q$, then $B$ does not cover all residue classes modulo $q$.
-/
lemma exists_omitted_residue (B : Finset ℕ) (q : ℕ) (hq : q > B.card) :
    ∃ r : ZMod q, ∀ b ∈ B, (b : ZMod q) ≠ r := by
      by_contra! h
      have h_card : Finset.card (Finset.image (fun b : ℕ => (b : ZMod q)) B) ≤ B.card := by
        exact Finset.card_image_le
      rcases q with ( _ | _ | q ) <;> simp_all +decide
      exact absurd ( Finset.card_le_card ( show Finset.univ ⊆ Finset.image ( fun b : ℕ => ( b : ZMod ( q + 1 + 1 ) ) ) B from fun x _ => by obtain ⟨ b, hb₁, hb₂ ⟩ := h x; aesop ) ) ( by simp +decide [ Finset.card_univ ] ; linarith )

/-
The function `zigzag` maps natural numbers to integers surjectively.
-/
def zigzag (n : ℕ) : ℤ := if n % 2 = 0 then (n / 2 : ℤ) else -((n + 1) / 2 : ℤ)

lemma zigzag_surjective : Function.Surjective zigzag := by
  intro z
  by_cases hz : z ≥ 0
  · exact ⟨ Int.toNat ( 2 * z ), by unfold zigzag; split_ifs <;> omega ⟩
  · -- If $z < 0$, let $n = 2(-z) - 1$. Then $n$ is odd, so $zigzag(n) = -(n+1)/2 = z$.
    use 2 * Int.natAbs z - 1
    unfold zigzag; split_ifs <;> omega

/-
The function `min_unconstrained_prime` returns the smallest prime not present in the constraints.
-/
noncomputable def min_unconstrained_prime (constraints : Finset (ℕ × ℕ)) : ℕ :=
  Nat.nth (fun p => Nat.Prime p ∧ ∀ x ∈ constraints, x.1 ≠ p) 0

lemma min_unconstrained_prime_spec (constraints : Finset (ℕ × ℕ)) :
    Nat.Prime (min_unconstrained_prime constraints) ∧
    (∀ x ∈ constraints, x.1 ≠ (min_unconstrained_prime constraints)) ∧
    (∀ q, Nat.Prime q → (∀ x ∈ constraints, x.1 ≠ q) → min_unconstrained_prime constraints ≤ q) := by
      unfold min_unconstrained_prime
      rw [ Nat.nth_zero ]
      -- The set of primes not in the constraints is infinite, so it has a smallest element.
      have h_inf : Set.Infinite {p : ℕ | Nat.Prime p ∧ ∀ x ∈ constraints, x.1 ≠ p} := by
        exact Set.Infinite.diff ( Nat.infinite_setOf_prime ) ( constraints.image Prod.fst |> Finset.finite_toSet ) |> Set.Infinite.mono fun p hp => by aesop
      exact ⟨ Nat.sInf_mem h_inf.nonempty |>.1, fun x hx => Nat.sInf_mem h_inf.nonempty |>.2 x hx, fun q hq hq' => Nat.sInf_le ⟨ hq, hq' ⟩ ⟩

/-
We can find a prime $q$ that is large enough and avoids a set of constraints.
-/
structure ConstructionStateV2 where
  B : Finset ℕ
  constraints : Finset (ℕ × ℕ)
  h_odd : ∀ b ∈ B, b % 2 = 1
  h_respects : ∀ x ∈ constraints, ∀ b ∈ B, b % x.1 ≠ x.2
  h_prime : ∀ x ∈ constraints, Nat.Prime x.1
  h_coprime : ∀ x ∈ constraints, ∀ y ∈ constraints, x ≠ y → x.1 ≠ y.1

lemma exists_suitable_prime_for_blocking (B : Finset ℕ) (constraints : Finset (ℕ × ℕ)) (n : ℤ) :
    ∃ q, Nat.Prime q ∧ q > B.card + 1 ∧ (∀ b ∈ B, b < q) ∧ (∀ x ∈ constraints, x.1 ≠ q) ∧ q > 2 ∧ q > n.natAbs := by
      have h_inf_primes : Set.Infinite {q : ℕ | Nat.Prime q ∧ q > B.card + 1 ∧ (∀ b ∈ B, b < q) ∧ (∀ x ∈ constraints, x.1 ≠ q) ∧ q > 2 ∧ q > Int.natAbs n} := by
        have h_inf_primes : Set.Infinite {q : ℕ | Nat.Prime q ∧ q > B.card + 1 ∧ (∀ b ∈ B, b < q) ∧ (∀ x ∈ constraints, x.1 ≠ q)} := by
          have h_inf_primes : Set.Infinite {q : ℕ | Nat.Prime q ∧ q > B.card + 1 ∧ (∀ x ∈ constraints, x.1 ≠ q)} := by
            exact Set.Infinite.mono ( by aesop_cat ) ( Nat.infinite_setOf_prime.diff ( Set.toFinite ( Finset.image Prod.fst constraints ∪ { 2 } ∪ Finset.range ( B.card + 2 ) ) ) )
          exact h_inf_primes.diff ( Finset.finite_toSet ( B.biUnion fun b => Finset.Iic b ) ) |> Set.Infinite.mono fun q hq => by aesop
        exact Set.Infinite.mono ( by aesop_cat ) ( h_inf_primes.diff ( Set.finite_le_nat ( Max.max 2 n.natAbs ) ) )
      exact h_inf_primes.nonempty

/-
We can find a large odd integer $x$ that satisfies a set of avoidance constraints, a specific congruence modulo $q$, and the density condition.
-/
lemma sparse_extension_mixed_odd (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (B₀ : Finset ℕ) (hB₀ : ∀ N, (B₀ ∩ Finset.Icc 1 N).card ≤ f N)
    (M : ℕ)
    (constraints : Finset (ℕ × ℕ))
    (h_prime : ∀ x ∈ constraints, Nat.Prime x.1)
    (h_coprime : ∀ x ∈ constraints, ∀ y ∈ constraints, x ≠ y → x.1 ≠ y.1)
    (h_respects_2 : ∀ x ∈ constraints, x.1 = 2 → x.2 = 0)
    (q : ℕ) (hq : Nat.Prime q) (hq_not_in : ∀ x ∈ constraints, x.1 ≠ q) (hq_gt_2 : q > 2)
    (target_n : ℤ) :
    ∃ x > M,
      (∀ c ∈ constraints, x % c.1 ≠ c.2) ∧
      (x + target_n) % q = 0 ∧
      x % 2 = 1 ∧
      ∀ N, ((B₀ ∪ {x}) ∩ Finset.Icc 1 N).card ≤ f N := by
        revert hq_not_in hq_gt_2
        intro hq_not_in hq_gt_2
        obtain ⟨x, hx⟩ : ∃ x > M, (x + target_n) % q = 0 ∧ x % 2 = 1 ∧ (∀ c ∈ constraints, x % c.1 ≠ c.2) ∧ ∀ N, ((B₀ ∪ {x}) ∩ Finset.Icc 1 N).card ≤ f N := by
          -- Apply the sparse_extension_fixing lemma with the set S and the target function T.
          obtain ⟨x, hx⟩ : ∃ x > M, (∀ p ∈ constraints.image Prod.fst ∪ {q, 2}, (x : ZMod p) = (if p = q then -target_n else if p = 2 then 1 else (if (p, (if p = 2 then 0 else 0)) ∈ constraints then (if (p, (if p = 2 then 0 else 0)).1 = 2 then 1 else 1) else 0))) ∧ ∀ N, ((B₀ ∪ {x}) ∩ Finset.Icc 1 N).card ≤ f N := by
            convert sparse_extension_fixing f hf B₀ hB₀ M ( constraints.image Prod.fst ∪ { q, 2 } ) _ _ using 4 ; simp +decide [ * ]
            exact fun a x hx => h_prime _ hx
          refine' ⟨ x, hx.1, _, _, _, hx.2.2 ⟩ <;> simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ]
          · rw [ ← ZMod.val_natCast ] ; aesop
          · intro a b hab; specialize hx; have := hx.2.1.2.2 a b hab; split_ifs at this <;> simp_all +decide [ ← ZMod.val_natCast ]
            · exact False.elim <| hq_not_in _ _ hab rfl
            · specialize h_respects_2 2 b hab rfl ; aesop
            · haveI := Fact.mk ( h_prime _ _ ‹_› ) ; simp_all +decide
              specialize h_coprime _ _ ‹_› _ _ hab ; aesop
            · grind +ring
        exact ⟨ x, hx.1, hx.2.2.2.1, hx.2.1, hx.2.2.1, hx.2.2.2.2 ⟩

/-
Given a set of odd numbers $B$ and a prime $p$ larger than $|B|$, there exists a residue $r$ modulo $p$ not in $B$ such that if $p=2$, $r=0$.
-/
lemma exists_admissible_residue_respecting_2 (B : Finset ℕ) (h_odd : ∀ b ∈ B, b % 2 = 1)
    (p : ℕ) (hp : Nat.Prime p) (h_card : B.card < p) :
    ∃ r : ZMod p, (∀ b ∈ B, (b : ZMod p) ≠ r) ∧ (p = 2 → r = 0) := by
      cases eq_or_ne p 2 <;> simp_all +decide
      · intro b hb; specialize h_odd b hb; erw [ ZMod.natCast_eq_zero_iff ]
        exact fun h => by have := Nat.mod_eq_zero_of_dvd h; aesop
      · haveI := Fact.mk hp
        exact exists_omitted_residue B p h_card

/-
We can add a constraint for a new prime `target_p` to the construction state, ensuring admissibility, provided `target_p` is large enough.
-/
lemma add_admissibility_constraint (state : ConstructionStateV2)
    (target_p : ℕ) (h_target_p : Nat.Prime target_p) (h_target_p_not_in : ∀ x ∈ state.constraints, x.1 ≠ target_p)
    (h_card : state.B.card < target_p)
    (h_consistent_2 : ∀ x ∈ state.constraints, x.1 = 2 → x.2 = 0) :
    ∃ state' : ConstructionStateV2,
      state.B = state'.B ∧
      state.constraints ⊆ state'.constraints ∧
      (∃ r, (target_p, r) ∈ state'.constraints) ∧
      (∀ x ∈ state'.constraints, x.1 = 2 → x.2 = 0) := by
        -- Let `r` be the residue modulo `target_p` that is not in `B` and satisfies `target_p = 2 → r = 0`.
        obtain ⟨r, hr⟩ : ∃ r : ℕ, r < target_p ∧ (∀ b ∈ state.B, b % target_p ≠ r) ∧ (target_p = 2 → r = 0) := by
          have := exists_admissible_residue_respecting_2 state.B state.h_odd target_p h_target_p h_card
          obtain ⟨ r, hr₁, hr₂ ⟩ := this; use r.val; haveI := Fact.mk h_target_p; simp_all +decide
          haveI := Fact.mk h_target_p; exact ⟨ ZMod.val_lt r, fun b hb => fun h => hr₁ b hb <| by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod target_p ) h ⟩
        refine' ⟨ ⟨ state.B, state.constraints ∪ { ( target_p, r ) }, _, _, _, _ ⟩, rfl, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ]
        · exact fun b hb => state.h_odd b hb
        · exact fun a b hab x hx => mod_cast state.h_respects _ hab _ hx
        · exact fun a b hab => state.h_prime _ hab
        · exact ⟨ fun a b ha hb => by tauto, fun a b ha => ⟨ fun hb => by tauto, fun c d hc hd => by have := state.h_coprime ( a, b ) ha ( c, d ) hc; aesop ⟩ ⟩

/-
We can find an odd number $b$ and a prime $p$ such that $b$ extends $B$ with density, respects constraints, and $b+n$ is divisible by $p$ (and large enough to be composite).
-/
lemma find_blocking_element (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (B : Finset ℕ) (h_dens : ∀ N, (B ∩ Finset.Icc 1 N).card ≤ f N)
    (constraints : Finset (ℕ × ℕ))
    (h_prime : ∀ x ∈ constraints, Nat.Prime x.1)
    (h_coprime : ∀ x ∈ constraints, ∀ y ∈ constraints, x ≠ y → x.1 ≠ y.1)
    (h_consistent_2 : ∀ x ∈ constraints, x.1 = 2 → x.2 = 0)
    (target_n : ℤ) :
    ∃ b p, Nat.Prime p ∧ p > 2 ∧
      b > B.sup id ∧
      (∀ c ∈ constraints, b % c.1 ≠ c.2) ∧
      (b + target_n) % p = 0 ∧
      b + target_n > p ∧
      b % 2 = 1 ∧
      (∀ N, ((B ∪ {b}) ∩ Finset.Icc 1 N).card ≤ f N) := by
        -- Use `exists_suitable_prime_for_blocking` to find a prime `p` such that `p > |B| + 1` and `p > max B`.
        obtain ⟨p, hp_prime, hp_gt_card, hp_gt_max, hp_not_in, hp_gt_2, hp_abs⟩ : ∃ p, Nat.Prime p ∧ p > B.card + 1 ∧ (∀ b ∈ B, b < p) ∧ (∀ x ∈ constraints, x.1 ≠ p) ∧ p > 2 ∧ p > target_n.natAbs := by
          exact exists_suitable_prime_for_blocking B constraints target_n
        -- Use `sparse_extension_mixed_odd` with $B, M, constraints, p, target_n$.
        obtain ⟨b, hb_gt_M, hb_respects, hb_div, hb_odd, hb_density⟩ : ∃ b, b > p + target_n.natAbs ∧ (∀ c ∈ constraints, b % c.1 ≠ c.2) ∧ (b + target_n) % p = 0 ∧ b % 2 = 1 ∧ ∀ N, ((B ∪ {b}) ∩ Finset.Icc 1 N).card ≤ f N := by
          convert sparse_extension_mixed_odd f hf B h_dens ( p + target_n.natAbs ) constraints h_prime h_coprime h_consistent_2 p hp_prime hp_not_in hp_gt_2 target_n using 1
        refine ⟨ b, p, hp_prime, hp_gt_2, ?_, hb_respects, hb_div, ?_, hb_odd, hb_density ⟩
        · exact lt_of_le_of_lt ( Finset.sup_le fun x hx => Nat.le_of_lt ( hp_gt_max x hx ) ) ( by linarith [ abs_nonneg target_n ] )
        · grind

/-
Definition of the construction sequence with invariants.
-/
structure GoodState (f : ℕ → ℕ) where
  state : ConstructionStateV2
  h_dens : ∀ N, (state.B ∩ Finset.Icc 1 N).card ≤ f N
  h_consistent_2 : ∀ x ∈ state.constraints, x.1 = 2 → x.2 = 0

/-
Helper lemma for the strict step.
-/

lemma state_with_b_h_respects (f : ℕ → ℕ) (gs : GoodState f) (b : ℕ)
  (h_respects_b : ∀ c ∈ gs.state.constraints, b % c.1 ≠ c.2) :
  ∀ x ∈ gs.state.constraints, ∀ y ∈ gs.state.B ∪ {b}, y % x.1 ≠ x.2 := by
  intro x hx y hy
  rw [Finset.mem_union, Finset.mem_singleton] at hy
  cases hy with
  | inl h => exact gs.state.h_respects x hx y h
  | inr h => subst h; exact h_respects_b x hx

lemma state_with_b_h_odd (f : ℕ → ℕ) (gs : GoodState f) (b : ℕ)
  (h_odd_b : b % 2 = 1) :
  ∀ x ∈ gs.state.B ∪ {b}, x % 2 = 1 := by
  intro x hx
  rw [Finset.mem_union, Finset.mem_singleton] at hx
  cases hx with
  | inl h => exact gs.state.h_odd x h
  | inr h => subst h; exact h_odd_b

/-
Helper lemma: element greater than sup is not in set.
-/
lemma not_mem_of_gt_sup (B : Finset ℕ) (b : ℕ) (h : b > B.sup id) : b ∉ B := by
  exact fun hb => h.not_ge <| Finset.le_sup ( f := id ) hb

/-
Step function for the strict construction.
-/
noncomputable def step_strict (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f) : GoodState f := by
  let p := min_unconstrained_prime gs.state.constraints
  by_cases h_card : gs.state.B.card + 1 < p
  · -- Case: we can add an element and a constraint
    -- 1. Find blocking element b
    let block_spec := find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints
      gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n
    let b := Classical.choose block_spec
    let h_b_spec := Classical.choose_spec block_spec
    let q := Classical.choose h_b_spec
    let h_block := Classical.choose_spec h_b_spec
    -- Construct state_with_b
    let state_with_b : ConstructionStateV2 := {
      B := gs.state.B ∪ {b}
      constraints := gs.state.constraints
      h_odd := by
        intro x hx
        rw [Finset.mem_union, Finset.mem_singleton] at hx
        cases hx with
        | inl h => exact gs.state.h_odd x h
        | inr h => subst h; exact h_block.2.2.2.2.2.2.1
      h_respects := by
        intro x hx y hy
        rw [Finset.mem_union, Finset.mem_singleton] at hy
        cases hy with
        | inl h => exact gs.state.h_respects x hx y h
        | inr h => subst h; exact h_block.2.2.2.1 x hx
      h_prime := gs.state.h_prime
      h_coprime := gs.state.h_coprime
    }
    -- 2. Add admissibility constraint for p
    have h_card_new : state_with_b.B.card < p := by
      have h_not_mem : b ∉ gs.state.B := not_mem_of_gt_sup gs.state.B b h_block.2.2.1
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr h_not_mem)]
      simp
      exact h_card
    let adm_spec := add_admissibility_constraint state_with_b p
      (min_unconstrained_prime_spec gs.state.constraints).1
      (min_unconstrained_prime_spec gs.state.constraints).2.1
      h_card_new
      gs.h_consistent_2
    let state_final := Classical.choose adm_spec
    let h_final := Classical.choose_spec adm_spec
    exact {
      state := state_final
      h_dens := by
        rw [← h_final.1]
        exact h_block.2.2.2.2.2.2.2
      h_consistent_2 := h_final.2.2.2
    }
  · -- Case: cannot add
    exact gs

/-
The set of the first k primes.
-/
noncomputable def first_k_primes (k : ℕ) : Finset ℕ :=
  Finset.image (Nat.nth Nat.Prime) (Finset.range k)

/-
Helper lemma for min unconstrained prime.
-/
lemma min_unconstrained_eq_nth (constraints : Finset (ℕ × ℕ)) (k : ℕ)
    (h : constraints.image Prod.fst = first_k_primes k) :
    min_unconstrained_prime constraints = Nat.nth Nat.Prime k := by
      unfold min_unconstrained_prime
      generalize_proofs at *
      rw [ Nat.nth_eq_sInf ]
      refine' le_antisymm ( Nat.sInf_le _ ) ( le_csInf _ _ )
      · simp +zetaDelta at *
        intro a b hab H; replace h := Finset.ext_iff.mp h a; simp_all +decide [ first_k_primes ]
        exact absurd ( h.mp ⟨ b, hab ⟩ ) ( by rintro ⟨ a, ha, ha' ⟩ ; exact absurd ha' ( ne_of_lt ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ha ) ) )
      · -- Since there are infinitely many primes, we can choose a prime $p$ such that $p > \max(\text{constraints.image Prod.fst})$.
        obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p > Finset.sup constraints (Prod.fst) := by
          exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( Finset.sup constraints Prod.fst + 1 ) )
        exact ⟨ p, ⟨ ⟨ hp.1, fun x hx => ne_of_lt <| lt_of_le_of_lt ( Finset.le_sup ( f := Prod.fst ) hx ) hp.2 ⟩, by norm_num ⟩ ⟩
      · intro b hb; have := hb.1.2; simp_all +decide [ Finset.ext_iff ]
        refine' Nat.le_of_not_lt fun h => _
        -- Since $b < \text{Nat.nth Nat.Prime } k$, $b$ must be one of the first $k$ primes.
        have hb_first_k : b ∈ Finset.image (Nat.nth Nat.Prime) (Finset.range k) := by
          have hb_first_k : ∃ i < k, b = Nat.nth Nat.Prime i := by
            refine' ⟨ Nat.count ( Nat.Prime ) b, _, _ ⟩
            · contrapose! h
              rw [ Nat.nth_eq_sInf ]
              refine' Nat.sInf_le ⟨ hb.1, _ ⟩
              intro i hi; exact Nat.nth_lt_of_lt_count <| by linarith
            · rw [ Nat.nth_count ] ; aesop
          aesop
        obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hb_first_k; specialize ‹∀ a : ℕ, ( ∃ x, ( a, x ) ∈ constraints ) ↔ a ∈ first_k_primes k› ( Nat.nth Nat.Prime x ) ; simp_all +decide [ first_k_primes ]
        exact this _ _ h.choose_spec rfl

/-
The set of constrained primes.
-/
def primes_in_constraints (state : ConstructionStateV2) : Finset ℕ :=
  state.constraints.image Prod.fst

/-
The n-th prime is at least n+2.
-/
lemma nth_prime_ge_add_two (n : ℕ) : Nat.nth Nat.Prime n ≥ n + 2 := by
  exact Nat.recOn n ( Nat.Prime.two_le <| Nat.prime_nth_prime 0 ) fun n ihn => Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt ihn <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| Nat.lt_succ_self n

/-
Recursive definition of first_k_primes.
-/
lemma first_k_primes_succ (k : ℕ) :
    first_k_primes (k + 1) = first_k_primes k ∪ {Nat.nth Nat.Prime k} := by
      unfold first_k_primes
      rw [Finset.range_add_one, Finset.image_insert]
      exact (Finset.union_singleton (Nat.nth Nat.Prime k)
        (Finset.image (Nat.nth Nat.Prime) (Finset.range k))).symm

/-
Cardinality increase in step_strict.
-/
lemma step_strict_card_eq (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f)
    (h_cond : gs.state.B.card + 1 < min_unconstrained_prime gs.state.constraints) :
    (step_strict f hf n gs).state.B.card = gs.state.B.card + 1 := by
      -- By definition of `step_strict`, we know that `step_strict f hf n gs` adds a new element `b` to `B`.
      obtain ⟨b, hb⟩ : ∃ b, b ∉ gs.state.B ∧ (step_strict f hf n gs).state.B = gs.state.B ∪ {b} := by
        unfold step_strict
        by_cases h : gs.state.B.card + 1 < min_unconstrained_prime gs.state.constraints <;> simp_all +decide
        have := Classical.choose_spec ( find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n )
        obtain ⟨ p, hp₁, hp₂, hp₃, hp₄, hp₅, hp₆, hp₇, hp₈ ⟩ := this
        have := Classical.choose_spec ( add_admissibility_constraint ( { B := gs.state.B ∪ { Classical.choose ( find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n ) }, constraints := gs.state.constraints, h_odd := by
                                                                          simp +zetaDelta at *
                                                                          exact ⟨ hp₇, fun a ha => gs.state.h_odd a ha ⟩, h_respects := by
                                                                          exact fun x a b a_1 =>
                                                                            state_with_b_h_respects
                                                                              f gs
                                                                              (Classical.choose
                                                                                (find_blocking_element
                                                                                  f hf gs.state.B
                                                                                  gs.h_dens
                                                                                  gs.state.constraints
                                                                                  gs.state.h_prime
                                                                                  gs.state.h_coprime
                                                                                  gs.h_consistent_2
                                                                                  n))
                                                                              hp₄ x a b a_1, h_prime := by
                                                                          exact gs.state.h_prime, h_coprime := by
                                                                          exact gs.state.h_coprime } : ConstructionStateV2 ) ( min_unconstrained_prime gs.state.constraints ) ( min_unconstrained_prime_spec gs.state.constraints |>.1 ) ( min_unconstrained_prime_spec gs.state.constraints |>.2.1 ) ( by
                                                                          grind ) ( by
                                                                          exact gs.h_consistent_2 ) )
        use Classical.choose ( find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n )
        generalize_proofs at *
        exact ⟨ fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) hp₃, by simpa [ Finset.union_comm ] using this.1.symm ⟩
      rw [ hb.2, Finset.card_union ] ; aesop

/-
Defining the minimal step state.
-/
noncomputable def step_strict_minimal_state (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f) : ConstructionStateV2 := by
  let p := min_unconstrained_prime gs.state.constraints
  by_cases h_card : gs.state.B.card + 1 < p
  · let block_spec := find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints
      gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n
    let b := Classical.choose block_spec
    let h_block := Classical.choose_spec (Classical.choose_spec block_spec)
    let B_new := gs.state.B ∪ {b}
    have h_odd_new : ∀ x ∈ B_new, x % 2 = 1 := by
      apply state_with_b_h_odd f gs b h_block.2.2.2.2.2.2.1
    have h_card_new : B_new.card < p := by
      have h_not_mem : b ∉ gs.state.B := not_mem_of_gt_sup gs.state.B b h_block.2.2.1
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr h_not_mem)]
      simp
      exact h_card
    have h_p_prime : Nat.Prime p := (min_unconstrained_prime_spec gs.state.constraints).1
    let r_spec := exists_admissible_residue_respecting_2 B_new h_odd_new p h_p_prime h_card_new
    let r := Classical.choose r_spec
    exact {
      B := B_new
      constraints := gs.state.constraints ∪ {(p, r.val)}
      h_odd := h_odd_new
      h_respects := by
        intro x hx b hb; simp_all +decide
        rcases hx with ( rfl | hx )
        · have := Classical.choose_spec r_spec |>.1 b hb
          contrapose! this
          convert congr_arg ( fun x : ℕ => x : ℕ → ZMod p ) this using 1
          · simp +decide
          · haveI := Fact.mk h_p_prime; simp +decide
            rfl
        · by_cases hb : b ∈ gs.state.B
          · exact gs.state.h_respects x hx b hb
          · convert Classical.choose_spec ( Classical.choose_spec block_spec ) |>.2.2.2.1 x hx using 1
            grind
      h_prime := by
        -- By definition of union, any element in the union is either in the original constraints or in the new element (p, r.val).
        intro x hx
        cases Finset.mem_union.mp hx <;> simp_all +decide [ Nat.prime_iff ]
        · exact Nat.prime_iff.mp ( gs.state.h_prime x ‹_› )
        · -- Since $p$ is a prime number, we can conclude that $p$ is prime.
          exact h_p_prime.prime
      h_coprime := by
        -- Let's split into cases based on whether x and y are in the original constraints or the new one.
        intro x hx y hy hxy
        rcases Finset.mem_union.mp hx with hx | hx' <;>
          rcases Finset.mem_union.mp hy with hy | hy' <;>
          simp_all +decide [Finset.mem_singleton]
        · exact gs.state.h_coprime x hx y hy hxy
        · exact fun h => by have := min_unconstrained_prime_spec gs.state.constraints; aesop
        · -- Since $p$ is the minimal unconstrained prime, it cannot be in the constraints.
          have h_p_not_in_constraints : ∀ y ∈ gs.state.constraints, y.1 ≠ p := by
            exact min_unconstrained_prime_spec gs.state.constraints |>.2.1
          exact Ne.symm ( h_p_not_in_constraints y hy )
    }
  · exact gs.state

/-
If the first k+1 primes are constrained and B has size k, then the next unconstrained prime is large enough to allow a step.
-/
lemma step_condition_relaxed (f : ℕ → ℕ) (gs : GoodState f) (k : ℕ)
    (h_card : gs.state.B.card = k)
    (h_primes : first_k_primes (k + 1) ⊆ primes_in_constraints gs.state) :
    gs.state.B.card + 1 < min_unconstrained_prime gs.state.constraints := by
      have h_p_ge_k3 : min_unconstrained_prime gs.state.constraints ≥ Nat.nth Nat.Prime (k + 1) := by
        apply Classical.byContradiction
        intro h_contra
        have h_p_index : ∃ i < k + 1, min_unconstrained_prime gs.state.constraints = Nat.nth Nat.Prime i := by
          have h_p_index : ∃ i, min_unconstrained_prime gs.state.constraints = Nat.nth Nat.Prime i := by
            exact ⟨ Nat.count ( Nat.Prime ) ( min_unconstrained_prime gs.state.constraints ), by rw [ Nat.nth_count ( min_unconstrained_prime_spec gs.state.constraints |>.1 ) ] ⟩
          obtain ⟨ i, hi ⟩ := h_p_index; exact ⟨ i, Nat.lt_of_not_ge fun hi' => h_contra <| hi.symm ▸ Nat.nth_monotone ( Nat.infinite_setOf_prime ) hi', hi ⟩
        obtain ⟨ i, hi, hi' ⟩ := h_p_index
        have := h_primes ( Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr hi, rfl ⟩ ) ; simp_all +decide [ primes_in_constraints ]
        exact absurd ( min_unconstrained_prime_spec gs.state.constraints |>.2.1 _ this.choose_spec ) ( by aesop )
      linarith [ nth_prime_ge_add_two ( k + 1 ) ]

/-
We define a new construction sequence using `step_strict_minimal_state` which guarantees valid residue classes, and prove it preserves invariants.
-/
lemma step_strict_minimal_valid (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f) :
    let s' := step_strict_minimal_state f hf n gs
    (∀ N, (s'.B ∩ Finset.Icc 1 N).card ≤ f N) ∧
    (∀ x ∈ s'.constraints, x.1 = 2 → x.2 = 0) := by
      unfold step_strict_minimal_state
      field_simp
      split_ifs <;> norm_num +zetaDelta at *
      · refine' ⟨ _, _, _ ⟩
        · convert Classical.choose_spec ( Classical.choose_spec ( find_blocking_element f hf gs.state.B gs.h_dens gs.state.constraints gs.state.h_prime gs.state.h_coprime gs.h_consistent_2 n ) ) |>.2.2.2.2.2.2.2 using 1
          congr! 2
          ext; simp [Finset.mem_inter]
        · intro h_min_unconstrained_prime_eq_two
          have h_contradiction : gs.state.B.card + 1 < 2 := by
            linarith
          generalize_proofs at *
          have := Classical.choose_spec ‹_›; aesop
        · exact fun a b hab ha => gs.h_consistent_2 _ hab ha
      · exact ⟨ gs.h_dens, fun a b hab ha => gs.h_consistent_2 _ hab ha ⟩

/-
The `step_strict_minimal_state` function preserves the density and consistency invariants.
-/
lemma step_strict_minimal_valid_v2 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f) :
    let s' := step_strict_minimal_state f hf n gs
    (∀ N, (s'.B ∩ Finset.Icc 1 N).card ≤ f N) ∧
    (∀ x ∈ s'.constraints, x.1 = 2 → x.2 = 0) := by
      convert step_strict_minimal_valid f hf n gs using 1

/-
We define the final construction sequence and the resulting set B (version 4).
-/
noncomputable def step_strict_v4 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f) : GoodState f :=
  {
    state := step_strict_minimal_state f hf n gs
    h_dens := (step_strict_minimal_valid_v2 f hf n gs).1
    h_consistent_2 := (step_strict_minimal_valid_v2 f hf n gs).2
  }

noncomputable def seq_strict_v4 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : ℕ → GoodState f
| 0 => {
    state := {
      B := ∅
      constraints := {(2, 0)}
      h_odd := by simp
      h_respects := by simp
      h_prime := by simp; decide
      h_coprime := by simp
    }
    h_dens := by simp
    h_consistent_2 := by simp
  }
| k + 1 => step_strict_v4 f hf (zigzag k) (seq_strict_v4 f hf k)

noncomputable def B_final_v4 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set ℕ :=
  ⋃ k, (seq_strict_v4 f hf k).state.B

/-
If the current state has cardinality k and constraints cover the first k+1 primes, then the strict step condition (card + 1 < min_unconstrained) is satisfied.
-/
lemma step_strict_v4_succeeds (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (k : ℕ)
    (gs : GoodState f)
    (h_card : gs.state.B.card = k)
    (h_primes : first_k_primes (k + 1) ⊆ primes_in_constraints gs.state) :
    gs.state.B.card + 1 < min_unconstrained_prime gs.state.constraints := by
      convert step_condition_relaxed f gs k h_card h_primes using 1

/-
The `step_strict_minimal_state` function increases cardinality by 1, adds a constraint, and the added constraint has a valid residue.
-/
lemma step_strict_minimal_state_properties (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℤ) (gs : GoodState f)
    (h_cond : gs.state.B.card + 1 < min_unconstrained_prime gs.state.constraints) :
    let s' := step_strict_minimal_state f hf n gs
    s'.B.card = gs.state.B.card + 1 ∧
    gs.state.constraints ⊆ s'.constraints ∧
    (∃ p r, s'.constraints = gs.state.constraints ∪ {(p, r)} ∧
            p = min_unconstrained_prime gs.state.constraints ∧
            r < p) := by
  dsimp
  unfold step_strict_minimal_state
  simp [h_cond]
  generalize_proofs at *
  rename_i block_spec residue_spec
  constructor
  · exact Finset.card_insert_of_notMem
      (not_mem_of_gt_sup gs.state.B (Classical.choose block_spec)
        (Classical.choose_spec (Classical.choose_spec block_spec)).2.2.1)
  · refine ⟨(Classical.choose residue_spec).val, rfl, ?_⟩
    haveI : NeZero (min_unconstrained_prime gs.state.constraints) :=
      ⟨Nat.Prime.ne_zero (min_unconstrained_prime_spec gs.state.constraints).1⟩
    exact ZMod.val_lt (Classical.choose residue_spec)

/-
The sequence `seq_strict_v4` satisfies the properties: cardinality is k, constraints are exactly the first k+1 primes, and all constraints have valid residues.
-/
lemma seq_strict_v4_properties (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (k : ℕ) :
    (seq_strict_v4 f hf k).state.B.card = k ∧
    primes_in_constraints (seq_strict_v4 f hf k).state = first_k_primes (k + 1) ∧
    (∀ x ∈ (seq_strict_v4 f hf k).state.constraints, x.2 < x.1) := by
      induction' k with k ih
      · -- For the base case when $k = 0$, the state is initialized with $B = \emptyset$ and constraints $\{(2, 0)\}$.
        simp [seq_strict_v4]
        unfold primes_in_constraints first_k_primes; aesop
      · -- By definition of `seq_strict_v4`, we have `seq_strict_v4 f hf (k + 1) = step_strict_v4 f hf (zigzag k) (seq_strict_v4 f hf k)`. Use this fact.
        have h_step : (seq_strict_v4 f hf (k + 1)).state.B.card = (seq_strict_v4 f hf k).state.B.card + 1 ∧
                       primes_in_constraints (seq_strict_v4 f hf (k + 1)).state = primes_in_constraints (seq_strict_v4 f hf k).state ∪ {min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints} ∧
                       ∀ x ∈ (seq_strict_v4 f hf (k + 1)).state.constraints, x.2 < x.1 := by
                         have h_step : (seq_strict_v4 f hf (k + 1)).state.B.card = (seq_strict_v4 f hf k).state.B.card + 1 ∧
                                            primes_in_constraints (seq_strict_v4 f hf (k + 1)).state = primes_in_constraints (seq_strict_v4 f hf k).state ∪ {min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints} ∧
                                            ∀ x ∈ (seq_strict_v4 f hf (k + 1)).state.constraints, x.2 < x.1 := by
                           have h_step_cond : (seq_strict_v4 f hf k).state.B.card + 1 < min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints := by
                             apply step_strict_v4_succeeds
                             exacts [ hf, ih.1, by simpa only [ ih.2.1 ] using Finset.Subset.refl _ ]
                           -- Apply the properties of `step_strict_minimal_state` with the condition `h_step_cond`.
                           have h_step_prop : (step_strict_minimal_state f hf (zigzag k) (seq_strict_v4 f hf k)).B.card = (seq_strict_v4 f hf k).state.B.card + 1 ∧
                                                primes_in_constraints (step_strict_minimal_state f hf (zigzag k) (seq_strict_v4 f hf k)) = primes_in_constraints (seq_strict_v4 f hf k).state ∪ {min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints} ∧
                                                ∀ x ∈ (step_strict_minimal_state f hf (zigzag k) (seq_strict_v4 f hf k)).constraints, x.2 < x.1 := by
                                                  apply step_strict_minimal_state_properties f hf (zigzag k) (seq_strict_v4 f hf k) h_step_cond |> fun h => ⟨h.left, by
                                                    unfold primes_in_constraints; aesop;, by
                                                    grind⟩
                           convert h_step_prop using 1
                         exact h_step
        -- By definition of `min_unconstrained_prime`, we know that `min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints = Nat.nth Nat.Prime (k + 1)`.
        have h_min_unconstrained : min_unconstrained_prime (seq_strict_v4 f hf k).state.constraints = Nat.nth Nat.Prime (k + 1) := by
          apply min_unconstrained_eq_nth
          exact ih.2.1
        simp_all +decide [ first_k_primes_succ ]
/-
Every prime number eventually appears in the set of constraints of the version 4 construction sequence.
-/
lemma eventually_constrained_v4 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (p : ℕ) (hp : p.Prime) :
    ∃ k, p ∈ primes_in_constraints (seq_strict_v4 f hf k).state := by
      -- By definition of `seq_strict_v4`, there exists some `k` such that `p` is the `k`-th prime.
      obtain ⟨k, hk⟩ : ∃ k, p = Nat.nth Nat.Prime k := by
        exact ⟨ Nat.count ( Nat.Prime ) p, Eq.symm ( Nat.nth_count hp ) ⟩
      use k
      have := seq_strict_v4_properties f hf k
      rw [this.2.1, hk]
      unfold first_k_primes
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩

/-
The sequence `seq_strict_v4` satisfies the properties: cardinality is k, constraints are exactly the first k+1 primes, and all constraints have valid residues.
-/
lemma seq_strict_v4_properties_final (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (k : ℕ) :
    (seq_strict_v4 f hf k).state.B.card = k ∧
    primes_in_constraints (seq_strict_v4 f hf k).state = first_k_primes (k + 1) ∧
    (∀ x ∈ (seq_strict_v4 f hf k).state.constraints, x.2 < x.1) := by
      convert seq_strict_v4_properties f hf k using 1

/-
The sequence `seq_strict_v4` is monotonic in both `B` and `constraints`.
-/
lemma seq_strict_v4_mono (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (k : ℕ) :
    (seq_strict_v4 f hf k).state.B ⊆ (seq_strict_v4 f hf (k + 1)).state.B ∧
    (seq_strict_v4 f hf k).state.constraints ⊆ (seq_strict_v4 f hf (k + 1)).state.constraints := by
      convert step_strict_minimal_state_properties f hf ( zigzag k ) ( seq_strict_v4 f hf k ) _ using 1
      · rw [ step_strict_minimal_state_properties f hf _ _ _ |>.1 ]
        · simp +decide
          -- By definition of `seq_strict_v4`, the state at step `k+1` is obtained by applying `step_strict_minimal_state` to the state at step `k`.
          have h_step : ∀ k, (seq_strict_v4 f hf (k + 1)).state = step_strict_minimal_state f hf (zigzag k) (seq_strict_v4 f hf k) := by
            exact fun k => rfl
          rw [h_step]
          intro x hx; unfold step_strict_minimal_state; aesop
        · convert step_strict_v4_succeeds f hf k ( seq_strict_v4 f hf k ) _ _
          · exact seq_strict_v4_properties_final f hf k |>.1
          · exact seq_strict_v4_properties_final f hf k |>.2.1.symm ▸ Finset.Subset.refl _
      · have := @step_strict_minimal_state_properties f hf ( zigzag k ) ( seq_strict_v4 f hf k ) ?_
        · bound
        · convert step_strict_v4_succeeds f hf k ( seq_strict_v4 f hf k ) _ _
          · exact seq_strict_v4_properties_final f hf k |>.1
          · exact seq_strict_v4_properties_final f hf k |>.2.1.symm ▸ Finset.Subset.refl _
      · convert step_strict_v4_succeeds f hf k ( seq_strict_v4 f hf k ) _ _
        · exact seq_strict_v4_properties_final f hf k |>.1
        · exact seq_strict_v4_properties_final f hf k |>.2.1.symm ▸ Finset.Subset.refl _

/-
The final set B respects any constraint that appears at any stage of the construction.
-/
lemma B_final_v4_respects (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (p r : ℕ) (k : ℕ)
    (h : (p, r) ∈ (seq_strict_v4 f hf k).state.constraints) :
    ∀ b ∈ B_final_v4 f hf, b % p ≠ r := by
      have h_b_in_Bm : ∀ b ∈ B_final_v4 f hf, ∀ k, ∃ j ≥ k, b ∈ (seq_strict_v4 f hf j).state.B := by
        intros b hb k
        obtain ⟨j, hj⟩ : ∃ j, b ∈ (seq_strict_v4 f hf j).state.B := by
          unfold B_final_v4 at hb; aesop
        use Max.max k j
        exact ⟨ le_max_left _ _, by exact Nat.le_induction ( by tauto ) ( fun n hn ih => by have := seq_strict_v4_mono f hf n; aesop ) _ ( le_max_right k j ) ⟩
      intros b hb
      obtain ⟨j, hj_ge_k, hj_mem⟩ : ∃ j ≥ k, b ∈ (seq_strict_v4 f hf j).state.B := h_b_in_Bm b hb k
      have h_constraint_in_j : (p, r) ∈ (seq_strict_v4 f hf j).state.constraints := by
        -- By definition of `seq_strict_v4`, the constraints are monotonic.
        have h_constraints_mono : ∀ k j, k ≤ j → (seq_strict_v4 f hf k).state.constraints ⊆ (seq_strict_v4 f hf j).state.constraints := by
          intros k j hkj
          induction' hkj with j hj ih ih
          · rfl
          · exact Set.Subset.trans ih ( by exact seq_strict_v4_mono f hf j |>.2 )
        generalize_proofs at *; (exact h_constraints_mono k j hj_ge_k h)
      exact ( seq_strict_v4 f hf j ).state.h_respects _ h_constraint_in_j _ hj_mem

/-
The constructed set B (version 4) is admissible.
-/
theorem B_final_v4_admissible (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Admissible (B_final_v4 f hf) := by
      -- Let `p` be a prime.
      intro p hp
      -- By `eventually_constrained_v4`, there exists `k` such that `p` is in `primes_in_constraints (seq_strict_v4 f hf k).state`.
      obtain ⟨k, hk⟩ : ∃ k, p ∈ primes_in_constraints (seq_strict_v4 f hf k).state := by
        exact eventually_constrained_v4 f hf p hp
      -- By `B_final_v4_respects`, for all `b ∈ B_final_v4`, `b % p ≠ r`.
      obtain ⟨r, hr⟩ : ∃ r, (p, r) ∈ (seq_strict_v4 f hf k).state.constraints ∧ r < p := by
        obtain ⟨r, hr⟩ : ∃ r, (p, r) ∈ (seq_strict_v4 f hf k).state.constraints := by
          unfold primes_in_constraints at hk; aesop
        exact ⟨ r, hr, by have := seq_strict_v4_properties_final f hf k; have := this.2.2 ( p, r ) hr; aesop ⟩
      use r
      intro b hb
      -- By `B_final_v4_respects`, for all `b ∈ B_final_v4`, `b % p ≠ r`.
      have h_respects : b % p ≠ r := by
        exact B_final_v4_respects f hf p r k hr.1 b hb
      contrapose! h_respects; haveI := Fact.mk hp; simp_all +decide
      exact Nat.mod_eq_of_lt hr.2 ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using h_respects

/-
For every integer shift n, there is an element b in B (version 4) such that b+n is composite.
-/
theorem B_final_v4_composite_shift (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∀ n : ℤ, ∃ b ∈ B_final_v4 f hf, ¬ Nat.Prime (Int.toNat (b + n)) := by
      intro n
      obtain ⟨k, hk⟩ : ∃ k, zigzag k = n := by
        exact zigzag_surjective n
      -- By the properties of the construction sequence, there exists an element `b` in `B_final_v4` such that `b + n` is divisible by a prime greater than 2.
      obtain ⟨b, hb⟩ : ∃ b ∈ (seq_strict_v4 f hf (k + 1)).state.B, ∃ p : ℕ, Nat.Prime p ∧ p > 2 ∧ (b + n) % p = 0 ∧ b + n > p := by
        -- By definition of `step_strict_minimal_state`, there exists a `b` in the `k+1`th state such that `b + zigzag k` is composite.
        obtain ⟨b, hb⟩ : ∃ b ∈ (step_strict_minimal_state f hf (zigzag k) (seq_strict_v4 f hf k)).B, ∃ p : ℕ, Nat.Prime p ∧ p > 2 ∧ (b + zigzag k) % p = 0 ∧ b + zigzag k > p := by
          unfold step_strict_minimal_state
          field_simp
          split_ifs
          · have := Classical.choose_spec ( find_blocking_element f hf ( seq_strict_v4 f hf k |> GoodState.state |> ConstructionStateV2.B ) ( seq_strict_v4 f hf k |> GoodState.h_dens ) ( seq_strict_v4 f hf k |> GoodState.state |> ConstructionStateV2.constraints ) ( seq_strict_v4 f hf k |> GoodState.state |> ConstructionStateV2.h_prime ) ( seq_strict_v4 f hf k |> GoodState.state |> ConstructionStateV2.h_coprime ) ( seq_strict_v4 f hf k |> GoodState.h_consistent_2 ) ( zigzag k ) )
            exact ⟨ _, Finset.mem_union_right _ ( Finset.mem_singleton_self _ ), this.choose, this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2.2.2.1, this.choose_spec.2.2.2.2.2.1 ⟩
          · rename_i h
            exact False.elim <| h <| by simpa [ seq_strict_v4_properties_final f hf k ] using step_strict_v4_succeeds f hf k ( seq_strict_v4 f hf k ) ( by simp [ seq_strict_v4_properties_final f hf k ] ) ( by simp [ seq_strict_v4_properties_final f hf k ] )
        aesop
      -- Since $b + n$ is divisible by a prime greater than 2, it must be composite.
      obtain ⟨p, hp_prime, hp_gt_two, hp_div, hp_gt⟩ := hb.right
      have h_composite : ¬Nat.Prime (Int.toNat (b + n)) := by
        intro H
        have h_mod : (Int.toNat (b + n)) % p = 0 := by
          grind
        have h_dvd := Nat.dvd_of_mod_eq_zero h_mod
        rw [H.dvd_iff_eq] at h_dvd <;> norm_cast at *
        · aesop
        · linarith [hp_prime.two_le]
      exact ⟨ b, Set.mem_iUnion.mpr ⟨ k + 1, hb.1 ⟩, h_composite ⟩

/-
The constructed set B (version 4) satisfies the density condition.
-/
theorem B_final_v4_density (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∀ N, ((B_final_v4 f hf) ∩ Set.Icc 1 N).toFinset.card ≤ f N := by
      -- Since $S$ is finite, there must be some $k$ where all elements of $S$ are in the $k$-th step's $B$.
      have h_exists_k : ∀ N, ∃ k, (B_final_v4 f hf ∩ Set.Icc 1 N).toFinset ⊆ (seq_strict_v4 f hf k).state.B := by
        intro N
        have h_seq_increasing : ∀ b ∈ B_final_v4 f hf ∩ Set.Icc 1 N, ∃ k, b ∈ (seq_strict_v4 f hf k).state.B := by
          unfold B_final_v4; aesop
        have h_seq_increasing : ∀ b ∈ B_final_v4 f hf ∩ Set.Icc 1 N, ∃ k, ∀ j ≥ k, b ∈ (seq_strict_v4 f hf j).state.B := by
          intros b hb
          obtain ⟨k, hk⟩ := h_seq_increasing b hb
          use k
          intro j hj
          induction' hj with j hj ih
          · assumption
          · exact seq_strict_v4_mono f hf j |>.1 ih
        choose! k hk using h_seq_increasing
        exact ⟨ Finset.sup ( Set.Finite.toFinset ( show Set.Finite ( B_final_v4 f hf ∩ Set.Icc 1 N ) from Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2.2 ⟩ ) ) k, fun x hx => hk x ( by simpa using hx ) _ ( Finset.le_sup ( f := k ) ( by simpa using hx ) ) ⟩
      intro N
      obtain ⟨k, hk⟩ := h_exists_k N
      have h_card_le_fN : ((seq_strict_v4 f hf k).state.B ∩ (Finset.Icc 1 N)).card ≤ f N := by
        convert ( seq_strict_v4 f hf k ).h_dens N using 1
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_le_fN

/-
The constructed set B (version 4) is infinite.
-/
theorem B_final_v4_infinite (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    (B_final_v4 f hf).Infinite := by
      -- By Lemma~\ref{lem:seq_strict_v4_properties_final}, B_final_v4 is infinite.
      have h_inf : ∀ k, (seq_strict_v4 f hf k).state.B.card = k := by
        exact fun k => seq_strict_v4_properties_final f hf k |>.1
      intro h_finite_inf
      -- Since B_final_v4 is finite, there exists some maximum size M.
      obtain ⟨M, hM⟩ : ∃ M, ∀ k, (seq_strict_v4 f hf k).state.B.card ≤ M := by
        exact ⟨ h_finite_inf.toFinset.card, fun k => Finset.card_le_card fun x hx => h_finite_inf.mem_toFinset.mpr <| Set.mem_iUnion.mpr ⟨ k, hx ⟩ ⟩
      linarith [ h_inf ( M + 1 ), hM ( M + 1 ) ]

/-
The main theorem: there exists an infinite set B satisfying the density condition, admissibility, and the composite shift property.
-/
theorem main_theorem (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ B : Set ℕ, B.Infinite ∧
    (∀ N, (B ∩ Set.Icc 1 N).toFinset.card ≤ f N) ∧
    Admissible B ∧
    (∀ n : ℤ, ∃ b ∈ B, ¬ Nat.Prime (Int.toNat (b + n))) := by
      -- Let's choose the set B_final_v4 as our witness.
      use B_final_v4 f hf
      exact ⟨ B_final_v4_infinite f hf, B_final_v4_density f hf, B_final_v4_admissible f hf, B_final_v4_composite_shift f hf ⟩


#print axioms main_theorem
-- 'Erdos429.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos429
