/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Answering Erdos Problem #221 (https://www.erdosproblems.com/221), Ruzsa proved that there exists a set $A$ with $|\{a \in A : a \le x\}| \le \frac{cx}{\log x}$ for all large enough $x$ and an absolute constant $c$, such that every large enough integer can be written as $2^k + a$ for some $k \ge 0$ and $a \in A$.

Ruzsa, Jr., I., On a problem of P. Erdős. Canad. Math. Bull. (1972), 309-310. Available here: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/802ABD868A907C2ADB78C580C73C86FC/S0008439500061348a.pdf/on-a-problem-of-p-erdos.pdf.

I rewrote his proof to make it slightly more explicit, which Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) then formalized, the result of which can be found below.

Boris Alexeev was kind enough to slightly alter the proof in order to get rid of all the warnings on unused variables. Thankyou!
-/

import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos221

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
For each integer n >= 1, A_n is the set of numbers of the form 5^n * m or 5^n * m + 1 where 1 <= m < 2^(5^(n+1)). A is the union of all A_n for n >= 1.
-/
def A_n (n : ℕ) : Set ℕ :=
  {x | ∃ m, 1 ≤ m ∧ m < 2^(5^(n+1)) ∧ (x = 5^n * m ∨ x = 5^n * m + 1)}

def A : Set ℕ := ⋃ n ≥ 1, A_n n

/-
The multiplicative order of 2 modulo 5 is 4.
-/
lemma lem_order_mod5 : orderOf (2 : ZMod 5) = 4 := by
  simp +decide only [orderOf_eq_iff]

/-
If the multiplicative order of 2 modulo 5^n is 4 * 5^(n-1), then the multiplicative order of 2 modulo 5^(n+1) is 4 * 5^n.
-/
theorem lem_order_lift_explicit (n : ℕ) (h : n ≥ 1)
  (h_ord : orderOf (2 : ZMod (5^n)) = 4 * 5^(n-1)) :
  orderOf (2 : ZMod (5^(n+1))) = 4 * 5^n := by
    -- Let $r_{n+1} := ord_{5^{n+1}}(2)$. Reduction modulo 5^n shows $2^{r_{n+1}} ≡ 1 (mod 5^n)$, hence $r_n | r_{n+1}$. Thus there exists $t ∈ Z_{≥1}$ with $r_{n+1} = r_n * t$.
    have h_div : (orderOf (2 : ZMod (5 ^ n))) ∣ (orderOf (2 : ZMod (5 ^ (n + 1)))) := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      -- By definition of order, we know that $2^{orderOf (2 : ZMod (5 ^ (n + 1)))} \equiv 1 \pmod{5^{n+1}}$.
      have h_order : 2 ^ orderOf (2 : ZMod (5 ^ (n + 1))) ≡ 1 [MOD 5 ^ (n + 1)] := by
        simp +decide [ ← ZMod.natCast_eq_natCast_iff, pow_orderOf_eq_one ];
      simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_order.of_dvd <| pow_dvd_pow _ <| Nat.le_succ _
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (orderOf (2 : ZMod (5 ^ (n + 1)))) = (orderOf (2 : ZMod (5 ^ n))) * t := h_div;
    -- We will show $t = 5$. Consider the integer $u := 2^{r_n}$. By definition of $r_n$, $u ≡ 1 (mod 5^n)$. Write $u = 1 + 5^n * s$ for an integer $s$. Note that $s$ is not congruent to $0 mod 5$.
    obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 ^ (orderOf (2 : ZMod (5 ^ n))) = 1 + 5 ^ n * s ∧ ¬(5 ∣ s) := by
      -- By definition of $r_n$, $u ≡ 1 (mod 5^n)$. Write $u = 1 + 5^n * s$ for an integer $s$. Note that $s$ is not congruent to $0 mod 5$.
      have h_u_mod : 2 ^ (orderOf (2 : ZMod (5 ^ n))) ≡ 1 [MOD 5 ^ n] ∧ ¬(5 ∣ (2 ^ (orderOf (2 : ZMod (5 ^ n))) - 1) / 5 ^ n) := by
        -- By definition of $r_n$, $u ≡ 1 (mod 5^n)$. Write $u = 1 + 5^n * s$ for an integer $s$. Note that $s$ is not congruent to $0 mod 5$ because $2^{r_n} ≡ 1 (mod 5^{n+1})$ would contradict $r_n$ being the order modulo $5^n$.
        have h_u_mod : 2 ^ (orderOf (2 : ZMod (5 ^ n))) ≡ 1 [MOD 5 ^ n] ∧ ¬(5 ∣ (2 ^ (orderOf (2 : ZMod (5 ^ n))) - 1) / 5 ^ n) := by
          have h_cong : 2 ^ (orderOf (2 : ZMod (5 ^ n))) ≡ 1 [MOD 5 ^ n] := by
            simp +decide [ ← ZMod.natCast_eq_natCast_iff, pow_orderOf_eq_one ]
          have h_not_div : ¬(5 ∣ (2 ^ (orderOf (2 : ZMod (5 ^ n))) - 1) / 5 ^ n) := by
            -- By definition of $r_n$, $u ≡ 1 (mod 5^n)$. Write $u = 1 + 5^n * s$ for an integer $s$. Note that $s$ is not congruent to $0 mod 5$ because $2^{r_n} ≡ 1 (mod 5^{n+1})$ would contradict $r_n$ being the order modulo $5^n$. Hence, $s$ must be not divisible by 5.
            have h_not_div : ¬(2 ^ (4 * 5 ^ (n - 1)) ≡ 1 [MOD 5 ^ (n + 1)]) := by
              -- We'll use that $2^{4 \cdot 5^{n-1}} \equiv 1 + 5^n \cdot k \pmod{5^{n+1}}$ for some integer $k$ not divisible by 5.
              have h_cong : ∃ k : ℕ, 2 ^ (4 * 5 ^ (n - 1)) = 1 + 5 ^ n * k ∧ ¬(5 ∣ k) := by
                -- We'll use induction to prove that the order of 2 modulo 5^n is 4*5^(n-1).
                have h_ind : ∀ n ≥ 1, ∃ k : ℕ, 2 ^ (4 * 5 ^ (n - 1)) = 1 + 5 ^ n * k ∧ ¬(5 ∣ k) := by
                  intro n hn
                  induction' n, Nat.succ_le_iff.mpr hn using Nat.le_induction with n hn ih;
                  · exists ( 2 ^ 4 - 1 ) / 5;
                  · rcases ih ‹_› with ⟨ k, hk₁, hk₂ ⟩ ; rcases n <;> simp_all +decide [ pow_succ, pow_mul ];
                    refine' ⟨ k + k ^ 2 * 5 ^ ‹_› * 10 + k ^ 3 * 5 ^ ( ‹_› * 2 ) * 50 + k ^ 4 * 5 ^ ( ‹_› * 3 ) * 125 + k ^ 5 * 5 ^ ( ‹_› * 4 ) * 125, _, _ ⟩ <;> ring_nf at * ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at * ; aesop ( simp_config := { decide := true } ) ;
                exact h_ind n h;
              rcases h_cong with ⟨ k, hk₁, hk₂ ⟩ ; rw [ hk₁ ] ; rw [ Nat.modEq_iff_dvd ] ; norm_num [ pow_add, pow_mul ];
              exact_mod_cast Nat.mul_dvd_mul_iff_left ( by positivity ) |>.not.mpr hk₂;
            contrapose! h_not_div; simp_all +decide [ Nat.ModEq ] ;
            -- If $5 \mid (2 ^ (4 * 5 ^ (n - 1)) - 1) / 5 ^ n$, then $2 ^ (4 * 5 ^ (n - 1)) - 1$ is divisible by $5^{n+1}$.
            have h_div : 5 ^ (n + 1) ∣ (2 ^ (4 * 5 ^ (n - 1)) - 1) := by
              convert Nat.mul_dvd_mul_left ( 5 ^ n ) h_not_div using 1 ; rw [ Nat.mul_div_cancel' ] ; simpa [ ← Int.natCast_dvd_natCast ] using Nat.modEq_iff_dvd.mp h_cong.symm;
            exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using h_div )
          exact ⟨h_cong, h_not_div⟩;
        exact h_u_mod;
      obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 ^ (orderOf (2 : ZMod (5 ^ n))) - 1 = 5 ^ n * s := by
        exact exists_eq_mul_right_of_dvd ( by simpa [ ← Int.natCast_dvd_natCast ] using h_u_mod.1.symm.dvd );
      exact ⟨ s, by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow ( orderOf ( 2 : ZMod ( 5 ^ n ) ) ) 2 zero_lt_two ) ], by simpa [ hs ] using h_u_mod.2 ⟩;
    -- We now compute $u^5$ modulo $5^{n+1}$ using the binomial expansion: $u^5 = (1 + 5^n * s)^5 ≡ 1 + 5 * 5^n * s (mod 5^{n+1})$, because all other binomial coefficients (5 choose j) for 2 <= j <= 5 have a factor $5^2$ and therefore contribute multiples of $5^{n+2}$.
    have h_u5 : 2 ^ (orderOf (2 : ZMod (5 ^ n)) * 5) ≡ 1 + 5 ^ (n + 1) * s [MOD 5 ^ (n + 1)] := by
      have h_u5 : (1 + 5 ^ n * s) ^ 5 ≡ 1 + 5 ^ (n + 1) * s [MOD 5 ^ (n + 1)] := by
        refine Nat.ModEq.symm ( Nat.modEq_of_dvd ?_ );
        norm_num [ ← geom_sum_mul ] ; ring_nf ;
        refine' dvd_add ( dvd_add ( dvd_add _ _ ) _ ) _;
        · exact ⟨ s ^ 2 * 5 ^ n * 2, by ring ⟩;
        · exact ⟨ s ^ 3 * 5 ^ ( n * 2 ) * 2, by ring ⟩;
        · exact ⟨ s ^ 4 * 5 ^ ( n * 3 ), by ring ⟩;
        · exact ⟨ s ^ 5 * 5 ^ ( n * 4 - 1 ), by rw [ show ( 5 : ℤ ) ^ ( n * 5 ) = 5 ^ ( n * 4 - 1 ) * 5 ^ ( n + 1 ) by rw [ ← pow_add ] ; congr 1; omega ] ; ring ⟩;
      convert h_u5 using 1 ; rw [ pow_mul, hs.1 ];
    -- Thus $2^{r_n * 5} ≡ 1 (mod 5^{n+1})$. So the order $r_{n+1}$ divides $r_n * 5$. Since $r_n | r_{n+1}$ we get $r_{n+1} = r_n$ or $r_n * 5$.
    have h_div : (orderOf (2 : ZMod (5 ^ (n + 1)))) ∣ (orderOf (2 : ZMod (5 ^ n))) * 5 := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
    have h_cases : (orderOf (2 : ZMod (5 ^ (n + 1)))) = (orderOf (2 : ZMod (5 ^ n))) ∨ (orderOf (2 : ZMod (5 ^ (n + 1)))) = (orderOf (2 : ZMod (5 ^ n))) * 5 := by
      simp_all +decide [ Nat.mul_dvd_mul_iff_left ];
      rwa [ Nat.dvd_prime ( by decide ) ] at h_div;
    -- But $r_{n+1} = r_n$ is impossible because that would imply $2^{r_n} ≡ 1 (mod 5^{n+1})$, contradicting $s$ is not congruent to $0 mod 5$.
    have h_contra : ¬(2 ^ (orderOf (2 : ZMod (5 ^ n))) ≡ 1 [MOD 5 ^ (n + 1)]) := by
      rw [ Nat.modEq_iff_dvd ];
      norm_num [ hs.1 ];
      rw [ pow_succ, mul_dvd_mul_iff_left ( by positivity ) ] ; norm_cast ; exact fun h => hs.2 <| by simpa [ Nat.Prime.dvd_iff_not_coprime ] using h;
    rcases h_cases with h_case | h_case
    · exfalso
      exact h_contra (by
        simpa [h_case, ← ZMod.natCast_eq_natCast_iff] using
          (pow_orderOf_eq_one (2 : ZMod (5 ^ (n + 1)))))
    · rw [h_case, h_ord]
      cases n with
      | zero => omega
      | succ n =>
          simp [pow_succ, Nat.mul_left_comm, Nat.mul_comm]

/-
For every integer n >= 1, the multiplicative order of 2 modulo 5^n is 4 * 5^(n-1).
-/
theorem thm_2_is_primitive_root (n : ℕ) (h : n ≥ 1) :
  orderOf (2 : ZMod (5^n)) = 4 * 5^(n-1) := by
    induction h <;> simp_all +decide;
    · exact lem_order_mod5;
    · convert lem_order_lift_explicit _ ‹_› ‹_› using 1

/-
For every residue r coprime to 5^n, there exists k with 1 <= k <= 4 * 5^(n-1) such that 2^k is congruent to r modulo 5^n.
-/
theorem cor_surject_powers (n : ℕ) (h : n ≥ 1) (r : ZMod (5^n)) (hr : IsUnit r) :
  ∃ k, 1 ≤ k ∧ k ≤ 4 * 5^(n-1) ∧ 2^k = r := by
    -- By definition of totient function, since r is coprime to 5^n, there exists some integer k such that 2^k ≡ r (mod 5^n).
    have ⟨k, hk⟩ : ∃ k, 0 ≤ k ∧ k < 4 * 5^(n-1) ∧ (2 : ZMod (5^n)) ^ k = r := by
      -- Since $\text{orderOf}(2) = 4 \cdot 5^{n-1}$, the powers of $2$ modulo $5^n$ generate all units modulo $5^n$.
      have h_order : (Finset.image (fun k => (2 : ZMod (5^n)) ^ k) (Finset.range (4 * 5^(n-1)))) = Finset.filter (fun x => IsUnit x) (Finset.univ : Finset (ZMod (5^n))) := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
        · -- Since $2$ is a unit modulo $5^n$, any power of $2$ is also a unit modulo $5^n$.
          have h_unit : IsUnit (2 : ZMod (5 ^ n)) := by
            -- Since $2$ is coprime to $5^n$, it is a unit modulo $5^n$.
            have h_coprime : Nat.gcd 2 (5 ^ n) = 1 := by
              cases n <;> norm_num;
            have h_unit : ∃ x : ℕ, 2 * x ≡ 1 [MOD 5 ^ n] := by
              obtain ⟨x, _hx_lt, hx⟩ :=
                Nat.exists_mul_mod_eq_one_of_coprime h_coprime
                  (one_lt_pow₀ (by decide : 1 < 5) (by linarith))
              exact ⟨x, by
                simpa [Nat.ModEq,
                  Nat.mod_eq_of_lt (show 1 < 5 ^ n from
                    one_lt_pow₀ (by decide : 1 < 5) (by linarith))] using hx⟩
            exact isUnit_iff_exists_inv.mpr ⟨ h_unit.choose, by simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_unit.choose_spec ⟩;
          exact fun x hx => by simpa using h_unit.pow x;
        · -- The set of units modulo $5^n$ has cardinality $\phi(5^n) = 4 \cdot 5^{n-1}$.
          have h_units_card : (Finset.filter (fun x => IsUnit x) (Finset.univ : Finset (ZMod (5^n)))).card = 4 * 5^(n-1) := by
            -- The set of units modulo $5^n$ is exactly the set of integers coprime to $5^n$, which has cardinality $\phi(5^n)$.
            have h_units : (Finset.filter (fun x : ZMod (5^n) => IsUnit x) (Finset.univ : Finset (ZMod (5^n)))).card = Nat.totient (5^n) := by
              have h_units_card : (Finset.filter (fun x : ZMod (5^n) => IsUnit x) (Finset.univ : Finset (ZMod (5^n)))).card = Nat.totient (5^n) := by
                have h_units : Finset.filter (fun x : ZMod (5^n) => IsUnit x) (Finset.univ : Finset (ZMod (5^n))) = Finset.image (fun x : ℕ => x : ℕ → ZMod (5^n)) (Finset.filter (fun x : ℕ => Nat.gcd x (5^n) = 1) (Finset.range (5^n))) := by
                  ext x; simp [IsUnit];
                  constructor <;> intro hx;
                  · obtain ⟨ a, rfl ⟩ := hx;
                    refine' ⟨ a.val.val, ⟨ _, _ ⟩, _ ⟩;
                    · exact ZMod.val_lt _;
                    · exact ZMod.val_coe_unit_coprime a;
                    · cases n <;> aesop;
                  · obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hx; use Units.mkOfMulEqOne a ( a⁻¹ ) ( by
                      exact ZMod.coe_mul_inv_eq_one a ha₂ ) ; aesop;
                rw [ h_units, Finset.card_image_of_injOn ] <;> norm_num [ Nat.totient ];
                · simp +decide only [Nat.coprime_comm];
                · exact fun x hx y hy hxy => Nat.mod_eq_of_lt hx.1 ▸ Nat.mod_eq_of_lt hy.1 ▸ by simpa [ ZMod.natCast_eq_natCast_iff' ] using hxy;
              linarith;
            rw [ h_units, Nat.totient_prime_pow ] <;> norm_num;
            · ring;
            · linarith;
          rw [ Finset.card_image_of_injOn ] ; aesop;
          -- Since $2$ is a primitive root modulo $5^n$, the powers of $2$ modulo $5^n$ are distinct.
          have h_distinct : ∀ k l : ℕ, k < l → k < 4 * 5^(n-1) → l < 4 * 5^(n-1) → (2 : ZMod (5^n)) ^ k ≠ (2 : ZMod (5^n)) ^ l := by
            intros k l hkl hk hl h_eq
            have h_order : orderOf (2 : ZMod (5^n)) = 4 * 5^(n-1) := by
              exact thm_2_is_primitive_root n h;
            -- Since $2^k = 2^l$, we have $2^{l-k} = 1$.
            have h_exp : (2 : ZMod (5^n)) ^ (l - k) = 1 := by
              have h_exp : (2 : ZMod (5^n)) ^ k * (2 : ZMod (5^n)) ^ (l - k) = (2 : ZMod (5^n)) ^ k := by
                rw [ ← pow_add, add_tsub_cancel_of_le hkl.le, h_eq ];
              have h_inv : IsUnit (2 ^ k : ZMod (5 ^ n)) := by
                have h_inv : IsUnit (2 : ZMod (5 ^ n)) := by
                  exact isUnit_iff_dvd_one.mpr ( by exact ⟨ 2 ^ ( orderOf ( 2 : ZMod ( 5 ^ n ) ) - 1 ), by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by aesop ) ] ; rw [ pow_orderOf_eq_one ] ⟩ );
                exact h_inv.pow _;
              exact h_inv.mul_left_cancel ( by linear_combination' h_exp );
            exact absurd ( h_order ▸ orderOf_dvd_iff_pow_eq_one.mpr h_exp ) ( Nat.not_dvd_of_pos_of_lt ( Nat.sub_pos_of_lt hkl ) ( by omega ) );
          exact fun k hk l hl hkl => le_antisymm ( le_of_not_gt fun hkl' => h_distinct _ _ hkl' ( Finset.mem_range.mp hl ) ( Finset.mem_range.mp hk ) hkl.symm ) ( le_of_not_gt fun hkl' => h_distinct _ _ hkl' ( Finset.mem_range.mp hk ) ( Finset.mem_range.mp hl ) hkl );
      replace h_order := Finset.ext_iff.mp h_order r; aesop;
    by_cases hk_zero : k = 0;
    · use 4 * 5^(n-1);
      have := thm_2_is_primitive_root n h; simp_all +decide [ orderOf_eq_iff ] ;
      exact Nat.mul_pos ( by decide ) ( pow_pos ( by decide ) _ );
    · exact ⟨ k, Nat.pos_of_ne_zero hk_zero, hk.2.1.le, hk.2.2 ⟩

/-
For x >= 2 and n >= 1, the number of elements in A_n less than or equal to x is at most min(2 * floor(x/5^n), 2 * (2^(5^(n+1)) - 1)).
-/
lemma lem_two_bounds_AnN (x : ℕ) (n : ℕ) :
  Set.ncard {a ∈ A_n n | a ≤ x} ≤ min (2 * (x / 5^n)) (2 * (2^(5^(n+1)) - 1)) := by
    refine' le_min _ _;
    · -- By definition of $A_n$, we know that every element in $A_n$ is of the form $5^n m$ or $5^n m + 1$ for some $m$.
      have h_A_n : {a : ℕ | a ∈ A_n n ∧ a ≤ x} ⊆ Finset.image (fun m => 5^n * m) (Finset.Ico 1 (x / 5^n + 1)) ∪ Finset.image (fun m => 5^n * m + 1) (Finset.Ico 1 (x / 5^n + 1)) := by
        simp +zetaDelta at *;
        rintro a ⟨ ⟨ m, hm₁, hm₂, rfl | rfl ⟩, ha ⟩ <;> [ exact Or.inl ⟨ m, ⟨ hm₁, Nat.lt_succ_of_le ( Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by nlinarith ) ⟩, rfl ⟩ ; exact Or.inr ⟨ m, ⟨ hm₁, Nat.lt_succ_of_le ( Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by nlinarith ) ⟩, rfl ⟩ ];
      refine' le_trans ( Set.ncard_le_ncard h_A_n ) _;
      rw [ Set.ncard_eq_toFinset_card' ] ; norm_num [ two_mul ];
      exact le_trans ( Finset.card_union_le _ _ ) ( by rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] );
    · refine' le_trans ( Set.ncard_le_ncard <| show { a : ℕ | a ∈ A_n n ∧ a ≤ x } ⊆ Set.image ( fun m ↦ 5 ^ n * m ) ( Set.Ico 1 ( 2 ^ 5 ^ ( n + 1 ) ) ) ∪ Set.image ( fun m ↦ 5 ^ n * m + 1 ) ( Set.Ico 1 ( 2 ^ 5 ^ ( n + 1 ) ) ) from _ ) _;
      · intro a ha; unfold A_n at ha; aesop;
      · refine' le_trans ( Set.ncard_union_le _ _ ) _;
        rw [ Set.ncard_image_of_injective, Set.ncard_image_of_injective ] <;> norm_num [ Function.Injective ];
        omega

/-
For every integer N >= 32, there exist n, k, m such that n >= 1, 5^n <= log2(N) < 5^(n+1), 1 <= k < 5^n, 1 <= m < 2^(5^(n+1)), and N - 2^k is either 5^n * m or 5^n * m + 1.
-/
lemma lem_choose_n_k_m (N : ℕ) (hN : N ≥ 32) :
  ∃ n k m, n ≥ 1 ∧ 5^n ≤ Real.logb 2 N ∧ Real.logb 2 N < 5^(n+1) ∧
  1 ≤ k ∧ k < 5^n ∧ m ≥ 1 ∧ m < 2^(5^(n+1)) ∧
  (N = 2^k + 5^n * m ∨ N = 2^k + 5^n * m + 1) := by
    -- By definition of exponentiation, we know that $2^{5^n} \leq N < 2^{5^{n+1}}$.
    obtain ⟨n, hn1, hn2⟩ : ∃ n, 5^n ≤ Real.logb 2 N ∧ Real.logb 2 N < 5^(n+1) ∧ n ≥ 1 := by
      use Nat.floor (Real.logb 5 (Real.logb 2 N));
      refine' ⟨ _, _, Nat.floor_pos.mpr _ ⟩;
      · have := Nat.floor_le ( Real.logb_nonneg ( show ( 5 : ℝ ) > 1 by norm_num ) ( show ( Real.logb 2 N : ℝ ) ≥ 1 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_num <;> linarith [ show ( N : ℝ ) ≥ 32 by norm_cast ] ) ) ; rw [ Real.le_logb_iff_rpow_le ] at this <;> norm_cast at *;
        exact Real.logb_pos ( by norm_num ) ( by norm_cast; linarith );
      · have := Nat.lt_floor_add_one ( Real.logb 5 ( Real.logb 2 N ) );
        rw [ Real.logb_lt_iff_lt_rpow ] at * <;> norm_cast at *;
        · rw [ Real.logb_lt_iff_lt_rpow ] at this <;> norm_cast at * ; linarith;
        · exact Real.logb_pos ( by norm_num ) ( by norm_cast; linarith );
        · linarith;
      · rw [ Real.le_logb_iff_rpow_le ] <;> norm_num;
        · rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast ; linarith;
        · exact Real.logb_pos ( by norm_num ) ( by norm_cast; linarith );
    -- By Corollary cor_surject_powers, there exists $k$ with $1 \leq k < 5^n$ such that $2^k \equiv N \pmod{5^n}$ or $2^k \equiv N-1 \pmod{5^n}$.
    obtain ⟨k, hk1, hk2⟩ : ∃ k, 1 ≤ k ∧ k < 5^n ∧ (2^k ≡ N [MOD 5^n] ∨ 2^k ≡ N - 1 [MOD 5^n]) := by
      -- By Corollary cor_surject_powers, there exists $k$ with $1 \leq k < 4 * 5^(n-1)$ such that $2^k \equiv N \pmod{5^n}$ or $2^k \equiv N-1 \pmod{5^n}$.
      obtain ⟨k, hk1, hk2⟩ : ∃ k, 1 ≤ k ∧ k ≤ 4 * 5^(n-1) ∧ (2^k ≡ N [ZMOD 5^n] ∨ 2^k ≡ N - 1 [ZMOD 5^n]) := by
        -- By Corollary cor_surject_powers, there exists $k$ with $1 \leq k \leq 4 * 5^(n-1)$ such that $2^k \equiv N \pmod{5^n}$ or $2^k \equiv N-1 \pmod{5^n}$.
        have h_surject : ∀ r : ZMod (5^n), IsUnit r → ∃ k, 1 ≤ k ∧ k ≤ 4 * 5^(n-1) ∧ (2^k : ZMod (5^n)) = r := by
          convert cor_surject_powers n hn2.2 using 1;
        -- Let $r$ be the residue of $N$ modulo $5^n$.
        obtain ⟨r, hr⟩ : ∃ r : ZMod (5^n), r = N ∧ IsUnit r ∨ ∃ r : ZMod (5^n), r = N - 1 ∧ IsUnit r := by
          -- Since $N$ and $N-1$ are consecutive integers, one of them must be coprime to $5^n$.
          have h_coprime : Nat.gcd N (5^n) = 1 ∨ Nat.gcd (N - 1) (5^n) = 1 := by
            rcases N with ( _ | _ | N ) <;> simp_all +decide;
            rcases n with ( _ | n ) <;> simp_all +decide;
            rw [ ← Nat.mod_add_div N 5 ] ; have := Nat.mod_lt N ( by decide : 5 > 0 ) ; interval_cases N % 5 <;> simp +arith +decide;
          rcases h_coprime with h | h;
          · refine' ⟨ _, Or.inl ⟨ rfl, _ ⟩ ⟩;
            exact (ZMod.isUnit_iff_coprime N (5 ^ n)).mpr h;
          · have h_unit : IsUnit ((N - 1 : ℕ) : ZMod (5^n)) := by
              exact (ZMod.isUnit_iff_coprime (N - 1) (5 ^ n)).mpr h;
            cases N <;> aesop;
        rcases hr with ( ⟨ rfl, hr ⟩ | ⟨ r, rfl, hr ⟩ ) <;> simp_all +decide;
        · obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_surject _ hr; use k; simp_all +decide ;
          norm_cast at *;
          erw [ ← ZMod.natCast_eq_natCast_iff ] at * ; aesop;
        · obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_surject _ hr; use k; simp_all +decide ;
          norm_cast at *;
          erw [ ← ZMod.intCast_eq_intCast_iff ] at * ; aesop;
      refine' ⟨ k, hk1, _, _ ⟩ <;> rcases n <;> simp_all +decide [ pow_succ' ];
      · linarith [ pow_pos ( by decide : 0 < 5 ) ‹_› ];
      · rcases N <;> simp_all +decide [ ← Int.natCast_modEq_iff ];
    -- Thus there exists an integer $m \geq 0$ with $N - 2^k = 5^n m$ or $N - 2^k = 5^n m + 1$.
    obtain ⟨m, hm⟩ : ∃ m, N - 2^k = 5^n * m ∨ N - 2^k = 5^n * m + 1 := by
      rcases hk2.2 with h | h;
      · rw [ ← Nat.mod_add_div ( N : ℕ ) ( 5 ^ n ), ← Nat.mod_add_div ( 2 ^ k ) ( 5 ^ n ), h ];
        exact ⟨ N / 5 ^ n - ( 2 ^ k / 5 ^ n ), Or.inl <| Nat.sub_eq_of_eq_add <| by nlinarith [ Nat.sub_add_cancel <| show 2 ^ k / 5 ^ n ≤ N / 5 ^ n from Nat.div_le_div_right <| show 2 ^ k ≤ N from by
                                                                                                                                                                                    rw [ Real.le_logb_iff_rpow_le ] at * <;> norm_cast at *;
                                                                                                                                                                                    · exact le_trans ( pow_le_pow_right₀ ( by decide ) hk2.1.le ) hn1;
                                                                                                                                                                                    · linarith ] ⟩;
      · -- Since $2^k \equiv N - 1 \pmod{5^n}$, we have $N - 2^k \equiv 1 \pmod{5^n}$.
        have h_mod : (N - 2^k) % 5^n = 1 % 5^n := by
          refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
          convert h.dvd using 1 ; norm_num [ Nat.cast_sub ( show 2 ^ k ≤ N from _ ) ];
          rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> ring_nf;
          · linarith;
          · rw [ Real.le_logb_iff_rpow_le ] at * <;> norm_cast at * <;> try linarith;
            exact le_trans ( pow_le_pow_right₀ ( by decide ) hk2.1.le ) hn1;
        exact ⟨ ( N - 2 ^ k ) / 5 ^ n, Or.inr ( by linarith [ Nat.mod_add_div ( N - 2 ^ k ) ( 5 ^ n ), Nat.mod_eq_of_lt ( show 1 < 5 ^ n from one_lt_pow₀ ( by decide ) ( by linarith ) ) ] ) ⟩;
    -- We must show $m \geq 1$ and $m < 2^{5^{n+1}}$.
    have hm_ge_1 : m ≥ 1 := by
      -- Since $N \geq 2^{5^n}$ and $2^k \leq 2^{5^n - 1}$, we have $N - 2^k \geq 2^{5^n} - 2^{5^n - 1} = 2^{5^n - 1}$.
      have h_diff_ge_2_pow : N - 2^k ≥ 2^(5^n - 1) := by
        have h_diff_ge_2_pow : N ≥ 2^(5^n) := by
          rw [ Real.le_logb_iff_rpow_le ] at * <;> norm_cast at * ; linarith;
        exact le_tsub_of_add_le_left ( by rw [ show 2 ^ 5 ^ n = 2 ^ ( 5 ^ n - 1 ) * 2 by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ] at h_diff_ge_2_pow; nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show k ≤ 5 ^ n - 1 from Nat.le_sub_one_of_lt hk2.1 ) ] );
      rcases m with ( _ | _ | m ) <;> simp_all +decide;
      rcases hm with ( hm | hm ) <;> linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show 5 ^ n - 1 ≥ 1 from Nat.sub_pos_of_lt ( one_lt_pow₀ ( by decide ) ( by linarith ) ) ) ]
    have hm_lt_2_pow_5_pow_succ : m < 2^(5^(n+1)) := by
      -- From the choice of $n$, $\log_2 N < 5^{n+1}$ implies $N < 2^{5^{n+1}}$.
      have hN_lt_2_pow_5_pow_succ : N < 2^(5^(n+1)) := by
        rw [ Real.logb_lt_iff_lt_rpow ] at * <;> norm_cast at * ; linarith;
        linarith;
      cases hm <;> nlinarith [ Nat.sub_le N ( 2 ^ k ), pow_pos ( show 0 < 5 by decide ) n ] ;
    exact ⟨ n, k, m, hn2.2, hn1, hn2.1, hk1, hk2.1, hm_ge_1, hm_lt_2_pow_5_pow_succ, by cases' hm with hm hm <;> [ left; right ] <;> linarith [ Nat.sub_add_cancel ( show 2 ^ k ≤ N from le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop ) ) ) ] ⟩

/-
For every integer N >= 32, there exist integers k >= 1 and a in A such that N = 2^k + a.
-/
theorem thm_covering_explicit (N : ℕ) (hN : N ≥ 32) :
  ∃ k a, k ≥ 1 ∧ a ∈ A ∧ N = 2^k + a := by
    -- By Lemma~\ref{lem:choose_n_k_m}, there exist $n$, $k$, $m$ such that $n \ge 1$, $5^n \le \log_2(N) < 5^{n+1}$, $1 \le k < 5^n$, $1 \le m < 2^{5^{n+1}}$, and $N - 2^k$ is either $5^n * m$ or $5^n * m + 1$.
    obtain ⟨n, k, m, hn, hlogn, hk, hm⟩ : ∃ n k m : ℕ, n ≥ 1 ∧ 5^n ≤ Real.logb 2 N ∧ Real.logb 2 N < 5^(n+1) ∧ 1 ≤ k ∧ k < 5^n ∧ m ≥ 1 ∧ m < 2^(5^(n+1)) ∧ (N = 2^k + 5^n * m ∨ N = 2^k + 5^n * m + 1) := by
      convert lem_choose_n_k_m N ( mod_cast hN ) using 1;
    cases' hm.2.2.2.2 with h h;
    · use k, 5^n * m;
      exact ⟨ hm.1, Set.mem_iUnion.2 ⟨ n, Set.mem_iUnion.2 ⟨ hn, ⟨ m, hm.2.2.1, hm.2.2.2.1, Or.inl rfl ⟩ ⟩ ⟩, h ⟩;
    · use k, 5^n * m + 1;
      exact ⟨ hm.1, Set.mem_iUnion.2 ⟨ n, Set.mem_iUnion.2 ⟨ hn, ⟨ m, hm.2.2.1, hm.2.2.2.1, by aesop ⟩ ⟩ ⟩, by linarith ⟩

/-
There exists an absolute constant c such that, for every x >= 2 and every n >= 1, the number of elements in A_n less than or equal to x is at most c * x / log x.
-/
theorem prop_upper_linear :
  ∃ c > 0, ∀ x ≥ 2, ∀ n ≥ 1, Set.ncard {a ∈ A_n n | a ≤ x} ≤ c * x / Real.log x := by
    -- Set $c$ to be $10$.
    use 10;
    -- We need to verify that $10 > 0$.
    norm_num;
    intro x hx n hn;
    -- We use Lemma lem_two_bounds_AnN.
    have h_bound : (Set.ncard {a ∈ (A_n n) | a ≤ x} : ℝ) ≤ min (2 * (x / 5^n)) (2 * (2^(5^(n+1)) - 1)) := by
      exact_mod_cast lem_two_bounds_AnN x n;
    -- We consider two cases: $\log x \leq 5^{n+1}$ and $\log x > 5^{n+1}$.
    by_cases h_log : Real.log x ≤ 5^(n+1);
    · refine le_trans h_bound ?_;
      rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast ) ];
      refine' le_trans ( mul_le_mul_of_nonneg_left h_log <| Nat.cast_nonneg _ ) _;
      norm_cast;
      cases min_cases ( 2 * ( x / 5 ^ n ) ) ( 2 * ( 2 ^ 5 ^ ( n + 1 ) - 1 ) ) <;> nlinarith [ Nat.div_mul_le_self x ( 5 ^ n ), pow_pos ( show 0 < 5 by decide ) n, pow_succ' 5 n ];
    · -- Since $x > \exp(5^{n+1})$, we have $x / \log x > \exp(5^{n+1}) / 5^{n+1}$.
      have h_exp_log : (x : ℝ) / Real.log x > Real.exp (5^(n+1)) / (5^(n+1)) := by
        have h_exp_log : (x : ℝ) > Real.exp (5^(n+1)) := by
          exact lt_of_lt_of_le ( Real.exp_lt_exp.mpr ( not_le.mp h_log ) ) ( by rw [ Real.exp_log ( by positivity ) ] );
        field_simp;
        rw [ lt_div_iff₀ ( Real.log_pos ( by norm_cast ) ) ];
        have := Real.log_lt_sub_one_of_pos ( div_pos ( show ( x : ℝ ) > 0 by positivity ) ( Real.exp_pos ( 5 ^ ( n + 1 ) ) ) );
        rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_exp ] at this;
        have := this ( div_ne_one_of_ne h_exp_log.ne' ) ; rw [ lt_sub_iff_add_lt, lt_div_iff₀ ( Real.exp_pos _ ) ] at this; nlinarith [ Real.exp_pos ( 5 ^ ( n + 1 ) ), pow_le_pow_right₀ ( by norm_num : ( 1 :ℝ ) ≤ 5 ) ( by linarith : n + 1 ≥ 2 ) ] ;
      -- We need to show that $2 \cdot 2^{5^{n+1}} \leq 10 \cdot \exp(5^{n+1}) / 5^{n+1}$.
      have h_exp_log_bound : 2 * (2^(5^(n+1)) : ℝ) ≤ 10 * Real.exp (5^(n+1)) / (5^(n+1)) := by
        rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num ; ring_nf ; norm_num;
        rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_exp ] ; ring_nf ; norm_num;
        rw [ Real.log_div ] <;> norm_num ; induction hn <;> norm_num [ pow_succ' ] at *;
        · norm_num [ mul_comm, ← Real.log_rpow, ← Real.log_mul, Real.log_le_iff_le_exp ];
          have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 25 = ( Real.exp 1 ) ^ 25 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
        · rename_i k hk ih;
          refine' Nat.recOn k _ _ <;> norm_num [ pow_succ' ] at *;
          · norm_num [ mul_comm, ← Real.log_rpow, ← Real.log_mul, Real.log_le_iff_le_exp ];
            have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp 25 = ( Real.exp 1 ) ^ 25 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
          · intro n hn; nlinarith [ Real.log_pos ( show 2 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 5 > 2 by norm_num ), pow_pos ( by norm_num : ( 0 : ℝ ) < 5 ) n ] ;
      refine le_trans h_bound ?_;
      refine le_trans ?_ ( h_exp_log_bound.trans ?_ );
      · norm_num [ min_le_iff ];
      · grind

/-
For n >= 1, the intersection of A_{n+1} with [1, M_n] is a subset of A_n.
-/
def M (n : ℕ) : ℕ := 5^n * 2^(5^(n+1))

lemma lemma_A_succ_subset_A_n (n : ℕ) :
  {a ∈ A_n (n+1) | a ≤ M n} ⊆ A_n n := by
    rintro a ⟨ ⟨ m, hm₁, hm₂, rfl | rfl ⟩, ha ⟩ <;> simp_all +decide [ A_n ];
    · refine' ⟨ 5 * m, _, _, _ ⟩ <;> ring_nf at *;
      · grind;
      · unfold M at ha;
        -- Dividing both sides of the inequality $m * 5^n * 5 \leq 5^n * 2^{5^{n+1}}$ by $5^n$, we get $m * 5 \leq 2^{5^{n+1}}$.
        have h_div : m * 5 ≤ 2^(5^(n+1)) := by
          nlinarith [ pow_pos ( by decide : 0 < 5 ) n ];
        cases lt_or_eq_of_le h_div <;> simp_all +decide [ pow_succ, pow_mul ];
        · linarith;
        · have := congr_arg ( · % 5 ) ‹_›; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
          rw [ ← Nat.mod_add_div ( 5 ^ n ) 4 ] at this; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this;
      · norm_num;
    · refine' ⟨ 5 * m, _, _, _ ⟩ <;> ring_nf at *;
      · linarith;
      · unfold M at ha;
        norm_num [ pow_succ, pow_mul ] at *;
        nlinarith [ pow_pos ( show 0 < 5 by norm_num ) n, pow_pos ( show 0 < 2 by norm_num ) ( 5 ^ n ) ];
      · norm_num

/-
For n >= 1 and k > n, the intersection of A_k with [1, M_n] is a subset of A_n.
-/
lemma lemma_Ak_subset_An (n k : ℕ) (hk : k > n) :
  {a ∈ A_n k | a ≤ M n} ⊆ A_n n := by
    -- Assume k > n. We proceed by induction on k.
    induction' hk with k ih;
    · exact lemma_A_succ_subset_A_n n;
    · -- Since $M_n < M_k$, we have $\{a \in A_{k+1} \mid a \leq M_n\} \subseteq \{a \in A_{k+1} \mid a \leq M_k\}$.
      have h_subset_Mk : {a ∈ A_n (k + 1) | a ≤ M n} ⊆ {a ∈ A_n (k + 1) | a ≤ M k} := by
        refine' fun x hx => ⟨ hx.1, le_trans hx.2 _ ⟩;
        exact Nat.mul_le_mul ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Nat.succ_le_iff.mp ih ] ) ) ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Nat.succ_le_iff.mp ih, Nat.pow_le_pow_right ( by decide : 1 ≤ 5 ) ( by linarith [ Nat.succ_le_iff.mp ih ] : n + 1 ≤ k + 1 ) ] ) );
      -- By lemma_A_succ_subset_A_n, we have {a ∈ A_{k+1} | a ≤ M_k} ⊆ A_k.
      have h_subset_Ak : {a ∈ A_n (k + 1) | a ≤ M k} ⊆ A_n k := by
        exact lemma_A_succ_subset_A_n k
      grind

/-
If x <= M_n, then the number of elements of A up to x is at most the sum of sizes of A_k for k < n plus the number of elements of A_n up to x.
-/
lemma lemma_card_A_bound (x : ℕ) (n : ℕ) (hn : n ≥ 1) (hx : x ≤ M n) :
  Set.ncard {a ∈ A | a ≤ x} ≤ (∑ k ∈ Finset.Ico 1 n, Set.ncard (A_n k)) + Set.ncard {a ∈ A_n n | a ≤ x} := by
    -- By definition of $A$, we know that $A \cap [1, x] \subseteq (⋃_{1 ≤ k < n} A_k) \cup (A_n \cap [1, x])$.
    have h_subset : {a ∈ A | a ≤ x} ⊆ (⋃ k ∈ Finset.Ico 1 n, A_n k) ∪ {a ∈ A_n n | a ≤ x} := by
      intro a ha
      obtain ⟨haA, hax⟩ := ha
      by_cases h_case : ∃ k, 1 ≤ k ∧ k < n ∧ a ∈ A_n k;
      · aesop;
      · -- Since there's no k < n such that a is in A_k, it must be that a is in A_n.
        have h_an : a ∈ A_n n := by
          obtain ⟨k, hk₁, hk₂⟩ : ∃ k, 1 ≤ k ∧ a ∈ A_n k := by
            exact Exists.elim ( Set.mem_iUnion.mp haA ) fun k hk => ⟨ k, by aesop ⟩;
          by_cases hk : k < n;
          · grind;
          · have h_ak_subset_an : {a ∈ A_n k | a ≤ M n} ⊆ A_n n := by
              by_cases hkn : k = n;
              · aesop;
              · exact lemma_Ak_subset_An n k ( lt_of_le_of_ne ( le_of_not_gt hk ) ( Ne.symm hkn ) );
            exact h_ak_subset_an ⟨ hk₂, le_trans hax hx ⟩;
        exact Set.mem_union_right _ ⟨ h_an, hax ⟩;
    have h_card_union : (Set.ncard {a ∈ A | a ≤ x}) ≤ (Set.ncard (⋃ k ∈ Finset.Ico 1 n, A_n k)) + (Set.ncard {a ∈ A_n n | a ≤ x}) := by
      have h_card_union : (Set.ncard {a ∈ A | a ≤ x}) ≤ (Set.ncard ((⋃ k ∈ Finset.Ico 1 n, A_n k) ∪ {a ∈ A_n n | a ≤ x})) := by
        apply_rules [ Set.ncard_le_ncard ];
        refine Set.Finite.union ?_ ?_;
        · refine Set.Finite.biUnion ( Finset.finite_toSet _ ) fun k hk => ?_;
          exact Set.finite_iff_bddAbove.mpr ⟨ 5 ^ k * 2 ^ ( 5 ^ ( k + 1 ) ), fun x hx => by rcases hx with ⟨ m, hm₁, hm₂, rfl | rfl ⟩ <;> nlinarith [ pow_pos ( show 0 < 5 by decide ) k, pow_pos ( show 0 < 2 by decide ) ( 5 ^ ( k + 1 ) ) ] ⟩;
        · exact Set.finite_iff_bddAbove.mpr ⟨ x, fun a ha => ha.2 ⟩;
      exact h_card_union.trans ( Set.ncard_union_le _ _ ) |> le_trans <| by norm_num;
    refine le_trans h_card_union <| add_le_add_left ?_ _;
    exact Finset.set_ncard_biUnion_le (Finset.Ico 1 n) A_n

/-
For n >= 2, the sum of the sizes of A_k for 1 <= k < n is at most 4 * 2^(5^n).
-/
lemma lemma_sum_Ak_bound (n : ℕ) (hn : n ≥ 2) :
  ∑ k ∈ Finset.Ico 1 n, Set.ncard (A_n k) ≤ 4 * 2^(5^n) := by
    -- We know |A_k| ≤ 2 * 2^(5^(k+1)).
    have h_card_bound : ∀ k ∈ Finset.Ico 1 n, Set.ncard (A_n k) ≤ 2 * 2^(5^(k+1)) := by
      -- By definition of $A_k$, we know that $|A_k| \leq 2 * 2^{5^{k+1}}$.
      intros k hk
      have h_card_bound : Set.ncard (A_n k) ≤ 2 * (2^(5^(k+1)) - 1) := by
        -- By definition of $A_k$, we know that $|A_k| \leq 2 * (2^{5^{k+1}} - 1)$.
        have h_card_bound : Set.ncard (A_n k) ≤ Set.ncard {x | ∃ m, 1 ≤ m ∧ m < 2^(5^(k+1)) ∧ (x = 5^k * m ∨ x = 5^k * m + 1)} := by
          exact le_rfl;
        refine le_trans h_card_bound ?_;
        erw [ show { x : ℕ | ∃ m : ℕ, 1 ≤ m ∧ m < 2 ^ 5 ^ ( k + 1 ) ∧ ( x = 5 ^ k * m ∨ x = 5 ^ k * m + 1 ) } = ( Finset.image ( fun m : ℕ => 5 ^ k * m ) ( Finset.Ico 1 ( 2 ^ 5 ^ ( k + 1 ) ) ) ) ∪ ( Finset.image ( fun m : ℕ => 5 ^ k * m + 1 ) ( Finset.Ico 1 ( 2 ^ 5 ^ ( k + 1 ) ) ) ) by ext; aesop ] ; rw [ Set.ncard_eq_toFinset_card' ] ; norm_num [ Finset.card_image_of_injective, Function.Injective, mul_assoc, mul_left_comm, mul_comm ] ;
        exact le_trans ( Finset.card_union_le _ _ ) ( by rw [ two_mul ] ; exact add_le_add ( Finset.card_image_le.trans <| by norm_num ) <| Finset.card_image_le.trans <| by norm_num );
      exact h_card_bound.trans ( Nat.mul_le_mul_left _ ( Nat.sub_le _ _ ) );
    refine le_trans ( Finset.sum_le_sum h_card_bound ) ?_;
    induction hn <;> simp_all +decide [pow_succ, pow_mul];
    rename_i k hk ih; rw [ Finset.sum_Ico_succ_top ] ;
    · refine' le_trans ( add_le_add_left ( ih fun x hx₁ hx₂ => h_card_bound x hx₁ ( by linarith ) ) _ ) _;
      nlinarith only [ show 0 < ( 2 ^ 5 ^ k : ℕ ) by positivity, show ( 2 ^ 5 ^ k : ℕ ) ^ 2 > 0 by positivity, show ( 2 ^ 5 ^ k : ℕ ) ^ 3 > 0 by positivity, show ( 2 ^ 5 ^ k : ℕ ) ^ 4 > 0 by positivity, show ( 2 ^ 5 ^ k : ℕ ) ^ 5 > 0 by positivity, show ( 2 ^ 5 ^ k : ℕ ) > 1 by exact one_lt_pow₀ ( by decide ) ( by positivity ) ];
    · linarith

/-
The sequence M_n is strictly increasing.
-/
lemma lemma_M_increasing : StrictMono M := by
  refine' strictMono_nat_of_lt_succ _;
  intro n
  unfold M
  ring_nf
  nlinarith [ pow_pos ( by decide : 0 < 2 ) ( 5 ^ n * 5 ), pow_lt_pow_right₀ ( by decide : 1 < 2 ) ( show 5 ^ n * 5 < 5 ^ n * 25 by linarith [ pow_pos ( by decide : 0 < 5 ) n ] ), pow_pos ( by decide : 0 < 5 ) n ]

/-
There exists a constant C such that for large n and x > M_{n-1}, 4 * 2^(5^n) <= C * x / log x.
-/
lemma lemma_sum_term_bound :
  ∃ C > 0, ∃ n₀, ∀ n ≥ n₀, ∀ x, M (n-1) < x → 4 * 2^(5^n) ≤ C * x / Real.log x := by
    -- Let's choose the constant $C = 100$.
    use 100, by norm_num;
    -- Let $y = x / 2^{5^n}$. Since $x > M_{n-1} = 5^{n-1} * 2^{5^n}$, we have $y > 5^{n-1}$.
    have hy_bound : ∀ n ≥ 2, ∀ x : ℕ, M (n - 1) < x → 4 * (2 : ℝ) ^ (5 ^ n) * Real.log x ≤ 100 * x := by
      -- Since $x > M_{n-1} = 5^{n-1} * 2^{5^n}$, we have $x = y * 2^{5^n}$ with $y > 5^{n-1}$.
      intro n hn x hx
      obtain ⟨y, hy⟩ : ∃ y : ℝ, x = y * (2 : ℝ) ^ (5 ^ n) ∧ y > 5 ^ (n - 1) := by
        refine' ⟨ x / 2 ^ 5 ^ n, _, _ ⟩ <;> norm_num;
        rw [ lt_div_iff₀ ] <;> norm_cast <;> norm_num [ M ] at *;
        cases n <;> aesop;
      -- Substitute $x = y * 2^{5^n}$ into the inequality.
      have h_subst : 4 * (2 : ℝ) ^ (5 ^ n) * (Real.log y + 5 ^ n * Real.log 2) ≤ 100 * y * (2 : ℝ) ^ (5 ^ n) := by
        -- Since $y > 5^{n-1}$, we have $5^n = 5 * 5^{n-1} < 5y$.
        have h_5n_lt_5y : 5 ^ n < 5 * y := by
          cases n <;> norm_num [ pow_succ' ] at * ; linarith;
        -- Since $y > 5^{n-1}$, we have $\log y < y$.
        have h_log_y_lt_y : Real.log y < y := by
          linarith [ Real.log_le_sub_one_of_pos ( show 0 < y by linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 5 ) ( n - 1 ) ] ) ];
        -- Since $y > 5^{n-1}$, we have $5^n \log 2 < 5y \cdot 0.7 = 3.5y$.
        have h_5n_log2_lt_3_5y : 5 ^ n * Real.log 2 < 3.5 * y := by
          have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 5 ) ( show n ≥ 2 by linarith ) ];
        nlinarith [ show ( 0 : ℝ ) < 2 ^ 5 ^ n by positivity ];
      convert h_subst using 1 <;> push_cast [ hy ] <;> ring_nf;
      rw [ Real.log_mul ( by linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 5 ) ( n - 1 ) ] ) ( by positivity ), Real.log_pow ] ; ring_nf;
      norm_num ; ring;
    exact ⟨ 2, fun n hn x hx => by rw [ le_div_iff₀ ( Real.log_pos <| mod_cast by linarith [ show x > 1 from lt_of_le_of_lt ( Nat.one_le_iff_ne_zero.mpr <| by exact ne_of_gt <| show 0 < M ( n - 1 ) from by exact Nat.mul_pos ( pow_pos ( by decide ) _ ) ( pow_pos ( by decide ) _ ) ) hx ] ) ] ; simpa using hy_bound n hn x hx ⟩

/-
There exists a constant c > 0 and x_0 such that for all x >= x_0, the number of elements of A up to x is at most c * x / log x.
-/
theorem density_bound : ∃ c > 0, ∃ x₀, ∀ x ≥ x₀, Set.ncard {a ∈ A | a ≤ x} ≤ c * x / Real.log x := by
  -- Let c_1 be the constant from prop_upper_linear.
  obtain ⟨c1, hc1⟩ : ∃ c1 > 0, ∀ x ≥ 2, ∀ n ≥ 1, Set.ncard {a ∈ A_n n | a ≤ x} ≤ c1 * x / Real.log x := by
    convert prop_upper_linear;
  -- Let C_2, n_0 be the constants from lemma_sum_term_bound.
  obtain ⟨C2, hC2⟩ : ∃ C2 > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x, M (n-1) < x → 4 * 2^(5^n) ≤ C2 * x / Real.log x := by
    exact lemma_sum_term_bound;
  -- Let c = c1 + C2.
  use c1 + C2, by linarith [hc1.left, hC2.left];
  -- Let x₀ be large enough such that for all x ≥ x₀, M(n-1) < x ≤ M(n) for some n ≥ n₀.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, ∀ x ≥ x₀, ∃ n : ℕ, n ≥ hC2.right.choose + 1 ∧ M (n - 1) < x ∧ x ≤ M n := by
    -- Since $M$ is strictly increasing, there exists $x₀$ such that for all $x ≥ x₀$, there exists $n$ with $M (n - 1) < x ≤ M n$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, ∀ x ≥ x₀, ∃ n : ℕ, M (n - 1) < x ∧ x ≤ M n := by
      use M 1 + 1;
      intro x hx
      obtain ⟨n, hn⟩ : ∃ n : ℕ, M n ≥ x := by
        have h_unbounded : Filter.Tendsto M Filter.atTop Filter.atTop := by
          exact strictMono_nat_of_lt_succ ( fun n => by exact mul_lt_mul'' ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) ) ( pow_lt_pow_right₀ ( by decide ) ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) ) ) ( by positivity ) ( by positivity ) ) |> StrictMono.tendsto_atTop;
        exact ( h_unbounded.eventually_ge_atTop x ) |> fun h => h.exists;
      induction' n with n ih;
      · exact absurd hn ( by linarith! [ show M 0 < M 1 from lemma_M_increasing ( by decide ) ] );
      · grind;
    use M ( hC2.2.choose + 1 ) + x₀ + 1;
    intro x hx;
    obtain ⟨ n, hn₁, hn₂ ⟩ := hx₀ x ( by linarith [ show M ( hC2.2.choose + 1 ) ≥ 0 by exact Nat.zero_le _ ] );
    refine' ⟨ n, _, hn₁, hn₂ ⟩;
    contrapose! hx;
    exact lt_of_le_of_lt hn₂ ( Nat.lt_succ_of_le ( Nat.le_trans ( show M n ≤ M ( hC2.2.choose + 1 ) from by exact monotone_nat_of_le_succ ( fun n => by exact Nat.mul_le_mul ( pow_le_pow_right₀ ( by decide ) ( Nat.le_succ _ ) ) ( pow_le_pow_right₀ ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) ) ) ( by linarith ) ) ( Nat.le_add_right _ _ ) ) );
  use x₀ + 2;
  intro x hx; obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := hx₀ x ( by linarith ) ; have := hc1.2 x ( by linarith ) n ( by linarith ) ; have := hC2.2.choose_spec n ( by linarith ) x hn₂; simp_all +decide [ add_mul, div_eq_mul_inv ] ;
  -- By lemma_card_A_bound, we have |A \cap [1, x]| <= sum_{k=1}^{n-1} |A_k| + |A_n \cap [1, x]|.
  have h_card_bound : Set.ncard {a ∈ A | a ≤ x} ≤ (∑ k ∈ Finset.Ico 1 n, Set.ncard (A_n k)) + Set.ncard {a ∈ A_n n | a ≤ x} := by
    convert lemma_card_A_bound x n ( by linarith ) hn₃ using 1;
  -- By lemma_sum_Ak_bound, we have sum_{k=1}^{n-1} |A_k| <= 4 * 2^(5^n).
  have h_sum_Ak_bound : (∑ k ∈ Finset.Ico 1 n, Set.ncard (A_n k)) ≤ 4 * 2^(5^n) := by
    by_cases hn : n ≥ 2;
    · exact lemma_sum_Ak_bound n hn;
    · interval_cases n <;> norm_num at *;
  exact le_trans ( Nat.cast_le.mpr h_card_bound ) ( by push_cast; linarith [ ( by norm_cast : ( ∑ k ∈ Finset.Ico 1 n, Set.ncard ( A_n k ) : ℝ ) ≤ 4 * 2 ^ 5 ^ n ) ] )

/-
There exists a set A such that for large x, the number of elements of A up to x is O(x/log x), and every large integer is of the form 2^k + a with a in A.
-/
theorem thm_main : ∃ A : Set ℕ,
  (∃ c > 0, ∃ x₀, ∀ x ≥ x₀, Set.ncard {a ∈ A | a ≤ x} ≤ c * x / Real.log x) ∧
  (∃ N₀, ∀ N ≥ N₀, ∃ k a, k ≥ 1 ∧ a ∈ A ∧ N = 2^k + a) := by
    obtain ⟨ c, hc, x₀, hx₀ ⟩ := density_bound;
    refine' ⟨ A, ⟨ c, hc, x₀, hx₀ ⟩, 32, _ ⟩;
    exact fun N a => thm_covering_explicit N a


#print axioms thm_main
-- 'thm_main' depends on axioms: [propext, Classical.choice, Quot.sound]

end
end Erdos221
