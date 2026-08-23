/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1198.
https://www.erdosproblems.com/forum/thread/1198

Informal authors:
- Gregory L. Smith

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1198.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 1198

Gregory L. Smith proved that there is a two-colouring of the positive
integers which separates finite products from sums of two ordered finite
products.  Pairing consecutive members of a hypothetical solution turns
every finite product into a nontrivial expression, so Smith's colouring
disproves the problem exactly as stated.

The mathematical reconstruction is in `tex/1198.tex`.
-/

namespace Erdos1198

open Filter
open scoped BigOperators

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
  Ultrafilter.add Ultrafilter.addSemigroup

/-- Ordered sums of two nonempty finite products from a stream. -/
def SP2 (x : Stream' ℕ+) : Set ℕ+ :=
  {n | ∃ F G : Finset ℕ,
    F.Nonempty ∧ G.Nonempty ∧
    (∀ i ∈ F, ∀ j ∈ G, i < j) ∧
    n = (∏ i ∈ F, x.get i) + ∏ j ∈ G, x.get j}

/-- A finite family of index blocks is an admissible Problem 1198 expression. -/
def Admissible (blocks : Finset (Finset ℕ)) : Prop :=
  blocks.Nonempty ∧
    (∀ S ∈ blocks, S.Nonempty) ∧
    (↑blocks : Set (Finset ℕ)).PairwiseDisjoint id

/-- The only excluded expressions are one-block, one-index expressions. -/
def Nontrivial (blocks : Finset (Finset ℕ)) : Prop :=
  ¬ ∃ i : ℕ, blocks = {{i}}

/-- The sum of products represented by a finite family of index blocks. -/
def expressionValue (a : ℕ → ℕ) (blocks : Finset (Finset ℕ)) : ℕ :=
  ∑ S ∈ blocks, ∏ i ∈ S, a i

/-- The exact positive assertion asked in Erdős Problem 1198. -/
def Erdos1198Statement : Prop :=
  ∀ c : ℕ → Fin 2,
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      ∃ color : Fin 2,
        ∀ blocks : Finset (Finset ℕ),
          Admissible blocks → Nontrivial blocks →
            c (expressionValue a blocks) = color

private def hi (n : ℕ+) : ℕ := Nat.log 2 n
private def lo (n : ℕ+) : ℕ := padicValNat 2 n

private abbrev ValBucket := Fin 3

private def valBucket (n : ℕ+) : ValBucket :=
  if lo n = 0 then 0 else if lo n = 1 then 1 else 2

private def IsTwoPower (n : ℕ+) : Prop := (n : ℕ) = 2 ^ hi n

private def LowSide (n : ℕ+) : Prop :=
  (n : ℕ) < 2 ^ hi n + 2 ^ (hi n - lo n)

private def HighSide (n : ℕ+) : Prop :=
  2 ^ (hi n + 1) - 2 ^ (hi n - lo n) < (n : ℕ)

private abbrev SmithColor := ValBucket × Bool × Fin 2 × Bool × Bool

/-- A finite refinement of the seven dyadic cells in Smith's proof. -/
private noncomputable def smithColor (n : ℕ+) : SmithColor :=
  by
    classical
    exact
      (valBucket n, if IsTwoPower n then true else false,
        ⟨hi n % 2, Nat.mod_lt _ (by omega)⟩,
        if LowSide n then true else false, if HighSide n then true else false)

private lemma valBucket_eq_zero_iff (n : ℕ+) : valBucket n = 0 ↔ lo n = 0 := by
  unfold valBucket
  by_cases h0 : lo n = 0
  · simp [h0]
  · by_cases h1 : lo n = 1 <;> simp [h0, h1]

private lemma valBucket_eq_one_iff (n : ℕ+) : valBucket n = 1 ↔ lo n = 1 := by
  unfold valBucket
  by_cases h0 : lo n = 0
  · simp [h0]
  · by_cases h1 : lo n = 1 <;> simp [h0, h1]

private lemma valBucket_eq_two_iff (n : ℕ+) : valBucket n = 2 ↔ 2 ≤ lo n := by
  unfold valBucket
  by_cases h0 : lo n = 0
  · simp [h0]
  · by_cases h1 : lo n = 1
    · simp [h1]
    · simp [h0, h1]
      omega

private lemma smithColor_val_eq {m n : ℕ+} (h : smithColor m = smithColor n) :
    valBucket m = valBucket n := by
  exact congrArg Prod.fst h

private lemma smithColor_power_eq {m n : ℕ+} (h : smithColor m = smithColor n) :
    IsTwoPower m ↔ IsTwoPower n := by
  have h' := congrArg (fun z : SmithColor => z.2.1) h
  simpa [smithColor] using h'

private lemma smithColor_hi_mod_eq {m n : ℕ+} (h : smithColor m = smithColor n) :
    hi m % 2 = hi n % 2 := by
  have h' := congrArg (fun z : SmithColor => z.2.2.1) h
  exact congrArg (fun z : Fin 2 => z.val) h'

private lemma smithColor_low_eq {m n : ℕ+} (h : smithColor m = smithColor n) :
    LowSide m ↔ LowSide n := by
  have h' := congrArg (fun z : SmithColor => z.2.2.2.1) h
  simpa [smithColor] using h'

private lemma smithColor_high_eq {m n : ℕ+} (h : smithColor m = smithColor n) :
    HighSide m ↔ HighSide n := by
  have h' := congrArg (fun z : SmithColor => z.2.2.2.2) h
  simpa [smithColor] using h'

private lemma hi_lower (n : ℕ+) : 2 ^ hi n ≤ (n : ℕ) := by
  exact Nat.pow_log_le_self 2 n.ne_zero

private lemma hi_upper (n : ℕ+) : (n : ℕ) < 2 ^ (hi n + 1) := by
  exact Nat.lt_pow_of_log_lt (by omega) (Nat.lt_succ_self (hi n))

private lemma lo_le_hi (n : ℕ+) : lo n ≤ hi n := by
  exact padicValNat_le_nat_log n

private lemma lo_mul (m n : ℕ+) : lo (m * n) = lo m + lo n := by
  exact padicValNat.mul m.ne_zero n.ne_zero

private lemma hi_mul_cases (m n : ℕ+) :
    hi (m * n) = hi m + hi n ∨ hi (m * n) = hi m + hi n + 1 := by
  have hlo : 2 ^ (hi m + hi n) ≤ ((m * n : ℕ+) : ℕ) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul (hi_lower m) (hi_lower n)
  have hhi : ((m * n : ℕ+) : ℕ) < 2 ^ (hi m + hi n + 2) := by
    rw [show hi m + hi n + 2 = (hi m + 1) + (hi n + 1) by omega, Nat.pow_add]
    calc
      (m : ℕ) * n < 2 ^ (hi m + 1) * n :=
        Nat.mul_lt_mul_of_pos_right (hi_upper m) n.2
      _ < 2 ^ (hi m + 1) * 2 ^ (hi n + 1) :=
        Nat.mul_lt_mul_of_pos_left (hi_upper n) (Nat.two_pow_pos _)
  have hlowlog : hi m + hi n ≤ hi (m * n) :=
    Nat.le_log_of_pow_le (by omega) hlo
  have hloghi : hi (m * n) < hi m + hi n + 2 :=
    Nat.log_lt_of_lt_pow (Nat.mul_ne_zero m.ne_zero n.ne_zero) hhi
  omega

private lemma lo_add_of_lt (m n : ℕ+) (h : lo m < lo n) : lo (m + n) = lo m := by
  have hqval : padicValRat 2 (m : ℚ) < padicValRat 2 (n : ℚ) := by
    rw [← padicValRat_of_nat, ← padicValRat_of_nat]
    exact_mod_cast h
  have hq := padicValRat.add_eq_of_lt (p := 2)
    (q := (m : ℚ)) (r := (n : ℚ)) (by positivity) (by positivity) (by positivity) hqval
  have hq' : padicValRat 2 (((m + n : ℕ+) : ℕ) : ℚ) =
      padicValRat 2 ((m : ℕ) : ℚ) := by
    convert hq using 1
    all_goals norm_num
  rw [← padicValRat_of_nat, ← padicValRat_of_nat] at hq'
  exact_mod_cast hq'

private lemma lo_add_eq_of_ne (m n : ℕ+) (h : lo m ≠ lo n) :
    lo (m + n) = min (lo m) (lo n) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [lo_add_of_lt m n hlt, min_eq_left hlt.le]
  · rw [add_comm, lo_add_of_lt n m hgt, min_eq_right hgt.le]

private lemma twoPower_add_lo_eq (m n : ℕ+) (hpow : IsTwoPower (m + n)) :
    lo m = lo n := by
  by_contra hne
  have hlo := lo_add_eq_of_ne m n hne
  have hpowlo : lo (m + n) = hi (m + n) := by
    rw [lo, hpow, padicValNat.prime_pow]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmn : 2 ^ lo m ≤ (m : ℕ) :=
      Nat.le_of_dvd m.2 pow_padicValNat_dvd
    have hsum : ((m + n : ℕ+) : ℕ) = 2 ^ lo m := by
      rw [hpow, ← hpowlo, hlo, min_eq_left hlt.le]
    have hlt_sum : (m : ℕ) < ((m + n : ℕ+) : ℕ) := by
      change (m : ℕ) < (m : ℕ) + (n : ℕ)
      exact Nat.lt_add_of_pos_right n.2
    rw [hsum] at hlt_sum
    exact (not_lt_of_ge hmn) hlt_sum
  · have hnn : 2 ^ lo n ≤ (n : ℕ) :=
      Nat.le_of_dvd n.2 pow_padicValNat_dvd
    have hsum : ((m + n : ℕ+) : ℕ) = 2 ^ lo n := by
      rw [hpow, ← hpowlo, hlo, min_eq_right hgt.le]
    have hlt_sum : (n : ℕ) < ((m + n : ℕ+) : ℕ) := by
      change (n : ℕ) < (m : ℕ) + (n : ℕ)
      rw [add_comm]
      exact Nat.lt_add_of_pos_right m.2
    rw [hsum] at hlt_sum
    exact (not_lt_of_ge hnn) hlt_sum

private lemma dvd_step_le {d a b : ℕ} (_hd : 0 < d) (hda : d ∣ a) (hdb : d ∣ b)
    (hab : a < b) : a + d ≤ b := by
  obtain ⟨x, rfl⟩ := hda
  obtain ⟨y, hy⟩ := hdb
  rw [hy] at hab ⊢
  have hxy : x < y := by
    exact Nat.lt_of_mul_lt_mul_left hab
  calc
    d * x + d = d * (x + 1) := by rw [mul_add, mul_one]
    _ ≤ d * y := Nat.mul_le_mul_left d (Nat.succ_le_iff.mpr hxy)

private lemma hi_lo_add_of_hi_lt_lo (m n : ℕ+) (h : hi m < lo n) :
    hi (m + n) = hi n ∧ lo (m + n) = lo m := by
  have hlomn : lo m < lo n := (lo_le_hi m).trans_lt h
  have hm_lt : (m : ℕ) < 2 ^ lo n := by
    calc
      (m : ℕ) < 2 ^ (hi m + 1) := hi_upper m
      _ ≤ 2 ^ lo n := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : (n : ℕ) + 2 ^ lo n ≤ 2 ^ (hi n + 1) := by
    apply dvd_step_le (Nat.two_pow_pos _)
    · exact pow_padicValNat_dvd
    · exact pow_dvd_pow 2 ((lo_le_hi n).trans (Nat.le_succ _))
    · exact hi_upper n
  have hadd_upper : ((m + n : ℕ+) : ℕ) < 2 ^ (hi n + 1) := by
    change (m : ℕ) + (n : ℕ) < 2 ^ (hi n + 1)
    omega
  have hadd_lower : 2 ^ hi n ≤ ((m + n : ℕ+) : ℕ) := by
    change 2 ^ hi n ≤ (m : ℕ) + (n : ℕ)
    exact (hi_lower n).trans (Nat.le_add_left _ _)
  refine ⟨Nat.log_eq_of_pow_le_of_lt_pow hadd_lower hadd_upper, lo_add_of_lt m n hlomn⟩

private lemma nonpower_lower (n : ℕ+) (hn : ¬IsTwoPower n) :
    2 ^ hi n + 2 ^ lo n ≤ (n : ℕ) := by
  apply dvd_step_le (Nat.two_pow_pos _)
  · exact pow_dvd_pow 2 (lo_le_hi n)
  · exact pow_padicValNat_dvd
  · exact lt_of_le_of_ne (hi_lower n) (Ne.symm hn)

private lemma nonpower_upper (n : ℕ+) (_hn : ¬IsTwoPower n) :
    (n : ℕ) ≤ 2 ^ (hi n + 1) - 2 ^ lo n := by
  have hstep : (n : ℕ) + 2 ^ lo n ≤ 2 ^ (hi n + 1) := by
    apply dvd_step_le (Nat.two_pow_pos _)
    · exact pow_padicValNat_dvd
    · exact pow_dvd_pow 2 ((lo_le_hi n).trans (Nat.le_succ _))
    · exact hi_upper n
  omega

private lemma lo_finset_prod (f : ℕ → ℕ+) (s : Finset ℕ) :
    lo (∏ i ∈ s, f i) = ∑ i ∈ s, lo (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lo]
  | @insert i s his ih =>
      simp only [Finset.prod_insert his, Finset.sum_insert his]
      rw [lo_mul, ih]

private lemma fp_singleton (x : Stream' ℕ+) (i : ℕ) :
    x.get i ∈ Hindman.FP x :=
  Hindman.FP.singleton x i

private lemma fp_pair (x : Stream' ℕ+) {i j : ℕ} (hij : i < j) :
    x.get i * x.get j ∈ Hindman.FP x :=
  Hindman.FP.mul_two x i j hij

private lemma sp2_singletons (x : Stream' ℕ+) {i j : ℕ} (hij : i < j) :
    x.get i + x.get j ∈ SP2 x := by
  refine ⟨{i}, {j}, by simp, by simp, ?_, by simp⟩
  intro u hu v hv
  simp only [Finset.mem_singleton] at hu hv
  subst u
  subst v
  exact hij

private lemma sp2_singleton_product (x : Stream' ℕ+) {i : ℕ} {G : Finset ℕ}
    (hG : G.Nonempty) (hord : ∀ j ∈ G, i < j) :
    x.get i + ∏ j ∈ G, x.get j ∈ SP2 x := by
  refine ⟨{i}, G, by simp, hG, ?_, by simp⟩
  intro u hu j hj
  simp only [Finset.mem_singleton] at hu
  subst u
  exact hord j hj

private lemma lo_zero_mod_two (n : ℕ+) (h : lo n = 0) : (n : ℕ) % 2 = 1 := by
  have hndvd : ¬2 ∣ (n : ℕ) := by
    simpa [lo, padicValNat.eq_zero_iff] using h
  exact Nat.two_dvd_ne_zero.mp hndvd

private lemma no_SP2_valBucket_zero (x : Stream' ℕ+)
    (h : ∀ n ∈ SP2 x, valBucket n = 0) : False := by
  have h01 := lo_zero_mod_two (x.get 0 + x.get 1)
    (valBucket_eq_zero_iff _ |>.mp (h _ (sp2_singletons x (by omega : 0 < 1))))
  have h02 := lo_zero_mod_two (x.get 0 + x.get 2)
    (valBucket_eq_zero_iff _ |>.mp (h _ (sp2_singletons x (by omega : 0 < 2))))
  have h12 := lo_zero_mod_two (x.get 1 + x.get 2)
    (valBucket_eq_zero_iff _ |>.mp (h _ (sp2_singletons x (by omega : 1 < 2))))
  change (((x.get 0 : ℕ) + (x.get 1 : ℕ)) % 2 = 1) at h01
  change (((x.get 0 : ℕ) + (x.get 2 : ℕ)) % 2 = 1) at h02
  change (((x.get 1 : ℕ) + (x.get 2 : ℕ)) % 2 = 1) at h12
  omega

private lemma no_FP_valBucket_one (y : Stream' ℕ+)
    (h : ∀ n ∈ Hindman.FP y, valBucket n = 1) : False := by
  have h0 := valBucket_eq_one_iff _ |>.mp (h _ (fp_singleton y 0))
  have h1 := valBucket_eq_one_iff _ |>.mp (h _ (fp_singleton y 1))
  have h01 := valBucket_eq_one_iff _ |>.mp (h _ (fp_pair y (by omega : 0 < 1)))
  rw [lo_mul, h0, h1] at h01
  omega

private lemma even_terms_of_SP2_valBucket_two (x : Stream' ℕ+)
    (h : ∀ n ∈ SP2 x, valBucket n = 2) : ∀ i, 2 ∣ (x.get i : ℕ) := by
  intro i
  let j := i + 1
  let k := i + 2
  have hlo (r s : ℕ) (hrs : r < s) : 2 ≤ lo (x.get r + x.get s) :=
    valBucket_eq_two_iff _ |>.mp (h _ (sp2_singletons x hrs))
  have hdvd (r s : ℕ) (hrs : r < s) : 4 ∣ (x.get r : ℕ) + x.get s := by
    have hp : 2 ^ 2 ∣ ((x.get r + x.get s : ℕ+) : ℕ) :=
      (padicValNat_dvd_iff_le (p := 2) (a := ((x.get r + x.get s : ℕ+) : ℕ))
        (n := 2) (x.get r + x.get s).ne_zero).2 (hlo r s hrs)
    norm_num at hp ⊢
    exact hp
  have hij := Nat.dvd_iff_mod_eq_zero.mp (hdvd i j (by simp [j]))
  have hik := Nat.dvd_iff_mod_eq_zero.mp (hdvd i k (by simp [k]))
  have hjk := Nat.dvd_iff_mod_eq_zero.mp (hdvd j k (by simp [j, k]))
  change (((x.get i : ℕ) + (x.get j : ℕ)) % 4 = 0) at hij
  change (((x.get i : ℕ) + (x.get k : ℕ)) % 4 = 0) at hik
  change (((x.get j : ℕ) + (x.get k : ℕ)) % 4 = 0) at hjk
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private lemma no_SP2_twoPower_of_valBucket_two (x : Stream' ℕ+)
    (hval : ∀ n ∈ SP2 x, valBucket n = 2)
    (hpow : ∀ n ∈ SP2 x, IsTwoPower n) : False := by
  have hp01 := hpow _ (sp2_singletons x (by omega : 0 < 1))
  have hp02 := hpow _ (sp2_singletons x (by omega : 0 < 2))
  have hm : x.get 0 + x.get 1 * x.get 2 ∈ SP2 x := by
    simpa using sp2_singleton_product x (i := 0) (G := {1, 2}) (by simp) (by simp)
  have hp0_12 := hpow _ hm
  have h01 := twoPower_add_lo_eq (x.get 0) (x.get 1) hp01
  have h02 := twoPower_add_lo_eq (x.get 0) (x.get 2) hp02
  have h0_12 := twoPower_add_lo_eq (x.get 0) (x.get 1 * x.get 2) hp0_12
  rw [lo_mul, ← h01, ← h02] at h0_12
  have heven := even_terms_of_SP2_valBucket_two x hval 0
  have hlo0 : 1 ≤ lo (x.get 0) :=
    one_le_padicValNat_of_dvd (x.get 0).ne_zero heven
  omega

private lemma no_FP_even_low (y : Stream' ℕ+)
    (hval : ∀ n ∈ Hindman.FP y, 2 ≤ lo n)
    (hpow : ∀ n ∈ Hindman.FP y, ¬IsTwoPower n)
    (hpar : ∀ n ∈ Hindman.FP y, hi n % 2 = 0)
    (hlow : ∀ n ∈ Hindman.FP y, LowSide n) : False := by
  classical
  let u := y.get 0
  let G := Finset.Icc 1 (hi u + 1)
  let v : ℕ+ := ∏ i ∈ G, y.get i
  have hG : G.Nonempty := by
    refine ⟨1, ?_⟩
    simp [G]
  have huFP : u ∈ Hindman.FP y := by simpa [u] using fp_singleton y 0
  have hvFP : v ∈ Hindman.FP y := by
    simpa [v] using Hindman.FP.finsetProd y G hG
  have hzero : 0 ∉ G := by simp [G]
  have huvFP : u * v ∈ Hindman.FP y := by
    have hm := Hindman.FP.finsetProd y (insert 0 G) (by simp)
    simpa [u, v, Finset.prod_insert hzero] using hm
  have hlo_v : hi u < lo v := by
    change hi u < lo (∏ i ∈ G, y.get i)
    rw [lo_finset_prod]
    calc
      hi u < 2 * (hi u + 1) := by omega
      _ = ∑ i ∈ G, 2 := by simp [G, Nat.card_Icc]; omega
      _ ≤ ∑ i ∈ G, lo (y.get i) := by
        exact Finset.sum_le_sum fun i hiG => hval _ (fp_singleton y i)
  have hhi_uv : hi (u * v) = hi u + hi v := by
    rcases hi_mul_cases u v with h | h
    · exact h
    · have hupar := hpar u huFP
      have hvpar := hpar v hvFP
      have huvpar := hpar (u * v) huvFP
      omega
  have hloe : hi (u * v) - lo (u * v) ≤ hi v + lo u := by
    rw [hhi_uv, lo_mul]
    omega
  have hpowle : 2 ^ (hi (u * v) - lo (u * v)) ≤ 2 ^ (hi v + lo u) :=
    Nat.pow_le_pow_right (by omega) hloe
  have hmain : 2 ^ hi (u * v) + 2 ^ (hi v + lo u) ≤ ((u * v : ℕ+) : ℕ) := by
    rw [hhi_uv, Nat.pow_add, Nat.pow_add]
    calc
      2 ^ hi u * 2 ^ hi v + 2 ^ hi v * 2 ^ lo u =
          (2 ^ hi u + 2 ^ lo u) * 2 ^ hi v := by ring
      _ ≤ (u : ℕ) * (v : ℕ) :=
        Nat.mul_le_mul (nonpower_lower u (hpow u huFP)) (hi_lower v)
  have hbad := hlow (u * v) huvFP
  unfold LowSide at hbad
  omega

private lemma no_FP_odd_high (y : Stream' ℕ+)
    (hval : ∀ n ∈ Hindman.FP y, 2 ≤ lo n)
    (hpow : ∀ n ∈ Hindman.FP y, ¬IsTwoPower n)
    (hpar : ∀ n ∈ Hindman.FP y, hi n % 2 = 1)
    (hhigh : ∀ n ∈ Hindman.FP y, HighSide n) : False := by
  classical
  let u := y.get 0
  let G := Finset.Icc 1 (hi u + 1)
  let v : ℕ+ := ∏ i ∈ G, y.get i
  have hG : G.Nonempty := by
    refine ⟨1, ?_⟩
    simp [G]
  have huFP : u ∈ Hindman.FP y := by simpa [u] using fp_singleton y 0
  have hvFP : v ∈ Hindman.FP y := by
    simpa [v] using Hindman.FP.finsetProd y G hG
  have hzero : 0 ∉ G := by simp [G]
  have huvFP : u * v ∈ Hindman.FP y := by
    have hm := Hindman.FP.finsetProd y (insert 0 G) (by simp)
    simpa [u, v, Finset.prod_insert hzero] using hm
  have hlo_v : hi u < lo v := by
    change hi u < lo (∏ i ∈ G, y.get i)
    rw [lo_finset_prod]
    calc
      hi u < 2 * (hi u + 1) := by omega
      _ = ∑ i ∈ G, 2 := by simp [G, Nat.card_Icc]; omega
      _ ≤ ∑ i ∈ G, lo (y.get i) := by
        exact Finset.sum_le_sum fun i hiG => hval _ (fp_singleton y i)
  have hhi_uv : hi (u * v) = hi u + hi v + 1 := by
    rcases hi_mul_cases u v with h | h
    · have hupar := hpar u huFP
      have hvpar := hpar v hvFP
      have huvpar := hpar (u * v) huvFP
      omega
    · exact h
  have hloe : hi (u * v) - lo (u * v) ≤ hi v + lo u + 1 := by
    rw [hhi_uv, lo_mul]
    omega
  have hpowle : 2 ^ (hi (u * v) - lo (u * v)) ≤ 2 ^ (hi v + lo u + 1) :=
    Nat.pow_le_pow_right (by omega) hloe
  have hmain : ((u * v : ℕ+) : ℕ) + 2 ^ (hi v + lo u + 1) <
      2 ^ (hi (u * v) + 1) := by
    change (u : ℕ) * (v : ℕ) + 2 ^ (hi v + lo u + 1) <
      2 ^ (hi (u * v) + 1)
    have hmul : (u : ℕ) * (v : ℕ) <
        (2 ^ (hi u + 1) - 2 ^ lo u) * 2 ^ (hi v + 1) := by
      calc
        (u : ℕ) * (v : ℕ) < (u : ℕ) * 2 ^ (hi v + 1) :=
          Nat.mul_lt_mul_of_pos_left (hi_upper v) u.2
        _ ≤ (2 ^ (hi u + 1) - 2 ^ lo u) * 2 ^ (hi v + 1) :=
          Nat.mul_le_mul_right _ (nonpower_upper u (hpow u huFP))
    rw [Nat.sub_mul] at hmul
    rw [hhi_uv]
    have hpowA : 2 ^ (hi u + 1) * 2 ^ (hi v + 1) =
        2 ^ (hi u + hi v + 2) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hpowB : 2 ^ lo u * 2 ^ (hi v + 1) = 2 ^ (hi v + lo u + 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpowA, hpowB] at hmul
    rw [show hi u + hi v + 1 + 1 = hi u + hi v + 2 by omega]
    exact Nat.add_lt_of_lt_sub hmul
  have hbad := hhigh (u * v) huvFP
  unfold HighSide at hbad
  omega

private lemma lower_crossing (D : ℕ) (z : ℕ → ℕ+)
    (hlarge : ∀ j, D + 1 ≤ hi (z j))
    (hfar : ∀ j, 2 ^ hi (z j) + 2 ^ (hi (z j) - D - 1) ≤ (z j : ℕ)) :
    ∃ k, 0 < k ∧
      hi (∏ j ∈ Finset.range k, z j) =
        (∑ j ∈ Finset.range k, hi (z j)) + 1 := by
  classical
  let q := 2 ^ (D + 1)
  let P : ℕ → ℕ+ := fun k => ∏ j ∈ Finset.range k, z j
  let S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, hi (z j)
  have hqpos : 0 < q := by simp [q]
  have hfactor (j : ℕ) :
      (q + 1) * 2 ^ hi (z j) ≤ q * (z j : ℕ) := by
    have hjlarge := hlarge j
    have hexp : D + 1 + (hi (z j) - D - 1) = hi (z j) := by
      omega
    have hpow : q * 2 ^ (hi (z j) - D - 1) = 2 ^ hi (z j) := by
      change 2 ^ (D + 1) * 2 ^ (hi (z j) - D - 1) = 2 ^ hi (z j)
      rw [← Nat.pow_add, hexp]
    calc
      (q + 1) * 2 ^ hi (z j) =
          q * 2 ^ hi (z j) + q * 2 ^ (hi (z j) - D - 1) := by
            rw [hpow]
            ring
      _ = q * (2 ^ hi (z j) + 2 ^ (hi (z j) - D - 1)) := by ring
      _ ≤ q * (z j : ℕ) := Nat.mul_le_mul_left q (hfar j)
  have hprod (k : ℕ) :
      (q + 1) ^ k * 2 ^ S k ≤ q ^ k * (P k : ℕ) := by
    have hp := Finset.prod_le_prod (s := Finset.range k)
      (f := fun j => (q + 1) * 2 ^ hi (z j))
      (g := fun j => q * (z j : ℕ)) (fun _ _ => by omega) (fun j _ => hfactor j)
    simpa [P, S, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] using hp
  have hqone : 1 ≤ q := hqpos
  have hterm : q * q ^ (q - 1) = q ^ q := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hbern : 2 * q ^ q ≤ (q + 1) ^ q := by
    have hb := pow_add_mul_le_add_pow (R := ℕ) (a := q) (b := 1)
      (by omega) (by omega) q
    simpa [hterm, two_mul] using hb
  have hcross : 2 ^ (S q + 1) ≤ (P q : ℕ) := by
    have hp := hprod q
    have hmul : q ^ q * 2 ^ (S q + 1) ≤ q ^ q * (P q : ℕ) := by
      calc
        q ^ q * 2 ^ (S q + 1) = (2 * q ^ q) * 2 ^ S q := by
          rw [pow_succ]
          ring
        _ ≤ (q + 1) ^ q * 2 ^ S q := Nat.mul_le_mul_right _ hbern
        _ ≤ q ^ q * (P q : ℕ) := hp
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos hqpos _)
  let Q : ℕ → Prop := fun k => 2 ^ (S k + 1) ≤ (P k : ℕ)
  have hQ : ∃ k, Q k := ⟨q, hcross⟩
  let k := Nat.find hQ
  have hkQ : Q k := Nat.find_spec hQ
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    have hk0Q : Q 0 := hk0 ▸ hkQ
    simp [Q, P, S] at hk0Q
  let t := k - 1
  have htk : t < k := by simp [t, hkpos]
  have htQ : ¬Q t := Nat.find_min hQ htk
  have hkt : k = t + 1 := by simp [t, Nat.sub_add_cancel hkpos]
  have hprev : (P t : ℕ) < 2 ^ (S t + 1) := by
    simpa [Q] using Nat.lt_of_not_ge htQ
  have hPk : P k = P t * z t := by
    simp [P, hkt, Finset.prod_range_succ]
  have hSk : S k = S t + hi (z t) := by
    simp [S, hkt, Finset.sum_range_succ]
  have hupp : (P k : ℕ) < 2 ^ (S k + 2) := by
    rw [hPk, hSk]
    change (P t : ℕ) * (z t : ℕ) < 2 ^ (S t + hi (z t) + 2)
    calc
      (P t : ℕ) * (z t : ℕ) < 2 ^ (S t + 1) * (z t : ℕ) :=
        Nat.mul_lt_mul_of_pos_right hprev (z t).2
      _ < 2 ^ (S t + 1) * 2 ^ (hi (z t) + 1) :=
        Nat.mul_lt_mul_of_pos_left (hi_upper (z t)) (Nat.two_pow_pos _)
      _ = 2 ^ (S t + hi (z t) + 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  refine ⟨k, hkpos, ?_⟩
  apply Nat.log_eq_of_pow_le_of_lt_pow hkQ
  exact hupp

private lemma no_SP2_even_not_low (x : Stream' ℕ+)
    (hval : ∀ n ∈ SP2 x, valBucket n = 2)
    (hpar : ∀ n ∈ SP2 x, hi n % 2 = 0)
    (hlow : ∀ n ∈ SP2 x, ¬LowSide n) : False := by
  classical
  let z0 := x.get 0
  let D := lo z0
  let B := hi z0 + D + 2
  let G : ℕ → Finset ℕ := fun j => Finset.Ico (1 + j * B) (1 + (j + 1) * B)
  let z : ℕ → ℕ+ := fun j => ∏ i ∈ G j, x.get i
  have hBpos : 0 < B := by simp [B]
  have hG (j : ℕ) : (G j).Nonempty := by
    refine ⟨1 + j * B, ?_⟩
    change 1 + j * B ∈ Finset.Ico (1 + j * B) (1 + (j + 1) * B)
    exact Finset.mem_Ico.mpr ⟨le_rfl,
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self j) hBpos) 1⟩
  have heven : ∀ i, 2 ∣ (x.get i : ℕ) := even_terms_of_SP2_valBucket_two x hval
  have hlo_x (i : ℕ) : 1 ≤ lo (x.get i) :=
    one_le_padicValNat_of_dvd (x.get i).ne_zero (heven i)
  have hlo_z (j : ℕ) : B ≤ lo (z j) := by
    change B ≤ lo (∏ i ∈ G j, x.get i)
    rw [lo_finset_prod]
    calc
      B = ∑ i ∈ G j, 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, G, Nat.card_Ico, add_mul,
          one_mul]
        rw [Nat.add_sub_add_left, Nat.add_sub_cancel_left]
        rfl
      _ ≤ ∑ i ∈ G j, lo (x.get i) :=
        Finset.sum_le_sum fun i hiG => hlo_x i
  have hhi0_lo (j : ℕ) : hi z0 < lo (z j) := by
    have := hlo_z j
    simp [B] at this ⊢
    omega
  have hlarge (j : ℕ) : D + 1 ≤ hi (z j) := by
    exact (by omega : D + 1 ≤ B).trans ((hlo_z j).trans (lo_le_hi (z j)))
  have hzSP (j : ℕ) : z0 + z j ∈ SP2 x := by
    have hm := sp2_singleton_product x (i := 0) (G := G j) (hG j) (by
      intro i hiG
      simp [G] at hiG
      omega)
    simpa [z0, z] using hm
  have hadd (j : ℕ) : hi (z0 + z j) = hi (z j) ∧ lo (z0 + z j) = D := by
    simpa [D] using hi_lo_add_of_hi_lt_lo z0 (z j) (hhi0_lo j)
  have hzpar (j : ℕ) : hi (z j) % 2 = 0 := by
    have hp := hpar _ (hzSP j)
    rwa [(hadd j).1] at hp
  have hflat (k : ℕ) :
      (∏ j ∈ Finset.range k, z j) =
        ∏ i ∈ Finset.Ico 1 (1 + k * B), x.get i := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.prod_range_succ, ih]
        change (∏ i ∈ Finset.Ico 1 (1 + k * B), x.get i) *
            (∏ i ∈ Finset.Ico (1 + k * B) (1 + (k + 1) * B), x.get i) =
          ∏ i ∈ Finset.Ico 1 (1 + (k + 1) * B), x.get i
        exact Finset.prod_Ico_consecutive _ (Nat.le_add_right _ _)
          (Nat.add_le_add_left (Nat.mul_le_mul_right B (Nat.le_succ k)) 1)
  have hnear : ∃ j, (z j : ℕ) <
      2 ^ hi (z j) + 2 ^ (hi (z j) - D - 1) := by
    by_contra hn
    push Not at hn
    obtain ⟨k, hkpos, hklog⟩ := lower_crossing D z hlarge hn
    let P : ℕ+ := ∏ j ∈ Finset.range k, z j
    have hkBpos : 0 < k * B := Nat.mul_pos hkpos hBpos
    have hPG : (Finset.Ico 1 (1 + k * B)).Nonempty := by
      refine ⟨1, ?_⟩
      exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_add_of_pos_right hkBpos⟩
    have hPSP : z0 + P ∈ SP2 x := by
      have hm := sp2_singleton_product x (i := 0)
        (G := Finset.Ico 1 (1 + k * B)) hPG (by
          intro i hi
          simp at hi
          omega)
      simpa [z0, P, hflat] using hm
    have hloP : hi z0 < lo P := by
      have hmem0 : 0 ∈ Finset.range k := by simp [hkpos]
      have hsingle : lo (z 0) ≤ ∑ j ∈ Finset.range k, lo (z j) :=
        Finset.single_le_sum (s := Finset.range k) (f := fun j => lo (z j))
          (fun _ _ => Nat.zero_le _) hmem0
      have hB : B ≤ lo P := by
        change B ≤ lo (∏ j ∈ Finset.range k, z j)
        rw [lo_finset_prod]
        exact (hlo_z 0).trans hsingle
      simp [B] at hB ⊢
      omega
    have hhiP : hi (z0 + P) = hi P :=
      (hi_lo_add_of_hi_lt_lo z0 P hloP).1
    have hsumpar : (∑ j ∈ Finset.range k, hi (z j)) % 2 = 0 := by
      rw [← Nat.dvd_iff_mod_eq_zero]
      exact Finset.dvd_sum fun j hj => Nat.dvd_iff_mod_eq_zero.mpr (hzpar j)
    have hPodd : hi P % 2 = 1 := by
      change hi (∏ j ∈ Finset.range k, z j) % 2 = 1
      rw [hklog]
      omega
    have hPeven := hpar _ hPSP
    rw [hhiP] at hPeven
    omega
  obtain ⟨j, hj⟩ := hnear
  have hz0small : (z0 : ℕ) < 2 ^ (hi (z j) - D - 1) := by
    calc
      (z0 : ℕ) < 2 ^ (hi z0 + 1) := hi_upper z0
      _ ≤ 2 ^ (hi (z j) - D - 1) := by
        apply Nat.pow_le_pow_right (by omega)
        have hhi := (hlo_z j).trans (lo_le_hi (z j))
        dsimp [B] at hhi
        omega
  have hpowsucc : 2 * 2 ^ (hi (z j) - D - 1) = 2 ^ (hi (z j) - D) := by
    rw [← Nat.pow_succ']
    congr 1
    have := hlarge j
    omega
  have hLow : LowSide (z0 + z j) := by
    unfold LowSide
    rw [(hadd j).1, (hadd j).2]
    change (z0 : ℕ) + (z j : ℕ) < 2 ^ hi (z j) + 2 ^ (hi (z j) - D)
    omega
  exact hlow _ (hzSP j) hLow

private lemma upper_crossing (D : ℕ) (z : ℕ → ℕ+)
    (hlarge : ∀ j, D + 1 ≤ hi (z j))
    (hfar : ∀ j, (z j : ℕ) ≤ 2 ^ (hi (z j) + 1) - 2 ^ (hi (z j) - D)) :
    ∃ k, 2 ≤ k ∧
      hi (∏ j ∈ Finset.range k, z j) =
        (∑ j ∈ Finset.range k, hi (z j)) + k - 2 := by
  classical
  let q := 2 ^ (D + 1)
  let P : ℕ → ℕ+ := fun k => ∏ j ∈ Finset.range k, z j
  let S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, hi (z j)
  have hq2 : 2 ≤ q := by
    change 2 ≤ 2 ^ (D + 1)
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hqpos : 0 < q := by omega
  have hqmpos : 0 < q - 1 := by omega
  have hfactor (j : ℕ) :
      q * (z j : ℕ) ≤ (q - 1) * 2 ^ (hi (z j) + 1) := by
    have hjlarge := hlarge j
    have hexp : D + 1 + (hi (z j) - D) = hi (z j) + 1 := by omega
    have hpow : q * 2 ^ (hi (z j) - D) = 2 ^ (hi (z j) + 1) := by
      change 2 ^ (D + 1) * 2 ^ (hi (z j) - D) = 2 ^ (hi (z j) + 1)
      rw [← Nat.pow_add, hexp]
    calc
      q * (z j : ℕ) ≤ q * (2 ^ (hi (z j) + 1) - 2 ^ (hi (z j) - D)) :=
        Nat.mul_le_mul_left q (hfar j)
      _ = q * 2 ^ (hi (z j) + 1) - q * 2 ^ (hi (z j) - D) :=
        Nat.mul_sub_left_distrib _ _ _
      _ = (q - 1) * 2 ^ (hi (z j) + 1) := by
        rw [hpow, Nat.sub_mul]
        simp
  have hprod (k : ℕ) :
      q ^ k * (P k : ℕ) ≤ (q - 1) ^ k * 2 ^ (S k + k) := by
    have hp := Finset.prod_le_prod (s := Finset.range k)
      (f := fun j => q * (z j : ℕ))
      (g := fun j => (q - 1) * 2 ^ (hi (z j) + 1))
      (fun _ _ => by omega) (fun j _ => hfactor j)
    simpa [P, S, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_add_distrib] using hp
  have hterm : (q - 1) * (q - 1) ^ (q - 1) = (q - 1) ^ q := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hbern : 2 * (q - 1) ^ q < q ^ q := by
    have hb := pow_add_mul_le_add_pow (R := ℕ) (a := q - 1) (b := 1)
      (by omega) (by omega) q
    have hstrict : (q - 1) ^ q < q * (q - 1) ^ (q - 1) := by
      rw [← hterm]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hqmpos _)
    have hsum : 2 * (q - 1) ^ q <
        (q - 1) ^ q + q * (q - 1) ^ (q - 1) := by omega
    have hqsub : q - 1 + 1 = q := by omega
    have hbound : (q - 1) ^ q + q * (q - 1) ^ (q - 1) ≤ q ^ q := by
      simpa [hqsub] using hb
    exact hsum.trans_le hbound
  have hcross : (P q : ℕ) < 2 ^ (S q + q - 1) := by
    have hp := hprod q
    have hpowpos : 0 < 2 ^ (S q + q - 1) := Nat.two_pow_pos _
    have hmul : q ^ q * (P q : ℕ) < q ^ q * 2 ^ (S q + q - 1) := by
      calc
        q ^ q * (P q : ℕ) ≤ (q - 1) ^ q * 2 ^ (S q + q) := hp
        _ = (2 * (q - 1) ^ q) * 2 ^ (S q + q - 1) := by
          have hexp : S q + q = (S q + q - 1) + 1 := by omega
          have hpowexp : 2 ^ (S q + q) = 2 ^ (S q + q - 1) * 2 := by
            calc
              2 ^ (S q + q) = 2 ^ ((S q + q - 1) + 1) := congrArg (fun e => 2 ^ e) hexp
              _ = 2 ^ (S q + q - 1) * 2 := pow_succ _ _
          rw [hpowexp]
          ring
        _ < q ^ q * 2 ^ (S q + q - 1) :=
          Nat.mul_lt_mul_of_pos_right hbern hpowpos
    exact Nat.lt_of_mul_lt_mul_left hmul
  let Q : ℕ → Prop := fun k => (P k : ℕ) < 2 ^ (S k + k - 1)
  have hQ : ∃ k, Q k := ⟨q, hcross⟩
  let k := Nat.find hQ
  have hkQ : Q k := Nat.find_spec hQ
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · have hk0Q : Q 0 := hk0 ▸ hkQ
      simp [Q, P, S] at hk0Q
    · have hk1Q : Q 1 := hk1 ▸ hkQ
      have hkbad : (z 0 : ℕ) < 2 ^ hi (z 0) := by simpa [Q, P, S] using hk1Q
      exact (not_lt_of_ge (hi_lower (z 0))) hkbad
  let t := k - 1
  have hkpos : 0 < k := by omega
  have htk : t < k := by simp [t, hkpos]
  have htQ : ¬Q t := Nat.find_min hQ htk
  have hkt : k = t + 1 := by simp [t, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have ht1 : 1 ≤ t := by simp [t]; omega
  have hprev : 2 ^ (S t + t - 1) ≤ (P t : ℕ) := by
    unfold Q at htQ
    exact Nat.le_of_not_gt htQ
  have hPk : P k = P t * z t := by
    simp [P, hkt, Finset.prod_range_succ]
  have hSk : S k = S t + hi (z t) := by
    simp [S, hkt, Finset.sum_range_succ]
  have hlower : 2 ^ (S k + k - 2) ≤ (P k : ℕ) := by
    rw [hPk, hSk]
    rw [hkt]
    change 2 ^ (S t + hi (z t) + (t + 1) - 2) ≤ (P t : ℕ) * (z t : ℕ)
    calc
      2 ^ (S t + hi (z t) + (t + 1) - 2) =
          2 ^ (S t + t - 1) * 2 ^ hi (z t) := by
            rw [← Nat.pow_add]
            congr 1
            omega
      _ ≤ (P t : ℕ) * (z t : ℕ) := Nat.mul_le_mul hprev (hi_lower (z t))
  refine ⟨k, hk2, ?_⟩
  apply Nat.log_eq_of_pow_le_of_lt_pow hlower
  have hupp : (P k : ℕ) < 2 ^ ((S k + k - 2) + 1) := by
    unfold Q at hkQ
    have hexp : S k + k - 1 = (S k + k - 2) + 1 := by omega
    rwa [← hexp]
  exact hupp

private lemma no_SP2_odd_not_high (x : Stream' ℕ+)
    (hval : ∀ n ∈ SP2 x, valBucket n = 2)
    (hpar : ∀ n ∈ SP2 x, hi n % 2 = 1)
    (hhigh : ∀ n ∈ SP2 x, ¬HighSide n) : False := by
  classical
  let z0 := x.get 0
  let D := lo z0
  let B := hi z0 + D + 2
  let G : ℕ → Finset ℕ := fun j => Finset.Ico (1 + j * B) (1 + (j + 1) * B)
  let z : ℕ → ℕ+ := fun j => ∏ i ∈ G j, x.get i
  have hBpos : 0 < B := by simp [B]
  have hG (j : ℕ) : (G j).Nonempty := by
    refine ⟨1 + j * B, ?_⟩
    change 1 + j * B ∈ Finset.Ico (1 + j * B) (1 + (j + 1) * B)
    exact Finset.mem_Ico.mpr ⟨le_rfl,
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self j) hBpos) 1⟩
  have heven : ∀ i, 2 ∣ (x.get i : ℕ) := even_terms_of_SP2_valBucket_two x hval
  have hlo_x (i : ℕ) : 1 ≤ lo (x.get i) :=
    one_le_padicValNat_of_dvd (x.get i).ne_zero (heven i)
  have hlo_z (j : ℕ) : B ≤ lo (z j) := by
    change B ≤ lo (∏ i ∈ G j, x.get i)
    rw [lo_finset_prod]
    calc
      B = ∑ i ∈ G j, 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, G, Nat.card_Ico, add_mul,
          one_mul]
        rw [Nat.add_sub_add_left, Nat.add_sub_cancel_left]
        rfl
      _ ≤ ∑ i ∈ G j, lo (x.get i) :=
        Finset.sum_le_sum fun i hiG => hlo_x i
  have hhi0_lo (j : ℕ) : hi z0 < lo (z j) := by
    have := hlo_z j
    simp [B] at this ⊢
    omega
  have hlarge (j : ℕ) : D + 1 ≤ hi (z j) := by
    exact (by omega : D + 1 ≤ B).trans ((hlo_z j).trans (lo_le_hi (z j)))
  have hzSP (j : ℕ) : z0 + z j ∈ SP2 x := by
    have hm := sp2_singleton_product x (i := 0) (G := G j) (hG j) (by
      intro i hiG
      simp [G] at hiG
      omega)
    simpa [z0, z] using hm
  have hadd (j : ℕ) : hi (z0 + z j) = hi (z j) ∧ lo (z0 + z j) = D := by
    simpa [D] using hi_lo_add_of_hi_lt_lo z0 (z j) (hhi0_lo j)
  have hzpar (j : ℕ) : hi (z j) % 2 = 1 := by
    have hp := hpar _ (hzSP j)
    rwa [(hadd j).1] at hp
  have hflat (k : ℕ) :
      (∏ j ∈ Finset.range k, z j) =
        ∏ i ∈ Finset.Ico 1 (1 + k * B), x.get i := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.prod_range_succ, ih]
        change (∏ i ∈ Finset.Ico 1 (1 + k * B), x.get i) *
            (∏ i ∈ Finset.Ico (1 + k * B) (1 + (k + 1) * B), x.get i) =
          ∏ i ∈ Finset.Ico 1 (1 + (k + 1) * B), x.get i
        exact Finset.prod_Ico_consecutive _ (Nat.le_add_right _ _)
          (Nat.add_le_add_left (Nat.mul_le_mul_right B (Nat.le_succ k)) 1)
  have hnear : ∃ j,
      2 ^ (hi (z j) + 1) - 2 ^ (hi (z j) - D) < (z j : ℕ) := by
    by_contra hn
    push Not at hn
    obtain ⟨k, hk2, hklog⟩ := upper_crossing D z hlarge hn
    let P : ℕ+ := ∏ j ∈ Finset.range k, z j
    have hkpos : 0 < k := by omega
    have hkBpos : 0 < k * B := Nat.mul_pos hkpos hBpos
    have hPG : (Finset.Ico 1 (1 + k * B)).Nonempty := by
      refine ⟨1, ?_⟩
      exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_add_of_pos_right hkBpos⟩
    have hPSP : z0 + P ∈ SP2 x := by
      have hm := sp2_singleton_product x (i := 0)
        (G := Finset.Ico 1 (1 + k * B)) hPG (by
          intro i hi
          simp at hi
          omega)
      simpa [z0, P, hflat] using hm
    have hloP : hi z0 < lo P := by
      have hmem0 : 0 ∈ Finset.range k := by simp [hkpos]
      have hsingle : lo (z 0) ≤ ∑ j ∈ Finset.range k, lo (z j) :=
        Finset.single_le_sum (s := Finset.range k) (f := fun j => lo (z j))
          (fun _ _ => Nat.zero_le _) hmem0
      have hB : B ≤ lo P := by
        change B ≤ lo (∏ j ∈ Finset.range k, z j)
        rw [lo_finset_prod]
        exact (hlo_z 0).trans hsingle
      simp [B] at hB ⊢
      omega
    have hhiP : hi (z0 + P) = hi P :=
      (hi_lo_add_of_hi_lt_lo z0 P hloP).1
    have hsumpar : (∑ j ∈ Finset.range k, hi (z j)) % 2 = k % 2 := by
      calc
        (∑ j ∈ Finset.range k, hi (z j)) % 2 =
            (∑ j ∈ Finset.range k, hi (z j) % 2) % 2 :=
          Finset.sum_nat_mod _ _ _
        _ = (∑ _j ∈ Finset.range k, 1) % 2 := by
          congr 1
          exact Finset.sum_congr rfl fun j hj => hzpar j
        _ = k % 2 := by simp
    have hPpar : hi P % 2 = 0 := by
      change hi (∏ j ∈ Finset.range k, z j) % 2 = 0
      rw [hklog]
      omega
    have hPodd := hpar _ hPSP
    rw [hhiP] at hPodd
    omega
  obtain ⟨j, hj⟩ := hnear
  have hHigh : HighSide (z0 + z j) := by
    unfold HighSide
    rw [(hadd j).1, (hadd j).2]
    change 2 ^ (hi (z j) + 1) - 2 ^ (hi (z j) - D) <
      (z0 : ℕ) + (z j : ℕ)
    omega
  exact hhigh _ (hzSP j) hHigh

/-- Smith's finite dyadic colouring separates ordered two-sums of products
from finite products. -/
private theorem smith_finite_separation :
    ¬ ∃ (x y : Stream' ℕ+) (η : SmithColor),
      (∀ n ∈ SP2 x, smithColor n = η) ∧
      (∀ n ∈ Hindman.FP y, smithColor n = η) := by
  rintro ⟨x, y, η, hx, hy⟩
  let r := x.get 0 + x.get 1
  have hr : r ∈ SP2 x := by simpa [r] using sp2_singletons x (by omega : 0 < 1)
  have heqSP (n : ℕ+) (hn : n ∈ SP2 x) : smithColor n = smithColor r :=
    (hx n hn).trans (hx r hr).symm
  have heqFP (n : ℕ+) (hn : n ∈ Hindman.FP y) : smithColor n = smithColor r :=
    (hy n hn).trans (hx r hr).symm
  by_cases hb0 : valBucket r = 0
  · apply no_SP2_valBucket_zero x
    intro n hn
    exact (smithColor_val_eq (heqSP n hn)).trans hb0
  by_cases hb1 : valBucket r = 1
  · apply no_FP_valBucket_one y
    intro n hn
    exact (smithColor_val_eq (heqFP n hn)).trans hb1
  have hb2 : valBucket r = 2 := by
    apply Fin.ext
    have hn0 : (valBucket r).val ≠ 0 := by
      intro h
      apply hb0
      exact Fin.ext h
    have hn1 : (valBucket r).val ≠ 1 := by
      intro h
      apply hb1
      exact Fin.ext h
    have hrange := (valBucket r).isLt
    omega
  have hvalSP : ∀ n ∈ SP2 x, valBucket n = 2 := by
    intro n hn
    exact (smithColor_val_eq (heqSP n hn)).trans hb2
  have hvalFP : ∀ n ∈ Hindman.FP y, 2 ≤ lo n := by
    intro n hn
    exact valBucket_eq_two_iff n |>.mp ((smithColor_val_eq (heqFP n hn)).trans hb2)
  by_cases hp : IsTwoPower r
  · apply no_SP2_twoPower_of_valBucket_two x hvalSP
    intro n hn
    exact (smithColor_power_eq (heqSP n hn)).mpr hp
  have hpowFP : ∀ n ∈ Hindman.FP y, ¬IsTwoPower n := by
    intro n hn hnp
    exact hp ((smithColor_power_eq (heqFP n hn)).mp hnp)
  by_cases hpar0 : hi r % 2 = 0
  · have hparSP : ∀ n ∈ SP2 x, hi n % 2 = 0 := by
      intro n hn
      exact (smithColor_hi_mod_eq (heqSP n hn)).trans hpar0
    have hparFP : ∀ n ∈ Hindman.FP y, hi n % 2 = 0 := by
      intro n hn
      exact (smithColor_hi_mod_eq (heqFP n hn)).trans hpar0
    by_cases hL : LowSide r
    · apply no_FP_even_low y hvalFP hpowFP hparFP
      intro n hn
      exact (smithColor_low_eq (heqFP n hn)).mpr hL
    · apply no_SP2_even_not_low x hvalSP hparSP
      intro n hn hLn
      exact hL ((smithColor_low_eq (heqSP n hn)).mp hLn)
  · have hpar1 : hi r % 2 = 1 := by omega
    have hparSP : ∀ n ∈ SP2 x, hi n % 2 = 1 := by
      intro n hn
      exact (smithColor_hi_mod_eq (heqSP n hn)).trans hpar1
    have hparFP : ∀ n ∈ Hindman.FP y, hi n % 2 = 1 := by
      intro n hn
      exact (smithColor_hi_mod_eq (heqFP n hn)).trans hpar1
    by_cases hH : HighSide r
    · apply no_FP_odd_high y hvalFP hpowFP hparFP
      intro n hn
      exact (smithColor_high_eq (heqFP n hn)).mpr hH
    · apply no_SP2_odd_not_high x hvalSP hparSP
      intro n hn hHn
      exact hH ((smithColor_high_eq (heqSP n hn)).mp hHn)

/-! ### The two-cell ultrafilter collapse -/

private def ustar (p : Ultrafilter ℕ+) (E : Set ℕ+) : Set ℕ+ :=
  E ∩ {x | {y | x * y ∈ E} ∈ p}

private lemma ustar_mem (p : Ultrafilter ℕ+) (hp : p * p = p) {E : Set ℕ+}
    (hE : E ∈ p) : ustar p E ∈ p := by
  have hmul : E ∈ (p * p) := by rwa [hp]
  have hevent : ∀ᶠ x in p, ∀ᶠ y in p, x * y ∈ E :=
    (Ultrafilter.eventually_mul p p E).mp hmul
  exact inter_mem hE hevent

private lemma ustar_shift_mem (p : Ultrafilter ℕ+) (hp : p * p = p) {E : Set ℕ+}
    {x : ℕ+} (hx : x ∈ ustar p E) : {y | x * y ∈ ustar p E} ∈ p := by
  have hxE : {y | x * y ∈ E} ∈ p := hx.2
  have hmul : {y | x * y ∈ E} ∈ (p * p) := by rwa [hp]
  have hevent : ∀ᶠ y in p, ∀ᶠ z in p, x * (y * z) ∈ E :=
    (Ultrafilter.eventually_mul p p {y | x * y ∈ E}).mp hmul
  have hshift : {y | {z | (x * y) * z ∈ E} ∈ p} ∈ p := by
    filter_upwards [hevent] with y hy
    filter_upwards [hy] with z hz
    simpa only [mul_assoc] using hz
  change {y | x * y ∈ E ∧ {z | (x * y) * z ∈ E} ∈ p} ∈ p
  exact inter_mem hxE hshift

private noncomputable def pickSet (K : Set ℕ+) : ℕ+ :=
  by
    classical
    exact if h : K.Nonempty then h.some else 1

private lemma pickSet_mem {K : Set ℕ+} (hK : K.Nonempty) : pickSet K ∈ K := by
  rw [pickSet]
  simp only [dif_pos hK]
  exact Classical.choose_spec hK

private def mulCandidates (p : Ultrafilter ℕ+) (D : Set ℕ+) (P : Finset ℕ+) : Set ℕ+ :=
  {x | x ∈ ustar p D ∧ ∀ u ∈ P, u * x ∈ ustar p D}

private lemma mulCandidates_mem (p : Ultrafilter ℕ+) (hp : p * p = p) {D : Set ℕ+}
    (hD : D ∈ p) (P : Finset ℕ+) (hP : ∀ u ∈ P, u ∈ ustar p D) :
    mulCandidates p D P ∈ p := by
  classical
  have hs : ustar p D ∈ p := ustar_mem p hp hD
  have hall : {x | ∀ u ∈ P, u * x ∈ ustar p D} ∈ p := by
    induction P using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall fun _ => by simp
    | @insert u P hu ih =>
        simp only [Finset.mem_insert, forall_eq_or_imp, Set.ofPred_and]
        exact inter_mem (ustar_shift_mem p hp (hP u (by simp)))
          (ih fun v hv => hP v (by simp [hv]))
  exact inter_mem hs hall

private def allTranslates (C : Set ℕ+) (N : Finset ℕ+) : Set ℕ+ :=
  {v | ∀ u ∈ N, u + v ∈ C}

private lemma allTranslates_mem (p : Ultrafilter ℕ+) {C D : Set ℕ+}
    (hD : ∀ u ∈ D, {v | u + v ∈ C} ∈ p) (N : Finset ℕ+) (hN : ↑N ⊆ D) :
    allTranslates C N ∈ p := by
  classical
  induction N using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall fun _ => by simp
  | @insert u N hu ih =>
      have huD : u ∈ D := hN (by simp)
      have hND : (↑N : Set ℕ+) ⊆ D := fun v hv => hN (by simp [hv])
      filter_upwards [hD u huD, ih hND] with v huv hv
      simp only [allTranslates, Finset.mem_insert, forall_eq_or_imp]
      exact ⟨huv, hv⟩

private abbrev BuildState := Finset ℕ+ × Set ℕ+

private def candidates (p : Ultrafilter ℕ+) (D : Set ℕ+) (s : BuildState) : Set ℕ+ :=
  ustar p s.2 ∩ mulCandidates p D s.1

private def newProducts (s : BuildState) (x : ℕ+) : Finset ℕ+ :=
  insert x (s.1.image fun u => u * x)

private noncomputable def buildNext (p : Ultrafilter ℕ+) (D C : Set ℕ+)
    (s : BuildState) : BuildState :=
  let x := pickSet (candidates p D s)
  let N := newProducts s x
  (s.1 ∪ N,
    (ustar p s.2 ∩ {y | x * y ∈ ustar p s.2}) ∩ allTranslates C N)

private noncomputable def buildState (p : Ultrafilter ℕ+) (D C : Set ℕ+) :
    ℕ → BuildState
  | 0 => (∅, Set.univ)
  | n + 1 => buildNext p D C (buildState p D C n)

private noncomputable def builtStream (p : Ultrafilter ℕ+) (D C : Set ℕ+) : Stream' ℕ+ :=
  fun n => pickSet (candidates p D (buildState p D C n))

private lemma candidates_mem (p : Ultrafilter ℕ+) (hp : p * p = p) {D : Set ℕ+}
    (s : BuildState) (hD : D ∈ p) (hE : s.2 ∈ p)
    (hP : ∀ u ∈ s.1, u ∈ ustar p D) : candidates p D s ∈ p := by
  exact inter_mem (ustar_mem p hp hE) (mulCandidates_mem p hp hD s.1 hP)

private lemma buildNext_invariant (p : Ultrafilter ℕ+) (hp : p * p = p)
    {D C : Set ℕ+} (hD : D ∈ p) (htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p)
    (s : BuildState) (hE : s.2 ∈ p) (hP : ∀ u ∈ s.1, u ∈ ustar p D) :
    (buildNext p D C s).2 ∈ p ∧
      ∀ u ∈ (buildNext p D C s).1, u ∈ ustar p D := by
  classical
  let K := candidates p D s
  let x := pickSet K
  let N := newProducts s x
  have hK : K ∈ p := candidates_mem p hp s hD hE hP
  have hKne : K.Nonempty := Filter.Eventually.exists hK
  have hx : x ∈ K := pickSet_mem hKne
  have hxE : x ∈ ustar p s.2 := hx.1
  have hxmul : x ∈ mulCandidates p D s.1 := hx.2
  have hN : ∀ u ∈ N, u ∈ ustar p D := by
    intro u hu
    simp only [N, newProducts, Finset.mem_insert, Finset.mem_image] at hu
    rcases hu with rfl | ⟨v, hv, rfl⟩
    · exact hxmul.1
    · exact hxmul.2 v hv
  have hND : (↑N : Set ℕ+) ⊆ D := by
    intro u hu
    exact (hN u hu).1
  have hbase : ustar p s.2 ∩ {y | x * y ∈ ustar p s.2} ∈ p :=
    inter_mem (ustar_mem p hp hE) (ustar_shift_mem p hp hxE)
  have hnextE :
      (ustar p s.2 ∩ {y | x * y ∈ ustar p s.2}) ∩ allTranslates C N ∈ p :=
    inter_mem hbase (allTranslates_mem p htrans N hND)
  constructor
  · simpa only [buildNext, x, N] using hnextE
  · intro u hu
    simp only [buildNext, Finset.mem_union] at hu
    exact hu.elim (hP u) (hN u)

private lemma build_invariant (p : Ultrafilter ℕ+) (hp : p * p = p)
    {D C : Set ℕ+} (hD : D ∈ p) (htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p) :
    ∀ n, (buildState p D C n).2 ∈ p ∧
      ∀ u ∈ (buildState p D C n).1, u ∈ ustar p D := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact Filter.Eventually.of_forall fun _ => trivial
      · simp [buildState]
  | succ n ih =>
      simpa only [buildState] using
        buildNext_invariant p hp hD htrans (buildState p D C n) ih.1 ih.2

private lemma built_mem_candidates (p : Ultrafilter ℕ+) (hp : p * p = p)
    {D C : Set ℕ+} (hD : D ∈ p) (htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p)
    (n : ℕ) :
    builtStream p D C n ∈ candidates p D (buildState p D C n) := by
  have hlarge := candidates_mem p hp (buildState p D C n) hD
    (build_invariant p hp hD htrans n).1 (build_invariant p hp hD htrans n).2
  exact pickSet_mem (Filter.Eventually.exists hlarge)

private lemma product_mem_buildState (p : Ultrafilter ℕ+) (_hp : p * p = p)
    {D C : Set ℕ+} (_hD : D ∈ p) (_htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p) :
    ∀ (n : ℕ) (F : Finset ℕ), F.Nonempty → F ⊆ Finset.range n →
      (∏ i ∈ F, builtStream p D C i) ∈ (buildState p D C n).1 := by
  classical
  intro n
  induction n with
  | zero =>
      intro F hF hsub
      obtain ⟨i, hi⟩ := hF
      have := hsub hi
      simp at this
  | succ n ih =>
      intro F hF hsub
      by_cases hn : n ∈ F
      · let H := F.erase n
        by_cases hH : H.Nonempty
        · have hHsub : H ⊆ Finset.range n := by
            intro i hi
            have hiF : i ∈ F := Finset.mem_of_mem_erase hi
            have hine : i ≠ n := Finset.ne_of_mem_erase hi
            have hir := Finset.mem_range.mp (hsub hiF)
            exact Finset.mem_range.mpr (by omega)
          have hprodH := ih H hH hHsub
          have himage : (∏ i ∈ H, builtStream p D C i) * builtStream p D C n ∈
              (buildState p D C n).1.image
                (fun u => u * builtStream p D C n) := by
            exact Finset.mem_image.mpr ⟨_, hprodH, rfl⟩
          have hnew : (∏ i ∈ H, builtStream p D C i) * builtStream p D C n ∈
              newProducts (buildState p D C n) (builtStream p D C n) := by
            exact Finset.mem_insert_of_mem himage
          have hmem : (∏ i ∈ H, builtStream p D C i) * builtStream p D C n ∈
              (buildState p D C (n + 1)).1 := by
            rw [buildState]
            change _ ∈ (buildState p D C n).1 ∪
              newProducts (buildState p D C n) (builtStream p D C n)
            exact Finset.mem_union_right _ hnew
          rw [← Finset.prod_erase_mul F (fun i => builtStream p D C i) hn]
          exact hmem
        · have hHe : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
          have hnew : builtStream p D C n ∈
              newProducts (buildState p D C n) (builtStream p D C n) := by
            simp [newProducts]
          have hmem : builtStream p D C n ∈ (buildState p D C (n + 1)).1 := by
            rw [buildState]
            change builtStream p D C n ∈ (buildState p D C n).1 ∪
              newProducts (buildState p D C n) (builtStream p D C n)
            exact Finset.mem_union_right _ hnew
          have hprod : (∏ i ∈ F, builtStream p D C i) = builtStream p D C n := by
            rw [← Finset.prod_erase_mul F (fun i => builtStream p D C i) hn]
            have hempty : (∏ i ∈ H, builtStream p D C i) = 1 := by
              rw [hHe]
              exact Finset.prod_empty
            rw [hempty, one_mul]
          rw [hprod]
          exact hmem
      · have hsub' : F ⊆ Finset.range n := by
          intro i hi
          have hir := Finset.mem_range.mp (hsub hi)
          have hine : i ≠ n := by
            intro hin
            exact hn (hin ▸ hi)
          exact Finset.mem_range.mpr (by omega)
        have hmem := ih F hF hsub'
        rw [buildState]
        change (∏ i ∈ F, builtStream p D C i) ∈ (buildState p D C n).1 ∪
          newProducts (buildState p D C n) (builtStream p D C n)
        exact Finset.mem_union_left _ hmem

private lemma build_succ_subset (p : Ultrafilter ℕ+) (D C : Set ℕ+) (n : ℕ) :
    (buildState p D C (n + 1)).2 ⊆ (buildState p D C n).2 := by
  intro y hy
  rw [buildState] at hy
  exact hy.1.1.1

private lemma build_succ_shift (p : Ultrafilter ℕ+) (D C : Set ℕ+) (n : ℕ)
    {y : ℕ+} (hy : y ∈ (buildState p D C (n + 1)).2) :
    builtStream p D C n * y ∈ (buildState p D C n).2 := by
  rw [buildState] at hy
  exact hy.1.2.1

private lemma build_succ_translate (p : Ultrafilter ℕ+) (D C : Set ℕ+) (n : ℕ)
    {u y : ℕ+}
    (hu : u ∈ newProducts (buildState p D C n) (builtStream p D C n))
    (hy : y ∈ (buildState p D C (n + 1)).2) : u + y ∈ C := by
  rw [buildState] at hy
  exact hy.2 u hu

private lemma build_antitone (p : Ultrafilter ℕ+) (D C : Set ℕ+) {m n : ℕ}
    (hmn : m ≤ n) : (buildState p D C n).2 ⊆ (buildState p D C m).2 := by
  induction n generalizing m with
  | zero =>
      have : m = 0 := by omega
      subst m
      exact Set.Subset.rfl
  | succ n ih =>
      by_cases h : m = n + 1
      · subst m
        exact Set.Subset.rfl
      · have hm : m ≤ n := by omega
        exact Set.Subset.trans (build_succ_subset p D C n) (ih hm)

private lemma tail_product_mem (p : Ultrafilter ℕ+) (hp : p * p = p)
    {D C : Set ℕ+} (hD : D ∈ p) (htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p) :
    ∀ (s : ℕ) (G : Finset ℕ), G.Nonempty → (∀ i ∈ G, s ≤ i) →
      (∏ i ∈ G, builtStream p D C i) ∈ (buildState p D C s).2 := by
  classical
  intro s G
  revert s
  refine Finset.strongInductionOn G ?_
  intro G ih s hG hs
  let i := G.min' hG
  let H := G.erase i
  have hiG : i ∈ G := G.min'_mem hG
  have hsi : s ≤ i := hs i hiG
  have hxi : builtStream p D C i ∈ (buildState p D C i).2 :=
    (built_mem_candidates p hp hD htrans i).1.1
  by_cases hH : H.Nonempty
  · have hproper : H ⊂ G := Finset.erase_ssubset hiG
    have hbound : ∀ j ∈ H, i + 1 ≤ j := by
      intro j hj
      have hj' : j ∈ G.erase (G.min' hG) := by simpa [H, i] using hj
      have hij : i < j := by
        simpa [i] using G.min'_lt_of_mem_erase_min' hG hj'
      omega
    have htail : (∏ j ∈ H, builtStream p D C j) ∈
        (buildState p D C (i + 1)).2 := ih H hproper (i + 1) hH hbound
    have hmul : builtStream p D C i * (∏ j ∈ H, builtStream p D C j) ∈
        (buildState p D C i).2 := build_succ_shift p D C i htail
    have hwhole : (∏ j ∈ G, builtStream p D C j) ∈
        (buildState p D C i).2 := by
      rw [← Finset.mul_prod_erase G (fun j => builtStream p D C j) hiG]
      exact hmul
    exact build_antitone p D C hsi hwhole
  · have hHe : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    have hwhole : (∏ j ∈ G, builtStream p D C j) = builtStream p D C i := by
      rw [← Finset.mul_prod_erase G (fun j => builtStream p D C j) hiG]
      have hempty : (∏ j ∈ H, builtStream p D C j) = 1 := by
        rw [hHe]
        exact Finset.prod_empty
      rw [hempty, mul_one]
    rw [hwhole]
    exact build_antitone p D C hsi hxi

private lemma product_mem_newProducts (p : Ultrafilter ℕ+) (hp : p * p = p)
    {D C : Set ℕ+} (hD : D ∈ p) (htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p)
    {n : ℕ} {F : Finset ℕ} (hn : n ∈ F) (hsub : F ⊆ Finset.range (n + 1)) :
    (∏ i ∈ F, builtStream p D C i) ∈
      newProducts (buildState p D C n) (builtStream p D C n) := by
  classical
  let H := F.erase n
  by_cases hH : H.Nonempty
  · have hHsub : H ⊆ Finset.range n := by
      intro i hi
      have hiF : i ∈ F := Finset.mem_of_mem_erase hi
      have hine : i ≠ n := Finset.ne_of_mem_erase hi
      have hir := Finset.mem_range.mp (hsub hiF)
      exact Finset.mem_range.mpr (by omega)
    have hprodH := product_mem_buildState p hp hD htrans n H hH hHsub
    have himage : (∏ i ∈ H, builtStream p D C i) * builtStream p D C n ∈
        (buildState p D C n).1.image (fun u => u * builtStream p D C n) :=
      Finset.mem_image.mpr ⟨_, hprodH, rfl⟩
    rw [← Finset.prod_erase_mul F (fun i => builtStream p D C i) hn]
    exact Finset.mem_insert_of_mem himage
  · have hHe : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    have hprod : (∏ i ∈ F, builtStream p D C i) = builtStream p D C n := by
      rw [← Finset.prod_erase_mul F (fun i => builtStream p D C i) hn]
      have hempty : (∏ i ∈ H, builtStream p D C i) = 1 := by
        rw [hHe]
        exact Finset.prod_empty
      rw [hempty, one_mul]
    rw [hprod]
    simp [newProducts]

/-- An additive square of a multiplicative idempotent contains an ordered
sum of two finite-product systems. -/
private lemma sp2_of_large (p : Ultrafilter ℕ+) (hp : p * p = p) {C : Set ℕ+}
    (hC : C ∈ p + p) : ∃ x : Stream' ℕ+, SP2 x ⊆ C := by
  let D : Set ℕ+ := {u | {v | u + v ∈ C} ∈ p}
  have hD : D ∈ p := (Ultrafilter.eventually_add p p C).mp hC
  have htrans : ∀ u ∈ D, {v | u + v ∈ C} ∈ p := by
    intro u hu
    exact hu
  refine ⟨builtStream p D C, ?_⟩
  intro z hz
  rcases hz with ⟨F, G, hF, hG, horder, rfl⟩
  let n := F.max' hF
  have hnF : n ∈ F := F.max'_mem hF
  have hFsub : F ⊆ Finset.range (n + 1) := by
    intro i hi
    have hin : i ≤ n := Finset.le_max' F i hi
    exact Finset.mem_range.mpr (by omega)
  have hu : (∏ i ∈ F, builtStream p D C i) ∈
      newProducts (buildState p D C n) (builtStream p D C n) :=
    product_mem_newProducts p hp hD htrans hnF hFsub
  have hGbound : ∀ j ∈ G, n + 1 ≤ j := by
    intro j hj
    have := horder n hnF j hj
    omega
  have hv : (∏ j ∈ G, builtStream p D C j) ∈
      (buildState p D C (n + 1)).2 :=
    tail_product_mem p hp hD htrans (n + 1) G hG hGbound
  exact build_succ_translate p D C n hu hv

private lemma exists_idempotent_ultrafilter_tails {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ n, Hindman.FP (a.drop n) ∈ U := by
  let S : Set (Ultrafilter M) := ⋂ n, {U | Hindman.FP (a.drop n) ∈ U}
  have h := exists_idempotent_in_compact_subsemigroup
    Ultrafilter.continuous_mul_left S (by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      · intro n U hU
        filter_upwards [hU]
        rw [← Stream'.drop_drop, ← Stream'.tail_eq_drop]
        exact Hindman.FP.tail _
      · intro n
        exact ⟨pure _, mem_pure.mpr <| Hindman.FP.head _⟩
      · exact (ultrafilter_isClosed_basic _).isCompact
      · intro n
        apply ultrafilter_isClosed_basic)
    (IsClosed.isCompact (isClosed_iInter fun _ => ultrafilter_isClosed_basic _)) (by
      intro U hU V hV
      rw [Set.mem_iInter] at *
      intro n
      change ∀ᶠ m in (U * V), m ∈ Hindman.FP (a.drop n)
      rw [Ultrafilter.eventually_mul]
      filter_upwards [hU n] with m hm
      obtain ⟨n', hn⟩ := Hindman.FP.mul hm
      filter_upwards [hV (n' + n)] with m' hm'
      apply hn
      simpa only [Stream'.drop_drop, add_comm] using hm')
  rcases h with ⟨U, hU, hUidem⟩
  exact ⟨U, hUidem, Set.mem_iInter.mp hU⟩

private lemma prod_image_succ (a : Stream' ℕ+) (F : Finset ℕ) :
    (∏ i ∈ F.image Nat.succ, a.get i) = ∏ i ∈ F, a.tail.get i := by
  rw [Finset.prod_image]
  · simp
  · exact Nat.succ_injective.injOn

private lemma fp_exists_finset {a : Stream' ℕ+} {m : ℕ+} (hm : m ∈ Hindman.FP a) :
    ∃ F : Finset ℕ, F.Nonempty ∧ m = ∏ i ∈ F, a.get i := by
  classical
  induction hm with
  | head' a =>
      exact ⟨{0}, Finset.singleton_nonempty 0, by simp [Stream'.head]⟩
  | tail' a m hm ih =>
      rcases ih with ⟨F, hF, rfl⟩
      refine ⟨F.image Nat.succ, hF.image _, ?_⟩
      exact (prod_image_succ a F).symm
  | cons' a m hm ih =>
      rcases ih with ⟨F, hF, rfl⟩
      refine ⟨insert 0 (F.image Nat.succ), Finset.insert_nonempty _ _, ?_⟩
      have hzero : 0 ∉ F.image Nat.succ := by simp
      rw [Finset.prod_insert hzero, prod_image_succ]

private lemma prod_image_add (a : Stream' ℕ+) (n : ℕ) (F : Finset ℕ) :
    (∏ i ∈ F.image (n + ·), a.get i) = ∏ i ∈ F, (a.drop n).get i := by
  rw [Finset.prod_image]
  · simp
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

private lemma fp_add_tail_subset_sp2 {a : Stream' ℕ+} {u : ℕ+}
    (hu : u ∈ Hindman.FP a) :
    ∃ n, ∀ v ∈ Hindman.FP (a.drop n), u + v ∈ SP2 a := by
  classical
  rcases fp_exists_finset hu with ⟨F, hF, rfl⟩
  let n := F.max' hF + 1
  refine ⟨n, ?_⟩
  intro v hv
  rcases fp_exists_finset hv with ⟨G, hG, rfl⟩
  let G' := G.image (n + ·)
  refine ⟨F, G', hF, hG.image _, ?_, ?_⟩
  · intro i hi j hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have himax : i ≤ F.max' hF := Finset.le_max' F i hi
    dsimp only [n]
    omega
  · rw [prod_image_add]

private lemma sp2_mem_add_of_tails (a : Stream' ℕ+) (p : Ultrafilter ℕ+)
    (htails : ∀ n, Hindman.FP (a.drop n) ∈ p) : SP2 a ∈ p + p := by
  change ∀ᶠ z in (p + p), z ∈ SP2 a
  rw [Ultrafilter.eventually_add]
  filter_upwards [htails 0] with u hu
  have hu' : u ∈ Hindman.FP a := by simpa using hu
  obtain ⟨n, hn⟩ := fp_add_tail_subset_sp2 hu'
  filter_upwards [htails n] with v hv
  exact hn v hv

private def GoodCell (η : SmithColor) : Prop :=
  ∃ y : Stream' ℕ+, Hindman.FP y ⊆ {n | smithColor n = η}

private noncomputable def smithSet : Set ℕ+ :=
  {n | GoodCell (smithColor n)}

private lemma smithSet_mem_idempotent (p : Ultrafilter ℕ+) (hp : p * p = p) :
    smithSet ∈ p := by
  have hall : ∀ᶠ n in p, ∃ η : SmithColor, smithColor n = η :=
    Filter.Eventually.of_forall fun n => ⟨smithColor n, rfl⟩
  obtain ⟨η, hη⟩ := (Ultrafilter.eventually_exists_iff.mp hall)
  obtain ⟨y, hy⟩ := Hindman.exists_FP_of_large p hp {n | smithColor n = η} hη
  have hgood : GoodCell η := ⟨y, hy⟩
  filter_upwards [hη] with n hn
  change GoodCell (smithColor n)
  simpa [hn] using hgood

private lemma smithSet_compl_mem_add (p : Ultrafilter ℕ+) (hp : p * p = p) :
    smithSetᶜ ∈ p + p := by
  have hall : ∀ᶠ n in (p + p), ∃ η : SmithColor, smithColor n = η :=
    Filter.Eventually.of_forall fun n => ⟨smithColor n, rfl⟩
  obtain ⟨η, hη⟩ := (Ultrafilter.eventually_exists_iff.mp hall)
  obtain ⟨x, hx⟩ := sp2_of_large p hp hη
  have hnot : ¬ GoodCell η := by
    rintro ⟨y, hy⟩
    apply smith_finite_separation
    exact ⟨x, y, η, fun n hn => hx hn, fun n hn => hy hn⟩
  filter_upwards [hη] with n hn
  change ¬ GoodCell (smithColor n)
  simpa [hn] using hnot

private theorem smith_two_cell_separation :
    ∃ B : Set ℕ+,
      (¬ ∃ y : Stream' ℕ+, Hindman.FP y ⊆ Bᶜ) ∧
      (¬ ∃ x : Stream' ℕ+, SP2 x ⊆ B) := by
  refine ⟨smithSet, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, htails⟩ := exists_idempotent_ultrafilter_tails y
    have hFP : Hindman.FP y ∈ p := by simpa using htails 0
    have hcomp : smithSetᶜ ∈ p := Filter.mem_of_superset hFP hy
    have hempty : (∅ : Set ℕ+) ∈ p := by
      simpa using inter_mem (smithSet_mem_idempotent p hp) hcomp
    exact Set.not_nonempty_empty (Filter.Eventually.exists hempty)
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, htails⟩ := exists_idempotent_ultrafilter_tails x
    have hSP : SP2 x ∈ p + p := sp2_mem_add_of_tails x p htails
    have hset : smithSet ∈ p + p := Filter.mem_of_superset hSP hx
    have hempty : (∅ : Set ℕ+) ∈ p + p := by
      simpa using inter_mem hset (smithSet_compl_mem_add p hp)
    exact Set.not_nonempty_empty (Filter.Eventually.exists hempty)

/-! ### Encoding the forbidden configurations as Problem 1198 expressions -/

private lemma disjoint_of_order {F G : Finset ℕ}
    (horder : ∀ i ∈ F, ∀ j ∈ G, i < j) : Disjoint F G := by
  rw [Finset.disjoint_left]
  intro i hiF hiG
  exact (Nat.lt_irrefl i) (horder i hiF i hiG)

private lemma two_blocks_admissible {F G : Finset ℕ} (hF : F.Nonempty)
    (hG : G.Nonempty) (horder : ∀ i ∈ F, ∀ j ∈ G, i < j) :
    Admissible {F, G} := by
  have hdisj : Disjoint F G := disjoint_of_order horder
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact hF
    · exact hG
  · intro S hS T hT hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · exact (hne rfl).elim
    · exact hdisj
    · exact hdisj.symm
    · exact (hne rfl).elim

private lemma two_blocks_nontrivial {F G : Finset ℕ} (hF : F.Nonempty)
    (hG : G.Nonempty) (horder : ∀ i ∈ F, ∀ j ∈ G, i < j) :
    Nontrivial {F, G} := by
  rintro ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  have hFm : F ∈ ({F, G} : Finset (Finset ℕ)) := by simp
  have hGm : G ∈ ({F, G} : Finset (Finset ℕ)) := by simp
  rw [hi] at hFm hGm
  have hFeq : F = {i} := by simpa using hFm
  have hGeq : G = {i} := by simpa using hGm
  have hfi : f = i := by simpa [hFeq] using hf
  have hgi : g = i := by simpa [hGeq] using hg
  exact (Nat.lt_irrefl i) (by simpa [hfi, hgi] using horder f hf g hg)

private lemma two_blocks_value (a : ℕ → ℕ) {F G : Finset ℕ}
    (hF : F.Nonempty) (horder : ∀ i ∈ F, ∀ j ∈ G, i < j) :
    expressionValue a {F, G} = (∏ i ∈ F, a i) + ∏ j ∈ G, a j := by
  have hne : F ≠ G := by
    intro hFG
    obtain ⟨i, hi⟩ := hF
    have hiG : i ∈ G := by simpa [hFG] using hi
    exact (Nat.lt_irrefl i) (horder i hi i hiG)
  simp [expressionValue, hne]

private def pairedStream (a : Stream' ℕ+) : Stream' ℕ+ :=
  fun j => a.get (2 * j) * a.get (2 * j + 1)

private def pairedSupport (F : Finset ℕ) : Finset ℕ :=
  F.image (2 * ·) ∪ F.image (fun j => 2 * j + 1)

private lemma even_odd_disjoint (F : Finset ℕ) :
    Disjoint (F.image (2 * ·)) (F.image fun j => 2 * j + 1) := by
  rw [Finset.disjoint_left]
  intro n hnE hnO
  rcases Finset.mem_image.mp hnE with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hnO with ⟨j, hj, hij⟩
  omega

private lemma paired_product_eq (a : Stream' ℕ+) (F : Finset ℕ) :
    (∏ j ∈ F, pairedStream a j) = ∏ i ∈ pairedSupport F, a.get i := by
  classical
  rw [pairedSupport, Finset.prod_union (even_odd_disjoint F)]
  rw [Finset.prod_image, Finset.prod_image]
  · rw [← Finset.prod_mul_distrib]
    rfl
  · intro i _ j _ hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega
  · intro i _ j _ hij
    change 2 * i = 2 * j at hij
    omega

private lemma pairedSupport_nonempty {F : Finset ℕ} (hF : F.Nonempty) :
    (pairedSupport F).Nonempty := by
  obtain ⟨j, hj⟩ := hF
  exact ⟨2 * j, by simp [pairedSupport, hj]⟩

private lemma pairedSupport_not_singleton {F : Finset ℕ} (hF : F.Nonempty) :
    ¬ ∃ i : ℕ, pairedSupport F = {i} := by
  obtain ⟨j, hj⟩ := hF
  rintro ⟨i, hi⟩
  have he : 2 * j ∈ pairedSupport F := by simp [pairedSupport, hj]
  have ho : 2 * j + 1 ∈ pairedSupport F := by simp [pairedSupport, hj]
  rw [hi] at he ho
  have hei : 2 * j = i := by simpa using he
  have hoi : 2 * j + 1 = i := by simpa using ho
  omega

private lemma singleton_block_admissible {H : Finset ℕ} (hH : H.Nonempty) :
    Admissible {H} := by
  refine ⟨Finset.singleton_nonempty H, ?_, ?_⟩
  · intro S hS
    have hS' : S = H := by simpa using hS
    simpa [hS'] using hH
  · intro S hS T hT hne
    have hS' : S = H := by simpa using hS
    have hT' : T = H := by simpa using hT
    exact (hne (hS'.trans hT'.symm)).elim

private lemma singleton_block_nontrivial {H : Finset ℕ}
    (hH : ¬ ∃ i : ℕ, H = {i}) : Nontrivial {H} := by
  rintro ⟨i, hi⟩
  apply hH
  exact ⟨i, Finset.singleton_injective hi⟩

private lemma positive_product_coe (a : ℕ → ℕ) (hpos : ∀ i, 0 < a i)
    (F : Finset ℕ) :
    ((∏ i ∈ F, (⟨a i, hpos i⟩ : ℕ+)) : ℕ+) = ∏ i ∈ F, a i := by
  exact Finset.PNat.coe_prod (fun i => ⟨a i, hpos i⟩) F

private lemma singleton_paired_value (a : ℕ → ℕ) (hpos : ∀ i, 0 < a i)
    (F : Finset ℕ) :
    expressionValue a {pairedSupport F} =
      ((∏ j ∈ F, pairedStream (fun i => ⟨a i, hpos i⟩) j : ℕ+) : ℕ) := by
  simp only [expressionValue, Finset.sum_singleton]
  let ap : Stream' ℕ+ := fun i => ⟨a i, hpos i⟩
  have hcoe := Finset.PNat.coe_prod ap (pairedSupport F)
  change (↑(∏ i ∈ pairedSupport F, ap i) : ℕ) =
    ∏ i ∈ pairedSupport F, a i at hcoe
  have hpair := congrArg Subtype.val (paired_product_eq ap F).symm
  exact hcoe.symm.trans hpair

private noncomputable def twoColor (B : Set ℕ+) : ℕ → Fin 2 :=
  by
    classical
    exact fun n => if h : 0 < n then if (⟨n, h⟩ : ℕ+) ∈ B then 0 else 1 else 0

private lemma twoColor_eq_zero (B : Set ℕ+) (n : ℕ+) :
    twoColor B n = 0 ↔ n ∈ B := by
  classical
  have heta (h : 0 < (n : ℕ)) : (⟨(n : ℕ), h⟩ : ℕ+) = n := Subtype.ext rfl
  simp [twoColor, n.pos, heta]
  exact Iff.rfl

private lemma twoColor_eq_one (B : Set ℕ+) (n : ℕ+) :
    twoColor B n = 1 ↔ n ∉ B := by
  classical
  have heta (h : 0 < (n : ℕ)) : (⟨(n : ℕ), h⟩ : ℕ+) = n := Subtype.ext rfl
  simp [twoColor, n.pos, heta]
  exact Iff.rfl

/-- Erdős Problem 1198 has a negative answer.  This is the exact negation of
the statement above, for all two-colourings and all admissible nontrivial
sums of products. -/
theorem erdos1198 : ¬ Erdos1198Statement := by
  classical
  obtain ⟨B, hnoFP, hnoSP⟩ := smith_two_cell_separation
  intro h1198
  obtain ⟨a, _ha, hpos, color, hmono⟩ := h1198 (twoColor B)
  let ap : Stream' ℕ+ := fun i => ⟨a i, hpos i⟩
  have hSPcolor : ∀ z ∈ SP2 ap, twoColor B z = color := by
    intro z hz
    rcases hz with ⟨F, G, hF, hG, horder, hz⟩
    have hadm : Admissible {F, G} := two_blocks_admissible hF hG horder
    have hnon : Nontrivial {F, G} := two_blocks_nontrivial hF hG horder
    have hvalue : expressionValue a {F, G} = (z : ℕ) := by
      rw [two_blocks_value a hF horder]
      rw [← positive_product_coe a hpos F, ← positive_product_coe a hpos G]
      exact (congrArg Subtype.val hz).symm
    change twoColor B (z : ℕ) = color
    rw [← hvalue]
    exact hmono {F, G} hadm hnon
  have hFPcolor : ∀ z ∈ Hindman.FP (pairedStream ap), twoColor B z = color := by
    intro z hz
    rcases fp_exists_finset hz with ⟨F, hF, hzF⟩
    have hadm : Admissible {pairedSupport F} :=
      singleton_block_admissible (pairedSupport_nonempty hF)
    have hnon : Nontrivial {pairedSupport F} :=
      singleton_block_nontrivial (pairedSupport_not_singleton hF)
    have hvalue : expressionValue a {pairedSupport F} = (z : ℕ) :=
      (singleton_paired_value a hpos F).trans (congrArg Subtype.val hzF).symm
    change twoColor B (z : ℕ) = color
    rw [← hvalue]
    exact hmono {pairedSupport F} hadm hnon
  fin_cases color
  · apply hnoSP
    refine ⟨ap, ?_⟩
    intro z hz
    exact (twoColor_eq_zero B z).mp (hSPcolor z hz)
  · apply hnoFP
    refine ⟨pairedStream ap, ?_⟩
    intro z hz
    exact (twoColor_eq_one B z).mp (hFPcolor z hz)

#print axioms erdos1198

end Erdos1198
