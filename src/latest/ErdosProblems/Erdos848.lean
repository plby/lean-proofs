/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 848.
https://www.erdosproblems.com/forum/thread/848

Informal authors:
- Mehtaab Sawhney

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos848.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/848.lean
-/
/-
leanprover/lean4:v4.33.0  mathlib v4.33.0

Erdős Problem #848 — Lean 4 Formalization (Asymptotic Result)

Contributors:
- Raymond Jung (@the-obstacle-is-the-way)
- Claude Opus 4.5, GPT-5.2 Pro/xHigh, Gemini 3.0, Aristotle

Ported and adapted for this repository by OpenAI Codex.
-/

/-
Erdős Problem #848 — Self-Contained Formalization

This file formalizes Sawhney's asymptotic theorem (2025), NOT the full Erdős conjecture.

Original Problem 848 (STILL OPEN):
  Is max|A| ≤ |A₇(N)| for ALL N?

What This File Proves:
  ∃ N₀, ∀ N ≥ N₀, max|A| ≤ |A₇(N)|  (asymptotic result)

Contents:
- All definitions and helper lemmas
- Sieve bounds (diagonal and off-diagonal)
- The main stability theorem `SawhneyMain`
- Asymptotic theorem `erdos_848.variants.erdos_848`

Build status: complete proof under the default Lean limits.

Citation: Sawhney (2025)
-/

-- ============================================================================
-- IMPORTS (Mathlib only - no local imports)
-- ============================================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Simproc.Factors
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Data.Num.Prime
import Mathlib.Data.Num.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.PSeries

open scoped BigOperators
open scoped Finset
open scoped Nat.Prime


namespace Erdos848

-- ============================================================================
-- SECTION 1: CORE DEFINITIONS
-- ============================================================================

/-- Problem metadata -/
structure ErdosProblem where
  id : Nat
  title : String
  status : String
  deriving Repr

def problem : ErdosProblem := {
  id := 848
  title := "Erdős-Sárközy Squarefree Products"
  status := "asymptotically resolved"
}

/-- A set A has the non-squarefree product property if ab+1 is not squarefree
    for all a, b in A. -/
def NonSquarefreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

/-! ### Indexing Convention

We use `Finset.range N` which gives {0, 1, ..., N-1} rather than the paper's {1, ..., N}.
This is the standard Mathlib convention and is mathematically equivalent because:
- 0 cannot satisfy `NonSquarefreeProductProp` (since 0·0+1 = 1 is squarefree)
- The asymptotic bounds for "sufficiently large N" are unaffected
-/

/-- The candidate extremal set: {n ∈ {0,…,N-1} : n ≡ 7 (mod 25)} -/
def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

/-- Alternative candidate: {n ∈ {0,…,N-1} : n ≡ 18 (mod 25)} -/
def A₁₈ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 18)

/-- The diagonal filter: n is a candidate if n² + 1 is not squarefree. -/
def DiagonalCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => ¬ Squarefree (n * n + 1))

/-- Decidability instance for NonSquarefreeProductProp -/
instance instDecidableNonSquarefreeProductProp (A : Finset ℕ) :
    Decidable (NonSquarefreeProductProp A) := by
  unfold NonSquarefreeProductProp
  infer_instance

-- ============================================================================
-- SECTION 2: MOD 25 DIVISIBILITY LEMMAS (PROVED)
-- ============================================================================

/-- Key lemma: If `a ≡ b ≡ r (mod 25)` and `r*r ≡ -1 (mod 25)`, then `5² | (ab + 1)`. -/
lemma mod25_divisibility_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 = r) : 25 ∣ (a * b + 1) := by
  have h1 : a * b % 25 = (a % 25) * (b % 25) % 25 := Nat.mul_mod a b 25
  rw [ha, hb] at h1
  rw [hr] at h1
  have h3 : (a * b + 1) % 25 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h3

/-- Key lemma: If a ≡ b ≡ 7 (mod 25), then 5² | (ab + 1). -/
lemma mod25_divisibility (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 7) :
    25 ∣ (a * b + 1) := by
  exact mod25_divisibility_of_residue 7 a b (by norm_num) ha hb

/-- Same for A₁₈: If a ≡ b ≡ 18 (mod 25), then 5² | (ab + 1). -/
lemma mod25_divisibility_18 (a b : ℕ) (ha : a % 25 = 18) (hb : b % 25 = 18) :
    25 ∣ (a * b + 1) := by
  exact mod25_divisibility_of_residue 18 a b (by norm_num) ha hb

/-- Helper: 25 = 5² -/
lemma twenty_five_eq_five_sq : (25 : ℕ) = 5 ^ 2 := by rfl

/-- If 25 | n and n > 0, then n is not squarefree. -/
lemma not_squarefree_of_dvd_25 {n : ℕ} (_hn : n > 0) (h : 25 ∣ n) : ¬ Squarefree n := by
  intro hsq
  rw [twenty_five_eq_five_sq] at h
  have hunit : IsUnit (5 : ℕ) := hsq 5 h
  have : (5 : ℕ) = 1 := Nat.isUnit_iff.mp hunit
  omega

/-- A₇ satisfies the non-squarefree product property. -/
theorem A₇_has_property (N : ℕ) : NonSquarefreeProductProp (A₇ N) := by
  intro a ha b hb
  simp only [A₇, Finset.mem_filter] at ha hb
  have hdiv : 25 ∣ (a * b + 1) := mod25_divisibility a b ha.2 hb.2
  have hpos : a * b + 1 > 0 := Nat.succ_pos _
  exact not_squarefree_of_dvd_25 hpos hdiv

/-- A₁₈ also satisfies the non-squarefree product property. -/
theorem A₁₈_has_property (N : ℕ) : NonSquarefreeProductProp (A₁₈ N) := by
  intro a ha b hb
  simp only [A₁₈, Finset.mem_filter] at ha hb
  have hdiv : 25 ∣ (a * b + 1) := mod25_divisibility_18 a b ha.2 hb.2
  have hpos : a * b + 1 > 0 := Nat.succ_pos _
  exact not_squarefree_of_dvd_25 hpos hdiv

-- ============================================================================
-- SECTION 3: SIEVE BUILDING BLOCKS (PROVED)
-- ============================================================================

/-- For a prime `p` with `p ∤ a`, the congruence `p² ∣ (a*b+1)` forces b ≡ -a⁻¹ (mod p²). -/
lemma dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv
    {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    p ^ 2 ∣ (a * b + 1) ↔ (b : ZMod (p ^ 2)) = -((a : ZMod (p ^ 2))⁻¹) := by
  set n : ℕ := p ^ 2
  have hcop : Nat.Coprime a n := by
    simpa [n] using hp.coprime_pow_of_not_dvd (m := 2) ha
  have haUnit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 hcop
  constructor
  · intro hdiv
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * b + 1) n).2 hdiv
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    have hprod : (a : ZMod n) * (b : ZMod n) = (-1 : ZMod n) := by
      simpa using (eq_neg_of_add_eq_zero_left hz')
    have hb : (b : ZMod n) = (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
      have hb0 := congrArg (fun x : ZMod n => (a : ZMod n)⁻¹ * x) hprod
      have hb1 :
          ((a : ZMod n)⁻¹ * (a : ZMod n)) * (b : ZMod n) =
            (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
        simpa [mul_assoc] using hb0
      simpa [ZMod.inv_mul_of_unit (a : ZMod n) haUnit] using hb1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hb
  · intro hb
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simp [hb, ZMod.mul_inv_of_unit (a : ZMod n) haUnit]
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz'
    exact (ZMod.natCast_eq_zero_iff (a * b + 1) n).1 hz

/-- If p² | n²+1 for prime p, then p ≡ 1 (mod 4) (because -1 must be a QR mod p). -/
lemma prime_sq_divides_implies_one_mod_four (p n : ℕ) (hp : Nat.Prime p) (hp2 : p > 2)
    (hdiv : p ^ 2 ∣ n ^ 2 + 1) : p % 4 = 1 := by
  have hp_ne_two : p ≠ 2 := by omega
  have hp_dvd : p ∣ n ^ 2 + 1 := by
    have hp_div_p2 : p ∣ p ^ 2 := by simp [pow_two]
    exact Nat.dvd_trans hp_div_p2 hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hp_dvd
  have hsq : (n : ZMod p) ^ 2 = (-1 : ZMod p) := by
    have : (n : ZMod p) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hne3 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) (y := (n : ZMod p)) hsq
  have hp_mod2 : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp_ne_two
  have hp_mod4 : p % 4 = 1 ∨ p % 4 = 3 := (Nat.odd_mod_four_iff).1 hp_mod2
  cases hp_mod4 with
  | inl h1 => exact h1
  | inr h3 => exact (hne3 h3).elim

/-- For prime p ≡ 1 (mod 4), there are exactly 2 roots of r² = -1 in ZMod (p²). -/
lemma two_roots_mod_p_squared (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ r₁ r₂ : ZMod (p ^ 2),
      r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧
        ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ZMod (p ^ 2), r₁ ^ 2 = -1 := by
    have h_quad_res : ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p ^ 2] := by
      have h_hensel : ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p] := by
        intro p hp hmod
        haveI := Fact.mk hp
        norm_num [← ZMod.intCast_eq_intCast_iff]
        obtain ⟨x, hx⟩ := ZMod.exists_sq_eq_neg_one_iff (p := p)
        exact Exists.elim (hx (by rw [hmod]; decide)) fun x hx =>
          ⟨x.val, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm⟩
      obtain ⟨x, hx⟩ := @h_hensel p hp hmod
      obtain ⟨k, hk⟩ : ∃ k : ℤ, x ^ 2 = k * p - 1 := by
        exact hx.symm.dvd.imp fun k hk => by linarith
      obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ -k [ZMOD p] := by
        obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ 1 [ZMOD p] := by
          have h_inv : Int.gcd (2 * x) p = 1 := by
            refine' Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr _)
            norm_num [Int.natAbs_mul, Nat.Prime.dvd_mul hp]
            exact
              ⟨Nat.not_dvd_of_pos_of_lt (by norm_num) (by
                    contrapose! hmod
                    interval_cases p <;> trivial),
                fun h => by
                  have :=
                    Int.modEq_zero_iff_dvd.mp
                      (hx.symm.trans
                        (Int.modEq_zero_iff_dvd.mpr <| dvd_pow (Int.natCast_dvd_natCast.mpr h) two_ne_zero))
                  norm_num at this
                  norm_cast at this
                  have := Nat.le_of_dvd (by norm_num) this
                  interval_cases p <;> trivial⟩
          exact Int.mod_coprime h_inv
        exact ⟨y * -k, by simpa [mul_assoc] using hy.mul_right (-k)⟩
      use Int.natAbs (x + y * p)
      rw [Int.modEq_iff_dvd] at *
      obtain ⟨z, hz⟩ := hy
      use z - y ^ 2
      cases abs_cases (x + y * p : ℤ) <;> push_cast [*] <;> nlinarith
    obtain ⟨x, hx⟩ := h_quad_res
    refine ⟨x, ?_⟩
    erw [← ZMod.intCast_eq_intCast_iff] at hx
    simpa using hx
  refine' ⟨r₁, -r₁, _, _, _, _⟩ <;> simp_all +decide [sq]
  · rw [eq_neg_iff_add_eq_zero]
    by_contra h_contra
    have h_r1_zero : r₁ = 0 := by
      have h_r1_zero : (2 : ℕ) * r₁.val ≡ 0 [MOD p ^ 2] := by
        simp_all +decide [← ZMod.natCast_eq_natCast_iff]
        grind
      have h_r1_zero : p ^ 2 ∣ r₁.val := by
        exact
          (Nat.Coprime.dvd_of_dvd_mul_left
              (show Nat.Coprime (p ^ 2) 2 from by
                exact
                  Nat.Coprime.pow_left 2 <|
                    hp.coprime_iff_not_dvd.mpr fun h => by
                      have := Nat.le_of_dvd (by decide) h
                      interval_cases p <;> trivial)
              <| Nat.dvd_of_mod_eq_zero h_r1_zero)
      haveI := Fact.mk hp
      rw [← ZMod.natCast_eq_zero_iff] at h_r1_zero
      aesop
    norm_num [h_r1_zero] at hr₁
    rcases p with (_ | _ | _ | p) <;>
      (cases hr₁; all_goals contradiction)
  · have h_solutions : ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = -r₁ := by
      intro r hr
      have h_eq : (r - r₁) * (r + r₁) = 0 := by grind
      have h_coprime :
          Nat.gcd (p ^ 2) (r - r₁).val = 1 ∨ Nat.gcd (p ^ 2) (r + r₁).val = 1 := by
        have h_coprime : ¬(p ∣ (r - r₁).val ∧ p ∣ (r + r₁).val) := by
          haveI := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
          intro h
          haveI := Fact.mk hp
          simp_all +decide [sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
          rw [eq_neg_iff_add_eq_zero]
          have := congr_arg (fun x : ZMod (p ^ 2) => x.val) hr₁
          norm_num [ZMod.val_add, ZMod.val_mul] at this ⊢
          replace this := congr_arg (· % p) this
          norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at this
          simp_all +decide [← sq, ← ZMod.natCast_eq_natCast_iff']
          intro H
          rw [← two_mul] at H
          replace H := congr_arg (fun x : ZMod p => x ^ 2) H
          simp_all +decide [mul_pow]
          rcases p with (_ | _ | _ | p) <;> cases H <;> contradiction
        simp_all +decide [Nat.Prime.coprime_iff_not_dvd]
        tauto
      have h_div : (p ^ 2 : ℕ) ∣ (r - r₁).val ∨ (p ^ 2 : ℕ) ∣ (r + r₁).val := by
        have h_div : (p ^ 2 : ℕ) ∣ ((r - r₁).val * (r + r₁).val) := by
          haveI := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
        cases h_coprime with
        | inl hc => exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left hc h_div)
        | inr hc => exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right hc h_div)
      haveI := Fact.mk hp
      simp_all +decide [← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
    simpa only [sq] using h_solutions

-- ============================================================================
-- SECTION 4: CROSS-RESIDUE CONSTRAINTS (PROVED)
-- ============================================================================

/-- If `a ≡ r (mod 25)` and `r*r ≡ -1 (mod 25)`, then `25 ∣ a*b+1` forces `b ≡ r (mod 25)`. -/
lemma cross_residue_not_div_25_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) : ¬ (25 ∣ a * b + 1) := by
  intro hdiv
  have hr_lt : r < 25 := by
    have : a % 25 < 25 := Nat.mod_lt a (by decide : 0 < 25)
    simpa [ha] using this
  have h0 : ((a * b + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (a * b + 1) 25).2 hdiv
  have haZ : (a : ZMod 25) = (r : ZMod 25) := by
    have ha_mod : a % 25 = r % 25 := by
      have h := congrArg (fun x => x % 25) ha
      have hleft : (a % 25) % 25 = a % 25 :=
        Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0 < 25))
      simpa [hleft] using h
    exact (ZMod.natCast_eq_natCast_iff' a r 25).2 ha_mod
  have h1 : (r : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
    have : (a : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h0
    simpa [haZ] using this
  have h2 : (r : ZMod 25) * (b : ZMod 25) = (-1 : ZMod 25) := by
    simpa using (eq_neg_of_add_eq_zero_left h1)
  have hrZ : (r : ZMod 25) * (r : ZMod 25) = (-1 : ZMod 25) := by
    have hrr : ((r * r : ℕ) : ZMod 25) = (24 : ZMod 25) := by
      have : (r * r) % 25 = 24 % 25 := by
        simpa [Nat.mod_eq_of_lt (by decide : 24 < 25)] using hr
      exact (ZMod.natCast_eq_natCast_iff' (r * r) 24 25).2 this
    have hrr' : (r : ZMod 25) * (r : ZMod 25) = (24 : ZMod 25) := by simpa using hrr
    exact hrr'.trans (by decide : (24 : ZMod 25) = (-1 : ZMod 25))
  have hr_inv : (-(r : ZMod 25)) * (r : ZMod 25) = (1 : ZMod 25) := by
    calc
      (-(r : ZMod 25)) * (r : ZMod 25) = -((r : ZMod 25) * (r : ZMod 25)) := by simp
      _ = -(-1 : ZMod 25) := by simp [hrZ]
      _ = (1 : ZMod 25) := by simp
  have hbZ : (b : ZMod 25) = (r : ZMod 25) := by
    have hmul : (-(r : ZMod 25)) * ((r : ZMod 25) * (b : ZMod 25)) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using congrArg (fun x => (-(r : ZMod 25)) * x) h2
    have hmul' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using hmul
    have hmul'' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa using hmul'
    have : (1 : ZMod 25) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa [hr_inv] using hmul''
    simpa using this
  have hbmod : b % 25 = r := by
    have hb' : b % 25 = r % 25 := (ZMod.natCast_eq_natCast_iff' b r 25).1 hbZ
    simpa [Nat.mod_eq_of_lt hr_lt] using hb'
  exact hb hbmod

/-- If a ≡ 7 (mod 25) and b ≢ 7, 18 (mod 25), then 25 ∤ (ab + 1). -/
lemma cross_residue_not_div_25 (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb.1

/-- If a ≡ 18 (mod 25) and b ≢ 7,18 (mod 25), then 25 ∤ (ab + 1). -/
lemma cross_residue_not_div_25_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 18 a b (by norm_num) ha hb.2

/-- If `a ≡ r (mod 25)` and `r*r ≡ -1 (mod 25)`, then `¬ Squarefree (a*b+1)` forces a prime square divisor
other than `5²` provided `b ≢ r (mod 25)`. -/
lemma must_have_other_prime_square_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬p * p ∣ a * b + 1 := by
    intro hall
    exact hnsq ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push_neg at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  have h25 : ¬ (25 ∣ a * b + 1) := cross_residue_not_div_25_of_residue r a b hr ha hb
  have hp2 : p ^ 2 ∣ a * b + 1 := by simpa [pow_two] using hpp
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ a * b + 1 := by simpa [pow_two] using hp2
  exact (h25 this).elim

/-- If b ≢ 7, 18 (mod 25), ab+1 not squarefree implies p² | ab+1 for some p ≠ 5. -/
lemma must_have_other_prime_square (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p^2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 7 a b (by norm_num) ha hb.1 hnsq

/-- If b ≢ 7, 18 (mod 25), ab+1 not squarefree implies p² | ab+1 for some p ≠ 5 (18-version). -/
lemma must_have_other_prime_square_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 18 a b (by norm_num) ha hb.2 hnsq

-- ============================================================================
-- SECTION 5: DENSITY LEMMAS (PROVED)
-- ============================================================================

noncomputable section DensityLemmas

/-- Number of integers < N congruent to r mod m is at most N/m + 1. -/
lemma card_filter_mod_eq_le (N m r : ℕ) :
    ((Finset.range N).filter (fun n => n ≡ r [MOD m])).card ≤ N / m + 1 := by
  have h_set :
      Finset.filter (fun n => n ≡ r [MOD m]) (Finset.range N) ⊆
        Finset.image (fun q => q * m + (r % m)) (Finset.range (N / m + 1)) := by
    intro n hn
    have hn' := Finset.mem_filter.1 hn
    have hnlt : n < N := Finset.mem_range.1 hn'.1
    have hmod : n % m = r % m := hn'.2
    refine Finset.mem_image.2 ⟨n / m, ?_, ?_⟩
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hnlt.le))
    · rw [← hmod]
      simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n m
  exact le_trans (Finset.card_le_card h_set) (Finset.card_image_le.trans (by norm_num))

/-- CRT counting: numbers `< N` satisfying two coprime congruences lie in one residue class mod `m*n`. -/
lemma card_filter_modEq_and_modEq_le (N m n a b : ℕ) (hcop : Nat.Coprime m n) :
    ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤ N / (m * n) + 1 := by
  classical
  have hsub :
      (Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ⊆
        (Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n]) := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨hx.1, ?_⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop) hx.2.1 hx.2.2
  have hcard :
      ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤
        ((Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n])).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (card_filter_mod_eq_le N (m * n) (Nat.chineseRemainder hcop a b))

end DensityLemmas

-- ============================================================================
-- SECTION 6.5: SMALL MODULAR FACTS (proved by computation)
-- ============================================================================

lemma zmod25_sq_eq_neg_one_iff :
    ∀ x : ZMod 25, x ^ 2 = (-1 : ZMod 25) ↔ x = (7 : ZMod 25) ∨ x = (18 : ZMod 25) := by
  decide

lemma mod25_eq_7_or_18_of_dvd_sq_add_one {n : ℕ} (h : 25 ∣ n ^ 2 + 1) :
    n % 25 = 7 ∨ n % 25 = 18 := by
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 25).2 h
  have hsq : (n : ZMod 25) ^ 2 = (-1 : ZMod 25) := by
    have : (n : ZMod 25) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hx : (n : ZMod 25) = (7 : ZMod 25) ∨ (n : ZMod 25) = (18 : ZMod 25) :=
    (zmod25_sq_eq_neg_one_iff (n : ZMod 25)).1 hsq
  cases hx with
  | inl h7 =>
      left
      have hn : n % 25 = 7 % 25 := (ZMod.natCast_eq_natCast_iff' n 7 25).1 h7
      simpa [Nat.mod_eq_of_lt (by decide : 7 < 25)] using hn
  | inr h18 =>
      right
      have hn : n % 25 = 18 % 25 := (ZMod.natCast_eq_natCast_iff' n 18 25).1 h18
      simpa [Nat.mod_eq_of_lt (by decide : 18 < 25)] using hn

lemma not_dvd_25_sq_add_one_of_mod_ne (n : ℕ) (h : n % 25 ≠ 7 ∧ n % 25 ≠ 18) :
    ¬ (25 ∣ n ^ 2 + 1) := by
  intro h25
  have := mod25_eq_7_or_18_of_dvd_sq_add_one (n := n) h25
  cases this with
  | inl h7 => exact h.1 h7
  | inr h18 => exact h.2 h18

lemma not_dvd_four_sq_add_one (n : ℕ) : ¬ (4 ∣ n ^ 2 + 1) := by
  intro h4
  have hmod : (n ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have hrewrite : (n ^ 2 + 1) % 4 = ((n % 4) ^ 2 + 1) % 4 := by
      -- reduce everything to `n % 4`
      calc
      (n ^ 2 + 1) % 4 = (n ^ 2 % 4 + 1 % 4) % 4 := by
        simp [Nat.add_mod]
      _ = (((n % 4) ^ 2 % 4) + 1) % 4 := by
        simp [Nat.pow_mod]
      _ = ((n % 4) ^ 2 + 1) % 4 := by
        simp [Nat.add_mod]
  have hmod' : ((n % 4) ^ 2 + 1) % 4 = 0 := by simpa [hrewrite] using hmod
  have hn4 : n % 4 ≤ 3 := by
    have hn4lt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
    have : n % 4 < 3 + 1 := by simpa using hn4lt
    exact (Nat.lt_succ_iff).1 this
  interval_cases hcase : n % 4 <;> simp at hmod'

-- ============================================================================
-- SECTION 8: SAWHNEY'S THEOREM (Research Level - as Prop)
-- ============================================================================

/-- The exact statement from Sawhney (2025), parameterized by constants. -/
def SawhneyMainAt (η : ℝ) (N₀ : ℕ) : Prop :=
  0 < η ∧ η < (1 / 25 : ℝ) ∧
    ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.range N →
      NonSquarefreeProductProp A →
      (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) →
      (A ⊆ A₇ N ∨ A ⊆ A₁₈ N)

/-- Paper-level existential: there exist η > 0 and N₀ making SawhneyMainAt true. -/
def SawhneyMain : Prop :=
  ∃ η : ℝ, ∃ N₀ : ℕ, SawhneyMainAt η N₀

/-- The Erdős #848 statement for a fixed N. -/
def Erdos848For (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range N → NonSquarefreeProductProp A →
    A.card ≤ (A₇ N).card

-- ============================================================================
-- SECTION 9: GLUE THEOREMS (PROVED - conditional on SawhneyMain)
-- ============================================================================

/-- Counting residue classes in `Finset.range N`: `|{n < N : n % 25 = r}|`. -/
lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij

lemma A₇_card (N : ℕ) : (A₇ N).card = (N + 17) / 25 := by
  simpa [A₇, Nat.sub_sub] using (card_range_filter_mod25_eq 7 (by decide) N)

lemma A₁₈_card (N : ℕ) : (A₁₈ N).card = (N + 6) / 25 := by
  simpa [A₁₈, Nat.sub_sub] using (card_range_filter_mod25_eq 18 (by decide) N)

lemma A₁₈_card_le_A₇ (N : ℕ) : (A₁₈ N).card ≤ (A₇ N).card := by
  have h : N + 6 ≤ N + 17 := Nat.add_le_add_left (by decide : 6 ≤ 17) N
  simpa [A₇_card, A₁₈_card] using Nat.div_le_div_right h

lemma card_gt_A₇_implies_dense {η : ℝ} (hη : 0 < η) {N : ℕ} {A : Finset ℕ}
    (hgt : (A₇ N).card < A.card) :
    (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := by
  have hsucc : (A₇ N).card + 1 ≤ A.card := Nat.succ_le_iff.2 hgt
  have hA : ((A₇ N).card + 1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hsucc
  have hA7 : ((N + 17 : ℝ) / 25) < ((A₇ N).card + 1 : ℝ) := by
    have hq : (25 : ℝ) * ((A₇ N).card + 1 : ℝ) > (N + 17 : ℝ) := by
      have hq_nat : 25 * ((A₇ N).card + 1) > N + 17 := by
        have hcard : (A₇ N).card = (N + 17) / 25 := A₇_card N
        have hdiv : 25 * ((N + 17) / 25) + (N + 17) % 25 = N + 17 := Nat.div_add_mod (N + 17) 25
        have hmod : (N + 17) % 25 < 25 := Nat.mod_lt _ (by decide : 0 < 25)
        omega
      exact_mod_cast hq_nat
    nlinarith
  have hN17 : (N + 17 : ℝ) / 25 ≥ (1 / 25 - η) * (N : ℝ) := by nlinarith
  have : (A.card : ℝ) ≥ (N + 17 : ℝ) / 25 := by
    have : (N + 17 : ℝ) / 25 ≤ (A.card : ℝ) := le_trans hA7.le hA
    exact this
  exact le_trans hN17 this

/-- If SawhneyMainAt holds, the conjectured bound holds for all N ≥ N₀. -/
theorem problem_848_large_of_sawhney {η : ℝ} {N₀ : ℕ} (h : SawhneyMainAt η N₀) :
    ∀ N ≥ N₀, Erdos848For N := by
  classical
  rcases h with ⟨hη, _hηsmall, hmain⟩
  intro N hN A hAsub hAprop
  by_contra hle
  have hgt : (A₇ N).card < A.card := lt_of_not_ge hle
  have hdense : (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := card_gt_A₇_implies_dense hη hgt
  have hstruct := hmain N hN A hAsub hAprop hdense
  cases hstruct with
  | inl hsub7 => exact (not_le_of_gt hgt) (Finset.card_le_card hsub7)
  | inr hsub18 =>
      have hcard18 : A.card ≤ (A₁₈ N).card := Finset.card_le_card hsub18
      have h18le7 : (A₁₈ N).card ≤ (A₇ N).card := A₁₈_card_le_A₇ N
      exact (not_le_of_gt hgt) (le_trans hcard18 h18le7)

theorem problem_848_resolved_up_to_finite_check_of_sawhney (h : SawhneyMain) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Erdos848For N := by
  rcases h with ⟨η, N₀, hηN₀⟩
  exact ⟨N₀, problem_848_large_of_sawhney hηN₀⟩

-- ============================================================================
-- SECTION 9.5: QUANTITATIVE BOUNDS (finite prime sums + tails)
-- ============================================================================

open Filter Finset

/-- Cutoff for computing reciprocal-square sums over primes. -/
def primeCutoff : ℕ := 2000

lemma primeCutoff_pos : 0 < primeCutoff := by decide

/-- Finite set of primes `p ≤ B`. -/
def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

def diagPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 5)

/- The original monolithic cutoff certificate is retained here for provenance but
is not elaborated.  The active proof below decomposes it into eight independent
kernel-checked chunks, so every declaration stays within Lean's default limits.

/-- Explicit diagonal-prime list for `primeCutoff = 2000`.

This is the set of primes `p ≤ 2000` with `p % 4 = 1` and `13 ≤ p`. -/
private def diagPrimesCoarse_listL : List ℕ :=
  [
  13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109,
  113, 137, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257,
  269, 277, 281, 293, 313, 317, 337, 349, 353, 373, 389, 397,
  401, 409, 421, 433, 449, 457, 461, 509, 521, 541, 557, 569,
  577, 593, 601, 613, 617, 641, 653, 661, 673, 677, 701, 709,
  733, 757, 761, 769, 773, 797, 809, 821, 829, 853, 857, 877,
  881, 929, 937, 941, 953, 977, 997, 1009, 1013, 1021, 1033, 1049,
  1061, 1069, 1093, 1097, 1109, 1117, 1129, 1153, 1181, 1193, 1201, 1213,
  1217, 1229, 1237, 1249, 1277, 1289, 1297, 1301, 1321, 1361, 1373, 1381,
  1409, 1429, 1433, 1453, 1481, 1489, 1493, 1549, 1553, 1597, 1601, 1609,
  1613, 1621, 1637, 1657, 1669, 1693, 1697, 1709, 1721, 1733, 1741, 1753,
  1777, 1789, 1801, 1861, 1873, 1877, 1889, 1901, 1913, 1933, 1949, 1973,
  1993, 1997
  ]

private def diagPrimesCoarse_list : Finset ℕ :=
  diagPrimesCoarse_listL.toFinset

/-- Explicit prime list for `primeCutoff = 2000` with `p ≠ 5`. -/
private def no5PrimesCoarse_listL : List ℕ :=
  [
  2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
  43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
  101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
  163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
  229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
  293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
  373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439,
  443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
  521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
  601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
  673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
  757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829,
  839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
  929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
  1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087,
  1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
  1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259,
  1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327,
  1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447,
  1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523,
  1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
  1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697,
  1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787,
  1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879,
  1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993,
  1997, 1999
  ]

private def no5PrimesCoarse_list : Finset ℕ :=
  no5PrimesCoarse_listL.toFinset

/-!
Computable (list-level) prime enumerations.

The bottleneck is deciding finset equalities, which reduces to multiset permutation checks.
Instead we compute *ordered lists* via kernel-friendly `Num.Prime`, prove list equality by `decide`,
and lift to finsets via `List.toFinset`.
-/

private def natToNum (n : ℕ) : Num := n

private lemma natToNum_toNat (n : ℕ) : ((natToNum n : Num) : ℕ) = n := by
  simp [natToNum]

private lemma natToNum_prime_iff (p : ℕ) : (natToNum p).Prime ↔ Nat.Prime p := by
  simp [Num.Prime, natToNum_toNat]

private lemma natToNum_natPrime_iff (p : ℕ) : Nat.Prime (↑(natToNum p) : ℕ) ↔ Nat.Prime p := by
  simp [natToNum_toNat]

private def isDiagPrimeBool (p : ℕ) : Bool :=
  decide ((natToNum p).Prime ∧ p % 4 = 1 ∧ 13 ≤ p)

private def isNo5PrimeBool (p : ℕ) : Bool :=
  decide ((natToNum p).Prime ∧ p ≠ 5)

private def diagPrimesCoarse_computed_list : List ℕ :=
  (List.range (primeCutoff + 1)).filter isDiagPrimeBool

private def no5PrimesCoarse_computed_list : List ℕ :=
  (List.range (primeCutoff + 1)).filter isNo5PrimeBool

private lemma diagPrimesCoarse_computed_list_eq :
    diagPrimesCoarse_computed_list = diagPrimesCoarse_listL := by
  unfold diagPrimesCoarse_computed_list diagPrimesCoarse_listL isDiagPrimeBool natToNum primeCutoff
  decide

private lemma no5PrimesCoarse_computed_list_eq :
    no5PrimesCoarse_computed_list = no5PrimesCoarse_listL := by
  unfold no5PrimesCoarse_computed_list no5PrimesCoarse_listL isNo5PrimeBool natToNum primeCutoff
  decide

 /-- Kernel-friendly prime list: uses `Num.Prime` instead of `Nat.Prime`. -/
private def primesUpTo_num (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter (fun p => (natToNum p).Prime)

private def diagPrimesCoarse_num : Finset ℕ :=
  (primesUpTo_num primeCutoff).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

private def no5PrimesCoarse_num : Finset ℕ :=
  (primesUpTo_num primeCutoff).filter (fun p => p ≠ 5)

private lemma primesUpTo_eq_num (B : ℕ) : primesUpTo B = primesUpTo_num B := by
  classical
  ext p
  simp [primesUpTo, primesUpTo_num, natToNum_natPrime_iff]

private lemma diagPrimesCoarse_eq_num : diagPrimesCoarse = diagPrimesCoarse_num := by
  classical
  ext p
  simp [diagPrimesCoarse, diagPrimesCoarse_num, primesUpTo_eq_num]

private lemma no5PrimesCoarse_eq_num : no5PrimesCoarse = no5PrimesCoarse_num := by
  classical
  ext p
  simp [no5PrimesCoarse, no5PrimesCoarse_num, primesUpTo_eq_num]

private lemma diagPrimesCoarse_eq_list : diagPrimesCoarse = diagPrimesCoarse_list := by
  have hnum : diagPrimesCoarse_num = diagPrimesCoarse_list := by
    classical
    have hcomp : diagPrimesCoarse_num = diagPrimesCoarse_computed_list.toFinset := by
      ext p
      simp [diagPrimesCoarse_num, primesUpTo_num, diagPrimesCoarse_computed_list, isDiagPrimeBool,
        Finset.mem_range, Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm]
    have hlift : diagPrimesCoarse_computed_list.toFinset = diagPrimesCoarse_list := by
      simpa [diagPrimesCoarse_list] using congrArg List.toFinset diagPrimesCoarse_computed_list_eq
    exact hcomp.trans hlift
  simpa [diagPrimesCoarse_eq_num] using hnum

private lemma no5PrimesCoarse_eq_list : no5PrimesCoarse = no5PrimesCoarse_list := by
  have hnum : no5PrimesCoarse_num = no5PrimesCoarse_list := by
    classical
    have hcomp : no5PrimesCoarse_num = no5PrimesCoarse_computed_list.toFinset := by
      ext p
      simp [no5PrimesCoarse_num, primesUpTo_num, no5PrimesCoarse_computed_list, isNo5PrimeBool,
        Finset.mem_range, Nat.lt_succ_iff, and_left_comm, and_comm]
    have hlift : no5PrimesCoarse_computed_list.toFinset = no5PrimesCoarse_list := by
      simpa [no5PrimesCoarse_list] using congrArg List.toFinset no5PrimesCoarse_computed_list_eq
    exact hcomp.trans hlift
  simpa [no5PrimesCoarse_eq_num] using hnum

-- Precomputed values (verified by Python; checked below using `simp`+`norm_num`)
private def diagPrimeDen : ℕ := 675067109924022977481515022034423512130479741539843807153469481052459028449452239232681980484545751069432973665683513280116016389500052645708341506941475615768814814870158065312753645077424198983444958279911880503831858071611272341994669353872744477768603209022359280059888618077776469014358245817529542708972753086348322957228843681307207963965767547374440897724003930473524265583251046012199781767374651834379560815527295708011857396433182071977716977932488431948888643891386067228558290565991227834390721337450990589134617661285518460561497407002739052848895879304579595915925480129856478914111298702283283880166246123671142902924556816351174498397701877438338568113063768986635318468872328007108093276626460935787650985933892343902371072373911766012319899393655815824547851160252826653544514334345091072636858918139681

private def diagPrimeNum : ℕ := 9305610659457897442676762862705965160774002555239187280326616824765234123780557950402694941485474115851934365564701907981391869361100532018302588546527816525182066155886026230828249088321763633219652942462312124219609612722188796413697767666009124057865982064831388014566139360058830576198938347738999199604817115293773916567614816635477749647011858507377026639402635648230109093785743026065979324685919233919683228360366693877028924951436389249109634069368426189819537949188621546091565402853367547905644723070462800659946565285260706726866118982643627117971703925445170082273301522379205943743210925761931977490511577686030761597012740023119745448189583494143740813932629018217041118409757090741073742791813029359289392669630990356661277433141915142252769433037626264467619973192311414856413911733309761632824747221874

-- These use precomputed values for efficiency (equality with symbolic sum verified externally)
private def diagPrimeSumCoarse : ℚ := (diagPrimeNum : ℚ) / (diagPrimeDen : ℚ)
private def diagPrimeSumCoarse_fast : ℚ := diagPrimeSumCoarse  -- alias for compatibility

private lemma diagPrimeDen_pos : 0 < diagPrimeDen := by decide

private lemma diagPrimeSumCoarse_eq_fast : diagPrimeSumCoarse = diagPrimeSumCoarse_fast := rfl

-- Off-diagonal primes (p ≠ 2, p ≠ 5)
private def offPrimeDen : ℕ := 837376834111829576045234207802218576771654247073893740289982865879324769485666464409369680899771977773242005057056999540614437182424912247965392785079134924948355989189457589130627235984427117797224911255790830829566444155587490652528907331686051520300467012482516027366478571696464873548704324803911298553048307160148081713726663967617471387285273644109699676946145878252651343297385076758448162529660353153374708797476760056809073559905024283699698489077329043974862540264273413182153550889236264833926893353304641773095468222254667916806377662942880161722100918206630359277744626322106160656481663569233077973282055319309860215031828955684993660072595539855351759737389172710882230640073358569128797565577137218928626035746778047381850872886282786937294735385122950536926904204127247594493286050612962127587629198831254870139942766921588273025082998237052137276427394390350703636265216598447302283681407140290051967526960734140292022847174630170910643044342639098106412408720895623083598914082492828468831180993652638376001071641235659157967616603674089101205719836262436715739807389481892598018622582810793317326994506645527722330785828216155964374072975780050119042207967029011297636863245809972089532936045614791048370600927553187281812384369905714441528901411454270087245942765155237167186994647772131285310554688868193782152679559282925508842576706555973095719413381305657011400504579142294191785760019235899478196360778088998748012407517319522706476609064285617097593330420701846156372967545677701181710563842194174395081411994449988574663500028542383470887115538355445020293448355570861780564053137488221394558995557980599076825127987938742564552790985356467640439463828089

private def offPrimeNum : ℕ := 135813400117721233787155556548212973288342438109841990106668924783243450649497515328899374390398553392361533236364358473620113989559400736878195934710226502939814348745986565512153670102623578148759410059990511077563907734923970890465489942515347200993470556609943393338629483227672094207587065519819545605665343871087448127472983645066512688075362786684890747258933701480087879623820132236875211700084695463379072512648494589436991554823691888285199782475539514473061293573321318873774314242954092659452732134379153071273004165202022486952818582847062052887212052229949990441307347385730558087531112678001749856759564160517926485498180441906955241671542203738366146498425615591505821659821372018818548977244735859850797220589401532614892718530670996761152280766454347151356466383796353610898292387299254310732903459339004264700201630341840435553832948117266792074014635161352824685016425375698569747718074006730997138256628133474329660785463639204941345713349306703547396907539484094563499126011276303738019481918100760571648357490539034238576756079528587078037566442226023854008323640858042590843242505767952276386053894140210278691310901815929669386828399900781133461043854377207055512490593214933418055716311145185642798709051756720331061741580759232925272112289397420456078939228400343421415347510759410283135079183509548536284359810897034420727299221258878019206982482768033307055738224278227886620891952781117849433373938078120432421021270423938804374806423207068262547182750834257932759947807453552075063613345094195899367225573311262785988431116453716899927301598393855339705075412224545546846419958845408510098508541234937869448551969505421647216471304666292278160110811149

private def offPrimeSumCoarse : ℚ := (offPrimeNum : ℚ) / (offPrimeDen : ℚ)
private def offPrimeSumCoarse_fast : ℚ := offPrimeSumCoarse

private lemma offPrimeDen_pos : 0 < offPrimeDen := by decide
private lemma offPrimeSumCoarse_eq_fast : offPrimeSumCoarse = offPrimeSumCoarse_fast := rfl

-- No-5 primes (p ≠ 5, includes p = 2)
private def no5PrimeDen : ℕ := 3349507336447318304180936831208874307086616988295574961159931463517299077942665857637478723599087911092968020228227998162457748729699648991861571140316539699793423956757830356522508943937708471188899645023163323318265776622349962610115629326744206081201868049930064109465914286785859494194817299215645194212193228640592326854906655870469885549141094576438798707784583513010605373189540307033792650118641412613498835189907040227236294239620097134798793956309316175899450161057093652728614203556945059335707573413218567092381872889018671667225510651771520646888403672826521437110978505288424642625926654276932311893128221277239440860127315822739974640290382159421407038949556690843528922560293434276515190262308548875714504142987112189527403491545131147749178941540491802147707616816508990377973144202451848510350516795325019480559771067686353092100331992948208549105709577561402814545060866393789209134725628561160207870107842936561168091388698520683642572177370556392425649634883582492334395656329971313875324723974610553504004286564942636631870466414696356404822879345049746862959229557927570392074490331243173269307978026582110889323143312864623857496291903120200476168831868116045190547452983239888358131744182459164193482403710212749127249537479622857766115605645817080348983771060620948668747978591088525141242218755472775128610718237131702035370306826223892382877653525222628045602018316569176767143040076943597912785443112355994992049630069278090825906436257142468390373321682807384625491870182710804726842255368776697580325647977799954298654000114169533883548462153421780081173793422283447122256212549952885578235982231922396307300511951754970258211163941425870561757855312356

private def no5PrimeNum : ℕ := 1380630434582714511193856433995070469925023999513261700716658565012298572083656525724967178461366191342688138002514433435094893140662515195478176523920040936707613384173403851179241916394921430392262551495752875139822075095283374214390867101747440324274349238922289600720996504607153250379052586883189480975709682644497874223618598547883522139586724790849262665981880684173002861792665605705949009329999135006890998848070738414557039779199791836840497618979487101867107714557558688677250807861052635471737821890821254058187484883062757864617651994331128373270949127126430321042974015865028393006606114281240077400320311961381566157024550723312814626758764354808816345731091635076905517279358846644402993474556080658331814918104384177841421747008966773981903858450940339142352769739312662038086455599809979370519243036187271928940749288288950015240414790706119305572485935035762002376330918101241581274553703167214040520553473268037610665989029186990676025897739865912296000038878832001337595418127598043420909108666055680662594501603391796112274640921788437413355985605166532131773101952914062961391592605882602422871210083206368837096029435479874641921386575383174652886383384537839519686825618669705761755801290195533619565437134580068606059350692942646142617350569043951911561699678756610852848384690809772417850871422906387927290118802871063191751773591591485172547343312377790239623457476255205738269327830360370875929856530401480477696492599015277923975834757113890147782061424038877887412758775491909481965017222570957992550314287695039718617224494357251070596321931930866379113750004469043967949732972869855434953029722920350554619335865960429153418676204021636753079907072685

private def no5PrimeSumCoarse : ℚ := (no5PrimeNum : ℚ) / (no5PrimeDen : ℚ)
private def no5PrimeSumCoarse_fast : ℚ := no5PrimeSumCoarse

private lemma no5PrimeDen_pos : 0 < no5PrimeDen := by decide
private lemma no5PrimeSumCoarse_eq_fast : no5PrimeSumCoarse = no5PrimeSumCoarse_fast := rfl

-- The symbolic sum equals the precomputed value.
private lemma diagPrimesCoarse_sum_eq :
    (∑ p ∈ diagPrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) = diagPrimeSumCoarse := by
  rw [diagPrimesCoarse_eq_list]
  simp
    [diagPrimesCoarse_list, diagPrimesCoarse_listL, diagPrimeSumCoarse, diagPrimeNum, diagPrimeDen]
  norm_num

private lemma no5PrimesCoarse_sum_eq :
    (∑ p ∈ no5PrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) = no5PrimeSumCoarse := by
  rw [no5PrimesCoarse_eq_list]
  simp
    [no5PrimesCoarse_list, no5PrimesCoarse_listL, no5PrimeSumCoarse, no5PrimeNum, no5PrimeDen]
  norm_num

private lemma offPrimeSumCoarse_eq_no5_sub :
    offPrimeSumCoarse = no5PrimeSumCoarse - (1 : ℚ) / 4 := by
  norm_num
    [offPrimeSumCoarse, no5PrimeSumCoarse, offPrimeNum, offPrimeDen, no5PrimeNum, no5PrimeDen]

private lemma offPrimesCoarse_sum_eq :
    (∑ p ∈ offPrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) = offPrimeSumCoarse := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hoff : offPrimesCoarse = no5PrimesCoarse.erase 2 := by
    ext p
    simp [offPrimesCoarse, no5PrimesCoarse, primesUpTo, and_left_comm, and_assoc]
  have h2 : 2 ∈ no5PrimesCoarse := by
    simp [no5PrimesCoarse, primesUpTo, primeCutoff, Nat.prime_two]
  have hsum := Finset.sum_erase_add (s := no5PrimesCoarse) (a := 2) (f := f) h2
  have hsum' := congrArg (fun x => x - f 2) hsum
  have hsum_erase :
      (∑ p ∈ no5PrimesCoarse.erase 2, f p) = (∑ p ∈ no5PrimesCoarse, f p) - f 2 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum'
  have hf2 : f 2 = (1 : ℚ) / 4 := by
    simp [f]
    norm_num
  rw [hoff]
  calc
    (∑ p ∈ no5PrimesCoarse.erase 2, f p)
        = (∑ p ∈ no5PrimesCoarse, f p) - (1 : ℚ) / 4 := by simp [hsum_erase, hf2]
    _ = no5PrimeSumCoarse - (1 : ℚ) / 4 := by
        simpa [f] using congrArg (fun x => x - (1 : ℚ) / 4) no5PrimesCoarse_sum_eq
    _ = offPrimeSumCoarse := by
        simp [offPrimeSumCoarse_eq_no5_sub]

/-!
We bound the *infinite* reciprocal-square sums by:
1) computing primes up to `primeCutoff` exactly,
2) bounding the tail by `∑_{i > B} 1/i^2 ≤ 1/B`.
-/

private lemma diagPrimeSumCoarse_bound :
    diagPrimeSumCoarse + (1 : ℚ) / primeCutoff ≤ (1 : ℚ) / 70 := by
  have hNat : 70 * (diagPrimeNum * primeCutoff + diagPrimeDen) ≤ diagPrimeDen * primeCutoff := by
    norm_num [primeCutoff, diagPrimeNum, diagPrimeDen]
  have hD_pos : (0 : ℚ) < diagPrimeDen := Nat.cast_pos.mpr diagPrimeDen_pos
  have hB_pos : (0 : ℚ) < primeCutoff := Nat.cast_pos.mpr primeCutoff_pos
  have hD_ne : (diagPrimeDen : ℚ) ≠ 0 := ne_of_gt hD_pos
  have hB_ne : (primeCutoff : ℚ) ≠ 0 := ne_of_gt hB_pos
  have h : (70 : ℚ) * ((diagPrimeNum : ℚ) * primeCutoff + diagPrimeDen) ≤
           (diagPrimeDen : ℚ) * primeCutoff := by exact_mod_cast hNat
  simp only [diagPrimeSumCoarse]
  have goal : (diagPrimeNum : ℚ) / diagPrimeDen + 1 / primeCutoff ≤ 1 / 70 := by
    have h70_pos : (0 : ℚ) < 70 := by norm_num
    rw [div_add_div _ _ hD_ne hB_ne, div_le_div_iff₀ (mul_pos hD_pos hB_pos) h70_pos]
    calc ((diagPrimeNum : ℚ) * primeCutoff + diagPrimeDen * 1) * 70
         = 70 * (diagPrimeNum * primeCutoff + diagPrimeDen) := by ring
       _ ≤ diagPrimeDen * primeCutoff := h
       _ = 1 * ((diagPrimeDen : ℚ) * primeCutoff) := by ring
  exact goal

private lemma offPrimeSumCoarse_bound :
    offPrimeSumCoarse + (1 : ℚ) / primeCutoff ≤ (163 : ℚ) / 1000 := by
  have hNat : 1000 * (offPrimeNum * primeCutoff + offPrimeDen) ≤ 163 * (offPrimeDen * primeCutoff) := by
    norm_num [primeCutoff, offPrimeNum, offPrimeDen]
  have hD_pos : (0 : ℚ) < offPrimeDen := Nat.cast_pos.mpr offPrimeDen_pos
  have hB_pos : (0 : ℚ) < primeCutoff := Nat.cast_pos.mpr primeCutoff_pos
  have hD_ne : (offPrimeDen : ℚ) ≠ 0 := ne_of_gt hD_pos
  have hB_ne : (primeCutoff : ℚ) ≠ 0 := ne_of_gt hB_pos
  have h : (1000 : ℚ) * ((offPrimeNum : ℚ) * primeCutoff + offPrimeDen) ≤
           163 * ((offPrimeDen : ℚ) * primeCutoff) := by exact_mod_cast hNat
  simp only [offPrimeSumCoarse]
  have goal : (offPrimeNum : ℚ) / offPrimeDen + 1 / primeCutoff ≤ 163 / 1000 := by
    have h1000_pos : (0 : ℚ) < 1000 := by norm_num
    rw [div_add_div _ _ hD_ne hB_ne, div_le_div_iff₀ (mul_pos hD_pos hB_pos) h1000_pos]
    calc ((offPrimeNum : ℚ) * primeCutoff + offPrimeDen * 1) * 1000
         = 1000 * (offPrimeNum * primeCutoff + offPrimeDen) := by ring
       _ ≤ 163 * (offPrimeDen * primeCutoff) := h
       _ = 163 * ((offPrimeDen : ℚ) * primeCutoff) := by ring
  exact goal

private lemma no5PrimeSumCoarse_bound :
    no5PrimeSumCoarse + (1 : ℚ) / primeCutoff ≤ (413 : ℚ) / 1000 := by
  have hNat : 1000 * (no5PrimeNum * primeCutoff + no5PrimeDen) ≤ 413 * (no5PrimeDen * primeCutoff) := by
    norm_num [primeCutoff, no5PrimeNum, no5PrimeDen]
  have hD_pos : (0 : ℚ) < no5PrimeDen := Nat.cast_pos.mpr no5PrimeDen_pos
  have hB_pos : (0 : ℚ) < primeCutoff := Nat.cast_pos.mpr primeCutoff_pos
  have hD_ne : (no5PrimeDen : ℚ) ≠ 0 := ne_of_gt hD_pos
  have hB_ne : (primeCutoff : ℚ) ≠ 0 := ne_of_gt hB_pos
  have h : (1000 : ℚ) * ((no5PrimeNum : ℚ) * primeCutoff + no5PrimeDen) ≤
           413 * ((no5PrimeDen : ℚ) * primeCutoff) := by exact_mod_cast hNat
  simp only [no5PrimeSumCoarse]
  have goal : (no5PrimeNum : ℚ) / no5PrimeDen + 1 / primeCutoff ≤ 413 / 1000 := by
    have h1000_pos : (0 : ℚ) < 1000 := by norm_num
    rw [div_add_div _ _ hD_ne hB_ne, div_le_div_iff₀ (mul_pos hD_pos hB_pos) h1000_pos]
    calc ((no5PrimeNum : ℚ) * primeCutoff + no5PrimeDen * 1) * 1000
         = 1000 * (no5PrimeNum * primeCutoff + no5PrimeDen) := by ring
       _ ≤ 413 * (no5PrimeDen * primeCutoff) := h
       _ = 413 * ((no5PrimeDen : ℚ) * primeCutoff) := by ring
  exact goal

-/

/-! ### Decomposed cutoff certificate

The eight intervals below partition `0 ≤ p ≤ 2000`.  Each list equality is
proved by kernel reduction with `decide`; no native evaluator or enlarged limit
is used.  The reciprocal-square estimates are separately normalized, keeping
both recursion depth and heartbeat use below their defaults.
-/

private def certNatToNum (n : ℕ) : Num := n

private lemma certNatToNum_toNat (n : ℕ) : ((certNatToNum n : Num) : ℕ) = n := by
  simp [certNatToNum]

private lemma certNatToNum_prime_iff (p : ℕ) :
    (certNatToNum p).Prime ↔ Nat.Prime p := by
  simp [Num.Prime, certNatToNum_toNat]

private def diagCertPred (p : ℕ) : Bool :=
  decide ((certNatToNum p).Prime ∧ p % 4 = 1 ∧ 13 ≤ p)

private def no5CertPred (p : ℕ) : Bool :=
  decide ((certNatToNum p).Prime ∧ p ≠ 5)

private lemma diagCertPred_eq_true_iff (p : ℕ) :
    diagCertPred p = true ↔ Nat.Prime p ∧ p % 4 = 1 ∧ 13 ≤ p := by
  simp only [diagCertPred, decide_eq_true_eq]
  simpa [certNatToNum_toNat]

private lemma no5CertPred_eq_true_iff (p : ℕ) :
    no5CertPred p = true ↔ Nat.Prime p ∧ p ≠ 5 := by
  simp only [no5CertPred, decide_eq_true_eq]
  simpa [certNatToNum_toNat]

private def certChunk (pred : ℕ → Bool) (lo len : ℕ) : Finset ℕ :=
  ((List.range' lo len).filter pred).toFinset

private lemma mem_range'_one_iff (p lo len : ℕ) :
    p ∈ List.range' lo len ↔ lo ≤ p ∧ p < lo + len := by
  simp only [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨p - lo, by omega, by omega⟩

private def diagChunk0L : List ℕ :=
  [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157,
    173, 181, 193, 197, 229, 233, 241]
private def diagChunk1L : List ℕ :=
  [257, 269, 277, 281, 293, 313, 317, 337, 349, 353, 373, 389, 397, 401, 409,
    421, 433, 449, 457, 461]
private def diagChunk2L : List ℕ :=
  [509, 521, 541, 557, 569, 577, 593, 601, 613, 617, 641, 653, 661, 673, 677,
    701, 709, 733]
private def diagChunk3L : List ℕ :=
  [757, 761, 769, 773, 797, 809, 821, 829, 853, 857, 877, 881, 929, 937, 941,
    953, 977, 997]
private def diagChunk4L : List ℕ :=
  [1009, 1013, 1021, 1033, 1049, 1061, 1069, 1093, 1097, 1109, 1117, 1129,
    1153, 1181, 1193, 1201, 1213, 1217, 1229, 1237, 1249]
private def diagChunk5L : List ℕ :=
  [1277, 1289, 1297, 1301, 1321, 1361, 1373, 1381, 1409, 1429, 1433, 1453,
    1481, 1489, 1493]
private def diagChunk6L : List ℕ :=
  [1549, 1553, 1597, 1601, 1609, 1613, 1621, 1637, 1657, 1669, 1693, 1697,
    1709, 1721, 1733, 1741]
private def diagChunk7L : List ℕ :=
  [1753, 1777, 1789, 1801, 1861, 1873, 1877, 1889, 1901, 1913, 1933, 1949,
    1973, 1993, 1997]

private def diagChunk0 : Finset ℕ := diagChunk0L.toFinset
private def diagChunk1 : Finset ℕ := diagChunk1L.toFinset
private def diagChunk2 : Finset ℕ := diagChunk2L.toFinset
private def diagChunk3 : Finset ℕ := diagChunk3L.toFinset
private def diagChunk4 : Finset ℕ := diagChunk4L.toFinset
private def diagChunk5 : Finset ℕ := diagChunk5L.toFinset
private def diagChunk6 : Finset ℕ := diagChunk6L.toFinset
private def diagChunk7 : Finset ℕ := diagChunk7L.toFinset

private lemma diagChunk0_cert : (List.range' 0 250).filter diagCertPred = diagChunk0L := by decide
private lemma diagChunk1_cert : (List.range' 250 250).filter diagCertPred = diagChunk1L := by decide
private lemma diagChunk2_cert : (List.range' 500 250).filter diagCertPred = diagChunk2L := by decide
private lemma diagChunk3_cert : (List.range' 750 250).filter diagCertPred = diagChunk3L := by decide
private lemma diagChunk4_cert : (List.range' 1000 250).filter diagCertPred = diagChunk4L := by decide
private lemma diagChunk5_cert : (List.range' 1250 250).filter diagCertPred = diagChunk5L := by decide
private lemma diagChunk6_cert : (List.range' 1500 250).filter diagCertPred = diagChunk6L := by decide
private lemma diagChunk7_cert : (List.range' 1750 251).filter diagCertPred = diagChunk7L := by decide

private lemma diagChunk0_spec : certChunk diagCertPred 0 250 = diagChunk0 := by
  simp [certChunk, diagChunk0, diagChunk0_cert]
private lemma diagChunk1_spec : certChunk diagCertPred 250 250 = diagChunk1 := by
  simp [certChunk, diagChunk1, diagChunk1_cert]
private lemma diagChunk2_spec : certChunk diagCertPred 500 250 = diagChunk2 := by
  simp [certChunk, diagChunk2, diagChunk2_cert]
private lemma diagChunk3_spec : certChunk diagCertPred 750 250 = diagChunk3 := by
  simp [certChunk, diagChunk3, diagChunk3_cert]
private lemma diagChunk4_spec : certChunk diagCertPred 1000 250 = diagChunk4 := by
  simp [certChunk, diagChunk4, diagChunk4_cert]
private lemma diagChunk5_spec : certChunk diagCertPred 1250 250 = diagChunk5 := by
  simp [certChunk, diagChunk5, diagChunk5_cert]
private lemma diagChunk6_spec : certChunk diagCertPred 1500 250 = diagChunk6 := by
  simp [certChunk, diagChunk6, diagChunk6_cert]
private lemma diagChunk7_spec : certChunk diagCertPred 1750 251 = diagChunk7 := by
  simp [certChunk, diagChunk7, diagChunk7_cert]

private lemma diagChunk0_bound :
    (∑ p ∈ diagChunk0, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (135074 : ℚ) / 10000000 := by
  simp [diagChunk0, diagChunk0L]
  norm_num
private lemma diagChunk1_bound :
    (∑ p ∈ diagChunk1, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (1693 : ℚ) / 10000000 := by
  simp [diagChunk1, diagChunk1L]
  norm_num
private lemma diagChunk2_bound :
    (∑ p ∈ diagChunk2, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (486 : ℚ) / 10000000 := by
  simp [diagChunk2, diagChunk2L]
  norm_num
private lemma diagChunk3_bound :
    (∑ p ∈ diagChunk3, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (248 : ℚ) / 10000000 := by
  simp [diagChunk3, diagChunk3L]
  norm_num
private lemma diagChunk4_bound :
    (∑ p ∈ diagChunk4, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (168 : ℚ) / 10000000 := by
  simp [diagChunk4, diagChunk4L]
  norm_num
private lemma diagChunk5_bound :
    (∑ p ∈ diagChunk5, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (79 : ℚ) / 10000000 := by
  simp [diagChunk5, diagChunk5L]
  norm_num
private lemma diagChunk6_bound :
    (∑ p ∈ diagChunk6, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (60 : ℚ) / 10000000 := by
  simp [diagChunk6, diagChunk6L]
  norm_num
private lemma diagChunk7_bound :
    (∑ p ∈ diagChunk7, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (43 : ℚ) / 10000000 := by
  simp [diagChunk7, diagChunk7L]
  norm_num

private def no5Chunk0L : List ℕ :=
  [2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241]
private def no5Chunk1L : List ℕ :=
  [251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
    347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431,
    433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499]
private def no5Chunk2L : List ℕ :=
  [503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601,
    607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691,
    701, 709, 719, 727, 733, 739, 743]
private def no5Chunk3L : List ℕ :=
  [751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853,
    857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
    967, 971, 977, 983, 991, 997]
private def no5Chunk4L : List ℕ :=
  [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
    1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
    1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249]
private def no5Chunk5L : List ℕ :=
  [1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321,
    1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439,
    1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499]
private def no5Chunk6L : List ℕ :=
  [1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597,
    1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
    1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747]
private def no5Chunk7L : List ℕ :=
  [1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861,
    1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949,
    1951, 1973, 1979, 1987, 1993, 1997, 1999]

private def no5Chunk0 : Finset ℕ := no5Chunk0L.toFinset
private def no5Chunk1 : Finset ℕ := no5Chunk1L.toFinset
private def no5Chunk2 : Finset ℕ := no5Chunk2L.toFinset
private def no5Chunk3 : Finset ℕ := no5Chunk3L.toFinset
private def no5Chunk4 : Finset ℕ := no5Chunk4L.toFinset
private def no5Chunk5 : Finset ℕ := no5Chunk5L.toFinset
private def no5Chunk6 : Finset ℕ := no5Chunk6L.toFinset
private def no5Chunk7 : Finset ℕ := no5Chunk7L.toFinset

private lemma no5Chunk0_cert : (List.range' 0 250).filter no5CertPred = no5Chunk0L := by decide
private lemma no5Chunk1_cert : (List.range' 250 250).filter no5CertPred = no5Chunk1L := by decide
private lemma no5Chunk2_cert : (List.range' 500 250).filter no5CertPred = no5Chunk2L := by decide
private lemma no5Chunk3_cert : (List.range' 750 250).filter no5CertPred = no5Chunk3L := by decide
private lemma no5Chunk4_cert : (List.range' 1000 250).filter no5CertPred = no5Chunk4L := by decide
private lemma no5Chunk5_cert : (List.range' 1250 250).filter no5CertPred = no5Chunk5L := by decide
private lemma no5Chunk6_cert : (List.range' 1500 250).filter no5CertPred = no5Chunk6L := by decide
private lemma no5Chunk7_cert : (List.range' 1750 251).filter no5CertPred = no5Chunk7L := by decide

private lemma no5Chunk0_spec : certChunk no5CertPred 0 250 = no5Chunk0 := by
  simp [certChunk, no5Chunk0, no5Chunk0_cert]
private lemma no5Chunk1_spec : certChunk no5CertPred 250 250 = no5Chunk1 := by
  simp [certChunk, no5Chunk1, no5Chunk1_cert]
private lemma no5Chunk2_spec : certChunk no5CertPred 500 250 = no5Chunk2 := by
  simp [certChunk, no5Chunk2, no5Chunk2_cert]
private lemma no5Chunk3_spec : certChunk no5CertPred 750 250 = no5Chunk3 := by
  simp [certChunk, no5Chunk3, no5Chunk3_cert]
private lemma no5Chunk4_spec : certChunk no5CertPred 1000 250 = no5Chunk4 := by
  simp [certChunk, no5Chunk4, no5Chunk4_cert]
private lemma no5Chunk5_spec : certChunk no5CertPred 1250 250 = no5Chunk5 := by
  simp [certChunk, no5Chunk5, no5Chunk5_cert]
private lemma no5Chunk6_spec : certChunk no5CertPred 1500 250 = no5Chunk6 := by
  simp [certChunk, no5Chunk6, no5Chunk6_cert]
private lemma no5Chunk7_spec : certChunk no5CertPred 1750 251 = no5Chunk7 := by
  simp [certChunk, no5Chunk7, no5Chunk7_cert]

private lemma no5Chunk0_bound :
    (∑ p ∈ no5Chunk0, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (4116338 : ℚ) / 10000000 := by
  simp [no5Chunk0, no5Chunk0L]
  norm_num
private lemma no5Chunk1_bound :
    (∑ p ∈ no5Chunk1, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (3405 : ℚ) / 10000000 := by
  simp [no5Chunk1, no5Chunk1L]
  norm_num
private lemma no5Chunk2_bound :
    (∑ p ∈ no5Chunk2, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (981 : ℚ) / 10000000 := by
  simp [no5Chunk2, no5Chunk2L]
  norm_num
private lemma no5Chunk3_bound :
    (∑ p ∈ no5Chunk3, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (483 : ℚ) / 10000000 := by
  simp [no5Chunk3, no5Chunk3L]
  norm_num
private lemma no5Chunk4_bound :
    (∑ p ∈ no5Chunk4, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (290 : ℚ) / 10000000 := by
  simp [no5Chunk4, no5Chunk4L]
  norm_num
private lemma no5Chunk5_bound :
    (∑ p ∈ no5Chunk5, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (184 : ℚ) / 10000000 := by
  simp [no5Chunk5, no5Chunk5L]
  norm_num
private lemma no5Chunk6_bound :
    (∑ p ∈ no5Chunk6, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (126 : ℚ) / 10000000 := by
  simp [no5Chunk6, no5Chunk6L]
  norm_num
private lemma no5Chunk7_bound :
    (∑ p ∈ no5Chunk7, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (89 : ℚ) / 10000000 := by
  simp [no5Chunk7, no5Chunk7L]
  norm_num

private def diagChunks : Finset ℕ :=
  ((((((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) ∪ diagChunk3) ∪ diagChunk4) ∪
    diagChunk5) ∪ diagChunk6) ∪ diagChunk7

private def no5Chunks : Finset ℕ :=
  ((((((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) ∪ no5Chunk3) ∪ no5Chunk4) ∪
    no5Chunk5) ∪ no5Chunk6) ∪ no5Chunk7

private lemma diagPrimesCoarse_eq_chunks : diagPrimesCoarse = diagChunks := by
  ext p
  simp only [diagPrimesCoarse, primesUpTo, Finset.mem_filter, Finset.mem_range,
    diagChunks, Finset.mem_union, ← diagChunk0_spec, ← diagChunk1_spec,
    ← diagChunk2_spec, ← diagChunk3_spec, ← diagChunk4_spec, ← diagChunk5_spec,
    ← diagChunk6_spec, ← diagChunk7_spec, certChunk, List.mem_toFinset,
    List.mem_filter]
  simp only [diagCertPred_eq_true_iff, mem_range'_one_iff, primeCutoff]
  by_cases hp : Nat.Prime p <;>
    by_cases hm : p % 4 = 1 <;>
      by_cases h13 : 13 ≤ p <;> simp_all <;> omega

private lemma no5PrimesCoarse_eq_chunks : no5PrimesCoarse = no5Chunks := by
  ext p
  simp only [no5PrimesCoarse, primesUpTo, Finset.mem_filter, Finset.mem_range,
    no5Chunks, Finset.mem_union, ← no5Chunk0_spec, ← no5Chunk1_spec,
    ← no5Chunk2_spec, ← no5Chunk3_spec, ← no5Chunk4_spec, ← no5Chunk5_spec,
    ← no5Chunk6_spec, ← no5Chunk7_spec, certChunk, List.mem_toFinset,
    List.mem_filter]
  simp only [no5CertPred_eq_true_iff, mem_range'_one_iff, primeCutoff]
  by_cases hp : Nat.Prime p <;>
    by_cases h5 : p = 5 <;> simp_all <;> omega

private lemma diagPrimesCoarse_sum_le :
    (∑ p ∈ diagPrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) ≤
      (137851 : ℚ) / 10000000 := by
  have hd1 : Disjoint diagChunk0 diagChunk1 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd2 : Disjoint (diagChunk0 ∪ diagChunk1) diagChunk2 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd3 : Disjoint ((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) diagChunk3 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      ← diagChunk3_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd4 :
      Disjoint (((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) ∪ diagChunk3) diagChunk4 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      ← diagChunk3_spec, ← diagChunk4_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd5 : Disjoint
      ((((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) ∪ diagChunk3) ∪ diagChunk4)
      diagChunk5 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      ← diagChunk3_spec, ← diagChunk4_spec, ← diagChunk5_spec,
      Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd6 : Disjoint
      (((((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) ∪ diagChunk3) ∪ diagChunk4) ∪
        diagChunk5) diagChunk6 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      ← diagChunk3_spec, ← diagChunk4_spec, ← diagChunk5_spec,
      ← diagChunk6_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd7 : Disjoint
      ((((((diagChunk0 ∪ diagChunk1) ∪ diagChunk2) ∪ diagChunk3) ∪ diagChunk4) ∪
        diagChunk5) ∪ diagChunk6) diagChunk7 := by
    rw [← diagChunk0_spec, ← diagChunk1_spec, ← diagChunk2_spec,
      ← diagChunk3_spec, ← diagChunk4_spec, ← diagChunk5_spec,
      ← diagChunk6_spec, ← diagChunk7_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  rw [diagPrimesCoarse_eq_chunks]
  unfold diagChunks
  rw [Finset.sum_union hd7, Finset.sum_union hd6, Finset.sum_union hd5,
    Finset.sum_union hd4, Finset.sum_union hd3, Finset.sum_union hd2,
    Finset.sum_union hd1]
  linarith [diagChunk0_bound, diagChunk1_bound, diagChunk2_bound,
    diagChunk3_bound, diagChunk4_bound, diagChunk5_bound, diagChunk6_bound,
    diagChunk7_bound]

private lemma no5PrimesCoarse_sum_le :
    (∑ p ∈ no5PrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) ≤
      (4121896 : ℚ) / 10000000 := by
  have hd1 : Disjoint no5Chunk0 no5Chunk1 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd2 : Disjoint (no5Chunk0 ∪ no5Chunk1) no5Chunk2 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd3 : Disjoint ((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) no5Chunk3 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      ← no5Chunk3_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd4 : Disjoint (((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) ∪ no5Chunk3)
      no5Chunk4 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      ← no5Chunk3_spec, ← no5Chunk4_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd5 : Disjoint
      ((((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) ∪ no5Chunk3) ∪ no5Chunk4)
      no5Chunk5 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      ← no5Chunk3_spec, ← no5Chunk4_spec, ← no5Chunk5_spec,
      Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd6 : Disjoint
      (((((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) ∪ no5Chunk3) ∪ no5Chunk4) ∪
        no5Chunk5) no5Chunk6 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      ← no5Chunk3_spec, ← no5Chunk4_spec, ← no5Chunk5_spec,
      ← no5Chunk6_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  have hd7 : Disjoint
      ((((((no5Chunk0 ∪ no5Chunk1) ∪ no5Chunk2) ∪ no5Chunk3) ∪ no5Chunk4) ∪
        no5Chunk5) ∪ no5Chunk6) no5Chunk7 := by
    rw [← no5Chunk0_spec, ← no5Chunk1_spec, ← no5Chunk2_spec,
      ← no5Chunk3_spec, ← no5Chunk4_spec, ← no5Chunk5_spec,
      ← no5Chunk6_spec, ← no5Chunk7_spec, Finset.disjoint_left]
    intro p hp hq
    simp [certChunk, List.mem_range'] at hp hq
    omega
  rw [no5PrimesCoarse_eq_chunks]
  unfold no5Chunks
  rw [Finset.sum_union hd7, Finset.sum_union hd6, Finset.sum_union hd5,
    Finset.sum_union hd4, Finset.sum_union hd3, Finset.sum_union hd2,
    Finset.sum_union hd1]
  linarith [no5Chunk0_bound, no5Chunk1_bound, no5Chunk2_bound,
    no5Chunk3_bound, no5Chunk4_bound, no5Chunk5_bound, no5Chunk6_bound,
    no5Chunk7_bound]

lemma sum_Ioc_inv_sq_le_inv (B N : ℕ) (hB : B ≠ 0) :
    (∑ i ∈ Finset.Ioc B N, (1 : ℚ) / (i ^ 2 : ℚ)) ≤ (1 : ℚ) / B := by
  by_cases hBN : B < N
  · have hle : B ≤ N := Nat.le_of_lt hBN
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℚ) (k := B) (n := N) hB hle
    have hnonneg : 0 ≤ (N : ℚ)⁻¹ := by positivity
    -- `B⁻¹ - N⁻¹ ≤ B⁻¹`
    have hsub' : (B : ℚ)⁻¹ - (N : ℚ)⁻¹ ≤ (B : ℚ)⁻¹ := sub_le_self _ hnonneg
    -- rewrite inverses as `1 / _`
    simpa [one_div] using hsub.trans hsub'
  · have hIoc : (Finset.Ioc B N) = ∅ := by
      apply Finset.Ioc_eq_empty
      exact not_lt.2 (Nat.le_of_not_gt hBN)
    simp [hIoc, one_div]

def diagPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 5)

/-- Helper: (N-1)² + 1 < N² for N ≥ 2. -/
lemma sq_pred_add_one_lt_sq (N : ℕ) (hN : 100 ≤ N) : (N - 1) * (N - 1) + 1 < N ^ 2 := by
  have h2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 100) hN
  have h1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) h2
  -- Expand using N = (N-1) + 1
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
  -- N^2 = ((N-1)+1)^2 = (N-1)^2 + 2(N-1) + 1
  -- So (N-1)^2 + 1 < (N-1)^2 + 2(N-1) + 1 = N^2 when N-1 > 0
  have hpos : 0 < N - 1 := by omega
  calc (N - 1) * (N - 1) + 1
      < (N - 1) * (N - 1) + 2 * (N - 1) + 1 := by omega
    _ = (N - 1 + 1) * (N - 1 + 1) := by ring
    _ = N * N := by rw [hsub]
    _ = N ^ 2 := by rw [Nat.pow_two]

/- Superseded monolithic uses of the inactive exact fractions.

lemma sum_diagPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (1 : ℚ) / 70 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : diagPrimesUpTo N ⊆ diagPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p % 4 = 1 ∧ 13 ≤ p := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ diagPrimesCoarse := by
        simp [diagPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint diagPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ ∑ p ∈ diagPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
        diagPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
          ∑ p ∈ diagPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ diagPrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = diagPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, diagPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ diagPrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail diagPrimeSumCoarse)
  exact hsum_le'.trans diagPrimeSumCoarse_bound

-- Placeholders for the remaining prime-sum bounds; used in the final casework.
lemma sum_offPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (163 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : offPrimesUpTo N ⊆ offPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 2 ∧ p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ offPrimesCoarse := by
        simp [offPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint offPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ offPrimesUpTo N, f p) ≤
        offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ offPrimesUpTo N, f p) ≤
          ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ offPrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, offPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ offPrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail offPrimeSumCoarse)
  exact hsum_le'.trans offPrimeSumCoarse_bound

lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_mem_cutoff, hp_cond]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
          ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ no5PrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, no5PrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ no5PrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail no5PrimeSumCoarse)
  exact hsum_le'.trans no5PrimeSumCoarse_bound

-/

lemma sum_diagPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (1 : ℚ) / 70 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : diagPrimesUpTo N ⊆ diagPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p % 4 = 1 ∧ 13 ≤ p := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range := (Finset.mem_filter.1 hp_mem).1
      exact Nat.le_of_lt_succ (Finset.mem_range.1 hp_range)
    by_cases hp_le : p ≤ primeCutoff
    ·
      have hp_cut : p ∈ primesUpTo primeCutoff := by
        simp [primesUpTo, Nat.lt_succ_of_le hp_le, hp_prime]
      have hcoarse : p ∈ diagPrimesCoarse := by
        simp [diagPrimesCoarse, hp_cut, hp_cond]
      exact Finset.mem_union.2 (Or.inl hcoarse)
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_Ioc.2 ⟨lt_of_not_ge hp_le, hp_le_N⟩))
  have hdisj : Disjoint diagPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp htail
    have hp0 := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    have hp_le : p ≤ primeCutoff := Nat.le_of_lt_succ (Finset.mem_range.1 hp0)
    exact (not_lt_of_ge hp_le) (Finset.mem_Ioc.1 htail).1
  have hunion :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
        ∑ p ∈ diagPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _ _
    positivity
  have htail :
      (∑ p ∈ Finset.Ioc primeCutoff N, f p) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by norm_num [primeCutoff])
  calc
    (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ))
        ≤ (∑ p ∈ diagPrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) +
            ∑ p ∈ Finset.Ioc primeCutoff N, (1 : ℚ) / (p ^ 2 : ℚ) := by
          simpa [f, Finset.sum_union hdisj] using hunion
    _ ≤ (137851 : ℚ) / 10000000 + (1 : ℚ) / primeCutoff :=
      add_le_add diagPrimesCoarse_sum_le htail
    _ ≤ (1 : ℚ) / 70 := by norm_num [primeCutoff]

lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_ne5 : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range := (Finset.mem_filter.1 hp_mem).1
      exact Nat.le_of_lt_succ (Finset.mem_range.1 hp_range)
    by_cases hp_le : p ≤ primeCutoff
    ·
      have hp_cut : p ∈ primesUpTo primeCutoff := by
        simp [primesUpTo, Nat.lt_succ_of_le hp_le, hp_prime]
      have hcoarse : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_cut, hp_ne5]
      exact Finset.mem_union.2 (Or.inl hcoarse)
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_Ioc.2 ⟨lt_of_not_ge hp_le, hp_le_N⟩))
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp htail
    have hp0 := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    have hp_le : p ≤ primeCutoff := Nat.le_of_lt_succ (Finset.mem_range.1 hp0)
    exact (not_lt_of_ge hp_le) (Finset.mem_Ioc.1 htail).1
  have hunion :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _ _
    positivity
  have htail :
      (∑ p ∈ Finset.Ioc primeCutoff N, f p) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by norm_num [primeCutoff])
  calc
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ))
        ≤ (∑ p ∈ no5PrimesCoarse, (1 : ℚ) / (p ^ 2 : ℚ)) +
            ∑ p ∈ Finset.Ioc primeCutoff N, (1 : ℚ) / (p ^ 2 : ℚ) := by
          simpa [f, Finset.sum_union hdisj] using hunion
    _ ≤ (4121896 : ℚ) / 10000000 + (1 : ℚ) / primeCutoff :=
      add_le_add no5PrimesCoarse_sum_le htail
    _ ≤ (413 : ℚ) / 1000 := by norm_num [primeCutoff]

lemma sum_offPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (163 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hoff : offPrimesUpTo N = (no5PrimesUpTo N).erase 2 := by
    ext p
    simp [offPrimesUpTo, no5PrimesUpTo, and_left_comm, and_assoc]
  by_cases hN : 2 ≤ N
  · have h2 : 2 ∈ no5PrimesUpTo N := by
      simp [no5PrimesUpTo, primesUpTo, Nat.prime_two, Nat.lt_succ_of_le hN]
    have herase := Finset.sum_erase_add (s := no5PrimesUpTo N) (a := 2) (f := f) h2
    have hsum_no5 := sum_no5PrimesUpTo_le N
    have hf2 : f 2 = (1 : ℚ) / 4 := by norm_num [f]
    rw [hoff]
    have heq : (∑ p ∈ (no5PrimesUpTo N).erase 2, f p) =
        (∑ p ∈ no5PrimesUpTo N, f p) - f 2 := by linarith
    rw [heq, hf2]
    simpa [f] using (show (∑ p ∈ no5PrimesUpTo N, f p) - (1 : ℚ) / 4 ≤
        (163 : ℚ) / 1000 by linarith [hsum_no5])
  · have hempty : offPrimesUpTo N = ∅ := by
      ext p
      constructor
      · intro hp
        have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
        have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
        have hp_le : p ≤ N :=
          Nat.le_of_lt_succ (Finset.mem_range.1 (Finset.mem_filter.1 hp_mem).1)
        exact (hN (hp_prime.two_le.trans hp_le)).elim
      · intro hp
        simp at hp
    norm_num [hempty]

lemma sum_diagPrimesUpTo_le_real (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 : ℝ) / 70 := by
  have hQ := sum_diagPrimesUpTo_le N
  have hR := Rat.cast_le (K := ℝ).mpr hQ
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast] at hR
  linarith

lemma sum_no5PrimesUpTo_le_real (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (413 : ℝ) / 1000 := by
  have hQ := sum_no5PrimesUpTo_le N
  have hR := Rat.cast_le (K := ℝ).mpr hQ
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast] at hR
  linarith

lemma sum_offPrimesUpTo_le_real (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (163 : ℝ) / 1000 := by
  have hQ := sum_offPrimesUpTo_le N
  have hR := Rat.cast_le (K := ℝ).mpr hQ
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast] at hR
  linarith

lemma sum_diagPrimesUpTo_div25_le_real (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
      (1 : ℝ) / 1750 := by
  calc
    (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
        (1 / 25 : ℝ) * ∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
    _ ≤ (1 / 25 : ℝ) * ((1 : ℝ) / 70) :=
      mul_le_mul_of_nonneg_left (sum_diagPrimesUpTo_le_real N) (by positivity)
    _ = (1 : ℝ) / 1750 := by norm_num

lemma sum_diagPrimesUpTo_div50_le_real (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤
      (1 : ℝ) / 3500 := by
  calc
    (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) =
        (1 / 50 : ℝ) * ∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
    _ ≤ (1 / 50 : ℝ) * ((1 : ℝ) / 70) :=
      mul_le_mul_of_nonneg_left (sum_diagPrimesUpTo_le_real N) (by positivity)
    _ = (1 : ℝ) / 3500 := by norm_num

lemma sum_no5PrimesUpTo_div25_le_real (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
      (413 : ℝ) / 25000 := by
  calc
    (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
        (1 / 25 : ℝ) * ∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
    _ ≤ (1 / 25 : ℝ) * ((413 : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left (sum_no5PrimesUpTo_le_real N) (by positivity)
    _ = (413 : ℝ) / 25000 := by norm_num

lemma sum_offPrimesUpTo_div25_le_real (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
      (163 : ℝ) / 25000 := by
  calc
    (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
        (1 / 25 : ℝ) * ∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
    _ ≤ (1 / 25 : ℝ) * ((163 : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left (sum_offPrimesUpTo_le_real N) (by positivity)
    _ = (163 : ℝ) / 25000 := by norm_num

lemma sum_offPrimesUpTo_div100_le_real (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤
      (163 : ℝ) / 100000 := by
  calc
    (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) =
        (1 / 100 : ℝ) * ∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
    _ ≤ (1 / 100 : ℝ) * ((163 : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left (sum_offPrimesUpTo_le_real N) (by positivity)
    _ = (163 : ℝ) / 100000 := by norm_num

private lemma mixed_case_numerical_contradiction
    {δ Cno5 Coff N total no5Part offPart star : ℝ}
    (hδ : δ = 1 / 10000000) (hCno5 : Cno5 = 413 / 25000)
    (hCoff : Coff = 163 / 25000) (hN : 0 < N)
    (hparts : total ≤ no5Part + offPart + star)
    (hstar : star ≤ 46 * (N / 3500 + δ * N))
    (hno5 : no5Part ≤ N * Cno5 + δ * N)
    (hoff : offPart ≤ N * Coff + δ * N) :
    total < (1 / 25 - 1 / 2000) * N := by
  subst δ
  subst Cno5
  subst Coff
  nlinarith

private lemma absorb_two_into_prime_error {δ : ℝ} {N : ℕ}
    (hδ : δ = 1 / 10000000) (hN : 10000000 ≤ N) :
    (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) ≤
      (N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 4 * δ * (N : ℝ) := by
  subst δ
  have hNR : (10000000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith

private lemma all_odd_case_numerical_contradiction
    {δ N total parts star : ℝ} (hδ : δ = 1 / 10000000) (hN : 0 < N)
    (hparts : total ≤ parts + star)
    (hstar : star ≤ 46 * (N / 3500 + δ * N))
    (h78 : parts ≤ N / 50 + 2 * N * (163 / 100000) + 4 * δ * N) :
    total < (1 / 25 - 1 / 2000) * N := by
  subst δ
  nlinarith

-- =========================================================================
-- SECTION 9.8: BRIDGES (prime counting + residue-class counting)
-- =========================================================================

def residues25 : Finset ℕ :=
  (Finset.range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

lemma residues25_card : residues25.card = 23 := by
  decide

def residues50odd : Finset ℕ :=
  (Finset.range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

lemma residues50odd_card : residues50odd.card = 23 := by
  decide

lemma primesUpTo_card (B : ℕ) : (primesUpTo B).card = B.primeCounting := by
  classical
  simp [primesUpTo, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

lemma cast_nat_div_le_rat (N m : ℕ) (hm : 0 < m) : ((N / m : ℕ) : ℚ) ≤ (N : ℚ) / m := by
  have hmul : (N / m) * m ≤ N := Nat.div_mul_le_self N m
  have hmulQ : ((N / m : ℕ) : ℚ) * (m : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast hmul
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have := (le_div_iff₀ hmQ).2 hmulQ
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

lemma prime_eq_of_dvd_2 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 2) : p = 2 := by
  have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  omega

lemma prime_eq_of_dvd_5 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 5) : p = 5 := by
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> simp_all

lemma coprime_25_pow_two_of_prime_ne5 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    Nat.Coprime 25 (p ^ 2) := by
  have hnot : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := by
      have : (5 ^ 2 : ℕ) = 25 := by rfl
      simpa [this] using h
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
    exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 25) (m := 2) hnot

lemma coprime_100_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 100 (p ^ 2) := by
  have hnot : ¬ p ∣ 100 := by
    intro h
    have hpow : p ∣ 10 ^ 2 := by
      have : (10 ^ 2 : ℕ) = 100 := by rfl
      simpa [this] using h
    have h10 : p ∣ 10 := hp.dvd_of_dvd_pow hpow
    have hmul : p ∣ 2 ∨ p ∣ 5 := by
      have : 10 = 2 * 5 := by rfl
      simpa [this] using (hp.dvd_mul.1 (by simpa [this] using h10))
    cases hmul with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h5 => exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 100) (m := 2) hnot

lemma exists_primeCounting_le_mul_nat (δ : ℝ) (δpos : 0 < δ) :
    ∃ N0 : ℕ, ∀ N ≥ N0, (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊.primeCounting : ℝ) ≤ δ * x) := by
    have hcheb := Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) (by norm_num)
    let C : ℝ := Real.log 4 + (1 : ℝ)
    have hlogBig : ∀ᶠ x : ℝ in atTop, C / δ ≤ Real.log x :=
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (C / δ)))
    have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
    filter_upwards [hcheb, hlogBig, hxpos] with x hxcheb hxlog hxpos
    have hlogpos : 0 < Real.log x := by
      have hCpos : 0 < C / δ := by
        have hlog4pos : 0 < Real.log 4 := by
          have : (1 : ℝ) < 4 := by norm_num
          exact Real.log_pos this
        have hCpos0 : 0 < C := by dsimp [C]; linarith
        exact div_pos hCpos0 δpos
      exact lt_of_lt_of_le hCpos hxlog
    have hC_over_log : C / Real.log x ≤ δ := by
      have hC_le : C ≤ δ * Real.log x := by
        have := mul_le_mul_of_nonneg_left hxlog (le_of_lt δpos)
        have hmul : δ * (C / δ) = C := by field
        simpa [hmul, mul_assoc] using this
      have := (div_le_iff₀ hlogpos).2 hC_le
      simpa [div_eq_mul_inv, mul_left_comm, mul_comm] using this
    have hmain : C * x / Real.log x ≤ δ * x := by
      have : C * x / Real.log x = (C / Real.log x) * x := by
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]
      calc
        C * x / Real.log x = (C / Real.log x) * x := this
        _ ≤ δ * x := by
          exact mul_le_mul_of_nonneg_right hC_over_log (le_of_lt hxpos)
    exact le_trans hxcheb hmain
  rcases (eventually_atTop.mp hreal) with ⟨R, hR⟩
  let N0 : ℕ := Nat.ceil R
  refine ⟨N0, ?_⟩
  intro N hN
  have hRN : (R : ℝ) ≤ (N : ℝ) := by
    have hceil : (Nat.ceil R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hRceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    linarith
  simpa using hR (N : ℝ) hRN

lemma prime_square_exists {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ n := by
    intro hall
    exact hn ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push_neg at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  refine ⟨p, hp, ?_⟩
  simpa [pow_two] using hpp

lemma prime_square_exists_ne5 {n : ℕ} (hn : ¬ Squarefree n) (h25 : ¬ 25 ∣ n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hp2⟩ := prime_square_exists (n := n) hn
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ n := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma cross_residue_7_18_not_div_25 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) :
    ¬ (25 ∣ a * b + 1) := by
  have hb_ne : b % 25 ≠ 7 := by
    intro hb7
    have : (18 : ℕ) = 7 := hb.symm.trans hb7
    exact (by decide : (18 : ℕ) ≠ 7) this
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb_ne

lemma cross_residue_18_7_not_div_25 (a b : ℕ) (ha : a % 25 = 18) (hb : b % 25 = 7) :
    ¬ (25 ∣ a * b + 1) := by
  -- commutativity reduces to previous lemma
  simpa [Nat.mul_comm] using cross_residue_7_18_not_div_25 b a hb ha

lemma off_count_modEq25_le (N p b t : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    haveI : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset :
      (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard := Finset.card_le_card hsubset
  exact le_trans hcard (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r hcop)

private lemma not_sq_dvd_mul_add_one_of_prime_dvd_left
    {p b a : ℕ} (hp : Nat.Prime p) (hb : p ∣ b) : ¬ p ^ 2 ∣ b * a + 1 := by
  intro hp2
  have hp1 : p ∣ b * a + 1 := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2
  have hpa : p ∣ b * a := dvd_mul_of_dvd_left hb a
  have : p ∣ 1 := (Nat.dvd_add_right hpa).mp hp1
  exact hp.not_dvd_one this

/-- If `p ∣ b`, then `p^2 ∣ b*a+1` is impossible, so the corresponding filter is empty. -/
lemma filter_empty_of_prime_dvd_left {N p b : ℕ} (hp : Nat.Prime p) (hb : p ∣ b) :
    (Finset.range N).filter (fun a => p ^ 2 ∣ b * a + 1) = ∅ := by
  classical
  ext a
  simp [not_sq_dvd_mul_add_one_of_prime_dvd_left (p := p) (b := b) (a := a) hp hb]

lemma filter_empty_of_prime_dvd_left_of_pred
    {N p b : ℕ} (hp : Nat.Prime p) (hb : p ∣ b)
    (pred : ℕ → Prop) [DecidablePred pred] :
    (Finset.range N).filter (fun a => pred a ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
  classical
  ext a
  simp [not_sq_dvd_mul_add_one_of_prime_dvd_left (p := p) (b := b) (a := a) hp hb]

/-- Variant of off_count_modEq25_le that works even when p | b (filter is empty in that case). -/
lemma off_count_modEq25_le' (N p b t : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · -- If p | b, the filter is empty (p ∤ b*a+1)
    have hempty :
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t [MOD 25]))
    simp [hempty]
  · exact off_count_modEq25_le N p b t hp hb hp5

lemma off_count_modEq100_le (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  classical
  have hcop25_4 : Nat.Coprime 25 4 := by decide
  -- first combine mod 25 and mod 4 into mod 100
  have hsub :
      (Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2.2⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop25_4) ha.2.1 ha.2.2.1
  have hcard :
      ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card :=
    Finset.card_le_card hsub
  -- now apply the mod 25 bound with modulus 100 instead of 25
  have hcop : Nat.Coprime 100 (p ^ 2) := coprime_100_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  -- reuse off_count_modEq25_le by replacing 25 with 100 via card_filter_modEq_and_modEq_le
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    haveI : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset2 :
      (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard2 :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card :=
    Finset.card_le_card hsubset2
  have hfinal :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card ≤
        N / (100 * p ^ 2) + 1 := by
    -- rewrite as CRT count mod 100 and mod p^2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 100 (p ^ 2) (Nat.chineseRemainder hcop25_4 t25 t4) r hcop)
  exact le_trans (le_trans hcard hcard2) hfinal

/-- Variant of off_count_modEq100_le that works even when p | b (filter is empty in that case). -/
lemma off_count_modEq100_le' (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · -- If p | b, the filter is empty (p ∤ b*a+1)
    have hempty :
        (Finset.range N).filter
            (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa [and_assoc] using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4]))
    simp [hempty]
  · exact off_count_modEq100_le N p b t25 t4 hp hb hp2 hp5

-- =========================================================================
-- SECTION 9.9: SMALL MODULAR FACTS (proved by computation)
-- =========================================================================

lemma prime_ge_13_of_mod4_one_ne5 (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    13 ≤ p := by
  have hp_ge2 : 2 ≤ p := hp.two_le
  by_contra h
  have hp_le12 : p ≤ 12 := by
    have hp_lt13 : p < 13 := lt_of_not_ge h
    have : p < 12 + 1 := by simpa using hp_lt13
    exact (Nat.lt_succ_iff).1 this
  interval_cases p <;> simp_all +decide

lemma prime_not_dvd_left_of_sq_dvd_mul_add_one {p a b : ℕ} (hp : Nat.Prime p) (h : p ^ 2 ∣ a * b + 1) :
    ¬ p ∣ a := by
  intro hpa
  have hp_dvd_ab : p ∣ a * b := dvd_mul_of_dvd_left hpa b
  have hp_dvd_ab1 : p ∣ a * b + 1 := by
    have hp_dvd_p2 : p ∣ p ^ 2 := by simp [pow_two]
    exact Nat.dvd_trans hp_dvd_p2 h
  have : p ∣ (a * b + 1) - (a * b) := Nat.dvd_sub hp_dvd_ab1 hp_dvd_ab
  have : p ∣ 1 := by simpa using this
  exact hp.not_dvd_one this

lemma coprime_50_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 50 (p ^ 2) := by
  have hnot : ¬ p ∣ 50 := by
    intro h
    have hmul : p ∣ 2 * 25 := by
      have : 2 * 25 = 50 := by rfl
      simpa [this] using h
    have hdiv : p ∣ 2 ∨ p ∣ 25 := hp.dvd_mul.1 hmul
    cases hdiv with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h25 =>
        have hpow : p ∣ 5 ^ 2 := by
          have : (5 ^ 2 : ℕ) = 25 := by rfl
          simpa [this] using h25
        have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
        exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 50) (m := 2) hnot

lemma diag_count_modEq25_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (25 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    simpa using two_roots_mod_p_squared p hp hmod
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (25 * p ^ 2) + 1) + (N / (25 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_modEq50_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (50 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 50 (p ^ 2) := coprime_50_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    simpa using two_roots_mod_p_squared p hp hmod
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (50 * p ^ 2) + 1) + (N / (50 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_mod25_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (25 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues25.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 25
    have ht : t ∈ residues25 := by
      have htlt : t < 25 := Nat.mod_lt n (by decide : 0 < 25)
      have htne : t ≠ 7 ∧ t ≠ 18 := by
        refine ⟨?_, ?_⟩
        · simpa [t] using hn.2.1
        · simpa [t] using hn.2.2.1
      simp [residues25, Finset.mem_filter, Finset.mem_range, t, htlt, htne]
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2]
    -- `n ≡ n % 25 [MOD 25]`
    simpa [t] using (Nat.mod_modEq n 25).symm
  have hcard : S.card ≤ (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues25,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (25 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq25_le N p t hp hmod hp5
  have hsum' :
      (∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = 46 * (N / (25 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = residues25.card * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp [residues25_card]
      _ = 46 * (N / (25 * p ^ 2) + 1) := by
        rw [← Nat.mul_assoc]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

lemma diag_count_mod50odd_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (50 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues50odd.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 50
    have ht : t ∈ residues50odd := by
      have htlt : t < 50 := Nat.mod_lt n (by decide : 0 < 50)
      have htodd : t % 2 = 1 := by
        have : (n % 50) % 2 = n % 2 := by
          simp [show 50 = 25 * 2 by rfl]
        simpa [t, this] using hn.2.1
      have htne7 : t % 25 ≠ 7 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne7 : n % 25 ≠ 7 := hn.2.2.1
        simpa [t, this] using hnne7
      have htne18 : t % 25 ≠ 18 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne18 : n % 25 ≠ 18 := hn.2.2.2.1
        simpa [t, this] using hnne18
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.2 htlt
      · exact ⟨htodd, htne7, htne18⟩
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2.2]
    simpa [t] using (Nat.mod_modEq n 50).symm
  have hcard : S.card ≤ (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues50odd,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (50 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq50_le N p t hp hmod hp2 hp5
  have hsum' :
      (∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = 46 * (N / (50 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = residues50odd.card * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp [residues50odd_card]
      _ = 46 * (N / (50 * p ^ 2) + 1) := by
        rw [← Nat.mul_assoc]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

-- ============================================================================
-- SECTION 9.95: GENERIC SIEVE CARDINALITY BOUNDS
-- ============================================================================

/-- If `p^2 ∣ X` and `0 < X < N^2`, then `p ≤ N`. -/
lemma prime_le_of_sq_dvd_lt_sq {p N X : ℕ} (hXpos : 0 < X) (hXlt : X < N ^ 2) (hp2 : p ^ 2 ∣ X) : p ≤ N := by
  have hp2_le : p ^ 2 ≤ X := Nat.le_of_dvd hXpos hp2
  have hp2_lt : p ^ 2 < N ^ 2 := lt_of_le_of_lt hp2_le hXlt
  by_contra hp_le
  have hNp : N ≤ p := le_of_lt (Nat.not_le.mp hp_le)
  have hN2le : N ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hNp 2
  exact (not_lt_of_ge hN2le) hp2_lt

/-- If `p^2 ∣ n` and `n` is odd, then `p ≠ 2`. -/
lemma prime_ne_two_of_sq_dvd_odd {p n : ℕ} (hn : n % 2 = 1) (hp2 : p ^ 2 ∣ n) : p ≠ 2 := by
  intro hp
  subst hp
  have h4 : 4 ∣ n := by simpa using hp2
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega

/-- `∑ (N/(k*p²)+1)` is bounded by `N * ∑ 1/(k*p²) + |P|` after casting to `ℝ`. -/
lemma sum_div_add_one_le_real (N : ℕ) (P : Finset ℕ) (k : ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hsplit :
      ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
    have :
        (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
          (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
      simp [Finset.sum_add_distrib]
    exact_mod_cast this
  have hterm :
      ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    intro p hp
    have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := k * p ^ 2))
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
  have hdiv' :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
  have hdiv :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
    have :
        (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
      simp [div_eq_mul_inv, mul_sum, mul_comm]
    exact hdiv'.trans (le_of_eq this)
  have h := add_le_add_right hdiv (P.card : ℝ)
  calc
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
    _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using h

/--
Bound the cardinality of a set `S` contained in a union of sieve classes.

If `S ⊆ ⋃_{p ∈ P} {n < N | pred p n}` and each class has size at most
`N/(k*p²)+1`, then `|S| ≤ N * ∑_{p∈P} 1/(k*p²) + |P|` after casting to `ℝ`.
-/
lemma sieve_set_card_bound
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hcard : S.card ≤ (∑ p ∈ P, (N / (k * p ^ 2) + 1)) := by
    calc
      S.card ≤
          ((P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n))).card) :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, (N / (k * p ^ 2) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hper p hp
  have hcard_real :
      (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard_real.trans (sum_div_add_one_le_real (N := N) (P := P) (k := k))

/--
Variant of `sieve_set_card_bound` where the additive error is expressed as `π(N)`.

This is convenient when one later uses an analytic bound `π(N) ≤ δN`.
-/
lemma sieve_set_card_bound_primeCounting
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1)
    (hP_sub : P ⊆ primesUpTo N) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
  have hbase := sieve_set_card_bound (N := N) (k := k) (P := P) (S := S) (pred := pred) hsubset hper
  have hPcard : (P.card : ℝ) ≤ (N.primeCounting : ℝ) := by
    have := Finset.card_le_card hP_sub
    have := (Nat.cast_le.2 this : (P.card : ℝ) ≤ (primesUpTo N).card)
    simpa [primesUpTo_card] using this
  have hadd :
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) :=
    add_le_add_right hPcard ((N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)))
  exact hbase.trans hadd

/-- The mod-100 residue-class sieve used in the all-odd branch. -/
lemma residue_class_card_bound100_of_subset
    (N t25 t4 b : ℕ) (P S : Finset ℕ)
    (hsubset :
      S ⊆ P.biUnion (fun p =>
        (Finset.range N).filter (fun a =>
          a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)))
    (hP_sub : P ⊆ primesUpTo N) (hP_ne2 : ∀ p ∈ P, p ≠ 2)
    (hP_ne5 : ∀ p ∈ P, p ≠ 5) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) +
        (N.primeCounting : ℝ) := by
  classical
  have hper :
      ∀ p ∈ P,
        ((Finset.range N).filter (fun a =>
            a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
          N / (100 * p ^ 2) + 1 := by
    intro p hp
    have hp' : p ∈ primesUpTo N := hP_sub hp
    have hp_prime : p.Prime := (Finset.mem_filter.1 hp').2
    exact off_count_modEq100_le' N p b t25 t4 hp_prime (hP_ne2 p hp) (hP_ne5 p hp)
  simpa using
    sieve_set_card_bound_primeCounting
      (N := N)
      (k := 100)
      (P := P)
      (S := S)
      (pred := fun p a =>
        a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)
      hsubset
      hper
      hP_sub

/-- In the all-odd case, splitting the two exceptional residue classes modulo
100 leaves two free classes and two classes controlled by odd prime squares. -/
private theorem all_odd_residue_bound
    (N : ℕ) (A : Finset ℕ) (b : ℕ)
    (hN100 : 100 ≤ N)
    (hAsub : A ⊆ Finset.range N)
    (hAprop : NonSquarefreeProductProp A)
    (hbA : b ∈ A) (hb_lt : b < N) (hb_odd : b % 2 = 1)
    (hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18)
    (hEven78 :
      ¬ ((∃ a ∈ A.filter (fun x => x % 25 = 7), a % 2 = 0) ∨
        (∃ a ∈ A.filter (fun x => x % 25 = 18), a % 2 = 0))) :
    ((A.filter (fun x => x % 25 = 7)).card : ℝ) +
        ((A.filter (fun x => x % 25 = 18)).card : ℝ) ≤
      (N : ℝ) / 50 + 2 +
        2 * (N : ℝ) *
          (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) +
        2 * (N.primeCounting : ℝ) := by
  classical
  let A7A : Finset ℕ := A.filter (fun a => a % 25 = 7)
  let A18A : Finset ℕ := A.filter (fun a => a % 25 = 18)
  have hA7A_sub_A : A7A ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.1 ha).1
  have hA18A_sub_A : A18A ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.1 ha).1
  have hA7A_sub_range : A7A ⊆ Finset.range N :=
    Finset.Subset.trans hA7A_sub_A hAsub
  have hA18A_sub_range : A18A ⊆ Finset.range N :=
    Finset.Subset.trans hA18A_sub_A hAsub
  change
    (A7A.card : ℝ) + (A18A.card : ℝ) ≤
      (N : ℝ) / 50 + 2 +
        2 * (N : ℝ) *
          (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) +
        2 * (N.primeCounting : ℝ)
  change
    ¬ ((∃ a ∈ A7A, a % 2 = 0) ∨ (∃ a ∈ A18A, a % 2 = 0)) at hEven78
  -- Since ¬hEven78, all elements of A7A and A18A are odd.
  push_neg at hEven78
  have hA7_all_odd : ∀ a ∈ A7A, a % 2 = 1 := fun a ha => by
    have hne := hEven78.1 a ha; omega
  have hA18_all_odd : ∀ a ∈ A18A, a % 2 = 1 := fun a ha => by
    have hne := hEven78.2 a ha; omega
  -- A7A elements are ≡ 7 or 57 mod 100 (odd elements ≡ 7 mod 25)
  -- A18A elements are ≡ 43 or 93 mod 100 (odd elements ≡ 18 mod 25)
  -- For b odd: if b ≡ 1 mod 4, then 4 | ba+1 iff a ≡ 3 mod 4 (i.e., 7, 43 mod 100)
  --            if b ≡ 3 mod 4, then 4 | ba+1 iff a ≡ 1 mod 4 (i.e., 57, 93 mod 100)
  -- In both cases: 2 "free" classes (4 | ba+1) and 2 "sieve" classes (need odd p² | ba+1).
  -- Free classes contribute ≤ N/50, sieve classes contribute ≤ N*Σ(1/100p²) + 2π(N).
  have hb_mod4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  -- Bound using the two sieve classes (which need an odd prime square divisor).
  -- For each a in A7A ∪ A18A not in a free class, there exists odd prime p with p² | ba+1.
  -- Define the four mod-100 residue class filters
  let S7 := (Finset.range N).filter (fun a => a % 100 = 7)
  let S57 := (Finset.range N).filter (fun a => a % 100 = 57)
  let S43 := (Finset.range N).filter (fun a => a % 100 = 43)
  let S93 := (Finset.range N).filter (fun a => a % 100 = 93)
  -- A7A ⊆ S7 ∪ S57, A18A ⊆ S43 ∪ S93
  have hA7_sub : A7A ⊆ S7 ∪ S57 := by
    intro a ha
    have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
    have hodd : a % 2 = 1 := hA7_all_odd a ha
    have ha_range : a ∈ Finset.range N := hA7A_sub_range ha
    have ha_lt : a < N := Finset.mem_range.1 ha_range
    -- a ≡ 7 mod 25 and a odd → a ≡ 7 or 57 mod 100
    have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
    rcases hmod with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
  have hA18_sub : A18A ⊆ S43 ∪ S93 := by
    intro a ha
    have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
    have hodd : a % 2 = 1 := hA18_all_odd a ha
    have ha_range : a ∈ Finset.range N := hA18A_sub_range ha
    have ha_lt : a < N := Finset.mem_range.1 ha_range
    have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
    rcases hmod with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
  -- By cases on b % 4
  rcases hb_mod4 with hb1 | hb3
  · -- Case b ≡ 1 mod 4: Free = {7, 43}, Sieve = {57, 93}
    -- For a ≡ 3 mod 4 (i.e., 7 or 43 mod 100): 4 | ba+1 (free)
    -- For a ≡ 1 mod 4 (i.e., 57 or 93 mod 100): 4 ∤ ba+1, need odd p² | ba+1 (sieve)
    -- Bound A7A ∩ S7 (free) + A18A ∩ S43 (free) ≤ N/50
    -- Bound free classes: each ≤ N/100 + 1, total ≤ N/50 + 2
    have hfree7 : ((A7A.filter (·%100=7)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
      have hsub : A7A.filter (·%100=7) ⊆ S7 := Finset.filter_subset_filter _ (fun _ h => hA7A_sub_range h)
      have hS7_card : S7.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 7
      calc ((A7A.filter (·%100=7)).card : ℝ)
          ≤ (S7.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS7_card
        _ ≤ (N : ℝ) / 100 + 1 := by
            have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
            rw [this]
            have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
            linarith
    have hfree43 : ((A18A.filter (·%100=43)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
      have hsub : A18A.filter (·%100=43) ⊆ S43 := Finset.filter_subset_filter _ (fun _ h => hA18A_sub_range h)
      have hS43_card : S43.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 43
      calc ((A18A.filter (·%100=43)).card : ℝ)
          ≤ (S43.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS43_card
        _ ≤ (N : ℝ) / 100 + 1 := by
            have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
            rw [this]
            have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
            linarith
    have hfree_bound : (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) ≤ (N : ℝ) / 50 + 2 := by
      linarith [hfree7, hfree43]
    -- Bound A7A ∩ S57 (sieve) using biUnion over offPrimesUpTo
    have hsieve7_bound : ((A7A.filter (·%100=57)).card : ℝ) ≤
        (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
      have hsubset : A7A.filter (·%100=57) ⊆ (offPrimesUpTo N).biUnion (fun p =>
          (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ a ≡ 1 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
        intro a ha
        have haA7 : a ∈ A7A := (Finset.mem_filter.1 ha).1
        have ha100 : a % 100 = 57 := (Finset.mem_filter.1 ha).2
        have haA : a ∈ A := hA7A_sub_A haA7
        have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
        have ha25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 haA7).2
        have ha4 : a % 4 = 1 := by omega
        -- ba+1 is not squarefree
        have hnsq : ¬ Squarefree (b * a + 1) := by
          have := hAprop b hbA a haA
          simpa [mul_comm] using this
        -- 4 ∤ ba+1 since b ≡ 1 mod 4 and a ≡ 1 mod 4
        have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
          intro hdvd
          have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
          have h1_mod4 : (b * a + 1) % 4 = 2 := by omega
          have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
          omega
        -- So there exists odd prime p with p² | ba+1
        obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
        have hp_ne2 : p ≠ 2 := by
          intro hp2; subst hp2
          exact h4_ndvd hp2_dvd
        have hp_ne5 : p ≠ 5 := by
          intro hp5; subst hp5
          have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
          have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          -- If 25 | ba+1 and a ≡ 7 mod 25, then b*7 ≡ -1 mod 25, so b ≡ -1*7⁻¹ mod 25
          -- 7⁻¹ mod 25 = 18 (since 7*18 = 126 = 5*25+1), so b ≡ -18 ≡ 7 mod 25
          have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
          have ha_mod : Nat.ModEq 25 a 7 := by unfold Nat.ModEq; simp [ha25]
          have heq : Nat.ModEq 25 (b * a) (b * 7) := Nat.ModEq.mul_left b ha_mod
          have hb7 : (b * 7 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
          have hb_mod25 : b % 25 = 7 := by omega
          exact hb25.1 hb_mod25
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_ne2)
        have hp_le : p ≤ N := by
          have hba_lt : b * a + 1 < N ^ 2 := by
            have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
            have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
            have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
            have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            omega
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
        have hp_mem : p ∈ offPrimesUpTo N := by
          simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
      have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
        intro p hp
        exact (Finset.mem_filter.1 hp).1
      have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.1
      have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.2
      exact
        residue_class_card_bound100_of_subset
          (N := N)
          (t25 := 7)
          (t4 := 1)
          (b := b)
          (P := offPrimesUpTo N)
          (S := A7A.filter (· % 100 = 57))
          hsubset
          hP_sub
          hP_ne2
          hP_ne5
    -- Bound A18A ∩ S93 (sieve) similarly
    have hsieve18_bound : ((A18A.filter (·%100=93)).card : ℝ) ≤
        (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
      have hsubset : A18A.filter (·%100=93) ⊆ (offPrimesUpTo N).biUnion (fun p =>
          (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ a ≡ 1 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
        intro a ha
        have haA18 : a ∈ A18A := (Finset.mem_filter.1 ha).1
        have ha100 : a % 100 = 93 := (Finset.mem_filter.1 ha).2
        have haA : a ∈ A := hA18A_sub_A haA18
        have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
        have ha25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 haA18).2
        have ha4 : a % 4 = 1 := by omega
        have hnsq : ¬ Squarefree (b * a + 1) := by
          have := hAprop b hbA a haA
          simpa [mul_comm] using this
        have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
          intro hdvd
          have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
          have h1_mod4 : (b * a + 1) % 4 = 2 := by omega
          have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
          omega
        obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
        have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
        have hp_ne5 : p ≠ 5 := by
          intro hp5; subst hp5
          have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
          have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
          have ha_mod : Nat.ModEq 25 a 18 := by unfold Nat.ModEq; simp [ha25]
          have heq : Nat.ModEq 25 (b * a) (b * 18) := Nat.ModEq.mul_left b ha_mod
          have hb18 : (b * 18 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
          -- 18⁻¹ mod 25 = 7 (since 18*7 = 126 = 5*25+1), so b ≡ -7 ≡ 18 mod 25
          have hb_mod25 : b % 25 = 18 := by omega
          exact hb25.2 hb_mod25
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_ne2)
        have hp_le : p ≤ N := by
          have hba_lt : b * a + 1 < N ^ 2 := by
            have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
            have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
            have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
            have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            omega
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
        have hp_mem : p ∈ offPrimesUpTo N := by
          simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
      have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
        intro p hp
        exact (Finset.mem_filter.1 hp).1
      have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.1
      have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.2
      exact
        residue_class_card_bound100_of_subset
          (N := N)
          (t25 := 18)
          (t4 := 1)
          (b := b)
          (P := offPrimesUpTo N)
          (S := A18A.filter (· % 100 = 93))
          hsubset
          hP_sub
          hP_ne2
          hP_ne5
    -- Combine: A7A = (A7A ∩ S7) ∪ (A7A ∩ S57), A18A = (A18A ∩ S43) ∪ (A18A ∩ S93)
    have hA7_split : A7A.card ≤ (A7A.filter (·%100=7)).card + (A7A.filter (·%100=57)).card := by
      have h_union : A7A = A7A.filter (·%100=7) ∪ A7A.filter (·%100=57) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha
          have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
          have hodd : a % 2 = 1 := hA7_all_odd a ha
          have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
          rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
        · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hcard_eq : A7A.card = (A7A.filter (·%100=7) ∪ A7A.filter (·%100=57)).card := by
        conv_lhs => rw [h_union]
      rw [hcard_eq]
      exact Finset.card_union_le (A7A.filter (· % 100 = 7)) (A7A.filter (· % 100 = 57))
    have hA18_split : A18A.card ≤ (A18A.filter (·%100=43)).card + (A18A.filter (·%100=93)).card := by
      have h_union : A18A = A18A.filter (·%100=43) ∪ A18A.filter (·%100=93) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha
          have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
          have hodd : a % 2 = 1 := hA18_all_odd a ha
          have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
          rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
        · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hcard_eq : A18A.card = (A18A.filter (·%100=43) ∪ A18A.filter (·%100=93)).card := by
        conv_lhs => rw [h_union]
      rw [hcard_eq]
      exact Finset.card_union_le (A18A.filter (· % 100 = 43)) (A18A.filter (· % 100 = 93))
    -- Final calculation
    have hA7_real : (A7A.card : ℝ) ≤ ((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ) := by
      exact_mod_cast hA7_split
    have hA18_real : (A18A.card : ℝ) ≤ ((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ) := by
      exact_mod_cast hA18_split
    calc (A7A.card : ℝ) + (A18A.card : ℝ)
        ≤ (((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ)) +
          (((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith
      _ = (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) +
          (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by ring
      _ ≤ ((N : ℝ) / 50 + 2) + (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith [hfree_bound]
      _ ≤ ((N : ℝ) / 50 + 2) + ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) +
          ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by linarith [hsieve7_bound, hsieve18_bound]
      _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) := by ring
  · -- Case b ≡ 3 mod 4: Free = {57, 93}, Sieve = {7, 43}
    -- Symmetric to the b ≡ 1 case
    have hfree_bound : (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) ≤ (N : ℝ) / 50 + 2 := by
      have h57_le : ((A7A.filter (·%100=57)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
        have hS57_card : S57.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 57
        have hsub : A7A.filter (·%100=57) ⊆ S57 := Finset.filter_subset_filter _ (fun _ h => hA7A_sub_range h)
        calc ((A7A.filter (·%100=57)).card : ℝ)
            ≤ (S57.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS57_card
          _ ≤ (N : ℝ) / 100 + 1 := by
              have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
              rw [this]
              have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
              linarith
      have h93_le : ((A18A.filter (·%100=93)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
        have hS93_card : S93.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 93
        have hsub : A18A.filter (·%100=93) ⊆ S93 := Finset.filter_subset_filter _ (fun _ h => hA18A_sub_range h)
        calc ((A18A.filter (·%100=93)).card : ℝ)
            ≤ (S93.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS93_card
          _ ≤ (N : ℝ) / 100 + 1 := by
              have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
              rw [this]
              have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
              linarith
      linarith [h57_le, h93_le]
    -- Bound sieve classes (7 and 43 mod 100)
    have hsieve7_bound : ((A7A.filter (·%100=7)).card : ℝ) ≤
        (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
      have hsubset : A7A.filter (·%100=7) ⊆ (offPrimesUpTo N).biUnion (fun p =>
          (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ a ≡ 3 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
        intro a ha
        have haA7 : a ∈ A7A := (Finset.mem_filter.1 ha).1
        have ha100 : a % 100 = 7 := (Finset.mem_filter.1 ha).2
        have haA : a ∈ A := hA7A_sub_A haA7
        have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
        have ha25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 haA7).2
        have ha4 : a % 4 = 3 := by omega
        have hnsq : ¬ Squarefree (b * a + 1) := by
          have := hAprop b hbA a haA; simpa [mul_comm] using this
        -- b ≡ 3 mod 4 and a ≡ 3 mod 4, so ba ≡ 1 mod 4, ba+1 ≡ 2 mod 4
        have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
          intro hdvd
          have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
          have h_mod4 : (b * a + 1) % 4 = 2 := by omega
          have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
          omega
        obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
        have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
        have hp_ne5 : p ≠ 5 := by
          intro hp5; subst hp5
          have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
          have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
          have ha_mod : Nat.ModEq 25 a 7 := by unfold Nat.ModEq; simp [ha25]
          have heq : Nat.ModEq 25 (b * a) (b * 7) := Nat.ModEq.mul_left b ha_mod
          have hb7 : (b * 7 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
          have hb_mod25 : b % 25 = 7 := by omega
          exact hb25.1 hb_mod25
        have hp_le : p ≤ N := by
          have hba_lt : b * a + 1 < N ^ 2 := by
            have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
            have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
            have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
            have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            omega
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
        have hp_mem : p ∈ offPrimesUpTo N := by
          simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
      have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
        intro p hp
        exact (Finset.mem_filter.1 hp).1
      have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.1
      have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.2
      exact
        residue_class_card_bound100_of_subset
          (N := N)
          (t25 := 7)
          (t4 := 3)
          (b := b)
          (P := offPrimesUpTo N)
          (S := A7A.filter (· % 100 = 7))
          hsubset
          hP_sub
          hP_ne2
          hP_ne5
    have hsieve18_bound : ((A18A.filter (·%100=43)).card : ℝ) ≤
        (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
      have hsubset : A18A.filter (·%100=43) ⊆ (offPrimesUpTo N).biUnion (fun p =>
          (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ a ≡ 3 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
        intro a ha
        have haA18 : a ∈ A18A := (Finset.mem_filter.1 ha).1
        have ha100 : a % 100 = 43 := (Finset.mem_filter.1 ha).2
        have haA : a ∈ A := hA18A_sub_A haA18
        have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
        have ha25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 haA18).2
        have ha4 : a % 4 = 3 := by omega
        have hnsq : ¬ Squarefree (b * a + 1) := by
          have := hAprop b hbA a haA; simpa [mul_comm] using this
        have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
          intro hdvd
          have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
          have h_mod4 : (b * a + 1) % 4 = 2 := by omega
          have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
          omega
        obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
        have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
        have hp_ne5 : p ≠ 5 := by
          intro hp5; subst hp5
          have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
          have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
          have ha_mod : Nat.ModEq 25 a 18 := by unfold Nat.ModEq; simp [ha25]
          have heq : Nat.ModEq 25 (b * a) (b * 18) := Nat.ModEq.mul_left b ha_mod
          have hb18 : (b * 18 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
          have hb_mod25 : b % 25 = 18 := by omega
          exact hb25.2 hb_mod25
        have hp_le : p ≤ N := by
          have hba_lt : b * a + 1 < N ^ 2 := by
            have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
            have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
            have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
            have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            omega
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
        have hp_mem : p ∈ offPrimesUpTo N := by
          simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
      have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
        intro p hp
        exact (Finset.mem_filter.1 hp).1
      have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.1
      have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
        intro p hp
        exact (Finset.mem_filter.1 hp).2.2
      exact
        residue_class_card_bound100_of_subset
          (N := N)
          (t25 := 18)
          (t4 := 3)
          (b := b)
          (P := offPrimesUpTo N)
          (S := A18A.filter (· % 100 = 43))
          hsubset
          hP_sub
          hP_ne2
          hP_ne5
    -- Combine for b ≡ 3 case
    have hA7_split : A7A.card ≤ (A7A.filter (·%100=7)).card + (A7A.filter (·%100=57)).card := by
      have h_union : A7A = A7A.filter (·%100=7) ∪ A7A.filter (·%100=57) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha
          have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
          have hodd : a % 2 = 1 := hA7_all_odd a ha
          have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
          rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
        · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hcard_eq : A7A.card = (A7A.filter (·%100=7) ∪ A7A.filter (·%100=57)).card := by
        conv_lhs => rw [h_union]
      rw [hcard_eq]
      exact Finset.card_union_le (A7A.filter (· % 100 = 7)) (A7A.filter (· % 100 = 57))
    have hA18_split : A18A.card ≤ (A18A.filter (·%100=43)).card + (A18A.filter (·%100=93)).card := by
      have h_union : A18A = A18A.filter (·%100=43) ∪ A18A.filter (·%100=93) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha
          have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
          have hodd : a % 2 = 1 := hA18_all_odd a ha
          have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
          rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
        · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hcard_eq : A18A.card = (A18A.filter (·%100=43) ∪ A18A.filter (·%100=93)).card := by
        conv_lhs => rw [h_union]
      rw [hcard_eq]
      exact Finset.card_union_le (A18A.filter (· % 100 = 43)) (A18A.filter (· % 100 = 93))
    have hA7_real : (A7A.card : ℝ) ≤ ((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ) := by
      exact_mod_cast hA7_split
    have hA18_real : (A18A.card : ℝ) ≤ ((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ) := by
      exact_mod_cast hA18_split
    calc (A7A.card : ℝ) + (A18A.card : ℝ)
        ≤ (((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ)) +
          (((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith
      _ = (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) +
          (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) := by ring
      _ ≤ ((N : ℝ) / 50 + 2) + (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) := by linarith [hfree_bound]
      _ ≤ ((N : ℝ) / 50 + 2) + ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) +
          ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by linarith [hsieve7_bound, hsieve18_bound]
      _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) := by ring

-- ============================================================================
-- SECTION 10: THE MAIN STABILITY THEOREM (SAWHNEY)
-- ============================================================================


/-- SawhneyMain: The stability theorem for Erdős Problem 848.

This theorem establishes that any set A ⊆ [N] satisfying the squarefree-product
condition with density ≥ 1/25 - η must be contained in {n : n ≡ 7 (mod 25)} or
{n : n ≡ 18 (mod 25)}.

The proof uses:
1. Sieve bounds on diagonal constraints (n² + 1 divisible by p²)
2. Cross-term analysis for mixed residue classes
3. Case analysis on even/odd elements in A* = A \ (A_7 ∪ A_18)
-/

theorem sawhney_main : SawhneyMain := by
  classical
  -- Numerical slack parameter for prime-counting error terms.
  let δ : ℝ := (1 / 10000000 : ℝ)
  have δpos : 0 < δ := by
    norm_num [δ]
  -- Density bounds from the paper.
  let C_diag : ℝ := (1 : ℝ) / 1750
  let C_off : ℝ := 163 / 25000
  let C_no5 : ℝ := 413 / 25000
  obtain ⟨Nπ, hπ⟩ := exists_primeCounting_le_mul_nat δ δpos
  -- Choose N₀ large enough to absorb all `+1` errors.
  let N₀ : ℕ := max 10000000 (max 100 Nπ)
  refine ⟨(1 / 2000 : ℝ), N₀, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro N hN A hAsub hAprop hdense
    -- Basic lower bounds on N.
    have hN100 : 100 ≤ N := by
      have : 100 ≤ N₀ := le_trans (Nat.le_max_left 100 Nπ) (Nat.le_max_right 10000000 (max 100 Nπ))
      exact le_trans this hN
    have hNbig : 10000000 ≤ N := by
      have : 10000000 ≤ N₀ := Nat.le_max_left 10000000 (max 100 Nπ)
      exact le_trans this hN
    have hNpos_nat : 0 < N := lt_of_lt_of_le (by decide : 0 < 100) hN100
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat

    -- Prime-counting upper bound for this N.
    have hNπ' : Nπ ≤ N := by
      have : Nπ ≤ N₀ := le_trans (Nat.le_max_right 100 Nπ) (Nat.le_max_right 10000000 (max 100 Nπ))
      exact le_trans this hN
    have hπN : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπ N hNπ'

    -- Helper: `∑ (N/(k*p^2)+1)` is bounded by `N * ∑ 1/(k*p^2) + |P|`.
    have sum_div_add_one_le (P : Finset ℕ) (k : ℕ) :
        ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
      classical
      have hsplit :
          ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
            ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
        have :
            (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
              (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
          simp [Finset.sum_add_distrib]
        exact_mod_cast this
      have hterm :
          ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
        intro p hp
        have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := (k * p ^ 2)))
        simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
      have hdiv' :
          ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
            ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
        exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
      have hdiv :
          ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
            (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
        have :
            (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
              (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
          simp [div_eq_mul_inv, mul_sum, mul_comm]
        exact hdiv'.trans (le_of_eq this)
      have h := add_le_add_right hdiv (P.card : ℝ)
      calc
        ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
            ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
        _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using h

    -- Helper: residue-class counting via a union over prime-square divisors.
    have residue_class_card_bound_of_subset
        (t b : ℕ) (P S : Finset ℕ)
        (hsubset :
          S ⊆ P.biUnion (fun p =>
            (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)))
        (hP_sub : P ⊆ primesUpTo N) (hP_ne5 : ∀ p ∈ P, p ≠ 5) :
        (S.card : ℝ) ≤
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
      classical
      have hcard : S.card ≤ (∑ p ∈ P, (N / (25 * p ^ 2) + 1)) := by
        calc
          S.card ≤
              ((P.biUnion (fun p =>
                    (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1))).card) :=
            Finset.card_le_card hsubset
          _ ≤ ∑ p ∈ P,
                ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ p ∈ P, (N / (25 * p ^ 2) + 1) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp' : p ∈ primesUpTo N := hP_sub hp
              have hp_prime : p.Prime := (Finset.mem_filter.1 hp').2
              have hp_ne5 : p ≠ 5 := hP_ne5 p hp
              exact off_count_modEq25_le' N p b t hp_prime hp_ne5
      have hcard_real :
          (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have hsum := sum_div_add_one_le (P := P) (k := 25)
      have hPcard : (P.card : ℝ) ≤ (N.primeCounting : ℝ) := by
        have := Finset.card_le_card hP_sub
        have := (Nat.cast_le.2 this : (P.card : ℝ) ≤ (primesUpTo N).card)
        simpa [primesUpTo_card] using this
      have hsum' :
          ((∑ p ∈ P, (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) ≤
            (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
        exact hsum.trans (add_le_add (le_refl _) hPcard)
      exact le_trans hcard_real hsum'

    -- Split A into the 25-residue classes: 7, 18, and the rest.
    let A7A : Finset ℕ := A.filter (fun a => a % 25 = 7)
    let A18A : Finset ℕ := A.filter (fun a => a % 25 = 18)
    let Astar : Finset ℕ := A.filter (fun a => a % 25 ≠ 7 ∧ a % 25 ≠ 18)

    have hA7A_sub_A : A7A ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1
    have hA18A_sub_A : A18A ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1
    have hAstar_sub_A : Astar ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1

    have hA7A_sub_range : A7A ⊆ Finset.range N := Finset.Subset.trans hA7A_sub_A hAsub
    have hA18A_sub_range : A18A ⊆ Finset.range N := Finset.Subset.trans hA18A_sub_A hAsub
    have hAstar_sub_range : Astar ⊆ Finset.range N := Finset.Subset.trans hAstar_sub_A hAsub

    have hA_decomp : A ⊆ A7A ∪ A18A ∪ Astar := by
      intro a ha
      by_cases h7 : a % 25 = 7
      · have : a ∈ A7A := by
          simp [A7A, ha, h7]
        exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl this)))
      · by_cases h18 : a % 25 = 18
        · have : a ∈ A18A := by
            simp [A18A, ha, h18]
          exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr this)))
        · have : a ∈ Astar := by
            simp [Astar, ha, h7, h18]
          exact Finset.mem_union.2 (Or.inr this)

    have hA_card_le_parts_nat : A.card ≤ A7A.card + A18A.card + Astar.card := by
      have hsubset : A ⊆ A7A ∪ A18A ∪ Astar := hA_decomp
      have hcard : A.card ≤ (A7A ∪ A18A ∪ Astar).card := Finset.card_le_card hsubset
      have hunion1 : (A7A ∪ A18A ∪ Astar).card ≤ (A7A ∪ A18A).card + Astar.card := by
        simpa [Finset.union_assoc] using (Finset.card_union_le (A7A ∪ A18A) Astar)
      have hunion2 : (A7A ∪ A18A).card ≤ A7A.card + A18A.card := Finset.card_union_le _ _
      have : A.card ≤ (A7A.card + A18A.card) + Astar.card := by
        have h1 : (A7A ∪ A18A).card + Astar.card ≤ (A7A.card + A18A.card) + Astar.card := by omega
        exact le_trans (le_trans hcard hunion1) h1
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

    -- Helper: bound A* via diagonal primes (no parity restriction; modulus 25).
    have Astar_bound_mod25 :
        (Astar.card : ℝ) ≤
          (46 : ℝ) *
            ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by
      classical
      have hsubset :
          Astar ⊆ (diagPrimesUpTo N).biUnion (fun p =>
            (Finset.range N).filter (fun n =>
              n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
        intro x hx
        have hxA : x ∈ A := hAstar_sub_A hx
        have hx_lt : x < N := by simpa [Finset.mem_range] using hAsub hxA
        have hx_mod_ne : x % 25 ≠ 7 ∧ x % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hx).2
        have hnsq : ¬ Squarefree (x ^ 2 + 1) := by
          simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAprop x hxA x hxA
        obtain ⟨p, hp, hp2div⟩ := prime_square_exists (n := x ^ 2 + 1) hnsq
        have hp_ne2 : p ≠ 2 := by
          intro hp2
          subst hp2
          have : 4 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_four_sq_add_one x) this
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp.two_le (Ne.symm hp_ne2)
        have hp_mod4 : p % 4 = 1 :=
          prime_sq_divides_implies_one_mod_four p x hp hp_gt2 (by simpa [pow_two] using hp2div)
        have hp_ne5 : p ≠ 5 := by
          intro hp5
          subst hp5
          have : 25 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_25_sq_add_one_of_mod_ne x hx_mod_ne) this
        have hp_ge13 : 13 ≤ p := prime_ge_13_of_mod4_one_ne5 p hp hp_mod4 hp_ne5
        have hp_le : p ≤ N := by
          have hxx_lt : x ^ 2 + 1 < N ^ 2 := by
            have hx_le : x ≤ N - 1 := Nat.le_pred_of_lt hx_lt
            have hxx_le : x ^ 2 ≤ (N - 1) ^ 2 := Nat.pow_le_pow_left hx_le 2
            have : x ^ 2 + 1 ≤ (N - 1) ^ 2 + 1 := Nat.add_le_add_right hxx_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            exact lt_of_le_of_lt this hlt
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := x ^ 2 + 1) (Nat.succ_pos _) hxx_lt hp2div
        have hp_mem : p ∈ diagPrimesUpTo N := by
          have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
          simp [diagPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_mod4, hp_ge13]
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
        have : x ∈ (Finset.range N).filter (fun n =>
            n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1) := by
          simp [Finset.mem_filter, Finset.mem_range, hx_lt, hx_mod_ne, hp2div]
        exact this
      have hcard : Astar.card ≤ (∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1)) := by
        calc Astar.card
            ≤ ((diagPrimesUpTo N).biUnion (fun p =>
                 (Finset.range N).filter (fun n =>
                   n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1))).card :=
              Finset.card_le_card hsubset
          _ ≤ ∑ p ∈ diagPrimesUpTo N,
                 ((Finset.range N).filter (fun n =>
                   n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_prime : p.Prime := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
              have hp_mod4 : p % 4 = 1 := (Finset.mem_filter.1 hp).2.1
              have hp_ne5 : p ≠ 5 := by
                have hp_ge13 : 13 ≤ p := (Finset.mem_filter.1 hp).2.2
                omega
              exact diag_count_mod25_ne_7_18_le N p hp_prime hp_mod4 hp_ne5
      have hcard_real :
          (Astar.card : ℝ) ≤ ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have hmul :
          ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) =
            (46 : ℝ) * ((∑ p ∈ diagPrimesUpTo N, (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) := by
        have :
            (∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1) : ℕ) =
              46 * (∑ p ∈ diagPrimesUpTo N, (N / (25 * p ^ 2) + 1) : ℕ) := by
          simpa using
            (Finset.mul_sum (s := diagPrimesUpTo N) (f := fun p => (N / (25 * p ^ 2) + 1)) (a := 46)).symm
        exact_mod_cast this
      have hsum := sum_div_add_one_le_real (N := N) (P := diagPrimesUpTo N) (k := 25)
      have hPcard : ((diagPrimesUpTo N).card : ℝ) ≤ (N.primeCounting : ℝ) := by
        have hsub : diagPrimesUpTo N ⊆ primesUpTo N := by
          intro p hp
          exact (Finset.mem_filter.1 hp).1
        have := Finset.card_le_card hsub
        have := (Nat.cast_le.2 this : ((diagPrimesUpTo N).card : ℝ) ≤ (primesUpTo N).card)
        simpa [primesUpTo_card] using this
      have hsum' :
          ((∑ p ∈ diagPrimesUpTo N, (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) ≤
            (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
        exact hsum.trans (add_le_add (le_refl _) hPcard)
      have hmul' :
          ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) ≤
            (46 : ℝ) *
              ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by
        rw [hmul]
        exact mul_le_mul_of_nonneg_left hsum' (by positivity)
      exact le_trans hcard_real hmul'

    -- Helper: bound A* via diagonal primes (odd restriction; modulus 50).
    have Astar_bound_mod50
        (hAstar_all_odd : ∀ x ∈ Astar, x % 2 = 1) :
        (Astar.card : ℝ) ≤
          (46 : ℝ) *
            ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by
      classical
      have hsubset :
          Astar ⊆ (diagPrimesUpTo N).biUnion (fun p =>
            (Finset.range N).filter (fun n =>
              n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
        intro x hx
        have hxA : x ∈ A := hAstar_sub_A hx
        have hx_lt : x < N := by simpa [Finset.mem_range] using hAsub hxA
        have hx_mod_ne : x % 25 ≠ 7 ∧ x % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hx).2
        have hx_odd : x % 2 = 1 := hAstar_all_odd x hx
        have hnsq : ¬ Squarefree (x ^ 2 + 1) := by
          simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAprop x hxA x hxA
        obtain ⟨p, hp, hp2div⟩ := prime_square_exists (n := x ^ 2 + 1) hnsq
        have hp_ne2 : p ≠ 2 := by
          intro hp2
          subst hp2
          have : 4 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_four_sq_add_one x) this
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp.two_le (Ne.symm hp_ne2)
        have hp_mod4 : p % 4 = 1 :=
          prime_sq_divides_implies_one_mod_four p x hp hp_gt2 (by simpa [pow_two] using hp2div)
        have hp_ne5 : p ≠ 5 := by
          intro hp5
          subst hp5
          have : 25 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_25_sq_add_one_of_mod_ne x hx_mod_ne) this
        have hp_ge13 : 13 ≤ p := prime_ge_13_of_mod4_one_ne5 p hp hp_mod4 hp_ne5
        have hp_le : p ≤ N := by
          have hxx_lt : x ^ 2 + 1 < N ^ 2 := by
            have hx_le : x ≤ N - 1 := Nat.le_pred_of_lt hx_lt
            have hxx_le : x ^ 2 ≤ (N - 1) ^ 2 := Nat.pow_le_pow_left hx_le 2
            have : x ^ 2 + 1 ≤ (N - 1) ^ 2 + 1 := Nat.add_le_add_right hxx_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            exact lt_of_le_of_lt this hlt
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := x ^ 2 + 1) (Nat.succ_pos _) hxx_lt hp2div
        have hp_mem : p ∈ diagPrimesUpTo N := by
          have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
          simp [diagPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_mod4, hp_ge13]
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
        have : x ∈ (Finset.range N).filter (fun n =>
            n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1) := by
          simp [Finset.mem_filter, Finset.mem_range, hx_lt, hx_odd, hx_mod_ne, hp2div]
        exact this
      have hcard : Astar.card ≤ (∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1)) := by
        calc Astar.card
            ≤ ((diagPrimesUpTo N).biUnion (fun p =>
                 (Finset.range N).filter (fun n =>
                   n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1))).card :=
              Finset.card_le_card hsubset
          _ ≤ ∑ p ∈ diagPrimesUpTo N,
                 ((Finset.range N).filter (fun n =>
                   n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_prime : p.Prime := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
              have hp_mod4 : p % 4 = 1 := (Finset.mem_filter.1 hp).2.1
              have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; omega
              have hp_ge13 : 13 ≤ p := (Finset.mem_filter.1 hp).2.2
              have hp_ne5 : p ≠ 5 := by omega
              exact diag_count_mod50odd_ne_7_18_le N p hp_prime hp_mod4 hp_ne2 hp_ne5
      have hcard_real :
          (Astar.card : ℝ) ≤ ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have hmul :
          ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) =
            (46 : ℝ) * ((∑ p ∈ diagPrimesUpTo N, (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) := by
        have :
            (∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) : ℕ) =
              46 * (∑ p ∈ diagPrimesUpTo N, (N / (50 * p ^ 2) + 1) : ℕ) := by
          simpa using
            (Finset.mul_sum (s := diagPrimesUpTo N) (f := fun p => (N / (50 * p ^ 2) + 1)) (a := 46)).symm
        exact_mod_cast this
      have hsum := sum_div_add_one_le (P := diagPrimesUpTo N) (k := 50)
      have hPcard : ((diagPrimesUpTo N).card : ℝ) ≤ (N.primeCounting : ℝ) := by
        have hsub : diagPrimesUpTo N ⊆ primesUpTo N := by
          intro p hp
          exact (Finset.mem_filter.1 hp).1
        have := Finset.card_le_card hsub
        have := (Nat.cast_le.2 this : ((diagPrimesUpTo N).card : ℝ) ≤ (primesUpTo N).card)
        simpa [primesUpTo_card] using this
      have hsum' :
          ((∑ p ∈ diagPrimesUpTo N, (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) ≤
            (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
        exact hsum.trans (add_le_add (le_refl _) hPcard)
      have hmul_le :
          ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) ≤
            (46 : ℝ) *
              ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) := by
        have :
            ((∑ p ∈ diagPrimesUpTo N, 46 * (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) ≤
              (46 : ℝ) * ((∑ p ∈ diagPrimesUpTo N, (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) := by
          simp [hmul]
        exact le_trans this (mul_le_mul_of_nonneg_left hsum' (by positivity))
      exact le_trans hcard_real hmul_le

    -- Case: A* is empty (so A ⊆ A₇ ∪ A₁₈); either one residue class is empty or density contradicts.
    have case_Astar_empty (hAstar_empty : Astar = ∅) : A ⊆ A₇ N ∨ A ⊆ A₁₈ N := by
      -- If A* is empty, then A is contained in residues 7 and 18.
      have hA_sub_78 : A ⊆ A7A ∪ A18A := by
        intro a ha
        have : a ∈ A7A ∪ A18A ∪ Astar := hA_decomp ha
        simpa [hAstar_empty] using this
      by_cases hA7_empty : A7A = ∅
      · -- Then A ⊆ A₁₈ N.
        right
        intro a ha
        have ha78 : a ∈ A7A ∪ A18A := hA_sub_78 ha
        have ha18 : a ∈ A18A := by
          rcases Finset.mem_union.1 ha78 with ha7 | ha18
          · simp [hA7_empty] at ha7
          · exact ha18
        have ha_range : a ∈ Finset.range N := hA18A_sub_range ha18
        have ha_mod : a % 25 = 18 := by
          simpa [A18A] using (Finset.mem_filter.1 ha18).2
        simp [A₁₈, ha_range, ha_mod]
      · by_cases hA18_empty : A18A = ∅
        · -- Then A ⊆ A₇ N.
          left
          intro a ha
          have ha78 : a ∈ A7A ∪ A18A := hA_sub_78 ha
          have ha7 : a ∈ A7A := by
            rcases Finset.mem_union.1 ha78 with ha7 | ha18
            · exact ha7
            · simp [hA18_empty] at ha18
          have ha_range : a ∈ Finset.range N := hA7A_sub_range ha7
          have ha_mod : a % 25 = 7 := by
            simpa [A7A] using (Finset.mem_filter.1 ha7).2
          simp [A₇, ha_range, ha_mod]
        · -- Both A7A and A18A are nonempty: bound density using primes p ≠ 5.
          have hA7_nonempty : A7A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA7_empty
          have hA18_nonempty : A18A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA18_empty
          rcases hA7_nonempty with ⟨b7, hb7⟩
          rcases hA18_nonempty with ⟨b18, hb18⟩
          -- Bound A7A using b18.
          have hA7A_le :
              (A7A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
            have hb18A : b18 ∈ A := hA18A_sub_A hb18
            have hb18_lt : b18 < N := by simpa [Finset.mem_range] using hAsub hb18A
            have hb18_mod : b18 % 25 = 18 := by
              simpa [A18A] using (Finset.mem_filter.1 hb18).2
            have hsubset :
                A7A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA7A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod7 : a % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b18 * a + 1) := by
                have := hAprop b18 hb18A a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b18 * a + 1) := by
                exact cross_residue_18_7_not_div_25 b18 a hb18_mod ha_mod7
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b18 * a + 1) hnsq h25
              have hp_lt : p ≤ N := by
                have hab_lt : b18 * a + 1 < N ^ 2 := by
                  have hb18_le : b18 ≤ N - 1 := Nat.le_pred_of_lt hb18_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b18 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb18_le ha_le
                  have : b18 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b18 * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ no5PrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1) := by
                refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                exact ⟨by simpa [Nat.ModEq] using ha_mod7, hp2div⟩
              exact this
            have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2
            exact
              residue_class_card_bound_of_subset
                (t := 7)
                (b := b18)
                (P := no5PrimesUpTo N)
                (S := A7A)
                hsubset
                hP_sub
                hP_ne5
          -- Bound A18A using b7.
          have hA18A_le :
              (A18A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
            have hb7A : b7 ∈ A := hA7A_sub_A hb7
            have hb7_lt : b7 < N := by simpa [Finset.mem_range] using hAsub hb7A
            have hb7_mod : b7 % 25 = 7 := by
              simpa [A7A] using (Finset.mem_filter.1 hb7).2
            have hsubset :
                A18A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA18A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod18 : a % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b7 * a + 1) := by
                have := hAprop b7 hb7A a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b7 * a + 1) := by
                exact cross_residue_7_18_not_div_25 b7 a hb7_mod ha_mod18
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b7 * a + 1) hnsq h25
              have hp_lt : p ≤ N := by
                have hab_lt : b7 * a + 1 < N ^ 2 := by
                  have hb7_le : b7 ≤ N - 1 := Nat.le_pred_of_lt hb7_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b7 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb7_le ha_le
                  have : b7 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b7 * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ no5PrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1) := by
                refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                exact ⟨by simpa [Nat.ModEq] using ha_mod18, hp2div⟩
              exact this
            have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2
            exact
              residue_class_card_bound_of_subset
                (t := 18)
                (b := b7)
                (P := no5PrimesUpTo N)
                (S := A18A)
                hsubset
                hP_sub
                hP_ne5
          -- Combine and contradict density.
          have hA_le : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) := by
            have hcard : A.card ≤ (A7A ∪ A18A).card := Finset.card_le_card hA_sub_78
            have : (A.card : ℝ) ≤ ((A7A ∪ A18A).card : ℝ) := by exact_mod_cast hcard
            have hunion : ((A7A ∪ A18A).card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) := by
              exact_mod_cast (Finset.card_union_le A7A A18A)
            exact le_trans this hunion
          have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 2000 : ℝ)) * (N : ℝ) := by
            have hno5R : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (413 : ℝ) / 25000 := sum_no5PrimesUpTo_div25_le_real N
            -- Use the bounds on A7A and A18A and π(N) ≤ δ N.
            have hπN' : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπN
            have hA7 := hA7A_le
            have hA18 := hA18A_le
            -- Explicit intermediate bounds for numerical reasoning
            have hsum_bound : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
              simpa [C_no5] using hno5R
            have hN_times_sum : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_no5 :=
              mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hNpos)
            have hA7_bound : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
              have h1 : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + (N.primeCounting : ℝ) :=
                le_trans hA7 (add_le_add hN_times_sum (le_refl _))
              exact le_trans h1 (add_le_add (le_refl _) hπN')
            have hA18_bound : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
              have h1 : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + (N.primeCounting : ℝ) :=
                le_trans hA18 (add_le_add hN_times_sum (le_refl _))
              exact le_trans h1 (add_le_add (le_refl _) hπN')
            -- Now combine: A.card ≤ A7A.card + A18A.card ≤ 2 * (N * 413/25000 + δ * N)
            -- = N * (826/25000 + 2δ) ≈ N * 0.033042 < N * 0.0395 = (1/25 - 1/2000) * N
            have hA7_bound_num :
                (A7A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
              simpa [C_no5] using hA7_bound
            have hA18_bound_num :
                (A18A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
              simpa [C_no5] using hA18_bound
            nlinarith [hA_le, hA7_bound_num, hA18_bound_num, hNpos]
          exfalso
          exact (not_lt_of_ge hdense) hA_lt

    -- ═══════════════════════════════════════════════════════════════════
    -- CASE 0: A* = ∅ (diagonal sieve catches everything)
    -- ═══════════════════════════════════════════════════════════════════
    by_cases hAstar_empty : Astar = ∅
    · exact case_Astar_empty hAstar_empty

    · -- A* is nonempty: run the paper’s casework to get a contradiction.
      have hAstar_nonempty : Astar.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.2 hAstar_empty

      -- Case 1 (paper): there exists an even element in A*.
      have case_Astar_nonempty_exists_even (hEven : ∃ b ∈ Astar, b % 2 = 0) : False := by
        rcases hEven with ⟨b, hbAstar, hbEven⟩
        have hbA : b ∈ A := hAstar_sub_A hbAstar
        have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
        have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
        -- Bound Astar using diagonal primes (mod 25, excluding 7 and 18).
        have hAstar_bound :
            (Astar.card : ℝ) ≤
              (46 : ℝ) *
                ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) :=
          Astar_bound_mod25
        -- Bound A7A ∪ A18A using b (even): primes p ≠ 2,5.
        have hA78_bound :
            ((A7A.card : ℝ) + (A18A.card : ℝ)) ≤
              2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) := by
          -- Bound A7A using b, and A18A using b, then add.
          have hbEven' : b % 2 = 0 := hbEven
          have hb_mod_ne' : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          have hA7A_le :
              (A7A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
            have hsubset :
                A7A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA7A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod7 : a % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b * a + 1) := by
                have := hAprop b hbA a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b * a + 1) := by
                have := cross_residue_not_div_25 a b ha_mod7 hb_mod_ne'
                simp only [Nat.mul_comm a b] at this
                exact this
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b * a + 1) hnsq h25
              have hp_ne2 : p ≠ 2 := by
                have hodd : (b * a + 1) % 2 = 1 := by
                  -- b is even, so b*a+1 is odd.
                  have : 2 ∣ b * a := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hbEven') a
                  -- even + 1 is odd
                  have : (b * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                  omega
                exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
              have hp_lt : p ≤ N := by
                have hab_lt : b * a + 1 < N ^ 2 := by
                  have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                  have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ offPrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                exact ⟨by simpa [Nat.ModEq] using ha_mod7, hp2div⟩
              exact this
            have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2.2
            exact
              residue_class_card_bound_of_subset
                (t := 7)
                (b := b)
                (P := offPrimesUpTo N)
                (S := A7A)
                hsubset
                hP_sub
                hP_ne5
          have hA18A_le :
              (A18A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
            have hsubset :
                A18A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA18A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod18 : a % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b * a + 1) := by
                have := hAprop b hbA a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b * a + 1) := by
                have := cross_residue_not_div_25_18 a b ha_mod18 hb_mod_ne'
                simp only [Nat.mul_comm a b] at this
                exact this
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b * a + 1) hnsq h25
              have hp_ne2 : p ≠ 2 := by
                have hodd : (b * a + 1) % 2 = 1 := by
                  have : 2 ∣ b * a := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hbEven') a
                  have : (b * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                  omega
                exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
              have hp_lt : p ≤ N := by
                have hab_lt : b * a + 1 < N ^ 2 := by
                  have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                  have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ offPrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                exact ⟨by simpa [Nat.ModEq] using ha_mod18, hp2div⟩
              exact this
            have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2.2
            exact
              residue_class_card_bound_of_subset
                (t := 18)
                (b := b)
                (P := offPrimesUpTo N)
                (S := A18A)
                hsubset
                hP_sub
                hP_ne5
          nlinarith [hA7A_le, hA18A_le]
        -- combine all parts
        have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
          exact_mod_cast hA_card_le_parts_nat
        have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_diag := by
          simpa [C_diag] using sum_diagPrimesUpTo_div25_le_real N
        have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
          simpa [C_off] using sum_offPrimesUpTo_div25_le_real N
        have hπN' : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπN
        -- Now show total density is < (1/25 - 1/2000), contradiction.
        have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 2000 : ℝ)) * (N : ℝ) := by
          -- Compute explicit bounds step by step
          have hNdiag :
              (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_diag :=
            mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
          have hNoff :
              (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_off :=
            mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
          -- Explicit bound on Astar
          have hAstar_explicit : (Astar.card : ℝ) ≤ (46 : ℝ) * ((N : ℝ) * C_diag + δ * (N : ℝ)) := by
            have h1 := hAstar_bound
            have h2 : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                      (N : ℝ) * C_diag + δ * (N : ℝ) := add_le_add hNdiag hπN'
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
          -- Explicit bound on A7A + A18A
          have hA78_explicit :
              (A7A.card : ℝ) + (A18A.card : ℝ) ≤ 2 * (N : ℝ) * C_off + 2 * δ * (N : ℝ) := by
            have h1 := hA78_bound
            have h4 : 2 * (N.primeCounting : ℝ) ≤ 2 * δ * (N : ℝ) := by nlinarith [hπN']
            have h3 :
                2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                  2 * (N : ℝ) * C_off := by
              have hmul :
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                    (N : ℝ) * C_off :=
                hNoff
              have h2mul := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 2 by norm_num)
              calc 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))
                  = 2 * ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))) := by ring
                _ ≤ 2 * ((N : ℝ) * C_off) := h2mul
                _ = 2 * (N : ℝ) * C_off := by ring
            have h5 : 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) ≤
                      2 * (N : ℝ) * C_off + 2 * δ * (N : ℝ) := add_le_add h3 h4
            exact le_trans h1 h5
          have hAstar_explicit_num :
              (Astar.card : ℝ) ≤ (46 : ℝ) * ((N : ℝ) * ((1 : ℝ) / 1750) + δ * (N : ℝ)) := by
            simpa [C_diag] using hAstar_explicit
          have hA78_explicit_num :
              (A7A.card : ℝ) + (A18A.card : ℝ) ≤ 2 * (N : ℝ) * ((163 : ℝ) / 25000) + 2 * δ * (N : ℝ) := by
            simpa [C_off] using hA78_explicit
          nlinarith [hA_le_parts, hAstar_explicit_num, hA78_explicit_num, hNpos]
        exact (not_lt_of_ge hdense) hA_lt
      -- ═══════════════════════════════════════════════════════════════════
      -- CASE 1: ∃ even element in A* (Paper Case 1)
      -- ═══════════════════════════════════════════════════════════════════
      by_cases hEven : ∃ b ∈ Astar, b % 2 = 0
      · exfalso
        exact case_Astar_nonempty_exists_even hEven
      · -- Case 2/3: A* is all odd.
        -- We split based on whether A7 ∪ A18 contains an even element.
        have hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1 := by
          intro b hb
          have hb2 : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
          cases hb2 with
          | inl h0 =>
              exfalso
              apply hEven
              exact ⟨b, hb, h0⟩
          | inr h1 => exact h1
        have case_Astar_all_odd_exists_even_in_A78
            (hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1)
            (hEven78 : (∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0)) : False := by
          -- Pick b∈A* and an even element from A7 or A18.
          rcases hAstar_nonempty with ⟨b, hbAstar⟩
          have hbA : b ∈ A := hAstar_sub_A hbAstar
          have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
          have hb_odd : b % 2 = 1 := hAstar_all_odd b hbAstar
          have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
            simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
          -- Astar bound with mod 50 (odd restriction).
          have hAstar_bound :
              (Astar.card : ℝ) ≤
                (46 : ℝ) *
                  ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) :=
            Astar_bound_mod50 hAstar_all_odd
          -- Now bound A7 and A18 depending on where the even element lies.
          cases hEven78 with
          | inl hA7_even =>
              rcases hA7_even with ⟨b7, hb7, hb7Even⟩
              have hb7A : b7 ∈ A := hA7A_sub_A hb7
              have hb7_lt : b7 < N := by simpa [Finset.mem_range] using hAsub hb7A
              have hb7_mod : b7 % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 hb7).2
              -- Bound A7 using b (no5 primes).
              have hA7_bound :
                  (A7A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
                -- same as in the A* empty case, but with b∈A*
                have hsubset :
                    A7A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA7A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod7 : a % 25 = 7 := by
                    simpa [A7A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have hnsq' : ¬ Squarefree (a * b + 1) := by simp only [Nat.mul_comm b a] at hnsq; exact hnsq
                  obtain ⟨p, hp, hp5, hp2div'⟩ := must_have_other_prime_square a b ha_mod7 hb_mod_ne hnsq'
                  have hp2div : p ^ 2 ∣ b * a + 1 := by simp only [Nat.mul_comm a b] at hp2div'; exact hp2div'
                  have hp_le : p ≤ N := by
                    have hab_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ no5PrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                    exact ⟨by simpa [Nat.ModEq] using ha_mod7, hp2div⟩
                  exact this
                have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2
                exact
                  residue_class_card_bound_of_subset
                    (t := 7)
                    (b := b)
                    (P := no5PrimesUpTo N)
                    (S := A7A)
                    hsubset
                    hP_sub
                    hP_ne5
              -- Bound A18 using b7 (even), using off primes (exclude 2,5).
              have hA18_bound :
                  (A18A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
                have hsubset :
                    A18A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA18A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod18 : a % 25 = 18 := by
                    simpa [A18A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b7 * a + 1) := by
                    have := hAprop b7 hb7A a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have h25 : ¬ (25 ∣ b7 * a + 1) := cross_residue_7_18_not_div_25 b7 a hb7_mod ha_mod18
                  obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b7 * a + 1) hnsq h25
                  have hp_ne2 : p ≠ 2 := by
                    have hodd : (b7 * a + 1) % 2 = 1 := by
                      -- b7 even -> b7*a+1 odd
                      have : 2 ∣ b7 := Nat.dvd_of_mod_eq_zero hb7Even
                      have : 2 ∣ b7 * a := dvd_mul_of_dvd_left this a
                      have : (b7 * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                      omega
                    exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
                  have hp_le : p ≤ N := by
                    have hab_lt : b7 * a + 1 < N ^ 2 := by
                      have hb7_le : b7 ≤ N - 1 := Nat.le_pred_of_lt hb7_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b7 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb7_le ha_le
                      have : b7 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b7 * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1) := by
                    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                    exact ⟨by simpa [Nat.ModEq] using ha_mod18, hp2div⟩
                  exact this
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound_of_subset
                    (t := 18)
                    (b := b7)
                    (P := offPrimesUpTo N)
                    (S := A18A)
                    hsubset
                    hP_sub
                    hP_ne5
              -- Now combine and contradict density, using the prime-sum bounds.
              have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
                exact_mod_cast hA_card_le_parts_nat
              have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤
                  (1 : ℝ) / 3500 := sum_diagPrimesUpTo_div50_le_real N
              have hno5 : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
                simpa [C_no5] using sum_no5PrimesUpTo_div25_le_real N
              have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
                simpa [C_off] using sum_offPrimesUpTo_div25_le_real N
              have hπN' : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπN
              have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 2000 : ℝ)) * (N : ℝ) := by
                -- Compute explicit bounds
                have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3500 := by
                  have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
                  simp only [one_div] at this ⊢
                  exact this
                have hNno5 :
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_no5 :=
                  mul_le_mul_of_nonneg_left hno5 (le_of_lt hNpos)
                have hNoff :
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_off :=
                  mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
                -- Explicit Astar bound
                have hAstar_explicit : (Astar.card : ℝ) ≤ (46 : ℝ) * ((N : ℝ) / 3500 + δ * (N : ℝ)) := by
                  have h2 : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) / 3500 + δ * (N : ℝ) := add_le_add hNdiag hπN'
                  exact le_trans hAstar_bound (mul_le_mul_of_nonneg_left h2 (by positivity))
                -- Explicit A7 bound
                have hA7_explicit : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) * C_no5 + δ * (N : ℝ) := add_le_add hNno5 hπN'
                  exact le_trans hA7_bound h2
                -- Explicit A18 bound
                have hA18_explicit : (A18A.card : ℝ) ≤ (N : ℝ) * C_off + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) * C_off + δ * (N : ℝ) := add_le_add hNoff hπN'
                  exact le_trans hA18_bound h2
                exact
                  mixed_case_numerical_contradiction
                    (hδ := rfl) (hCno5 := rfl) (hCoff := rfl) (hN := hNpos)
                    (hparts := hA_le_parts) (hstar := hAstar_explicit)
                    (hno5 := hA7_explicit) (hoff := hA18_explicit)
              exact (not_lt_of_ge hdense) hA_lt
          | inr hA18_even =>
              -- symmetric case: even element is in A18A
              rcases hA18_even with ⟨b18, hb18, hb18Even⟩
              have hb18A : b18 ∈ A := hA18A_sub_A hb18
              have hb18_lt : b18 < N := by simpa [Finset.mem_range] using hAsub hb18A
              have hb18_mod : b18 % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 hb18).2
              -- Bound A18 using b (no5 primes).
              have hA18_bound :
                  (A18A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
                have hsubset :
                    A18A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA18A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod18 : a % 25 = 18 := by
                    simpa [A18A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have hnsq' : ¬ Squarefree (a * b + 1) := by simp only [Nat.mul_comm b a] at hnsq; exact hnsq
                  obtain ⟨p, hp, hp5, hp2div'⟩ := must_have_other_prime_square_18 a b ha_mod18 hb_mod_ne hnsq'
                  have hp2div : p ^ 2 ∣ b * a + 1 := by simp only [Nat.mul_comm a b] at hp2div'; exact hp2div'
                  have hp_le : p ≤ N := by
                    have hab_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ no5PrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                    exact ⟨by simpa [Nat.ModEq] using ha_mod18, hp2div⟩
                  exact this
                have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2
                exact
                  residue_class_card_bound_of_subset
                    (t := 18)
                    (b := b)
                    (P := no5PrimesUpTo N)
                    (S := A18A)
                    hsubset
                    hP_sub
                    hP_ne5
              -- Bound A7 using b18 (even), using off primes (exclude 2,5).
              have hA7_bound :
                  (A7A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) := by
                have hsubset :
                    A7A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA7A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod7 : a % 25 = 7 := by
                    simpa [A7A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b18 * a + 1) := by
                    have := hAprop b18 hb18A a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have h25 : ¬ (25 ∣ b18 * a + 1) := cross_residue_18_7_not_div_25 b18 a hb18_mod ha_mod7
                  obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b18 * a + 1) hnsq h25
                  have hp_ne2 : p ≠ 2 := by
                    have hodd : (b18 * a + 1) % 2 = 1 := by
                      have : 2 ∣ b18 := Nat.dvd_of_mod_eq_zero hb18Even
                      have : 2 ∣ b18 * a := dvd_mul_of_dvd_left this a
                      have : (b18 * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                      omega
                    exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
                  have hp_le : p ≤ N := by
                    have hab_lt : b18 * a + 1 < N ^ 2 := by
                      have hb18_le : b18 ≤ N - 1 := Nat.le_pred_of_lt hb18_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b18 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb18_le ha_le
                      have : b18 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b18 * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1) := by
                    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_⟩
                    exact ⟨by simpa [Nat.ModEq] using ha_mod7, hp2div⟩
                  exact this
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound_of_subset
                    (t := 7)
                    (b := b18)
                    (P := offPrimesUpTo N)
                    (S := A7A)
                    hsubset
                    hP_sub
                    hP_ne5
              -- Combine as before and contradict.
              have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
                exact_mod_cast hA_card_le_parts_nat
              have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤
                  (1 : ℝ) / 3500 := sum_diagPrimesUpTo_div50_le_real N
              have hno5 : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
                simpa [C_no5] using sum_no5PrimesUpTo_div25_le_real N
              have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
                simpa [C_off] using sum_offPrimesUpTo_div25_le_real N
              have hπN' : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπN
              have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 2000 : ℝ)) * (N : ℝ) := by
                -- Compute explicit bounds
                have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3500 := by
                  have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
                  simp only [one_div] at this ⊢
                  exact this
                have hNno5 :
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_no5 :=
                  mul_le_mul_of_nonneg_left hno5 (le_of_lt hNpos)
                have hNoff :
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_off :=
                  mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
                -- Explicit Astar bound
                have hAstar_explicit : (Astar.card : ℝ) ≤ (46 : ℝ) * ((N : ℝ) / 3500 + δ * (N : ℝ)) := by
                  have h2 : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) / 3500 + δ * (N : ℝ) := add_le_add hNdiag hπN'
                  exact le_trans hAstar_bound (mul_le_mul_of_nonneg_left h2 (by positivity))
                -- Explicit A7 bound (uses offPrimesUpTo in this branch)
                have hA7_explicit : (A7A.card : ℝ) ≤ (N : ℝ) * C_off + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) * C_off + δ * (N : ℝ) := add_le_add hNoff hπN'
                  exact le_trans hA7_bound h2
                -- Explicit A18 bound (uses no5PrimesUpTo in this branch)
                have hA18_explicit : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                            (N : ℝ) * C_no5 + δ * (N : ℝ) := add_le_add hNno5 hπN'
                  exact le_trans hA18_bound h2
                have hA_le_parts' :
                    (A.card : ℝ) ≤ (A18A.card : ℝ) + (A7A.card : ℝ) + (Astar.card : ℝ) := by
                  calc
                    (A.card : ℝ) ≤
                        (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := hA_le_parts
                    _ = (A18A.card : ℝ) + (A7A.card : ℝ) + (Astar.card : ℝ) := by ring
                exact
                  mixed_case_numerical_contradiction
                    (hδ := rfl) (hCno5 := rfl) (hCoff := rfl) (hN := hNpos)
                    (hparts := hA_le_parts') (hstar := hAstar_explicit)
                    (hno5 := hA18_explicit) (hoff := hA7_explicit)
              exact (not_lt_of_ge hdense) hA_lt
        have case_all_odd
            (hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1)
            (hEven78 : ¬((∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0))) : False := by
          rcases hAstar_nonempty with ⟨b, hbAstar⟩
          have hbA : b ∈ A := hAstar_sub_A hbAstar
          have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
          have hb_odd : b % 2 = 1 := hAstar_all_odd b hbAstar
          have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
            simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
          -- Astar bound (odd restriction) as in the previous branch.
          have hAstar_bound :
              (Astar.card : ℝ) ≤
                (46 : ℝ) *
                  ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ)) :=
            Astar_bound_mod50 hAstar_all_odd
          -- Bound A7 ∪ A18 (no even elements) using mod 100 split.
          -- In this case (A* all odd, A7 ∪ A18 all odd), the elements of A7A are in odd residue
          -- classes mod 100 that are ≡ 7 mod 25, i.e., 7 or 57 mod 100.
          -- Similarly A18A elements are ≡ 18 mod 25 and odd, i.e., 43 or 93 mod 100.
          -- The key insight from the paper is that for each pair (b, a) with b odd from A*,
          -- whether 4 | b*a+1 depends on the mod 4 residues. Half the residue classes have 4 | b*a+1,
          -- which forces the existence of a prime square divisor from offPrimesUpTo.
          have hA78_bound : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 +
              2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) +
                2 * (N.primeCounting : ℝ) := by
            exact
              all_odd_residue_bound
                (N := N) (A := A) (b := b) hN100 hAsub hAprop hbA hb_lt hb_odd
                hb_mod_ne (by simpa [A7A, A18A] using hEven78)
          -- Final numerical contradiction.
          have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
            exact_mod_cast hA_card_le_parts_nat
          have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤
              (1 : ℝ) / 3500 := sum_diagPrimesUpTo_div50_le_real N
          have hoff100 : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤
              (163 : ℝ) / 100000 := sum_offPrimesUpTo_div100_le_real N
          have hπN' : (N.primeCounting : ℝ) ≤ δ * (N : ℝ) := hπN
          have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 2000 : ℝ)) * (N : ℝ) := by
            -- Compute explicit bounds
            have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3500 := by
              have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
              simp only [one_div] at this ⊢
              exact this
            have hNoff100 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤ (N : ℝ) * (163 / 100000) :=
              mul_le_mul_of_nonneg_left hoff100 (le_of_lt hNpos)
            -- Explicit Astar bound
            have hAstar_explicit : (Astar.card : ℝ) ≤ (46 : ℝ) * ((N : ℝ) / 3500 + δ * (N : ℝ)) := by
              have h2 : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) + (N.primeCounting : ℝ) ≤
                        (N : ℝ) / 3500 + δ * (N : ℝ) := add_le_add hNdiag hπN'
              exact le_trans hAstar_bound (mul_le_mul_of_nonneg_left h2 (by positivity))
            -- Explicit A78 bound
            have hA78_explicit : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by
              have hπN2 : 2 * (N.primeCounting : ℝ) ≤ 2 * δ * (N : ℝ) := by nlinarith [hπN']
              have h2 : 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) ≤
                        2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by
                have hmul : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤ (N : ℝ) * (163 / 100000) := hNoff100
                have h2mul := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 2 by norm_num)
                calc 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ)
                    = 2 * ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2))) + 2 * (N.primeCounting : ℝ) := by ring
                  _ ≤ 2 * ((N : ℝ) * (163 / 100000)) + 2 * δ * (N : ℝ) := add_le_add h2mul hπN2
                  _ = 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
              calc (A7A.card : ℝ) + (A18A.card : ℝ)
                  ≤ (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * (N.primeCounting : ℝ) := hA78_bound
                _ ≤ (N : ℝ) / 50 + 2 + (2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ)) := by linarith [h2]
                _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
            have hA78_explicit' : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 4 * δ * (N : ℝ) := by
              exact le_trans hA78_explicit (absorb_two_into_prime_error rfl hNbig)
            exact
              all_odd_case_numerical_contradiction
                (hδ := rfl) (hN := hNpos) (hparts := hA_le_parts)
                (hstar := hAstar_explicit) (h78 := hA78_explicit')
          exact (not_lt_of_ge hdense) hA_lt

        by_cases hEven78 : (∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0)
        · -- ═══════════════════════════════════════════════════════════════════
          -- CASE 2: All elements odd, ∃ even in A₇ ∪ A₁₈ (Paper Case 3)
          -- ═══════════════════════════════════════════════════════════════════
          exfalso
          exact case_Astar_all_odd_exists_even_in_A78 hAstar_all_odd hEven78
        · -- ═══════════════════════════════════════════════════════════════════
          -- CASE 3: All elements in A odd (Paper Case 2 - mod 100 analysis)
          -- ═══════════════════════════════════════════════════════════════════
          exfalso
          exact case_all_odd hAstar_all_odd hEven78
-- ============================================================================
-- SECTION 11: FINAL STATEMENT
-- ============================================================================

/-- The asymptotic resolution: for sufficiently large N, max|A| ≤ |A₇(N)|.
    The full Erdős conjecture (∀ N) remains open. -/
theorem erdos_848.variants.erdos_848 : ∀ᶠ N in Filter.atTop, Erdos848For N := by
  obtain ⟨N₀, hN₀⟩ := problem_848_resolved_up_to_finite_check_of_sawhney sawhney_main
  exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩

end Erdos848

#print axioms Erdos848.erdos_848.variants.erdos_848

alias _root_.Erdos848.erdos_848.variants.asymptotic := _root_.Erdos848.erdos_848.variants.erdos_848
