/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 27.
https://www.erdosproblems.com/forum/thread/27

Informal authors:
- Michael Filaseta
- Kevin Ford
- Sergei Konyagin
- Carl Pomerance
- Gang Yu

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos27.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos277
import ErdosProblems.Erdos281
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 27

There is no fixed multiplicative interval `[N, C * N]` in which distinct
moduli can form arbitrarily good almost-covering systems at every scale.

The mathematical proof and its Leanization map are in `tex/27.tex`.  The
formal proof follows the fixed-ratio specialization of the
Filaseta--Ford--Konyagin--Pomerance--Yu smooth/rough fiber argument.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos27

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact residue systems and their periodic density -/

/-- A finite system with one residue class for every member of a finset of
moduli.  Using a finset makes distinctness of the moduli definitional. -/
structure ResidueSystem where
  moduli : Finset ℕ
  residue : (n : ℕ) → ZMod n
  modulus_pos : ∀ n ∈ moduli, 0 < n

/-- The common period of a residue system. -/
def ResidueSystem.period (A : ResidueSystem) : ℕ := A.moduli.lcm id

lemma ResidueSystem.dvd_period (A : ResidueSystem) {n : ℕ} (hn : n ∈ A.moduli) :
    n ∣ A.period := by
  exact Finset.dvd_lcm hn

lemma ResidueSystem.period_pos (A : ResidueSystem) : 0 < A.period := by
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [ResidueSystem.period, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨n, hn, hnzero⟩ := hzero
  exact (A.modulus_pos n hn).ne' hnzero

/-- The integers missed by every congruence in the system. -/
def ResidueSystem.uncovered (A : ResidueSystem) : Set ℤ :=
  {z | ∀ n ∈ A.moduli, (z : ZMod n) ≠ A.residue n}

/-- Natural representatives of the uncovered residue classes in one common
period.  Keeping the representatives in `Finset.range` makes the connection
with the periodic-density lemma definitional. -/
def ResidueSystem.uncoveredMod (A : ResidueSystem) : Finset ℕ :=
  (Finset.range A.period).filter fun x => (x : ℤ) ∈ A.uncovered

/-- The exact rational density of the periodic uncovered set. -/
def ResidueSystem.uncoveredDensity (A : ResidueSystem) : ℝ :=
  (A.uncoveredMod.card : ℝ) / A.period

/-- Bounds saying that every modulus lies in the closed interval
`[N, C * N]`. -/
def ResidueSystem.InWindow (A : ResidueSystem) (C : ℝ) (N : ℕ) : Prop :=
  ∀ n ∈ A.moduli, N ≤ n ∧ (n : ℝ) ≤ C * N

/-- Exact formalization of an `ε`-almost covering system in the requested
multiplicative interval. -/
def IsEpsilonAlmostCovering (C : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ A : ResidueSystem, A.InWindow C N ∧ A.uncoveredDensity ≤ ε

/-- The literal positive assertion asked in Erdős Problem 27. -/
def Erdos27Question : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
      IsEpsilonAlmostCovering C N ε

lemma uncovered_periodic (A : ResidueSystem) :
    ∀ z : ℤ, z ∈ A.uncovered ↔ z + A.period ∈ A.uncovered := by
  intro z
  simp only [ResidueSystem.uncovered, Set.mem_setOf_eq]
  constructor <;> intro hz n hn
  · intro heq
    apply hz n hn
    have hcast : ((A.period : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact A.dvd_period hn
    simpa [Int.cast_add, hcast] using heq
  · intro heq
    apply hz n hn
    have hcast : ((A.period : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact A.dvd_period hn
    simpa [Int.cast_add, hcast] using heq

/-- The finite one-period definition really is the two-sided natural density
of the set of uncovered integers. -/
lemma uncovered_hasIntDensity (A : ResidueSystem) :
    Erdos281.HasIntDensity A.uncovered A.uncoveredDensity := by
  have h := Erdos281.dens_periodic A.uncovered A.period A.period_pos
    (uncovered_periodic A)
  simpa [ResidueSystem.uncoveredDensity, ResidueSystem.uncoveredMod] using h

/-! ## Splitting a modulus at a fixed smoothness threshold -/

/-- The part of `d` supported on primes at most `Q`. -/
def smallFactorization (Q d : ℕ) : ℕ →₀ ℕ :=
  d.factorization.filter fun p => p ≤ Q

/-- The part of `d` supported on primes greater than `Q`. -/
def roughFactorization (Q d : ℕ) : ℕ →₀ ℕ :=
  d.factorization.filter fun p => Q < p

def smallPart (Q d : ℕ) : ℕ :=
  (smallFactorization Q d).prod fun p e => p ^ e

def roughPart (Q d : ℕ) : ℕ :=
  (roughFactorization Q d).prod fun p e => p ^ e

lemma smallFactorization_le (Q d : ℕ) :
    smallFactorization Q d ≤ d.factorization := by
  intro p
  simp only [smallFactorization, Finsupp.filter_apply]
  split <;> simp

lemma roughFactorization_le (Q d : ℕ) :
    roughFactorization Q d ≤ d.factorization := by
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split <;> simp

lemma factorization_smallPart (Q d : ℕ) :
    (smallPart Q d).factorization = smallFactorization Q d :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization
    (smallFactorization_le Q d)

lemma factorization_roughPart (Q d : ℕ) :
    (roughPart Q d).factorization = roughFactorization Q d :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization
    (roughFactorization_le Q d)

lemma smallPart_mul_roughPart {Q d : ℕ} (hd : d ≠ 0) :
    smallPart Q d * roughPart Q d = d := by
  rw [smallPart, roughPart, smallFactorization, roughFactorization]
  have hsplit := d.factorization.prod_filter_mul_prod_filter_not
    (fun p => p ≤ Q) (fun p e => p ^ e)
  simpa only [not_le] using hsplit.trans (Nat.prod_factorization_pow_eq_self hd)

lemma smallPart_pos {Q d : ℕ} (hd : 0 < d) : 0 < smallPart Q d := by
  have h := smallPart_mul_roughPart (Q := Q) hd.ne'
  exact pos_of_mul_pos_left (h ▸ hd) (Nat.zero_le _)

lemma roughPart_pos {Q d : ℕ} (hd : 0 < d) : 0 < roughPart Q d := by
  have h := smallPart_mul_roughPart (Q := Q) hd.ne'
  exact pos_of_mul_pos_right (h ▸ hd) (Nat.zero_le _)

lemma smallPart_dvd {Q d : ℕ} (hd : 0 < d) : smallPart Q d ∣ d :=
  ⟨roughPart Q d, (smallPart_mul_roughPart hd.ne').symm⟩

lemma roughPart_dvd {Q d : ℕ} (hd : 0 < d) : roughPart Q d ∣ d :=
  ⟨smallPart Q d, by
    rw [Nat.mul_comm]
    exact (smallPart_mul_roughPart hd.ne').symm⟩

lemma smallPart_smooth {Q d : ℕ} (hd : 0 < d) :
    smallPart Q d ∈ (Q + 1).smoothNumbers := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpdvd
  have hpos := hp.factorization_pos_of_dvd (smallPart_pos (Q := Q) hd).ne' hpdvd
  rw [factorization_smallPart, smallFactorization, Finsupp.filter_apply] at hpos
  split at hpos
  · omega
  · simp at hpos

/-- A small part and a (possibly different) rough part have disjoint prime
support.  This cross-coprimality is the structural reason the fibre argument
can recombine its two coordinates by CRT. -/
lemma smallPart_coprime_roughPart {Q d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (smallPart Q d).Coprime (roughPart Q e) := by
  by_contra hcop
  obtain ⟨p, hp, hps, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hsmall := hp.factorization_pos_of_dvd (smallPart_pos (Q := Q) hd).ne' hps
  have hrough := hp.factorization_pos_of_dvd (roughPart_pos (Q := Q) he).ne' hpr
  rw [factorization_smallPart, smallFactorization, Finsupp.filter_apply] at hsmall
  rw [factorization_roughPart, roughFactorization, Finsupp.filter_apply] at hrough
  split at hsmall
  · split at hrough
    · omega
    · simp at hrough
  · simp at hsmall

lemma roughPart_eq_one_smooth {Q d : ℕ} (hd : 0 < d)
    (hr : roughPart Q d = 1) : d ∈ (Q + 1).smoothNumbers := by
  have hs := smallPart_smooth (Q := Q) hd
  rw [← smallPart_mul_roughPart (Q := Q) hd.ne', hr, mul_one]
  exact hs

lemma prime_dvd_finset_lcm {ι : Type*} [DecidableEq ι]
    (p : ℕ) (hp : p.Prime) (s : Finset ι) (f : ι → ℕ)
    (h : p ∣ s.lcm f) : ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.lcm_empty] at h
      exact (hp.ne_one (Nat.dvd_one.mp h)).elim
  | @insert i s hi ih =>
      rw [Finset.lcm_insert] at h
      rcases hp.dvd_lcm.mp h with hfi | hs
      · exact ⟨i, Finset.mem_insert_self i s, hfi⟩
      · obtain ⟨j, hj, hpj⟩ := ih hs
        exact ⟨j, Finset.mem_insert_of_mem hj, hpj⟩

def smallPeriod (Q : ℕ) (A : ResidueSystem) : ℕ :=
  A.moduli.lcm (smallPart Q)

def roughPeriod (Q : ℕ) (A : ResidueSystem) : ℕ :=
  A.moduli.lcm (roughPart Q)

lemma small_dvd_smallPeriod (Q : ℕ) (A : ResidueSystem) {n : ℕ}
    (hn : n ∈ A.moduli) : smallPart Q n ∣ smallPeriod Q A :=
  Finset.dvd_lcm hn

lemma rough_dvd_roughPeriod (Q : ℕ) (A : ResidueSystem) {n : ℕ}
    (hn : n ∈ A.moduli) : roughPart Q n ∣ roughPeriod Q A :=
  Finset.dvd_lcm hn

lemma smallPeriod_pos (Q : ℕ) (A : ResidueSystem) : 0 < smallPeriod Q A := by
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [smallPeriod, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨n, hn, hnzero⟩ := hzero
  exact (smallPart_pos (Q := Q) (A.modulus_pos n hn)).ne' hnzero

lemma roughPeriod_pos (Q : ℕ) (A : ResidueSystem) : 0 < roughPeriod Q A := by
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [roughPeriod, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨n, hn, hnzero⟩ := hzero
  exact (roughPart_pos (Q := Q) (A.modulus_pos n hn)).ne' hnzero

local instance smallPeriod_neZero (Q : ℕ) (A : ResidueSystem) :
    NeZero (smallPeriod Q A) := ⟨(smallPeriod_pos Q A).ne'⟩

local instance roughPeriod_neZero (Q : ℕ) (A : ResidueSystem) :
    NeZero (roughPeriod Q A) := ⟨(roughPeriod_pos Q A).ne'⟩

lemma smallPeriod_coprime_roughPeriod (Q : ℕ) (A : ResidueSystem) :
    (smallPeriod Q A).Coprime (roughPeriod Q A) := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpR⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  obtain ⟨n, hn, hpn⟩ := prime_dvd_finset_lcm p hp A.moduli (smallPart Q) hpM
  obtain ⟨m, hm, hpm⟩ := prime_dvd_finset_lcm p hp A.moduli (roughPart Q) hpR
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpn, hpm⟩)
    (smallPart_coprime_roughPart (Q := Q) (A.modulus_pos n hn)
      (A.modulus_pos m hm))

/-! ## Uniform counting in residue rings -/

def castFiber {m n : ℕ} (hn : 0 < n) (h : m ∣ n) (a : ZMod m) : Finset (ZMod n) :=
  letI : NeZero n := ⟨hn.ne'⟩
  Finset.univ.filter fun x => ZMod.castHom h (ZMod m) x = a

@[simp] lemma mem_castFiber {m n : ℕ} (hn : 0 < n) (h : m ∣ n)
    (a : ZMod m) (x : ZMod n) :
    x ∈ castFiber hn h a ↔ ZMod.castHom h (ZMod m) x = a := by
  letI : NeZero n := ⟨hn.ne'⟩
  change x ∈ (Finset.univ.filter fun y : ZMod n =>
    ZMod.castHom h (ZMod m) y = a) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every fibre of reduction `ZMod n → ZMod m` has `n / m` elements. -/
lemma card_castFiber {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) (a : ZMod m) : (castFiber hn h a).card = n / m := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  let f := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective f := ZMod.castHom_surjective h
  have heq : ∀ b : ZMod m,
      (Finset.univ.filter fun x : ZMod n => f x = b).card =
        (Finset.univ.filter fun x : ZMod n => f x = a).card := by
    intro b
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj b) (hsurj a)
  have htotal : n = m * (Finset.univ.filter fun x : ZMod n => f x = a).card := by
    calc
      n = (Finset.univ : Finset (ZMod n)).card := by simp
      _ = ∑ b ∈ (Finset.univ : Finset (ZMod m)),
          (Finset.univ.filter fun x : ZMod n => f x = b).card :=
        Finset.card_eq_sum_card_fiberwise (by simp)
      _ = ∑ _b ∈ (Finset.univ : Finset (ZMod m)),
          (Finset.univ.filter fun x : ZMod n => f x = a).card := by
        apply Finset.sum_congr rfl
        intro b _
        exact heq b
      _ = m * (Finset.univ.filter fun x : ZMod n => f x = a).card := by simp
  simp only [castFiber]
  change (Finset.univ.filter fun x : ZMod n => f x = a).card = n / m
  calc
    (Finset.univ.filter fun x : ZMod n => f x = a).card =
        (m * (Finset.univ.filter fun x : ZMod n => f x = a).card) / m := by
      rw [Nat.mul_div_cancel_left _ hm]
    _ = n / m := congrArg (fun t => t / m) htotal.symm

def castPreimage {m n : ℕ} (hn : 0 < n) (h : m ∣ n)
    (S : Finset (ZMod m)) : Finset (ZMod n) :=
  letI : NeZero n := ⟨hn.ne'⟩
  Finset.univ.filter fun x => ZMod.castHom h (ZMod m) x ∈ S

/-- The full preimage of a finite set under reduction has the expected
cardinality. -/
lemma card_preimage_cast {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) (S : Finset (ZMod m)) :
    (castPreimage hn h S).card = (n / m) * S.card := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  let f := ZMod.castHom h (ZMod m)
  simp only [castPreimage]
  calc
    (Finset.univ.filter fun x : ZMod n => f x ∈ S).card =
        ∑ a ∈ S, (Finset.univ.filter fun x : ZMod n => f x = a).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ S f
    _ = ∑ _a ∈ S, n / m := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [castFiber] using card_castFiber hm hn h a
    _ = (n / m) * S.card := by simp [Nat.mul_comm]

/-- Uniform measure of an arbitrary finite subset of `ZMod n`. -/
lemma residueMeasure_finset_real {n : ℕ} (hn : 0 < n) (S : Finset (ZMod n)) :
    (Erdos277.residueMeasure n).real (S : Set (ZMod n)) =
      (S.card : ℝ) / n := by
  letI : NeZero n := ⟨hn.ne'⟩
  simp [Erdos277.residueMeasure, Measure.real, uniformOn_univ, ZMod.card,
    Set.ncard_coe_finset]

lemma residueMeasure_preimage_cast_real {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) (S : Finset (ZMod m)) :
    (Erdos277.residueMeasure n).real
        {x | ZMod.castHom h (ZMod m) x ∈ S} =
      (Erdos277.residueMeasure m).real (S : Set (ZMod m)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  let T := castPreimage hn h S
  have hTset : (T : Set (ZMod n)) =
      {x | ZMod.castHom h (ZMod m) x ∈ S} := by
    ext x
    change x ∈ T ↔ ZMod.castHom h (ZMod m) x ∈ S
    change x ∈ (Finset.univ.filter fun y : ZMod n =>
      ZMod.castHom h (ZMod m) y ∈ S) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hTset, residueMeasure_finset_real hn T,
    residueMeasure_finset_real hm S, card_preimage_cast hm hn h S]
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := by
    by_contra hk0
    simp only [not_lt, nonpos_iff_eq_zero] at hk0
    subst k
    simp at hn
  push_cast
  field_simp
  rw [Nat.mul_div_cancel_left _ hm]
  ring

lemma card_crt_left_mem_right_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (S : Finset (ZMod m)) (a : ZMod n) :
    letI : NeZero m := ⟨hm.ne'⟩
    letI : NeZero n := ⟨hn.ne'⟩
    letI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
    (Finset.univ.filter fun x : ZMod (m * n) =>
      (ZMod.chineseRemainder hcop x).1 ∈ S ∧
        (ZMod.chineseRemainder hcop x).2 = a).card = S.card := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  let e := ZMod.chineseRemainder hcop
  let U := Finset.univ.filter fun x : ZMod (m * n) =>
    (e x).1 ∈ S ∧ (e x).2 = a
  change U.card = S.card
  apply Finset.card_bij (fun x _ => (e x).1)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  · intro x hx y hy hxy
    apply e.injective
    apply Prod.ext
    · exact hxy
    · rw [(Finset.mem_filter.mp hx).2.2, (Finset.mem_filter.mp hy).2.2]
  · intro b hb
    refine ⟨e.symm (b, a), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      simp [hb]
    · simp

lemma finset_lcm_coprime_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (r : ℕ)
    (hcop : ∀ i ∈ s, (f i).Coprime r) : (s.lcm f).Coprime r := by
  by_contra h
  obtain ⟨p, hp, hpl, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  obtain ⟨i, hi, hpi⟩ := prime_dvd_finset_lcm p hp s f hpl
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpi, hpr⟩) (hcop i hi)

lemma residueMeasure_crt_independent {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (S : Finset (ZMod m)) (a : ZMod n) :
    letI : NeZero m := ⟨hm.ne'⟩
    letI : NeZero n := ⟨hn.ne'⟩
    letI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
    (Erdos277.residueMeasure (m * n)).real
        {x | (ZMod.chineseRemainder hcop x).1 ∈ S ∧
          (ZMod.chineseRemainder hcop x).2 = a} =
      (Erdos277.residueMeasure m).real (S : Set (ZMod m)) *
        (Erdos277.residueMeasure n).real ({a} : Set (ZMod n)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  let U := Finset.univ.filter fun x : ZMod (m * n) =>
    (ZMod.chineseRemainder hcop x).1 ∈ S ∧
      (ZMod.chineseRemainder hcop x).2 = a
  have hUset : (U : Set (ZMod (m * n))) =
      {x | (ZMod.chineseRemainder hcop x).1 ∈ S ∧
        (ZMod.chineseRemainder hcop x).2 = a} := by
    ext x
    simp only [U, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_ofPred_eq]
  rw [← hUset, residueMeasure_finset_real (Nat.mul_pos hm hn) U,
    residueMeasure_finset_real hm S,
    Erdos277.residueMeasure_singleton_real hn a]
  rw [show U.card = S.card from card_crt_left_mem_right_eq hm hn hcop S a]
  push_cast
  field_simp

/-! ## The small-prime fibres -/

abbrev ModIndex (A : ResidueSystem) := {n // n ∈ A.moduli}

def active (Q : ℕ) (A : ResidueSystem) (h : ZMod (smallPeriod Q A))
    (i : ModIndex A) : Prop :=
  ZMod.castHom (small_dvd_smallPeriod Q A i.property) (ZMod (smallPart Q i)) h =
    ZMod.castHom (smallPart_dvd (A.modulus_pos i i.property))
      (ZMod (smallPart Q i)) (A.residue i)

def activeIndices (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) : Finset (ModIndex A) :=
  Finset.univ.filter fun i => active Q A h i

def roughResidue (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    ZMod (roughPart Q i) :=
  ZMod.castHom (roughPart_dvd (A.modulus_pos i i.property))
    (ZMod (roughPart Q i)) (A.residue i)

def roughEvent (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    Set (ZMod (roughPeriod Q A)) :=
  {y | ZMod.castHom (rough_dvd_roughPeriod Q A i.property)
      (ZMod (roughPart Q i)) y = roughResidue Q A i}

def roughCylinder (Q : ℕ) (A : ResidueSystem) :
    Erdos277.CylinderFamily (ZMod (roughPeriod Q A)) ℕ (ModIndex A) where
  event := roughEvent Q A
  support := fun i => (roughPart Q i).primeFactors

lemma roughEvent_measurable (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    MeasurableSet (roughEvent Q A i) := by
  exact MeasurableSet.of_discrete

lemma roughEvent_measureReal (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    (Erdos277.residueMeasure (roughPeriod Q A)).real (roughEvent Q A i) =
      ((roughPart Q i : ℕ) : ℝ)⁻¹ := by
  have hr := roughPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hR := roughPeriod_pos Q A
  let a := roughResidue Q A i
  let S : Finset (ZMod (roughPart Q i)) := {a}
  have hpre := residueMeasure_preimage_cast_real hr hR
    (rough_dvd_roughPeriod Q A i.property) S
  have hS : (S : Set (ZMod (roughPart Q i))) = {a} := by simp [S]
  rw [hS, Erdos277.residueMeasure_singleton_real hr a] at hpre
  simpa [roughEvent, a, S] using hpre

lemma rough_support_disjoint_iff_coprime (Q : ℕ) (A : ResidueSystem)
    (i j : ModIndex A) :
    Disjoint ((roughCylinder Q A).support i) ((roughCylinder Q A).support j) ↔
      (roughPart Q i).Coprime (roughPart Q j) := by
  simpa [roughCylinder] using
    (Nat.disjoint_primeFactors
      (roughPart_pos (Q := Q) (A.modulus_pos i i.property)).ne'
      (roughPart_pos (Q := Q) (A.modulus_pos j j.property)).ne')

lemma castHom_trans_apply {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c)
    (x : ZMod c) :
    ZMod.castHom hab (ZMod a) (ZMod.castHom hbc (ZMod b) x) =
      ZMod.castHom (hab.trans hbc) (ZMod a) x := by
  exact congrArg (fun f => f x) (ZMod.castHom_comp hab hbc)

@[simp] lemma chineseRemainder_fst {m n : ℕ} (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).1 =
      ZMod.castHom (show m ∣ m * n by exact ⟨n, rfl⟩) (ZMod m) x := by
  change (ZMod.cast x : ZMod m × ZMod n).1 = (ZMod.cast x : ZMod m)
  exact Prod.fst_zmod_cast x

@[simp] lemma chineseRemainder_snd {m n : ℕ} (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).2 =
      ZMod.castHom (show n ∣ m * n by exact ⟨m, Nat.mul_comm m n⟩) (ZMod n) x := by
  change (ZMod.cast x : ZMod m × ZMod n).2 = (ZMod.cast x : ZMod n)
  exact Prod.snd_zmod_cast x

/-- Events whose rough prime supports are disjoint are independent after
conditioning on a small-prime fibre. -/
lemma rough_residual_independent (Q : ℕ) (A : ResidueSystem)
    (a : ModIndex A) (s : Finset (ModIndex A))
    (hdis : ∀ i ∈ s,
      Disjoint ((roughCylinder Q A).support i) ((roughCylinder Q A).support a)) :
    (Erdos277.residueMeasure (roughPeriod Q A)).real
        (Erdos277.residual s (roughEvent Q A) ∩ roughEvent Q A a) =
      (Erdos277.residueMeasure (roughPeriod Q A)).real
          (Erdos277.residual s (roughEvent Q A)) *
        (Erdos277.residueMeasure (roughPeriod Q A)).real (roughEvent Q A a) := by
  let B := s.lcm fun i => roughPart Q i
  let r := roughPart Q a
  have hB : 0 < B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    change s.lcm (fun i => roughPart Q i) = 0 at hzero
    rw [Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨i, hi, hiz⟩ := hzero
    exact (roughPart_pos (Q := Q) (A.modulus_pos i i.property)).ne' hiz
  have hr : 0 < r := roughPart_pos (Q := Q) (A.modulus_pos a a.property)
  have hR : 0 < roughPeriod Q A := roughPeriod_pos Q A
  have hBR : B ∣ roughPeriod Q A := by
    apply Finset.lcm_dvd
    intro i hi
    exact rough_dvd_roughPeriod Q A i.property
  have hcop : B.Coprime r := by
    apply finset_lcm_coprime_right
    intro i hi
    exact (rough_support_disjoint_iff_coprime Q A i a).mp (hdis i hi)
  letI : NeZero B := ⟨hB.ne'⟩
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero (roughPeriod Q A) := ⟨hR.ne'⟩
  let S : Finset (ZMod B) := Finset.univ.filter fun u =>
    ∀ i, (hi : i ∈ s) →
      ZMod.castHom (Finset.dvd_lcm hi) (ZMod (roughPart Q i)) u ≠
        roughResidue Q A i
  have hres : Erdos277.residual s (roughEvent Q A) =
      {y | ZMod.castHom hBR (ZMod B) y ∈ S} := by
    ext y
    simp only [Erdos277.residual, Set.mem_compl_iff, Set.mem_iUnion,
      not_exists, roughEvent, Set.mem_ofPred_eq]
    constructor
    · intro hy
      change ZMod.castHom hBR (ZMod B) y ∈ S
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi
      have hc := castHom_trans_apply (Finset.dvd_lcm hi) hBR y
      simpa only [rough_dvd_roughPeriod] using
        fun heq => hy i hi (hc ▸ heq)
    · intro hy i hi heq
      have hy' := (Finset.mem_filter.mp hy).2 i hi
      apply hy'
      have hc := castHom_trans_apply (Finset.dvd_lcm hi) hBR y
      exact hc.trans heq
  have hmrR : B * r ∣ roughPeriod Q A :=
    hcop.mul_dvd_of_dvd_of_dvd hBR (rough_dvd_roughPeriod Q A a.property)
  have hmr : 0 < B * r := Nat.mul_pos hB hr
  let U : Finset (ZMod (B * r)) := Finset.univ.filter fun x =>
    (ZMod.chineseRemainder hcop x).1 ∈ S ∧
      (ZMod.chineseRemainder hcop x).2 = roughResidue Q A a
  have hint : Erdos277.residual s (roughEvent Q A) ∩ roughEvent Q A a =
      {y | ZMod.castHom hmrR (ZMod (B * r)) y ∈ U} := by
    ext y
    rw [Set.mem_inter_iff, hres]
    change (ZMod.castHom hBR (ZMod B) y ∈ S ∧
      ZMod.castHom (rough_dvd_roughPeriod Q A a.property) (ZMod r) y =
        roughResidue Q A a) ↔ _
    change _ ↔ ZMod.castHom hmrR (ZMod (B * r)) y ∈ U
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hyB, hyr⟩
      constructor
      · rw [chineseRemainder_fst, castHom_trans_apply]
        exact hyB
      · rw [chineseRemainder_snd, castHom_trans_apply]
        exact hyr
    · rintro ⟨hyB, hyr⟩
      constructor
      · rw [chineseRemainder_fst, castHom_trans_apply] at hyB
        exact hyB
      · rw [chineseRemainder_snd, castHom_trans_apply] at hyr
        exact hyr
  have hleft := residueMeasure_preimage_cast_real hmr hR hmrR U
  have hsmall := residueMeasure_preimage_cast_real hB hR hBR S
  have hcrt := residueMeasure_crt_independent hB hr hcop S (roughResidue Q A a)
  have hsmall' :
      (Erdos277.residueMeasure (roughPeriod Q A)).real
          (Erdos277.residual s (roughEvent Q A)) =
        (Erdos277.residueMeasure B).real (S : Set (ZMod B)) := by
    rw [hres]
    exact hsmall
  have hleft' :
      (Erdos277.residueMeasure (roughPeriod Q A)).real
          (Erdos277.residual s (roughEvent Q A) ∩ roughEvent Q A a) =
        (Erdos277.residueMeasure (B * r)).real (U : Set (ZMod (B * r))) := by
    rw [hint]
    exact hleft
  have hUset : (U : Set (ZMod (B * r))) =
      {x | (ZMod.chineseRemainder hcop x).1 ∈ S ∧
        (ZMod.chineseRemainder hcop x).2 = roughResidue Q A a} := by
    ext x
    simp only [U, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_ofPred_eq]
  calc
    (Erdos277.residueMeasure (roughPeriod Q A)).real
        (Erdos277.residual s (roughEvent Q A) ∩ roughEvent Q A a) =
        (Erdos277.residueMeasure (B * r)).real (U : Set (ZMod (B * r))) := hleft'
    _ = (Erdos277.residueMeasure B).real (S : Set (ZMod B)) *
          (Erdos277.residueMeasure r).real
            ({roughResidue Q A a} : Set (ZMod r)) := by rw [hUset]; exact hcrt
    _ = (Erdos277.residueMeasure (roughPeriod Q A)).real
          (Erdos277.residual s (roughEvent Q A)) *
        (Erdos277.residueMeasure (roughPeriod Q A)).real (roughEvent Q A a) := by
      rw [hsmall', roughEvent_measureReal Q A a,
        Erdos277.residueMeasure_singleton_real hr (roughResidue Q A a)]

def roughWeight (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) : ℝ :=
  ((roughPart Q i : ℕ) : ℝ)⁻¹

def fibreLoad (Q : ℕ) (A : ResidueSystem) (h : ZMod (smallPeriod Q A)) : ℝ :=
  ∑ i ∈ activeIndices Q A h, roughWeight Q A i

def fibreAlpha (Q : ℕ) (A : ResidueSystem) (h : ZMod (smallPeriod Q A)) : ℝ :=
  ∏ i ∈ activeIndices Q A h, (1 - roughWeight Q A i)

def fibreBeta (Q : ℕ) (A : ResidueSystem) (h : ZMod (smallPeriod Q A)) : ℝ :=
  ∑ i ∈ activeIndices Q A h, roughWeight Q A i *
    ∑ j ∈ (activeIndices Q A h).filter
      (fun j : ModIndex A =>
        ¬(roughPart Q (i : ℕ)).Coprime (roughPart Q (j : ℕ))),
        roughWeight Q A j

lemma roughWeight_nonneg (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    0 ≤ roughWeight Q A i := by
  simp [roughWeight]

lemma dependencyErrorList_le_fibreBeta (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) :
    Erdos277.dependencyErrorList (roughCylinder Q A)
        (Erdos277.residueMeasure (roughPeriod Q A))
        (activeIndices Q A h).toList ≤ fibreBeta Q A h := by
  let I := activeIndices Q A h
  let row : ModIndex A → ℝ := fun i =>
    ∑ j ∈ I.filter (fun j : ModIndex A =>
        ¬(roughPart Q (i : ℕ)).Coprime (roughPart Q (j : ℕ))),
      roughWeight Q A j
  have haux : ∀ l : List (ModIndex A), l.Nodup →
      l.toFinset ⊆ I →
      Erdos277.dependencyErrorList (roughCylinder Q A)
          (Erdos277.residueMeasure (roughPeriod Q A)) l ≤
        ∑ i ∈ l.toFinset, roughWeight Q A i * row i := by
    intro l
    induction l with
    | nil => simp [Erdos277.dependencyErrorList]
    | cons a l ih =>
        intro hnodup hsub
        have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
        have hlnodup := (List.nodup_cons.mp hnodup).2
        have haI : a ∈ I := hsub (by simp)
        have hlI : l.toFinset ⊆ I := by
          intro i hi
          exact hsub (by simp [hi])
        have hih := ih hlnodup hlI
        have hbad :
            ∑ b ∈ l.toFinset.filter (fun b =>
                ¬Disjoint ((roughCylinder Q A).support b)
                  ((roughCylinder Q A).support a)),
                (Erdos277.residueMeasure (roughPeriod Q A)).real
                  ((roughCylinder Q A).event b) ≤ row a := by
          calc
            ∑ b ∈ l.toFinset.filter (fun b =>
                ¬Disjoint ((roughCylinder Q A).support b)
                  ((roughCylinder Q A).support a)),
                (Erdos277.residueMeasure (roughPeriod Q A)).real
                  ((roughCylinder Q A).event b) =
                ∑ b ∈ l.toFinset.filter (fun b =>
                  ¬Disjoint ((roughCylinder Q A).support b)
                    ((roughCylinder Q A).support a)),
                    roughWeight Q A b := by
              apply Finset.sum_congr rfl
              intro b hb
              exact roughEvent_measureReal Q A b
            _ ≤ row a := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro b hb
                have hbdata := Finset.mem_filter.mp hb
                apply Finset.mem_filter.mpr
                refine ⟨hlI hbdata.1, ?_⟩
                intro hcop
                exact hbdata.2
                  ((rough_support_disjoint_iff_coprime Q A b a).2 hcop.symm)
              · intro b hbI hbnot
                exact roughWeight_nonneg Q A b
        simp only [Erdos277.dependencyErrorList]
        rw [List.toFinset_cons, Finset.sum_insert (by simpa using hal)]
        change _ +
            (Erdos277.residueMeasure (roughPeriod Q A)).real
              (roughEvent Q A a) * _ ≤ _
        rw [roughEvent_measureReal Q A a]
        change _ ≤ roughWeight Q A a * row a + _
        calc
          _ ≤ _ + roughWeight Q A a * row a :=
            add_le_add hih
              (mul_le_mul_of_nonneg_left hbad (roughWeight_nonneg Q A a))
          _ = roughWeight Q A a * row a + _ := add_comm _ _
  have hnodup := Finset.nodup_toList I
  have hsub : I.toList.toFinset ⊆ I := by simp
  have := haux I.toList hnodup hsub
  simpa [I, row, fibreBeta] using this

lemma independentResidualList_eq_fibreAlpha (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) :
    Erdos277.independentResidualList (roughCylinder Q A)
        (Erdos277.residueMeasure (roughPeriod Q A))
        (activeIndices Q A h).toList = fibreAlpha Q A h := by
  let I := activeIndices Q A h
  have hrec : ∀ l : List (ModIndex A),
      Erdos277.independentResidualList (roughCylinder Q A)
          (Erdos277.residueMeasure (roughPeriod Q A)) l =
        (l.map fun i =>
          1 - (Erdos277.residueMeasure (roughPeriod Q A)).real
            ((roughCylinder Q A).event i)).prod := by
    intro l
    induction l with
    | nil => simp [Erdos277.independentResidualList]
    | cons a l ih => simp [Erdos277.independentResidualList, ih]
  rw [hrec]
  simp_rw [roughCylinder, roughEvent_measureReal]
  change (I.toList.map (fun i => 1 - roughWeight Q A i)).prod =
    ∏ i ∈ I, (1 - roughWeight Q A i)
  exact I.prod_map_toList (fun i => 1 - roughWeight Q A i)

/-- The FFKPY residual inequality on one small-prime fibre, with the recursive
dependency error dominated by the ordered-pair quantity `fibreBeta`. -/
lemma fibre_residual_measure_lower (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) :
    (Erdos277.residueMeasure (roughPeriod Q A)).real
        (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) ≥
      fibreAlpha Q A h - fibreBeta Q A h := by
  letI : NeZero (roughPeriod Q A) := ⟨(roughPeriod_pos Q A).ne'⟩
  let l := (activeIndices Q A h).toList
  have hdensity := Erdos277.residualDensity_list (roughCylinder Q A)
    (Erdos277.residueMeasure (roughPeriod Q A))
    (roughEvent_measurable Q A)
    (rough_residual_independent Q A) l (Finset.nodup_toList _)
  have hbeta := dependencyErrorList_le_fibreBeta Q A h
  rw [independentResidualList_eq_fibreAlpha] at hdensity
  have hdensity' :
      (Erdos277.residueMeasure (roughPeriod Q A)).real
          (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) ≥
        fibreAlpha Q A h -
          Erdos277.dependencyErrorList (roughCylinder Q A)
            (Erdos277.residueMeasure (roughPeriod Q A))
            (activeIndices Q A h).toList := by
    simpa [l, roughCylinder] using hdensity
  linarith

/-! ## Uniform estimates in a fixed natural window -/

/-- A natural-valued version of the multiplicative window, used for the
finite estimates.  The final real window is reduced to this one by taking a
ceiling. -/
def ResidueSystem.InNatWindow (A : ResidueSystem) (K N : ℕ) : Prop :=
  ∀ n ∈ A.moduli, N ≤ n ∧ n ≤ K * N

def activeFibers (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    Finset (ZMod (smallPeriod Q A)) :=
  Finset.univ.filter fun h => active Q A h i

lemma card_activeFibers (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    (activeFibers Q A i).card = smallPeriod Q A / smallPart Q i := by
  let a := ZMod.castHom (smallPart_dvd (A.modulus_pos i i.property))
    (ZMod (smallPart Q i)) (A.residue i)
  have hcard := card_castFiber
    (smallPart_pos (Q := Q) (A.modulus_pos i i.property))
    (smallPeriod_pos Q A) (small_dvd_smallPeriod Q A i.property) a
  rw [← hcard]
  congr 1
  ext h
  simp only [activeFibers, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_castFiber]
  unfold active
  dsimp only [a]
  rfl

lemma periodDiv_mul_roughWeight (Q : ℕ) (A : ResidueSystem)
    (i : ModIndex A) :
    ((smallPeriod Q A / smallPart Q i : ℕ) : ℝ) * roughWeight Q A i =
      (smallPeriod Q A : ℝ) * ((i : ℕ) : ℝ)⁻¹ := by
  have hs : 0 < smallPart Q i :=
    smallPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hr : 0 < roughPart Q i :=
    roughPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hd := small_dvd_smallPeriod Q A i.property
  have hfact : ((i : ℕ) : ℝ) =
      (smallPart Q i : ℝ) * (roughPart Q i : ℝ) := by
    exact_mod_cast (smallPart_mul_roughPart (Q := Q)
      (A.modulus_pos i i.property).ne').symm
  have hsR : (0 : ℝ) < (smallPart Q i : ℕ) := by exact_mod_cast hs
  rw [roughWeight, Nat.cast_div hd hsR.ne', hfact, div_eq_mul_inv, mul_inv]
  ring

/-- Double-counting active congruences over the small-prime fibres. -/
lemma sum_fibreLoad (Q : ℕ) (A : ResidueSystem) :
    ∑ h : ZMod (smallPeriod Q A), fibreLoad Q A h =
      (smallPeriod Q A : ℝ) *
        ∑ i : ModIndex A, (((i : ℕ) : ℝ)⁻¹) := by
  letI : NeZero (smallPeriod Q A) := ⟨(smallPeriod_pos Q A).ne'⟩
  calc
    ∑ h : ZMod (smallPeriod Q A), fibreLoad Q A h =
        ∑ h : ZMod (smallPeriod Q A),
          ∑ i : ModIndex A, if active Q A h i then roughWeight Q A i else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      simp [fibreLoad, activeIndices, Finset.sum_filter]
    _ = ∑ i : ModIndex A,
          ∑ h : ZMod (smallPeriod Q A),
            if active Q A h i then roughWeight Q A i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : ModIndex A,
          ((activeFibers Q A i).card : ℝ) * roughWeight Q A i := by
      apply Finset.sum_congr rfl
      intro i _
      change (∑ h ∈ (Finset.univ : Finset (ZMod (smallPeriod Q A))),
        if active Q A h i then roughWeight Q A i else 0) = _
      rw [← Finset.sum_filter]
      simp [activeFibers, mul_comm]
    _ = ∑ i : ModIndex A,
          (smallPeriod Q A : ℝ) * (((i : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [card_activeFibers]
      exact periodDiv_mul_roughWeight Q A i
    _ = (smallPeriod Q A : ℝ) *
        ∑ i : ModIndex A, (((i : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]

lemma card_moduli_le_window (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) : A.moduli.card ≤ K * N + 1 := by
  have hsub : A.moduli ⊆ Finset.range (K * N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hw n hn).2)
  simpa using Finset.card_le_card hsub

lemma sum_moduli_inv_le (A : ResidueSystem) {K N : ℕ} (hN : 0 < N)
    (hw : A.InNatWindow K N) :
    (∑ i : ModIndex A, (((i : ℕ) : ℝ)⁻¹)) ≤ K + 1 := by
  have hterm : ∀ i : ModIndex A,
      (((i : ℕ) : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ := by
    intro i
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hNi : (N : ℝ) ≤ (i : ℕ) := by
      exact_mod_cast (hw i i.property).1
    simpa only [one_div] using one_div_le_one_div_of_le hNR hNi
  calc
    (∑ i : ModIndex A, (((i : ℕ) : ℝ)⁻¹)) ≤
        ∑ _i : ModIndex A, (N : ℝ)⁻¹ :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (A.moduli.card : ℝ) * (N : ℝ)⁻¹ := by simp [mul_comm]
    _ ≤ ((K * N + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      gcongr
      exact_mod_cast card_moduli_le_window A hw
    _ ≤ K + 1 := by
      push_cast
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
      field_simp
      nlinarith

lemma sum_fibreLoad_le (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N) :
    ∑ h : ZMod (smallPeriod Q A), fibreLoad Q A h ≤
      (smallPeriod Q A : ℝ) * (K + 1) := by
  rw [sum_fibreLoad]
  exact mul_le_mul_of_nonneg_left (sum_moduli_inv_le A hN hw) (by positivity)

def highLoadFibers (Q K : ℕ) (A : ResidueSystem) :
    Finset (ZMod (smallPeriod Q A)) :=
  Finset.univ.filter fun h => 4 * (K + 1 : ℝ) < fibreLoad Q A h

lemma fibreLoad_nonneg (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) : 0 ≤ fibreLoad Q A h := by
  exact Finset.sum_nonneg fun i _ => roughWeight_nonneg Q A i

/-- Finite Markov inequality for the fibre loads. -/
lemma four_mul_card_highLoad_le (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N) :
    4 * (highLoadFibers Q K A).card ≤ smallPeriod Q A := by
  let H := highLoadFibers Q K A
  have hlarge : (H.card : ℝ) * (4 * (K + 1 : ℝ)) ≤
      ∑ h ∈ H, fibreLoad Q A h := by
    calc
      (H.card : ℝ) * (4 * (K + 1 : ℝ)) =
          ∑ _h ∈ H, 4 * (K + 1 : ℝ) := by simp
      _ ≤ ∑ h ∈ H, fibreLoad Q A h := by
        apply Finset.sum_le_sum
        intro h hh
        have hh' : h ∈ highLoadFibers Q K A := hh
        exact (Finset.mem_filter.mp hh').2.le
  have hsubset : H ⊆ (Finset.univ : Finset (ZMod (smallPeriod Q A))) :=
    fun h _ => Finset.mem_univ h
  have hsumsub : (∑ h ∈ H, fibreLoad Q A h) ≤
      ∑ h : ZMod (smallPeriod Q A), fibreLoad Q A h := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun h _ _ => fibreLoad_nonneg Q A h)
  have htotal := sum_fibreLoad_le Q A hN hw
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hreal : (4 * H.card : ℕ) ≤ smallPeriod Q A := by
    exact_mod_cast (by
      push_cast
      nlinarith [hlarge.trans (hsumsub.trans htotal)] :
        (4 : ℝ) * H.card ≤ smallPeriod Q A)
  exact hreal

def smoothIndices (Q : ℕ) (A : ResidueSystem) : Finset (ModIndex A) :=
  Finset.univ.filter fun i => roughPart Q i = 1

def smoothBadFibers (Q : ℕ) (A : ResidueSystem) :
    Finset (ZMod (smallPeriod Q A)) :=
  Finset.univ.filter fun h =>
    ∃ i ∈ smoothIndices Q A, active Q A h i

lemma card_smoothBad_le_sum_active (Q : ℕ) (A : ResidueSystem) :
    (smoothBadFibers Q A).card ≤
      ∑ i ∈ smoothIndices Q A, (activeFibers Q A i).card := by
  let B := smoothBadFibers Q A
  let J := smoothIndices Q A
  have hsub : B ⊆ J.biUnion (activeFibers Q A) := by
    intro h hh
    have hh' : h ∈ smoothBadFibers Q A := hh
    obtain ⟨i, hiJ, hia⟩ := (Finset.mem_filter.mp hh').2
    apply Finset.mem_biUnion.mpr
    exact ⟨i, hiJ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hia⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma card_smoothIndices_le (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) :
    (smoothIndices Q A).card ≤
      (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card := by
  let f : ModIndex A → ℕ := fun i => i
  have hinj : Function.Injective f := fun i j hij => Subtype.ext hij
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    have hir : roughPart Q i = 1 := (Finset.mem_filter.mp hi).2
    apply Nat.mem_smoothNumbersUpTo.mpr
    exact ⟨(hw i i.property).2,
      roughPart_eq_one_smooth (A.modulus_pos i i.property) hir⟩
  · exact hinj.injOn

lemma active_card_le_period_div_N (Q : ℕ) (A : ResidueSystem)
    {N : ℕ} (hN : 0 < N) (hwlower : ∀ n ∈ A.moduli, N ≤ n)
    (i : ModIndex A) (hir : roughPart Q i = 1) :
    (activeFibers Q A i).card ≤ smallPeriod Q A / N := by
  rw [card_activeFibers]
  have hi : smallPart Q i = (i : ℕ) := by
    have hfactor := smallPart_mul_roughPart (Q := Q)
      (A.modulus_pos i i.property).ne'
    simpa [hir] using hfactor
  rw [hi]
  exact Nat.div_le_div_left (hwlower i i.property) hN

/-- The union-bound estimate for fibres containing a completely smooth
modulus. -/
lemma four_mul_card_smoothBad_le (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N)
    (hsparse : 4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ N) :
    4 * (smoothBadFibers Q A).card ≤ smallPeriod Q A := by
  let B := smoothBadFibers Q A
  let J := smoothIndices Q A
  have hactive : ∀ i ∈ J,
      (activeFibers Q A i).card ≤ smallPeriod Q A / N := by
    intro i hi
    exact active_card_le_period_div_N Q A hN (fun n hn => (hw n hn).1) i
      (Finset.mem_filter.mp hi).2
  have hsum : B.card ≤ J.card * (smallPeriod Q A / N) := by
    calc
      B.card ≤ ∑ i ∈ J, (activeFibers Q A i).card :=
        card_smoothBad_le_sum_active Q A
      _ ≤ ∑ _i ∈ J, smallPeriod Q A / N :=
        Finset.sum_le_sum hactive
      _ = J.card * (smallPeriod Q A / N) := by simp
  have hJ := card_smoothIndices_le Q A hw
  calc
    4 * B.card ≤ 4 * (J.card * (smallPeriod Q A / N)) :=
      Nat.mul_le_mul_left 4 hsum
    _ = (4 * J.card) * (smallPeriod Q A / N) :=
      (Nat.mul_assoc 4 J.card _).symm
    _ ≤ N * (smallPeriod Q A / N) :=
      Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left 4 hJ).trans hsparse)
    _ ≤ smallPeriod Q A := Nat.mul_div_le _ _

def goodFibers (Q K : ℕ) (A : ResidueSystem) :
    Finset (ZMod (smallPeriod Q A)) :=
  Finset.univ \ (highLoadFibers Q K A ∪ smoothBadFibers Q A)

lemma two_mul_period_le_four_mul_good (Q : ℕ) (A : ResidueSystem)
    {K N : ℕ} (hN : 0 < N) (hw : A.InNatWindow K N)
    (hsparse : 4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ N) :
    2 * smallPeriod Q A ≤ 4 * (goodFibers Q K A).card := by
  let H := highLoadFibers Q K A
  let B := smoothBadFibers Q A
  let G := goodFibers Q K A
  have hH : 4 * H.card ≤ smallPeriod Q A :=
    four_mul_card_highLoad_le Q A hN hw
  have hB : 4 * B.card ≤ smallPeriod Q A :=
    four_mul_card_smoothBad_le Q A hN hw hsparse
  have hU : (H ∪ B).card ≤ H.card + B.card := Finset.card_union_le H B
  have hpart : G.card + (H ∪ B).card = smallPeriod Q A := by
    have hsub : H ∪ B ⊆ (Finset.univ : Finset (ZMod (smallPeriod Q A))) :=
      fun x _ => Finset.mem_univ x
    simpa [G, goodFibers] using Finset.card_sdiff_add_card_eq_card hsub
  change 2 * smallPeriod Q A ≤ 4 * G.card
  omega

lemma roughWeight_le_one (Q : ℕ) (A : ResidueSystem) (i : ModIndex A) :
    roughWeight Q A i ≤ 1 := by
  have hr : (1 : ℝ) ≤ roughPart Q i := by
    exact_mod_cast (roughPart_pos (Q := Q) (A.modulus_pos i i.property))
  simpa [roughWeight] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr

lemma fibreAlpha_nonneg (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) : 0 ≤ fibreAlpha Q A h := by
  apply Finset.prod_nonneg
  intro i hi
  exact sub_nonneg.mpr (roughWeight_le_one Q A i)

lemma roughWeight_le_half_of_ne_one (Q : ℕ) (A : ResidueSystem)
    (i : ModIndex A) (hi : roughPart Q i ≠ 1) :
    roughWeight Q A i ≤ (1 / 2 : ℝ) := by
  have hrpos := roughPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hr2 : 2 ≤ roughPart Q i := by omega
  have hrR : (0 : ℝ) < roughPart Q i := by exact_mod_cast hrpos
  simpa [roughWeight, one_div] using
    (one_div_le_one_div hrR (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast hr2)

lemma fibreAlpha_lower_of_good (Q K : ℕ) (A : ResidueSystem)
    {h : ZMod (smallPeriod Q A)} (hh : h ∈ goodFibers Q K A) :
    Real.exp (-8 * (K + 1 : ℝ)) ≤ fibreAlpha Q A h := by
  have hgood := Finset.mem_sdiff.mp hh
  have hnotH : h ∉ highLoadFibers Q K A := by
    intro hH
    exact hgood.2 (Finset.mem_union_left _ hH)
  have hnotB : h ∉ smoothBadFibers Q A := by
    intro hB
    exact hgood.2 (Finset.mem_union_right _ hB)
  have hload : fibreLoad Q A h ≤ 4 * (K + 1 : ℝ) := by
    exact le_of_not_gt (fun hgt => hnotH (by
      simp [highLoadFibers, hgt]))
  have hrough : ∀ i ∈ activeIndices Q A h, roughPart Q i ≠ 1 := by
    intro i hi hir
    apply hnotB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hir⟩,
      (Finset.mem_filter.mp hi).2⟩
  have hterm : ∀ i ∈ activeIndices Q A h,
      Real.exp (-2 * roughWeight Q A i) ≤ 1 - roughWeight Q A i := by
    intro i hi
    exact Erdos277.exp_neg_two_mul_le_one_sub (roughWeight_nonneg Q A i)
      (roughWeight_le_half_of_ne_one Q A i (hrough i hi))
  have hprod : Real.exp (-2 * fibreLoad Q A h) ≤ fibreAlpha Q A h := by
    calc
      Real.exp (-2 * fibreLoad Q A h) =
          ∏ i ∈ activeIndices Q A h,
            Real.exp (-2 * roughWeight Q A i) := by
        rw [fibreLoad, ← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
      _ ≤ ∏ i ∈ activeIndices Q A h, (1 - roughWeight Q A i) := by
        exact Finset.prod_le_prod
          (fun i hi => (Real.exp_pos _).le) hterm
      _ = fibreAlpha Q A h := rfl
  have hexp : Real.exp (-8 * (K + 1 : ℝ)) ≤
      Real.exp (-2 * fibreLoad Q A h) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hexp.trans hprod

/-- The averaged independent product has a fixed positive lower bound on
the good half of the fibres. -/
lemma sum_fibreAlpha_lower (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N)
    (hsparse : 4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ N) :
    (smallPeriod Q A : ℝ) * Real.exp (-8 * (K + 1 : ℝ)) ≤
      2 * ∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h := by
  let G := goodFibers Q K A
  have hcard := two_mul_period_le_four_mul_good Q A hN hw hsparse
  have hrestricted : (G.card : ℝ) * Real.exp (-8 * (K + 1 : ℝ)) ≤
      ∑ h ∈ G, fibreAlpha Q A h := by
    calc
      (G.card : ℝ) * Real.exp (-8 * (K + 1 : ℝ)) =
          ∑ _h ∈ G, Real.exp (-8 * (K + 1 : ℝ)) := by simp
      _ ≤ ∑ h ∈ G, fibreAlpha Q A h := by
        exact Finset.sum_le_sum fun h hh => fibreAlpha_lower_of_good Q K A hh
  have hfull : (∑ h ∈ G, fibreAlpha Q A h) ≤
      ∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun h _ => Finset.mem_univ h) (fun h _ _ => fibreAlpha_nonneg Q A h)
  have hcardR : (2 : ℝ) * smallPeriod Q A ≤ 4 * G.card := by
    exact_mod_cast hcard
  have he : 0 < Real.exp (-8 * (K + 1 : ℝ)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_right hcardR he.le,
    hrestricted.trans hfull]

def sparseBase (Q K : ℕ) : ℕ :=
  4 * 2 ^ (Q + 1).primesBelow.card * K + 1

def sparseScale (Q K : ℕ) : ℕ := (sparseBase Q K) ^ 2

lemma sparseScale_pos (Q K : ℕ) : 0 < sparseScale Q K := by
  simp [sparseScale, sparseBase]

/-- An explicit square scale at which the elementary smooth-number bound
makes the smooth-bad fibres occupy at most one quarter of the small period. -/
lemma smooth_card_sparse_at_scale (Q K : ℕ) (hK : 1 ≤ K) :
    4 * (Nat.smoothNumbersUpTo (K * sparseScale Q K) (Q + 1)).card ≤
      sparseScale Q K := by
  let P := 2 ^ (Q + 1).primesBelow.card
  let L := sparseBase Q K
  have hL : L = 4 * P * K + 1 := rfl
  have hbound := Nat.smoothNumbersUpTo_card_le (K * sparseScale Q K) (Q + 1)
  have harg : K * sparseScale Q K ≤ (K * L) ^ 2 := by
    simp only [sparseScale, L]
    nlinarith
  have hsqrt : (K * sparseScale Q K).sqrt ≤ K * L := by
    calc
      (K * sparseScale Q K).sqrt ≤ ((K * L) ^ 2).sqrt :=
        Nat.sqrt_le_sqrt harg
      _ = K * L := Nat.sqrt_eq' _
  have hcount :
      (Nat.smoothNumbersUpTo (K * sparseScale Q K) (Q + 1)).card ≤
        P * (K * L) := hbound.trans (Nat.mul_le_mul_left P hsqrt)
  have hfinal : 4 * (P * (K * L)) ≤ L ^ 2 := by
    rw [hL]
    nlinarith
  simpa [sparseScale, L] using
    (Nat.mul_le_mul_left 4 hcount |>.trans hfinal)

def simultaneousFibers (Q : ℕ) (A : ResidueSystem)
    (i j : ModIndex A) : Finset (ZMod (smallPeriod Q A)) :=
  Finset.univ.filter fun h => active Q A h i ∧ active Q A h j

/-- Two small-part congruences have either no common solution or one residue
class modulo their least common multiple. -/
lemma card_simultaneousFibers_le (Q : ℕ) (A : ResidueSystem)
    (i j : ModIndex A) :
    (simultaneousFibers Q A i j).card ≤
      smallPeriod Q A / (smallPart Q i).lcm (smallPart Q j) := by
  let M := smallPeriod Q A
  let s := smallPart Q i
  let t := smallPart Q j
  let L := s.lcm t
  have hs : 0 < s := smallPart_pos (Q := Q) (A.modulus_pos i i.property)
  have ht : 0 < t := smallPart_pos (Q := Q) (A.modulus_pos j j.property)
  have hM : 0 < M := smallPeriod_pos Q A
  have hLM : L ∣ M := Nat.lcm_dvd
    (small_dvd_smallPeriod Q A i.property)
    (small_dvd_smallPeriod Q A j.property)
  have hL : 0 < L := Nat.lcm_pos hs ht
  by_cases hne : (simultaneousFibers Q A i j).Nonempty
  · obtain ⟨h₀, hh₀⟩ := hne
    let a : ZMod L := ZMod.castHom hLM (ZMod L) h₀
    have hsub : simultaneousFibers Q A i j ⊆ castFiber hM hLM a := by
      intro h hh
      have hhmem : h ∈ simultaneousFibers Q A i j := hh
      have hh₀mem : h₀ ∈ simultaneousFibers Q A i j := hh₀
      have hh' := (Finset.mem_filter.mp hhmem).2
      have hh₀' := (Finset.mem_filter.mp hh₀mem).2
      have hsi : ZMod.castHom (small_dvd_smallPeriod Q A i.property)
          (ZMod s) h =
          ZMod.castHom (small_dvd_smallPeriod Q A i.property) (ZMod s) h₀ :=
        hh'.1.trans hh₀'.1.symm
      have htj : ZMod.castHom (small_dvd_smallPeriod Q A j.property)
          (ZMod t) h =
          ZMod.castHom (small_dvd_smallPeriod Q A j.property) (ZMod t) h₀ :=
        hh'.2.trans hh₀'.2.symm
      have hcast_s (x : ZMod M) :
          ZMod.castHom (small_dvd_smallPeriod Q A i.property) (ZMod s) x =
            (x.val : ZMod s) := by
        simpa only [map_natCast] using congrArg
          (ZMod.castHom (small_dvd_smallPeriod Q A i.property) (ZMod s))
          (ZMod.natCast_zmod_val x).symm
      have hcast_t (x : ZMod M) :
          ZMod.castHom (small_dvd_smallPeriod Q A j.property) (ZMod t) x =
            (x.val : ZMod t) := by
        simpa only [map_natCast] using congrArg
          (ZMod.castHom (small_dvd_smallPeriod Q A j.property) (ZMod t))
          (ZMod.natCast_zmod_val x).symm
      have hsmod : h.val ≡ h₀.val [MOD s] := by
        rw [← ZMod.natCast_eq_natCast_iff, ← hcast_s h, ← hcast_s h₀]
        exact hsi
      have htmod : h.val ≡ h₀.val [MOD t] := by
        rw [← ZMod.natCast_eq_natCast_iff, ← hcast_t h, ← hcast_t h₀]
        exact htj
      have hLmod : h.val ≡ h₀.val [MOD L] :=
        Nat.mod_lcm hsmod htmod
      have hcast_L (x : ZMod M) :
          ZMod.castHom hLM (ZMod L) x = (x.val : ZMod L) := by
        simpa only [map_natCast] using congrArg (ZMod.castHom hLM (ZMod L))
          (ZMod.natCast_zmod_val x).symm
      rw [mem_castFiber]
      calc
        ZMod.castHom hLM (ZMod L) h = (h.val : ZMod L) := hcast_L h
        _ = (h₀.val : ZMod L) := by
          rw [ZMod.natCast_eq_natCast_iff]
          exact hLmod
        _ = ZMod.castHom hLM (ZMod L) h₀ := (hcast_L h₀).symm
    calc
      (simultaneousFibers Q A i j).card ≤ (castFiber hM hLM a).card :=
        Finset.card_le_card hsub
      _ = M / L := card_castFiber hL hM hLM a
  · have hempty : simultaneousFibers Q A i j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

lemma lcm_small_mul_rough_cast (Q : ℕ) (A : ResidueSystem)
    (i j : ModIndex A) :
    (((smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
        ((roughPart Q i : ℕ) : ℝ) * ((roughPart Q j : ℕ) : ℝ) =
      (((i : ℕ) : ℝ) * ((j : ℕ) : ℝ)) /
        ((smallPart Q i).gcd (smallPart Q j) : ℕ) := by
  have hsi := smallPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hsj := smallPart_pos (Q := Q) (A.modulus_pos j j.property)
  have hg : 0 < (smallPart Q i).gcd (smallPart Q j) := Nat.gcd_pos_of_pos_left _ hsi
  have hfi : ((i : ℕ) : ℝ) =
      (smallPart Q i : ℝ) * (roughPart Q i : ℝ) := by
    exact_mod_cast (smallPart_mul_roughPart (Q := Q)
      (A.modulus_pos i i.property).ne').symm
  have hfj : ((j : ℕ) : ℝ) =
      (smallPart Q j : ℝ) * (roughPart Q j : ℝ) := by
    exact_mod_cast (smallPart_mul_roughPart (Q := Q)
      (A.modulus_pos j j.property).ne').symm
  have hlcmg : (smallPart Q i).lcm (smallPart Q j) *
      (smallPart Q i).gcd (smallPart Q j) =
        smallPart Q i * smallPart Q j := Nat.lcm_mul_gcd _ _
  have hlcmgR : (((smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
      ((smallPart Q i).gcd (smallPart Q j) : ℕ) =
        (smallPart Q i : ℝ) * (smallPart Q j : ℝ) := by exact_mod_cast hlcmg
  apply (eq_div_iff (by exact_mod_cast hg.ne')).2
  rw [hfi, hfj]
  calc
    (((smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
          (roughPart Q i : ℝ) * (roughPart Q j : ℝ) *
          ((smallPart Q i).gcd (smallPart Q j) : ℕ) =
        ((((smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
          ((smallPart Q i).gcd (smallPart Q j) : ℕ)) *
          (roughPart Q i : ℝ) * (roughPart Q j : ℝ) := by ring
    _ = ((smallPart Q i : ℝ) * (smallPart Q j : ℝ)) *
          (roughPart Q i : ℝ) * (roughPart Q j : ℝ) := by rw [hlcmgR]
    _ = ((smallPart Q i : ℝ) * (roughPart Q i : ℝ)) *
          ((smallPart Q j : ℝ) * (roughPart Q j : ℝ)) := by ring

def dependentPairs (Q : ℕ) (A : ResidueSystem) :
    Finset (ModIndex A × ModIndex A) :=
  (Finset.univ.product Finset.univ).filter fun ij =>
    ¬(roughPart Q (ij.1 : ℕ)).Coprime (roughPart Q (ij.2 : ℕ))

def pairKernel (Q : ℕ) (A : ResidueSystem) : ℝ :=
  ∑ ij ∈ dependentPairs Q A,
    ((smallPart Q ij.1).gcd (smallPart Q ij.2) : ℕ) *
      ((((ij.1 : ℕ) : ℝ)⁻¹) * (((ij.2 : ℕ) : ℝ)⁻¹))

lemma periodDivL_mul_weights_eq_kernelTerm (Q : ℕ) (A : ResidueSystem)
    (i j : ModIndex A) :
    ((smallPeriod Q A / (smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
        roughWeight Q A i * roughWeight Q A j =
      (smallPeriod Q A : ℝ) *
        (((smallPart Q i).gcd (smallPart Q j) : ℕ) *
          ((((i : ℕ) : ℝ)⁻¹) * (((j : ℕ) : ℝ)⁻¹))) := by
  have hL : (smallPart Q i).lcm (smallPart Q j) ∣ smallPeriod Q A :=
    Nat.lcm_dvd (small_dvd_smallPeriod Q A i.property)
      (small_dvd_smallPeriod Q A j.property)
  have hLp : 0 < (smallPart Q i).lcm (smallPart Q j) := Nat.lcm_pos
    (smallPart_pos (Q := Q) (A.modulus_pos i i.property))
    (smallPart_pos (Q := Q) (A.modulus_pos j j.property))
  have hri : 0 < roughPart Q i :=
    roughPart_pos (Q := Q) (A.modulus_pos i i.property)
  have hrj : 0 < roughPart Q j :=
    roughPart_pos (Q := Q) (A.modulus_pos j j.property)
  have hii : 0 < (i : ℕ) := A.modulus_pos i i.property
  have hij : 0 < (j : ℕ) := A.modulus_pos j j.property
  have hLpR : (0 : ℝ) < ((smallPart Q i).lcm (smallPart Q j) : ℕ) := by
    exact_mod_cast hLp
  rw [roughWeight, roughWeight, Nat.cast_div hL hLpR.ne']
  have hid := lcm_small_mul_rough_cast Q A i j
  have hg : (0 : ℝ) < (smallPart Q i).gcd (smallPart Q j) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _
      (smallPart_pos (Q := Q) (A.modulus_pos i i.property))
  have hprod : (((smallPart Q i).lcm (smallPart Q j) : ℕ) : ℝ) *
      (roughPart Q i : ℝ) * (roughPart Q j : ℝ) *
        ((smallPart Q i).gcd (smallPart Q j) : ℕ) =
      ((i : ℕ) : ℝ) * ((j : ℕ) : ℝ) := by
    exact (eq_div_iff hg.ne').mp hid
  have hriR : (0 : ℝ) < (roughPart Q i : ℕ) := by exact_mod_cast hri
  have hrjR : (0 : ℝ) < (roughPart Q j : ℕ) := by exact_mod_cast hrj
  have hiiR : (0 : ℝ) < (i : ℕ) := by exact_mod_cast hii
  have hijR : (0 : ℝ) < (j : ℕ) := by exact_mod_cast hij
  field_simp [hLpR.ne', hriR.ne', hrjR.ne', hiiR.ne', hijR.ne']
  nlinarith [hprod]

/-- Averaging the ordered dependency error over all small fibres reduces it
to the standard arithmetic pair kernel. -/
lemma sum_fibreBeta_le_pairKernel (Q : ℕ) (A : ResidueSystem) :
    ∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h ≤
      (smallPeriod Q A : ℝ) * pairKernel Q A := by
  letI : NeZero (smallPeriod Q A) := ⟨(smallPeriod_pos Q A).ne'⟩
  have hrewrite :
      ∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h =
        ∑ ij ∈ dependentPairs Q A,
          (simultaneousFibers Q A ij.1 ij.2).card *
            (roughWeight Q A ij.1 * roughWeight Q A ij.2) := by
    let G : ModIndex A × ModIndex A → ℝ := fun ij =>
      if ¬(roughPart Q (ij.1 : ℕ)).Coprime (roughPart Q (ij.2 : ℕ)) then
        (simultaneousFibers Q A ij.1 ij.2).card *
          (roughWeight Q A ij.1 * roughWeight Q A ij.2)
      else 0
    simp only [fibreBeta, activeIndices, dependentPairs, simultaneousFibers]
    simp_rw [Finset.sum_filter]
    change _ = ∑ ij ∈ (Finset.univ.product Finset.univ), G ij
    trans ∑ i : ModIndex A, ∑ j : ModIndex A, G (i, j)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      trans ∑ j : ModIndex A, ∑ h : ZMod (smallPeriod Q A),
          if active Q A h i then
            roughWeight Q A i *
              (if active Q A h j then
                if ¬(roughPart Q (i : ℕ)).Coprime (roughPart Q (j : ℕ)) then
                  roughWeight Q A j else 0
              else 0)
          else 0
      · calc
          (∑ h : ZMod (smallPeriod Q A),
              if active Q A h i then
                roughWeight Q A i *
                  ∑ j : ModIndex A,
                    if active Q A h j then
                      if ¬(roughPart Q (i : ℕ)).Coprime
                          (roughPart Q (j : ℕ)) then
                        roughWeight Q A j else 0
                    else 0
              else 0) =
            ∑ h : ZMod (smallPeriod Q A), ∑ j : ModIndex A,
              if active Q A h i then
                roughWeight Q A i *
                  (if active Q A h j then
                    if ¬(roughPart Q (i : ℕ)).Coprime
                        (roughPart Q (j : ℕ)) then
                      roughWeight Q A j else 0
                  else 0)
              else 0 := by
                apply Finset.sum_congr rfl
                intro h hh
                by_cases hai : active Q A h i
                · simp only [hai, if_true, Finset.mul_sum]
                · simp [hai]
          _ = ∑ j : ModIndex A, ∑ h : ZMod (smallPeriod Q A),
              if active Q A h i then
                roughWeight Q A i *
                  (if active Q A h j then
                    if ¬(roughPart Q (i : ℕ)).Coprime
                        (roughPart Q (j : ℕ)) then
                      roughWeight Q A j else 0
                  else 0)
              else 0 := Finset.sum_comm
      · apply Finset.sum_congr rfl
        intro j _
        dsimp only [G]
        by_cases hdep : ¬(roughPart Q (i : ℕ)).Coprime (roughPart Q (j : ℕ))
        · simp only [hdep, not_false_eq_true, if_true]
          calc
            (∑ h : ZMod (smallPeriod Q A),
                if active Q A h i then
                  roughWeight Q A i *
                    (if active Q A h j then roughWeight Q A j else 0)
                else 0) =
              ∑ h : ZMod (smallPeriod Q A),
                if active Q A h i ∧ active Q A h j then
                  roughWeight Q A i * roughWeight Q A j else 0 := by
                apply Finset.sum_congr rfl
                intro h hh
                by_cases hi : active Q A h i <;>
                  by_cases hj : active Q A h j <;> simp [hi, hj]
            _ = ∑ h ∈ simultaneousFibers Q A i j,
                  roughWeight Q A i * roughWeight Q A j := by
                rw [simultaneousFibers, Finset.sum_filter]
            _ = (simultaneousFibers Q A i j).card *
                  (roughWeight Q A i * roughWeight Q A j) := by simp
        · simp [hdep]
    · exact (Finset.sum_product
        (Finset.univ : Finset (ModIndex A))
        (Finset.univ : Finset (ModIndex A)) G).symm
  rw [hrewrite, pairKernel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ij hij
  have hcard := card_simultaneousFibers_le Q A ij.1 ij.2
  have hw0 : 0 ≤ roughWeight Q A ij.1 * roughWeight Q A ij.2 :=
    mul_nonneg (roughWeight_nonneg Q A ij.1) (roughWeight_nonneg Q A ij.2)
  calc
    ((simultaneousFibers Q A ij.1 ij.2).card : ℝ) *
        (roughWeight Q A ij.1 * roughWeight Q A ij.2) ≤
      ((smallPeriod Q A /
        (smallPart Q ij.1).lcm (smallPart Q ij.2) : ℕ) : ℝ) *
          (roughWeight Q A ij.1 * roughWeight Q A ij.2) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hw0
    _ = (smallPeriod Q A : ℝ) *
        (((smallPart Q ij.1).gcd (smallPart Q ij.2) : ℕ) *
          ((((ij.1 : ℕ) : ℝ)⁻¹) * (((ij.2 : ℕ) : ℝ)⁻¹))) := by
      rw [← periodDivL_mul_weights_eq_kernelTerm]
      ring

lemma prime_dvd_roughPart_gt {Q d p : ℕ} (hd : 0 < d) (hp : p.Prime)
    (hpd : p ∣ roughPart Q d) : Q < p := by
  have hpos := hp.factorization_pos_of_dvd
    (roughPart_pos (Q := Q) hd).ne' hpd
  rw [factorization_roughPart, roughFactorization, Finsupp.filter_apply] at hpos
  split at hpos
  · assumption
  · simp at hpos

def pairSmallKey (Q : ℕ) {A : ResidueSystem}
    (ij : ModIndex A × ModIndex A) : ℕ :=
  (smallPart Q ij.1).gcd (smallPart Q ij.2)

def pairPrimeKey (Q : ℕ) {A : ResidueSystem}
    (ij : ModIndex A × ModIndex A) : ℕ :=
  ((roughPart Q ij.1).gcd (roughPart Q ij.2)).minFac

def keyPair (Q : ℕ) {A : ResidueSystem}
    (ij : ModIndex A × ModIndex A) : (ℕ × ℕ) × (ModIndex A × ModIndex A) :=
  ((pairSmallKey Q ij, pairPrimeKey Q ij), ij)

lemma keyPair_injective (Q : ℕ) {A : ResidueSystem} :
    Function.Injective (keyPair Q (A := A)) := by
  intro x y h
  exact congrArg Prod.snd h

def smallKeys (Q K N : ℕ) : Finset ℕ :=
  Nat.smoothNumbersUpTo (K * N) (Q + 1)

def largePrimeKeys (Q K N : ℕ) : Finset ℕ :=
  (Finset.range (K * N + 1)).filter fun p => p.Prime ∧ Q < p

def groupedPairs (Q K N : ℕ) (A : ResidueSystem) :
    Finset ((ℕ × ℕ) × (ModIndex A × ModIndex A)) :=
  (((smallKeys Q K N).product (largePrimeKeys Q K N)).product
      (Finset.univ.product Finset.univ)).filter fun z =>
    z.1.1 ∣ smallPart Q z.2.1 ∧ z.1.1 ∣ smallPart Q z.2.2 ∧
      z.1.2 ∣ roughPart Q z.2.1 ∧ z.1.2 ∣ roughPart Q z.2.2

def keyedDependentPairs (Q : ℕ) (A : ResidueSystem) :
    Finset ((ℕ × ℕ) × (ModIndex A × ModIndex A)) :=
  (dependentPairs Q A).image (keyPair Q)

lemma pairPrimeKey_spec (Q : ℕ) (A : ResidueSystem)
    {ij : ModIndex A × ModIndex A} (hij : ij ∈ dependentPairs Q A) :
    (pairPrimeKey Q ij).Prime ∧ Q < pairPrimeKey Q ij ∧
      pairPrimeKey Q ij ∣ roughPart Q ij.1 ∧
      pairPrimeKey Q ij ∣ roughPart Q ij.2 := by
  have hdep := (Finset.mem_filter.mp hij).2
  have hg : (roughPart Q ij.1).gcd (roughPart Q ij.2) ≠ 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one] using hdep
  have hp : (pairPrimeKey Q ij).Prime := Nat.minFac_prime hg
  have hpg : pairPrimeKey Q ij ∣
      (roughPart Q ij.1).gcd (roughPart Q ij.2) := Nat.minFac_dvd _
  have hpi : pairPrimeKey Q ij ∣ roughPart Q ij.1 :=
    hpg.trans (Nat.gcd_dvd_left _ _)
  have hpj : pairPrimeKey Q ij ∣ roughPart Q ij.2 :=
    hpg.trans (Nat.gcd_dvd_right _ _)
  exact ⟨hp,
    prime_dvd_roughPart_gt (A.modulus_pos ij.1 ij.1.property) hp hpi,
    hpi, hpj⟩

lemma pairSmallKey_mem (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) (ij : ModIndex A × ModIndex A) :
    pairSmallKey Q ij ∈ smallKeys Q K N := by
  apply Nat.mem_smoothNumbersUpTo.mpr
  have hdvd : pairSmallKey Q ij ∣ smallPart Q ij.1 := Nat.gcd_dvd_left _ _
  have hdvd_i : pairSmallKey Q ij ∣ (ij.1 : ℕ) :=
    hdvd.trans (smallPart_dvd (A.modulus_pos ij.1 ij.1.property))
  exact ⟨Nat.le_trans (Nat.le_of_dvd (A.modulus_pos ij.1 ij.1.property) hdvd_i)
      (hw ij.1 ij.1.property).2,
    Nat.mem_smoothNumbers_of_dvd
      (smallPart_smooth (Q := Q) (A.modulus_pos ij.1 ij.1.property)) hdvd⟩

lemma pairPrimeKey_mem (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) {ij : ModIndex A × ModIndex A}
    (hij : ij ∈ dependentPairs Q A) :
    pairPrimeKey Q ij ∈ largePrimeKeys Q K N := by
  obtain ⟨hp, hQp, hpi, hpj⟩ := pairPrimeKey_spec Q A hij
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), hp, hQp⟩
  exact (Nat.le_of_dvd (A.modulus_pos ij.1 ij.1.property)
    (hpi.trans (roughPart_dvd (A.modulus_pos ij.1 ij.1.property)))).trans
      (hw ij.1 ij.1.property).2

lemma keyedDependentPairs_subset_grouped (Q : ℕ) (A : ResidueSystem)
    {K N : ℕ} (hw : A.InNatWindow K N) :
    keyedDependentPairs Q A ⊆ groupedPairs Q K N A := by
  intro z hz
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨pairSmallKey_mem Q A hw ij, pairPrimeKey_mem Q A hw hij⟩,
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, ?_⟩
  obtain ⟨hp, hQp, hpi, hpj⟩ := pairPrimeKey_spec Q A hij
  exact ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _, hpi, hpj⟩

def eligibleIndices (Q : ℕ) (A : ResidueSystem) (d p : ℕ) :
    Finset (ModIndex A) :=
  Finset.univ.filter fun i => d ∣ smallPart Q i ∧ p ∣ roughPart Q i

lemma eligible_dvd_modulus (Q : ℕ) (A : ResidueSystem) {d p : ℕ}
    {i : ModIndex A} (hi : i ∈ eligibleIndices Q A d p) : d * p ∣ (i : ℕ) := by
  have hi' := (Finset.mem_filter.mp hi).2
  have hmul : d * p ∣ smallPart Q i * roughPart Q i :=
    Nat.mul_dvd_mul hi'.1 hi'.2
  simpa [smallPart_mul_roughPart (Q := Q)
    (A.modulus_pos i i.property).ne'] using hmul

lemma card_eligibleIndices_le (Q : ℕ) (A : ResidueSystem) {K N d p : ℕ}
    (hw : A.InNatWindow K N) (hd : 0 < d) (hp : 0 < p) :
    (eligibleIndices Q A d p).card ≤ K * N / (d * p) := by
  let m := d * p
  let f : ModIndex A → ℕ := fun i => (i : ℕ) / m
  have hm : 0 < m := Nat.mul_pos hd hp
  have hsub : Set.MapsTo f (eligibleIndices Q A d p)
      (Finset.Icc 1 (K * N / m) : Set ℕ) := by
    intro i hi
    have hdiv := eligible_dvd_modulus Q A hi
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (A.modulus_pos i i.property) hdiv) hm
    · exact Nat.div_le_div_right (hw i i.property).2
  have hinj : Set.InjOn f (eligibleIndices Q A d p) := by
    intro i hi j hj hij
    apply Subtype.ext
    have hdi := eligible_dvd_modulus Q A hi
    have hdj := eligible_dvd_modulus Q A hj
    change (i : ℕ) / m = (j : ℕ) / m at hij
    calc
      (i : ℕ) = m * ((i : ℕ) / m) := (Nat.mul_div_cancel' hdi).symm
      _ = m * ((j : ℕ) / m) := by rw [hij]
      _ = (j : ℕ) := Nat.mul_div_cancel' hdj
  have hc := Finset.card_le_card_of_injOn f hsub hinj
  simpa [Nat.card_Icc, hm.ne', m] using hc

lemma sum_eligible_inv_le (Q : ℕ) (A : ResidueSystem) {K N d p : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N) (hd : 0 < d) (hp : 0 < p) :
    (∑ i ∈ eligibleIndices Q A d p, (((i : ℕ) : ℝ)⁻¹)) ≤
      (K : ℝ) / (d * p : ℕ) := by
  have hterm : ∀ i ∈ eligibleIndices Q A d p,
      (((i : ℕ) : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ := by
    intro i hi
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hNi : (N : ℝ) ≤ (i : ℕ) := by exact_mod_cast (hw i i.property).1
    simpa only [one_div] using one_div_le_one_div_of_le hNR hNi
  have hcard := card_eligibleIndices_le Q A hw hd hp
  have hm : 0 < d * p := Nat.mul_pos hd hp
  have hmul : (eligibleIndices Q A d p).card * (d * p) ≤ K * N :=
    (Nat.le_div_iff_mul_le hm).mp hcard
  calc
    (∑ i ∈ eligibleIndices Q A d p, (((i : ℕ) : ℝ)⁻¹)) ≤
        ∑ _i ∈ eligibleIndices Q A d p, (N : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm
    _ = ((eligibleIndices Q A d p).card : ℝ) * (N : ℝ)⁻¹ := by
      simp [mul_comm]
    _ ≤ (K : ℝ) / (d * p : ℕ) := by
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hmR : (0 : ℝ) < d * p := by exact_mod_cast hm
      have hmul' : (eligibleIndices Q A d p).card * (d * p) ≤ N * K := by
        simpa [Nat.mul_comm] using hmul
      rw [div_eq_mul_inv]
      field_simp
      exact_mod_cast hmul'

def groupedWeight {A : ResidueSystem}
    (z : (ℕ × ℕ) × (ModIndex A × ModIndex A)) : ℝ :=
  (z.1.1 : ℝ) * ((((z.2.1 : ℕ) : ℝ)⁻¹) * (((z.2.2 : ℕ) : ℝ)⁻¹))

lemma pairKernel_le_grouped (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) :
    pairKernel Q A ≤ ∑ z ∈ groupedPairs Q K N A, groupedWeight z := by
  calc
    pairKernel Q A =
        ∑ z ∈ keyedDependentPairs Q A, groupedWeight z := by
      rw [pairKernel, keyedDependentPairs, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ij hij
        rfl
      · intro i hi j hj heq
        exact keyPair_injective Q heq
    _ ≤ ∑ z ∈ groupedPairs Q K N A, groupedWeight z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (keyedDependentPairs_subset_grouped Q A hw)
      intro z hz hznot
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (by positivity))

lemma grouped_sum_eq (Q K N : ℕ) (A : ResidueSystem) :
    (∑ z ∈ groupedPairs Q K N A, groupedWeight z) =
      ∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
        (d : ℝ) *
          (∑ i ∈ eligibleIndices Q A d p, (((i : ℕ) : ℝ)⁻¹)) ^ 2 := by
  classical
  unfold groupedPairs groupedWeight eligibleIndices
  simp_rw [Finset.sum_filter]
  let F : ((ℕ × ℕ) × (ModIndex A × ModIndex A)) → ℝ := fun a =>
    if a.1.1 ∣ smallPart Q a.2.1 ∧ a.1.1 ∣ smallPart Q a.2.2 ∧
        a.1.2 ∣ roughPart Q a.2.1 ∧ a.1.2 ∣ roughPart Q a.2.2 then
      (a.1.1 : ℝ) *
        ((((a.2.1 : ℕ) : ℝ)⁻¹) * (((a.2.2 : ℕ) : ℝ)⁻¹))
    else 0
  change (∑ a ∈ (((smallKeys Q K N).product (largePrimeKeys Q K N)).product
    ((Finset.univ : Finset (ModIndex A)).product Finset.univ)), F a) = _
  trans ∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
      ∑ i : ModIndex A, ∑ j : ModIndex A, F ((d, p), (i, j))
  · calc
      (∑ a ∈ (((smallKeys Q K N).product (largePrimeKeys Q K N)).product
          ((Finset.univ : Finset (ModIndex A)).product Finset.univ)), F a) =
        ∑ dp ∈ (smallKeys Q K N).product (largePrimeKeys Q K N),
          ∑ ij ∈ (Finset.univ : Finset (ModIndex A)).product Finset.univ,
            F (dp, ij) := Finset.sum_product _ _ F
      _ = ∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
          ∑ ij ∈ (Finset.univ : Finset (ModIndex A)).product Finset.univ,
            F ((d, p), ij) := Finset.sum_product _ _ _
      _ = ∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
          ∑ i : ModIndex A, ∑ j : ModIndex A,
            F ((d, p), (i, j)) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_product _ _ _
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [F]
  let W : ModIndex A → ℝ := fun i =>
    if d ∣ smallPart Q i ∧ p ∣ roughPart Q i then
      (((i : ℕ) : ℝ)⁻¹) else 0
  change (∑ i : ModIndex A, ∑ j : ModIndex A,
      if d ∣ smallPart Q i ∧ d ∣ smallPart Q j ∧
          p ∣ roughPart Q i ∧ p ∣ roughPart Q j then
        (d : ℝ) * (((i : ℕ) : ℝ)⁻¹ * ((j : ℕ) : ℝ)⁻¹)
      else 0) = (d : ℝ) * (∑ i : ModIndex A, W i) ^ 2
  have hpoint (i j : ModIndex A) :
      (if d ∣ smallPart Q i ∧ d ∣ smallPart Q j ∧
          p ∣ roughPart Q i ∧ p ∣ roughPart Q j then
        (d : ℝ) * (((i : ℕ) : ℝ)⁻¹ * ((j : ℕ) : ℝ)⁻¹)
      else 0) = (d : ℝ) * (W i * W j) := by
    dsimp only [W]
    by_cases hdi : d ∣ smallPart Q i <;>
      by_cases hdj : d ∣ smallPart Q j <;>
      by_cases hpi : p ∣ roughPart Q i <;>
      by_cases hpj : p ∣ roughPart Q j <;> simp [hdi, hdj, hpi, hpj]
  simp_rw [hpoint]
  rw [pow_two]
  calc
    (∑ i : ModIndex A, ∑ j : ModIndex A, (d : ℝ) * (W i * W j)) =
        ∑ i : ModIndex A, (d : ℝ) * W i * (∑ j : ModIndex A, W j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (d : ℝ) *
        ((∑ i : ModIndex A, W i) * (∑ j : ModIndex A, W j)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma grouped_sum_le_euler_tail (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hN : 0 < N) (hw : A.InNatWindow K N) :
    (∑ z ∈ groupedPairs Q K N A, groupedWeight z) ≤
      (K : ℝ) ^ 2 *
        (∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹) *
        (∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2) := by
  rw [grouped_sum_eq]
  calc
    (∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
        (d : ℝ) *
          (∑ i ∈ eligibleIndices Q A d p, (((i : ℕ) : ℝ)⁻¹)) ^ 2) ≤
      ∑ d ∈ smallKeys Q K N, ∑ p ∈ largePrimeKeys Q K N,
        (K : ℝ) ^ 2 * (d : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_smoothNumbers
          (Nat.mem_smoothNumbersUpTo.mp hd).2)
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := (Finset.mem_filter.mp hp).2.1
      have hp0 : 0 < p := hpprime.pos
      have hsum := sum_eligible_inv_le Q A hN hw hdpos hp0
      have hsum0 : 0 ≤ ∑ i ∈ eligibleIndices Q A d p,
          (((i : ℕ) : ℝ)⁻¹) := by positivity
      have hK0 : (0 : ℝ) ≤ K := by positivity
      have hdp0 : (0 : ℝ) < d * p := by positivity
      calc
        (d : ℝ) *
            (∑ i ∈ eligibleIndices Q A d p, (((i : ℕ) : ℝ)⁻¹)) ^ 2 ≤
          (d : ℝ) * ((K : ℝ) / (d * p : ℕ)) ^ 2 := by
            gcongr
        _ = (K : ℝ) ^ 2 * (d : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ 2 := by
          push_cast
          field_simp
    _ = (K : ℝ) ^ 2 *
        (∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹) *
        (∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2) := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      rw [← Finset.sum_mul]

def reciprocalHom27 : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    change (((a * b : ℕ) : ℝ))⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    rw [Nat.cast_mul, mul_inv]

/-- Finite smooth reciprocal sums are bounded by their geometric Euler
product. -/
lemma sum_smallKeys_inv_le_euler (Q K N : ℕ) :
    (∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹) ≤
      ∏ p ∈ (Q + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let s := smallKeys Q K N
  let e : {d // d ∈ s} ↪ (Q + 1).smoothNumbers :=
    ⟨fun d => ⟨d.1, (Nat.mem_smoothNumbersUpTo.mp d.2).2⟩, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : (Q + 1).smoothNumbers => z.1) h⟩
  let T : Finset ((Q + 1).smoothNumbers) := s.attach.map e
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom27 p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (by exact_mod_cast hp.pos.le))]
    change (p : ℝ)⁻¹ < 1
    rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalHom27) hprime (Q + 1)
  have hfinite :
      (∑ d ∈ T, reciprocalHom27 d.1) ≤
        ∑' d : (Q + 1).smoothNumbers, reciprocalHom27 d.1 :=
    (Summable.of_norm heuler.1).sum_le_tsum T (fun d _ => by
      change 0 ≤ (d.1 : ℝ)⁻¹
      positivity)
  have hsum : (∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹) =
      ∑ d ∈ T, reciprocalHom27 d.1 := by
    change (∑ d ∈ s, (d : ℝ)⁻¹) = _
    rw [← Finset.sum_attach, Finset.sum_map]
    rfl
  rw [hsum]
  exact hfinite.trans_eq (by simpa [reciprocalHom27] using heuler.2.tsum_eq)

noncomputable def eulerConstant27 : ℝ :=
  Classical.choose weak_mertens_third_upper_all

lemma eulerConstant27_pos : 0 < eulerConstant27 :=
  (Classical.choose_spec weak_mertens_third_upper_all).1

lemma euler_le_const_log (Q : ℕ) (hQ : 3 ≤ Q) :
    (∏ p ∈ (Q + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      eulerConstant27 * Real.log Q := by
  have hm := (Classical.choose_spec weak_mertens_third_upper_all).2
    (Q : ℝ) (by exact_mod_cast (show 2 ≤ Q by omega))
  rw [Real.norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    Real.norm_of_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))] at hm
  have heq :
      (∏ p ∈ (Q + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) =
        partial_euler_product Q := by
    have hsets : (Q + 1).primesBelow =
        (Finset.Icc 1 Q).filter Nat.Prime := by
      ext p
      simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
        Finset.mem_Icc, Nat.lt_succ_iff]
      constructor
      · rintro ⟨hpQ, hp⟩
        exact ⟨⟨hp.one_le, hpQ⟩, hp⟩
      · rintro ⟨⟨hp1, hpQ⟩, hp⟩
        exact ⟨hpQ, hp⟩
    rw [hsets]
    rfl
  rw [heq]
  simpa [eulerConstant27] using hm

lemma sum_largePrimeKeys_inv_sq_le (Q K N : ℕ) :
    (∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2) ≤
      2 / (Q + 1 : ℕ) := by
  have hsub : largePrimeKeys Q K N ⊆ Finset.Ioo Q (K * N + 1) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_Ioo.mpr ⟨hp'.2.2, Finset.mem_range.mp hp'.1⟩
  calc
    (∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2) ≤
        ∑ p ∈ Finset.Ioo Q (K * N + 1), ((p : ℝ)⁻¹) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => sq_nonneg _)
    _ ≤ 2 / (Q + 1 : ℕ) := by
      simpa [inv_pow, Nat.cast_add, Nat.cast_one] using
        (sum_Ioo_inv_sq_le (α := ℝ) Q (K * N + 1))

lemma pairKernel_le_log_div (Q : ℕ) (A : ResidueSystem) {K N : ℕ}
    (hQ : 3 ≤ Q) (hN : 0 < N) (hw : A.InNatWindow K N) :
    pairKernel Q A ≤
      2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q := by
  have hgroup := (pairKernel_le_grouped Q A hw).trans
    (grouped_sum_le_euler_tail Q A hN hw)
  have hsmooth := sum_smallKeys_inv_le_euler Q K N |>.trans
    (euler_le_const_log Q hQ)
  have htail := sum_largePrimeKeys_inv_sq_le Q K N
  have hnonnegK : 0 ≤ (K : ℝ) ^ 2 := sq_nonneg _
  have hsmooth0 : 0 ≤ ∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹ := by positivity
  have htail0 : 0 ≤ ∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2 := by positivity
  have hsmoothUpper0 : 0 ≤ eulerConstant27 * Real.log Q :=
    mul_nonneg eulerConstant27_pos.le
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
  calc
    pairKernel Q A ≤ (K : ℝ) ^ 2 *
        (∑ d ∈ smallKeys Q K N, (d : ℝ)⁻¹) *
        (∑ p ∈ largePrimeKeys Q K N, ((p : ℝ)⁻¹) ^ 2) := hgroup
    _ ≤ (K : ℝ) ^ 2 * (eulerConstant27 * Real.log Q) *
        (2 / (Q + 1 : ℕ)) := by gcongr
    _ ≤ 2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q := by
      have hlog0 : 0 ≤ Real.log Q :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
      have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ.trans_lt' (by norm_num)
      have hle : (Q : ℝ) ≤ Q + 1 := by norm_num
      have hinv : ((Q : ℝ) + 1)⁻¹ ≤ (Q : ℝ)⁻¹ :=
        by simpa [one_div] using one_div_le_one_div_of_le hQR hle
      push_cast
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (K : ℝ) ^ 2 * (eulerConstant27 * Real.log Q) *
            (2 * ((Q : ℝ) + 1)⁻¹) =
            2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q *
              ((Q : ℝ) + 1)⁻¹ := by ring
        _ ≤ 2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q *
              (Q : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) eulerConstant27_pos.le)
                (sq_nonneg _)) hlog0)
        _ = 2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q *
              (Q : ℝ)⁻¹ := rfl

lemma exists_large_cutoff (K : ℕ) :
    ∃ Q : ℕ, 3 ≤ Q ∧
      4 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q <
        Real.exp (-8 * (K + 1 : ℝ)) := by
  have hbase := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat : Tendsto (fun Q : ℕ => Real.log (Q : ℝ) / (Q : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      hbase.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun Q : ℕ =>
        4 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q)
      atTop (nhds 0) := by
    have ht := hnat.const_mul (4 * eulerConstant27 * (K : ℝ) ^ 2)
    simpa only [div_eq_mul_inv, mul_assoc, mul_zero] using ht
  have he : 0 < Real.exp (-8 * (K + 1 : ℝ)) := Real.exp_pos _
  have hev : ∀ᶠ Q : ℕ in atTop,
      4 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q <
        Real.exp (-8 * (K + 1 : ℝ)) :=
    hlim.eventually (Iio_mem_nhds he)
  obtain ⟨Q, hsmall, hQ⟩ := (hev.and (eventually_ge_atTop 3)).exists
  exact ⟨Q, hQ, hsmall⟩

/-- At the explicit square scale, some rough fibre has positive residual
measure.  This is the fixed-ratio specialization of the FFKPY estimate. -/
lemma exists_positive_rough_fibre (K : ℕ) (hK : 1 ≤ K) :
    ∃ Q N : ℕ, 3 ≤ Q ∧ 0 < N ∧
      ∀ A : ResidueSystem, A.InNatWindow K N →
        ∃ h : ZMod (smallPeriod Q A),
          0 < (Erdos277.residueMeasure (roughPeriod Q A)).real
            (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) := by
  obtain ⟨Q, hQ, hcut⟩ := exists_large_cutoff K
  let N := sparseScale Q K
  refine ⟨Q, N, hQ, sparseScale_pos Q K, ?_⟩
  intro A hw
  have hsparse :
      4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ N := by
    exact smooth_card_sparse_at_scale Q K hK
  have halpha := sum_fibreAlpha_lower Q A (sparseScale_pos Q K) hw hsparse
  have hbeta0 := sum_fibreBeta_le_pairKernel Q A
  have hkernel := pairKernel_le_log_div Q A hQ (sparseScale_pos Q K) hw
  have hbeta : ∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h ≤
      (smallPeriod Q A : ℝ) *
        (2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q) :=
    hbeta0.trans (mul_le_mul_of_nonneg_left hkernel (by positivity))
  have hres : ∑ h : ZMod (smallPeriod Q A),
      (fibreAlpha Q A h - fibreBeta Q A h) ≤
        ∑ h : ZMod (smallPeriod Q A),
          (Erdos277.residueMeasure (roughPeriod Q A)).real
            (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) := by
    exact Finset.sum_le_sum fun h _ => fibre_residual_measure_lower Q A h
  have hsumsub :
      (∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h) -
        (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) =
      ∑ h : ZMod (smallPeriod Q A),
        (fibreAlpha Q A h - fibreBeta Q A h) := by
    rw [Finset.sum_sub_distrib]
  have hpos : 0 < ∑ h : ZMod (smallPeriod Q A),
      (Erdos277.residueMeasure (roughPeriod Q A)).real
        (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) := by
    rw [← hsumsub] at hres
    have hM : (0 : ℝ) < smallPeriod Q A := by
      exact_mod_cast smallPeriod_pos Q A
    have hcutM := mul_lt_mul_of_pos_left hcut hM
    have htwob :
        2 * (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) <
          (smallPeriod Q A : ℝ) * Real.exp (-8 * (K + 1 : ℝ)) := by
      calc
        2 * (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) ≤
            2 * ((smallPeriod Q A : ℝ) *
              (2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q)) :=
          mul_le_mul_of_nonneg_left hbeta (by norm_num)
        _ = (smallPeriod Q A : ℝ) *
              (4 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q) := by ring
        _ < (smallPeriod Q A : ℝ) * Real.exp (-8 * (K + 1 : ℝ)) := hcutM
    have hba :
        (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) <
          ∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h := by
      nlinarith
    linarith
  by_contra hnone
  push Not at hnone
  have hzero : ∀ h : ZMod (smallPeriod Q A),
      (Erdos277.residueMeasure (roughPeriod Q A)).real
        (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)) = 0 := by
    intro h
    apply le_antisymm (hnone h)
    positivity
  simp_rw [hzero] at hpos
  simp at hpos

/-- A residue surviving the rough subsystem on one small fibre recombines by
CRT to an integer missed by the original congruence system. -/
lemma uncovered_nonempty_of_rough_residual (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A))
    (hne : (Erdos277.residual (activeIndices Q A h) (roughEvent Q A)).Nonempty) :
    A.uncovered.Nonempty := by
  obtain ⟨y, hy⟩ := hne
  let M := smallPeriod Q A
  let R := roughPeriod Q A
  have hM : 0 < M := smallPeriod_pos Q A
  have hR : 0 < R := roughPeriod_pos Q A
  have hcop : M.Coprime R := smallPeriod_coprime_roughPeriod Q A
  letI : NeZero M := ⟨hM.ne'⟩
  letI : NeZero R := ⟨hR.ne'⟩
  letI : NeZero (M * R) := ⟨(Nat.mul_pos hM hR).ne'⟩
  let e := ZMod.chineseRemainder hcop
  let x : ZMod (M * R) := e.symm (h, y)
  let z : ℤ := x.val
  have hxy : e x = (h, y) := e.apply_symm_apply (h, y)
  have hxM : ZMod.castHom (show M ∣ M * R by exact ⟨R, rfl⟩) (ZMod M) x = h := by
    have := congrArg Prod.fst hxy
    simpa [e, chineseRemainder_fst] using this
  have hxR : ZMod.castHom (show R ∣ M * R by exact ⟨M, Nat.mul_comm M R⟩)
      (ZMod R) x = y := by
    have := congrArg Prod.snd hxy
    simpa [e, chineseRemainder_snd] using this
  refine ⟨z, ?_⟩
  intro n hn heq
  let i : ModIndex A := ⟨n, hn⟩
  let s := smallPart Q n
  let r := roughPart Q n
  have hsN : s ∣ n := smallPart_dvd (A.modulus_pos n hn)
  have hrN : r ∣ n := roughPart_dvd (A.modulus_pos n hn)
  have hsM : s ∣ M := small_dvd_smallPeriod Q A hn
  have hrR : r ∣ R := rough_dvd_roughPeriod Q A hn
  have hnMR : n ∣ M * R := by
    rw [← smallPart_mul_roughPart (Q := Q) (A.modulus_pos n hn).ne']
    exact Nat.mul_dvd_mul hsM hrR
  have hzx : (z : ZMod (M * R)) = x := by
    simpa [z] using ZMod.natCast_zmod_val x
  have hxn : ZMod.castHom hnMR (ZMod n) x = A.residue n := by
    rw [← hzx]
    simpa using heq
  have hsmallEq :
      ZMod.castHom hsM (ZMod s) h =
        ZMod.castHom hsN (ZMod s) (A.residue n) := by
    calc
      ZMod.castHom hsM (ZMod s) h =
          ZMod.castHom hsM (ZMod s)
            (ZMod.castHom (show M ∣ M * R by exact ⟨R, rfl⟩) (ZMod M) x) := by
              rw [hxM]
      _ = ZMod.castHom (hsM.trans (show M ∣ M * R by exact ⟨R, rfl⟩))
            (ZMod s) x := castHom_trans_apply hsM _ x
      _ = ZMod.castHom (hsN.trans hnMR) (ZMod s) x := by rfl
      _ = ZMod.castHom hsN (ZMod s) (ZMod.castHom hnMR (ZMod n) x) :=
        (castHom_trans_apply hsN hnMR x).symm
      _ = ZMod.castHom hsN (ZMod s) (A.residue n) := by rw [hxn]
  have hactive : i ∈ activeIndices Q A h := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hsmallEq
  have hroughEq :
      ZMod.castHom hrR (ZMod r) y =
        ZMod.castHom hrN (ZMod r) (A.residue n) := by
    calc
      ZMod.castHom hrR (ZMod r) y =
          ZMod.castHom hrR (ZMod r)
            (ZMod.castHom (show R ∣ M * R by exact ⟨M, Nat.mul_comm M R⟩)
              (ZMod R) x) := by rw [hxR]
      _ = ZMod.castHom (hrR.trans
            (show R ∣ M * R by exact ⟨M, Nat.mul_comm M R⟩)) (ZMod r) x :=
        castHom_trans_apply hrR _ x
      _ = ZMod.castHom (hrN.trans hnMR) (ZMod r) x := by rfl
      _ = ZMod.castHom hrN (ZMod r) (ZMod.castHom hnMR (ZMod n) x) :=
        (castHom_trans_apply hrN hnMR x).symm
      _ = ZMod.castHom hrN (ZMod r) (A.residue n) := by rw [hxn]
  have hyavoid : ∀ j, j ∈ activeIndices Q A h → y ∉ roughEvent Q A j := by
    simpa only [Erdos277.residual, Set.mem_compl_iff, Set.mem_iUnion,
      not_exists] using hy
  exact hyavoid i hactive hroughEq

lemma exists_uncovered_at_fixed_ratio (K : ℕ) (hK : 1 ≤ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ A : ResidueSystem,
      A.InNatWindow K N → A.uncovered.Nonempty := by
  obtain ⟨Q, N, hQ, hN, hmain⟩ := exists_positive_rough_fibre K hK
  refine ⟨N, hN, ?_⟩
  intro A hw
  obtain ⟨h, hh⟩ := hmain A hw
  apply uncovered_nonempty_of_rough_residual Q A h
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hh
  simpa using hh

lemma uncoveredMod_nonempty_of_uncovered (A : ResidueSystem)
    (hne : A.uncovered.Nonempty) : A.uncoveredMod.Nonempty := by
  obtain ⟨z, hz⟩ := hne
  let P := A.period
  let u := (z % P).toNat
  have hP : 0 < P := A.period_pos
  have hmodnonneg : 0 ≤ z % P := Int.emod_nonneg z (by exact_mod_cast hP.ne')
  have hutoInt : (u : ℤ) = z % P := Int.toNat_of_nonneg hmodnonneg
  have huP : u < P := by
    rw [← Int.ofNat_lt]
    rw [hutoInt]
    exact Int.emod_lt_of_pos z (by exact_mod_cast hP)
  refine ⟨u, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr huP, ?_⟩
  intro n hn heq
  apply hz n hn
  have hzu : (z : ZMod n) = ((u : ℤ) : ZMod n) := by
    rw [ZMod.intCast_eq_intCast_iff]
    have hnp : (n : ℤ) ∣ (P : ℤ) := by
      exact_mod_cast A.dvd_period hn
    have hm := (Int.mod_modEq z P).of_dvd hnp
    rw [hutoInt]
    exact hm.symm
  exact hzu.trans heq

lemma inv_period_le_uncoveredDensity (A : ResidueSystem)
    (hne : A.uncovered.Nonempty) :
    (A.period : ℝ)⁻¹ ≤ A.uncoveredDensity := by
  have hcard : 1 ≤ A.uncoveredMod.card :=
    Finset.one_le_card.mpr (uncoveredMod_nonempty_of_uncovered A hne)
  have hP : (0 : ℝ) < A.period := by exact_mod_cast A.period_pos
  rw [ResidueSystem.uncoveredDensity, div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (1 : ℝ) ≤ A.uncoveredMod.card)
    (inv_nonneg.mpr hP.le)

lemma period_dvd_factorial_of_natWindow (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) : A.period ∣ Nat.factorial (K * N) := by
  apply Finset.lcm_dvd
  intro n hn
  exact Nat.dvd_factorial (A.modulus_pos n hn) (hw n hn).2

lemma factorial_inv_le_uncoveredDensity (A : ResidueSystem) {K N : ℕ}
    (hw : A.InNatWindow K N) (hne : A.uncovered.Nonempty) :
    ((Nat.factorial (K * N) : ℕ) : ℝ)⁻¹ ≤ A.uncoveredDensity := by
  have hdvd := period_dvd_factorial_of_natWindow A hw
  have hper : A.period ≤ Nat.factorial (K * N) :=
    Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  have hP : (0 : ℝ) < A.period := by exact_mod_cast A.period_pos
  have hperR : (A.period : ℝ) ≤ Nat.factorial (K * N) := by exact_mod_cast hper
  have hinv : ((Nat.factorial (K * N) : ℕ) : ℝ)⁻¹ ≤
      (A.period : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hP hperR
  exact hinv.trans (inv_period_le_uncoveredDensity A hne)

lemma realWindow_to_natWindow (A : ResidueSystem) {C : ℝ} {K N : ℕ}
    (hCK : C ≤ K) (hw : A.InWindow C N) : A.InNatWindow K N := by
  intro n hn
  refine ⟨(hw n hn).1, ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have := (hw n hn).2.trans (mul_le_mul_of_nonneg_right hCK hN0)
  exact_mod_cast this

/-- The exact positive assertion in Problem 27 is false. -/
theorem not_erdos27Question : ¬Erdos27Question := by
  rintro ⟨C, hC, hall⟩
  let K : ℕ := ⌈C⌉₊
  have hCK : C ≤ (K : ℝ) := by
    exact Nat.le_ceil C
  have hK : 1 ≤ K := by
    exact_mod_cast (hC.le.trans hCK)
  obtain ⟨N, hN, hfixed⟩ := exists_uncovered_at_fixed_ratio K hK
  let F : ℕ := Nat.factorial (K * N)
  let ε : ℝ := (2 * F : ℕ)⁻¹
  have hF : 0 < F := Nat.factorial_pos _
  have hε : 0 < ε := by positivity
  obtain ⟨A, hwreal, hdensity⟩ := hall ε hε N hN
  have hwnat : A.InNatWindow K N := realWindow_to_natWindow A hCK hwreal
  have hunc : A.uncovered.Nonempty := hfixed A hwnat
  have hlower := factorial_inv_le_uncoveredDensity A hwnat hunc
  have hstrict : ε < (F : ℝ)⁻¹ := by
    dsimp only [ε]
    push_cast
    have hFR : (0 : ℝ) < F := by exact_mod_cast hF
    rw [mul_inv]
    nlinarith [inv_pos.mpr hFR]
  linarith

/-- **Erdős Problem 27.** The answer is no. -/
theorem erdos_27 : ¬ Erdos27Question := by
  simpa using not_erdos27Question

theorem not_erdos_27 :
    ¬ (∃ C : ℝ, 1 < C ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
        IsEpsilonAlmostCovering C N ε) := by
  exact erdos_27

#print axioms not_erdos_27

end

end Erdos27
