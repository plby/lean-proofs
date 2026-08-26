import ErdosProblems.Erdos796.KST
import ErdosProblems.Erdos796.Extremal
import Mathlib.Data.Finset.Sym

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pairwise overlap of semiprime fibres

This file formalizes the finite combinatorial core of the manuscript's
pairwise-overlap lemma.  Two copies of the prime variables are kept as
labelled bipartite vertex classes.  A nondegenerate four-cycle would produce
four genuine strict representations of one integer, contradicting
admissibility.
-/

namespace Erdos796

open scoped Nat.Prime

namespace PairwiseOverlap

/-- The integer attached to a multiplier and an oriented prime pair. -/
def multipliedPrimePair (u q r : ℕ) : ℕ := u * q * r

/-- Canonical factorization is injective when both labelled primes exceed
both positive multipliers and the pair in each factorization is decreasing.
This arithmetic lemma is what makes the eight values around a four-cycle
genuinely distinct. -/
theorem multipliedPrimePair_injective
    {u v q r Q R : ℕ}
    (hv : 0 < v)
    (hq : q.Prime) (hr : r.Prime) (hQ : Q.Prime) (hR : R.Prime)
    (hvq : v < q) (hvr : v < r)
    (hqr : r < q) (hQR : R < Q)
    (heq : multipliedPrimePair u q r = multipliedPrimePair v Q R) :
    u = v ∧ q = Q ∧ r = R := by
  have hqdvd : q ∣ v * Q * R := by
    refine ⟨u * r, ?_⟩
    calc
      v * Q * R = u * q * r := heq.symm
      _ = q * (u * r) := by ring
  have hrdvd : r ∣ v * Q * R := by
    refine ⟨u * q, ?_⟩
    calc
      v * Q * R = u * q * r := heq.symm
      _ = r * (u * q) := by ring
  have hq_cases : q = Q ∨ q = R := by
    rcases hq.dvd_mul.mp hqdvd with hqvQ | hqR'
    · rcases hq.dvd_mul.mp hqvQ with hqv | hqQ'
      · have hqle : q ≤ v := Nat.le_of_dvd hv hqv
        exact False.elim ((Nat.not_lt_of_ge hqle) hvq)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hQ).mp hqQ')
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hR).mp hqR')
  have hr_cases : r = Q ∨ r = R := by
    rcases hr.dvd_mul.mp hrdvd with hrvQ | hrR'
    · rcases hr.dvd_mul.mp hrvQ with hrv | hrQ'
      · have hrle : r ≤ v := Nat.le_of_dvd hv hrv
        exact False.elim ((Nat.not_lt_of_ge hrle) hvr)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hQ).mp hrQ')
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hR).mp hrR')
  have hprimePairs : q = Q ∧ r = R := by
    rcases hq_cases with hqQ | hqR'
    · rcases hr_cases with hrQ' | hrR'
      · exfalso
        subst Q
        exact (Nat.ne_of_lt hqr) hrQ'
      · exact ⟨hqQ, hrR'⟩
    · rcases hr_cases with hrQ' | hrR'
      · exfalso
        subst Q
        subst R
        exact (Nat.not_lt_of_ge hqr.le) hQR
      · exfalso
        exact (Nat.ne_of_lt hqr) (hqR'.trans hrR'.symm).symm
  rcases hprimePairs with ⟨rfl, rfl⟩
  have huv : u = v := by
    apply Nat.mul_right_cancel (Nat.mul_pos hq.pos hr.pos)
    simpa [multipliedPrimePair, mul_assoc] using! heq
  exact ⟨huv, rfl, rfl⟩

/-- A labelled multiplier/large-prime/small-prime factorization. -/
structure LabeledFactorization where
  multiplier : ℕ
  largePrime : ℕ
  smallPrime : ℕ
  deriving DecidableEq

/-- Constructor with names matching the three arithmetic roles. -/
def datum (u q r : ℕ) : LabeledFactorization := ⟨u, q, r⟩

/-- The integer represented by a labelled factorization. -/
def LabeledFactorization.value (d : LabeledFactorization) : ℕ :=
  multipliedPrimePair d.multiplier d.largePrime d.smallPrime

/-- Validity relative to two multiplier labels and two finite vertex
classes. -/
def LabeledFactorization.Valid (s t : ℕ) (Q R : Finset ℕ)
    (d : LabeledFactorization) : Prop :=
  (d.multiplier = s ∨ d.multiplier = t) ∧
    d.largePrime ∈ Q ∧ d.smallPrime ∈ R ∧
    d.largePrime.Prime ∧ d.smallPrime.Prime ∧
    d.smallPrime < d.largePrime

/-- Valid labelled factorizations have distinct integer values. -/
theorem valid_value_injective
    {s t : ℕ} {Q R : Finset ℕ}
    (hs : 0 < s) (ht : 0 < t)
    (hQ : ∀ q ∈ Q, s < q ∧ t < q)
    (hR : ∀ r ∈ R, s < r ∧ t < r) :
    Set.InjOn LabeledFactorization.value
      {d | LabeledFactorization.Valid s t Q R d} := by
  intro d hd e he hvalue
  have hd' := hd
  have he' := he
  rcases hd' with ⟨hdu, hdq, hdr, hdqp, hdrp, hdrq⟩
  rcases he' with ⟨heu, heq, her, heqp, herp, herq⟩
  have heupos : 0 < e.multiplier := heu.elim (fun h => h ▸ hs) (fun h => h ▸ ht)
  have hdQ := hQ d.largePrime hdq
  have hdR := hR d.smallPrime hdr
  have heQ := hQ e.largePrime heq
  have heR := hR e.smallPrime her
  have hbound (u : ℕ) (hu : u = s ∨ u = t) (x : ℕ)
      (hx : s < x ∧ t < x) : u < x := by
    rcases hu with rfl | rfl
    · exact hx.1
    · exact hx.2
  have hfactor := multipliedPrimePair_injective
    heupos hdqp hdrp heqp herp
    (hbound e.multiplier heu d.largePrime hdQ)
    (hbound e.multiplier heu d.smallPrime hdR)
    hdrq herq hvalue
  cases d
  cases e
  simp_all

theorem valid_value_ne
    {s t : ℕ} {Q R : Finset ℕ}
    {d e : LabeledFactorization}
    (hinj : Set.InjOn LabeledFactorization.value
      {x | LabeledFactorization.Valid s t Q R x})
    (hd : LabeledFactorization.Valid s t Q R d)
    (he : LabeledFactorization.Valid s t Q R e)
    (hne : d ≠ e) : d.value ≠ e.value := by
  intro hvalue
  exact hne (hinj hd he hvalue)

/-- Sort two distinct natural numbers into the order required by
`strictProductRepCount`. -/
def strictOrder (a b : ℕ) : ℕ × ℕ :=
  if a < b then (a, b) else (b, a)

theorem strictOrder_fst_lt_snd {a b : ℕ} (hab : a ≠ b) :
    (strictOrder a b).1 < (strictOrder a b).2 := by
  unfold strictOrder
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (Nat.le_of_not_gt h) hab.symm

theorem strictOrder_members {A : Finset ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) :
    (strictOrder a b).1 ∈ A ∧ (strictOrder a b).2 ∈ A := by
  unfold strictOrder
  split_ifs <;> simp_all

theorem strictOrder_product (a b : ℕ) :
    (strictOrder a b).1 * (strictOrder a b).2 = a * b := by
  unfold strictOrder
  split_ifs <;> simp [Nat.mul_comm]

theorem strictOrder_eq_imp_unordered {a b c d : ℕ}
    (h : strictOrder a b = strictOrder c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hsab : s((strictOrder a b).1, (strictOrder a b).2) = s(a, b) := by
    unfold strictOrder
    split_ifs <;> simp [Sym2.eq_swap]
  have hscd : s((strictOrder c d).1, (strictOrder c d).2) = s(c, d) := by
    unfold strictOrder
    split_ifs <;> simp [Sym2.eq_swap]
  have hs : s(a, b) = s(c, d) := by
    rw [← hsab, h, hscd]
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact Or.inl hs
  · exact Or.inr hs

theorem strictOrder_ne_of_cross_ne {a b c d : ℕ}
    (hac : a ≠ c) (had : a ≠ d) :
    strictOrder a b ≠ strictOrder c d := by
  intro h
  rcases strictOrder_eq_imp_unordered h with hparallel | hcross
  · exact hac hparallel.1
  · exact had hcross.1

/-- Four distinct strict solutions give a lower bound of four for the
representation count. -/
theorem four_strict_solutions_le_count
    {A : Finset ℕ} {m : ℕ} {x₁ x₂ x₃ x₄ : ℕ × ℕ}
    (h₁ : x₁.1 ∈ A ∧ x₁.2 ∈ A ∧ x₁.1 < x₁.2 ∧ x₁.1 * x₁.2 = m)
    (h₂ : x₂.1 ∈ A ∧ x₂.2 ∈ A ∧ x₂.1 < x₂.2 ∧ x₂.1 * x₂.2 = m)
    (h₃ : x₃.1 ∈ A ∧ x₃.2 ∈ A ∧ x₃.1 < x₃.2 ∧ x₃.1 * x₃.2 = m)
    (h₄ : x₄.1 ∈ A ∧ x₄.2 ∈ A ∧ x₄.1 < x₄.2 ∧ x₄.1 * x₄.2 = m)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₁₄ : x₁ ≠ x₄)
    (h₂₃ : x₂ ≠ x₃) (h₂₄ : x₂ ≠ x₄) (h₃₄ : x₃ ≠ x₄) :
    4 ≤ strictProductRepCount A m := by
  let S : Finset (ℕ × ℕ) := {x₁, x₂, x₃, x₄}
  have hcard : S.card = 4 := by
    simp [S, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]
  have hsub : S ⊆
      (A ×ˢ A).filter fun ab => ab.1 < ab.2 ∧ ab.1 * ab.2 = m := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₁.1, h₁.2.1⟩, h₁.2.2⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₂.1, h₂.2.1⟩, h₂.2.2⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₃.1, h₃.2.1⟩, h₃.2.2⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₄.1, h₄.2.1⟩, h₄.2.2⟩
  rw [strictProductRepCount, ← hcard]
  exact Finset.card_le_card hsub

/-- The labelled overlap graph on supplied large-prime and small-prime
vertex sets.  An edge records that both multipliers produce elements of
`A`; the inequality `r < q` is the manuscript's canonical orientation. -/
def overlapGraph (A : Finset ℕ) (s t : ℕ) (Q R : Finset ℕ) :
    Finset (ℕ × ℕ) :=
  (Q ×ˢ R).filter fun qr =>
    qr.1.Prime ∧ qr.2.Prime ∧ qr.2 < qr.1 ∧
      multipliedPrimePair s qr.1 qr.2 ∈ A ∧
      multipliedPrimePair t qr.1 qr.2 ∈ A

@[simp] theorem mem_overlapGraph {A : Finset ℕ} {s t : ℕ}
    {Q R : Finset ℕ} {q r : ℕ} :
    (q, r) ∈ overlapGraph A s t Q R ↔
      q ∈ Q ∧ r ∈ R ∧ q.Prime ∧ r.Prime ∧ r < q ∧
        multipliedPrimePair s q r ∈ A ∧
        multipliedPrimePair t q r ∈ A := by
  simp [overlapGraph, and_assoc]

/-- A nondegenerate four-cycle in an overlap graph gives four distinct
strict representations of the same integer. -/
theorem four_le_count_of_overlap_c4
    {A : Finset ℕ} {s t : ℕ} {Q R : Finset ℕ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hQ : ∀ q ∈ Q, s < q ∧ t < q)
    (hR : ∀ r ∈ R, s < r ∧ t < r)
    {q₁ q₂ r₁ r₂ : ℕ}
    (h₁₁ : (q₁, r₁) ∈ overlapGraph A s t Q R)
    (h₁₂ : (q₁, r₂) ∈ overlapGraph A s t Q R)
    (h₂₁ : (q₂, r₁) ∈ overlapGraph A s t Q R)
    (h₂₂ : (q₂, r₂) ∈ overlapGraph A s t Q R)
    (hq : q₁ ≠ q₂) (hr : r₁ ≠ r₂) :
    4 ≤ strictProductRepCount A (s * t * q₁ * q₂ * r₁ * r₂) := by
  have e₁₁ := mem_overlapGraph.mp h₁₁
  have e₁₂ := mem_overlapGraph.mp h₁₂
  have e₂₁ := mem_overlapGraph.mp h₂₁
  have e₂₂ := mem_overlapGraph.mp h₂₂
  let s₁₁ := datum s q₁ r₁
  let s₁₂ := datum s q₁ r₂
  let s₂₁ := datum s q₂ r₁
  let s₂₂ := datum s q₂ r₂
  let t₁₁ := datum t q₁ r₁
  let t₁₂ := datum t q₁ r₂
  let t₂₁ := datum t q₂ r₁
  let t₂₂ := datum t q₂ r₂
  have vs₁₁ : s₁₁.Valid s t Q R :=
    ⟨Or.inl rfl, e₁₁.1, e₁₁.2.1, e₁₁.2.2.1, e₁₁.2.2.2.1,
      e₁₁.2.2.2.2.1⟩
  have vs₁₂ : s₁₂.Valid s t Q R :=
    ⟨Or.inl rfl, e₁₂.1, e₁₂.2.1, e₁₂.2.2.1, e₁₂.2.2.2.1,
      e₁₂.2.2.2.2.1⟩
  have vs₂₁ : s₂₁.Valid s t Q R :=
    ⟨Or.inl rfl, e₂₁.1, e₂₁.2.1, e₂₁.2.2.1, e₂₁.2.2.2.1,
      e₂₁.2.2.2.2.1⟩
  have vs₂₂ : s₂₂.Valid s t Q R :=
    ⟨Or.inl rfl, e₂₂.1, e₂₂.2.1, e₂₂.2.2.1, e₂₂.2.2.2.1,
      e₂₂.2.2.2.2.1⟩
  have vt₁₁ : t₁₁.Valid s t Q R :=
    ⟨Or.inr rfl, e₁₁.1, e₁₁.2.1, e₁₁.2.2.1, e₁₁.2.2.2.1,
      e₁₁.2.2.2.2.1⟩
  have vt₁₂ : t₁₂.Valid s t Q R :=
    ⟨Or.inr rfl, e₁₂.1, e₁₂.2.1, e₁₂.2.2.1, e₁₂.2.2.2.1,
      e₁₂.2.2.2.2.1⟩
  have vt₂₁ : t₂₁.Valid s t Q R :=
    ⟨Or.inr rfl, e₂₁.1, e₂₁.2.1, e₂₁.2.2.1, e₂₁.2.2.2.1,
      e₂₁.2.2.2.2.1⟩
  have vt₂₂ : t₂₂.Valid s t Q R :=
    ⟨Or.inr rfl, e₂₂.1, e₂₂.2.1, e₂₂.2.2.1, e₂₂.2.2.2.1,
      e₂₂.2.2.2.2.1⟩
  have hinj := valid_value_injective hs ht hQ hR
  have value_ne {d e : LabeledFactorization}
      (vd : d.Valid s t Q R) (ve : e.Valid s t Q R) (hde : d ≠ e) :
      d.value ≠ e.value := valid_value_ne hinj vd ve hde
  have multiplier_ne {q r Q' R' : ℕ} :
      datum s q r ≠ datum t Q' R' := by
    intro h
    exact hst (congrArg LabeledFactorization.multiplier h)
  have large_ne {u r R' : ℕ} : datum u q₁ r ≠ datum u q₂ R' := by
    intro h
    exact hq (congrArg LabeledFactorization.largePrime h)
  have small_ne {u q Q' : ℕ} : datum u q r₁ ≠ datum u Q' r₂ := by
    intro h
    exact hr (congrArg LabeledFactorization.smallPrime h)
  let x₁ := strictOrder s₁₁.value t₂₂.value
  let x₂ := strictOrder s₁₂.value t₂₁.value
  let x₃ := strictOrder s₂₁.value t₁₂.value
  let x₄ := strictOrder s₂₂.value t₁₁.value
  have hne₁ : s₁₁.value ≠ t₂₂.value :=
    value_ne vs₁₁ vt₂₂ multiplier_ne
  have hne₂ : s₁₂.value ≠ t₂₁.value :=
    value_ne vs₁₂ vt₂₁ multiplier_ne
  have hne₃ : s₂₁.value ≠ t₁₂.value :=
    value_ne vs₂₁ vt₁₂ multiplier_ne
  have hne₄ : s₂₂.value ≠ t₁₁.value :=
    value_ne vs₂₂ vt₁₁ multiplier_ne
  have hx₁ : x₁.1 ∈ A ∧ x₁.2 ∈ A ∧ x₁.1 < x₁.2 ∧
      x₁.1 * x₁.2 = s * t * q₁ * q₂ * r₁ * r₂ := by
    refine ⟨(strictOrder_members e₁₁.2.2.2.2.2.1
      e₂₂.2.2.2.2.2.2).1,
      (strictOrder_members e₁₁.2.2.2.2.2.1
      e₂₂.2.2.2.2.2.2).2, strictOrder_fst_lt_snd hne₁, ?_⟩
    rw [strictOrder_product]
    simp only [s₁₁, t₂₂, LabeledFactorization.value, datum,
      multipliedPrimePair]
    ring
  have hx₂ : x₂.1 ∈ A ∧ x₂.2 ∈ A ∧ x₂.1 < x₂.2 ∧
      x₂.1 * x₂.2 = s * t * q₁ * q₂ * r₁ * r₂ := by
    refine ⟨(strictOrder_members e₁₂.2.2.2.2.2.1
      e₂₁.2.2.2.2.2.2).1,
      (strictOrder_members e₁₂.2.2.2.2.2.1
      e₂₁.2.2.2.2.2.2).2, strictOrder_fst_lt_snd hne₂, ?_⟩
    rw [strictOrder_product]
    simp only [s₁₂, t₂₁, LabeledFactorization.value, datum,
      multipliedPrimePair]
    ring
  have hx₃ : x₃.1 ∈ A ∧ x₃.2 ∈ A ∧ x₃.1 < x₃.2 ∧
      x₃.1 * x₃.2 = s * t * q₁ * q₂ * r₁ * r₂ := by
    refine ⟨(strictOrder_members e₂₁.2.2.2.2.2.1
      e₁₂.2.2.2.2.2.2).1,
      (strictOrder_members e₂₁.2.2.2.2.2.1
      e₁₂.2.2.2.2.2.2).2, strictOrder_fst_lt_snd hne₃, ?_⟩
    rw [strictOrder_product]
    simp only [s₂₁, t₁₂, LabeledFactorization.value, datum,
      multipliedPrimePair]
    ring
  have hx₄ : x₄.1 ∈ A ∧ x₄.2 ∈ A ∧ x₄.1 < x₄.2 ∧
      x₄.1 * x₄.2 = s * t * q₁ * q₂ * r₁ * r₂ := by
    refine ⟨(strictOrder_members e₂₂.2.2.2.2.2.1
      e₁₁.2.2.2.2.2.2).1,
      (strictOrder_members e₂₂.2.2.2.2.2.1
      e₁₁.2.2.2.2.2.2).2, strictOrder_fst_lt_snd hne₄, ?_⟩
    rw [strictOrder_product]
    simp only [s₂₂, t₁₁, LabeledFactorization.value, datum,
      multipliedPrimePair]
    ring
  have hx₁₂ : x₁ ≠ x₂ := strictOrder_ne_of_cross_ne
    (value_ne vs₁₁ vs₁₂ small_ne)
    (value_ne vs₁₁ vt₂₁ multiplier_ne)
  have hx₁₃ : x₁ ≠ x₃ := strictOrder_ne_of_cross_ne
    (value_ne vs₁₁ vs₂₁ large_ne)
    (value_ne vs₁₁ vt₁₂ multiplier_ne)
  have hx₁₄ : x₁ ≠ x₄ := strictOrder_ne_of_cross_ne
    (value_ne vs₁₁ vs₂₂ large_ne)
    (value_ne vs₁₁ vt₁₁ multiplier_ne)
  have hx₂₃ : x₂ ≠ x₃ := strictOrder_ne_of_cross_ne
    (value_ne vs₁₂ vs₂₁ large_ne)
    (value_ne vs₁₂ vt₁₂ multiplier_ne)
  have hx₂₄ : x₂ ≠ x₄ := strictOrder_ne_of_cross_ne
    (value_ne vs₁₂ vs₂₂ large_ne)
    (value_ne vs₁₂ vt₁₁ multiplier_ne)
  have hx₃₄ : x₃ ≠ x₄ := strictOrder_ne_of_cross_ne
    (value_ne vs₂₁ vs₂₂ small_ne)
    (value_ne vs₂₁ vt₁₁ multiplier_ne)
  exact four_strict_solutions_le_count hx₁ hx₂ hx₃ hx₄
    hx₁₂ hx₁₃ hx₁₄ hx₂₃ hx₂₄ hx₃₄

/-- The labelled overlap graph is `C₄`-free under the admissibility
condition. -/
theorem overlapGraph_c4Free
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {s t : ℕ} {Q R : Finset ℕ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hQ : ∀ q ∈ Q, s < q ∧ t < q)
    (hR : ∀ r ∈ R, s < r ∧ t < r) :
    Bipartite.C4Free (overlapGraph A s t Q R) := by
  intro q₁ q₂ r₁ r₂ h₁₁ h₁₂ h₂₁ h₂₂
  by_cases hq : q₁ = q₂
  · exact Or.inl hq
  by_cases hr : r₁ = r₂
  · exact Or.inr hr
  exfalso
  have hlower := four_le_count_of_overlap_c4 hs ht hst hQ hR
    h₁₁ h₁₂ h₂₁ h₂₂ hq hr
  have hupper := hA.2 (s * t * q₁ * q₂ * r₁ * r₂)
  omega

/-- Since the overlap graph is supported on `Q × R`, its displayed edge
count is its cardinality. -/
theorem overlapGraph_edgeCount_eq_card
    (A : Finset ℕ) (s t : ℕ) (Q R : Finset ℕ) :
    Bipartite.edgeCount (overlapGraph A s t Q R) Q R =
      (overlapGraph A s t Q R).card := by
  classical
  have hmap : Set.MapsTo Prod.snd
      (overlapGraph A s t Q R : Set (ℕ × ℕ)) (R : Set ℕ) := by
    intro qr hqr
    exact (mem_overlapGraph.mp hqr).2.1
  have hfiber (r : ℕ) (hr : r ∈ R) :
      ((overlapGraph A s t Q R).filter fun qr => qr.2 = r).card =
        Bipartite.leftDegree (overlapGraph A s t Q R) Q r := by
    rw [Bipartite.leftDegree]
    refine Finset.card_bij (fun qr _ => qr.1) ?_ ?_ ?_
    · intro qr hqr
      have hgraph := (Finset.mem_filter.mp hqr).1
      have hreq := (Finset.mem_filter.mp hqr).2
      exact Finset.mem_filter.mpr
        ⟨(mem_overlapGraph.mp hgraph).1, by simpa [← hreq] using! hgraph⟩
    · intro qr₁ h₁ qr₂ h₂ hfst
      apply Prod.ext hfst
      exact (Finset.mem_filter.mp h₁).2.trans
        (Finset.mem_filter.mp h₂).2.symm
    · intro q hq
      have hqQ := (Finset.mem_filter.mp hq).1
      have hqrGraph := (Finset.mem_filter.mp hq).2
      exact ⟨(q, r), Finset.mem_filter.mpr ⟨hqrGraph, rfl⟩, rfl⟩
  calc
    Bipartite.edgeCount (overlapGraph A s t Q R) Q R =
        ∑ r ∈ R,
          ((overlapGraph A s t Q R).filter fun qr => qr.2 = r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hfiber r hr).symm
    _ = (overlapGraph A s t Q R).card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmap

/-- The finite Kővári--Sós--Turán edge bound for the overlap graph on
any supplied vertex sets. -/
theorem overlapGraph_edgeCount_le
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {s t : ℕ} {Q R : Finset ℕ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hQ : ∀ q ∈ Q, s < q ∧ t < q)
    (hR : ∀ r ∈ R, s < r ∧ t < r) :
    (Bipartite.edgeCount (overlapGraph A s t Q R) Q R : ℝ) ≤
      (R.card : ℝ) +
        Real.sqrt (2 * (R.card : ℝ) * (Nat.choose Q.card 2 : ℝ)) :=
  Bipartite.edgeCount_le_card_add_sqrt
    (overlapGraph_c4Free hA hs ht hst hQ hR) Q R

/-- Cardinality form of the finite overlap estimate. -/
theorem overlapGraph_card_le
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {s t : ℕ} {Q R : Finset ℕ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hQ : ∀ q ∈ Q, s < q ∧ t < q)
    (hR : ∀ r ∈ R, s < r ∧ t < r) :
    ((overlapGraph A s t Q R).card : ℝ) ≤
      (R.card : ℝ) +
        Real.sqrt (2 * (R.card : ℝ) * (Nat.choose Q.card 2 : ℝ)) := by
  rw [← overlapGraph_edgeCount_eq_card]
  exact overlapGraph_edgeCount_le hA hs ht hst hQ hR

end PairwiseOverlap

end Erdos796
