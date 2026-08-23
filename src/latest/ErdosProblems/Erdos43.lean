/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 43.
https://www.erdosproblems.com/forum/thread/43

Informal authors:
- Kevin Barreto

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos43.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/43.lean
-/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/

import Mathlib
import ErdosProblems.Erdos42
import ErdosProblems.Erdos862

open scoped Pointwise

syntax (name := answerSyntax43) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

/-- The formal-conjectures definition of a Sidon set. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Finset

instance (A : Finset α) [AddCommMonoid α] [DecidableEq α] :
    Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The formal-conjectures maximum-cardinality definition. -/
def maxSidonSubsetCard {α : Type*} [AddCommMonoid α]
    (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end Finset

namespace Erdos43

open Filter

noncomputable abbrev f (N : ℕ) : ℕ :=
  Finset.maxSidonSubsetCard (Finset.Icc 1 N)

private lemma isSidon_iff_erdos42 (A : Set ℕ) :
    IsSidon A ↔ Erdos42.IsSidon A := by
  constructor
  · intro h a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ heq
    exact h a₁ ha₁ a₃ ha₃ a₂ ha₂ a₄ ha₄ heq
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    exact h hi₁ hi₂ hj₁ hj₂ heq

private lemma singleton_sidon (a : ℕ) : IsSidon ({a} : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
  simp_all

private lemma isSidon_iff_erdos862 {α : Type} [AddCommMonoid α] (A : Set α) :
    IsSidon A ↔ Erdos862.Sidon A := by
  constructor
  · intro h a b c d ha hb hc hd heq
    exact Set.pair_eq_pair_iff.mpr (h a ha c hc b hb d hd heq)
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    exact Set.pair_eq_pair_iff.mp (h i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ heq)

private lemma f_eq_erdos862_f (N : ℕ) : f N = Erdos862.f N := by
  classical
  unfold f Finset.maxSidonSubsetCard Erdos862.f
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact and_congr_right fun _ => isSidon_iff_erdos862 (A : Set ℕ)

private lemma sidon_of_sidonMod_of_lt {Q : ℕ} [NeZero Q] {T : Finset ℕ}
    (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) : IsSidon (T : Set ℕ) := by
  rw [isSidon_iff_erdos862]
  intro a b c d ha hb hc hd heq
  have hpair := hT (a : ZMod Q) (b : ZMod Q) (c : ZMod Q) (d : ZMod Q)
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      (by simpa using congrArg (fun n : ℕ => (n : ZMod Q)) heq)
  exact Erdos862.set_pair_eq_of_zmod_pair_eq Q (hlt a ha) (hlt b hb) (hlt c hc)
    (hlt d hd) hpair

private lemma orderedDiff_unique {Q : ℕ} [NeZero Q] {T : Finset ℕ}
    (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) {x y u v : ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (hu : u ∈ T) (hv : v ∈ T)
    (hxy : x ≠ y)
    (hdiff : (x : ZMod Q) - y = (u : ZMod Q) - v) : x = u ∧ y = v := by
  have hsum : (x : ZMod Q) + v = u + y := by linear_combination hdiff
  have hpairs := hT (x : ZMod Q) (v : ZMod Q) (u : ZMod Q) (y : ZMod Q)
    ⟨x, hx, rfl⟩ ⟨v, hv, rfl⟩ ⟨u, hu, rfl⟩ ⟨y, hy, rfl⟩ hsum
  rcases Set.pair_eq_pair_iff.mp hpairs with h | h
  · exact ⟨Erdos862.eq_of_zmod_eq_of_lt Q x u (hlt x hx) (hlt u hu) h.1,
      Erdos862.eq_of_zmod_eq_of_lt Q y v (hlt y hy) (hlt v hv) h.2.symm⟩
  · exact False.elim (hxy <|
      Erdos862.eq_of_zmod_eq_of_lt Q x y (hlt x hx) (hlt y hy) h.1)

private lemma zmod_sub_val_even {Q x y : ℕ} [NeZero Q]
    (hx : x < Q) (hy : y < Q) (hQ : Even Q)
    (hpar : Even x ↔ Even y) : Even (((x : ZMod Q) - y).val) := by
  have hxval : (x : ZMod Q).val = x := ZMod.val_natCast_of_lt hx
  have hyval : (y : ZMod Q).val = y := ZMod.val_natCast_of_lt hy
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hyx : y ≤ x
  · rw [ZMod.val_sub (by simpa [hxval, hyval] using hyx), hxval, hyval]
    exact (Nat.even_sub hyx).2 hpar
  · have hxylt : x < y := lt_of_not_ge hyx
    have hsubne : (y : ZMod Q) - x ≠ 0 := by
      intro h
      have : (y : ZMod Q) = x := sub_eq_zero.mp h
      exact hxy (Erdos862.eq_of_zmod_eq_of_lt Q x y hx hy this.symm)
    rw [show (x : ZMod Q) - y = -((y : ZMod Q) - x) by abel]
    rw [ZMod.neg_val, if_neg hsubne]
    rw [ZMod.val_sub (by simpa [hxval, hyval] using hxylt.le), hxval, hyval]
    apply (Nat.even_sub (by omega : y - x ≤ Q)).2
    constructor
    · intro _
      exact (Nat.even_sub hxylt.le).2 hpar.symm
    · intro _
      exact hQ

private lemma parity_count {Q N : ℕ} [NeZero Q] {T : Finset ℕ}
    (hQeq : Q = 2 * N) (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) :
    let E := T.filter Even
    let O := T.filter fun x => ¬ Even x
    E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1 := by
  classical
  let E := T.filter Even
  let O := T.filter fun x => ¬ Even x
  let D := E.offDiag ∪ O.offDiag
  let code : ℕ × ℕ → ℕ := fun p => (((p.1 : ZMod Q) - p.2).val) / 2
  have hQeven : Even Q := ⟨N, by omega⟩
  have hdisj : Disjoint E.offDiag O.offDiag := by
    rw [Finset.disjoint_left]
    intro p hpE hpO
    have he := Finset.mem_offDiag.mp hpE
    have ho := Finset.mem_offDiag.mp hpO
    exact (Finset.mem_filter.mp ho.1).2 (Finset.mem_filter.mp he.1).2
  have hDcard : D.card =
      (E.card * E.card - E.card) + (O.card * O.card - O.card) := by
    dsimp only [D]
    rw [Finset.card_union_of_disjoint hdisj, Finset.offDiag_card,
      Finset.offDiag_card]
  have hcode_even {p : ℕ × ℕ} (hp : p ∈ D) :
      Even (((p.1 : ZMod Q) - p.2).val) := by
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := Finset.mem_offDiag.mp hp
      exact zmod_sub_val_even (hlt p.1 (Finset.filter_subset _ _ h.1))
        (hlt p.2 (Finset.filter_subset _ _ h.2.1)) hQeven
        (iff_of_true (Finset.mem_filter.mp h.1).2 (Finset.mem_filter.mp h.2.1).2)
    · have h := Finset.mem_offDiag.mp hp
      exact zmod_sub_val_even (hlt p.1 (Finset.filter_subset _ _ h.1))
        (hlt p.2 (Finset.filter_subset _ _ h.2.1)) hQeven
        (iff_of_false (Finset.mem_filter.mp h.1).2 (Finset.mem_filter.mp h.2.1).2)
  have hcode_inj : Set.InjOn code (D : Set (ℕ × ℕ)) := by
    intro p hp r hr heq
    have hevenp := hcode_even hp
    have hevenr := hcode_even hr
    rcases hevenp with ⟨kp, hkp⟩
    rcases hevenr with ⟨kr, hkr⟩
    have hval : (((p.1 : ZMod Q) - p.2).val) =
        (((r.1 : ZMod Q) - r.2).val) := by
      change (((p.1 : ZMod Q) - p.2).val) / 2 =
        (((r.1 : ZMod Q) - r.2).val) / 2 at heq
      omega
    have hdiff : (p.1 : ZMod Q) - p.2 = (r.1 : ZMod Q) - r.2 :=
      ZMod.val_injective Q hval
    have hp' := Finset.mem_union.mp hp
    have hr' := Finset.mem_union.mp hr
    have hpT : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 := by
      rcases hp' with hp' | hp' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').2.1,
          (Finset.mem_offDiag.mp hp').2.2⟩
    have hrT : r.1 ∈ T ∧ r.2 ∈ T ∧ r.1 ≠ r.2 := by
      rcases hr' with hr' | hr' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hr').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hr').2.1,
          (Finset.mem_offDiag.mp hr').2.2⟩
    obtain ⟨h1, h2⟩ := orderedDiff_unique hT hlt hpT.1 hpT.2.1 hrT.1 hrT.2.1
      hpT.2.2 hdiff
    exact Prod.ext h1 h2
  have hcode_mem {p : ℕ × ℕ} (hp : p ∈ D) : code p ∈ Finset.Icc 1 (N - 1) := by
    have hp' := Finset.mem_union.mp hp
    have hpT : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 := by
      rcases hp' with hp' | hp' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').2.1,
          (Finset.mem_offDiag.mp hp').2.2⟩
    have hne : (p.1 : ZMod Q) - p.2 ≠ 0 := by
      intro hz
      have hz' : (p.1 : ZMod Q) = p.2 := sub_eq_zero.mp hz
      exact hpT.2.2 (Erdos862.eq_of_zmod_eq_of_lt Q p.1 p.2
        (hlt p.1 hpT.1) (hlt p.2 hpT.2.1) hz')
    have hvalpos : 0 < (((p.1 : ZMod Q) - p.2).val) :=
      Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero _).mp hne)
    have hvallt : (((p.1 : ZMod Q) - p.2).val) < 2 * N := by
      rw [← hQeq]
      exact ZMod.val_lt _
    rcases hcode_even hp with ⟨k, hk⟩
    apply Finset.mem_Icc.mpr
    change 1 ≤ (((p.1 : ZMod Q) - p.2).val) / 2 ∧
      (((p.1 : ZMod Q) - p.2).val) / 2 ≤ N - 1
    omega
  have himage : D.image code ⊆ Finset.Icc 1 (N - 1) := by
    rw [Finset.image_subset_iff]
    exact fun p hp => hcode_mem hp
  change E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1
  rw [← hDcard]
  calc
    D.card = (D.image code).card := (Finset.card_image_of_injOn hcode_inj).symm
    _ ≤ (Finset.Icc 1 (N - 1)).card := Finset.card_le_card himage
    _ = N - 1 := by simp

private lemma parity_imbalance_sq {q N a b : ℕ} (hq : 3 ≤ q)
    (hsum : a + b = q) (hN : 2 * N = q * q - 1)
    (hcount : a * a - a + (b * b - b) ≤ N - 1) :
    ((a : ℝ) - b) ^ 2 ≤ 2 * q - 3 := by
  have hqq1 : 1 ≤ q * q := by nlinarith
  have hNpos : 1 ≤ N := by
    have hqq9 : 9 ≤ q * q := by nlinarith
    omega
  have hNR : 2 * (N : ℝ) = (q : ℝ) * q - 1 := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hN
    norm_num only [Nat.cast_mul, Nat.cast_sub hqq1, Nat.cast_one] at hc
    exact hc
  have ha : 1 ≤ a := by
    by_contra hapos
    have ha0 : a = 0 := by omega
    subst a
    have hbq : b = q := by omega
    subst b
    have hqle : q ≤ q * q := by nlinarith
    have hcount' : q * q - q ≤ N - 1 := by simpa using hcount
    have hc : ((q * q - q : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcount'
    rw [Nat.cast_sub hqle, Nat.cast_mul, Nat.cast_sub hNpos] at hc
    norm_num at hc
    nlinarith
  have hb : 1 ≤ b := by
    by_contra hbpos
    have hb0 : b = 0 := by omega
    subst b
    have haq : a = q := by omega
    subst a
    have hqle : q ≤ q * q := by nlinarith
    have hcount' : q * q - q ≤ N - 1 := by simpa using hcount
    have hc : ((q * q - q : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcount'
    rw [Nat.cast_sub hqle, Nat.cast_mul, Nat.cast_sub hNpos] at hc
    norm_num at hc
    nlinarith
  have hale : a ≤ a * a := by nlinarith
  have hble : b ≤ b * b := by nlinarith
  have hc : ((a * a - a + (b * b - b) : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  rw [Nat.cast_add, Nat.cast_sub hale, Nat.cast_sub hble, Nat.cast_sub hNpos,
    Nat.cast_mul, Nat.cast_mul] at hc
  norm_num at hc
  have hs := congrArg (fun n : ℕ => (n : ℝ)) hsum
  norm_num only [Nat.cast_add] at hs
  nlinarith

private def halfShift (x : ℕ) : ℕ := x / 2 + 1

private lemma halfShift_injOn {S : Finset ℕ} {r : ℕ}
    (hpar : ∀ x ∈ S, x % 2 = r) : Set.InjOn halfShift (S : Set ℕ) := by
  intro x hx y hy hxy
  have hxpar := hpar x hx
  have hypar := hpar y hy
  simp only [halfShift] at hxy
  omega

private lemma halfShift_sidon {T S : Finset ℕ} {r : ℕ}
    (hST : S ⊆ T) (hT : IsSidon (T : Set ℕ))
    (hpar : ∀ x ∈ S, x % 2 = r) :
    IsSidon (S.image halfShift : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hi₁
  obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hj₁
  obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hi₂
  obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hj₂
  have horig : x₁ + x₂ = y₁ + y₂ := by
    have hx₁p := hpar x₁ hx₁
    have hx₂p := hpar x₂ hx₂
    have hy₁p := hpar y₁ hy₁
    have hy₂p := hpar y₂ hy₂
    simp only [halfShift] at heq
    omega
  rcases hT x₁ (hST hx₁) y₁ (hST hy₁) x₂ (hST hx₂) y₂ (hST hy₂) horig with h | h
  · exact Or.inl ⟨congrArg halfShift h.1, congrArg halfShift h.2⟩
  · exact Or.inr ⟨congrArg halfShift h.1, congrArg halfShift h.2⟩

private lemma halfShift_bounds {N : ℕ} {S : Finset ℕ}
    (hbound : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * N - 1) :
    S.image halfShift ⊆ Finset.Icc 1 N := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have h := hbound x hx
  apply Finset.mem_Icc.mpr
  simp only [halfShift]
  omega

private lemma halfShift_diff_disjoint {Q : ℕ} [NeZero Q]
    {T E O : Finset ℕ} (hET : E ⊆ T) (hOT : O ⊆ T)
    (hTmod : Erdos862.SidonMod Q (T : Set ℕ)) (hlt : ∀ x ∈ T, x < Q)
    (hEpar : ∀ x ∈ E, x % 2 = 0) (hOpar : ∀ x ∈ O, x % 2 = 1)
    (hEne : E.Nonempty) (hOne : O.Nonempty) :
    (E.image halfShift - E.image halfShift) ∩
      (O.image halfShift - O.image halfShift) = ({0} : Finset ℕ) := by
  ext d
  constructor
  · intro hd
    have hdE := (Finset.mem_inter.mp hd).1
    have hdO := (Finset.mem_inter.mp hd).2
    obtain ⟨ae₁, hae₁, ae₂, hae₂, hde⟩ := Finset.mem_sub.mp hdE
    obtain ⟨ao₁, hao₁, ao₂, hao₂, hdo⟩ := Finset.mem_sub.mp hdO
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hae₁
    obtain ⟨e₂, he₂, rfl⟩ := Finset.mem_image.mp hae₂
    obtain ⟨o₁, ho₁, rfl⟩ := Finset.mem_image.mp hao₁
    obtain ⟨o₂, ho₂, rfl⟩ := Finset.mem_image.mp hao₂
    have he₁p := hEpar e₁ he₁
    have he₂p := hEpar e₂ he₂
    have ho₁p := hOpar o₁ ho₁
    have ho₂p := hOpar o₂ ho₂
    by_cases hd0 : d = 0
    · simpa [hd0]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hediff : e₁ - e₂ = 2 * d := by
        simp only [halfShift] at hde
        omega
      have hodiff : o₁ - o₂ = 2 * d := by
        simp only [halfShift] at hdo
        omega
      have he12 : e₂ ≤ e₁ := by omega
      have ho12 : o₂ ≤ o₁ := by omega
      have hnatdiff : e₁ - e₂ = o₁ - o₂ := by omega
      have hzcast := congrArg (fun n : ℕ => (n : ZMod Q)) hnatdiff
      have hzdiff : (e₁ : ZMod Q) - e₂ = (o₁ : ZMod Q) - o₂ := by
        simpa [Nat.cast_sub he12, Nat.cast_sub ho12] using hzcast
      obtain ⟨heo, _⟩ := orderedDiff_unique hTmod hlt (hET he₁) (hET he₂)
        (hOT ho₁) (hOT ho₂) (by omega) hzdiff
      omega
  · intro hd
    have hd0 : d = 0 := by simpa using hd
    subst d
    obtain ⟨e, he⟩ := hEne
    obtain ⟨o, ho⟩ := hOne
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_sub.mpr
      exact ⟨halfShift e, Finset.mem_image.mpr ⟨e, he, rfl⟩,
        halfShift e, Finset.mem_image.mpr ⟨e, he, rfl⟩, Nat.sub_self _⟩
    · apply Finset.mem_sub.mpr
      exact ⟨halfShift o, Finset.mem_image.mpr ⟨o, ho, rfl⟩,
        halfShift o, Finset.mem_image.mpr ⟨o, ho, rfl⟩, Nat.sub_self _⟩

private lemma coefficient_comparison {r : ℝ} :
    1 - 3 * r ≤ (1 - r) * (1 - 2 * r) := by
  nlinarith [sq_nonneg r]

private lemma product_lower_bound {r q N m : ℝ} (hrle : r ≤ 1 / 4)
    (hN : 2 * N = q ^ 2 - 1)
    (hprod : ((1 - r) * q / 2) * ((1 - 2 * r) * q / 2) ≤ m * (m - 1)) :
    (1 - 3 * r) * N / 2 ≤ m * (m - 1) := by
  have hcoef : 0 ≤ 1 - 3 * r := by linarith
  have hNq : N / 2 ≤ q ^ 2 / 4 := by nlinarith
  calc
    (1 - 3 * r) * N / 2 = (1 - 3 * r) * (N / 2) := by ring
    _ ≤ (1 - 3 * r) * (q ^ 2 / 4) := mul_le_mul_of_nonneg_left hNq hcoef
    _ ≤ ((1 - r) * (1 - 2 * r)) * (q ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right coefficient_comparison (by positivity)
    _ = ((1 - r) * q / 2) * ((1 - 2 * r) * q / 2) := by ring
    _ ≤ m * (m - 1) := hprod

private lemma choose_two_cast_le_sq (n : ℕ) :
    (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  have htwo : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have hc := congrArg (fun k : ℕ => (k : ℝ)) htwo
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    norm_num only [Nat.cast_mul, Nat.cast_sub hn1] at hc
    nlinarith

private lemma coefficient_gap {η : ℝ} (hη : 0 < η) :
    (1 - 7 * η) * (1 + η) ^ 2 < 1 - 3 * (η / 4) := by
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hη3 : 0 ≤ η ^ 2 * η := mul_nonneg hη2 hη.le
  nlinarith

private lemma choose_upper_of_sqrt_bound {n N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (n : ℝ) ≤ (1 + ε) * Real.sqrt N) :
    (n.choose 2 : ℝ) ≤ (1 + ε) ^ 2 * (N : ℝ) / 2 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hrhs : 0 ≤ (1 + ε) * Real.sqrt N := by positivity
  have hsq : (n : ℝ) ^ 2 ≤ ((1 + ε) * Real.sqrt N) ^ 2 :=
    (sq_le_sq₀ hn hrhs).2 h
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)] at hsq
  exact (choose_two_cast_le_sq n).trans (by nlinarith)

private theorem exists_good_pair (q : ℕ) (hqprime : q.Prime) (hq : 3 ≤ q)
    (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1 / 4)
    (hlargeSq : 2 ≤ r ^ 2 * q) (hlargeLin : 4 ≤ r * q) :
    let N := (q ^ 2 - 1) / 2
    ∃ A B : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
      IsSidon (A : Set ℕ) ∧ IsSidon (B : Set ℕ) ∧
      A.card = B.card ∧ (A - A) ∩ (B - B) = {0} ∧
      (1 - 3 * r) * (N : ℝ) / 2 ≤
        ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) := by
  classical
  let Q := q ^ 2 - 1
  let N := Q / 2
  have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
  have hqq1 : 1 ≤ q * q := by nlinarith
  have hQeven : Even Q := by
    simp only [Q, pow_two]
    apply (Nat.even_sub hqq1).2
    exact iff_of_false (Nat.not_even_iff_odd.mpr (hqodd.mul hqodd)) (by norm_num)
  have hQeq : Q = 2 * N := by
    exact (Nat.two_mul_div_two_of_even hQeven).symm
  have hQgt : 1 < Q := by
    have hqq9 : 9 ≤ q * q := by nlinarith
    simp only [Q, pow_two]
    omega
  letI : NeZero Q := ⟨by omega⟩
  obtain ⟨S, hSsidon, hScard⟩ :
      ∃ S : Finset (ZMod Q), Erdos862.Sidon (S : Set (ZMod Q)) ∧ S.card = q := by
    simpa only [Q] using
      (Erdos862.bose_chowla_at_h_eq_2 q hqprime.isPrimePow)
  have hScardQ : S.card < Q := by
    rw [hScard]
    have hqgap : q + 1 < q * q := by nlinarith
    simp only [Q, pow_two]
    omega
  obtain ⟨S', hS'sidon, hS'card, hS'zero⟩ :=
    Erdos862.shift_sidon_mod Q hQgt S hSsidon hScardQ
  obtain ⟨T, hTmod, hTcard, hTsub, _hTdef⟩ :=
    Erdos862.lift_sidon_mod Q hQgt S' hS'sidon hS'zero
  have hTcardq : T.card = q := hTcard.trans (hS'card.trans hScard)
  have hTlt : ∀ x ∈ T, x < Q := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub hx
    have hx' := Finset.mem_Icc.mp hxmem
    exact lt_of_le_of_lt hx'.2 (Nat.sub_lt (by omega) zero_lt_one)
  have hTsidon : IsSidon (T : Set ℕ) := sidon_of_sidonMod_of_lt hTmod hTlt
  let E := T.filter Even
  let O := T.filter fun x => ¬ Even x
  have hEsumO : E.card + O.card = q := by
    calc
      E.card + O.card = T.card := by
        simpa only [E, O] using
          (Finset.card_filter_add_card_filter_not (s := T) Even)
      _ = q := hTcardq
  have hcount : E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1 :=
    parity_count hQeq hTmod hTlt
  have hNrel : 2 * N = q * q - 1 := by simpa [Q, pow_two] using hQeq.symm
  have himb : (((E.card : ℝ) - O.card) ^ 2) ≤ 2 * q - 3 :=
    parity_imbalance_sq hq hEsumO hNrel hcount
  have hsumR : (E.card : ℝ) + O.card = q := by exact_mod_cast hEsumO
  have hsqdom : 2 * (q : ℝ) ≤ (r * q) ^ 2 := by
    have hqnonneg : (0 : ℝ) ≤ q := by positivity
    have := mul_le_mul_of_nonneg_right hlargeSq hqnonneg
    nlinarith
  have hdiffE : (E.card : ℝ) - O.card ≤ r * q := by
    have hrq : 0 ≤ r * (q : ℝ) := by positivity
    nlinarith [sq_nonneg ((E.card : ℝ) - O.card + r * q)]
  have hdiffO : (O.card : ℝ) - E.card ≤ r * q := by
    have hrq : 0 ≤ r * (q : ℝ) := by positivity
    nlinarith [sq_nonneg ((E.card : ℝ) - O.card - r * q)]
  let m := min E.card O.card
  have hmR : (1 - r) * (q : ℝ) / 2 ≤ (m : ℝ) := by
    by_cases hEO : E.card ≤ O.card
    · rw [show m = E.card by simp [m, hEO]]
      nlinarith
    · have hOE : O.card ≤ E.card := by omega
      rw [show m = O.card by simp [m, hOE]]
      nlinarith
  have hmpos : 0 < m := by
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have : (0 : ℝ) < m := by nlinarith
    exact_mod_cast this
  obtain ⟨E', hE'E, hE'card⟩ := Finset.exists_subset_card_eq (min_le_left E.card O.card)
  obtain ⟨O', hO'O, hO'card⟩ := Finset.exists_subset_card_eq (min_le_right E.card O.card)
  have hE'cardm : E'.card = m := hE'card
  have hO'cardm : O'.card = m := hO'card
  have hE'T : E' ⊆ T := hE'E.trans (Finset.filter_subset _ _)
  have hO'T : O' ⊆ T := hO'O.trans (Finset.filter_subset _ _)
  have hE'par : ∀ x ∈ E', x % 2 = 0 := by
    intro x hx
    exact Nat.even_iff.mp (Finset.mem_filter.mp (hE'E hx)).2
  have hO'par : ∀ x ∈ O', x % 2 = 1 := by
    intro x hx
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp (hO'O hx)).2)
  let A := E'.image halfShift
  let B := O'.image halfShift
  have hAcard : A.card = m := by
    dsimp only [A]
    rw [Finset.card_image_of_injOn (halfShift_injOn hE'par), hE'cardm]
  have hBcard : B.card = m := by
    dsimp only [B]
    rw [Finset.card_image_of_injOn (halfShift_injOn hO'par), hO'cardm]
  have hboundE : ∀ x ∈ E', 1 ≤ x ∧ x ≤ 2 * N - 1 := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub (hE'T hx)
    rw [hQeq] at hxmem
    exact Finset.mem_Icc.mp hxmem
  have hboundO : ∀ x ∈ O', 1 ≤ x ∧ x ≤ 2 * N - 1 := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub (hO'T hx)
    rw [hQeq] at hxmem
    exact Finset.mem_Icc.mp hxmem
  have hAsub : A ⊆ Finset.Icc 1 N := by
    exact halfShift_bounds hboundE
  have hBsub : B ⊆ Finset.Icc 1 N := by
    exact halfShift_bounds hboundO
  have hAsidon : IsSidon (A : Set ℕ) := halfShift_sidon hE'T hTsidon hE'par
  have hBsidon : IsSidon (B : Set ℕ) := halfShift_sidon hO'T hTsidon hO'par
  have hE'ne : E'.Nonempty := Finset.card_pos.mp (by rw [hE'cardm]; exact hmpos)
  have hO'ne : O'.Nonempty := Finset.card_pos.mp (by rw [hO'cardm]; exact hmpos)
  have hdiff : (A - A) ∩ (B - B) = ({0} : Finset ℕ) :=
    halfShift_diff_disjoint hE'T hO'T hTmod hTlt hE'par hO'par hE'ne hO'ne
  have hm1R : (1 - 2 * r) * (q : ℝ) / 2 ≤ (m : ℝ) - 1 := by
    nlinarith
  have hleftnonneg : 0 ≤ (1 - r) * (q : ℝ) / 2 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hleftnonneg' : 0 ≤ (1 - 2 * r) * (q : ℝ) / 2 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hmnonneg : 0 ≤ (m : ℝ) := by positivity
  have hprod : ((1 - r) * (q : ℝ) / 2) * ((1 - 2 * r) * (q : ℝ) / 2) ≤
      (m : ℝ) * ((m : ℝ) - 1) :=
    mul_le_mul hmR hm1R hleftnonneg' hmnonneg
  have hNR : 2 * (N : ℝ) = (q : ℝ) * q - 1 := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hNrel
    norm_num only [Nat.cast_mul, Nat.cast_sub hqq1, Nat.cast_one] at hc
    exact hc
  have hlower : (1 - 3 * r) * (N : ℝ) / 2 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    exact product_lower_bound hrle (by simpa [pow_two] using hNR) hprod
  have htwochoose : 2 * m.choose 2 = m * (m - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self m)
  refine ⟨A, B, hAsub, hBsub, hAsidon, hBsidon, hAcard.trans hBcard.symm,
    hdiff, ?_⟩
  rw [hAcard, hBcard]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) htwochoose
  norm_num only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)] at hc
  norm_num only [Nat.cast_add]
  nlinarith

theorem erdos_43.parts.i : answer(False) ↔
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C := by
  constructor
  · exact False.elim
  · rintro ⟨C, hC⟩
    obtain ⟨m : ℕ, hm : C < m⟩ := exists_nat_gt C
    let M := 2 * m + 2
    have hM : 1 ≤ M := by simp [M]
    obtain ⟨N₁, hN₁⟩ := Erdos42.theorem_1_1_via_cayley M hM
    obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 hC)
    let N := max (max N₁ N₂) 1
    have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN₂' : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hNpos : 1 ≤ N := le_max_right _ _
    let candidates : Finset (Finset ℕ) :=
      (Finset.Icc 1 N).powerset.filter fun A : Finset ℕ ↦ IsSidon (A : Set ℕ)
    have hsingleton : ({1} : Finset ℕ) ∈ candidates := by
      simp [candidates, hNpos, singleton_sidon]
    have hcandidates : candidates.Nonempty := ⟨{1}, hsingleton⟩
    obtain ⟨A, hAcand, hAmax⟩ :=
      Finset.exists_mem_eq_sup candidates hcandidates Finset.card
    have hAsub : A ⊆ Finset.Icc 1 N :=
      Finset.mem_powerset.1 (Finset.mem_filter.1 hAcand).1
    have hAsidon : IsSidon (A : Set ℕ) :=
      (Finset.mem_filter.1 hAcand).2
    have hAcard : A.card = f N := by
      exact hAmax.symm
    have hAone : 1 ≤ A.card := by
      rw [← hAmax]
      exact Finset.le_sup (f := Finset.card) hsingleton
    have hAnonempty : (A : Set ℕ).Nonempty := by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      exact ⟨a, ha⟩
    obtain ⟨Bset, hBsub, hBsidon, hBcard, hdiff⟩ :=
      hN₁ N hN₁' (A : Set ℕ) (by
        intro a ha
        exact Finset.mem_Icc.mp (hAsub ha))
        ((isSidon_iff_erdos42 _).1 hAsidon) hAnonempty
    have hBfinite : Bset.Finite := Set.finite_Icc 1 N |>.subset hBsub
    let B : Finset ℕ := hBfinite.toFinset
    have hBsub' : B ⊆ Finset.Icc 1 N := by
      intro b hb
      exact Finset.mem_Icc.mpr (hBsub (by simpa [B] using hb))
    have hBsidon' : IsSidon (B : Set ℕ) := by
      rw [show (B : Set ℕ) = Bset by ext; simp [B]]
      exact (isSidon_iff_erdos42 _).2 hBsidon
    have hBcard' : B.card = M := by
      change hBfinite.toFinset.card = M
      rw [← Set.ncard_eq_toFinset_card Bset hBfinite]
      exact hBcard
    have hdiff' : (A - A) ∩ (B - B) = ({0} : Finset ℕ) := by
      apply Finset.coe_injective
      simpa [B] using hdiff
    have hbound := hN₂ N hN₂' A B hAsub hBsub' hAsidon hBsidon' hdiff'
    rw [hAcard, hBcard'] at hbound
    have hchoose : m < M.choose 2 := by
      rw [show M = (2 * m + 1) + 1 by simp [M]]
      rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
      simp
      omega
    have hchooseR : (m : ℝ) < (M.choose 2 : ℝ) := by exact_mod_cast hchoose
    norm_num only [Nat.cast_add] at hbound
    linarith

theorem erdos_43.parts.ii : answer(False) ↔
    ∃ᵉ (c > 0), ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      A.card = B.card →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤
        (1 - c + o N) * ((f N).choose 2 : ℝ) := by
  constructor
  · exact False.elim
  · rintro ⟨c, hc, o, ho, hall⟩
    let η : ℝ := min (c / 8) (1 / 8)
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min (div_pos hc (by norm_num)) (by norm_num)
    have hηc : η ≤ c / 8 := min_le_left _ _
    have hηle : η ≤ 1 / 8 := min_le_right _ _
    let r : ℝ := η / 4
    have hr : 0 < r := div_pos hη (by norm_num)
    have hrle : r ≤ 1 / 4 := by dsimp only [r]; nlinarith
    obtain ⟨NT, hNT⟩ := Erdos862.ErdosTuran η hη
    have hoevent : ∀ᶠ N : ℕ in atTop, |o N| ≤ η := by
      have h := (Asymptotics.isLittleO_iff.mp ho) hη
      exact h.mono fun N hN => by simpa using hN
    obtain ⟨No, hNo⟩ := eventually_atTop.mp hoevent
    obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hall
    obtain ⟨Lsq : ℕ, hLsq : 2 / r ^ 2 < Lsq⟩ := exists_nat_gt (2 / r ^ 2)
    obtain ⟨Llin : ℕ, hLlin : 4 / r < Llin⟩ := exists_nat_gt (4 / r)
    let R := max NT (max No Nb)
    let Q₀ := max (max Lsq Llin) (2 * R + 3)
    obtain ⟨q, hQq, hqprime⟩ := Nat.exists_infinite_primes Q₀
    have hqR : 2 * R + 3 ≤ q := (le_max_right _ _).trans hQq
    have hq3 : 3 ≤ q := by omega
    have hqLsq : Lsq ≤ q :=
      (le_max_left Lsq Llin).trans (le_max_left _ _ |>.trans hQq)
    have hqLlin : Llin ≤ q :=
      (le_max_right Lsq Llin).trans (le_max_left _ _ |>.trans hQq)
    have hlargeSq : 2 ≤ r ^ 2 * (q : ℝ) := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
      have hs : 2 < r ^ 2 * (Lsq : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hr2).mp hLsq
      have hcast : (Lsq : ℝ) ≤ q := by exact_mod_cast hqLsq
      nlinarith [mul_le_mul_of_nonneg_left hcast hr2.le]
    have hlargeLin : 4 ≤ r * (q : ℝ) := by
      have hs : 4 < r * (Llin : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hr).mp hLlin
      have hcast : (Llin : ℝ) ≤ q := by exact_mod_cast hqLlin
      nlinarith [mul_le_mul_of_nonneg_left hcast hr.le]
    let N := (q ^ 2 - 1) / 2
    have hRtwo : R * 2 ≤ q ^ 2 - 1 := by
      have hqR' : 2 * R + 3 ≤ q := hqR
      have haux : R * 2 + 1 ≤ q ^ 2 := by nlinarith
      omega
    have hRN : R ≤ N := by
      dsimp only [N]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hRtwo
    have hNTN : NT ≤ N := (le_max_left NT (max No Nb)).trans hRN
    have hNoN : No ≤ N :=
      (le_trans (le_max_left No Nb) (le_max_right NT (max No Nb))).trans hRN
    have hNbN : Nb ≤ N :=
      (le_trans (le_max_right No Nb) (le_max_right NT (max No Nb))).trans hRN
    obtain ⟨A, B, hAsub, hBsub, hAsidon, hBsidon, hcard, hdiff, hlower⟩ :=
      exists_good_pair q hqprime hq3 r hr hrle hlargeSq hlargeLin
    have hNpos : 0 < N := by
      have hq9 : 9 ≤ q ^ 2 := by nlinarith
      dsimp only [N]
      omega
    have hoNabs : |o N| ≤ η := hNo N hNoN
    have hoN : o N ≤ η := (le_abs_self (o N)).trans hoNabs
    have hcoefle : 1 - c + o N ≤ 1 - 7 * η := by nlinarith
    have hfbound := hNT N hNTN
    rw [← f_eq_erdos862_f N] at hfbound
    have hfchoose : ((f N).choose 2 : ℝ) ≤ (1 + η) ^ 2 * (N : ℝ) / 2 :=
      choose_upper_of_sqrt_bound hη.le hfbound
    have halleged := hNb N hNbN A B hAsub hBsub hAsidon hBsidon hcard hdiff
    have hleftpos : 0 < ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) := by
      have hcoefpos : 0 < 1 - 3 * r := by
        dsimp only [r]
        nlinarith
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
      have : 0 < (1 - 3 * r) * (N : ℝ) / 2 := by positivity
      exact lt_of_lt_of_le this hlower
    by_cases hcoef : 0 ≤ 1 - c + o N
    · have huppernonneg : 0 ≤ (1 + η) ^ 2 * (N : ℝ) / 2 := by positivity
      have hseven : 0 ≤ 1 - 7 * η := by nlinarith
      have hgap := coefficient_gap hη
      have hNhalf : 0 < (N : ℝ) / 2 := by positivity
      have hstrict :
          (1 - 7 * η) * ((1 + η) ^ 2 * (N : ℝ) / 2) <
            (1 - 3 * r) * (N : ℝ) / 2 := by
        have hg := mul_lt_mul_of_pos_right hgap hNhalf
        dsimp only [r]
        nlinarith
      have hchain :
          ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) <
            (1 - 3 * r) * (N : ℝ) / 2 := calc
        ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)
            ≤ (1 - c + o N) * ((f N).choose 2 : ℝ) := halleged
        _ ≤ (1 - c + o N) * ((1 + η) ^ 2 * (N : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hfchoose hcoef
        _ ≤ (1 - 7 * η) * ((1 + η) ^ 2 * (N : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcoefle huppernonneg
        _ < (1 - 3 * r) * (N : ℝ) / 2 := hstrict
      exact (not_lt_of_ge hlower) hchain
    · have hcoefneg : 1 - c + o N < 0 := lt_of_not_ge hcoef
      have hchoose_nonneg : (0 : ℝ) ≤ ((f N).choose 2 : ℝ) := by positivity
      have : (1 - c + o N) * ((f N).choose 2 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcoefneg.le hchoose_nonneg
      linarith

#print axioms Erdos43.erdos_43.parts.i
#print axioms Erdos43.erdos_43.parts.ii

end Erdos43
