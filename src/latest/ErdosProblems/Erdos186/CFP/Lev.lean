/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Elementary
import ErdosProblems.Erdos186.CFP.LevBox
import ErdosProblems.Erdos186.CFP.LevExtension
import ErdosProblems.Erdos186.CFP.LevNormalization
import ErdosProblems.Erdos186.CFP.LevProposition
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin

/-!
# Lev's one-dimensional interval theorem

This file gives the finite-set interface used for Lemmas 2.10 and 2.11 of
Conlon--Fox--Pham.  An integer set is `Primitive` when it is not contained
in an arithmetic progression of integral common difference greater than one.
The divisibility formulation below avoids making an arbitrary choice of an
initial term.

All interval lengths are numbers of points.  Thus `Icc a (a + m - 1)` has
length `m` when `m` is positive, while the conclusion of Lev's theorem is
written as `Icc a (a + ℓ * (n - 1))`, which has
`ℓ * (n - 1) + 1` points.
-/

namespace Erdos186.CFP.Lev

open scoped BigOperators Pointwise

/-! ## Finite iterated sumsets -/

/-- The sumset of a finite family of integer sets.  We define it recursively
so that the empty sum is `{0}` (pointwise addition of finsets itself uses the
empty finset as its `AddMonoid` zero). -/
def familySumset : {ℓ : ℕ} → (Fin ℓ → Finset ℤ) → Finset ℤ
  | 0, _ => {0}
  | ℓ + 1, S => S 0 + familySumset (fun i : Fin ℓ ↦ S i.succ)

@[simp] theorem familySumset_zero (S : Fin 0 → Finset ℤ) :
    familySumset S = {0} := by
  simp [familySumset]

@[simp] theorem familySumset_succ {ℓ : ℕ} (S : Fin (ℓ + 1) → Finset ℤ) :
    familySumset S = S 0 + familySumset (fun i : Fin ℓ ↦ S i.succ) := by
  rw [familySumset]

/-- The list and finite-index presentations of an iterated sumset agree. -/
theorem listSumset_ofFn_eq_familySumset {ℓ : ℕ} (S : Fin ℓ → Finset ℤ) :
    LevMultipleAddition.listSumset (List.ofFn S) = familySumset S := by
  induction ℓ with
  | zero => simp [familySumset, LevMultipleAddition.listSumset]
  | succ ℓ ih =>
      rw [List.ofFn_succ, LevMultipleAddition.listSumset_cons,
        familySumset_succ, ih]

@[simp] theorem mem_familySumset_one {S : Fin 1 → Finset ℤ} {x : ℤ} :
    x ∈ familySumset S ↔ x ∈ S 0 := by
  simp only [familySumset, Finset.mem_add, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, rfl, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨x, hx, 0, rfl, by simp⟩

/-- Membership in a two-set pointwise sum. -/
theorem mem_add_iff {A B : Finset ℤ} {z : ℤ} :
    z ∈ A + B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = z := by
  simp only [Finset.mem_add]

/-- A pointwise sum of two nonempty finite sets is nonempty. -/
theorem add_nonempty {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a + b, mem_add_iff.mpr ⟨a, ha, b, hb, rfl⟩⟩

/-- Every sumset contains the sum of any selected pair of elements. -/
theorem add_mem_add {A B : Finset ℤ} {a b : ℤ}
    (ha : a ∈ A) (hb : b ∈ B) : a + b ∈ A + B :=
  mem_add_iff.mpr ⟨a, ha, b, hb, rfl⟩

/-- Membership in an iterated sumset is equivalent to choosing one element
from every summand and adding the chosen elements. -/
theorem mem_familySumset_iff {ℓ : ℕ} {S : Fin ℓ → Finset ℤ} {x : ℤ} :
    x ∈ familySumset S ↔
      ∃ f : Fin ℓ → ℤ, (∀ i, f i ∈ S i) ∧ ∑ i, f i = x := by
  induction ℓ generalizing x with
  | zero =>
      simp [familySumset, eq_comm]
  | succ ℓ ih =>
      rw [familySumset_succ, mem_add_iff]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨f, hf, hfsum⟩ := ih.mp hb
        refine ⟨Fin.cases a f, ?_, ?_⟩
        · intro i
          refine Fin.cases ha (fun j ↦ ?_) i
          exact hf j
        · rw [Fin.sum_univ_succ]
          simpa using congrArg (a + ·) hfsum
      · rintro ⟨f, hf, rfl⟩
        refine ⟨f 0, hf 0, ∑ i : Fin ℓ, f i.succ, ?_, ?_⟩
        · apply ih.mpr
          exact ⟨fun i ↦ f i.succ, fun i ↦ hf i.succ, rfl⟩
        · rw [Fin.sum_univ_succ]

/-- Iterated sumsets are invariant under reindexing by an equivalence. -/
theorem familySumset_equiv {k ℓ : ℕ} (e : Fin k ≃ Fin ℓ)
    (S : Fin ℓ → Finset ℤ) :
    familySumset (fun i ↦ S (e i)) = familySumset S := by
  ext x
  simp only [mem_familySumset_iff]
  constructor
  · rintro ⟨f, hf, hsum⟩
    refine ⟨fun j ↦ f (e.symm j), fun j ↦ ?_, ?_⟩
    · simpa using hf (e.symm j)
    · rw [← hsum]
      exact Equiv.sum_comp e.symm f
  · rintro ⟨f, hf, hsum⟩
    refine ⟨fun i ↦ f (e i), fun i ↦ hf (e i), ?_⟩
    rw [← hsum]
    exact Equiv.sum_comp e f

/-- Splitting an indexed family into two consecutive blocks turns its
iterated sumset into the pointwise sum of the two block sumsets. -/
theorem familySumset_append {k m : ℕ} (A : Fin k → Finset ℤ)
    (B : Fin m → Finset ℤ) :
    familySumset (Fin.append A B) = familySumset A + familySumset B := by
  ext x
  simp only [mem_familySumset_iff, mem_add_iff]
  constructor
  · rintro ⟨f, hf, hsum⟩
    refine ⟨∑ i : Fin k, f (Fin.castAdd m i), ?_,
      ∑ j : Fin m, f (Fin.natAdd k j), ?_, ?_⟩
    · refine ⟨fun i ↦ f (Fin.castAdd m i), fun i ↦ ?_, rfl⟩
      simpa using hf (Fin.castAdd m i)
    · refine ⟨fun j ↦ f (Fin.natAdd k j), fun j ↦ ?_, rfl⟩
      simpa using hf (Fin.natAdd k j)
    · rw [← hsum]
      exact (Fin.sum_univ_add f).symm
  · rintro ⟨a, ⟨f, hf, rfl⟩, b, ⟨g, hg, rfl⟩, hab⟩
    refine ⟨Fin.append f g, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simpa using hf j
      · simpa using hg j
    · rw [Fin.sum_univ_add]
      simpa using hab

/-- The first copy of `Fin k` enumerates the even positions and the second
copy enumerates the odd positions in `Fin (k+k)`. -/
noncomputable def alternateEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (k + k) :=
  Equiv.ofBijective
    (fun s ↦ match s with
      | Sum.inl i => ⟨2 * i, by omega⟩
      | Sum.inr i => ⟨2 * i + 1, by omega⟩)
    (by
      constructor
      · intro a b hab
        rcases a with i | i <;> rcases b with j | j
        · congr
          apply Fin.ext
          simpa using congrArg Fin.val hab
        · have := congrArg Fin.val hab
          simp at this
          omega
        · have := congrArg Fin.val hab
          simp at this
          omega
        · congr
          apply Fin.ext
          simpa using congrArg Fin.val hab
      · intro x
        have hmodlt : x.val % 2 < 2 := Nat.mod_lt _ (by omega)
        have hdecomp : x.val % 2 + 2 * (x.val / 2) = x.val :=
          Nat.mod_add_div x.val 2
        by_cases heven : x.val % 2 = 0
        · let i : Fin k := ⟨x.val / 2, by omega⟩
          refine ⟨Sum.inl i, Fin.ext ?_⟩
          simp [i]
          omega
        · have hodd : x.val % 2 = 1 := by omega
          let i : Fin k := ⟨x.val / 2, by omega⟩
          refine ⟨Sum.inr i, Fin.ext ?_⟩
          simp [i]
          omega)

/-- The full sumset is the sum of the alternating even and odd blocks. -/
theorem familySumset_even_add_odd {k : ℕ} (S : Fin (k + k) → Finset ℤ) :
    familySumset S =
      familySumset (fun i : Fin k ↦ S ⟨2 * i, by omega⟩) +
        familySumset (fun i : Fin k ↦ S ⟨2 * i + 1, by omega⟩) := by
  let e : Fin (k + k) ≃ Fin (k + k) := finSumFinEquiv.symm.trans (alternateEquiv k)
  rw [← familySumset_append]
  rw [← familySumset_equiv e S]
  congr 1
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
      Fin.append_left]
    apply congrArg S
    apply Fin.ext
    rfl
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      Fin.append_right]
    apply congrArg S
    apply Fin.ext
    rfl

/-- Every finite family of natural-number weights admits a nondecreasing
enumeration.  Ties are broken by the original index, only to make the sorting
relation antisymmetric. -/
theorem exists_monotone_reindex {k : ℕ} (w : Fin k → ℕ) :
    ∃ e : Fin k ≃ Fin k, ∀ {i j : Fin k}, i ≤ j → w (e i) ≤ w (e j) := by
  classical
  let key : Fin k → Lex (ℕ × ℕ) := fun i ↦ toLex (w i, i)
  have hkey : Function.Injective key := by
    intro i j hij
    exact Fin.ext (congrArg (fun x ↦ (ofLex x).2) hij)
  let r : Fin k → Fin k → Prop := fun i j ↦ key i ≤ key j
  letI : IsTrans (Fin k) r := ⟨fun _ _ _ hab hbc ↦ hab.trans hbc⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ hab hba ↦ hkey (le_antisymm hab hba)⟩
  letI : Std.Total r := ⟨fun a b ↦ le_total (key a) (key b)⟩
  let l := (Finset.univ : Finset (Fin k)).sort r
  have hlen : l.length = k := by simp [l]
  have hnodup : l.Nodup := by simpa [l] using
    (Finset.sort_nodup (Finset.univ : Finset (Fin k)) r)
  have hall : ∀ i : Fin k, i ∈ l := by intro i; simp [l]
  let e₀ : Fin l.length ≃ Fin k := hnodup.getEquivOfForallMemList l hall
  let c : Fin k ≃ Fin l.length := finCongr hlen.symm
  refine ⟨c.trans e₀, ?_⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · have hcij : c i < c j := by
      exact_mod_cast hij
    have hp := (Finset.pairwise_sort (Finset.univ : Finset (Fin k))
      r).rel_get_of_lt hcij
    change key (l.get (c i)) ≤ key (l.get (c j)) at hp
    change w (l.get (c i)) ≤ w (l.get (c j))
    by_contra hn
    have hlt : w (l.get (c j)) < w (l.get (c i)) := Nat.lt_of_not_ge hn
    have hkey : key (l.get (c j)) < key (l.get (c i)) := by
      exact Prod.Lex.left _ _ hlt
    exact (not_lt_of_ge hp) hkey

/-- A finite sumset of nonempty summands is nonempty. -/
theorem familySumset_nonempty {ℓ : ℕ} {S : Fin ℓ → Finset ℤ}
    (hS : ∀ i, (S i).Nonempty) : (familySumset S).Nonempty := by
  classical
  let f : Fin ℓ → ℤ := fun i ↦ (S i).min' (hS i)
  exact ⟨∑ i, f i, mem_familySumset_iff.mpr
    ⟨f, fun i ↦ Finset.min'_mem _ _, rfl⟩⟩

/-! ## Primitive integer sets -/

/-- `S` is not contained in an arithmetic progression with common difference
greater than one.  Indeed, containment in `a + dℤ` is equivalent to all
pairwise differences being divisible by `d`. -/
def Primitive (S : Finset ℤ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ x ∈ S, ∃ y ∈ S, ¬ (d : ℤ) ∣ x - y

/-- The literal negation of primitivity: all elements lie in one residue
class modulo some integer `d ≥ 2`. -/
theorem not_primitive_iff (S : Finset ℤ) :
    ¬ Primitive S ↔
      ∃ d : ℕ, 2 ≤ d ∧ ∀ x ∈ S, ∀ y ∈ S, (d : ℤ) ∣ x - y := by
  classical
  simp only [Primitive]
  push Not
  rfl

/-- Literal arithmetic-progression formulation of non-primitivity.  The
progression is the residue class `a + dℤ`. -/
theorem not_primitive_iff_exists_residue (S : Finset ℤ) :
    ¬ Primitive S ↔
      ∃ d : ℕ, 2 ≤ d ∧ ∃ a : ℤ, ∀ x ∈ S, (d : ℤ) ∣ x - a := by
  rw [not_primitive_iff]
  constructor
  · rintro ⟨d, hd, hpair⟩
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨d, hd, 0, by simp⟩
    · obtain ⟨a, ha⟩ := hS
      exact ⟨d, hd, a, fun x hx ↦ hpair x hx a ha⟩
  · rintro ⟨d, hd, a, ha⟩
    refine ⟨d, hd, ?_⟩
    intro x hx y hy
    obtain ⟨u, hu⟩ := ha x hx
    obtain ⟨v, hv⟩ := ha y hy
    refine ⟨u - v, ?_⟩
    rw [mul_sub, ← hu, ← hv]
    ring

/-- Primitivity is invariant under translation. -/
theorem primitive_image_add (S : Finset ℤ) (a : ℤ) :
    Primitive (S.image (fun x ↦ a + x)) ↔ Primitive S := by
  constructor <;> intro h d hd
  · obtain ⟨x, hx, y, hy, hxy⟩ := h d hd
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    refine ⟨x', hx', y', hy', ?_⟩
    simpa using hxy
  · obtain ⟨x, hx, y, hy, hxy⟩ := h d hd
    refine ⟨a + x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      a + y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    simpa using hxy

/-- A primitive set contains two distinct elements, hence is nonempty. -/
theorem Primitive.nonempty {S : Finset ℤ} (hS : Primitive S) : S.Nonempty := by
  obtain ⟨x, hx, y, hy, _⟩ := hS 2 (by omega)
  exact ⟨x, hx⟩

/-! ## Diameter and interval containment -/

/-- The integral diameter of a nonempty finite integer set. -/
def diameter (S : Finset ℤ) (hS : S.Nonempty) : ℕ :=
  (S.max' hS - S.min' hS).toNat

theorem min'_le_max' (S : Finset ℤ) (hS : S.Nonempty) :
    S.min' hS ≤ S.max' hS :=
  Finset.min'_le S _ (Finset.max'_mem S hS)

theorem diameter_eq_sub (S : Finset ℤ) (hS : S.Nonempty) :
    (diameter S hS : ℤ) = S.max' hS - S.min' hS := by
  rw [diameter, Int.toNat_of_nonneg]
  exact sub_nonneg.mpr (min'_le_max' S hS)

/-- The maximum of a nonempty integer sumset is the sum of the maxima. -/
theorem max'_add {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + B).max' (add_nonempty hA hB) = A.max' hA + B.max' hB := by
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add_iff.mp hz
    exact add_le_add (Finset.le_max' A a ha) (Finset.le_max' B b hb)
  · exact Finset.le_max' (A + B) _
      (add_mem_add (Finset.max'_mem A hA) (Finset.max'_mem B hB))

/-- The minimum of a nonempty integer sumset is the sum of the minima. -/
theorem min'_add {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + B).min' (add_nonempty hA hB) = A.min' hA + B.min' hB := by
  apply le_antisymm
  · exact Finset.min'_le (A + B) _
      (add_mem_add (Finset.min'_mem A hA) (Finset.min'_mem B hB))
  · apply Finset.le_min'
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add_iff.mp hz
    exact add_le_add (Finset.min'_le A a ha) (Finset.min'_le B b hb)

/-- Diameter is exactly additive under pointwise addition of nonempty
integer finsets. -/
theorem diameter_add {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    diameter (A + B) (add_nonempty hA hB) = diameter A hA + diameter B hB := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [diameter_eq_sub (A + B) (add_nonempty hA hB),
    diameter_eq_sub A hA, diameter_eq_sub B hB,
    max'_add hA hB, min'_add hA hB]
  ring

/-- The diameter of an iterated sumset is the sum of the diameters of its
nonempty summands. -/
theorem diameter_familySumset {ℓ : ℕ} (S : Fin ℓ → Finset ℤ)
    (hS : ∀ i, (S i).Nonempty) :
    diameter (familySumset S) (familySumset_nonempty hS) =
      ∑ i, diameter (S i) (hS i) := by
  induction ℓ with
  | zero => simp [familySumset, diameter]
  | succ ℓ ih =>
      have htail : ∀ i : Fin ℓ, (S i.succ).Nonempty := fun i ↦ hS i.succ
      calc
        diameter (familySumset S) (familySumset_nonempty hS) =
            diameter (S 0 + familySumset (fun i : Fin ℓ ↦ S i.succ))
              (add_nonempty (hS 0) (familySumset_nonempty htail)) := by
                congr 1
        _ = diameter (S 0) (hS 0) +
              diameter (familySumset (fun i : Fin ℓ ↦ S i.succ))
                (familySumset_nonempty htail) :=
          diameter_add (hS 0) (familySumset_nonempty htail)
        _ = ∑ i, diameter (S i) (hS i) := by
          rw [ih (fun i ↦ S i.succ) htail, Fin.sum_univ_succ]

/-- A nonempty integer set has at most one more point than its diameter. -/
theorem card_le_diameter_add_one (S : Finset ℤ) (hS : S.Nonempty) :
    S.card ≤ diameter S hS + 1 := by
  calc
    S.card ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card :=
      Finset.card_le_card (by
        intro x hx
        exact Finset.mem_Icc.mpr
          ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩)
    _ = diameter S hS + 1 := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [Int.card_Icc_of_le _ _ (by have := min'_le_max' S hS; omega),
        diameter_eq_sub]
      ring

/-- Cardinality supplies the elementary lower bound on diameter. -/
theorem card_sub_one_le_diameter {S : Finset ℤ} (hS : S.Nonempty)
    {n : ℕ} (hcard : n ≤ S.card) : n - 1 ≤ diameter S hS := by
  have := card_le_diameter_add_one S hS
  omega

/-- Translate a nonempty finite integer set so that its minimum is zero. -/
def translateToZero (S : Finset ℤ) (hS : S.Nonempty) : Finset ℤ :=
  S.image fun x ↦ x - S.min' hS

@[simp] theorem card_translateToZero (S : Finset ℤ) (hS : S.Nonempty) :
    (translateToZero S hS).card = S.card := by
  rw [translateToZero, Finset.card_image_iff.mpr]
  intro x _ y _ hxy
  exact sub_left_injective hxy

theorem translateToZero_subset_Icc (S : Finset ℤ) (hS : S.Nonempty) :
    translateToZero S hS ⊆ Finset.Icc 0 (diameter S hS : ℤ) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hymin := Finset.min'_le S y hy
  have hymax := Finset.le_max' S y hy
  rw [diameter_eq_sub]
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- Translation-invariant form of the dense two-sumset interval lemma. -/
theorem dense_two_sumset_interval {A B : Finset ℤ}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hDA : 0 < diameter A hA) (hDB : 0 < diameter B hB)
    (hdense : max (diameter A hA) (diameter B hB) ≤ A.card + B.card - 2) :
    ∃ d : ℤ,
      Finset.Icc d
          (d + (2 * (A.card + B.card - 2) - diameter A hA - diameter B hB : ℕ)) ⊆
        A + B := by
  let LA := diameter A hA
  let LB := diameter B hB
  let c := A.card + B.card - 2
  have hLA : LA ≤ c := (le_max_left LA LB).trans hdense
  have hLB : LB ≤ c := (le_max_right LA LB).trans hdense
  have hsum : LA + LB ≤ 2 * c := by omega
  have hbox := LevBox.dense_two_sumset_Icc hDA hDB
    (translateToZero_subset_Icc A hA) (translateToZero_subset_Icc B hB) (by
      simpa [LA, LB, c] using hdense)
  let d : ℤ := A.min' hA + B.min' hB + ((LA : ℤ) + (LB : ℤ) - (c : ℤ))
  refine ⟨d, ?_⟩
  intro x hx
  have hx' := Finset.mem_Icc.mp hx
  let y := x - (A.min' hA + B.min' hB)
  have hylo : (LA : ℤ) + (LB : ℤ) - (c : ℤ) ≤ y := by
    dsimp [d, y] at hx' ⊢
    omega
  have hyhi : y ≤ (c : ℤ) := by
    have hwidth :
        ((2 * c - LA - LB : ℕ) : ℤ) = 2 * (c : ℤ) - (LA : ℤ) - (LB : ℤ) := by
      omega
    dsimp [d, y] at hx' ⊢
    rw [hwidth] at hx'
    omega
  have hy : y ∈ translateToZero A hA + translateToZero B hB := by
    apply hbox
    exact Finset.mem_Icc.mpr ⟨by simpa [LA, LB, c] using hylo,
      by simpa [c] using hyhi⟩
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := mem_add_iff.mp hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha₀
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb₀
  apply mem_add_iff.mpr
  refine ⟨a, ha, b, hb, ?_⟩
  dsimp [y] at hab
  omega

/-- Once an interval is at least as long as the ambient width `q`, adding
further summands of cardinality at least `n` extends it by `n - 1` steps per
summand.  This is the iterated form of `LevExtension.interval_extension`. -/
theorem extend_family_interval {r q n m : ℕ} {T : Finset ℤ}
    (S : Fin r → Finset ℤ) (hn : 1 ≤ n)
    (hcard : ∀ i, n ≤ (S i).card)
    (hbound : ∀ i, ∃ c : ℤ, S i ⊆ Finset.Icc c (c + q))
    (hqm : q ≤ m) {a : ℤ}
    (hT : Finset.Icc a (a + m) ⊆ T) :
    ∃ d : ℤ,
      Finset.Icc d (d + (m + r * (n - 1) : ℕ)) ⊆ T + familySumset S := by
  induction r generalizing m T a with
  | zero =>
      refine ⟨a, ?_⟩
      intro x hx
      exact mem_add_iff.mpr ⟨x, hT (by simpa using hx), 0,
        by simp [familySumset], by simp⟩
  | succ r ih =>
      obtain ⟨c, hc⟩ := hbound 0
      obtain ⟨b, hb⟩ := LevExtension.interval_extension hn (hcard 0) hc hqm hT
      have hqm' : q ≤ m + (n - 1) := hqm.trans (Nat.le_add_right _ _)
      obtain ⟨d, hd⟩ := ih (fun i : Fin r ↦ S i.succ)
        (fun i ↦ hcard i.succ) (fun i ↦ hbound i.succ) hqm' hb
      refine ⟨d, ?_⟩
      simpa only [familySumset_succ, add_assoc, Nat.succ_eq_add_one,
        Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hd

/-- Even-indexed half of a family with twice as many summands. -/
def evenFamily {k : ℕ} (S : Fin (k + k) → Finset ℤ) : Fin k → Finset ℤ :=
  fun i ↦ S ⟨2 * i, by omega⟩

/-- Odd-indexed half of a family with twice as many summands. -/
def oddFamily {k : ℕ} (S : Fin (k + k) → Finset ℤ) : Fin k → Finset ℤ :=
  fun i ↦ S ⟨2 * i + 1, by omega⟩

private theorem base_growth_arithmetic {DE DO cE cO t : ℕ} (ht : 0 < t)
    (hEO : DE ≤ DO) (hgap : DO ≤ DE + 2 * t)
    (hgE : DE + t + 2 ≤ 2 * cE)
    (hgO : DO + t + 2 ≤ 2 * cO) :
    max DE DO ≤ cE + cO - 2 ∧
      2 * t ≤ 2 * (cE + cO - 2) - DE - DO := by
  constructor <;> omega

/-- Proposition 1(ii) of Lev, combined with the telescoped multiple-addition
bound, for a nondecreasing finite family. -/
theorem ordered_block_growth {k q n : ℕ} (T : Fin k → Finset ℤ)
    (hn : 3 ≤ n) (hT : ∀ i, (T i).Nonempty)
    (hcard : ∀ i, n ≤ (T i).card)
    (hprim : ∀ i, Primitive (T i))
    (hmono : ∀ ⦃i j : Fin k⦄, i ≤ j →
      diameter (T i) (hT i) ≤ diameter (T j) (hT j))
    (hupper : ∀ i, diameter (T i) (hT i) ≤ q)
    (hk : q - 1 ≤ k * (n - 2)) :
    diameter (familySumset T) (familySumset_nonempty hT) +
        k * (n - 1) + 2 ≤ 2 * (familySumset T).card := by
  let ell : ℕ → ℕ := fun i ↦
    if hi : i < k then diameter (T ⟨i, hi⟩) (hT ⟨i, hi⟩) else 0
  have hmonoEll : ∀ {i j}, i < k → j < k → i ≤ j → ell i ≤ ell j := by
    intro i j hi hj hij
    simp only [ell, dif_pos hi, dif_pos hj]
    exact hmono (by exact_mod_cast hij)
  have hlower : ∀ i < k, n - 1 ≤ ell i := by
    intro i hi
    simp only [ell, dif_pos hi]
    exact card_sub_one_le_diameter (hT ⟨i, hi⟩) (hcard ⟨i, hi⟩)
  have hupperEll : ∀ i < k, ell i ≤ q := by
    intro i hi
    simpa only [ell, dif_pos hi] using hupper ⟨i, hi⟩
  have hgrowth0 := LevNormalization.lev1997_ordered_growth_fin T
    (by omega : 2 ≤ n) hT hcard
    (fun i ↦ by simpa only [Primitive, LevNormalization.IntPrimitive] using hprim i)
    (fun {_ _} hij ↦ hmono hij.le)
  rw [listSumset_ofFn_eq_familySumset] at hgrowth0
  have hsumWeight :
      (∑ i : Fin k, min (LevNormalization.intDiameter (T i) (hT i))
          ((i.val + 1) * (n - 2) + 1)) =
        ∑ i ∈ Finset.range k,
          min (ell i) ((i + 1) * (n - 2) + 1) := by
    calc
      _ = ∑ i : Fin k,
          min (ell i.val) ((i.val + 1) * (n - 2) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ell, dif_pos i.isLt, diameter, LevNormalization.intDiameter]
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun i ↦ min (ell i) ((i + 1) * (n - 2) + 1)) k
  have hgrowth :
      1 + ∑ i ∈ Finset.range k,
        min (ell i) ((i + 1) * (n - 2) + 1) ≤ (familySumset T).card := by
    rwa [hsumWeight] at hgrowth0
  apply LevProposition.of_growth_bound ell hn hmonoEll hlower hupperEll hk
  · rw [diameter_familySumset T hT]
    apply le_of_eq
    calc
      (∑ i : Fin k, diameter (T i) (hT i)) =
          ∑ i : Fin k, ell i.val := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ell, dif_pos i.isLt]
      _ = ∑ i ∈ Finset.range k, ell i :=
        Fin.sum_univ_eq_sum_range ell k
  · exact hgrowth

/-- The final, purely arithmetic, two-block step in Lev's argument.  Each
alternating block has already acquired the cardinality lower bound supplied
by the multiple-addition theorem. -/
theorem base_interval_of_growth {k n : ℕ} (hk : 0 < k) (hn : 3 ≤ n)
    (S : Fin (k + k) → Finset ℤ)
    (hS : ∀ i, (S i).Nonempty)
    (hdiam : ∀ i, n - 1 ≤ diameter (S i) (hS i))
    (hEO :
      diameter (familySumset (evenFamily S))
          (familySumset_nonempty (fun i ↦ hS _)) ≤
        diameter (familySumset (oddFamily S))
          (familySumset_nonempty (fun i ↦ hS _)))
    (hgap :
      diameter (familySumset (oddFamily S))
          (familySumset_nonempty (fun i ↦ hS _)) ≤
        diameter (familySumset (evenFamily S))
          (familySumset_nonempty (fun i ↦ hS _)) + 2 * k * (n - 1))
    (hgE :
      diameter (familySumset (evenFamily S))
          (familySumset_nonempty (fun i ↦ hS _)) + k * (n - 1) + 2 ≤
        2 * (familySumset (evenFamily S)).card)
    (hgO :
      diameter (familySumset (oddFamily S))
          (familySumset_nonempty (fun i ↦ hS _)) + k * (n - 1) + 2 ≤
        2 * (familySumset (oddFamily S)).card) :
    ∃ d : ℤ, Finset.Icc d (d + (2 * k * (n - 1) : ℕ)) ⊆ familySumset S := by
  let E : Fin k → Finset ℤ := evenFamily S
  let O : Fin k → Finset ℤ := oddFamily S
  let hEnonempty : ∀ i, (E i).Nonempty := fun i ↦ hS _
  let hOnonempty : ∀ i, (O i).Nonempty := fun i ↦ hS _
  let SE := familySumset E
  let SO := familySumset O
  let hEne : SE.Nonempty := familySumset_nonempty hEnonempty
  let hOne : SO.Nonempty := familySumset_nonempty hOnonempty
  let DE := diameter SE hEne
  let DO := diameter SO hOne
  have hEO' : DE ≤ DO := by
    simpa only [E, O, SE, SO, DE, DO] using hEO
  have hgap' : DO ≤ DE + 2 * k * (n - 1) := by
    simpa only [E, O, SE, SO, DE, DO] using hgap
  have hgE' : DE + k * (n - 1) + 2 ≤ 2 * SE.card := by
    simpa only [E, SE, DE] using hgE
  have hgO' : DO + k * (n - 1) + 2 ≤ 2 * SO.card := by
    simpa only [O, SO, DO] using hgO
  let i0 : Fin k := ⟨0, hk⟩
  have hDEpos : 0 < DE := by
    rw [show DE = ∑ i, diameter (E i) (hEnonempty i) by
      exact diameter_familySumset E hEnonempty]
    have hi := hdiam (⟨2 * i0, by omega⟩ : Fin (k + k))
    have hi' : 0 < diameter (E i0) (hEnonempty i0) := by
      simpa only [E, evenFamily] using (lt_of_lt_of_le (by omega : 0 < n - 1) hi)
    have hsingle : diameter (E i0) (hEnonempty i0) ≤
        ∑ i, diameter (E i) (hEnonempty i) :=
      Finset.single_le_sum (f := fun i : Fin k ↦ diameter (E i) (hEnonempty i))
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ i0)
    exact hi'.trans_le hsingle
  have hDOpos : 0 < DO := by
    rw [show DO = ∑ i, diameter (O i) (hOnonempty i) by
      exact diameter_familySumset O hOnonempty]
    have hi := hdiam (⟨2 * i0 + 1, by omega⟩ : Fin (k + k))
    have hi' : 0 < diameter (O i0) (hOnonempty i0) := by
      simpa only [O, oddFamily] using (lt_of_lt_of_le (by omega : 0 < n - 1) hi)
    have hsingle : diameter (O i0) (hOnonempty i0) ≤
        ∑ i, diameter (O i) (hOnonempty i) :=
      Finset.single_le_sum (f := fun i : Fin k ↦ diameter (O i) (hOnonempty i))
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ i0)
    exact hi'.trans_le hsingle
  have ht : 0 < k * (n - 1) := Nat.mul_pos hk (by omega)
  have harith := base_growth_arithmetic ht hEO'
    (by simpa only [Nat.mul_assoc] using hgap') hgE' hgO'
  have hdense : max DE DO ≤ SE.card + SO.card - 2 := harith.1
  obtain ⟨d, hd⟩ := dense_two_sumset_interval hEne hOne hDEpos hDOpos hdense
  have hwidth : 2 * k * (n - 1) ≤
      2 * (SE.card + SO.card - 2) - DE - DO := by
    simpa only [Nat.mul_assoc] using harith.2
  refine ⟨d, ?_⟩
  rw [familySumset_even_add_odd]
  change Finset.Icc d (d + (2 * k * (n - 1) : ℕ)) ⊆ SE + SO
  change Finset.Icc d
      (d + (2 * (SE.card + SO.card - 2) - DE - DO : ℕ)) ⊆ SE + SO at hd
  intro x hx
  apply hd
  have hxI := Finset.mem_Icc.mp hx
  have hwidthZ : ((2 * k * (n - 1) : ℕ) : ℤ) ≤
      ((2 * (SE.card + SO.card - 2) - DE - DO : ℕ) : ℤ) := by
    exact_mod_cast hwidth
  refine Finset.mem_Icc.mpr ⟨hxI.1, ?_⟩
  exact hxI.2.trans (add_le_add_right hwidthZ d)

/-- The first `2k` summands of a diameter-ordered family already contain
the long interval needed to start the extension argument. -/
theorem ordered_base_interval {k q n : ℕ} (hkpos : 0 < k) (hn : 3 ≤ n)
    (B : Fin (k + k) → Finset ℤ)
    (hB : ∀ i, (B i).Nonempty)
    (hcard : ∀ i, n ≤ (B i).card)
    (hprim : ∀ i, Primitive (B i))
    (hmono : ∀ ⦃i j : Fin (k + k)⦄, i ≤ j →
      diameter (B i) (hB i) ≤ diameter (B j) (hB j))
    (hupper : ∀ i, diameter (B i) (hB i) ≤ q)
    (hk : q - 1 ≤ k * (n - 2)) :
    ∃ d : ℤ, Finset.Icc d (d + (2 * k * (n - 1) : ℕ)) ⊆ familySumset B := by
  let E := evenFamily B
  let O := oddFamily B
  have hE : ∀ i, (E i).Nonempty := fun i ↦ hB _
  have hO : ∀ i, (O i).Nonempty := fun i ↦ hB _
  have hdiam : ∀ i, n - 1 ≤ diameter (B i) (hB i) :=
    fun i ↦ card_sub_one_le_diameter (hB i) (hcard i)
  have hEO : diameter (familySumset E) (familySumset_nonempty hE) ≤
      diameter (familySumset O) (familySumset_nonempty hO) := by
    rw [diameter_familySumset E hE, diameter_familySumset O hO]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [E, O, evenFamily, oddFamily] using
      hmono (show (⟨2 * i, by omega⟩ : Fin (k + k)) ≤
        ⟨2 * i + 1, by omega⟩ by exact Fin.mk_le_mk.mpr (by omega))
  let w : ℕ → ℕ := fun i ↦
    if hi : i < 2 * k then diameter (B ⟨i, by omega⟩) (hB ⟨i, by omega⟩) else 0
  have hwmono : ∀ {i j}, i < 2 * k → j < 2 * k → i ≤ j → w i ≤ w j := by
    intro i j hi hj hij
    simp only [w, dif_pos hi, dif_pos hj]
    exact hmono (by exact_mod_cast hij)
  have hwupper : ∀ i < 2 * k, w i ≤ q := by
    intro i hi
    simpa only [w, dif_pos hi] using hupper ⟨i, by omega⟩
  have hodd := LevProposition.odd_sum_le_even_sum_add w hwmono hwupper
  have hevenSum : (∑ i : Fin k, diameter (E i) (hE i)) =
      ∑ i ∈ Finset.range k, w (2 * i) := by
    calc
      _ = ∑ i : Fin k, w (2 * i.val) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [E, evenFamily, w, dif_pos (by omega : 2 * i.val < 2 * k)]
      _ = _ := Fin.sum_univ_eq_sum_range (fun i ↦ w (2 * i)) k
  have hoddSum : (∑ i : Fin k, diameter (O i) (hO i)) =
      ∑ i ∈ Finset.range k, w (2 * i + 1) := by
    calc
      _ = ∑ i : Fin k, w (2 * i.val + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [O, oddFamily, w, dif_pos (by omega : 2 * i.val + 1 < 2 * k)]
      _ = _ := Fin.sum_univ_eq_sum_range (fun i ↦ w (2 * i + 1)) k
  have hq : q ≤ 2 * k * (n - 1) := by
    calc
      q ≤ k * (n - 2) + 1 := by omega
      _ ≤ k * (n - 1) + k * (n - 1) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left k (by omega)
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
            (Nat.ne_of_gt hkpos) (by omega))
      _ = 2 * k * (n - 1) := by ring
  have hgap : diameter (familySumset O) (familySumset_nonempty hO) ≤
      diameter (familySumset E) (familySumset_nonempty hE) + 2 * k * (n - 1) := by
    rw [diameter_familySumset E hE, diameter_familySumset O hO,
      hevenSum, hoddSum]
    exact hodd.trans (Nat.add_le_add_left hq _)
  have hgE := ordered_block_growth E hn hE (fun i ↦ hcard _)
    (fun i ↦ hprim _) (fun {i j} hij ↦ hmono (by
      exact Fin.mk_le_mk.mpr (by omega)))
    (fun i ↦ hupper _) hk
  have hgO := ordered_block_growth O hn hO (fun i ↦ hcard _)
    (fun i ↦ hprim _) (fun {i j} hij ↦ hmono (by
      exact Fin.mk_le_mk.mpr (by omega)))
    (fun i ↦ hupper _) hk
  exact base_interval_of_growth hkpos hn B hB hdiam
    (by simpa only [E, O] using hEO)
    (by simpa only [E, O] using hgap)
    (by simpa only [E] using hgE) (by simpa only [O] using hgO)

/-- Every nonempty finite integer set lies between its extrema. -/
theorem subset_Icc_min'_max' (S : Finset ℤ) (hS : S.Nonempty) :
    S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := by
  intro x hx
  exact Finset.mem_Icc.mpr ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩

/-- A set contained in an interval of `q + 1` integers has diameter at most
`q`. -/
theorem diameter_le_of_subset_Icc {S : Finset ℤ} (hS : S.Nonempty)
    {a : ℤ} {q : ℕ} (hsub : S ⊆ Finset.Icc a (a + q)) :
    diameter S hS ≤ q := by
  have hmin := Finset.mem_Icc.mp (hsub (Finset.min'_mem S hS))
  have hmax := Finset.mem_Icc.mp (hsub (Finset.max'_mem S hS))
  have hz : S.max' hS - S.min' hS ≤ (q : ℤ) := by omega
  rw [← Int.ofNat_le, diameter_eq_sub]
  exact hz

/-- Exact cardinality of an integer interval specified by its number of
steps. -/
@[simp] theorem card_Icc_add_nat (a : ℤ) (m : ℕ) :
    (Finset.Icc a (a + m)).card = m + 1 := by
  rw [Int.card_Icc]
  have h : a + (m : ℤ) + 1 - a = ((m + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h]
  norm_num

/-- Translation of an integral interval. -/
theorem image_add_Icc (c a b : ℤ) :
    (Finset.Icc a b).image (fun x ↦ c + x) =
      Finset.Icc (c + a) (c + b) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨x - c, ⟨by omega, by omega⟩, by omega⟩

/-- Translating every summand translates the family sumset by the sum of
the translation parameters. -/
theorem familySumset_image_add {ℓ : ℕ} (S : Fin ℓ → Finset ℤ)
    (a : Fin ℓ → ℤ) :
    familySumset (fun i ↦ (S i).image (fun x ↦ a i + x)) =
      (familySumset S).image (fun x ↦ (∑ i, a i) + x) := by
  classical
  induction ℓ with
  | zero => simp [familySumset]
  | succ ℓ ih =>
      rw [familySumset_succ, familySumset_succ]
      rw [ih]
      simp only [Fin.sum_univ_succ]
      ext z
      simp only [Finset.mem_add, Finset.mem_image]
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨u + v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
        abel
      · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
        refine ⟨a 0 + u, ⟨u, hu, rfl⟩,
          (∑ i : Fin ℓ, a i.succ) + v, ⟨v, hv, rfl⟩, ?_⟩
        abel

/-- A homomorphism `x ↦ v*x` commutes with a finite family sumset. -/
theorem familySumset_image_mul {ℓ : ℕ} (S : Fin ℓ → Finset ℤ) (v : ℤ) :
    familySumset (fun i ↦ (S i).image (fun x ↦ v * x)) =
      (familySumset S).image (fun x ↦ v * x) := by
  classical
  induction ℓ with
  | zero => simp [familySumset]
  | succ ℓ ih =>
      rw [familySumset_succ, familySumset_succ, ih]
      ext z
      simp only [Finset.mem_add, Finset.mem_image]
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨u + w, ⟨u, hu, w, hw, rfl⟩, by ring⟩
      · rintro ⟨w, ⟨u, hu, y, hy, rfl⟩, rfl⟩
        exact ⟨v * u, ⟨u, hu, rfl⟩, v * y, ⟨y, hy, rfl⟩, by ring⟩

/-- Simultaneous affine normalization of all summands. -/
theorem familySumset_image_affine {ℓ : ℕ} (S : Fin ℓ → Finset ℤ)
    (a : Fin ℓ → ℤ) (v : ℤ) :
    familySumset (fun i ↦ (S i).image (fun x ↦ a i + v * x)) =
      (familySumset S).image (fun x ↦ (∑ i, a i) + v * x) := by
  rw [show (fun i ↦ (S i).image (fun x ↦ a i + v * x)) =
      (fun i ↦ ((S i).image (fun x ↦ v * x)).image (fun x ↦ a i + x)) by
    funext i
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨v * y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩]
  rw [familySumset_image_add, familySumset_image_mul]
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨v * z, ⟨z, hz, rfl⟩, rfl⟩

/-! ## Lev's theorem (CFP Lemma 2.10) -/

/-- The exact finite formulation of Lev's one-dimensional theorem used as
Conlon--Fox--Pham Lemma 2.10.  It is packaged as a proposition while the
proof is assembled from the multiple-addition and dense-two-sum lemmas
below; the eventual theorem has this literal type. -/
def LevIntervalStatement : Prop :=
  ∀ {ℓ q n : ℕ}, 1 ≤ ℓ → 1 ≤ q → 3 ≤ n →
    2 * ((q - 1 + (n - 2) - 1) / (n - 2)) ≤ ℓ →
    ∀ S : Fin ℓ → Finset ℤ,
      (∀ i, n ≤ (S i).card) →
      (∀ i, ∃ a : ℤ, S i ⊆ Finset.Icc a (a + q)) →
      (∀ i, Primitive (S i)) →
      ∃ a : ℤ, Finset.Icc a (a + (ℓ * (n - 1) : ℕ)) ⊆ familySumset S

/-- Lev's one-dimensional interval theorem, in the exact form used as
Conlon--Fox--Pham Lemma 2.10. -/
theorem lev_interval : LevIntervalStatement := by
  intro ℓ q n hℓ hq hn hlarge S hcard hbound hprim
  by_cases hq1 : q = 1
  · let i0 : Fin ℓ := ⟨0, hℓ⟩
    obtain ⟨a, ha⟩ := hbound i0
    have hsmall : (S i0).card ≤ 2 := by
      calc
        (S i0).card ≤ (Finset.Icc a (a + q)).card := Finset.card_le_card ha
        _ = q + 1 := card_Icc_add_nat a q
        _ = 2 := by omega
    have := hcard i0
    omega
  have hq2 : 2 ≤ q := by omega
  have hden : 0 < n - 2 := by omega
  let k := (q - 1 + (n - 2) - 1) / (n - 2)
  have hk : q - 1 ≤ k * (n - 2) := by
    have hc : q - 1 ≤ (n - 2) * ((q - 1) ⌈/⌉ (n - 2)) :=
      le_smul_ceilDiv hden
    simpa only [Nat.ceilDiv_eq_add_pred_div, k, Nat.mul_comm] using hc
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0] at hk
    simp only [zero_mul] at hk
    omega
  have h2k : k + k ≤ ℓ := by simpa [two_mul] using hlarge
  let wt : Fin ℓ → ℕ := fun i ↦ diameter (S i) (hprim i).nonempty
  obtain ⟨e, he⟩ := exists_monotone_reindex wt
  let R : Fin ℓ → Finset ℤ := fun i ↦ S (e i)
  have hR : ∀ i, (R i).Nonempty := fun i ↦ (hprim (e i)).nonempty
  have hRcard : ∀ i, n ≤ (R i).card := fun i ↦ hcard (e i)
  have hRbound : ∀ i, ∃ a : ℤ, R i ⊆ Finset.Icc a (a + q) :=
    fun i ↦ hbound (e i)
  have hRprim : ∀ i, Primitive (R i) := fun i ↦ hprim (e i)
  have hRmono : ∀ ⦃i j : Fin ℓ⦄, i ≤ j →
      diameter (R i) (hR i) ≤ diameter (R j) (hR j) := by
    intro i j hij
    simpa only [wt, R] using he hij
  let r := ℓ - (k + k)
  have hlen : k + k + r = ℓ := by
    dsimp [r]
    omega
  let f : Fin (k + k + r) ≃ Fin ℓ := finCongr hlen
  let U : Fin (k + k + r) → Finset ℤ := fun i ↦ R (f i)
  have hU : ∀ i, (U i).Nonempty := fun i ↦ hR (f i)
  have hUcard : ∀ i, n ≤ (U i).card := fun i ↦ hRcard (f i)
  have hUbound : ∀ i, ∃ a : ℤ, U i ⊆ Finset.Icc a (a + q) :=
    fun i ↦ hRbound (f i)
  have hUprim : ∀ i, Primitive (U i) := fun i ↦ hRprim (f i)
  have hUmono : ∀ ⦃i j : Fin (k + k + r)⦄, i ≤ j →
      diameter (U i) (hU i) ≤ diameter (U j) (hU j) := by
    intro i j hij
    apply hRmono
    apply Fin.mk_le_mk.mpr
    change i.val ≤ j.val
    exact hij
  let B : Fin (k + k) → Finset ℤ := fun i ↦ U (Fin.castAdd r i)
  let Tail : Fin r → Finset ℤ := fun i ↦ U (Fin.natAdd (k + k) i)
  have hB : ∀ i, (B i).Nonempty := fun i ↦ hU _
  have hBcard : ∀ i, n ≤ (B i).card := fun i ↦ hUcard _
  have hBprim : ∀ i, Primitive (B i) := fun i ↦ hUprim _
  have hBmono : ∀ ⦃i j : Fin (k + k)⦄, i ≤ j →
      diameter (B i) (hB i) ≤ diameter (B j) (hB j) := by
    intro i j hij
    apply hUmono
    exact Fin.mk_le_mk.mpr hij
  have hBupper : ∀ i, diameter (B i) (hB i) ≤ q := by
    intro i
    obtain ⟨a, ha⟩ := hUbound (Fin.castAdd r i)
    exact diameter_le_of_subset_Icc (hB i) ha
  obtain ⟨a, ha⟩ := ordered_base_interval hkpos hn B hB hBcard hBprim
    hBmono hBupper hk
  have hTailCard : ∀ i, n ≤ (Tail i).card := fun i ↦ hUcard _
  have hTailBound : ∀ i, ∃ c : ℤ, Tail i ⊆ Finset.Icc c (c + q) :=
    fun i ↦ hUbound _
  have hqm : q ≤ 2 * k * (n - 1) := by
    calc
      q ≤ k * (n - 2) + 1 := by omega
      _ ≤ k * (n - 1) + k * (n - 1) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left k (by omega)
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
            (Nat.ne_of_gt hkpos) (by omega))
      _ = 2 * k * (n - 1) := by ring
  obtain ⟨d, hd⟩ := extend_family_interval Tail (by omega : 1 ≤ n)
    hTailCard hTailBound hqm ha
  have happ : Fin.append B Tail = U := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [B, Tail, Fin.append_left]
    · simp only [B, Tail, Fin.append_right]
  have hsum : familySumset B + familySumset Tail = familySumset S := by
    calc
      familySumset B + familySumset Tail = familySumset (Fin.append B Tail) :=
        (familySumset_append B Tail).symm
      _ = familySumset U := by rw [happ]
      _ = familySumset R := familySumset_equiv f R
      _ = familySumset S := familySumset_equiv e S
  have hwidth : 2 * k * (n - 1) + r * (n - 1) = ℓ * (n - 1) := by
    rw [← hlen]
    ring
  refine ⟨d, ?_⟩
  rw [← hsum]
  intro x hx
  apply hd
  simpa only [hwidth] using hx

/-! ## Affine form (the structural content of CFP Lemma 2.11) -/

/-- Affine-image transport of an interval conclusion.  After the sets have been
normalized inside the primitive lattice `ℤ`, their original sum contains a
translate of `v · [0, ℓ(n-1)]`.  This is the exact algebraic step used in
CFP Lemma 2.11; its remaining displayed constants merely verify the
hypothesis `hlarge`. -/
theorem affine_interval_of_interval {ℓ n : ℕ}
    (S : Fin ℓ → Finset ℤ) (a : Fin ℓ → ℤ) (v b : ℤ)
    (hb : Finset.Icc b (b + (ℓ * (n - 1) : ℕ)) ⊆ familySumset S) :
    ∃ c : ℤ,
      (Finset.Icc (0 : ℤ) ((ℓ * (n - 1) : ℕ) : ℤ)).image
          (fun j ↦ c + v * j) ⊆
        familySumset (fun i ↦ (S i).image (fun x ↦ a i + v * x)) := by
  refine ⟨(∑ i, a i) + v * b, ?_⟩
  rw [familySumset_image_affine]
  intro z hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  apply Finset.mem_image.mpr
  refine ⟨b + j, hb ?_, ?_⟩
  · have hj' := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · ring

/-- Affine version of `lev_interval`, corresponding to the one-dimensional
content of CFP Lemma 2.11.  Each primitive normalized summand is transported
back to a common lattice of step `v`. -/
theorem lev_affine_interval {ℓ q n : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q) (hn : 3 ≤ n)
    (hlarge : 2 * ((q - 1 + (n - 2) - 1) / (n - 2)) ≤ ℓ)
    (S : Fin ℓ → Finset ℤ)
    (hcard : ∀ i, n ≤ (S i).card)
    (hbound : ∀ i, ∃ b : ℤ, S i ⊆ Finset.Icc b (b + q))
    (hprim : ∀ i, Primitive (S i))
    (a : Fin ℓ → ℤ) (v : ℤ) :
    ∃ c : ℤ,
      (Finset.Icc (0 : ℤ) ((ℓ * (n - 1) : ℕ) : ℤ)).image
          (fun j ↦ c + v * j) ⊆
        familySumset (fun i ↦ (S i).image (fun x ↦ a i + v * x)) := by
  obtain ⟨b, hb⟩ := lev_interval hℓ hq hn hlarge S hcard hbound hprim
  exact affine_interval_of_interval S a v b hb

end Erdos186.CFP.Lev
