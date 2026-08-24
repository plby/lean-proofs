/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1180.
https://www.erdosproblems.com/forum/thread/1180

Informal authors:
- A. A. Glibichuk

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1180.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin

/-!
# Erdős Problem 1180

For every `ε > 0`, the inverses modulo a prime `p` of the positive integers
at most `p ^ ε` form an additive basis of `ZMod p` of order bounded only in
terms of `ε`.

The proof follows Glibichuk's 2006 solution.  See `tex/1180.tex` for the
detailed mathematical proof and the correspondence between its lemmas and
the declarations below.
-/

open scoped BigOperators Pointwise Combinatorics.Additive
open Finset

namespace Erdos1180

/-- A positive integer whose residue modulo `p` is invertible and whose real
size is at most `p ^ ε`. -/
def AdmissibleDenom (ε : ℝ) (p n : ℕ) : Prop :=
  0 < n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ Nat.Coprime n p

/-- A list of natural-number denominators represents a residue as a sum of
their modular inverses. -/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (xs : List ℕ) : Prop :=
  (∀ n ∈ xs, AdmissibleDenom ε p n) ∧
    (List.map (fun n : ℕ ↦ ((n : ZMod p)⁻¹)) xs).sum = a

/-- The exact affirmative formulation of Erdős Problem 1180. -/
def Erdos1180Claim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ xs : List ℕ, xs.length ≤ C ∧ Represents ε p a xs

section Elementary

lemma int_eq_zero_of_dvd_of_abs_lt {p : ℕ} {z : ℤ} (hp : 0 < p)
    (hdvd : (p : ℤ) ∣ z) (habs : |z| < p) : z = 0 := by
  obtain ⟨t, rfl⟩ := hdvd
  rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg p)] at habs
  have : |t| < 1 := by
    rw [← Int.mul_lt_mul_left (show (0 : ℤ) < p by exact_mod_cast hp)]
    simpa [mul_comm] using habs
  have ht : t = 0 := by
    have := (abs_lt.mp this)
    omega
  simp [ht]

end Elementary

section Glibichuk

variable {p : ℕ} [NeZero p]

/-- The image of `X × Y` under `(x,y) ↦ x + ξy`. -/
noncomputable def affineImage (ξ : ZMod p) (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  (X ×ˢ Y).image fun z ↦ z.1 + ξ * z.2

/-- The number of ordered pairs of pairs in `X × Y` with equal image under
`(x,y) ↦ x + ξy`. -/
noncomputable def affineEnergy (ξ : ZMod p) (X Y : Finset (ZMod p)) : ℕ :=
  #{z ∈ (X ×ˢ Y) ×ˢ (X ×ˢ Y) |
    z.1.1 + ξ * z.1.2 = z.2.1 + ξ * z.2.2}

lemma affineEnergy_eq_sum_sq (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    affineEnergy ξ X Y =
      ∑ a ∈ affineImage ξ X Y,
        #{z ∈ X ×ˢ Y | z.1 + ξ * z.2 = a} ^ 2 := by
  classical
  simp_rw [affineEnergy, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add simp [affineImage])

lemma card_sq_le_card_affineImage_mul_energy (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    (X.card * Y.card) ^ 2 ≤ (affineImage ξ X Y).card * affineEnergy ξ X Y := by
  classical
  let D := X ×ˢ Y
  let f : ZMod p × ZMod p → ZMod p := fun z ↦ z.1 + ξ * z.2
  calc
    (X.card * Y.card) ^ 2 = (∑ a ∈ affineImage ξ X Y, #{z ∈ D | f z = a}) ^ 2 := by
      rw [← card_product]
      congr 1
      rw [sum_card_fiberwise_eq_card_filter]
      rw [filter_eq_self.2]
      intro z hz
      exact mem_image.mpr ⟨z, hz, rfl⟩
    _ ≤ (affineImage ξ X Y).card *
          ∑ a ∈ affineImage ξ X Y, #{z ∈ D | f z = a} ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ)
        (affineImage ξ X Y) 1 (fun a ↦ #{z ∈ D | f z = a})
    _ = (affineImage ξ X Y).card * affineEnergy ξ X Y := by
      rw [affineEnergy_eq_sum_sq]

noncomputable def nonzeroScalars (p : ℕ) [NeZero p] : Finset (ZMod p) := univ.erase 0

@[simp] lemma card_nonzeroScalars (hp : p.Prime) : (nonzeroScalars p).card = p - 1 := by
  classical
  rw [nonzeroScalars, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]

lemma sum_card_filter_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop) [DecidableRel P] :
    ∑ a ∈ s, #(t.filter (P a)) = #((s ×ˢ t).filter fun z ↦ P z.1 z.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [sum_insert ha, show insert a s = {a} ∪ s by simp, union_product]
      rw [filter_union, card_union_of_disjoint]
      · have hmap :
            (t.filter (P a)).map ⟨Prod.mk a, Prod.mk_right_injective a⟩ =
              (({a} ×ˢ t).filter fun z ↦ P z.1 z.2) := by
          ext ⟨x, y⟩
          simp
          constructor
          · rintro ⟨⟨hy, hP⟩, hax⟩
            subst x
            exact ⟨⟨hy, rfl⟩, hP⟩
          · rintro ⟨⟨hy, hax⟩, hP⟩
            subst x
            exact ⟨⟨hy, hP⟩, rfl⟩
        rw [ih, ← hmap, card_map]
      · rw [disjoint_left]
        intro z hz₁ hz₂
        simp only [mem_filter, mem_product, mem_singleton] at hz₁ hz₂
        exact ha (hz₁.1.1 ▸ hz₂.1.1)

lemma sum_affineEnergy_eq_card (X Y : Finset (ZMod p)) :
    ∑ ξ ∈ nonzeroScalars p, affineEnergy ξ X Y =
      #{w ∈ nonzeroScalars p ×ˢ ((X ×ˢ Y) ×ˢ (X ×ˢ Y)) |
        w.2.1.1 + w.1 * w.2.1.2 = w.2.2.1 + w.1 * w.2.2.2} := by
  classical
  unfold affineEnergy
  exact sum_card_filter_product (nonzeroScalars p) ((X ×ˢ Y) ×ˢ (X ×ˢ Y))
    (fun ξ (w : (ZMod p × ZMod p) × (ZMod p × ZMod p)) ↦
      w.1.1 + ξ * w.1.2 = w.2.1 + ξ * w.2.2)

lemma scalar_eq_of_affine_eq_of_ne (hp : p.Prime) {ξ η : ZMod p}
    {u v : ZMod p × ZMod p} (huv : u ≠ v)
    (hξ : u.1 + ξ * u.2 = v.1 + ξ * v.2)
    (hη : u.1 + η * u.2 = v.1 + η * v.2) : ξ = η := by
  letI : Fact p.Prime := ⟨hp⟩
  have hy : u.2 ≠ v.2 := by
    intro hy
    apply huv
    apply Prod.ext
    · rw [hy] at hξ
      exact add_right_cancel hξ
    · exact hy
  have hmul : (ξ - η) * (u.2 - v.2) = 0 := by
    linear_combination hξ - hη
  rcases mul_eq_zero.mp hmul with h | h
  · exact sub_eq_zero.mp h
  · exact (hy (sub_eq_zero.mp h)).elim

lemma sum_affineEnergy_le (hp : p.Prime) (X Y : Finset (ZMod p)) :
    ∑ ξ ∈ nonzeroScalars p, affineEnergy ξ X Y ≤
      (nonzeroScalars p).card * (X.card * Y.card) + (X.card * Y.card) ^ 2 := by
  classical
  let D := X ×ˢ Y
  let U := nonzeroScalars p ×ˢ (D ×ˢ D)
  let C := U.filter fun w ↦
    w.2.1.1 + w.1 * w.2.1.2 = w.2.2.1 + w.1 * w.2.2.2
  let Cdiag := C.filter fun w ↦ w.2.1 = w.2.2
  let Coff := C.filter fun w ↦ w.2.1 ≠ w.2.2
  have hsum : ∑ ξ ∈ nonzeroScalars p, affineEnergy ξ X Y = C.card := by
    simpa [C, U, D] using sum_affineEnergy_eq_card (p := p) X Y
  have hsplit : Cdiag.card + Coff.card = C.card := by
    simpa [Cdiag, Coff] using
      card_filter_add_card_filter_not (s := C) (fun w ↦ w.2.1 = w.2.2)
  have hdiag : Cdiag.card ≤ (nonzeroScalars p ×ˢ D).card := by
    refine card_le_card_of_injOn (fun w ↦ (w.1, w.2.1)) ?_ ?_
    · intro w hw
      change w ∈ Cdiag at hw
      simp only [Cdiag, mem_filter] at hw
      have hwU : w ∈ U := (mem_filter.mp hw.1).1
      exact mem_product.mpr ⟨(mem_product.mp hwU).1, (mem_product.mp (mem_product.mp hwU).2).1⟩
    · intro w hw w' hw' heq
      change w ∈ Cdiag at hw
      change w' ∈ Cdiag at hw'
      simp only [Cdiag, mem_filter] at hw hw'
      have hξ : w.1 = w'.1 := congrArg (fun z ↦ z.1) heq
      have hu : w.2.1 = w'.2.1 := congrArg (fun z ↦ z.2) heq
      have hv : w.2.2 = w'.2.2 := by
        calc
          w.2.2 = w.2.1 := hw.2.symm
          _ = w'.2.1 := hu
          _ = w'.2.2 := hw'.2
      exact Prod.ext hξ (Prod.ext hu hv)
  have hoff : Coff.card ≤ (D ×ˢ D).card := by
    refine card_le_card_of_injOn (fun w ↦ w.2) ?_ ?_
    · intro w hw
      change w ∈ Coff at hw
      simp only [Coff, mem_filter] at hw
      exact (mem_product.mp (mem_filter.mp hw.1).1).2
    · intro w hw w' hw' heq
      change w ∈ Coff at hw
      change w' ∈ Coff at hw'
      simp only [Coff, mem_filter] at hw hw'
      have hξ : w.1 = w'.1 := by
        apply scalar_eq_of_affine_eq_of_ne hp hw.2
        · exact (mem_filter.mp hw.1).2
        · simpa [heq] using (mem_filter.mp hw'.1).2
      exact Prod.ext hξ heq
  rw [hsum, ← hsplit]
  calc
    Cdiag.card + Coff.card ≤
        (nonzeroScalars p ×ˢ D).card + (D ×ˢ D).card := Nat.add_le_add hdiag hoff
    _ = (nonzeroScalars p).card * (X.card * Y.card) +
          (X.card * Y.card) ^ 2 := by simp [D, pow_two]

lemma exists_good_scalar (hp : p.Prime) (X Y : Finset (ZMod p)) :
    ∃ ξ ∈ nonzeroScalars p,
      (affineEnergy ξ X Y : ℚ) ≤
        (X.card * Y.card : ℚ) +
          (X.card * Y.card : ℚ) ^ 2 / (nonzeroScalars p).card := by
  classical
  have hGpos : 0 < (nonzeroScalars p).card := by
    rw [card_nonzeroScalars hp]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hnat := sum_affineEnergy_le (p := p) hp X Y
  have hcast :
      (∑ ξ ∈ nonzeroScalars p, (affineEnergy ξ X Y : ℚ)) ≤
        ((nonzeroScalars p).card : ℚ) * (X.card * Y.card : ℚ) +
          (X.card * Y.card : ℚ) ^ 2 := by
    exact_mod_cast hnat
  have hsum :
      (∑ ξ ∈ nonzeroScalars p, (affineEnergy ξ X Y : ℚ)) ≤
        ∑ ξ ∈ nonzeroScalars p,
          ((X.card * Y.card : ℚ) +
            (X.card * Y.card : ℚ) ^ 2 / (nonzeroScalars p).card) := by
    calc
      _ ≤ ((nonzeroScalars p).card : ℚ) * (X.card * Y.card : ℚ) +
            (X.card * Y.card : ℚ) ^ 2 := hcast
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul]
        field_simp [Nat.ne_of_gt hGpos]
  exact exists_le_of_sum_le (card_pos.mp hGpos) hsum

/-- Swapping the two `Y`-coordinates changes the slope from `ξ` to `-ξ`
without changing the collision count. -/
lemma affineEnergy_neg (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    affineEnergy (-ξ) X Y = affineEnergy ξ X Y := by
  classical
  let swapY : ((ZMod p × ZMod p) × (ZMod p × ZMod p)) →
      ((ZMod p × ZMod p) × (ZMod p × ZMod p)) := fun w ↦
    ((w.1.1, w.2.2), (w.2.1, w.1.2))
  have hinv : Function.Involutive swapY := by
    intro w
    rcases w with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    rfl
  unfold affineEnergy
  apply card_bijective swapY hinv.bijective
  rintro ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩, h⟩
    refine ⟨⟨⟨hx₁, hy₂⟩, ⟨hx₂, hy₁⟩⟩, ?_⟩
    dsimp [swapY]
    linear_combination h
  · rintro ⟨⟨⟨hx₁, hy₂⟩, ⟨hx₂, hy₁⟩⟩, h⟩
    refine ⟨⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩, ?_⟩
    dsimp [swapY] at h
    linear_combination h

lemma card_affineImage_large_of_good_energy (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (ξ : ZMod p) (hprod : p < X.card * Y.card)
    (henergy : (affineEnergy ξ X Y : ℚ) ≤
      (X.card * Y.card : ℚ) +
        (X.card * Y.card : ℚ) ^ 2 / (nonzeroScalars p).card) :
    p < 2 * (affineImage ξ X Y).card := by
  classical
  let q : ℚ := X.card * Y.card
  let s : ℚ := (affineImage ξ X Y).card
  let e : ℚ := affineEnergy ξ X Y
  let r : ℚ := ((p - 1 : ℕ) : ℚ)
  rw [card_nonzeroScalars hp] at henergy
  have hrposN : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hrpos : (0 : ℚ) < r := by
    dsimp [r]
    exact_mod_cast hrposN
  have hrEq : r = (p : ℚ) - 1 := by
    dsimp [r]
    rw [Nat.cast_sub hp.one_lt.le]
    norm_num
  have hqpos : (0 : ℚ) < q := by
    dsimp [q]
    exact_mod_cast (lt_trans hp.pos hprod)
  have hpq : (p : ℚ) < q := by
    dsimp [q]
    exact_mod_cast hprod
  have hcauchy : q ^ 2 ≤ s * e := by
    dsimp [q, s, e]
    exact_mod_cast card_sq_le_card_affineImage_mul_energy (p := p) ξ X Y
  by_contra hlarge
  have hsNat : 2 * (affineImage ξ X Y).card ≤ p := Nat.le_of_not_gt hlarge
  have hpne2 : p ≠ 2 := by omega
  have hpnotEven : ¬ Even p := by
    rw [hp.even_iff]
    exact hpne2
  have hslt : 2 * (affineImage ξ X Y).card < p := by
    apply lt_of_le_of_ne hsNat
    intro heq
    apply hpnotEven
    exact ⟨(affineImage ξ X Y).card, by omega⟩
  have hsNat' : 2 * (affineImage ξ X Y).card ≤ p - 1 := by omega
  have hs : 2 * s ≤ r := by
    dsimp [s, r]
    exact_mod_cast hsNat'
  have he0 : 0 ≤ e := by positivity
  have hc2 : 2 * q ^ 2 ≤ r * e := by
    have h₁ := mul_le_mul_of_nonneg_left hcauchy (show (0 : ℚ) ≤ 2 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right hs he0
    nlinarith
  have hemul : e * r ≤ q * r + q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right henergy (le_of_lt hrpos)
    dsimp [q, e, r] at h ⊢
    field_simp [ne_of_gt hrpos] at h
    simpa [pow_two, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  nlinarith [hrEq]

lemma exists_opposite_large_affineImages (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (hprod : p < X.card * Y.card) :
    ∃ ξ ∈ nonzeroScalars p,
      p < 2 * (affineImage ξ X Y).card ∧
      p < 2 * (affineImage (-ξ) X Y).card := by
  obtain ⟨ξ, hξ, henergy⟩ := exists_good_scalar (p := p) hp X Y
  refine ⟨ξ, hξ, card_affineImage_large_of_good_energy hp hp2 X Y ξ hprod henergy, ?_⟩
  apply card_affineImage_large_of_good_energy hp hp2 X Y (-ξ) hprod
  simpa [affineEnergy_neg] using henergy

/-- No element of an antisymmetric set occurs together with its negative. -/
def IsAntisymmetric (Y : Finset (ZMod p)) : Prop :=
  ∀ y ∈ Y, -y ∉ Y

/-- Four sums of products from `X · Y`. -/
noncomputable def fourfoldProductSum (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  let P := X * Y
  (P + P) + (P + P)

/-- Eight sums of products from `X · Y`. -/
noncomputable def eightfoldProductSum (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  fourfoldProductSum X Y + fourfoldProductSum X Y

lemma inter_negImage_nonempty_of_card_large (hp : p.Prime)
    (A : Finset (ZMod p)) (hA : p < 2 * A.card) :
    (A ∩ A.image fun z ↦ -z).Nonempty := by
  classical
  by_contra hne
  have hd : Disjoint A (A.image fun z ↦ -z) := by
    by_contra hnd
    exact hne (not_disjoint_iff_nonempty_inter.mp hnd)
  have hcardImage : (A.image fun z ↦ -z).card = A.card :=
    card_image_iff.mpr neg_injective.injOn
  have hle : (A ∪ A.image fun z ↦ -z).card ≤ p := by
    calc
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := ZMod.card p
  have hsplit := card_union_of_disjoint hd
  omega

/-- Glibichuk's finite-field covering lemma in the exact eight-summand form. -/
theorem glibichuk_cover (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (hprod : p < X.card * Y.card)
    (hanti : IsAntisymmetric Y) :
    eightfoldProductSum X Y = univ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ξ, hξ, hplus, hminus⟩ :=
    exists_opposite_large_affineImages (p := p) hp hp2 X Y hprod
  obtain ⟨z, hz⟩ :=
    inter_negImage_nonempty_of_card_large (p := p) hp (affineImage ξ X Y) hplus
  have hz₁ : z ∈ affineImage ξ X Y := (mem_inter.mp hz).1
  obtain ⟨z', hz₂, hzz'⟩ := mem_image.mp (mem_inter.mp hz).2
  rw [affineImage] at hz₁ hz₂
  obtain ⟨⟨x₁, y₁⟩, hxy₁, h₁⟩ := mem_image.mp hz₁
  obtain ⟨⟨x₂, y₂⟩, hxy₂, h₂⟩ := mem_image.mp hz₂
  have hx₁ : x₁ ∈ X := (mem_product.mp hxy₁).1
  have hy₁ : y₁ ∈ Y := (mem_product.mp hxy₁).2
  have hx₂ : x₂ ∈ X := (mem_product.mp hxy₂).1
  have hy₂ : y₂ ∈ Y := (mem_product.mp hxy₂).2
  have hc : y₁ + y₂ ≠ 0 := by
    intro hy
    have hy' : y₂ = -y₁ := by linear_combination hy
    exact hanti y₁ hy₁ (hy' ▸ hy₂)
  have hrel : ξ * (y₁ + y₂) = -(x₁ + x₂) := by
    linear_combination h₁ + h₂ - hzz'
  have hmap : Set.MapsTo (fun z ↦ (y₁ + y₂) * z)
      (affineImage (-ξ) X Y) (fourfoldProductSum X Y) := by
    intro w hw
    rw [affineImage] at hw
    obtain ⟨⟨x₃, y₃⟩, hxy₃, rfl⟩ := mem_image.mp hw
    have hx₃ : x₃ ∈ X := (mem_product.mp hxy₃).1
    have hy₃ : y₃ ∈ Y := (mem_product.mp hxy₃).2
    have hp₁ : x₃ * y₁ ∈ X * Y := mul_mem_mul hx₃ hy₁
    have hp₂ : x₃ * y₂ ∈ X * Y := mul_mem_mul hx₃ hy₂
    have hp₃ : y₃ * x₁ ∈ X * Y := by
      simpa [mul_comm] using mul_mem_mul hx₁ hy₃
    have hp₄ : y₃ * x₂ ∈ X * Y := by
      simpa [mul_comm] using mul_mem_mul hx₂ hy₃
    have hfour : x₃ * y₁ + x₃ * y₂ + (y₃ * x₁ + y₃ * x₂) ∈
        fourfoldProductSum X Y := by
      exact add_mem_add (add_mem_add hp₁ hp₂) (add_mem_add hp₃ hp₄)
    have heq : (y₁ + y₂) * (x₃ + -ξ * y₃) =
        x₃ * y₁ + x₃ * y₂ + (y₃ * x₁ + y₃ * x₂) := by
      linear_combination -y₃ * hrel
    change (y₁ + y₂) * (x₃ + -ξ * y₃) ∈ fourfoldProductSum X Y
    rw [heq]
    exact hfour
  have hinj : Set.InjOn (fun z ↦ (y₁ + y₂) * z) (affineImage (-ξ) X Y) := by
    intro a _ b _ hab
    exact (mul_left_cancel₀ hc) hab
  have hfourCard : (affineImage (-ξ) X Y).card ≤ (fourfoldProductSum X Y).card :=
    card_le_card_of_injOn _ hmap hinj
  have hfourLarge : p < 2 * (fourfoldProductSum X Y).card :=
    lt_of_lt_of_le hminus (Nat.mul_le_mul_left 2 hfourCard)
  have hfourNonempty : (fourfoldProductSum X Y).Nonempty := by
    rw [← card_pos]
    omega
  have hCD := ZMod.cauchy_davenport hp hfourNonempty hfourNonempty
  have hpEight : p ≤ (eightfoldProductSum X Y).card := by
    rw [eightfoldProductSum]
    apply le_trans _ hCD
    simp only [le_min_iff]
    constructor
    · exact le_rfl
    · omega
  exact eq_of_subset_of_card_le (subset_univ _) (by simpa using hpEight)

end Glibichuk

section PrimeBlocks

variable {p k L H : ℕ}

/-- The product of the selected denominators in one choice vector. -/
def denomProduct (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) : ℕ :=
  ∏ i, q i (u i)

/-- The numerator obtained after putting a reciprocal sum over a common
denominator. -/
def recipNumerator (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) : ℕ :=
  ∑ i, ∏ j ∈ (univ.erase i), q j (u j)

/-- A sum of one reciprocal from every prime block. -/
def primeRecipSum (p : ℕ) (q : Fin k → Fin L → ℕ)
    (u : Fin k → Fin L) : ZMod p :=
  ∑ i, ((q i (u i) : ZMod p)⁻¹)

/-- The set of all blockwise reciprocal sums. -/
noncomputable def primeRecipSumSet (p : ℕ) (q : Fin k → Fin L → ℕ) :
    Finset (ZMod p) :=
  univ.image (primeRecipSum p q)

lemma denomProduct_mul_primeRecipSum (hp : p.Prime)
    (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_lt : ∀ i j, q i j < p) (hq_pos : ∀ i j, 0 < q i j) :
    (denomProduct q u : ZMod p) * primeRecipSum p q u = recipNumerator q u := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [primeRecipSum, mul_sum]
  simp only [denomProduct, recipNumerator, Nat.cast_sum, Nat.cast_prod]
  apply sum_congr rfl
  intro i _
  have hqi : (q i (u i) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (hq_pos i (u i)) (hq_lt i (u i))
  rw [← mul_prod_erase univ (fun j ↦ (q j (u j) : ZMod p)) (mem_univ i)]
  field_simp

lemma primeRecipSum_cross (hp : p.Prime)
    (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_lt : ∀ i j, q i j < p) (hq_pos : ∀ i j, 0 < q i j)
    (huv : primeRecipSum p q u = primeRecipSum p q v) :
    (recipNumerator q u * denomProduct q v : ZMod p) =
      recipNumerator q v * denomProduct q u := by
  have hu := denomProduct_mul_primeRecipSum hp q u hq_lt hq_pos
  have hv := denomProduct_mul_primeRecipSum hp q v hq_lt hq_pos
  push_cast
  calc
    (recipNumerator q u : ZMod p) * denomProduct q v =
        ((denomProduct q u : ZMod p) * primeRecipSum p q u) * denomProduct q v := by rw [hu]
    _ = ((denomProduct q v : ZMod p) * primeRecipSum p q v) * denomProduct q u := by
      rw [huv]
      ring
    _ = (recipNumerator q v : ZMod p) * denomProduct q u := by rw [hv]

lemma denomProduct_le (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_le : ∀ i j, q i j ≤ H) : denomProduct q u ≤ H ^ k := by
  classical
  calc
    denomProduct q u ≤ ∏ _i : Fin k, H :=
      prod_le_prod' fun i _ ↦ hq_le i (u i)
    _ = H ^ k := by simp

lemma recipNumerator_le (hk : 0 < k) (q : Fin k → Fin L → ℕ)
    (u : Fin k → Fin L) (hq_le : ∀ i j, q i j ≤ H) :
    recipNumerator q u ≤ k * H ^ (k - 1) := by
  classical
  calc
    recipNumerator q u ≤ ∑ _i : Fin k, H ^ (k - 1) := by
      apply sum_le_sum
      intro i _
      calc
        ∏ j ∈ (univ.erase i), q j (u j) ≤ ∏ _j ∈ (univ.erase i), H :=
          prod_le_prod' fun j _ ↦ hq_le j (u j)
        _ = H ^ (k - 1) := by simp [card_erase_of_mem]
    _ = k * H ^ (k - 1) := by simp

lemma prime_not_dvd_denomProduct_of_changed
    (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    {i : Fin k} (hi : u i ≠ v i) :
    ¬ q i (u i) ∣ denomProduct q v := by
  classical
  intro hd
  rw [denomProduct] at hd
  obtain ⟨j, _, hj⟩ :=
    (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (hq_prime i (u i))) _).mp hd
  have hqeq : q i (u i) = q j (v j) :=
    (Nat.prime_dvd_prime_iff_eq (hq_prime i (u i)) (hq_prime j (v j))).mp hj
  have hpairs : (i, u i) = (j, v j) := hq_inj hqeq
  have hij : i = j := congrArg Prod.fst hpairs
  subst j
  exact hi (congrArg Prod.snd hpairs)

lemma prime_not_dvd_recipNumerator
    (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (i : Fin k) : ¬ q i (u i) ∣ recipNumerator q u := by
  classical
  let r := q i (u i)
  let term : Fin k → ℕ := fun a ↦ ∏ j ∈ (univ.erase a), q j (u j)
  have hterm : ¬ r ∣ term i := by
    apply (Nat.prime_iff.mp (hq_prime i (u i))).not_dvd_finsetProd
    intro j hj hd
    have hqeq : q i (u i) = q j (u j) :=
      (Nat.prime_dvd_prime_iff_eq (hq_prime i (u i)) (hq_prime j (u j))).mp hd
    have hpairs : (i, u i) = (j, u j) := hq_inj hqeq
    exact (mem_erase.mp hj).1 (congrArg Prod.fst hpairs).symm
  have hrest : r ∣ ∑ a ∈ (univ.erase i), term a := by
    apply dvd_sum
    intro a ha
    apply dvd_prod_of_mem (fun j ↦ q j (u j))
    exact mem_erase.mpr ⟨fun h ↦ (mem_erase.mp ha).1 h.symm, mem_univ i⟩
  have hdecomp : recipNumerator q u = term i + ∑ a ∈ (univ.erase i), term a := by
    rw [recipNumerator]
    exact (add_sum_erase univ term (mem_univ i)).symm
  intro hnum
  apply hterm
  rw [hdecomp] at hnum
  exact (Nat.dvd_add_iff_left hrest).mpr hnum

lemma numerator_cross_ne_of_ne
    (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (huv : u ≠ v) :
    recipNumerator q u * denomProduct q v ≠
      recipNumerator q v * denomProduct q u := by
  classical
  have hcoord : ∃ i, u i ≠ v i := by
    by_contra h
    push_neg at h
    exact huv (funext h)
  obtain ⟨i, hi⟩ := hcoord
  let r := q i (u i)
  have hrD : r ∣ denomProduct q u := by
    rw [denomProduct]
    exact dvd_prod_of_mem (fun j ↦ q j (u j)) (mem_univ i)
  have hrDv : ¬ r ∣ denomProduct q v :=
    prime_not_dvd_denomProduct_of_changed q u v hq_prime hq_inj hi
  have hrN : ¬ r ∣ recipNumerator q u :=
    prime_not_dvd_recipNumerator q u hq_prime hq_inj i
  intro heq
  have hrLeft : r ∣ recipNumerator q u * denomProduct q v := by
    rw [heq]
    exact dvd_mul_of_dvd_right hrD _
  exact hrN ((hq_prime i (u i)).dvd_mul.mp hrLeft |>.resolve_right hrDv)

lemma numerator_mul_denom_le (hk : 0 < k)
    (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_le : ∀ i j, q i j ≤ H) :
    recipNumerator q u * denomProduct q v ≤ k * H ^ (2 * k - 1) := by
  calc
    recipNumerator q u * denomProduct q v ≤
        (k * H ^ (k - 1)) * H ^ k :=
      Nat.mul_le_mul (recipNumerator_le hk q u hq_le) (denomProduct_le q v hq_le)
    _ = k * H ^ (2 * k - 1) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

lemma primeRecipSum_injective (hp : p.Prime) (hk : 0 < k)
    (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p)
    (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    Function.Injective (primeRecipSum p q) := by
  intro u v huv
  by_contra huvne
  have hq_lt : ∀ i j, q i j < p := fun i j ↦ lt_of_le_of_lt (hq_le i j) hHlt
  have hq_pos : ∀ i j, 0 < q i j := fun i j ↦ (hq_prime i j).pos
  have hcross := primeRecipSum_cross hp q u v hq_lt hq_pos huv
  let A := recipNumerator q u * denomProduct q v
  let B := recipNumerator q v * denomProduct q u
  have hcast : (A : ZMod p) = (B : ZMod p) := by simpa [A, B] using hcross
  have hcastInt : ((A : ℤ) : ZMod p) = (B : ℤ) := by exact_mod_cast hcast
  have hdvd : (p : ℤ) ∣ (B : ℤ) - A :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (A : ℤ) (B : ℤ) p).mp hcastInt
  have hAle : A ≤ k * H ^ (2 * k - 1) := numerator_mul_denom_le hk q u v hq_le
  have hBle : B ≤ k * H ^ (2 * k - 1) := numerator_mul_denom_le hk q v u hq_le
  have habs : |(B : ℤ) - A| < p := by
    calc
      |(B : ℤ) - A| ≤ |(B : ℤ)| + |(A : ℤ)| := abs_sub _ _
      _ = (B : ℤ) + A := by simp
      _ ≤ 2 * k * H ^ (2 * k - 1) := by
        have hNat : B + A ≤ 2 * k * H ^ (2 * k - 1) := by
          calc
            B + A ≤ k * H ^ (2 * k - 1) + k * H ^ (2 * k - 1) :=
              Nat.add_le_add hBle hAle
            _ = 2 * k * H ^ (2 * k - 1) := by ring
        exact_mod_cast hNat
      _ < p := by exact_mod_cast hsmall
  have hzero := int_eq_zero_of_dvd_of_abs_lt hp.pos hdvd habs
  have hAB : A = B := by omega
  exact numerator_cross_ne_of_ne q u v hq_prime hq_inj huvne hAB

lemma card_primeRecipSumSet (hp : p.Prime) (hk : 0 < k)
    (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p)
    (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    (primeRecipSumSet p q).card = L ^ k := by
  classical
  rw [primeRecipSumSet, card_image_iff.mpr
    (primeRecipSum_injective hp hk q hq_prime hq_inj hq_le hHlt hsmall).injOn]
  simp

lemma denomProduct_pos (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_pos : ∀ i j, 0 < q i j) : 0 < denomProduct q u := by
  classical
  exact prod_pos fun i _ ↦ hq_pos i (u i)

lemma recipNumerator_pos (hk : 0 < k) (q : Fin k → Fin L → ℕ)
    (u : Fin k → Fin L) (hq_pos : ∀ i j, 0 < q i j) :
    0 < recipNumerator q u := by
  classical
  rw [recipNumerator]
  apply sum_pos'
  · exact fun _ _ ↦ Nat.zero_le _
  · let i : Fin k := ⟨0, hk⟩
    refine ⟨i, mem_univ i, ?_⟩
    exact prod_pos fun j _ ↦ hq_pos j (u j)

lemma primeRecipSumSet_antisymmetric (hp : p.Prime) (hk : 0 < k)
    (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p)
    (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    IsAntisymmetric (primeRecipSumSet p q) := by
  classical
  intro y hy hny
  rw [primeRecipSumSet] at hy hny
  obtain ⟨u, _, rfl⟩ := mem_image.mp hy
  obtain ⟨v, _, hvneg⟩ := mem_image.mp hny
  have hq_lt : ∀ i j, q i j < p := fun i j ↦ lt_of_le_of_lt (hq_le i j) hHlt
  have hq_pos : ∀ i j, 0 < q i j := fun i j ↦ (hq_prime i j).pos
  have hu := denomProduct_mul_primeRecipSum hp q u hq_lt hq_pos
  have hv := denomProduct_mul_primeRecipSum hp q v hq_lt hq_pos
  have hneg : primeRecipSum p q u = -primeRecipSum p q v := by
    rw [hvneg]
    simp
  let A := recipNumerator q u * denomProduct q v
  let B := recipNumerator q v * denomProduct q u
  have hABcast : (A : ZMod p) = -(B : ZMod p) := by
    dsimp [A, B]
    push_cast
    calc
      (recipNumerator q u : ZMod p) * denomProduct q v =
          ((denomProduct q u : ZMod p) * primeRecipSum p q u) * denomProduct q v := by rw [hu]
      _ = -(((denomProduct q v : ZMod p) * primeRecipSum p q v) * denomProduct q u) := by
        rw [hneg]
        ring
      _ = -((recipNumerator q v : ZMod p) * denomProduct q u) := by rw [hv]
  have hsumcast : ((A + B : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hABcast]
    simp
  have hpdiv : p ∣ A + B := (ZMod.natCast_eq_zero_iff (A + B) p).mp hsumcast
  have hAle : A ≤ k * H ^ (2 * k - 1) := numerator_mul_denom_le hk q u v hq_le
  have hBle : B ≤ k * H ^ (2 * k - 1) := numerator_mul_denom_le hk q v u hq_le
  have hsumlt : A + B < p := by
    calc
      A + B ≤ k * H ^ (2 * k - 1) + k * H ^ (2 * k - 1) :=
        Nat.add_le_add hAle hBle
      _ = 2 * k * H ^ (2 * k - 1) := by ring
      _ < p := hsmall
  have hApos : 0 < A := mul_pos (recipNumerator_pos hk q u hq_pos)
    (denomProduct_pos q v hq_pos)
  exact Nat.not_dvd_of_pos_of_lt (lt_of_lt_of_le hApos (Nat.le_add_right A B)) hsumlt hpdiv

/-- The `k²` natural denominators obtained by expanding a product of two
blockwise reciprocal sums. -/
noncomputable def productDenoms (q : Fin k → Fin L → ℕ)
    (u v : Fin k → Fin L) : List ℕ :=
  ((univ : Finset (Fin k)) ×ˢ univ).toList.map fun ij ↦ q ij.1 (u ij.1) * q ij.2 (v ij.2)

lemma sum_map_toList {M : Type*} [AddCommMonoid M] {I : Type*}
    (s : Finset I) (f : I → M) : (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hperm : List.Perm ((insert a s).toList.map f) (f a :: s.toList.map f) :=
        (toList_insert ha).map f
      calc
        _ = (f a :: s.toList.map f).sum := hperm.sum_eq
        _ = _ := by simp [ha, ih]

@[simp] lemma length_productDenoms (q : Fin k → Fin L → ℕ)
    (u v : Fin k → Fin L) : (productDenoms q u v).length = k ^ 2 := by
  classical
  simp [productDenoms, pow_two]

lemma sum_productDenoms (hp : p.Prime) (q : Fin k → Fin L → ℕ)
    (u v : Fin k → Fin L) :
    (List.map (fun n : ℕ ↦ ((n : ZMod p)⁻¹)) (productDenoms q u v)).sum =
      primeRecipSum p q u * primeRecipSum p q v := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  calc
    (List.map (fun n : ℕ ↦ ((n : ZMod p)⁻¹)) (productDenoms q u v)).sum =
        ∑ ij ∈ ((univ : Finset (Fin k)) ×ˢ univ),
          (((q ij.1 (u ij.1) * q ij.2 (v ij.2) : ℕ) : ZMod p)⁻¹) := by
      simpa [productDenoms, List.map_map] using
        (sum_map_toList ((univ : Finset (Fin k)) ×ˢ univ)
          (fun ij ↦ (((q ij.1 (u ij.1) * q ij.2 (v ij.2) : ℕ) : ZMod p)⁻¹)))
    _ = ∑ i, ∑ j, ((q i (u i) : ZMod p)⁻¹) * ((q j (v j) : ZMod p)⁻¹) := by
      rw [sum_product]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      simp only [Prod.fst, Prod.snd, Nat.cast_mul]
      rw [mul_inv_rev, mul_comm]
    _ = primeRecipSum p q u * primeRecipSum p q v := by
      rw [primeRecipSum, primeRecipSum, Fintype.sum_mul_sum]

lemma productDenoms_admissible (hp : p.Prime) {ε : ℝ}
    (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ n ∈ productDenoms q u v, AdmissibleDenom ε p n := by
  classical
  intro n hn
  rw [productDenoms, List.mem_map] at hn
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := hn
  have hi : i ∈ (univ : Finset (Fin k)) := (mem_product.mp (Finset.mem_toList.mp hij)).1
  have hj : j ∈ (univ : Finset (Fin k)) := (mem_product.mp (Finset.mem_toList.mp hij)).2
  have hqi_lt : q i (u i) < p := lt_of_le_of_lt (hq_le i (u i)) hHlt
  have hqj_lt : q j (v j) < p := lt_of_le_of_lt (hq_le j (v j)) hHlt
  refine ⟨mul_pos (hq_prime i (u i)).pos (hq_prime j (v j)).pos, ?_, ?_⟩
  · apply le_trans _ hHsq
    norm_cast
    simpa [pow_two] using Nat.mul_le_mul (hq_le i (u i)) (hq_le j (v j))
  · apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with hdvd | hdvd
    · exact Nat.not_dvd_of_pos_of_lt (hq_prime i (u i)).pos hqi_lt hdvd
    · exact Nat.not_dvd_of_pos_of_lt (hq_prime j (v j)).pos hqj_lt hdvd

lemma represents_append {ε : ℝ} {a b : ZMod p} {xs ys : List ℕ}
    (hxs : Represents ε p a xs) (hys : Represents ε p b ys) :
    Represents ε p (a + b) (xs ++ ys) := by
  constructor
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hxs.1 n hn
    · exact hys.1 n hn
  · simp only [List.map_append, List.sum_append]
    rw [hxs.2, hys.2]

def ExactlyRepresentable (ε : ℝ) (p m : ℕ) (a : ZMod p) : Prop :=
  ∃ xs : List ℕ, xs.length = m ∧ Represents ε p a xs

lemma exactlyRepresentable_add {m n : ℕ} {S T : Finset (ZMod p)} {ε : ℝ}
    (hS : ∀ a ∈ S, ExactlyRepresentable ε p m a)
    (hT : ∀ b ∈ T, ExactlyRepresentable ε p n b) :
    ∀ z ∈ S + T, ExactlyRepresentable ε p (m + n) z := by
  classical
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
  obtain ⟨xs, hlenx, hxs⟩ := hS a ha
  obtain ⟨ys, hleny, hys⟩ := hT b hb
  refine ⟨xs ++ ys, by simp [hlenx, hleny], represents_append hxs hys⟩

lemma product_mem_exactlyRepresentable (hp : p.Prime) {ε : ℝ}
    (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ z ∈ primeRecipSumSet p q * primeRecipSumSet p q,
      ExactlyRepresentable ε p (k ^ 2) z := by
  classical
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hz
  rw [primeRecipSumSet] at ha hb
  obtain ⟨u, _, rfl⟩ := mem_image.mp ha
  obtain ⟨v, _, rfl⟩ := mem_image.mp hb
  refine ⟨productDenoms q u v, length_productDenoms q u v,
    productDenoms_admissible hp q u v hq_prime hq_le hHlt hHsq, ?_⟩
  exact sum_productDenoms hp q u v

lemma eightfold_mem_exactlyRepresentable (hp : p.Prime) {ε : ℝ}
    (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ z ∈ eightfoldProductSum (primeRecipSumSet p q) (primeRecipSumSet p q),
      ExactlyRepresentable ε p (8 * k ^ 2) z := by
  classical
  let B := primeRecipSumSet p q
  let P := B * B
  have hP : ∀ z ∈ P, ExactlyRepresentable ε p (k ^ 2) z := by
    simpa [P, B] using product_mem_exactlyRepresentable hp q hq_prime hq_le hHlt hHsq
  have hTwo : ∀ z ∈ P + P, ExactlyRepresentable ε p (2 * k ^ 2) z := by
    simpa [two_mul] using exactlyRepresentable_add hP hP
  have hFour : ∀ z ∈ (P + P) + (P + P),
      ExactlyRepresentable ε p (4 * k ^ 2) z := by
    have := exactlyRepresentable_add hTwo hTwo
    convert this using 1 <;> ring
  have hEight : ∀ z ∈ ((P + P) + (P + P)) + ((P + P) + (P + P)),
      ExactlyRepresentable ε p (8 * k ^ 2) z := by
    have := exactlyRepresentable_add hFour hFour
    convert this using 1 <;> ring
  simpa [eightfoldProductSum, fourfoldProductSum, P, B] using hEight

end PrimeBlocks

section AsymptoticEstimates

open Filter Topology Asymptotics Real

lemma sq_succ_le_two_pow (n : ℕ) (hn : 6 ≤ n) : (n + 1) ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1 + 1) ^ 2 ≤ 2 * (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

lemma eventually_log_le_const_rpow {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, log x ≤ c * x ^ r := by
  have hbound := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx1), Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg (by positivity) _)] at hx
  exact hx

lemma eventually_const_mul_rpow_lt_rpow {a b c : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a < x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_gt_atTop c] with x hx hxc
  calc
    c * x ^ a < x ^ (b - a) * x ^ a :=
      mul_lt_mul_of_pos_right hxc (rpow_pos_of_pos hx a)
    _ = x ^ b := by
      rw [← Real.rpow_add hx]
      congr 2
      ring

lemma eventually_nat_const_mul_rpow_lt_rpow {a b c : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b :=
  tendsto_natCast_atTop_atTop.eventually (eventually_const_mul_rpow_lt_rpow hab)

lemma eventually_primeCounting_ge_rpow {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ t ≤ Nat.primeCounting n := by
  have hlogReal := eventually_log_le_const_rpow (sub_pos.mpr ht1)
    (show 0 < log 2 / 2 by positivity)
  have hlog := tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [eventually_ge_atTop 6, hlog] with n hn hlogn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 6) hn)
  have hlogpos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 6) hn))
  have hsquare := sq_succ_le_two_pow n hn
  have hsquareR : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast hsquare
  have hnum : log ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * log 2 / 2 := by
    have hlogpow := log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2) hsquareR
    rw [Real.log_pow, Real.log_pow] at hlogpow
    norm_num at hlogpow ⊢
    linarith
  apply le_trans _ (Chebyshev.pi_ge n)
  rw [le_div_iff₀ hlogpos]
  have hrpow : (n : ℝ) ^ t * (n : ℝ) ^ (1 - t) = n := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hlogn (rpow_nonneg hnpos.le t)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hmul' : (n : ℝ) ^ t * log n ≤ (n : ℝ) * log 2 / 2 := by
    calc
      _ ≤ (n : ℝ) ^ t * (log 2 / 2 * (n : ℝ) ^ (1 - t)) := hmul
      _ = (log 2 / 2) * ((n : ℝ) ^ t * (n : ℝ) ^ (1 - t)) := by ring
      _ = (n : ℝ) * log 2 / 2 := by rw [hrpow]; ring
  norm_num [Nat.cast_add, Nat.cast_one] at hnum
  linarith

/-- Natural floor of a real power. -/
noncomputable def powFloor (a : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ a⌋₊

lemma powFloor_cast_le (a : ℝ) (n : ℕ) :
    (powFloor a n : ℝ) ≤ (n : ℝ) ^ a := by
  exact Nat.floor_le (rpow_nonneg (Nat.cast_nonneg n) a)

lemma half_rpow_lt_powFloor {a : ℝ} {n : ℕ} (hpow : 1 ≤ (n : ℝ) ^ a) :
    (n : ℝ) ^ a / 2 < powFloor a n := by
  simpa [powFloor] using Nat.div_two_lt_floor hpow

lemma tendsto_powFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (powFloor a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  have ht := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := (eventually_atTop.1 (ht.eventually_ge_atTop (N : ℝ)))
  refine ⟨M, fun n hn ↦ ?_⟩
  rw [powFloor]
  exact (Nat.le_floor_iff (rpow_nonneg (Nat.cast_nonneg n) a)).mpr (by
    simpa only [Function.comp_apply] using hM n hn)

lemma eventually_powFloor_lt_self {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in atTop, powFloor a n < n := by
  have hcmp := eventually_nat_const_mul_rpow_lt_rpow (c := 1) ha
  filter_upwards [hcmp] with n hn
  have hreal : (powFloor a n : ℝ) < n :=
    lt_of_le_of_lt (powFloor_cast_le a n) (by simpa using hn)
  exact_mod_cast hreal

lemma eventually_small_clearing_bound {k : ℕ} {δ : ℝ}
    (hmargin : ((2 * k - 1 : ℕ) : ℝ) * δ < 1) :
    ∀ᶠ n : ℕ in atTop, 2 * k * (powFloor δ n) ^ (2 * k - 1) < n := by
  have hcmp := eventually_nat_const_mul_rpow_lt_rpow
    (c := (2 * k : ℝ)) (a := δ * (2 * k - 1 : ℕ)) (b := 1) (by
      simpa [mul_comm] using hmargin)
  filter_upwards [hcmp, eventually_gt_atTop 0] with n hn hnpos
  have hH := powFloor_cast_le δ n
  have hpow : ((powFloor δ n : ℝ) ^ (2 * k - 1)) ≤
      (((n : ℝ) ^ δ) ^ (2 * k - 1)) :=
    pow_le_pow_left₀ (by positivity) hH _
  have hreal : ((2 * k * (powFloor δ n) ^ (2 * k - 1) : ℕ) : ℝ) < n := by
    calc
      _ = (2 * k : ℝ) * (powFloor δ n : ℝ) ^ (2 * k - 1) := by norm_num
      _ ≤ (2 * k : ℝ) * (((n : ℝ) ^ δ) ^ (2 * k - 1)) := by gcongr
      _ = (2 * k : ℝ) * (n : ℝ) ^ (δ * (2 * k - 1 : ℕ)) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity)]
      _ < (n : ℝ) ^ (1 : ℝ) := hn
      _ = n := by simp
  exact_mod_cast hreal

lemma powFloor_sq_le_rpow {δ ε : ℝ} {n : ℕ} (hn : 1 ≤ n) (hmargin : 2 * δ ≤ ε) :
    (powFloor δ n : ℝ) ^ 2 ≤ (n : ℝ) ^ ε := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (powFloor δ n : ℝ) ^ 2 ≤ ((n : ℝ) ^ δ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (powFloor_cast_le δ n) _
    _ = (n : ℝ) ^ (δ * 2) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    _ = (n : ℝ) ^ (2 * δ) := by ring_nf
    _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hnreal hmargin

lemma eventually_self_lt_powFloor_pow {k : ℕ} {γ : ℝ}
    (hk : 0 < k) (hγ : 0 < γ) (hmargin : 1 < (2 * k : ℝ) * γ) :
    ∀ᶠ n : ℕ in atTop, n < (powFloor γ n) ^ (2 * k) := by
  have hcmp := eventually_nat_const_mul_rpow_lt_rpow
    (c := (2 : ℝ) ^ (2 * k : ℕ)) (a := 1) (b := (2 * k : ℕ) * γ) (by
      simpa [mul_comm] using hmargin)
  have hpowOne := ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hcmp, hpowOne, eventually_gt_atTop 0] with n hnGrow hnOne hnpos
  have hlow := half_rpow_lt_powFloor hnOne
  have hlowPow : (((n : ℝ) ^ γ / 2) ^ (2 * k)) <
      (powFloor γ n : ℝ) ^ (2 * k) := by
    exact pow_lt_pow_left₀ hlow (by positivity) (by omega)
  have hbase : (n : ℝ) < ((n : ℝ) ^ γ / 2) ^ (2 * k) := by
    have hpowEq : (n : ℝ) ^ ((2 * k : ℕ) * γ) =
        ((n : ℝ) ^ γ) ^ (2 * k) := by
      calc
        _ = (n : ℝ) ^ (γ * (2 * k : ℕ)) := by congr 1 <;> ring
        _ = ((n : ℝ) ^ γ) ^ (((2 * k : ℕ) : ℝ)) :=
          Real.rpow_mul (x := (n : ℝ)) (by positivity) γ ((2 * k : ℕ) : ℝ)
        _ = ((n : ℝ) ^ γ) ^ (2 * k) := Real.rpow_natCast _ _
    rw [div_pow]
    rw [← hpowEq]
    have hden : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    rw [lt_div_iff₀ hden]
    simpa [mul_comm] using hnGrow
  have hreal : (n : ℝ) < ((powFloor γ n) ^ (2 * k) : ℕ) := by
    have hlowPow' : ((n : ℝ) ^ γ / 2) ^ (2 * k) <
        (((powFloor γ n) ^ (2 * k) : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow] using hlowPow
    exact hbase.trans hlowPow'
  exact_mod_cast hreal

lemma eventually_prime_supply {k : ℕ} {δ γ t : ℝ}
    (hδ : 0 < δ) (ht0 : 0 < t) (ht1 : t < 1) (hmargin : γ < δ * t) :
    ∀ᶠ n : ℕ in atTop,
      k * powFloor γ n ≤ (Nat.primesLE (powFloor δ n)).card := by
  have hprimeAtH := (tendsto_powFloor_atTop hδ).eventually
    (eventually_primeCounting_ge_rpow ht0 ht1)
  have hcmp := eventually_nat_const_mul_rpow_lt_rpow
    (c := (k : ℝ) * (2 : ℝ) ^ t) (a := γ) (b := δ * t) hmargin
  have hpowOne := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hprimeAtH, hcmp, hpowOne, eventually_gt_atTop 0] with n hprime hgrow hnOne hnpos
  have hHlow := half_rpow_lt_powFloor hnOne
  have hHlowPow : (((n : ℝ) ^ δ / 2) ^ t) < (powFloor δ n : ℝ) ^ t :=
    Real.rpow_lt_rpow (by positivity) hHlow ht0
  have hbase : (k : ℝ) * (n : ℝ) ^ γ < ((n : ℝ) ^ δ / 2) ^ t := by
    rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_mul (by positivity)]
    have hden : (0 : ℝ) < (2 : ℝ) ^ t := rpow_pos_of_pos (by norm_num) _
    rw [lt_div_iff₀ hden]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgrow
  have hKLreal : ((k * powFloor γ n : ℕ) : ℝ) ≤ Nat.primeCounting (powFloor δ n) := by
    apply le_of_lt
    calc
      _ = (k : ℝ) * (powFloor γ n : ℝ) := by norm_num
      _ ≤ (k : ℝ) * (n : ℝ) ^ γ := by
        gcongr
        exact powFloor_cast_le γ n
      _ < ((n : ℝ) ^ δ / 2) ^ t := hbase
      _ < (powFloor δ n : ℝ) ^ t := hHlowPow
      _ ≤ Nat.primeCounting (powFloor δ n) := hprime
  rw [Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast hKLreal

def LargeParameters (ε : ℝ) (k : ℕ) (δ γ : ℝ) (n : ℕ) : Prop :=
  2 < n ∧
  powFloor δ n < n ∧
  2 * k * (powFloor δ n) ^ (2 * k - 1) < n ∧
  (powFloor δ n : ℝ) ^ 2 ≤ (n : ℝ) ^ ε ∧
  n < (powFloor γ n) ^ (2 * k) ∧
  k * powFloor γ n ≤ (Nat.primesLE (powFloor δ n)).card

lemma eventually_largeParameters {ε δ γ t : ℝ} {k : ℕ}
    (hk : 0 < k) (hδ : 0 < δ) (hγ : 0 < γ) (hδone : δ < 1)
    (hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1)
    (hdenom : 2 * δ ≤ ε) (hgrow : 1 < (2 * k : ℝ) * γ)
    (ht0 : 0 < t) (ht1 : t < 1) (hsupply : γ < δ * t) :
    ∀ᶠ n : ℕ in atTop, LargeParameters ε k δ γ n := by
  have hHlt := eventually_powFloor_lt_self hδone
  have hsmall := eventually_small_clearing_bound (k := k) hclear
  have hlarge := eventually_self_lt_powFloor_pow hk hγ hgrow
  have hprimes := eventually_prime_supply (k := k) hδ ht0 ht1 hsupply
  filter_upwards [eventually_gt_atTop 2, eventually_ge_atTop 1, hHlt, hsmall, hlarge, hprimes]
    with n hn hn1 hHn hsmalln hlargen hprimesn
  exact ⟨hn, hHn, hsmalln, powFloor_sq_le_rpow hn1 hdenom, hlargen, hprimesn⟩

lemma largeParameters_threshold {ε δ γ t : ℝ} {k : ℕ}
    (hk : 0 < k) (hδ : 0 < δ) (hγ : 0 < γ) (hδone : δ < 1)
    (hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1)
    (hdenom : 2 * δ ≤ ε) (hgrow : 1 < (2 * k : ℝ) * γ)
    (ht0 : 0 < t) (ht1 : t < 1) (hsupply : γ < δ * t) :
    ∃ P₀ : ℕ, ∀ n ≥ P₀, LargeParameters ε k δ γ n := by
  exact eventually_atTop.1 (eventually_largeParameters hk hδ hγ hδone hclear hdenom hgrow
    ht0 ht1 hsupply)

lemma choose_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (δ γ t : ℝ),
      0 < k ∧ 0 < δ ∧ 0 < γ ∧ δ < 1 ∧
      ((2 * k - 1 : ℕ) : ℝ) * δ < 1 ∧
      2 * δ ≤ ε ∧ 1 < (2 * k : ℝ) * γ ∧
      0 < t ∧ t < 1 ∧ γ < δ * t := by
  obtain ⟨k, hkbig⟩ := exists_nat_gt (2 / ε + 1)
  have hkR : (1 : ℝ) < k := by
    have : 0 < 2 / ε := div_pos (by norm_num) hε
    linarith
  have hk : 0 < k := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hkR)
  let d : ℝ := 4 * k - 1
  let δ : ℝ := 2 / d
  let s : ℝ := 1 / (2 * k)
  let γ : ℝ := (δ + s) / 2
  let t : ℝ := (γ / δ + 1) / 2
  have h2kpos : (0 : ℝ) < 2 * k := by positivity
  have hdpos : 0 < d := by
    dsimp [d]
    nlinarith
  have hδ : 0 < δ := div_pos (by norm_num) hdpos
  have hs : 0 < s := div_pos (by norm_num) h2kpos
  have hsδ : s < δ := by
    dsimp [s, δ]
    rw [div_lt_div_iff₀ h2kpos hdpos]
    dsimp [d]
    nlinarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγδ : γ < δ := by dsimp [γ]; linarith
  have hδone : δ < 1 := by
    dsimp [δ]
    rw [div_lt_one hdpos]
    dsimp [d]
    nlinarith
  have hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1 := by
    have hkcast : (((2 * k - 1 : ℕ) : ℝ)) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
      norm_num
    rw [hkcast]
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_one hdpos]
    dsimp [d]
    nlinarith
  have hkε : 2 + ε < (k : ℝ) * ε := by
    calc
      2 + ε = (2 / ε + 1) * ε := by field_simp
      _ < (k : ℝ) * ε := mul_lt_mul_of_pos_right hkbig hε
  have hdenomStrict : 2 * δ < ε := by
    have hfour : (4 : ℝ) < ε * d := by
      dsimp [d]
      nlinarith
    dsimp [δ]
    rw [show 2 * (2 / d) = 4 / d by ring]
    rw [div_lt_iff₀ hdpos]
    nlinarith
  have hgrow : 1 < (2 * k : ℝ) * γ := by
    have hone : (2 * k : ℝ) * s = 1 := by dsimp [s]; field_simp
    calc
      1 = (2 * k : ℝ) * s := hone.symm
      _ < (2 * k : ℝ) * γ := mul_lt_mul_of_pos_left (by dsimp [γ]; linarith) h2kpos
  have hratio0 : 0 < γ / δ := div_pos hγ hδ
  have hratio1 : γ / δ < 1 := (div_lt_one hδ).mpr hγδ
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hdt : δ * t = (γ + δ) / 2 := by
    dsimp [t]
    field_simp [ne_of_gt hδ]
  have hsupply : γ < δ * t := by rw [hdt]; linarith
  exact ⟨k, δ, γ, t, hk, hδ, hγ, hδone, hclear, hdenomStrict.le,
    hgrow, ht0, ht1, hsupply⟩

end AsymptoticEstimates

section Assembly

lemma one_admissible {ε : ℝ} {p : ℕ} (hε : 0 < ε) (hp : p.Prime) :
    AdmissibleDenom ε p 1 := by
  refine ⟨by norm_num, ?_, by simp⟩
  norm_num only [Nat.cast_one]
  apply Real.one_le_rpow
  · exact_mod_cast hp.one_le
  · exact hε.le

/-- For the finitely many small primes, repeat the denominator `1` exactly
`a.val` times. -/
lemma repeat_one_represents {ε : ℝ} {p : ℕ} (hε : 0 < ε) (hp : p.Prime)
    (a : ZMod p) : Represents ε p a (List.replicate a.val 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro n hn
    rw [List.eq_of_mem_replicate hn]
    exact one_admissible hε hp
  · simp [ZMod.natCast_zmod_val]

/-- For parameters satisfying all the large-prime estimates, the prime blocks
and Glibichuk's covering lemma give an exact representation by `8k²` terms. -/
lemma large_prime_representation {ε δ γ : ℝ} {k p : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpar : LargeParameters ε k δ γ p)
    (a : ZMod p) :
    ExactlyRepresentable ε p (8 * k ^ 2) a := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases hpar with ⟨hp2, hHlt, hsmall, hHsq, hlarge, hsupply⟩
  have hcardDomain :
      Fintype.card (Fin k × Fin (powFloor γ p)) ≤
        (Nat.primesLE (powFloor δ p)).card := by
    simpa using hsupply
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hcardDomain
  let q : Fin k → Fin (powFloor γ p) → ℕ := fun i j ↦ e (i, j)
  have hq_mem : ∀ i j, q i j ∈ Nat.primesLE (powFloor δ p) := by
    intro i j
    apply he
    exact ⟨(i, j), rfl⟩
  have hq_prime : ∀ i j, (q i j).Prime := fun i j ↦
    Nat.prime_of_mem_primesLE (hq_mem i j)
  have hq_le : ∀ i j, q i j ≤ powFloor δ p := fun i j ↦
    Nat.le_of_mem_primesLE (hq_mem i j)
  have hq_inj : Function.Injective
      (fun ij : Fin k × Fin (powFloor γ p) ↦ q ij.1 ij.2) := by
    intro x y hxy
    apply e.injective
    simpa [q] using hxy
  let B := primeRecipSumSet p q
  have hcardB : B.card = (powFloor γ p) ^ k := by
    simpa [B] using card_primeRecipSumSet hp hk q hq_prime hq_inj hq_le hHlt hsmall
  have hprod : p < B.card * B.card := by
    calc
      p < (powFloor γ p) ^ (2 * k) := hlarge
      _ = (powFloor γ p) ^ k * (powFloor γ p) ^ k := by
        rw [two_mul, pow_add]
      _ = B.card * B.card := by rw [hcardB]
  have hanti : IsAntisymmetric B := by
    simpa [B] using primeRecipSumSet_antisymmetric hp hk q hq_prime hq_le hHlt hsmall
  have hcover : eightfoldProductSum B B = univ :=
    glibichuk_cover hp hp2 B B hprod hanti
  have ha : a ∈ eightfoldProductSum B B := by rw [hcover]; simp
  simpa [B] using
    (eightfold_mem_exactlyRepresentable hp q hq_prime hq_le hHlt hHsq a ha)

/-- The affirmative resolution of Erdős Problem 1180. -/
theorem erdos_1180 : (∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
  ∃ xs : List ℕ, xs.length ≤ C ∧ Erdos1180.Represents ε p a xs) := by
  intro ε hε
  obtain ⟨k, δ, γ, t, hk, hδ, hγ, hδone, hclear, hdenom,
    hgrow, ht0, ht1, hsupply⟩ := choose_parameters hε
  obtain ⟨P₀, hP₀⟩ := largeParameters_threshold hk hδ hγ hδone hclear hdenom
    hgrow ht0 ht1 hsupply
  refine ⟨max (8 * k ^ 2) P₀, ?_⟩
  intro p hp a
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hlarge : P₀ ≤ p
  · obtain ⟨xs, hlen, hrep⟩ :=
      large_prime_representation hp hk (hP₀ p hlarge) a
    refine ⟨xs, ?_, hrep⟩
    calc
      xs.length = 8 * k ^ 2 := hlen
      _ ≤ max (8 * k ^ 2) P₀ := le_max_left _ _
  · let xs := List.replicate a.val 1
    refine ⟨xs, ?_, by simpa [xs] using repeat_one_represents hε hp a⟩
    have hpP₀ : p < P₀ := Nat.lt_of_not_ge hlarge
    calc
      xs.length = a.val := by simp [xs]
      _ ≤ P₀ := Nat.le_of_lt (a.val_lt.trans hpP₀)
      _ ≤ max (8 * k ^ 2) P₀ := le_max_right _ _

end Assembly

end Erdos1180

#print axioms Erdos1180.erdos_1180
