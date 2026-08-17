/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# The outer profile-count reduction for Erdős Problem 636

The Kwan--Sudakov profile-count reduction associates to every parameter
`ell` one of two large fixed-order spectra.  Their orders have the forms

* `ell - f + h`, and
* `2 * (ell - f) + h`.

On a parameter set on which `f ≤ ell`, each of these two maps is injective.
Consequently an order occurs with multiplicity at most two after the two
families are combined.  This file isolates that entirely finite argument.
It does not depend on graphs or on the analytic part of the proof.
-/

open scoped BigOperators

namespace Erdos636.ProfileReduction

section TwoMaps

variable {Iota Kappa E : Type*}

/-- The orders represented by either of two maps on a finite parameter set. -/
def representedOrders [DecidableEq Kappa] (I : Finset Iota)
    (left right : Iota → Kappa) : Finset Kappa :=
  I.image left ∪ I.image right

/-- A fixed-order spectrum tagged by its order.  The tag makes spectra at
different orders disjoint, even when their elements coincide. -/
def taggedSpectrum [DecidableEq Kappa] [DecidableEq E]
    (spectra : Kappa → Finset E) (k : Kappa) : Finset (Kappa × E) :=
  (spectra k).image fun e ↦ (k, e)

/-- The union of all tagged spectra at the orders in `K`. -/
def taggedSpectra [DecidableEq Kappa] [DecidableEq E]
    (K : Finset Kappa) (spectra : Kappa → Finset E) : Finset (Kappa × E) :=
  K.biUnion (taggedSpectrum spectra)

@[simp] lemma mem_taggedSpectrum [DecidableEq Kappa] [DecidableEq E]
    {spectra : Kappa → Finset E} {k : Kappa} {p : Kappa × E} :
    p ∈ taggedSpectrum spectra k ↔ p.1 = k ∧ p.2 ∈ spectra k := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨e, he, rfl⟩
    exact ⟨rfl, he⟩
  · rintro ⟨hp, he⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, he, Prod.ext hp.symm rfl⟩

@[simp] lemma card_taggedSpectrum [DecidableEq Kappa] [DecidableEq E]
    (spectra : Kappa → Finset E) (k : Kappa) :
    (taggedSpectrum spectra k).card = (spectra k).card := by
  rw [taggedSpectrum, Finset.card_image_iff.mpr]
  intro x _hx y _hy hxy
  exact congrArg Prod.snd hxy

lemma taggedSpectrum_pairwiseDisjoint [DecidableEq Kappa] [DecidableEq E]
    (K : Finset Kappa) (spectra : Kappa → Finset E) :
    (K : Set Kappa).PairwiseDisjoint (taggedSpectrum spectra) := by
  intro k _hk l _hl hkl
  change Disjoint (taggedSpectrum spectra k) (taggedSpectrum spectra l)
  rw [Finset.disjoint_left]
  intro p hpk hpl
  have hk : p.1 = k := (mem_taggedSpectrum.mp hpk).1
  have hl : p.1 = l := (mem_taggedSpectrum.mp hpl).1
  exact hkl (hk.symm.trans hl)

/-- Tagged fixed-order spectra have exactly the sum of their cardinalities. -/
lemma card_taggedSpectra [DecidableEq Kappa] [DecidableEq E]
    (K : Finset Kappa) (spectra : Kappa → Finset E) :
    (taggedSpectra K spectra).card = ∑ k ∈ K, (spectra k).card := by
  rw [taggedSpectra, Finset.card_biUnion
    (taggedSpectrum_pairwiseDisjoint K spectra)]
  simp

/-! ## Maps with uniformly bounded fibres -/

/-- The part of a finite domain which an order map sends to `k`. -/
def orderFiber [DecidableEq Kappa] (L : Finset Iota) (order : Iota → Kappa)
    (k : Kappa) : Finset Iota :=
  L.filter fun ell ↦ order ell = k

@[simp] lemma mem_orderFiber [DecidableEq Kappa] {L : Finset Iota}
    {order : Iota → Kappa} {k : Kappa} {ell : Iota} :
    ell ∈ orderFiber L order k ↔ ell ∈ L ∧ order ell = k := by
  simp [orderFiber]

/-- A weighted finite sum through a map with fibres of size at most `M`
is at most `M` times the sum over the image. -/
lemma sum_comp_le_fiberBound_mul_sum_image [DecidableEq Kappa]
    (L : Finset Iota) (order : Iota → Kappa) (weight : Kappa → ℝ) (M : ℕ)
    (hweight : ∀ k, 0 ≤ weight k)
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M) :
    ∑ ell ∈ L, weight (order ell) ≤
      M * ∑ k ∈ L.image order, weight k := by
  have hreindex :
      ∑ ell ∈ L, weight (order ell) =
        ∑ k ∈ L.image order, ∑ ell ∈ orderFiber L order k, weight (order ell) := by
    symm
    simpa only [orderFiber] using
      (Finset.sum_fiberwise_of_maps_to
        (s := L) (t := L.image order) (g := order)
        (fun ell hell ↦ Finset.mem_image_of_mem order hell)
        (fun ell ↦ weight (order ell)))
  rw [hreindex]
  calc
    (∑ k ∈ L.image order, ∑ ell ∈ orderFiber L order k, weight (order ell)) =
        ∑ k ∈ L.image order,
          ((orderFiber L order k).card : ℝ) * weight k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ ell ∈ orderFiber L order k, weight (order ell)) =
            ∑ _ell ∈ orderFiber L order k, weight k := by
          apply Finset.sum_congr rfl
          intro ell hell
          rw [(mem_orderFiber.mp hell).2]
        _ = ((orderFiber L order k).card : ℝ) * weight k := by simp
    _ ≤ ∑ k ∈ L.image order, (M : ℝ) * weight k := by
      exact Finset.sum_le_sum fun k hk ↦
        mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber k hk) (hweight k)
    _ = M * ∑ k ∈ L.image order, weight k := by
      rw [Finset.mul_sum]

/-- Generic bounded-fibre profile count.  If every point of `L` selects a
fixed-order spectrum of real cardinality at least `mass`, and every selected
order has at most `M` preimages, then the tagged union contains at least the
total promised mass divided by `M`. -/
theorem fiberBound_spectra_bound [DecidableEq Kappa] [DecidableEq E]
    (L : Finset Iota) (order : Iota → Kappa) (spectra : Kappa → Finset E)
    (mass : ℝ) (M : ℕ)
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M)
    (hlarge : ∀ ell ∈ L, mass ≤ ((spectra (order ell)).card : ℝ)) :
    (L.card : ℝ) * mass ≤
      M * ((taggedSpectra (L.image order) spectra).card : ℝ) := by
  let weight : Kappa → ℝ := fun k ↦ ((spectra k).card : ℝ)
  have hlower :
      (L.card : ℝ) * mass ≤ ∑ ell ∈ L, weight (order ell) := by
    simpa [weight] using Finset.sum_le_sum hlarge
  have hupper := sum_comp_le_fiberBound_mul_sum_image L order weight M
    (fun _ ↦ Nat.cast_nonneg _) hfiber
  have hcard :
      ((taggedSpectra (L.image order) spectra).card : ℝ) =
        ∑ k ∈ L.image order, ((spectra k).card : ℝ) := by
    exact_mod_cast card_taggedSpectra (L.image order) spectra
  calc
    (L.card : ℝ) * mass ≤ ∑ ell ∈ L, weight (order ell) := hlower
    _ ≤ M * ∑ k ∈ L.image order, weight k := hupper
    _ = M * ((taggedSpectra (L.image order) spectra).card : ℝ) := by
      rw [hcard]

/-- Bounded-fibre profile count inside any global profile set containing all
relevant tagged spectra. -/
theorem fiberBound_globalProfiles_bound [DecidableEq Kappa] [DecidableEq E]
    (L : Finset Iota) (order : Iota → Kappa) (spectra : Kappa → Finset E)
    (profiles : Finset (Kappa × E)) (mass : ℝ) (M : ℕ)
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M)
    (hlarge : ∀ ell ∈ L, mass ≤ ((spectra (order ell)).card : ℝ))
    (hprofiles : taggedSpectra (L.image order) spectra ⊆ profiles) :
    (L.card : ℝ) * mass ≤ M * (profiles.card : ℝ) := by
  calc
    (L.card : ℝ) * mass ≤
        M * ((taggedSpectra (L.image order) spectra).card : ℝ) :=
      fiberBound_spectra_bound L order spectra mass M hfiber hlarge
    _ ≤ M * (profiles.card : ℝ) := by gcongr

/-- The generic bounded-fibre reduction at the scale of Problem 636. -/
theorem fiberBound_quadraticSqrt_bound [DecidableEq Kappa] [DecidableEq E]
    (n : ℕ) (c a : ℝ) (L : Finset Iota) (order : Iota → Kappa)
    (spectra : Kappa → Finset E) (profiles : Finset (Kappa × E)) (M : ℕ)
    (ha : 0 ≤ a) (hM : 0 < M) (hL : c * n ≤ (L.card : ℝ))
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M)
    (hlarge : ∀ ell ∈ L,
      a * n * Real.sqrt n ≤ ((spectra (order ell)).card : ℝ))
    (hprofiles : taggedSpectra (L.image order) spectra ⊆ profiles) :
    (c * a / M) * (n : ℝ) ^ 2 * Real.sqrt n ≤ (profiles.card : ℝ) := by
  have hmass : 0 ≤ a * (n : ℝ) * Real.sqrt n := by positivity
  have houter :
      (L.card : ℝ) * (a * n * Real.sqrt n) ≤ M * (profiles.card : ℝ) :=
    fiberBound_globalProfiles_bound L order spectra profiles
      (a * n * Real.sqrt n) M hfiber hlarge hprofiles
  have hscaled :
      (c * n) * (a * n * Real.sqrt n) ≤ M * (profiles.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hL hmass).trans houter
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    (c * a / M) * (n : ℝ) ^ 2 * Real.sqrt n =
        ((c * n) * (a * n * Real.sqrt n)) / M := by ring
    _ ≤ (M * (profiles.card : ℝ)) / M :=
      (div_le_div_iff_of_pos_right hMreal).2 hscaled
    _ = (profiles.card : ℝ) := by field_simp

/-! ## From bounded multiplicity to many fixed orders -/

/-- A finite map with fibres of size at most `M` has image cardinality at
least its domain cardinality divided by `M`, in the real-valued form needed
for asymptotic constants. -/
lemma div_mul_le_card_image_of_fiberBound [DecidableEq Kappa]
    (n : ℕ) (c : ℝ) (L : Finset Iota) (order : Iota → Kappa) (M : ℕ)
    (hM : 0 < M) (hL : c * n ≤ (L.card : ℝ))
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M) :
    (c / M) * n ≤ ((L.image order).card : ℝ) := by
  have hcardNat : L.card ≤ M * (L.image order).card := by
    simpa only [orderFiber] using Finset.card_le_mul_card_image L M hfiber
  have hcardReal : (L.card : ℝ) ≤ M * ((L.image order).card : ℝ) := by
    exact_mod_cast hcardNat
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hbase : c * n ≤ ((L.image order).card : ℝ) * M := by
    simpa [mul_comm] using hL.trans hcardReal
  calc
    (c / M) * n = (c * n) / M := by ring
    _ ≤ ((L.image order).card : ℝ) := (div_le_iff₀ hMreal).2 hbase

/-- Linear-size bounded-multiplicity data yield a linear-size image of
orders, every one of which inherits the fixed-order spectrum bound.  The
single constant `min (c / M) sigma` is chosen so that the result feeds
directly into a fixed-order-spectrum statement using one constant twice. -/
theorem fiberBound_largeImage_fixedOrderSpectra [DecidableEq Kappa]
    (n : ℕ) (c sigma : ℝ) (L : Finset Iota) (order : Iota → Kappa)
    (spectra : Kappa → Finset E) (M : ℕ)
    (hM : 0 < M) (hL : c * n ≤ (L.card : ℝ))
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M)
    (hlarge : ∀ ell ∈ L,
      sigma * n * Real.sqrt n ≤ ((spectra (order ell)).card : ℝ)) :
    ∃ I : Finset Kappa,
      min (c / M) sigma * n ≤ (I.card : ℝ) ∧
        ∀ k ∈ I,
          min (c / M) sigma * n * Real.sqrt n ≤ ((spectra k).card : ℝ) := by
  refine ⟨L.image order, ?_, ?_⟩
  · calc
      min (c / M) sigma * n ≤ (c / M) * n := by
        gcongr
        exact min_le_left _ _
      _ ≤ ((L.image order).card : ℝ) :=
        div_mul_le_card_image_of_fiberBound n c L order M hM hL hfiber
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨ell, hell, rfl⟩
    calc
      min (c / M) sigma * n * Real.sqrt n ≤
          sigma * n * Real.sqrt n := by
        gcongr
        exact min_le_right _ _
      _ ≤ ((spectra (order ell)).card : ℝ) := hlarge ell hell

/-- Positive-constant packaging of
`fiberBound_largeImage_fixedOrderSpectra`. -/
theorem fiberBound_to_largeFixedOrderSpectra [DecidableEq Kappa]
    (n : ℕ) (c sigma : ℝ) (L : Finset Iota) (order : Iota → Kappa)
    (spectra : Kappa → Finset E) (M : ℕ)
    (hc : 0 < c) (hsigma : 0 < sigma) (hM : 0 < M)
    (hL : c * n ≤ (L.card : ℝ))
    (hfiber : ∀ k ∈ L.image order, (orderFiber L order k).card ≤ M)
    (hlarge : ∀ ell ∈ L,
      sigma * n * Real.sqrt n ≤ ((spectra (order ell)).card : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ ∃ I : Finset Kappa,
      d * n ≤ (I.card : ℝ) ∧
        ∀ k ∈ I,
          d * n * Real.sqrt n ≤ ((spectra k).card : ℝ) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨min (c / M) sigma, lt_min (div_pos hc hMreal) hsigma, ?_⟩
  exact fiberBound_largeImage_fixedOrderSpectra n c sigma L order spectra M
    hM hL hfiber hlarge

/-- Reindexing a sum through a map which is injective on its finite domain. -/
lemma sum_comp_eq_sum_image [DecidableEq Kappa] {R : Type*} [AddCommMonoid R]
    (I : Finset Iota) (map : Iota → Kappa) (weight : Kappa → R)
    (hmap : Set.InjOn map (I : Set Iota)) :
    ∑ i ∈ I, weight (map i) = ∑ k ∈ I.image map, weight k := by
  simpa using (Finset.sum_image hmap).symm

/-- The precise at-most-two multiplicity inequality.  If `left` and `right`
are separately injective on `I`, then summing a nonnegative weight after both
maps costs at most twice the weight of their combined image. -/
lemma sum_two_injective_maps_le_twice [DecidableEq Kappa]
    (I : Finset Iota) (left right : Iota → Kappa) (weight : Kappa → ℝ)
    (hweight : ∀ k, 0 ≤ weight k)
    (hleft : Set.InjOn left (I : Set Iota))
    (hright : Set.InjOn right (I : Set Iota)) :
    ∑ i ∈ I, (weight (left i) + weight (right i)) ≤
      2 * ∑ k ∈ representedOrders I left right, weight k := by
  have hleftSub : I.image left ⊆ representedOrders I left right := by
    exact Finset.subset_union_left
  have hrightSub : I.image right ⊆ representedOrders I left right := by
    exact Finset.subset_union_right
  have hleftSum :
      ∑ i ∈ I, weight (left i) ≤
        ∑ k ∈ representedOrders I left right, weight k := by
    rw [sum_comp_eq_sum_image I left weight hleft]
    exact Finset.sum_le_sum_of_subset_of_nonneg hleftSub
      (fun k _hk _ ↦ hweight k)
  have hrightSum :
      ∑ i ∈ I, weight (right i) ≤
        ∑ k ∈ representedOrders I left right, weight k := by
    rw [sum_comp_eq_sum_image I right weight hright]
    exact Finset.sum_le_sum_of_subset_of_nonneg hrightSub
      (fun k _hk _ ↦ hweight k)
  rw [Finset.sum_add_distrib]
  linarith

/-- Abstract two-spectrum profile bound.  If every parameter supplies a
large spectrum through at least one of two injective order maps, then the
union of tagged spectra has at least half the total promised mass. -/
theorem twoMap_spectra_bound [DecidableEq Kappa] [DecidableEq E]
    (I : Finset Iota) (left right : Iota → Kappa)
    (spectra : Kappa → Finset E) (mass : ℝ)
    (hleft : Set.InjOn left (I : Set Iota))
    (hright : Set.InjOn right (I : Set Iota))
    (hlarge : ∀ i ∈ I,
      mass ≤ ((spectra (left i)).card : ℝ) ∨
        mass ≤ ((spectra (right i)).card : ℝ)) :
    (I.card : ℝ) * mass ≤
      2 * ((taggedSpectra (representedOrders I left right) spectra).card : ℝ) := by
  let weight : Kappa → ℝ := fun k ↦ ((spectra k).card : ℝ)
  have hpoint : ∀ i ∈ I, mass ≤ weight (left i) + weight (right i) := by
    intro i hi
    rcases hlarge i hi with h | h
    · exact h.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    · exact h.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hlower :
      (I.card : ℝ) * mass ≤
        ∑ i ∈ I, (weight (left i) + weight (right i)) := by
    simpa using Finset.sum_le_sum hpoint
  have hupper := sum_two_injective_maps_le_twice I left right weight
    (fun _ ↦ Nat.cast_nonneg _) hleft hright
  have hcard :
      ((taggedSpectra (representedOrders I left right) spectra).card : ℝ) =
        ∑ k ∈ representedOrders I left right, ((spectra k).card : ℝ) := by
    exact_mod_cast card_taggedSpectra (representedOrders I left right) spectra
  calc
    (I.card : ℝ) * mass ≤
        ∑ i ∈ I, (weight (left i) + weight (right i)) := hlower
    _ ≤ 2 * ∑ k ∈ representedOrders I left right, weight k := hupper
    _ = 2 * ((taggedSpectra
        (representedOrders I left right) spectra).card : ℝ) := by
      rw [hcard]

/-- A version of `twoMap_spectra_bound` for any global profile set which
contains every relevant tagged fixed-order spectrum. -/
theorem twoMap_globalProfiles_bound [DecidableEq Kappa] [DecidableEq E]
    (I : Finset Iota) (left right : Iota → Kappa)
    (spectra : Kappa → Finset E) (profiles : Finset (Kappa × E)) (mass : ℝ)
    (hleft : Set.InjOn left (I : Set Iota))
    (hright : Set.InjOn right (I : Set Iota))
    (hlarge : ∀ i ∈ I,
      mass ≤ ((spectra (left i)).card : ℝ) ∨
        mass ≤ ((spectra (right i)).card : ℝ))
    (hprofiles : taggedSpectra (representedOrders I left right) spectra ⊆ profiles) :
    (I.card : ℝ) * mass ≤ 2 * (profiles.card : ℝ) := by
  calc
    (I.card : ℝ) * mass ≤
        2 * ((taggedSpectra (representedOrders I left right) spectra).card : ℝ) :=
      twoMap_spectra_bound I left right spectra mass hleft hright hlarge
    _ ≤ 2 * (profiles.card : ℝ) := by
      gcongr

end TwoMaps

section AffineOrders

/-- The first order in the Kwan--Sudakov profile-count reduction. -/
def firstAffineOrder (f h ell : ℕ) : ℕ :=
  ell - f + h

/-- The second order in the Kwan--Sudakov profile-count reduction. -/
def secondAffineOrder (f h ell : ℕ) : ℕ :=
  2 * (ell - f) + h

lemma firstAffineOrder_injOn (I : Finset ℕ) (f h : ℕ)
    (hf : ∀ ell ∈ I, f ≤ ell) :
    Set.InjOn (firstAffineOrder f h) (I : Set ℕ) := by
  intro x hx y hy hxy
  have hfx : f ≤ x := hf x (by simpa using hx)
  have hfy : f ≤ y := hf y (by simpa using hy)
  simp only [firstAffineOrder] at hxy
  omega

lemma secondAffineOrder_injOn (I : Finset ℕ) (f h : ℕ)
    (hf : ∀ ell ∈ I, f ≤ ell) :
    Set.InjOn (secondAffineOrder f h) (I : Set ℕ) := by
  intro x hx y hy hxy
  have hfx : f ≤ x := hf x (by simpa using hx)
  have hfy : f ≤ y := hf y (by simpa using hy)
  simp only [secondAffineOrder] at hxy
  omega

/-! ## A bounded set of offsets -/

/-- One of the two affine orders with a specified offset.  `false` denotes
the first branch and `true` the second. -/
def offsetAffineOrder (f h : ℕ) : Bool → ℕ → ℕ
  | false, ell => firstAffineOrder f h ell
  | true, ell => secondAffineOrder f h ell

/-- The order selected by parameter-dependent offset and branch functions. -/
def selectedOffsetOrder (f : ℕ) (offset : ℕ → ℕ) (branch : ℕ → Bool)
    (ell : ℕ) : ℕ :=
  offsetAffineOrder f (offset ell) (branch ell) ell

/-- If the selected offset always belongs to `H`, the selected two-branch
order map has fibres of size at most `2 * |H|`, hence at most `2 * K` when
`|H| ≤ K`. -/
lemma selectedOffsetOrder_fiberBound (L H : Finset ℕ) (K f : ℕ)
    (offset : ℕ → ℕ) (branch : ℕ → Bool)
    (hH : H.card ≤ K) (hf : ∀ ell ∈ L, f ≤ ell)
    (hoffset : ∀ ell ∈ L, offset ell ∈ H) :
    ∀ q ∈ L.image (selectedOffsetOrder f offset branch),
      (orderFiber L (selectedOffsetOrder f offset branch) q).card ≤ 2 * K := by
  intro q _hq
  let F := orderFiber L (selectedOffsetOrder f offset branch) q
  let choice : ℕ → ℕ × Bool := fun ell ↦ (offset ell, branch ell)
  have hinj : Set.InjOn choice (F : Set ℕ) := by
    intro x hx y hy hxy
    have hxF : x ∈ F := by simpa using hx
    have hyF : y ∈ F := by simpa using hy
    have hxData := mem_orderFiber.mp hxF
    have hyData := mem_orderFiber.mp hyF
    have hoffsetEq : offset x = offset y := congrArg Prod.fst hxy
    have hbranchEq : branch x = branch y := congrArg Prod.snd hxy
    have horderEq :
        selectedOffsetOrder f offset branch x =
          selectedOffsetOrder f offset branch y :=
      hxData.2.trans hyData.2.symm
    have hfx : f ≤ x := hf x hxData.1
    have hfy : f ≤ y := hf y hyData.1
    simp only [selectedOffsetOrder] at horderEq
    rw [hoffsetEq, hbranchEq] at horderEq
    cases hb : branch y <;>
      simp only [hb, offsetAffineOrder] at horderEq <;>
      simp only [firstAffineOrder, secondAffineOrder] at horderEq <;>
      omega
  have hchoiceSubset : F.image choice ⊆ H.product (Finset.univ : Finset Bool) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨ell, hell, rfl⟩
    have hellL : ell ∈ L := (mem_orderFiber.mp (by simpa [F] using hell)).1
    exact Finset.mem_product.mpr ⟨hoffset ell hellL, Finset.mem_univ _⟩
  have hcard : F.card ≤ (H.product (Finset.univ : Finset Bool)).card := by
    calc
      F.card = (F.image choice).card := by
        symm
        exact Finset.card_image_iff.mpr hinj
      _ ≤ (H.product (Finset.univ : Finset Bool)).card :=
        Finset.card_le_card hchoiceSubset
  have hcard' : F.card ≤ 2 * H.card := by
    simpa [Nat.mul_comm] using hcard
  change F.card ≤ 2 * K
  omega

/-- The corrected bounded-offset interface: parameter-dependent choices of
an offset in `H` and one of two affine branches cost at most the divisor
`2 * K`, provided `|H| ≤ K`. -/
theorem boundedOffset_globalProfiles_bound {E : Type*} [DecidableEq E]
    (L H : Finset ℕ) (K f : ℕ) (offset : ℕ → ℕ) (branch : ℕ → Bool)
    (spectra : ℕ → Finset E) (profiles : Finset (ℕ × E)) (mass : ℝ)
    (hH : H.card ≤ K) (hf : ∀ ell ∈ L, f ≤ ell)
    (hoffset : ∀ ell ∈ L, offset ell ∈ H)
    (hlarge : ∀ ell ∈ L,
      mass ≤ ((spectra (selectedOffsetOrder f offset branch ell)).card : ℝ))
    (hprofiles : taggedSpectra
      (L.image (selectedOffsetOrder f offset branch)) spectra ⊆ profiles) :
    (L.card : ℝ) * mass ≤ (2 * K) * (profiles.card : ℝ) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    fiberBound_globalProfiles_bound L (selectedOffsetOrder f offset branch)
      spectra profiles mass (2 * K)
        (selectedOffsetOrder_fiberBound L H K f offset branch hH hf hoffset)
        hlarge hprofiles

/-- Existential form of the corrected bounded-offset interface.  This is the
form produced directly by the Kwan--Sudakov profile-count reduction: for each
parameter there is an offset in `H` and at least one successful branch. -/
theorem boundedOffsetExists_globalProfiles_bound {E : Type*} [DecidableEq E]
    (L H : Finset ℕ) (K f : ℕ) (spectra : ℕ → Finset E)
    (profiles : Finset (ℕ × E)) (mass : ℝ)
    (hH : H.card ≤ K) (hf : ∀ ell ∈ L, f ≤ ell)
    (hlarge : ∀ ell ∈ L, ∃ h ∈ H,
      mass ≤ ((spectra (firstAffineOrder f h ell)).card : ℝ) ∨
        mass ≤ ((spectra (secondAffineOrder f h ell)).card : ℝ))
    (hprofiles : ∀ k, taggedSpectrum spectra k ⊆ profiles) :
    (L.card : ℝ) * mass ≤ (2 * K) * (profiles.card : ℝ) := by
  classical
  have hchoice : ∀ ell : ℕ, ∃ h : ℕ, ∃ b : Bool,
      ell ∈ L → h ∈ H ∧
        mass ≤ ((spectra (offsetAffineOrder f h b ell)).card : ℝ) := by
    intro ell
    by_cases hell : ell ∈ L
    · rcases hlarge ell hell with ⟨h, hh, hfirst | hsecond⟩
      · exact ⟨h, false, fun _ ↦ ⟨hh, hfirst⟩⟩
      · exact ⟨h, true, fun _ ↦ ⟨hh, hsecond⟩⟩
    · exact ⟨0, false, fun hell' ↦ (hell hell').elim⟩
  choose offset branch hselected using hchoice
  have hoffset : ∀ ell ∈ L, offset ell ∈ H := by
    intro ell hell
    exact (hselected ell hell).1
  have hlargeSelected : ∀ ell ∈ L,
      mass ≤ ((spectra (selectedOffsetOrder f offset branch ell)).card : ℝ) := by
    intro ell hell
    exact (hselected ell hell).2
  have hprofilesSelected : taggedSpectra
      (L.image (selectedOffsetOrder f offset branch)) spectra ⊆ profiles := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨k, _hk, hpk⟩
    exact hprofiles k hpk
  exact boundedOffset_globalProfiles_bound L H K f offset branch spectra profiles mass
    hH hf hoffset hlargeSelected hprofilesSelected

/-- The bounded-offset reduction at the scale of Problem 636. -/
theorem boundedOffset_quadraticSqrt_bound {E : Type*} [DecidableEq E]
    (n : ℕ) (c a : ℝ) (L H : Finset ℕ) (K f : ℕ)
    (offset : ℕ → ℕ) (branch : ℕ → Bool)
    (spectra : ℕ → Finset E) (profiles : Finset (ℕ × E))
    (ha : 0 ≤ a) (hK : 0 < K) (hL : c * n ≤ (L.card : ℝ))
    (hH : H.card ≤ K) (hf : ∀ ell ∈ L, f ≤ ell)
    (hoffset : ∀ ell ∈ L, offset ell ∈ H)
    (hlarge : ∀ ell ∈ L,
      a * n * Real.sqrt n ≤
        ((spectra (selectedOffsetOrder f offset branch ell)).card : ℝ))
    (hprofiles : taggedSpectra
      (L.image (selectedOffsetOrder f offset branch)) spectra ⊆ profiles) :
    (c * a / (2 * K)) * (n : ℝ) ^ 2 * Real.sqrt n ≤
      (profiles.card : ℝ) := by
  have h2K : 0 < 2 * K := by omega
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    fiberBound_quadraticSqrt_bound n c a L
      (selectedOffsetOrder f offset branch) spectra profiles (2 * K)
      ha h2K hL
      (selectedOffsetOrder_fiberBound L H K f offset branch hH hf hoffset)
      hlarge hprofiles

/-- Quadratic-square-root consequence of the existential bounded-offset
profile reduction, with the exact divisor `2 * K`. -/
theorem boundedOffsetExists_quadraticSqrt_bound {E : Type*} [DecidableEq E]
    (n : ℕ) (c a : ℝ) (L H : Finset ℕ) (K f : ℕ)
    (spectra : ℕ → Finset E) (profiles : Finset (ℕ × E))
    (ha : 0 ≤ a) (hK : 0 < K) (hL : c * n ≤ (L.card : ℝ))
    (hH : H.card ≤ K) (hf : ∀ ell ∈ L, f ≤ ell)
    (hlarge : ∀ ell ∈ L, ∃ h ∈ H,
      a * n * Real.sqrt n ≤
          ((spectra (firstAffineOrder f h ell)).card : ℝ) ∨
        a * n * Real.sqrt n ≤
          ((spectra (secondAffineOrder f h ell)).card : ℝ))
    (hprofiles : ∀ k, taggedSpectrum spectra k ⊆ profiles) :
    (c * a / (2 * K)) * (n : ℝ) ^ 2 * Real.sqrt n ≤
      (profiles.card : ℝ) := by
  have hmass : 0 ≤ a * (n : ℝ) * Real.sqrt n := by positivity
  have houter :
      (L.card : ℝ) * (a * n * Real.sqrt n) ≤
        (2 * K) * (profiles.card : ℝ) :=
    boundedOffsetExists_globalProfiles_bound L H K f spectra profiles
      (a * n * Real.sqrt n) hH hf hlarge hprofiles
  have hscaled :
      (c * n) * (a * n * Real.sqrt n) ≤
        (2 * K) * (profiles.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hL hmass).trans houter
  have h2Kreal : (0 : ℝ) < 2 * K := by positivity
  calc
    (c * a / (2 * K)) * (n : ℝ) ^ 2 * Real.sqrt n =
        ((c * n) * (a * n * Real.sqrt n)) / (2 * K) := by ring
    _ ≤ ((2 * K) * (profiles.card : ℝ)) / (2 * K) :=
      (div_le_div_iff_of_pos_right h2Kreal).2 hscaled
    _ = (profiles.card : ℝ) := by field_simp

/-- The profile bound specialized to the two affine order maps in the
Kwan--Sudakov reduction. -/
theorem affine_globalProfiles_bound {E : Type*} [DecidableEq E]
    (I : Finset ℕ) (f h : ℕ) (spectra : ℕ → Finset E)
    (profiles : Finset (ℕ × E)) (mass : ℝ)
    (hf : ∀ ell ∈ I, f ≤ ell)
    (hlarge : ∀ ell ∈ I,
      mass ≤ ((spectra (firstAffineOrder f h ell)).card : ℝ) ∨
        mass ≤ ((spectra (secondAffineOrder f h ell)).card : ℝ))
    (hprofiles : taggedSpectra
      (representedOrders I (firstAffineOrder f h) (secondAffineOrder f h)) spectra ⊆
        profiles) :
    (I.card : ℝ) * mass ≤ 2 * (profiles.card : ℝ) := by
  exact twoMap_globalProfiles_bound I (firstAffineOrder f h) (secondAffineOrder f h)
    spectra profiles mass (firstAffineOrder_injOn I f h hf)
      (secondAffineOrder_injOn I f h hf) hlarge hprofiles

/-- Quantitative outer reduction at the scale needed for Problem 636.
Linearly many parameters, each supplying `a * n * sqrt n` profiles through
one affine family, yield `(c * a / 2) * n^2 * sqrt n` global profiles. -/
theorem affine_quadraticSqrt_bound {E : Type*} [DecidableEq E]
    (n : ℕ) (c a : ℝ) (I : Finset ℕ) (f h : ℕ)
    (spectra : ℕ → Finset E) (profiles : Finset (ℕ × E))
    (ha : 0 ≤ a) (hI : c * n ≤ (I.card : ℝ))
    (hf : ∀ ell ∈ I, f ≤ ell)
    (hlarge : ∀ ell ∈ I,
      a * n * Real.sqrt n ≤
          ((spectra (firstAffineOrder f h ell)).card : ℝ) ∨
        a * n * Real.sqrt n ≤
          ((spectra (secondAffineOrder f h ell)).card : ℝ))
    (hprofiles : taggedSpectra
      (representedOrders I (firstAffineOrder f h) (secondAffineOrder f h)) spectra ⊆
        profiles) :
    (c * a / 2) * (n : ℝ) ^ 2 * Real.sqrt n ≤ (profiles.card : ℝ) := by
  have hmass : 0 ≤ a * (n : ℝ) * Real.sqrt n := by positivity
  have houter :
      (I.card : ℝ) * (a * n * Real.sqrt n) ≤ 2 * (profiles.card : ℝ) :=
    affine_globalProfiles_bound I f h spectra profiles
      (a * n * Real.sqrt n) hf hlarge hprofiles
  have hscaled :
      (c * n) * (a * n * Real.sqrt n) ≤ 2 * (profiles.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hI hmass).trans houter
  calc
    (c * a / 2) * (n : ℝ) ^ 2 * Real.sqrt n =
        ((c * n) * (a * n * Real.sqrt n)) / 2 := by ring
    _ ≤ (2 * (profiles.card : ℝ)) / 2 := by gcongr
    _ = (profiles.card : ℝ) := by ring

end AffineOrders

end Erdos636.ProfileReduction
