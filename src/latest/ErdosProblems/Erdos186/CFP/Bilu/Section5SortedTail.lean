/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonInduction
import ErdosProblems.Erdos186.GAP

/-!
# Bilu Section 5.5: bounded widths after the critical dimension

This file formalizes Proposition 5.7's packing argument.  A large subset of
the coefficient set lies in an affine plane of dimension below `d`.  One of
the first `d` coordinate directions is therefore transverse to that plane.
Translating the slice along this direction injects the product of the slice
with the corresponding coefficient interval into the twofold coefficient
box.  The resulting cardinal inequality bounds that width, and sortedness
bounds every later width.

We use the ordinary twofold GAP box, whose volume costs at most `3 ^ rank`,
instead of the source's bespoke one-coordinate doubled box.  Once the rank is
uniformly bounded this gives exactly the required uniform tail conclusion.
-/

namespace Erdos186.CFP.Bilu.Section5SortedTail

open Module Submodule
open Section7FreimanMap Section5TwoN Section5Theorem56
  Section5EpsilonInduction

noncomputable section

/-- A GAP coefficient vector, regarded as a point of real coefficient space. -/
def realCoord {ambient rank : ℕ} (P : GAP ambient rank) (c : P.Coord) :
    Fin rank → ℝ :=
  fun i ↦ (c i : ℝ)

theorem realCoord_injective {ambient rank : ℕ} (P : GAP ambient rank) :
    Function.Injective (realCoord P) := by
  intro c e h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change (((c i : ℕ) : ℝ)) = ((e i : ℕ) : ℝ) at hi
  exact_mod_cast hi

/-- The real realization of a finite set of GAP coefficient vectors. -/
def realCoordinateSet {ambient rank : ℕ} (P : GAP ambient rank)
    (K : Finset P.Coord) : Finset (Fin rank → ℝ) :=
  K.image (realCoord P)

@[simp]
theorem card_realCoordinateSet {ambient rank : ℕ} (P : GAP ambient rank)
    (K : Finset P.Coord) :
    (realCoordinateSet P K).card = K.card := by
  exact Finset.card_image_of_injective K (realCoord_injective P)

/-- The first `d` standard coordinate vectors inside real rank-space. -/
def headBasisVector {rank d : ℕ} (hd : d ≤ rank) (i : Fin d) :
    Fin rank → ℝ :=
  Pi.single (Fin.castLE hd i) 1

theorem linearIndependent_headBasisVector {rank d : ℕ} (hd : d ≤ rank) :
    LinearIndependent ℝ (headBasisVector hd) := by
  exact (Pi.linearIndependent_single_one (Fin rank) ℝ).comp
    (Fin.castLE hd) (Fin.castLE_injective hd)

/-- A subspace of dimension below `d` misses one of the first `d` standard
coordinate vectors. -/
theorem exists_headBasisVector_not_mem {rank d : ℕ} (hd : d ≤ rank)
    (L : Submodule ℝ (Fin rank → ℝ)) (hL : finrank ℝ L < d) :
    ∃ j : Fin rank, (j : ℕ) < d ∧ Pi.single j (1 : ℝ) ∉ L := by
  by_contra hnone
  push Not at hnone
  have hspan : span ℝ (Set.range (headBasisVector hd)) ≤ L := by
    rw [span_le]
    rintro x ⟨i, rfl⟩
    exact hnone (Fin.castLE hd i) i.isLt
  have hmono := Submodule.finrank_mono hspan
  have hhead : finrank ℝ (span ℝ (Set.range (headBasisVector hd))) = d := by
    rw [finrank_span_eq_card (linearIndependent_headBasisVector hd)]
    simp
  rw [hhead] at hmono
  omega

/-- The Section 5.5 packing inequality for a supplied affine slice. -/
theorem width_le_of_affineSliceWitness
    {ambient rank d proportionConstant volumeConstant : ℕ}
    (P : GAP ambient rank) (K : Finset P.Coord) (hK : K.Nonempty)
    (hd : d ≤ rank)
    (hvolume : P.volume ≤ volumeConstant * K.card)
    (W : AffineSliceWitness d proportionConstant (realCoordinateSet P K)) :
    ∃ j : Fin rank, (j : ℕ) < d ∧
      P.widths j ≤ 3 ^ rank * volumeConstant * proportionConstant := by
  classical
  obtain ⟨j, hjd, hjtransverse⟩ :=
    exists_headBasisVector_not_mem hd W.plane.direction W.dimension_lt
  let SlicePoint := {x // x ∈ W.slice}
  let sourceCoord : SlicePoint → P.Coord := fun x ↦
    Classical.choose (Finset.mem_image.mp (W.slice_subset x.property))
  have sourceCoord_spec (x : SlicePoint) : realCoord P (sourceCoord x) = x :=
    (Classical.choose_spec
      (Finset.mem_image.mp (W.slice_subset x.property))).2
  let pack : Fin (P.widths j) × SlicePoint → (P.dilate 2).Coord := fun q i ↦
    ⟨if i = j then (q.1 : ℕ) + (sourceCoord q.2 i : ℕ)
      else (sourceCoord q.2 i : ℕ), by
      by_cases hij : i = j
      · subst i
        simp only [GAP.dilate_widths, if_pos]
        have ha := q.1.isLt
        have hc := (sourceCoord q.2 j).isLt
        have hw := P.width_pos j
        omega
      · simp only [GAP.dilate_widths, if_neg hij]
        have hc := (sourceCoord q.2 i).isLt
        have hw := P.width_pos i
        omega⟩
  have pack_injective : Function.Injective pack := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hab
    have hpoint :
        (a : ℝ) • Pi.single j (1 : ℝ) + (x : Fin rank → ℝ) =
          (b : ℝ) • Pi.single j (1 : ℝ) + (y : Fin rank → ℝ) := by
      funext i
      have hi := congrArg (fun c : (P.dilate 2).Coord ↦ (c i : ℕ)) hab
      by_cases hij : i = j
      · subst i
        simp only [pack, if_pos] at hi
        change (a : ℝ) * (Pi.single j (1 : ℝ) : Fin rank → ℝ) j + x.val j =
          (b : ℝ) * (Pi.single j (1 : ℝ) : Fin rank → ℝ) j + y.val j
        rw [← congrFun (sourceCoord_spec x) j,
          ← congrFun (sourceCoord_spec y) j]
        simp only [Pi.single_eq_same, mul_one, realCoord]
        exact_mod_cast hi
      · simp only [pack, if_neg hij] at hi
        change (a : ℝ) * (Pi.single j (1 : ℝ) : Fin rank → ℝ) i + x.val i =
          (b : ℝ) * (Pi.single j (1 : ℝ) : Fin rank → ℝ) i + y.val i
        rw [← congrFun (sourceCoord_spec x) i,
          ← congrFun (sourceCoord_spec y) i]
        simp only [Pi.single_apply, hij, if_false, mul_zero, zero_add, realCoord]
        exact_mod_cast hi
    have hyx : (y : Fin rank → ℝ) - (x : Fin rank → ℝ) ∈
        W.plane.direction :=
      AffineSubspace.vsub_mem_direction (W.slice_mem_plane y y.property)
        (W.slice_mem_plane x x.property)
    have hscalar :
        ((a : ℝ) - (b : ℝ)) • Pi.single j (1 : ℝ) =
          (y : Fin rank → ℝ) - (x : Fin rank → ℝ) := by
      have haeq :
          (a : ℝ) • Pi.single j (1 : ℝ) =
            (b : ℝ) • Pi.single j (1 : ℝ) +
              (y : Fin rank → ℝ) - (x : Fin rank → ℝ) := by
        rw [eq_sub_iff_add_eq]
        exact hpoint
      rw [sub_smul]
      rw [haeq]
      abel
    have habval : (a : ℕ) = b := by
      by_contra hne
      have hscalar0 : (a : ℝ) - (b : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast hne)
      apply hjtransverse
      apply (W.plane.direction.smul_mem_iff hscalar0).mp
      rw [hscalar]
      exact hyx
    have hab' : a = b := Fin.ext habval
    subst b
    have hxy : (x : Fin rank → ℝ) = y := by
      exact add_left_cancel hpoint
    have hxy' : x = y := Subtype.ext hxy
    subst y
    rfl
  have hpackCard := Fintype.card_le_of_injective pack pack_injective
  have hcount : P.widths j * W.slice.card ≤ (P.dilate 2).volume := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Fintype.card_pi, GAP.volume, SlicePoint] using hpackCard
  have hslice : W.slice.Nonempty := by
    apply Finset.card_pos.mp
    have hKcard : 0 < K.card := Finset.card_pos.mpr hK
    have hrealcard : (realCoordinateSet P K).card = K.card :=
      card_realCoordinateSet P K
    have hcardle := W.card_le
    rw [hrealcard] at hcardle
    by_contra hz
    have : W.slice.card = 0 := Nat.eq_zero_of_not_pos hz
    rw [this, Nat.mul_zero] at hcardle
    omega
  have hmul : P.widths j * W.slice.card ≤
      (3 ^ rank * volumeConstant * proportionConstant) * W.slice.card := by
    calc
      P.widths j * W.slice.card ≤ (P.dilate 2).volume := hcount
      _ ≤ 3 ^ rank * P.volume := by
        simpa using P.volume_dilate_le 2
      _ ≤ 3 ^ rank * (volumeConstant * K.card) :=
        Nat.mul_le_mul_left _ hvolume
      _ ≤ 3 ^ rank * (volumeConstant *
          (proportionConstant * W.slice.card)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        simpa only [card_realCoordinateSet] using W.card_le
      _ = (3 ^ rank * volumeConstant * proportionConstant) * W.slice.card := by
        ring
  exact ⟨j, hjd,
    Nat.le_of_mul_le_mul_right hmul (Finset.card_pos.mpr hslice)⟩

/-- Sortedness propagates the transverse-coordinate estimate to every
coordinate at or after `d`. -/
theorem sorted_tail_width_le_of_affineSliceWitness
    {ambient rank d proportionConstant volumeConstant rankBound : ℕ}
    (P : GAP ambient rank) (K : Finset P.Coord) (hK : K.Nonempty)
    (hd : d ≤ rank) (hrank : rank ≤ rankBound)
    (hsorted : ∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
      P.widths j ≤ P.widths i)
    (hvolume : P.volume ≤ volumeConstant * K.card)
    (W : AffineSliceWitness d proportionConstant (realCoordinateSet P K)) :
    ∀ i : Fin rank, d ≤ (i : ℕ) →
      P.widths i ≤ 3 ^ rankBound * volumeConstant * proportionConstant := by
  obtain ⟨j, hjd, hjwidth⟩ :=
    width_le_of_affineSliceWitness P K hK hd hvolume W
  intro i hdi
  calc
    P.widths i ≤ P.widths j := hsorted j i (by omega)
    _ ≤ 3 ^ rank * volumeConstant * proportionConstant := hjwidth
    _ ≤ 3 ^ rankBound * volumeConstant * proportionConstant := by
      gcongr
      omega

/-- Bilu Proposition 5.7 in the uniform form needed downstream.  For fixed
critical dimension, rank bound, and linear-volume constant, this supplies a
single positive natural tail bound valid for every rank, GAP, and coefficient
set satisfying the small-doubling hypothesis.

The returned bound depends only on `d`, `rankBound`, and `volumeConstant`;
in particular it is independent of `rank`, `P`, and `K`. -/
theorem exists_uniform_tailBound
    (d rankBound volumeConstant : ℕ) (hdpos : 0 < d) :
    ∃ tailBound : ℕ, 0 < tailBound ∧
      ∀ {ambient rank : ℕ} (P : GAP ambient rank) (K : Finset P.Coord),
        K.Nonempty → d ≤ rank → rank ≤ rankBound →
        (∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
          P.widths j ≤ P.widths i) →
        P.volume ≤ volumeConstant * K.card →
        (pairSumset (realCoordinateSet P K)).card <
          (2 * d - 1) * (realCoordinateSet P K).card →
        ∀ i : Fin rank, d ≤ (i : ℕ) → P.widths i ≤ tailBound := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_constant_affineSlice d hdpos
  let tailBound := 3 ^ rankBound * volumeConstant * proportionConstant + 1
  refine ⟨tailBound, by simp [tailBound], ?_⟩
  intro ambient rank P K hK hdrank hrank hsorted hvolume hdouble
  have hfinrank : d ≤ finrank ℝ (Fin rank → ℝ) := by
    simpa using hdrank
  obtain ⟨W⟩ := hslice (Fin rank → ℝ) hfinrank
    (realCoordinateSet P K) (hK.image _) hdouble
  intro i hdi
  exact (sorted_tail_width_le_of_affineSliceWitness P K hK hdrank hrank
    hsorted hvolume W i hdi).trans (Nat.le_succ _)

end

end Erdos186.CFP.Bilu.Section5SortedTail

#print axioms Erdos186.CFP.Bilu.Section5SortedTail.exists_headBasisVector_not_mem
#print axioms Erdos186.CFP.Bilu.Section5SortedTail.width_le_of_affineSliceWitness
#print axioms Erdos186.CFP.Bilu.Section5SortedTail.exists_uniform_tailBound
