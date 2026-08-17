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
import ErdosProblems.Erdos13.Erdos13Additive
import ErdosProblems.Erdos54.LevStructure

/-!
# The dense-sumset interval input for Erdős Problem 54

This file develops the interval-producing part of Lev's theorem on sums of
many dense integer sets.  The central two-set lemma below is Lemma 1 in
Lev's proof: two normalized finite sets whose total number of holes is small
have an explicitly determined interval in their sumset.

All statements are over `ℕ`, which is the specialization used by the
Conlon--Fox--Pham construction (the summands there are sets of subset sums).
-/

open Finset Nat
open scoped Pointwise

namespace Erdos54

open Erdos13Additive
open LevStructure

/-! ## Primitive sets and finite iterated sumsets -/

/-- A finite natural-number set is not contained in a translate of
`d * ℤ` for any `d > 1`.  For a finite integer set this is equivalent to
not being contained in an arithmetic progression of common difference
greater than one. -/
def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ d : ℕ, 1 < d → ¬ Erdos13Additive.InOneResidue A d

/-- For a set containing zero, primitivity is exactly the existence, for
every nontrivial modulus, of an element not divisible by that modulus. -/
theorem isPrimitive_iff_not_all_dvd {A : Finset ℕ} (hzero : 0 ∈ A) :
    IsPrimitive A ↔ ∀ d : ℕ, 1 < d → ∃ a ∈ A, ¬d ∣ a := by
  constructor
  · intro hprim d hd
    by_contra hnot
    push Not at hnot
    apply hprim d hd
    refine ⟨0, ?_⟩
    intro a ha
    exact (ZMod.natCast_eq_zero_iff a d).mpr (hnot a ha)
  · intro h d hd hres
    obtain ⟨r, hr⟩ := hres
    have hrzero : r = 0 := by
      simpa using (hr 0 hzero).symm
    obtain ⟨a, ha, hda⟩ := h d hd
    apply hda
    apply (ZMod.natCast_eq_zero_iff a d).mp
    simpa [hrzero] using hr a ha

/-- A primitive finite set containing a positive element has integer gcd
one.  This is the bridge from the progression formulation used by CFP to
the subgroup formulation in Kneser's theorem. -/
theorem gcd_eq_one_of_isPrimitive {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (hapos : 0 < a) (hprim : IsPrimitive A) :
    A.gcd (fun x : ℕ ↦ x) = 1 := by
  let d := A.gcd (fun x : ℕ ↦ x)
  have hda : d ∣ a := Finset.gcd_dvd ha
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    rw [hd0] at hda
    have ha0 : a = 0 := by simpa using hda
    omega
  by_contra hd1
  have hdgt : 1 < d := by omega
  apply hprim d hdgt
  refine ⟨0, ?_⟩
  intro x hx
  apply (ZMod.natCast_eq_zero_iff x d).mpr
  exact Finset.gcd_dvd hx

theorem int_gcd_eq_one_of_isPrimitive {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (hapos : 0 < a) (hprim : IsPrimitive A) :
    A.gcd (fun x ↦ (x : ℤ)) = 1 := by
  rw [Erdos13Additive.nat_int_finset_gcd,
    gcd_eq_one_of_isPrimitive ha hapos hprim]
  norm_num

/-- The residues of a primitive set cannot all lie in the stabilizer of a
proper nonempty modular sumset. -/
theorem modImage_not_subset_addStab_of_primitive
    {A : Finset ℕ} {L : ℕ} [NeZero L] {W : Finset (ZMod L)}
    (hL : 0 < L) (hLA : L ∈ A)
    (hprim : IsPrimitive A) (hW0 : (0 : ZMod L) ∈ W)
    (hWproper : W ≠ (Finset.univ : Finset (ZMod L))) :
    ¬ modImage A L ⊆ W.addStab := by
  intro hsub
  have hWne : W.Nonempty := ⟨0, hW0⟩
  let K : AddSubgroup (ZMod L) :=
    AddAction.stabilizer (ZMod L) (W : Set (ZMod L))
  have hHK : (W.addStab : Set (ZMod L)) = (K : Set (ZMod L)) := by
    exact coe_addStab hWne
  have hAK : ∀ a ∈ A, (a : ZMod L) ∈ K := by
    intro a ha
    have haH : (a : ZMod L) ∈ W.addStab :=
      hsub (mem_modImage.mpr ⟨a, ha, rfl⟩)
    have haHs : (a : ZMod L) ∈ (W.addStab : Set (ZMod L)) := haH
    rw [hHK] at haHs
    exact haHs
  have hKtop := stabilizer_eq_top_of_gcd_one
    (int_gcd_eq_one_of_isPrimitive hLA hL hprim) K hAK
  have hHuniv : W.addStab = (Finset.univ : Finset (ZMod L)) := by
    ext x
    simp only [mem_univ, iff_true]
    have hxK : x ∈ K := by rw [hKtop]; trivial
    have hxKs : x ∈ (K : Set (ZMod L)) := hxK
    rw [← hHK] at hxKs
    exact hxKs
  apply hWproper
  apply Subset.antisymm (subset_univ W)
  intro x hx
  have hxH : x ∈ W.addStab := by simpa [hHuniv]
  have hxsum : x ∈ W + W.addStab :=
    mem_add.mpr ⟨0, hW0, x, hxH, by simp⟩
  simpa only [add_addStab] using hxsum

/-- In the proper modular case there is a final-sum residue lying outside
the stabilizer saturation of the prefix residues. -/
theorem exists_residue_outside_prefix_saturation
    {C A : Finset ℕ} {L : ℕ} [NeZero L] (hL : 0 < L)
    (hC0 : 0 ∈ C) (hA0 : 0 ∈ A) (hLA : L ∈ A)
    (hprim : IsPrimitive A)
    (hproper : modImage (C + A) L ≠ (Finset.univ : Finset (ZMod L))) :
    let C₀ := modImage C L
    let A₀ := modImage A L
    let W := C₀ + A₀
    let H := W.addStab
    ∃ c ∈ W, c ∉ C₀ + H := by
  dsimp only
  let C₀ := modImage C L
  let A₀ := modImage A L
  let W := C₀ + A₀
  let H := W.addStab
  have hC₀0 : (0 : ZMod L) ∈ C₀ := zero_mem_modImage hC0
  have hA₀0 : (0 : ZMod L) ∈ A₀ := zero_mem_modImage hA0
  have hW0 : (0 : ZMod L) ∈ W := mem_add.mpr ⟨0, hC₀0, 0, hA₀0, by simp⟩
  have hWne : W.Nonempty := ⟨0, hW0⟩
  have hproperW : W ≠ (Finset.univ : Finset (ZMod L)) := by
    intro h
    apply hproper
    rw [modImage_add C A L]
    exact h
  have hnotA : ¬ A₀ ⊆ H :=
    modImage_not_subset_addStab_of_primitive hL hLA hprim hW0 hproperW
  have hCsubW : C₀ ⊆ W := by
    intro c hc
    exact mem_add.mpr ⟨c, hc, 0, hA₀0, by simp⟩
  have hCsatW : C₀ + H ⊆ W := by
    have hs := add_subset_add hCsubW (subset_rfl : H ⊆ H)
    change C₀ + H ⊆ W + W.addStab at hs
    simpa only [add_addStab] using hs
  by_contra hn
  push_neg at hn
  have hWsub : W ⊆ C₀ + H := fun c hc ↦ hn c hc
  have hWeq : W = C₀ + H := Subset.antisymm hWsub hCsatW
  apply hnotA
  intro a ha
  apply (mem_addStab hWne).mpr
  have htrans : a +ᵥ W ⊆ W := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_vadd_finset.mp hz
    rw [hWeq] at hw
    obtain ⟨c, hc, h, hh, hch⟩ := mem_add.mp hw
    have hcaw : c + a ∈ W := mem_add.mpr ⟨c, hc, a, ha, rfl⟩
    have hzsum : a + (c + h) ∈ W + H := by
      apply mem_add.mpr
      refine ⟨c + a, hcaw, h, hh, ?_⟩
      abel
    dsimp only [vadd_eq_add]
    rw [← hch]
    change a + (c + h) ∈ W + W.addStab at hzsum
    simpa only [add_addStab] using hzsum
  apply Finset.eq_of_subset_of_card_le htrans
  rw [card_vadd_finset]

/-- The Minkowski sum of a list of finite natural-number sets. -/
def listSum : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | A :: As => A + listSum As

@[simp] theorem listSum_nil : listSum [] = {0} := rfl

@[simp] theorem listSum_cons (A : Finset ℕ) (As : List (Finset ℕ)) :
    listSum (A :: As) = A + listSum As := rfl

private theorem singleton_zero_add (S : Finset ℕ) : ({0} : Finset ℕ) + S = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    have ha0 : a = 0 := by simpa using ha
    subst a
    have hbx : b = x := by omega
    simpa [hbx] using hb
  · intro hx
    exact Finset.mem_add.mpr ⟨0, by simp, x, hx, by simp⟩

@[simp] theorem listSum_singleton (A : Finset ℕ) : listSum [A] = A := by
  rw [listSum_cons, listSum_nil]
  simpa only [add_comm] using singleton_zero_add A

theorem listSum_append (As Bs : List (Finset ℕ)) :
    listSum (As ++ Bs) = listSum As + listSum Bs := by
  induction As with
  | nil => exact (singleton_zero_add _).symm
  | cons A As ih => simp only [List.cons_append, listSum_cons, ih]
                    rw [add_assoc]

theorem listSum_eq_of_perm {As Bs : List (Finset ℕ)} (h : As.Perm Bs) :
    listSum As = listSum Bs := by
  induction h with
  | nil => rfl
  | cons A h ih => simp only [listSum_cons, ih]
  | swap A B As => simp only [listSum_cons]; ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Reduction modulo `L` commutes with an iterated integer sumset. -/
theorem modImage_listSum (As : List (Finset ℕ)) (L : ℕ) :
    modImage (listSum As) L =
      groupListSum (As.map fun A ↦ modImage A L) := by
  induction As with
  | nil => simp [listSum, groupListSum, modImage]
  | cons A As ih =>
      simp only [listSum_cons, List.map_cons, groupListSum_cons, ← ih]
      exact modImage_add A (listSum As) L

/-- Membership in a list sumset is equivalent to choosing one member of
each summand. -/
theorem mem_groupListSum_iff
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {As : List (Finset G)} {z : G} :
    z ∈ groupListSum As ↔
      ∃ xs : List G, xs.length = As.length ∧
        List.Forall₂ (fun A x ↦ x ∈ A) As xs ∧ xs.sum = z := by
  induction As generalizing z with
  | nil =>
      constructor
      · intro hz
        have hz0 : z = 0 := by simpa [groupListSum] using hz
        exact ⟨[], rfl, .nil, by simpa [hz0]⟩
      · rintro ⟨xs, hlen, -, hsum⟩
        have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst xs
        simpa [groupListSum] using hsum.symm
  | cons A As ih =>
      constructor
      · intro hz
        obtain ⟨a, ha, t, ht, hat⟩ := Finset.mem_add.mp hz
        obtain ⟨xs, hlen, hrel, hsum⟩ := ih.mp ht
        refine ⟨a :: xs, by simp [hlen], .cons ha hrel, ?_⟩
        simp only [List.sum_cons]
        rw [hsum, hat]
      · rintro ⟨xs, hlen, hrel, hsum⟩
        cases xs with
        | nil => simp at hlen
        | cons a xs =>
            have hrel' := List.forall₂_cons.mp hrel
            apply Finset.mem_add.mpr
            refine ⟨a, hrel'.1, xs.sum, ih.mpr ⟨xs, ?_, hrel'.2, rfl⟩, ?_⟩
            · simpa using hlen
            · simpa using hsum

theorem listSum_nonempty {As : List (Finset ℕ)}
    (hne : ∀ A ∈ As, A.Nonempty) : (listSum As).Nonempty := by
  induction As with
  | nil => simp [listSum]
  | cons A As ih =>
      rw [listSum_cons, Finset.add_nonempty]
      exact ⟨hne A (by simp), ih fun B hB ↦ hne B (by simp [hB])⟩

/-- The variable-cardinality iterated Cauchy--Davenport estimate. -/
theorem sum_cards_sub_length_add_one_le_listSum {As : List (Finset ℕ)}
    (hne : ∀ A ∈ As, A.Nonempty) :
    (As.map Finset.card).sum - As.length + 1 ≤ (listSum As).card := by
  induction As with
  | nil => simp [listSum]
  | cons A As ih =>
      have hA : A.Nonempty := hne A (by simp)
      have htail : ∀ B ∈ As, B.Nonempty := fun B hB ↦ hne B (by simp [hB])
      have hS : (listSum As).Nonempty := listSum_nonempty htail
      have hc := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hS
      have hi := ih htail
      rw [listSum_cons]
      change A.card + (listSum As).card - 1 ≤ (A + listSum As).card at hc
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hAc : 0 < A.card := card_pos.mpr hA
      have hSc : 0 < (listSum As).card := card_pos.mpr hS
      omega

theorem zero_mem_listSum {As : List (Finset ℕ)}
    (hzero : ∀ A ∈ As, 0 ∈ A) : 0 ∈ listSum As := by
  induction As with
  | nil => simp [listSum]
  | cons A As ih =>
      apply Finset.mem_add.mpr
      exact ⟨0, hzero A (by simp), 0, ih fun B hB ↦ hzero B (by simp [hB]), by simp⟩

/-- A sum of `k` sets contained in `[0,Q]` is contained in `[0,kQ]`. -/
theorem listSum_subset_Icc {As : List (Finset ℕ)} {Q : ℕ}
    (hbound : ∀ A ∈ As, A ⊆ Icc 0 Q) :
    listSum As ⊆ Icc 0 (As.length * Q) := by
  induction As with
  | nil => simp [listSum]
  | cons A As ih =>
      rw [listSum_cons]
      have hA : A ⊆ Icc 0 Q := hbound A (by simp)
      have hAs : listSum As ⊆ Icc 0 (As.length * Q) :=
        ih fun B hB ↦ hbound B (by simp [hB])
      have hadd := Erdos13Additive.add_subset_ambient hA hAs
      simpa [List.length_cons, Nat.succ_mul, add_comm] using hadd

/-- The iterated Cauchy--Davenport lower bound in the integers. -/
theorem card_listSum_lower {As : List (Finset ℕ)} {n : ℕ}
    (hn : 1 ≤ n) (hcard : ∀ A ∈ As, n ≤ A.card) :
    As.length * (n - 1) + 1 ≤ (listSum As).card := by
  induction As with
  | nil => simp [listSum]
  | cons A As ih =>
      have hAc : n ≤ A.card := hcard A (by simp)
      have hAne : A.Nonempty := card_pos.mp (by omega)
      have htailcard : ∀ B ∈ As, n ≤ B.card :=
        fun B hB ↦ hcard B (by simp [hB])
      have htailne : (listSum As).Nonempty := by
        apply listSum_nonempty
        intro B hB
        exact card_pos.mp (by have := htailcard B hB; omega)
      have hcauchy :=
        cauchy_davenport_add_of_linearOrder_isCancelAdd hAne htailne
      have hind := ih htailcard
      rw [listSum_cons]
      change A.card + (listSum As).card - 1 ≤ (A + listSum As).card at hcauchy
      simp only [List.length_cons, Nat.succ_mul]
      omega

private theorem natListSum_eq_listSum (As : List (Finset ℕ)) :
    natListSum As = listSum As := by
  induction As with
  | nil => rfl
  | cons A As ih => simp only [natListSum_cons, listSum_cons, ih]

private theorem length_le_sum_cards {As : List (Finset ℕ)}
    (hne : ∀ A ∈ As, A.Nonempty) :
    As.length ≤ (As.map Finset.card).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
      have hA : 1 ≤ A.card := card_pos.mpr (hne A (by simp))
      have ht : As.length ≤ (As.map Finset.card).sum :=
        ih fun B hB ↦ hne B (by simp [hB])
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-! ## Lev's multiple-addition increment -/

/-- The multiple-addition theorem of Lev in the normalized form used by
CFP.  The last summand contains both `0` and the modulus `L` and is
primitive.  The gain over the prefix is the smaller of `L` and the total
number of modular degrees of freedom of all summands.

This proof is the stabilizer/fiber argument of Lev's 1997 addendum.  In the
proper modular case, Kneser's stabilizer deficit is paid exactly by one
selected integer fiber in every summand. -/
theorem lev_multiple_increment
    {Bs : List (Finset ℕ)} {B : Finset ℕ} {L : ℕ}
    (hL : 0 < L) (hzero : ∀ A ∈ Bs, 0 ∈ A)
    (hB0 : 0 ∈ B) (hLB : L ∈ B) (hprim : IsPrimitive B) :
    let all := Bs ++ [B]
    (listSum Bs).card +
        min L ((all.map fun A ↦ (modImage A L).card).sum - all.length + 1) ≤
      (listSum all).card := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  dsimp only
  let all := Bs ++ [B]
  let C := listSum Bs
  let S := C + B
  let mods := all.map fun A ↦ modImage A L
  let W := groupListSum mods
  let H := W.addStab
  have hC0 : 0 ∈ C := zero_mem_listSum hzero
  have hallzero : ∀ A ∈ all, 0 ∈ A := by
    intro A hA
    simp only [all, List.mem_append, List.mem_singleton] at hA
    rcases hA with hA | rfl
    · exact hzero A hA
    · exact hB0
  have hallne : ∀ A ∈ all, A.Nonempty := by
    intro A hA
    exact ⟨0, hallzero A hA⟩
  have hmodsne : ∀ A₀ ∈ mods, A₀.Nonempty := by
    intro A₀ hA₀
    simp only [mods, List.mem_map] at hA₀
    obtain ⟨A, hA, rfl⟩ := hA₀
    exact modImage_nonempty (hallne A hA)
  have hallnonempty : all ≠ [] := by simp [all]
  have hmodsnil : mods ≠ [] := by simp [mods, all]
  have hsum : listSum all = S := by
    simp only [all, listSum_append, listSum_singleton, S, C]
  have hWimage : W = modImage S L := by
    calc
      W = modImage (listSum all) L := (modImage_listSum all L).symm
      _ = modImage S L := by rw [hsum]
  have hW0 : (0 : ZMod L) ∈ W := by
    rw [hWimage]
    exact zero_mem_modImage (by simpa [S] using Finset.add_mem_add hC0 hB0)
  have hWne : W.Nonempty := ⟨0, hW0⟩
  have hH0 : (0 : ZMod L) ∈ H := zero_mem_addStab hWne
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hWne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hWne hx
  by_cases hwhole : modImage S L = (Finset.univ : Finset (ZMod L))
  · have himagecard : (modImage S L).card = L := by
      rw [hwhole]
      simp [ZMod.card]
    have hlift := card_add_modImage_add_card_le
      (C := C) (B := B) hL hB0 hLB
    change (modImage S L).card + C.card ≤ S.card at hlift
    rw [himagecard] at hlift
    rw [hsum]
    exact (Nat.add_le_add_left (min_le_left _ _) C.card).trans (by omega)
  · have hproper : W ≠ (Finset.univ : Finset (ZMod L)) := by
      rw [hWimage]
      exact hwhole
    obtain ⟨c, hcW, hcSat⟩ :=
      exists_residue_outside_prefix_saturation hL hC0 hB0 hLB hprim (by
        simpa [S] using hwhole)
    have hHbin : H = (modImage C L + modImage B L).addStab := by
      change W.addStab = _
      rw [hWimage]
      simp only [S, modImage_add]
    have hcW' : c ∈ W := by
      rw [hWimage]
      simpa [S, modImage_add] using hcW
    have hcSat' : c ∉ modImage C L + H := by
      rw [hHbin]
      exact hcSat
    obtain ⟨as, haslen, halignMods, hasum⟩ :=
      mem_groupListSum_iff.mp hcW'
    have halign : List.Forall₂ (fun A a ↦ a ∈ modImage A L) all as := by
      exact List.forall₂_map_left_iff.mp halignMods
    let fibers := selectedResidueFibers all as H
    let F := natListSum fibers
    let D := c +ᵥ H
    have hfiberslen : fibers.length = all.length :=
      selectedResidueFibers_length halign
    have hfibersne : ∀ R ∈ fibers, R.Nonempty :=
      selectedResidueFibers_nonempty hH0 halign
    have hFsubAll : F ⊆ listSum all := by
      rw [← natListSum_eq_listSum all]
      exact natListSum_selectedResidueFibers_subset halign
    have hFsub : F ⊆ S := by simpa only [hsum] using hFsubAll
    have hFres : ∀ z ∈ F, (z : ZMod L) ∈ D := by
      intro z hz
      have hz' := natListSum_selectedResidueFibers_cast_mem hH0 hHadd halign z hz
      rw [hasum] at hz'
      exact hz'
    have hDsub : D ⊆ modImage S L := by
      rw [← hWimage]
      have hs : c +ᵥ H ⊆ W + H := vadd_finset_subset_add hcW'
      change c +ᵥ H ⊆ W + W.addStab at hs
      simpa only [add_addStab] using hs
    have hCsat : modImage C L ⊆ modImage C L + H := by
      intro x hx
      exact mem_add.mpr ⟨x, hx, 0, hH0, by simp⟩
    have hDdisjSat : Disjoint D (modImage C L + H) :=
      disjoint_vadd_add_of_not_mem hHadd hHneg hcSat'
    have hDdisjC : Disjoint D (modImage C L) :=
      hDdisjSat.mono_right hCsat
    have hDcard : D.card = H.card := card_vadd_finset c H
    have hrefined := card_modImage_add_card_add_fiber_le
      (C := C) (B := B) (F := F) D hL hB0 hLB
      (by simpa [S] using hDsub) hDdisjC (by simpa [S] using hFsub) hFres
    have hrefined' : W.card + C.card + F.card ≤ S.card + H.card := by
      rw [← hWimage, hDcard] at hrefined
      simpa only [S] using hrefined
    have hkneser := groupListSum_kneser hmodsnil hmodsne
    change (mods.map fun A₀ ↦ (A₀ + H).card).sum ≤
      W.card + (mods.length - 1) * H.card at hkneser
    have hkneser' :
        (all.map fun A ↦ (modImage A L + H).card).sum ≤
          W.card + (all.length - 1) * H.card := by
      dsimp only [mods] at hkneser
      simpa only [List.map_map, List.length_map, Function.comp_def] using hkneser
    have haggregate :=
      sum_modImage_cards_add_length_mul_card_le_saturated_add_fibers hH0 halign
    change (all.map fun A ↦ (modImage A L).card).sum + all.length * H.card ≤
      (all.map fun A ↦ (modImage A L + H).card).sum +
        (fibers.map Finset.card).sum at haggregate
    have hcauchy := sum_cards_sub_length_add_one_le_listSum hfibersne
    have hsumfib :
        (fibers.map Finset.card).sum - fibers.length + 1 ≤ F.card := by
      change (fibers.map Finset.card).sum - fibers.length + 1 ≤
        (natListSum fibers).card
      rw [natListSum_eq_listSum]
      exact hcauchy
    have hsumfiblen : fibers.length ≤ (fibers.map Finset.card).sum :=
      length_le_sum_cards hfibersne
    have hmodsumlen :
        all.length ≤ (all.map fun A ↦ (modImage A L).card).sum := by
      have hm : (mods.map Finset.card).length ≤
          (mods.map Finset.card).sum := by
        apply List.length_le_sum_of_one_le
        intro k hk
        simp only [List.mem_map] at hk
        obtain ⟨A₀, hA₀, rfl⟩ := hk
        exact card_pos.mpr (hmodsne A₀ hA₀)
      dsimp only [mods] at hm
      simpa only [List.length_map, List.map_map, Function.comp_def] using hm
    have halllen : 1 ≤ all.length := by simp [all]
    have hmul : all.length * H.card =
        (all.length - 1) * H.card + H.card := by
      calc
        all.length * H.card = ((all.length - 1) + 1) * H.card := by
          rw [Nat.sub_add_cancel halllen]
        _ = (all.length - 1) * H.card + H.card := by
          rw [Nat.add_mul, one_mul]
    rw [hsum]
    change C.card +
        min L ((all.map fun A ↦ (modImage A L).card).sum - all.length + 1) ≤
      S.card
    apply (Nat.add_le_add_left (min_le_right _ _) C.card).trans
    rw [hfiberslen] at hsumfib hsumfiblen
    have hsubfib :
        (fibers.map Finset.card).sum - all.length + all.length =
          (fibers.map Finset.card).sum :=
      Nat.sub_add_cancel hsumfiblen
    have hsubmods :
        (all.map fun A ↦ (modImage A L).card).sum - all.length + all.length =
          (all.map fun A ↦ (modImage A L).card).sum :=
      Nat.sub_add_cancel hmodsumlen
    omega

/-! ## Sorted-list consequences of the increment theorem -/

/-- The right endpoint of a normalized finite natural-number set. -/
def setTop (A : Finset ℕ) : ℕ := A.sup id

theorem mem_setTop {A : Finset ℕ} (hA : A.Nonempty) : setTop A ∈ A := by
  have h := Finset.sup_mem_of_nonempty (f := id) hA
  simpa [setTop] using h

theorem subset_Icc_setTop (A : Finset ℕ) : A ⊆ Icc 0 (setTop A) := by
  intro a ha
  apply mem_Icc.mpr
  refine ⟨Nat.zero_le a, ?_⟩
  change a ≤ A.sup id
  exact Finset.le_sup (f := fun x : ℕ ↦ x) ha

theorem card_le_setTop_add_one (A : Finset ℕ) : A.card ≤ setTop A + 1 := by
  simpa using card_le_card (subset_Icc_setTop A)

/-- The sum of the right endpoints of a list of normalized sets. -/
def topSum (As : List (Finset ℕ)) : ℕ :=
  (As.map setTop).sum

theorem listSum_subset_Icc_topSum (As : List (Finset ℕ)) :
    listSum As ⊆ Icc 0 (topSum As) := by
  induction As with
  | nil => simp [listSum, topSum]
  | cons A As ih =>
      rw [listSum_cons]
      have h := Erdos13Additive.add_subset_ambient (subset_Icc_setTop A) ih
      simpa [topSum, add_comm] using h

/-- Indexed sum of the gains supplied by `lev_multiple_increment`. -/
def levGainAux (d k : ℕ) : List (Finset ℕ) → ℕ
  | [] => 0
  | A :: As => min (setTop A) ((k + 1) * d + 1) + levGainAux d (k + 1) As

private theorem card_sub_one_le_modImage_of_subset
    {A : Finset ℕ} {L : ℕ} (hL : 0 < L)
    (hA : A ⊆ Icc 0 L) (hA0 : 0 ∈ A) :
    A.card - 1 ≤ (modImage A L).card := by
  by_cases hLA : L ∈ A
  · have h := card_modImage_add_one_eq hL hA hA0 hLA
    omega
  · have hA' : A ⊆ Icc 0 (L - 1) := by
      intro a ha
      have haI := mem_Icc.mp (hA ha)
      have haL : a ≠ L := fun h ↦ hLA (h ▸ ha)
      exact mem_Icc.mpr ⟨haI.1, by omega⟩
    have h := card_modImage_eq_card_of_lt hA' (by omega : L - 1 < L)
    omega

private theorem length_mul_le_sum_of_forall
    {As : List (Finset ℕ)} {f : Finset ℕ → ℕ} {r : ℕ}
    (h : ∀ A ∈ As, r ≤ f A) : As.length * r ≤ (As.map f).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
      have hA := h A (by simp)
      have ht := ih fun B hB ↦ h B (by simp [hB])
      simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
      omega

private theorem lev_increment_uniform
    {Bs : List (Finset ℕ)} {B : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hsorted : ∀ A ∈ Bs, setTop A ≤ setTop B)
    (hzero : ∀ A ∈ Bs, 0 ∈ A) (hB0 : 0 ∈ B)
    (hcard : ∀ A ∈ Bs, n ≤ A.card) (hBcard : n ≤ B.card)
    (hprim : IsPrimitive B) :
    (listSum Bs).card +
        min (setTop B) ((Bs.length + 1) * (n - 2) + 1) ≤
      (listSum (Bs ++ [B])).card := by
  let L := setTop B
  have hBne : B.Nonempty := ⟨0, hB0⟩
  have hLB : L ∈ B := mem_setTop hBne
  have hBtop := card_le_setTop_add_one B
  have hL : 0 < L := by omega
  have hallzero : ∀ A ∈ Bs ++ [B], 0 ∈ A := by
    intro A hA
    simp only [List.mem_append, List.mem_singleton] at hA
    rcases hA with hA | rfl
    · exact hzero A hA
    · exact hB0
  have hallcard : ∀ A ∈ Bs ++ [B], n ≤ A.card := by
    intro A hA
    simp only [List.mem_append, List.mem_singleton] at hA
    rcases hA with hA | rfl
    · exact hcard A hA
    · exact hBcard
  have hmod : ∀ A ∈ Bs ++ [B], n - 1 ≤ (modImage A L).card := by
    intro A hA
    have hAtop : setTop A ≤ L := by
      simp only [List.mem_append, List.mem_singleton] at hA
      rcases hA with hA | rfl
      · exact hsorted A hA
      · exact le_rfl
    have hAI : A ⊆ Icc 0 L := by
      intro a ha
      have haI := mem_Icc.mp (subset_Icc_setTop A ha)
      exact mem_Icc.mpr ⟨haI.1, haI.2.trans hAtop⟩
    have hm := card_sub_one_le_modImage_of_subset hL hAI (hallzero A hA)
    have hc := hallcard A hA
    omega
  have hsum := length_mul_le_sum_of_forall hmod
  have hraw := lev_multiple_increment (Bs := Bs) (B := B) hL hzero hB0 hLB hprim
  have hlen : (Bs ++ [B]).length = Bs.length + 1 := by simp
  have hnm : (Bs.length + 1) * (n - 1) =
      (Bs.length + 1) * (n - 2) + (Bs.length + 1) := by
    have hn' : n - 1 = (n - 2) + 1 := by omega
    rw [hn', Nat.mul_add, mul_one]
  have hgain : (Bs.length + 1) * (n - 2) + 1 ≤
      (((Bs ++ [B]).map fun A ↦ (modImage A L).card).sum -
        (Bs ++ [B]).length + 1) := by
    rw [hlen] at hsum ⊢
    omega
  have hmin : min L ((Bs.length + 1) * (n - 2) + 1) ≤
      min L (((Bs ++ [B]).map fun A ↦ (modImage A L).card).sum -
        (Bs ++ [B]).length + 1) := min_le_min le_rfl hgain
  dsimp only [L] at hraw hmin ⊢
  omega

private theorem levGainAux_card
    {Prefix Rest : List (Finset ℕ)} {n : ℕ} (hn : 3 ≤ n)
    (hsorted : (Prefix ++ Rest).Pairwise
      (fun A B ↦ setTop A ≤ setTop B))
    (hzero : ∀ A ∈ Prefix ++ Rest, 0 ∈ A)
    (hcard : ∀ A ∈ Prefix ++ Rest, n ≤ A.card)
    (hprim : ∀ A ∈ Prefix ++ Rest, IsPrimitive A) :
    (listSum Prefix).card + levGainAux (n - 2) Prefix.length Rest ≤
      (listSum (Prefix ++ Rest)).card := by
  induction Rest generalizing Prefix with
  | nil => simp [levGainAux]
  | cons A Rest ih =>
      have hsplit := List.pairwise_append.mp hsorted
      have hPA : ∀ P ∈ Prefix, setTop P ≤ setTop A := by
        intro P hP
        exact hsplit.2.2 P hP A (by simp)
      have hPzero : ∀ P ∈ Prefix, 0 ∈ P := by
        intro P hP
        exact hzero P (by simp [hP])
      have hPcard : ∀ P ∈ Prefix, n ≤ P.card := by
        intro P hP
        exact hcard P (by simp [hP])
      have hA0 : 0 ∈ A := hzero A (by simp)
      have hAcard : n ≤ A.card := hcard A (by simp)
      have hAprim : IsPrimitive A := hprim A (by simp)
      have hstep := lev_increment_uniform hn hPA hPzero hA0 hPcard hAcard hAprim
      have ih' := ih (Prefix := Prefix ++ [A])
        (by simpa [List.append_assoc] using hsorted)
        (by simpa [List.append_assoc] using hzero)
        (by simpa [List.append_assoc] using hcard)
        (by simpa [List.append_assoc] using hprim)
      simp only [levGainAux, List.length_append, List.length_singleton] at ih' ⊢
      simpa only [List.append_assoc, List.singleton_append] using (show
        (listSum Prefix).card +
              (min (setTop A) ((Prefix.length + 1) * (n - 2) + 1) +
                levGainAux (n - 2) (Prefix.length + 1) Rest) ≤
            (listSum ((Prefix ++ [A]) ++ Rest)).card by omega)

/-- A sorted normalized list gains the sum of all of Lev's indexed
increments. -/
theorem lev_sorted_density
    {As : List (Finset ℕ)} {n : ℕ} (hn : 3 ≤ n)
    (hsorted : As.Pairwise (fun A B ↦ setTop A ≤ setTop B))
    (hzero : ∀ A ∈ As, 0 ∈ A)
    (hcard : ∀ A ∈ As, n ≤ A.card)
    (hprim : ∀ A ∈ As, IsPrimitive A) :
    1 + levGainAux (n - 2) 0 As ≤ (listSum As).card := by
  simpa [listSum] using
    (levGainAux_card (Prefix := []) hn hsorted hzero hcard hprim)

/-! ## The two-set box principle -/

/-- The two-set interval lemma from Lev's proof, in normalized natural
coordinates.  The endpoints are inclusive, so the displayed interval has
`2 * (A.card + B.card - 2) - (L₁ + L₂) + 1` elements when nonempty.

The proof is entirely finitary.  A missing sum to the left or right of the
middle interval would force more holes in `A` and `B` than their total
number of holes. -/
theorem dense_pair_interval_of_le
    {A B : Finset ℕ} {L₁ L₂ : ℕ}
    (hL : L₂ ≤ L₁)
    (hA : A ⊆ Icc 0 L₁) (hB : B ⊆ Icc 0 L₂)
    (hcards : 2 ≤ A.card + B.card)
    (hdense : L₁ ≤ A.card + B.card - 2) :
    Icc (L₁ + L₂ - (A.card + B.card - 2))
        (A.card + B.card - 2) ⊆ A + B := by
  have hAcard : A.card ≤ L₁ + 1 := by
    simpa using card_le_card hA
  have hBcard : B.card ≤ L₂ + 1 := by
    simpa using card_le_card hB
  have hAh := Erdos13Additive.card_holes hA
  have hBh := Erdos13Additive.card_holes hB
  have hAhAdd : (Erdos13Additive.holes A L₁).card + A.card = L₁ + 1 := by
    omega
  have hBhAdd : (Erdos13Additive.holes B L₂).card + B.card = L₂ + 1 := by
    omega
  have hmiddle : Icc L₂ L₁ ⊆ A + B := by
    apply Erdos13Additive.middle_interval_subset_sum hL hA hB
    omega
  intro g hg
  have hgI := mem_Icc.mp hg
  by_contra hgsum
  by_cases hgL₂ : g < L₂
  · have hp := Erdos13Additive.prefix_hole_count hA hB (by omega) hgsum
    have hpA :
        (Erdos13Additive.holesIcc A 0 g).card ≤
          (Erdos13Additive.holes A L₁).card :=
      Erdos13Additive.card_holesIcc_le_card_holes (by omega) (by omega)
    have hpB :
        (Erdos13Additive.holesIcc B 0 g).card ≤
          (Erdos13Additive.holes B L₂).card :=
      Erdos13Additive.card_holesIcc_le_card_holes (by omega) (by omega)
    omega
  · by_cases hgL₁ : g ≤ L₁
    · exact hgsum (hmiddle (mem_Icc.mpr ⟨by omega, hgL₁⟩))
    · have hs := Erdos13Additive.suffix_hole_count hL (by omega) (by omega) hgsum
      have hsA :
          (Erdos13Additive.holesIcc A (g - L₂) L₁).card ≤
            (Erdos13Additive.holes A L₁).card :=
        Erdos13Additive.card_holesIcc_le_card_holes (by omega) (by omega)
      have hsB :
          (Erdos13Additive.holesIcc B (g - L₁) L₂).card ≤
            (Erdos13Additive.holes B L₂).card :=
        Erdos13Additive.card_holesIcc_le_card_holes (by omega) (by omega)
      omega

/-- Symmetric form of `dense_pair_interval_of_le`. -/
theorem dense_pair_interval
    {A B : Finset ℕ} {L₁ L₂ : ℕ}
    (hA : A ⊆ Icc 0 L₁) (hB : B ⊆ Icc 0 L₂)
    (hcards : 2 ≤ A.card + B.card)
    (hdense : max L₁ L₂ ≤ A.card + B.card - 2) :
    Icc (L₁ + L₂ - (A.card + B.card - 2))
        (A.card + B.card - 2) ⊆ A + B := by
  rcases le_total L₂ L₁ with hL | hL
  · exact dense_pair_interval_of_le hL hA hB hcards
      ((le_max_left L₁ L₂).trans hdense)
  · have h := dense_pair_interval_of_le (A := B) (B := A)
      (L₁ := L₂) (L₂ := L₁) hL hB hA (by omega)
      (by rw [add_comm (a := B.card) A.card]
          exact (le_max_right L₁ L₂).trans hdense)
    simpa only [add_comm (a := L₂) L₁, add_comm (a := B) A,
      add_comm (a := B.card) A.card] using h

/-! ## Extending an interval by another summand -/

/-- If a sumset already contains an interval at least as long as the distance
between two elements of a new summand, adding the new summand joins the two
endpoint translates into one larger interval.

This is the deterministic extension step used after Lev's initial long block
has been found.  It is also the elementary last step in Lev's Corollary 1. -/
theorem interval_add_of_endpoints
    {S T : Finset ℕ} {lo hi a b : ℕ}
    (hlohi : lo ≤ hi) (hab : a ≤ b)
    (hlen : b - a ≤ hi + 1 - lo)
    (ha : a ∈ T) (hb : b ∈ T)
    (hinterval : Icc lo hi ⊆ S) :
    Icc (lo + a) (hi + b) ⊆ S + T := by
  intro z hz
  have hzI := mem_Icc.mp hz
  by_cases hza : z ≤ hi + a
  · have haz : a ≤ z := by omega
    apply Finset.mem_add.mpr
    refine ⟨z - a, hinterval (mem_Icc.mpr ⟨by omega, by omega⟩), a, ha, ?_⟩
    omega
  · have hbz : b ≤ z := by omega
    apply Finset.mem_add.mpr
    refine ⟨z - b, hinterval (mem_Icc.mpr ⟨by omega, by omega⟩), b, hb, ?_⟩
    omega

/-- The normalized form of `interval_add_of_endpoints`, where the new
summand contains both endpoints of `[0,L]`. -/
theorem interval_add_normalized
    {S T : Finset ℕ} {lo hi L : ℕ}
    (hlohi : lo ≤ hi) (hlen : L ≤ hi + 1 - lo)
    (hzero : 0 ∈ T) (hL : L ∈ T)
    (hinterval : Icc lo hi ⊆ S) :
    Icc lo (hi + L) ⊆ S + T := by
  simpa using interval_add_of_endpoints hlohi (Nat.zero_le L)
    (by simpa using hlen) hzero hL hinterval

/-! ## The fixed numerical inequality for forty summands -/

private theorem min_pair_bound {d rd sd x y : ℕ}
    (hrd : d ≤ rd) (hrs : rd + sd = 18 * d) (hsd : 9 * d ≤ sd)
    (hxd : d ≤ x) (hxy : x ≤ y) (hy : y ≤ 17 * d) :
    x + y + 2 * d ≤ 2 * min x rd + 2 * min y sd := by
  simp only [Nat.min_def]
  split <;> split <;> omega

private theorem min_late_bound {d cutoff x : ℕ}
    (hi : 9 * d ≤ cutoff) (hxd : d ≤ x) (hx : x ≤ 17 * d) :
    x + d ≤ 2 * min x cutoff := by
  simp only [Nat.min_def]
  split <;> omega

private theorem min_pair_bound_succ {d rd sd x y : ℕ}
    (hrd : d + 1 ≤ rd) (hrs : rd + sd = 18 * d + 2)
    (hsd : 9 * d + 1 ≤ sd) (hxd : d + 1 ≤ x)
    (hxy : x ≤ y) (hy : y ≤ 17 * d + 1) :
    x + y + 2 * (d + 1) ≤ 2 * min x rd + 2 * min y sd := by
  simp only [Nat.min_def]
  split <;> split <;> omega

private theorem min_late_bound_succ {d cutoff x : ℕ}
    (hi : 9 * d + 1 ≤ cutoff) (hxd : d + 1 ≤ x)
    (hx : x ≤ 17 * d + 1) :
    x + (d + 1) ≤ 2 * min x cutoff := by
  simp only [Nat.min_def]
  split <;> omega

/-- Fixed, recursion-free arithmetic form of Proposition 1(ii) in Lev's
argument.  Keeping the twenty variables explicit avoids unfolding a large
`Fin` sum during elaboration. -/
theorem twenty_min_sum_bound
    (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 : ℕ)
    (hlo : d + 1 ≤ x0)
    (h01 : x0 ≤ x1) (h12 : x1 ≤ x2) (h23 : x2 ≤ x3)
    (h34 : x3 ≤ x4) (h45 : x4 ≤ x5) (h56 : x5 ≤ x6)
    (h67 : x6 ≤ x7) (h78 : x7 ≤ x8) (h89 : x8 ≤ x9)
    (h9a : x9 ≤ x10) (hab : x10 ≤ x11) (hbc : x11 ≤ x12)
    (hcd : x12 ≤ x13) (hde : x13 ≤ x14) (hef : x14 ≤ x15)
    (hfg : x15 ≤ x16) (hgh : x16 ≤ x17) (hhi' : x17 ≤ x18)
    (hij : x18 ≤ x19) (hhi : x19 ≤ 17 * d + 1) :
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 +
        x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + 20 * (d + 1) ≤
      2 * (min x0 (d + 1) + min x1 (2 * d + 1) +
        min x2 (3 * d + 1) + min x3 (4 * d + 1) +
        min x4 (5 * d + 1) + min x5 (6 * d + 1) +
        min x6 (7 * d + 1) + min x7 (8 * d + 1) +
        min x8 (9 * d + 1) + min x9 (10 * d + 1) +
        min x10 (11 * d + 1) + min x11 (12 * d + 1) +
        min x12 (13 * d + 1) + min x13 (14 * d + 1) +
        min x14 (15 * d + 1) + min x15 (16 * d + 1) +
        min x16 (17 * d + 1) + min x17 (18 * d + 1) +
        min x18 (19 * d + 1) + min x19 (20 * d + 1)) := by
  have p1 := min_pair_bound_succ (d := d) (rd := d + 1)
    (sd := 17 * d + 1) (x := x0) (y := x16)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p2 := min_pair_bound_succ (d := d) (rd := 2 * d + 1)
    (sd := 16 * d + 1) (x := x1) (y := x15)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p3 := min_pair_bound_succ (d := d) (rd := 3 * d + 1)
    (sd := 15 * d + 1) (x := x2) (y := x14)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p4 := min_pair_bound_succ (d := d) (rd := 4 * d + 1)
    (sd := 14 * d + 1) (x := x3) (y := x13)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p5 := min_pair_bound_succ (d := d) (rd := 5 * d + 1)
    (sd := 13 * d + 1) (x := x4) (y := x12)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p6 := min_pair_bound_succ (d := d) (rd := 6 * d + 1)
    (sd := 12 * d + 1) (x := x5) (y := x11)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p7 := min_pair_bound_succ (d := d) (rd := 7 * d + 1)
    (sd := 11 * d + 1) (x := x6) (y := x10)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p8 := min_pair_bound_succ (d := d) (rd := 8 * d + 1)
    (sd := 10 * d + 1) (x := x7) (y := x9)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have q9 := min_late_bound_succ (d := d) (cutoff := 9 * d + 1)
    (x := x8) (by omega) (by omega) (by omega)
  have q18 := min_late_bound_succ (d := d) (cutoff := 18 * d + 1)
    (x := x17) (by omega) (by omega) (by omega)
  have q19 := min_late_bound_succ (d := d) (cutoff := 19 * d + 1)
    (x := x18) (by omega) (by omega) (by omega)
  have q20 := min_late_bound_succ (d := d) (cutoff := 20 * d + 1)
    (x := x19) (by omega) (by omega) (by omega)
  omega

/-! ## Alternating halves and the forty-set corollary -/

/-- Split a list into its even- and odd-positioned entries. -/
def alternatingSplit {α : Type*} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: xs =>
      let p := alternatingSplit xs
      (a :: p.1, b :: p.2)

@[simp] theorem alternatingSplit_nil {α : Type*} :
    alternatingSplit ([] : List α) = ([], []) := rfl

@[simp] theorem alternatingSplit_singleton {α : Type*} (a : α) :
    alternatingSplit [a] = ([a], []) := rfl

@[simp] theorem alternatingSplit_cons_cons {α : Type*} (a b : α) (xs : List α) :
    alternatingSplit (a :: b :: xs) =
      (a :: (alternatingSplit xs).1, b :: (alternatingSplit xs).2) := by
  rfl

theorem alternatingSplit_perm {α : Type*} (xs : List α) :
    List.Perm ((alternatingSplit xs).1 ++ (alternatingSplit xs).2) xs := by
  induction xs using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b xs ih =>
      simp only [alternatingSplit_cons_cons, Prod.fst, Prod.snd, List.cons_append]
      exact List.Perm.cons a (List.perm_middle.trans (List.Perm.cons b ih))

theorem alternatingSplit_fst_sublist {α : Type*} (xs : List α) :
    List.Sublist (alternatingSplit xs).1 xs := by
  induction xs using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b xs ih =>
      simp only [alternatingSplit_cons_cons, Prod.fst]
      exact (ih.cons b).cons_cons a

theorem alternatingSplit_snd_sublist {α : Type*} (xs : List α) :
    List.Sublist (alternatingSplit xs).2 xs := by
  induction xs using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b xs ih =>
      simp only [alternatingSplit_cons_cons, Prod.snd]
      exact (ih.cons_cons b).cons a

theorem alternatingSplit_lengths {α : Type*} {xs : List α} {k : ℕ}
    (hlen : xs.length = 2 * k) :
    (alternatingSplit xs).1.length = k ∧
      (alternatingSplit xs).2.length = k := by
  induction k generalizing xs with
  | zero =>
      have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs
      simp
  | succ k ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          cases xs with
          | nil => simp at hlen; omega
          | cons b xs =>
              have htail : xs.length = 2 * k := by simp at hlen; omega
              have ht := ih htail
              simp only [alternatingSplit_cons_cons, Prod.fst, Prod.snd,
                List.length_cons]
              omega

/- The first direct encoding of the twenty-term calculation is retained as
documentation below.  The checked theorem following it uses two ten-term
chunks, which is definitionally identical but substantially lighter for the
elaborator. -/
/-
private def setList20
    (A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17
      A18 A19 : Finset ℕ) : List (Finset ℕ) :=
  [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14,
    A15, A16, A17, A18, A19]

private theorem twenty_gain_bound_explicit
    (A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17
      A18 A19 : Finset ℕ) (d : ℕ)
    (hsorted : (setList20 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13
      A14 A15 A16 A17 A18 A19).Pairwise
        (fun A B ↦ setTop A ≤ setTop B))
    (hlo0 : d + 1 ≤ setTop A0)
    (hhi19 : setTop A19 ≤ 17 * d + 1) :
    topSum (setList20 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
        A15 A16 A17 A18 A19) + 20 * (d + 1) ≤
      2 * levGainAux d 0 (setList20 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11
        A12 A13 A14 A15 A16 A17 A18 A19) := by
  dsimp only [setList20] at hsorted ⊢
  have h01 : setTop A0 ≤ setTop A1 :=
    (List.pairwise_cons.mp hsorted).1 A1 (by simp)
  have hs1 := (List.pairwise_cons.mp hsorted).2
  have h12 : setTop A1 ≤ setTop A2 :=
    (List.pairwise_cons.mp hs1).1 A2 (by simp)
  have hs2 := (List.pairwise_cons.mp hs1).2
  have h23 : setTop A2 ≤ setTop A3 :=
    (List.pairwise_cons.mp hs2).1 A3 (by simp)
  have hs3 := (List.pairwise_cons.mp hs2).2
  have h34 : setTop A3 ≤ setTop A4 :=
    (List.pairwise_cons.mp hs3).1 A4 (by simp)
  have hs4 := (List.pairwise_cons.mp hs3).2
  have h45 : setTop A4 ≤ setTop A5 :=
    (List.pairwise_cons.mp hs4).1 A5 (by simp)
  have hs5 := (List.pairwise_cons.mp hs4).2
  have h56 : setTop A5 ≤ setTop A6 :=
    (List.pairwise_cons.mp hs5).1 A6 (by simp)
  have hs6 := (List.pairwise_cons.mp hs5).2
  have h67 : setTop A6 ≤ setTop A7 :=
    (List.pairwise_cons.mp hs6).1 A7 (by simp)
  have hs7 := (List.pairwise_cons.mp hs6).2
  have h78 : setTop A7 ≤ setTop A8 :=
    (List.pairwise_cons.mp hs7).1 A8 (by simp)
  have hs8 := (List.pairwise_cons.mp hs7).2
  have h89 : setTop A8 ≤ setTop A9 :=
    (List.pairwise_cons.mp hs8).1 A9 (by simp)
  have hs9 := (List.pairwise_cons.mp hs8).2
  have h9a : setTop A9 ≤ setTop A10 :=
    (List.pairwise_cons.mp hs9).1 A10 (by simp)
  have hs10 := (List.pairwise_cons.mp hs9).2
  have hab : setTop A10 ≤ setTop A11 :=
    (List.pairwise_cons.mp hs10).1 A11 (by simp)
  have hs11 := (List.pairwise_cons.mp hs10).2
  have hbc : setTop A11 ≤ setTop A12 :=
    (List.pairwise_cons.mp hs11).1 A12 (by simp)
  have hs12 := (List.pairwise_cons.mp hs11).2
  have hcd : setTop A12 ≤ setTop A13 :=
    (List.pairwise_cons.mp hs12).1 A13 (by simp)
  have hs13 := (List.pairwise_cons.mp hs12).2
  have hde : setTop A13 ≤ setTop A14 :=
    (List.pairwise_cons.mp hs13).1 A14 (by simp)
  have hs14 := (List.pairwise_cons.mp hs13).2
  have hef : setTop A14 ≤ setTop A15 :=
    (List.pairwise_cons.mp hs14).1 A15 (by simp)
  have hs15 := (List.pairwise_cons.mp hs14).2
  have hfg : setTop A15 ≤ setTop A16 :=
    (List.pairwise_cons.mp hs15).1 A16 (by simp)
  have hs16 := (List.pairwise_cons.mp hs15).2
  have hgh : setTop A16 ≤ setTop A17 :=
    (List.pairwise_cons.mp hs16).1 A17 (by simp)
  have hs17 := (List.pairwise_cons.mp hs16).2
  have hhi' : setTop A17 ≤ setTop A18 :=
    (List.pairwise_cons.mp hs17).1 A18 (by simp)
  have hs18 := (List.pairwise_cons.mp hs17).2
  have hij : setTop A18 ≤ setTop A19 :=
    (List.pairwise_cons.mp hs18).1 A19 (by simp)
  have h := twenty_min_sum_bound d
    (setTop A0) (setTop A1) (setTop A2) (setTop A3) (setTop A4)
    (setTop A5) (setTop A6) (setTop A7) (setTop A8) (setTop A9)
    (setTop A10) (setTop A11) (setTop A12) (setTop A13) (setTop A14)
    (setTop A15) (setTop A16) (setTop A17) (setTop A18) (setTop A19)
    hlo0 h01 h12 h23 h34 h45 h56 h67 h78 h89 h9a hab hbc hcd hde hef hfg hgh
    hhi' hij hhi19
  simp only [topSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    levGainAux] at ⊢
  omega

private theorem twenty_gain_bound
    {As : List (Finset ℕ)} {d : ℕ}
    (hlen : As.length = 20)
    (hsorted : As.Pairwise (fun A B ↦ setTop A ≤ setTop B))
    (hlo : ∀ A ∈ As, d + 1 ≤ setTop A)
    (hhi : ∀ A ∈ As, setTop A ≤ 17 * d + 1) :
    topSum As + 20 * (d + 1) ≤ 2 * levGainAux d 0 As := by
  rcases As with _ | ⟨A0, As⟩
  · simp at hlen
  rcases As with _ | ⟨A1, As⟩
  · simp at hlen
  rcases As with _ | ⟨A2, As⟩
  · simp at hlen
  rcases As with _ | ⟨A3, As⟩
  · simp at hlen
  rcases As with _ | ⟨A4, As⟩
  · simp at hlen
  rcases As with _ | ⟨A5, As⟩
  · simp at hlen
  rcases As with _ | ⟨A6, As⟩
  · simp at hlen
  rcases As with _ | ⟨A7, As⟩
  · simp at hlen
  rcases As with _ | ⟨A8, As⟩
  · simp at hlen
  rcases As with _ | ⟨A9, As⟩
  · simp at hlen
  rcases As with _ | ⟨A10, As⟩
  · simp at hlen
  rcases As with _ | ⟨A11, As⟩
  · simp at hlen
  rcases As with _ | ⟨A12, As⟩
  · simp at hlen
  rcases As with _ | ⟨A13, As⟩
  · simp at hlen
  rcases As with _ | ⟨A14, As⟩
  · simp at hlen
  rcases As with _ | ⟨A15, As⟩
  · simp at hlen
  rcases As with _ | ⟨A16, As⟩
  · simp at hlen
  rcases As with _ | ⟨A17, As⟩
  · simp at hlen
  rcases As with _ | ⟨A18, As⟩
  · simp at hlen
  rcases As with _ | ⟨A19, As⟩
  · simp at hlen
  have hnil : As = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst As
  apply twenty_gain_bound_explicit A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11
    A12 A13 A14 A15 A16 A17 A18 A19 d hsorted
  · exact hlo A0 (by simp)
  · exact hhi A19 (by simp)
-/

theorem topSum_append (As Bs : List (Finset ℕ)) :
    topSum (As ++ Bs) = topSum As + topSum Bs := by
  simp [topSum, List.map_append, List.sum_append]

theorem levGainAux_append (d k : ℕ) (As Bs : List (Finset ℕ)) :
    levGainAux d k (As ++ Bs) =
      levGainAux d k As + levGainAux d (k + As.length) Bs := by
  induction As generalizing k with
  | nil => simp [levGainAux]
  | cons A As ih =>
      simp only [List.cons_append, levGainAux, List.length_cons]
      rw [ih]
      have hk : k + (As.length + 1) = k + 1 + As.length := by omega
      rw [hk]
      omega

/-- The exact twenty-summand density calculation used in Lev's alternating
partition argument. -/
theorem twenty_gain_bound
    {As : List (Finset ℕ)} {d : ℕ}
    (hlen : As.length = 20)
    (hsorted : As.Pairwise (fun A B ↦ setTop A ≤ setTop B))
    (hlo : ∀ A ∈ As, d + 1 ≤ setTop A)
    (hhi : ∀ A ∈ As, setTop A ≤ 17 * d + 1) :
    topSum As + 20 * (d + 1) ≤ 2 * levGainAux d 0 As := by
  rcases As with _ | ⟨A0, As⟩
  · simp at hlen
  rcases As with _ | ⟨A1, As⟩
  · simp at hlen
  rcases As with _ | ⟨A2, As⟩
  · simp at hlen
  rcases As with _ | ⟨A3, As⟩
  · simp at hlen
  rcases As with _ | ⟨A4, As⟩
  · simp at hlen
  rcases As with _ | ⟨A5, As⟩
  · simp at hlen
  rcases As with _ | ⟨A6, As⟩
  · simp at hlen
  rcases As with _ | ⟨A7, As⟩
  · simp at hlen
  rcases As with _ | ⟨A8, As⟩
  · simp at hlen
  rcases As with _ | ⟨A9, As⟩
  · simp at hlen
  rcases As with _ | ⟨A10, As⟩
  · simp at hlen
  rcases As with _ | ⟨A11, As⟩
  · simp at hlen
  rcases As with _ | ⟨A12, As⟩
  · simp at hlen
  rcases As with _ | ⟨A13, As⟩
  · simp at hlen
  rcases As with _ | ⟨A14, As⟩
  · simp at hlen
  rcases As with _ | ⟨A15, As⟩
  · simp at hlen
  rcases As with _ | ⟨A16, As⟩
  · simp at hlen
  rcases As with _ | ⟨A17, As⟩
  · simp at hlen
  rcases As with _ | ⟨A18, As⟩
  · simp at hlen
  rcases As with _ | ⟨A19, As⟩
  · simp at hlen
  have hnil : As = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst As
  have hlo0 : d + 1 ≤ setTop A0 := hlo A0 (by simp)
  have hhi19 : setTop A19 ≤ 17 * d + 1 := hhi A19 (by simp)
  have h01 : setTop A0 ≤ setTop A1 :=
    (List.pairwise_cons.mp hsorted).1 A1 (by simp)
  have hs1 := (List.pairwise_cons.mp hsorted).2
  have h12 : setTop A1 ≤ setTop A2 :=
    (List.pairwise_cons.mp hs1).1 A2 (by simp)
  have hs2 := (List.pairwise_cons.mp hs1).2
  have h23 : setTop A2 ≤ setTop A3 :=
    (List.pairwise_cons.mp hs2).1 A3 (by simp)
  have hs3 := (List.pairwise_cons.mp hs2).2
  have h34 : setTop A3 ≤ setTop A4 :=
    (List.pairwise_cons.mp hs3).1 A4 (by simp)
  have hs4 := (List.pairwise_cons.mp hs3).2
  have h45 : setTop A4 ≤ setTop A5 :=
    (List.pairwise_cons.mp hs4).1 A5 (by simp)
  have hs5 := (List.pairwise_cons.mp hs4).2
  have h56 : setTop A5 ≤ setTop A6 :=
    (List.pairwise_cons.mp hs5).1 A6 (by simp)
  have hs6 := (List.pairwise_cons.mp hs5).2
  have h67 : setTop A6 ≤ setTop A7 :=
    (List.pairwise_cons.mp hs6).1 A7 (by simp)
  have hs7 := (List.pairwise_cons.mp hs6).2
  have h78 : setTop A7 ≤ setTop A8 :=
    (List.pairwise_cons.mp hs7).1 A8 (by simp)
  have hs8 := (List.pairwise_cons.mp hs7).2
  have h89 : setTop A8 ≤ setTop A9 :=
    (List.pairwise_cons.mp hs8).1 A9 (by simp)
  have hs9 := (List.pairwise_cons.mp hs8).2
  have h9a : setTop A9 ≤ setTop A10 :=
    (List.pairwise_cons.mp hs9).1 A10 (by simp)
  have hs10 := (List.pairwise_cons.mp hs9).2
  have hab : setTop A10 ≤ setTop A11 :=
    (List.pairwise_cons.mp hs10).1 A11 (by simp)
  have hs11 := (List.pairwise_cons.mp hs10).2
  have hbc : setTop A11 ≤ setTop A12 :=
    (List.pairwise_cons.mp hs11).1 A12 (by simp)
  have hs12 := (List.pairwise_cons.mp hs11).2
  have hcd : setTop A12 ≤ setTop A13 :=
    (List.pairwise_cons.mp hs12).1 A13 (by simp)
  have hs13 := (List.pairwise_cons.mp hs12).2
  have hde : setTop A13 ≤ setTop A14 :=
    (List.pairwise_cons.mp hs13).1 A14 (by simp)
  have hs14 := (List.pairwise_cons.mp hs13).2
  have hef : setTop A14 ≤ setTop A15 :=
    (List.pairwise_cons.mp hs14).1 A15 (by simp)
  have hs15 := (List.pairwise_cons.mp hs14).2
  have hfg : setTop A15 ≤ setTop A16 :=
    (List.pairwise_cons.mp hs15).1 A16 (by simp)
  have hs16 := (List.pairwise_cons.mp hs15).2
  have hgh : setTop A16 ≤ setTop A17 :=
    (List.pairwise_cons.mp hs16).1 A17 (by simp)
  have hs17 := (List.pairwise_cons.mp hs16).2
  have hhi' : setTop A17 ≤ setTop A18 :=
    (List.pairwise_cons.mp hs17).1 A18 (by simp)
  have hs18 := (List.pairwise_cons.mp hs17).2
  have hij : setTop A18 ≤ setTop A19 :=
    (List.pairwise_cons.mp hs18).1 A19 (by simp)
  have harith := twenty_min_sum_bound d
    (setTop A0) (setTop A1) (setTop A2) (setTop A3) (setTop A4)
    (setTop A5) (setTop A6) (setTop A7) (setTop A8) (setTop A9)
    (setTop A10) (setTop A11) (setTop A12) (setTop A13) (setTop A14)
    (setTop A15) (setTop A16) (setTop A17) (setTop A18) (setTop A19)
    hlo0 h01 h12 h23 h34 h45 h56 h67 h78 h89 h9a hab hbc hcd hde hef hfg hgh
    hhi' hij hhi19
  let L₁ : List (Finset ℕ) := [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9]
  let L₂ : List (Finset ℕ) := [A10, A11, A12, A13, A14, A15, A16, A17, A18, A19]
  have htop := topSum_append L₁ L₂
  have hgain := levGainAux_append d 0 L₁ L₂
  have htop₁ : topSum L₁ = setTop A0 + setTop A1 + setTop A2 + setTop A3 +
      setTop A4 + setTop A5 + setTop A6 + setTop A7 + setTop A8 + setTop A9 := by
    simp [L₁, topSum] <;> omega
  have htop₂ : topSum L₂ = setTop A10 + setTop A11 + setTop A12 + setTop A13 +
      setTop A14 + setTop A15 + setTop A16 + setTop A17 + setTop A18 + setTop A19 := by
    simp [L₂, topSum] <;> omega
  have hgain₁ : levGainAux d 0 L₁ =
      min (setTop A0) (d + 1) + min (setTop A1) (2*d + 1) +
      min (setTop A2) (3*d + 1) + min (setTop A3) (4*d + 1) +
      min (setTop A4) (5*d + 1) + min (setTop A5) (6*d + 1) +
      min (setTop A6) (7*d + 1) + min (setTop A7) (8*d + 1) +
      min (setTop A8) (9*d + 1) + min (setTop A9) (10*d + 1) := by
    simp [L₁, levGainAux] <;> omega
  have hgain₂ : levGainAux d 10 L₂ =
      min (setTop A10) (11*d + 1) + min (setTop A11) (12*d + 1) +
      min (setTop A12) (13*d + 1) + min (setTop A13) (14*d + 1) +
      min (setTop A14) (15*d + 1) + min (setTop A15) (16*d + 1) +
      min (setTop A16) (17*d + 1) + min (setTop A17) (18*d + 1) +
      min (setTop A18) (19*d + 1) + min (setTop A19) (20*d + 1) := by
    simp [L₂, levGainAux] <;> omega
  change topSum (L₁ ++ L₂) + 20 * (d + 1) ≤
    2 * levGainAux d 0 (L₁ ++ L₂)
  rw [htop, hgain, htop₁, htop₂, hgain₁]
  have hlen₁ : L₁.length = 10 := by simp [L₁]
  rw [hlen₁, zero_add, hgain₂]
  omega

/-- The two alternating halves of an even sorted list have ordered endpoint
sums, and their difference is at most the width of the ambient interval. -/
theorem alternatingSplit_topSum_balance
    {As : List (Finset ℕ)} {k lo Q : ℕ}
    (hlen : As.length = 2 * k)
    (hsorted : As.Pairwise (fun A B ↦ setTop A ≤ setTop B))
    (hloQ : lo ≤ Q)
    (hlo : ∀ A ∈ As, lo ≤ setTop A)
    (hhi : ∀ A ∈ As, setTop A ≤ Q) :
    topSum (alternatingSplit As).1 ≤ topSum (alternatingSplit As).2 ∧
      topSum (alternatingSplit As).2 + lo ≤
        topSum (alternatingSplit As).1 + Q := by
  induction k generalizing As lo with
  | zero =>
      have hnil : As = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst As
      simp [topSum, hloQ]
  | succ k ih =>
      cases As with
      | nil => simp at hlen
      | cons A As =>
          cases As with
          | nil => simp at hlen; omega
          | cons B As =>
              have htail : As.length = 2 * k := by simp at hlen; omega
              have hsB := (List.pairwise_cons.mp hsorted).2
              have hAB : setTop A ≤ setTop B :=
                (List.pairwise_cons.mp hsorted).1 B (by simp)
              have hsTail := (List.pairwise_cons.mp hsB).2
              have hBtail : ∀ C ∈ As, setTop B ≤ setTop C :=
                (List.pairwise_cons.mp hsB).1
              have hhiTail : ∀ C ∈ As, setTop C ≤ Q := by
                intro C hC
                exact hhi C (by simp [hC])
              have hBQ : setTop B ≤ Q := hhi B (by simp)
              have hrec := ih htail hsTail hBQ hBtail hhiTail
              have hloA : lo ≤ setTop A := hlo A (by simp)
              simp only [alternatingSplit_cons_cons, Prod.fst, Prod.snd, topSum,
                List.map_cons, List.sum_cons] at ⊢
              change
                setTop A + topSum (alternatingSplit As).1 ≤
                    setTop B + topSum (alternatingSplit As).2 ∧
                  setTop B + topSum (alternatingSplit As).2 + lo ≤
                    setTop A + topSum (alternatingSplit As).1 + Q
              omega

/-- Each sorted twenty-set half has enough density for the final two-set
box principle. -/
theorem twenty_listSum_density
    {As : List (Finset ℕ)} {n : ℕ}
    (hn : 3 ≤ n) (hlen : As.length = 20)
    (hsorted : As.Pairwise (fun A B ↦ setTop A ≤ setTop B))
    (hzero : ∀ A ∈ As, 0 ∈ A)
    (hcard : ∀ A ∈ As, n ≤ A.card)
    (hprim : ∀ A ∈ As, IsPrimitive A)
    (hupper : ∀ A ∈ As, setTop A ≤ 17 * (n - 2) + 1) :
    topSum As + 20 * (n - 1) + 2 ≤ 2 * (listSum As).card := by
  have hdensity := lev_sorted_density hn hsorted hzero hcard hprim
  have hlo : ∀ A ∈ As, n - 2 + 1 ≤ setTop A := by
    intro A hA
    have hc := hcard A hA
    have ht := card_le_setTop_add_one A
    omega
  have harith := twenty_gain_bound hlen hsorted hlo hupper
  have hnm : n - 1 = n - 2 + 1 := by omega
  rw [hnm]
  omega

/-- Lev's forty-set interval theorem in the exact specialization used by
Conlon--Fox--Pham.  The interval is inclusive, hence has
`40 * (n - 1) + 1` consecutive integers. -/
theorem lev_forty_interval
    (As : List (Finset ℕ)) (n Q : ℕ)
    (hlen : As.length = 40)
    (hn : 3 ≤ n)
    (hcard : ∀ A ∈ As, n ≤ A.card)
    (hbound : ∀ A ∈ As, A ⊆ Icc 0 Q)
    (hzero : ∀ A ∈ As, 0 ∈ A)
    (hprim : ∀ A ∈ As, IsPrimitive A)
    (hratio : Q - 1 ≤ 17 * (n - 2)) :
    ∃ L, Icc L (L + 40 * (n - 1)) ⊆ listSum As := by
  let rel : Finset ℕ → Finset ℕ → Prop := fun A B ↦ setTop A ≤ setTop B
  let sorted := As.mergeSort (fun A B ↦ setTop A ≤ setTop B)
  have hsperm : sorted.Perm As := by
    exact List.mergeSort_perm As (fun A B ↦ setTop A ≤ setTop B)
  have hslen : sorted.length = 40 := by
    rw [hsperm.length_eq, hlen]
  have hsmem : ∀ A ∈ sorted, A ∈ As := by
    intro A hA
    exact hsperm.mem_iff.mp hA
  have hszero : ∀ A ∈ sorted, 0 ∈ A := by
    intro A hA
    exact hzero A (hsmem A hA)
  have hscard : ∀ A ∈ sorted, n ≤ A.card := by
    intro A hA
    exact hcard A (hsmem A hA)
  have hsprim : ∀ A ∈ sorted, IsPrimitive A := by
    intro A hA
    exact hprim A (hsmem A hA)
  have hstopQ : ∀ A ∈ sorted, setTop A ≤ Q := by
    intro A hA
    have hAne : A.Nonempty := ⟨0, hszero A hA⟩
    exact (mem_Icc.mp (hbound A (hsmem A hA) (mem_setTop hAne))).2
  have hsorted : sorted.Pairwise rel := by
    dsimp only [sorted, rel]
    have hs := List.pairwise_mergeSort
      (le := fun A B : Finset ℕ ↦ decide (setTop A ≤ setTop B))
      (fun A B C hAB hBC ↦ by
        simp only [decide_eq_true_eq] at hAB hBC ⊢
        exact hAB.trans hBC)
      (fun A B ↦ by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (setTop A) (setTop B)) As
    simpa only [decide_eq_true_eq] using hs
  have hQupper : Q ≤ 17 * (n - 2) + 1 := by omega
  let P := (alternatingSplit sorted).1
  let R := (alternatingSplit sorted).2
  have hslen' : sorted.length = 2 * 20 := by omega
  have hPRlen := alternatingSplit_lengths hslen'
  have hPlen : P.length = 20 := hPRlen.1
  have hRlen : R.length = 20 := hPRlen.2
  have hPsub : P.Sublist sorted := alternatingSplit_fst_sublist sorted
  have hRsub : R.Sublist sorted := alternatingSplit_snd_sublist sorted
  have hPsorted : P.Pairwise rel := hsorted.sublist hPsub
  have hRsorted : R.Pairwise rel := hsorted.sublist hRsub
  have hPmem : ∀ A ∈ P, A ∈ sorted := fun A hA ↦ hPsub.subset hA
  have hRmem : ∀ A ∈ R, A ∈ sorted := fun A hA ↦ hRsub.subset hA
  have hPzero : ∀ A ∈ P, 0 ∈ A := fun A hA ↦ hszero A (hPmem A hA)
  have hRzero : ∀ A ∈ R, 0 ∈ A := fun A hA ↦ hszero A (hRmem A hA)
  have hPcard : ∀ A ∈ P, n ≤ A.card := fun A hA ↦ hscard A (hPmem A hA)
  have hRcard : ∀ A ∈ R, n ≤ A.card := fun A hA ↦ hscard A (hRmem A hA)
  have hPprim : ∀ A ∈ P, IsPrimitive A := fun A hA ↦ hsprim A (hPmem A hA)
  have hRprim : ∀ A ∈ R, IsPrimitive A := fun A hA ↦ hsprim A (hRmem A hA)
  have hPupper : ∀ A ∈ P, setTop A ≤ 17 * (n - 2) + 1 := by
    intro A hA
    exact (hstopQ A (hPmem A hA)).trans hQupper
  have hRupper : ∀ A ∈ R, setTop A ≤ 17 * (n - 2) + 1 := by
    intro A hA
    exact (hstopQ A (hRmem A hA)).trans hQupper
  have hPden := twenty_listSum_density hn hPlen hPsorted hPzero hPcard hPprim hPupper
  have hRden := twenty_listSum_density hn hRlen hRsorted hRzero hRcard hRprim hRupper
  have hbalance := alternatingSplit_topSum_balance hslen' hsorted
    (Nat.zero_le Q) (fun A _ ↦ Nat.zero_le (setTop A)) hstopQ
  change topSum P ≤ topSum R ∧ topSum R + 0 ≤ topSum P + Q at hbalance
  let D₁ := topSum P
  let D₂ := topSum R
  let S₁ := listSum P
  let S₂ := listSum R
  let M := S₁.card + S₂.card - 2
  have hS₁bound : S₁ ⊆ Icc 0 D₁ := listSum_subset_Icc_topSum P
  have hS₂bound : S₂ ⊆ Icc 0 D₂ := listSum_subset_Icc_topSum R
  have hS₁card : S₁.card ≤ D₁ + 1 := by
    simpa using card_le_card hS₁bound
  have hS₂card : S₂.card ≤ D₂ + 1 := by
    simpa using card_le_card hS₂bound
  have hcards : 2 ≤ S₁.card + S₂.card := by
    change D₁ + 20 * (n - 1) + 2 ≤ 2 * S₁.card at hPden
    change D₂ + 20 * (n - 1) + 2 ≤ 2 * S₂.card at hRden
    omega
  have hMadd : M + 2 = S₁.card + S₂.card := Nat.sub_add_cancel hcards
  have hMle : M ≤ D₁ + D₂ := by omega
  have htotal : D₁ + D₂ + 40 * (n - 1) ≤ 2 * M := by
    change D₁ + 20 * (n - 1) + 2 ≤ 2 * S₁.card at hPden
    change D₂ + 20 * (n - 1) + 2 ≤ 2 * S₂.card at hRden
    omega
  have hQlong : Q ≤ 40 * (n - 1) := by omega
  have hDorder : D₁ ≤ D₂ := hbalance.1
  have hDbalance : D₂ ≤ D₁ + Q := by omega
  have hD₂M : D₂ ≤ M := by omega
  have hdense : max D₁ D₂ ≤ M := by simpa [max_eq_right hDorder] using hD₂M
  have hinterval : Icc (D₁ + D₂ - M) M ⊆ S₁ + S₂ :=
    dense_pair_interval hS₁bound hS₂bound hcards hdense
  have hloweq : D₁ + D₂ - M + M = D₁ + D₂ := Nat.sub_add_cancel hMle
  have hlong : D₁ + D₂ - M + 40 * (n - 1) ≤ M := by omega
  have hsplitperm : (P ++ R).Perm sorted := by
    simpa only [P, R] using alternatingSplit_perm sorted
  have hsumEq : S₁ + S₂ = listSum As := by
    calc
      S₁ + S₂ = listSum (P ++ R) := (listSum_append P R).symm
      _ = listSum sorted := listSum_eq_of_perm hsplitperm
      _ = listSum As := listSum_eq_of_perm hsperm
  refine ⟨D₁ + D₂ - M, ?_⟩
  intro z hz
  rw [← hsumEq]
  apply hinterval
  have hzI := mem_Icc.mp hz
  exact mem_Icc.mpr ⟨hzI.1, hzI.2.trans hlong⟩

end Erdos54
