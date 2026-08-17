/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Erdos13.Erdos13Additive

/-!
# Structural lemmas for Lev's multiple-addition theorem

This file isolates the modular-fiber lift which is the first step of Lev's
multiple-addition estimate.  Unlike the version used in the two-set Ruzsa
argument, the prefix summand need not have diameter at most the modulus.

If `0,L ∈ B`, every element `c` of a prefix sumset `C` gives the sum
`c + L`.  In each residue represented by `C + B`, take its least integer
representative.  These least representatives are disjoint from `C + L`, so

`|C + B| ≥ |C| + |(C+B) mod L|`.

The final theorem combines this lift with the axiom-free Kneser theorem and
records precisely the stabilizer term which a proof of the full theorem must
recover from the integer fibers.
-/

open Finset Nat
open scoped Pointwise

namespace Erdos54

namespace LevStructure

open Erdos13Additive

/-! ## A generic finite-group list sum -/

/-- Pointwise sum of a list of finite subsets of an additive group. -/
def groupListSum {G : Type*} [AddCommGroup G] [DecidableEq G] :
    List (Finset G) → Finset G
  | [] => {0}
  | A :: As => A + groupListSum As

@[simp] lemma groupListSum_nil {G : Type*} [AddCommGroup G] [DecidableEq G] :
    groupListSum ([] : List (Finset G)) = {0} := rfl

@[simp] lemma groupListSum_cons {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (As : List (Finset G)) :
    groupListSum (A :: As) = A + groupListSum As := rfl

@[simp] private lemma add_singleton_zero
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    A + ({0} : Finset G) = A := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hz
    have hb0 : b = 0 := by simpa using hb
    subst b
    have haz : a = z := by simpa using hab
    simpa [← haz] using ha
  · intro hz
    exact mem_add.mpr ⟨z, hz, 0, by simp, by simp⟩

lemma groupListSum_nonempty {G : Type*} [AddCommGroup G] [DecidableEq G]
    {As : List (Finset G)} (hne : ∀ A ∈ As, A.Nonempty) :
    (groupListSum As).Nonempty := by
  induction As with
  | nil => simp
  | cons A As ih =>
      rw [groupListSum_cons, Finset.add_nonempty]
      exact ⟨hne A (by simp), ih fun B hB ↦ hne B (by simp [hB])⟩

private lemma addStab_add_self {G : Type*} [AddCommGroup G] [DecidableEq G]
    {W : Finset G} (hW : W.Nonempty) : W.addStab + W.addStab = W.addStab := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    exact addStab_add_mem hW hx hy
  · intro z hz
    exact mem_add.mpr ⟨z, hz, 0, zero_mem_addStab hW, by simp⟩

private lemma vadd_finset_eq_self_of_subgroup
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : Finset G} {x : G}
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H)
    (hneg : ∀ a ∈ H, -a ∈ H) (hx : x ∈ H) :
    x +ᵥ H = H := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.mp hz
    exact hadd x hx h hh
  · intro z hz
    apply mem_vadd_finset.mpr
    refine ⟨-x + z, hadd (-x) (hneg x hx) z hz, ?_⟩
    dsimp only [vadd_eq_add]
    abel

private lemma vadd_add_finset_right
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (A B : Finset G) : x +ᵥ (A + B) = A + (x +ᵥ B) := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hxt⟩ := mem_vadd_finset.mp hz
    obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp ht
    apply mem_add.mpr
    refine ⟨a, ha, x + b, mem_vadd_finset.mpr ⟨b, hb, rfl⟩, ?_⟩
    dsimp only [vadd_eq_add] at hxt ⊢
    rw [← hxt, ← hab]
    abel
  · intro hz
    obtain ⟨a, ha, t, ht, hat⟩ := mem_add.mp hz
    obtain ⟨b, hb, hxb⟩ := mem_vadd_finset.mp ht
    apply mem_vadd_finset.mpr
    refine ⟨a + b, mem_add.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
    dsimp only [vadd_eq_add] at hxb ⊢
    rw [← hat, ← hxb]
    abel

private lemma groupListSum_map_add
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {As : List (Finset G)} {H : Finset G}
    (hAs : As ≠ []) (hHH : H + H = H) :
    groupListSum (As.map fun A ↦ A + H) = groupListSum As + H := by
  induction As with
  | nil => exact (hAs rfl).elim
  | cons A As ih =>
      by_cases ht : As ≠ []
      · simp only [List.map_cons, groupListSum_cons]
        rw [ih ht]
        calc
          (A + H) + (groupListSum As + H) =
              (A + groupListSum As) + (H + H) := by ac_rfl
          _ = (A + groupListSum As) + H := by rw [hHH]
      · have hnil : As = [] := not_ne_iff.mp ht
        subst As
        simp

/-- If `H` is the stabilizer of `A+T`, then adjoining `H` to the suffix
`T` gives a set whose stabilizer is still exactly `H`. -/
private lemma addStab_add_suffix
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A T : Finset G} (hA : A.Nonempty) (hT : T.Nonempty) :
    let W := A + T
    let H := W.addStab
    (T + H).addStab = H := by
  dsimp only
  let W := A + T
  let H := W.addStab
  let S := T + H
  have hW : W.Nonempty := hA.add hT
  have hH0 : (0 : G) ∈ H := zero_mem_addStab hW
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hW hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hW hx
  have hS : S.Nonempty := hT.add ⟨0, hH0⟩
  have hWAS : A + S = W := by
    calc
      A + S = (A + T) + H := by simp only [S]; rw [add_assoc]
      _ = W + W.addStab := by rfl
      _ = W := add_addStab W
  apply Subset.antisymm
  · intro x hx
    have hxS : x +ᵥ S = S := (mem_addStab hS).mp hx
    apply (mem_addStab hW).mpr
    calc
      x +ᵥ W = x +ᵥ (A + S) := by rw [hWAS]
      _ = A + (x +ᵥ S) := vadd_add_finset_right x A S
      _ = A + S := by rw [hxS]
      _ = W := hWAS
  · intro x hx
    apply (mem_addStab hS).mpr
    rw [vadd_add_finset_right]
    have hxH : x +ᵥ H = H :=
      vadd_finset_eq_self_of_subgroup hHadd hHneg hx
    rw [hxH]

/-- Iterated Kneser inequality for a nonempty list of nonempty finite sets.
All summands are saturated by the stabilizer of the *final* list sum. -/
theorem groupListSum_kneser
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {As : List (Finset G)} (hAs : As ≠ [])
    (hne : ∀ A ∈ As, A.Nonempty) :
    let W := groupListSum As
    let H := W.addStab
    (As.map fun A ↦ (A + H).card).sum ≤
      W.card + (As.length - 1) * H.card := by
  cases As with
  | nil => exact (hAs rfl).elim
  | cons A As =>
      by_cases htail : As = []
      · subst As
        simp [groupListSum, add_addStab]
      · let T := groupListSum As
        let W := A + T
        let H := W.addStab
        let satTail := As.map fun X ↦ X + H
        have hA : A.Nonempty := hne A (by simp)
        have htailne : ∀ X ∈ As, X.Nonempty := by
          intro X hX
          exact hne X (by simp [hX])
        have hT : T.Nonempty := groupListSum_nonempty htailne
        have hW : W.Nonempty := hA.add hT
        have hHH : H + H = H := addStab_add_self hW
        have hsatTail : satTail ≠ [] := by simp [satTail, htail]
        have hsatne : ∀ X ∈ satTail, X.Nonempty := by
          intro X hX
          simp only [satTail, List.mem_map] at hX
          obtain ⟨Y, hY, rfl⟩ := hX
          exact (htailne Y hY).add ⟨0, zero_mem_addStab hW⟩
        have hsumSat : groupListSum satTail = T + H := by
          exact groupListSum_map_add htail hHH
        have hstabSat : (groupListSum satTail).addStab = H := by
          rw [hsumSat]
          exact addStab_add_suffix hA hT
        have ih := groupListSum_kneser hsatTail hsatne
        change
          (satTail.map fun X ↦ (X + (groupListSum satTail).addStab).card).sum ≤
            (groupListSum satTail).card +
              (satTail.length - 1) * (groupListSum satTail).addStab.card at ih
        rw [hstabSat] at ih
        rw [hsumSat] at ih
        have haddH (X : Finset G) : (X + H) + H = X + H := by
          rw [add_assoc, hHH]
        have hleft :
            (satTail.map fun X ↦ (X + H).card).sum =
              (As.map fun X ↦ (X + H).card).sum := by
          dsimp only [satTail]
          rw [List.map_map]
          change (As.map fun X ↦ ((X + H) + H).card).sum = _
          simp_rw [haddH]
        rw [hleft] at ih
        simp only [satTail, List.length_map] at ih
        have hkneser : (A + H).card + (T + H).card ≤ W.card + H.card := by
          simpa only [W, T, H] using Finset.add_kneser A T
        change (A + H).card + (As.map fun X ↦ (X + H).card).sum ≤
          W.card + ((A :: As).length - 1) * H.card
        simp only [List.length_cons, Nat.add_one_sub_one]
        have hlen0 : 0 < As.length := (List.length_pos_iff_ne_nil).2 htail
        have hlen : 1 ≤ As.length := hlen0
        have hmul : (As.length - 1) * H.card + H.card =
            As.length * H.card := by
          calc
            (As.length - 1) * H.card + H.card =
                ((As.length - 1) + 1) * H.card := by rw [Nat.add_mul]; simp
            _ = As.length * H.card := by rw [Nat.sub_add_cancel hlen]
        calc
          (A + H).card + (As.map fun X ↦ (X + H).card).sum ≤
              (A + H).card +
                ((T + H).card + (As.length - 1) * H.card) :=
            Nat.add_le_add_left ih _
          _ = ((A + H).card + (T + H).card) +
                (As.length - 1) * H.card := by omega
          _ ≤ (W.card + H.card) + (As.length - 1) * H.card :=
            Nat.add_le_add_right hkneser _
          _ = W.card + ((As.length - 1) * H.card + H.card) := by omega
          _ = W.card + As.length * H.card := by rw [hmul]
termination_by As.length
decreasing_by simp_all [satTail]

/-! ## Lists of selected integer fibers -/

/-- The integer fibers selected by a list of occupied residues. -/
def selectedResidueFibers {L : ℕ} (Bs : List (Finset ℕ))
    (as : List (ZMod L)) (H : Finset (ZMod L)) : List (Finset ℕ) :=
  Bs.zipWith (fun B a ↦ residueFiberSet B L (a +ᵥ H)) as

@[simp] lemma selectedResidueFibers_nil_left {L : ℕ}
    (as : List (ZMod L)) (H : Finset (ZMod L)) :
    selectedResidueFibers [] as H = [] := rfl

@[simp] lemma selectedResidueFibers_cons_cons {L : ℕ}
    (B : Finset ℕ) (Bs : List (Finset ℕ)) (a : ZMod L)
    (as : List (ZMod L)) (H : Finset (ZMod L)) :
    selectedResidueFibers (B :: Bs) (a :: as) H =
      residueFiberSet B L (a +ᵥ H) :: selectedResidueFibers Bs as H := rfl

/-- Pointwise sum of a list of finite sets of natural numbers. -/
def natListSum : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | B :: Bs => B + natListSum Bs

@[simp] lemma natListSum_nil : natListSum [] = {0} := rfl

@[simp] lemma natListSum_cons (B : Finset ℕ) (Bs : List (Finset ℕ)) :
    natListSum (B :: Bs) = B + natListSum Bs := rfl

/-- Aligned input sets and residues produce exactly one selected fiber per
input set. -/
lemma selectedResidueFibers_length {L : ℕ} {Bs : List (Finset ℕ)}
    {as : List (ZMod L)} {H : Finset (ZMod L)}
    (halign : List.Forall₂ (fun B a ↦ a ∈ modImage B L) Bs as) :
    (selectedResidueFibers Bs as H).length = Bs.length := by
  induction halign with
  | nil => rfl
  | cons _ _ ih => simp only [selectedResidueFibers_cons_cons,
      List.length_cons, ih]

/-- Every selected fiber is nonempty, since its distinguished residue is
occupied and zero belongs to the stabilizer. -/
lemma selectedResidueFibers_nonempty {L : ℕ} {Bs : List (Finset ℕ)}
    {as : List (ZMod L)} {H : Finset (ZMod L)}
    (hzero : (0 : ZMod L) ∈ H)
    (halign : List.Forall₂ (fun B a ↦ a ∈ modImage B L) Bs as) :
    ∀ R ∈ selectedResidueFibers Bs as H, R.Nonempty := by
  induction halign with
  | nil => simp
  | @cons B a Bs as ha halign ih =>
      intro R hR
      simp only [selectedResidueFibers_cons_cons, List.mem_cons] at hR
      rcases hR with rfl | hR
      · obtain ⟨z, hzB, hza⟩ := mem_modImage.mp ha
        refine ⟨z, mem_residueFiberSet.mpr ⟨hzB, ?_⟩⟩
        apply mem_vadd_finset.mpr
        refine ⟨0, hzero, ?_⟩
        simp [hza]
      · exact ih R hR

/-- Every integer selected from a fiber is selected from its original
summand; hence the sum of the fibers lies in the original list sumset. -/
lemma natListSum_selectedResidueFibers_subset {L : ℕ}
    {Bs : List (Finset ℕ)} {as : List (ZMod L)} {H : Finset (ZMod L)}
    (halign : List.Forall₂ (fun B a ↦ a ∈ modImage B L) Bs as) :
    natListSum (selectedResidueFibers Bs as H) ⊆ natListSum Bs := by
  induction halign with
  | nil => simp
  | @cons B a Bs as ha halign ih =>
      intro z hz
      simp only [selectedResidueFibers_cons_cons, natListSum_cons] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
      exact mem_add.mpr ⟨x, (mem_residueFiberSet.mp hx).1,
        y, ih hy, rfl⟩

/-- All sums of selected integer fibers lie in the single output coset
whose representative is the sum of the selected residues. -/
lemma natListSum_selectedResidueFibers_cast_mem {L : ℕ}
    {Bs : List (Finset ℕ)} {as : List (ZMod L)} {H : Finset (ZMod L)}
    (hzero : (0 : ZMod L) ∈ H)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (halign : List.Forall₂ (fun B a ↦ a ∈ modImage B L) Bs as) :
    ∀ z ∈ natListSum (selectedResidueFibers Bs as H),
      (z : ZMod L) ∈ as.sum +ᵥ H := by
  induction halign with
  | nil =>
      intro z hz
      have hz0 : z = 0 := by simpa [natListSum] using hz
      subst z
      exact mem_vadd_finset.mpr ⟨0, hzero, by simp⟩
  | @cons B a Bs as ha halign ih =>
      intro z hz
      simp only [selectedResidueFibers_cons_cons, natListSum_cons] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
      have hx' := mem_residueFiberSet.mp hx
      obtain ⟨h₁, hh₁, hah₁⟩ := mem_vadd_finset.mp hx'.2
      obtain ⟨h₂, hh₂, hash₂⟩ := mem_vadd_finset.mp (ih y hy)
      apply mem_vadd_finset.mpr
      refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
      change (a :: as).sum + (h₁ + h₂) = ((x + y : ℕ) : ZMod L)
      simp only [List.sum_cons]
      push_cast
      dsimp only [vadd_eq_add] at hah₁ hash₂ ⊢
      rw [← hah₁, ← hash₂]
      abel

/-- Summing the one-summand saturation/fiber estimates over an aligned
list.  This is the aggregate inequality used to cancel Kneser's stabilizer
term in Lev's theorem. -/
lemma sum_modImage_cards_add_length_mul_card_le_saturated_add_fibers
    {L : ℕ} {Bs : List (Finset ℕ)} {as : List (ZMod L)}
    {H : Finset (ZMod L)} (hzero : (0 : ZMod L) ∈ H)
    (halign : List.Forall₂ (fun B a ↦ a ∈ modImage B L) Bs as) :
    (Bs.map fun B ↦ (modImage B L).card).sum + Bs.length * H.card ≤
      (Bs.map fun B ↦ (modImage B L + H).card).sum +
        ((selectedResidueFibers Bs as H).map Finset.card).sum := by
  induction halign with
  | nil => simp
  | @cons B a Bs as ha halign ih =>
      have hone := card_modImage_add_card_le_saturation_add_fiber hzero ha
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        selectedResidueFibers_cons_cons, Nat.succ_mul]
      omega

/-- Least residue representatives of `C+B` never belong to the `L`-shifted
copy of `C`.  No diameter bound on `C` is needed. -/
lemma residueReps_disjoint_shiftedBy_general
    {C B : Finset ℕ} {L : ℕ} (hL : 0 < L) (hB0 : 0 ∈ B) :
    Disjoint (residueReps (C + B) L) (shiftedBy C L) := by
  rw [Finset.disjoint_left]
  intro z hzR hzE
  simp only [shiftedBy, mem_image] at hzE
  obtain ⟨c, hc, rfl⟩ := hzE
  simp only [residueReps, mem_image] at hzR
  obtain ⟨r, hr, hrep⟩ := hzR
  have hcast : r.1 = (c : ZMod L) := by
    rw [← residueRep_cast (C + B) L r, hrep]
    simp
  let rc : ↑(modImage (C + B) L) :=
    ⟨(c : ZMod L), mem_modImage.mpr ⟨c, Finset.add_mem_add hc hB0, rfl⟩⟩
  have hrc : r = rc := by
    apply Subtype.ext
    exact hcast
  subst r
  have hle : residueRep (C + B) L rc ≤ c :=
    residueRep_le rc (Finset.add_mem_add hc hB0) rfl
  dsimp only [rc] at hrep hle
  omega

/-- General modular-fiber lift.  The hypotheses `0,L ∈ B` give a copy of
`C` one level above the least representative in every occupied residue. -/
lemma card_add_modImage_add_card_le
    {C B : Finset ℕ} {L : ℕ} (hL : 0 < L) (hB0 : 0 ∈ B) (hLB : L ∈ B) :
    (modImage (C + B) L).card + C.card ≤ (C + B).card := by
  have hR := residueReps_subset (C + B) L
  have hE := shiftedBy_subset_add (A := C) hLB
  have hdisj := residueReps_disjoint_shiftedBy_general (C := C) hL hB0
  rw [← card_residueReps (C + B) L, ← card_shiftedBy C L,
    ← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset hR hE)

/-- Generalized refined lift through one selected residue set `D`.

Besides the shifted copy `C + L`, retain one least representative of every
residue of `C+B` outside `D`, and an arbitrary set `F` of actual sums whose
residues lie in `D`.  If `D` is disjoint from the residues of `C`, these three
sets are pairwise disjoint.  In the application, `D` is a stabilizer coset and
`F` is a sum of one integer fiber from every summand. -/
lemma card_modImage_add_card_add_fiber_le
    {C B F : Finset ℕ} {L : ℕ} (D : Finset (ZMod L))
    (hL : 0 < L) (hB0 : 0 ∈ B) (hLB : L ∈ B)
    (hD : D ⊆ modImage (C + B) L)
    (hDC : Disjoint D (modImage C L))
    (hF : F ⊆ C + B)
    (hFres : ∀ z ∈ F, (z : ZMod L) ∈ D) :
    (modImage (C + B) L).card + C.card + F.card ≤
      (C + B).card + D.card := by
  let R := residueRepsOutside (C + B) L D
  let E := shiftedBy C L
  have hRS : R ⊆ C + B := residueRepsOutside_subset (C + B) L D
  have hES : E ⊆ C + B := shiftedBy_subset_add hLB
  have hRE : Disjoint R E := by
    apply Disjoint.mono_left _
      (residueReps_disjoint_shiftedBy_general (C := C) hL hB0)
    intro z hz
    change z ∈ residueRepsOutside (C + B) L D at hz
    simp only [residueRepsOutside, residueReps, mem_image] at hz ⊢
    obtain ⟨c, -, rfl⟩ := hz
    exact ⟨⟨c.1, (mem_sdiff.mp c.2).1⟩, by simp, rfl⟩
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_of_mem_residueRepsOutside hzR) (hFres z hzF)
  have hEF : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro z hzE hzFmem
    simp only [E, shiftedBy, mem_image] at hzE
    obtain ⟨c, hc, rfl⟩ := hzE
    have hcD : (c : ZMod L) ∈ D := by
      simpa using hFres (c + L) hzFmem
    exact (Finset.disjoint_left.mp hDC) hcD
      (mem_modImage.mpr ⟨c, hc, rfl⟩)
  have hREF : Disjoint (R ∪ E) F := by
    rw [Finset.disjoint_left]
    intro z hz hzFmem
    rcases mem_union.mp hz with hzR | hzE
    · exact (Finset.disjoint_left.mp hRF) hzR hzFmem
    · exact (Finset.disjoint_left.mp hEF) hzE hzFmem
  have hU : (R ∪ E) ∪ F ⊆ C + B :=
    union_subset (union_subset hRS hES) hF
  have hcardU := card_le_card hU
  rw [card_union_of_disjoint hREF, card_union_of_disjoint hRE,
    card_residueRepsOutside, card_shiftedBy] at hcardU
  have hsplit := card_sdiff_add_card_eq_card hD
  change (modImage (C + B) L \ D).card + D.card =
    (modImage (C + B) L).card at hsplit
  omega

/-- Kneser's theorem inserted into the general fiber lift.  Here `H` is the
stabilizer of the final modular sumset.  This is a subtraction-free form of

`|C+B|-|C| ≥ |C̄+H| + |B̄+H| - |H|`.

The full multiple-addition theorem amounts to paying a possible stabilizer
deficit by additional elements in the integer fibers. -/
lemma card_addStab_saturations_le_add_card_add
    {C B : Finset ℕ} {L : ℕ} (hL : 0 < L) (hB0 : 0 ∈ B) (hLB : L ∈ B) :
    let C₀ := modImage C L
    let B₀ := modImage B L
    let H := (C₀ + B₀).addStab
    C.card + (C₀ + H).card + (B₀ + H).card ≤
      (C + B).card + H.card := by
  dsimp only
  let C₀ := modImage C L
  let B₀ := modImage B L
  let D := C₀ + B₀
  let H := D.addStab
  have hImage : D = modImage (C + B) L := by
    exact (modImage_add C B L).symm
  have hlift : D.card + C.card ≤ (C + B).card := by
    rw [hImage]
    exact card_add_modImage_add_card_le hL hB0 hLB
  have hkneser : (C₀ + H).card + (B₀ + H).card ≤ D.card + H.card := by
    simpa only [H, D] using Finset.add_kneser C₀ B₀
  change C.card + (C₀ + H).card + (B₀ + H).card ≤
    (C + B).card + H.card
  omega

/-- In the aperiodic case the stabilizer term disappears, and the fiber lift
has the exact Cauchy--Davenport strength expected in Lev's theorem. -/
lemma card_modImages_add_card_le_of_addStab_card_one
    {C B : Finset ℕ} {L : ℕ} (hC : C.Nonempty) (hL : 0 < L)
    (hB0 : 0 ∈ B) (hLB : L ∈ B)
    (hstab : ((modImage C L + modImage B L).addStab).card = 1) :
    C.card + (modImage C L).card + (modImage B L).card ≤ (C + B).card + 1 := by
  let C₀ := modImage C L
  let B₀ := modImage B L
  let D := C₀ + B₀
  let H := D.addStab
  have hDne : D.Nonempty := by
    exact (modImage_nonempty hC).add (modImage_nonempty ⟨0, hB0⟩)
  have hHzero : (0 : ZMod L) ∈ H := zero_mem_addStab hDne
  have hCsub : C₀ ⊆ C₀ + H := by
    intro c hc
    exact mem_add.mpr ⟨c, hc, 0, hHzero, by simp⟩
  have hBsub : B₀ ⊆ B₀ + H := by
    intro b hb
    exact mem_add.mpr ⟨b, hb, 0, hHzero, by simp⟩
  have hsaturated := card_addStab_saturations_le_add_card_add (C := C) hL hB0 hLB
  change C.card + (C₀ + H).card + (B₀ + H).card ≤
    (C + B).card + H.card at hsaturated
  have hCcard := card_le_card hCsub
  have hBcard := card_le_card hBsub
  change H.card = 1 at hstab
  change C.card + C₀.card + B₀.card ≤ (C + B).card + 1
  omega

end LevStructure

end Erdos54
