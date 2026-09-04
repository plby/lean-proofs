/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.FiniteGroupCover
import ErdosProblems.Erdos186.CFP.LatticeBasis

/-!
# Covering a finite lattice quotient by bounded iterated sums

This file isolates the quotient-saturation step in Conlon--Fox--Pham
Lemma 2.16.  If `H ≤ Γ` has finite relative index and a finite subset of
`Γ` contains zero and generates `Γ`, then exactly `[Γ : H]` copies of that
set meet every coset of `H`.  The final specialization bounds the number of
copies by the volume of a rectangular subgroup.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

/-- A finite generating set containing zero is not contained in a coset of
a proper subgroup. -/
theorem notInProperCoset_of_zero_mem_closure_eq_top
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (hzero : 0 ∈ A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) :
    NotInProperCoset (A : Set G) := by
  intro K hK a hcontained
  have hnega : -a ∈ K := by
    simpa using hcontained 0 hzero
  have ha : a ∈ K := by
    simpa only [neg_neg] using K.neg_mem hnega
  have hAK : (A : Set G) ⊆ K := by
    intro x hx
    have hsub : x - a ∈ K := hcontained x hx
    simpa [sub_add_cancel] using K.add_mem hsub ha
  have htop : (⊤ : AddSubgroup G) ≤ K := by
    rw [← hgen, AddSubgroup.closure_le]
    exact hAK
  exact hK (top_unique htop)

/-- An additive homomorphism commutes with a finite family sumset. -/
theorem image_iteratedSumset
    {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    [DecidableEq G] [DecidableEq G']
    (f : G →+ G') (A : ℕ → Finset G) (n : ℕ) :
    (iteratedSumset A n).image f =
      iteratedSumset (fun i ↦ (A i).image f) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedSumset_succ, iteratedSumset_succ, ← ih]
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_add.mp hx
        apply Finset.mem_add.mpr
        exact ⟨f s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
          f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, (map_add f s a).symm⟩
      · intro hy
        obtain ⟨s', hs', a', ha', hsa⟩ := Finset.mem_add.mp hy
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hs'
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
        apply Finset.mem_image.mpr
        refine ⟨s + a, Finset.mem_add.mpr ⟨s, hs, a, ha, rfl⟩, ?_⟩
        simpa using hsa

/-- If `H` has finite relative index in `Γ`, then `[Γ : H]` copies of a
finite generating set of `Γ` containing zero meet every coset of `H`.
The representative is returned in the original subgroup, not merely in the
quotient. -/
theorem exists_iteratedSumset_sub_mem_of_finiteRelIndex
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H Gamma : AddSubgroup G) (B : Finset Gamma)
    (hzero : (0 : Gamma) ∈ B)
    (hgen : AddSubgroup.closure (B : Set Gamma) = ⊤)
    (hrel : H.relIndex Gamma ≠ 0) :
    ∀ y : Gamma, ∃ s ∈ iteratedSumset (fun _ ↦ B) (H.relIndex Gamma),
      ((y - s : Gamma) : G) ∈ H := by
  classical
  let J : AddSubgroup Gamma := H.addSubgroupOf Gamma
  let Q := Gamma ⧸ J
  let q : Gamma →+ Q := QuotientAddGroup.mk' J
  let Y : Finset Q := B.image q
  let : H.IsFiniteRelIndex Gamma := ⟨hrel⟩
  let : Fintype Q := Fintype.ofFinite Q
  have hzeroY : (0 : Q) ∈ Y := by
    exact Finset.mem_image.mpr ⟨0, hzero, map_zero q⟩
  have hgenY : AddSubgroup.closure (Y : Set Q) = ⊤ := by
    rw [show (Y : Set Q) = q '' (B : Set Gamma) by simp [Y],
      ← AddMonoidHom.map_closure, hgen]
    exact AddSubgroup.map_top_of_surjective q
      (QuotientAddGroup.mk'_surjective J)
  have hcoset : NotInProperCoset (Y : Set Q) :=
    notInProperCoset_of_zero_mem_closure_eq_top Y hzeroY hgenY
  have hcover :
      iteratedSumset (fun _ : ℕ ↦ Y) (Fintype.card Q) = Finset.univ := by
    apply finite_group_sumset_cover (fun _ : ℕ ↦ Y)
    · intro _ _
      exact ⟨0, hzeroY⟩
    · intro _ _
      exact hcoset
  have hrelCard : H.relIndex Gamma = Fintype.card Q := by
    change Nat.card Q = Fintype.card Q
    exact Nat.card_eq_fintype_card
  intro y
  have hqy : q y ∈ iteratedSumset (fun _ : ℕ ↦ Y) (Fintype.card Q) := by
    rw [hcover]
    exact Finset.mem_univ _
  have hqy' : q y ∈
      (iteratedSumset (fun _ : ℕ ↦ B) (Fintype.card Q)).image q := by
    rw [image_iteratedSumset]
    exact hqy
  obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hqy'
  refine ⟨s, ?_, ?_⟩
  · simpa [hrelCard] using hs
  · have hmemJ : y - s ∈ J := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact hsy.symm
    exact hmemJ

/-- Rectangular specialization of
`exists_iteratedSumset_sub_mem_of_finiteRelIndex`.  It supplies both the
uniform copy bound and representatives of every coset. -/
theorem rectangular_iteratedSumset_covers_cosets
    {d : ℕ} (v : Fin d → ℕ) (hv : ∀ i, 0 < v i)
    (Gamma : LatticeBasis.Sublattice d)
    (hrect : LatticeBasis.rectangularSubgroup v ≤ Gamma)
    (B : Finset Gamma) (hzero : (0 : Gamma) ∈ B)
    (hgen : AddSubgroup.closure (B : Set Gamma) = ⊤) :
    (LatticeBasis.rectangularSubgroup v).relIndex Gamma ≤ ∏ i, v i ∧
      ∀ y : Gamma,
        ∃ s ∈ iteratedSumset (fun _ ↦ B)
            ((LatticeBasis.rectangularSubgroup v).relIndex Gamma),
          (((y - s : Gamma) : LatticePoint d) ∈
            LatticeBasis.rectangularSubgroup v) := by
  have hprod : 0 < ∏ i, v i := Finset.prod_pos fun i _ ↦ hv i
  have hmul := LatticeBasis.rectangular_relIndex_mul_index v Gamma hrect
  have hrel : (LatticeBasis.rectangularSubgroup v).relIndex Gamma ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    omega
  exact ⟨LatticeBasis.rectangular_relIndex_le_prod hv Gamma hrect,
    exists_iteratedSumset_sub_mem_of_finiteRelIndex
      (LatticeBasis.rectangularSubgroup v) Gamma B hzero hgen hrel⟩

end Erdos186.CFP
