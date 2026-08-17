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
import ErdosProblems.Erdos13.Erdos13Kneser

/-!
# Iterated sumset growth for Erdős Problem 54

This file proves the finite-abelian-group growth estimate used in the
Cochrane--Ostergaard--Spencer step of Conlon--Fox--Pham's construction.
-/

open Finset
open scoped Pointwise

namespace Erdos54

noncomputable section

/-- A finite set is not contained in a coset of a proper additive subgroup.

The subgroup is represented by its underlying finset: nonemptiness, closure
under addition, and closure under negation are exactly the subgroup axioms in
a finite ambient additive group. -/
def NotContainedInProperCoset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : Finset G) : Prop :=
  ∀ (H : Finset G), H.Nonempty →
    (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) →
    (∀ x ∈ H, -x ∈ H) →
    H ≠ Finset.univ → ∀ a : G, ¬ B ⊆ a +ᵥ H

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma addStab_add_mem {C : Finset G} (hC : C.Nonempty) {x y : G}
    (hx : x ∈ C.addStab) (hy : y ∈ C.addStab) : x + y ∈ C.addStab := by
  rw [← Finset.mem_coe, Finset.coe_addStab hC] at hx hy ⊢
  exact (AddAction.stabilizer G (C : Set G)).add_mem hx hy

private lemma addStab_neg_mem {C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : x ∈ C.addStab) : -x ∈ C.addStab := by
  rw [← Finset.mem_coe, Finset.coe_addStab hC] at hx ⊢
  exact (AddAction.stabilizer G (C : Set G)).neg_mem hx

/-- A nonempty finite set whose translation stabilizer is the whole group is
the whole group. -/
lemma eq_univ_of_addStab_eq_univ {C : Finset G} (hC : C.Nonempty)
    (hstab : C.addStab = Finset.univ) : C = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨c, hc⟩ := hC
  have hxc : x - c ∈ C.addStab := by simp [hstab]
  have htranslate : (x - c) +ᵥ C = C :=
    (Finset.mem_addStab (s := C) (⟨c, hc⟩ : C.Nonempty)).mp hxc
  have hxmem : (x - c) + c ∈ (x - c) +ᵥ C :=
    Finset.vadd_mem_vadd_finset hc
  rw [htranslate] at hxmem
  simpa using hxmem

private lemma disjoint_vadd_vadd_of_not_mem {H : Finset G} {a b : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hb : b ∉ a +ᵥ H) :
    Disjoint (a +ᵥ H) (b +ᵥ H) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  obtain ⟨x, hx, hax⟩ := Finset.mem_vadd_finset.mp hza
  obtain ⟨y, hy, hby⟩ := Finset.mem_vadd_finset.mp hzb
  apply hb
  apply Finset.mem_vadd_finset.mpr
  refine ⟨x + -y, hadd x hx (-y) (hneg y hy), ?_⟩
  dsimp only [vadd_eq_add] at hax hby ⊢
  calc
    a + (x + -y) = (a + x) + -y := by abel
    _ = z + -y := by rw [hax]
    _ = (b + y) + -y := by rw [hby]
    _ = b := by abel

/-- The one-step Cochrane--Ostergaard--Spencer growth estimate.  Kneser's
theorem says that `S + B` either fills the group or gains at least half of
`B`.  The inequality is doubled so that it is integral and has no rounding
convention hidden in its statement. -/
lemma add_step_eq_univ_or_two_mul_card_growth (S B : Finset G)
    (hS : S.Nonempty) (hB : B.Nonempty)
    (haper : NotContainedInProperCoset B) :
    S + B = Finset.univ ∨ 2 * S.card + B.card ≤ 2 * (S + B).card := by
  let C := S + B
  let H := C.addStab
  have hC : C.Nonempty := hS.add hB
  have hHne : H.Nonempty := hC.addStab
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hC hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hC hx
  by_cases hHuniv : H = Finset.univ
  · exact Or.inl (eq_univ_of_addStab_eq_univ hC hHuniv)
  right
  obtain ⟨b₀, hb₀⟩ := hB
  have hnotcoset : ¬ B ⊆ b₀ +ᵥ H :=
    haper H hHne hHadd hHneg hHuniv b₀
  obtain ⟨b₁, hb₁, hb₁coset⟩ := Finset.not_subset.mp hnotcoset
  have hdisj : Disjoint (b₀ +ᵥ H) (b₁ +ᵥ H) :=
    disjoint_vadd_vadd_of_not_mem hHadd hHneg hb₁coset
  have hb₀sub : b₀ +ᵥ H ⊆ B + H := Finset.vadd_finset_subset_add hb₀
  have hb₁sub : b₁ +ᵥ H ⊆ B + H := Finset.vadd_finset_subset_add hb₁
  have htwoH : 2 * H.card ≤ (B + H).card := by
    have hc := Finset.card_le_card (Finset.union_subset hb₀sub hb₁sub)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_vadd_finset,
      Finset.card_vadd_finset] at hc
    omega
  have hBsat : B.card ≤ (B + H).card := Finset.card_le_card_add_right hHne
  have hSsat : S.card ≤ (S + H).card := Finset.card_le_card_add_right hHne
  have hkneser := Finset.add_kneser S B
  change (S + H).card + (B + H).card ≤ C.card + H.card at hkneser
  change 2 * S.card + B.card ≤ 2 * C.card
  omega

private lemma univ_add_of_nonempty (B : Finset G) (hB : B.Nonempty) :
    (Finset.univ : Finset G) + B = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨b, hb⟩ := hB
  exact Finset.mem_add.mpr ⟨x - b, Finset.mem_univ _, b, hb, sub_add_cancel x b⟩

/-- Iterating the one-step estimate: either the `k`-fold sumset is the whole
finite group, or its doubled cardinality is at least `(k+1)|B|`.  This is the
`s = 0` case of the Cochrane--Ostergaard--Spencer estimate used by
Conlon--Fox--Pham. -/
theorem nsmul_eq_univ_or_two_mul_card_growth (B : Finset G)
    (hB : B.Nonempty) (haper : NotContainedInProperCoset B) :
    ∀ k : ℕ, 1 ≤ k →
      k • B = Finset.univ ∨ (k + 1) * B.card ≤ 2 * (k • B).card := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      right
      simp
  | succ k hk ih =>
      have hsumne : (k • B).Nonempty := hB.nsmul
      rcases ih with hfull | hgrowth
      · left
        rw [succ_nsmul, hfull]
        exact univ_add_of_nonempty B hB
      · rw [succ_nsmul]
        rcases add_step_eq_univ_or_two_mul_card_growth (k • B) B hsumne hB haper with
          hfull | hstep
        · exact Or.inl hfull
        · right
          calc
            (k + 1 + 1) * B.card = (k + 1) * B.card + B.card := by ring
            _ ≤ 2 * (k • B).card + B.card := Nat.add_le_add_right hgrowth _
            _ ≤ 2 * (k • B + B).card := hstep

/-- Min-form of the cyclic growth estimate.  It avoids division by two:
`min (2|G|, (k+1)|B|) ≤ 2|kB|`. -/
theorem min_two_card_le_two_card_nsmul (B : Finset G)
    (hB : B.Nonempty) (haper : NotContainedInProperCoset B)
    (k : ℕ) (hk : 1 ≤ k) :
    min (2 * Fintype.card G) ((k + 1) * B.card) ≤ 2 * (k • B).card := by
  rcases nsmul_eq_univ_or_two_mul_card_growth B hB haper k hk with hfull | hgrowth
  · rw [hfull, Finset.card_univ]
    exact min_le_left _ _
  · exact (min_le_right _ _).trans hgrowth

end FiniteGroup

end

end Erdos54
