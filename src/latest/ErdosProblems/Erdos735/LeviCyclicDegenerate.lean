/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos735.PolarBoundaryOrder

/-!
# A cyclic bound for degenerate Levi arrangements

If the corners of a cyclic polygon away from one distinguished supporting
line all collapse to the same geometric vertex, an injective boundary has at
most three sides.  This is the finite combinatorial core of the concurrent
branch of Levi's triangle theorem.
-/

open Classical
noncomputable section

namespace Erdos735.LeviCyclicDegenerate

open Erdos957

universe uI uV

variable {I : Type uI} {V : Type uV}

private lemma fin_ofNat_eq_nsmul_one {n : ℕ} [NeZero n] (m : ℕ) :
    Fin.ofNat n m = m • (1 : Fin n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, ← ih]
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]

/-- One forward step in a nontrivial cyclic order does not return to its
starting index. -/
theorem cyclicSucc_ne_self_of_two_le
    {k : ℕ} (hk : 2 ≤ k) (r : Fin k) : cyclicSucc r ≠ r := by
  letI : NeZero k := ⟨by omega⟩
  have hform : cyclicSucc r = r + (1 : Fin k) := by
    change finRotate k r = _
    rw [finRotate_apply]
  rw [hform]
  intro h
  have hzero : (1 : Fin k) = 0 := by
    apply add_left_cancel (a := r)
    simpa using h
  have hv := congrArg Fin.val hzero
  change 1 % k = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Two forward steps in a cyclic order of size at least three do not return
to the starting index. -/
theorem cyclicSucc_two_ne_self_of_three_le
    {k : ℕ} (hk : 3 ≤ k) (r : Fin k) :
    cyclicSucc (cyclicSucc r) ≠ r := by
  letI : NeZero k := ⟨by omega⟩
  have hform : cyclicSucc (cyclicSucc r) = r + (2 : Fin k) := by
    change finRotate k (finRotate k r) = _
    simp only [finRotate_apply]
    change r + 1 + 1 = r + Fin.ofNat k 2
    rw [fin_ofNat_eq_nsmul_one]
    abel
  rw [hform]
  intro h
  have hzero : (2 : Fin k) = 0 := by
    apply add_left_cancel (a := r)
    simpa using h
  have hv := congrArg Fin.val hzero
  change 2 % k = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Three forward steps in a cyclic order of size at least four do not return
to the starting index. -/
theorem cyclicSucc_three_ne_self_of_four_le
    {k : ℕ} (hk : 4 ≤ k) (r : Fin k) :
    cyclicSucc (cyclicSucc (cyclicSucc r)) ≠ r := by
  letI : NeZero k := ⟨by omega⟩
  have hform : cyclicSucc (cyclicSucc (cyclicSucc r)) = r + (3 : Fin k) := by
    change finRotate k (finRotate k (finRotate k r)) = _
    simp only [finRotate_apply]
    change r + 1 + 1 + 1 = r + Fin.ofNat k 3
    rw [fin_ofNat_eq_nsmul_one]
    abel
  rw [hform]
  intro h
  have hzero : (3 : Fin k) = 0 := by
    apply add_left_cancel (a := r)
    simpa using h
  have hv := congrArg Fin.val hzero
  change 3 % k = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Four forward steps in a cyclic order of size at least five do not return
to the starting index. -/
theorem cyclicSucc_four_ne_self_of_five_le
    {k : ℕ} (hk : 5 ≤ k) (r : Fin k) :
    cyclicSucc (cyclicSucc (cyclicSucc (cyclicSucc r))) ≠ r := by
  letI : NeZero k := ⟨by omega⟩
  have hform : cyclicSucc (cyclicSucc (cyclicSucc (cyclicSucc r))) =
      r + (4 : Fin k) := by
    change finRotate k (finRotate k (finRotate k (finRotate k r))) = _
    simp only [finRotate_apply]
    change r + 1 + 1 + 1 + 1 = r + Fin.ofNat k 4
    rw [fin_ofNat_eq_nsmul_one]
    abel
  rw [hform]
  intro h
  have hzero : (4 : Fin k) = 0 := by
    apply add_left_cancel (a := r)
    simpa using h
  have hv := congrArg Fin.val hzero
  change 4 % k = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Four forward steps return to the starting index in a four-cycle. -/
theorem cyclicSucc_four_eq_self (r : Fin 4) :
    cyclicSucc (cyclicSucc (cyclicSucc (cyclicSucc r))) = r := by
  fin_cases r <;> rfl

/-- The four successive indices of a four-cycle are pairwise distinct. -/
theorem cyclicFour_pairwise_distinct (r : Fin 4) :
    r ≠ cyclicSucc r ∧
    r ≠ cyclicSucc (cyclicSucc r) ∧
    r ≠ cyclicSucc (cyclicSucc (cyclicSucc r)) ∧
    cyclicSucc r ≠ cyclicSucc (cyclicSucc r) ∧
    cyclicSucc r ≠ cyclicSucc (cyclicSucc (cyclicSucc r)) ∧
    cyclicSucc (cyclicSucc r) ≠ cyclicSucc (cyclicSucc (cyclicSucc r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (cyclicSucc_ne_self_of_two_le (by omega) r).symm
  · exact (cyclicSucc_two_ne_self_of_three_le (by omega) r).symm
  · exact (cyclicSucc_three_ne_self_of_four_le (by omega) r).symm
  · exact (cyclicSucc_ne_self_of_two_le (by omega) (cyclicSucc r)).symm
  · exact (cyclicSucc_two_ne_self_of_three_le (by omega) (cyclicSucc r)).symm
  · exact
      (cyclicSucc_ne_self_of_two_le (by omega) (cyclicSucc (cyclicSucc r))).symm

/-- In an injectively labelled cyclic polygon, if every corner not touching
the distinguished owner `p` is the same vertex, there are at most three
owners. -/
theorem card_le_three_of_nonselected_corners_constant
    {k : ℕ} [DecidableEq I]
    (owner : Fin k → I) (vertex : Fin k → V)
    (howner : Function.Injective owner)
    (hvertex : Function.Injective vertex)
    (p : I) (v : V)
    (hconstant : ∀ t,
      owner t ≠ p → owner (cyclicSucc t) ≠ p → vertex t = v) :
    k ≤ 3 := by
  by_contra hk
  have hkfour : 4 ≤ k := by omega
  let leftBad : Finset (Fin k) :=
    Finset.univ.filter fun t ↦ owner t = p
  let rightBad : Finset (Fin k) :=
    Finset.univ.filter fun t ↦ owner (cyclicSucc t) = p
  have hleft : leftBad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    apply howner
    exact ((Finset.mem_filter.mp ht).2).trans
      ((Finset.mem_filter.mp hu).2).symm
  have hsucc : Function.Injective (cyclicSucc : Fin k → Fin k) :=
    (finRotate k).injective
  have hright : rightBad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    apply hsucc
    apply howner
    exact ((Finset.mem_filter.mp ht).2).trans
      ((Finset.mem_filter.mp hu).2).symm
  let bad := leftBad ∪ rightBad
  have hbad : bad.card ≤ 2 := by
    calc
      bad.card ≤ leftBad.card + rightBad.card := by
        simpa [bad] using Finset.card_union_le leftBad rightBad
      _ ≤ 2 := by omega
  let good := (Finset.univ : Finset (Fin k)) \ bad
  have hgood : 2 ≤ good.card := by
    have hbadsub : bad ⊆ (Finset.univ : Finset (Fin k)) :=
      Finset.subset_univ _
    have hsplit := Finset.card_sdiff_add_card_eq_card hbadsub
    change ((Finset.univ : Finset (Fin k)) \ bad).card + bad.card =
      (Finset.univ : Finset (Fin k)).card at hsplit
    simp only [Finset.card_univ, Fintype.card_fin] at hsplit
    change 2 ≤ ((Finset.univ : Finset (Fin k)) \ bad).card
    omega
  obtain ⟨t, ht, u, hu, htu⟩ := Finset.one_lt_card.mp (by omega : 1 < good.card)
  have htbad : t ∉ bad := (Finset.mem_sdiff.mp ht).2
  have hubad : u ∉ bad := (Finset.mem_sdiff.mp hu).2
  have htleft : owner t ≠ p := by
    intro h
    apply htbad
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have htright : owner (cyclicSucc t) ≠ p := by
    intro h
    apply htbad
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have huleft : owner u ≠ p := by
    intro h
    apply hubad
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have huright : owner (cyclicSucc u) ≠ p := by
    intro h
    apply hubad
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  apply htu
  apply hvertex
  rw [hconstant t htleft htright, hconstant u huleft huright]

/-- In an injectively labelled cyclic polygon, suppose that among any three
corners not touching the distinguished owner `p`, two of the corresponding
vertices coincide.  Then the polygon has at most four sides. -/
theorem card_le_four_of_nonselected_corners_no_three
    {k : ℕ} [DecidableEq I]
    (owner : Fin k → I) (vertex : Fin k → V)
    (howner : Function.Injective owner)
    (hvertex : Function.Injective vertex)
    (p : I)
    (hcollision : ∀ t u z,
      owner t ≠ p → owner (cyclicSucc t) ≠ p →
      owner u ≠ p → owner (cyclicSucc u) ≠ p →
      owner z ≠ p → owner (cyclicSucc z) ≠ p →
      vertex t = vertex u ∨ vertex t = vertex z ∨ vertex u = vertex z) :
    k ≤ 4 := by
  by_contra hk
  have hkfive : 5 ≤ k := by omega
  let leftBad : Finset (Fin k) :=
    Finset.univ.filter fun t ↦ owner t = p
  let rightBad : Finset (Fin k) :=
    Finset.univ.filter fun t ↦ owner (cyclicSucc t) = p
  have hleft : leftBad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    apply howner
    exact ((Finset.mem_filter.mp ht).2).trans
      ((Finset.mem_filter.mp hu).2).symm
  have hsucc : Function.Injective (cyclicSucc : Fin k → Fin k) :=
    (finRotate k).injective
  have hright : rightBad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    apply hsucc
    apply howner
    exact ((Finset.mem_filter.mp ht).2).trans
      ((Finset.mem_filter.mp hu).2).symm
  let bad := leftBad ∪ rightBad
  have hbad : bad.card ≤ 2 := by
    calc
      bad.card ≤ leftBad.card + rightBad.card := by
        simpa [bad] using Finset.card_union_le leftBad rightBad
      _ ≤ 2 := by omega
  let good := (Finset.univ : Finset (Fin k)) \ bad
  have hgood : 3 ≤ good.card := by
    have hbadsub : bad ⊆ (Finset.univ : Finset (Fin k)) :=
      Finset.subset_univ _
    have hsplit := Finset.card_sdiff_add_card_eq_card hbadsub
    change ((Finset.univ : Finset (Fin k)) \ bad).card + bad.card =
      (Finset.univ : Finset (Fin k)).card at hsplit
    simp only [Finset.card_univ, Fintype.card_fin] at hsplit
    change 3 ≤ ((Finset.univ : Finset (Fin k)) \ bad).card
    omega
  obtain ⟨t, u, z, ht, hu, hz, htu, htz, huz⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < good.card)
  have good_owner (x : Fin k) (hx : x ∈ good) :
      owner x ≠ p ∧ owner (cyclicSucc x) ≠ p := by
    have hxbad : x ∉ bad := (Finset.mem_sdiff.mp hx).2
    constructor
    · intro h
      apply hxbad
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · intro h
      apply hxbad
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  obtain ⟨htleft, htright⟩ := good_owner t ht
  obtain ⟨huleft, huright⟩ := good_owner u hu
  obtain ⟨hzleft, hzright⟩ := good_owner z hz
  rcases hcollision t u z htleft htright huleft huright hzleft hzright with
    htu' | htz' | huz'
  · exact htu (hvertex htu')
  · exact htz (hvertex htz')
  · exact huz (hvertex huz')

/-- If three consecutive corners whose four boundary owners all avoid `p`
are impossible, then an injectively owner-labelled cyclic polygon has at most
four sides.  This is the exact cyclic wrapper used in the collinear branch of
Levi's triangle theorem. -/
theorem card_le_four_of_three_consecutive_nonselected_corners_impossible
    {k : ℕ} [DecidableEq I]
    (owner : Fin k → I) (howner : Function.Injective owner) (p : I)
    (himpossible : ∀ t,
      owner t ≠ p →
      owner (cyclicSucc t) ≠ p →
      owner (cyclicSucc (cyclicSucc t)) ≠ p →
      owner (cyclicSucc (cyclicSucc (cyclicSucc t))) ≠ p → False) :
    k ≤ 4 := by
  by_contra hk
  have hkfive : 5 ≤ k := by omega
  by_cases hp : ∃ r, owner r = p
  · obtain ⟨r, hr⟩ := hp
    have hs1 : cyclicSucc r ≠ r := cyclicSucc_ne_self_of_two_le (by omega) r
    have hs2 : cyclicSucc (cyclicSucc r) ≠ r :=
      cyclicSucc_two_ne_self_of_three_le (by omega) r
    have hs3 : cyclicSucc (cyclicSucc (cyclicSucc r)) ≠ r :=
      cyclicSucc_three_ne_self_of_four_le (by omega) r
    have hs4 : cyclicSucc (cyclicSucc (cyclicSucc (cyclicSucc r))) ≠ r :=
      cyclicSucc_four_ne_self_of_five_le hkfive r
    have owner_ne (x : Fin k) (hx : x ≠ r) : owner x ≠ p := by
      intro hxp
      apply hx
      apply howner
      exact hxp.trans hr.symm
    exact himpossible (cyclicSucc r)
      (owner_ne _ hs1)
      (owner_ne _ hs2)
      (owner_ne _ hs3)
      (owner_ne _ hs4)
  · let r : Fin k := ⟨0, by omega⟩
    have owner_ne (x : Fin k) : owner x ≠ p := by
      intro hxp
      exact hp ⟨x, hxp⟩
    exact himpossible r (owner_ne _) (owner_ne _) (owner_ne _) (owner_ne _)

end Erdos735.LeviCyclicDegenerate
