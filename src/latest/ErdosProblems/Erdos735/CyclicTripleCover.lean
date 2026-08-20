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

import ErdosProblems.Erdos735.ChartOrder

/-!
# Three consecutive intervals exhaust a finite cyclic order

This is the finite order lemma used by the triangle exceptional pattern: if
three distinct vertices follow one another cyclically and the third is
followed by the first, then there are no further vertices.
-/

open Classical

namespace Erdos735.ChartOrder

variable {V : Type*} [DecidableEq V]

private theorem eq_of_coord_eq
    {coord : V → ℝ} {S : Finset V}
    (hinj : Set.InjOn coord (S : Set V))
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : coord x = coord y) : x = y :=
  hinj hx hy hxy

/-- Three pairwise-distinct vertices which form a complete cycle of cyclic
consecutive pairs are all the vertices of the finite cyclic order. -/
theorem eq_triple_of_cyclicConsecutive_cycle
    (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V))
    {a b c : V} (habne : a ≠ b) (hbcne : b ≠ c) (hcane : c ≠ a)
    (hab : CyclicConsecutive coord S a b)
    (hbc : CyclicConsecutive coord S b c)
    (hca : CyclicConsecutive coord S c a) :
    S = {a, b, c} := by
  have ha := hab.left_mem
  have hb := hab.right_mem
  have hc := hbc.right_mem
  apply Finset.Subset.antisymm
  · intro x hx
    have finish (hxa : coord x = coord a ∨
        coord x = coord b ∨ coord x = coord c) : x ∈ ({a, b, c} : Finset V) := by
      rcases hxa with hxa | hxb | hxc
      · exact Finset.mem_insert.mpr <| Or.inl
          (eq_of_coord_eq hinj hx ha hxa)
      · exact Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_insert.mpr <| Or.inl (eq_of_coord_eq hinj hx hb hxb)
      · exact Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_insert.mpr <| Or.inr <|
            Finset.mem_singleton.mpr (eq_of_coord_eq hinj hx hc hxc)
    rcases hab with hab | ⟨ha', hb', hamax, hbmin⟩ <;>
      rcases hbc with hbc | ⟨hb'', hc', hbmax, hcmin⟩ <;>
      rcases hca with hca | ⟨hc'', ha'', hcmax, hamin⟩
    · exfalso
      linarith [hab.lt, hbc.lt, hca.lt]
    · by_cases hxa : coord x = coord a
      · exact finish (Or.inl hxa)
      by_cases hxb : coord x = coord b
      · exact finish (Or.inr (Or.inl hxb))
      by_cases hxc : coord x = coord c
      · exact finish (Or.inr (Or.inr hxc))
      have hax : coord a < coord x := lt_of_le_of_ne (hamin x hx) (Ne.symm hxa)
      have hxc' : coord x < coord c := lt_of_le_of_ne (hcmax x hx) hxc
      by_cases hxb' : coord x < coord b
      · exact (hab.no_between hx ⟨hax, hxb'⟩).elim
      · have hbx : coord b < coord x := lt_of_le_of_ne (le_of_not_gt hxb') (Ne.symm hxb)
        exact (hbc.no_between hx ⟨hbx, hxc'⟩).elim
    · by_cases hxa : coord x = coord a
      · exact finish (Or.inl hxa)
      by_cases hxb : coord x = coord b
      · exact finish (Or.inr (Or.inl hxb))
      by_cases hxc : coord x = coord c
      · exact finish (Or.inr (Or.inr hxc))
      have hcx : coord c < coord x := lt_of_le_of_ne (hcmin x hx) (Ne.symm hxc)
      have hxb' : coord x < coord b := lt_of_le_of_ne (hbmax x hx) hxb
      by_cases hxa' : coord x < coord a
      · exact (hca.no_between hx ⟨hcx, hxa'⟩).elim
      · have hax : coord a < coord x := lt_of_le_of_ne (le_of_not_gt hxa') (Ne.symm hxa)
        exact (hab.no_between hx ⟨hax, hxb'⟩).elim
    · exfalso
      linarith [hab.lt, hcmin a ha, hcmax b hb]
    · by_cases hxa : coord x = coord a
      · exact finish (Or.inl hxa)
      by_cases hxb : coord x = coord b
      · exact finish (Or.inr (Or.inl hxb))
      by_cases hxc : coord x = coord c
      · exact finish (Or.inr (Or.inr hxc))
      have hbx : coord b < coord x := lt_of_le_of_ne (hbmin x hx) (Ne.symm hxb)
      have hxa' : coord x < coord a := lt_of_le_of_ne (hamax x hx) hxa
      by_cases hxc' : coord x < coord c
      · exact (hbc.no_between hx ⟨hbx, hxc'⟩).elim
      · have hcx : coord c < coord x := lt_of_le_of_ne (le_of_not_gt hxc') (Ne.symm hxc)
        exact (hca.no_between hx ⟨hcx, hxa'⟩).elim
    · exfalso
      linarith [hbc.lt, hamin b hb, hamax c hc]
    · exfalso
      have hbcCoord : coord b = coord c := le_antisymm
        (hbmin c hc') (hbmax c hc')
      exact hbcne (eq_of_coord_eq hinj hb hc hbcCoord)
    · exfalso
      have hbcCoord : coord b = coord c := le_antisymm
        (hbmin c hc') (hbmax c hc')
      exact hbcne (eq_of_coord_eq hinj hb hc hbcCoord)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

/-- Cardinal form of `eq_triple_of_cyclicConsecutive_cycle`. -/
theorem card_eq_three_of_cyclicConsecutive_cycle
    (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V))
    {a b c : V} (habne : a ≠ b) (hbcne : b ≠ c) (hcane : c ≠ a)
    (hab : CyclicConsecutive coord S a b)
    (hbc : CyclicConsecutive coord S b c)
    (hca : CyclicConsecutive coord S c a) :
    S.card = 3 := by
  rw [eq_triple_of_cyclicConsecutive_cycle coord S hinj habne hbcne hcane hab hbc hca]
  simp [habne, hbcne, hcane, hcane.symm]

end Erdos735.ChartOrder
