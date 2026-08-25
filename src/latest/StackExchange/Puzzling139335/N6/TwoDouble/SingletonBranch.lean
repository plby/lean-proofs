import StackExchange.Puzzling139335.N6.TwoDouble.PairReduction

/-!
# A repeated full corner cannot occur in singleton pieces at six incidences

The proof uses the actual center exclusions supplied by corner and side
rigidity. If the repeated full-corner copies were singletons, the two
remaining pieces would have two corners each and use the same two types.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N6.TwoDouble

noncomputable section

private theorem other_counts_two {f : Fin 4 → ℕ} (hmax : ∀ i, f i ≤ 2)
    (hsum : (∑ i, f i) = 6) {i j : Fin 4} (hij : i ≠ j)
    (hi : f i = 1) (hj : f j = 1) {k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) :
    f k = 2 := by
  rw [CornerCounting.sum_fin_four] at hsum
  have h0 := hmax 0
  have h1 := hmax 1
  have h2 := hmax 2
  have h3 := hmax 3
  clear hmax
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

private theorem exists_fourth {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  have hcard : ({i, j, k} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    simp [hij, hik, hjk]
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨l, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hl⟩

/-- Two two-element subsets of a set of size at most three are equal if
both omit the same member of that ambient set. -/
theorem pair_eq_of_omitted_type {α : Type*}
    {U s t : Finset α} {r : α} (hU : U.card ≤ 3)
    (hs : s.card = 2) (ht : t.card = 2) (hsU : s ⊆ U) (htU : t ⊆ U)
    (hrU : r ∈ U) (hrs : r ∉ s) (hrt : r ∉ t) : s = t := by
  classical
  have hcard : (U.erase r).card ≤ 2 := by
    have := Finset.card_erase_add_one hrU
    omega
  have hs' : s ⊆ U.erase r := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, hsU hx⟩
    intro hxr
    exact hrs (hxr ▸ hx)
  have ht' : t ⊆ U.erase r := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, htU hx⟩
    intro hxr
    exact hrt (hxr ▸ hx)
  have hse := Finset.eq_of_subset_of_card_le hs' (by omega)
  have hte := Finset.eq_of_subset_of_card_le ht' (by omega)
  exact hse.trans hte.symm

/-- At six incidences and at most three used intrinsic types, two copies
of a uniquely owned corner type cannot each have only one square corner. -/
theorem not_singleton_repeated_unique (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    {i j a b : Fin 4} (hij : i ≠ j) (ha : corner a ∈ d.piece i)
    (hunique : ∀ l, l ≠ i → corner a ∉ d.piece l)
    (htype : d.intrinsicCorner i a = d.intrinsicCorner j b)
    (hi : d.tileCornerCount i = 1) : False := by
  classical
  have hj : d.tileCornerCount j = 1 :=
    (d.tileCornerCount_eq_of_repeated_unique_corner hunique htype).symm.trans hi
  have hsum : (∑ k, d.tileCornerCount k) = 6 :=
    d.cornerIncidenceCount_eq_sum_tileCornerCount.symm.trans hN
  have hother {k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) : d.tileCornerCount k = 2 :=
    other_counts_two (d.tileCornerCount_le_two hc) hsum hij hi hj hki hkj
  have hcenter := d.center_not_mem_of_repeated_unique_corner hij hunique htype
  obtain ⟨k, hk⟩ := hc
  have hki : k ≠ i := by
    intro hki
    exact hcenter.1 (hki ▸ hk)
  have hkj : k ≠ j := by
    intro hkj
    exact hcenter.2 (hkj ▸ hk)
  obtain ⟨l, hli, hlj, hlk⟩ := exists_fourth hij (Ne.symm hki) (Ne.symm hkj)
  have hr : d.intrinsicCorner i a ∈ d.usedCornerTypes :=
    d.mem_usedCornerTypes.mpr ⟨i, a, ha, rfl⟩
  have homit {m : Fin 4} (hmi : m ≠ i) (hmj : m ≠ j) :
      d.intrinsicCorner i a ∉ N8.intrinsicPair d m := by
    intro hrm
    obtain ⟨c, _, hmc⟩ := (N8.mem_intrinsicPair d m _).mp hrm
    have heq := d.tileCornerCount_eq_of_repeated_unique_corner hunique hmc.symm
    have hm := hother hmi hmj
    omega
  have hpair : N8.intrinsicPair d k = N8.intrinsicPair d l :=
    pair_eq_of_omitted_type hU
      ((N8.intrinsicPair_card d k).trans (hother hki hkj))
      ((N8.intrinsicPair_card d l).trans (hother hli hlj))
      (N8.intrinsicPair_subset_usedCornerTypes d k)
      (N8.intrinsicPair_subset_usedCornerTypes d l) hr
      (homit hki hkj) (homit hli hlj)
  exact (center_not_mem_of_pair_eq d ⟨k, hk⟩ (Ne.symm hlk)
    (hother hki hkj) hpair).1 hk

/-- A repeated full-corner type in the six-incidence branch is carried
by two-corner pieces. This discharges the singleton alternative before
any local-angle analysis is needed. -/
theorem repeated_unique_counts_two (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    {i j a b : Fin 4} (hij : i ≠ j) (ha : corner a ∈ d.piece i)
    (hunique : ∀ l, l ≠ i → corner a ∉ d.piece l)
    (htype : d.intrinsicCorner i a = d.intrinsicCorner j b) :
    d.tileCornerCount i = 2 ∧ d.tileCornerCount j = 2 := by
  have hpos : 0 < d.tileCornerCount i := by
    rw [← N8.cornerSet_card]
    exact Finset.card_pos.mpr ⟨a, (N8.mem_cornerSet d i a).mpr ha⟩
  have hle := d.tileCornerCount_le_two hc i
  have hne : d.tileCornerCount i ≠ 1 :=
    not_singleton_repeated_unique d hc hN hU hij ha hunique htype
  have hi : d.tileCornerCount i = 2 := by omega
  exact ⟨hi, (d.tileCornerCount_eq_of_repeated_unique_corner hunique htype).symm.trans hi⟩

end

end Puzzling139335.N6.TwoDouble
