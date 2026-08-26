/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The uniform good/bad coordinate alternative for finite box covers.
Informal source: BBMST Lemma 3.4(b,c). We use the rational garbage weight (5/6)^m.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GoodCoordinates

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

def CoordinateAlternativeAt (H : α → Box q) (A : Finset α) (lam ε δ : ℝ) (i : ι) : Prop :=
    (∃ F ⊆ A, (1 - ε) * ((q i : ℝ) - 1) ≤ (F.card : ℝ) ∧
      ∀ a ∈ F, i ∈ fixed (H a) ∧ δ < boxMeasureOn (univ.erase i) (H a)) ∨
    (∃ G ⊆ A, (q i : ℝ) / lam ≤ ∑ a ∈ G, (5 / 6 : ℝ) ^ (fixed (H a)).card ∧
      ∀ a ∈ G, i ∈ fixed (H a) ∧ 2 ≤ (fixed (H a)).card)

def CoordinateAlternative (H : α → Box q) (A : Finset α) (lam ε δ : ℝ) : Prop :=
  ∃ i : ι, CoordinateAlternativeAt H A lam ε δ i

lemma CoordinateAlternativeAt.mem_familyFixed {H : α → Box q} {A : Finset α}
    {lam ε δ : ℝ} {i : ι} (h : CoordinateAlternativeAt H A lam ε δ i)
    (hlam : 0 < lam) (hε : ε < 1) (hq : 2 ≤ q i) : i ∈ familyFixed H A := by
  have hqi : (1 : ℝ) < q i := by exact_mod_cast (show 1 < q i by omega)
  rcases h with ⟨F, hFA, hcard, hF⟩ | ⟨G, hGA, hsum, hG⟩
  · have hpos : (0 : ℝ) < F.card :=
      (mul_pos (sub_pos.mpr hε) (sub_pos.mpr hqi)).trans_le hcard
    have hnonempty : F.Nonempty := card_pos.mp (by exact_mod_cast hpos)
    obtain ⟨a, ha⟩ := hnonempty
    exact Grid.mem_familyFixed.mpr ⟨a, hFA ha, (hF a ha).1⟩
  · have hnonempty : G.Nonempty := by
      by_contra hnot
      rw [not_nonempty_iff_eq_empty.mp hnot, sum_empty] at hsum
      have hpos := div_pos (zero_lt_one.trans hqi) hlam
      linarith
    obtain ⟨a, ha⟩ := hnonempty
    exact Grid.mem_familyFixed.mpr ⟨a, hGA ha, (hG a ha).1⟩

lemma coordinate_alternative_of_cutoff {lam ε δ : ℝ} (hlam : 0 < lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ1 : δ < 1)
    (hcut : ∀ m : ℕ, ∀ z : ℝ, z ≤ δ / ε ^ m → z ≤ (2 / ε) * (1 / 2 : ℝ) ^ m →
      z ≤ (lam / 16) * (35 / 48 : ℝ) ^ m)
    (H : α → Box q) (A : Finset α) (hq : ∀ i, 2 ≤ q i)
    (hfixed : ∀ a ∈ A, (fixed (H a)).Nonempty) (hcover : CoversOn H A Set.univ) :
    CoordinateAlternative H A lam ε δ := by
  classical
  let R := remainingValues H A δ
  by_cases hfew : ∃ i, ((R i).card : ℝ) < ε * ((q i : ℝ) - 1) + 1
  · obtain ⟨i, hi⟩ := hfew
    refine ⟨i, Or.inl ⟨goodBoxFamily H A δ i, filter_subset _ _,
      good_family_of_few_remaining H A δ ε hi, ?_⟩⟩
    intro a ha
    exact (mem_filter.mp ha).2
  · have hlarge : ∀ i, ε * ((q i : ℝ) - 1) + 1 ≤ (R i).card := by
      intro i
      exact le_of_not_gt (fun h => hfew ⟨i, h⟩)
    have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by norm_num) (hq i)
    have hR2 : ∀ i, 2 ≤ (R i).card := by
      intro i
      have hqi : (2 : ℝ) ≤ q i := by exact_mod_cast hq i
      have hpos : 0 < ε * ((q i : ℝ) - 1) := mul_pos hε (by linarith)
      have hgt : (1 : ℝ) < (R i).card := by linarith [hlarge i]
      exact_mod_cast hgt
    have hrel : ∀ i, ε * q i ≤ (R i).card := by
      intro i
      linarith [hlarge i]
    let A' := restrictionFamily R H A
    have hcompat : ∀ a ∈ A', RestrictionCompatible R (H a) := fun a ha => (mem_filter.mp ha).2
    have hA'A : A' ⊆ A := filter_subset _ _
    have hnewcover := hcover.restrict_values R
    have hnewfixed : ∀ a ∈ A', (fixed (restrictedBox R (H a))).Nonempty := by
      intro a ha
      rw [fixed_restrictedBox R (hcompat a ha)]
      exact hfixed a (hA'A ha)
    obtain ⟨i, hweight⟩ := exists_large_incident_weight (fun a => restrictedBox R (H a)) A'
      (fun i => by have := hR2 i; omega) hnewfixed hnewcover
    let G := A'.filter fun a => i ∈ fixed (restrictedBox R (H a))
    have hGA' : G ⊆ A' := filter_subset _ _
    have hiG : ∀ a ∈ G, i ∈ fixed (H a) := by
      intro a ha
      have hi := (mem_filter.mp ha).2
      rwa [fixed_restrictedBox R (hcompat a (hGA' ha))] at hi
    refine ⟨i, Or.inr ⟨G, hGA'.trans hA'A, ?_, fun a ha => ⟨hiG a ha,
      surviving_box_two_fixed H A hδ1 hfixed (hGA' ha)⟩⟩⟩
    have hsum : (∑ a ∈ G, localBoxWeight (restrictedBox R (H a))) * q i ≤
        (lam / 16) * ∑ a ∈ G, (5 / 6 : ℝ) ^ (fixed (H a)).card := by
      rw [sum_mul, mul_sum]
      apply sum_le_sum
      intro a ha
      exact restricted_weight_bound_of_cutoff hε hcut R (H a) (hcompat a (hGA' ha))
        hqpos hR2 hrel i (hiG a ha) (surviving_box_small H A δ (hGA' ha) (hiG a ha))
    change (1 / 8 : ℝ) < ∑ a ∈ G, localBoxWeight (restrictedBox R (H a)) at hweight
    have hqi : (0 : ℝ) < q i := by exact_mod_cast hqpos i
    have hstrict := mul_lt_mul_of_pos_right hweight hqi
    apply (div_le_iff₀ hlam).mpr
    nlinarith

end Erdos1189.Grid

namespace Erdos1189

/-- The cutoff depends only on the error parameters, uniformly over all finite grids. -/
theorem exists_uniform_coordinate_dichotomy {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (ι α : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℕ)
        (H : α → Grid.Box q) (A : Finset α),
        (∀ i, 2 ≤ q i) → (∀ a ∈ A, (Grid.fixed (H a)).Nonempty) →
        Grid.CoversOn H A Set.univ → Grid.CoordinateAlternative H A lam ε δ := by
  obtain ⟨δ, hδ, hδ1, hcut⟩ := exists_small_measure_cutoff hlam hε hε1
  exact ⟨δ, hδ, hδ1, fun _ _ _ _ _ H A hq hfixed hcover =>
    Grid.coordinate_alternative_of_cutoff hlam hε hε1 hδ1 hcut H A hq hfixed hcover⟩

end Erdos1189
