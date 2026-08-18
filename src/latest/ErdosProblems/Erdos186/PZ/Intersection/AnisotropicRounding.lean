/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Zonotope

/-!
# Coordinate-adapted zonotope rounding

Normalizing each coordinate before applying the energy argument preserves
the separate source GAP widths.  This is essential: replacing them by one
uniform maximum destroys the scale hierarchy in Theorem 4.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

theorem exists_subset_sum_approximation_anisotropic
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ)
    (width : Fin d → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1)
    (hwidth : ∀ i, 0 < width i)
    (hv : ∀ a ∈ s, ∀ i, |v a i| ≤ width i) :
    ∃ t : Finset ι, t ⊆ s ∧ ∀ i,
      |(∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i| ≤
        Real.sqrt (((d * s.card : ℕ) : ℝ)) * width i := by
  let normalized : ι → Fin d → ℝ := fun a i ↦ v a i / width i
  have hnormalized : ∀ a ∈ s, ∀ i, |normalized a i| ≤ 1 := by
    intro a ha i
    change |v a i / width i| ≤ 1
    rw [abs_div, abs_of_pos (hwidth i), div_le_one (hwidth i)]
    exact hv a ha i
  obtain ⟨t, hts, ht⟩ :=
    Erdos186.Zonotope.exists_subset_sum_approximation
      s c normalized 1 hc (by norm_num) hnormalized
  refine ⟨t, hts, ?_⟩
  intro i
  have hi := ht i
  have hnormalize :
      (∑ a ∈ s, c a * normalized a i) -
          ∑ a ∈ t, normalized a i =
        ((∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i) / width i := by
    change (∑ a ∈ s, c a * (v a i / width i)) -
        ∑ a ∈ t, v a i / width i = _
    have hsum₁ :
        (∑ a ∈ s, c a * (v a i / width i)) =
          (∑ a ∈ s, c a * v a i) / width i := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    have hsum₂ :
        (∑ a ∈ t, v a i / width i) =
          (∑ a ∈ t, v a i) / width i := by
      rw [Finset.sum_div]
    calc
      (∑ a ∈ s, c a * (v a i / width i)) -
            ∑ a ∈ t, v a i / width i =
          (∑ a ∈ s, c a * v a i) / width i -
            (∑ a ∈ t, v a i) / width i := by rw [hsum₁, hsum₂]
      _ = ((∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i) / width i := by
            ring
  rw [hnormalize, abs_div, abs_of_pos (hwidth i)] at hi
  have hi' :
      |(∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i| / width i ≤
        Real.sqrt (((d * s.card : ℕ) : ℝ)) := by
    simpa using hi
  exact (div_le_iff₀ (hwidth i)).mp hi'

end

end Erdos186.PZ.Intersection
