import StackExchange.Puzzling139335.N5Facet.Aligned

/-!
# The translated aligned placement has incompatible support contacts

The source contains `(0,0)` and `(1,0)` and lies in the strip
`0 ≤ x ≤ 1`, `0 ≤ y`.  The union of its aligned image and a strictly
leftward translate has two distinct lowest points but only one leftmost
point, so it cannot be invariant under diagonal reflection.
-/

namespace Puzzling139335.N5Facet

def alignedImageMap (c s u v : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (u - s * p.1 + c * p.2, v + c * p.1 + s * p.2)

def alignedTranslatedMap (c s T u v : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((alignedImageMap c s u v p).1 - T, (alignedImageMap c s u v p).2)

def alignedTranslatedUnion (P : Set (ℝ × ℝ)) (c s T u v : ℝ) : Set (ℝ × ℝ) :=
  alignedImageMap c s u v '' P ∪ alignedTranslatedMap c s T u v '' P

private theorem image_coordinate_bounds {c s u v : ℝ} {p : ℝ × ℝ}
    (hc : 0 < c) (hs : 0 < s)
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2) :
    u - s ≤ (alignedImageMap c s u v p).1 ∧
      v ≤ (alignedImageMap c s u v p).2 := by
  dsimp [alignedImageMap]
  constructor
  · nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hp.2.1),
      mul_nonneg hc.le hp.2.2]
  · nlinarith only [mul_nonneg hc.le hp.1, mul_nonneg hs.le hp.2.2]

private theorem translated_min_source {c s T u v : ℝ} {p : ℝ × ℝ}
    (hc : 0 < c) (hs : 0 < s)
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2)
    (hmin : (alignedTranslatedMap c s T u v p).1 = u - s - T) :
    p = (1, 0) := by
  have hx : 0 ≤ s * (1 - p.1) := mul_nonneg hs.le (sub_nonneg.mpr hp.2.1)
  have hy : 0 ≤ c * p.2 := mul_nonneg hc.le hp.2.2
  have hsum : s * (1 - p.1) + c * p.2 = 0 := by
    dsimp [alignedTranslatedMap, alignedImageMap] at hmin
    nlinarith only [hmin]
  have hxzero : s * (1 - p.1) = 0 := by linarith
  have hyzero : c * p.2 = 0 := by linarith
  have hxone : p.1 = 1 := by
    have hx' : 1 - p.1 = 0 := (mul_eq_zero.mp hxzero).resolve_left (ne_of_gt hs)
    linarith
  have hyzero' : p.2 = 0 := (mul_eq_zero.mp hyzero).resolve_left (ne_of_gt hc)
  exact Prod.ext hxone hyzero'

/-- The complete coordinate-set obstruction for the translated incoming-aligned
case.  No compactness, polygonality, or regularity assumption is needed. -/
theorem aligned_translation_impossible {P : Set (ℝ × ℝ)} {c s T u v : ℝ}
    (hA : (0, 0) ∈ P) (hB : (1, 0) ∈ P)
    (hbounds : ∀ p ∈ P, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2)
    (hc : 0 < c) (hs : 0 < s) (hT : 0 < T)
    (hstable : ∀ p ∈ alignedTranslatedUnion P c s T u v,
      (p.2, p.1) ∈ alignedTranslatedUnion P c s T u v) : False := by
  refine diagonal_support_contact_mismatch
    (alignedTranslatedUnion P c s T u v) Prod.fst Prod.snd Prod.swap
    hstable (fun _ => rfl) (fun _ => rfl)
    (mx := u - s - T) (my := v) ?_ ?_
    (r := alignedTranslatedMap c s T u v (1, 0))
    (a := alignedImageMap c s u v (0, 0))
    (b := alignedTranslatedMap c s T u v (0, 0))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rcases hw with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · have h := (image_coordinate_bounds (u := u) (v := v) hc hs (hbounds p hp)).1
      linarith only [h, hT]
    · have h := (image_coordinate_bounds (u := u) (v := v) hc hs (hbounds p hp)).1
      exact sub_le_sub_right h T
  · intro w hw
    rcases hw with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (image_coordinate_bounds (u := u) (v := v) hc hs (hbounds p hp)).2
    · exact (image_coordinate_bounds (u := u) (v := v) hc hs (hbounds p hp)).2
  · exact Or.inr (Set.mem_image_of_mem _ hB)
  · exact Or.inl (Set.mem_image_of_mem _ hA)
  · exact Or.inr (Set.mem_image_of_mem _ hA)
  · simp [alignedTranslatedMap, alignedImageMap]
  · simp [alignedImageMap]
  · simp [alignedTranslatedMap, alignedImageMap]
  · intro w hw hmin
    rcases hw with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · have h := (image_coordinate_bounds (u := u) (v := v) hc hs (hbounds p hp)).1
      exfalso
      linarith only [h, hT, hmin]
    · rw [translated_min_source hc hs (hbounds p hp) hmin]
  · simp only [alignedTranslatedMap, alignedImageMap, mul_zero,
      sub_zero, add_zero]
    linarith only [hT]

end Puzzling139335.N5Facet
