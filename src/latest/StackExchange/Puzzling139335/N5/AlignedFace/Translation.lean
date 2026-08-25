import StackExchange.Puzzling139335.N5Facet.TranslationAligned
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Plane form of the translated aligned-face obstruction

The actual placements are given as maps on the Euclidean plane. Passing
to their two coordinates identifies their union with the scalar union in
`N5Facet.aligned_translation_impossible`, including its diagonal symmetry.
No new support-contact argument is needed here.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

/-- An incoming-aligned image and its strict leftward translate cannot
form a union invariant under the actual square-diagonal reflection. -/
theorem translation_impossible {P : Set Plane} (R D : Plane → Plane)
    {c s T u v : ℝ} (hP : P ⊆ unitSquare)
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P)
    (hc : 0 < c) (hs : 0 < s) (hT : 0 < T)
    (hR : ∀ p, R p = !₂[u - s * p 0 + c * p 1, v + c * p 0 + s * p 1])
    (hD : ∀ p, D p = !₂[(R p) 0 - T, (R p) 1])
    (hstable : ∀ p ∈ R '' P ∪ D '' P,
      ReflectionSeparation.diagonal p ∈ R '' P ∪ D '' P) : False := by
  let toPair : Plane → ℝ × ℝ := fun p => (p 0, p 1)
  have hRpair (p : Plane) :
      toPair (R p) = N5Facet.alignedImageMap c s u v (toPair p) := by
    rw [hR]
    rfl
  have hDpair (p : Plane) :
      toPair (D p) = N5Facet.alignedTranslatedMap c s T u v (toPair p) := by
    rw [hD, hR]
    rfl
  have hRimage : toPair '' (R '' P) =
      N5Facet.alignedImageMap c s u v '' (toPair '' P) := by
    rw [image_image, image_image]
    congr 1
    funext p
    exact hRpair p
  have hDimage : toPair '' (D '' P) =
      N5Facet.alignedTranslatedMap c s T u v '' (toPair '' P) := by
    rw [image_image, image_image]
    congr 1
    funext p
    exact hDpair p
  have hUnion : toPair '' (R '' P ∪ D '' P) =
      N5Facet.alignedTranslatedUnion (toPair '' P) c s T u v := by
    rw [image_union, hRimage, hDimage]
    rfl
  have hA' : (0, 0) ∈ toPair '' P := by
    refine ⟨corner 0, hA, ?_⟩
    norm_num [toPair, corner, Fin.ext_iff]
  have hB' : (1, 0) ∈ toPair '' P := by
    refine ⟨corner 1, hB, ?_⟩
    norm_num [toPair, corner, Fin.ext_iff]
  refine N5Facet.aligned_translation_impossible (c := c) (s := s)
    (T := T) (u := u) (v := v) hA' hB' ?_ hc hs hT ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hP hp).1.1, (hP hp).1.2, (hP hp).2.1⟩
  · intro p hp
    rw [← hUnion] at hp ⊢
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨ReflectionSeparation.diagonal q, hstable q hq, rfl⟩

end Puzzling139335.N5.AlignedFace
