import StackExchange.Puzzling139335.DoubleCorner.Reflection.Conjugation
import StackExchange.Puzzling139335.DoubleCorner.HalfGerm.Closure
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Rigidity of a forty-five-degree cone under isometric inclusion

An origin-fixing plane isometry cannot carry a closed forty-five-degree
cone strictly into itself. In the direct coordinate form the two boundary
rays force the identity. In the reversing form the isometry is an
involution, so inclusion already implies equality.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement

open AcuteCorner DoubleCorner PlaneIsometries ReflectionSeparation

private theorem image_eq_of_involutive_of_subset {f : Plane → Plane}
    {P : Set Plane} (hf : Function.Involutive f) (hsub : f '' P ⊆ P) :
    f '' P = P := by
  apply Subset.antisymm hsub
  intro p hp
  exact ⟨f p, hsub (mem_image_of_mem f hp), hf p⟩

/-- An affine Euclidean isometry fixing the vertex and carrying the lower
forty-five-degree cone into itself carries it onto itself. -/
theorem image_cone45_eq_of_subset (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he0 : e 0 = 0) (hsub : e '' cone45 ⊆ cone45) :
    e '' cone45 = cone45 := by
  obtain ⟨c, s, hcs, he | he⟩ := affine_coordinate_classification e
  · have hb : 0 ≤ s ∧ s ≤ c := by
      have h := hsub (mem_image_of_mem e
        (show (!₂[1, 0] : Plane) ∈ cone45 by norm_num [cone45]))
      simpa [he !₂[1, 0], he0, cone45, directCoordinates] using h
    have hd : 0 ≤ s + c ∧ s + c ≤ c - s := by
      have h := hsub (mem_image_of_mem e
        (show (!₂[1, 1] : Plane) ∈ cone45 by norm_num [cone45]))
      simpa [he !₂[1, 1], he0, cone45, directCoordinates] using h
    have hs : s = 0 := by linarith only [hb.1, hd.2]
    have hc : c = 1 := by nlinarith only [hcs, hb.2, hs]
    have heid (p : Plane) : e p = p := by
      rw [he p, he0, hc, hs]
      apply plane_ext <;> simp [directCoordinates]
    apply image_eq_of_involutive_of_subset _ hsub
    intro p
    rw [heid, heid]
  · exact image_eq_of_involutive_of_subset
      (involutive_of_reversing_coordinates e hcs he0 he) hsub

/-- The same rigidity holds when the target is the upper
forty-five-degree cone, by interchanging the two coordinates. -/
theorem image_cone45_eq_upper_of_subset (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he0 : e 0 = 0) (hsub : e '' cone45 ⊆ upperCone45) :
    e '' cone45 = upperCone45 := by
  let f := e.trans diagonal
  have hf0 : f 0 = 0 := by
    change diagonal (e 0) = 0
    rw [he0]
    apply plane_ext <;> simp
  have hfsub : f '' cone45 ⊆ cone45 := by
    rintro p ⟨q, hq, rfl⟩
    change 0 ≤ e q 0 ∧ e q 0 ≤ e q 1
    exact hsub (mem_image_of_mem e hq)
  have hf := image_cone45_eq_of_subset f hf0 hfsub
  apply Subset.antisymm hsub
  intro p hp
  have hd : diagonal p ∈ f '' cone45 := by
    rw [hf]
    exact hp
  obtain ⟨q, hq, heq⟩ := hd
  refine ⟨q, hq, ?_⟩
  change diagonal (e q) = diagonal p at heq
  exact diagonal.injective heq

end Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement
