import StackExchange.Puzzling139335.N4TwoOneOne.Configuration
import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds
import StackExchange.Puzzling139335.PlaneIsometries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The normalized angle comes from an actual singleton congruence

An orientation-preserving singleton map has its two upper-corner support
normals in the upper half-plane. A negative vertical component would force
their common maximizer to be one of the two bottom corners. The singleton
corner count has already excluded those two source points.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries

/-- Two perpendicular upper supports at a point other than the bottom
corners determine nonnegative entries in the normalized rotation. -/
theorem upper_support_rotation_nonneg {c s x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hA : ¬ (x = 0 ∧ y = 0)) (hB : ¬ (x = 1 ∧ y = 0))
    (heA : 0 ≤ c * x + s * y) (heB : c ≤ c * x + s * y)
    (hfA : 0 ≤ -s * x + c * y) (hfB : -s ≤ -s * x + c * y) :
    0 ≤ c ∧ 0 ≤ s := by
  have hc : 0 ≤ c := by
    by_contra hc
    have hc : c < 0 := lt_of_not_ge hc
    by_cases hs : 0 ≤ s
    · have hsy : 0 ≤ s * x := mul_nonneg hs hx0
      have hy0 : y = 0 := by nlinarith only [hfA, hsy, hc, hy]
      have hcx0 : 0 ≤ c * x := by
        simpa only [hy0, mul_zero, add_zero] using heA
      have hxzero : x = 0 := by nlinarith only [hcx0, hc, hx0]
      exact hA ⟨hxzero, hy0⟩
    · have hs : s < 0 := lt_of_not_ge hs
      have hcx : c * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hx0
      have hsy : s * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hy
      have hxzero : x = 0 := by nlinarith only [heA, hsy, hc, hx0]
      have hy0 : y = 0 := by nlinarith only [heA, hcx, hs, hy]
      exact hA ⟨hxzero, hy0⟩
  refine ⟨hc, ?_⟩
  by_contra hs
  have hs : s < 0 := lt_of_not_ge hs
  have hcx : c * x ≤ c := by nlinarith only [hc, hx1]
  have hy0 : y = 0 := by nlinarith only [heB, hcx, hs, hy]
  have hfx : -s ≤ -s * x := by
    simpa only [hy0, mul_zero, add_zero] using hfB
  have hxone : x = 1 := by nlinarith only [hfx, hs, hx1]
  exact hB ⟨hxone, hy0⟩

theorem exists_first_quadrant_angle {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) (Real.pi / 2) ∧
      Real.cos θ = c ∧ Real.sin θ = s := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hcneg : -1 ≤ c := by linarith
  refine ⟨Real.arccos c, ⟨Real.arccos_nonneg c, ?_⟩,
    Real.cos_arccos hcneg hc1, ?_⟩
  · simpa only [Real.arccos_zero] using Real.arccos_le_arccos hc
  · rw [Real.sin_arccos, show 1 - c ^ 2 = s ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

/-- The actual direct matrix of a singleton placement has a nonnegative
cosine and a nonnegative normalized sine. -/
theorem Configuration.direct_coefficients_nonneg {d : SquareDissection}
    (h : Configuration d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1) {c s : ℝ}
    (hform : ∀ p, e p = directCoordinates c (-s) (e 0) p) :
    0 ≤ c ∧ 0 ≤ s := by
  let C := e.symm (corner 2)
  have hC : C ∈ d.piece 0 := h.singleton_preimage_mem e he
  have hCS := d.piece_subset 0 hC
  have hCA : ¬ (C 0 = 0 ∧ C 1 = 0) := by
    rintro ⟨hx, hy⟩
    apply h.singleton_preimage_ne_bottom e he (Or.inl rfl)
    apply plane_ext
    · simpa [C, corner, Fin.ext_iff] using hx
    · simpa [C, corner, Fin.ext_iff] using hy
  have hCB : ¬ (C 0 = 1 ∧ C 1 = 0) := by
    rintro ⟨hx, hy⟩
    apply h.singleton_preimage_ne_bottom e he (Or.inr rfl)
    apply plane_ext
    · simpa [C, corner, Fin.ext_iff] using hx
    · simpa [C, corner, Fin.ext_iff] using hy
  have heC : e C = corner 2 := e.apply_symm_apply _
  have heC0 := congrArg (fun p : Plane => p 0) (hform C)
  have heC1 := congrArg (fun p : Plane => p 1) (hform C)
  rw [heC] at heC0 heC1
  norm_num [directCoordinates, corner, Fin.ext_iff] at heC0 heC1
  have hfit (p : Plane) (hp : p ∈ d.piece 0) : e p ∈ unitSquare := by
    apply d.piece_subset 1
    rw [← he]
    exact mem_image_of_mem e hp
  have hfitA := hfit (corner 0) h.bottom_left
  have hfitB := hfit (corner 1) h.bottom_right
  rw [hform] at hfitA hfitB
  norm_num [unitSquare, directCoordinates, corner, Fin.ext_iff] at hfitA hfitB
  apply upper_support_rotation_nonneg hCS.1.1 hCS.1.2 hCS.2.1 hCA hCB
  all_goals linarith

/-- A direct singleton placement produces the full normalized map data.
The angle interval and translation parameters are conclusions. -/
theorem Configuration.sourceData_of_direct {d : SquareDissection}
    (h : Configuration d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p = directCoordinates c (-s) (e 0) p) :
    ∃ θ u v : ℝ, SourceData d θ u v ∧ ∀ p, e p = rightMap θ u v p := by
  obtain ⟨hc, hs⟩ := h.direct_coefficients_nonneg e he hform
  obtain ⟨θ, hθ, hcos, hsin⟩ := exists_first_quadrant_angle hcs hc hs
  let u := 1 - (e 0) 0
  let v := 1 - (e 0) 1
  have hmap (p : Plane) : e p = rightMap θ u v p := by
    rw [hform]
    ext i
    fin_cases i <;> simp [directCoordinates, rightMap, eCoord, fCoord,
      hcos, hsin, u, v] <;> ring
  have hright : rightMap θ u v '' d.piece 0 = d.piece 1 := by
    have hfun : rightMap θ u v = e := funext fun p => (hmap p).symm
    rw [hfun, he]
  have hleft : leftMap θ u v '' d.piece 0 = d.piece 2 := by
    rw [← h.reflected, ← hright, image_image]
    congr 1
    funext p
    exact (vertical_rightMap θ u v p).symm
  exact ⟨θ, u, v,
    ⟨hθ.1, hθ.2, hright, hleft, h.bottom_left, h.bottom_right,
      h.top_right, h.top_left⟩, hmap⟩

end Puzzling139335.N4TwoOneOne
