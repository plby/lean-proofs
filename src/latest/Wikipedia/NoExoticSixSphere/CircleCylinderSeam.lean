import Wikipedia.NoExoticSixSphere.CircleCylinderNativeFiber

/-!
# The actual seam time on the compact circle double

The second circle coordinate is a global smooth time. Its zero set
is precisely the union of the two original endpoint inclusions. The
clock always lies in the original closed cylinder interval.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

local instance : Fact (Module.finrank ℝ V = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩

def seamLinear : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun v := v 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }

def seam (c : Sphere 1) : ℝ := seamLinear c.val

theorem seam_apply (c : Sphere 1) : seam c = c.val 1 := rfl

theorem contMDiff_seam : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ seam := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, V) ∞ (Subtype.val : Sphere 1 → V) :=
    contMDiff_coe_sphere
  exact seamLinear.contDiff.contMDiff.comp hc

theorem seam_left : seam (SphereCylinder.endPole 0 true) = 0 := rfl

theorem seam_right : seam (SphereCylinder.endPole 0 false) = 0 := rfl

theorem seam_eq_zero_iff (c : Sphere 1) :
    seam c = 0 ↔ c = SphereCylinder.endPole 0 true ∨ c = SphereCylinder.endPole 0 false := by
  constructor
  · intro hc
    have hb : c ∉ SphereCylinder.band 0 := by
      intro h
      apply h
      ext i
      fin_cases i
      exact hc
    exact ((SphereCylinder.not_mem_band_iff 0 c).mp hb).symm
  · rintro (rfl | rfl)
    · exact seam_left
    · exact seam_right

theorem clock_mem_interval (c : Sphere 1) : clock c ∈ Icc (0 : ℝ) 1 := by
  have hh : |c.val 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs, ClosedHemisphere.unit_norm] using PiLp.norm_apply_le c.val 0
  obtain ⟨hlo, hhi⟩ := abs_le.mp hh
  rw [clock_apply]
  constructor <;> linarith

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def time (p : Fiber d) : ℝ := seam p.val.1

theorem contMDiff_time (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, ℝ) ∞ (time d) := by
  let := fiberAtlas d k hd
  exact contMDiff_seam.comp (contMDiff_fst.comp
    (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (dimension_eq k hd)))

theorem time_leftInclusion (x : {x : Sphere m // d.leftMap x = b}) :
    time d (leftInclusion d x) = 0 := seam_left

theorem time_rightInclusion (x : {x : Sphere m // d.rightMap x = b}) :
    time d (rightInclusion d x) = 0 := seam_right

theorem time_eq_zero_iff (p : Fiber d) : time d p = 0 ↔
    (∃ x, leftInclusion d x = p) ∨ ∃ y, rightInclusion d y = p := by
  constructor
  · intro hp
    rcases (seam_eq_zero_iff p.val.1).mp hp with hl | hr
    · left
      have hx : d.leftMap p.val.2 = b := by
        have he : map d (SphereCylinder.endPole 0 true, p.val.2) = b := by
          rw [← hl]
          exact p.property
        rwa [map_left] at he
      refine ⟨⟨p.val.2, hx⟩, Subtype.ext ?_⟩
      exact Prod.ext hl.symm rfl
    · right
      have hx : d.rightMap p.val.2 = b := by
        have he : map d (SphereCylinder.endPole 0 false, p.val.2) = b := by
          rw [← hr]
          exact p.property
        rwa [map_right] at he
      refine ⟨⟨p.val.2, hx⟩, Subtype.ext ?_⟩
      exact Prod.ext hr.symm rfl
  · rintro (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact time_leftInclusion d x
    · exact time_rightInclusion d y

end NoExoticSixSphere.CircleCylinder
