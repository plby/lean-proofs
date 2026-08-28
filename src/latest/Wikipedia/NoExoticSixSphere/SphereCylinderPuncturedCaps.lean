import Wikipedia.NoExoticSixSphere.SphereCylinderCaps
import Mathlib.Analysis.Convex.Contractible

/-!
# Actual sphere models for the punctured endpoint caps

The cylinder coordinates identify each punctured cap with a sphere times
an open time ray. Contracting that ray gives a homotopy equivalence whose
inverse is the actual time slice at minus one or two.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def capTime (b : Bool) : Set ℝ := if b then Ioi 1 else Iio 0

def capBaseTime (b : Bool) : capTime b :=
  ⟨if b then 2 else -1, by cases b <;> norm_num [capTime]⟩

theorem convex_capTime (b : Bool) : Convex ℝ (capTime b) := by
  cases b
  · exact convex_Iio 0
  · exact convex_Ioi 1

def puncturedCap (n : ℕ) (b : Bool) : Set (Sphere (n + 1)) :=
  capRegion n b \ {endPole n b}

theorem puncturedCap_subset_band (n : ℕ) (b : Bool) : puncturedCap n b ⊆ band n := by
  intro y hy
  by_contra hn
  rcases (not_mem_band_iff n y).mp hn with he | he
  · subst y
    cases b
    · exact hy.2 rfl
    · have h := hy.1
      change ‖tail n (endPole n false).val‖ < (endPole n false).val 0 at h
      norm_num [tail_endPole, endPole_head] at h
  · subst y
    cases b
    · have h := hy.1
      change (endPole n true).val 0 < 0 at h
      norm_num [endPole_head] at h
    · exact hy.2 rfl

theorem point_mem_capRegion_iff (n : ℕ) (b : Bool) (p : ℝ × Sphere n) :
    point n p ∈ capRegion n b ↔ p.1 ∈ capTime b := by
  cases b
  · exact point_mem_lowerCap_iff n p
  · exact point_mem_upperCap_iff n p

theorem point_mem_puncturedCap_iff (n : ℕ) (b : Bool) (p : ℝ × Sphere n) :
    point n p ∈ puncturedCap n b ↔ p.1 ∈ capTime b := by
  constructor
  · exact fun hp ↦ (point_mem_capRegion_iff n b p).mp hp.1
  · intro hp
    refine ⟨(point_mem_capRegion_iff n b p).mpr hp, ?_⟩
    intro he
    exact endPole_not_mem_band n b (he ▸ tail_point_ne_zero n p)

def capCoordinates (n : ℕ) (b : Bool) : puncturedCap n b ≃ₜ Sphere n × capTime b where
  toFun y := ((inverse n y.val).2, ⟨(inverse n y.val).1, by
    apply (point_mem_capRegion_iff n b _).mp
    rw [point_inverse n y.val (puncturedCap_subset_band n b y.property)]
    exact y.property.1⟩)
  invFun p := ⟨point n (p.2.val, p.1),
    (point_mem_puncturedCap_iff n b _).mpr p.2.property⟩
  left_inv y := Subtype.ext (point_inverse n y.val (puncturedCap_subset_band n b y.property))
  right_inv p := by
    apply Prod.ext
    · exact congrArg Prod.snd (inverse_point n (p.2.val, p.1))
    · exact Subtype.ext (congrArg Prod.fst (inverse_point n (p.2.val, p.1)))
  continuous_toFun := by
    have hc : Continuous (fun y : puncturedCap n b ↦ inverse n y.val) :=
      ((chart n).contMDiffOn_invFun.continuousOn.mono (puncturedCap_subset_band n b)).domRestrict
    exact hc.snd.prodMk (hc.fst.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (point n).continuous.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

def capTimeContraction (b : Bool) : (ContinuousMap.id (capTime b)).Homotopy
    (ContinuousMap.const _ (capBaseTime b)) where
  toFun p := ⟨(p.1 : ℝ) * (capBaseTime b).val + (1 - (p.1 : ℝ)) * p.2.val,
    (convex_capTime b) (capBaseTime b).property p.2.property
      p.1.property.1 (sub_nonneg.mpr p.1.property.2) (add_sub_cancel _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd))
  map_zero_left t := Subtype.ext (by simp)
  map_one_left t := Subtype.ext (by simp)

def capTimePointEquiv (b : Bool) : capTime b ≃ₕ Unit where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ (capBaseTime b)
  left_inv := ⟨(capTimeContraction b).symm⟩
  right_inv := by
    convert Homotopic.refl (ContinuousMap.id Unit) using 1
    ext u

def capProductSphereEquiv (n : ℕ) (b : Bool) : (Sphere n × capTime b) ≃ₕ Sphere n :=
  ((ContinuousMap.HomotopyEquiv.refl (Sphere n)).prodCongr (capTimePointEquiv b)).trans
    (Homeomorph.prodUnique (Sphere n) Unit).toHomotopyEquiv

def capSphereEquiv (n : ℕ) (b : Bool) : puncturedCap n b ≃ₕ Sphere n :=
  (capCoordinates n b).toHomotopyEquiv.trans (capProductSphereEquiv n b)

theorem capSphereEquiv_symm_apply (n : ℕ) (b : Bool) (s : Sphere n) :
    ((capSphereEquiv n b).symm s).val = point n ((capBaseTime b).val, s) := rfl

end NoExoticSixSphere.SphereCylinder
