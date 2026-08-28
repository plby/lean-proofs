import Wikipedia.HopfProblem.DegreeCollapsePuncturedSphereMaps
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# The exact endpoint-plus-meridian relation in a two-point complement

An outer sphere centered at zero encloses both punctures. Its positive
homology map equals the sum of an inner sphere around zero and a small
linking sphere around the second puncture, with the actual affine sphere
parametrizations. The proof uses the two genuine one-point complements,
explicit homotopies there, and Mayer--Vietoris injectivity.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoPunctureSphereMap (p q c : E) (r : ℝ)
    (hp : ∀ u : sphere (0 : E) 1, c + r • u.val ≠ p)
    (hq : ∀ u : sphere (0 : E) 1, c + r • u.val ≠ q) :
    C(sphere (0 : E) 1, twoPunctureSet p q) where
  toFun u := ⟨c + r • u.val, hp u, hq u⟩
  continuous_toFun := (continuous_const.add
    (continuous_const.smul continuous_subtype_val)).subtype_mk _

def innerSphere (b : E) (r : ℝ) (hr : 0 < r) (hrb : r < ‖b‖) :
    C(sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 r
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [sub_self, norm_zero] using hr.ne))
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [zero_sub, norm_neg] using hrb.ne'))

def outerSphere (b : E) (R : ℝ) (hbR : ‖b‖ < R) :
    C(sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 R
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [sub_self, norm_zero] using ((norm_nonneg b).trans_lt hbR).ne))
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [zero_sub, norm_neg] using hbR.ne))

def linkingSphere (b : E) (ε : ℝ) (hε : 0 < ε) (hεb : ε < ‖b‖) :
    C(sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b b ε
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_zero] using hεb.ne'))
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_self, norm_zero] using hε.ne))

theorem radial_sphere_homology_relation (b : E) {r R ε : ℝ}
    (hr : 0 < r) (hrb : r < ‖b‖) (hbR : ‖b‖ < R) (hε : 0 < ε) (hεb : ε < ‖b‖)
    (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (outerSphere b R hbR) n =
      singularHomologyMap (innerSphere b r hr hrb) n +
        singularHomologyMap (linkingSphere b ε hε hεb) n := by
  have hb : b ≠ 0 := norm_pos_iff.mp (hr.trans hrb)
  have hR : 0 < R := (norm_nonneg b).trans_lt hbR
  let i := firstPunctureInclusion (0 : E) b
  let j := secondPunctureInclusion (0 : E) b
  let inner := innerSphere b r hr hrb
  let outer := outerSphere b R hbR
  let link := linkingSphere b ε hε hεb
  have hio : (i.comp outer).Homotopic (i.comp inner) :=
    puncturedSphereMap_radius_homotopic 0 hR hr
      (fun u => (outer u).property.1) (fun u => (inner u).property.1)
  have hil : (i.comp link).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic 0 b hε.le
      (by simpa only [sub_zero] using hεb) (fun u => (link u).property.1)
  have hji : (j.comp inner).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic b 0 hr.le
      (by simpa only [zero_sub, norm_neg] using hrb) (fun u => (inner u).property.2)
  have hcenter : ∀ u : sphere (0 : E) 1, b + R • u.val ≠ b :=
    affine_sphere_ne_of_norm_ne hR.le (by simpa only [sub_self, norm_zero] using hR.ne)
  let center := puncturedSphereMap b b R hcenter
  have hoc : (j.comp outer).Homotopic center :=
    puncturedSphereMap_center_homotopic b 0
      (by simpa only [zero_sub, norm_neg] using hbR) (fun u => (outer u).property.2) hcenter
  have hcl : center.Homotopic (j.comp link) :=
    puncturedSphereMap_radius_homotopic b hR hε hcenter (fun u => (link u).property.2)
  have hjo := hoc.trans hcl
  have hioMap := homotopic_homologyMap hio n
  have hjoMap := homotopic_homologyMap hjo n
  have hilMap := CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic
    (i.comp link) hil n hn
  have hjiMap := CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic
    (j.comp inner) hji n hn
  apply LinearMap.ext
  intro a
  change singularHomologyMap outer n a =
    singularHomologyMap inner n a + singularHomologyMap link n a
  apply two_puncture_homology_ext hb.symm n
  · change singularHomologyMap i n (singularHomologyMap outer n a) = _
    rw [map_add]
    have ho : singularHomologyMap i n (singularHomologyMap outer n a) =
        singularHomologyMap i n (singularHomologyMap inner n a) := by
      simpa only [singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hioMap a
    have hl : singularHomologyMap i n (singularHomologyMap link n a) = 0 := by
      simpa only [singularHomologyMap_comp, LinearMap.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun hilMap a
    rw [ho, hl, add_zero]
  · change singularHomologyMap j n (singularHomologyMap outer n a) = _
    rw [map_add]
    have ho : singularHomologyMap j n (singularHomologyMap outer n a) =
        singularHomologyMap j n (singularHomologyMap link n a) := by
      simpa only [singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hjoMap a
    have hi : singularHomologyMap j n (singularHomologyMap inner n a) = 0 := by
      simpa only [singularHomologyMap_comp, LinearMap.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun hjiMap a
    rw [ho, hi, zero_add]

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
