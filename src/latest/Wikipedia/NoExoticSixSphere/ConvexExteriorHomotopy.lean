import Wikipedia.NoExoticSixSphere.BallExteriorHomotopy
import Mathlib.Analysis.Convex.Basic

/-!
# Radial deformation outside an actual bounded convex support

For a convex subset containing zero and contained strictly inside a sphere,
the original complement retracts radially onto that enclosing sphere.
Outward scaling cannot enter the convex support; inward scaling from
beyond the sphere stays outside its enclosing radius. No interior point
or full-dimensionality assumption on the support is used.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.ConvexExterior

open Wikipedia.SmoothSixDPoincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Space (K : Set E) := Kᶜ

omit [NormedSpace ℝ E] in
theorem ne_zero (K : Set E) (h0 : (0 : E) ∈ K) (x : Space K) : (x : E) ≠ 0 := by
  intro hx
  exact x.property (hx.symm ▸ h0)

/-- Outward radial scaling cannot enter the convex support. -/
theorem smul_not_mem (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (x : E) (hx : x ∉ K) (a : ℝ) (ha : 1 ≤ a) : a • x ∉ K := by
  intro hm
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hi : a⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr ha0.le, inv_le_one_of_one_le₀ ha⟩
  have h := hK.smul_mem_of_zero_mem h0 hm hi
  exact hx (by simpa only [inv_smul_smul₀ ha0.ne'] using h)

def toPunctured (K : Set E) (h0 : (0 : E) ∈ K) : C(Space K, PuncturedRadial.Space E) :=
  ⟨fun x => ⟨x.1, ne_zero K h0 x⟩, continuous_subtype_val.subtype_mk _⟩

def toSphere (K : Set E) (h0 : (0 : E) ∈ K) : C(Space K, sphere (0 : E) 1) :=
  PuncturedRadial.toSphere.comp (toPunctured K h0)

theorem sphere_smul_not_mem (K : Set E) (r : ℝ) (hr : 0 < r)
    (hB : ∀ x ∈ K, ‖x‖ < r) (u : sphere (0 : E) 1) : r • (u : E) ∉ K := by
  intro hm
  have h := hB _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp u.property, mul_one] at h
  exact (lt_irrefl r) h

def fromSphere (K : Set E) (r : ℝ) (hr : 0 < r) (hB : ∀ x ∈ K, ‖x‖ < r) :
    C(sphere (0 : E) 1, Space K) :=
  ⟨fun u => ⟨r • (u : E), sphere_smul_not_mem K r hr hB u⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

theorem toSphere_fromSphere (K : Set E) (h0 : (0 : E) ∈ K) (r : ℝ) (hr : 0 < r)
    (hB : ∀ x ∈ K, ‖x‖ < r) (u : sphere (0 : E) 1) :
    toSphere K h0 (fromSphere K r hr hB u) = u := by
  apply Subtype.ext
  change ‖r • (u : E)‖⁻¹ • (r • (u : E)) = (u : E)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, inv_smul_smul₀ hr.ne']

def blendVector (K : Set E) (h0 : (0 : E) ∈ K) (r : ℝ) (q : I × Space K) : E :=
  PuncturedRadial.blendVector r (q.1, toPunctured K h0 q.2)

theorem continuous_blendVector (K : Set E) (h0 : (0 : E) ∈ K) (r : ℝ) :
    Continuous (blendVector K h0 r) :=
  (PuncturedRadial.continuous_blendVector r).comp
    (continuous_fst.prodMk ((toPunctured K h0).continuous.comp continuous_snd))

/-- Every time of the original radial interpolation avoids the actual convex support. -/
theorem blendVector_not_mem (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ x ∈ K, ‖x‖ < r) (q : I × Space K) :
    blendVector K h0 r q ∉ K := by
  have hx : 0 < ‖(q.2 : E)‖ := norm_pos_iff.mpr (ne_zero K h0 q.2)
  let a : ℝ := (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖(q.2 : E)‖)
  change a • (q.2 : E) ∉ K
  by_cases hs : ‖(q.2 : E)‖ ≤ r
  · have hd : 1 ≤ r / ‖(q.2 : E)‖ := (le_div_iff₀ hx).mpr (by simpa using hs)
    have ha : 1 ≤ a := by
      dsimp [a]
      nlinarith [mul_nonneg q.1.property.1 (sub_nonneg.mpr hd)]
    exact smul_not_mem K hK h0 q.2 q.2.property a ha
  · have ha : 0 ≤ a :=
      add_nonneg (sub_nonneg.mpr q.1.property.2)
        (mul_nonneg q.1.property.1 (div_nonneg hr.le hx.le))
    have ht := (convex_Ici (𝕜 := ℝ) r) (not_le.mp hs).le (le_refl r)
      (sub_nonneg.mpr q.1.property.2) q.1.property.1 (sub_add_cancel 1 (q.1 : ℝ))
    have hn : r ≤ ‖a • (q.2 : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      dsimp [a]
      rw [add_mul, mul_assoc, div_mul_cancel₀ r hx.ne']
      exact ht
    exact fun hm => (not_lt_of_ge hn) (hB _ hm)

/-- The actual complement deformation retains the original point at time zero. -/
def deformation (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ x ∈ K, ‖x‖ < r) :
    (ContinuousMap.id (Space K)).Homotopy ((fromSphere K r hr hB).comp (toSphere K h0)) where
  toFun q := ⟨blendVector K h0 r q, blendVector_not_mem K hK h0 r hr hB q⟩
  continuous_toFun := (continuous_blendVector K h0 r).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured]
  map_one_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      PuncturedRadial.toSphere, RadialExtension.direction, div_eq_mul_inv, smul_smul]

def sphereHomotopyEquiv (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ x ∈ K, ‖x‖ < r) : sphere (0 : E) 1 ≃ₕ Space K where
  toFun := fromSphere K r hr hB
  invFun := toSphere K h0
  left_inv := by
    have h : (toSphere K h0).comp (fromSphere K r hr hB) =
        ContinuousMap.id (sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere K h0 r hr hB)
    rw [h]
  right_inv := ⟨(deformation K hK h0 r hr hB).symm⟩

end NoExoticSixSphere.ConvexExterior
