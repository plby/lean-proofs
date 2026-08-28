import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates

/-!
# Exact radial cylinder coordinates near the actual equatorial fiber

Radial normalization of `(s,v)` does not change its cylinder coordinates:
they are exactly `(s / ‖v‖, v / ‖v‖)` when the tail is nonzero. The fallback
points are irrelevant there. At an equatorial unit vector, the first
coordinate has derivative equal to the new coordinate projection.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.SphereRadialRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem retract_pos_smul_ne_zero (a b : UnitSphere E) {c : ℝ} (hc : 0 < c)
    {v : E} (hv : v ≠ 0) : retract a (c • v) = retract b v := by
  apply Subtype.ext
  simp only [retract, dif_neg (smul_ne_zero hc.ne' hv), dif_neg hv]
  exact NormedSpace.normalize_smul_of_pos hc v

end NoExoticSixSphere.SphereRadialRetraction

namespace NoExoticSixSphere.SphereCylinder

theorem join_ne_zero_of_tail_ne_zero (m : ℕ) (s : ℝ)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ≠ 0) : join m (s, v) ≠ 0 := by
  intro h
  have he := congrArg (tail m) h
  rw [tail_join, map_zero] at he
  exact hv he

theorem inverse_retract_join (m : ℕ) (a : Sphere (m + 1)) (b : Sphere m)
    (s : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) (hv : v ≠ 0) :
    inverse m (SphereRadialRetraction.retract a (join m (s, v))) =
      (s / ‖v‖, SphereRadialRetraction.retract b v) := by
  have hq := join_ne_zero_of_tail_ne_zero m s hv
  have hc : 0 < ‖join m (s, v)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hq)
  have hr : (SphereRadialRetraction.retract a (join m (s, v))).val =
      ‖join m (s, v)‖⁻¹ • join m (s, v) := by
    rw [SphereRadialRetraction.retract, dif_neg hq]
    rfl
  have ht : tail m (SphereRadialRetraction.retract a (join m (s, v))).val =
      ‖join m (s, v)‖⁻¹ • v := by
    rw [hr, map_smul, tail_join]
  apply Prod.ext
  · change (SphereRadialRetraction.retract a (join m (s, v))).val 0 /
      ‖tail m (SphereRadialRetraction.retract a (join m (s, v))).val‖ = s / ‖v‖
    rw [ht, norm_smul, Real.norm_eq_abs, abs_of_pos hc, hr]
    change (‖join m (s, v)‖⁻¹ * s) / (‖join m (s, v)‖⁻¹ * ‖v‖) = s / ‖v‖
    field_simp
  · change SphereRadialRetraction.retract _
      (tail m (SphereRadialRetraction.retract a (join m (s, v))).val) =
        SphereRadialRetraction.retract b v
    rw [ht]
    exact SphereRadialRetraction.retract_pos_smul_ne_zero _ b hc hv

theorem hasFDerivAt_height_ratio (m : ℕ) (x : Sphere m) :
    HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ p.1 / ‖p.2‖)
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (m + 1)))) (0, x.val) := by
  have hN : DifferentiableAt ℝ
      (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖p.2‖) (0, x.val) := by
    have hn : DifferentiableAt ℝ
        (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖y‖) x.val :=
      (contDiffAt_norm (n := ∞) ℝ (ne_zero_of_mem_unit_sphere x)).differentiableAt (by simp)
    have hs : DifferentiableAt ℝ
        (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ p.2) (0, x.val) :=
      differentiableAt_snd
    exact hn.comp (0, x.val) hs
  have hF : HasFDerivAt
      (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (m + 1)))) (0, x.val) :=
    hasFDerivAt_fst
  have hi := (hN.inv
    (show ‖x.val‖ ≠ 0 from norm_ne_zero_iff.mpr (ne_zero_of_mem_unit_sphere x))).hasFDerivAt
  have h := hF.mul hi
  convert! h using 1
  simp only [Pi.inv_apply, ClosedHemisphere.unit_norm, inv_one, zero_smul, one_smul, zero_add]

end NoExoticSixSphere.SphereCylinder
