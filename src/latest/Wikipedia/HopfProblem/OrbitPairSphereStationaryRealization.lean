import Wikipedia.HopfProblem.OrbitPairSpherePolygonRealization
import Wikipedia.HopfProblem.OrbitPairSphereMinimumPolygonSpace

/-!
# The broken realization of a stationary polygon is its actual smooth geodesic

The already proved common-generator identity identifies every realized edge
with the same exponential curve. At the minimum antipodal energy its speed is
pi. Thus the realization of every minimum polygon is a literal semicircle,
and sampling then realizing a semicircle recovers it at every time.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization CayleyTransform OrthogonalExponential
  SphereVertexSpace SphereTangentExponential SphereAngle SphereSemicircle

variable {n m : ℕ}

theorem path_val_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v.val) {t : ℝ}
    (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    (path a b τ hτ v t).val = curve a.val (initialTangent a b τ v.val) (t - τ 0) := by
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent τ ht
  have hstep : τ i.succ - τ i.castSucc ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hτ (show i.castSucc < i.succ by simp)))
  rw [path_eq_segment a b τ hτ v i hi]
  change (exp (((t - τ i.castSucc) / (τ i.succ - τ i.castSucc)) •
    generator (vertices a b v.val i.castSucc).val
      (tangentLog (vertices a b v.val i.castSucc).val (vertices a b v.val i.succ).val
        (ClosedHemisphere.unit_norm _)))).val.val (vertices a b v.val i.castSucc).val = _
  rw [← edgeGenerator_scaled a b τ v.val i hstep, smul_smul, div_mul_cancel₀ _ hstep,
    edgeGenerator_eq_first_of_stationary a b τ v.val v.2 hstat i,
    vertices_eq_exp_of_stationary a b τ hτ v.val v.2 hstat i.castSucc, ← exp_add_apply]
  rw [show (t - τ i.castSucc) + (τ i.castSucc - τ 0) = t - τ 0 by ring]
  rw [curve, generator_initialTangent]

theorem exists_minimum_path_direction (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (v : minimumSet a b τ) :
    ∃ y : Direction a, ∀ t ∈ Icc (0 : ℝ) 1,
      (path a b τ hτ ⟨v.val, v.2.1⟩ t).val = SphereGreatCircle.curve a.val y.val Real.pi t := by
  have hstat := isStationary_of_minimum_energy a b τ hτ hzero hone hanti
    (Real.pi ^ 2) hmesh v.val v.2.2.le v.2.2
  let V := initialTangent a b τ v.val
  have hV : V ≠ 0 := initialTangent_ne_zero_of_endpoints_ne a b τ hτ v.val v.2.1 hstat
    (endpoints_ne_of_antipodal a b hanti)
  have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hE := energy_eq_speed_sq_mul_of_stationary a b τ hτ v.val v.2.1 hstat
  rw [v.2.2, hzero, hone, sub_zero, mul_one] at hE
  have hnpi : ‖V‖ = Real.pi := by
    change Real.pi ^ 2 = ‖V‖ ^ 2 at hE
    nlinarith [Real.pi_pos]
  let y : Direction a := ⟨‖V‖⁻¹ • (V : Vector (n + 1)), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    change ‖V‖⁻¹ * ‖V‖ = 1
    exact inv_mul_cancel₀ (ne_of_gt hn), by
      rw [real_inner_smul_right, inner_tangent, mul_zero]⟩
  refine ⟨y, ?_⟩
  intro t ht
  have htime : t ∈ Icc (τ 0) (τ (Fin.last (m + 1))) := by simpa only [hzero, hone] using ht
  rw [path_val_of_stationary a b τ hτ ⟨v.val, v.2.1⟩ hstat htime, hzero, sub_zero]
  change curve a.val V t = SphereGreatCircle.curve a.val y.val Real.pi t
  rw [curve_formula_of_ne_zero (ClosedHemisphere.unit_norm a) V hV]
  change SphereGreatCircle.curve a.val y.val ‖V‖ t = _
  rw [hnpi]

theorem path_semicircleVertices (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) (y : Direction a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (path a b τ hτ ⟨semicircleVertices a τ y,
      (semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hmesh y).1⟩ t).val =
        SphereGreatCircle.curve a.val y.val Real.pi t := by
  let v : minimumSet a b τ :=
    ⟨semicircleVertices a τ y, semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hmesh y⟩
  obtain ⟨z, hz⟩ := exists_minimum_path_direction a b τ hτ hzero hone hanti hmesh v
  have he : minimumParametrization a b τ hτ hzero hone hanti hmesh z = v := by
    apply Subtype.ext
    funext k
    apply Subtype.ext
    have htime := interior_time_mem τ hτ hzero hone k
    have h := hz (τ k.castSucc.succ) ⟨htime.1.le, htime.2.le⟩
    rw [path_vertex, vertices_interior] at h
    exact h.symm
  have hzy : z = y := minimumParametrization_injective a b τ hτ hzero hone hanti hmesh j he
  subst z
  exact hz t ht

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
