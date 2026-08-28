import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Wikipedia.HopfProblem.SphereHomologySuspensionCoordinates

/-!
# Smooth cylinder coordinates on the sphere away from its poles

Normalize the vector `(s,x)`, where `s` is real and `x` is a unit vector.
Its norm is never zero. This gives a smooth map from the genuine product
`ℝ × Sⁿ` into `Sⁿ⁺¹`, with no singularity at its equator.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def join (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin (n + 1))) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun p := WithLp.toLp 2 (Fin.cons p.1 (fun i ↦ p.2 i))
    invFun y := (y 0, WithLp.toLp 2 (fun i ↦ y i.succ))
    left_inv p := by
      apply Prod.ext rfl
      ext i
      rfl
    right_inv y := by
      ext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    map_add' p q := by
      ext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    map_smul' a p := by
      ext i
      exact Fin.cases rfl (fun _ ↦ rfl) i }

@[simp] theorem join_head (n : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    join n (s, x) 0 = s := rfl

@[simp] theorem join_tail (n : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : join n (s, x) i.succ = x i := rfl

def tail (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ]
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (n + 1)))).comp
    (join n).symm.toContinuousLinearMap

@[simp] theorem tail_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) : tail n y i = y i.succ := rfl

@[simp] theorem tail_join (n : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    tail n (join n (s, x)) = x := by ext i; rfl

theorem norm_join_sq (n : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖join n (s, x)‖ ^ 2 = s ^ 2 + ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [join_head, join_tail]
  rw [← EuclideanSpace.real_norm_sq_eq]

def vector (n : ℕ) (p : ℝ × Sphere n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  join n (p.1, p.2.val)

theorem vector_ne_zero (n : ℕ) (p : ℝ × Sphere n) : vector n p ≠ 0 := by
  intro h
  have ht := congrArg (tail n) h
  change tail n (join n (p.1, p.2.val)) = tail n 0 at ht
  rw [tail_join, map_zero] at ht
  exact ne_zero_of_mem_unit_sphere p.2 ht

theorem contMDiff_vector (n : ℕ) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 (n + 2)) ∞ (vector n) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
      (fun x : Sphere n ↦ x.val) := contMDiff_coe_sphere
  exact (join n).contDiff.contMDiff.comp
    (contMDiff_fst.prodMk_space (hc.comp contMDiff_snd))

def point (n : ℕ) : C(ℝ × Sphere n, Sphere (n + 1)) :=
  normalizedSphereMap ⟨vector n, (contMDiff_vector n).continuous⟩ (vector_ne_zero n)

theorem contMDiff_point (n : ℕ) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (point n) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact (contMDiff_normalize (contMDiff_vector n) (vector_ne_zero n)).codRestrict_sphere _

@[simp] theorem point_head (n : ℕ) (p : ℝ × Sphere n) :
    (point n p).val 0 = ‖vector n p‖⁻¹ * p.1 := rfl

@[simp] theorem tail_point (n : ℕ) (p : ℝ × Sphere n) :
    tail n (point n p).val = ‖vector n p‖⁻¹ • p.2.val := by
  change tail n (‖vector n p‖⁻¹ • vector n p) = _
  rw [map_smul]
  rfl

theorem norm_tail_point (n : ℕ) (p : ℝ × Sphere n) :
    ‖tail n (point n p).val‖ = ‖vector n p‖⁻¹ := by
  rw [tail_point, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), ClosedHemisphere.unit_norm, mul_one]

theorem tail_point_ne_zero (n : ℕ) (p : ℝ × Sphere n) :
    tail n (point n p).val ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_tail_point]
  exact inv_ne_zero (norm_ne_zero_iff.mpr (vector_ne_zero n p))

end NoExoticSixSphere.SphereCylinder
