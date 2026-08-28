import Wikipedia.NoExoticSixSphere.SquareDouble

/-!
# The square double is a native closed smooth seven-manifold

At the seam the original time differential is surjective. Away from the
seam the new scalar derivative is nonzero. Thus the square equation has
zero as a regular value, giving the actual double a boundaryless regular-
fiber atlas. No smoothness of the square-root section is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SquareDouble

open GLOrthonormalization

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (t : C(M, ℝ)) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hr : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))

include ht in
theorem smooth_equation :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 7)) 𝓘(ℝ, ℝ) ∞ (equation t) :=
  (ht.comp contMDiff_snd).sub (contMDiff_fst.pow 2)

def timeDifferential (p : M) : Vector 7 →L[ℝ] ℝ :=
  mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p

def equationDifferential (q : ℝ × M) : (ℝ × Vector 7) →L[ℝ] ℝ :=
  mfderiv (𝓘(ℝ, ℝ).prod (𝓡 7)) 𝓘(ℝ, ℝ) (equation t) q

include ht in
theorem mfderiv_equation_apply (q : ℝ × M) (v : ℝ × Vector 7) :
    equationDifferential t q v =
      timeDifferential t q.2 v.2 - (q.1 * v.1 + v.1 * q.1) := by
  have hf : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 7)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × M → ℝ) q (ContinuousLinearMap.fst ℝ ℝ (Vector 7)) :=
    hasMFDerivAt_fst q
  have hs : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 7)) (𝓡 7)
      (Prod.snd : ℝ × M → M) q (ContinuousLinearMap.snd ℝ ℝ (Vector 7)) :=
    hasMFDerivAt_snd q
  have hsq := hf.mul' hf
  have hfun : (Prod.fst : ℝ × M → ℝ) * Prod.fst = (fun r : ℝ × M ↦ r.1 ^ 2) := by
    funext r
    exact (pow_two r.1).symm
  rw [hfun] at hsq
  have h := ((ht.mdifferentiableAt (by simp)).hasMFDerivAt.comp q hs).sub hsq
  have he := h.mfderiv
  change equationDifferential t q = _ at he
  rw [he]
  rfl

include ht hr in
theorem regular_equation : ∀ q, equation t q = 0 →
    Surjective (equationDifferential t q) := by
  intro q hq z
  by_cases hu : q.1 = 0
  · have hzero : t q.2 = 0 := by
      have h := sub_eq_zero.mp hq
      simpa only [hu, zero_pow (by decide : 2 ≠ 0)] using h
    obtain ⟨v, hv⟩ := hr q.2 hzero z
    change timeDifferential t q.2 v = z at hv
    refine ⟨(0, v), ?_⟩
    rw [mfderiv_equation_apply t ht]
    simpa only [mul_zero, zero_mul, add_zero, sub_zero] using hv
  · refine ⟨(-z / (2 * q.1), 0), ?_⟩
    rw [mfderiv_equation_apply t ht, map_zero]
    field_simp [hu]
    ring

@[instance_reducible]
def atlas : ChartedSpace (Vector 7) (Space t) :=
  regularFiberAtlas (equation t) (smooth_equation t ht) 0 (regular_equation t ht hr) 7 (by simp)

theorem isManifold : letI := atlas t ht hr; IsManifold (𝓡 7) ∞ (Space t) :=
  regularFiber_isManifold (equation t) (smooth_equation t ht) 0
    (regular_equation t ht hr) 7 (by simp)

end NoExoticSixSphere.SquareDouble
