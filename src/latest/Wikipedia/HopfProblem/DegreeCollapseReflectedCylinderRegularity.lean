import Wikipedia.HopfProblem.DegreeCollapseReflectedCollaredCylinder
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Regularity of the actual reflected cylinder fiber

At the seam and clamping points, regularity comes from the endpoint maps.
On the open halves it comes from the original map and the invertible time
reflection. No regularity of the nonsmooth scalar fold is assumed.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

def timeReflection (m : ℕ) : (ℝ × Sphere m) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod (𝓡 m),
    (𝓘(ℝ, ℝ)).prod (𝓡 m)⟯ (ℝ × Sphere m) :=
  (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph.prodCongr
    (Diffeomorph.refl (𝓡 m) (Sphere m) ∞)

theorem timeReflection_apply (m : ℕ) (p : ℝ × Sphere m) :
    timeReflection m p = (-p.1, p.2) := rfl

theorem surjective_mfderiv_endpoint {m n : ℕ} (f : C(Sphere m, Sphere n))
    (hs : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (p : ℝ × Sphere m)
    (hr : Surjective (mfderiv (𝓡 m) (𝓡 n) f p.2)) :
    Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n)
      (fun q : ℝ × Sphere m ↦ f q.2) p) := by
  change Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) (f ∘ Prod.snd) p)
  rw [mfderiv_comp p (hs.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
  intro v
  obtain ⟨w, hw⟩ := hr v
  exact ⟨(0, w), hw⟩

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem regular_map (p : ℝ × Sphere m) (hp : map d p = b) :
    Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) (map d) p) := by
  by_cases hz : foldTime p.1 = 0
  · have he := left_germ d hz
    rw [he.mfderiv_eq]
    exact surjective_mfderiv_endpoint d.leftMap d.smooth_left p
      (d.regular_left p.2 (he.self_of_nhds.symm.trans hp))
  by_cases ho : foldTime p.1 = 1
  · have he := right_germ d ho
    rw [he.mfderiv_eq]
    exact surjective_mfderiv_endpoint d.rightMap d.smooth_right p
      (d.regular_right p.2 (he.self_of_nhds.symm.trans hp))
  have hi : foldTime p.1 ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (foldTime_nonneg p.1) (Ne.symm hz),
      lt_of_le_of_ne (foldTime_le_one p.1) ho⟩
  have ha := (foldTime_interior_iff p.1).mp hi
  by_cases ht : 0 ≤ p.1
  · rw [abs_of_nonneg ht] at ha
    have he := positive_germ d ha
    rw [he.mfderiv_eq]
    exact d.regular_map p (he.self_of_nhds.symm.trans hp)
  · have ht' : p.1 < 0 := lt_of_not_ge ht
    have htime : p.1 ∈ Ioo (-1 : ℝ) 0 := by
      rw [abs_of_neg ht'] at ha
      exact ⟨by linarith [ha.2], ht'⟩
    have he : (map d : ℝ × Sphere m → Sphere n) =ᶠ[𝓝 p]
        (fun q ↦ d.map (timeReflection m q)) := negative_germ d htime
    have hr := d.regular_map (timeReflection m p) (he.self_of_nhds.symm.trans hp)
    rw [he.mfderiv_eq]
    change Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n)
      (d.map ∘ timeReflection m) p)
    rw [mfderiv_comp p (d.smooth_map.mdifferentiableAt (by simp))
      ((timeReflection m).contMDiff.mdifferentiableAt (by simp))]
    exact hr.comp (((timeReflection m).isLocalDiffeomorph p).mfderivToContinuousLinearEquiv
      (by simp)).surjective

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
