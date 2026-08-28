import Wikipedia.NoExoticSixSphere.SmoothKernelFrame

/-!
# Exact normal projection and deformation of transverse equation frames

Every right inverse projects to the same canonical orthogonal right inverse.
The affine interpolation remains a right inverse, even before orthogonal
projection. Appending an injective kernel operator remains injective along
the whole deformation. No homotopy of arbitrary frames is assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RightInverseFrameHomotopy

open NoExoticSixSphere

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem projection_rightInverse (D : E →L[ℝ] F) (R : F →L[ℝ] E)
    (hR : ∀ v, D (R v) = v) :
    D.kerᗮ.starProjection.comp R = orthogonalRightInverse D := by
  have hD : Surjective D := fun v ↦ ⟨R v, hR v⟩
  apply (orthogonalRightInverse_eq_of_rightInverse D hD
    (D.kerᗮ.starProjection.comp R) ?_ ?_).symm
  · intro v
    have hk : R v - D.kerᗮ.starProjection (R v) ∈ D.ker := by
      simpa only [Submodule.orthogonal_orthogonal] using
        (D.kerᗮ.sub_starProjection_mem_orthogonal (R v))
    change D (R v - D.kerᗮ.starProjection (R v)) = 0 at hk
    rw [map_sub, hR] at hk
    exact (sub_eq_zero.mp hk).symm
  · rintro _ ⟨v, rfl⟩
    exact D.kerᗮ.starProjection_apply_mem (R v)

def blend (t : ℝ) (R S : F →L[ℝ] E) : F →L[ℝ] E := (1 - t) • R + t • S

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem blend_zero (R S : F →L[ℝ] E) : blend 0 R S = R := by simp [blend]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem blend_one (R S : F →L[ℝ] E) : blend 1 R S = S := by simp [blend]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem blend_rightInverse (D : E →L[ℝ] F) (R S : F →L[ℝ] E)
    (hR : ∀ v, D (R v) = v) (hS : ∀ v, D (S v) = v) (t : ℝ) (v : F) :
    D (blend t R S v) = v := by
  change D ((1 - t) • R v + t • S v) = v
  simp only [map_add, map_smul, hR, hS, ← add_smul, sub_add_cancel, one_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem blend_injective (D : E →L[ℝ] F) (R S : F →L[ℝ] E)
    (hR : ∀ v, D (R v) = v) (hS : ∀ v, D (S v) = v) (t : ℝ) :
    Injective (blend t R S) := by
  intro u v h
  exact (blend_rightInverse D R S hR hS t u).symm.trans
    ((congrArg D h).trans (blend_rightInverse D R S hR hS t v))

theorem blend_projection (D : E →L[ℝ] F) (R S : F →L[ℝ] E)
    (hR : ∀ v, D (R v) = v) (hS : ∀ v, D (S v) = v) (t : ℝ) :
    D.kerᗮ.starProjection.comp (blend t R S) = orthogonalRightInverse D :=
  projection_rightInverse D (blend t R S) (blend_rightInverse D R S hR hS t)

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem blend_coprod_injective (D : E →L[ℝ] F) (R S : F →L[ℝ] E)
    (hR : ∀ v, D (R v) = v) (hS : ∀ v, D (S v) = v)
    (A : K →L[ℝ] E) (hA : ∀ w, D (A w) = 0) (hi : Injective A) (t : ℝ) :
    Injective ((blend t R S).coprod A) := by
  intro u v h
  have hu : u.1 = v.1 := by
    have hh := congrArg D h
    change D (blend t R S u.1 + A u.2) = D (blend t R S v.1 + A v.2) at hh
    simpa only [map_add, blend_rightInverse D R S hR hS, hA, add_zero] using hh
  apply Prod.ext hu
  apply hi
  change blend t R S u.1 + A u.2 = blend t R S v.1 + A v.2 at h
  rw [hu] at h
  exact add_left_cancel h

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contMDiff_blend {R S : M → F →L[ℝ] E}
    (hR : ContMDiff I 𝓘(ℝ, F →L[ℝ] E) ∞ R)
    (hS : ContMDiff I 𝓘(ℝ, F →L[ℝ] E) ∞ S) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F →L[ℝ] E) ∞
      (fun p : ℝ × M ↦ blend p.1 (R p.2) (S p.2)) := by
  have hm : ContMDiff 𝓘(ℝ, ℝ × (F →L[ℝ] E)) 𝓘(ℝ, F →L[ℝ] E) ∞
      (fun p : ℝ × (F →L[ℝ] E) ↦ p.1 • p.2) :=
    (contDiff_smul : ContDiff ℝ ∞ (fun p : ℝ × (F →L[ℝ] E) ↦ p.1 • p.2)).contMDiff
  have ht : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ 1 - p.1) := contMDiff_const.sub contMDiff_fst
  exact (hm.comp (ht.prodMk_space (hR.comp contMDiff_snd))).add
    (hm.comp (contMDiff_fst.prodMk_space (hS.comp contMDiff_snd)))

def normalize (D : M → E →L[ℝ] F) (R : M → F →L[ℝ] E) (p : ℝ × M) : F →L[ℝ] E :=
  blend p.1 (R p.2) (orthogonalRightInverse (D p.2))

omit [TopologicalSpace M] in
theorem normalize_zero (D : M → E →L[ℝ] F) (R : M → F →L[ℝ] E) (x : M) :
    normalize D R (0, x) = R x := blend_zero _ _

omit [TopologicalSpace M] in
theorem normalize_one (D : M → E →L[ℝ] F) (R : M → F →L[ℝ] E) (x : M) :
    normalize D R (1, x) = orthogonalRightInverse (D x) := blend_one _ _

theorem contMDiff_canonical {D : M → E →L[ℝ] F} {R : M → F →L[ℝ] E}
    (hD : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ D)
    (hr : ∀ x v, D x (R x v) = v) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun x ↦ orthogonalRightInverse (D x)) := by
  intro x
  apply contMDiffAt_orthogonalRightInverse (I := I) (hD x)
  intro v
  exact ⟨R x v, hr x v⟩

theorem contMDiff_normalize {D : M → E →L[ℝ] F} {R : M → F →L[ℝ] E}
    (hD : ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ D)
    (hR : ContMDiff I 𝓘(ℝ, F →L[ℝ] E) ∞ R)
    (hr : ∀ x v, D x (R x v) = v) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F →L[ℝ] E) ∞ (normalize D R) := by
  change ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F →L[ℝ] E) ∞
    (fun p : ℝ × M ↦ blend p.1 (R p.2) (orthogonalRightInverse (D p.2)))
  have hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] E) ∞
      (fun x : M ↦ orthogonalRightInverse (D x)) :=
    contMDiff_canonical (I := I) (D := D) (R := R) hD hr
  exact contMDiff_blend (I := I) (R := R)
    (S := fun x : M ↦ orthogonalRightInverse (D x)) hR hs

omit [TopologicalSpace M] in
theorem normalize_rightInverse (D : M → E →L[ℝ] F) (R : M → F →L[ℝ] E)
    (hr : ∀ x v, D x (R x v) = v) (p : ℝ × M) (v : F) :
    D p.2 (normalize D R p v) = v :=
  blend_rightInverse (D p.2) (R p.2) (orthogonalRightInverse (D p.2)) (hr p.2)
    (apply_orthogonalRightInverse (D p.2) (fun w ↦ ⟨R p.2 w, hr p.2 w⟩)) p.1 v

end Wikipedia.HopfProblem.DegreeCollapse.RightInverseFrameHomotopy
