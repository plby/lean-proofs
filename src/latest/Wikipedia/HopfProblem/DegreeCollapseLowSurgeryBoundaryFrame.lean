import Wikipedia.NoExoticSixSphere.StabilizedDiskBoundaryNormal

/-!

# The exact prescribed boundary columns for low-dimensional surgery disks

Add the graph-coordinate axes to the original normal frame, omitting the
height coordinate that supplies the radial disk tangent. The operator is
orthonormal and smooth, in every sphere dimension. Its normality is proved
against the actual derivative of the retained radial collar and therefore
against any disk retaining that whole open collar.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

def boundaryFrameOperator (d : ℕ) {N k : ℕ} (a : Vector k →L[ℝ] Vector N) :
    Vector (k + (1 + (d + 1))) →L[ℝ] Vector (N + (1 + (1 + (d + 1)))) :=
  (coordinates N (d + 1)).toContinuousLinearMap.comp
    ((((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a).prodMap
      (DiskGraph.extraCoordinates (d + 1)).symm.toContinuousLinearMap).comp
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k)
          (m := 1 + (d + 1))).toContinuousLinearMap)

theorem boundaryFrameOperator_apply (d : ℕ) {N k : ℕ} (a : Vector k →L[ℝ] Vector N)
    (w : Vector (k + (1 + (d + 1)))) :
    boundaryFrameOperator d a w = coordinates N (d + 1)
      ((a (EuclideanSpace.finAddEquivProd w).1, 0),
        (DiskGraph.extraCoordinates (d + 1)).symm (EuclideanSpace.finAddEquivProd w).2) := rfl

theorem inner_boundaryFrameOperator (d : ℕ) {N k : ℕ} (a : Space N k)
    (u v : Vector (k + (1 + (d + 1)))) :
    inner ℝ (boundaryFrameOperator d a.val u) (boundaryFrameOperator d a.val v) =
      inner ℝ u v := by
  rw [boundaryFrameOperator_apply, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_left, zero_add]
  rw [← DiskGraph.inner_extraCoordinates (d + 1),
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have ha := (toIsometry a).inner_map_map
    (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1
  change inner ℝ (a.val _) (a.val _) = _ at ha
  rw [ha]
  exact (inner_finAdd_split u v).symm

theorem norm_boundaryFrameOperator (d : ℕ) {N k : ℕ} (a : Space N k)
    (w : Vector (k + (1 + (d + 1)))) : ‖boundaryFrameOperator d a.val w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_boundaryFrameOperator d a w w

def boundaryFrame (d : ℕ) {N k : ℕ} (a : Space N k) :
    Space (N + (1 + (1 + (d + 1)))) (k + (1 + (d + 1))) :=
  ⟨boundaryFrameOperator d a.val, norm_boundaryFrameOperator d a⟩

section Smooth

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_boundaryFrameOperator (d : ℕ) {N k : ℕ}
    {a : M → Vector k →L[ℝ] Vector N}
    (ha : ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ a) :
    ContMDiff I 𝓘(ℝ, Vector (k + (1 + (d + 1))) →L[ℝ]
      Vector (N + (1 + (1 + (d + 1))))) ∞ (fun x => boundaryFrameOperator d (a x)) := by
  exact contMDiff_const.clm_comp
    (((contMDiff_const.clm_comp ha).clm_prodMap contMDiff_const).clm_comp contMDiff_const)

end Smooth

theorem fderiv_collar_apply {d N : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (s : NoExoticSixSphere.Sphere d)
    (v : Vector (d + 1)) :
    fderiv ℝ (collar b f) s.val v = coordinates N (d + 1)
      ((fderiv ℝ (SmoothSphereAmbient.extension b f) s.val v,
        fderiv ℝ (definingFunction (E := Vector (d + 1))) s.val v), 0) := by
  have he : DifferentiableAt ℝ (SmoothSphereAmbient.extension b f) s.val :=
    (SmoothSphereAmbient.contDiff_extension b f hf).contDiffAt.differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ (definingFunction (E := Vector (d + 1))) s.val :=
    contDiff_definingFunction.contDiffAt.differentiableAt (by simp)
  have hd := (coordinates N (d + 1)).hasFDerivAt.comp s.val
    ((he.hasFDerivAt.prodMk hρ.hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector (d + 1)) s.val))
  rw [show fderiv ℝ (collar b f) s.val = _ from hd.fderiv]
  rfl

theorem boundaryFrame_normal_collar {d N k : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (s : NoExoticSixSphere.Sphere d) (a : Space N k)
    (ha : a.val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ) :
    (boundaryFrame d a).val.range ≤ (fderiv ℝ (collar b f) s.val).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (collar b f) s.val v) (boundaryFrameOperator d a.val w) = 0
  rw [fderiv_collar_apply b f hf, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  apply Submodule.inner_right_of_mem_orthogonal
    ((SmoothSphereAmbient.range_fderiv_extension_le b f hf s) ⟨v, rfl⟩)
  exact ha ⟨_, rfl⟩

theorem boundaryFrame_normal_disk {d N k : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (a : NoExoticSixSphere.Sphere d → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ)
    {G : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))}
    {V : Set (Vector (d + 1))} (hV : IsOpen V)
    (hSV : Metric.sphere 0 1 ⊆ V) (heq : EqOn G (collar b f) V)
    (s : NoExoticSixSphere.Sphere d) :
    (boundaryFrame d (a s)).val.range ≤ (fderiv ℝ G s.val).rangeᗮ := by
  have he : G =ᶠ[𝓝 s.val] collar b f :=
    Filter.mem_of_superset (hV.mem_nhds (hSV s.property)) heq
  rw [he.fderiv_eq]
  exact boundaryFrame_normal_collar b f hf s (a s) (ha s)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
