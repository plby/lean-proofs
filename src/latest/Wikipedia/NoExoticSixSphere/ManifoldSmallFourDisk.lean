import Wikipedia.NoExoticSixSphere.LocalInverse
import Wikipedia.NoExoticSixSphere.ManifoldDiskParityZero
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# A genuine small four-disk in an original six-manifold chart

A scaled coordinate four-plane lies inside the target of an original smooth
chart. Its inverse image is injective and immersive on the whole closed
unit disk. The boundary is consequently an actual smooth embedded immersive
three-sphere of zero geometric parity for every given normal framing.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem exists_smallFourDisk (x : M) :
    ∃ h : Vector 4 → M,
      (∀ z ∈ closedBall (0 : Vector 4) 1, ContMDiffAt (𝓡 4) (𝓡 6) ∞ h z) ∧
      InjOn h (closedBall (0 : Vector 4) 1) ∧
      (∀ z ∈ closedBall (0 : Vector 4) 1, Injective (mfderiv (𝓡 4) (𝓡 6) h z)) ∧
      h 0 = x := by
  let c := modelChartPartialDiffeomorph (I := 𝓡 6) x
  have hx : x ∈ c.source := mem_extChartAt_source x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (c.map_source hx)
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let L := appendZeroMap 4 2
  have hLnorm (z : Vector 4) : ‖L z‖ = ‖z‖ := by
    have he := inner_appendZeroMap 4 2 z z
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
  let B : Vector 4 →L[ℝ] Vector 6 := δ • L
  have hBi : Injective B := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have he : L z = 0 := (smul_eq_zero.mp hz).resolve_left hδ.ne'
    apply appendZeroMap_injective 4 2
    simpa only [map_zero] using he
  let A : Vector 4 → Vector 6 := fun z ↦ c x + B z
  have hA : ContDiff ℝ ∞ A := contDiff_const.add B.contDiff
  have hAi : Injective A := by
    intro z w he
    exact hBi (add_left_cancel he)
  have hAd (z : Vector 4) : fderiv ℝ A z = B := by
    have hd := (hasFDerivAt_const (c x) z).add (B.hasFDerivAt)
    have hd' : HasFDerivAt A B z := by
      simpa only [zero_add, Pi.add_apply] using! hd
    exact hd'.fderiv
  have hAtarget (z : Vector 4) (hz : z ∈ closedBall (0 : Vector 4) 1) : A z ∈ c.target := by
    apply hball
    have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [mem_ball, dist_eq_norm]
    change ‖c x + δ • L z - c x‖ < ε
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hLnorm]
    calc
      δ * ‖z‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left hn hδ.le
      _ < ε := by dsimp [δ]; linarith
  let h : Vector 4 → M := c.symm ∘ A
  have hs (z : Vector 4) (hz : z ∈ closedBall (0 : Vector 4) 1) :
      ContMDiffAt (𝓡 4) (𝓡 6) ∞ h z :=
    (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds (hAtarget z hz))).comp z
      hA.contMDiff.contMDiffAt
  refine ⟨h, hs, ?_, ?_, ?_⟩
  · intro z hz w hw he
    apply hAi
    have hc := congrArg c he
    change c (c.symm (A z)) = c (c.symm (A w)) at hc
    have hz' : c (c.symm (A z)) = A z := c.right_inv (hAtarget z hz)
    have hw' : c (c.symm (A w)) = A w := c.right_inv (hAtarget w hw)
    exact hz'.symm.trans (hc.trans hw')
  · intro z hz
    have hc : IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ c.symm (A z) :=
      ⟨c.symm, hAtarget z hz, fun _ _ ↦ rfl⟩
    have hd := (hc.mfderivToContinuousLinearEquiv (by simp)).injective
    change Injective (mfderiv (𝓡 6) (𝓡 6) c.symm (A z)) at hd
    change Injective (mfderiv (𝓡 4) (𝓡 6) (c.invFun ∘ A) z)
    rw [mfderiv_comp z
      ((c.contMDiffOn_invFun.contMDiffAt
        (c.open_target.mem_nhds (hAtarget z hz))).mdifferentiableAt (by simp))
      (hA.contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, hAd]
    exact hd.comp hBi
  · change c.symm (c x + B 0) = x
    rw [map_zero, add_zero]
    exact c.left_inv hx

namespace EuclideanEmbedding

variable (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_zeroParitySphere_homotopic_const (x : M) :
    ∃ f : C(Sphere 3, M), ∃ hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f,
      ∃ hi : Injective f, ∃ hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s),
        e.sphereParity a f hf hi hd = 0 ∧ f.Homotopic (ContinuousMap.const _ x) := by
  obtain ⟨h, hs, hhi, hhd, hzero⟩ := exists_smallFourDisk x
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hval : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere
  have hf : ContMDiff (𝓡 3) (𝓡 6) ∞ (h ∘ (Subtype.val : Sphere 3 → Vector 4)) := by
    intro s
    exact (hs s.val (sphere_subset_closedBall s.property)).comp s hval.contMDiffAt
  let f : C(Sphere 3, M) := ⟨h ∘ Subtype.val, hf.continuous⟩
  have hi : Injective f := by
    intro s t he
    exact Subtype.ext (hhi (sphere_subset_closedBall s.property)
      (sphere_subset_closedBall t.property) he)
  have hd (s : Sphere 3) : Injective (mfderiv (𝓡 3) (𝓡 6) f s) := by
    have hc := injective_mvfderiv_subtypeVal_sphere (n := 3) s
    change Injective (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → Vector 4) s) at hc
    change Injective (mfderiv (𝓡 3) (𝓡 6) (h ∘ Subtype.val) s)
    rw [mfderiv_comp s ((hs s.val (sphere_subset_closedBall s.property)).mdifferentiableAt
      (by simp)) (hval.mdifferentiableAt (by simp))]
    exact (hhd s.val (sphere_subset_closedBall s.property)).comp hc
  have hcont : ContinuousOn h (closedBall (0 : Vector 4) 1) :=
    fun z hz ↦ (hs z hz).continuousAt.continuousWithinAt
  let F : C(Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder.Disk (E := Vector 4), M) :=
    ⟨fun z ↦ h z.val, continuousOn_iff_continuous_restrict.mp hcont⟩
  let b : Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder.Disk (E := Vector 4) :=
    ⟨0, mem_closedBall_self (by norm_num)⟩
  have H : f.Homotopic (ContinuousMap.const _ x) := by
    refine ⟨{
      toFun q := F (DiskBoundary.segment b (q.1,
        Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder.boundaryToDisk q.2))
      continuous_toFun := F.continuous.comp ((DiskBoundary.segment b).continuous.comp
        (continuous_fst.prodMk
          (Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder.boundaryToDisk.continuous.comp
            continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
    }⟩
    · intro s
      rw [DiskBoundary.segment_zero]
      rfl
    · intro s
      rw [DiskBoundary.segment_one]
      exact hzero
  exact ⟨f, hf, hi, hd, e.sphereParity_zero_of_embedded_disk a f hf hi hd h
    (fun _ ↦ rfl) hs hhi hhd, H⟩

theorem exists_zeroParitySphere (x : M) :
    ∃ f : C(Sphere 3, M), ∃ hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f,
      ∃ hi : Injective f, ∃ hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s),
        e.sphereParity a f hf hi hd = 0 := by
  obtain ⟨f, hf, hi, hd, hz, _⟩ := e.exists_zeroParitySphere_homotopic_const a x
  exact ⟨f, hf, hi, hd, hz⟩

end EuclideanEmbedding
end NoExoticSixSphere
