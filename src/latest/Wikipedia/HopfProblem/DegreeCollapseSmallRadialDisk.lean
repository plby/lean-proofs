import Wikipedia.HopfProblem.DegreeCollapseSupportedDiskObstacleAlignment

/-!
# Global smooth disk parametrizations inside an arbitrary local chart

A bounded radial map has invertible differential everywhere and sends
the entire Euclidean source into an arbitrarily small neighborhood of
zero. Composing with an injective affine chart slice constructs an actual
global smooth embedded immersive closed disk with its center fixed.
-/

noncomputable section

open Set Function Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A F E H M : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_small_radial_disk {U : Set A} (hU : IsOpen U) (h0 : (0 : A) ∈ U) :
    ∃ ψ : A → A, ContDiff ℝ ∞ ψ ∧ Injective ψ ∧
      (∀ x, Bijective (fderiv ℝ ψ x)) ∧ ψ 0 = 0 ∧ ∀ x, ψ x ∈ U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let s := r / 4
  have hs : 0 < s := by dsimp only [s]; positivity
  refine ⟨DiskShrinking.boundedRadialDiskMap s,
    DiskShrinking.boundedRadialDiskMap_smooth s,
    DiskShrinking.boundedRadialDiskMap_injective hs, ?_,
    DiskShrinking.boundedRadialDiskMap_zero s, ?_⟩
  · intro x
    have hi := DiskShrinking.boundedRadialDiskMap_derivative_injective (N := A) hs x
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  · intro x
    apply hball
    rw [mem_ball_zero_iff, DiskShrinking.boundedRadialDiskMap, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs)]
    have hn : ‖(OpenPartialHomeomorph.univUnitBall : A → A) x‖ < 1 :=
      mem_ball_zero_iff.mp (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ x))
    have hroot : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hscalar : 0 < Real.sqrt (2 : ℝ) * s :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs
    have hle := mul_le_of_le_one_right hscalar.le hn.le
    have hsbound : Real.sqrt 2 * s < r := by dsimp only [s]; nlinarith
    exact hle.trans_lt hsbound

theorem exists_global_affine_disk_in_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) J F M ∞)
    (L : A →L[ℝ] F) (hL : Injective L) (w : F) (hw : w ∈ Φ.source) :
    ∃ ψ : A → A, ContDiff ℝ ∞ ψ ∧ Injective ψ ∧
      (∀ x, Bijective (fderiv ℝ ψ x)) ∧ ψ 0 = 0 ∧
      (∀ x, L (ψ x) + w ∈ Φ.source) ∧
      ContMDiff 𝓘(ℝ, A) J ∞ (fun x => Φ (L (ψ x) + w)) ∧
      Injective (fun x => Φ (L (ψ x) + w)) ∧
      (∀ x, Injective (mfderiv 𝓘(ℝ, A) J (fun y => Φ (L (ψ y) + w)) x)) ∧
      IsClosedEmbedding (fun x : closedBall (0 : A) 1 => Φ (L (ψ x.val) + w)) := by
  have haff : ContDiff ℝ ∞ (fun x => L x + w) := L.contDiff.add contDiff_const
  have h0 : (0 : A) ∈ (fun x => L x + w) ⁻¹' Φ.source := by
    simpa only [mem_preimage, map_zero, zero_add] using hw
  obtain ⟨ψ, hψ, hi, hd, hψ0, hsource⟩ :=
    exists_small_radial_disk (Φ.open_source.preimage haff.continuous) h0
  have hcoords : ContDiff ℝ ∞ (fun x => L (ψ x) + w) := haff.comp hψ
  have hg : ContMDiff 𝓘(ℝ, A) J ∞ (fun x => Φ (L (ψ x) + w)) :=
    Φ.contMDiffOn_toFun.comp_contMDiff hcoords.contMDiff hsource
  have hgi : Injective (fun x => Φ (L (ψ x) + w)) := by
    intro x y hxy
    exact hi (hL (add_right_cancel
      (Φ.toPartialEquiv.injOn (hsource x) (hsource y) hxy)))
  refine ⟨ψ, hψ, hi, hd, hψ0, hsource, hg, hgi, ?_,
    (hg.continuous.comp continuous_subtype_val).isClosedEmbedding
      (hgi.comp Subtype.val_injective)⟩
  intro x
  have hdc : fderiv ℝ (fun y => L (ψ y) + w) x = L.comp (fderiv ℝ ψ x) :=
    (((L.hasFDerivAt.comp x (hψ.differentiable (by simp) x).hasFDerivAt).add_const w)).fderiv
  change Injective (mfderiv 𝓘(ℝ, A) J (Φ ∘ (fun y => L (ψ y) + w)) x)
  rw [mfderiv_comp x (Φ.mdifferentiableAt (by simp) (hsource x))
    (hcoords.contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, hdc]
  exact (PartialChart.bijective_mfderiv Φ (hsource x)).injective.comp (hL.comp (hd x).1)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
