import Wikipedia.HopfProblem.DegreeCollapseNativeBeltMeridian
import Wikipedia.SmoothSixDPoincare.MorseSphereEmbeddings

/-!
# The actual upper belt meridian is smooth, embedded, and immersive

Its fixed positive coordinate and nonzero scaled negative coordinate make
it an affine sphere in the original inverse Morse chart. Its image misses
the entire original belt, hence the whole forward basin of that critical
point on the upper level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

section Affine

variable {N F E H X : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

theorem injective_mfderiv_affine_sphere {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F X ∞) (L : N →L[ℝ] F) (hL : Injective L)
    (w : F) (u : sphere (0 : N) 1) (hu : L u.val + w ∈ Φ.source) :
    Injective (mfderiv (𝓡 n) I (fun v : sphere (0 : N) 1 => Φ (L v.val + w)) u) := by
  have hcoesm : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞
      (Subtype.val : sphere (0 : N) 1 → N) := contMDiff_coe_sphere (E := N) (n := n)
  have hcoe := hcoesm.mdifferentiableAt (x := u) (by simp)
  have haffine : ContDiff ℝ ∞ (fun x => L x + w) := L.contDiff.add contDiff_const
  have hlinear : MDifferentiableAt 𝓘(ℝ, N) 𝓘(ℝ, F) (fun x => L x + w) u.val :=
    haffine.contMDiff.mdifferentiableAt (by simp)
  have hderiv : fderiv ℝ (fun x => L x + w) u.val = L := (L.hasFDerivAt.add_const w).fderiv
  change Injective (mfderiv (𝓡 n) I (Φ ∘ ((fun x => L x + w) ∘ Subtype.val)) u)
  rw [mfderiv_comp u (Φ.mdifferentiableAt (by simp) hu) (hlinear.comp u hcoe),
    mfderiv_comp u hlinear hcoe, mfderiv_eq_fderiv, hderiv]
  exact (PartialChart.bijective_mfderiv Φ hu).injective.comp
    (hL.comp (mfderiv_coe_sphere_injective u))

end Affine

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem nativeUpperMeridian_injective (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ)) : Injective (nativeUpperMeridian S q v s) := by
  intro u w huw
  have hbound : |(s : ℝ)| ≤ 1 := by rw [abs_of_nonneg s.property.1]; exact s.property.2
  have hcoords := (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
    (nativeBeltArc_coordinates_mem_target S q u v hbound)
    (nativeBeltArc_coordinates_mem_target S q w v hbound) (congrArg Subtype.val huw)
  apply Subtype.ext
  exact smul_right_injective _ (mul_pos (S.data q).radius_pos hs).ne'
    (congrArg Prod.fst hcoords)

theorem nativeUpperMeridian_isClosedEmbedding (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ)) : IsClosedEmbedding (nativeUpperMeridian S q v s) :=
  (nativeUpperMeridian S q v s).continuous.isClosedEmbedding
    (nativeUpperMeridian_injective S q v s hs)

theorem nativeUpperMeridian_avoids_belt (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ))
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    nativeUpperMeridian S q v s u ∉ range (S.data q).surgery.beltSphere := by
  rintro ⟨w, hw⟩
  have he := (nativeBeltArc_belt_eq_iff S q u v w
    (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)).mp
      (congrArg Subtype.val hw.symm)
  exact hs.ne' he.1

theorem nativeUpperMeridian_contMDiff_ambient (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)]
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ nativeUpperMeridian S q v s) := by
  have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, (S.data q).chart.NegativeCoordinates) ∞
      (Subtype.val : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 → _) :=
    contMDiff_coe_sphere (n := n)
  have hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
        (S.data q).radius * (s : ℝ)) := contMDiff_const
  have hneg : ContMDiff (𝓡 n) 𝓘(ℝ, (S.data q).chart.NegativeCoordinates) ∞
      (fun u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
        ((S.data q).radius * (s : ℝ)) • u.val) := hscalar.smul hcoe
  have hcoords : ContMDiff (𝓡 n)
      𝓘(ℝ, (S.data q).chart.NegativeCoordinates × (S.data q).chart.PositiveCoordinates) ∞
      (fun u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
        BeltPassage.upper (S.data q).radius (s : ℝ) u.val v.val) :=
    hneg.prodMk_space contMDiff_const
  exact (S.data q).chart.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
    (fun u => nativeBeltArc_coordinates_mem_target S q u v
      (by rw [abs_of_nonneg s.property.1]; exact s.property.2))

theorem nativeUpperMeridian_immersive_ambient (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)]
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ nativeUpperMeridian S q v s) u) := by
  let N := (S.data q).chart.NegativeCoordinates
  let P := (S.data q).chart.PositiveCoordinates
  let L : N →L[ℝ] N × P := ((S.data q).radius * (s : ℝ)) • ContinuousLinearMap.inl ℝ N P
  let w : N × P := (0, ((S.data q).radius * Real.sqrt (1 + (s : ℝ) ^ 2)) • v.val)
  have hL : Injective L := by
    intro x y hxy
    exact smul_right_injective _ (mul_pos (S.data q).radius_pos hs).ne' (congrArg Prod.fst hxy)
  have hcoords (z : N) : L z + w = BeltPassage.upper (S.data q).radius (s : ℝ) z v.val := by
    simp [L, w, BeltPassage.upper]
  have heq : Subtype.val ∘ nativeUpperMeridian S q v s =
      fun z : sphere (0 : N) 1 => (S.data q).chart.splitChart.symm (L z.val + w) := by
    funext z
    rw [hcoords]
    rfl
  rw [heq]
  apply injective_mfderiv_affine_sphere (S.data q).chart.splitChart.symm L hL w u
  rw [hcoords]
  exact nativeBeltArc_coordinates_mem_target S q u v
    (by rw [abs_of_nonneg s.property.1]; exact s.property.2)

variable [FiniteDimensional ℝ E]

theorem nativeUpperMeridian_smooth_immersive (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)]
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeUpperMeridian S q v s) ∧
      ∀ u, Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        (nativeUpperMeridian S q v s) u) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  refine ⟨(RegularLevel.contMDiff_iff_inclusion hf (S.data q).upper_regular (𝓡 n)
    (nativeUpperMeridian S q v s)).mpr (nativeUpperMeridian_contMDiff_ambient S q n v s), ?_⟩
  intro u
  exact RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular (𝓡 n)
    (nativeUpperMeridian S q v s) u (nativeUpperMeridian_contMDiff_ambient S q n v s u)
    (nativeUpperMeridian_immersive_ambient S q n v s hs u)

theorem nativeUpperMeridian_avoids_forward_basin (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    ¬Tendsto (fun t => S.flow t (nativeUpperMeridian S q v s u).val) atTop (𝓝 q.val) := by
  intro h
  exact nativeUpperMeridian_avoids_belt S q v s hs u
    ((S.belt_basin_iff hf q (nativeUpperMeridian S q v s u)).mp h)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
