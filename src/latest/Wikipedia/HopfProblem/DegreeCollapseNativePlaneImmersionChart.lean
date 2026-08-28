import Wikipedia.HopfProblem.DegreeCollapseKinkPlaneCoordinates
import Wikipedia.HopfProblem.OrbitPairLocalImmersionChart
import Wikipedia.NoExoticSixSphere.Definitions

/-!
# An original native immersion as the literal kink plane

Complete the actual derivative by its constructed complement. The resulting
native target chart proves that this complement has dimension three. A
continuous linear change identifies the chart domain with R6 while keeping
the original three-plane pointwise in its prescribed parameter coordinates.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem exists_native_plane_immersion_chart {f : Vector 3 → M} {U : Set (Vector 3)}
    (hU : IsOpen U) (h0U : (0 : Vector 3) ∈ U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 6) ∞ f U)
    (hi : Injective (mfderiv (𝓡 3) (𝓡 6) f 0))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Φ : PartialDiffeomorph (𝓡 6) (𝓡 6) (Vector 6) M ∞,
      closedBall (0 : Vector 6) ε ⊆ Φ.source ∧ Φ.target ⊆ O ∧
      ∀ x, plane x ∈ Φ.source → Φ (plane x) = f x := by
  obtain ⟨W, δ, hδ, Φ, hball, _, htarget, hplane⟩ :=
    OrbitPair.NativeImmersion.exists_local_immersion_chart hU h0U hf hi hO h0O
  have hzero : ((0 : Vector 3), (0 : W)) ∈ Φ.source :=
    hball ⟨mem_closedBall_self hδ.le, mem_closedBall_self hδ.le⟩
  have hlocal := Φ.isLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × W) (𝓡 6) ∞ hzero
  let L := hlocal.mfderivToContinuousLinearEquiv (by simp)
  have hdim : Module.finrank ℝ (Vector 3 × W) = Module.finrank ℝ (Vector 6) :=
    L.toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod, finrank_euclideanSpace_fin] at hdim
  have hW : Module.finrank ℝ W = 3 := by omega
  let C : Vector 3 ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq (by simp [hW])
  let A : Vector 6 ≃L[ℝ] Vector 3 × W :=
    planeSplit.trans ((ContinuousLinearEquiv.refl ℝ (Vector 3)).prodCongr C)
  have hA (x : Vector 3) : A (plane x) = (x, 0) := by
    change ((ContinuousLinearEquiv.refl ℝ (Vector 3)) (planeSplit (plane x)).1,
      C (planeSplit (plane x)).2) = (x, 0)
    rw [planeSplit_plane]
    simp
  let Q := A.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have h0Q : (0 : Vector 6) ∈ Q.source := by
    refine ⟨mem_univ _, ?_⟩
    change A 0 ∈ Φ.source
    rw [map_zero]
    exact hzero
  obtain ⟨ε, hε, hεQ⟩ := nhds_basis_closedBall.mem_iff.mp (Q.open_source.mem_nhds h0Q)
  refine ⟨ε, hε, Q, hεQ, fun _ hy ↦ htarget hy.1, ?_⟩
  intro x hx
  have hxΦ : (x, 0) ∈ Φ.source := by
    have h := hx.2
    change A (plane x) ∈ Φ.source at h
    rwa [hA] at h
  change Φ (A (plane x)) = f x
  rw [hA]
  exact hplane x hxΦ

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
