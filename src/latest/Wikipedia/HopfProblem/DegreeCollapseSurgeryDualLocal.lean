import Wikipedia.HopfProblem.DegreeCollapseSurgeryBeltVanishing
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# A single regular dual crossing kills the canonical belt class

Delete the unique source point of a continuous three-sphere meeting the
attaching core. Its map into the old patch factors every small link
through a contractible punctured three-sphere. The invertible derivative
of the actual native normal coordinate constructs a small link with
surjective normal homology map. The proved tube homotopy then kills the
literal belt map in degree two.
-/

noncomputable section

open Set Function Filter Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₃" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [Fact (Module.finrank ℝ F = 2 + 1)]

def dualNormal (g : C(S₃, X)) (q : S₃) (z : P₃) : F :=
  (A.chart.symm (g (NativeParametrization.centered (D := P₃) q z))).2

def dualNeighborhood (g : C(S₃, X)) (q : S₃) : Set P₃ :=
  let Φ := NativeParametrization.centered (D := P₃) q
  Φ.source ∩
    ((fun z : P₃ => g (Φ z)) ⁻¹' A.chart.target ∩ dualNormal A g q ⁻¹' ball 0 1)

theorem nonempty_dual_boundary (g : C(S₃, X)) (q : S₃) (u : UnitSphere E)
    (hpoint : g q = coreMap A u)
    (L : P₃ ≃L[ℝ] F) (hL : HasFDerivAt (dualNormal A g q) L.toContinuousLinearMap 0) :
    Nonempty (LocalDegree.BoundaryData (dualNormal A g q) L (dualNeighborhood A g q)) := by
  let Φ := NativeParametrization.centered (D := P₃) q
  have hΦ0 : (0 : P₃) ∈ Φ.source := NativeParametrization.zero_mem_centered_source q
  have hΦq : Φ 0 = q := NativeParametrization.centered_zero q
  have hu : (u, (0 : F)) ∈ A.chart.source := A.source ⟨mem_univ _, by simp⟩
  have hchart : A.chart (u, (0 : F)) = g q := by
    exact (A.point u ⟨0, by simp⟩).trans hpoint.symm
  have ht0 : g q ∈ A.chart.target := hchart ▸ A.chart.map_source' hu
  have hinv : A.chart.symm (g q) = (u, (0 : F)) := by
    rw [← hchart]
    exact A.chart.left_inv hu
  have hzero : dualNormal A g q 0 = 0 := by
    change (A.chart.symm (g (Φ 0))).2 = 0
    rw [hΦq, hinv]
  have hΦc : ContinuousAt Φ 0 :=
    Φ.contMDiffOn_toFun.continuousOn.continuousAt (Φ.open_source.mem_nhds hΦ0)
  have hgc : ContinuousAt (fun z : P₃ => g (Φ z)) 0 := g.continuous.continuousAt.comp hΦc
  have hic : ContinuousAt A.chart.symm (g (Φ 0)) := by
    apply A.chart.contMDiffOn_invFun.continuousOn.continuousAt
    apply A.chart.open_target.mem_nhds
    rwa [hΦq]
  have hcc := hic.comp (f := fun z : P₃ => g (Φ z)) hgc
  have hnc : ContinuousAt (dualNormal A g q) 0 := hcc.snd
  let s := dualNeighborhood A g q
  have hs : s ∈ 𝓝 (0 : P₃) := by
    refine inter_mem (Φ.open_source.mem_nhds hΦ0) (inter_mem ?_ ?_)
    · apply hgc.preimage_mem_nhds
      apply A.chart.open_target.mem_nhds
      rwa [hΦq]
    · apply hnc.preimage_mem_nhds
      rw [hzero]
      exact ball_mem_nhds _ (by norm_num)
  have hcs : ContinuousOn (dualNormal A g q) s := by
    have hg : ContinuousOn (fun z : P₃ => g (Φ z)) s :=
      g.continuous.comp_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono inter_subset_left)
    exact (A.chart.contMDiffOn_invFun.continuousOn.comp hg (fun z hz => hz.2.1)).snd
  exact LocalDegree.nonempty_boundaryData L hL hzero hs hcs

def puncturedDual (g : C(S₃, X)) (q : S₃)
    (hunique : ∀ x, g x ∈ range (coreMap A) → x = q) :
    C(({q}ᶜ : Set S₃), oldPatch A) where
  toFun x := ⟨g x.val, fun h => x.property (hunique x.val h)⟩
  continuous_toFun := (g.continuous.comp continuous_subtype_val).subtype_mk _

section Boundary

variable (g : C(S₃, X)) (q : S₃) {L : P₃ ≃L[ℝ] F}
  (b : LocalDegree.BoundaryData (dualNormal A g q) L (dualNeighborhood A g q))

theorem dual_boundary_mem (v : sphere (0 : P₃) 1) :
    b.radius • v.val ∈ dualNeighborhood A g q := by
  apply b.ball_subset
  rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos v]

theorem dual_boundary_ne (v : sphere (0 : P₃) 1) :
    NativeParametrization.centered (D := P₃) q (b.radius • v.val) ≠ q := by
  let Φ := NativeParametrization.centered (D := P₃) q
  have hΦ0 : (0 : P₃) ∈ Φ.source := NativeParametrization.zero_mem_centered_source q
  have hΦq : Φ 0 = q := NativeParametrization.centered_zero q
  intro hv
  have hsrc : b.radius • v.val ∈ Φ.source := (dual_boundary_mem A g q b v).1
  have heq : Φ (b.radius • v.val) = Φ 0 := hv.trans hΦq.symm
  have he : b.radius • v.val = (0 : P₃) := Φ.toPartialEquiv.injOn hsrc hΦ0 heq
  have hn := congrArg norm he
  rw [LocalDegree.norm_radius_smul b.radius b.radius_pos v, norm_zero] at hn
  exact b.radius_pos.ne' hn

def dualBoundaryLink : C(sphere (0 : P₃) 1, ({q}ᶜ : Set S₃)) where
  toFun v := ⟨NativeParametrization.centered (D := P₃) q (b.radius • v.val),
    dual_boundary_ne A g q b v⟩
  continuous_toFun := by
    let Φ := NativeParametrization.centered (D := P₃) q
    have hp : Continuous (fun v : sphere (0 : P₃) 1 => b.radius • v.val) :=
      (continuous_subtype_val : Continuous (fun v : sphere (0 : P₃) 1 => v.val)).const_smul
        b.radius
    have h := Φ.contMDiffOn_toFun.continuousOn.comp_continuous hp
      (fun v => (dual_boundary_mem A g q b v).1)
    exact h.subtype_mk _

def dualBoundaryCoordinates : C(sphere (0 : P₃) 1, UnitSphere E × F) where
  toFun v := A.chart.symm (g ((dualBoundaryLink A g q b v).val))
  continuous_toFun :=
    A.chart.contMDiffOn_invFun.continuousOn.comp_continuous
      (g.continuous.comp (continuous_subtype_val.comp (dualBoundaryLink A g q b).continuous))
      (fun v => (dual_boundary_mem A g q b v).2.1)

def dualBoundaryOverlap : C(sphere (0 : P₃) 1, Overlap E F) where
  toFun v := ((dualBoundaryCoordinates A g q b v).1,
    ⟨(dualBoundaryCoordinates A g q b v).2, (b.map v).property,
      mem_ball_zero_iff.mp (dual_boundary_mem A g q b v).2.2⟩)
  continuous_toFun := (dualBoundaryCoordinates A g q b).continuous.fst.prodMk
    ((dualBoundaryCoordinates A g q b).continuous.snd.subtype_mk _)

theorem dual_boundary_factor
    (hunique : ∀ x, g x ∈ range (coreMap A) → x = q) :
    (puncturedDual A g q hunique).comp (dualBoundaryLink A g q b) =
      (oldTube A).comp (dualBoundaryOverlap A g q b) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  change g ((dualBoundaryLink A g q b v).val) = A.map _
  calc
    _ = A.chart (A.chart.symm (g ((dualBoundaryLink A g q b v).val))) :=
      (A.chart.right_inv (dual_boundary_mem A g q b v).2.1).symm
    _ = _ := A.point (dualBoundaryCoordinates A g q b v).1
      ⟨(dualBoundaryCoordinates A g q b v).2,
        mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp (dual_boundary_mem A g q b v).2.2).le⟩

theorem dual_boundary_normal : (normalDirection (E := E) (m := m) 2).comp
    (dualBoundaryOverlap A g q b) = b.normalizedMap := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rfl

end Boundary

theorem single_regular_dual_kills_belt (g : C(S₃, X)) (q : S₃) (u : UnitSphere E)
    (hpoint : g q = coreMap A u)
    (hunique : ∀ x, g x ∈ range (coreMap A) → x = q)
    (L : P₃ ≃L[ℝ] F) (hL : HasFDerivAt (dualNormal A g q) L.toContinuousLinearMap 0) :
    singularHomologyMap (beltMap A 2) 2 = 0 := by
  obtain ⟨b⟩ := nonempty_dual_boundary A g q u hpoint L hL
  let Z := ({q}ᶜ : Set S₃)
  let : ContractibleSpace Z := SpherePoint.puncture_contractible (n := 3) q
  let : Subsingleton (SingularHomology Z 2) :=
    contractible_homology_subsingleton Z 2 (by decide)
  apply belt_homology_zero_of_link A 2 2 (puncturedDual A g q hunique)
    (dualBoundaryLink A g q b) (dualBoundaryOverlap A g q b)
    (dual_boundary_factor A g q b hunique)
  rw [dual_boundary_normal]
  have he : (b.normalizedHomologyEquiv 2 :
      SingularHomology (sphere (0 : P₃) 1) 2 → SingularHomology (sphere (0 : F) 1) 2) =
      singularHomologyMap b.normalizedMap 2 := funext (b.normalizedHomologyEquiv_apply 2)
  rw [← he]
  exact (b.normalizedHomologyEquiv 2).surjective

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink
