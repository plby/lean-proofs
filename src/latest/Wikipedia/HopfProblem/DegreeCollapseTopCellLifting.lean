import Wikipedia.HopfProblem.DegreeCollapseBasedDiskLifting
import Wikipedia.HopfProblem.DegreeCollapseLowCellLifting
import Wikipedia.HopfProblem.DegreeCollapseBoundaryPathTransport
import Wikipedia.HopfProblem.DegreeCollapseSideRectification

/-!
# Exact relative lifting at the six-dimensional obstruction

Contract the source boundary and transport the target disk along the reversed
prescribed side path and reversed boundary contraction. The resulting constant
boundary disk lifts by the actual sixth-homotopy surjection. Transport its
source boundary back. The extra boundary paths cancel in the genuine mapping
space, and full-cylinder HEP restores the original side path exactly.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TopCellLifting

open SixSphereCube SpecialPeriods.Threefold DiskCylinder MappingPaths

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Every prescribed boundary and side family is retained in the top-dimensional disk lift. -/
theorem exists_top_disk_lift (x : Space) (L : V ≃L[ℝ] (Fin 6 → ℝ))
    (hd : Module.finrank ℝ V ≤ 6)
    (a : C(DiskCylinder.Sphere (E := V), StandardSphere))
    (u : C(Disk (E := V), Space)) (H : C(I × DiskCylinder.Sphere (E := V), Space))
    (h0 : ∀ s, H (0, s) = SphereHomologyEquivalence.sphereMap x (a s))
    (h1 : ∀ s, H (1, s) = u (boundaryToDisk s)) :
    ∃ (v : C(Disk (E := V), StandardSphere)) (G : C(I × Disk (E := V), Space)),
      (∀ s, v (boundaryToDisk s) = a s) ∧
      (∀ z, G (0, z) = SphereHomologyEquivalence.sphereMap x (v z)) ∧
      (∀ z, G (1, z) = u z) ∧ ∀ t s, G (t, boundaryToDisk s) = H (t, s) := by
  let F := SphereHomologyEquivalence.sphereMap x
  let c : C(DiskCylinder.Sphere (E := V), StandardSphere) :=
    ContinuousMap.const _ sphereBasePoint
  obtain ⟨Ac⟩ := (Sphere.boundary_homotopic_const hd a sphereBasePoint).symm
  let A : Path c a := ofHomotopy Ac
  let FA : Path (F.comp c) (F.comp a) := A.map (ContinuousMap.continuous_postcomp F)
  let HP : Path (F.comp a) (u.comp boundaryToDisk) := {
    toContinuousMap := H.curry
    source' := ContinuousMap.ext h0
    target' := ContinuousMap.ext h1
  }
  let K := HP.symm.trans FA.symm
  obtain ⟨u₀, E, hE, hu₀⟩ := BoundaryPathTransport.exists_transport u K rfl
  have hu₀' : ∀ z : Disk (E := V), ‖(z : V)‖ = 1 → u₀ z = F sphereBasePoint := by
    intro z hz
    exact ContinuousMap.congr_fun hu₀ ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨p, hp, ⟨B⟩⟩ := BasedDiskLifting.exists_based_disk_lift x L u₀ hu₀'
  have hp' : p.comp boundaryToDisk = c := by
    apply ContinuousMap.ext
    intro s
    exact hp (boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)
  obtain ⟨v, P, hP, hv⟩ := BoundaryPathTransport.exists_transport p A hp'
  let FP : Path (F.comp p) (F.comp v) := P.map (ContinuousMap.continuous_postcomp F)
  let BP := ofHomotopy B.toHomotopy
  have hFP : Over (fun w : C(Disk (E := V), Space) => w.comp boundaryToDisk) FP FA := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact congrArg F (ContinuousMap.congr_fun (hP t) s)
  have hBP : Over (fun w : C(Disk (E := V), Space) => w.comp boundaryToDisk) BP
      (Path.refl (F.comp c)) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(boundaryToDisk s : V)‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
    exact (B.eq_fst t hs).trans (congrArg F (hp (boundaryToDisk s) hs))
  let R := FP.symm.trans (BP.trans E.symm)
  let Q := FA.symm.trans ((Path.refl (F.comp c)).trans K.symm)
  have hR : Over (fun w : C(Disk (E := V), Space) => w.comp boundaryToDisk) R Q :=
    hFP.symm.trans (hBP.trans hE.symm)
  have hQ : Q.Homotopic HP := normalization_cancellation FA HP
  obtain ⟨G, hG0, hG1, hGside⟩ := SideRectification.exists_rectification R Q HP hR hQ
  exact ⟨v, G, fun s => ContinuousMap.congr_fun hv s, hG0, hG1, hGside⟩

/-- The original sphere map has exact relative disk lifting through dimension six. -/
theorem sphereMap_relativeDiskLifting_six (x : Space) :
    FiniteCells.RelativeDiskLifting (SphereHomologyEquivalence.sphereMap x) 6 := by
  intro V _ _ _ hd a u H h0 h1
  by_cases hlow : Module.finrank ℝ V ≤ 5
  · exact LowCellLifting.sphereMap_relativeDiskLifting_five x V hlow a u H h0 h1
  · have heq : Module.finrank ℝ V = 6 := by omega
    obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ (Fin 6 → ℝ) by simpa using heq)
    exact exists_top_disk_lift x L hd a u H h0 h1

end Wikipedia.HopfProblem.DegreeCollapse.TopCellLifting
