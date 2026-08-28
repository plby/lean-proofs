import Wikipedia.HopfProblem.DegreeCollapseDiskCube
import Wikipedia.HopfProblem.DegreeCollapseDiskCone
import Wikipedia.HopfProblem.DegreeCollapseBoundaryPathTransport
import Wikipedia.HopfProblem.DegreeCollapseSideRectification
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Relative disk lifting in arbitrary dimension

A prescribed source filling contracts its boundary to its center value.
Exact boundary transport reduces to a constant-boundary disk, and native
homotopy surjectivity lifts that disk. Transport back and the actual side
rectification restore the original nonconstant boundary pointwise.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.RelativeDiskLifting

open DegreeCollapse DegreeCollapse.DiskCylinder DegreeCollapse.MappingPaths

variable {n : ℕ} {A B V : Type} [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_based_lift (F : C(A, B))
    (hF : ∀ x : A, Function.Surjective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (L : V ≃L[ℝ] (Fin n → ℝ)) (x : A) (u : C(Disk (E := V), B))
    (hu : ∀ z : Disk (E := V), ‖(z : V)‖ = 1 → u z = F x) :
    ∃ v : C(Disk (E := V), A),
      (∀ z : Disk (E := V), ‖(z : V)‖ = 1 → v z = x) ∧
      (F.comp v).HomotopicRel u {z : Disk (E := V) | ‖(z : V)‖ = 1} := by
  let e := DiskCube.homeomorph L
  let q : GenLoop (Fin n) B (F x) :=
    ⟨u.comp (e.symm : C(_, _)), fun z hz ↦ hu (e.symm z)
      ((DiskCube.symm_boundary_iff L z).mpr hz)⟩
  obtain ⟨a, ha⟩ := hF x ⟦q⟧
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  have hh : GenLoop.Homotopic (HigherHomotopy.genLoopMap F rfl p) q := Quotient.exact ha
  obtain ⟨H⟩ := hh
  let v : C(Disk (E := V), A) := p.val.comp (e : C(_, _))
  refine ⟨v, fun z hz ↦ p.property (e z) ((DiskCube.boundary_iff L z).mpr hz), ⟨{
    toFun := fun z ↦ H (z.1, e z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := fun z ↦ H.apply_zero (e z)
    map_one_left := fun z ↦ (H.apply_one (e z)).trans (congrArg u (e.symm_apply_apply z))
    prop' := fun t z hz ↦ H.eq_fst t ((DiskCube.boundary_iff L z).mpr hz) }⟩⟩

theorem exists_relative_lift (F : C(A, B))
    (hF : ∀ x : A, Function.Surjective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (L : V ≃L[ℝ] (Fin n → ℝ)) (a : C(Disk (E := V), A)) (u : C(Disk (E := V), B))
    (hu : ∀ s : Sphere (E := V), u (boundaryToDisk s) = F (a (boundaryToDisk s))) :
    ∃ v : C(Disk (E := V), A),
      (∀ s : Sphere (E := V), v (boundaryToDisk s) = a (boundaryToDisk s)) ∧
      (F.comp v).HomotopicRel u {z : Disk (E := V) | ‖(z : V)‖ = 1} := by
  let x := a ⟨0, by simp⟩
  let c : C(Sphere (E := V), A) := ContinuousMap.const _ x
  let aB : C(Sphere (E := V), A) := a.comp boundaryToDisk
  let Ac : c.Homotopy aB := {
    toContinuousMap := a.comp DiskCone.radial
    map_zero_left := fun s ↦ congrArg a (DiskCone.radial_zero s)
    map_one_left := fun s ↦ congrArg a (DiskCone.radial_one s) }
  let AP : Path c aB := ofHomotopy Ac
  let FA : Path (F.comp c) (F.comp aB) := AP.map (ContinuousMap.continuous_postcomp F)
  let HP : Path (F.comp aB) (u.comp boundaryToDisk) := {
    toFun _ := F.comp aB
    continuous_toFun := continuous_const
    source' := rfl
    target' := ContinuousMap.ext (fun s ↦ (hu s).symm) }
  let K := HP.symm.trans FA.symm
  obtain ⟨u₀, E, hE, hu₀⟩ := BoundaryPathTransport.exists_transport u K rfl
  have hu₀' (z : Disk (E := V)) (hz : ‖(z : V)‖ = 1) : u₀ z = F x :=
    ContinuousMap.congr_fun hu₀ ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨p, hp, ⟨Hbased⟩⟩ := exists_based_lift F hF L x u₀ hu₀'
  have hp' : p.comp boundaryToDisk = c := by
    apply ContinuousMap.ext
    intro s
    exact hp (boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)
  obtain ⟨v, P, hP, hv⟩ := BoundaryPathTransport.exists_transport p AP hp'
  let FP : Path (F.comp p) (F.comp v) := P.map (ContinuousMap.continuous_postcomp F)
  let BP := ofHomotopy Hbased.toHomotopy
  have hFP : Over (fun w : C(Disk (E := V), B) ↦ w.comp boundaryToDisk) FP FA := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact congrArg F (ContinuousMap.congr_fun (hP t) s)
  have hBP : Over (fun w : C(Disk (E := V), B) ↦ w.comp boundaryToDisk) BP
      (Path.refl (F.comp c)) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(boundaryToDisk s : V)‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
    exact (Hbased.eq_fst t hs).trans (congrArg F (hp (boundaryToDisk s) hs))
  let R := FP.symm.trans (BP.trans E.symm)
  let Q := FA.symm.trans ((Path.refl (F.comp c)).trans K.symm)
  have hR : Over (fun w : C(Disk (E := V), B) ↦ w.comp boundaryToDisk) R Q :=
    hFP.symm.trans (hBP.trans hE.symm)
  obtain ⟨G, hG0, hG1, hGside⟩ := SideRectification.exists_rectification R Q HP hR
    (normalization_cancellation FA HP)
  refine ⟨v, fun s ↦ ContinuousMap.congr_fun hv s, ⟨{
    toContinuousMap := G
    map_zero_left := hG0
    map_one_left := hG1
    prop' := ?_ }⟩⟩
  intro t z hz
  let s : Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  exact (hGside t s).trans (congrArg F (ContinuousMap.congr_fun hv s)).symm

end NoExoticSixSphere.RelativeDiskLifting
