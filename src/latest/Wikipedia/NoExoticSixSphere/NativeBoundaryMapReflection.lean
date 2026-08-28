import Wikipedia.NoExoticSixSphere.RelativeDiskLiftingWithSide
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.HopfProblem.DegreeCollapseSphereBoundaryExtension

/-!
# Native injectivity reflects exact sphere-boundary extensions

An actual filling contracts its boundary to a specified boundary point
by straight segments inside the original closed ball. This is a based
nullhomotopy in an arbitrary target. The original cube/sphere
correspondence reflects that homotopy through the native induced map;
radial descent then gives a source filling with the exact boundary.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.RelativeDiskLifting

variable {n : ℕ} {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

theorem sphere_homotopicRel_reflect (hn : 0 < n) (F : C(A, B))
    (hF : ∀ x : A, Function.Injective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (f g : C(Sphere n, A)) (hp : f (spherePole n) = g (spherePole n))
    (H : (F.comp f).HomotopicRel (F.comp g) {spherePole n}) :
    f.HomotopicRel g {spherePole n} := by
  let f₀ : SmoothCube.BasedMap n A (f (spherePole n)) := ⟨f, rfl⟩
  let g₀ : SmoothCube.BasedMap n A (f (spherePole n)) := ⟨g, hp.symm⟩
  apply (SmoothCube.sphereClass_eq_iff hn f₀ g₀).mp
  apply hF (f (spherePole n))
  change SmoothCube.sphereClass ⟨F.comp f, rfl⟩ =
    SmoothCube.sphereClass ⟨F.comp g, congrArg F hp.symm⟩
  exact (SmoothCube.sphereClass_eq_iff hn _ _).mpr H

open DegreeCollapse DegreeCollapse.DiskCylinder

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def boundarySegment (p : DiskCylinder.Sphere (E := V)) :
    C(I × DiskCylinder.Sphere (E := V), Disk (E := V)) where
  toFun z := ⟨(1 - z.1.val) • z.2.val + z.1.val • p.val,
    convex_closedBall (0 : V) 1
      (sphere_subset_closedBall z.2.property) (sphere_subset_closedBall p.property)
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 z.1.val)⟩
  continuous_toFun := by fun_prop

theorem boundarySegment_zero (p s : DiskCylinder.Sphere (E := V)) :
    boundarySegment p (0, s) = boundaryToDisk s := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) • s.val + (0 : ℝ) • p.val = s.val
  simp

theorem boundarySegment_one (p s : DiskCylinder.Sphere (E := V)) :
    boundarySegment p (1, s) = boundaryToDisk p := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) • s.val + (1 : ℝ) • p.val = p.val
  simp

theorem boundarySegment_fixed (p : DiskCylinder.Sphere (E := V)) (t : I) :
    boundarySegment p (t, p) = boundaryToDisk p := by
  apply Subtype.ext
  change (1 - t.val) • p.val + t.val • p.val = p.val
  rw [← add_smul, sub_add_cancel, one_smul]

def boundaryNullhomotopy (a : C(Disk (E := V), A)) (p : DiskCylinder.Sphere (E := V)) :
    (a.comp boundaryToDisk).HomotopyRel (ContinuousMap.const _ (a (boundaryToDisk p))) {p} where
  toContinuousMap := a.comp (boundarySegment p)
  map_zero_left s := congrArg a (boundarySegment_zero p s)
  map_one_left s := congrArg a (boundarySegment_one p s)
  prop' := by
    intro t s hs
    have hsp : s = p := hs
    subst s
    exact congrArg a (boundarySegment_fixed p t)

variable [FiniteDimensional ℝ V]

theorem boundary_extension_of_native_injective (hn : 0 < n) (F : C(A, B))
    (hF : ∀ x : A, Function.Injective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (e : DiskCylinder.Sphere (E := V) ≃ₜ NoExoticSixSphere.Sphere n)
    (a : C(DiskCylinder.Sphere (E := V), A)) (u : C(Disk (E := V), B))
    (hu : ∀ s, u (boundaryToDisk s) = F (a s)) :
    ∃ v : C(Disk (E := V), A), ∀ s, v (boundaryToDisk s) = a s := by
  let p := e.symm (spherePole n)
  let f : C(NoExoticSixSphere.Sphere n, A) := a.comp (e.symm : C(_, _))
  let K := boundaryNullhomotopy u p
  have hK : (F.comp f).HomotopicRel
      (F.comp (ContinuousMap.const _ (f (spherePole n)))) {spherePole n} := by
    refine ⟨{
      toContinuousMap := K.toHomotopy.toContinuousMap.comp
        ((ContinuousMap.id I).prodMap (e.symm : C(_, _)))
      map_zero_left := fun s ↦ (K.apply_zero (e.symm s)).trans (hu (e.symm s))
      map_one_left := fun _ ↦ (K.apply_one _).trans (hu p)
      prop' := ?_ }⟩
    intro t s hs
    rcases Set.mem_singleton_iff.mp hs with rfl
    exact (K.eq_fst t (Set.mem_singleton p)).trans (hu p)
  have hA := sphere_homotopicRel_reflect hn F hF f
    (ContinuousMap.const _ (f (spherePole n))) rfl hK
  have hnull : a.Homotopic (ContinuousMap.const _ (a p)) :=
    DegreeCollapse.Sphere.homotopic_const_of_homeomorph e a (a p) hA.homotopic
  obtain ⟨H⟩ := hnull.symm
  refine ⟨DiskCone.extension p H.toContinuousMap (a p) H.map_zero_left, ?_⟩
  intro s
  exact (DiskCone.extension_boundary p H.toContinuousMap (a p) H.map_zero_left s).trans
    (H.map_one_left s)

end NoExoticSixSphere.RelativeDiskLifting
