import Wikipedia.HopfProblem.DegreeCollapseUnitSphereEquiv
import Wikipedia.HopfProblem.DegreeCollapseSphereCube
import Wikipedia.HopfProblem.DegreeCollapseSixSphereConnectivity
import Mathlib.Topology.Homotopy.Path

/-!
# Every cell boundary through dimension six extends into the standard sphere

All positive-dimensional source spheres use the native vanishing homotopy
groups and actual cube-quotient descent. Zero-dimensional spheres use paths;
the empty boundary of a zero-dimensional cell is handled separately.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.Sphere

open SixSphereCube DiskCylinder

theorem pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6) (x : StandardSphere) :
    Subsingleton (π_ n StandardSphere x) := by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact piTwo_subsingleton x
  · exact piThree_subsingleton x
  · exact piFour_subsingleton x
  · exact piFive_subsingleton x

theorem homotopic_const_discrete {Z X : Type} [TopologicalSpace Z] [DiscreteTopology Z]
    [TopologicalSpace X] [PathConnectedSpace X] (u : C(Z, X)) (x : X) :
    u.Homotopic (ContinuousMap.const Z x) := by
  refine ⟨{
    toFun := fun p => (PathConnectedSpace.somePath (u p.2) x) p.1
    continuous_toFun := continuous_prod_of_discrete_right.mpr
      (fun z => (PathConnectedSpace.somePath (u z) x).continuous)
    map_zero_left := fun z => (PathConnectedSpace.somePath (u z) x).source
    map_one_left := fun z => (PathConnectedSpace.somePath (u z) x).target
  }⟩

theorem real_unitSphere_finite : (sphere (0 : ℝ) 1).Finite := by
  apply (Set.toFinite ({1, -1} : Set ℝ)).subset
  intro x hx
  have h : |x| = |(1 : ℝ)| := by simpa using mem_sphere_zero_iff_norm.mp hx
  rcases abs_eq_abs.mp h with h | h <;> simp [h]

theorem homotopic_const_of_homeomorph {Z W X : Type} [TopologicalSpace Z]
    [TopologicalSpace W] [TopologicalSpace X] (e : Z ≃ₜ W) (u : C(Z, X)) (x : X)
    (h : (u.comp (e.symm : C(W, Z))).Homotopic (ContinuousMap.const W x)) :
    u.Homotopic (ContinuousMap.const Z x) := by
  have hh := h.comp (ContinuousMap.Homotopic.refl (e : C(Z, W)))
  convert hh using 1
  · apply ContinuousMap.ext
    intro z
    exact (congrArg u (e.symm_apply_apply z)).symm
  · rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {d : ℕ}

/-- Native homotopy vanishing supplies actual nullhomotopies
on all bounded-dimensional boundaries. -/
theorem boundary_homotopic_const_of_pi
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d)
    (u : C(DiskCylinder.Sphere (E := V), X)) (x : X) :
    u.Homotopic (ContinuousMap.const _ x) := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl h =>
    have hempty (s : DiskCylinder.Sphere (E := V)) : False :=
      UnitSphereEquiv.vector_ne_zero s (Subsingleton.elim _ _)
    have he : u = ContinuousMap.const _ x := ContinuousMap.ext (fun s => (hempty s).elim)
    rw [he]
  | inr h =>
    by_cases hd1 : Module.finrank ℝ V = 1
    · obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
        (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hd1)
      let e := UnitSphereEquiv.homeomorph L
      let : Finite (DiskCylinder.Sphere (E := ℝ)) := real_unitSphere_finite.to_subtype
      let : Finite (DiskCylinder.Sphere (E := V)) := Finite.of_injective e e.injective
      exact homotopic_const_discrete u x
    · have hdpos : 0 < Module.finrank ℝ V := Module.finrank_pos
      let n := Module.finrank ℝ V - 1
      have hn : 0 < n := by dsimp [n]; omega
      have hnd : n < d := by dsimp [n]; omega
      obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
        (show Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) by
          simp only [finrank_euclideanSpace, Fintype.card_fin]
          dsimp [n]
          omega)
      let e := UnitSphereEquiv.homeomorph L
      let v : C(SphereCube.Sphere n, X) := u.comp (e.symm : C(_, _))
      let := hpi n hn hnd (v (SphereCube.point n))
      obtain ⟨H⟩ := SphereCube.homotopicRel_const_of_subsingleton hn v
      have hstart : v.Homotopic (ContinuousMap.const _ (v (SphereCube.point n))) :=
        ⟨H.toHomotopy⟩
      have hv : v.Homotopic (ContinuousMap.const _ x) :=
        hstart.trans
          ⟨(PathConnectedSpace.somePath (v (SphereCube.point n)) x).toHomotopyConst⟩
      exact homotopic_const_of_homeomorph e u x hv

/-- The extension is an actual continuous disk map with exactly the prescribed boundary. -/
theorem exists_boundary_extension_of_pi
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d) (u : C(DiskCylinder.Sphere (E := V), X)) (x : X) :
    ∃ v : C(Disk (E := V), X),
      (∀ s, v (boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x := by
  classical
  cases isEmpty_or_nonempty (DiskCylinder.Sphere (E := V)) with
  | inl h =>
    exact ⟨ContinuousMap.const _ x, fun s => isEmptyElim s, rfl⟩
  | inr h =>
    let s0 : DiskCylinder.Sphere (E := V) := Classical.choice h
    obtain ⟨H⟩ := (boundary_homotopic_const_of_pi hpi hd u x).symm
    let G := H.toContinuousMap
    have h0 : ∀ s, G (0, s) = x := H.map_zero_left
    refine ⟨DiskCone.extension s0 G x h0, ?_, DiskCone.extension_center s0 G x h0⟩
    intro s
    exact (DiskCone.extension_boundary s0 G x h0 s).trans (H.map_one_left s)

/-- Any map from the full boundary of a cell of dimension at most six is nullhomotopic in S⁶. -/
theorem boundary_homotopic_const (hd : Module.finrank ℝ V ≤ 6)
    (u : C(DiskCylinder.Sphere (E := V), StandardSphere)) (x : StandardSphere) :
    u.Homotopic (ContinuousMap.const _ x) :=
  boundary_homotopic_const_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

/-- All connectivity premises are discharged for the literal standard sphere. -/
theorem exists_boundary_extension (hd : Module.finrank ℝ V ≤ 6)
    (u : C(DiskCylinder.Sphere (E := V), StandardSphere)) (x : StandardSphere) :
    ∃ v : C(Disk (E := V), StandardSphere),
      (∀ s, v (boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x :=
  exists_boundary_extension_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

end Wikipedia.HopfProblem.DegreeCollapse.Sphere
