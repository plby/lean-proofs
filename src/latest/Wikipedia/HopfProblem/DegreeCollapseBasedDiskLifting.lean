import Wikipedia.HopfProblem.DegreeCollapseDiskCube
import Wikipedia.HopfProblem.DegreeCollapseHomotopySixMap

/-!
# Actual six-dimensional disk lifts with constant boundary

The exact boundary-preserving disk/cube homeomorphism transports the proved
surjectivity of native sixth homotopy to an actual relative disk lift.
Reducing a nonconstant prescribed boundary and side homotopy to this case
is a separate obligation; this file does not discard those data.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.BasedDiskLifting

open SixSphereCube SpecialPeriods.Threefold DiskCylinder

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The native sixth-homotopy surjection gives a genuine disk lift
relative to its whole boundary. -/
theorem exists_based_disk_lift (x : Space) (L : V ≃L[ℝ] (Fin 6 → ℝ))
    (u : C(Disk (E := V), Space))
    (hu : ∀ z : Disk (E := V), ‖(z : V)‖ = 1 →
      u z = SphereHomologyEquivalence.sphereMap x sphereBasePoint) :
    ∃ v : C(Disk (E := V), StandardSphere),
      (∀ z : Disk (E := V), ‖(z : V)‖ = 1 → v z = sphereBasePoint) ∧
      ((SphereHomologyEquivalence.sphereMap x).comp v).HomotopicRel u
        {z : Disk (E := V) | ‖(z : V)‖ = 1} := by
  let F := SphereHomologyEquivalence.sphereMap x
  let e := DiskCube.homeomorph L
  let q : GenLoop (Fin 6) Space (F sphereBasePoint) :=
    ⟨u.comp (e.symm : C(_, _)), fun z hz => hu (e.symm z)
      ((DiskCube.symm_boundary_iff L z).mpr hz)⟩
  obtain ⟨a, ha⟩ := (sphereMap_piSix_bijective x).2 ⟦q⟧
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  have he : SixthHurewicz.homotopyMap F sphereBasePoint ⟦p⟧ = ⟦q⟧ :=
    (congrArg (SixthHurewicz.homotopyMap F sphereBasePoint) hp).trans ha
  have hh : GenLoop.Homotopic (SecondHurewicz.mapGenLoop F sphereBasePoint p) q :=
    Quotient.exact he
  obtain ⟨H⟩ := hh
  let v : C(Disk (E := V), StandardSphere) := p.val.comp (e : C(_, _))
  refine ⟨v, ?_, ⟨{
    toFun := fun z => H (z.1, e z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩⟩
  · intro z hz
    exact p.property (e z) ((DiskCube.boundary_iff L z).mpr hz)
  · intro z
    exact H.apply_zero (e z)
  · intro z
    exact (H.apply_one (e z)).trans (congrArg u (e.symm_apply_apply z))
  · intro t z hz
    exact H.eq_fst t ((DiskCube.boundary_iff L z).mpr hz)

end Wikipedia.HopfProblem.DegreeCollapse.BasedDiskLifting
