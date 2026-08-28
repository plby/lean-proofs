import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Actual sphere contractions imply native homotopy vanishing

An unbased nullhomotopy first extends over the actual disk. Contracting
that disk toward a selected boundary point then fixes the basepoint.
The exact sphere quotient converts this into a homotopy of native cubes
relative to every face. No assumption about a basepoint-change action is
needed, and no new homotopy relation is introduced.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SphereNullhomotopy

open DegreeCollapse DegreeCollapse.DiskCylinder

variable {X : Type*} [TopologicalSpace X]

theorem based_of_unbased {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (u : C(Sphere (E := V), X))
    (b : Sphere (E := V)) (c : X) (h : u.Homotopic (ContinuousMap.const _ c)) :
    u.HomotopicRel (ContinuousMap.const _ (u b)) {b} := by
  obtain ⟨H⟩ := h.symm
  let G := H.toContinuousMap
  have hG : ∀ s, G (0, s) = c := H.apply_zero
  apply (NoExoticSixSphere.DiskBoundary.exists_extension_iff b u).mp
  refine ⟨DiskCone.extension b G c hG, fun s => ?_⟩
  exact (DiskCone.extension_boundary b G c hG s).trans (H.apply_one s)

theorem genLoop_nullhomotopic_of_sphere_nullhomotopies {n : ℕ} (hn : 0 < n)
    (hnull : ∀ f : C(NoExoticSixSphere.Sphere n, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (x : X) (p : GenLoop (Fin n) X x) : GenLoop.Homotopic p GenLoop.const := by
  let f := NoExoticSixSphere.SmoothCube.descend hn p
  obtain ⟨c, hc⟩ := hnull f
  obtain ⟨H⟩ := based_of_unbased f (NoExoticSixSphere.spherePole n) c hc
  refine ⟨{
    toFun := fun z => H (z.1, NoExoticSixSphere.SmoothCube.quotient n z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk
        ((NoExoticSixSphere.SmoothCube.quotient n).continuous.comp continuous_snd))
    map_zero_left := fun z => (H.apply_zero _).trans
      (NoExoticSixSphere.SmoothCube.descend_quotient hn p z)
    map_one_left := fun z => (H.apply_one _).trans
      (NoExoticSixSphere.SmoothCube.descend_pole hn p)
    prop' := by
      intro t z hz
      exact (H.eq_fst t (show NoExoticSixSphere.SmoothCube.quotient n z ∈
        ({NoExoticSixSphere.spherePole n} : Set (NoExoticSixSphere.Sphere n)) from
          NoExoticSixSphere.SmoothCube.quotient_boundary n z hz)).trans
        (NoExoticSixSphere.SmoothCube.descend_quotient hn p z) }⟩

theorem pi_subsingleton_of_sphere_nullhomotopies {n : ℕ} (hn : 0 < n)
    (hnull : ∀ f : C(NoExoticSixSphere.Sphere n, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (x : X) : Subsingleton (π_ n X x) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b ?_⟩
  intro p q
  exact Quotient.sound ((genLoop_nullhomotopic_of_sphere_nullhomotopies hn hnull x p).trans
    (genLoop_nullhomotopic_of_sphere_nullhomotopies hn hnull x q).symm)

end Wikipedia.HopfProblem.OrbitPair.SphereNullhomotopy
