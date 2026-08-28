import Wikipedia.HopfProblem.OrbitPairFreeHomotopyLifting
import Wikipedia.HopfProblem.OrbitPairMeridianPullback
import Wikipedia.HopfProblem.OrbitPairFreeLocus

/-!
# Compact homotopy lifting for the actual Hopf sphere map

The existing meridian diagram is a proved topological pullback of the
free circle projection. Pulling its homotopy lifts back gives lifts on
the normal three-sphere, retaining all stationary parameters.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.OrbitPair
open HopfProblem.SpecialPeriods HopfProblem.SpecialPeriods.Threefold
open HopfProblem.CuspCircleNormalTrivialization

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

/-- The Hopf map has the compact homotopy lifting property, fixing stationary parameters. -/
theorem hopf_exists_homotopy_lift (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius)
    (H : C(I × X, MeridianSphere r)) (a₀ : C(X, NormalSphere r))
    (ha₀ : ∀ x, sphereHopfMap r (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, NormalSphere r), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, sphereHopfMap r (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x := by
  let e := meridianPullbackHomeomorph b r hr₀ hr
  obtain ⟨G, hG₀, hGp, hGfix⟩ := freeOrbitProjection_exists_homotopy_lift
    ((freeMeridian b r hr₀ hr).comp H) ((freeNormalSphereMap b r hr₀ hr).comp a₀)
    (fun x => by
      change freeOrbitProjection (freeNormalSphereMap b r hr₀ hr (a₀ x)) =
        freeMeridian b r hr₀ hr (H (0, x))
      rw [freeOrbitProjection_freeNormalSphereMap, ha₀ x])
  let K : C(I × X, MeridianPullback b r hr) := {
    toFun z := ⟨(H z, (G z).val),
      (congrArg (fun y : freeOrbitLocus => y.val) (hGp z.1 z.2)).symm⟩
    continuous_toFun :=
      (H.continuous.prodMk (continuous_subtype_val.comp G.continuous)).subtype_mk _ }
  let L : C(I × X, NormalSphere r) := (e.symm : C(_, _)).comp K
  have hK (t : I) (x : X) : e (L (t, x)) = K (t, x) := e.apply_symm_apply _
  have hinit (x : X) : K (0, x) = e (a₀ x) := by
    apply Subtype.ext
    exact Prod.ext (ha₀ x).symm (congrArg (fun z : freeLocus => z.val) (hG₀ x))
  refine ⟨L, fun x => e.injective ((hK 0 x).trans (hinit x)), ?_, ?_⟩
  · intro t x
    exact congrArg (fun z : MeridianPullback b r hr => z.val.1) (hK t x)
  · intro x hx t
    apply e.injective
    rw [hK]
    apply Subtype.ext
    apply Prod.ext
    · exact (hx t).trans (ha₀ x).symm
    · exact congrArg (fun z : freeLocus => z.val)
        (hGfix x (fun s => congrArg (freeMeridian b r hr₀ hr) (hx s)) t)

end Wikipedia.HomotopyGroupsOfSpheres
