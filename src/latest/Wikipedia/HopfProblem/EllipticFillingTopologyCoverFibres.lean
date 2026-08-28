import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifted endpoints of loops in a simply connected cover

For an actual covering with simply connected total space, the endpoint of
the lifted loop identifies its fundamental group, as a set, with the fibre
above the basepoint. This is the topological input for explicit affine
normal forms; no quotient-group action or presentation is assumed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] {p : E → X} (hp : IsCoveringMap p) (e : E)

theorem covering_monodromy_at_injective :
    Function.Injective (fun γ : FundamentalGroup X (p e) =>
      hp.monodromy γ ⟨e, rfl⟩) := by
  intro γ δ h
  have hend : (hp.monodromy γ ⟨e, rfl⟩ : E) =
      (hp.monodromy δ ⟨e, rfl⟩ : E) := congrArg Subtype.val h
  let Γ := hp.liftPathQuotient γ ⟨e, rfl⟩
  let Δ := hp.liftPathQuotient δ ⟨e, rfl⟩
  let f : ContinuousMap E X := ⟨p, hp.continuous⟩
  have hpath : Γ = Δ.cast rfl hend := Subsingleton.elim _ _
  have hmap := congrArg (fun q => q.map f) hpath
  have hΓ : HEq (Γ.map f) γ :=
    (heq_of_eq (hp.map_liftPathQuotient γ ⟨e, rfl⟩)).trans
      (Path.Homotopic.Quotient.cast_heq _ _)
  have hΔ : HEq ((Δ.cast rfl hend).map f) δ := by
    apply (heq_of_eq (Path.Homotopic.Quotient.map_cast Δ)).trans
    apply (Path.Homotopic.Quotient.cast_heq _ _).trans
    exact (heq_of_eq (hp.map_liftPathQuotient δ ⟨e, rfl⟩)).trans
      (Path.Homotopic.Quotient.cast_heq _ _)
  exact eq_of_heq (hΓ.symm.trans ((heq_of_eq hmap).trans hΔ))

theorem covering_monodromy_at_surjective :
    Function.Surjective (fun γ : FundamentalGroup X (p e) =>
      hp.monodromy γ ⟨e, rfl⟩) := by
  intro y
  let Γ := PathConnectedSpace.somePath e (y : E)
  let γ := (Path.Homotopic.Quotient.mk Γ).map ⟨p, hp.continuous⟩
  refine ⟨FundamentalGroup.fromPath (γ.cast rfl y.property.symm), ?_⟩
  apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The actual lifted-endpoint correspondence for a simply connected cover. -/
def fundamentalGroupCoverFibreEquiv : FundamentalGroup X (p e) ≃ p ⁻¹' {p e} :=
  Equiv.ofBijective (fun γ => hp.monodromy γ ⟨e, rfl⟩)
    ⟨covering_monodromy_at_injective hp e, covering_monodromy_at_surjective hp e⟩

@[simp] theorem fundamentalGroupCoverFibreEquiv_apply
    (γ : FundamentalGroup X (p e)) :
    fundamentalGroupCoverFibreEquiv hp e γ = hp.monodromy γ ⟨e, rfl⟩ := rfl

end Wikipedia.HopfProblem
