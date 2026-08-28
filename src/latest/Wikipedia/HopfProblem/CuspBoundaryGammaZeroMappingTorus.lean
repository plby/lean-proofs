import Wikipedia.HopfProblem.MappingTorusTopology

/-!
# Actual mapping-torus maps from equivariant fibre maps

A continuous map intertwining two homeomorphisms intertwines all their
integer powers.  Its product with the identity on real time therefore
descends through the original deck-orbit quotients.  The resulting map is
continuous, preserves the actual base-circle map, and is injective when
the original fibre map is injective.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x))

include he in
private theorem equivariant_zpow (n : ℤ) (x : X) :
    e ((f ^ n) x) = (g ^ n) (e x) := by
  have hinv (x : X) : e (f.symm x) = g.symm (e x) := by
    apply g.injective
    rw [← he, f.apply_symm_apply, g.apply_symm_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [zpow_add_one, Homeomorph.mul_apply]
    rw [ih, he]
  | pred n ih =>
    simp only [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply]
    rw [ih, hinv]

/-- The actual map on deck-orbit quotients induced by the equivariant fibre map. -/
def mappingTorusMap : C(MappingTorus.Torus f, MappingTorus.Torus g) where
  toFun := Quotient.lift
    (fun p : ℝ × X => MappingTorus.mk g (p.1, e p.2)) (by
      rintro p q ⟨n, rfl⟩
      change MappingTorus.mk g (p.1, e p.2) =
        MappingTorus.mk g (p.1 + (n : ℝ), e ((f ^ (-n)) p.2))
      rw [equivariant_zpow f g e he]
      exact (MappingTorus.mk_deck g n (p.1, e p.2)).symm)
  continuous_toFun :=
    ((MappingTorus.mk_continuous g).comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd))).quotient_lift _

/-- On every real-cylinder representative, only the fibre coordinate changes. -/
@[simp] theorem mappingTorusMap_mk (t : ℝ) (x : X) :
    mappingTorusMap f g e he (MappingTorus.mk f (t, x)) =
      MappingTorus.mk g (t, e x) := rfl

/-- The quotient map preserves the actual projection to the base circle. -/
@[simp] theorem mappingTorusMap_base (q : MappingTorus.Torus f) :
    MappingTorus.base g (mappingTorusMap f g e he q) = MappingTorus.base f q := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective f q
  rfl

/-- An injective equivariant fibre map induces an injective mapping-torus map. -/
theorem mappingTorusMap_injective (hinj : Function.Injective e) :
    Function.Injective (mappingTorusMap f g e he) := by
  intro p q hpq
  obtain ⟨⟨s, x⟩, rfl⟩ := MappingTorus.mk_surjective f p
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective f q
  rw [mappingTorusMap_mk, mappingTorusMap_mk] at hpq
  obtain ⟨n, ht, hx⟩ := (MappingTorus.mk_eq_mk_iff g _ _).mp hpq
  apply (MappingTorus.mk_eq_mk_iff f _ _).mpr
  refine ⟨n, ht, hinj ?_⟩
  exact hx.trans (equivariant_zpow f g e he (-n) x).symm

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
