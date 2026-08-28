import Wikipedia.NoExoticSixSphere.ArfFiniteSums

/-!
# Recognizing the anisotropic plane from actual coordinates and values

In dimension two, nondegeneracy forces the off-diagonal polar coefficient
to be one. Thus a quadratic form taking value one on both coordinate
vectors is the anisotropic plane and has Arf invariant one. This uses
proved coordinates and nondegeneracy, not a chosen matrix for the form.
-/

noncomputable section

namespace NoExoticSixSphere.Arf

theorem plane_cross_eq_one (q : QuadraticForm F₂ (F₂ × F₂))
    (hq : q.polarBilin.Nondegenerate) : q.polarBilin (1, 0) (0, 1) = 1 := by
  have hd : q.polarBilin (1, 0) (1, 0) = 0 := by
    change QuadraticMap.polar q (1, 0) (1, 0) = 0
    rw [QuadraticMap.polar_self, two_nsmul]
    exact ZModModule.add_self (q (1, 0))
  have hn : q.polarBilin (1, 0) (0, 1) ≠ 0 := by
    intro hz
    have he : ((1, 0) : F₂ × F₂) = 0 := hq.1 (1, 0) (by
      intro p
      have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
      rw [hp, map_add, map_smul, map_smul, hd, hz, smul_zero, smul_zero, zero_add])
    exact one_ne_zero (congrArg Prod.fst he)
  rcases (show ∀ z : F₂, z = 0 ∨ z = 1 from by decide)
    (q.polarBilin (1, 0) (0, 1)) with h | h
  · exact (hn h).elim
  · exact h

theorem eq_anisotropicPlane_of_values (q : QuadraticForm F₂ (F₂ × F₂))
    (hq : q.polarBilin.Nondegenerate) (h₁ : q (1, 0) = 1) (h₂ : q (0, 1) = 1) :
    q = anisotropicPlane := by
  ext p
  rw [quadratic_plane_formula q (plane_cross_eq_one q hq) p, h₁, h₂]

variable {V W : Type*} [AddCommGroup V] [Module F₂ V] [AddCommGroup W] [Module F₂ W]

theorem polar_comp_nondegenerate (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) (E : W ≃ₗ[F₂] V) :
    (q.comp E.toLinearMap).polarBilin.Nondegenerate := by
  rw [QuadraticMap.polarBilin_comp]
  constructor
  · intro x hx
    apply E.injective
    rw [map_zero]
    apply hq.1 (E x)
    intro y
    obtain ⟨z, rfl⟩ := E.surjective y
    exact hx z
  · intro x hx
    apply E.injective
    rw [map_zero]
    apply hq.2 (E x)
    intro y
    obtain ⟨z, rfl⟩ := E.surjective y
    exact hx z

def anisotropicCoordinatesIsometry (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) (E : V ≃ₗ[F₂] F₂ × F₂)
    (h₁ : q (E.symm (1, 0)) = 1) (h₂ : q (E.symm (0, 1)) = 1) :
    q.IsometryEquiv anisotropicPlane where
  toLinearEquiv := E
  map_app' x := by
    have he := eq_anisotropicPlane_of_values (q.comp E.symm.toLinearMap)
      (polar_comp_nondegenerate q hq E.symm) h₁ h₂
    have h := congrArg (fun Q : QuadraticForm F₂ (F₂ × F₂) ↦ Q (E x)) he
    change q (E.symm (E x)) = anisotropicPlane (E x) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm

theorem invariant_eq_one_of_two_coordinates [Fintype V] (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) (E : V ≃ₗ[F₂] F₂ × F₂)
    (h₁ : q (E.symm (1, 0)) = 1) (h₂ : q (E.symm (0, 1)) = 1) :
    invariant q hq = 1 :=
  (invariant_isometry q anisotropicPlane hq (plane_nondegenerate 1 1)
    (anisotropicCoordinatesIsometry q hq E h₁ h₂)).trans invariant_anisotropicPlane

end NoExoticSixSphere.Arf
