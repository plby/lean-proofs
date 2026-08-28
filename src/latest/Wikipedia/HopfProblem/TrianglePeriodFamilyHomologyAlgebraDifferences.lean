import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

/-!
# The range of the monodromy-difference map

The image of `(b,c) ↦ (P b - b) + (Q c - c)` is exactly the sum of
the two individual difference-map images. The resulting quotient
equivalence is induced by the identity on the ambient integral module.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

variable {H : Type*} [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H)

/-- The two monodromy differences generate exactly the range of `delta`. -/
theorem delta_range_eq_sup :
    LinearMap.range (delta P Q) =
      LinearMap.range (P - LinearMap.id) ⊔ LinearMap.range (Q - LinearMap.id) := by
  ext z
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    rw [delta_apply]
    exact Submodule.add_mem_sup ⟨b, rfl⟩ ⟨c, rfl⟩
  · intro hz
    obtain ⟨a, ⟨b, rfl⟩, d, ⟨c, rfl⟩, h⟩ := Submodule.mem_sup.mp hz
    refine ⟨(b, c), ?_⟩
    change (P b - b) + (Q c - c) = z at h
    exact (delta_apply P Q (b, c)).trans h

/-- The actual quotient by `range delta` is the quotient by the sum of
the two monodromy-difference images, using the identity on representatives. -/
def deltaCokernelSupEquiv :
    (H ⧸ LinearMap.range (delta P Q)) ≃ₗ[ℤ]
      H ⧸ (LinearMap.range (P - LinearMap.id) ⊔ LinearMap.range (Q - LinearMap.id)) := by
  let e : (H ⧸ LinearMap.range (delta P Q)) ≃+
      H ⧸ (LinearMap.range (P - LinearMap.id) ⊔ LinearMap.range (Q - LinearMap.id)) :=
    { toEquiv := @Quotient.congr H H
        (Submodule.quotientRel (LinearMap.range (delta P Q)))
        (Submodule.quotientRel
          (LinearMap.range (P - LinearMap.id) ⊔ LinearMap.range (Q - LinearMap.id)))
        (Equiv.refl H) (fun _ _ => by rw [delta_range_eq_sup P Q]; rfl)
      map_add' := by
        rintro ⟨x⟩ ⟨y⟩
        rfl }
  exact e.toIntLinearEquiv

@[simp] theorem deltaCokernelSupEquiv_mk (x : H) :
    deltaCokernelSupEquiv P Q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

@[simp] theorem deltaCokernelSupEquiv_symm_mk (x : H) :
    (deltaCokernelSupEquiv P Q).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
