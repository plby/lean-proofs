import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalSections

/-!
# The genuine local kernel of the global cochain unit

The native sheafification unit kills an original global cochain exactly
when that cochain restricts to zero near each point. The reverse direction
uses the actual isomorphism on stalks of the native sheafification unit.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

/-- Locally zero original cochains have zero image under the actual unit. -/
theorem globalCochainUnit_eq_zero_of_local (φ : Cochains X A n)
    (hφ : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n φ U = 0) :
    globalCochainUnit X A n φ = 0 := by
  apply TopCat.Presheaf.section_ext (cochainSheaf X A n) ⊤
  intro x hx
  obtain ⟨U, hxU, hU⟩ := hφ x
  calc
    (cochainSheaf X A n).presheaf.germ ⊤ x hx (globalCochainUnit X A n φ) =
      (cochainSheaf X A n).presheaf.germ U x hxU
        ((cochainSheafUnit X A n).app (op U) (restrictGlobalCochain A n φ U)) :=
      globalCochainUnit_germ X A n φ U x hxU
    _ = 0 := by rw [hU, map_zero, map_zero]
    _ = (cochainSheaf X A n).presheaf.germ ⊤ x hx 0 := (map_zero _).symm

/-- Zero under the actual unit implies literal zero restrictions of the
original cochain on genuine open neighborhoods. -/
theorem globalCochainUnit_locally_zero (φ : Cochains X A n)
    (hφ : globalCochainUnit X A n φ = 0) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n φ U = 0 := by
  have hg : (cochainSheaf X A n).presheaf.germ ⊤ x (by trivial)
      ((Sheafification.unit (cochainPresheaf X A n)).app (op ⊤)
        (restrictGlobalCochain A n φ ⊤)) =
    (cochainSheaf X A n).presheaf.germ ⊤ x (by trivial)
      ((Sheafification.unit (cochainPresheaf X A n)).app (op ⊤) 0) := by
    change (cochainSheaf X A n).presheaf.germ ⊤ x (by trivial)
      (globalCochainUnit X A n φ) = _
    rw [hφ, map_zero, map_zero, map_zero]
  obtain ⟨U, hxU, i, j, hij⟩ :=
    Sheafification.exists_restriction_eq_of_germ_unit_eq
      (cochainPresheaf X A n) ⊤ ⊤ x (by trivial) (by trivial)
      (restrictGlobalCochain A n φ ⊤) 0 hg
  exact ⟨U, hxU, (restrictGlobalCochain_restrict A n φ i).symm.trans
    (hij.trans (map_zero _))⟩

/-- The actual sheafification kernel, expressed using original restrictions. -/
theorem globalCochainUnit_eq_zero_iff_local (φ : Cochains X A n) :
    globalCochainUnit X A n φ = 0 ↔
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n φ U = 0 :=
  ⟨globalCochainUnit_locally_zero X A n φ,
    globalCochainUnit_eq_zero_of_local X A n φ⟩

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
