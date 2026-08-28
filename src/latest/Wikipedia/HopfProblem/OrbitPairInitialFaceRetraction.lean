import Wikipedia.HopfProblem.OrbitPairDualSubdivisionRegularity

/-!
# The retraction onto a generated zeroth face

The standard codegeneracy retracts a simplex onto its zeroth face.
The regularity pushout extends this to a native simplicial retraction of
the generated subcomplex. Realization preserves the retraction equations.
A relative homotopy is still required to obtain a deformation retraction.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.InitialFace

theorem delta_sigma_zero (n : ℕ) :
    SSet.stdSimplex.{u}.δ (0 : Fin (n + 2)) ≫ SSet.stdSimplex.σ (0 : Fin (n + 1)) = 𝟙 _ := by
  have h : SimplexCategory.δ (0 : Fin (n + 2)) ≫ SimplexCategory.σ (0 : Fin (n + 1)) = 𝟙 _ :=
    SimplexCategory.δ_comp_σ_self
  exact (SSet.stdSimplex.map_comp (SimplexCategory.δ 0) (SimplexCategory.σ 0)).symm.trans
    ((congrArg SSet.stdSimplex.map h).trans (SSet.stdSimplex.map_id ⦋n⦌))

variable {X : SSet.{u}} {n : ℕ} (z : X _⦋n + 1⦌)

theorem collapse_compatible : SSet.Subcomplex.toOfSimplex (X.δ 0 z) ≫ 𝟙 _ =
    SSet.stdSimplex.δ 0 ≫ (SSet.stdSimplex.σ 0 ≫ SSet.Subcomplex.toOfSimplex (X.δ 0 z)) := by
  rw [← Category.assoc, delta_sigma_zero, Category.id_comp, Category.comp_id]

variable (hz : InitialInjective z)

def retraction : (SSet.Subcomplex.ofSimplex z : SSet) ⟶
    (SSet.Subcomplex.ofSimplex (X.δ 0 z) : SSet) :=
  (pushout z hz).desc (𝟙 _) (SSet.stdSimplex.σ 0 ≫ SSet.Subcomplex.toOfSimplex (X.δ 0 z))
    (collapse_compatible z)

theorem inclusion_retraction : inclusion z ≫ retraction z hz = 𝟙 _ :=
  (pushout z hz).inl_desc _ _ _

theorem characteristic_retraction : SSet.Subcomplex.toOfSimplex z ≫ retraction z hz =
    SSet.stdSimplex.σ 0 ≫ SSet.Subcomplex.toOfSimplex (X.δ 0 z) :=
  (pushout z hz).inr_desc _ _ _

theorem realized_inclusion_retraction :
    SSet.toTop.map (inclusion z) ≫ SSet.toTop.map (retraction z hz) = 𝟙 _ := by
  rw [← SSet.toTop.map_comp, inclusion_retraction, SSet.toTop.map_id]

theorem realized_characteristic_retraction :
    SSet.toTop.map (SSet.Subcomplex.toOfSimplex z) ≫ SSet.toTop.map (retraction z hz) =
      SSet.toTop.map (SSet.stdSimplex.σ 0) ≫
        SSet.toTop.map (SSet.Subcomplex.toOfSimplex (X.δ 0 z)) := by
  rw [← SSet.toTop.map_comp, characteristic_retraction, SSet.toTop.map_comp]

end Wikipedia.HopfProblem.OrbitPair.InitialFace
