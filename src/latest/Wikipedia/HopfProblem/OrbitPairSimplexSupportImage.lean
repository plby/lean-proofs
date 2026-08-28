import Wikipedia.HopfProblem.OrbitPairSimplexSupportFace
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Supporting faces under simplicial operators

Factor the composite of a support inclusion and a simplicial operator
through its categorical image. The epimorphism sums the positive
coordinates and the monomorphism is the unique supporting face of the
image point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SimplexSupport

open FirstHurewicz

def imageFace {m n : ℕ} {t : Simplex m} (a : Face m t) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    Face n (stdSimplex.map f.toOrderHom t) where
  dim := (image (a.inclusion ≫ f)).len
  inclusion := image.ι (a.inclusion ≫ f)
  mono_inclusion := inferInstance
  point := stdSimplex.map (factorThruImage (a.inclusion ≫ f)).toOrderHom a.point
  positive := map_positive (factorThruImage (a.inclusion ≫ f)).toOrderHom
    (SimplexCategory.epi_iff_surjective.mp
      (inferInstance : Epi (factorThruImage (a.inclusion ≫ f))))
    a.point a.positive
  map_point := by
    calc
      _ = stdSimplex.map (a.inclusion ≫ f).toOrderHom a.point := by
        have h := stdSimplex.map_comp_apply
          (factorThruImage (a.inclusion ≫ f)).toOrderHom
          (image.ι (a.inclusion ≫ f)).toOrderHom a.point
        change _ = stdSimplex.map
          (factorThruImage (a.inclusion ≫ f) ≫ image.ι (a.inclusion ≫ f)).toOrderHom a.point at h
        rw [image.fac] at h
        exact h
      _ = stdSimplex.map f.toOrderHom (stdSimplex.map a.inclusion.toOrderHom a.point) :=
        (stdSimplex.map_comp_apply a.inclusion.toOrderHom f.toOrderHom a.point).symm
      _ = _ := congrArg (stdSimplex.map f.toOrderHom) a.map_point

theorem imageFace_eq {m n : ℕ} {t : Simplex m} (a : Face m t) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    imageFace a f = face n (stdSimplex.map f.toOrderHom t) := face_eq _ _

end Wikipedia.HopfProblem.OrbitPair.SimplexSupport
