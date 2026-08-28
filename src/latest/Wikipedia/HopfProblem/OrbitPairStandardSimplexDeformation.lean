import Wikipedia.HopfProblem.OrbitPairPushoutHomotopy
import Wikipedia.HopfProblem.OrbitPairSubdivisionGeometry

/-!
# Relative deformation of the actual realized standard simplex

The checked coordinate homeomorphism permits convex interpolation between
maps into a native realized standard simplex. Equal endpoint values stay
fixed. Applied to the identity and the realized codegeneracy followed by
the zeroth-face inclusion, this gives a homotopy relative to that face.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.InitialFace

open FirstHurewicz SecondHurewicz.SimplyConnected Subdivision

def standardBlend (n : ℕ) {Y : Type v} [TopologicalSpace Y]
    (f g : C(Y, SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n⦌))) : f.Homotopy g where
  toFun p := (standardCoordinates n).symm
    (tetrahedronSimplexBlend p.1 (standardCoordinates n (f p.2)) (standardCoordinates n (g p.2)))
  continuous_toFun := (standardCoordinates n).symm.continuous.comp
    ((tetrahedronSimplexBlendMap
      (ContinuousMap.fst : C(Simplex n × Simplex n, Simplex n)) ContinuousMap.snd).continuous.comp
        (continuous_fst.prodMk
          (((standardCoordinates n).continuous.comp (f.continuous.comp continuous_snd)).prodMk
            ((standardCoordinates n).continuous.comp (g.continuous.comp continuous_snd)))))
  map_zero_left y := by
    change (standardCoordinates n).symm
      (tetrahedronSimplexBlend 0 (standardCoordinates n (f y)) (standardCoordinates n (g y))) = f y
    rw [tetrahedronSimplexBlend_zero, Homeomorph.symm_apply_apply]
  map_one_left y := by
    change (standardCoordinates n).symm
      (tetrahedronSimplexBlend 1 (standardCoordinates n (f y)) (standardCoordinates n (g y))) = g y
    rw [tetrahedronSimplexBlend_one, Homeomorph.symm_apply_apply]

theorem standardBlend_fixed (n : ℕ) {Y : Type v} [TopologicalSpace Y]
    (f g : C(Y, SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n⦌)))
    (t : I) (y : Y) (hy : f y = g y) : standardBlend n f g (t, y) = f y := by
  change (standardCoordinates n).symm
    (tetrahedronSimplexBlend t (standardCoordinates n (f y)) (standardCoordinates n (g y))) = f y
  rw [← hy, tetrahedronSimplexBlend_self, Homeomorph.symm_apply_apply]

def standardCollapse (n : ℕ) : SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n + 1⦌) ⟶
    SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n + 1⦌) :=
  SSet.toTop.map (SSet.stdSimplex.σ (0 : Fin (n + 1)) ≫ SSet.stdSimplex.δ 0)

theorem standardCollapse_face (n : ℕ) :
    SSet.toTop.map (SSet.stdSimplex.{u}.δ (0 : Fin (n + 2))) ≫ standardCollapse n =
      SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin (n + 2))) := by
  unfold standardCollapse
  rw [← SSet.toTop.map_comp, ← Category.assoc, delta_sigma_zero, Category.id_comp]

def standardCollapseHomotopy (n : ℕ) :
    (ContinuousMap.id (SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n + 1⦌))).HomotopyRel
      (standardCollapse n).hom
      (Set.range (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin (n + 2))))) where
  toHomotopy := standardBlend (n + 1) (ContinuousMap.id _) (standardCollapse n).hom
  prop' t y hy := by
    obtain ⟨a, rfl⟩ := hy
    apply standardBlend_fixed
    exact (congrArg (fun f ↦ f a) (standardCollapse_face n)).symm

end Wikipedia.HopfProblem.OrbitPair.InitialFace
