import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFamily

/-!
# Hopf construction under actual sphere precomposition

Precomposing the orthogonal family by a sphere map is exactly the same
as precomposing its Hopf construction by the canonical radial join of
that map. The identity is proved on all ambient vectors, including
the zero first component, before restriction to the unit spheres.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfRadialPrecomposition

open RadialSphereMap RadialSphereAction HopfBlockVanishing OrthogonalHopfMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

theorem extend_ne_zero (g : C(UnitSphere E, UnitSphere F)) (a : E) (ha : a ≠ 0) :
    extend g a ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [extend_norm]
  exact norm_ne_zero_iff.mpr ha

theorem direction_extend (g : C(UnitSphere E, UnitSphere F)) (a : E) (ha : a ≠ 0) :
    direction (extend g a) (extend_ne_zero g a ha) = g (direction a ha) := by
  apply Subtype.ext
  change NormedSpace.normalize (extend g a) = (g (direction a ha)).val
  rw [extend_of_ne_zero g a ha, NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr ha)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp (g (direction a ha)).property)

theorem radial_precompose (f : C(UnitSphere F, OrthogonalOperators n))
    (g : C(UnitSphere E, UnitSphere F)) (a : E) (b : Vector n) :
    value (action (parameterize (f.comp g))) () a b =
      value (action (parameterize f)) () (extend g a) b := by
  by_cases ha : a = 0
  · subst a
    rw [value_zero, extend_zero, value_zero]
  · rw [value_of_ne_zero _ _ _ _ ha,
      value_of_ne_zero _ _ _ _ (extend_ne_zero g a ha), extend_norm, direction_extend g a ha]
    rfl

theorem vector_precompose (f : C(UnitSphere F, OrthogonalOperators n))
    (g : C(UnitSphere E, UnitSphere F)) (x : WithLp 2 (E × Vector n)) :
    vector (parameterize (f.comp g)) () x =
      vector (parameterize f) () (RadialSphereJoin.vector g x) := by
  change WithLp.toLp 2 (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2,
    (2 : ℝ) • value (action (parameterize (f.comp g))) () x.fst x.snd) =
      WithLp.toLp 2 (‖extend g x.fst‖ ^ 2 - ‖x.snd‖ ^ 2,
        (2 : ℝ) • value (action (parameterize f)) () (extend g x.fst) x.snd)
  rw [extend_norm, radial_precompose]

theorem sphereMap_precompose (f : C(UnitSphere F, OrthogonalOperators n))
    (g : C(UnitSphere E, UnitSphere F)) (x : Source E n) :
    OrthogonalHopfMap.sphereMap (f.comp g) x =
      OrthogonalHopfMap.sphereMap f (RadialSphereJoin.sphereMap (G := Vector n) g x) :=
  Subtype.ext (vector_precompose f g x.val)

end Wikipedia.HopfProblem.DegreeCollapse.HopfRadialPrecomposition
