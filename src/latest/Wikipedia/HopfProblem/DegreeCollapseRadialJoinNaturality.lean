import Wikipedia.HopfProblem.DegreeCollapseRadialJoinSuspension
import Mathlib.Topology.Homotopy.Contractible

/-!
# Exact coordinate naturality for radial joins

Linear isometries commute with the canonical radial extension. Thus a
commuting sphere-map square remains commuting after adjoining a summand.
The nullhomotopy comparison below uses actual homeomorphisms and an
actual commuting square, with no homotopy-class substitution.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialJoinNaturality

open RadialSphereMap RadialSphereAction HopfBlockCoordinates

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem extend_naturality (e : E ≃ₗᵢ[ℝ] E') (d : F ≃ₗᵢ[ℝ] F')
    (f : C(UnitSphere E, UnitSphere F)) (g : C(UnitSphere E', UnitSphere F'))
    (h : ∀ x, g (unitSphereCoordinates e x) = unitSphereCoordinates d (f x)) (x : E) :
    extend g (e x) = d (extend f x) := by
  by_cases hx : x = 0
  · subst x
    rw [e.map_zero, extend_zero, extend_zero, d.map_zero]
  · have he : e x ≠ 0 := by
      intro hz
      apply hx
      apply e.injective
      simpa only [e.map_zero] using hz
    have hd : direction (e x) he = unitSphereCoordinates e (direction x hx) := by
      apply Subtype.ext
      change ‖e x‖⁻¹ • e x = e (‖x‖⁻¹ • x)
      rw [e.norm_map, e.map_smul]
    rw [extend_of_ne_zero g (e x) he, extend_of_ne_zero f x hx, e.norm_map, hd, h]
    exact (d.map_smul ‖x‖ (f (direction x hx)).val).symm

variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

theorem sphereMap_naturality (e : E ≃ₗᵢ[ℝ] E') (d : F ≃ₗᵢ[ℝ] F') (a : G ≃ₗᵢ[ℝ] G')
    (f : C(UnitSphere E, UnitSphere F)) (g : C(UnitSphere E', UnitSphere F'))
    (h : ∀ x, g (unitSphereCoordinates e x) = unitSphereCoordinates d (f x))
    (x : UnitSphere (WithLp 2 (E × G))) :
    RadialSphereJoin.sphereMap (G := G') g
      (unitSphereCoordinates (LinearIsometryEquiv.withLpProdCongr 2 e a) x) =
    unitSphereCoordinates (LinearIsometryEquiv.withLpProdCongr 2 d a)
      (RadialSphereJoin.sphereMap (G := G) f x) := by
  apply Subtype.ext
  change WithLp.toLp 2 (extend g (e x.val.fst), a x.val.snd) =
    WithLp.toLp 2 (d (extend f x.val.fst), a x.val.snd)
  rw [extend_naturality e d f g h]

section Nullhomotopy

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

theorem nullhomotopic_iff_of_homeomorph_square (e : X ≃ₜ X') (d : Y ≃ₜ Y')
    (f : C(X, Y)) (g : C(X', Y')) (h : ∀ x, d (f x) = g (e x)) :
    f.Nullhomotopic ↔ g.Nullhomotopic := by
  constructor
  · intro hf
    have hn := (hf.comp_right (d : C(Y, Y'))).comp_left (e.symm : C(X', X))
    have he : ((d : C(Y, Y')).comp f).comp (e.symm : C(X', X)) = g := by
      apply ContinuousMap.ext
      intro x
      change d (f (e.symm x)) = g x
      rw [h, e.apply_symm_apply]
    rwa [he] at hn
  · intro hg
    have hn := (hg.comp_left (e : C(X, X'))).comp_right (d.symm : C(Y', Y))
    have he : (d.symm : C(Y', Y)).comp (g.comp (e : C(X, X'))) = f := by
      apply ContinuousMap.ext
      intro x
      change d.symm (g (e x)) = f x
      rw [← h, d.symm_apply_apply]
    rwa [he] at hn

end Nullhomotopy

end Wikipedia.HopfProblem.DegreeCollapse.RadialJoinNaturality
