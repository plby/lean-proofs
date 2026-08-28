import Wikipedia.HopfProblem.DegreeCollapseRadialJoinIteration
import Wikipedia.HopfProblem.DegreeCollapseHopfBlockVanishing

/-!
# The Hopf radial formula is the canonical radial join

The ambient Hopf vector is positively homogeneous of degree two.
Dividing by the source radius gives the unique degree-one radial
extension of its actual sphere map. This identifies the previously
contracted block formula with the canonical join, through the actual
associativity isometries.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialHopfIdentification

open OrthogonalHopfMap HopfBlockGeometry HopfBlockCoordinates HopfBlockVanishing
open RadialSphereAction RadialSphereMap RadialJoinNaturality

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem radial_smul_left (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (c : ℝ) (hc : 0 ≤ c) (a : E) (b : Vector n) :
    value (action f) p (c • a) b = c • value (action f) p a b := by
  by_cases hc0 : c = 0
  · subst c
    rw [zero_smul, value_zero, zero_smul]
  by_cases ha : a = 0
  · subst a
    rw [smul_zero, value_zero, smul_zero]
  have hca : c • a ≠ 0 := smul_ne_zero hc0 ha
  have hd : direction (c • a) hca = direction a ha :=
    Subtype.ext (NormedSpace.normalize_smul_of_pos (lt_of_le_of_ne hc (Ne.symm hc0)) a)
  rw [value_of_ne_zero _ _ _ _ hca, value_of_ne_zero _ _ _ _ ha, hd, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hc, smul_smul]

theorem radial_smul_right (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (a : E) (c : ℝ) (b : Vector n) :
    value (action f) p a (c • b) = c • value (action f) p a b := by
  by_cases ha : a = 0
  · subst a
    rw [value_zero, value_zero, smul_zero]
  · rw [value_of_ne_zero _ _ _ _ ha, value_of_ne_zero _ _ _ _ ha]
    change ‖a‖ • (f (p, direction a ha)).val.val (c • b) =
      c • (‖a‖ • (f (p, direction a ha)).val.val b)
    rw [map_smul]
    exact smul_comm _ _ _

theorem vector_smul_nonneg (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (c : ℝ) (hc : 0 ≤ c) (x : WithLp 2 (E × Vector n)) :
    vector f p (c • x) = c ^ 2 • vector f p x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change ‖c • x.fst‖ ^ 2 - ‖c • x.snd‖ ^ 2 =
      c ^ 2 * (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  · change (2 : ℝ) • value (action f) p (c • x.fst) (c • x.snd) =
      c ^ 2 • ((2 : ℝ) • value (action f) p x.fst x.snd)
    rw [radial_smul_left f p c hc, radial_smul_right]
    simp only [smul_smul]
    apply congrArg (fun r : ℝ ↦ r • value (action f) p x.fst x.snd)
    ring

theorem suspendedHead_smul_nonneg (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (c : ℝ) (hc : 0 ≤ c) (x : WithLp 2 (E × Vector n)) :
    suspendedHead f p (c • x) = c • suspendedHead f p x := by
  by_cases hc0 : c = 0
  · subst c
    rw [zero_smul, suspendedHead_zero, zero_smul]
  have hcoef : (c * ‖x‖)⁻¹ * c ^ 2 = c * ‖x‖⁻¹ := by
    by_cases hx : ‖x‖ = 0
    · rw [hx, mul_zero, inv_zero, zero_mul, mul_zero]
    · field_simp
  simp only [suspendedHead, vector_smul_nonneg f p c hc, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, smul_smul, hcoef]

theorem extend_hopfMap (f : C(UnitSphere E, OrthogonalOperators n))
    (x : WithLp 2 (E × Vector n)) :
    extend (OrthogonalHopfMap.sphereMap f) x = suspendedHead (parameterize f) () x := by
  apply extend_unique (OrthogonalHopfMap.sphereMap f)
    (fun y ↦ suspendedHead (parameterize f) () y) (suspendedHead_zero _ _)
    (fun c hc y ↦ suspendedHead_smul_nonneg _ _ c hc y)
  intro z
  change suspendedHead (parameterize f) () z.val = vector (parameterize f) () z.val
  rw [suspendedHead, mem_sphere_zero_iff_norm.mp z.property, inv_one, one_smul]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem join_hopf_coordinates (f : C(UnitSphere E, OrthogonalOperators n))
    (x : UnitSphere (WithLp 2 (WithLp 2 (E × Vector n) × G))) :
    unitSphereCoordinates (LinearIsometryEquiv.withLpProdAssoc 2 ℝ ℝ (Vector n) G)
      (RadialSphereJoin.sphereMap (G := G) (OrthogonalHopfMap.sphereMap f) x) =
    suspendedSphereMap (G := G) f
      (unitSphereCoordinates (LinearIsometryEquiv.withLpProdAssoc 2 ℝ E (Vector n) G) x) := by
  apply Subtype.ext
  change WithLp.toLp 2 ((extend (OrthogonalHopfMap.sphereMap f) x.val.fst).fst,
    WithLp.toLp 2 ((extend (OrthogonalHopfMap.sphereMap f) x.val.fst).snd, x.val.snd)) =
      WithLp.toLp 2 ((suspendedHead (parameterize f) () x.val.fst).fst,
        WithLp.toLp 2 ((suspendedHead (parameterize f) () x.val.fst).snd, x.val.snd))
  rw [extend_hopfMap]

theorem hopf_join_twelve_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 4)) :
    (RadialSphereJoin.sphereMap (G := Vector 12) (OrthogonalHopfMap.sphereMap f)).Nullhomotopic :=
  (nullhomotopic_iff_of_homeomorph_square
    (unitSphereCoordinates
      (LinearIsometryEquiv.withLpProdAssoc 2 ℝ (Vector 5) (Vector 4) (Vector 12)))
    (unitSphereCoordinates (LinearIsometryEquiv.withLpProdAssoc 2 ℝ ℝ (Vector 4) (Vector 12)))
    (RadialSphereJoin.sphereMap (OrthogonalHopfMap.sphereMap f)) (suspendedSphereMap f)
    (join_hopf_coordinates f)).mpr (four_twelve_radial_suspension_nullhomotopic f)

end Wikipedia.HopfProblem.DegreeCollapse.RadialHopfIdentification
