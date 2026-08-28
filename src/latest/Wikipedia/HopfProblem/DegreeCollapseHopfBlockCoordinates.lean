import Wikipedia.HopfProblem.DegreeCollapseHopfBlockHomotopy
import Wikipedia.NoExoticSixSphere.ColumnFiber

/-!
# The Hopf block formula is the actual enlarged orthogonal-family map

Conjugate the original operator plus an identity block by a supplied
linear isometry to the literal Euclidean operator space. The exact
radial identity and the resulting sphere-map square retain this
coordinate change; no arbitrary homotopy-class identification is used.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfBlockCoordinates

open OrthogonalHopfMap HopfBlockGeometry OrthogonalPaths

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n q : ℕ}

def blockOperator (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (T : OrthogonalOperators n) : OrthogonalOperators q :=
  ofEquiv ((e.symm.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (toEquiv T) (LinearIsometryEquiv.refl ℝ G))).trans e)

theorem blockOperator_apply (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (T : OrthogonalOperators n) (w : Vector q) :
    (blockOperator e T).val.val w =
      e (WithLp.toLp 2 (T.val.val (e.symm w).fst, (e.symm w).snd)) := rfl

def blockOperatorMap (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q) :
    C(OrthogonalOperators n, OrthogonalOperators q) :=
  ⟨blockOperator e, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_clm_apply.mpr
    intro w
    have hT : Continuous (fun T : OrthogonalOperators n ↦ T.val.val (e.symm w).fst) :=
      (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const
    have hc : Continuous (fun T : OrthogonalOperators n ↦
        e (WithLp.toLp 2 (T.val.val (e.symm w).fst, (e.symm w).snd))) :=
      e.continuous.comp ((WithLp.prod_continuous_toLp 2 (Vector n) G).comp
        (hT.prodMk continuous_const))
    exact hc⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordinates (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q) :
    Triple E (Vector n) G ≃ₗᵢ[ℝ] WithLp 2 (E × Vector q) :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E) e

theorem coordinates_apply (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (x : Triple E (Vector n) G) : coordinates e x = WithLp.toLp 2 (x.fst, e x.snd) := rfl

def unitSphereCoordinates {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (e : U ≃ₗᵢ[ℝ] V) :
    UnitSphere U ≃ₜ UnitSphere V where
  toFun x := ⟨e x.val, by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.property⟩
  invFun y := ⟨e.symm y.val, by
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

variable {P : Type*} [TopologicalSpace P]

theorem radial_coordinates (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(P × UnitSphere E, OrthogonalOperators n)) (p : P) (a : E)
    (y : WithLp 2 (Vector n × G)) :
    RadialSphereAction.value (action ((blockOperatorMap e).comp f)) p a (e y) =
      e (WithLp.toLp 2 (RadialSphereAction.value (action f) p a y.fst, ‖a‖ • y.snd)) := by
  by_cases ha : a = 0
  · subst a
    rw [RadialSphereAction.value_zero, RadialSphereAction.value_zero, norm_zero, zero_smul]
    exact e.map_zero.symm
  · rw [RadialSphereAction.value_of_ne_zero _ _ _ _ ha,
      RadialSphereAction.value_of_ne_zero _ _ _ _ ha]
    change ‖a‖ • (blockOperator e (f (p, RadialSphereAction.direction a ha))).val.val (e y) = _
    rw [blockOperator_apply, e.symm_apply_apply, ← e.map_smul]
    rfl

theorem vector_coordinates (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(P × UnitSphere E, OrthogonalOperators n)) (p : P)
    (x : Triple E (Vector n) G) :
    vector ((blockOperatorMap e).comp f) p (coordinates e x) =
      coordinates (E := ℝ) e (blockVector f p x) := by
  rw [coordinates_apply, vector]
  change WithLp.toLp 2 (‖x.fst‖ ^ 2 - ‖e x.snd‖ ^ 2,
    (2 : ℝ) • RadialSphereAction.value (action ((blockOperatorMap e).comp f)) p x.fst (e x.snd)) =
      WithLp.toLp 2 (‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2 - ‖x.snd.snd‖ ^ 2,
        e (WithLp.toLp 2 ((2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst,
          (2 * ‖x.fst‖) • x.snd.snd)))
  rw [e.norm_map, WithLp.prod_norm_sq_eq_of_L2, radial_coordinates, ← e.map_smul]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · ring
  · apply congrArg e
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · exact smul_smul (2 : ℝ) ‖x.fst‖ x.snd.snd

theorem familyMap_coordinates (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(P × UnitSphere E, OrthogonalOperators n)) (p : P)
    (x : UnitSphere (Triple E (Vector n) G)) :
    familyMap ((blockOperatorMap e).comp f) (p, unitSphereCoordinates (coordinates e) x) =
      unitSphereCoordinates (coordinates (E := ℝ) e) (blockMap f (p, x)) :=
  Subtype.ext (vector_coordinates e f p x.val)

end Wikipedia.HopfProblem.DegreeCollapse.HopfBlockCoordinates
