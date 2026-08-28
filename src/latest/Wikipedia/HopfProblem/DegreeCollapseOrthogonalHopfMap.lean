import Wikipedia.HopfProblem.DegreeCollapseRadialSphereAction
import Wikipedia.NoExoticSixSphere.OrthogonalPaths

/-!
# An actual Hopf construction for continuous orthogonal families

On the unit sphere of the Hilbert sum the map is
(a,b) ↦ (‖a‖² - ‖b‖², 2 ‖a‖ A(a/‖a‖) b).
The preceding radial extension treats a = 0 continuously. Parameters are
retained throughout, so an actual homotopy of orthogonal families gives
a homotopy of these sphere maps. The identification with the original
cubical suspension operations is a separate, still open comparison.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

abbrev Source (E : Type*) [NormedAddCommGroup E] (n : ℕ) :=
  UnitSphere (WithLp 2 (E × Vector n))

abbrev Target (n : ℕ) := UnitSphere (WithLp 2 (ℝ × Vector n))

def action (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (a : UnitSphere E) (b : Vector n) : Vector n :=
  (f (p, a)).val.val b

omit [NormedSpace ℝ E] in
theorem action_norm (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (a : UnitSphere E) (b : Vector n) : ‖action f p a b‖ = ‖b‖ :=
  (f (p, a)).property b

omit [NormedSpace ℝ E] in
theorem continuous_action (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    Continuous (fun z : P × (UnitSphere E × Vector n) ↦ action f z.1 z.2.1 z.2.2) := by
  have hc : Continuous (fun z : P × (UnitSphere E × Vector n) ↦ (f (z.1, z.2.1)).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
    (f.continuous.comp (continuous_fst.prodMk continuous_snd.fst)))
  exact hc.clm_apply continuous_snd.snd

def vector (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : WithLp 2 (E × Vector n)) : WithLp 2 (ℝ × Vector n) :=
  WithLp.toLp 2 (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2,
    (2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd)

theorem vector_norm_sq (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : WithLp 2 (E × Vector n)) :
    ‖vector f p x‖ ^ 2 = (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2‖ ^ 2 +
    ‖(2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd‖ ^ 2 = _
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    RadialSphereAction.value_norm (action f) (action_norm f), sq_abs]
  ring

omit [NormedSpace ℝ E] in
theorem source_norms (x : Source E n) : ‖x.val.fst‖ ^ 2 + ‖x.val.snd‖ ^ 2 = 1 := by
  rw [← WithLp.prod_norm_sq_eq_of_L2, mem_sphere_zero_iff_norm.mp x.property, one_pow]

theorem vector_mem_sphere (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Source E n) : vector f p x.val ∈ UnitSphere (WithLp 2 (ℝ × Vector n)) := by
  rw [mem_sphere_zero_iff_norm]
  have h := vector_norm_sq f p x.val
  rw [source_norms x, one_pow] at h
  nlinarith [norm_nonneg (vector f p x.val)]

theorem continuous_vector (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    Continuous (fun z : P × WithLp 2 (E × Vector n) ↦ vector f z.1 z.2) := by
  have ha : Continuous (fun z : P × WithLp 2 (E × Vector n) ↦ z.2.fst) :=
    (WithLp.continuous_fst 2 E (Vector n)).comp continuous_snd
  have hb : Continuous (fun z : P × WithLp 2 (E × Vector n) ↦ z.2.snd) :=
    (WithLp.continuous_snd 2 E (Vector n)).comp continuous_snd
  have hr := (RadialSphereAction.continuous_value (action f) (action_norm f)
    (continuous_action f)).comp (continuous_fst.prodMk (ha.prodMk hb))
  exact (WithLp.prod_continuous_toLp 2 ℝ (Vector n)).comp
    (((ha.norm.pow 2).sub (hb.norm.pow 2)).prodMk
      ((continuous_const : Continuous (fun _ : P × WithLp 2 (E × Vector n) ↦ (2 : ℝ))).smul hr))

def familyMap (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    C(P × Source E n, Target n) :=
  ⟨fun z ↦ ⟨vector f z.1 z.2.val, vector_mem_sphere f z.1 z.2⟩,
    ((continuous_vector f).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

def sphereMap (f : C(UnitSphere E, OrthogonalOperators n)) : C(Source E n, Target n) :=
  (familyMap (f.comp ⟨Prod.snd, continuous_snd⟩)).comp
    ⟨fun x ↦ ((), x), continuous_const.prodMk continuous_id⟩

theorem sphereMap_val (f : C(UnitSphere E, OrthogonalOperators n)) (x : Source E n) :
    (sphereMap f x).val =
      WithLp.toLp 2 (‖x.val.fst‖ ^ 2 - ‖x.val.snd‖ ^ 2,
        (2 : ℝ) • RadialSphereAction.value
          (fun (_ : Unit) a b ↦ (f a).val.val b) () x.val.fst x.val.snd) := rfl

def pole (n : ℕ) : Target n :=
  ⟨WithLp.toLp 2 (1, 0), by
    rw [mem_sphere_zero_iff_norm, WithLp.norm_toLp_fst]
    exact norm_one⟩

theorem sphereMap_pole_fiber (f : C(UnitSphere E, OrthogonalOperators n))
    (x : Source E n) (hx : x.val.snd = 0) : sphereMap f x = pole n := by
  apply Subtype.ext
  rw [sphereMap_val, hx]
  have h := source_norms x
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
    RadialSphereAction.value_zero_right _ (fun _ a b ↦ (f a).property b), smul_zero]
  rfl

def mapHomotopy {f g : C(UnitSphere E, OrthogonalOperators n)} (H : f.Homotopy g) :
    (sphereMap f).Homotopy (sphereMap g) where
  toFun := familyMap H.toContinuousMap
  continuous_toFun := (familyMap H.toContinuousMap).continuous
  map_zero_left x := by
    apply Subtype.ext
    change WithLp.toLp 2 (_, (2 : ℝ) • RadialSphereAction.value _ 0 _ _) = _
    rw [sphereMap_val]
    congr 2
    by_cases ha : x.val.fst = 0
    · rw [ha, RadialSphereAction.value_zero, RadialSphereAction.value_zero]
    · rw [RadialSphereAction.value_of_ne_zero _ _ _ _ ha,
        RadialSphereAction.value_of_ne_zero _ _ _ _ ha]
      congr 1
      exact congrArg (fun T : OrthogonalOperators n ↦ ‖x.val.fst‖ • T.val.val x.val.snd)
        (H.apply_zero _)
  map_one_left x := by
    apply Subtype.ext
    change WithLp.toLp 2 (_, (2 : ℝ) • RadialSphereAction.value _ 1 _ _) = _
    rw [sphereMap_val]
    congr 2
    by_cases ha : x.val.fst = 0
    · rw [ha, RadialSphereAction.value_zero, RadialSphereAction.value_zero]
    · rw [RadialSphereAction.value_of_ne_zero _ _ _ _ ha,
        RadialSphereAction.value_of_ne_zero _ _ _ _ ha]
      congr 1
      exact congrArg (fun T : OrthogonalOperators n ↦ ‖x.val.fst‖ • T.val.val x.val.snd)
        (H.apply_one _)

end Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap
