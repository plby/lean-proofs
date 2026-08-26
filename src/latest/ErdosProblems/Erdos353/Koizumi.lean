/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 353.
Informal authors: Junnosuke Koizumi.
Formal authors: Aristotle, JoshuaB.
Original Lean/Mathlib version: 4.28.0.
Source: https://www.erdosproblems.com/forum/thread/353#post-7085
Exact editor URL: data/urls.yaml, JoshuaB_353_koizumi.
-/
import ErdosProblems.Erdos353.KoizumiGeometry

open RealInnerProductSpace MeasureTheory
open scoped BigOperators Real Nat Pointwise

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false
/-!
# Isosceles trapezoids of unit area with vertices in sets of infinite planar measure
This file formalizes Theorems 1 and 2 of J. Koizumi, *Isosceles trapezoids of unit area with
vertices in sets of infinite planar measure*.
The plane is modelled as `EuclideanSpace ℝ (Fin 2)`, so that `dist` is the Euclidean distance
and `volume` is the two–dimensional Lebesgue measure.
-/
namespace Erdos353

namespace Koizumi
/-- Rotation of a planar vector `v` by angle `a` (counter-clockwise). -/
noncomputable def rot (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1]
@[simp] lemma rot_apply0 (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (rot a v) 0 = Real.cos a * v 0 - Real.sin a * v 1 := by simp [rot]
@[simp] lemma rot_apply1 (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (rot a v) 1 = Real.sin a * v 0 + Real.cos a * v 1 := by simp [rot]
/-- The radius-dependent rotation (twist) about a center `O` by angle `ang ‖p - O‖`. -/
noncomputable def twistAt (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  O + rot (ang ‖p - O‖) (p - O)
/-- The midpoint map `g(p) = (p + twist p)/2` about center `O` with angle `ang ‖p - O‖`. -/
noncomputable def avgAt (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  O + (1 / 2 : ℝ) • ((p - O) + rot (ang ‖p - O‖) (p - O))
/-- Trapezoid angle function `ψ_R(t) = arcsin((R²/(R²-1))·(2/t²))`. -/
noncomputable def psi (R : ℝ) : ℝ → ℝ := fun t => Real.arcsin (R ^ 2 / (R ^ 2 - 1) * (2 / t ^ 2))
/-- Rotation preserves the norm. -/
lemma norm_rot (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ‖rot a v‖ = ‖v‖ := by
  classical
  rw [ EuclideanSpace.norm_eq, EuclideanSpace.norm_eq ];
  simp +zetaDelta at *;
  exact congrArg Real.sqrt ( by nlinarith [ Real.sin_sq_add_cos_sq a ] )
lemma norm_rot_sub_sq (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖rot a v - v‖ ^ 2 = 2 * (1 - Real.cos a) * ‖v‖ ^ 2 := by
  classical
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, PiLp.sub_apply,
    rot_apply0, rot_apply1]
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.sin_sq_add_cos_sq a

/-- **Geometry of the twist.**  With the angle function `φ(t) = arcsin(2/t²)`, for any point `p` with
`‖p - O‖ > √2` the three points `O`, `p`, `twistAt O φ p` form an isosceles triangle of area `1`. -/
lemma twistAt_isosceles (O p : EuclideanSpace ℝ (Fin 2))
    (hp : Real.sqrt 2 < ‖p - O‖) :
    IsoscelesTriangleArea1 O p (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) := by
  classical
  constructor;
  · unfold area2; unfold twistAt; norm_num [ EuclideanSpace.norm_eq ] at *;
    rw [ Real.sq_sqrt <| by positivity, Real.sin_arcsin, Real.cos_arcsin ];
    · grind;
    · rw [ le_div_iff₀ ] <;> linarith;
    · rw [ div_le_iff₀ ] <;> linarith;
  · unfold twistAt; norm_num [ dist_eq_norm' ] ;
    exact Or.inl ( by rw [ norm_rot ] )
/-
The fiberwise rotation `w ↦ rot (ang ‖w‖) w` is injective.
-/
lemma rotTwist_inj (ang : ℝ → ℝ) :
    Function.Injective (fun w : EuclideanSpace ℝ (Fin 2) => rot (ang ‖w‖) w) := by
  classical
  intro w w' h_eq
  have h_norm : ‖w‖ = ‖w'‖ := by
    simpa [ norm_rot ] using congr_arg Norm.norm h_eq
  have h_angle : ang ‖w‖ = ang ‖w'‖ := by
    rw [ h_norm ]
  have h_rot_eq : rot (ang ‖w‖) w = rot (ang ‖w‖) w' := by
    aesop
  have h_w_eq_w' : w = w' := by
    simp +decide [ rot, ← List.ofFn_inj ] at h_rot_eq ⊢;
    ext i; fin_cases i <;> simp_all +decide ;
    · cases le_or_gt 0 ( Real.cos ( ang ‖w'‖ ) ) <;> cases le_or_gt 0 ( Real.sin ( ang ‖w'‖ ) ) <;> nlinarith [ Real.sin_sq_add_cos_sq ( ang ‖w'‖ ) ];
    · cases le_or_gt 0 ( Real.cos ( ang ‖w'‖ ) ) <;> cases le_or_gt 0 ( Real.sin ( ang ‖w'‖ ) ) <;> nlinarith [ Real.sin_sq_add_cos_sq ( ang ‖w'‖ ) ]
  exact h_w_eq_w'
/-- A directional derivative equals the Fréchet derivative applied to the direction. -/
lemma fderiv_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (w v : E) (h : DifferentiableAt ℝ f w) :
    (fderiv ℝ f w) v = deriv (fun t : ℝ => f (w + t • v)) 0 := by
  classical
  have hline : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v |>.const_add w
  have hf : HasFDerivAt f (fderiv ℝ f w) ((fun t : ℝ => w + t • v) 0) := by
    simpa using h.hasFDerivAt
  have hc := hf.comp_hasDerivAt (0:ℝ) hline
  have : HasDerivAt (fun t : ℝ => f (w + t • v)) ((fderiv ℝ f w) v) 0 := hc
  rw [this.deriv]
/-
The fiberwise rotation `w ↦ rot (ang ‖w‖) w` is differentiable at `w ≠ 0`, provided `ang` is
differentiable at `‖w‖`.
-/
lemma twist_differentiableAt (ang : ℝ → ℝ) {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0)
    (hang : DifferentiableAt ℝ ang ‖w‖) :
    DifferentiableAt ℝ (fun w : EuclideanSpace ℝ (Fin 2) => rot (ang ‖w‖) w) w := by
  classical
  -- Apply the differentiability of the norm and the composition rule.
  have h_norm_diff : DifferentiableAt ℝ (fun w => ‖w‖) w := by
    exact differentiableAt_id.norm ℝ hw;
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun w => ( Real.cos ( ang ‖w‖ ) * w 0 - Real.sin ( ang ‖w‖ ) * w 1 ) • EuclideanSpace.single 0 1 + ( Real.sin ( ang ‖w‖ ) * w 0 + Real.cos ( ang ‖w‖ ) * w 1 ) • EuclideanSpace.single 1 1;
  · fun_prop;
  · filter_upwards [ ] with w using by ext i; fin_cases i <;> simp +decide ;
/-- Derivative of `t ↦ ‖x + t • v‖` at `0` for `x ≠ 0`. -/
lemma norm_line_hasDerivAt {x v : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖x + t • v‖) (inner ℝ x v / ‖x‖) 0 := by
  classical
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2) (2 * inner ℝ x v) 0 := by
    have heq : (fun t : ℝ => ‖x + t • v‖ ^ 2)
        = (fun t : ℝ => ‖x‖^2 + 2 * inner ℝ x v * t + ‖v‖^2 * t^2) := by
      funext t
      rw [norm_add_sq_real, norm_smul]
      simp [inner_smul_right, mul_pow]
      ring
    rw [heq]
    have := ((hasDerivAt_const (0:ℝ) (‖x‖^2)).add
      ((hasDerivAt_id (0:ℝ)).const_mul (2 * inner ℝ x v))).add
      ((hasDerivAt_pow 2 (0:ℝ)).const_mul (‖v‖^2))
    convert this using 1 <;> try rfl
    norm_num
  have hne : ‖x + (0:ℝ) • v‖ ^ 2 ≠ 0 := by
    simp only [zero_smul, add_zero]; exact pow_ne_zero 2 (ne_of_gt hxpos)
  have hsqrt := h2.sqrt hne
  have heq : (fun t : ℝ => Real.sqrt (‖x + t • v‖ ^ 2)) = (fun t : ℝ => ‖x + t • v‖) := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [heq] at hsqrt
  convert hsqrt using 1
  simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg x)]
  field_simp
/-
Directional (line) derivative of the fiberwise rotation at `x ≠ 0`, provided `ang` is
differentiable at `‖x‖`.
-/
lemma twist_line_hasDerivAt (ang : ℝ → ℝ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (hang : DifferentiableAt ℝ ang ‖x‖)
    (v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => rot (ang ‖x + t • v‖) (x + t • v))
      (!₂[ Real.cos (ang ‖x‖) * v 0 - Real.sin (ang ‖x‖) * v 1
            - (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.sin (ang ‖x‖) * x 0 + Real.cos (ang ‖x‖) * x 1),
          Real.sin (ang ‖x‖) * v 0 + Real.cos (ang ‖x‖) * v 1
            + (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.cos (ang ‖x‖) * x 0 - Real.sin (ang ‖x‖) * x 1)]) 0 := by
  classical
  have h_deriv : HasDerivAt (fun t : ℝ => ang ‖x + t • v‖) (deriv ang ‖x‖ * (⟪x, v⟫ / ‖x‖)) 0 := by
    have hang' : HasDerivAt ang (deriv ang ‖x‖) ‖x + (0 : ℝ) • v‖ := by
      simpa only [zero_smul, add_zero] using hang.hasDerivAt
    exact hang'.comp 0 (norm_line_hasDerivAt (v := v) hx)
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  use fun t => ( Real.cos ( ang ‖x + t • v‖ ) * ( x 0 + t * v 0 ) - Real.sin ( ang ‖x + t • v‖ ) * ( x 1 + t * v 1 ) ) • EuclideanSpace.single 0 1 + ( Real.sin ( ang ‖x + t • v‖ ) * ( x 0 + t * v 0 ) + Real.cos ( ang ‖x + t • v‖ ) * ( x 1 + t * v 1 ) ) • EuclideanSpace.single 1 1;
  · convert HasDerivAt.add ( HasDerivAt.smul ( HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.cos h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ( HasDerivAt.mul ( HasDerivAt.sin h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.smul ( HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.sin h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ( HasDerivAt.mul ( HasDerivAt.cos h_deriv ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_mul_const _ ) ) ) ) ( hasDerivAt_const _ _ ) ) using 1;
    congr! 1;
    · ext i; fin_cases i <;> norm_num <;> ring;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · infer_instance;
  · filter_upwards [ ] with t ; ext i ; fin_cases i <;> simp +decide [ rot ]
/-- Determinant of a continuous linear endomorphism of the plane via its action on the unit axes. -/
lemma det_two (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    L.det = (L (EuclideanSpace.single 0 1)) 0 * (L (EuclideanSpace.single 1 1)) 1
          - (L (EuclideanSpace.single 0 1)) 1 * (L (EuclideanSpace.single 1 1)) 0 := by
  classical
  rw [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis L.toLinearMap]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr]
  ring
/-
**Measure preservation of the twist.**  The twist about `O` preserves Lebesgue measure of any
measurable set `T` avoiding `O`, provided the angle function is differentiable at each radius
`‖x - O‖` for `x ∈ T` (where the Jacobian determinant is `1`).
-/
lemma twistAt_volume (O : EuclideanSpace ℝ (Fin 2)) (ang : ℝ → ℝ)
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : MeasurableSet T) (hO : O ∉ closure T)
    (hang : ∀ x ∈ T, DifferentiableAt ℝ ang ‖x - O‖) :
    volume (twistAt O ang '' T) = volume T := by
  classical
  -- Set T' := T - {O} (i.e. {x - O : x ∈ T}), which is measurable.
  set T' : Set (EuclideanSpace ℝ (Fin 2)) := T - {O} with hT';
  -- For every y ∈ T', y = x - O for some x ∈ T, hence y ≠ 0 (as O ∉ closure T ⊇ T) and DifferentiableAt ℝ ang ‖y‖ (since ‖y‖ = ‖x - O‖ and hang x).
  have hT'_meas : MeasurableSet T' := by
    convert hT.preimage ( show Measurable ( fun x => x + O ) from measurable_id.add_const O ) using 1 ; aesop
  have hT'_nonzero : ∀ y ∈ T', y ≠ 0 := by
    simp_all +decide [ sub_eq_zero, mem_closure_iff ];
    exact fun x hx hx' => hO.choose_spec.2.2 ⟨ x, hO.choose_spec.2.1 |> fun h => by aesop ⟩
  have hT'_diff : ∀ y ∈ T', DifferentiableAt ℝ (fun w => rot (ang ‖w‖) w) y := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ : ∃ x ∈ T, y = x - O := by
      rw [ Set.mem_sub ] at hy ; aesop;
    convert twist_differentiableAt ang ( hT'_nonzero _ hy ) ( hang _ hxT ) using 1
  have hT'_det : ∀ y ∈ T', (fderiv ℝ (fun w => rot (ang ‖w‖) w) y).det = 1 := by
    intro y hy
    have h_det : (fderiv ℝ (fun w => rot (ang ‖w‖) w) y) (EuclideanSpace.single 0 1) = !₂[Real.cos (ang ‖y‖) - (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 0 1) / ‖y‖) * (Real.sin (ang ‖y‖) * y 0 + Real.cos (ang ‖y‖) * y 1), Real.sin (ang ‖y‖) + (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 0 1) / ‖y‖) * (Real.cos (ang ‖y‖) * y 0 - Real.sin (ang ‖y‖) * y 1)] := by
      convert HasDerivAt.deriv ( twist_line_hasDerivAt ang ( hT'_nonzero y hy ) ( show DifferentiableAt ℝ ang ‖y‖ from ?_ ) ( EuclideanSpace.single 0 1 ) ) using 1;
      · convert fderiv_dir _ _ _ ( hT'_diff y hy ) using 1;
      · ext i; fin_cases i <;> norm_num;
      · rw [ Set.mem_sub ] at hy ; aesop;
    have h_det' : (fderiv ℝ (fun w => rot (ang ‖w‖) w) y) (EuclideanSpace.single 1 1) = !₂[-Real.sin (ang ‖y‖) - (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 1 1) / ‖y‖) * (Real.sin (ang ‖y‖) * y 0 + Real.cos (ang ‖y‖) * y 1), Real.cos (ang ‖y‖) + (deriv ang ‖y‖) * (inner ℝ y (EuclideanSpace.single 1 1) / ‖y‖) * (Real.cos (ang ‖y‖) * y 0 - Real.sin (ang ‖y‖) * y 1)] := by
      convert HasDerivAt.deriv ( twist_line_hasDerivAt ang ( hT'_nonzero y hy ) ( show DifferentiableAt ℝ ang ‖y‖ from ?_ ) ( EuclideanSpace.single 1 1 ) ) using 1;
      · rw [ fderiv_dir ];
        exact hT'_diff y hy;
      · ext i; fin_cases i <;> norm_num;
      · rw [ Set.mem_sub ] at hy ; aesop;
    convert det_two _ using 1;
    simp_all +decide [ EuclideanSpace.norm_eq ];
    norm_num [ EuclideanSpace.inner_single_right ] ; ring;
    rw [ Real.cos_sq_add_sin_sq ];
  -- Apply lintegral_abs_det_fderiv_eq_addHaar_image to h := (fun w => rot (ang ‖w‖) w) on T'.
  have h_volume_eq : volume ((fun w => rot (ang ‖w‖) w) '' T') = volume T' := by
    have h_volume_eq : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ (fun w => rot (ang ‖w‖) w) y).det| = volume T' := by
      rw [ MeasureTheory.lintegral_congr_ae ];
      rw [ MeasureTheory.lintegral_one ];
      · norm_num;
      · filter_upwards [ MeasureTheory.ae_restrict_mem hT'_meas ] with y hy using by rw [ hT'_det y hy ] ; norm_num;
    rw [ ← h_volume_eq, lintegral_abs_det_fderiv_eq_addHaar_image ];
    · exact hT'_meas;
    · exact fun x hx => DifferentiableAt.hasFDerivAt ( hT'_diff x hx ) |> HasFDerivAt.hasFDerivWithinAt;
    · exact fun x hx y hy hxy => rotTwist_inj _ hxy;
  convert h_volume_eq using 1;
  · rw [ show twistAt O ang '' T = ( fun w => O + w ) '' ( ( fun w => rot ( ang ‖w‖ ) w ) '' ( T - { O } ) ) from ?_ ];
    · simp +zetaDelta at *;
    · ext; simp [twistAt];
      grind +qlia;
  · simp +decide [ T', sub_eq_add_neg ]
/-- Volume of the half-radius ball is a quarter of the full ball (in the plane). -/
lemma volume_ball_half (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (Metric.ball A (ε / 2)) * 4 = volume (Metric.ball A ε) := by
  classical
  convert congr_arg ( fun x : ENNReal => x * 4 ) ( MeasureTheory.Measure.addHaar_ball ( μ := MeasureTheory.MeasureSpace.volume ) ( x := A ) ( show 0 ≤ ε / 2 by positivity ) ) using 1 ; ring;
  convert MeasureTheory.Measure.addHaar_ball ( μ := MeasureTheory.MeasureSpace.volume ) ( x := A ) ( show 0 ≤ ε by positivity ) using 1 ; norm_num ; ring;
  rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num ; ring;
  · rw [ ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ) ] ; ring;
  · exact ENNReal.mul_ne_top ( ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top ) ) ( by norm_num );
  · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top )
/-- **Abstract matching lemma.**  If `S` has high density in the ball `B = B(A, ε)` (its
complement occupies less than `1/10` of `B`), and `f` is a volume-preserving map sending the
half-ball `B' = B(A, ε/2)` into `B`, then there is a point `p ∈ B' ∩ S` whose image `f p` also lies
in `S`. -/
lemma matching (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hmap : ∀ T : Set (EuclideanSpace ℝ (Fin 2)), T ⊆ Metric.ball A (ε / 2) → MeasurableSet T →
      volume (f '' T) = volume T)
    (hfB : Set.MapsTo f (Metric.ball A (ε / 2)) (Metric.ball A ε))
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε)) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ f p ∈ S := by
  classical
  by_contra! h_contra;
  -- Set T := B' ∩ S, which is measurable (B' is open, S measurable). Claim f '' T ⊆ B \ S: if x = f p with p ∈ B'∩S then f p ∈ B by hfB (MapsTo), and f p ∉ S by the contradiction hypothesis applied to p. Hence by measure_mono, volume (B \ S) ≥ volume (f '' T) = volume T (using hmap T with T measurable).
  set T := Metric.ball A (ε / 2) ∩ S with hT_def
  have hT_meas : MeasurableSet T := by
    exact measurableSet_ball.inter hS
  have hT_image : f '' T ⊆ Metric.ball A ε \ S := by
    exact Set.image_subset_iff.mpr fun x hx => ⟨ hfB hx.1, h_contra x hx.1 hx.2 ⟩
  have hT_volume : volume (Metric.ball A ε \ S) ≥ volume T := by
    exact hmap T Set.inter_subset_left hT_meas ▸ MeasureTheory.measure_mono hT_image
  have hT_eq : volume (f '' T) = volume T := by
    exact hmap T Set.inter_subset_left hT_meas;
  -- So (1) volume (B \ S) ≥ volume B' - volume (B \ S), i.e. (using volume(B\S) finite) volume (B \ S) + volume (B \ S) ≥ volume B'. So 2 * volume (B \ S) ≥ volume B'.
  have h_half : 2 * volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A (ε / 2)) := by
    have h_half : volume (Metric.ball A (ε / 2)) = volume T + volume (Metric.ball A (ε / 2) \ S) := by
      rw [ ← MeasureTheory.measure_inter_add_sdiff _ hS ];
    have h_half : volume (Metric.ball A (ε / 2) \ S) ≤ volume (Metric.ball A ε \ S) := by
      exact MeasureTheory.measure_mono ( Set.sdiff_subset_sdiff ( Metric.ball_subset_ball ( by linarith ) ) le_rfl );
    rw [ two_mul ] ; exact le_trans ( by aesop ) ( add_le_add hT_volume h_half ) ;
  -- By volume_ball_half, volume B' * 4 = volume B, so volume B' = volume B / 4. Hence 2 * volume (B\S) ≥ volume B / 4, giving volume (B \ S) ≥ volume B / 8.
  have h_quarter : volume (Metric.ball A (ε / 2)) = volume (Metric.ball A ε) / 4 := by
    convert congr_arg ( fun x : ENNReal => x / 4 ) ( volume_ball_half A hε.le ) using 1;
    rw [ ENNReal.mul_div_cancel_right ] <;> norm_num
  have h_eighth : volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A ε) / 8 := by
    simp_all +decide [ div_eq_mul_inv, mul_comm, mul_left_comm ];
    convert ( mul_le_mul_right h_half ( 1 / 2 : ENNReal ) ) using 1 <;> ring;
    · rw [ show ( 8⁻¹ : ENNReal ) = 4⁻¹ * ( 1 / 2 ) by
            rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
            norm_num [ ENNReal.mul_eq_top ] ] ; ring;
    · rw [ mul_right_comm, ENNReal.div_mul_cancel ] <;> norm_num;
  refine' hdens.not_ge _;
  refine' le_trans _ h_eighth;
  rw [ ENNReal.div_eq_inv_mul ];
  rw [ ENNReal.div_eq_inv_mul ] ; gcongr ; norm_num
/-- An unbounded set contains points arbitrarily far from any fixed point. -/
lemma farPoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hunb : ¬ Bornology.IsBounded S)
    (A : EuclideanSpace ℝ (Fin 2)) (M : ℝ) : ∃ O ∈ S, dist O A > M := by
  classical
  by_contra! h;
  exact hunb <| isBounded_iff_forall_norm_le.mpr ⟨ M + ‖A‖, by rintro x ( hx : x ∈ S ) ; exact le_trans ( norm_le_of_mem_closedBall <| by simpa using h x hx ) ( by linarith ) ⟩
/-- **Density point extraction.**  A measurable set of positive measure has a point `A ∈ S` around
which `S` is dense: for some radius `ε ∈ (0,1)`, the complement of `S` occupies less than `1/10` of
the ball `B(A, ε)`. -/
lemma densityPoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (hpos : 0 < volume S) :
    ∃ A ∈ S, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε) := by
  classical
  -- By Besicovitch's theorem, there exists a point $A \in S$ such that $\lim_{r \to 0} \frac{\lambda(S \cap B(A, r))}{\lambda(B(A, r))} = 1$.
  obtain ⟨A, hA⟩ : ∃ A ∈ S, Filter.Tendsto (fun r => volume (S ∩ Metric.ball A r) / volume (Metric.ball A r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h_besicovitch : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (S ∩ Metric.ball x r) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have := @Besicovitch.ae_tendsto_measure_inter_div;
      specialize this volume S;
      filter_upwards [ this ] with x hx;
      have h_eq : ∀ r > 0, volume (S ∩ Metric.closedBall x r) = volume (S ∩ Metric.ball x r) := by
        intro r hr; rw [ MeasureTheory.measure_congr ] ; filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( show volume ( Metric.sphere x r ) = 0 from by simp +decide [ MeasureTheory.Measure.addHaar_sphere ] ) ] with y hy; simp_all +decide ;
        exact ⟨ fun h => ⟨ h.1, lt_of_le_of_ne ( by simpa [dist_eq_norm] using h.2 ) hy ⟩, fun h => ⟨ h.1, le_of_lt ( by simpa [dist_eq_norm] using h.2 ) ⟩ ⟩;
      refine' hx.congr' _;
      filter_upwards [ self_mem_nhdsWithin ] with r hr using by rw [ h_eq r hr, MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball ] ;
    contrapose! h_besicovitch;
    refine' fun h => _;
    simp_all +decide [ Filter.eventually_inf_principal ];
    exact hpos.ne' ( MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h );
  -- By the definition of limit, there exists a δ > 0 such that for all 0 < r < δ, we have volume (S ∩ Metric.ball A r) / volume (Metric.ball A r) > 9 / 10.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ r, 0 < r ∧ r < δ → volume (S ∩ Metric.ball A r) / volume (Metric.ball A r) > 9 / 10 := by
    have := Metric.mem_nhdsWithin_iff.mp ( hA.2.eventually ( lt_mem_nhds ( show 1 > 9 / 10 by norm_num [ ENNReal.div_lt_iff ] ) ) );
    exact ⟨ this.choose, this.choose_spec.1, fun r hr => this.choose_spec.2 ⟨ mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩, hr.1 ⟩ ⟩;
  refine' ⟨ A, hA.1, Min.min δ 1 / 2, _, _, _ ⟩ <;> norm_num [ hδ_pos ];
  · linarith [ min_le_left δ 1, min_le_right δ 1 ];
  · have h_complement : volume (Metric.ball A (min δ 1 / 2) \ S) = volume (Metric.ball A (min δ 1 / 2)) - volume (S ∩ Metric.ball A (min δ 1 / 2)) := by
      rw [ ← MeasureTheory.measure_sdiff ] <;> norm_num [ hS, Set.inter_comm ];
      · exact hS.nullMeasurableSet.inter ( measurableSet_ball.nullMeasurableSet );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by exact ( Metric.isBounded_ball.measure_lt_top ) ) );
    have := hδ ( Min.min δ 1 / 2 ) ⟨ by positivity, by linarith [ min_le_left δ 1, min_le_right δ 1 ] ⟩ ; rw [ gt_iff_lt, ENNReal.lt_div_iff_mul_lt ] at this <;> norm_num at *;
    · rw [ h_complement, ENNReal.sub_lt_iff_lt_right ];
      · refine' lt_of_le_of_lt _ ( ENNReal.add_lt_add_left _ this );
        · rw [ ENNReal.div_eq_inv_mul ] ; ring_nf ; norm_num;
          rw [ mul_assoc, ENNReal.inv_mul_cancel ] <;> norm_num;
        · norm_num [ ENNReal.mul_eq_top ];
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by exact ( Metric.isBounded_ball.measure_lt_top ) ) );
      · refine' le_trans ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) _;
        rw [ ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul ] <;> norm_num;
        · rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
        · positivity;
        · positivity;
    · exact Or.inl ⟨ hδ_pos, Real.pi_pos ⟩
/-
`arcsin (2/t²)` is differentiable at any `r` with `√2 < r` (so the argument lies in `(-1,1)`).
-/
lemma phi_differentiableAt {r : ℝ} (hr : Real.sqrt 2 < r) :
    DifferentiableAt ℝ (fun t => Real.arcsin (2 / t ^ 2)) r := by
  classical
  refine' ( Real.differentiableAt_arcsin.2 _ ) |> DifferentiableAt.comp _ <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) <| _;
  · exact ⟨ by linarith [ show 0 < 2 / r ^ 2 by exact div_pos zero_lt_two ( sq_pos_of_pos ( lt_trans ( Real.sqrt_pos.mpr zero_lt_two ) hr ) ) ], by rw [ Ne.eq_def, div_eq_iff ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩;
  · nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
/-
Distance moved by the isosceles twist is at most `2√2 / ‖p - O‖`.
-/
lemma dist_twistAt_phi_le (O p : EuclideanSpace ℝ (Fin 2)) (hp : Real.sqrt 2 < ‖p - O‖) :
    dist (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
  classical
  -- Use the fact that `dist (twistAt O φ p) p = ‖rot a v - v‖` and `‖rot a v - v‖^2 = 2*(1 - cos a)*r^2`.
  set v := p - O
  set r := ‖v‖
  set a := Real.arcsin (2 / r^2)
  have hdist : dist (twistAt O (fun t => Real.arcsin (2 / t^2)) p) p = ‖rot a v - v‖ := by
    unfold twistAt; simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
    simp +zetaDelta at *;
    norm_num [ EuclideanSpace.norm_eq ] ; ring
  have hnorm : ‖rot a v - v‖^2 = 2 * (1 - Real.cos a) * r^2 := by
    -- By definition of `rot`, we have `rot a v = !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1]`.
    have hrot : rot a v = !₂[Real.cos a * v 0 - Real.sin a * v 1, Real.sin a * v 0 + Real.cos a * v 1] := by
      rfl;
    rw [ hrot, EuclideanSpace.norm_eq ];
    simp +zetaDelta at *;
    rw [ Real.sq_sqrt <| by positivity ] ; rw [ EuclideanSpace.norm_eq ] ; norm_num ; ring;
    rw [ Real.sq_sqrt ] <;> try nlinarith [ sq_nonneg ( p.ofLp 0 - O.ofLp 0 ), sq_nonneg ( p.ofLp 1 - O.ofLp 1 ) ];
    rw [ Real.sin_sq, Real.cos_arcsin ] ; ring;
  -- Since $r > \sqrt{2}$, we have $0 < 2 / r^2 < 1$, so $\sin a = 2 / r^2$ and $\cos a \in [0, 1]$.
  have h_sin_cos : Real.sin a = 2 / r^2 ∧ 0 ≤ Real.cos a ∧ Real.cos a ≤ 1 := by
    rw [ Real.sin_arcsin, Real.cos_arcsin ];
    · exact ⟨ rfl, Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ⟩;
    · exact le_trans ( by norm_num ) ( div_nonneg zero_le_two ( sq_nonneg _ ) );
    · rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  -- Therefore, $1 - \cos a \leq (1 - \cos a)(1 + \cos a) = 1 - \cos^2 a = \sin^2 a = (2 / r^2)^2 = 4 / r^4$.
  have h_cos_sin : 1 - Real.cos a ≤ 4 / r^4 := by
    have := Real.sin_sq_add_cos_sq a; rw [ h_sin_cos.1 ] at this; ring_nf at this ⊢; nlinarith;
  rw [ le_div_iff₀ ] at * <;> try nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  · rw [ ← Real.sqrt_sq ( show 0 ≤ 2 * Real.sqrt 2 by positivity ) ];
    exact Real.le_sqrt_of_sq_le ( by rw [ mul_pow, hdist ] ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] );
  · exact pow_pos ( lt_trans ( Real.sqrt_pos.mpr zero_lt_two ) hp ) _
/-
**Core existence step.**  Given a density point `A` (radius `ε ∈ (0,1)`) and a far center `O`,
and a measure-preserving twist with small displacement, there is `p ∈ B(A, ε/2) ∩ S` whose twist
image also lies in `S`.
-/
lemma exists_twist_point (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A O : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ang : ℝ → ℝ)
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε))
    (hfar : 100 / ε + ε < dist O A)
    (hdiff : ∀ r : ℝ, 100 < r → DifferentiableAt ℝ ang r)
    (hbound : ∀ p : EuclideanSpace ℝ (Fin 2), dist p A < ε / 2 → dist (twistAt O ang p) p < ε / 2) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ twistAt O ang p ∈ S := by
  classical
  apply_rules [ @matching ];
  · intro T hT_sub hT_meas
    apply twistAt_volume O ang T hT_meas;
    · intro hO_in_closure_T
      have hO_in_closedBall : O ∈ Metric.closedBall A (ε / 2) := by
        exact closure_minimal ( hT_sub.trans ( Metric.ball_subset_closedBall ) ) ( Metric.isClosed_closedBall ) hO_in_closure_T;
      simp +zetaDelta at *;
      rw [ div_add', div_lt_iff₀ ] at hfar <;> nlinarith;
    · intro x hx
      have h_dist : dist x O ≥ dist O A - dist x A := by
        linarith [ dist_triangle_left O A x ]
      have h_dist_gt : dist x O > 100 := by
        nlinarith [ div_mul_cancel₀ 100 hε.ne', show dist x A < ε / 2 from hT_sub hx ]
      have h_norm_gt : ‖x - O‖ > 100 := by
        simpa only [ dist_eq_norm ] using h_dist_gt
      exact hdiff _ h_norm_gt;
  · intro p hp;
    simp_all +decide [ dist_eq_norm ];
    have := hbound p hp; rw [ show twistAt O ang p - A = ( twistAt O ang p - p ) + ( p - A ) by abel1 ] ; exact lt_of_le_of_lt ( norm_add_le _ _ ) ( by linarith ) ;
/-
**Geometry of the midpoint map.**  With angle `χ(t) = arcsin(4/t²)`, for `‖p - O‖ > 2` the points
`O`, `p`, `avgAt O χ p` form a right-angled triangle of area `1` (right angle at `avgAt O χ p`).
-/
lemma avgAt_right (O p : EuclideanSpace ℝ (Fin 2)) (hp : 2 < ‖p - O‖) :
    RightTriangleArea1 O p (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) := by
  classical
  constructor;
  · unfold area2; norm_num [ EuclideanSpace.norm_eq ] at *;
    unfold avgAt; norm_num [ rot ] ; ring_nf ;
    rw [ Real.sin_arcsin ];
    · norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ Real.sq_sqrt ( by positivity ) ] ; ring_nf at *;
      grind;
    · exact le_trans ( by norm_num ) ( mul_nonneg ( sq_nonneg _ ) zero_le_four );
    · norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ inv_mul_eq_div, div_le_iff₀ ] <;> nlinarith [ Real.mul_self_sqrt ( add_nonneg ( sq_nonneg ( p.ofLp 0 - O.ofLp 0 ) ) ( sq_nonneg ( p.ofLp 1 - O.ofLp 1 ) ) ) ];
  · refine Or.inr <| Or.inr ?_;
    unfold avgAt; norm_num [ EuclideanSpace.norm_eq ] at *;
    norm_num [ rot, inner ] ; ring;
    rw [ Real.sin_sq, Real.cos_sq ] ; ring
/-
`arcsin (4/t²)` is differentiable at any `r` with `2 < r`.
-/
lemma chi_differentiableAt {r : ℝ} (hr : 2 < r) :
    DifferentiableAt ℝ (fun t => Real.arcsin (4 / t ^ 2)) r := by
  classical
  exact ( Real.differentiableAt_arcsin.2 ⟨ by rw [ Ne, div_eq_iff ] <;> nlinarith, by rw [ Ne, div_eq_iff ] <;> nlinarith ⟩ ) |> DifferentiableAt.comp r <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) <| by positivity;
/-
Distance moved by the midpoint map is at most `2√2 / ‖p - O‖`.
-/
lemma dist_avgAt_chi_le (O p : EuclideanSpace ℝ (Fin 2)) (hp : 2 < ‖p - O‖) :
    dist (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
  classical
  -- Let $v = p - O$, $r = ‖v‖$, and $a = \arcsin(4/r^2)$. Then $avgAt O \chi p - p = (1/2)(rot a v - v)$.
  set v : EuclideanSpace ℝ (Fin 2) := p - O
  set r := ‖v‖
  set a := Real.arcsin (4 / r ^ 2)
  have h_avg : avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p - p = (1 / 2 : ℝ) • (rot a v - v) := by
    unfold avgAt;
    ext i ; norm_num ; ring!;
    norm_num [ div_eq_inv_mul ] ; ring!;
  -- Then ‖rot a v - v‖² = 2(1 - cos a)r². Since r² > 4, 0 < 4/r² ≤ 1, sin a = 4/r², cos a ∈ [0,1], 1 - cos a ≤ 1 - cos²a = sin²a = 16/r⁴.
  have h_norm_sq : ‖rot a v - v‖ ^ 2 ≤ 2 * (1 - Real.cos a) * r ^ 2 := by
    norm_num [ EuclideanSpace.norm_eq, rot ];
    rw [ Real.sq_sqrt <| by positivity ];
    rw [ show r ^ 2 = ‖v‖ ^ 2 by rfl, EuclideanSpace.norm_eq ] ; norm_num ; ring_nf;
    rw [ Real.sq_sqrt <| by positivity ] ; rw [ Real.sin_sq ] ; ring_nf ; norm_num
  have h_cos_sq : 1 - Real.cos a ≤ 16 / r ^ 4 := by
    rw [ Real.cos_arcsin ];
    ring_nf;
    nlinarith only [ show 0 ≤ r⁻¹ ^ 4 * 16 by positivity, Real.sqrt_nonneg ( 1 - r⁻¹ ^ 4 * 16 ), Real.mul_self_sqrt ( show 0 ≤ 1 - r⁻¹ ^ 4 * 16 by nlinarith [ show r⁻¹ ^ 4 ≤ 1 / 16 by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( inv_anti₀ ( by positivity ) hp.le ) 4 ) ( by norm_num ) ] ) ];
  -- Hence ‖rot a v - v‖² ≤ 2·(16/r⁴)·r² = 32/r², so ‖rot a v - v‖ ≤ 4√2/r.
  have h_norm_le : ‖rot a v - v‖ ≤ 4 * Real.sqrt 2 / r := by
    rw [ le_div_iff₀ ( by positivity ) ] at *;
    nlinarith [ show 0 < r ^ 2 by positivity, show 0 < r ^ 4 by positivity, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  rw [ dist_eq_norm, h_avg ];
  rw [ norm_smul, Real.norm_of_nonneg ] <;> ring_nf at * <;> linarith
/-
`arcsin (4/t²)` has non-positive derivative for `t > 2` (it is decreasing).
-/
lemma chi_deriv_nonpos {r : ℝ} (hr : 2 < r) :
    deriv (fun t => Real.arcsin (4 / t ^ 2)) r ≤ 0 := by
  classical
  erw [ deriv_comp _ ( Real.hasDerivAt_arcsin .. |> HasDerivAt.differentiableAt ) ] <;> norm_num;
  · norm_num [ show r ≠ 0 by linarith ];
    exact mul_nonpos_of_nonneg_of_nonpos ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) ) ( div_nonpos_of_nonpos_of_nonneg ( by linarith ) ( sq_nonneg _ ) );
  · exact DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) ( by positivity );
  · rw [ div_eq_iff ] <;> nlinarith;
  · rw [ div_eq_iff ] <;> nlinarith
/-
For `r > 100`, `cos (arcsin (4/r²)) ≥ 3/5`.
-/
lemma cos_chi_ge {r : ℝ} (hr : 100 < r) :
    (3 / 5 : ℝ) ≤ Real.cos (Real.arcsin (4 / r ^ 2)) := by
  classical
  rw [ Real.cos_arcsin ] ; exact Real.le_sqrt_of_sq_le ( by nlinarith [ show 0 ≤ 4 / r ^ 2 by positivity, show 4 / r ^ 2 ≤ 1 / 25 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith ] ) ;
/-
Directional (line) derivative of the origin midpoint map at `x ≠ 0`.
-/
lemma avg_line_hasDerivAt (ang : ℝ → ℝ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (hang : DifferentiableAt ℝ ang ‖x‖)
    (v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) • ((x + t • v) + rot (ang ‖x + t • v‖) (x + t • v)))
      ((1 / 2 : ℝ) • (v +
        (!₂[ Real.cos (ang ‖x‖) * v 0 - Real.sin (ang ‖x‖) * v 1
              - (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.sin (ang ‖x‖) * x 0 + Real.cos (ang ‖x‖) * x 1),
            Real.sin (ang ‖x‖) * v 0 + Real.cos (ang ‖x‖) * v 1
              + (deriv ang ‖x‖) * (inner ℝ x v / ‖x‖) * (Real.cos (ang ‖x‖) * x 0 - Real.sin (ang ‖x‖) * x 1)]))) 0 := by
  classical
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  convert (hl.add (twist_line_hasDerivAt ang hx hang v)).const_smul (1 / 2 : ℝ)
    using 1 <;> rfl

/-
The Jacobian determinant of the origin midpoint map at `x` with `100 < ‖x‖` is `≥ 4/5`.
-/
lemma avg_chi_det_ge {x : EuclideanSpace ℝ (Fin 2)} (hx : 100 < ‖x‖) :
    (4 / 5 : ℝ) ≤ (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) =>
      (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w)) x).det := by
  classical
  have h_deriv : ∀ j : Fin 2, (fderiv ℝ (fun w => (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w)) x) (EuclideanSpace.single j 1) =
    (1 / 2 : ℝ) • (EuclideanSpace.single j 1 +
      (!₂[ Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 0) - Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 1)
            - (deriv (fun t => Real.arcsin (4 / t ^ 2)) ‖x‖) * (inner ℝ x (EuclideanSpace.single j 1) / ‖x‖) * (Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * x 0 + Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * x 1),
          Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 0) + Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * (EuclideanSpace.single j 1 1)
            + (deriv (fun t => Real.arcsin (4 / t ^ 2)) ‖x‖) * (inner ℝ x (EuclideanSpace.single j 1) / ‖x‖) * (Real.cos (Real.arcsin (4 / ‖x‖ ^ 2)) * x 0 - Real.sin (Real.arcsin (4 / ‖x‖ ^ 2)) * x 1)])) := by
              intro j;
              convert HasDerivAt.deriv ( avg_line_hasDerivAt ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) ( show x ≠ 0 from by rintro rfl; norm_num at hx ) ( chi_differentiableAt ( show 2 < ‖x‖ from by linarith ) ) ( EuclideanSpace.single j 1 ) ) using 1;
              convert fderiv_dir _ _ _ _ using 1;
              convert DifferentiableAt.const_smul ( DifferentiableAt.add ( differentiableAt_id ) ( twist_differentiableAt _ _ _ ) ) _ using 1;
              rotate_left;
              exact ℝ;
              all_goals try infer_instance;
              exacts [ fun t => Real.arcsin ( 4 / t ^ 2 ), by rintro rfl; norm_num at hx, chi_differentiableAt ( show 2 < ‖x‖ from by linarith ), 1 / 2, by ext; norm_num ];
  convert ( show ( 4 : ℝ ) / 5 ≤ ( 1 / 2 ) * ( 1 + Real.cos ( Real.arcsin ( 4 / ‖x‖ ^ 2 ) ) ) - ( 1 / 4 ) * ( deriv ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) ‖x‖ ) * ‖x‖ * Real.sin ( Real.arcsin ( 4 / ‖x‖ ^ 2 ) ) from ?_ ) using 1;
  · rw [ det_two ];
    simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_two ];
    norm_num [ EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right ] ; ring;
    rw [ Real.sin_sq, Real.cos_arcsin ] ; ring;
    grind;
  · refine' le_trans _ ( sub_le_sub_left ( mul_nonpos_of_nonpos_of_nonneg _ _ ) _ );
    · linarith [ cos_chi_ge hx ];
    · exact mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos ( by norm_num ) ( chi_deriv_nonpos ( by linarith ) ) ) ( by positivity );
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ( Real.arcsin_nonneg.2 <| by positivity ) ( Real.arcsin_le_pi_div_two _ |> le_trans <| by linarith [ Real.pi_pos ] )
/-
The origin midpoint map (angle `χ`) is injective on the annulus `{w | 2 < ‖w‖}`.
-/
lemma avg_chi_inj :
    Set.InjOn (fun w : EuclideanSpace ℝ (Fin 2) =>
      (1 / 2 : ℝ) • (w + rot ((fun t => Real.arcsin (4 / t ^ 2)) ‖w‖) w))
      {w : EuclideanSpace ℝ (Fin 2) | 2 < ‖w‖} := by
  classical
  intros w₁ hw₁ w₂ hw₂ h_eq
  have h_norm : ‖w₁‖ = ‖w₂‖ := by
    have h_norm_eq : ‖w₁‖^2 / 2 + Real.sqrt (‖w₁‖^4 - 16) / 2 = ‖w₂‖^2 / 2 + Real.sqrt (‖w₂‖^4 - 16) / 2 := by
      have h_norm_sq : ∀ w : EuclideanSpace ℝ (Fin 2), 2 < ‖w‖ → ‖(1 / 2 : ℝ) • (w + rot (Real.arcsin (4 / ‖w‖ ^ 2)) w)‖ ^ 2 = ‖w‖ ^ 2 / 2 + Real.sqrt (‖w‖ ^ 4 - 16) / 2 := by
        intros w hw
        have h_norm_sq : ‖w + rot (Real.arcsin (4 / ‖w‖ ^ 2)) w‖ ^ 2 = 2 * ‖w‖ ^ 2 * (1 + Real.cos (Real.arcsin (4 / ‖w‖ ^ 2))) := by
          norm_num [ EuclideanSpace.norm_eq, rot ];
          rw [ Real.sq_sqrt <| by positivity ] ; ring;
          rw [ Real.sin_sq, Real.sq_sqrt <| by positivity ] ; ring;
        rw [ norm_smul, Real.norm_of_nonneg ] <;> norm_num [ h_norm_sq ] ; ring;
        rw [ show ( -16 + ‖w‖ ^ 4 : ℝ ) = ( ‖w‖ ^ 2 ) ^ 2 * ( 1 - 16 / ‖w‖ ^ 4 ) by nlinarith [ show 0 < ‖w‖ ^ 4 by positivity, div_mul_cancel₀ 16 ( show ( ‖w‖ ^ 4 : ℝ ) ≠ 0 by positivity ) ], Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf at * ; norm_num at *;
        rw [ h_norm_sq, Real.cos_arcsin ] ; ring;
      rw [← h_norm_sq w₁ hw₁, ← h_norm_sq w₂ hw₂]
      exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2) h_eq
    have h_sqrt_eq : Real.sqrt (‖w₁‖^4 - 16) = Real.sqrt (‖w₂‖^4 - 16) := by
      by_contra h_contra;
      cases lt_or_gt_of_ne h_contra <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ‖w₁‖ ^ 4 - 16 by nlinarith [ show ‖w₁‖ ^ 2 > 4 by nlinarith [ hw₁.out ] ] ), Real.mul_self_sqrt ( show 0 ≤ ‖w₂‖ ^ 4 - 16 by nlinarith [ show ‖w₂‖ ^ 2 > 4 by nlinarith [ hw₂.out ] ] ), Real.sqrt_nonneg ( ‖w₁‖ ^ 4 - 16 ), Real.sqrt_nonneg ( ‖w₂‖ ^ 4 - 16 ) ];
    nlinarith [ show 0 < ‖w₁‖ by linarith [ hw₁.out ], show 0 < ‖w₂‖ by linarith [ hw₂.out ] ];
  have h_det : (1 + Real.cos (Real.arcsin (4 / ‖w₁‖ ^ 2))) ^ 2 + (Real.sin (Real.arcsin (4 / ‖w₁‖ ^ 2))) ^ 2 ≠ 0 := by
    exact ne_of_gt ( add_pos_of_pos_of_nonneg ( sq_pos_of_pos ( by nlinarith only [ Real.cos_sq' ( Real.arcsin ( 4 / ‖w₁‖ ^ 2 ) ), Real.sin_pos_of_pos_of_lt_pi ( show 0 < Real.arcsin ( 4 / ‖w₁‖ ^ 2 ) from Real.arcsin_pos.mpr ( by exact div_pos zero_lt_four ( sq_pos_of_pos ( by linarith [ hw₁.out ] ) ) ) ) ( by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( 4 / ‖w₁‖ ^ 2 ) ] ) ] ) ) ( sq_nonneg _ ) );
  ext i; fin_cases i <;> simp_all +decide [ rot ];
  · have := congr_arg ( fun x => x 0 ) h_eq; norm_num at this; ( have := congr_arg ( fun x => x 1 ) h_eq; norm_num at this; );
    grind;
  · have := congr_arg ( fun x : EuclideanSpace ℝ ( Fin 2 ) => x 0 ) h_eq; have := congr_arg ( fun x : EuclideanSpace ℝ ( Fin 2 ) => x 1 ) h_eq; norm_num at * ;
    grobner
/-
**Measure lower bound for the midpoint map.**  For `ang = χ` and `T` avoiding `O` with all radii
`> 100`, the midpoint map expands measure by at least the factor `4/5`.
-/
lemma avgAt_volume_ge (O : EuclideanSpace ℝ (Fin 2))
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : MeasurableSet T)
    (hbig : ∀ x ∈ T, 100 < ‖x - O‖) :
    (4 / 5 : ENNReal) * volume T ≤ volume (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) '' T) := by
  classical
  -- Let χ t = arcsin(4/t²), M w = (1/2)•(w + rot(χ‖w‖)w), T' = T - {O}.
  set χ : ℝ → ℝ := fun t => Real.arcsin (4 / t ^ 2)
  set M : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w => (1 / 2 : ℝ) • (w + rot (χ ‖w‖) w)
  set T' : Set (EuclideanSpace ℝ (Fin 2)) := (fun p => p - O) '' T;
  -- By the change-of-variables area formula, we have $\int_{T'} |(fderiv ℝ M y).det| \, dy = \text{volume}(M(T'))$.
  have h_change : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ M y).det| = volume (M '' T') := by
    apply_rules [ MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image ];
    · convert hT.preimage (show Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p + O)
        from measurable_id.add_const O) using 1 <;> try rfl
      ext p
      simp [T', Set.mem_image, sub_eq_iff_eq_add]
    · intro x hx
      have hx' : x ≠ 0 := by
        obtain ⟨ p, hp, rfl ⟩ := hx; specialize hbig p hp; contrapose! hbig; aesop;
      have h_diff : DifferentiableAt ℝ M x := by
        have h_diff : DifferentiableAt ℝ (fun w => rot (χ ‖w‖) w) x := by
          apply_rules [ twist_differentiableAt ];
          obtain ⟨ p, hp, rfl ⟩ := hx; exact chi_differentiableAt ( by linarith [ hbig p hp ] ) ;
        fun_prop
      exact h_diff.hasFDerivAt.hasFDerivWithinAt;
    · intro x hx y hy; obtain ⟨ p, hp, rfl ⟩ := hx; obtain ⟨ q, hq, rfl ⟩ := hy; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have := avg_chi_inj ( show 2 < ‖p - O‖ from by linarith [ hbig p hp ] ) ( show 2 < ‖q - O‖ from by linarith [ hbig q hq ] ) ; aesop;
  -- Since $|(fderiv ℝ M y).det| \geq 4/5$ for all $y \in T'$, we have $\int_{T'} |(fderiv ℝ M y).det| \, dy \geq \int_{T'} (4/5) \, dy$.
  have h_integral : ∫⁻ y in T', ENNReal.ofReal |(fderiv ℝ M y).det| ≥ ∫⁻ y in T', ENNReal.ofReal (4 / 5) := by
    have h_integral : ∀ y ∈ T', |(fderiv ℝ M y).det| ≥ 4 / 5 := by
      have h_det : ∀ y ∈ T', (fderiv ℝ M y).det ≥ 4 / 5 := by
        rintro _ ⟨ x, hx, rfl ⟩ ; exact avg_chi_det_ge ( by simpa using hbig x hx ) ;
      exact fun y hy => le_trans ( h_det y hy ) ( le_abs_self _ );
    refine' MeasureTheory.setLIntegral_mono' _ _;
    · convert hT.preimage (show Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p + O)
        from measurable_id.add_const O) using 1 <;> try rfl
      ext p
      simp [T', Set.mem_image, sub_eq_iff_eq_add]
    · exact fun x hx => ENNReal.ofReal_le_ofReal <| h_integral x hx;
  convert h_integral.trans_eq h_change using 1;
  · norm_num [ ENNReal.ofReal_div_of_pos ];
    rw [ show T' = ( fun p => p + ( -O ) ) '' T by ext; aesop ];
    rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ];
  · rw [ show avgAt O χ '' T = ( fun p => p + O ) '' ( M '' T' ) from ?_ ];
    · rw [ Set.image_add_right ];
      rw [ MeasureTheory.measure_preimage_add_right ];
    · ext; simp [avgAt, M, T'];
      grind
/-
**Matching lemma, expanding version.**  If `f` expands measure by a factor `≥ 4/5` on subsets of
`B' = B(A, ε/2)` and maps `B'` into `B = B(A, ε)`, with `S` dense in `B`, then some `p ∈ B' ∩ S` has
`f p ∈ S`.
-/
lemma matching_ge (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : MeasurableSet S)
    (A : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hmap : ∀ T : Set (EuclideanSpace ℝ (Fin 2)), T ⊆ Metric.ball A (ε / 2) → MeasurableSet T →
      (4 / 5 : ENNReal) * volume T ≤ volume (f '' T))
    (hfB : Set.MapsTo f (Metric.ball A (ε / 2)) (Metric.ball A ε))
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε)) :
    ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ f p ∈ S := by
  classical
  by_contra! h_contra;
  -- Set T := ball A (ε/2) ∩ S (measurable, ⊆ ball A (ε/2)).
  set T := Metric.ball A (ε / 2) ∩ S
  have hT_meas : MeasurableSet T := by
    exact measurableSet_ball.inter hS
  have hT_subset : T ⊆ Metric.ball A (ε / 2) := by
    exact Set.inter_subset_left
  have hT_image_subset : f '' T ⊆ Metric.ball A ε \ S := by
    exact Set.image_subset_iff.mpr fun x hx => ⟨ hfB hx.1, h_contra x hx.1 hx.2 ⟩
  have hT_image_measure : volume (f '' T) ≥ (4 / 5) * volume T := by
    exact hmap T hT_subset hT_meas
  have hT_measure : volume T = volume (Metric.ball A (ε / 2)) - volume (Metric.ball A (ε / 2) \ S) := by
    have hfinite : volume (Metric.ball A (ε / 2) \ S) ≠ ⊤ :=
      ne_of_lt ((measure_mono Set.sdiff_subset).trans_lt Metric.isBounded_ball.measure_lt_top)
    rw [← measure_sdiff Set.sdiff_subset (measurableSet_ball.diff hS).nullMeasurableSet hfinite]
    congr 1
    ext x
    simp [T]
  have hT_measure_le : volume (Metric.ball A (ε / 2) \ S) ≤ volume (Metric.ball A ε \ S) := by
    exact MeasureTheory.measure_mono ( Set.sdiff_subset_sdiff ( Metric.ball_subset_ball ( by linarith ) ) le_rfl )
  have hT_measure_le' : volume (Metric.ball A (ε / 2)) = volume (Metric.ball A ε) / 4 := by
    rw [ ← volume_ball_half A hε.le ] ; ring; norm_num;
    rw [ ENNReal.mul_div_cancel_right ] <;> norm_num
  have h_contradiction : volume (Metric.ball A ε \ S) ≥ (4 / 5) * (volume (Metric.ball A ε) / 4 - volume (Metric.ball A ε \ S)) := by
    refine' le_trans _ ( hT_image_measure.trans ( MeasureTheory.measure_mono hT_image_subset ) );
    gcongr;
    exact hT_measure ▸ hT_measure_le'.symm ▸ tsub_le_tsub_left hT_measure_le _
  have h_final : volume (Metric.ball A ε \ S) ≥ volume (Metric.ball A ε) / 10 := by
    contrapose! h_contradiction;
    refine' lt_of_lt_of_le h_contradiction _;
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ ENNReal.toReal_mul, ENNReal.toReal_ofReal, hε.le, Real.pi_pos.le ] ; ring_nf ; norm_num [ hε.le, Real.pi_pos.le ] ;
      · rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
        · rw [ ENNReal.toReal_ofReal ( by positivity ), ENNReal.toReal_ofReal ( by positivity ) ] at * ; nlinarith [ Real.pi_pos ] ;
        · exact ne_of_lt ( lt_of_lt_of_le hdens ( by exact le_top ) );
        · exact ENNReal.mul_ne_top ( by norm_num ) ( ENNReal.mul_ne_top ( by norm_num ) ( by norm_num ) );
        · exact ne_of_lt ( lt_of_lt_of_le h_contradiction ( by exact le_top ) );
        · norm_num [ ENNReal.div_eq_top ];
          exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      · refine' le_trans h_contradiction.le _;
        rw [ show ( Metric.ball A ε : Set ( EuclideanSpace ℝ ( Fin 2 ) ) ) = ( Metric.ball A ε : Set ( EuclideanSpace ℝ ( Fin 2 ) ) ) from rfl, MeasureTheory.Measure.addHaar_ball ] <;> norm_num [ hε.le ] ; ring_nf ;
        gcongr ; norm_num;
      · norm_num [ ENNReal.mul_eq_top, ENNReal.div_eq_top ];
    · norm_num [ ENNReal.div_eq_top ];
      exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · simp +decide [ ENNReal.mul_eq_top ];
      norm_num [ ENNReal.div_eq_top ];
      exact fun h => absurd h ( by exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num ) )
  exact absurd h_final (by
  convert hdens using 1;
  rw [ ENNReal.div_eq_inv_mul ] ; norm_num)
/-
`S` (unbounded, positive measure, measurable) contains the vertices of a right-angled triangle of
area `1`.
-/
lemma exists_right (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ RightTriangleArea1 A B C := by
  classical
  -- Apply densityPoint to get A ∈ S, ε ∈ (0,1), and l.2.2.2.
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ : ∃ A ∈ S, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ volume (Metric.ball A ε \ S) < (1/10 : ENNReal) * volume (Metric.ball A ε) := densityPoint hS hpos;
  obtain ⟨O, hOS, hOfar⟩ : ∃ O ∈ S, 100 / ε + ε < dist O A := by
    contrapose! hunb;
    exact isBounded_iff_forall_norm_le.mpr ⟨ 100 / ε + ε + ‖A‖, fun x hx => by simpa using le_trans ( norm_le_of_mem_closedBall <| show x ∈ Metric.closedBall A ( 100 / ε + ε ) from hunb x hx ) ( by linarith ) ⟩;
  -- Apply `matching_ge` to get `⟨p, hpB, hpS, hfpS⟩`.
  obtain ⟨p, hpB, hpS, hfpS⟩ : ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p ∈ S := by
    apply_rules [ matching_ge ];
    · intro T hT hmeasT
      apply avgAt_volume_ge O T hmeasT (by
      intro x hx
      have h_dist : dist x O ≥ dist O A - dist x A := by
        linarith [ dist_triangle_left O A x ]
      have h_dist_xA : dist x A < ε / 2 := by
        exact hT hx
      have h_dist_OA : dist O A > 100 / ε + ε := by
        exact hOfar
      have h_dist_xO : dist x O > 100 := by
        nlinarith [ mul_div_cancel₀ 100 hε.ne' ]
      exact (by
      simpa only [ dist_eq_norm ] using h_dist_xO));
    · intro p hp
      have h_dist : dist (avgAt O (fun t => Real.arcsin (4 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
        apply dist_avgAt_chi_le;
        have := norm_sub_le ( p - O ) ( p - A ) ; simp_all +decide [ dist_eq_norm' ];
        rw [ norm_sub_rev p A ] at this ; nlinarith [ mul_div_cancel₀ 100 hε.ne' ];
      -- Since ‖p - O‖ > 100 / ε, we have 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2.
      have h_bound : 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2 := by
        have h_bound : ‖p - O‖ > 100 / ε := by
          have := dist_triangle_left O A p;
          linarith [ show dist p A < ε / 2 from hp, show dist p O = ‖p - O‖ from dist_eq_norm p O ];
        rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ 100 hε.ne', mul_pos hε ( Real.sqrt_pos.mpr zero_lt_two ) ];
      have := dist_triangle ( avgAt O ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) p ) p A; norm_num at *; linarith;
  refine' ⟨ O, p, avgAt O ( fun t => Real.arcsin ( 4 / t ^ 2 ) ) p, hOS, hpS, hfpS, avgAt_right O p _ ⟩;
  rw [ dist_eq_norm' ] at hOfar;
  rw [ Metric.mem_ball, dist_eq_norm ] at hpB;
  have := norm_sub_le ( p - O ) ( p - A ) ; norm_num at * ; nlinarith [ mul_div_cancel₀ 100 hε.ne' ]
/-- `S` (unbounded, positive measure, measurable) contains the vertices of an isosceles triangle of
area `1`. -/
lemma exists_isosceles (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    ∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ IsoscelesTriangleArea1 A B C := by
  classical
  -- By density point, get A ∈ S, ε ∈ (0,1), hdens.
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ := densityPoint hS hpos;
  obtain ⟨O, hOS, hOfar⟩ : ∃ O ∈ S, 100 / ε + ε < dist O A := farPoint hunb A (100 / ε + ε);
  obtain ⟨p, hpB, hpS, hfpS⟩ : ∃ p, p ∈ Metric.ball A (ε / 2) ∧ p ∈ S ∧ twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p ∈ S := by
    apply exists_twist_point S hS A O hε hε1 (fun t => Real.arcsin (2 / t ^ 2)) hdens hOfar;
    · exact fun r hr => phi_differentiableAt <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
    · intro p hp
      have h_dist : dist (twistAt O (fun t => Real.arcsin (2 / t ^ 2)) p) p ≤ 2 * Real.sqrt 2 / ‖p - O‖ := by
        apply dist_twistAt_phi_le;
        have h_dist : ‖p - O‖ ≥ dist O A - dist p A := by
          have := dist_triangle_left O A p; simp_all +decide [ dist_eq_norm' ] ;
          simpa only [ norm_sub_rev ] using this;
        rw [ Real.sqrt_lt ] <;> nlinarith [ show ( 0 : ℝ ) ≤ 100 / ε by positivity, mul_div_cancel₀ 100 ( ne_of_gt hε ) ];
      -- Since ‖p - O‖ > 100 / ε, we have 2 * Real.sqrt 2 / ‖p - O‖ < ε / 2.
      have h_norm : ‖p - O‖ > 100 / ε := by
        have := dist_triangle_left O A p;
        linarith! [ dist_eq_norm' p O ];
      refine lt_of_le_of_lt h_dist ?_;
      rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ 100 hε.ne', mul_pos hε ( Real.sqrt_pos.mpr zero_lt_two ) ];
  refine' ⟨ O, p, twistAt O ( fun t => Real.arcsin ( 2 / t ^ 2 ) ) p, hOS, hpS, hfpS, _ ⟩;
  apply twistAt_isosceles;
  -- By the triangle inequality, we have ‖p - O‖ ≥ dist O A - dist p A.
  have h_triangle : ‖p - O‖ ≥ dist O A - dist p A := by
    simpa [ dist_eq_norm', norm_sub_rev ] using dist_triangle_left O A p;
  nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( 100 : ℝ ) / ε ≥ 100 by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith, show ( dist p A : ℝ ) < ε / 2 by simpa using hpB ]
/-- **Theorem 1.**  Let `S ⊆ ℝ²` be an unbounded measurable set of positive Lebesgue measure.
Then `S` contains the vertices of an isosceles triangle of area `1`, and also the vertices of a
right-angled triangle of area `1`. -/
theorem thm_iso_right (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hpos : 0 < volume S) (hunb : ¬ Bornology.IsBounded S) :
    (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ IsoscelesTriangleArea1 A B C) ∧
    (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ RightTriangleArea1 A B C) :=
  ⟨exists_isosceles S hS hpos hunb, exists_right S hS hpos hunb⟩
/-
`psi R` is differentiable at `r` when `2 ≤ R` and `2 < r` (argument in `(-1,1)`).
-/
lemma psi_differentiableAt {R r : ℝ} (hR : 2 ≤ R) (hr : 2 < r) :
    DifferentiableAt ℝ (psi R) r := by
  classical
  -- Use the fact that `psi` differs from `chi` only by the factor `R^2/(R^2-1)` and establish:
  -- `0 < R^2/(R^2-1) ≤ 4/3` and `0 < 2/r^2 < 1/2` (so `0 < psi R r < 1`), hence `psi` is differentiable.
  have hr0 : 0 < r := by linarith;
  have hpos : 0 < R^2 / (R^2 - 1) ∧ R^2 / (R^2 - 1) ≤ 4 / 3 := by
    exact ⟨ div_pos ( by positivity ) ( by nlinarith ), by rw [ div_le_iff₀ ] <;> nlinarith ⟩;
  have harg : 0 < 2 / r^2 ∧ 2 / r^2 < 1 / 2 := by
    exact ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> nlinarith ⟩;
  have hlt : R^2 / (R^2 - 1) * (2 / r^2) < 1 := by
    nlinarith;
  exact DifferentiableAt.comp r ( Real.differentiableAt_arcsin.2 ⟨ by nlinarith, by nlinarith ⟩ ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.pow 2 ) ( by positivity ) ) )
/-
Distance moved by the trapezoid twist is at most `4 / ‖p - O‖` (for `2 ≤ R`, `‖p - O‖ > 2`).
-/
lemma dist_twistAt_psi_le {R : ℝ} (hR : 2 ≤ R) (O p : EuclideanSpace ℝ (Fin 2))
    (hp : 2 < ‖p - O‖) :
    dist (twistAt O (psi R) p) p ≤ 4 / ‖p - O‖ := by
  classical
  have h_dist : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖^2 ≤ 16 / ‖p - O‖^2 := by
    -- Using the fact that `rot a v - v` has norm squared `2 * (1 - cos a) * r^2`
    have h_norm_sq : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖^2 = 2 * (1 - Real.cos (psi R ‖p - O‖)) * ‖p - O‖^2 := by
      norm_num [ EuclideanSpace.norm_eq, rot ];
      rw [ Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; ring;
      rw [ Real.sin_sq ] ; ring;
    -- Using the fact that `sin a ≤ (4/3)*(2/r^2) = 8/(3r^2)` and `1 - cos a ≤ 1 - cos²a = sin²a`.
    have h_sin_a : Real.sin (psi R ‖p - O‖) ≤ 8 / (3 * ‖p - O‖^2) := by
      unfold psi;
      rw [ Real.sin_arcsin ];
      · field_simp;
        rw [ div_le_iff₀ ] <;> nlinarith only [ hR ];
      · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
      · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_pos ( sub_pos.mpr hp ) ( sub_pos.mpr hp ) ];
    -- Using the fact that `1 - cos a ≤ 1 - cos²a = sin²a`.
    have h_cos_a : 1 - Real.cos (psi R ‖p - O‖) ≤ Real.sin (psi R ‖p - O‖)^2 := by
      nlinarith only [ Real.sin_sq_add_cos_sq ( psi R ‖p - O‖ ), show 0 ≤ Real.cos ( psi R ‖p - O‖ ) from Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show psi R ‖p - O‖ ≥ 0 from Real.arcsin_nonneg.2 <| by exact mul_nonneg ( div_nonneg ( sq_nonneg _ ) <| by nlinarith ) <| by positivity ], by linarith [ Real.pi_pos, show psi R ‖p - O‖ ≤ Real.pi / 2 from Real.arcsin_le_pi_div_two _ ] ⟩ ];
    refine le_trans ( h_norm_sq.le.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_cos_a.trans <| pow_le_pow_left₀ ( Real.sin_nonneg_of_nonneg_of_le_pi ( ?_ ) <| ?_ ) h_sin_a 2 ) zero_le_two ) <| sq_nonneg _ ) ) ?_;
    · exact Real.arcsin_nonneg.2 ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
    · exact le_trans ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] );
    · field_simp;
      norm_num;
  convert Real.le_sqrt_of_sq_le h_dist using 1 <;> norm_num [ dist_eq_norm, twistAt ];
  exact congr_arg Norm.norm ( by abel1 )
/-
**Geometry of the trapezoid.**  For `2 ≤ R` and `‖p - O‖ > 2`, the four points `p`,
`twistAt O ψ_R p`, `conAt O R (twistAt O ψ_R p)`, `conAt O R p` form an isosceles trapezoid of
area `1`.
-/
lemma trapezoid_geom_raw {R : ℝ} (hR : 2 ≤ R) (O p : EuclideanSpace ℝ (Fin 2)) (hr : 2 < ‖p - O‖) :
    RawIsoTrapArea1 p (twistAt O (psi R) p)
      (conAt O R (twistAt O (psi R) p)) (conAt O R p) := by
  classical
  constructor;
  · unfold quadArea twistAt conAt psi;
    unfold rot;
    rw [ Real.sin_arcsin, Real.cos_arcsin ];
    · simp +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_two ] at *;
      rw [ Real.sq_sqrt ( by positivity ) ] ; ring_nf ; norm_num [ show R ≠ 0 by linarith, show R ^ 2 - 1 ≠ 0 by nlinarith ] ;
      field_simp;
      rw [ abs_eq ] <;> norm_num;
      exact Or.inl <| by rw [ div_eq_iff <| mul_ne_zero ( by nlinarith ) <| by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( p.ofLp 0 - O.ofLp 0 ) ^ 2 + ( p.ofLp 1 - O.ofLp 1 ) ^ 2 by positivity ) ] ] ; ring;
    · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
    · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_lt_mul_of_pos_left hr ( show 0 < R by linarith ) ];
  · refine' ⟨ _, _, _, _, _ ⟩;
    · unfold twistAt conAt;
      unfold rot; norm_num; ring;
    · unfold conAt twistAt;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
      exact congrArg Real.sqrt ( by nlinarith [ Real.sin_sq_add_cos_sq ( psi R ( Real.sqrt ( ( p.ofLp 0 - O.ofLp 0 ) ^ 2 + ( p.ofLp 1 - O.ofLp 1 ) ^ 2 ) ) ) ] );
    · unfold conAt; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
      unfold twistAt; norm_num [ rot_apply0, rot_apply1 ] ; ring;
      rw [ Real.sin_sq, Real.cos_sq ] ; ring;
    · unfold twistAt;
      unfold rot; intro h; have := congr_arg ( fun x => x 0 ) h; have := congr_arg ( fun x => x 1 ) h; norm_num at *;
      -- Since $\sin(\psi_R(\|p - O\|)) \neq 0$, we can divide both sides of the equation by $\sin(\psi_R(\|p - O\|))$.
      have h_sin_ne_zero : Real.sin (psi R ‖p - O‖) ≠ 0 := by
        unfold psi;
        rw [ Real.sin_arcsin ];
        · exact mul_ne_zero ( div_ne_zero ( by positivity ) ( by nlinarith ) ) ( div_ne_zero ( by positivity ) ( by positivity ) );
        · exact le_trans ( by norm_num ) ( mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by nlinarith ) ) ( div_nonneg zero_le_two ( sq_nonneg _ ) ) );
        · rw [ div_mul_div_comm, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( R - 2 ), mul_pos ( sub_pos.mpr hr ) ( sub_pos.mpr hr ) ];
      -- Since $\sin(\psi_R(\|p - O\|)) \neq 0$, we can divide both sides of the equation by $\sin(\psi_R(\|p - O\|))$ to get a contradiction.
      have h_contra : (p.ofLp 0 - O.ofLp 0)^2 + (p.ofLp 1 - O.ofLp 1)^2 = 0 := by
        grind;
      norm_num [ show p = O by ext i; fin_cases i <;> nlinarith! only [ h_contra ] ] at *;
    · refine' ⟨ _, _, _, _, _ ⟩;
      · unfold twistAt conAt; norm_num;
        intro h; have := congr_arg ( fun x => ‖x‖ ) h; norm_num [ norm_rot ] at this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this;
        rw [ norm_rot ] at this ; nlinarith [ inv_mul_cancel₀ ( by linarith : R ≠ 0 ) ];
      · unfold conAt twistAt;
        intro h; have := congr_arg ( fun x => x - O ) h; norm_num [ norm_smul, ne_of_gt ( zero_lt_two.trans_le hR ) ] at this;
        -- Since $rot (psi R ‖p - O‖) (p - O) = p - O$, we have $‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0$.
        have h_norm_zero : ‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0 := by
          rw [ this, sub_self, norm_zero ];
        -- Since $‖rot (psi R ‖p - O‖) (p - O) - (p - O)‖ = 0$, we have $2(1 - cos(psi R ‖p - O‖))‖p - O‖^2 = 0$.
        have h_cos_zero : 2 * (1 - Real.cos (psi R ‖p - O‖)) * ‖p - O‖^2 = 0 := by
          rw [← norm_rot_sub_sq, this, sub_self, norm_zero, zero_pow (by decide)]
        norm_num [ show ‖p - O‖ ≠ 0 by linarith ] at h_cos_zero;
        rw [ sub_eq_zero, eq_comm, Real.cos_eq_one_iff ] at h_cos_zero;
        obtain ⟨ n, hn ⟩ := h_cos_zero; rcases n with ⟨ _ | n ⟩ <;> norm_num at hn;
        · exact absurd hn ( ne_of_lt ( Real.arcsin_pos.mpr ( mul_pos ( div_pos ( by positivity ) ( by nlinarith ) ) ( div_pos ( by positivity ) ( by positivity ) ) ) ) );
        · unfold psi at hn;
          nlinarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( R ^ 2 / ( R ^ 2 - 1 ) * ( 2 / ‖p - O‖ ^ 2 ) ) ];
        · nlinarith [ Real.pi_pos, show 0 ≤ psi R ‖p - O‖ from Real.arcsin_nonneg.2 <| mul_nonneg ( div_nonneg ( sq_nonneg _ ) <| by nlinarith ) <| div_nonneg zero_le_two <| sq_nonneg _ ];
      · unfold conAt; intro H; have := congr_arg ( fun x => x - O ) H; norm_num at this;
        replace this := congr_arg ( fun x => ‖x‖ ) this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ), norm_nonneg ( p - O ) ];
      · intro h_eq
        have h_norm : ‖p - O‖ = ‖conAt O R (twistAt O (psi R) p) - O‖ := by
          rw [ ← h_eq ];
        unfold conAt at h_norm;
        norm_num [ norm_smul, abs_of_nonneg ( by positivity : 0 ≤ R ) ] at h_norm;
        rw [ show twistAt O ( psi R ) p - O = rot ( psi R ‖p - O‖ ) ( p - O ) by rw [ twistAt ] ; norm_num ] at h_norm ; rw [ norm_rot ] at h_norm ; nlinarith [ inv_mul_cancel₀ ( by linarith : R ≠ 0 ) ];
      · unfold twistAt conAt;
        intro h; have := congr_arg ( fun x => x - O ) h; norm_num at this;
        replace this := congr_arg ( fun x => ‖x‖ ) this ; norm_num [ norm_rot ] at this;
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] at this ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ), norm_nonneg ( p - O ) ]
lemma trapezoid_geom {R : ℝ} (hR : 2 ≤ R) (O p : EuclideanSpace ℝ (Fin 2))
    (hr : 2 < ‖p - O‖) :
    IsoTrapArea1 p (twistAt O (psi R) p)
      (conAt O R (twistAt O (psi R) p)) (conAt O R p) := by
  classical
  have hraw := trapezoid_geom_raw hR O p hr
  exact ⟨hraw, contraction_quad_convex hR O p (twistAt O (psi R) p) hraw.1⟩

/-
**Density-one far point.**  A measurable set of infinite measure has a point `O ∈ S`, arbitrarily
far from `A`, at which `S` has density `1` (its complement has density `0`).
-/
lemma densityOnePoint {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (hinf : volume S = ⊤) (A : EuclideanSpace ℝ (Fin 2)) (M : ℝ) :
    ∃ O ∈ S, M < dist O A ∧
      Filter.Tendsto (fun δ => volume (Metric.ball O δ \ S) / volume (Metric.ball O δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  contrapose! hinf; simp_all +decide ;
  -- By Besicovitch's density theorem, for volume.restrict S-a.e. x the ratio volume(S ∩ closedBall x r)/volume(closedBall x r) → 1.
  have h_density : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (S ∩ Metric.closedBall x r) / volume (Metric.closedBall x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert Besicovitch.ae_tendsto_measure_inter_div volume S using 1;
  -- Converting closedBall to ball (spheres null) and to the complement, the set G of points where volume(ball x δ \ S)/volume(ball x δ) → 0 is co-null in S, i.e. volume(S \ G) = 0.
  have h_complement : ∀ᵐ x ∂(volume.restrict S), Filter.Tendsto (fun r => volume (Metric.ball x r \ S) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [ h_density ] with x hx;
    have h_complement : ∀ r > 0, volume (Metric.ball x r \ S) = volume (Metric.ball x r) - volume (S ∩ Metric.ball x r) := by
      intro r hr; rw [ ← MeasureTheory.measure_sdiff ] <;> norm_num [ hS, hr ] ;
      · exact hS.nullMeasurableSet.inter ( measurableSet_ball.nullMeasurableSet );
      · finiteness;
    have h_complement : ∀ r > 0, volume (Metric.ball x r \ S) / volume (Metric.ball x r) = 1 - volume (S ∩ Metric.ball x r) / volume (Metric.ball x r) := by
      intro r hr; rw [ h_complement r hr, ENNReal.sub_div ] ;
      · rw [ ENNReal.div_self ] <;> norm_num [ hr ];
        · positivity;
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      · grind;
    have h_complement : Filter.Tendsto (fun r => volume (S ∩ Metric.ball x r) / volume (Metric.ball x r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h_complement : ∀ r > 0, volume (S ∩ Metric.ball x r) = volume (S ∩ Metric.closedBall x r) := by
        intro r hr; rw [ MeasureTheory.measure_congr ] ; filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( show MeasureTheory.MeasureSpace.volume ( Metric.sphere x r ) = 0 from by
                                                                                                                            rw [ MeasureTheory.Measure.addHaar_sphere ] ) ] with y hy; simp_all +decide ;
        exact ⟨ fun h => ⟨ h.1, Metric.mem_closedBall.mpr <| le_of_lt h.2 ⟩, fun h => ⟨ h.1, lt_of_le_of_ne ( Metric.mem_closedBall.mp h.2 ) hy ⟩ ⟩;
      have h_complement : ∀ r > 0, volume (Metric.ball x r) = volume (Metric.closedBall x r) := by
        intro r hr; rw [ MeasureTheory.Measure.addHaar_closedBall ] ; norm_num [ hr.le ] ;
        positivity;
      exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun r hr => by rw [ ‹∀ r > 0, volume ( S ∩ Metric.ball x r ) = volume ( S ∩ Metric.closedBall x r ) › r hr, h_complement r hr ] ) hx;
    rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun r hr => by rw [ ‹∀ r > 0, volume ( Metric.ball x r \ S ) / volume ( Metric.ball x r ) = 1 - volume ( S ∩ Metric.ball x r ) / volume ( Metric.ball x r ) › r hr ] ) ] ; convert ENNReal.Tendsto.sub tendsto_const_nhds h_complement _ using 1 <;> norm_num;
  rw [ MeasureTheory.ae_iff ] at h_complement;
  rw [ MeasureTheory.Measure.restrict_apply' ] at h_complement;
  · -- Since $S$ is contained in the union of the set where the complement density does not tend to 0 and the closed ball of radius $M$ centered at $A$, and the volume of the closed ball is finite, the volume of $S$ must also be finite.
    have h_finite : volume S ≤ volume ({a | ¬Filter.Tendsto (fun r => volume (Metric.ball a r \ S) / volume (Metric.ball a r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)} ∩ S) + volume (Metric.closedBall A M) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro x hx; by_cases hx' : M < dist x A <;> simp_all +decide [ dist_comm ] ;
    exact ne_of_lt ( lt_of_le_of_lt h_finite ( by rw [ h_complement ] ; exact ENNReal.add_lt_top.mpr ⟨ by norm_num, by exact ( Metric.isBounded_closedBall.measure_lt_top ) ⟩ ) );
  · exact hS
/-
**The `S_R` density step.**  Given a density point `A` and a density-one far center `O`, for some
`R ≥ 2` the refined set `S_R = {x | x ∈ S ∧ conAt O R x ∈ S}` is still dense in `B(A, ε)`.
-/
lemma exists_SR {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (A O : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hdens : volume (Metric.ball A ε \ S) < (1 / 10 : ENNReal) * volume (Metric.ball A ε))
    (hfar : 100 / ε + ε < dist O A)
    (hdens1 : Filter.Tendsto (fun δ => volume (Metric.ball O δ \ S) / volume (Metric.ball O δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ R : ℝ, 2 ≤ R ∧
      volume (Metric.ball A ε \ {x | x ∈ S ∧ conAt O R x ∈ S}) <
        (1 / 10 : ENNReal) * volume (Metric.ball A ε) := by
  classical
  -- Let $d = \text{dist}(O, A)$ and $B = \text{Metric.ball}(A, \epsilon)$.
  set d := dist O A with hd
  set B := Metric.ball A ε with hB;
  -- For $x \in B$, $conAt O R x \in ball O (2d/R)$ (since $‖conAt O R x - O‖ = R⁻¹‖x-O‖ < R⁻¹(ε+d) ≤ 2d/R$ as $ε < d$).
  have h_conAt_ball : ∀ R : ℝ, 2 ≤ R → ∀ x ∈ B, conAt O R x ∈ Metric.ball O (2 * d / R) := by
    intros R hR x hx
    have h_conAt_ball : ‖conAt O R x - O‖ < 2 * d / R := by
      have h_conAt_ball : ‖x - O‖ < 2 * d := by
        have h_conAt_ball : ‖x - O‖ ≤ ‖x - A‖ + ‖A - O‖ := by
          simpa using norm_add_le ( x - A ) ( A - O );
        simp_all +decide [ dist_eq_norm' ];
        linarith [ norm_sub_rev x A, show ‖A - O‖ > 100 by nlinarith [ div_mul_cancel₀ 100 hε.ne' ] ];
      unfold conAt; norm_num [ norm_smul, abs_of_nonneg ( by positivity : 0 ≤ R ) ] ; ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( R : ℝ ) ≠ 0 ) ] ;
    exact h_conAt_ball;
  -- Set `bad R := B ∩ {x | conAt O R x ∉ S}`. Then `bad R ⊆ conAt O R ⁻¹'(ball O (2d/R) \ S)`, and since the homothety `conAt O R` scales volume of preimages by `R²`, `volume (bad R) ≤ R²·volume(ball O (2d/R) \ S)`.
  have h_bad_R : ∀ R : ℝ, 2 ≤ R → volume (B ∩ {x | conAt O R x ∉ S}) ≤ ENNReal.ofReal (R^2) * volume (Metric.ball O (2 * d / R) \ S) := by
    intro R hR;
    have h_bad_R_subset : B ∩ {x | conAt O R x ∉ S} ⊆ (fun x => O + R • (x - O)) '' (Metric.ball O (2 * d / R) \ S) := by
      intro x hx;
      use conAt O R x; simp_all +decide [ conAt ] ;
      simp +decide [ show R ≠ 0 by linarith ];
    refine' le_trans ( MeasureTheory.measure_mono h_bad_R_subset ) _;
    have h_volume_image : ∀ (T : Set (EuclideanSpace ℝ (Fin 2))), MeasurableSet T → volume ((fun x => O + R • (x - O)) '' T) = ENNReal.ofReal (R^2) * volume T := by
      intro T hT
      have h_volume_image : volume ((fun x => R • x) '' (T - {O})) = ENNReal.ofReal (R^2) * volume (T - {O}) := by
        norm_num [ abs_of_nonneg ( by positivity : 0 ≤ R ) ];
      convert h_volume_image using 1;
      · rw [ show ( fun x => O + R • ( x - O ) ) '' T = ( fun x => R • x ) '' ( T - { O } ) + { O } from ?_ ];
        · simp +decide [ Set.add_singleton ];
        · ext; simp [Set.mem_image];
          simp +decide [ Set.mem_smul_set, eq_comm ];
          grind +qlia;
      · simp +decide [ sub_eq_add_neg ];
    rw [ h_volume_image _ ( measurableSet_ball.diff hS ) ];
  -- Writing `g δ = volume(ball O δ \ S)/volume(ball O δ)` and using `volume(ball O δ) = ofReal(δ²)·volume(ball 0 1)`, we get `R²·volume(ball O (2d/R)\S) = volume(ball O (2d))·g(2d/R)`.
  have h_volume_bad_R : ∀ R : ℝ, 2 ≤ R → volume (B ∩ {x | conAt O R x ∉ S}) ≤ volume (Metric.ball O (2 * d)) * (volume (Metric.ball O (2 * d / R) \ S) / volume (Metric.ball O (2 * d / R))) := by
    intro R hR
    have h_volume_ball : volume (Metric.ball O (2 * d)) = ENNReal.ofReal ((2 * d)^2) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      convert MeasureTheory.Measure.addHaar_ball ( MeasureTheory.MeasureSpace.volume ) O ( show 0 ≤ 2 * d by exact mul_nonneg zero_le_two ( dist_nonneg ) ) using 1;
      norm_num
    have h_volume_ball_R : volume (Metric.ball O (2 * d / R)) = ENNReal.ofReal ((2 * d / R)^2) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      have := @MeasureTheory.Measure.addHaar_ball ( EuclideanSpace ℝ ( Fin 2 ) );
      convert this volume O ( show 0 ≤ 2 * d / R by exact div_nonneg ( mul_nonneg zero_le_two ( dist_nonneg ) ) ( by positivity ) ) using 1 ; norm_num;
    refine le_trans ( h_bad_R R hR ) ?_;
    rw [ h_volume_ball, h_volume_ball_R, mul_div ];
    rw [ ENNReal.le_div_iff_mul_le ];
    · rw [ show ( 2 * d ) ^ 2 = ( 2 * d / R ) ^ 2 * R ^ 2 by rw [ div_pow, div_mul_cancel₀ _ ( by positivity ) ] ] ; rw [ ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf ; norm_num;
    · simp +zetaDelta at *;
      exact Or.inl ⟨ ⟨ by rintro rfl; norm_num at hfar; linarith [ div_pos ( by norm_num : ( 0 : ℝ ) < 100 ) hε ], by linarith ⟩, Real.pi_pos ⟩;
    · exact Or.inl <| ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) <| by exact ne_of_lt <| by exact ( Metric.isBounded_ball.measure_lt_top ) ;
  -- As $R \to \infty$, $2d/R \to 0⁺$ so $g(2d/R) \to 0$ (hdens1), hence $volume(bad R) \to 0$.
  have h_volume_bad_R_zero : Filter.Tendsto (fun R : ℝ => volume (B ∩ {x | conAt O R x ∉ S})) Filter.atTop (nhds 0) := by
    have h_volume_bad_R_zero : Filter.Tendsto (fun R : ℝ => volume (Metric.ball O (2 * d)) * (volume (Metric.ball O (2 * d / R) \ S) / volume (Metric.ball O (2 * d / R)))) Filter.atTop (nhds 0) := by
      have hscale : Filter.Tendsto (fun R : ℝ => 2 * d / R) Filter.atTop
          (nhdsWithin 0 (Set.Ioi 0)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨tendsto_const_nhds.div_atTop Filter.tendsto_id,
          Filter.eventually_atTop.mpr ⟨1, fun R hR =>
            div_pos (mul_pos zero_lt_two (lt_of_le_of_lt (by positivity) hfar)) (by positivity)⟩⟩
      have hfinite : volume (Metric.ball O (2 * d)) ≠ ⊤ :=
        ne_of_lt Metric.isBounded_ball.measure_lt_top
      simpa only [mul_zero, Function.comp_def] using
        (ENNReal.Tendsto.const_mul (a := volume (Metric.ball O (2 * d)))
          (hdens1.comp hscale) (Or.inr hfinite))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_volume_bad_R_zero ( Filter.eventually_atTop.mpr ⟨ 2, fun R hR => zero_le ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 2, fun R hR => h_volume_bad_R R hR ⟩ );
  -- Now $B \ S_R \subseteq (B \ S) \cup bad R$, so $volume(B \ S_R) \le volume(B \ S) + volume(bad R)$.
  have h_volume_B_S_R : ∀ R : ℝ, 2 ≤ R → volume (B \ {x | x ∈ S ∧ conAt O R x ∈ S}) ≤ volume (B \ S) + volume (B ∩ {x | conAt O R x ∉ S}) := by
    intro R hR; refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ ) ; intro x ; by_cases hx : x ∈ S <;> by_cases hx' : conAt O R x ∈ S <;> aesop;
  have := h_volume_bad_R_zero.eventually ( gt_mem_nhds <| show 0 < 1 / 10 * volume B - volume ( B \ S ) from tsub_pos_of_lt hdens ) ; have := this.and ( Filter.eventually_ge_atTop 2 ) ; obtain ⟨ R, hR₁, hR₂ ⟩ := this.exists; use R;
  rw [ lt_tsub_iff_left ] at hR₁;
  exact ⟨ hR₂, lt_of_le_of_lt ( h_volume_B_S_R R hR₂ ) hR₁ ⟩
/-- **Theorem 2.**  Let `S ⊆ ℝ²` be a measurable set of infinite Lebesgue measure.  Then `S`
contains the four vertices of an isosceles trapezoid of area `1`. -/
theorem thm_trapezoid (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) (hinf : volume S = ⊤) :
    ∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ IsoTrapArea1 A B C D := by
  classical
  have hpos : 0 < volume S := by rw [hinf]; exact ENNReal.zero_lt_top
  obtain ⟨A, hAS, ε, hε, hε1, hdens⟩ := densityPoint hS hpos
  obtain ⟨O, hOS, hOfar', hdens1⟩ := densityOnePoint hS hinf A (100 / ε + ε)
  have hOfar : 100 / ε + ε < dist O A := hOfar'
  obtain ⟨R, hR, hdensSR⟩ := exists_SR hS A O hε hε1 hdens hOfar hdens1
  set SR : Set (EuclideanSpace ℝ (Fin 2)) := {x | x ∈ S ∧ conAt O R x ∈ S} with hSR_def
  have hcon : Measurable (conAt O R) := by
    unfold conAt; fun_prop
  have hSR : MeasurableSet SR := hS.inter (hcon hS)
  obtain ⟨p, hpB, hpSR, hfpSR⟩ :=
    exists_twist_point SR hSR A O hε hε1 (psi R) hdensSR hOfar
      (fun r hr => psi_differentiableAt hR (by linarith))
      (by
        intro q hq
        have hqO : 100 / ε < ‖q - O‖ := by
          have h1 : dist O A ≤ dist O q + dist q A := dist_triangle O q A
          have h2 : dist O q = ‖q - O‖ := by rw [dist_eq_norm']
          have : (0:ℝ) < 100 / ε := by positivity
          nlinarith [dist_nonneg (x := q) (y := A)]
        have hb := dist_twistAt_psi_le hR O q (by
          have : (100:ℝ) / ε ≥ 100 := by rw [ge_iff_le, le_div_iff₀ hε]; nlinarith
          linarith)
        have hpos' : (0:ℝ) < ‖q - O‖ := by linarith [show (100:ℝ)/ε > 0 by positivity]
        have : 4 / ‖q - O‖ < ε / 2 := by
          rw [div_lt_iff₀ hpos']
          have : (100:ℝ) / ε * ε = 100 := by field_simp
          nlinarith [mul_pos hε hpos']
        linarith)
  have hr2 : 2 < ‖p - O‖ := by
    have h1 : dist O A ≤ dist O p + dist p A := dist_triangle O p A
    have h2 : dist O p = ‖p - O‖ := by rw [dist_eq_norm']
    have h3 : dist p A < ε / 2 := by simpa [Metric.mem_ball] using hpB
    have : (100:ℝ) / ε ≥ 100 := by rw [ge_iff_le, le_div_iff₀ hε]; nlinarith
    nlinarith
  exact ⟨p, twistAt O (psi R) p, conAt O R (twistAt O (psi R) p), conAt O R p,
    hpSR.1, hfpSR.1, hfpSR.2, hpSR.2, trapezoid_geom hR O p hr2⟩

end Koizumi
end Erdos353
