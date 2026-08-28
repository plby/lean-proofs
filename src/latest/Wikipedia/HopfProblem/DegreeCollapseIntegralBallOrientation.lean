import Wikipedia.NoExoticSixSphere.ClosedBallLocalEvaluation
import Wikipedia.NoExoticSixSphere.LocalHomologyChartTransport

/-!
# Integral orientation compatibility on a closed Euclidean ball

The actual exterior-to-puncture inclusion, followed by translation of
the puncture to zero, is homotopic to the original zero-puncture inclusion.
Naturality and injectivity of the actual relative connecting map then
identify translated local evaluations. This keeps the integral sign;
nonvanishing alone would not identify the two generators.
-/

noncomputable section

open CategoryTheory Metric ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralBallOrientation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open NoExoticSixSphere
open Wikipedia.SmoothSixDPoincare

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem shift_ne_zero (R : ℝ) (x : E) (hx : ‖x‖ ≤ R)
    (t : I) (y : BallExterior.Space E R) : (y : E) - (t : ℝ) • x ≠ 0 := by
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  have hle : ‖(y : E)‖ ≤ R := he.le.trans ((BallExterior.time_smul_norm_le t x).trans hx)
  exact (not_lt_of_ge hle) (BallExterior.norm_gt R y)

/-- A homotopy of the literal punctured-space maps, also when x lies on the boundary. -/
def exteriorShift (R : ℝ) (hR : 0 ≤ R) (x : E) (hx : ‖x‖ ≤ R) :
    (BallExterior.toPunctured R hR).Homotopy
      ((BallExterior.puncturedTranslate x :
        C(({x}ᶜ : Set E), PuncturedRadial.Space E)).comp
          (BallExterior.toPointPuncture R x hx)) where
  toFun q := ⟨(q.2 : E) - (q.1 : ℝ) • x, shift_ne_zero R x hx q.1 q.2⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_snd).sub
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).subtype_mk _
  map_zero_left y := by
    apply Subtype.ext
    simp [BallExterior.toPunctured]
  map_one_left y := by
    apply Subtype.ext
    simp [BallExterior.puncturedTranslate, BallExterior.toPointPuncture]

abbrev evaluation (R : ℝ) (x : E) (hx : x ∈ closedBall (0 : E) R) (k : ℕ) :=
  RelativeSingularHomology.map (ContinuousMap.id E)
    (ClosedBallLocalHomology.point_mapsTo R x hx) k

/-- The already proved integral quasi-isomorphism gives the original evaluation equivalence. -/
def evaluationEquiv (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) (k : ℕ) :
    RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ k ≃ₗ[ℤ]
      RelativeSingularHomology.LocalHomology x k := by
  let := ClosedBallLocalHomology.evaluationChain_quasiIso R hR x hx
  exact (isoOfQuasiIsoAt (ClosedBallLocalHomology.evaluationChain R x hx) k).toLinearEquiv

theorem evaluationEquiv_toLinearMap (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) (k : ℕ) :
    (evaluationEquiv R hR x hx k).toLinearMap = evaluation R x hx k := rfl

omit [NormedSpace ℝ E] in
theorem translation_mapsTo (x : E) :
    Set.MapsTo (Homeomorph.subRight x : C(E, E)) ({x}ᶜ : Set E) ({(0 : E)}ᶜ : Set E) := by
  intro y hy
  exact sub_ne_zero.mpr hy

theorem localHomeomorphEquivAt_toLinearMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    (x : X) (y : Y) (hxy : h x = y)
    (hf : Set.MapsTo (h : C(X, Y)) ({x}ᶜ : Set X) ({y}ᶜ : Set Y)) (k : ℕ) :
    (RelativeSingularHomology.localHomeomorphEquivAt h x y hxy k).toLinearMap =
      RelativeSingularHomology.map (h : C(X, Y)) hf k := by
  subst y
  rfl

omit [NormedSpace ℝ E] in
theorem translation_toLinearMap (x : E) (k : ℕ) :
    (RelativeSingularHomology.translateLocalEquiv E x k).toLinearMap =
      RelativeSingularHomology.map (Homeomorph.subRight x : C(E, E)) (translation_mapsTo x) k :=
  localHomeomorphEquivAt_toLinearMap (Homeomorph.subRight x) x 0 (sub_self x)
    (translation_mapsTo x) k

theorem translated_evaluation (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) (n : ℕ) (hn : n ≠ 0)
    (a : RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 1)) :
    RelativeSingularHomology.translateLocalEquiv E x (n + 1) (evaluation R x hx (n + 1) a) =
      evaluation R 0 (mem_closedBall_self hR) (n + 1) a := by
  apply (RelativeSingularHomology.contractibleConnectingEquiv ({(0 : E)}ᶜ : Set E) n hn).injective
  change RelativeSingularHomology.connecting ({(0 : E)}ᶜ : Set E) n
      ((RelativeSingularHomology.translateLocalEquiv E x (n + 1)).toLinearMap
        (evaluation R x hx (n + 1) a)) = _
  rw [translation_toLinearMap]
  have ht := LinearMap.congr_fun
    (RelativeSingularHomology.connecting_naturality (Homeomorph.subRight x : C(E, E))
      (translation_mapsTo x) n) (evaluation R x hx (n + 1) a)
  have hxev := LinearMap.congr_fun
    (RelativeSingularHomology.connecting_naturality (ContinuousMap.id E)
      (ClosedBallLocalHomology.point_mapsTo R x hx) n) a
  have h0ev := LinearMap.congr_fun
    (RelativeSingularHomology.connecting_naturality (ContinuousMap.id E)
      (ClosedBallLocalHomology.point_mapsTo R 0 (mem_closedBall_self hR)) n) a
  have htmap : RelativeSingularHomology.restrictedMap
      (Homeomorph.subRight x : C(E, E)) (translation_mapsTo x) =
      (BallExterior.puncturedTranslate x : C(({x}ᶜ : Set E), PuncturedRadial.Space E)) := by
    ext y
    rfl
  have h0map : RelativeSingularHomology.restrictedMap (ContinuousMap.id E)
      (ClosedBallLocalHomology.point_mapsTo R 0 (mem_closedBall_self hR)) =
      BallExterior.toPunctured R hR := by
    ext y
    rfl
  rw [htmap] at ht
  rw [ClosedBallLocalHomology.restrictedPointMap_eq R x hx] at hxev
  rw [h0map] at h0ev
  simp only [LinearMap.comp_apply] at ht hxev h0ev
  have hh := homotopy_homologyMap (exteriorShift R hR x (mem_closedBall_zero_iff.mp hx)) n
  rw [singularHomologyMap_comp] at hh
  change _ = RelativeSingularHomology.connecting ({(0 : E)}ᶜ : Set E) n
    (evaluation R 0 (mem_closedBall_self hR) (n + 1) a)
  rw [← ht, ← hxev]
  exact (LinearMap.congr_fun hh
    (RelativeSingularHomology.connecting (closedBall (0 : E) R)ᶜ n a)).symm.trans h0ev

end Wikipedia.HopfProblem.DegreeCollapse.IntegralBallOrientation
