import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiberFactors
import Wikipedia.HopfProblem.DegreeCollapseSphereFrameRawComparison

/-!
# The explicit lifted Hopf columns compute the original factor-frame parities

Pull back the checked product deformation along an actual immersed sphere
in the original regular fiber. Its quaternionic tangent columns lie in the
actual equation kernel. This gives a homotopy of injective combined operators
to the raw frame, then to the existing orthonormalized geometric operator.
The final parity equality retains the original source twist.
-/

noncomputable section

open Function unitInterval
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFactorFrameComparison

open NoExoticSixSphere QuaternionicHopf GLOrthonormalization Stiefel SpanningDiskFrameCoordinates
open QuaternionicHopfProductDiffeomorph QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors
open QuaternionicHopfInducedProductFrame QuaternionicHopfProductLift

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

theorem operator_injective_of_equation
    (D : V 17 →L[ℝ] Normal) (R : V 11 →L[ℝ] V 17) (B : V 3 →L[ℝ] V 17)
    (hR : ∀ w, D (R w) = normalCoordinates w) (hB : ∀ v, D (B v) = 0)
    (hiB : Injective B) : Injective (OperatorSum.operator R B) := by
  let c : V 14 ≃L[ℝ] (V 11 × V 3) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 11) (m := 3)
  have hD (v : V 14) : D (OperatorSum.operator R B v) = normalCoordinates (c v).1 := by
    rw [OperatorSum.operator_apply, map_add, hR, hB, add_zero]
  intro u v huv
  have hu : (c u).1 = (c v).1 := by
    apply normalCoordinates.injective
    rw [← hD, ← hD]
    exact congrArg D huv
  have h := huv
  rw [OperatorSum.operator_apply, OperatorSum.operator_apply] at h
  change R (c u).1 + B (c u).2 = R (c v).1 + B (c v).2 at h
  rw [hu] at h
  exact c.injective (Prod.ext hu (hiB (add_left_cancel h)))

def parameter (f : Sphere 3 → Fiber) (s : Sphere 3) : Sphere 3 × Sphere 3 :=
  fiberDiffeomorph.symm (f s)

theorem ambient_parameter (x : Fiber) :
    ambientInclusion (fiberDiffeomorph.symm x) = embedding.toFun x := by
  have h := embedding_fiberDiffeomorph (fiberDiffeomorph.symm x)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

variable (a : Sphere 16) (f : Sphere 3 → Fiber)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

include hf in
theorem contMDiff_parameter : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (parameter f) :=
  fiberDiffeomorph.symm.contMDiff.comp hf

include hf in
theorem tangent_equation_zero (s : Sphere 3) (v : V 3) :
    equationDerivative a (parameter f s)
      (SphereFrameRawComparison.tangent embedding f s v) = 0 := by
  let F : Sphere 3 → V 17 := fun q ↦ (f q).val.val
  have hF : ContMDiff (𝓡 3) 𝓘(ℝ, V 17) ∞ F := embedding.smooth.comp hf
  have hE := (SphereFiberNormalFrame.contDiffAt_equations smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point a (f s).val (f s).property).differentiableAt (by simp)
  change DifferentiableAt ℝ (equations a) (F s) at hE
  have he : equations a ∘ F = fun _ : Sphere 3 ↦ (0 : Normal) := by
    funext q
    exact SphereFiberNormalFrame.equations_zero smoothMap QuaternionicHopfProductFiber.point a
      (f q).val (f q).property
  have hc : mfderiv (𝓡 3) 𝓘(ℝ, Normal) (equations a ∘ F) s =
      (mfderiv 𝓘(ℝ, V 17) 𝓘(ℝ, Normal) (equations a) (F s)).comp
        (mfderiv (𝓡 3) 𝓘(ℝ, V 17) F s) :=
    mfderiv_comp s hE.mdifferentiableAt
      (hF.mdifferentiableAt (by simp))
  rw [he, mfderiv_const, mfderiv_eq_fderiv] at hc
  have hm : SphereFrameRawComparison.tangent embedding f s v ∈
      (mfderiv (𝓡 3) 𝓘(ℝ, V 17) F s).range := by
    rw [← SphereThreeTangentFrame.range_framedDerivative F hF s]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hm
  change fderiv ℝ (equations a) (ambientInclusion (parameter f s))
    (SphereFrameRawComparison.tangent embedding f s v) = 0
  rw [parameter, ambient_parameter, ← hw]
  exact (congrArg (fun L : V 3 →L[ℝ] Normal ↦ L w) hc).symm

def columns (p : ℝ × Sphere 3) : V 11 →L[ℝ] V 17 :=
  framingDeformation a (p.1, parameter f p.2)

include hf in
theorem contMDiff_columns :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 11 →L[ℝ] V 17) ∞ (columns a f) :=
  (contMDiff_framingDeformation a).comp
    (contMDiff_fst.prodMk ((contMDiff_parameter f hf).comp contMDiff_snd))

theorem columns_zero (s : Sphere 3) : columns a f (0, s) =
    (fullRightInverse (parameter f s)).comp normalCoordinates.toContinuousLinearMap :=
  framingDeformation_zero a (parameter f s)

theorem columns_one (s : Sphere 3) : columns a f (1, s) = (framing a).ambient (f s) := by
  rw [columns, framingDeformation_one, parameter, Diffeomorph.apply_symm_apply]

theorem columns_equation (p : ℝ × Sphere 3) (w : V 11) :
    equationDerivative a (parameter f p.2) (columns a f p w) = normalCoordinates w :=
  normalization_rightInverse a (p.1, parameter f p.2) (normalCoordinates w)

include hf hd in
theorem columns_operator_injective (p : ℝ × Sphere 3) :
    Injective (OperatorSum.operator (columns a f p)
      (SphereFrameRawComparison.tangent embedding f p.2)) :=
  operator_injective_of_equation (equationDerivative a (parameter f p.2)) (columns a f p)
    (SphereFrameRawComparison.tangent embedding f p.2) (columns_equation a f p)
    (tangent_equation_zero a f hf p.2)
    (SphereFrameRawComparison.tangent_injective embedding f hf hd p.2)

def liftedMap : C(Sphere 3, Monomorphism.Space 17 14) where
  toFun s := ⟨OperatorSum.operator (columns a f (0, s))
    (SphereFrameRawComparison.tangent embedding f s), columns_operator_injective a f hf hd (0, s)⟩
  continuous_toFun := (OperatorSum.continuous_operator (fun s ↦ columns a f (0, s))
    (SphereFrameRawComparison.tangent embedding f)
    ((contMDiff_columns a f hf).continuous.comp (continuous_const.prodMk continuous_id))
    (SphereFrameRawComparison.contMDiff_tangent embedding f hf).continuous).subtype_mk _

theorem liftedMap_value (s : Sphere 3) :
    (liftedMap a f hf hd s).val = OperatorSum.operator
      ((fullRightInverse (parameter f s)).comp normalCoordinates.toContinuousLinearMap)
      (SphereThreeTangentFrame.framedDerivative (embedding.toFun ∘ f) s) := by
  change OperatorSum.operator (columns a f (0, s)) _ = _
  rw [columns_zero]
  rfl

include hf in
theorem continuous_interval_operator : Continuous (fun p : I × Sphere 3 ↦
    OperatorSum.operator (columns a f ((p.1 : ℝ), p.2))
      (SphereFrameRawComparison.tangent embedding f p.2)) := by
  let B : Sphere 3 → V 3 →L[ℝ] V 17 := SphereFrameRawComparison.tangent embedding f
  have hB : Continuous B := (SphereFrameRawComparison.contMDiff_tangent embedding f hf).continuous
  have ht : Continuous (fun p : I × Sphere 3 ↦ ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact OperatorSum.continuous_operator
    (fun p : I × Sphere 3 ↦ columns a f ((p.1 : ℝ), p.2))
    (fun p : I × Sphere 3 ↦ B p.2)
    ((contMDiff_columns a f hf).continuous.comp ht) (hB.comp continuous_snd)

theorem columns_operator_one (s : Sphere 3) :
    OperatorSum.operator (columns a f (1, s)) (SphereFrameRawComparison.tangent embedding f s) =
      (SphereFrameRawComparison.rawMap embedding (framing a) f hf hd s).val := by
  let B : V 3 →L[ℝ] V 17 := SphereFrameRawComparison.tangent embedding f s
  have hR : columns a f (1, s) = (framing a).ambient (f s) := columns_one a f s
  have h1 : OperatorSum.operator (columns a f (1, s)) B =
      OperatorSum.operator ((framing a).ambient (f s)) B :=
    congrArg (fun R : V 11 →L[ℝ] V 17 ↦ OperatorSum.operator R B) hR
  have h2 : OperatorSum.operator ((framing a).ambient (f s)) B =
      (SphereFrameRawComparison.rawMap embedding (framing a) f hf hd s).val :=
    (SphereFrameRawComparison.rawMap_value embedding (framing a) f hf hd s).symm
  exact h1.trans h2

def operatorFamily (p : I × Sphere 3) : Monomorphism.Space 17 14 :=
  ⟨OperatorSum.operator (columns a f ((p.1 : ℝ), p.2))
    (SphereFrameRawComparison.tangent embedding f p.2),
    columns_operator_injective a f hf hd ((p.1 : ℝ), p.2)⟩

theorem operatorFamily_one (s : Sphere 3) : operatorFamily a f hf hd (1, s) =
    SphereFrameRawComparison.rawMap embedding (framing a) f hf hd s := by
  apply Subtype.ext
  dsimp only [operatorFamily, Prod.fst, Prod.snd]
  exact columns_operator_one a f hf hd s

def operatorHomotopy : (liftedMap a f hf hd).Homotopy
    (SphereFrameRawComparison.rawMap embedding (framing a) f hf hd) where
  toFun := operatorFamily a f hf hd
  continuous_toFun := (continuous_interval_operator a f hf).subtype_mk _
  map_zero_left s := by
    apply Subtype.ext
    rfl
  map_one_left := operatorFamily_one a f hf hd

theorem liftedMap_homotopic_actual :
    (liftedMap a f hf hd).Homotopic (embedding.sphereFrameOperatorMap (framing a) f hf hd) :=
  (show (liftedMap a f hf hd).Homotopic
    (SphereFrameRawComparison.rawMap embedding (framing a) f hf hd) from
      ⟨operatorHomotopy a f hf hd⟩).trans
    (SphereFrameRawComparison.rawMap_homotopic embedding (framing a) f hf hd)

theorem parity_eq_lifted : embedding.immersedSphereFrameParity (framing a) f hf hd =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap (liftedMap a f hf hd)) :=
  (Monomorphism.sphereParityOfDimension_homotopic _ _ _
    (twistedBlockMap_homotopic (liftedMap_homotopic_actual a f hf hd))).symm

theorem leftParity_eq_lifted (r : Sphere 3) : leftParity a r =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap (liftedMap a (left r) (contMDiff_left r) (left_mfderiv_injective r))) :=
  parity_eq_lifted a (left r) (contMDiff_left r) (left_mfderiv_injective r)

theorem rightParity_eq_lifted (q : Sphere 3) : rightParity a q =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap (liftedMap a (right q) (contMDiff_right q) (right_mfderiv_injective q))) :=
  parity_eq_lifted a (right q) (contMDiff_right q) (right_mfderiv_injective q)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFactorFrameComparison
