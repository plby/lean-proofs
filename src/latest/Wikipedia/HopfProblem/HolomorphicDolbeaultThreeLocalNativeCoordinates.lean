import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalCoordinates

/-!
# Complex coordinates on the original three-dimensional model

The equivalence here only lists the three original complex coordinates of
`ℂ × ComplexPlane₂`.  In particular, it does not replace a manifold atlas.
The basis comparison below is for actual real continuous linear covectors
which are antiholomorphic for this original complex structure.
-/

noncomputable section

open Complex Filter Set
open scoped ContDiff Topology ComplexConjugate

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- List the base coordinate first, followed by the two fibre coordinates. -/
def nativeLinearEquiv : Model ≃ₗ[ℂ] Coordinates where
  toFun q := Fin.cons q.1 q.2
  invFun q := (q 0, fun i => q i.succ)
  left_inv q := rfl
  right_inv q := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_add' q r := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_smul' c q := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The original complex model and its three complex coordinates. -/
def nativeEquiv : Model ≃L[ℂ] Coordinates :=
  nativeLinearEquiv.toContinuousLinearEquiv

/-- Restrict the same complex coordinate map to real scalars for smooth
calculus, retaining its original function and topology. -/
def nativeRealEquiv : Model ≃L[ℝ] Coordinates where
  toLinearEquiv := nativeEquiv.toLinearEquiv.restrictScalars ℝ
  continuous_toFun := nativeEquiv.continuous
  continuous_invFun := nativeEquiv.symm.continuous

@[simp] theorem nativeEquiv_apply_zero (q : Model) : nativeEquiv q 0 = q.1 := rfl

@[simp] theorem nativeEquiv_apply_succ (q : Model) (i : Fin 2) :
    nativeEquiv q i.succ = q.2 i := rfl

theorem nativeEquiv_apply (q : Model) : nativeEquiv q = ![q.1, q.2 0, q.2 1] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeEquiv_symm_apply (q : Coordinates) :
    nativeEquiv.symm q = (q 0, fun i => q i.succ) := rfl

/-- A coordinate direction, as a vector in the original complex model. -/
def nativeBasis (i : Fin 3) : Model := nativeEquiv.symm (basisVector i)

@[simp] theorem nativeEquiv_nativeBasis (i : Fin 3) :
    nativeEquiv (nativeBasis i) = basisVector i :=
  nativeEquiv.apply_symm_apply _

/-- These are a complex basis of the original model, with literal coordinates. -/
theorem nativeBasis_sum (q : Model) :
    (∑ i : Fin 3, nativeEquiv q i • nativeBasis i) = q := by
  apply nativeEquiv.injective
  simp only [map_sum, map_smul, nativeEquiv_nativeBasis]
  ext j
  simp [basisVector, Pi.single_apply]

section Antilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Real linearity and the anti-linearity identity for `I` imply the full
conjugate scalar identity. -/
theorem antiCovector_map_complex_smul {L : E →L[ℝ] ℂ}
    (hL : L ∈ antiCovectors) (c : ℂ) (v : E) :
    L (c • v) = conj c * L v := by
  have hs (r : ℝ) (x : E) : (r : ℂ) • x = r • x :=
    IsScalarTower.algebraMap_smul ℂ r x
  have hc : c • v = c.re • v + c.im • (I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, hs, hs]
  have hc' : conj c = (c.re : ℂ) - (c.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hc, map_add, map_smul, map_smul, hL v, hc']
  simp only [Complex.real_smul]
  ring

end Antilinear

/-- An actual antiholomorphic covector is determined by its values on the
three original complex coordinate vectors. -/
theorem antiCovector_ext_nativeBasis {L K : Model →L[ℝ] ℂ}
    (hL : L ∈ antiCovectors) (hK : K ∈ antiCovectors)
    (h : ∀ i : Fin 3, L (nativeBasis i) = K (nativeBasis i)) : L = K := by
  apply ContinuousLinearMap.ext
  intro q
  rw [← nativeBasis_sum q, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [antiCovector_map_complex_smul hL, antiCovector_map_complex_smul hK, h i]

/-- The antiholomorphic derivative in a coordinate of the original model. -/
def nativeCoordinateDbar (i : Fin 3) (f : Model → ℂ) (q : Model) : ℂ :=
  dbar f q (nativeBasis i)

/-- The full derivative under the complex coordinate listing map. -/
theorem dbar_comp_nativeEquiv {f : Coordinates → ℂ} {q : Model}
    (hf : DifferentiableAt ℝ f (nativeEquiv q)) :
    dbar (f ∘ nativeEquiv) q =
      (dbar f (nativeEquiv q)).comp
        (nativeEquiv.toContinuousLinearMap.restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  exact dbar_complex_linear_comp nativeEquiv.toContinuousLinearMap hf v

/-- The full derivative under the inverse complex coordinate listing map. -/
theorem dbar_comp_nativeEquiv_symm {f : Model → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f (nativeEquiv.symm q)) :
    dbar (f ∘ nativeEquiv.symm) q =
      (dbar f (nativeEquiv.symm q)).comp
        (nativeEquiv.symm.toContinuousLinearMap.restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  exact dbar_complex_linear_comp nativeEquiv.symm.toContinuousLinearMap hf v

/-- Coordinate primitives transfer to the original complex model with their
actual antiholomorphic derivatives. -/
theorem nativeCoordinateDbar_comp_nativeEquiv (i : Fin 3)
    {f : Coordinates → ℂ} {q : Model}
    (hf : DifferentiableAt ℝ f (nativeEquiv q)) :
    nativeCoordinateDbar i (f ∘ nativeEquiv) q =
      coordinateDbar i f (nativeEquiv q) := by
  rw [nativeCoordinateDbar, dbar_comp_nativeEquiv hf]
  change dbar f (nativeEquiv q) (nativeEquiv (nativeBasis i)) = _
  rw [nativeEquiv_nativeBasis]
  rfl

/-- The coordinate derivative of a native function is its native derivative
evaluated at the corresponding original basis vector. -/
theorem coordinateDbar_comp_nativeEquiv_symm (i : Fin 3)
    {f : Model → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f (nativeEquiv.symm q)) :
    coordinateDbar i (f ∘ nativeEquiv.symm) q =
      nativeCoordinateDbar i f (nativeEquiv.symm q) := by
  rw [coordinateDbar, dbar_comp_nativeEquiv_symm hf]
  rfl

section Smooth

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞ω}

/-- The original complex coordinate listing is smooth over the reals. -/
theorem contDiff_nativeEquiv : ContDiff ℝ n nativeEquiv :=
  nativeRealEquiv.contDiff

/-- The inverse complex coordinate listing is smooth over the reals. -/
theorem contDiff_nativeEquiv_symm : ContDiff ℝ n nativeEquiv.symm :=
  nativeRealEquiv.symm.contDiff

theorem contDiff_comp_nativeEquiv_iff {f : Coordinates → G} :
    ContDiff ℝ n (f ∘ nativeEquiv) ↔ ContDiff ℝ n f :=
  nativeRealEquiv.contDiff_comp_iff

theorem contDiff_comp_nativeEquiv_symm_iff {f : Model → G} :
    ContDiff ℝ n (f ∘ nativeEquiv.symm) ↔ ContDiff ℝ n f :=
  nativeRealEquiv.symm.contDiff_comp_iff

theorem contDiffOn_comp_nativeEquiv_iff {f : Coordinates → G} {U : Set Coordinates} :
    ContDiffOn ℝ n (f ∘ nativeEquiv) (nativeEquiv ⁻¹' U) ↔ ContDiffOn ℝ n f U :=
  nativeRealEquiv.contDiffOn_comp_iff

theorem contDiffOn_comp_nativeEquiv_symm_iff {f : Model → G} {U : Set Model} :
    ContDiffOn ℝ n (f ∘ nativeEquiv.symm) (nativeEquiv.symm ⁻¹' U) ↔
      ContDiffOn ℝ n f U :=
  nativeRealEquiv.symm.contDiffOn_comp_iff

end Smooth

/-- Three coordinate primitive equations imply equality of the full actual
native antiholomorphic differential as a germ. -/
theorem dbar_comp_nativeEquiv_eventuallyEq {u : Coordinates → ℂ}
    {a : Model → Model →L[ℝ] ℂ} {x : Model}
    (hu : Differentiable ℝ u)
    (ha : ∀ᶠ q in 𝓝 x, a q ∈ antiCovectors)
    (h : ∀ i : Fin 3, coordinateDbar i u =ᶠ[𝓝 (nativeEquiv x)]
      fun q => a (nativeEquiv.symm q) (nativeBasis i)) :
    dbar (u ∘ nativeEquiv) =ᶠ[𝓝 x] a := by
  have hi : ∀ i : Fin 3, ∀ᶠ q in 𝓝 x,
      coordinateDbar i u (nativeEquiv q) = a q (nativeBasis i) := by
    intro i
    filter_upwards [nativeEquiv.continuous.continuousAt.eventually (h i)] with q hq
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hq
  have hall : ∀ᶠ q in 𝓝 x, ∀ i : Fin 3,
      coordinateDbar i u (nativeEquiv q) = a q (nativeBasis i) :=
    Filter.eventually_all.mpr hi
  filter_upwards [ha, hall] with q haq hq
  apply antiCovector_ext_nativeBasis (dbar_mem _ _) haq
  intro i
  exact (nativeCoordinateDbar_comp_nativeEquiv i (hu (nativeEquiv q))).trans (hq i)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
