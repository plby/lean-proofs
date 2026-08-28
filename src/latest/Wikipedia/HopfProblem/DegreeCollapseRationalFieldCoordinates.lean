import Wikipedia.HopfProblem.DegreeCollapseNativeCubicEndpoint
import Wikipedia.HopfProblem.DegreeCollapseCubicDescent
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Rational linearization of the cubic field at its endpoints

The map `(s - e*a)/(a + e*s)` conjugates the longitudinal cubic field
`a² - s²` to the linear field of rate `-2*e*a`, for `e² = 1`.
With `a = 1/2` these are exactly the two rates in the Morse descent field.
The transverse coordinates are unchanged. This is a field normal form;
no identity between the original Morse function and the cubic is needed.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def endpointFieldCoordinate (a e s : ℝ) : ℝ := (s - e * a) / (a + e * s)

def endpointFieldDomain (a e : ℝ) : Set ℝ := {s | 0 < a + e * s}

theorem endpointFieldDomain_open (a e : ℝ) : IsOpen (endpointFieldDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem endpointField_mem_domain {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    e * a ∈ endpointFieldDomain a e := by
  change 0 < a + e * (e * a)
  have h : e * (e * a) = a := by rw [← mul_assoc, ← pow_two, he, one_mul]
  rw [h]
  linarith

theorem endpointFieldCoordinate_center (a e : ℝ) :
    endpointFieldCoordinate a e (e * a) = 0 := by
  simp [endpointFieldCoordinate]

theorem contDiffOn_endpointFieldCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointFieldCoordinate a e) (endpointFieldDomain a e) := by
  intro s hs
  exact ((contDiffAt_id.sub contDiffAt_const).div
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) (ne_of_gt hs)).contDiffWithinAt

theorem hasDerivAt_endpointFieldCoordinate (a : ℝ) {e : ℝ} (he : e ^ 2 = 1)
    {s : ℝ} (hs : s ∈ endpointFieldDomain a e) :
    HasDerivAt (endpointFieldCoordinate a e) (2 * a / (a + e * s) ^ 2) s := by
  have hd := ((hasDerivAt_id s).sub_const (e * a)).div
    (((hasDerivAt_id s).const_mul e).const_add a) (ne_of_gt hs)
  convert! hd using 1
  congr 1
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

theorem endpointFieldCoordinate_pushforward (a : ℝ) {e : ℝ} (he : e ^ 2 = 1)
    {s : ℝ} (hs : s ∈ endpointFieldDomain a e) :
    deriv (endpointFieldCoordinate a e) s * (a ^ 2 - s ^ 2) =
      (-2 * e * a) * endpointFieldCoordinate a e s := by
  rw [(hasDerivAt_endpointFieldCoordinate a he hs).deriv]
  unfold endpointFieldCoordinate
  have hn : a + e * s ≠ 0 := ne_of_gt hs
  field_simp
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- An actual scalar partial diffeomorphism, defined through the endpoint. -/
theorem exists_endpoint_field_scalar_chart {a : ℝ} (ha : 0 < a)
    {e : ℝ} (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ P.source ∧ P.source ⊆ endpointFieldDomain a e ∧
      (P : ℝ → ℝ) = endpointFieldCoordinate a e ∧ P (e * a) = 0 := by
  have hm := endpointField_mem_domain ha he
  have hd := (hasDerivAt_endpointFieldCoordinate a he hm).hasFDerivAt
  have hn : 2 * a / (a + e * (e * a)) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ (ne_of_gt hm))
  have hi : Injective (fderiv ℝ (endpointFieldCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * (2 * a / (a + e * (e * a)) ^ 2) =
      y * (2 * a / (a + e * (e * a)) ^ 2) at hxy
    exact mul_right_cancel₀ hn hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ (endpointFieldCoordinate a e) (e * a)).toLinearMap hi).toContinuousLinearEquiv
  obtain ⟨P, hp, hsub, hP⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    (endpointFieldDomain_open a e) hm (contDiffOn_endpointFieldCoordinate a e) ⟨A, rfl⟩
  exact ⟨P, hp, hsub, hP, by rw [hP, endpointFieldCoordinate_center]⟩

variable {m : ℕ}

def endpointLinearField (σ : Fin m → ℝ) (a e : ℝ) (p : Model m) : Model m :=
  ((-2 * e * a) * p.1, fun i => -σ i * p.2 i)

def endpointFieldProduct (a e : ℝ) (p : Model m) : Model m :=
  (endpointFieldCoordinate a e p.1, p.2)

theorem fderiv_endpointFieldProduct_cubic (σ : Fin m → ℝ) (a : ℝ)
    {e : ℝ} (he : e ^ 2 = 1) {p : Model m} (hp : p.1 ∈ endpointFieldDomain a e) :
    fderiv ℝ (endpointFieldProduct a e) p (cubicDescent σ (-(a ^ 2)) p) =
      endpointLinearField σ a e (endpointFieldProduct a e p) := by
  have hd := ((hasDerivAt_endpointFieldCoordinate a he hp).comp_hasFDerivAt p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (endpointFieldProduct a e) _ p at hd
  rw [hd.fderiv]
  apply Prod.ext
  · change (2 * a / (a + e * p.1) ^ 2) * (-(p.1 ^ 2 + -(a ^ 2))) =
      (-2 * e * a) * endpointFieldCoordinate a e p.1
    have hh := endpointFieldCoordinate_pushforward a he hp
    rw [(hasDerivAt_endpointFieldCoordinate a he hp).deriv] at hh
    convert! hh using 1 <;> ring
  · rfl

/-- The actual product coordinate chart conjugates the fields on its entire source. -/
theorem exists_endpoint_field_product_chart (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {e : ℝ} (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) = 0 ∧
      (P : Model m → Model m) = endpointFieldProduct a e ∧
      ∀ p ∈ P.source, fderiv ℝ P p (cubicDescent σ (-(a ^ 2)) p) =
        endpointLinearField σ a e (P p) := by
  obtain ⟨Q, hq, hsub, hQ, hzero⟩ := exists_endpoint_field_scalar_chart ha he
  let P := scalarProductChart (V := Fin m → ℝ) Q
  have hP : (P : Model m → Model m) = endpointFieldProduct a e := by
    funext p
    exact Prod.ext (congrFun hQ p.1) rfl
  refine ⟨P, ⟨hq, mem_univ _⟩, ?_, hP, ?_⟩
  · rw [hP]
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  · intro p hp
    rw [hP]
    exact fderiv_endpointFieldProduct_cubic σ a he (hsub hp.1)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
