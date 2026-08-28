import Wikipedia.HopfProblem.OrbitPairSphereNonantipodalEnergy
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual first variation of squared spherical angle

The logarithm vector is the familiar arccos coefficient times the tangent
projection of the endpoint. At a repeated endpoint it is zero. The first
variation formula is proved by differentiating arccos off the diagonal and
by native smoothness and the local minimum property on the diagonal.
Thus the formula includes zero-length edges; no differentiability of
arccos at one is asserted or used.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereAngle

open NoExoticSixSphere GLOrthonormalization SpherePairedGeodesic

def factor (c : ℝ) : ℝ := Real.arccos c / Real.sqrt (1 - c ^ 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logVector (x y : E) : E := factor (inner ℝ x y) • (y - inner ℝ x y • x)

theorem logVector_diagonal {x : E} (hx : ‖x‖ = 1) : logVector x x = 0 := by
  rw [logVector, real_inner_self_eq_norm_sq, hx, one_pow, one_smul, sub_self, smul_zero]

theorem inner_logVector {x : E} (hx : ‖x‖ = 1) (y : E) :
    inner ℝ x (logVector x y) = 0 := by
  simp only [logVector, real_inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, hx, one_pow, mul_one, sub_self, mul_zero]

theorem pairing_logVector {x v : E} (hv : inner ℝ x v = 0) (y : E) :
    inner ℝ v (logVector x y) = factor (inner ℝ x y) * inner ℝ v y := by
  have hv' : inner ℝ v x = 0 := by rw [real_inner_comm]; exact hv
  simp only [logVector, real_inner_smul_right, inner_sub_right,
    hv', mul_zero, sub_zero]

theorem inner_derivative_of_unit {a : ℝ → E} {a' : E} {s : ℝ}
    (ha : HasDerivAt a a' s) (hunit : ∀ t, ‖a t‖ = 1) : inner ℝ (a s) a' = 0 := by
  have hd := ha.norm_sq
  have he : (fun t => ‖a t‖ ^ 2) = (fun _ : ℝ => (1 : ℝ)) := by
    funext t
    rw [hunit t, one_pow]
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const s (1 : ℝ))
  linarith

theorem hasDerivAt_angle_sq {a b : ℝ → E} {a' b' : E} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s)
    (hlo : -1 < inner ℝ (a s) (b s)) (hhi : inner ℝ (a s) (b s) < 1) :
    HasDerivAt (fun t => Real.arccos (inner ℝ (a t) (b t)) ^ 2)
      (-2 * factor (inner ℝ (a s) (b s)) *
        (inner ℝ (a s) b' + inner ℝ a' (b s))) s := by
  have hd := ((Real.hasDerivAt_arccos (ne_of_gt hlo) (ne_of_lt hhi)).comp s
    (ha.inner ℝ hb)).pow 2
  convert! hd using 1
  simp only [factor, Function.comp_apply, Nat.reduceSub, pow_one]
  ring

section NativeSphere

variable {n : ℕ} {a b : ℝ → Sphere n} {s : ℝ}

theorem hasDerivAt_sphereCost_diagonal
    (ha : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ a s)
    (hb : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ b s) (he : a s = b s) :
    HasDerivAt (fun t => sphereCost n (a t, b t)) 0 s := by
  have hmem : (a s, b s) ∈ nonantipodal n := by
    rw [he]
    exact diagonal_mem_nonantipodal (b s)
  have hc : ContDiffAt ℝ ∞ (fun t => sphereCost n (a t, b t)) s :=
    (ContMDiffAt.comp (g := sphereCost n) (f := fun t => (a t, b t)) s
      (contMDiffAt_sphereCost_of_nonantipodal _ hmem) (ha.prodMk hb)).contDiffAt
  have hzero : sphereCost n (a s, b s) = 0 := by
    rw [he, sphereCost_diagonal]
  have hmin : IsLocalMin (fun t => sphereCost n (a t, b t)) s :=
    Filter.Eventually.of_forall (fun t => by
      change sphereCost n (a s, b s) ≤ sphereCost n (a t, b t)
      rw [hzero]
      exact sphereCost_nonneg _)
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  rw [hmin.deriv_eq_zero] at hd
  exact hd

theorem hasDerivAt_sphereCost
    (ha : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ a s)
    (hb : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ b s)
    {a' b' : Vector (n + 1)}
    (hda : HasDerivAt (fun t => (a t).val) a' s)
    (hdb : HasDerivAt (fun t => (b t).val) b' s)
    (hmem : (a s, b s) ∈ nonantipodal n) :
    HasDerivAt (fun t => sphereCost n (a t, b t))
      (-2 * (inner ℝ a' (logVector (a s).val (b s).val) +
        inner ℝ b' (logVector (b s).val (a s).val))) s := by
  by_cases he : a s = b s
  · have hd := hasDerivAt_sphereCost_diagonal ha hb he
    simpa only [he, logVector_diagonal (ClosedHemisphere.unit_norm (b s)),
      inner_zero_right, add_zero, mul_zero] using hd
  · have hne : (a s).val ≠ (b s).val := fun h => he (Subtype.ext h)
    have hhi : inner ℝ (a s).val (b s).val < 1 :=
      (inner_lt_one_iff_real_of_norm_eq_one (ClosedHemisphere.unit_norm (a s))
        (ClosedHemisphere.unit_norm (b s))).mpr hne
    have hd := hasDerivAt_angle_sq hda hdb hmem hhi
    have horthA := inner_derivative_of_unit hda (fun t => ClosedHemisphere.unit_norm (a t))
    have horthB := inner_derivative_of_unit hdb (fun t => ClosedHemisphere.unit_norm (b t))
    have hcomm : inner ℝ (b s).val (a s).val = inner ℝ (a s).val (b s).val :=
      real_inner_comm _ _
    have hcomm' : inner ℝ b' (a s).val = inner ℝ (a s).val b' := real_inner_comm _ _
    rw [pairing_logVector horthA, pairing_logVector horthB, hcomm, hcomm']
    convert! hd using 1 <;> ring

end NativeSphere

end Wikipedia.HopfProblem.OrbitPair.SphereAngle
