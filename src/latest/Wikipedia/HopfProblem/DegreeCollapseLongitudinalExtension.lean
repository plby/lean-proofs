import Wikipedia.HopfProblem.DegreeCollapseLongitudinalDiffeomorph
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Extending a small transverse neighborhood to a global longitudinal diffeomorphism

A smooth displacement vanishing on the center axis and supported in a
compact scalar interval has zero longitudinal derivative on that axis.
Uniform compact control and a transverse cutoff preserve positive scalar
derivative. The resulting actual global diffeomorphism agrees with the
original displacement on a uniform tube and retains every zero germ.
-/

noncomputable section

open Set Filter Function Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

open Wikipedia.SmoothSixDPoincare

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- A displacement fixing the whole axis has zero scalar derivative there. -/
theorem scalar_derivative_zero_axis {v : ℝ × V → ℝ} (hv : ContDiff ℝ ∞ v)
    (haxis : ∀ s, v (s, 0) = 0) (s : ℝ) : fderiv ℝ v (s, 0) (1, 0) = 0 := by
  have he : (fun t : ℝ => v (t, 0)) = fun _ => 0 := funext haxis
  have hd := (scalar_derivative hv s 0).deriv
  rw [he, deriv_const] at hd
  exact hd.symm

omit [FiniteDimensional ℝ V] in
theorem scalar_derivative_zero_outside {v : ℝ × V → ℝ} (hv : ContDiff ℝ ∞ v)
    {K : Set ℝ} (hK : IsClosed K) (hfix : ∀ p, p.1 ∉ K → v p = 0)
    {p : ℝ × V} (hp : p.1 ∉ K) : fderiv ℝ v p (1, 0) = 0 := by
  have he : (fun t : ℝ => v (t, p.2)) =ᶠ[𝓝 p.1] fun _ => 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hp] with t ht
    exact hfix (t, p.2) ht
  rw [← (scalar_derivative hv p.1 p.2).deriv, he.deriv_eq, deriv_const]

/-- The exact germ of a longitudinal correction extends to an actual
compactly supported diffeomorphism after shrinking only the transverse radius. -/
theorem exists_longitudinal_extension {v : ℝ × V → ℝ}
    (hv : ContDiff ℝ ∞ v) (haxis : ∀ s, v (s, 0) = 0)
    {K : Set ℝ} (hK : IsCompact K) (hfix : ∀ p, p.1 ∉ K → v p = 0) :
    ∃ (r : ℝ), 0 < r ∧
      ∃ D : (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V),
        (∀ p, ‖p.2‖ ≤ r → D p = (p.1 + v p, p.2)) ∧
        (∀ s, D (s, 0) = (s, 0)) ∧
        (∀ p, (D p).2 = p.2) ∧
        (∀ p, p.1 ∉ K → D p = p) ∧
        HasCompactSupport (fun p => D p - p) ∧
        (∀ p, v =ᶠ[𝓝 p] (fun _ => 0) → D =ᶠ[𝓝 p] id) := by
  let d (p : ℝ × V) := fderiv ℝ v p (1, 0)
  have hd : Continuous d :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hU : IsOpen {p : ℝ × V | |d p| < 1 / 2} :=
    isOpen_lt hd.abs continuous_const
  have hKU : K ×ˢ {(0 : V)} ⊆ {p : ℝ × V | |d p| < 1 / 2} := by
    rintro ⟨s, z⟩ ⟨_, hz⟩
    have hz' : z = 0 := hz
    subst z
    change |fderiv ℝ v (s, 0) (1, 0)| < 1 / 2
    rw [scalar_derivative_zero_axis hv haxis s]
    norm_num
  obtain ⟨R, hR, htube⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK hU hKU
  let β : ContDiffBump (0 : V) := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let u (p : ℝ × V) := β p.2 * v p
  have hu : ContDiff ℝ ∞ u := (β.contDiff.comp contDiff_snd).mul hv
  have hzero (p : ℝ × V) (hp : p ∉ K ×ˢ closedBall (0 : V) β.rOut) : u p = 0 := by
    by_cases hs : p.1 ∈ K
    · have hz : p.2 ∉ tsupport β := by
        rw [β.tsupport_eq]
        exact fun h => hp ⟨hs, h⟩
      simp only [u, image_eq_zero_of_notMem_tsupport hz, zero_mul]
    · simp only [u, hfix p hs, mul_zero]
  have hucompact : HasCompactSupport u :=
    HasCompactSupport.intro (hK.prod (isCompact_closedBall 0 β.rOut)) hzero
  have hrate (p : ℝ × V) :
      fderiv ℝ (displacedHeight u) p (1, 0) = 1 + β p.2 * d p := by
    have ha := (scalar_derivative (contDiff_displacedHeight hu) p.1 p.2).deriv
    have hb := ((hasDerivAt_id p.1).add
      ((scalar_derivative hv p.1 p.2).const_mul (β p.2))).deriv
    exact ha.symm.trans hb
  have hpos (p : ℝ × V) : 0 < fderiv ℝ (displacedHeight u) p (1, 0) := by
    rw [hrate]
    by_cases hz : β p.2 = 0
    · simp only [hz, zero_mul, add_zero, zero_lt_one]
    by_cases hs : p.1 ∈ K
    · have hzball : p.2 ∈ ball (0 : V) β.rOut := by
        rw [← β.support_eq]
        exact hz
      have hzR : p.2 ∈ closedBall (0 : V) R :=
        closedBall_subset_closedBall (by change R / 2 ≤ R; linarith)
          (ball_subset_closedBall hzball)
      have hsmall : |d p| < 1 / 2 := htube ⟨hs, hzR⟩
      have hmul : |β p.2 * d p| < 1 / 2 := by
        rw [abs_mul, abs_of_nonneg β.nonneg]
        exact (mul_le_of_le_one_left (abs_nonneg (d p)) β.le_one).trans_lt hsmall
      linarith [(abs_lt.mp hmul).1]
    · have hzeroD : d p = 0 := scalar_derivative_zero_outside hv hK.isClosed hfix hs
      simp only [hzeroD, mul_zero, add_zero, zero_lt_one]
  let D := longitudinalDiffeomorph hu hucompact hpos
  have hD (p : ℝ × V) : D p = (p.1 + u p, p.2) := rfl
  refine ⟨β.rIn, β.rIn_pos, D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hD]
    have hβ : β p.2 = 1 := β.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hp)
    simp only [u, hβ, one_mul]
  · intro s
    rw [hD]
    simp only [u, haxis, mul_zero, add_zero]
  · intro p
    rfl
  · intro p hp
    rw [hD]
    simp only [u, hfix p hp, mul_zero, add_zero, Prod.mk.eta]
  · apply HasCompactSupport.intro (hK.prod (isCompact_closedBall 0 β.rOut))
    intro p hp
    rw [hD, hzero p hp, add_zero]
    exact sub_self p
  · intro p hp
    filter_upwards [hp] with q hq
    rw [hD]
    simp only [u, hq, mul_zero, add_zero, id_eq, Prod.mk.eta]

end Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates
