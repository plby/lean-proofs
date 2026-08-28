import Wikipedia.HopfProblem.DegreeCollapseSmallScalarGerm
import Wikipedia.HopfProblem.DegreeCollapseBoundedStepProfile

/-!
# A supported transverse phase germ gives an actual smooth time change

The time change is identity on the left and a prescribed small
transverse-dependent translation on the right. Its time derivative stays
above one half, and its global smooth inverse is proved. Only the time
derivative changes in the middle slab; the right-hand phase is retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Construct an invertible smooth time change with the original phase
germ on the right, identity on the left, and the whole axis fixed. -/
theorem exists_supported_phase_clock {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (g : E → ℝ) (τ : ℝ → ℝ)
      (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞),
      IsCompact K ∧ K ⊆ U ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ K ∧
      g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧ (∀ x, |g x| < 1 / 12) ∧
      ContDiff ℝ ∞ τ ∧ (∀ t, τ t ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, D p = (p.1 + τ p.1 * g p.2, p.2)) ∧
      (∀ s, D (s, 0) = (s, 0)) ∧
      (∀ p, p.1 ≤ 1 / 3 → D p = p) ∧
      (∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) ∧
      ∀ p, 1 / 2 < fderiv ℝ (fun q => (D q).1) p (1, 0) := by
  obtain ⟨τ, L, hτ, hL, hrange, hleft, hright, -, hder⟩ := exists_bounded_step_profile
  let ε : ℝ := min (1 / 12) (1 / (2 * L))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨K, g, hK, hKU, hg, hsupp, hgerm, hg0, hsmall⟩ :=
    exists_small_supported_scalar_germ hv hv0 hU h0U hε
  let u (p : ℝ × E) := τ p.1 * g p.2
  have hu : ContDiff ℝ ∞ u := (hτ.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hbound (p : ℝ × E) : |u p| ≤ ε := by
    change |τ p.1 * g p.2| ≤ ε
    rw [abs_mul, abs_of_nonneg (hrange p.1).1]
    exact (mul_le_of_le_one_left (abs_nonneg (g p.2)) (hrange p.1).2).trans (hsmall p.2).le
  have hrate (p : ℝ × E) :
      fderiv ℝ (displacedHeight u) p (1, 0) = 1 + deriv τ p.1 * g p.2 := by
    have ha := (scalar_derivative (contDiff_displacedHeight hu) p.1 p.2).deriv
    have hb := ((hasDerivAt_id p.1).add
      ((hτ.differentiable (by simp) p.1).hasDerivAt.mul_const (g p.2))).deriv
    exact ha.symm.trans hb
  have hsmall' (p : ℝ × E) : |deriv τ p.1 * g p.2| < 1 / 2 := by
    rw [abs_mul]
    calc
      |deriv τ p.1| * |g p.2| ≤ L * |g p.2| :=
        mul_le_mul_of_nonneg_right (hder _) (abs_nonneg _)
      _ < L * ε := mul_lt_mul_of_pos_left (hsmall _) hL
      _ ≤ L * (1 / (2 * L)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le
      _ = 1 / 2 := by field_simp
  have hpositive (p : ℝ × E) : 1 / 2 < fderiv ℝ (displacedHeight u) p (1, 0) := by
    rw [hrate]
    linarith [(abs_lt.mp (hsmall' p)).1]
  have hpos (p : ℝ × E) : 0 < fderiv ℝ (displacedHeight u) p (1, 0) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans (hpositive p)
  have hF := contDiff_displacedHeight hu
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞
      (heightMap (displacedHeight u)) := fun p => heightMap_localDiffeomorph hF (hpos p).ne'
  let D := hlocal.diffeomorphOfBijective
    ⟨heightMap_injective_of_positive hF hpos,
      heightMap_surjective_of_bounded hu.continuous ε hε.le hbound⟩
  have hD (p : ℝ × E) : D p = (p.1 + τ p.1 * g p.2, p.2) := rfl
  refine ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0,
    fun x => (hsmall x).trans_le (min_le_left _ _), hτ, hrange, hD, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hD, hg0, mul_zero, add_zero]
  · intro p hp
    rw [hD, hleft p.1 hp, zero_mul, add_zero]
  · intro p hp
    rw [hD, hright p.1 hp, one_mul]
  · exact hpositive

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
