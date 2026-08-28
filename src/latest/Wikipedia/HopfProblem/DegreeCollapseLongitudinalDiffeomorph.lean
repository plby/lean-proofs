import Wikipedia.HopfProblem.DegreeCollapseRegularHeightCoordinates
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Global smooth coordinate changes preserving transverse coordinates

A compactly supported scalar displacement with positive longitudinal
derivative gives a genuine global diffeomorphism. Each scalar fiber map is
strictly increasing and surjective by the intermediate value theorem.
The triangular differential supplies smooth local inverses everywhere.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def displacedHeight (u : ℝ × V → ℝ) (p : ℝ × V) : ℝ := p.1 + u p

theorem contDiff_displacedHeight {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (displacedHeight u) := contDiff_fst.add hu

theorem scalar_derivative {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t : ℝ => F (t, z)) (fderiv ℝ F (s, z) (1, 0)) s :=
  ((hF.differentiable (by simp) (s, z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

/-- Positivity in the one moving coordinate is enough for global injectivity. -/
theorem heightMap_injective_of_positive {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ p, 0 < fderiv ℝ F p (1, 0)) : Injective (heightMap F) := by
  have hmono (z : V) : StrictMono (fun s : ℝ => F (s, z)) :=
    strictMono_of_deriv_pos (fun s => by rw [(scalar_derivative hF s z).deriv]; exact hpos _)
  rintro ⟨s, z⟩ ⟨t, w⟩ he
  have hzw : z = w := congrArg Prod.snd he
  subst w
  have hst : s = t := (hmono z).injective (congrArg Prod.fst he)
  exact Prod.ext hst rfl

omit [NormedSpace ℝ V] in
/-- A bounded continuous displacement reaches every value on each scalar fiber. -/
theorem heightMap_surjective_of_bounded {u : ℝ × V → ℝ} (hu : Continuous u)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ p, |u p| ≤ C) :
    Surjective (heightMap (displacedHeight u)) := by
  rintro ⟨r, z⟩
  let a := r - (C + 1)
  let b := r + (C + 1)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hs : Continuous (fun s : ℝ => displacedHeight u (s, z)) :=
    continuous_id.add (hu.comp (continuous_id.prodMk continuous_const))
  have hlo : displacedHeight u (a, z) ≤ r := by
    have h := (abs_le.mp (hbound (a, z))).2
    dsimp [displacedHeight, a] at *
    linarith
  have hhi : r ≤ displacedHeight u (b, z) := by
    have h := (abs_le.mp (hbound (b, z))).1
    dsimp [displacedHeight, b] at *
    linarith
  obtain ⟨s, _, he⟩ := intermediate_value_Icc hab hs.continuousOn ⟨hlo, hhi⟩
  exact ⟨(s, z), Prod.ext he rfl⟩

theorem heightMap_surjective_of_compactSupport {u : ℝ × V → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Surjective (heightMap (displacedHeight u)) := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hu.continuous).isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ ⟨0, rfl⟩)
  exact heightMap_surjective_of_bounded hu.continuous C hC0
    (fun p => by simpa only [Real.norm_eq_abs] using hC _ ⟨p, rfl⟩)

variable [FiniteDimensional ℝ V]

/-- The coordinate change has a proved global smooth inverse. -/
def longitudinalDiffeomorph {u : ℝ × V → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) :
    (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V) := by
  have hs := contDiff_displacedHeight hu
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞
      (heightMap (displacedHeight u)) := fun p => heightMap_localDiffeomorph hs (hpos p).ne'
  exact hloc.diffeomorphOfBijective
    ⟨heightMap_injective_of_positive hs hpos, heightMap_surjective_of_compactSupport hu hc⟩

theorem longitudinalDiffeomorph_apply {u : ℝ × V → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) (p : ℝ × V) :
    longitudinalDiffeomorph hu hc hpos p = (p.1 + u p, p.2) := rfl

theorem longitudinalDiffeomorph_fixed {u : ℝ × V → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0))
    {p : ℝ × V} (hp : p ∉ tsupport u) : longitudinalDiffeomorph hu hc hpos p = p := by
  rw [longitudinalDiffeomorph_apply, image_eq_zero_of_notMem_tsupport hp, add_zero]

end Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates
