/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedRenewalRow
import ErdosProblems.Erdos1165.ProfileAnnularRowRegular

/-!
# Profile specialization of the decorated-renewal row bound

This module exposes the two literal pieces left after deleting every
inner-to-middle return from one profile gap: the first inward hit and the
final escape.  The regular annular estimates bound both rows by the same
`(1 + n⁻⁶) / 2` factor.  Combined with
`sum_decoratedRenewalKernel_le_rowProduct`, an arbitrary recursively refined
child return can therefore be inserted once using only its row sum.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularDecoratedProfileRow

open AnnularDecoratedRenewalKernel AnnularDecoratedRenewalRow
open AnnularOffspringKernel AnnularOffspringKernelRadial
open AnnularProfileClocks AppendixFirstMoment
open MarkedBoundaryVisitKernel ProfileAnnularRowRegular RealDiscFinite
open ThickPoint

noncomputable section

/-- The retained inward piece of one erased profile child cycle. -/
def profileInwardKernelENNReal
    (n k : ℕ) (center : Point) :
    ProfileCycleMiddlePoint n k center →
      ProfileCycleInnerPoint n k center → ℝ≥0∞ :=
  fun u z ↦ skeletonExitKernel
    (profileInnerBoundary n (k + 1) center ∪
      profileOuterBoundary n k center) u.1 z.1

/-- The retained final middle-to-outer piece of one erased profile gap. -/
def profileEscapeKernelENNReal
    (n k : ℕ) (center : Point) :
    ProfileCycleMiddlePoint n k center →
      ProfileCycleOuterPoint n k center → ℝ≥0∞ :=
  annularEscapeKernel
    (profileOuterBoundary n k center)
    (profileInnerBoundary n (k + 1) center)
    (fun u : ProfileCycleMiddlePoint n k center ↦ u.1)
    (fun w : ProfileCycleOuterPoint n k center ↦ w.1)

theorem profileInwardKernelENNReal_ne_top
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center)
    (z : ProfileCycleInnerPoint n k center) :
    profileInwardKernelENNReal n k center u z ≠ ∞ :=
  measure_ne_top fairSteps _

theorem profileEscapeKernelENNReal_ne_top
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    profileEscapeKernelENNReal n k center u w ≠ ∞ :=
  measure_ne_top fairSteps _

/-- The real inward row is the already checked profile cycle row: the
omitted return has total mass one. -/
theorem sum_profileInwardKernelENNReal_toReal
    {n k : ℕ} {center : Point}
    (hmiddle : (profileInnerBoundary n k center).Nonempty)
    (u : ProfileCycleMiddlePoint n k center) :
    (∑ z, profileInwardKernelENNReal n k center u z).toReal =
      ∑ v, profileAnnularCycleKernelReal n k center u v := by
  rw [ENNReal.toReal_sum]
  · exact (sum_profileAnnularCycleKernelReal_eq_inwardRow hmiddle u).symm
  · intro z _
    exact profileInwardKernelENNReal_ne_top n k center u z

/-- The real escape row is definitionally the endpoint-integrated profile
escape row. -/
theorem sum_profileEscapeKernelENNReal_toReal
    {n k : ℕ} {center : Point}
    (u : ProfileCycleMiddlePoint n k center) :
    (∑ w, profileEscapeKernelENNReal n k center u w).toReal =
      profileAnnularEscapeRowReal n k center u := by
  rw [ENNReal.toReal_sum]
  · rfl
  · intro w _
    exact profileEscapeKernelENNReal_ne_top n k center u w

/-- Eventually both literal pieces of every regular profile gap have row
mass at most `(1 + n⁻⁶) / 2`. -/
theorem eventually_profileErasedPieceRows_le_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (center : Point) (u : ProfileCycleMiddlePoint n k center),
        ∑ z, profileInwardKernelENNReal n k center u z ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2) ∧
          ∑ w, profileEscapeKernelENNReal n k center u w ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2) := by
  filter_upwards [eventually_profileRegularRowError_le_inv_pow_six,
      eventually_ge_atTop 2] with n herror hn
  intro k hk0 hk center u
  obtain ⟨hinner, hmiddle, houter, hInnerSep, hOuterSep,
      _hdelta, _hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  have hmiddleNonempty : (profileInnerBoundary n k center).Nonempty := by
    unfold profileInnerBoundary
    exact discBoundary_center_nonempty_of_nonneg center (by linarith)
  have houterNonempty : (profileOuterBoundary n k center).Nonempty := by
    unfold profileOuterBoundary
    exact discBoundary_center_nonempty_of_nonneg center (by linarith)
  let rowError := LiteralRealAnnulusRadialExit.literalRealAnnulusRowError
    (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
  have hcycle := sum_profileAnnularCycleKernelReal_half_bounds_regular
    hn hk0 hk u
  have hrenew := profileAnnularCycle_escape_isStochasticRenewalRow
    houterNonempty (by linarith) hOuterSep u
  have hrowError : rowError ≤ 1 / (n : ℝ) ^ 6 := herror k hk0 hk
  have hinwardReal :
      (∑ z, profileInwardKernelENNReal n k center u z).toReal ≤
        (1 + 1 / (n : ℝ) ^ 6) / 2 := by
    rw [sum_profileInwardKernelENNReal_toReal hmiddleNonempty u]
    exact hcycle.2.trans (by linarith)
  have hescapeReal :
      (∑ w, profileEscapeKernelENNReal n k center u w).toReal ≤
        (1 + 1 / (n : ℝ) ^ 6) / 2 := by
    rw [sum_profileEscapeKernelENNReal_toReal]
    linarith [hcycle.1]
  have hupper0 : 0 ≤ (1 + 1 / (n : ℝ) ^ 6) / 2 := by positivity
  constructor
  · apply (ENNReal.toReal_le_toReal
      (ENNReal.sum_ne_top.mpr fun z _ ↦
        profileInwardKernelENNReal_ne_top n k center u z)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hupper0] using hinwardReal
  · apply (ENNReal.toReal_le_toReal
      (ENNReal.sum_ne_top.mpr fun w _ ↦
        profileEscapeKernelENNReal_ne_top n k center u w)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hupper0] using hescapeReal

/-- A one-gap recursive profile row.  `childKernel child` is the actual
refined inner-to-middle return for one deleted child; it may be zero at
arbitrary endpoints. -/
def profileDecoratedGapKernelENNReal
    {Child : Type*} (n k : ℕ) (center : Point)
    (childKernel : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → ℝ≥0∞) :
    List Child → ProfileCycleMiddlePoint n k center →
      ProfileCycleOuterPoint n k center → ℝ≥0∞ :=
  decoratedRenewalKernel
    (profileInwardKernelENNReal n k center) childKernel
    (profileEscapeKernelENNReal n k center)

/-- Profile-specific recursive row upper.  Every child contributes only its
own row cost; the remaining factor is exactly one half-row for each inward
hit and one half-row for the final escape. -/
theorem eventually_profileDecoratedGapKernel_row_le :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (center : Point) (Child : Type*)
        (childKernel : Child → ProfileCycleInnerPoint n k center →
          ProfileCycleMiddlePoint n k center → ℝ≥0∞)
        (childUpper : Child → ℝ≥0∞)
        (hchild : ∀ child z, ∑ v, childKernel child z v ≤ childUpper child)
        (children : List Child) (u : ProfileCycleMiddlePoint n k center),
        ∑ w, profileDecoratedGapKernelENNReal n k center childKernel
            children u w ≤
          (children.map childUpper).prod *
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2) ^
              (children.length + 1) := by
  filter_upwards [eventually_profileErasedPieceRows_le_inv_pow_six]
      with n hrows
  intro k hk0 hk center Child childKernel childUpper hchild children u
  have h := sum_decoratedRenewalKernel_le_rowProduct
    (profileInwardKernelENNReal n k center) childKernel
    (profileEscapeKernelENNReal n k center)
    (ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2))
    (ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2))
    childUpper (fun u ↦ (hrows k hk0 hk center u).1) hchild
    (fun u ↦ (hrows k hk0 hk center u).2) children u
  simpa only [profileDecoratedGapKernelENNReal, pow_succ, mul_assoc] using h

private theorem list_prod_map_ofReal
    {Child : Type*} (cost : Child → ℝ)
    (hcost : ∀ child, 0 ≤ cost child) :
    ∀ children : List Child,
      (children.map fun child ↦ ENNReal.ofReal (cost child)).prod =
        ENNReal.ofReal ((children.map cost).prod)
  | [] => by simp
  | child :: children => by
      simp only [List.map_cons, List.prod_cons, list_prod_map_ofReal cost hcost]
      rw [ENNReal.ofReal_mul (hcost child)]

theorem halfRow_pow_eq_one_add_pow_mul_halfGeometricMass
    (epsilon : ℝ) (q : ℕ) :
    ((1 + epsilon) / 2) ^ (q + 1) =
      (1 + epsilon) ^ (q + 1) * halfGeometricMass q := by
  unfold halfGeometricMass
  simp only [div_eq_mul_inv, one_mul, mul_pow]

/-- Real-reference form of the recursive one-gap estimate.  This is the
form that composes along a fixed profile tree and ultimately feeds the
canonical `exp 1` radial-tail certificate. -/
theorem eventually_profileDecoratedGapKernel_row_le_ofReal :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (center : Point) (Child : Type*)
        (childKernel : Child → ProfileCycleInnerPoint n k center →
          ProfileCycleMiddlePoint n k center → ℝ≥0∞)
        (childCost : Child → ℝ)
        (hchildCost : ∀ child, 0 ≤ childCost child)
        (hchild : ∀ child z, ∑ v, childKernel child z v ≤
          ENNReal.ofReal (childCost child))
        (children : List Child) (u : ProfileCycleMiddlePoint n k center),
        ∑ w, profileDecoratedGapKernelENNReal n k center childKernel
            children u w ≤
          ENNReal.ofReal
            ((children.map childCost).prod *
              (1 + 1 / (n : ℝ) ^ 6) ^ (children.length + 1) *
                halfGeometricMass children.length) := by
  filter_upwards [eventually_profileDecoratedGapKernel_row_le]
      with n hrow
  intro k hk0 hk center Child childKernel childCost hchildCost hchild
    children u
  have h := hrow k hk0 hk center Child childKernel
    (fun child ↦ ENNReal.ofReal (childCost child)) hchild children u
  have hhalf0 : 0 ≤ (1 + 1 / (n : ℝ) ^ 6) / 2 := by positivity
  have hprod0 : 0 ≤ (children.map childCost).prod := by
    apply List.prod_nonneg
    intro value hvalue
    obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hvalue
    exact hchildCost child
  calc
    ∑ w, profileDecoratedGapKernelENNReal n k center childKernel
          children u w ≤
        (children.map fun child ↦ ENNReal.ofReal (childCost child)).prod *
          ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 6) / 2) ^
            (children.length + 1) := h
    _ = ENNReal.ofReal
          ((children.map childCost).prod *
            ((1 + 1 / (n : ℝ) ^ 6) / 2) ^
              (children.length + 1)) := by
      rw [list_prod_map_ofReal childCost hchildCost,
        ← ENNReal.ofReal_pow hhalf0]
      rw [ENNReal.ofReal_mul hprod0]
    _ = ENNReal.ofReal
          ((children.map childCost).prod *
            (1 + 1 / (n : ℝ) ^ 6) ^ (children.length + 1) *
              halfGeometricMass children.length) := by
      congr 1
      rw [halfRow_pow_eq_one_add_pow_mul_halfGeometricMass]
      ring

end

end Erdos1165.AnnularDecoratedProfileRow
