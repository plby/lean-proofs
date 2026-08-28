import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalDomain

/-!
# The two cyclic sectors for the actual triangle action

Doubling the half-Ford triangle across its circular side gives the
intersection of two explicit cyclic sectors.  The excluded sectors lie
on opposite sides of `Re z = -1`; this separation will allow the normal
form in `C₃ * C₄` to prove genuine disjointness of translates.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The open fundamental sector at the order-three vertex. -/
def firstSector : Set ℍ := {z | z.re < -(1 / 2) ∧ 1 < ‖(z : ℂ)‖}

/-- The open fundamental sector at the order-four vertex. -/
def secondSector : Set ℍ :=
  {z | stripLeft < z.re ∧ stripRight < ‖(z : ℂ) - (stripLeft : ℂ)‖}

/-- The open complement of the closed first sector. -/
def firstExcluded : Set ℍ := {z | -(1 / 2) < z.re ∨ ‖(z : ℂ)‖ < 1}

/-- The open complement of the closed second sector. -/
def secondExcluded : Set ℍ :=
  {z | z.re < stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ < stripRight}

/-- The open polygon obtained by doubling across the circular side. -/
def circularDoubleInterior : Set ℍ := firstSector ∩ secondSector

theorem stripLeft_add_stripRight : stripLeft + stripRight = -1 := by
  unfold stripLeft stripRight
  ring

theorem stripLeft_lt_neg_one : stripLeft < -1 := by
  linarith [stripLeft_add_stripRight, stripRight_pos]

theorem firstExcluded_subset_pingPongOne : firstExcluded ⊆ pingPongOne := by
  intro z hz
  rcases hz with hx | hn
  · change -1 < z.re
    linarith
  · have hr := Complex.re_le_norm (-(z : ℂ))
    simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
    change -1 < z.re
    linarith

theorem secondExcluded_subset_pingPongTwo : secondExcluded ⊆ pingPongTwo := by
  intro z hz
  rcases hz with hx | hn
  · exact hx.trans stripLeft_lt_neg_one
  · have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
    change z.re < -1
    linarith [stripLeft_add_stripRight]

theorem pingPongTwo_subset_firstSector : pingPongTwo ⊆ firstSector := by
  intro z hz
  change z.re < -1 at hz
  refine ⟨by linarith, ?_⟩
  have hr := Complex.re_le_norm (-(z : ℂ))
  simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
  linarith

theorem pingPongOne_subset_secondSector : pingPongOne ⊆ secondSector := by
  intro z hz
  change -1 < z.re at hz
  refine ⟨stripLeft_lt_neg_one.trans hz, ?_⟩
  have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
  simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
  linarith [stripLeft_add_stripRight]

theorem secondExcluded_subset_firstSector : secondExcluded ⊆ firstSector :=
  secondExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

theorem firstExcluded_subset_secondSector : firstExcluded ⊆ secondSector :=
  firstExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

theorem excluded_disjoint : Disjoint firstExcluded secondExcluded :=
  pingPong_disjoint.mono firstExcluded_subset_pingPongOne secondExcluded_subset_pingPongTwo

theorem circularDoubleInterior_disjoint_firstExcluded :
    Disjoint circularDoubleInterior firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.1.1 hx
  · exact lt_asymm hz.1.2 hn

theorem circularDoubleInterior_disjoint_secondExcluded :
    Disjoint circularDoubleInterior secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.2.1 hx
  · exact lt_asymm hz.2.2 hn

theorem circularDoubleInterior_isOpen : IsOpen circularDoubleInterior := by
  apply IsOpen.inter
  · exact (isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt continuous_const continuous_coe.norm)
  · exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const ((continuous_coe.sub continuous_const).norm))

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
