/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Basic
import ErdosProblems.Erdos957.Angle

/-!
# Exact local geometry for Erdős 957

This module records algebraic pieces of the planar unit-distance geometry used in the
charging argument.  We use `ℂ` as a concrete copy of the Euclidean plane.  Squared distances
are expressed with `Complex.normSq`; this removes square roots from all coordinate calculations.
-/

open InnerProductGeometry Set
open scoped BigOperators ComplexConjugate RealInnerProductSpace

namespace Erdos957Hex

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact equality case in the elementary angular-separation estimate: two unit vectors at
unit distance have real inner product `1 / 2`. -/
lemma inner_eq_half_of_unit_norm_of_unit_sub {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    ⟪x, y⟫ = (1 / 2 : ℝ) := by
  have h := norm_sub_sq_real x y
  rw [hx, hy, hxy] at h
  norm_num at h ⊢
  linarith

/-- The weak form used for packing: unit vectors at distance at least one have angle at least
`pi / 3`. -/
lemma pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : 1 ≤ ‖x - y‖) :
    Real.pi / 3 ≤ angle x y := by
  have hsq : 1 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y)]
  have hinner : ⟪x, y⟫ ≤ (1 / 2 : ℝ) := by
    rw [norm_sub_sq_real, hx, hy] at hsq
    norm_num at hsq ⊢
    linarith
  rw [angle, hx, hy]
  norm_num
  calc
    Real.pi / 3 = Real.arccos (Real.cos (Real.pi / 3)) := by
      rw [Real.arccos_cos] <;> nlinarith [Real.pi_pos]
    _ ≤ Real.arccos ⟪x, y⟫ := Real.arccos_le_arccos (by
      simpa only [Real.cos_pi_div_three] using hinner)

/-- For the same equilateral pair, the long diagonal `x + y` has squared norm three. -/
lemma norm_add_sq_eq_three_of_unit_norm_of_unit_sub {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    ‖x + y‖ ^ 2 = 3 := by
  have hi := inner_eq_half_of_unit_norm_of_unit_sub hx hy hxy
  rw [norm_add_sq_real, hx, hy, hi]
  norm_num

/-- If two unit vectors attain the minimum allowed distance one, then their difference is itself
a unit vector.  Its scalar products with the two original vectors are `1/2` and `-1/2`. -/
lemma equilateral_difference_inner {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    ⟪x, x - y⟫ = (1 / 2 : ℝ) ∧
      ⟪y, x - y⟫ = (-1 / 2 : ℝ) := by
  have hi := inner_eq_half_of_unit_norm_of_unit_sub hx hy hxy
  constructor
  · rw [inner_sub_right, real_inner_self_eq_norm_sq, hx, hi]
    norm_num
  · have hyx : ⟪y, x⟫ = (1 / 2 : ℝ) := by
      rw [real_inner_comm]
      exact hi
    rw [inner_sub_right, hyx, real_inner_self_eq_norm_sq, hy]
    norm_num

end InnerProduct

section SixGaps

/-- Six circular gaps of at least `π / 3` whose sum is one full turn are all exactly `π / 3`.
This is the numerical equality case behind the regular-hexagon rigidity theorem. -/
lemma six_gaps_eq_pi_div_three (g : Fin 6 → ℝ)
    (hg : ∀ i, Real.pi / 3 ≤ g i)
    (hsum : ∑ i, g i = 2 * Real.pi) :
    ∀ i, g i = Real.pi / 3 := by
  intro i
  have hrest :
      ∑ j ∈ (Finset.univ.erase i), Real.pi / 3 ≤
        ∑ j ∈ (Finset.univ.erase i), g j := by
    exact Finset.sum_le_sum fun j _ ↦ hg j
  have hcard : (Finset.univ.erase i).card = 5 := by simp
  have hsplit : g i + ∑ j ∈ (Finset.univ.erase i), g j = 2 * Real.pi := by
    rw [← hsum, Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)]
  have hconst : ∑ _j ∈ (Finset.univ.erase i), Real.pi / 3 =
      5 * (Real.pi / 3) := by simp [hcard]
  have hle : g i ≤ Real.pi / 3 := by
    rw [hconst] at hrest
    nlinarith
  exact le_antisymm hle (hg i)

end SixGaps

section SupportingHalfPlane

/-- Four angular bins partition the closed upper semicircle.  The fourth bin consists only of
the negative real endpoint when the input is constrained to the upper semicircle. -/
noncomputable def upperPhaseBin (z : ℂ) : Fin 4 :=
  ⟨⌊max 0 (3 * z.arg / Real.pi)⌋₊, by
    apply (Nat.floor_lt (le_max_left _ _)).2
    rw [max_lt_iff]
    constructor
    · norm_num
    · rw [div_lt_iff₀ Real.pi_pos]
      have h := mul_le_mul_of_nonneg_left (Complex.arg_le_pi z)
        (by norm_num : (0 : ℝ) ≤ 3)
      calc
        3 * z.arg ≤ 3 * Real.pi := h
        _ < 4 * Real.pi := by nlinarith [Real.pi_pos]⟩

private lemma upper_phase_nonneg {z : ℂ} (him : 0 ≤ z.im) :
    0 ≤ 3 * z.arg / Real.pi := by
  have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.2 him
  positivity

/-- Points in the same upper-semicircle bin have arguments differing by less than `pi / 3`. -/
lemma abs_arg_sub_lt_pi_div_three_of_upperPhaseBin_eq {x y : ℂ}
    (hxim : 0 ≤ x.im) (hyim : 0 ≤ y.im)
    (hbin : upperPhaseBin x = upperPhaseBin y) :
    |x.arg - y.arg| < Real.pi / 3 := by
  let tx : ℝ := 3 * x.arg / Real.pi
  let ty : ℝ := 3 * y.arg / Real.pi
  have htx0 : 0 ≤ tx := upper_phase_nonneg hxim
  have hty0 : 0 ≤ ty := upper_phase_nonneg hyim
  have hfloor : ⌊tx⌋₊ = ⌊ty⌋₊ := by
    simpa [upperPhaseBin, tx, ty, max_eq_right htx0, max_eq_right hty0] using
      congrArg Fin.val hbin
  have hxy : tx < ty + 1 := by
    calc
      tx < (⌊tx⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one tx
      _ = (⌊ty⌋₊ : ℝ) + 1 := by rw [hfloor]
      _ ≤ ty + 1 := by simpa [add_comm] using add_le_add_right (Nat.floor_le hty0) 1
  have hyx : ty < tx + 1 := by
    calc
      ty < (⌊ty⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ty
      _ = (⌊tx⌋₊ : ℝ) + 1 := by rw [hfloor]
      _ ≤ tx + 1 := by simpa [add_comm] using add_le_add_right (Nat.floor_le htx0) 1
  have hupper : x.arg - y.arg < Real.pi / 3 := by
    dsimp [tx, ty] at hxy hyx
    have hxy' := (div_lt_iff₀ Real.pi_pos).mp hxy
    field_simp at hxy'
    nlinarith
  have hyx' : y.arg - x.arg < Real.pi / 3 := by
    dsimp [tx, ty] at hxy hyx
    have hyx'' := (div_lt_iff₀ Real.pi_pos).mp hyx
    field_simp at hyx''
    nlinarith
  have hlower : -(Real.pi / 3) < x.arg - y.arg := by linarith
  exact abs_lt.2 ⟨hlower, hupper⟩

/-- On the closed upper semicircle, two arguments in the same bin differ by the unoriented
Euclidean angle. -/
lemma angle_eq_abs_arg_sub_of_upperPhaseBin_eq {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxim : 0 ≤ x.im) (hyim : 0 ≤ y.im)
    (hbin : upperPhaseBin x = upperPhaseBin y) :
    angle x y = |x.arg - y.arg| := by
  have hclose := abs_arg_sub_lt_pi_div_three_of_upperPhaseBin_eq hxim hyim hbin
  have hdiff : x.arg - y.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [mem_Ioc]
    have hthird : Real.pi / 3 < Real.pi := by nlinarith [Real.pi_pos]
    have hlo : -(Real.pi / 3) < x.arg - y.arg := neg_lt_of_abs_lt hclose
    have hhi : x.arg - y.arg < Real.pi / 3 := lt_of_abs_lt hclose
    exact ⟨by linarith, (hhi.trans hthird).le⟩
  have hxexp : Complex.exp (x.arg * Complex.I) = x := by
    simpa [hx] using Complex.norm_mul_exp_arg_mul_I x
  have hyexp : Complex.exp (y.arg * Complex.I) = y := by
    simpa [hy] using Complex.norm_mul_exp_arg_mul_I y
  have hdiff' : x.arg - y.arg ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    simpa [two_mul] using hdiff
  calc
    angle x y = angle (Complex.exp (x.arg * Complex.I))
        (Complex.exp (y.arg * Complex.I)) := by rw [hxexp, hyexp]
    _ = |toIocMod Real.two_pi_pos (-Real.pi) (x.arg - y.arg)| :=
      Complex.angle_exp_exp x.arg y.arg
    _ = |x.arg - y.arg| := by rw [(toIocMod_eq_self Real.two_pi_pos).2 hdiff']

/-- The four-bin map is injective on a one-separated family of unit vectors contained in a
closed supporting half-plane. -/
lemma upperPhaseBin_injOn_of_unit_oneSeparated (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hupper : ∀ z ∈ S, 0 ≤ z.im)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    Set.InjOn upperPhaseBin S := by
  intro x hx y hy hbin
  by_contra hxy
  have hangle_ge := pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
    (hnorm x hx) (hnorm y hy) (hsep x hx y hy hxy)
  have hangle_eq := angle_eq_abs_arg_sub_of_upperPhaseBin_eq
    (hnorm x hx) (hnorm y hy) (hupper x hx) (hupper y hy) hbin
  have hangle_lt := abs_arg_sub_lt_pi_div_three_of_upperPhaseBin_eq
    (hupper x hx) (hupper y hy) hbin
  linarith

/-- A one-separated collection of unit vectors in a closed supporting half-plane has at most
four elements. -/
theorem card_le_four_of_unit_oneSeparated_of_im_nonneg (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hupper : ∀ z ∈ S, 0 ≤ z.im)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    S.card ≤ 4 := by
  have hcard := Finset.card_le_card_of_injOn upperPhaseBin
    (s := S) (t := Finset.univ) (by simp [Set.MapsTo])
    (upperPhaseBin_injOn_of_unit_oneSeparated S hnorm hupper hsep)
  simpa using hcard

/-- A point strictly above the supporting line never occupies the endpoint bin `3`. -/
lemma upperPhaseBin_ne_three_of_im_pos {z : ℂ} (him : 0 < z.im) :
    upperPhaseBin z ≠ ⟨3, by norm_num⟩ := by
  intro h
  have hphase0 : 0 ≤ 3 * z.arg / Real.pi := upper_phase_nonneg him.le
  have hval : ⌊3 * z.arg / Real.pi⌋₊ = 3 := by
    simpa [upperPhaseBin, max_eq_right hphase0] using congrArg Fin.val h
  have harglt : z.arg < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr him.ne')
  have hfloorlt : ⌊3 * z.arg / Real.pi⌋₊ < 3 := by
    apply (Nat.floor_lt hphase0).2
    rw [div_lt_iff₀ Real.pi_pos]
    have h := mul_lt_mul_of_pos_left harglt (by norm_num : (0 : ℝ) < 3)
    exact h
  omega

/-- A one-separated collection of unit vectors in an open supporting half-plane has at most
three elements.  In particular an extreme convex-hull vertex has unit-distance degree at most
three after translating and rotating its supporting cone into the upper half-plane. -/
theorem card_le_three_of_unit_oneSeparated_of_im_pos (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hupper : ∀ z ∈ S, 0 < z.im)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    S.card ≤ 3 := by
  let T : Finset (Fin 4) := Finset.univ.erase ⟨3, by omega⟩
  have hmaps : Set.MapsTo upperPhaseBin S T := by
    intro z hz
    change upperPhaseBin z ∈ T
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true]
    exact upperPhaseBin_ne_three_of_im_pos (hupper z hz)
  have hcard := Finset.card_le_card_of_injOn upperPhaseBin hmaps
    (upperPhaseBin_injOn_of_unit_oneSeparated S hnorm
      (fun z hz ↦ (hupper z hz).le) hsep)
  have hTcard : T.card = 3 := by simp [T]
  omega

/-! ### Translation back to finite point sets -/

/-- A finite planar set is one-separated when every two distinct members are at distance at
least one. -/
def IsOneSeparated (A : Finset ℂ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y

/-- Members of `A` at unit distance from `p`. -/
noncomputable def unitNeighbors (A : Finset ℂ) (p : ℂ) : Finset ℂ :=
  A.filter fun q ↦ dist p q = 1

/-- Translate the unit neighbors so their common centre becomes the origin. -/
noncomputable def unitNeighborVectors (A : Finset ℂ) (p : ℂ) : Finset ℂ :=
  (unitNeighbors A p).image fun q ↦ q - p

lemma card_unitNeighborVectors (A : Finset ℂ) (p : ℂ) :
    (unitNeighborVectors A p).card = (unitNeighbors A p).card := by
  apply Finset.card_image_iff.mpr
  intro x _ y _ hxy
  exact sub_left_inj.mp hxy

lemma norm_eq_one_of_mem_unitNeighborVectors {A : Finset ℂ} {p z : ℂ}
    (hz : z ∈ unitNeighborVectors A p) :
    ‖z‖ = 1 := by
  rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
  rw [← dist_eq_norm]
  simpa [dist_comm] using (Finset.mem_filter.1 hq).2

lemma one_le_norm_sub_of_mem_unitNeighborVectors {A : Finset ℂ} {p x y : ℂ}
    (hA : IsOneSeparated A)
    (hx : x ∈ unitNeighborVectors A p) (hy : y ∈ unitNeighborVectors A p)
    (hxy : x ≠ y) :
    1 ≤ ‖x - y‖ := by
  rcases Finset.mem_image.1 hx with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.1 hy with ⟨r, hr, rfl⟩
  have hqr : q ≠ r := by
    intro h
    subst r
    exact hxy rfl
  simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
    hA q (Finset.mem_filter.1 hq).1 r (Finset.mem_filter.1 hr).1 hqr

/-- Unit neighbours lying in a closed supporting half-plane have degree at most four. -/
theorem card_unitNeighbors_le_four_of_sub_im_nonneg {A : Finset ℂ} {p : ℂ}
    (hA : IsOneSeparated A)
    (hupper : ∀ q ∈ unitNeighbors A p, 0 ≤ (q - p).im) :
    (unitNeighbors A p).card ≤ 4 := by
  let V := unitNeighborVectors A p
  have hnorm : ∀ z ∈ V, ‖z‖ = 1 := by
    intro z hz
    exact norm_eq_one_of_mem_unitNeighborVectors hz
  have him : ∀ z ∈ V, 0 ≤ z.im := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
    exact hupper q hq
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact one_le_norm_sub_of_mem_unitNeighborVectors hA hx hy hxy
  rw [← card_unitNeighborVectors A p]
  exact card_le_four_of_unit_oneSeparated_of_im_nonneg V hnorm him hsep

/-- Unit neighbours lying strictly in an open supporting half-plane have degree at most three.
This is the local minimum-distance degree bound at a strict convex-hull vertex. -/
theorem card_unitNeighbors_le_three_of_sub_im_pos {A : Finset ℂ} {p : ℂ}
    (hA : IsOneSeparated A)
    (hupper : ∀ q ∈ unitNeighbors A p, 0 < (q - p).im) :
    (unitNeighbors A p).card ≤ 3 := by
  let V := unitNeighborVectors A p
  have hnorm : ∀ z ∈ V, ‖z‖ = 1 := by
    intro z hz
    exact norm_eq_one_of_mem_unitNeighborVectors hz
  have him : ∀ z ∈ V, 0 < z.im := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
    exact hupper q hq
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact one_le_norm_sub_of_mem_unitNeighborVectors hA hx hy hxy
  rw [← card_unitNeighborVectors A p]
  exact card_le_three_of_unit_oneSeparated_of_im_pos V hnorm him hsep

end SupportingHalfPlane

section ComplexCoordinates

/-- The squared-distance equations for the two unit circles centred at `0` and `1` force the
real coordinate of an intersection point to be `1/2`. -/
lemma re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one {z : ℂ}
    (hz0 : Complex.normSq z = 1)
    (hz1 : Complex.normSq (z - 1) = 1) :
    z.re = (1 / 2 : ℝ) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hz0 hz1
  nlinarith

/-- The imaginary coordinate of an intersection of the two unit circles has square `3/4`. -/
lemma im_sq_eq_three_fourths_of_normSq_eq_one_of_normSq_sub_one_eq_one {z : ℂ}
    (hz0 : Complex.normSq z = 1)
    (hz1 : Complex.normSq (z - 1) = 1) :
    z.im ^ 2 = (3 / 4 : ℝ) := by
  have hre := re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one hz0 hz1
  simp only [Complex.normSq_apply] at hz0
  nlinarith

/-- Two intersections of the unit circles about `0` and `1` either coincide or are mirror images
across the real axis. -/
lemma eq_or_eq_conj_of_two_common_unit_neighbors {z w : ℂ}
    (hz0 : Complex.normSq z = 1) (hz1 : Complex.normSq (z - 1) = 1)
    (hw0 : Complex.normSq w = 1) (hw1 : Complex.normSq (w - 1) = 1) :
    z = w ∨ z = conj w := by
  have hzre := re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one hz0 hz1
  have hwre := re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one hw0 hw1
  have hzim := im_sq_eq_three_fourths_of_normSq_eq_one_of_normSq_sub_one_eq_one hz0 hz1
  have hwim := im_sq_eq_three_fourths_of_normSq_eq_one_of_normSq_sub_one_eq_one hw0 hw1
  have him : z.im = w.im ∨ z.im = -w.im :=
    (sq_eq_sq_iff_eq_or_eq_neg).mp (hzim.trans hwim.symm)
  rcases him with him | him
  · left
    apply Complex.ext
    · exact hzre.trans hwre.symm
    · exact him
  · right
    apply Complex.ext
    · simpa using hzre.trans hwre.symm
    · simpa using him

/-- Distinct common unit neighbours of a unit segment are separated by squared distance `3`.
This is the exact `√3`-diagonal occurring in a regular hexagon. -/
lemma normSq_sub_eq_three_of_two_distinct_common_unit_neighbors {z w : ℂ}
    (hz0 : Complex.normSq z = 1) (hz1 : Complex.normSq (z - 1) = 1)
    (hw0 : Complex.normSq w = 1) (hw1 : Complex.normSq (w - 1) = 1)
    (hzw : z ≠ w) :
    Complex.normSq (z - w) = 3 := by
  have hzre := re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one hz0 hz1
  have hwre := re_eq_half_of_normSq_eq_one_of_normSq_sub_one_eq_one hw0 hw1
  have hzim := im_sq_eq_three_fourths_of_normSq_eq_one_of_normSq_sub_one_eq_one hz0 hz1
  have hwim := im_sq_eq_three_fourths_of_normSq_eq_one_of_normSq_sub_one_eq_one hw0 hw1
  have him : z.im = -w.im := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hzim.trans hwim.symm) with h | h
    · exfalso
      apply hzw
      apply Complex.ext
      · exact hzre.trans hwre.symm
      · exact h
    · exact h
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith

/-- The two unit circles about the ends of a unit segment have at most two common points. -/
lemma eq_first_or_second_of_three_common_unit_neighbors {z₁ z₂ z₃ : ℂ}
    (hz₁0 : Complex.normSq z₁ = 1) (hz₁1 : Complex.normSq (z₁ - 1) = 1)
    (hz₂0 : Complex.normSq z₂ = 1) (hz₂1 : Complex.normSq (z₂ - 1) = 1)
    (hz₃0 : Complex.normSq z₃ = 1) (hz₃1 : Complex.normSq (z₃ - 1) = 1)
    (hz₁z₂ : z₁ ≠ z₂) :
    z₃ = z₁ ∨ z₃ = z₂ := by
  rcases eq_or_eq_conj_of_two_common_unit_neighbors hz₁0 hz₁1 hz₂0 hz₂1 with
    h₁₂ | h₁₂
  · exact (hz₁z₂ h₁₂).elim
  rcases eq_or_eq_conj_of_two_common_unit_neighbors hz₁0 hz₁1 hz₃0 hz₃1 with
    h₁₃ | h₁₃
  · exact Or.inl h₁₃.symm
  · right
    calc
      z₃ = conj z₁ := by simpa using (congrArg conj h₁₃).symm
      _ = z₂ := by simpa [h₁₂]

/-- Three pairwise distinct common unit neighbours of a unit segment do not exist. -/
lemma not_three_pairwise_distinct_common_unit_neighbors {z₁ z₂ z₃ : ℂ}
    (hz₁0 : Complex.normSq z₁ = 1) (hz₁1 : Complex.normSq (z₁ - 1) = 1)
    (hz₂0 : Complex.normSq z₂ = 1) (hz₂1 : Complex.normSq (z₂ - 1) = 1)
    (hz₃0 : Complex.normSq z₃ = 1) (hz₃1 : Complex.normSq (z₃ - 1) = 1) :
    ¬ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  rintro ⟨h₁₂, h₁₃, h₂₃⟩
  rcases eq_first_or_second_of_three_common_unit_neighbors hz₁0 hz₁1 hz₂0 hz₂1
      hz₃0 hz₃1 h₁₂ with h | h
  · exact h₁₃ h.symm
  · exact h₂₃ h.symm

end ComplexCoordinates

end Erdos957Hex
