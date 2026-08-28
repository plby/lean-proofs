import Wikipedia.HopfProblem.SpecialPeriodsTriangleRepresentation
import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Ping-pong geometry of the explicit triangle generators

The vertical half-planes on either side of `Re z = -1` form actual
ping-pong domains in the upper half-plane.  The two nonidentity powers of
the first elliptic generator send the left domain into the right one;
the three nonidentity powers of the second generator send the right
domain into the left one.  The ping-pong theorem then proves that the
actual geometric representation of the free product is faithful.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The domain controlled by the order-three factor. -/
def pingPongOne : Set ℍ := {z | -1 < z.re}

/-- The domain controlled by the order-four factor. -/
def pingPongTwo : Set ℍ := {z | z.re < -1}

theorem pingPongOne_nonempty : pingPongOne.Nonempty := by
  exact ⟨UpperHalfPlane.I, by norm_num [pingPongOne]⟩

theorem pingPongTwo_nonempty : pingPongTwo.Nonempty := by
  refine ⟨⟨(-2 : ℂ) + Complex.I, by norm_num⟩, ?_⟩
  norm_num [pingPongTwo]

theorem pingPong_disjoint : Disjoint pingPongOne pingPongTwo := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  change -1 < z.re at hz₁
  change z.re < -1 at hz₂
  exact lt_asymm hz₁ hz₂

private theorem smul_coe_of_matrix (g : SL(2, ℝ)) (a b c d : ℝ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
  rw [coe_specialLinearGroup_apply]
  change (((((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℂ) * z +
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) : ℂ)) /
    (((((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℂ)) * z +
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℂ))) = _
  rw [hg]
  rfl

private theorem add_real_ne_zero (z : ℍ) (c : ℝ) : (z : ℂ) + c ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem generatorOneSL_smul_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix generatorOneSL 0 (-1) 1 1 coe_generatorOneSL]
  simp [div_eq_mul_inv]

theorem generatorOneSL_sq_smul_coe (z : ℍ) :
    (((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) = -1 - (z : ℂ)⁻¹ := by
  rw [smul_coe_of_matrix (generatorOneSL ^ 2) (-1) (-1) 1 0 coe_generatorOneSL_sq]
  push_cast
  field_simp [z.ne_zero]
  ring

theorem generatorTwoSL_smul_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) = -1 - ((z : ℂ) + (width : ℂ))⁻¹ := by
  rw [smul_coe_of_matrix generatorTwoSL 1 (width + 1) (-1) (-width)
    coe_generatorTwoSL]
  push_cast
  let u : ℂ := (z : ℂ) + (width : ℂ)
  have hu : u ≠ 0 := add_real_ne_zero z width
  calc
    _ = (u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -(1 + u⁻¹) := by rw [div_neg, add_div, div_self hu, one_div]
    _ = -1 - u⁻¹ := by ring

theorem generatorTwoSL_sq_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) =
      -1 - ((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ)) := by
  rw [smul_coe_of_matrix (generatorTwoSL ^ 2) (-width) (-2 * width) (width - 1) width
    coe_generatorTwoSL_sq]
  have hd : ((width : ℂ) - 1) * (z : ℂ) + (width : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero,
      zero_mul, add_zero, UpperHalfPlane.coe_im] at hi
    exact (mul_pos (sub_pos.mpr one_lt_width) z.im_pos).ne' hi
  push_cast
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hd]
  ring

theorem coe_generatorTwoSL_cube :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![width, width + 1; -1, -1] := by
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul,
    coe_generatorTwoSL_sq, coe_generatorTwoSL, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

theorem generatorTwoSL_cube_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 3 : SL(2, ℝ)) • z : ℍ) : ℂ) =
      -(width : ℂ) - ((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix (generatorTwoSL ^ 3) width (width + 1) (-1) (-1)
    coe_generatorTwoSL_cube]
  have hd : (z : ℂ) + 1 ≠ 0 := by simpa using add_real_ne_zero z 1
  push_cast
  let u : ℂ := (z : ℂ) + 1
  calc
    _ = ((width : ℂ) * u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -((width : ℂ) + u⁻¹) := by
      rw [div_neg, add_div, mul_div_cancel_right₀ _ hd, one_div]
    _ = -(width : ℂ) - u⁻¹ := by ring

theorem generatorOne_pingPong :
    MapsTo (fun z : ℍ => generatorOneSL • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < (generatorOneSL • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, Complex.one_re,
    UpperHalfPlane.coe_re]
  have hden : 0 < Complex.normSq ((z : ℂ) + 1) :=
    Complex.normSq_pos.mpr (by simpa using add_real_ne_zero z 1)
  have hn : (z.re + 1) / Complex.normSq ((z : ℂ) + 1) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  linarith

theorem generatorOne_sq_pingPong :
    MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < ((generatorOneSL ^ 2 : SL(2, ℝ)) • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    UpperHalfPlane.coe_re]
  have hn : z.re / Complex.normSq (z : ℂ) < 0 :=
    div_neg_of_neg_of_pos (by linarith) z.normSq_pos
  linarith

theorem generatorTwo_pingPong :
    MapsTo (fun z : ℍ => generatorTwoSL • z) pingPongOne pingPongTwo := by
  intro z hz
  change (generatorTwoSL • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + width) / Complex.normSq ((z : ℂ) + (width : ℂ)) :=
    div_pos (by linarith [one_lt_width])
      (Complex.normSq_pos.mpr (add_real_ne_zero z width))
  linarith

theorem generatorTwo_sq_pingPong :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  suffices hpos : 0 <
      (((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ))).re by
    linarith
  let u : ℂ := (z : ℂ) + (width : ℂ)
  let v : ℂ := ((width : ℂ) - 1) * z + (width : ℂ)
  have hu : 0 < u.re := by
    change 0 < z.re + width
    linarith [one_lt_width]
  have hv : 0 < v.re := by
    simp only [v, Complex.add_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.one_re, Complex.sub_im, Complex.ofReal_im,
      Complex.one_im, sub_zero, zero_mul, UpperHalfPlane.coe_re]
    nlinarith [one_lt_width]
  have hvi : 0 < v.im := by
    simp only [v, Complex.add_im, Complex.mul_im, Complex.sub_re,
      Complex.ofReal_re, Complex.one_re, Complex.sub_im, Complex.ofReal_im,
      Complex.one_im, sub_zero, zero_mul, add_zero, UpperHalfPlane.coe_im]
    exact mul_pos (sub_pos.mpr one_lt_width) z.im_pos
  have hui : 0 < u.im := by simpa [u] using z.im_pos
  have hn : 0 < Complex.normSq v := by
    apply Complex.normSq_pos.mpr
    intro h
    exact hv.ne' (by simpa using congrArg Complex.re h)
  change 0 < (u / v).re
  rw [Complex.div_re]
  exact add_pos (div_pos (mul_pos hu hv) hn) (div_pos (mul_pos hui hvi) hn)

theorem generatorTwo_cube_pingPong :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_cube_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.inv_re,
    Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + 1) / Complex.normSq ((z : ℂ) + 1) :=
    div_pos (by linarith)
      (Complex.normSq_pos.mpr (by simpa using add_real_ne_zero z 1))
  linarith [one_lt_width]


/-- The matrix-power action agrees with the corresponding permutation power. -/
theorem generatorOnePerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorOnePerm ^ n) z = (generatorOneSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorOnePerm, ← map_pow, realSLPermutation_apply]

theorem generatorTwoPerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorTwoPerm ^ n) z = (generatorTwoSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorTwoPerm, ← map_pow, realSLPermutation_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

namespace Wikipedia.HopfProblem.SpecialPeriods

open Function


private theorem cyclicPowerHom_natCast' {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) (m : ℕ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (m : ZMod n)) = a ^ m := by
  simpa only [Int.cast_natCast, zpow_natCast] using
    cyclicPowerHom_intCast n a ha (m : ℤ)

private theorem cyclicPowerHom_two' {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast' n a ha 2

private theorem cyclicPowerHom_three' {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast' n a ha 3

/-- Ping-pong for the actual binary free product of the cyclic groups of
orders three and four. -/
theorem triangleLift_injective_of_pingPong {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1)
    (X Y : Set α) (hXY : Disjoint X Y) (hX : X.Nonempty) (hY : Y.Nonempty)
    (ha₁ : MapsTo (fun z => a • z) Y X)
    (ha₂ : MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : MapsTo (fun z => b • z) X Y)
    (hb₂ : MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : MapsTo (fun z => b ^ 3 • z) X Y) :
    Injective (triangleLift a b ha hb) := by
  let H : Bool → Type := fun i => cond i
    (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i => match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := false))
      (Monoid.CoprodI.of (M := H) (i := true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i => match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have htoI : Injective toI := by
    apply LeftInverse.injective (g := fromI)
    intro z
    exact DFunLike.congr_fun hleft z
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  rw [hrepresentation, MonoidHom.coe_comp]
  apply Injective.comp _ htoI
  let U : Bool → Set α := fun i => cond i Y X
  apply Monoid.CoprodI.lift_injective_of_ping_pong f _ U
  · intro i
    cases i
    · exact hX
    · exact hY
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hXY
    · exact hXY.symm
    · exact (hij rfl).elim
  · intro i j hij g hg
    cases i <;> cases j
    · exact (hij rfl).elim
    · change cyclicPowerHom 3 a ha g • Y ⊆ X
      have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨
          g = Multiplicative.ofAdd (2 : ZMod 3) := by
        exact (by decide : ∀ x : Multiplicative (ZMod 3), x ≠ 1 →
          x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2) g hg
      rcases hc with rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₁ hz)
      · rw [cyclicPowerHom_two' 3 a ha]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₂ hz)
    · change cyclicPowerHom 4 b hb g • X ⊆ Y
      have hc : g = Multiplicative.ofAdd (1 : ZMod 4) ∨
          g = Multiplicative.ofAdd (2 : ZMod 4) ∨
          g = Multiplicative.ofAdd (3 : ZMod 4) := by
        exact (by decide : ∀ x : Multiplicative (ZMod 4), x ≠ 1 →
          x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨
          x = Multiplicative.ofAdd 3) g hg
      rcases hc with rfl | rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₁ hz)
      · rw [cyclicPowerHom_two' 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [cyclicPowerHom_three' 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  · right
    refine ⟨false, ?_⟩
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp


/-- The constructed Möbius representation of the actual free product is
faithful.  This follows from the five strict half-plane inclusions above;
no faithfulness or discreteness hypothesis is supplied. -/
theorem triangleGeometricRepresentation_injective :
    Function.Injective triangleGeometricRepresentation := by
  apply triangleLift_injective_of_pingPong
    Triangle.generatorOnePerm Triangle.generatorTwoPerm
    Triangle.generatorOnePerm_cube Triangle.generatorTwoPerm_fourth
    Triangle.pingPongOne Triangle.pingPongTwo Triangle.pingPong_disjoint
    Triangle.pingPongOne_nonempty Triangle.pingPongTwo_nonempty
  · intro z hz
    exact Triangle.generatorOne_pingPong hz
  · intro z hz
    change (Triangle.generatorOnePerm ^ 2) z ∈ Triangle.pingPongOne
    rw [Triangle.generatorOnePerm_pow_apply]
    exact Triangle.generatorOne_sq_pingPong hz
  · intro z hz
    exact Triangle.generatorTwo_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 2) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_sq_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 3) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_cube_pingPong hz

/-- Faithfulness of the corresponding named action on the upper half-plane. -/
theorem triangleGeometricAction_faithful :
    letI := triangleGeometricAction
    FaithfulSMul TriangleGroup ℍ := by
  let := triangleGeometricAction
  constructor
  intro g h hgh
  apply triangleGeometricRepresentation_injective
  apply Equiv.ext
  exact hgh

end Wikipedia.HopfProblem.SpecialPeriods
