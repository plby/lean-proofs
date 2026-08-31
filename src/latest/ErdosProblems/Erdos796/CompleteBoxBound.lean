import ErdosProblems.Erdos796.CompleteBox
import Mathlib.Data.Nat.Choose.Bounds

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit unbalanced complete-box bound

This file turns the pair-codegree estimate and the exact second-moment
identity from `Erdos796.CompleteBox` into a bound for the number of displayed
hyperedges.  We also record the version of the pair-codegree estimate obtained
by interchanging the last two vertex classes; that is the orientation needed
when their sizes are ordered.
-/

namespace Erdos796

namespace Tripartite

open scoped BigOperators

variable {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Interchange the last two coordinates of a finite tripartite hypergraph. -/
def swapYZ (H : Finset (X × Y × Z)) : Finset (X × Z × Y) :=
  H.image fun p => (p.1, p.2.2, p.2.1)

@[simp]
theorem mem_swapYZ {H : Finset (X × Y × Z)} {x : X} {y : Y} {z : Z} :
    (x, z, y) ∈ swapYZ H ↔ (x, y, z) ∈ H := by
  simp [swapYZ, Prod.ext_iff]

/-- Box-freeness is unchanged by interchanging the last two parts. -/
theorem k222Free_swapYZ {H : Finset (X × Y × Z)} (hH : K222Free H) :
    K222Free (swapYZ H) := by
  intro x₁ x₂ z₁ z₂ y₁ y₂ h₁₁₁ h₁₁₂ h₁₂₁ h₁₂₂
    h₂₁₁ h₂₁₂ h₂₂₁ h₂₂₂
  have h := hH
    (mem_swapYZ.mp h₁₁₁) (mem_swapYZ.mp h₁₂₁)
    (mem_swapYZ.mp h₁₁₂) (mem_swapYZ.mp h₁₂₂)
    (mem_swapYZ.mp h₂₁₁) (mem_swapYZ.mp h₂₂₁)
    (mem_swapYZ.mp h₂₁₂) (mem_swapYZ.mp h₂₂₂)
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

@[simp]
theorem codegree_swapYZ (H : Finset (X × Y × Z)) (L : Finset X)
    (y : Y) (z : Z) :
    codegree (swapYZ H) L z y = codegree H L y z := by
  simp [codegree]

/-- Swapping the last two parts does not change the displayed edge count. -/
theorem edgeCount_swapYZ (H : Finset (X × Y × Z)) (L : Finset X)
    (M : Finset Y) (R : Finset Z) :
    edgeCount (swapYZ H) L R M = edgeCount H L M R := by
  simp only [edgeCount, codegree_swapYZ]
  rw [Finset.sum_comm]

/-- Swapping the last two parts does not change the pair-codegree mass. -/
theorem pairCodegreeMass_swapYZ (H : Finset (X × Y × Z))
    (L : Finset X) (M : Finset Y) (R : Finset Z) :
    pairCodegreeMass (swapYZ H) L R M = pairCodegreeMass H L M R := by
  simp only [pairCodegreeMass, codegree_swapYZ]
  rw [Finset.sum_comm]

@[simp]
theorem card_swapYZ (H : Finset (X × Y × Z)) :
    (swapYZ H).card = H.card := by
  rw [swapYZ, Finset.card_image_of_injective]
  intro p q hpq
  rcases p with ⟨x, y, z⟩
  rcases q with ⟨x', y', z'⟩
  simp only [Prod.mk.injEq] at hpq
  simp only [Prod.mk.injEq]
  aesop

/-- Support in a Cartesian product is preserved when the last two parts are
interchanged. -/
theorem swapYZ_subset_product {H : Finset (X × Y × Z)}
    {L : Finset X} {M : Finset Y} {R : Finset Z}
    (hsub : H ⊆ L ×ˢ (M ×ˢ R)) :
    swapYZ H ⊆ L ×ˢ (R ×ˢ M) := by
  intro p hp
  rcases p with ⟨x, z, y⟩
  have hold : (x, y, z) ∈ H := mem_swapYZ.mp hp
  have hs := Finset.mem_product.mp (hsub hold)
  have hsMR := Finset.mem_product.mp hs.2
  exact Finset.mem_product.mpr
    ⟨hs.1, Finset.mem_product.mpr ⟨hsMR.2, hsMR.1⟩⟩

/-- Cyclically rotate the three vertex classes. -/
def rotateXYZ (H : Finset (X × Y × Z)) : Finset (Y × Z × X) :=
  H.image fun p => (p.2.1, p.2.2, p.1)

@[simp]
theorem mem_rotateXYZ {H : Finset (X × Y × Z)}
    {x : X} {y : Y} {z : Z} :
    (y, z, x) ∈ rotateXYZ H ↔ (x, y, z) ∈ H := by
  simp [rotateXYZ, Prod.ext_iff]

@[simp]
theorem card_rotateXYZ (H : Finset (X × Y × Z)) :
    (rotateXYZ H).card = H.card := by
  rw [rotateXYZ, Finset.card_image_of_injective]
  intro p q hpq
  rcases p with ⟨x, y, z⟩
  rcases q with ⟨x', y', z'⟩
  simp only [Prod.mk.injEq] at hpq
  simp only [Prod.mk.injEq]
  aesop

/-- Box-freeness is invariant under a cyclic rotation of the parts. -/
theorem k222Free_rotateXYZ {H : Finset (X × Y × Z)} (hH : K222Free H) :
    K222Free (rotateXYZ H) := by
  intro y₁ y₂ z₁ z₂ x₁ x₂ h₁₁₁ h₁₁₂ h₁₂₁ h₁₂₂
    h₂₁₁ h₂₁₂ h₂₂₁ h₂₂₂
  have h := hH
    (mem_rotateXYZ.mp h₁₁₁) (mem_rotateXYZ.mp h₁₂₁)
    (mem_rotateXYZ.mp h₂₁₁) (mem_rotateXYZ.mp h₂₂₁)
    (mem_rotateXYZ.mp h₁₁₂) (mem_rotateXYZ.mp h₁₂₂)
    (mem_rotateXYZ.mp h₂₁₂) (mem_rotateXYZ.mp h₂₂₂)
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Cartesian-product support rotates with the vertex classes. -/
theorem rotateXYZ_subset_product {H : Finset (X × Y × Z)}
    {L : Finset X} {M : Finset Y} {R : Finset Z}
    (hsub : H ⊆ L ×ˢ (M ×ˢ R)) :
    rotateXYZ H ⊆ M ×ˢ (R ×ˢ L) := by
  intro p hp
  rcases p with ⟨y, z, x⟩
  have hold : (x, y, z) ∈ H := mem_rotateXYZ.mp hp
  have hs := Finset.mem_product.mp (hsub hold)
  have hsMR := Finset.mem_product.mp hs.2
  exact Finset.mem_product.mpr
    ⟨hsMR.1, Finset.mem_product.mpr ⟨hsMR.2, hs.1⟩⟩

/-- The KST pair-codegree estimate in the orientation in which the second
part is summed over and the third part supplies the left vertices. -/
theorem pairCodegreeMass_le_kst_swap {H : Finset (X × Y × Z)}
    (hH : K222Free H) (L : Finset X) (M : Finset Y) (R : Finset Z) :
    (pairCodegreeMass H L M R : ℝ) ≤
      (Nat.choose L.card 2 : ℝ) *
        ((M.card : ℝ) +
          Real.sqrt (2 * (M.card : ℝ) * (Nat.choose R.card 2 : ℝ))) := by
  have h := pairCodegreeMass_le_kst (k222Free_swapYZ hH) L R M
  simpa [pairCodegreeMass_swapYZ] using! h

/-- Cauchy--Schwarz followed by the pair-codegree estimate.  This is the
quadratic form of the complete-box bound. -/
theorem edgeCount_sq_le_kst_swap {H : Finset (X × Y × Z)}
    (hH : K222Free H) (L : Finset X) (M : Finset Y) (R : Finset Z) :
    (edgeCount H L M R : ℝ) ^ 2 ≤
      ((M.card : ℝ) * (R.card : ℝ)) *
        ((edgeCount H L M R : ℝ) +
          2 * ((Nat.choose L.card 2 : ℝ) *
            ((M.card : ℝ) +
              Real.sqrt
                (2 * (M.card : ℝ) * (Nat.choose R.card 2 : ℝ))))) := by
  have hpair := pairCodegreeMass_le_kst_swap hH L M R
  have hsquares := sum_sq_codegree_eq H L M R
  have hcs :
      (edgeCount H L M R : ℝ) ^ 2 ≤
        ((M ×ˢ R).card : ℝ) *
          ∑ yz ∈ M ×ˢ R, (codegree H L yz.1 yz.2 : ℝ) ^ 2 := by
    rw [edgeCount_eq_sum_product]
    push_cast
    exact sq_sum_le_card_mul_sum_sq
  rw [Finset.card_product, Nat.cast_mul, hsquares] at hcs
  calc
    (edgeCount H L M R : ℝ) ^ 2 ≤
        ((M.card : ℝ) * (R.card : ℝ)) *
          ((edgeCount H L M R : ℝ) +
            2 * (pairCodegreeMass H L M R : ℝ)) := hcs
    _ ≤ ((M.card : ℝ) * (R.card : ℝ)) *
        ((edgeCount H L M R : ℝ) +
          2 * ((Nat.choose L.card 2 : ℝ) *
            ((M.card : ℝ) +
              Real.sqrt
                (2 * (M.card : ℝ) * (Nat.choose R.card 2 : ℝ))))) := by
      gcongr

/-- Solving the quadratic inequality in the preceding second-moment
argument, while retaining the exact pair-codegree mass. -/
theorem edgeCount_le_card_product_add_sqrt_pairMass
    (H : Finset (X × Y × Z)) (L : Finset X) (M : Finset Y)
    (R : Finset Z) :
    (edgeCount H L M R : ℝ) ≤
      (M.card : ℝ) * (R.card : ℝ) +
        Real.sqrt
          (2 * ((M.card : ℝ) * (R.card : ℝ)) *
            (pairCodegreeMass H L M R : ℝ)) := by
  let e : ℝ := edgeCount H L M R
  let b : ℝ := (M.card : ℝ) * (R.card : ℝ)
  let s : ℝ := pairCodegreeMass H L M R
  have he : 0 ≤ e := by positivity
  have hb : 0 ≤ b := by positivity
  have hs : 0 ≤ s := by positivity
  have hcs : e ^ 2 ≤ b * (e + 2 * s) := by
    have h :
        (edgeCount H L M R : ℝ) ^ 2 ≤
          ((M ×ˢ R).card : ℝ) *
            ∑ yz ∈ M ×ˢ R, (codegree H L yz.1 yz.2 : ℝ) ^ 2 := by
      rw [edgeCount_eq_sum_product]
      push_cast
      exact sq_sum_le_card_mul_sum_sq
    rw [Finset.card_product, Nat.cast_mul, sum_sq_codegree_eq] at h
    simpa [e, b, s] using! h
  have hrad : 0 ≤ 2 * b * s := by positivity
  have hsqrt : 0 ≤ Real.sqrt (2 * b * s) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (2 * b * s) ^ 2 = 2 * b * s :=
    Real.sq_sqrt hrad
  by_cases heb : e ≤ b
  · dsimp [e, b, s] at heb hsqrt
    linarith
  · have hbe : b ≤ e := (lt_of_not_ge heb).le
    have hshift : 0 ≤ e - b := sub_nonneg.mpr hbe
    have hshift_sq : (e - b) ^ 2 ≤ 2 * b * s := by
      nlinarith [mul_nonneg hb (sub_nonneg.mpr hbe)]
    have hshift_le : e - b ≤ Real.sqrt (2 * b * s) := by
      nlinarith
    dsimp [e, b, s] at hshift_le ⊢
    linarith

/-- The fourth root written using only the elementary real square root. -/
noncomputable def realFourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem realFourthRoot_nonneg (x : ℝ) : 0 ≤ realFourthRoot x := by
  exact Real.sqrt_nonneg _

theorem realFourthRoot_mono {x y : ℝ} (hxy : x ≤ y) :
    realFourthRoot x ≤ realFourthRoot y := by
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy)

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

theorem realFourthRoot_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    realFourthRoot x ≤ x := by
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  exact (sqrt_le_self_of_one_le hsx).trans (sqrt_le_self_of_one_le hx)

theorem realFourthRoot_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 < realFourthRoot x := by
  have : 1 ≤ realFourthRoot x := by
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hx)
  linarith

/-- The elementary identity `y^(1/4) y^(3/4) = y`, expressed with square
roots so that no real-power API is needed. -/
theorem realFourthRoot_mul_threeQuarterRoot {y : ℝ} (hy : 0 ≤ y) :
    realFourthRoot y * Real.sqrt (y * Real.sqrt y) = y := by
  calc
    realFourthRoot y * Real.sqrt (y * Real.sqrt y) =
        realFourthRoot y * (Real.sqrt y * realFourthRoot y) := by
          rw [Real.sqrt_mul hy]
          rfl
    _ = Real.sqrt y * realFourthRoot y ^ 2 := by ring
    _ = Real.sqrt y * Real.sqrt y := by
          rw [realFourthRoot, Real.sq_sqrt (Real.sqrt_nonneg y)]
    _ = y := Real.mul_self_sqrt hy

/-- A coarse but convenient ordered form of the pair-codegree estimate.
For positive `|L| ≤ |M| ≤ |R|`, its right side has precisely the scale
`|L|² |R| sqrt |M|` used in the manuscript. -/
theorem pairCodegreeMass_le_three_mul_ordered {H : Finset (X × Y × Z)}
    (hH : K222Free H) (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hL : 0 < L.card) (hLM : L.card ≤ M.card) (hMR : M.card ≤ R.card) :
    (pairCodegreeMass H L M R : ℝ) ≤
      3 * (L.card : ℝ) ^ 2 * (R.card : ℝ) *
        Real.sqrt (M.card : ℝ) := by
  have hbase := pairCodegreeMass_le_kst_swap hH L M R
  have hchooseLNat := Nat.choose_le_pow L.card 2
  have hchooseRNat := Nat.choose_le_pow R.card 2
  have hchooseL : (Nat.choose L.card 2 : ℝ) ≤ (L.card : ℝ) ^ 2 := by
    exact_mod_cast hchooseLNat
  have hchooseR : (Nat.choose R.card 2 : ℝ) ≤ (R.card : ℝ) ^ 2 := by
    exact_mod_cast hchooseRNat
  have hy0 : 0 ≤ (M.card : ℝ) := by positivity
  have hz0 : 0 ≤ (R.card : ℝ) := by positivity
  have hsqrty : 0 ≤ Real.sqrt (M.card : ℝ) := Real.sqrt_nonneg _
  have hsqrty_sq : Real.sqrt (M.card : ℝ) ^ 2 = (M.card : ℝ) :=
    Real.sq_sqrt hy0
  have hsqrt_choose :
      Real.sqrt
          (2 * (M.card : ℝ) * (Nat.choose R.card 2 : ℝ)) ≤
        2 * (R.card : ℝ) * Real.sqrt (M.card : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hmulg := mul_le_mul_of_nonneg_left hchooseR hy0
      nlinarith
  have hy1Nat : 1 ≤ M.card := by omega
  have hy1 : (1 : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast hy1Nat
  have hone_sqrty : (1 : ℝ) ≤ Real.sqrt (M.card : ℝ) :=
    Real.one_le_sqrt.mpr hy1
  have hymr : (M.card : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hMR
  have hy_le :
      (M.card : ℝ) ≤
        (R.card : ℝ) * Real.sqrt (M.card : ℝ) := by
    calc
      (M.card : ℝ) ≤ (R.card : ℝ) := hymr
      _ ≤ (R.card : ℝ) * Real.sqrt (M.card : ℝ) := by
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hone_sqrty)]
  calc
    (pairCodegreeMass H L M R : ℝ) ≤
        (Nat.choose L.card 2 : ℝ) *
          ((M.card : ℝ) +
            Real.sqrt
              (2 * (M.card : ℝ) * (Nat.choose R.card 2 : ℝ))) := hbase
    _ ≤ (L.card : ℝ) ^ 2 *
          ((M.card : ℝ) +
            2 * (R.card : ℝ) * Real.sqrt (M.card : ℝ)) := by
      gcongr
    _ ≤ 3 * (L.card : ℝ) ^ 2 * (R.card : ℝ) *
        Real.sqrt (M.card : ℝ) := by
      nlinarith [sq_nonneg (L.card : ℝ)]

/-- An additive ordered complete-box bound.  It is the direct finite analogue
of the estimate obtained in the manuscript immediately after solving the
second-moment inequality. -/
theorem edgeCount_le_ordered_additive {H : Finset (X × Y × Z)}
    (hH : K222Free H) (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hL : 0 < L.card) (hLM : L.card ≤ M.card) (hMR : M.card ≤ R.card) :
    (edgeCount H L M R : ℝ) ≤
      (M.card : ℝ) * (R.card : ℝ) +
        3 * (L.card : ℝ) * (R.card : ℝ) *
          Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) := by
  have hedge := edgeCount_le_card_product_add_sqrt_pairMass H L M R
  have hpair := pairCodegreeMass_le_three_mul_ordered hH L M R hL hLM hMR
  have hx0 : 0 ≤ (L.card : ℝ) := by positivity
  have hy0 : 0 ≤ (M.card : ℝ) := by positivity
  have hz0 : 0 ≤ (R.card : ℝ) := by positivity
  have hsqrty : 0 ≤ Real.sqrt (M.card : ℝ) := Real.sqrt_nonneg _
  have hthree :
      0 ≤ 3 * (L.card : ℝ) * (R.card : ℝ) *
        Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) := by
    positivity
  have hthree_sq :
      Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) ^ 2 =
        (M.card : ℝ) * Real.sqrt (M.card : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg hy0 hsqrty)
  have hscaled := mul_le_mul_of_nonneg_left hpair
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hy0) hz0)
  have hrad_le :
      2 * ((M.card : ℝ) * (R.card : ℝ)) *
          (pairCodegreeMass H L M R : ℝ) ≤
        6 * (L.card : ℝ) ^ 2 * (M.card : ℝ) *
          (R.card : ℝ) ^ 2 * Real.sqrt (M.card : ℝ) := by
    calc
      2 * ((M.card : ℝ) * (R.card : ℝ)) *
          (pairCodegreeMass H L M R : ℝ) =
          2 * (M.card : ℝ) * (R.card : ℝ) *
            (pairCodegreeMass H L M R : ℝ) := by ring
      _ ≤ 2 * (M.card : ℝ) * (R.card : ℝ) *
          (3 * (L.card : ℝ) ^ 2 * (R.card : ℝ) *
            Real.sqrt (M.card : ℝ)) := hscaled
      _ = 6 * (L.card : ℝ) ^ 2 * (M.card : ℝ) *
          (R.card : ℝ) ^ 2 * Real.sqrt (M.card : ℝ) := by ring
  have hcoarse_to_square :
      6 * (L.card : ℝ) ^ 2 * (M.card : ℝ) *
          (R.card : ℝ) ^ 2 * Real.sqrt (M.card : ℝ) ≤
        (3 * (L.card : ℝ) * (R.card : ℝ) *
          Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ))) ^ 2 := by
    rw [mul_pow, hthree_sq]
    have hnonneg :
        0 ≤ (L.card : ℝ) ^ 2 * (M.card : ℝ) *
          (R.card : ℝ) ^ 2 * Real.sqrt (M.card : ℝ) := by
      positivity
    nlinarith
  have hsqrt :
      Real.sqrt
          (2 * ((M.card : ℝ) * (R.card : ℝ)) *
            (pairCodegreeMass H L M R : ℝ)) ≤
        3 * (L.card : ℝ) * (R.card : ℝ) *
          Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hthree
    · exact hrad_le.trans hcoarse_to_square
  linarith

/-- Ordered unbalanced complete-box bound in denominator-free form.  The
factor on the left is the fourth root of the smallest part size. -/
theorem realFourthRoot_mul_edgeCount_le_four_mul_ordered
    {H : Finset (X × Y × Z)} (hH : K222Free H)
    (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hL : 0 < L.card) (hLM : L.card ≤ M.card) (hMR : M.card ≤ R.card) :
    realFourthRoot (L.card : ℝ) * (edgeCount H L M R : ℝ) ≤
      4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ) := by
  have hedge := edgeCount_le_ordered_additive hH L M R hL hLM hMR
  have hx0 : 0 ≤ (L.card : ℝ) := by positivity
  have hy0 : 0 ≤ (M.card : ℝ) := by positivity
  have hz0 : 0 ≤ (R.card : ℝ) := by positivity
  have hxy : (L.card : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast hLM
  have hx1Nat : 1 ≤ L.card := by omega
  have hx1 : (1 : ℝ) ≤ (L.card : ℝ) := by exact_mod_cast hx1Nat
  have hq0 : 0 ≤ realFourthRoot (L.card : ℝ) :=
    realFourthRoot_nonneg _
  have hq_le_x : realFourthRoot (L.card : ℝ) ≤ (L.card : ℝ) :=
    realFourthRoot_le_self_of_one_le hx1
  have hq_le_qy :
      realFourthRoot (L.card : ℝ) ≤ realFourthRoot (M.card : ℝ) :=
    realFourthRoot_mono hxy
  have ht0 :
      0 ≤ Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) :=
    Real.sqrt_nonneg _
  have hqt :
      realFourthRoot (L.card : ℝ) *
          Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) ≤
        (M.card : ℝ) := by
    calc
      realFourthRoot (L.card : ℝ) *
          Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) ≤
          realFourthRoot (M.card : ℝ) *
            Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hq_le_qy ht0
      _ = (M.card : ℝ) :=
        realFourthRoot_mul_threeQuarterRoot hy0
  have hfirst :
      realFourthRoot (L.card : ℝ) *
          ((M.card : ℝ) * (R.card : ℝ)) ≤
        (L.card : ℝ) * ((M.card : ℝ) * (R.card : ℝ)) :=
    mul_le_mul_of_nonneg_right hq_le_x (mul_nonneg hy0 hz0)
  have hsecond :
      (3 * (L.card : ℝ) * (R.card : ℝ)) *
          (realFourthRoot (L.card : ℝ) *
            Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ))) ≤
        (3 * (L.card : ℝ) * (R.card : ℝ)) * (M.card : ℝ) :=
    mul_le_mul_of_nonneg_left hqt (by positivity)
  have hweighted := mul_le_mul_of_nonneg_left hedge hq0
  calc
    realFourthRoot (L.card : ℝ) * (edgeCount H L M R : ℝ) ≤
        realFourthRoot (L.card : ℝ) *
          ((M.card : ℝ) * (R.card : ℝ) +
            3 * (L.card : ℝ) * (R.card : ℝ) *
              Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ))) :=
      hweighted
    _ = realFourthRoot (L.card : ℝ) *
          ((M.card : ℝ) * (R.card : ℝ)) +
        (3 * (L.card : ℝ) * (R.card : ℝ)) *
          (realFourthRoot (L.card : ℝ) *
            Real.sqrt ((M.card : ℝ) * Real.sqrt (M.card : ℝ))) := by ring
    _ ≤ (L.card : ℝ) * ((M.card : ℝ) * (R.card : ℝ)) +
        (3 * (L.card : ℝ) * (R.card : ℝ)) * (M.card : ℝ) :=
      add_le_add hfirst hsecond
    _ = 4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ) := by ring

/-- Explicit ordered unbalanced complete-box bound.  Thus the absolute
constant hidden by the manuscript's `\ll` may be taken to be `4`. -/
theorem edgeCount_le_four_mul_div_fourthRoot_ordered
    {H : Finset (X × Y × Z)} (hH : K222Free H)
    (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hL : 0 < L.card) (hLM : L.card ≤ M.card) (hMR : M.card ≤ R.card) :
    (edgeCount H L M R : ℝ) ≤
      (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
        realFourthRoot (L.card : ℝ) := by
  have hq : 0 < realFourthRoot (L.card : ℝ) := by
    have hx1Nat : 1 ≤ L.card := by omega
    apply realFourthRoot_pos_of_one_le
    exact_mod_cast hx1Nat
  rw [le_div_iff₀ hq]
  simpa [mul_comm] using!
    realFourthRoot_mul_edgeCount_le_four_mul_ordered hH L M R hL hLM hMR

/-- If every hyperedge lies in the displayed product, the codegree sum counts
each hyperedge exactly once. -/
theorem edgeCount_eq_card_of_subset_product
    {H : Finset (X × Y × Z)} {L : Finset X} {M : Finset Y} {R : Finset Z}
    (hsub : H ⊆ L ×ˢ (M ×ˢ R)) :
    edgeCount H L M R = H.card := by
  have hmap : Set.MapsTo Prod.snd
      (H : Set (X × Y × Z)) ((M ×ˢ R : Finset (Y × Z)) : Set (Y × Z)) := by
    intro e he
    exact (Finset.mem_product.mp (hsub he)).2
  have hfiber (yz : Y × Z) (hyz : yz ∈ M ×ˢ R) :
      (H.filter fun e => e.2 = yz).card = codegree H L yz.1 yz.2 := by
    rw [codegree]
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      have heH := (Finset.mem_filter.mp he).1
      have heyz := (Finset.mem_filter.mp he).2
      have heLMR := Finset.mem_product.mp (hsub heH)
      exact Finset.mem_filter.mpr
        ⟨heLMR.1, by simpa [← heyz] using! heH⟩
    · intro e₁ he₁ e₂ he₂ hfst
      apply Prod.ext hfst
      exact (Finset.mem_filter.mp he₁).2.trans
        (Finset.mem_filter.mp he₂).2.symm
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      have hxyz := (Finset.mem_filter.mp hx).2
      exact ⟨(x, yz), Finset.mem_filter.mpr ⟨hxyz, rfl⟩, rfl⟩
  calc
    edgeCount H L M R =
        ∑ yz ∈ M ×ˢ R, codegree H L yz.1 yz.2 :=
      edgeCount_eq_sum_product H L M R
    _ = ∑ yz ∈ M ×ˢ R, (H.filter fun e => e.2 = yz).card := by
      apply Finset.sum_congr rfl
      intro yz hyz
      exact (hfiber yz hyz).symm
    _ = H.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmap

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- The ordered, supported form of the manuscript's unbalanced
`K^{(3)}_{2,2,2}` lemma, with explicit absolute constant `4`. -/
theorem card_le_four_mul_div_fourthRoot_ordered
    {H : Finset (X × Y × Z)} (hH : K222Free H)
    (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hsub : H ⊆ L ×ˢ (M ×ˢ R))
    (hL : 0 < L.card) (hLM : L.card ≤ M.card) (hMR : M.card ≤ R.card) :
    (H.card : ℝ) ≤
      (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
        realFourthRoot (L.card : ℝ) := by
  classical
  rw [← edgeCount_eq_card_of_subset_product hsub]
  exact edgeCount_le_four_mul_div_fourthRoot_ordered hH L M R hL hLM hMR

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- Fully symmetric unbalanced complete-box bound.  No ordering of the three
positive part sizes is assumed; the denominator is the fourth root of their
minimum.  The proof relabels the parts and applies the ordered estimate. -/
theorem card_le_four_mul_div_fourthRoot_min
    {H : Finset (X × Y × Z)} (hH : K222Free H)
    (L : Finset X) (M : Finset Y) (R : Finset Z)
    (hsub : H ⊆ L ×ˢ (M ×ˢ R))
    (hL : 0 < L.card) (hM : 0 < M.card) (hR : 0 < R.card) :
    (H.card : ℝ) ≤
      (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
        realFourthRoot (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
  classical
  by_cases hLM : L.card ≤ M.card
  · by_cases hLR : L.card ≤ R.card
    · by_cases hMR : M.card ≤ R.card
      · have hb := card_le_four_mul_div_fourthRoot_ordered
            hH L M R hsub hL hLM hMR
        simpa [Nat.min_eq_left hMR, Nat.min_eq_left hLM] using! hb
      · have hRM : R.card ≤ M.card := (lt_of_not_ge hMR).le
        have hb := card_le_four_mul_div_fourthRoot_ordered
          (k222Free_swapYZ hH) L R M (swapYZ_subset_product hsub)
          hL hLR hRM
        calc
          (H.card : ℝ) = ((swapYZ H).card : ℝ) := by simp
          _ ≤ (4 * (L.card : ℝ) * (R.card : ℝ) * (M.card : ℝ)) /
              realFourthRoot (L.card : ℝ) := hb
          _ = (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
              realFourthRoot
                (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
            have hmin : Nat.min L.card (Nat.min M.card R.card) = L.card := by
              exact Nat.min_eq_left (le_min hLM hLR)
            rw [hmin]
            ring
    · have hRL : R.card ≤ L.card := (lt_of_not_ge hLR).le
      have hRM : R.card ≤ M.card := hRL.trans hLM
      have hrot : K222Free (rotateXYZ (rotateXYZ H)) :=
        k222Free_rotateXYZ (k222Free_rotateXYZ hH)
      have hsubrot :
          rotateXYZ (rotateXYZ H) ⊆ R ×ˢ (L ×ˢ M) :=
        rotateXYZ_subset_product (rotateXYZ_subset_product hsub)
      have hb := card_le_four_mul_div_fourthRoot_ordered
        hrot R L M hsubrot hR hRL hLM
      calc
        (H.card : ℝ) = ((rotateXYZ (rotateXYZ H)).card : ℝ) := by simp
        _ ≤ (4 * (R.card : ℝ) * (L.card : ℝ) * (M.card : ℝ)) /
            realFourthRoot (R.card : ℝ) := hb
        _ = (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
            realFourthRoot
              (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
          have hmin : Nat.min L.card (Nat.min M.card R.card) = R.card := by
            apply Nat.le_antisymm
            · exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
            · exact Nat.le_min_of_le_of_le hRL
                (Nat.le_min_of_le_of_le hRM (Nat.le_refl _))
          rw [hmin]
          ring
  · have hML : M.card ≤ L.card := (lt_of_not_ge hLM).le
    by_cases hMR : M.card ≤ R.card
    · by_cases hLR : L.card ≤ R.card
      · have hrot := k222Free_rotateXYZ hH
        have hsrot := rotateXYZ_subset_product hsub
        have hb := card_le_four_mul_div_fourthRoot_ordered
          (k222Free_swapYZ hrot) M L R (swapYZ_subset_product hsrot)
          hM hML hLR
        calc
          (H.card : ℝ) = ((swapYZ (rotateXYZ H)).card : ℝ) := by simp
          _ ≤ (4 * (M.card : ℝ) * (L.card : ℝ) * (R.card : ℝ)) /
              realFourthRoot (M.card : ℝ) := hb
          _ = (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
              realFourthRoot
                (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
            have hmin : Nat.min L.card (Nat.min M.card R.card) = M.card := by
              apply Nat.le_antisymm
              · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
              · exact Nat.le_min_of_le_of_le hML
                  (Nat.le_min_of_le_of_le (Nat.le_refl _) hMR)
            rw [hmin]
            ring
      · have hRL : R.card ≤ L.card := (lt_of_not_ge hLR).le
        have hrot := k222Free_rotateXYZ hH
        have hsrot := rotateXYZ_subset_product hsub
        have hb := card_le_four_mul_div_fourthRoot_ordered
          hrot M R L hsrot hM hMR hRL
        calc
          (H.card : ℝ) = ((rotateXYZ H).card : ℝ) := by simp
          _ ≤ (4 * (M.card : ℝ) * (R.card : ℝ) * (L.card : ℝ)) /
              realFourthRoot (M.card : ℝ) := hb
          _ = (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
              realFourthRoot
                (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
            have hmin : Nat.min L.card (Nat.min M.card R.card) = M.card := by
              apply Nat.le_antisymm
              · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
              · exact Nat.le_min_of_le_of_le hML
                  (Nat.le_min_of_le_of_le (Nat.le_refl _) hMR)
            rw [hmin]
            ring
    · have hRM : R.card ≤ M.card := (lt_of_not_ge hMR).le
      have hRL : R.card ≤ L.card := hRM.trans hML
      have hrot : K222Free (rotateXYZ (rotateXYZ H)) :=
        k222Free_rotateXYZ (k222Free_rotateXYZ hH)
      have hsrot :
          rotateXYZ (rotateXYZ H) ⊆ R ×ˢ (L ×ˢ M) :=
        rotateXYZ_subset_product (rotateXYZ_subset_product hsub)
      have hb := card_le_four_mul_div_fourthRoot_ordered
        (k222Free_swapYZ hrot) R M L (swapYZ_subset_product hsrot)
        hR hRM hML
      calc
        (H.card : ℝ) = ((swapYZ (rotateXYZ (rotateXYZ H))).card : ℝ) := by simp
        _ ≤ (4 * (R.card : ℝ) * (M.card : ℝ) * (L.card : ℝ)) /
            realFourthRoot (R.card : ℝ) := hb
        _ = (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
            realFourthRoot
              (Nat.min L.card (Nat.min M.card R.card) : ℝ) := by
          have hmin : Nat.min L.card (Nat.min M.card R.card) = R.card := by
            apply Nat.le_antisymm
            · exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
            · exact Nat.le_min_of_le_of_le hRL
                (Nat.le_min_of_le_of_le hRM (Nat.le_refl _))
          rw [hmin]
          ring

end Tripartite

end Erdos796
