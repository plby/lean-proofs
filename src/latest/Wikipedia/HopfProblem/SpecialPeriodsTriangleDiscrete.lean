import Wikipedia.HopfProblem.SpecialPeriodsTriangleGeometry
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# Discreteness of the actual triangle matrix group

Finite point-image tests from the proved ping-pong action isolate the
identity of the generated real special-linear subgroup in its inherited
matrix topology.  The only matrices acting trivially are `1` and `-1`;
a positive diagonal-entry condition separates these two central elements.
-/

noncomputable section

open Function Set UpperHalfPlane
open scoped Topology MatrixGroups Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods


private theorem finiteTest_mixed_word {G α : Type*} [Group G] [MulAction G α]
    {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (U : Bool → Set α)
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H false)) (xB : α) (hxB : xB ∈ U true)
    (w : Monoid.CoprodI.NeWord H false true) :
    ∃ h : H false,
      (f false h * Monoid.CoprodI.lift f w.prod * (f false h)⁻¹) • xB ∈ U false := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : Monoid.CoprodI.NeWord H false false :=
    Monoid.CoprodI.NeWord.append (w.mulHead h hnot1) (by decide)
      (Monoid.CoprodI.NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : Monoid.CoprodI.lift f w'.prod • xB ∈ U false :=
    Set.smul_set_subset_iff.mp
      (Monoid.CoprodI.lift_word_ping_pong f U hpp w' (by decide)) hxB
  refine ⟨h, ?_⟩
  simpa [w'] using hw'

private theorem finiteTest_coprodI {G α : Type*} [Group G] [MulAction G α]
    {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (U : Bool → Set α) (hdisj : Disjoint (U false) (U true))
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H false))
    (xA xB : α) (hxA : xA ∈ U false) (hxB : xB ∈ U true)
    (w : Monoid.CoprodI H)
    (hA : Monoid.CoprodI.lift f w • xA ∈ U false)
    (hB : ∀ h : H false,
      (f false h * Monoid.CoprodI.lift f w * (f false h)⁻¹) • xB ∈ U true ∧
      (f false h * (Monoid.CoprodI.lift f w)⁻¹ * (f false h)⁻¹) • xB ∈ U true) :
    Monoid.CoprodI.lift f w = 1 := by
  classical
  let r := Monoid.CoprodI.Word.equiv (M := H) w
  have hr : r.prod = w := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply w
  by_cases hr0 : r = Monoid.CoprodI.Word.empty
  · have hw1 : w = 1 := by
      rw [← hr, hr0, Monoid.CoprodI.Word.prod_empty]
    simp [hw1]
  obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word r hr0
  have hvprod : v.prod = w := by
    change v.toWord.prod = w
    rw [hv]
    exact hr
  rw [← hvprod] at hA hB ⊢
  suffices False by contradiction
  cases i <;> cases j
  · have hm : Monoid.CoprodI.lift f v.prod • xB ∈ U false :=
      Set.smul_set_subset_iff.mp
        (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxB
    have hn : Monoid.CoprodI.lift f v.prod • xB ∈ U true := by
      simpa only [map_one, one_mul, inv_one, mul_one] using (hB 1).1
    exact hdisj.le_bot ⟨hm, hn⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word f U hpp hcard xB hxB v
    exact hdisj.le_bot ⟨hm, (hB h).1⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word f U hpp hcard xB hxB v.inv
    have hm' : (f false h * (Monoid.CoprodI.lift f v.prod)⁻¹ *
        (f false h)⁻¹) • xB ∈ U false := by
      simpa only [Monoid.CoprodI.NeWord.inv_prod, map_inv] using hm
    exact hdisj.le_bot ⟨hm', (hB h).2⟩
  · have hm : Monoid.CoprodI.lift f v.prod • xA ∈ U true :=
      Set.smul_set_subset_iff.mp
        (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxA
    exact hdisj.le_bot ⟨hA, hm⟩

private theorem finiteTest_cyclicPowerHom_two {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem finiteTest_cyclicPowerHom_three {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

/-- Seven point-membership tests, one in `X` and two for each of the three
cyclic conjugators in `Y`, detect the identity in the triangle image. -/
theorem triangleLift_eq_one_of_pingPong_finite_tests
    {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1)
    (X Y : Set α) (hXY : Disjoint X Y)
    (ha₁ : MapsTo (fun z => a • z) Y X)
    (ha₂ : MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : MapsTo (fun z => b • z) X Y)
    (hb₂ : MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : MapsTo (fun z => b ^ 3 • z) X Y)
    (xA xB : α) (hxA : xA ∈ X) (hxB : xB ∈ Y) (w : TriangleGroup)
    (hA : triangleLift a b ha hb w • xA ∈ X)
    (hB : ∀ h : Multiplicative (ZMod 3),
      (cyclicPowerHom 3 a ha h * triangleLift a b ha hb w *
        (cyclicPowerHom 3 a ha h)⁻¹) • xB ∈ Y ∧
      (cyclicPowerHom 3 a ha h * (triangleLift a b ha hb w)⁻¹ *
        (cyclicPowerHom 3 a ha h)⁻¹) • xB ∈ Y) :
    triangleLift a b ha hb w = 1 := by
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
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij g hg
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
      · rw [finiteTest_cyclicPowerHom_two 3 a ha]
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
      · rw [finiteTest_cyclicPowerHom_two 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [finiteTest_cyclicPowerHom_three 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  have hcard : 3 ≤ Cardinal.mk (H false) := by
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp
  have heval : triangleLift a b ha hb w = Monoid.CoprodI.lift f (toI w) :=
    DFunLike.congr_fun hrepresentation w
  rw [heval] at hA hB ⊢
  exact finiteTest_coprodI f U hXY hpp hcard xA xB hxA hxB (toI w) hA hB


namespace Triangle

/-- The algebraic subgroup generated by the two actual real matrices.
The topology below is the inherited subspace topology, not a chosen discrete one. -/
def matrixGroup : Subgroup (SL(2, ℝ)) :=
  Subgroup.closure ({generatorOneSL, generatorTwoSL} : Set (SL(2, ℝ)))

theorem generatorOneSL_mem_matrixGroup : generatorOneSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

theorem generatorTwoSL_mem_matrixGroup : generatorTwoSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

theorem cuspSL_mem_matrixGroup : cuspSL ∈ matrixGroup := by
  have h := matrixGroup.inv_mem
    (matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup)
  simpa only [generatorOneSL_mul_generatorTwoSL, cuspSL] using h

theorem neg_one_mem_matrixGroup : (-1 : SL(2, ℝ)) ∈ matrixGroup := by
  have h := matrixGroup.pow_mem generatorOneSL_mem_matrixGroup 3
  simpa only [generatorOneSL_cube] using h

theorem matrixGroup_map_realSLPermutation :
    matrixGroup.map realSLPermutation = triangleGeometricRepresentation.range := by
  rw [matrixGroup, MonoidHom.map_closure, Set.image_pair, triangle_range]
  simp only [triangleGeometricRepresentation_generator₁,
    triangleGeometricRepresentation_generator₂, generatorOnePerm, generatorTwoPerm]

/-- Every element of the generated matrix group acts as an element of
the constructed abstract triangle group. -/
theorem matrixGroup_permutation_lift (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) :
    ∃ w : TriangleGroup, triangleGeometricRepresentation w = realSLPermutation A := by
  have hm : realSLPermutation A ∈ matrixGroup.map realSLPermutation := ⟨A, hA, rfl⟩
  rw [matrixGroup_map_realSLPermutation] at hm
  exact hm

/-- Every abstract triangle transformation has a lift in the generated
matrix subgroup itself. -/
theorem triangleGeometricRepresentation_matrixGroup_lift (w : TriangleGroup) :
    ∃ A : matrixGroup, realSLPermutation A = triangleGeometricRepresentation w := by
  have hm : triangleGeometricRepresentation w ∈ triangleGeometricRepresentation.range :=
    ⟨w, rfl⟩
  rw [← matrixGroup_map_realSLPermutation] at hm
  obtain ⟨A, hA, hA'⟩ := hm
  exact ⟨⟨A, hA⟩, hA'⟩

/-- The exact ineffective kernel of the actual real special-linear action. -/
theorem realSLPermutation_eq_one_iff (A : SL(2, ℝ)) :
    realSLPermutation A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    have hfix : ∀ z : ℍ, Matrix.SpecialLinearGroup.mapGL ℝ A • z = z := by
      intro z
      change realSLPermutation A z = z
      rw [h]
      rfl
    have hc := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp hfix
    obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
    change Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) ℝ) at hr
    have hs : r ^ 2 = 1 := by
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using
        congrArg Matrix.det hr
    rcases sq_eq_one_iff.mp hs with h₁ | hneg
    · left
      apply Subtype.ext
      simpa [h₁] using hr.symm
    · right
      apply Subtype.ext
      simpa only [hneg, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] using hr.symm
  · rintro (rfl | rfl)
    · exact map_one realSLPermutation
    · exact realSLPermutation_neg_one

def testPointOne : ℍ := UpperHalfPlane.I

def testPointTwo : ℍ := ⟨(-2 : ℂ) + Complex.I, by norm_num⟩

theorem testPointOne_mem : testPointOne ∈ pingPongOne := by
  norm_num [testPointOne, pingPongOne]

theorem testPointTwo_mem : testPointTwo ∈ pingPongTwo := by
  norm_num [testPointTwo, pingPongTwo]

theorem pingPongOne_isOpen : IsOpen pingPongOne :=
  isOpen_lt continuous_const UpperHalfPlane.continuous_re

theorem pingPongTwo_isOpen : IsOpen pingPongTwo :=
  isOpen_lt UpperHalfPlane.continuous_re continuous_const

/-- Three matrix representatives for the order-three cyclic conjugators. -/
def cyclicConjugator (h : Multiplicative (ZMod 3)) : SL(2, ℝ) :=
  generatorOneSL ^ h.toAdd.val

theorem cyclicConjugator_permutation (h : Multiplicative (ZMod 3)) :
    realSLPermutation (cyclicConjugator h) =
      cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h := by
  rw [cyclicConjugator, map_pow]
  change generatorOnePerm ^ h.toAdd.val = _
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd,
    zpow_natCast] using
    (cyclicPowerHom_intCast 3 generatorOnePerm generatorOnePerm_cube (h.toAdd.val : ℤ)).symm

/-- Seven open point-image tests, together with a sign separating the
two central matrices. -/
def identityTestSet : Set (SL(2, ℝ)) := {A |
  0 < A 0 0 ∧ A • testPointOne ∈ pingPongOne ∧
  ∀ h : Multiplicative (ZMod 3),
    (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
    (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo}

theorem identityTestSet_isOpen : IsOpen identityTestSet := by
  have he : IsOpen {A : SL(2, ℝ) | 0 < A 0 0} :=
    isOpen_lt continuous_const (by fun_prop)
  have h₁ : IsOpen {A : SL(2, ℝ) | A • testPointOne ∈ pingPongOne} :=
    pingPongOne_isOpen.preimage (by fun_prop)
  have h₂ (h : Multiplicative (ZMod 3)) : IsOpen {A : SL(2, ℝ) |
      (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
      (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo} :=
    (pingPongTwo_isOpen.preimage (by fun_prop)).inter
      (pingPongTwo_isOpen.preimage (by fun_prop))
  simpa only [identityTestSet, ofPred_and, ofPred_forall] using
    he.inter (h₁.inter (isOpen_iInter_of_finite h₂))

theorem one_mem_identityTestSet : (1 : SL(2, ℝ)) ∈ identityTestSet := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  · simpa using testPointOne_mem
  · intro h
    simpa using And.intro testPointTwo_mem testPointTwo_mem

/-- The seven tests exclude every nonidentity transformation in the
actual triangle image. -/
theorem realSLPermutation_eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) :
    realSLPermutation A = 1 := by
  obtain ⟨w, hw⟩ := matrixGroup_permutation_lift A hA
  rw [← hw]
  refine triangleLift_eq_one_of_pingPong_finite_tests
    generatorOnePerm generatorTwoPerm generatorOnePerm_cube generatorTwoPerm_fourth
    pingPongOne pingPongTwo pingPong_disjoint ?_ ?_ ?_ ?_ ?_
    testPointOne testPointTwo testPointOne_mem testPointTwo_mem w ?_ ?_
  · intro z hz
    exact generatorOne_pingPong hz
  · intro z hz
    change (generatorOnePerm ^ 2) z ∈ pingPongOne
    rw [generatorOnePerm_pow_apply]
    exact generatorOne_sq_pingPong hz
  · intro z hz
    exact generatorTwo_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 2) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_sq_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 3) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_cube_pingPong hz
  · change triangleGeometricRepresentation w testPointOne ∈ pingPongOne
    rw [hw]
    exact hT.2.1
  · intro h
    change
      (cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
        triangleGeometricRepresentation w *
        (cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
          testPointTwo ∈ pingPongTwo ∧
      (cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
        (triangleGeometricRepresentation w)⁻¹ *
        (cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
          testPointTwo ∈ pingPongTwo
    rw [hw, ← cyclicConjugator_permutation]
    have ht := hT.2.2 h
    change
      realSLPermutation (cyclicConjugator h * A * (cyclicConjugator h)⁻¹)
          testPointTwo ∈ pingPongTwo ∧
      realSLPermutation (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹)
          testPointTwo ∈ pingPongTwo at ht
    simpa only [map_mul, map_inv] using ht

/-- The additional positive matrix entry separates the two central
matrices, so the open test set isolates the actual matrix identity. -/
theorem eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) : A = 1 := by
  rcases (realSLPermutation_eq_one_iff A).mp
    (realSLPermutation_eq_one_of_mem_identityTestSet hA hT) with h | h
  · exact h
  · have hp := hT.1
    subst A
    norm_num [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply] at hp

theorem identityTestSet_preimage_matrixGroup :
    (fun A : matrixGroup => (A : SL(2, ℝ))) ⁻¹' identityTestSet = {1} := by
  ext A
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr
      (Subtype.ext (eq_one_of_mem_identityTestSet A.property h))
  · rintro rfl
    exact one_mem_identityTestSet

/-- The generated subgroup is discrete in its inherited real-matrix
topology.  No discrete topology is assigned by definition. -/
instance matrixGroup_discrete : DiscreteTopology matrixGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  rw [← identityTestSet_preimage_matrixGroup]
  exact identityTestSet_isOpen.preimage continuous_subtype_val

theorem matrixGroup_isClosed : IsClosed (matrixGroup : Set (SL(2, ℝ))) :=
  Subgroup.isClosed_of_discrete

/-- Proper discontinuity follows for this proved-discrete subgroup from
the proper special-linear action on the upper half-plane. -/
instance matrixGroup_properlyDiscontinuous : ProperlyDiscontinuousSMul matrixGroup ℍ :=
  inferInstance

/-- The subgroup action is proper as a continuous group action as well. -/
instance matrixGroup_properSMul : ProperSMul matrixGroup ℍ := by
  have : IsClosed (matrixGroup : Set (SL(2, ℝ))) := matrixGroup_isClosed
  infer_instance

theorem matrixGroup_isCompact_transporter {K L : Set ℍ}
    (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact {g : matrixGroup | (g • K ∩ L).Nonempty} :=
  ProperSMul.isCompact_setOfPred_inter_nonempty hK hL

/-- Compact subsets of the upper half-plane have only finitely many
translating subgroup elements that can make them intersect. -/
theorem matrixGroup_finite_compact_transporter {K L : Set ℍ}
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : matrixGroup | (g • K ∩ L).Nonempty}.Finite :=
  isCompact_iff_finite.mp (matrixGroup_isCompact_transporter hK hL)

/-- Only finitely many generated matrices send a fixed point into a
compact subset of the upper half-plane. -/
theorem matrixGroup_finite_orbit_candidates (z : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    {g : matrixGroup | g • z ∈ K}.Finite := by
  simpa only [Set.smul_set_singleton, Set.singleton_inter_nonempty] using
    matrixGroup_finite_compact_transporter (isCompact_singleton (x := z)) hK

end Triangle
end Wikipedia.HopfProblem.SpecialPeriods
