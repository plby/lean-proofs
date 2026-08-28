import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsAlgebra
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturalityCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCoordinateMatrixBlocks

/-!
# Actual coordinate-subtorus maps in Pascal order

The recursive maps insert zeroes in the omitted ambient coordinates. Their
index order is exactly `binomialPascalIndexEquiv`: first omit the first
ambient coordinate, then take it. All maps here are actual continuous maps
of the products of circles; no homology groups are defined in this file.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open CircleTopology

/-- The actual coordinate inclusion indexed by the Pascal decomposition. -/
def coordinateTorusMap : (r n : ℕ) → Fin (r.choose n) → C(ProductTorus n, ProductTorus r)
  | 0, 0, _ => ContinuousMap.const _ 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => ContinuousMap.const _ 0
  | r + 1, n + 1, i =>
      match binomialPascalIndexEquiv r n i with
      | Sum.inl j =>
          ((productTorusSuccHomeomorph r).symm :
            C(Circle × ProductTorus r, ProductTorus (r + 1))).comp
            ((productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j))
      | Sum.inr j =>
          ((productTorusSuccHomeomorph r).symm :
            C(Circle × ProductTorus r, ProductTorus (r + 1))).comp
            ((circleProductMap (coordinateTorusMap r n j)).comp
              (productTorusSuccHomeomorph n :
                C(ProductTorus (n + 1), Circle × ProductTorus n)))

@[simp] theorem coordinateTorusMap_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMap r 0 i = ContinuousMap.const _ 0 := by
  cases r <;> rfl

@[simp] theorem coordinateTorusMap_omit_apply (r n : ℕ) (j : Fin (r.choose (n + 1)))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x =
      Fin.cons 0 (coordinateTorusMap r (n + 1) j x) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

@[simp] theorem coordinateTorusMap_take_apply (r n : ℕ) (j : Fin (r.choose n))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x =
      Fin.cons (x 0) (coordinateTorusMap r n j (fun k => x k.succ)) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

/-- Omitting the first coordinate is the literal fixed-zero section after
splitting the target torus. -/
theorem coordinateTorusMap_omit (r n : ℕ) (j : Fin (r.choose (n + 1))) :
    (productTorusSuccHomeomorph r :
      C(ProductTorus (r + 1), Circle × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) =
      (productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j) := by
  apply ContinuousMap.ext
  intro x
  change productTorusSuccHomeomorph r
      (coordinateTorusMap (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x) = _
  rw [coordinateTorusMap_omit_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- Taking the first coordinate is the literal product with the identity
on the first circle after splitting the source and target tori. -/
theorem coordinateTorusMap_take (r n : ℕ) (j : Fin (r.choose n)) :
    (productTorusSuccHomeomorph r :
      C(ProductTorus (r + 1), Circle × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1)
          ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) =
      (circleProductMap (coordinateTorusMap r n j)).comp
        (productTorusSuccHomeomorph n :
          C(ProductTorus (n + 1), Circle × ProductTorus n)) := by
  apply ContinuousMap.ext
  intro x
  change productTorusSuccHomeomorph r
      (coordinateTorusMap (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x) = _
  rw [coordinateTorusMap_take_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- Every actual coordinate-subtorus map is injective. -/
theorem coordinateTorusMap_injective (r n : ℕ) (i : Fin (r.choose n)) :
    Function.Injective (coordinateTorusMap r n i) := by
  induction r generalizing n with
  | zero =>
      cases n with
      | zero => exact fun _ _ _ => Subsingleton.elim _ _
      | succ n => exact Fin.elim0 i
  | succ r ih =>
      cases n with
      | zero => exact fun _ _ _ => Subsingleton.elim _ _
      | succ n =>
          obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
          cases j with
          | inl j =>
              intro x y h
              apply ih (n + 1) j
              have ht := congrArg (fun z : ProductTorus (r + 1) => fun k : Fin r => z k.succ) h
              simpa only [coordinateTorusMap_omit_apply, Fin.cons_succ] using ht
          | inr j =>
              intro x y h
              apply (productTorusSuccHomeomorph n).injective
              apply Prod.ext
              · change x 0 = y 0
                have hh := congrArg (fun z : ProductTorus (r + 1) => z 0) h
                simpa only [coordinateTorusMap_take_apply, Fin.cons_zero] using hh
              · change (fun k : Fin n => x k.succ) = (fun k : Fin n => y k.succ)
                apply ih n j
                have ht := congrArg (fun z : ProductTorus (r + 1) => fun k : Fin r => z k.succ) h
                simpa only [coordinateTorusMap_take_apply, Fin.cons_succ] using ht

/-- The integral coordinate-inclusion matrix in the same Pascal order. -/
def coordinateTorusMatrix : (r n : ℕ) → Fin (r.choose n) → Matrix (Fin r) (Fin n) ℤ
  | 0, 0, _ => 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => 0
  | r + 1, n + 1, i =>
      match binomialPascalIndexEquiv r n i with
      | Sum.inl j => omitHeadMatrix (coordinateTorusMatrix r (n + 1) j)
      | Sum.inr j => takeHeadMatrix (coordinateTorusMatrix r n j)

@[simp] theorem coordinateTorusMatrix_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMatrix r 0 i = 0 := by
  cases r <;> rfl

@[simp] theorem coordinateTorusMatrix_omit (r n : ℕ) (j : Fin (r.choose (n + 1))) :
    coordinateTorusMatrix (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) =
      omitHeadMatrix (coordinateTorusMatrix r (n + 1) j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

@[simp] theorem coordinateTorusMatrix_take (r n : ℕ) (j : Fin (r.choose n)) :
    coordinateTorusMatrix (r + 1) (n + 1)
        ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) =
      takeHeadMatrix (coordinateTorusMatrix r n j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

/-- The recursively inserted-coordinate map is exactly the map induced
by its integral coordinate-inclusion matrix, on all torus points. -/
theorem coordinateTorusMap_eq_torusMatrixMap (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusMap r n i = torusMatrixMap (coordinateTorusMatrix r n i) := by
  induction r generalizing n with
  | zero =>
      cases n with
      | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
      | succ n => exact Fin.elim0 i
  | succ r ih =>
      cases n with
      | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
      | succ n =>
          obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
          cases j with
          | inl j =>
              apply ContinuousMap.ext
              intro x
              rw [coordinateTorusMap_omit_apply, coordinateTorusMatrix_omit,
                torusMatrixMap_omitHeadMatrix, ih (n + 1) j]
          | inr j =>
              apply ContinuousMap.ext
              intro x
              rw [coordinateTorusMap_take_apply, coordinateTorusMatrix_take,
                torusMatrixMap_takeHeadMatrix, ih n j]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
