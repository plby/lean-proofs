/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.OneDimensionalDiscrepancy
import ErdosProblems.Erdos1124.ProductGrid
import ErdosProblems.Erdos1124.TorusAction

/-!
# The product-orbit bridge

The quantitative construction used for circle squaring first chooses two
independent families of thirty-two rotations of the circle.  This file puts
the first family in the first coordinate of the two-torus, puts the second
family in the second coordinate, and identifies the resulting
sixty-four-dimensional orbit cubes with Cartesian products of the two
one-dimensional orbit boxes.

The final lemmas also record the exact reindexing needed by
`ProductGrid`: after each one-dimensional box has been enumerated by
`Fin (m*q)`, its product enumeration is precisely the indexing of the
sixty-four-dimensional cube.  Consequently `TorusAction.cubeDensity` is
literally a `ProductGrid.normalizedFineCount`.
-/

open scoped BigOperators

namespace Erdos1124.ProductOrbit

noncomputable section

open OneDimensionalDiscrepancy

/-- A local unambiguous name for the additive unit circle. -/
abbrev OCircle := OneDimensionalDiscrepancy.Circle

/-- Number of generators used in each coordinate. -/
abbrev coordinateDimension : ℕ := 32

/-- Total number of coordinate-supported generators. -/
abbrev productDimension : ℕ := coordinateDimension + coordinateDimension

/-- Put a circle element in the first coordinate of the two-torus. -/
def firstCoordinate (z : OCircle) : TorusAction.Torus 2 := ![z, 0]

/-- Put a circle element in the second coordinate of the two-torus. -/
def secondCoordinate (z : OCircle) : TorusAction.Torus 2 := ![0, z]

@[simp] lemma firstCoordinate_apply_zero (z : OCircle) : firstCoordinate z 0 = z := rfl
@[simp] lemma firstCoordinate_apply_one (z : OCircle) : firstCoordinate z 1 = 0 := rfl
@[simp] lemma secondCoordinate_apply_zero (z : OCircle) : secondCoordinate z 0 = 0 := rfl
@[simp] lemma secondCoordinate_apply_one (z : OCircle) : secondCoordinate z 1 = z := rfl

/-- The concrete `Fin 32 ⊕ Fin 32 ≃ Fin 64` used throughout the bridge. -/
abbrev generatorEquiv : Fin coordinateDimension ⊕ Fin coordinateDimension ≃
    Fin productDimension := finSumFinEquiv

/-- The two circle-generator families, supported in separate torus
coordinates and joined using `generatorEquiv`. -/
def productGenerators
    (u v : Fin coordinateDimension → OCircle) :
    Fin productDimension → TorusAction.Torus 2 :=
  fun i => Sum.elim (fun j => firstCoordinate (u j))
    (fun j => secondCoordinate (v j)) (generatorEquiv.symm i)

@[simp] lemma productGenerators_left
    (u v : Fin coordinateDimension → OCircle) (i : Fin coordinateDimension) :
    productGenerators u v (generatorEquiv (Sum.inl i)) = firstCoordinate (u i) := by
  simp [productGenerators]

@[simp] lemma productGenerators_right
    (u v : Fin coordinateDimension → OCircle) (i : Fin coordinateDimension) :
    productGenerators u v (generatorEquiv (Sum.inr i)) = secondCoordinate (v i) := by
  unfold productGenerators
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma productGenerators_castAdd
    (u v : Fin coordinateDimension → OCircle) (i : Fin coordinateDimension) :
    productGenerators u v (Fin.castAdd coordinateDimension i) =
      firstCoordinate (u i) := by
  simpa [generatorEquiv] using productGenerators_left u v i

@[simp] lemma productGenerators_natAdd
    (u v : Fin coordinateDimension → OCircle) (i : Fin coordinateDimension) :
    productGenerators u v (Fin.natAdd coordinateDimension i) =
      secondCoordinate (v i) := by
  simpa [generatorEquiv] using productGenerators_right u v i

@[simp] lemma productGenerators_addNat
    (u v : Fin coordinateDimension → OCircle) (i : Fin coordinateDimension) :
    productGenerators u v (Fin.addNat i coordinateDimension) =
      secondCoordinate (v i) := by
  rw [show Fin.addNat i coordinateDimension =
      Fin.natAdd coordinateDimension i by
    apply Fin.ext
    simp]
  exact productGenerators_natAdd u v i

/-- Split a sixty-four-dimensional coefficient vector into its two
thirty-two-dimensional coordinate vectors. -/
def splitCoefficients :
    (Fin productDimension → ℤ) ≃
      (Fin coordinateDimension → ℤ) × (Fin coordinateDimension → ℤ) :=
  (Equiv.arrowCongr generatorEquiv (Equiv.refl ℤ)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] lemma splitCoefficients_fst (n : Fin productDimension → ℤ)
    (i : Fin coordinateDimension) :
    (splitCoefficients n).1 i = n (generatorEquiv (Sum.inl i)) := rfl

@[simp] lemma splitCoefficients_snd (n : Fin productDimension → ℤ)
    (i : Fin coordinateDimension) :
    (splitCoefficients n).2 i = n (generatorEquiv (Sum.inr i)) := rfl

/-- Displacement on one copy of the circle. -/
def circleDisplacement (u : Fin coordinateDimension → OCircle)
    (n : Fin coordinateDimension → ℤ) : OCircle :=
  ∑ i, n i • u i

/-- The displacement of the coordinate-supported action is the ordered
pair of the two circle displacements. -/
theorem displacement_productGenerators
    (u v : Fin coordinateDimension → OCircle)
    (n : Fin productDimension → ℤ) :
    TorusAction.displacement (productGenerators u v) n =
      ![circleDisplacement u (splitCoefficients n).1,
        circleDisplacement v (splitCoefficients n).2] := by
  funext j
  simp only [TorusAction.displacement, Finset.sum_apply, Pi.smul_apply]
  fin_cases j <;>
    rw [← Equiv.sum_comp generatorEquiv
        (fun i => n i • productGenerators u v i _)] <;>
    simp [circleDisplacement]

/-- Freeness of a family of circle rotations. -/
def CircleFree (u : Fin coordinateDimension → OCircle) : Prop :=
  Function.Injective (circleDisplacement u)

/-- Independent free circle actions give a free action on the two-torus. -/
theorem free_productGenerators {u v : Fin coordinateDimension → OCircle}
    (hu : CircleFree u) (hv : CircleFree v) :
    TorusAction.Free (productGenerators u v) := by
  intro a b hab
  apply splitCoefficients.injective
  apply Prod.ext
  · apply hu
    have h := congrFun hab 0
    simpa [displacement_productGenerators] using h
  · apply hv
    have h := congrFun hab 1
    simpa [displacement_productGenerators] using h

/-- Split a sixty-four-dimensional cube index into the two coordinate box
indices. -/
def splitCubeIndex (N : ℕ) :
    (Fin productDimension → Fin N) ≃
      (Fin coordinateDimension → Fin N) ×
        (Fin coordinateDimension → Fin N) :=
  (Equiv.arrowCongr generatorEquiv (Equiv.refl (Fin N))).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] lemma splitCubeIndex_fst {N : ℕ}
    (a : Fin productDimension → Fin N) (i : Fin coordinateDimension) :
    (splitCubeIndex N a).1 i = a (generatorEquiv (Sum.inl i)) := rfl

@[simp] lemma splitCubeIndex_snd {N : ℕ}
    (a : Fin productDimension → Fin N) (i : Fin coordinateDimension) :
    (splitCubeIndex N a).2 i = a (generatorEquiv (Sum.inr i)) := rfl

/-- A point in a negative one-dimensional orbit box. -/
def circleOrbitPoint (u : Fin coordinateDimension → OCircle) (x : OCircle)
    {N : ℕ} (a : Fin coordinateDimension → Fin N) : OCircle :=
  circleDisplacement u (-Flow.cubeIndex a) + x

/-- The two coordinates of a product orbit point are exactly the two
one-dimensional orbit-box points. -/
theorem orbitPoint_productGenerators
    (u v : Fin coordinateDimension → OCircle) (x : TorusAction.Torus 2)
    {N : ℕ} (a : Fin productDimension → Fin N) :
    TorusAction.orbitPoint (productGenerators u v) x a =
      ![circleOrbitPoint u (x 0) (splitCubeIndex N a).1,
        circleOrbitPoint v (x 1) (splitCubeIndex N a).2] := by
  have hfst : (splitCoefficients (-Flow.cubeIndex a)).1 =
      -Flow.cubeIndex (splitCubeIndex N a).1 := by
    funext i
    simp [Flow.cubeIndex]
  have hsnd : (splitCoefficients (-Flow.cubeIndex a)).2 =
      -Flow.cubeIndex (splitCubeIndex N a).2 := by
    funext i
    simp [Flow.cubeIndex]
  rw [TorusAction.orbitPoint, displacement_productGenerators]
  rw [hfst, hsnd]
  funext j
  fin_cases j <;> simp [circleOrbitPoint]

/-- Under coordinatewise freeness the product orbit cube has exactly
`N^64` points. -/
theorem card_product_cubePoints {u v : Fin coordinateDimension → OCircle}
    (hu : CircleFree u) (hv : CircleFree v) (N : ℕ)
    (x : TorusAction.Torus 2) :
    (TorusAction.cubePoints (productGenerators u v) N x).card =
      N ^ productDimension :=
  TorusAction.card_cubePoints (free_productGenerators hu hv) N x

/-! ## Reindexing by ordered one-dimensional orbit boxes -/

/-- Turn two enumerations of the one-dimensional orbit boxes into an exact
enumeration of the sixty-four-dimensional cube.  The two occurrences of
`finProdFinEquiv` split each ordered rank into its coarse-cell and
within-cell coordinates. -/
def fineIndexCubeEquiv {m q N : ℕ}
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    ProductGrid.FineIndex 2 m q ≃
      (Fin productDimension → Fin N) :=
  (finTwoArrowEquiv (Fin m × Fin q)).trans
    ((finProdFinEquiv.prodCongr finProdFinEquiv).trans
      ((e₀.prodCongr e₁).trans (splitCubeIndex N).symm))

@[simp] lemma splitCubeIndex_fineIndexCubeEquiv_fst {m q N : ℕ}
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N))
    (p : ProductGrid.FineIndex 2 m q) :
    (splitCubeIndex N (fineIndexCubeEquiv e₀ e₁ p)).1 =
      e₀ (finProdFinEquiv (p 0)) := by
  simp [fineIndexCubeEquiv]

@[simp] lemma splitCubeIndex_fineIndexCubeEquiv_snd {m q N : ℕ}
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N))
    (p : ProductGrid.FineIndex 2 m q) :
    (splitCubeIndex N (fineIndexCubeEquiv e₀ e₁ p)).2 =
      e₁ (finProdFinEquiv (p 1)) := by
  simp [fineIndexCubeEquiv]

/-- Real representatives, in `[0,1)`, of the two enumerated orbit boxes. -/
def orderedOrbitSamples {m q N : ℕ}
    (u v : Fin coordinateDimension → OCircle) (x : TorusAction.Torus 2)
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    Fin 2 → Fin (m * q) → ℝ
  | 0, j => ((AddCircle.equivIco 1 0) (circleOrbitPoint u (x 0) (e₀ j)) : ℝ)
  | 1, j => ((AddCircle.equivIco 1 0) (circleOrbitPoint v (x 1) (e₁ j)) : ℝ)

/-- Quotient a point of the fundamental square coordinatewise. -/
def quotientPoint (y : ProductGrid.Point 2) : TorusAction.Torus 2 :=
  fun i => (y i : OCircle)

/-- `ProductGrid.samplePoint` for the ordered orbit enumerations is the
corresponding sixty-four-dimensional product orbit point. -/
theorem quotientPoint_samplePoint_orderedOrbitSamples {m q N : ℕ}
    (u v : Fin coordinateDimension → OCircle) (x : TorusAction.Torus 2)
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N))
    (p : ProductGrid.FineIndex 2 m q) :
    quotientPoint (ProductGrid.samplePoint
      (orderedOrbitSamples u v x e₀ e₁) p) =
      TorusAction.orbitPoint (productGenerators u v) x
        (fineIndexCubeEquiv e₀ e₁ p) := by
  rw [orbitPoint_productGenerators]
  funext j
  fin_cases j <;>
    simp [quotientPoint, ProductGrid.samplePoint, orderedOrbitSamples,
      AddCircle.coe_equivIco]

/-- The existence of either box enumeration forces the numerical identity
`m*q = N^32`. -/
lemma mul_eq_pow_of_boxEquiv {m q N : ℕ}
    (e : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    m * q = N ^ coordinateDimension := by
  simpa using Fintype.card_congr e

/-- Hence the normalization of a product grid is exactly the normalization
of a sixty-four-dimensional orbit cube. -/
lemma product_normalization_eq {m q N : ℕ}
    (e : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    (m : ℝ) ^ 2 * (q : ℝ) ^ 2 = (N : ℝ) ^ productDimension := by
  have h : (m : ℝ) * q = (N : ℝ) ^ coordinateDimension := by
    exact_mod_cast mul_eq_pow_of_boxEquiv e
  rw [show (m : ℝ) ^ 2 * (q : ℝ) ^ 2 = ((m : ℝ) * q) ^ 2 by ring, h]
  norm_num [productDimension, coordinateDimension, ← pow_mul]

/-- The fine-grid predicate count attached to the two ordered orbit
enumerations. -/
noncomputable def orderedFineCount {m q N : ℕ}
    (u v : Fin coordinateDimension → OCircle) (E : Set (TorusAction.Torus 2))
    (x : TorusAction.Torus 2)
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : ProductGrid.FineIndex 2 m q =>
    quotientPoint (ProductGrid.samplePoint
      (orderedOrbitSamples u v x e₀ e₁) p) ∈ E).card

/-- Reindexing the cube count by the product of the two ordered
one-dimensional orbit enumerations. -/
theorem cubeCount_eq_fineCount_card {m q N : ℕ}
    (u v : Fin coordinateDimension → OCircle) (E : Set (TorusAction.Torus 2))
    (x : TorusAction.Torus 2)
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    TorusAction.cubeCount (productGenerators u v) E N x =
      orderedFineCount u v E x e₀ e₁ := by
  classical
  unfold TorusAction.cubeCount orderedFineCount
  let _ := TorusAction.torusAddAction (productGenerators u v)
  rw [← Equiv.sum_comp (fineIndexCubeEquiv e₀ e₁)
    (fun a => if (-Flow.cubeIndex a +ᵥ x) ∈ E then 1 else 0)]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have heq : (-Flow.cubeIndex (fineIndexCubeEquiv e₀ e₁ p) +ᵥ x) =
      quotientPoint (ProductGrid.samplePoint
        (orderedOrbitSamples u v x e₀ e₁) p) := by
    symm
    change quotientPoint (ProductGrid.samplePoint
        (orderedOrbitSamples u v x e₀ e₁) p) =
      TorusAction.orbitPoint (productGenerators u v) x
        (fineIndexCubeEquiv e₀ e₁ p)
    exact
      quotientPoint_samplePoint_orderedOrbitSamples u v x e₀ e₁ p
  rw [heq]

/-- **Product-orbit density identity.**  After ordered enumeration of the
two thirty-two-dimensional circle boxes, `cubeDensity` is exactly the
normalized fine-grid count used by `ProductGrid`. -/
theorem cubeDensity_eq_normalizedFineCount {m q N : ℕ}
    (u v : Fin coordinateDimension → OCircle) (E : Set (TorusAction.Torus 2))
    (x : TorusAction.Torus 2)
    (e₀ e₁ : Fin (m * q) ≃ (Fin coordinateDimension → Fin N)) :
    TorusAction.cubeDensity (productGenerators u v) E N x =
      ProductGrid.normalizedFineCount (fun p : ProductGrid.FineIndex 2 m q =>
        quotientPoint (ProductGrid.samplePoint
          (orderedOrbitSamples u v x e₀ e₁) p) ∈ E) := by
  rw [TorusAction.cubeDensity, ProductGrid.normalizedFineCount]
  rw [cubeCount_eq_fineCount_card]
  change (orderedFineCount u v E x e₀ e₁ : ℝ) / (N : ℝ) ^ productDimension =
    (orderedFineCount u v E x e₀ e₁ : ℝ) /
      ((m : ℝ) ^ 2 * (q : ℝ) ^ 2)
  rw [product_normalization_eq e₀]

end

end Erdos1124.ProductOrbit
