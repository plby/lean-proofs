import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldFibres
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldCompact
import Wikipedia.HopfProblem.ConifoldStandardBoundary

/-!
# The genuine native conifold-boundary homeomorphism

The original matrix map restricts to a continuous bijection from the
compact normal-radius boundary onto the literal determinant-zero
Frobenius level. Compactness and the actual Hausdorff target prove that
its inverse is continuous. The resulting toric-boundary homeomorphism
retains the original matrix formula and the opposite-weight circle action.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ConifoldStandardBoundary

/-- The original product matrix map restricted to its literal radius level. -/
def productBoundaryMap (r : ℝ) (p : ProductBoundary r) : ConifoldBoundary r :=
  ⟨productMap p.val, productMap_det p.val,
    (frobeniusSq_productMap p.val).trans p.property⟩

@[simp] theorem productBoundaryMap_val (r : ℝ) (p : ProductBoundary r) :
    (productBoundaryMap r p).val = productMap p.val := rfl

theorem productBoundary_fibre_ne_zero {r : ℝ} (hr : r ≠ 0) (p : ProductBoundary r) :
    p.val.2 ≠ 0 := by
  intro h
  have he := p.property
  rw [h, radiusSq_zero] at he
  exact pow_ne_zero 2 hr he.symm

/-- Nonzero radius removes exactly the exceptional zero fibre. -/
theorem productBoundaryMap_injective {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (productBoundaryMap r) := by
  intro p q he
  apply Subtype.ext
  exact @productMap_injOn p.val (productBoundary_fibre_ne_zero hr p)
    q.val (productBoundary_fibre_ne_zero hr q) (congrArg Subtype.val he)

/-- The explicit elementary matrix representatives have exactly the required radius. -/
theorem productBoundaryMap_surjective (r : ℝ) :
    Function.Surjective (productBoundaryMap r) := by
  intro M
  obtain ⟨p, hp⟩ := exists_productMap_of_det_zero M.val M.property.1
  have hrad : radiusSq p.2 = r ^ 2 := by
    rw [← frobeniusSq_productMap, hp]
    exact M.property.2
  exact ⟨⟨p, hrad⟩, Subtype.ext hp⟩

theorem continuous_productBoundaryMap (r : ℝ) : Continuous (productBoundaryMap r) :=
  (continuous_productMap.comp continuous_subtype_val).subtype_mk _

/-- The actual product normal boundary and literal conifold link are homeomorphic. -/
def productBoundaryHomeomorph {r : ℝ} (hr : r ≠ 0) :
    ProductBoundary r ≃ₜ ConifoldBoundary r :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (productBoundaryMap r)
      ⟨productBoundaryMap_injective hr, productBoundaryMap_surjective r⟩)
    (continuous_productBoundaryMap r)

@[simp] theorem productBoundaryHomeomorph_apply_val {r : ℝ} (hr : r ≠ 0)
    (p : ProductBoundary r) :
    (productBoundaryHomeomorph hr p).val = productMap p.val := rfl

/-- The genuine toric radius boundary maps to the original rank-one matrix level. -/
def toricBoundaryHomeomorph {r : ℝ} (hr : r ≠ 0) :
    ToricBoundary r ≃ₜ ConifoldBoundary r :=
  (productToricBoundaryHomeomorph r).symm.trans (productBoundaryHomeomorph hr)

@[simp] theorem toricBoundaryHomeomorph_apply_val {r : ℝ} (hr : r ≠ 0)
    (y : ToricBoundary r) :
    (toricBoundaryHomeomorph hr y).val = toricMap y.val := rfl

/-- The actual inverse point maps back to the given original matrix. -/
theorem toricMap_toricBoundaryHomeomorph_symm {r : ℝ} (hr : r ≠ 0)
    (M : ConifoldBoundary r) :
    toricMap ((toricBoundaryHomeomorph hr).symm M).val = M.val := by
  have h := congrArg Subtype.val ((toricBoundaryHomeomorph hr).apply_symm_apply M)
  exact h

/-- The scalar normal action restricted to the actual product radius level. -/
def productBoundaryCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) (p : ProductBoundary r) :
    ProductBoundary r :=
  ⟨(p.val.1, u • p.val.2), (radiusSq_unit_smul u hu p.val.2).trans p.property⟩

@[simp] theorem productBoundaryCircle_val {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (p : ProductBoundary r) :
    (productBoundaryCircle u hu p).val = (p.val.1, u • p.val.2) := rfl

theorem continuous_productBoundaryCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) :
    Continuous (productBoundaryCircle (r := r) u hu) := by
  have hc : Continuous (fun p : ProductBoundary r => (p.val.1, u • p.val.2)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_const : Continuous (fun _ : ProductBoundary r => u)).smul
        (continuous_snd.comp continuous_subtype_val))
  exact hc.subtype_mk _

/-- The actual product boundary map has the exact original matrix circle weights. -/
theorem productBoundaryHomeomorph_circle {r : ℝ} (hr : r ≠ 0)
    (u : ℂ) (hu : ‖u‖ = 1) (p : ProductBoundary r) :
    productBoundaryHomeomorph hr (productBoundaryCircle u hu p) =
      conifoldCircle u hu (productBoundaryHomeomorph hr p) := by
  apply Subtype.ext
  exact productMap_unit_smul u hu p.val

/-- The same action on the actual toric level, through its proved native coordinates. -/
def toricBoundaryCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) (y : ToricBoundary r) :
    ToricBoundary r :=
  productToricBoundaryHomeomorph r
    (productBoundaryCircle u hu ((productToricBoundaryHomeomorph r).symm y))

@[simp] theorem toricBoundaryCircle_val {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (y : ToricBoundary r) :
    (toricBoundaryCircle u hu y).val =
      toricNeighborhoodDiffeomorph ((toricNeighborhoodDiffeomorph.symm y.val).1,
        u • (toricNeighborhoodDiffeomorph.symm y.val).2) := rfl

theorem continuous_toricBoundaryCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) :
    Continuous (toricBoundaryCircle (r := r) u hu) :=
  (productToricBoundaryHomeomorph r).continuous.comp
    ((continuous_productBoundaryCircle u hu).comp
      (productToricBoundaryHomeomorph r).symm.continuous)

/-- The toric boundary homeomorphism preserves the literal matrix circle action. -/
theorem toricBoundaryHomeomorph_circle {r : ℝ} (hr : r ≠ 0)
    (u : ℂ) (hu : ‖u‖ = 1) (y : ToricBoundary r) :
    toricBoundaryHomeomorph hr (toricBoundaryCircle u hu y) =
      conifoldCircle u hu (toricBoundaryHomeomorph hr y) := by
  apply Subtype.ext
  change productMap
      (toricNeighborhoodDiffeomorph.symm
        (toricNeighborhoodDiffeomorph ((toricNeighborhoodDiffeomorph.symm y.val).1,
          u • (toricNeighborhoodDiffeomorph.symm y.val).2))) =
    rightCircle u (productMap (toricNeighborhoodDiffeomorph.symm y.val))
  rw [toricNeighborhoodDiffeomorph.symm_apply_apply]
  exact productMap_unit_smul u hu (toricNeighborhoodDiffeomorph.symm y.val)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
