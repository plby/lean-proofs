import Wikipedia.HopfProblem.CuspCentralHomologyRadialGauge
import Mathlib.Topology.Homotopy.Contractible

/-!
# The actual contraction of the open honeycomb cell

The straight radial homotopy `(s, x) ↦ (1 - s) • x` stays in the literal
interior of the central dual hexagon. It fixes the origin, exhibits the
interior as contractible, and gives the explicit projection equivalence
from a product with this interior to the other factor.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

open CuspHoneycombTiling

/-- The ordinary topological interior of the literal central cell. -/
abbrev InteriorCell := interior baseCell

/-- The distinguished center is the actual zero vector. -/
def interiorCellZero : InteriorCell :=
  ⟨0, (mem_interior_baseCell_iff 0).mpr (by rw [cellGauge_zero]; norm_num)⟩

@[simp] theorem interiorCellZero_coe : (interiorCellZero : Plane) = 0 := rfl

/-- Contract the actual open cell along its literal straight rays. -/
def interiorCellContract (s : unitInterval) (x : InteriorCell) : InteriorCell :=
  ⟨(1 - (s : ℝ)) • (x : Plane), by
    apply (mem_interior_baseCell_iff _).mpr
    rw [cellGauge_smul_of_nonneg _ (sub_nonneg.mpr s.2.2)]
    calc
      (1 - (s : ℝ)) * cellGauge x ≤ 1 * cellGauge x :=
        mul_le_mul_of_nonneg_right (sub_le_self 1 s.2.1) (cellGauge_nonneg x)
      _ = cellGauge x := one_mul _
      _ < 1 := (mem_interior_baseCell_iff x).mp x.2⟩

@[simp] theorem interiorCellContract_coe (s : unitInterval) (x : InteriorCell) :
    (interiorCellContract s x : Plane) = (1 - (s : ℝ)) • (x : Plane) := rfl

theorem interiorCellContract_continuous :
    Continuous (fun p : unitInterval × InteriorCell => interiorCellContract p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem interiorCellContract_gauge (s : unitInterval) (x : InteriorCell) :
    cellGauge (interiorCellContract s x) = (1 - (s : ℝ)) * cellGauge x :=
  cellGauge_smul_of_nonneg _ (sub_nonneg.mpr s.2.2) _

@[simp] theorem interiorCellContract_zero (x : InteriorCell) :
    interiorCellContract 0 x = x := by
  apply Subtype.ext
  simp [interiorCellContract]

@[simp] theorem interiorCellContract_one (x : InteriorCell) :
    interiorCellContract 1 x = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

@[simp] theorem interiorCellContract_fixed_zero (s : unitInterval) :
    interiorCellContract s interiorCellZero = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

/-- The explicit contraction is a homotopy fixed at the actual center. -/
def interiorCellContraction :
    (ContinuousMap.id InteriorCell).HomotopyRel
      (ContinuousMap.const InteriorCell interiorCellZero) {interiorCellZero} where
  toFun p := interiorCellContract p.1 p.2
  continuous_toFun := interiorCellContract_continuous
  map_zero_left := interiorCellContract_zero
  map_one_left := interiorCellContract_one
  prop' s x hx := by
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact interiorCellContract_fixed_zero s

@[simp] theorem interiorCellContraction_apply (s : unitInterval) (x : InteriorCell) :
    interiorCellContraction (s, x) = interiorCellContract s x := rfl

theorem interiorCell_id_nullhomotopic : (ContinuousMap.id InteriorCell).Nullhomotopic :=
  ⟨interiorCellZero, ⟨interiorCellContraction.toHomotopy⟩⟩

/-- Contractibility is proved by the displayed radial contraction. -/
instance interiorCellContractible : ContractibleSpace InteriorCell :=
  (contractible_iff_id_nullhomotopic InteriorCell).mpr interiorCell_id_nullhomotopic

/-- The literal cell interior is equivalent to a point; the inverse picks zero. -/
def interiorCellPointHomotopyEquiv : InteriorCell ≃ₕ Unit where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ interiorCellZero
  left_inv := ⟨interiorCellContraction.toHomotopy.symm⟩
  right_inv := by
    convert Homotopic.refl (ContinuousMap.id Unit) using 1
    ext u

@[simp] theorem interiorCellPointHomotopyEquiv_apply (x : InteriorCell) :
    interiorCellPointHomotopyEquiv x = () := rfl

@[simp] theorem interiorCellPointHomotopyEquiv_symm_apply (u : Unit) :
    interiorCellPointHomotopyEquiv.symm u = interiorCellZero := rfl

/-- Projection from a product with the actual open cell is a homotopy equivalence. -/
def interiorCellProductHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    (X × InteriorCell) ≃ₕ X :=
  ((HomotopyEquiv.refl X).prodCongr interiorCellPointHomotopyEquiv).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv

@[simp] theorem interiorCellProductHomotopyEquiv_apply
    {X : Type*} [TopologicalSpace X] (p : X × InteriorCell) :
    interiorCellProductHomotopyEquiv X p = p.1 := rfl

@[simp] theorem interiorCellProductHomotopyEquiv_symm_apply
    {X : Type*} [TopologicalSpace X] (x : X) :
    (interiorCellProductHomotopyEquiv X).symm x = (x, interiorCellZero) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.Radial
