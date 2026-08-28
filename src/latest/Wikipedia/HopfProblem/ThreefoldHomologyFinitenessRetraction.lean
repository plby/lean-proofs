import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetractionExtension
import Mathlib.Topology.Homotopy.Equiv

/-!
# Extending punctured radial homotopies to actual sublevel equivalences

A continuous homotopy on the positive-radius locus, fixed below a positive
cutoff, extends by the identity over the zero-radius locus.  If radius never
increases and the final map lies below a target bound, the extension restricts
to that sublevel and gives a genuine homotopy equivalence with the ambient
space.  One map is exactly the subtype inclusion.  The construction does not
require any nonnegativity hypothesis on the continuous radius function.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetraction

variable {X : Type*} [TopologicalSpace X]
variable (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ))
variable (η : ℝ) (hη : 0 < η)
variable (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)

/-- The identity extension agrees with the identity at time zero. -/
theorem extension_zero (hzero : ∀ x : Positive ρ, H (0, x) = x) (x : X) :
    extension ρ H η hη hfix (0, x) = x := by
  by_cases hx : 0 < ρ x
  · exact (extension_apply_of_pos ρ H η hη hfix (0, x) hx).trans
      (congrArg Subtype.val (hzero ⟨x, hx⟩))
  · exact extension_apply_of_nonpos ρ H η hη hfix (0, x) (le_of_not_gt hx)

/-- Every point of the zero-radius locus is fixed at every time. -/
theorem extension_apply_of_zero (t : unitInterval) (x : X) (hx : ρ x = 0) :
    extension ρ H η hη hfix (t, x) = x :=
  extension_apply_of_nonpos ρ H η hη hfix (t, x) hx.le

/-- The extended homotopy preserves the genuine nonincreasing-radius bound. -/
theorem extension_radius_le
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (s : unitInterval × X) :
    ρ (extension ρ H η hη hfix s) ≤ ρ s.2 := by
  by_cases hs : 0 < ρ s.2
  · rw [extension_apply_of_pos ρ H η hη hfix s hs]
    exact hmono s.1 ⟨s.2, hs⟩
  · exact (congrArg ρ
      (extension_apply_of_nonpos ρ H η hη hfix s (le_of_not_gt hs))).le

/-- At the final time every ambient point lies in the target sublevel. -/
theorem extension_one_lt (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : X) :
    ρ (extension ρ H η hη hfix (1, x)) < δ := by
  by_cases hx : 0 < ρ x
  · rw [extension_apply_of_pos ρ H η hη hfix (1, x) hx]
    exact hone ⟨x, hx⟩
  · rw [extension_apply_of_nonpos ρ H η hη hfix (1, x) (le_of_not_gt hx)]
    exact (le_of_not_gt hx).trans_lt (hη.trans_le hηδ)

/-- Nonincreasing radius makes each actual sublevel invariant. -/
theorem extension_stays_sublevel
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (s : unitInterval × Sublevel ρ δ) :
    ρ (extension ρ H η hη hfix (s.1, s.2.val)) < δ :=
  (extension_radius_le ρ H η hη hfix hmono (s.1, s.2.val)).trans_lt s.2.property

/-- The literal inclusion of the target open sublevel into the ambient space. -/
def sublevelInclusion (ρ : C(X, ℝ)) (δ : ℝ) : C(Sublevel ρ δ, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem sublevelInclusion_apply (δ : ℝ) (x : Sublevel ρ δ) :
    sublevelInclusion ρ δ x = x.val := rfl

/-- The endpoint of the actual extended homotopy, with its image restricted
to the target sublevel. -/
def sublevelMap (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : C(X, Sublevel ρ δ) where
  toFun x := ⟨extension ρ H η hη hfix (1, x),
    extension_one_lt ρ H η hη hfix δ hηδ hone x⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

@[simp] theorem sublevelMap_val (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : X) :
    (sublevelMap ρ H η hη hfix δ hηδ hone x).val =
      extension ρ H η hη hfix (1, x) := rfl

/-- The actual ambient homotopy from the identity to inclusion after the
endpoint map, fixed pointwise on the inner sublevel. -/
def extendedHomotopy (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id X).HomotopyRel
      ((sublevelInclusion ρ δ).comp (sublevelMap ρ H η hη hfix δ hηδ hone))
      {x : X | ρ x < η} where
  toFun := extension ρ H η hη hfix
  continuous_toFun := (extension ρ H η hη hfix).continuous
  map_zero_left := extension_zero ρ H η hη hfix hzero
  map_one_left _ := rfl
  prop' t x hx := extension_apply_of_small ρ H η hη hfix (t, x) hx

/-- Restricting the same actual homotopy to the invariant target sublevel
gives the other inverse homotopy, still fixed on the inner sublevel. -/
def restrictedHomotopy (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id (Sublevel ρ δ)).HomotopyRel
      ((sublevelMap ρ H η hη hfix δ hηδ hone).comp (sublevelInclusion ρ δ))
      {x : Sublevel ρ δ | ρ x.val < η} where
  toFun s := ⟨extension ρ H η hη hfix (s.1, s.2.val),
    extension_stays_sublevel ρ H η hη hfix hmono δ s⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    exact extension_zero ρ H η hη hfix hzero x.val
  map_one_left _ := rfl
  prop' t x hx := by
    apply Subtype.ext
    exact extension_apply_of_small ρ H η hη hfix (t, x.val) hx

/-- The actual extended radial homotopy exhibits the target sublevel as
homotopy equivalent to the ambient space, with inverse exactly inclusion. -/
def sublevelHomotopyEquiv (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : X ≃ₕ Sublevel ρ δ where
  toFun := sublevelMap ρ H η hη hfix δ hηδ hone
  invFun := sublevelInclusion ρ δ
  left_inv := ⟨(extendedHomotopy ρ H η hη hfix hzero δ hηδ hone).toHomotopy.symm⟩
  right_inv :=
    ⟨(restrictedHomotopy ρ H η hη hfix hzero hmono δ hηδ hone).toHomotopy.symm⟩

@[simp] theorem sublevelHomotopyEquiv_toFun
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (sublevelHomotopyEquiv ρ H η hη hfix hzero hmono δ hηδ hone).toFun =
      sublevelMap ρ H η hη hfix δ hηδ hone := rfl

/-- The reverse map of the constructed equivalence is literally the subtype inclusion. -/
@[simp] theorem sublevelHomotopyEquiv_invFun
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (sublevelHomotopyEquiv ρ H η hη hfix hzero hmono δ hηδ hone).invFun =
      sublevelInclusion ρ δ := rfl

@[simp] theorem sublevelHomotopyEquiv_apply_val
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : X) :
    (sublevelHomotopyEquiv ρ H η hη hfix hzero hmono δ hηδ hone x).val =
      extension ρ H η hη hfix (1, x) := rfl

@[simp] theorem sublevelHomotopyEquiv_symm_apply
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : Sublevel ρ δ) :
    (sublevelHomotopyEquiv ρ H η hη hfix hzero hmono δ hηδ hone).symm x = x.val := rfl

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetraction
