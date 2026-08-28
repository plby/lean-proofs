import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic.Linarith

/-!
# The two components of a punctured interval

Removing the midpoint from the open unit interval gives an actual
topological sum of its two open subintervals. The homeomorphism preserves
the real coordinate, and its inverse is given by the two interval
inclusions. Nonempty open intervals are contractible by real convexity.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology

/-- A nonempty open real interval contracts inside itself by convexity. -/
theorem intervalContractible (a b : ℝ) (hab : a < b) : ContractibleSpace (Ioo a b) :=
  (convex_Ioo a b).contractibleSpace ⟨(a + b) / 2, by constructor <;> linarith⟩

/-- The left component included into the actual punctured open unit interval. -/
def puncturedIntervalInl (t : Ioo (0 : ℝ) (1 / 2)) :
    {s : Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2} :=
  ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ne_of_lt t.property.2⟩

/-- The right component included into the actual punctured open unit interval. -/
def puncturedIntervalInr (t : Ioo (1 / 2 : ℝ) 1) :
    {s : Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2} :=
  ⟨⟨t, (by norm_num : (0 : ℝ) < 1 / 2).trans t.property.1, t.property.2⟩,
    ne_of_gt t.property.1⟩

@[simp] theorem puncturedIntervalInl_coordinate (t : Ioo (0 : ℝ) (1 / 2)) :
    ((puncturedIntervalInl t).val : ℝ) = t := rfl

@[simp] theorem puncturedIntervalInr_coordinate (t : Ioo (1 / 2 : ℝ) 1) :
    ((puncturedIntervalInr t).val : ℝ) = t := rfl

theorem puncturedIntervalInl_continuous : Continuous puncturedIntervalInl :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedIntervalInr_continuous : Continuous puncturedIntervalInr :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedIntervalInl_isOpenMap : IsOpenMap puncturedIntervalInl :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedIntervalInr_isOpenMap : IsOpenMap puncturedIntervalInr :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

private def puncturedIntervalSumEquiv :
    (Ioo (0 : ℝ) (1 / 2) ⊕ Ioo (1 / 2 : ℝ) 1) ≃
      {t : Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2} :=
  Equiv.ofBijective (Sum.elim puncturedIntervalInl puncturedIntervalInr) (by
    constructor
    · intro s t h
      have hcoord := congrArg (fun u : {t : Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2} =>
        (u.val : ℝ)) h
      rcases s with s | s <;> rcases t with t | t
      · exact congrArg Sum.inl (Subtype.ext hcoord)
      · change (s : ℝ) = (t : ℝ) at hcoord
        linarith [s.property.2, t.property.1]
      · change (s : ℝ) = (t : ℝ) at hcoord
        linarith [s.property.1, t.property.2]
      · exact congrArg Sum.inr (Subtype.ext hcoord)
    · intro t
      rcases lt_or_gt_of_ne t.property with ht | ht
      · exact ⟨Sum.inl ⟨t.val, t.val.property.1, ht⟩, rfl⟩
      · exact ⟨Sum.inr ⟨t.val, ht, t.val.property.2⟩, rfl⟩)

/-- Removing the midpoint splits the open unit interval into its two actual open components. -/
def puncturedIntervalHomeomorph :
    {t : Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2} ≃ₜ
      (Ioo (0 : ℝ) (1 / 2) ⊕ Ioo (1 / 2 : ℝ) 1) :=
  (puncturedIntervalSumEquiv.toHomeomorphOfContinuousOpen
    (puncturedIntervalInl_continuous.sumElim puncturedIntervalInr_continuous)
    (puncturedIntervalInl_isOpenMap.sumElim puncturedIntervalInr_isOpenMap)).symm

/-- The inverse on the left component is its coordinate-preserving inclusion. -/
@[simp] theorem puncturedIntervalHomeomorph_symm_inl (t : Ioo (0 : ℝ) (1 / 2)) :
    puncturedIntervalHomeomorph.symm (Sum.inl t) = puncturedIntervalInl t := rfl

/-- The inverse on the right component is its coordinate-preserving inclusion. -/
@[simp] theorem puncturedIntervalHomeomorph_symm_inr (t : Ioo (1 / 2 : ℝ) 1) :
    puncturedIntervalHomeomorph.symm (Sum.inr t) = puncturedIntervalInr t := rfl

@[simp] theorem puncturedIntervalHomeomorph_symm_inl_coordinate
    (t : Ioo (0 : ℝ) (1 / 2)) :
    ((puncturedIntervalHomeomorph.symm (Sum.inl t)).val : ℝ) = t := rfl

@[simp] theorem puncturedIntervalHomeomorph_symm_inr_coordinate
    (t : Ioo (1 / 2 : ℝ) 1) :
    ((puncturedIntervalHomeomorph.symm (Sum.inr t)).val : ℝ) = t := rfl

@[simp] theorem puncturedIntervalHomeomorph_apply_inl (t : Ioo (0 : ℝ) (1 / 2)) :
    puncturedIntervalHomeomorph (puncturedIntervalInl t) = Sum.inl t :=
  puncturedIntervalHomeomorph.apply_symm_apply (Sum.inl t)

@[simp] theorem puncturedIntervalHomeomorph_apply_inr (t : Ioo (1 / 2 : ℝ) 1) :
    puncturedIntervalHomeomorph (puncturedIntervalInr t) = Sum.inr t :=
  puncturedIntervalHomeomorph.apply_symm_apply (Sum.inr t)

/-- On either component, the inverse homeomorphism preserves the real coordinate. -/
theorem puncturedIntervalHomeomorph_symm_coordinate
    (t : Ioo (0 : ℝ) (1 / 2) ⊕ Ioo (1 / 2 : ℝ) 1) :
    ((puncturedIntervalHomeomorph.symm t).val : ℝ) =
      Sum.elim (fun x : Ioo (0 : ℝ) (1 / 2) => (x : ℝ))
        (fun x : Ioo (1 / 2 : ℝ) 1 => (x : ℝ)) t := by
  cases t <;> rfl

/-- Splitting into the two components does not change the underlying real point. -/
theorem puncturedIntervalHomeomorph_coordinate
    (t : {s : Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2}) :
    Sum.elim (fun x : Ioo (0 : ℝ) (1 / 2) => (x : ℝ))
      (fun x : Ioo (1 / 2 : ℝ) 1 => (x : ℝ)) (puncturedIntervalHomeomorph t) =
      (t.val : ℝ) := by
  rw [← puncturedIntervalHomeomorph_symm_coordinate,
    puncturedIntervalHomeomorph.symm_apply_apply]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology
