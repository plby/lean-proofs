import Wikipedia.HopfProblem.SpecialPeriodsTriangleShimizuMatrices
import Wikipedia.HopfProblem.SpecialPeriodsTriangleDiscrete
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Translation subgroups of discrete real matrix groups

The actual matrices `[[1,t],[0,1]]` identify the translation parameters in
a subgroup of `SL₂(ℝ)` with an additive subgroup of `ℝ`.  If the matrix
subgroup is discrete in its inherited topology, this parameter subgroup
is discrete and therefore cyclic.  No discrete topology or cyclicity is
assigned by definition.

For the triangle matrix group, both signs of the proved cusp width occur
as translation parameters.  Identifying this width with the primitive
translation generator is a separate assertion.
-/

noncomputable section

open Function Set Matrix UpperHalfPlane Topology
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

@[simp] theorem shimizuTranslation_zero : shimizuTranslation 0 = 1 := by
  apply Subtype.ext
  simp [coe_shimizuTranslation, Matrix.one_fin_two]

theorem shimizuTranslation_add (s t : ℝ) :
    shimizuTranslation (s + t) = shimizuTranslation s * shimizuTranslation t := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_shimizuTranslation, add_comm]

@[simp] theorem shimizuTranslation_inv (t : ℝ) :
    (shimizuTranslation t)⁻¹ = shimizuTranslation (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← shimizuTranslation_add, add_neg_cancel, shimizuTranslation_zero]

/-- The additive real translation parameters, written multiplicatively,
map homomorphically to the actual special-linear matrices. -/
def shimizuTranslationHom : Multiplicative ℝ →* SL(2, ℝ) where
  toFun t := shimizuTranslation t.toAdd
  map_one' := shimizuTranslation_zero
  map_mul' s t := shimizuTranslation_add s.toAdd t.toAdd

@[simp] theorem shimizuTranslationHom_apply (t : ℝ) :
    shimizuTranslationHom (Multiplicative.ofAdd t) = shimizuTranslation t := rfl

theorem shimizuTranslation_zpow (t : ℝ) (n : ℤ) :
    shimizuTranslation t ^ n = shimizuTranslation ((n : ℝ) * t) := by
  simpa only [← ofAdd_zsmul, shimizuTranslationHom_apply, zsmul_eq_mul] using
    (map_zpow shimizuTranslationHom (Multiplicative.ofAdd t) n).symm

theorem shimizuTranslation_pow (t : ℝ) (n : ℕ) :
    shimizuTranslation t ^ n = shimizuTranslation ((n : ℝ) * t) := by
  simpa only [zpow_natCast, Int.cast_natCast] using shimizuTranslation_zpow t (n : ℤ)

theorem shimizuTranslation_injective : Function.Injective shimizuTranslation := by
  intro s t h
  have he := congrArg (fun A : SL(2, ℝ) => A 0 1) h
  simpa [shimizuTranslation] using he

theorem shimizuTranslation_continuous : Continuous shimizuTranslation := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  change Continuous (fun t : ℝ => (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | exact continuous_const | exact continuous_id

/-- The translation matrices act by the literal horizontal translation
on Mathlib's upper half-plane. -/
theorem shimizuTranslation_smul (t : ℝ) (z : ℍ) :
    shimizuTranslation t • z = t +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd]
  simp [shimizuTranslation, add_comm]

@[simp] theorem realSLPermutation_shimizuTranslation (t : ℝ) (z : ℍ) :
    realSLPermutation (shimizuTranslation t) z = t +ᵥ z :=
  shimizuTranslation_smul t z

theorem shimizuTranslation_neg_width : shimizuTranslation (-width) = cuspSL := by
  rw [← shimizuTranslation_inv, shimizuTranslation_width]
  rfl

/-- The real parameters whose actual translation matrices belong to the
specified matrix subgroup. -/
def translationSubgroup (Γ : Subgroup (SL(2, ℝ))) : AddSubgroup ℝ where
  carrier := {t | shimizuTranslation t ∈ Γ}
  zero_mem' := by
    change shimizuTranslation 0 ∈ Γ
    rw [shimizuTranslation_zero]
    exact Γ.one_mem
  add_mem' := by
    intro s t hs ht
    change shimizuTranslation (s + t) ∈ Γ
    rw [shimizuTranslation_add]
    exact Γ.mul_mem hs ht
  neg_mem' := by
    intro t ht
    change shimizuTranslation (-t) ∈ Γ
    rw [← shimizuTranslation_inv]
    exact Γ.inv_mem ht

@[simp] theorem mem_translationSubgroup (Γ : Subgroup (SL(2, ℝ))) (t : ℝ) :
    t ∈ translationSubgroup Γ ↔ shimizuTranslation t ∈ Γ := Iff.rfl

/-- The translation parameters map into the matrix subgroup without
changing either inherited topology. -/
def translationSubgroupMap (Γ : Subgroup (SL(2, ℝ))) : translationSubgroup Γ → Γ :=
  fun t => ⟨shimizuTranslation t, t.property⟩

@[simp] theorem translationSubgroupMap_coe (Γ : Subgroup (SL(2, ℝ)))
    (t : translationSubgroup Γ) :
    (translationSubgroupMap Γ t : SL(2, ℝ)) = shimizuTranslation t := rfl

theorem translationSubgroupMap_injective (Γ : Subgroup (SL(2, ℝ))) :
    Function.Injective (translationSubgroupMap Γ) := by
  intro s t h
  apply Subtype.ext
  exact shimizuTranslation_injective (congrArg Subtype.val h)

theorem translationSubgroupMap_continuous (Γ : Subgroup (SL(2, ℝ))) :
    Continuous (translationSubgroupMap Γ) := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  exact shimizuTranslation_continuous.comp continuous_subtype_val

/-- Discreteness of the parameter subgroup is inherited through its
continuous injection into the already-discrete matrix subgroup. -/
instance translationSubgroup_discrete (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ] :
    DiscreteTopology (translationSubgroup Γ) :=
  DiscreteTopology.of_continuous_injective (translationSubgroupMap_continuous Γ)
    (translationSubgroupMap_injective Γ)

/-- A discrete real matrix subgroup has a cyclic subgroup of horizontal
translation parameters. -/
theorem translationSubgroup_cyclic (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ] :
    ∃ t : ℝ, translationSubgroup Γ = AddSubgroup.zmultiples t := by
  have hc : IsAddCyclic (translationSubgroup Γ) :=
    AddSubgroup.discrete_iff_addCyclic.mpr inferInstance
  obtain ⟨t, ht⟩ :=
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top (translationSubgroup Γ)).mp hc
  exact ⟨t, ht.symm⟩

/-- A positive translation in a discrete subgroup ensures that its
cyclic translation subgroup admits a strictly positive generator. -/
theorem translationSubgroup_cyclic_pos_of_mem (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] {w : ℝ} (hw : 0 < w) (hwΓ : w ∈ translationSubgroup Γ) :
    ∃ t : ℝ, 0 < t ∧ translationSubgroup Γ = AddSubgroup.zmultiples t := by
  obtain ⟨t, ht⟩ := translationSubgroup_cyclic Γ
  have ht₀ : t ≠ 0 := by
    intro h
    subst t
    rw [ht] at hwΓ
    have hw₀ : w = 0 := by simpa using hwΓ
    exact hw.ne' hw₀
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos
  · refine ⟨-t, neg_pos.mpr hneg, ?_⟩
    simpa only [AddSubgroup.zmultiples_neg] using ht
  · exact ⟨t, hpos, ht⟩

theorem width_mem_translationSubgroup_matrixGroup :
    width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation width ∈ matrixGroup
  rw [shimizuTranslation_width, ← cuspSL_inv]
  exact matrixGroup.inv_mem cuspSL_mem_matrixGroup

theorem neg_width_mem_translationSubgroup_matrixGroup :
    -width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation (-width) ∈ matrixGroup
  rw [shimizuTranslation_neg_width]
  exact cuspSL_mem_matrixGroup

/-- Cyclicity for the actual triangle matrix group, using its proved
inherited discreteness rather than a cyclicity hypothesis. -/
theorem matrixGroup_translationSubgroup_cyclic :
    ∃ t : ℝ, translationSubgroup matrixGroup = AddSubgroup.zmultiples t :=
  translationSubgroup_cyclic matrixGroup

theorem matrixGroup_translationSubgroup_cyclic_pos :
    ∃ t : ℝ, 0 < t ∧ translationSubgroup matrixGroup = AddSubgroup.zmultiples t :=
  translationSubgroup_cyclic_pos_of_mem matrixGroup width_pos
    width_mem_translationSubgroup_matrixGroup

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
