import Wikipedia.NoExoticSixSphere.StabilizedReflections
import Wikipedia.NoExoticSixSphere.OrthogonalLieGroup
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue

/-!
# The two actual path components of the orthogonal group

Cartan--Dieudonne factors the original operator into hyperplane reflections.
Paths between unit normals make all nontrivial reflections joined, so every
operator is joined to the identity or one fixed reflection. The continuous,
nowhere-zero determinant separates these representatives.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.OrthogonalComponents

open NoExoticSixSphere GLOrthonormalization

variable {n : ℕ}

def ofEquivHom (n : ℕ) :
    (Vector n ≃ₗᵢ[ℝ] Vector n) →* OrthogonalOperators n where
  toFun := OrthogonalPaths.ofEquiv
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_mul' f g := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

theorem exists_reflection_product (a : OrthogonalOperators n) :
    ∃ l : List (Vector n), a = (l.map OrthogonalPaths.reflection).prod := by
  obtain ⟨l, _, h⟩ := (OrthogonalPaths.toEquiv a).reflections_generate_dim
  have he := congrArg (ofEquivHom n) h
  rw [map_list_prod, List.map_map] at he
  exact ⟨l, (OrthogonalPaths.ofEquiv_toEquiv a).symm.trans he⟩

theorem reflection_zero : OrthogonalPaths.reflection (0 : Vector n) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change (ℝ ∙ (0 : Vector n))ᗮ.reflection x = x
  exact Submodule.reflection_mem_subspace_eq_self (by simp)

theorem reflection_square (w : Vector n) :
    OrthogonalPaths.reflection w * OrthogonalPaths.reflection w = 1 := by
  have h := congrArg (ofEquivHom n) (Submodule.reflection_mul_reflection (ℝ ∙ w)ᗮ)
  rw [map_mul, map_one] at h
  exact h

def unitNormal (w : Vector n) (hw : w ≠ 0) : UnitSphere (Vector n) :=
  ⟨‖w‖⁻¹ • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩

theorem reflection_unitNormal (w : Vector n) (hw : w ≠ 0) :
    OrthogonalPaths.reflection (unitNormal w hw).val = OrthogonalPaths.reflection w := by
  have hs : (ℝ ∙ (unitNormal w hw).val) = ℝ ∙ w :=
    Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hw))) w
  exact congrArg (fun K : Submodule ℝ (Vector n) ↦ OrthogonalPaths.ofEquiv Kᗮ.reflection) hs

variable [PathConnectedSpace (UnitSphere (Vector n))] (v : UnitSphere (Vector n))

theorem reflection_joined (w : Vector n) (hw : w ≠ 0) :
    Joined (OrthogonalPaths.reflection w) (OrthogonalPaths.reflection v.val) := by
  have h := (PathConnectedSpace.joined (unitNormal w hw) v).map
    (OrthogonalPaths.reflectionMap (n := n)).continuous
  change Joined (OrthogonalPaths.reflection (unitNormal w hw).val)
    (OrthogonalPaths.reflection v.val) at h
  rw [reflection_unitNormal] at h
  exact h

theorem reflection_joined_one_or_fixed (w : Vector n) :
    Joined (OrthogonalPaths.reflection w) (1 : OrthogonalOperators n) ∨
      Joined (OrthogonalPaths.reflection w) (OrthogonalPaths.reflection v.val) := by
  by_cases hw : w = 0
  · left
    rw [hw, reflection_zero]
  · exact Or.inr (reflection_joined v w hw)

theorem product_joined_one_or_fixed (l : List (Vector n)) :
    Joined (l.map OrthogonalPaths.reflection).prod (1 : OrthogonalOperators n) ∨
      Joined (l.map OrthogonalPaths.reflection).prod (OrthogonalPaths.reflection v.val) := by
  induction l with
  | nil => exact Or.inl (Joined.refl _)
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases reflection_joined_one_or_fixed v w with hw | hw <;>
      rcases ih with hl | hl
    · exact Or.inl (by simpa only [one_mul] using hw.mul hl)
    · exact Or.inr (by simpa only [one_mul] using hw.mul hl)
    · exact Or.inr (by simpa only [mul_one] using hw.mul hl)
    · exact Or.inl (by simpa only [reflection_square] using hw.mul hl)

theorem joined_one_or_fixed (a : OrthogonalOperators n) :
    Joined a (1 : OrthogonalOperators n) ∨ Joined a (OrthogonalPaths.reflection v.val) := by
  obtain ⟨l, rfl⟩ := exists_reflection_product a
  exact product_joined_one_or_fixed v l

omit [PathConnectedSpace (UnitSphere (Vector n))] in
def determinant (a : OrthogonalOperators n) : ℝ := a.val.val.det

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem continuous_determinant : Continuous (determinant (n := n)) :=
  ContinuousLinearMap.continuous_det.comp
    (continuous_subtype_val.comp continuous_subtype_val)

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem determinant_one : determinant (1 : OrthogonalOperators n) = 1 :=
  LinearMap.det_id

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem determinant_ne_zero (a : OrthogonalOperators n) : determinant a ≠ 0 :=
  (OrthogonalPaths.toEquiv a).toLinearEquiv.isUnit_det'.ne_zero

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem determinant_reflection : determinant (OrthogonalPaths.reflection v.val) = -1 := by
  change LinearMap.det (ℝ ∙ v.val)ᗮ.reflection.toLinearMap = -1
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton (ne_zero_of_mem_unit_sphere v), pow_one]

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem not_joined_one_reflection :
    ¬ Joined (1 : OrthogonalOperators n) (OrthogonalPaths.reflection v.val) := by
  rintro ⟨p⟩
  have h₀ : determinant (p 0) = 1 := by rw [p.source, determinant_one]
  have h₁ : determinant (p 1) = -1 := by rw [p.target, determinant_reflection]
  obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) (0 : I)
    (continuous_determinant.comp p.continuous) (show (0 : ℝ) ∈
      Set.Icc (determinant (p 1)) (determinant (p 0)) from by rw [h₀, h₁]; norm_num)
  exact determinant_ne_zero (p t) ht

def representativeClass (b : Bool) : ZerothHomotopy (OrthogonalOperators n) :=
  ZerothHomotopy.mk (if b then OrthogonalPaths.reflection v.val else 1)

omit [PathConnectedSpace (UnitSphere (Vector n))] in
theorem representativeClass_injective : Function.Injective (representativeClass v) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact False.elim (not_joined_one_reflection v (Quotient.exact h))
  · exact False.elim (not_joined_one_reflection v (Quotient.exact h.symm))
  · rfl

theorem representativeClass_surjective : Function.Surjective (representativeClass v) := by
  intro c
  obtain ⟨a, rfl⟩ := ZerothHomotopy.mk_surjective c
  rcases joined_one_or_fixed v a with h | h
  · exact ⟨false, (Quotient.sound h).symm⟩
  · exact ⟨true, (Quotient.sound h).symm⟩

/-- The two values classify actual paths in the original orthogonal operator topology. -/
def componentsEquiv : ZerothHomotopy (OrthogonalOperators n) ≃ Bool :=
  (Equiv.ofBijective (representativeClass v)
    ⟨representativeClass_injective v, representativeClass_surjective v⟩).symm

theorem componentsEquiv_one : componentsEquiv v (ZerothHomotopy.mk 1) = false :=
  (Equiv.ofBijective (representativeClass v)
    ⟨representativeClass_injective v, representativeClass_surjective v⟩).symm_apply_apply false

theorem componentsEquiv_reflection :
    componentsEquiv v (ZerothHomotopy.mk (OrthogonalPaths.reflection v.val)) = true :=
  (Equiv.ofBijective (representativeClass v)
    ⟨representativeClass_injective v, representativeClass_surjective v⟩).symm_apply_apply true

end Wikipedia.HopfProblem.DegreeCollapse.OrthogonalComponents
