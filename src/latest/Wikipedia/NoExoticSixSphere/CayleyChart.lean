import Wikipedia.NoExoticSixSphere.CayleyInverse

/-!
# A genuine Cayley chart on the orthogonal group

The open subset where `1 + A` is invertible is homeomorphic to the actual
vector space of skew-adjoint operators. The chart is packaged as an open
partial homeomorphism on the original orthogonal operator space, and contains
the identity. Its rational ambient expressions are smooth on their domains.
-/

open scoped ContDiff
open Set

namespace NoExoticSixSphere.CayleyTransform

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

/-- The open Cayley domain in the original orthogonal operator space. -/
def domain : Set (OrthogonalOperators n) := {a | (1 + a.1.1).IsInvertible}

theorem isOpen_domain : IsOpen (domain (n := n)) := by
  have hi : IsOpen {A : Vector n →L[ℝ] Vector n | A.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  exact hi.preimage
    (continuous_const.add (continuous_subtype_val.comp continuous_subtype_val))

/-- The ambient rational coordinate expression is smooth wherever its denominator is invertible. -/
theorem contDiffAt_fraction (A : Vector n →L[ℝ] Vector n) (hA : (1 + A).IsInvertible) :
    ContDiffAt ℝ ∞ fraction A := by
  have hp : ContDiffAt ℝ ∞ (fun B : Vector n →L[ℝ] Vector n ↦ 1 + B) A :=
    contDiffAt_const.add contDiffAt_id
  have hm : ContDiffAt ℝ ∞ (fun B : Vector n →L[ℝ] Vector n ↦ 1 - B) A :=
    contDiffAt_const.sub contDiffAt_id
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse :
        (Vector n →L[ℝ] Vector n) → (Vector n →L[ℝ] Vector n)) (1 + A) :=
    hA.contDiffAt_map_inverse
  have hinv : ContDiffAt ℝ ∞ (fun B : Vector n →L[ℝ] Vector n ↦ (1 + B).inverse) A :=
    ContDiffAt.comp (f := fun B : Vector n →L[ℝ] Vector n ↦ 1 + B)
      (g := (ContinuousLinearMap.inverse :
        (Vector n →L[ℝ] Vector n) → (Vector n →L[ℝ] Vector n))) A hi hp
  exact hm.clm_comp hinv

variable {X : Type*} [TopologicalSpace X]

theorem continuous_coordinate (a : X → OrthogonalOperators n) (ha : Continuous a)
    (hdom : ∀ x, a x ∈ domain) : Continuous (fun x ↦ coordinate (a x) (hdom x)) := by
  have hA : Continuous (fun x ↦ (a x).1.1) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have hf : Continuous (fun x ↦ fraction (a x).1.1) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun x ↦ (a x).1.1) (x := x)
      (contDiffAt_fraction (a x).1.1 (hdom x)).continuousAt hA.continuousAt
  exact hf.subtype_mk _

/-- The Cayley domain with its subspace topology is homeomorphic to the skew-adjoint model. -/
noncomputable def homeomorph : ↥(domain (n := n)) ≃ₜ SkewOperators n where
  toFun a := coordinate a.1 a.2
  invFun K := ⟨orthogonal K, orthogonal_mem_domain K⟩
  left_inv a := Subtype.ext (orthogonal_coordinate a.1 a.2)
  right_inv := coordinate_orthogonal
  continuous_toFun := continuous_coordinate Subtype.val continuous_subtype_val Subtype.property
  continuous_invFun := continuous_orthogonal.subtype_mk _

/-- The total coordinate function, using zero only outside the chart's stated source. -/
noncomputable def coordinates (a : OrthogonalOperators n) : SkewOperators n := by
  classical
  exact if h : a ∈ domain then coordinate a h else 0

theorem coordinates_of_mem (a : OrthogonalOperators n) (ha : a ∈ domain) :
    coordinates a = coordinate a ha := dif_pos ha

/-- The native open partial homeomorphism has the original orthogonal group as domain type. -/
noncomputable def chart : OpenPartialHomeomorph (OrthogonalOperators n) (SkewOperators n) where
  toFun := coordinates
  invFun := orthogonal
  source := domain
  target := univ
  map_source' _ _ := mem_univ _
  map_target' K _ := orthogonal_mem_domain K
  left_inv' a ha := by
    rw [coordinates_of_mem a ha]
    exact orthogonal_coordinate a ha
  right_inv' K _ := by
    rw [coordinates_of_mem _ (orthogonal_mem_domain K), coordinate_orthogonal]
  open_source := isOpen_domain
  open_target := isOpen_univ
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := continuous_coordinate (n := n) Subtype.val continuous_subtype_val Subtype.property
    exact hc.congr (fun a ↦ (coordinates_of_mem a.1 a.2).symm)
  continuousOn_invFun := continuous_orthogonal.continuousOn

theorem operator_zero : operator (0 : SkewOperators n) = 1 := by
  rw [operator_eq_fraction]
  simp only [fraction, Submodule.coe_zero, sub_zero, add_zero]
  change (ContinuousLinearMap.id ℝ (Vector n)).comp
    (ContinuousLinearMap.id ℝ (Vector n)).inverse = 1
  rw [ContinuousLinearMap.inverse_id]
  rfl

theorem orthogonal_zero : orthogonal (0 : SkewOperators n) = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  exact operator_zero

theorem identity_mem_domain : identity n ∈ domain := by
  rw [← orthogonal_zero (n := n)]
  exact orthogonal_mem_domain (0 : SkewOperators n)

theorem chart_identity : chart (identity n) = 0 := by
  change coordinates (identity n) = 0
  rw [← orthogonal_zero (n := n), coordinates_of_mem _ (orthogonal_mem_domain _),
    coordinate_orthogonal]

end NoExoticSixSphere.CayleyTransform
