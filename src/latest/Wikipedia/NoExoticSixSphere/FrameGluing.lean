import Wikipedia.NoExoticSixSphere.HemisphereClutching
import Mathlib.Topology.ContinuousOn

/-!
# Gluing actual range frames on a closed cover

Continuous frames agreeing on an overlap glue to a global frame. A continuous
invertible change of model coordinates can be applied before gluing. These are
constructions on the actual projection fibers, not an assumed bundle classification.
-/

open Set

namespace NoExoticSixSphere

variable {M F K : Type*} [TopologicalSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

namespace ContinuousRangeFrame

variable {P : M → F →L[ℝ] F}

/-- Change model coordinates in a frame by a continuous invertible operator family. -/
noncomputable def twist (a : ContinuousRangeFrame P K) (g : C(M, InvertibleOperators K)) :
    ContinuousRangeFrame P K where
  equiv x := (invertibleOperatorEquiv (g x).1 (g x).2).trans (a.equiv x)
  continuous := by
    have heq : (fun x ↦ (P x).range.subtypeL.comp
        (((invertibleOperatorEquiv (g x).1 (g x).2).trans (a.equiv x)).toContinuousLinearMap)) =
        (fun x ↦ ((P x).range.subtypeL.comp (a.equiv x).toContinuousLinearMap).comp (g x).1) := by
      funext x
      apply ContinuousLinearMap.ext
      intro w
      rfl
    rw [heq]
    exact a.continuous.clm_comp (continuous_subtype_val.comp g.continuous)

variable (s t : Set M) (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
  (a : ContinuousRangeFrame (fun x : s ↦ P x.1) K)
  (b : ContinuousRangeFrame (fun x : t ↦ P x.1) K)
  (hab : ∀ (x : M) (hx : x ∈ s) (hy : x ∈ t), a.equiv ⟨x, hx⟩ = b.equiv ⟨x, hy⟩)

omit [TopologicalSpace M] in
include hcover in
/-- A point outside the first member of a two-set cover lies in the second member. -/
theorem mem_right_of_not_mem_left (x : M) (hx : x ∉ s) : x ∈ t := by
  have h : x ∈ s ∪ t := by rw [hcover]; exact mem_univ x
  exact h.resolve_left hx

/-- Pointwise equivalences for the glued frame. -/
noncomputable def glueEquiv (x : M) : K ≃L[ℝ] (P x).range := by
  classical
  exact if hx : x ∈ s then a.equiv ⟨x, hx⟩
    else b.equiv ⟨x, mem_right_of_not_mem_left s t hcover x hx⟩

/-- The glued equivalences restrict to the original frame on the first closed set. -/
theorem glueEquiv_left (x : s) : glueEquiv s t hcover a b x.1 = a.equiv x := by
  classical
  simp only [glueEquiv, dif_pos x.2]

include hab in
/-- Agreement on the overlap also identifies the restriction to the second closed set. -/
theorem glueEquiv_right (x : t) : glueEquiv s t hcover a b x.1 = b.equiv x := by
  classical
  by_cases hx : x.1 ∈ s
  · rw [glueEquiv, dif_pos hx]
    exact hab x.1 hx x.2
  · simp only [glueEquiv, dif_neg hx]

/-- Actual continuous range frames glue across a finite closed cover. -/
noncomputable def glue : ContinuousRangeFrame P K where
  equiv := glueEquiv s t hcover a b
  continuous := by
    let A : M → K →L[ℝ] F := fun x ↦
      (P x).range.subtypeL.comp (glueEquiv s t hcover a b x).toContinuousLinearMap
    change Continuous A
    have ha : ContinuousOn A s := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : s.domRestrict A = fun x : s ↦ (P x.1).range.subtypeL.comp
          (a.equiv x).toContinuousLinearMap := by
        funext x
        change (P x.1).range.subtypeL.comp (glueEquiv s t hcover a b x.1).toContinuousLinearMap = _
        rw [glueEquiv_left s t hcover a b x]
      rw [heq]
      exact a.continuous
    have hb : ContinuousOn A t := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : t.domRestrict A = fun x : t ↦ (P x.1).range.subtypeL.comp
          (b.equiv x).toContinuousLinearMap := by
        funext x
        change (P x.1).range.subtypeL.comp (glueEquiv s t hcover a b x.1).toContinuousLinearMap = _
        rw [glueEquiv_right s t hcover a b hab x]
      rw [heq]
      exact b.continuous
    exact continuousOn_univ.mp (hcover ▸ ha.union_of_isClosed hb hs ht)

end ContinuousRangeFrame

end NoExoticSixSphere
