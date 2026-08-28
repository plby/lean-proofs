import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Smooth extension across the outer edge of a gauge neighborhood

A smooth function on an open set that equals a fixed value off a
closed subset contained in that open set extends smoothly by the
fixed value. The closed subset need not be compact. This distinction
allows a gauge correction to approach a deleted fixed sphere while
remaining supported away from the outer edge of its normal tube.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

variable {V H M W K N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  (I : ModelWithCorners ℝ V H) (J : ModelWithCorners ℝ W K)

def openExtend (U : TopologicalSpace.Opens M) (f : U → N) (c : N) (x : M) : N := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else c

@[simp] theorem openExtend_on (U : TopologicalSpace.Opens M) (f : U → N) (c : N) (x : U) :
    openExtend U f c x.val = f x := by
  classical
  simp only [openExtend, dif_pos x.property]

theorem openExtend_off (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (x : M) (hx : x ∉ U) : openExtend U f c x = c := by
  classical
  simp only [openExtend, dif_neg hx]

theorem openExtend_smoothAt_on (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (hf : ContMDiff I J ∞ f) (x : M) (hx : x ∈ U) :
    ContMDiffAt I J ∞ (openExtend U f c) x := by
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
  have he : (fun z : U => openExtend U f c z.val) = f := funext (openExtend_on U f c)
  rw [he]
  exact hf ⟨x, hx⟩

theorem openExtend_eq_const_off (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (S : Set M) (hf : ∀ x : U, x.val ∉ S → f x = c) (x : M) (hx : x ∉ S) :
    openExtend U f c x = c := by
  classical
  by_cases hU : x ∈ U
  · exact (openExtend_on U f c ⟨x, hU⟩).trans (hf ⟨x, hU⟩ hx)
  · exact openExtend_off U f c x hU

theorem openExtend_smooth (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (hf : ContMDiff I J ∞ f) (S : Set M) (hS : IsClosed S) (hSU : S ⊆ U)
    (hfc : ∀ x : U, x.val ∉ S → f x = c) :
    ContMDiff I J ∞ (openExtend U f c) := by
  intro x
  by_cases hx : x ∈ U
  · apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
    have he : (fun z : U => openExtend U f c z.val) = f :=
      funext (openExtend_on U f c)
    rw [he]
    exact hf ⟨x, hx⟩
  · have hxS : x ∉ S := fun h => hx (hSU h)
    have he : ∀ᶠ y in 𝓝 x, openExtend U f c y = c := by
      filter_upwards [hS.isOpen_compl.mem_nhds hxS] with y hy
      exact openExtend_eq_const_off U f c S hfc y hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

end Wikipedia.HopfProblem.OrbitPair
