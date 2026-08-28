import Wikipedia.HopfProblem.HolomorphicPicardNativeGluingBasic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Native scalar transition functions of an actual Čech cocycle

On its actual overlap, a transition is the pointwise value of the given
unit section. Off that overlap it is one. The arbitrary outside values
do not enter the bundle construction: actual holomorphicity on the open
overlap follows by comparison with the original holomorphic section in
the induced manifold charts.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicExponentialSheaf
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M)
  (c : CechOneCocycle (unitsSheaf I M) U)

/-- The actual overlap value, extended by one away from the overlap. -/
def cocycleTransition (i j : ι) (x : M) : ℂˣ := by
  classical
  exact if hx : x ∈ U i ⊓ U j then
    Units.mk0 (unitSectionEval (c.value i j) ⟨x, hx⟩)
      (unitSectionEval_ne_zero (c.value i j) ⟨x, hx⟩)
    else 1

/-- On the original overlap the transition is the given actual section. -/
theorem cocycleTransition_apply (i j : ι) (x : M) (hx : x ∈ U i ⊓ U j) :
    (cocycleTransition I M U c i j x : ℂ) = unitSectionEval (c.value i j) ⟨x, hx⟩ := by
  classical
  simp only [cocycleTransition, dif_pos hx, Units.val_mk0]

theorem cocycleTransition_of_not_mem (i j : ι) (x : M) (hx : x ∉ U i ⊓ U j) :
    cocycleTransition I M U c i j x = 1 := by
  classical
  simp only [cocycleTransition, dif_neg hx]

/-- Restriction to the open overlap is literally the underlying
holomorphic map of the original cocycle value. -/
theorem cocycleTransition_comp_val (i j : ι) :
    (fun x : ↥(U i ⊓ U j) => (cocycleTransition I M U c i j x : ℂ)) =
      (unitSectionVal (c.value i j) : ↥(U i ⊓ U j) → ℂ) :=
  funext (fun x => cocycleTransition_apply I M U c i j x x.property)

/-- Holomorphicity on the actual overlap follows from the original
section and the proved open-subtype manifold comparison. -/
theorem cocycleTransition_contMDiffOn (i j : ι) :
    ContMDiffOn I 𝓘(ℂ) ω (fun x => (cocycleTransition I M U c i j x : ℂ))
      ((U i : Set M) ∩ U j) := by
  intro x hx
  have hd : ContMDiffAt I 𝓘(ℂ) ω (fun x => (cocycleTransition I M U c i j x : ℂ)) x := by
    apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : ↥(U i ⊓ U j)))).mp
    rw [cocycleTransition_comp_val I M U c i j]
    exact (unitSectionVal (c.value i j)).contMDiff _
  exact hd.contMDiffWithinAt

end Wikipedia.HopfProblem.HolomorphicPicardNative
