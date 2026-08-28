import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheafBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesCoordinates

/-!
# The actual finite-chart frame of the vanishing sheaf

Every open subset of the finite sphere chart excludes infinity.  Its
vanishing-at-infinity condition is therefore vacuous, and the literal
constant-one section is a frame.  The resulting linear equivalence is
the identity on underlying holomorphic sections and commutes with the
actual restriction maps on every smaller open subset.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

theorem infty_not_mem_of_le_finiteChart (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    (∞ : RiemannSphere) ∉ U :=
  fun h => infty_not_mem_finiteChart (hU h)

/-- On a subopen of the finite chart, every actual holomorphic section
belongs to the actual vanishing ideal. -/
theorem finiteSection_mem_vanishingIdeal (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    f ∈ vanishingIdeal U :=
  fun h => (infty_not_mem_of_le_finiteChart U hU h).elim

/-- The literal constant-one section is the finite-chart frame. -/
def finiteFrame (U : Opens RiemannSphere) (hU : U ≤ finiteChart) : NegativeOneSection U :=
  ⟨1, finiteSection_mem_vanishingIdeal U hU 1⟩

@[simp] theorem finiteFrame_val (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    (finiteFrame U hU).val = 1 := rfl

@[simp] theorem finiteFrame_apply (U : Opens RiemannSphere) (hU : U ≤ finiteChart) (p : U) :
    finiteFrame U hU p = 1 := rfl

/-- The actual finite-chart trivialization is linear over the full
ring of holomorphic sections of the given subopen set. -/
def finiteTrivialization (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U ≃ₗ[
      HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U where
  toFun f := ⟨f, finiteSection_mem_vanishingIdeal U hU f⟩
  invFun f := f.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finiteTrivialization_val (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    (finiteTrivialization U hU f).val = f := rfl

@[simp] theorem finiteTrivialization_apply (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (p : U) :
    finiteTrivialization U hU f p = f p := rfl

@[simp] theorem finiteTrivialization_symm_apply (U : Opens RiemannSphere)
    (hU : U ≤ finiteChart) (f : NegativeOneSection U) :
    (finiteTrivialization U hU).symm f = f.val := rfl

@[simp] theorem finiteTrivialization_one (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    finiteTrivialization U hU 1 = finiteFrame U hU := rfl

/-- The trivialization is actual multiplication of the coefficient
section by the constant-one frame. -/
theorem finiteTrivialization_as_frame (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    finiteTrivialization U hU f = f • finiteFrame U hU := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  change f p = f p * 1
  exact (mul_one _).symm

/-- The frame restricts to the literal frame on every smaller finite
chart open set. -/
theorem finiteFrame_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ finiteChart) :
    negativeOneRestriction h (finiteFrame V hV) = finiteFrame U (h.trans hV) := rfl

/-- The module trivializations commute with actual restriction of both
coefficient functions and sections of the vanishing sheaf. -/
theorem finiteTrivialization_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ finiteChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere V) :
    negativeOneRestriction h (finiteTrivialization V hV f) =
      finiteTrivialization U (h.trans hV)
        (ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h f) := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
