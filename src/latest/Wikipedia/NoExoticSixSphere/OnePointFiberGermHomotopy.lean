import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Homotopies from agreement near a common distinguished fiber

Maps into a one-point compactification of a real normed space which agree
on an open neighborhood of their common infinity fiber are homotopic.
Outside that fiber the homotopy is affine interpolation in the original
finite coordinates. Near the fiber it is exactly the original map, so
continuity there does not assert continuity of interpolation at infinity.
Every point where the endpoint maps agree is fixed throughout.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.OnePointFiberGerm

variable {E X : Type*} [NormedAddCommGroup E]

def finitePart (y : OnePoint E) : E := y.elim 0 id

theorem coe_finitePart {y : OnePoint E} (hy : y ≠ ∞) :
    ((finitePart y : E) : OnePoint E) = y := by
  obtain ⟨v, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hy
  rfl

theorem continuousAt_finitePart {y : OnePoint E} (hy : y ≠ ∞) :
    ContinuousAt (finitePart : OnePoint E → E) y := by
  obtain ⟨v, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hy
  exact OnePoint.continuousAt_coe.mpr continuousAt_id

variable [NormedSpace ℝ E]

def interpolate (f g : X → OnePoint E) (t : I) (x : X) : OnePoint E := by
  classical
  exact if f x = ∞ then ∞ else
    (((1 - (t : ℝ)) • finitePart (f x) + (t : ℝ) • finitePart (g x) : E) : OnePoint E)

theorem interpolate_fixed (f g : X → OnePoint E) (t : I) (x : X) (h : f x = g x) :
    interpolate f g t x = f x := by
  classical
  by_cases hf : f x = ∞
  · simp [interpolate, hf]
  · rw [interpolate, if_neg hf, ← h, ← add_smul, sub_add_cancel, one_smul]
    exact coe_finitePart hf

theorem interpolate_zero (f g : X → OnePoint E) (x : X) :
    interpolate f g 0 x = f x := by
  classical
  by_cases hf : f x = ∞
  · simp [interpolate, hf]
  · simpa [interpolate, hf] using coe_finitePart hf

theorem interpolate_one (f g : X → OnePoint E)
    (hK : ∀ x, f x = ∞ ↔ g x = ∞) (x : X) :
    interpolate f g 1 x = g x := by
  classical
  by_cases hf : f x = ∞
  · simp [interpolate, hf, (hK x).mp hf]
  · have hg : g x ≠ ∞ := fun h ↦ hf ((hK x).mpr h)
    simpa [interpolate, hf] using coe_finitePart hg

variable [TopologicalSpace X]

theorem continuous_interpolate (f g : C(X, OnePoint E))
    (hK : ∀ x, f x = ∞ ↔ g x = ∞) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {∞} ⊆ U) (hfg : EqOn f g U) :
    Continuous (fun z : I × X ↦ interpolate f g z.1 z.2) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z.2 ∈ U
  · apply (f.continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [(hU.preimage continuous_snd).mem_nhds hz] with w hw
    exact interpolate_fixed f g w.1 w.2 (hfg hw)
  · have hf : f z.2 ≠ ∞ := fun h ↦ hz (hKU h)
    have hg : g z.2 ≠ ∞ := fun h ↦ hf ((hK z.2).mpr h)
    have hF : ContinuousAt (fun w : I × X ↦ finitePart (f w.2)) z :=
      (continuousAt_finitePart hf).comp (f := fun w : I × X ↦ f w.2)
      (f.continuous.comp continuous_snd).continuousAt
    have hG : ContinuousAt (fun w : I × X ↦ finitePart (g w.2)) z :=
      (continuousAt_finitePart hg).comp (f := fun w : I × X ↦ g w.2)
      (g.continuous.comp continuous_snd).continuousAt
    have ht : ContinuousAt (fun w : I × X ↦ (w.1 : ℝ)) z :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have hl : ContinuousAt (fun w : I × X ↦
        (1 - (w.1 : ℝ)) • finitePart (f w.2) + (w.1 : ℝ) • finitePart (g w.2)) z :=
      ((continuousAt_const.sub ht).smul hF).add (ht.smul hG)
    have hc := OnePoint.continuous_coe.continuousAt.comp hl
    apply hc.congr_of_eventuallyEq
    have hne : ∀ᶠ w : I × X in 𝓝 z, f w.2 ≠ ∞ :=
      (f.continuous.comp continuous_snd).continuousAt.eventually
        (OnePoint.isClosed_infty.isOpen_compl.mem_nhds hf)
    filter_upwards [hne] with w hw
    exact if_neg hw

/-- A concrete homotopy in the original one-point compactification. -/
def homotopy (f g : C(X, OnePoint E))
    (hK : ∀ x, f x = ∞ ↔ g x = ∞) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {∞} ⊆ U) (hfg : EqOn f g U) : f.Homotopy g where
  toFun z := interpolate f g z.1 z.2
  continuous_toFun := continuous_interpolate f g hK U hU hKU hfg
  map_zero_left := interpolate_zero f g
  map_one_left := interpolate_one f g hK

theorem homotopy_fixed (f g : C(X, OnePoint E))
    (hK : ∀ x, f x = ∞ ↔ g x = ∞) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {∞} ⊆ U) (hfg : EqOn f g U) (t : I) (x : X) (hx : f x = g x) :
    homotopy f g hK U hU hKU hfg (t, x) = f x :=
  interpolate_fixed f g t x hx

end NoExoticSixSphere.OnePointFiberGerm
