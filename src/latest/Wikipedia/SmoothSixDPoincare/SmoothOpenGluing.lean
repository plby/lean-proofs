import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Gluing compatible smooth maps on two open sets

The glued map agrees on the whole of each open set, so all local germs and
derivatives are retained. No embedding or boundary-framing claim is made here.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace Y] [ChartedSpace F Y]

/-- Glue two compatible smooth maps, retaining their full restrictions to the open patches. -/
theorem exists_smooth_open_gluing {f g : X → Y} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g V) (hfg : EqOn f g (U ∩ V)) :
    ∃ k : X → Y, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k (U ∪ V) ∧
      EqOn k f U ∧ EqOn k g V := by
  classical
  let k := U.piecewise f g
  have hkf : EqOn k f U := fun x hx => piecewise_eq_of_mem U f g hx
  have hkg : EqOn k g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hkf hxU).trans (hfg ⟨hxU, hx⟩)
    · exact piecewise_eq_of_notMem U f g hxU
  exact ⟨k, (hf.congr (fun _ hx => hkf hx)).union_of_isOpen
    (hg.congr (fun _ hx => hkg hx)) hU hV, hkf, hkg⟩

end Wikipedia.SmoothSixDPoincare
