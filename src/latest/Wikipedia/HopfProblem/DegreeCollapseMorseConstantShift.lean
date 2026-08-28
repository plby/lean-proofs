import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationPreservation

/-!
# Constant critical-value shifts preserve native Morse data

The same signed chart and signs describe an additive constant change of
the actual function. Its first and second coordinate derivatives are
unchanged. Full constant-shift germs therefore preserve nondegeneracy,
the intrinsic Morse index, and the native derivative used for descent.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}

def shiftedSignedMorseChart (c : SignedMorseChart (E := E) f p) (k : ℝ) :
    SignedMorseChart (E := E) (fun x => f x + k) p where
  weights := c.weights
  signs := c.signs
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation x hx := by rw [c.equation x hx]; ring
  inverse_equation z hz := by rw [c.inverse_equation z hz]; ring

theorem isMorseAt_add_const (hm : IsMorseAt E f p) (k : ℝ) :
    IsMorseAt E (fun x => f x + k) p := by
  obtain ⟨e, he, hp, hgood⟩ := hm
  have hd : fderiv ℝ ((fun x => f x + k) ∘ e.symm) = fderiv ℝ (f ∘ e.symm) := by
    funext z
    exact fderiv_add_const k
  refine ⟨e, he, hp, ?_⟩
  rw [hd]
  exact hgood

theorem isMorse_add_const (hm : IsMorse E f) (k : ℝ) : IsMorse E (fun x => f x + k) :=
  fun x => isMorseAt_add_const (hm x) k

theorem isMorseAt_of_add_const_germ (hm : IsMorseAt E f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) : IsMorseAt E g p :=
  MorseCancellationPreservation.isMorseAt_of_same_germ (isMorseAt_add_const hm k) hgerm

theorem nativeMorseIndex_add_const (c : SignedMorseChart (E := E) f p) (k : ℝ) :
    nativeMorseIndex E (fun x => f x + k) p = nativeMorseIndex E f p := by
  rw [nativeMorseIndex_eq_chart (shiftedSignedMorseChart c k), nativeMorseIndex_eq_chart c]
  rfl

theorem nativeMorseIndex_of_add_const_germ (c : SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    nativeMorseIndex E g p = nativeMorseIndex E f p :=
  (nativeMorseIndex_congr_germ hgerm).trans (nativeMorseIndex_add_const c k)

theorem mfderiv_of_add_const_germ
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p := by
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p : E →L[ℝ] ℝ) =
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p : E →L[ℝ] ℝ)
  calc
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun x => f x + k) p : E →L[ℝ] ℝ) := hgerm.mfderiv_eq
    _ = _ := by
      have hs : mvfderiv 𝓘(ℝ, E) (fun x => f x + k) p = mvfderiv 𝓘(ℝ, E) f p := by
        rw [mvfderiv_fun_add hf mdifferentiableAt_const, mvfderiv_const, add_zero]
      exact hs

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
