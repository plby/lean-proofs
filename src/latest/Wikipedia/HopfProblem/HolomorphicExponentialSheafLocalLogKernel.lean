import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The actual local kernel of the holomorphic exponential

A holomorphic section with exponential equal to one is locally an actual
constant integer multiple of `2πi`. Continuity supplies an open neighborhood
where its difference from its value at the chosen point lies in the open
imaginary strip `(-π, π)`. Injectivity of the complex exponential on that
strip proves constancy. No connectedness, separation, or countability
assumption on the base space is needed.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

/-- Equal exponentials determine equal complex numbers when their
difference has imaginary part in the open fundamental strip. -/
theorem eq_of_exp_eq_of_sub_im_mem_Ioo {a b : ℂ}
    (he : Complex.exp a = Complex.exp b)
    (hs : (a - b).im ∈ Ioo (-Real.pi) Real.pi) : a = b := by
  have hd : Complex.exp (a - b) = Complex.exp 0 := by
    rw [Complex.exp_sub, he, div_self (Complex.exp_ne_zero b), Complex.exp_zero]
  have hz : a - b = 0 := Complex.exp_inj_of_neg_pi_lt_of_le_pi hs.1 hs.2.le
    (by simpa only [Complex.zero_im] using neg_lt_zero.mpr Real.pi_pos)
    (by simpa only [Complex.zero_im] using Real.pi_pos.le) hd
  exact sub_eq_zero.mp hz

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Every actual section in the exponential kernel is an integer multiple
of `2πi` on a constructed open neighborhood of each of its points. -/
theorem exists_localKernelInteger {U : Opens M}
    (f : HolomorphicFunctionSheaf.Section I M U)
    (hexp : ∀ y : U, Complex.exp (f y) = 1) (x : U) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
      ∃ n : ℤ, ∀ y : V,
        f ⟨y, hVU y.property⟩ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  let W : Set U := {y | (f y - f x).im ∈ Ioo (-Real.pi) Real.pi}
  have hWo : IsOpen W := isOpen_Ioo.preimage
    (Complex.continuous_im.comp (f.contMDiff.continuous.sub continuous_const))
  have hxW : x ∈ W := by
    change (f x - f x).im ∈ Ioo (-Real.pi) Real.pi
    simpa only [sub_self, Complex.zero_im] using
      (show (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi from
        ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩)
  let V : Opens M := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val _ hWo⟩
  have hVU : V ≤ U := Subtype.coe_image_subset (U : Set M) W
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexp x)
  refine ⟨V, hVU, ⟨x, hxW, rfl⟩, n, ?_⟩
  rintro ⟨y, ⟨u, hu, rfl⟩⟩
  change f u = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  exact (eq_of_exp_eq_of_sub_im_mem_Ioo ((hexp u).trans (hexp x).symm) hu).trans hn

/-- The same local-kernel result with an ambient point and its membership
proof, retaining the actual inclusion into the original open set. -/
theorem exists_localKernelInteger_at {U : Opens M}
    (f : HolomorphicFunctionSheaf.Section I M U)
    (hexp : ∀ y : U, Complex.exp (f y) = 1) (x : M) (hx : x ∈ U) :
    ∃ (V : Opens M) (hVU : V ≤ U), x ∈ V ∧
      ∃ n : ℤ, ∀ y : V,
        f ⟨y, hVU y.property⟩ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
  exists_localKernelInteger I M f hexp ⟨x, hx⟩

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
