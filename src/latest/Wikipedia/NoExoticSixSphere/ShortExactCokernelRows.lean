import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Cokernels of maps between short exact rows

This is the snake-lemma input needed for coefficient changes on actual
relative singular complexes. Exactness is proved for the categorical
cokernel row. A monomorphism on the third component makes that row short
exact, rather than leaving the vanishing connecting morphism as an input.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.ShortExactCokernelRows

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex C} (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)

/-- The actual kernel-cokernel diagram of the given map of short complexes. -/
def snake : ShortComplex.SnakeInput C where
  L₀ := kernel f
  L₁ := S
  L₂ := T
  L₃ := cokernel f
  v₀₁ := kernel.ι f
  v₁₂ := f
  v₂₃ := cokernel.π f
  w₀₂ := kernel.condition f
  w₁₃ := cokernel.condition f
  h₀ := kernelIsKernel f
  h₃ := cokernelIsCokernel f
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

include hS hT

/-- The actual cokernel row is exact. -/
theorem cokernel_exact : (cokernel f).Exact := (snake f hS hT).L₃_exact

/-- Injectivity of the third vertical map kills the snake connecting source
and proves injectivity of the first map in the cokernel row. -/
theorem cokernel_shortExact [Mono f.τ₃] : (cokernel f).ShortExact := by
  let D := snake f hS hT
  have : Mono D.v₁₂.τ₃ := inferInstanceAs (Mono f.τ₃)
  have hzero : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
  have hm : Mono D.L₃.f := D.L₂'_exact.mono_g (hzero.eq_of_src _ _)
  have : Epi D.L₂.g := hT.epi_g
  exact {
    exact := D.L₃_exact
    mono_f := hm
    epi_g := ShortComplex.SnakeInput.epi_L₃_g D }

end NoExoticSixSphere.ShortExactCokernelRows
