import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The actual low-degree augmented resolution of a cochain complex

For a natural-degree cochain complex `K`, this is the exact sequence
`0 → H⁰(K) → K⁰ → Z¹(K) → H¹(K) → 0` in the original abelian category.
No injectivity or acyclicity assumption is required.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- The actual degree-zero differential with its codomain restricted to cycles. -/
def boundaryToCycles (K : CochainComplex C ℕ) : K.X 0 ⟶ K.cycles 1 :=
  K.toCycles 0 1

@[reassoc (attr := simp)]
theorem boundaryToCycles_iCycles (K : CochainComplex C ℕ) :
    boundaryToCycles K ≫ K.iCycles 1 = K.d 0 1 :=
  K.toCycles_i 0 1

@[reassoc (attr := simp)]
theorem boundaryToCycles_homologyπ (K : CochainComplex C ℕ) :
    boundaryToCycles K ≫ K.homologyπ 1 = 0 :=
  K.toCycles_comp_homologyπ 0 1

/-- The native short complex `K⁰ → Z¹(K) → H¹(K)`. -/
@[simps]
def complex (K : CochainComplex C ℕ) : ShortComplex C :=
  ShortComplex.mk (boundaryToCycles K) (K.homologyπ 1)
    (boundaryToCycles_homologyπ K)

/-- Its final arrow is the actual homology cokernel. -/
theorem complex_exact (K : CochainComplex C ℕ) : (complex K).Exact :=
  (complex K).exact_of_g_is_cokernel
    (K.homologyIsCokernel 0 1 (CochainComplex.prev_nat_succ 0))

instance complex_epi_g (K : CochainComplex C ℕ) : Epi (complex K).g :=
  inferInstanceAs (Epi (K.homologyπ 1))

/-- In degree zero there are no incoming boundaries, so homology equals cycles. -/
def initialCyclesIso (K : CochainComplex C ℕ) : K.homology 0 ≅ K.cycles 0 :=
  (K.isoHomologyπ 0 0 CochainComplex.prev_nat_zero (K.shape 0 0 (by decide))).symm

/-- The actual degree-zero homology inclusion. -/
def initialι (K : CochainComplex C ℕ) : K.homology 0 ⟶ K.X 0 :=
  (initialCyclesIso K).hom ≫ K.iCycles 0

instance initialι_mono (K : CochainComplex C ℕ) : Mono (initialι K) := by
  dsimp only [initialι]
  infer_instance

/-- The homology inclusion identifies the representative of every degree-zero cycle. -/
@[reassoc (attr := simp)]
theorem homologyπ_initialι (K : CochainComplex C ℕ) :
    K.homologyπ 0 ≫ initialι K = K.iCycles 0 := by
  dsimp only [initialι, initialCyclesIso, Iso.symm_hom]
  rw [K.isoHomologyπ_hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem initialι_boundaryToCycles (K : CochainComplex C ℕ) :
    initialι K ≫ boundaryToCycles K = 0 := by
  rw [← cancel_mono (K.iCycles 1), assoc, boundaryToCycles_iCycles, zero_comp]
  simp only [initialι, assoc, K.iCycles_d, comp_zero]

/-- Exactness at `K⁰` follows from the native cycles kernel. -/
theorem initial_exact (K : CochainComplex C ℕ) :
    (ShortComplex.mk (initialι K) (boundaryToCycles K)
      (initialι_boundaryToCycles K)).Exact := by
  let S := ShortComplex.mk (initialι K) (boundaryToCycles K)
    (initialι_boundaryToCycles K)
  let T := ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)
  let φ : S ⟶ T :=
    { τ₁ := (initialCyclesIso K).hom
      τ₂ := 𝟙 (K.X 0)
      τ₃ := K.iCycles 1
      comm₁₂ := by simp [S, T, initialι]
      comm₂₃ := by simp [S, T] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (initialCyclesIso K).hom)
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X 0)))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (K.iCycles 1))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (T.exact_of_f_is_kernel (K.cyclesIsKernel 0 1 (CochainComplex.next ℕ 0)))

/-- The low-degree augmented resolution, with literal homology and cycles objects. -/
def resolution (K : CochainComplex C ℕ) :
    CuspNormalization.SheafCohomologyResolution.AugmentedResolution C where
  F := K.homology 0
  complex := complex K
  ι := initialι K
  zero := initialι_boundaryToCycles K
  initial_exact := initial_exact K
  exact := complex_exact K
  mono_ι := initialι_mono K
  epi_g := complex_epi_g K

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
