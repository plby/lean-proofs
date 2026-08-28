import Mathlib.Algebra.Exact.Sequence
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Rational rank formulas for actual exact sequences

Finiteness of the unknown middle vector space is derived from the finite
adjacent terms. The five-term formula requires injectivity at the first end
and surjectivity at the last end. Integral sequences are rationalized by the
literal tensor base-change maps, using flatness of `ℚ` over `ℤ`; no freeness or
rank formula for an unknown integral module is assumed.
-/

noncomputable section

open Function Module
open scoped TensorProduct

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra

section Rational

variable {A B C H D : Type*}
variable [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C] [AddCommGroup H] [Module ℚ H]
variable [AddCommGroup D] [Module ℚ D]

/-- Exactness at the middle and finiteness of both adjacent vector spaces
already imply finiteness of the middle; neither endpoint condition is needed. -/
theorem rational_finite_of_exact [Module.Finite ℚ A] [Module.Finite ℚ C]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C) (hfg : Exact f g) :
    Module.Finite ℚ B := by
  have h : Exact f g.rangeRestrict := by
    apply ((Submodule.subtype_injective (LinearMap.range g)).comp_exact_iff_exact).mp
    exact hfg
  exact Module.Finite.of_exact h g.surjective_rangeRestrict

/-- Rank additivity for a short exact rational sequence. Finiteness of the
middle is a consequence, not an additional hypothesis. -/
theorem rational_finrank_eq_add_of_shortExact
    [Module.Finite ℚ A] [Module.Finite ℚ C]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g) :
    finrank ℚ B = finrank ℚ A + finrank ℚ C := by
  have := Module.Finite.of_exact hfg hg
  have h := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hfg.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hf] at h
  omega

/-- For an arbitrary exact middle, its dimension is the sum of the dimensions
of the adjacent images. This does not impose either endpoint condition. -/
theorem rational_finrank_eq_add_ranges_of_exact
    [Module.Finite ℚ A] [Module.Finite ℚ C]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C) (hfg : Exact f g) :
    finrank ℚ B = finrank ℚ (LinearMap.range f) + finrank ℚ (LinearMap.range g) := by
  have := rational_finite_of_exact f g hfg
  have h := g.finrank_range_add_finrank_ker
  rw [hfg.linearMap_ker_eq] at h
  omega

/-- The unsigned dimension identity for a five-term exact sequence, with both
endpoint conditions retained explicitly. Only the four outer terms are
assumed finite-dimensional. -/
theorem rational_finrank_balance_of_exact_five
    [Module.Finite ℚ A] [Module.Finite ℚ B]
    [Module.Finite ℚ C] [Module.Finite ℚ D]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] H) (h : H →ₗ[ℚ] C) (k : C →ₗ[ℚ] D)
    (hf : Injective f) (hfg : Exact f g) (hgh : Exact g h)
    (hhk : Exact h k) (hk : Surjective k) :
    finrank ℚ B + finrank ℚ C = finrank ℚ A + finrank ℚ H + finrank ℚ D := by
  have := rational_finite_of_exact g h hgh
  have hB := g.finrank_range_add_finrank_ker
  have hH := h.finrank_range_add_finrank_ker
  have hC := k.finrank_range_add_finrank_ker
  rw [hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hB
  rw [hgh.linearMap_ker_eq] at hH
  rw [LinearMap.range_eq_top.mpr hk, finrank_top, hhk.linearMap_ker_eq] at hC
  omega

/-- The signed Euler form of the genuine five-term identity. -/
theorem rational_finrank_euler_of_exact_five
    [Module.Finite ℚ A] [Module.Finite ℚ B]
    [Module.Finite ℚ C] [Module.Finite ℚ D]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] H) (h : H →ₗ[ℚ] C) (k : C →ₗ[ℚ] D)
    (hf : Injective f) (hfg : Exact f g) (hgh : Exact g h)
    (hhk : Exact h k) (hk : Surjective k) :
    (finrank ℚ A : ℤ) - finrank ℚ B + finrank ℚ H - finrank ℚ C + finrank ℚ D = 0 := by
  have h := rational_finrank_balance_of_exact_five f g h k hf hfg hgh hhk hk
  omega

end Rational

section Rationalization

variable {A B C H D : Type*}
variable [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
variable [AddCommGroup C] [Module ℤ C] [AddCommGroup H] [Module ℤ H]
variable [AddCommGroup D] [Module ℤ D]

/-- Base change by `ℚ` preserves the exactness of the actual integral maps. -/
theorem rationalization_exact (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (hfg : Exact f g) :
    Exact (f.baseChange ℚ) (g.baseChange ℚ) := by
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  change Exact (f.lTensor ℚ) (g.lTensor ℚ)
  exact Module.Flat.lTensor_exact ℚ hfg

/-- No torsion-free assumption on either module is required for the
rationalization of an injective integral map to be injective. -/
theorem rationalization_injective (f : A →ₗ[ℤ] B) (hf : Injective f) :
    Injective (f.baseChange ℚ) := by
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  change Injective (f.lTensor ℚ)
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Tensor base change preserves surjectivity of the original map. -/
theorem rationalization_surjective (f : A →ₗ[ℤ] B) (hf : Surjective f) :
    Surjective (f.baseChange ℚ) :=
  LinearMap.baseChange_surjective ℚ hf

/-- The literal rationalized maps form a short exact sequence. -/
theorem rationalization_shortExact (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g) :
    Injective (f.baseChange ℚ) ∧ Exact (f.baseChange ℚ) (g.baseChange ℚ) ∧
      Surjective (g.baseChange ℚ) :=
  ⟨rationalization_injective f hf, rationalization_exact f g hfg,
    rationalization_surjective g hg⟩

/-- Rationalization of a finitely generated integral module is finite-dimensional. -/
theorem rationalization_finite (A : Type*) [AddCommGroup A] [Module ℤ A]
    [Module.Finite ℤ A] : Module.Finite ℚ (ℚ ⊗[ℤ] A) := inferInstance

/-- Rank additivity for the actual rationalization of an integral short exact
sequence, with only integral finiteness of its endpoint modules assumed. -/
theorem rationalization_finrank_eq_add_of_shortExact
    [Module.Finite ℤ A] [Module.Finite ℤ C]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g) :
    finrank ℚ (ℚ ⊗[ℤ] B) = finrank ℚ (ℚ ⊗[ℤ] A) + finrank ℚ (ℚ ⊗[ℤ] C) :=
  rational_finrank_eq_add_of_shortExact (f.baseChange ℚ) (g.baseChange ℚ)
    (rationalization_injective f hf) (rationalization_exact f g hfg)
    (rationalization_surjective g hg)

/-- The five-term rational rank balance of actual integral maps. -/
theorem rationalization_finrank_balance_of_exact_five
    [Module.Finite ℤ A] [Module.Finite ℤ B]
    [Module.Finite ℤ C] [Module.Finite ℤ D]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] H) (h : H →ₗ[ℤ] C) (k : C →ₗ[ℤ] D)
    (hf : Injective f) (hfg : Exact f g) (hgh : Exact g h)
    (hhk : Exact h k) (hk : Surjective k) :
    finrank ℚ (ℚ ⊗[ℤ] B) + finrank ℚ (ℚ ⊗[ℤ] C) =
      finrank ℚ (ℚ ⊗[ℤ] A) + finrank ℚ (ℚ ⊗[ℤ] H) + finrank ℚ (ℚ ⊗[ℤ] D) :=
  rational_finrank_balance_of_exact_five
    (f.baseChange ℚ) (g.baseChange ℚ) (h.baseChange ℚ) (k.baseChange ℚ)
    (rationalization_injective f hf) (rationalization_exact f g hfg)
    (rationalization_exact g h hgh) (rationalization_exact h k hhk)
    (rationalization_surjective k hk)

end Rationalization

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra
