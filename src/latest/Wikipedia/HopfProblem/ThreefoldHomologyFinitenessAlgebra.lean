import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finiteness and vanishing in genuine integral exact sequences

The only finiteness assumptions are on the two neighbors of the middle
module. Since the integers are Noetherian, an exact sequence between those
neighbors makes the middle module finitely generated as well. Neither
freeness nor projectivity of the middle module is required. The five-term
version uses the original cokernel-to-kernel short exact sequence.

Vanishing is likewise a consequence of the actual maps and exactness:
if both neighbors vanish, so does the middle module.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra

variable {B H C : Type u}
  [AddCommGroup B] [AddCommGroup H] [AddCommGroup C]
  [Module ℤ B] [Module ℤ H] [Module ℤ C]

/-- An integral exact middle term between two finite modules is Noetherian. -/
theorem noetherian_of_exact (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) [Module.Finite ℤ B] [Module.Finite ℤ C] :
    IsNoetherian ℤ H :=
  isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm

/-- Finite generation needs exactness only at the middle term, not surjectivity
of its outgoing map or any projectivity assumption. -/
theorem finite_of_exact (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) [Module.Finite ℤ B] [Module.Finite ℤ C] :
    Module.Finite ℤ H := by
  have := noetherian_of_exact f g h
  infer_instance

/-- The same finiteness criterion in literal kernel-image form. -/
theorem finite_of_range_eq_ker (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Module.Finite ℤ B] [Module.Finite ℤ C] : Module.Finite ℤ H := by
  have : IsNoetherian ℤ H := isNoetherian_of_range_eq_ker f g h
  infer_instance

/-- Every middle element vanishes when both neighboring modules vanish. -/
theorem eq_zero_of_exact (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) [Subsingleton B] [Subsingleton C] (a : H) : a = 0 := by
  obtain ⟨b, hb⟩ := (h a).mp (Subsingleton.elim (g a) 0)
  exact hb.symm.trans ((congrArg f (Subsingleton.elim b 0)).trans (map_zero f))

theorem subsingleton_of_exact (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) [Subsingleton B] [Subsingleton C] : Subsingleton H :=
  ⟨fun a b => (eq_zero_of_exact f g h a).trans (eq_zero_of_exact f g h b).symm⟩

/-- Vanishing of the actual middle integral module as a categorical zero object. -/
theorem isZero_of_exact (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) [Subsingleton B] [Subsingleton C] :
    IsZero (ModuleCat.of ℤ H) :=
  ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_of_exact f g h)

/-- Categorical zero hypotheses on the two original neighbors suffice. -/
theorem isZero_of_exact_of_isZero (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) (hB : IsZero (ModuleCat.of ℤ B))
    (hC : IsZero (ModuleCat.of ℤ C)) : IsZero (ModuleCat.of ℤ H) := by
  have := ModuleCat.subsingleton_of_isZero hB
  have := ModuleCat.subsingleton_of_isZero hC
  exact isZero_of_exact f g h

/-- Exactness also detects vanishing when the two actual maps are both zero. -/
theorem eq_zero_of_exact_of_zero_maps (f : B →ₗ[ℤ] H) (g : H →ₗ[ℤ] C)
    (h : Function.Exact f g) (hf : f = 0) (hg : g = 0) (a : H) : a = 0 := by
  obtain ⟨b, hb⟩ := (h a).mp (by rw [hg]; rfl)
  exact hb.symm.trans (by rw [hf]; rfl)

section ShortComplex

variable (S : ShortComplex (ModuleCat.{u} ℤ))

/-- The criterion applies to any genuine categorical integral short complex. -/
theorem finite_of_shortComplex_exact (hS : S.Exact)
    [Module.Finite ℤ S.X₁] [Module.Finite ℤ S.X₃] : Module.Finite ℤ S.X₂ :=
  finite_of_range_eq_ker S.f.hom S.g.hom hS.moduleCat_range_eq_ker

/-- In particular, finite endpoints of a genuine short exact sequence give a finite middle. -/
theorem finite_of_shortExact (hS : S.ShortExact)
    [Module.Finite ℤ S.X₁] [Module.Finite ℤ S.X₃] : Module.Finite ℤ S.X₂ :=
  finite_of_shortComplex_exact S hS.exact

theorem subsingleton_of_shortComplex_exact (hS : S.Exact)
    [Subsingleton S.X₁] [Subsingleton S.X₃] : Subsingleton S.X₂ :=
  subsingleton_of_exact S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)

/-- Zero endpoints of an exact short complex force its actual middle object to be zero. -/
theorem isZero_of_shortComplex_exact (hS : S.Exact)
    (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ :=
  hS.isZero_of_both_isZero h₁ h₃

end ShortComplex

section FiveTerm

open TrianglePeriodFamilyHomologyAlgebra

variable {A D : Type u} [AddCommGroup A] [AddCommGroup D] [Module ℤ A] [Module ℤ D]

local instance finitenessCokernelModule (p : Submodule ℤ B) : Module ℤ (B ⧸ p) :=
  Submodule.Quotient.module p

local instance finitenessKernelModule (p : Submodule ℤ C) : Module ℤ p :=
  Submodule.module p

/-- The actual five-term sequence gives finite middle homology via its literal
cokernel-to-kernel extension. Only `B` and `C` need be finitely generated. -/
theorem finite_of_fiveTerm (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] H)
    (δ : H →ₗ[ℤ] C) (d : C →ₗ[ℤ] D)
    (hfj : Function.Exact f j) (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d)
    [Module.Finite ℤ B] [Module.Finite ℤ C] : Module.Finite ℤ H := by
  have : Module.Finite ℤ (cokernelKernelShortComplex f j δ d hfj hjδ hδd).X₁ := by
    change Module.Finite ℤ (B ⧸ LinearMap.range f)
    infer_instance
  have : Module.Finite ℤ (cokernelKernelShortComplex f j δ d hfj hjδ hδd).X₃ := by
    change Module.Finite ℤ (LinearMap.ker d)
    infer_instance
  exact finite_of_shortExact (cokernelKernelShortComplex f j δ d hfj hjδ hδd)
    (cokernelKernelShortComplex_shortExact f j δ d hfj hjδ hδd)

end FiveTerm

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra
