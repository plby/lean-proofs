import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The cokernel-to-kernel extension of an exact sequence

For an exact segment `A → B → C → D → E` of integral modules, the original
maps induce a short exact sequence `coker(A → B) → C → ker(D → E)`.
The constructions below use the literal quotient of `B` and submodule of
`D`, and retain the original maps on representatives. They do not assume
any geometric identification of the modules.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

open CategoryTheory

variable {A B C D E : Type u}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
  [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]

local instance cokernelQuotientModule (p : Submodule ℤ B) : Module ℤ (B ⧸ p) :=
  Submodule.Quotient.module p

local instance kernelModule (p : Submodule ℤ D) : Module ℤ p :=
  Submodule.module p

/-- The middle map descended to the quotient by the preceding image. -/
def cokernelToMiddle (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (hfj : Function.Exact f j) :
    (B ⧸ LinearMap.range f) →ₗ[ℤ] C :=
  (LinearMap.range f).liftQ j hfj.linearMap_ker_eq.ge

/-- On a quotient representative the descended map is exactly `j`. -/
@[simp] theorem cokernelToMiddle_mkQ (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C)
    (hfj : Function.Exact f j) (b : B) :
    cokernelToMiddle f j hfj ((LinearMap.range f).mkQ b) = j b := rfl

/-- Descending through the kernel does not change the image of `j`. -/
theorem cokernelToMiddle_range (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C)
    (hfj : Function.Exact f j) :
    LinearMap.range (cokernelToMiddle f j hfj) = LinearMap.range j :=
  (LinearMap.range f).range_liftQ j _

/-- Exactness identifies the quotient relation with the full kernel of `j`,
so the descended map is injective. -/
theorem cokernelToMiddle_injective (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C)
    (hfj : Function.Exact f j) :
    Function.Injective (cokernelToMiddle f j hfj) := by
  apply LinearMap.ker_eq_bot.mp
  exact (LinearMap.range f).ker_liftQ_eq_bot j _ hfj.linearMap_ker_eq.le

/-- The outgoing map with codomain restricted to the following kernel. -/
def middleToKernel (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E) (hδd : Function.Exact δ d) :
    C →ₗ[ℤ] LinearMap.ker d :=
  δ.codRestrict (LinearMap.ker d) hδd.apply_apply_eq_zero

/-- Forgetting the kernel subtype recovers exactly the outgoing map `δ`. -/
@[simp] theorem middleToKernel_val (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hδd : Function.Exact δ d) (c : C) :
    (middleToKernel δ d hδd c : D) = δ c := rfl

/-- Exactness at `D` makes the kernel-restricted outgoing map surjective. -/
theorem middleToKernel_surjective (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hδd : Function.Exact δ d) :
    Function.Surjective (middleToKernel δ d hδd) := by
  intro y
  obtain ⟨c, hc⟩ := (hδd y.1).mp y.2
  exact ⟨c, Subtype.ext hc⟩

/-- The two induced maps compose to zero. -/
theorem middleToKernel_comp_cokernelToMiddle
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hfj : Function.Exact f j) (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    (middleToKernel δ d hδd).comp (cokernelToMiddle f j hfj) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨b, rfl⟩ := (LinearMap.range f).mkQ_surjective q
  apply Subtype.ext
  change δ (j b) = 0
  exact hjδ.apply_apply_eq_zero b

/-- Exactness at the middle module is preserved by passage to the preceding
cokernel and the following kernel. -/
theorem cokernelToMiddle_middleToKernel_exact
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hfj : Function.Exact f j) (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    Function.Exact (cokernelToMiddle f j hfj) (middleToKernel δ d hδd) := by
  intro c
  constructor
  · intro hc
    have hδc : δ c = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb⟩ := (hjδ c).mp hδc
    exact ⟨(LinearMap.range f).mkQ b, hb⟩
  · rintro ⟨q, rfl⟩
    exact LinearMap.congr_fun
      (middleToKernel_comp_cokernelToMiddle f j δ d hfj hjδ hδd) q

/-- The actual short complex of integral modules induced by the exact
five-term segment. -/
def cokernelKernelShortComplex
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hfj : Function.Exact f j) (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.moduleCatMk (cokernelToMiddle f j hfj) (middleToKernel δ d hδd)
    (middleToKernel_comp_cokernelToMiddle f j δ d hfj hjδ hδd)

/-- The cokernel-to-kernel sequence is short exact in `ModuleCat ℤ`. -/
theorem cokernelKernelShortComplex_shortExact
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E)
    (hfj : Function.Exact f j) (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    (cokernelKernelShortComplex f j δ d hfj hjδ hδd).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact cokernelToMiddle_middleToKernel_exact f j δ d hfj hjδ hδd
  · exact cokernelToMiddle_injective f j hfj
  · exact middleToKernel_surjective δ d hδd

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
