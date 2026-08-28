import Wikipedia.HopfProblem.SingularMayerVietorisSmallChains
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsBasis

/-!
# Genuine small singular chains for an arbitrary family of subsets

These are submodules of the original integral singular chain groups,
spanned by precisely the singular simplices lying in a member of the
family. The differential is the restriction of the original singular
differential, and the comparison map is the literal submodule inclusion.
The family need not be finite, open, or a cover for these constructions.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}

/-- Actual singular simplices carried by one member of the family. -/
abbrev SmallSimplex (U : ι → Set X) (n : ℕ) :=
  {σ : SingularSimplex X n // ∃ i, range σ ⊆ U i}

/-- The actual small-chain submodule for an arbitrary family. -/
def smallChainSubmodule (U : ι → Set X) (n : ℕ) : Submodule ℤ (Chains X n) :=
  Submodule.span ℤ
    (simplexChain X n '' {σ : SingularSimplex X n | ∃ i, range σ ⊆ U i})

theorem simplexChain_mem_small (U : ι → Set X) (n : ℕ) (σ : SingularSimplex X n)
    (hσ : ∃ i, range σ ⊆ U i) : simplexChain X n σ ∈ smallChainSubmodule U n :=
  Submodule.subset_span ⟨σ, hσ, rfl⟩

/-- Chains supported in any one member are small in the entire family. -/
theorem supportedChainSubmodule_le_small (U : ι → Set X) (i : ι) (n : ℕ) :
    SingularMayerVietoris.supportedChainSubmodule (U i) n ≤ smallChainSubmodule U n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  exact simplexChain_mem_small U n σ ⟨i, hσ⟩

/-- A simplex boundary is still carried by the same cover member. -/
theorem boundary_mem_small_succ (U : ι → Set X) (n : ℕ) (c : Chains X (n + 1))
    (hc : c ∈ smallChainSubmodule U (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom c ∈ smallChainSubmodule U n := by
  have hle : smallChainSubmodule U (n + 1) ≤
      (smallChainSubmodule U n).comap ((singularComplex X).d (n + 1) n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨i, hσ⟩, rfl⟩
    change (singularComplex X).d (n + 1) n (simplexChain X (n + 1) σ) ∈
      smallChainSubmodule U n
    rw [boundary_simplex]
    apply Submodule.sum_mem
    intro j hj
    apply (smallChainSubmodule U n).toAddSubgroup.zsmul_mem
    apply simplexChain_mem_small
    exact ⟨i, SingularMayerVietoris.simplex_face_supported (U i) n σ hσ j⟩
  exact hle hc

/-- The actual singular differential preserves all small-chain groups. -/
theorem boundary_mem_small (U : ι → Set X) (i j : ℕ) (c : Chains X i)
    (hc : c ∈ smallChainSubmodule U i) :
    ((singularComplex X).d i j).hom c ∈ smallChainSubmodule U j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have he : j + 1 = i := hij
    subst i
    exact boundary_mem_small_succ U j c hc
  · have he := congrArg (fun f : Chains X i ⟶ Chains X j => f.hom c)
      ((singularComplex X).shape i j hij)
    rw [he]
    exact Submodule.zero_mem _

instance smallChainModule (U : ι → Set X) (n : ℕ) : Module ℤ (smallChainSubmodule U n) :=
  (smallChainSubmodule U n).module

/-- Restriction of the original singular differential. -/
def smallDifferential (U : ι → Set X) (i j : ℕ) :
    smallChainSubmodule U i →ₗ[ℤ] smallChainSubmodule U j :=
  (((singularComplex X).d i j).hom.comp (smallChainSubmodule U i).subtype).codRestrict _
    (fun c => boundary_mem_small U i j c.1 c.2)

@[simp] theorem smallDifferential_val (U : ι → Set X) (i j : ℕ)
    (c : smallChainSubmodule U i) :
    (smallDifferential U i j c).1 = ((singularComplex X).d i j).hom c.1 := rfl

/-- The original singular chains restricted to small generators. -/
def smallComplex (U : ι → Set X) : ChainComplex (ModuleCat ℤ) ℕ where
  X n := ModuleCat.of ℤ (smallChainSubmodule U n)
  d i j := ModuleCat.ofHom (smallDifferential U i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains X i ⟶ Chains X j => f.hom c.1)
      ((singularComplex X).shape i j hij)
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains X i ⟶ Chains X k => f.hom c.1)
      ((singularComplex X).d_comp_d i j k)

/-- Literal inclusion into the original singular complex. -/
def smallInclusion (U : ι → Set X) : smallComplex U ⟶ singularComplex X where
  f n := ModuleCat.ofHom (smallChainSubmodule U n).subtype
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

@[simp] theorem smallInclusion_f_apply (U : ι → Set X) (n : ℕ)
    (c : (smallComplex U).X n) : (smallInclusion U).f n c = c.1 := rfl

theorem smallInclusion_f_injective (U : ι → Set X) (n : ℕ) :
    Function.Injective ((smallInclusion U).f n) :=
  Subtype.val_injective

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
