import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

open scoped BigOperators

/-- Normalize a prospective full-support relation by setting its distinguished
`none` coordinate to one. -/
def normalizedNull {K ι : Type*} [One K] (tail : ι → K) : Option ι → K
  | none => 1
  | some i => tail i

/-- Given a basis-sized row family, define the last row so that
`normalizedNull tail` is a relation. -/
def generatedRows {K D ι : Type*} [Field K] [AddCommGroup D] [Module K D]
    [Fintype ι] (tail : ι → K) (basis : ι → D) : Option ι → D
  | none => -Fintype.linearCombination K basis tail
  | some i => basis i

/-- The generated rows have the advertised normalized relation. -/
theorem normalizedNull_generatedRows_relation
    {K D ι : Type*} [Field K] [AddCommGroup D] [Module K D]
    [Fintype ι] (tail : ι → K) (basis : ι → D) :
    ∑ o : Option ι, normalizedNull tail o • generatedRows tail basis o = 0 := by
  rw [Fintype.sum_option]
  simp [normalizedNull, generatedRows, Fintype.linearCombination_apply]

/-- If the tail is coordinatewise nonzero, the normalized relation has full
support. -/
theorem normalizedNull_fullSupport
    {K ι : Type*} [One K] [Zero K] (hone : (1 : K) ≠ 0)
    (tail : ι → K) (htail : ∀ i, tail i ≠ 0) :
    ∀ o : Option ι, normalizedNull tail o ≠ 0 := by
  intro o
  cases o with
  | none => simpa [normalizedNull] using hone
  | some i => simpa [normalizedNull] using htail i

/-- A linearly independent family indexed by `ι` spans the coordinate space
`ι → K`; hence the generated `Option ι` rows span as well. -/
theorem generatedRows_surjective
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (tail : ι → K) (basis : ι → (ι → K))
    (hli : LinearIndependent K basis) :
    Function.Surjective (Fintype.linearCombination K (generatedRows tail basis)) := by
  have hcard : Fintype.card ι = Module.finrank K (ι → K) :=
    (Module.finrank_fintype_fun_eq_card K).symm
  let bas : Module.Basis ι K (ι → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbas : (bas : ι → (ι → K)) = basis :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  intro y
  let a : Option ι → K
    | none => 0
    | some i => bas.repr y i
  refine ⟨a, ?_⟩
  rw [Fintype.linearCombination_apply, Fintype.sum_option]
  simp only [a, zero_smul, zero_add, generatedRows]
  simpa [hbas] using bas.sum_repr y

/-- The generated child rows determine both the basis rows and the normalized
relation tail.  This injectivity prevents overcounting in the favorable-sample
enumeration. -/
theorem generatedRows_pair_injective
    {K D ι : Type*} [Field K] [AddCommGroup D] [Module K D]
    [Fintype ι]
    {tail₁ tail₂ : ι → K} {basis₁ basis₂ : ι → D}
    (hli : LinearIndependent K basis₁)
    (hrows : generatedRows tail₁ basis₁ = generatedRows tail₂ basis₂) :
    tail₁ = tail₂ ∧ basis₁ = basis₂ := by
  have hbasis : basis₁ = basis₂ := by
    funext i
    have h := congrFun hrows (some i)
    simpa [generatedRows] using h
  subst basis₂
  have hnone := congrFun hrows none
  simp only [generatedRows, neg_inj] at hnone
  have hinj := hli.fintypeLinearCombination_injective
  exact ⟨hinj hnone, rfl⟩

end Erdos538.IsotropicKernel
