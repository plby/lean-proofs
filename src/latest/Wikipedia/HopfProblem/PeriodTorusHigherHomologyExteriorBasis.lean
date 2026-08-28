import Wikipedia.HopfProblem.LocalSystemMatrices
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorMinors

/-!
# Ordered bases of the actual rank-four exterior powers

The degree-two order is `01, 02, 03, 12, 13, 23`, and the degree-three order
is `012, 013, 023, 123`. These are the increasing-subset bases of Mathlib's
exterior powers of the integral rank-four lattice. The same index order applies
to the source's basis `(γ,u,w,δ)` and its hatted dual basis on the lattice.
This file makes no identification with singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

open LocalSystemMatrices

/-- The actual integral exterior power of the rank-four lattice. -/
abbrev latticeExterior (n : ℕ) := ⋀[ℤ]^n Lattice

/-- The standard ordered lattice basis. -/
def latticeBasis : Module.Basis (Fin 4) ℤ Lattice := Pi.basisFun ℤ (Fin 4)

/-- The actual exterior-power basis before the finite lexicographic reindexing. -/
def latticeExteriorBasis (n : ℕ) :
    Module.Basis (Set.powersetCard (Fin 4) n) ℤ (latticeExterior n) :=
  standardExteriorBasis 4 n

theorem pairIndices_strictMono (i : Fin 6) : StrictMono (pairIndices i) := by
  fin_cases i <;> decide

theorem tripleIndices_strictMono (i : Fin 4) : StrictMono (tripleIndices i) := by
  fin_cases i <;> decide

theorem pairIndices_injective : Function.Injective pairIndices := by decide

theorem tripleIndices_injective : Function.Injective tripleIndices := by decide

def pairEmbedding (i : Fin 6) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (pairIndices i) (pairIndices_strictMono i)

def tripleEmbedding (i : Fin 4) : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (tripleIndices i) (tripleIndices_strictMono i)

def pairSubset (i : Fin 6) : Set.powersetCard (Fin 4) 2 :=
  Set.powersetCard.ofFinEmbEquiv (pairEmbedding i)

def tripleSubset (i : Fin 4) : Set.powersetCard (Fin 4) 3 :=
  Set.powersetCard.ofFinEmbEquiv (tripleEmbedding i)

@[simp] theorem pairSubset_ordered (i : Fin 6) :
    (Set.powersetCard.ofFinEmbEquiv.symm (pairSubset i) : Fin 2 → Fin 4) =
      pairIndices i := by
  rw [pairSubset, Equiv.symm_apply_apply]
  rfl

@[simp] theorem tripleSubset_ordered (i : Fin 4) :
    (Set.powersetCard.ofFinEmbEquiv.symm (tripleSubset i) : Fin 3 → Fin 4) =
      tripleIndices i := by
  rw [tripleSubset, Equiv.symm_apply_apply]
  rfl

theorem pairSubset_injective : Function.Injective pairSubset := by
  intro i j hij
  apply pairIndices_injective
  simpa only [pairSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 2 → Fin 4)) hij

theorem tripleSubset_injective : Function.Injective tripleSubset := by
  intro i j hij
  apply tripleIndices_injective
  simpa only [tripleSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 3 → Fin 4)) hij

theorem pairSubset_bijective : Function.Bijective pairSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨pairSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using
    (Set.powersetCard.card (Fin 4) 2).symm

theorem tripleSubset_bijective : Function.Bijective tripleSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨tripleSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 3 = 4 by decide] using
    (Set.powersetCard.card (Fin 4) 3).symm

/-- The complete lexicographic enumeration of two-element subsets. -/
def pairSubsetEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective pairSubset pairSubset_bijective

/-- The complete lexicographic enumeration of three-element subsets. -/
def tripleSubsetEquiv : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective tripleSubset tripleSubset_bijective

@[simp] theorem pairSubsetEquiv_apply (i : Fin 6) :
    pairSubsetEquiv i = pairSubset i := rfl

@[simp] theorem tripleSubsetEquiv_apply (i : Fin 4) :
    tripleSubsetEquiv i = tripleSubset i := rfl

/-- The degree-two basis in the source's ordered-minor convention. -/
def squareBasis : Module.Basis (Fin 6) ℤ (latticeExterior 2) :=
  (latticeExteriorBasis 2).reindex pairSubsetEquiv.symm

/-- The degree-three basis in the source's ordered-minor convention. -/
def cubeBasis : Module.Basis (Fin 4) ℤ (latticeExterior 3) :=
  (latticeExteriorBasis 3).reindex tripleSubsetEquiv.symm

theorem squareBasis_apply (i : Fin 6) :
    squareBasis i = exteriorPower.ιMulti ℤ 2 (latticeBasis ∘ pairIndices i) := by
  rw [squareBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 2 (pairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, pairSubset_ordered]
  rfl

theorem cubeBasis_apply (i : Fin 4) :
    cubeBasis i = exteriorPower.ιMulti ℤ 3 (latticeBasis ∘ tripleIndices i) := by
  rw [cubeBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 3 (tripleSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, tripleSubset_ordered]
  rfl

/-- Actual degree-two exterior coordinates, not a separately defined model module. -/
def squareCoordinates : latticeExterior 2 ≃ₗ[ℤ] (Fin 6 → ℤ) := squareBasis.equivFun

/-- Actual degree-three exterior coordinates. -/
def cubeCoordinates : latticeExterior 3 ≃ₗ[ℤ] (Fin 4 → ℤ) := cubeBasis.equivFun

@[simp] theorem squareCoordinates_apply (x : latticeExterior 2) (i : Fin 6) :
    squareCoordinates x i = squareBasis.repr x i :=
  congrFun (squareBasis.equivFun_apply x) i

@[simp] theorem cubeCoordinates_apply (x : latticeExterior 3) (i : Fin 4) :
    cubeCoordinates x i = cubeBasis.repr x i :=
  congrFun (cubeBasis.equivFun_apply x) i

theorem latticeExterior_finrank (n : ℕ) :
    Module.finrank ℤ (latticeExterior n) = Nat.choose 4 n := by
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis latticeBasis, Fintype.card_fin]

theorem square_finrank : Module.finrank ℤ (latticeExterior 2) = 6 := by
  rw [latticeExterior_finrank]
  decide

theorem cube_finrank : Module.finrank ℤ (latticeExterior 3) = 4 := by
  rw [latticeExterior_finrank]
  decide

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
