import Wikipedia.HopfProblem.EllipticHigherHomologyData
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorMinors

/-!
# Ordered bases of the actual rank-three exterior powers

The exterior square has the ordered basis `01, 02, 12`. The exterior cube
has the single ordered basis vector `012`. These are bases of Mathlib's
actual exterior powers of the integral elliptic fibre lattice. The scalar
coordinate in degree three evaluates the single basis coefficient.
This file makes no identification with singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open PeriodTorusHigherHomologyExterior

/-- The actual integral exterior power of the rank-three elliptic fibre lattice. -/
abbrev torusExterior (n : ℕ) := ⋀[ℤ]^n FibreLattice

/-- The standard ordered basis of the integral elliptic fibre lattice. -/
def torusLatticeBasis : Module.Basis (Fin 3) ℤ FibreLattice := Pi.basisFun ℤ (Fin 3)

/-- The actual exterior-power basis indexed by increasing subsets. -/
def torusExteriorBasis (n : ℕ) :
    Module.Basis (Set.powersetCard (Fin 3) n) ℤ (torusExterior n) :=
  standardExteriorBasis 3 n

theorem fibrePair_strictMono (i : Fin 3) : StrictMono (fibrePair i) := by
  fin_cases i <;> decide

theorem fibrePair_injective : Function.Injective fibrePair := by decide

/-- The increasing embedding for one of the ordered pairs `01, 02, 12`. -/
def torusPairEmbedding (i : Fin 3) : Fin 2 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono (fibrePair i) (fibrePair_strictMono i)

/-- The unique increasing enumeration of the three basis directions. -/
def torusTripleEmbedding (_i : Fin 1) : Fin 3 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono id strictMono_id

/-- The two-element subset corresponding to an ordered pair. -/
def torusPairSubset (i : Fin 3) : Set.powersetCard (Fin 3) 2 :=
  Set.powersetCard.ofFinEmbEquiv (torusPairEmbedding i)

/-- The three-element subset corresponding to the single ordered triple. -/
def torusTripleSubset (i : Fin 1) : Set.powersetCard (Fin 3) 3 :=
  Set.powersetCard.ofFinEmbEquiv (torusTripleEmbedding i)

@[simp] theorem torusPairSubset_ordered (i : Fin 3) :
    (Set.powersetCard.ofFinEmbEquiv.symm (torusPairSubset i) : Fin 2 → Fin 3) =
      fibrePair i := by
  rw [torusPairSubset, Equiv.symm_apply_apply]
  rfl

@[simp] theorem torusTripleSubset_ordered (i : Fin 1) :
    (Set.powersetCard.ofFinEmbEquiv.symm (torusTripleSubset i) : Fin 3 → Fin 3) =
      id := by
  rw [torusTripleSubset, Equiv.symm_apply_apply]
  rfl

theorem torusPairSubset_injective : Function.Injective torusPairSubset := by
  intro i j hij
  apply fibrePair_injective
  simpa only [torusPairSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 2 → Fin 3)) hij

theorem torusTripleSubset_injective : Function.Injective torusTripleSubset := by
  intro i j _
  exact Subsingleton.elim i j

theorem torusPairSubset_bijective : Function.Bijective torusPairSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨torusPairSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin,
    show Nat.choose 3 2 = 3 by decide] using (Set.powersetCard.card (Fin 3) 2).symm

theorem torusTripleSubset_bijective : Function.Bijective torusTripleSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨torusTripleSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin,
    show Nat.choose 3 3 = 1 by decide] using (Set.powersetCard.card (Fin 3) 3).symm

/-- The complete ordered enumeration of two-element subsets of the three directions. -/
def torusPairSubsetEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 :=
  Equiv.ofBijective torusPairSubset torusPairSubset_bijective

/-- The enumeration of the single three-element subset. -/
def torusTripleSubsetEquiv : Fin 1 ≃ Set.powersetCard (Fin 3) 3 :=
  Equiv.ofBijective torusTripleSubset torusTripleSubset_bijective

@[simp] theorem torusPairSubsetEquiv_apply (i : Fin 3) :
    torusPairSubsetEquiv i = torusPairSubset i := rfl

@[simp] theorem torusTripleSubsetEquiv_apply (i : Fin 1) :
    torusTripleSubsetEquiv i = torusTripleSubset i := rfl

/-- The actual exterior-square basis ordered as `01, 02, 12`. -/
def torusSquareBasis : Module.Basis (Fin 3) ℤ (torusExterior 2) :=
  (torusExteriorBasis 2).reindex torusPairSubsetEquiv.symm

/-- The actual exterior-cube basis consisting of the ordered triple `012`. -/
def torusCubeBasis : Module.Basis (Fin 1) ℤ (torusExterior 3) :=
  (torusExteriorBasis 3).reindex torusTripleSubsetEquiv.symm

theorem torusSquareBasis_apply (i : Fin 3) :
    torusSquareBasis i = exteriorPower.ιMulti ℤ 2 (torusLatticeBasis ∘ fibrePair i) := by
  rw [torusSquareBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 3)).exteriorPower 2 (torusPairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, torusPairSubset_ordered]
  rfl

theorem torusCubeBasis_apply (i : Fin 1) :
    torusCubeBasis i = exteriorPower.ιMulti ℤ 3 torusLatticeBasis := by
  rw [torusCubeBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 3)).exteriorPower 3 (torusTripleSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, torusTripleSubset_ordered]
  rfl

/-- Coordinates in the actual exterior square, ordered as `01, 02, 12`. -/
def torusSquareCoordinates : torusExterior 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  torusSquareBasis.equivFun

/-- Coordinates in the actual exterior cube, retaining its one-element index type. -/
def torusCubeVectorCoordinates : torusExterior 3 ≃ₗ[ℤ] (Fin 1 → ℤ) :=
  torusCubeBasis.equivFun

/-- The scalar coefficient of the ordered generator `012` of the exterior cube. -/
def torusCubeCoordinates : torusExterior 3 ≃ₗ[ℤ] ℤ :=
  torusCubeVectorCoordinates.trans (LinearEquiv.piUnique ℤ (fun _ : Fin 1 => ℤ))

@[simp] theorem torusSquareCoordinates_apply (x : torusExterior 2) (i : Fin 3) :
    torusSquareCoordinates x i = torusSquareBasis.repr x i :=
  congrFun (torusSquareBasis.equivFun_apply x) i

@[simp] theorem torusCubeVectorCoordinates_apply (x : torusExterior 3) (i : Fin 1) :
    torusCubeVectorCoordinates x i = torusCubeBasis.repr x i :=
  congrFun (torusCubeBasis.equivFun_apply x) i

@[simp] theorem torusCubeCoordinates_apply (x : torusExterior 3) :
    torusCubeCoordinates x = torusCubeBasis.repr x 0 :=
  congrFun (torusCubeBasis.equivFun_apply x) 0

@[simp] theorem torusSquareCoordinates_basis (i : Fin 3) :
    torusSquareCoordinates (torusSquareBasis i) = Pi.single i 1 := by
  ext j
  simp only [torusSquareCoordinates_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]

@[simp] theorem torusCubeVectorCoordinates_basis (i : Fin 1) :
    torusCubeVectorCoordinates (torusCubeBasis i) = Pi.single i 1 := by
  ext j
  simp only [torusCubeVectorCoordinates_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single]

@[simp] theorem torusCubeCoordinates_basis (i : Fin 1) :
    torusCubeCoordinates (torusCubeBasis i) = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi, torusCubeCoordinates_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

instance torusExteriorFree (n : ℕ) : Module.Free ℤ (torusExterior n) := inferInstance

instance torusExteriorFinite (n : ℕ) : Module.Finite ℤ (torusExterior n) := inferInstance

theorem torusExterior_finrank (n : ℕ) :
    Module.finrank ℤ (torusExterior n) = Nat.choose 3 n := by
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis torusLatticeBasis,
    Fintype.card_fin]

theorem torusSquare_finrank : Module.finrank ℤ (torusExterior 2) = 3 := by
  rw [torusExterior_finrank]
  decide

theorem torusCube_finrank : Module.finrank ℤ (torusExterior 3) = 1 := by
  rw [torusExterior_finrank]
  decide

end Wikipedia.HopfProblem.Elliptic.HigherHomology
