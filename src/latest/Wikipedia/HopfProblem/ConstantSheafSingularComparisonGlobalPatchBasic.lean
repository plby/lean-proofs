import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonClosedRefinement

/-!
# Patching original cochain values along a closed refinement

A singular cochain imposes no continuity on its simplex values. A closed
refinement therefore selects one local representative at the first vertex;
when the whole simplex lies in that representative's open set, its actual
value is used. Otherwise the value is zero. Every operation below acts on
the original singular chains.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : TopCat.{0}} (A : AddCommGrpCat.{0}) (n : ℕ)

/-- The actual simplex, with codomain restricted to a containing open set. -/
def simplexInOpen (σ : SingularSimplex X n) (U : Opens X) (hσ : range σ ⊆ U) :
    SingularSimplex U n where
  toFun z := ⟨σ z, hσ (mem_range_self z)⟩
  continuous_toFun := σ.continuous.subtype_mk _

@[simp]
theorem simplexInOpen_val (σ : SingularSimplex X n) (U : Opens X)
    (hσ : range σ ⊆ U) (z : Simplex n) :
    (simplexInOpen n σ U hσ z : X) = σ z := rfl

/-- Pulling an actual global cochain back to an actual open subspace. -/
def restrictGlobalCochain (φ : Cochains X A n) (U : Opens X) : Cochains U A n :=
  (singularPullback A (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).f n φ

@[simp]
theorem restrictGlobalCochain_simplex (φ : Cochains X A n) (U : Opens X)
    (σ : SingularSimplex U n) :
    restrictGlobalCochain A n φ U (simplexChain U n σ) =
      φ (simplexChain X n
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp σ)) :=
  singularPullback_simplex A _ n φ σ

/-- Successive actual restrictions are the direct global restriction. -/
theorem restrictGlobalCochain_restrict (φ : Cochains X A n)
    {U V : Opens X} (i : V ⟶ U) :
    (cochainPresheaf X A n).map i.op (restrictGlobalCochain A n φ U) =
      restrictGlobalCochain A n φ V := by
  apply cochain_ext V A n
  intro σ
  let f : C(V, U) := ((Opens.toTopCat X).map i).hom
  exact (cochainPresheaf_map_simplex X A n i (restrictGlobalCochain A n φ U) σ).trans
    ((restrictGlobalCochain_simplex A n φ U (f.comp σ)).trans
      (restrictGlobalCochain_simplex A n φ V σ).symm)

variable {ι : Type} (U : ι → Opens X) (R : ClosedRefinement U)
  (t : ∀ i, Cochains (U i) A n)

/-- The selected original cover index at the actual first simplex vertex. -/
def patchIndex (σ : SingularSimplex X n) : ι :=
  R.index (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))))

/-- The patched value, read from one actual local cochain when possible. -/
def patchedValue (σ : SingularSimplex X n) : A := by
  classical
  exact if h : range σ ⊆ U (patchIndex n U R σ) then
    t (patchIndex n U R σ)
      (simplexChain (U (patchIndex n U R σ)) n
        (simplexInOpen n σ (U (patchIndex n U R σ)) h))
  else 0

/-- The original simplex basis extends the patched values to an actual cochain. -/
def patchedCochain : Cochains X A n :=
  cochainFromValues X A n (patchedValue A n U R t)

@[simp]
theorem patchedCochain_simplex (σ : SingularSimplex X n) :
    patchedCochain A n U R t (simplexChain X n σ) = patchedValue A n U R t σ :=
  cochainFromValues_simplex X A n _ σ

/-- On a simplex contained in its selected actual chart, patching is the
literal value of the selected original representative. -/
theorem patchedCochain_simplex_of_subset (σ : SingularSimplex X n)
    (hσ : range σ ⊆ U (patchIndex n U R σ)) :
    patchedCochain A n U R t (simplexChain X n σ) =
      t (patchIndex n U R σ)
        (simplexChain (U (patchIndex n U R σ)) n
          (simplexInOpen n σ (U (patchIndex n U R σ)) hσ)) := by
  rw [patchedCochain_simplex, patchedValue, dif_pos hσ]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
