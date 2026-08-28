import Wikipedia.HopfProblem.OrbitPairSubdivisionMonomorphisms

/-!
# Simplicial operators on subdivision cell parameters

The simplicial direction acts on a cell's parameter while leaving its
original simplex unchanged. This action commutes with native projection.
In particular, a nondegenerate projected simplex has a nondegenerate cell
parameter. Normalization can only lower the original carrier dimension.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

open SubdivisionColimit SubdivisionSupport

variable (A : SimplexCategory ⥤ SSet.{u}) (X : SSet.{u})

def degreeParameters {l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌) (p : Parameters A X k) :
    Parameters A X l := ⟨p.1, (A.obj ⦋p.1.1⦌).map f.op p.2⟩

theorem degreeParameters_projection (L : SSet.{u} ⥤ SSet.{u})
    (α : A ⟶ SSet.stdSimplex.{u} ⋙ L) {l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (p : Parameters A X k) :
    projection A L α X l (degreeParameters A X f p) =
      (L.obj X).map f.op (projection A L α X k p) := by
  exact congrArg (fun g ↦ g p.2) ((cellMap A L α X p.1.1 p.1.2).naturality f.op)

theorem nonDegenerate_parameter_of_projection (L : SSet.{u} ⥤ SSet.{u})
    (α : A ⟶ SSet.stdSimplex.{u} ⋙ L) {k : ℕ} (p : Parameters A X k)
    (hp : projection A L α X k p ∈ (L.obj X).nonDegenerate k) :
    p.2 ∈ (A.obj ⦋p.1.1⦌).nonDegenerate k := by
  intro ht
  exact hp (SSet.degenerate_app_apply ht (cellMap A L α X p.1.1 p.1.2))

theorem coreParameters_dim_le (k n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌) :
    (coreParameters A X k n x t).1.1 ≤ n :=
  SimplexCategory.len_le_of_epi (RealizationSimplex.core X n x).collapse

theorem normalize_dim_le_face {k : ℕ} (s : Law A k) (faces : ∀ n t, Face s n t)
    (p : Parameters A X k) : (normalize s faces X p).1.1 ≤ (faces p.1.1 p.2).dim :=
  coreParameters_dim_le A X k (faces p.1.1 p.2).dim
    (X.map (faces p.1.1 p.2).inclusion.op p.1.2) (faces p.1.1 p.2).point

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters
