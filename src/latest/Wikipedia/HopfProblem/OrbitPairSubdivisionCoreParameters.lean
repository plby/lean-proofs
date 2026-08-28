import Wikipedia.HopfProblem.OrbitPairSubdivisionRelations
import Wikipedia.HopfProblem.OrbitPairRealizationNondegenerateCore

/-!
# Removing degeneracy from subdivision cell parameters

This is the algebraic part of carrier normalization. It applies to an
arbitrary cosimplicial simplicial set. The existing unique nondegenerate
core determines the new cell, and the cosimplicial map transports its
parameter. No geometric realization comparison is used.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

variable (A : SimplexCategory ⥤ SSet.{u}) (X : SSet.{u}) (k : ℕ)

def coreDataParameters {n : ℕ} {x : X _⦋n⦌}
    (a : RealizationSimplex.Core X n x) (t : (A.obj ⦋n⦌) _⦋k⦌) : Parameters A X k :=
  ⟨⟨a.dim, a.simplex.val⟩, (A.map a.collapse).app (Opposite.op ⦋k⦌) t⟩

def coreParameters (n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌) :
    Parameters A X k :=
  coreDataParameters A X k (RealizationSimplex.core X n x) t

theorem coreParameters_eq (n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌)
    (a : RealizationSimplex.Core X n x) :
    coreParameters A X k n x t = coreDataParameters A X k a t := by
  unfold coreParameters
  rw [RealizationSimplex.core_eq X (RealizationSimplex.core X n x) a]

theorem coreParameters_nonDegenerate (n : ℕ) (x : X.nonDegenerate n)
    (t : (A.obj ⦋n⦌) _⦋k⦌) : coreParameters A X k n x.val t = ⟨⟨n, x.val⟩, t⟩ := by
  rw [coreParameters_eq A X k n x.val t (RealizationSimplex.fullCore X n x)]
  change (⟨⟨n, x.val⟩, (A.map (𝟙 ⦋n⦌)).app (Opposite.op ⦋k⦌) t⟩ : Parameters A X k) = _
  have h : (A.map (𝟙 ⦋n⦌)).app (Opposite.op ⦋k⦌) t = t :=
    congrArg (fun f : A.obj ⦋n⦌ ⟶ A.obj ⦋n⦌ ↦ f.app (Opposite.op ⦋k⦌) t) (A.map_id ⦋n⦌)
  exact congrArg (fun v ↦ (⟨⟨n, x.val⟩, v⟩ : Parameters A X k)) h

theorem coreParameters_epi {m n : ℕ} (e : ⦋m⦌ ⟶ ⦋n⦌) [Epi e]
    (x : X _⦋n⦌) (t : (A.obj ⦋m⦌) _⦋k⦌) :
    coreParameters A X k m (X.map e.op x) t =
      coreParameters A X k n x ((A.map e).app (Opposite.op ⦋k⦌) t) := by
  rw [coreParameters_eq A X k m (X.map e.op x) t
    (RealizationSimplex.pullbackCore X e x (RealizationSimplex.core X n x))]
  change (⟨⟨(RealizationSimplex.core X n x).dim, (RealizationSimplex.core X n x).simplex.val⟩,
    (A.map (e ≫ (RealizationSimplex.core X n x).collapse)).app (Opposite.op ⦋k⦌) t⟩ :
      Parameters A X k) = _
  rw [Functor.map_comp]
  rfl

theorem coreParameters_glue (n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌) :
    Glue A X k ⟨⟨n, x⟩, t⟩ (coreParameters A X k n x t) := by
  let a := RealizationSimplex.core X n x
  have h := Glue.of_map (A := A) (X := X) (k := k) n a.dim a.collapse a.simplex.val t
  have hx : X.map a.collapse.op a.simplex.val = x := a.decomposes.symm
  rw [hx] at h
  exact h

theorem coreParameters_projection (L : SSet.{u} ⥤ SSet.{u}) (α : A ⟶ SSet.stdSimplex ⋙ L)
    (n : ℕ) (x : X _⦋n⦌) (t : (A.obj ⦋n⦌) _⦋k⦌) :
    projection A L α X k (coreParameters A X k n x t) =
      projection A L α X k ⟨⟨n, x⟩, t⟩ :=
  (glue_projection_eq A L α X k (coreParameters_glue A X k n x t)).symm

theorem coreParameters_isNonDegenerate (n : ℕ) (x : X _⦋n⦌)
    (t : (A.obj ⦋n⦌) _⦋k⦌) :
    (coreParameters A X k n x t).1.2 ∈ X.nonDegenerate (coreParameters A X k n x t).1.1 :=
  (RealizationSimplex.core X n x).simplex.property

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters
