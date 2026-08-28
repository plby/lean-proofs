import Wikipedia.HopfProblem.OrbitPairSubdivisionSubcomplexes
import Wikipedia.HopfProblem.OrbitPairRealizationSubcomplexEmbedding
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Actual closed attachments after subdivision and realization

Realization sends every simplicial monomorphism to a closed embedding.
The actual subdivided object of a subcomplex is identified with the
range of its subdivided inclusion. Union and skeletal attachment squares
are carried to genuine topological pushouts. When the target is finite,
the native relative-cell index and its boundary/standard-simplex
coproducts are finite.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial Topology

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

theorem realizedMono_isClosedEmbedding {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    IsClosedEmbedding (SSet.toTop.map f) := by
  let e := SSet.toTop.mapIso (asIso (SSet.Subcomplex.toRange f))
  have hc := (isClosedEmbedding_realizedSubcomplex (SSet.Subcomplex.range f)).comp
    (TopCat.homeoOfIso e).isClosedEmbedding
  have he : SSet.toTop.map (SSet.Subcomplex.toRange f) ≫
      SSet.toTop.map (SSet.Subcomplex.range f).ι = SSet.toTop.map f := by
    rw [← SSet.toTop.map_comp, SSet.Subcomplex.toRange_ι]
  have he' : (fun x ↦ (SSet.toTop.map (SSet.Subcomplex.range f).ι)
      ((SSet.toTop.map (SSet.Subcomplex.toRange f)) x)) = (SSet.toTop.map f) :=
    funext (fun x ↦ congrArg (fun g ↦ g x) he)
  exact he' ▸ hc

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex

variable (L : SSet.{u} ⥤ SSet.{u}) [L.PreservesMonomorphisms] {X : SSet.{u}}

def imageIso (A : X.Subcomplex) : L.obj (A : SSet) ≅ (image L A : SSet) := by
  change L.obj (A : SSet) ≅ (SSet.Subcomplex.range (L.map A.ι) : SSet)
  let : Mono (L.map A.ι) := inferInstance
  exact asIso (SSet.Subcomplex.toRange (L.map A.ι))

theorem imageIso_inclusion (A : X.Subcomplex) :
    (imageIso L A).hom ≫ (image L A).ι = L.map A.ι :=
  SSet.Subcomplex.toRange_ι (L.map A.ι)

def realizedImageIso (A : X.Subcomplex) :
    SSet.toTop.obj (L.obj (A : SSet)) ≃ₜ SSet.toTop.obj (image L A : SSet) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (imageIso L A))

theorem realized_inclusion_isClosedEmbedding (A : X.Subcomplex) :
    IsClosedEmbedding (SSet.toTop.map (L.map A.ι)) :=
  RealizationSimplex.realizedMono_isClosedEmbedding (L.map A.ι)

variable [PreservesColimitsOfShape WalkingSpan L]

omit [L.PreservesMonomorphisms] in
theorem realized_union_isPushout (A B : X.Subcomplex) :
    IsPushout (SSet.toTop.map (L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))))
      (SSet.toTop.map (L.map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))))
      (SSet.toTop.map (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))))
      (SSet.toTop.map (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)))) :=
  (union_isPushout L A B).map SSet.toTop

end Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open SSet.relativeCellComplexOfMono

variable {X Y : SSet.{u}} (i : X ⟶ Y)

instance relative_cells_finite [Y.Finite] (d : ℕ) : Finite (Cell i d) :=
  Finite.of_injective (fun c : Cell i d ↦ (⟨c.simplex, c.nonDegenerate⟩ : Y.nonDegenerate d))
    (by intro a b h; ext; exact congrArg Subtype.val h)

instance relative_standard_finite [Y.Finite] (d : ℕ) : (sigmaStdSimplex i d).Finite := by
  infer_instance

instance relative_boundary_finite [Y.Finite] (d : ℕ) : (sigmaBoundary i d).Finite := by
  infer_instance

theorem realized_skeletal_isPushout (L : SSet.{u} ⥤ SSet.{u})
    [PreservesColimitsOfShape WalkingSpan L] (d : ℕ) :
    IsPushout (SSet.toTop.map (L.map (t i d))) (SSet.toTop.map (L.map (l i d)))
      (SSet.toTop.map (L.map (r i d))) (SSet.toTop.map (L.map (b i d))) :=
  ((SSet.relativeCellComplexOfMono.isPushout i d).map L).map SSet.toTop

theorem sd_realized_skeletal_isPushout (d : ℕ) :
    IsPushout (SSet.toTop.map (SSet.sd.map (t i d))) (SSet.toTop.map (SSet.sd.map (l i d)))
      (SSet.toTop.map (SSet.sd.map (r i d))) (SSet.toTop.map (SSet.sd.map (b i d))) :=
  realized_skeletal_isPushout i SSet.sd d

theorem dual_realized_skeletal_isPushout (d : ℕ) :
    IsPushout (SSet.toTop.map (dualSd.map (t i d))) (SSet.toTop.map (dualSd.map (l i d)))
      (SSet.toTop.map (dualSd.map (r i d))) (SSet.toTop.map (dualSd.map (b i d))) :=
  realized_skeletal_isPushout i dualSd d

end Wikipedia.HopfProblem.OrbitPair.Subdivision
