/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.RedChordPolarBoundaryIndices
import ErdosProblems.Erdos735.ConcreteRedChordExtraction

/-!
# Red-chord geometry from a concrete polar boundary

This file packages the projective polar endpoint theorem into the interface
consumed by `RedChordExtraction`.  A rotation realization only has to expose
the equivalence between its face indices and the concrete polar boundary,
and show that vertices, successors, and supporting owners agree.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.RedChordExtraction

noncomputable section

open ProjectiveArrangement SignVector
open SignVector.RotationRealization
open SignVector.PolarBoundaryAcross
open RedChordPolarBoundaryIndices

private theorem blue_normal_cross
    {B : Finset Point} (i j : BlueLine B) (hij : i ≠ j) :
    blueNormals B i ⨯₃ blueNormals B j ≠ 0 := by
  apply normalVec_cross_ne_zero
  intro h
  exact hij (Subtype.ext h)

/-- Construct the full reduced red-chord geometry from an owner-preserving
identification of a rotation realization's boundary with the concrete polar
boundary. -/
theorem Geometry.ofPolarBoundaryCompatibility
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    [Nonempty (BlueLine (nonordinaryPoints P))]
    {G : SimpleGraph (BlueVertex (nonordinaryPoints P))}
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (X : RotationRealization (G := G)
      (blueNormals (nonordinaryPoints P))
      (blueNormals_ne_zero (nonordinaryPoints P)))
    (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (blueNormals (nonordinaryPoints P))) = ⊤)
    (indexEquiv : ∀ f : StrictFace (blueNormals (nonordinaryPoints P)),
      Fin (X.strictC.faceDegree f) ≃
        BoundaryIndex (blueNormals (nonordinaryPoints P)) f)
    (indexEquiv_succ : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (i : Fin (X.strictC.faceDegree f)),
      indexEquiv f (X.strictFaceSucc f i) =
        Erdos957.cyclicSucc (indexEquiv f i))
    (boundaryVertex_projective : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (i : Fin (X.strictC.faceDegree f)),
      (X.boundaryVertex f i).1 =
        boundaryVertex (blueNormals (nonordinaryPoints P))
          blue_normal_cross hspan f (indexEquiv f i))
    (boundaryEdge_owner : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (i : Fin (X.strictC.faceDegree f)),
      strictEdgeOwner (X.boundaryEdge f i) =
        (boundaryEdge (blueNormals (nonordinaryPoints P))
          blue_normal_cross hspan f (indexEquiv f i)).1.1) :
    Geometry (A := ordinaryPoints P) (B := nonordinaryPoints P) X :=
  Geometry.ofReducedMagic X hred
    (by
      intro f a ha
      have hrest : RestrictedRealizable
          (blueNormals (nonordinaryPoints P)) (normalVec a.1) f.1 :=
        (mem_redChordLines_iff f a).mp ha
      exact compatibleEndpointIndices_card_of_restricted
        hred a.2 f hspan hrest (indexEquiv f)
          (fun i ↦ (X.boundaryVertex f i).1)
          (boundaryVertex_projective f))
    (by
      intro f i
      rw [boundaryVertex_projective f i, boundaryEdge_owner f i]
      simpa [Incident, blueNormals] using
        boundaryVertex_on_edge_start
          (blueNormals (nonordinaryPoints P)) blue_normal_cross hspan
          f (indexEquiv f i))
    (by
      intro f i
      rw [boundaryVertex_projective f (X.strictFaceSucc f i),
        indexEquiv_succ f i, boundaryEdge_owner f i]
      simpa [Incident, blueNormals] using
        boundaryVertex_on_edge_finish
          (blueNormals (nonordinaryPoints P)) blue_normal_cross hspan
          f (indexEquiv f i))

end

end Erdos735.RedChordExtraction
