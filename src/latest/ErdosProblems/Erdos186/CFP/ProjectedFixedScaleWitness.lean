/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationAssembly
import ErdosProblems.Erdos186.CFP.Corollary217MapBack

/-!
# Generic projection of a fixed-scale CFP witness

The projected-properization theorem is not special to Appendix
dehomogenization.  This wrapper exposes its generic form: projection may
collapse the ambient progression, but if it is injective on the original
finite set then Lemma 2.27 reconstructs a proper lower-rank witness at a
dimension-only denominator loss.
-/

namespace Erdos186.CFP.ProjectedProperization

noncomputable section

/-- Project a fixed-scale witness through an additive homomorphism, using
the genuine properization theorem rather than requiring injectivity on a
large dilate of its progression. -/
theorem exists_projectedFixedScaleWitness
    {d e s D k loss scaleNum scaleDen : ℕ}
    {H : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : FixedScaleWitness H s D k loss scaleNum scaleDen)
    (hinjective : Set.InjOn f H)
    (hk : projectionFactor D ≤ k) :
    ∃ k' : ℕ, Nonempty (FixedScaleWitness (H.image f) s D k' loss
      scaleNum (scaleDen * projectionFactor D)) := by
  obtain ⟨Z⟩ := exists_data_of_projectionFactor_le f W.enhanced hk
  exact ⟨Z.scale, ⟨Z.transportFixed W hinjective
    (projectionFactor_pos D)⟩⟩

/-- The source-line evaluation is injective on centered coordinates of the
original source set.  Properness is only used for the base identification;
no injectivity on a dilated progression is needed. -/
theorem sourceLineEvaluation_injOn_image_centeredIdentification
    {W B : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP W d)
    (hproper : P.progression.Proper) (hzero : 0 ∈ W)
    (hBW : B ⊆ W) :
    Set.InjOn (sourceLineEvaluation P.progression)
      (B.image (Preprocessing.centeredIdentification P hproper hzero)) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : Stability.integerPoint a = Stability.integerPoint b := by
    simpa only [sourceLineEvaluation_centeredIdentification P hproper hzero
      (hBW ha), sourceLineEvaluation_centeredIdentification P hproper hzero
      (hBW hb)] using hxy
  have hab' : a = b := Stability.integerPoint_injective hab
  subst b
  rfl

/-- Evaluating the centered coordinate copy recovers exactly the canonical
one-dimensional lattice copy of the source set. -/
theorem image_sourceLineEvaluation_image_centeredIdentification
    {W B : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP W d)
    (hproper : P.progression.Proper) (hzero : 0 ∈ W)
    (hBW : B ⊆ W) :
    (B.image (Preprocessing.centeredIdentification P hproper hzero)).image
        (sourceLineEvaluation P.progression) =
      Stability.integerPoints B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    rw [sourceLineEvaluation_centeredIdentification P hproper hzero
      (hBW hz)]
    exact Stability.integerPoint_mem_integerPoints_iff.mpr hz
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
    apply Finset.mem_image.mpr
    refine ⟨Preprocessing.centeredIdentification P hproper hzero z,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    exact sourceLineEvaluation_centeredIdentification P hproper hzero
      (hBW hz)

end

end Erdos186.CFP.ProjectedProperization

#print axioms
  Erdos186.CFP.ProjectedProperization.exists_projectedFixedScaleWitness
#print axioms
  Erdos186.CFP.ProjectedProperization.sourceLineEvaluation_injOn_image_centeredIdentification
#print axioms
  Erdos186.CFP.ProjectedProperization.image_sourceLineEvaluation_image_centeredIdentification
