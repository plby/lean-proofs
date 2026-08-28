import Wikipedia.NoExoticSixSphere.SubcomplexRelativeChains
import Wikipedia.NoExoticSixSphere.CokernelBiproduct
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exactness of the native relative subcomplex sequence

The actual relative difference-and-sum sequence is identified with the
proved cokernel row. The middle identification is the native biproduct
cokernel isomorphism. All three comparison maps retain the original
quotient projections, so exactness concerns the specified relative maps.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SubcomplexRelative

open SimplicialCoefficients

variable (R : ModuleCat.{0} ℤ) {X : SSet.{0}} (A B : X.Subcomplex)

abbrev cokernelRow := cokernel (inclusionSequenceMap R A B)

def firstComparison : complex R (A ⊓ B) ⟶ (cokernelRow R A B).X₁ :=
  cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₁

def diagonalComparison :
    cokernel (biprod.map ((chains R).map A.ι) ((chains R).map B.ι)) ⟶ (cokernelRow R A B).X₂ :=
  cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₂

def middleComparison : complex R A ⊞ complex R B ⟶ (cokernelRow R A B).X₂ :=
  (CokernelBiproduct.iso ((chains R).map A.ι) ((chains R).map B.ι)).inv ≫
    diagonalComparison R A B

def lastComparison : complex R (A ⊔ B) ⟶ (cokernelRow R A B).X₃ :=
  cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₃

def rowProjection₁ : X.chainComplex R ⟶ (cokernelRow R A B).X₁ :=
  (cokernel.π (inclusionSequenceMap R A B)).τ₁

def rowProjection₂ : X.chainComplex R ⊞ X.chainComplex R ⟶ (cokernelRow R A B).X₂ :=
  (cokernel.π (inclusionSequenceMap R A B)).τ₂

def rowProjection₃ : X.chainComplex R ⟶ (cokernelRow R A B).X₃ :=
  (cokernel.π (inclusionSequenceMap R A B)).τ₃

theorem projection_firstComparison :
    projection R (A ⊓ B) ≫ firstComparison R A B = rowProjection₁ R A B :=
  π_comp_cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₁

theorem projection_diagonalComparison :
    cokernel.π (biprod.map ((chains R).map A.ι) ((chains R).map B.ι)) ≫
        diagonalComparison R A B = rowProjection₂ R A B :=
  π_comp_cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₂

theorem projection_middleComparison :
    middleProjection R A B ≫ middleComparison R A B = rowProjection₂ R A B := by
  change CokernelBiproduct.projection ((chains R).map A.ι) ((chains R).map B.ι) ≫
    ((CokernelBiproduct.iso ((chains R).map A.ι) ((chains R).map B.ι)).inv ≫
      diagonalComparison R A B) = _
  rw [← CokernelBiproduct.projection_iso, Category.assoc, Iso.hom_inv_id_assoc,
    projection_diagonalComparison]

theorem projection_lastComparison :
    projection R (A ⊔ B) ≫ lastComparison R A B = rowProjection₃ R A B :=
  π_comp_cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₃

theorem rowProjection_comm₁₂ :
    rowProjection₁ R A B ≫ (cokernelRow R A B).f =
      (ambientSequence R X).f ≫ rowProjection₂ R A B :=
  (cokernel.π (inclusionSequenceMap R A B)).comm₁₂

theorem rowProjection_comm₂₃ :
    rowProjection₂ R A B ≫ (cokernelRow R A B).g =
      (ambientSequence R X).g ≫ rowProjection₃ R A B :=
  (cokernel.π (inclusionSequenceMap R A B)).comm₂₃

/-- The comparison of sequences commutes on the original relative quotient maps. -/
def sequenceComparison : sequence R A B ⟶ cokernelRow R A B where
  τ₁ := firstComparison R A B
  τ₂ := middleComparison R A B
  τ₃ := lastComparison R A B
  comm₁₂ := by
    apply (cancel_epi (projection R (A ⊓ B))).mp
    rw [← Category.assoc, projection_firstComparison, rowProjection_comm₁₂,
      ← Category.assoc, projection_sequence_f, Category.assoc, projection_middleComparison]
  comm₂₃ := by
    apply (cancel_epi (middleProjection R A B)).mp
    rw [← Category.assoc, projection_middleComparison, rowProjection_comm₂₃,
      ← Category.assoc, projection_sequence_g, Category.assoc, projection_lastComparison]

instance sequenceComparison_isIso : IsIso (sequenceComparison R A B) := by
  apply (ShortComplex.isIso_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₁))
  · have : IsIso (diagonalComparison R A B) :=
      inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₂))
    change IsIso ((CokernelBiproduct.iso ((chains R).map A.ι) ((chains R).map B.ι)).inv ≫
      diagonalComparison R A B)
    infer_instance
  · exact inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap R A B) ShortComplex.π₃))

/-- The actual relative subcomplex Mayer–Vietoris chain sequence is short exact. -/
theorem sequence_shortExact : (sequence R A B).ShortExact :=
  ShortComplex.shortExact_of_iso (asIso (sequenceComparison R A B)).symm
    (inclusionCokernel_shortExact R A B)

end NoExoticSixSphere.SubcomplexRelative
