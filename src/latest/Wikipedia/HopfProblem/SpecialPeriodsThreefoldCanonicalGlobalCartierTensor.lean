import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartier
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# Products of actual Cartier presentations

The product of the local fractions defines the tensor product of the
two actual line bundles on the intersection cover.  Its generic open is
the intersection of the original dense opens.  The constructed section
is identified through the full fibre tensor-product equivalence, not
merely through a product of formal divisor names.
-/

noncomputable section

open Set Topology
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobal.CartierData

variable {E H M ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℂ E H} (A : CartierData I M ι) (B : CartierData I M κ)

/-- Multiplication of actual meromorphic fractions on the paired cover. -/
def tensor : CartierData I M (ι × κ) where
  transitions := CanonicalGlobalLineBundle.tensor A.transitions B.transitions
  isHolomorphic := inferInstance
  numerator i x := A.numerator i.1 x * B.numerator i.2 x
  denominator i x := A.denominator i.1 x * B.denominator i.2 x
  numerator_holomorphic i :=
    ((A.numerator_holomorphic i.1).mono inter_subset_left).mul
      ((B.numerator_holomorphic i.2).mono inter_subset_right)
  denominator_holomorphic i :=
    ((A.denominator_holomorphic i.1).mono inter_subset_left).mul
      ((B.denominator_holomorphic i.2).mono inter_subset_right)
  genericSet := A.genericSet ⊓ B.genericSet
  genericSet_dense := A.genericSet_dense.inter_of_isOpen_right B.genericSet_dense
    B.genericSet.isOpen
  numerator_ne_zero i x hi hx :=
    mul_ne_zero (A.numerator_ne_zero i.1 x hi.1 hx.1)
      (B.numerator_ne_zero i.2 x hi.2 hx.2)
  denominator_ne_zero i x hi hx :=
    mul_ne_zero (A.denominator_ne_zero i.1 x hi.1 hx.1)
      (B.denominator_ne_zero i.2 x hi.2 hx.2)
  ratio i j x hx := by
    have hA := A.ratio i.1 j.1 x ⟨hx.1.1, hx.2.1⟩
    have hB := B.ratio i.2 j.2 x ⟨hx.1.2, hx.2.2⟩
    change (A.numerator j.1 x * B.numerator j.2 x) *
        (A.denominator i.1 x * B.denominator i.2 x) =
      ((A.transitions.transition i.1 j.1 x : ℂ) *
        (B.transitions.transition i.2 j.2 x : ℂ)) *
        (A.numerator i.1 x * B.numerator i.2 x) *
        (A.denominator j.1 x * B.denominator j.2 x)
    calc
      _ = (A.numerator j.1 x * A.denominator i.1 x) *
          (B.numerator j.2 x * B.denominator i.2 x) := by ac_rfl
      _ = ((A.transitions.transition i.1 j.1 x : ℂ) * A.numerator i.1 x *
            A.denominator j.1 x) *
          ((B.transitions.transition i.2 j.2 x : ℂ) * B.numerator i.2 x *
            B.denominator j.2 x) := by rw [hA, hB]
      _ = _ := by ac_rfl

@[simp] theorem tensor_transitions :
    (A.tensor B).transitions = CanonicalGlobalLineBundle.tensor A.transitions B.transitions := rfl

@[simp] theorem tensor_genericSet : (A.tensor B).genericSet = A.genericSet ⊓ B.genericSet := rfl

@[simp] theorem tensor_numerator (i : ι × κ) (x : M) :
    (A.tensor B).numerator i x = A.numerator i.1 x * B.numerator i.2 x := rfl

@[simp] theorem tensor_denominator (i : ι × κ) (x : M) :
    (A.tensor B).denominator i x = A.denominator i.1 x * B.denominator i.2 x := rfl

theorem tensor_localFraction (i : ι × κ) (x : M) :
    (A.tensor B).localFraction i x = A.localFraction i.1 x * B.localFraction i.2 x := by
  change (A.numerator i.1 x * B.numerator i.2 x) /
      (A.denominator i.1 x * B.denominator i.2 x) =
    (A.numerator i.1 x / A.denominator i.1 x) *
      (B.numerator i.2 x / B.denominator i.2 x)
  exact (div_mul_div_comm _ _ _ _).symm

/-- The associated native fibre is the full tensor product of the
two associated original fibres. -/
def tensorFiberEquiv (x : M) :
    A.associatedBundle.Fiber x ⊗[ℂ] B.associatedBundle.Fiber x ≃ₗ[ℂ]
      (A.tensor B).associatedBundle.Fiber x :=
  CanonicalGlobalLineBundle.fibreTensorEquiv A.transitions B.transitions x

/-- The chosen meromorphic section is the actual tensor of the two
original sections under the genuine fibre tensor equivalence. -/
theorem tensor_rawSection (x : M) :
    (A.tensor B).rawSection x =
      A.tensorFiberEquiv B x (A.rawSection x ⊗ₜ[ℂ] B.rawSection x) := by
  change (A.tensor B).localFraction (A.transitions.indexAt x, B.transitions.indexAt x) x = _
  rw [tensor_localFraction]
  exact (CanonicalGlobalLineBundle.fibreTensorEquiv_tmul A.transitions B.transitions x
    (A.rawSection x) (B.rawSection x)).symm

end Wikipedia.HopfProblem.CanonicalGlobal.CartierData
