import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyCharts
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Singular Mayer--Vietoris for the actual regular period family

The constructed inverse images of the two slit domains are an actual open
cover of the regular family. Applying the proved singular-chain
Mayer--Vietoris theorem gives its genuine all-degree exact sequence and
the resulting cokernel-to-kernel short exact sequence. The middle object
throughout is the actual singular homology of the descended family.

This file precedes the explicit torus-coordinate normalization of the
outer maps; no such normalization is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris TrianglePeriodFamilyHomologyAlgebra
open CategoryTheory

variable (D : Data ℂ TriangleRegularPoint)

/-- The genuine signed intersection-inclusion homology map for the slit cover. -/
abbrev familyLeftHomologyMap (n : ℕ) :=
  leftHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n

/-- The genuine sum of inclusion maps from the cover members into the regular family. -/
abbrev familyRightHomologyMap (n : ℕ) :=
  rightHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n

/-- The actual singular Mayer--Vietoris connecting homomorphism of the regular family. -/
def familyConnectingHomomorphism (n : ℕ) :
    SingularHomology D.Space (n + 1) →ₗ[ℤ]
      SingularHomology ((upperFamily D : Set D.Space) ∩ lowerFamily D : Set D.Space) n :=
  connectingHomomorphism (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n

/-- Exactness at the pair of actual cover homology groups. -/
theorem family_exact_at_pair (n : ℕ) :
    Function.Exact (familyLeftHomologyMap D n) (familyRightHomologyMap D n) := by
  apply LinearMap.exact_iff.mpr
  exact (exact_at_pair (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

/-- Exactness at the actual positive-degree family homology. -/
theorem family_exact_at_ambient (n : ℕ) :
    Function.Exact (familyRightHomologyMap D (n + 1))
      (familyConnectingHomomorphism D n) := by
  apply LinearMap.exact_iff.mpr
  exact (exact_at_ambient (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

/-- Exactness at the actual overlap homology. -/
theorem family_exact_at_intersection (n : ℕ) :
    Function.Exact (familyConnectingHomomorphism D n) (familyLeftHomologyMap D n) := by
  apply LinearMap.exact_iff.mpr
  exact (exact_at_intersection (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

/-- The degree-zero endpoint is surjective for the genuine family cover. -/
theorem familyRightHomologyMap_zero_surjective :
    Function.Surjective (familyRightHomologyMap D 0) :=
  rightHomologyMap_zero_surjective (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D)

/-- The actual cokernel-to-kernel short complex obtained from the family open cover. -/
def familyRawExtension (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  cokernelKernelShortComplex
    (familyLeftHomologyMap D (n + 1)) (familyRightHomologyMap D (n + 1))
    (familyConnectingHomomorphism D n) (familyLeftHomologyMap D n)
    (family_exact_at_pair D (n + 1)) (family_exact_at_ambient D n)
    (family_exact_at_intersection D n)

/-- Its middle object is the actual singular homology of the constructed regular family. -/
@[simp] theorem familyRawExtension_middle (n : ℕ) :
    (familyRawExtension D n).X₂ = SingularHomology D.Space (n + 1) := rfl

/-- The actual family homology is an extension of the actual overlap kernel
by the actual preceding overlap cokernel, in every positive degree. -/
theorem familyRawExtension_shortExact (n : ℕ) : (familyRawExtension D n).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (familyLeftHomologyMap D (n + 1)) (familyRightHomologyMap D (n + 1))
    (familyConnectingHomomorphism D n) (familyLeftHomologyMap D n)
    (family_exact_at_pair D (n + 1)) (family_exact_at_ambient D n)
    (family_exact_at_intersection D n)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
