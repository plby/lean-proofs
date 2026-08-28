import Wikipedia.HopfProblem.ThreefoldHomologyGluingInitial
import Wikipedia.HopfProblem.ThreefoldHomologyGluingTerminal
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact

/-!
# The actual integral homology attachment sequences of the threefold

Every genuine filling attachment has an all-degree singular Mayer–Vietoris
sequence. The initial pair uses the original regular family and the original
filling piece. The terminal ambient term is the actual singular homology
of the constructed global threefold, identified through the proved full
stage homeomorphism.

All inclusion maps are induced by the literal geometric continuous maps.
The two components of the overlap map have signs positive and negative;
the incoming map is the sum of the two actual inclusions. The connecting
maps come from the actual singular small-chain exact sequence. The
cokernel-to-kernel short complexes below retain those same maps on
representatives, without assuming any integer-matrix evaluations or
abstract descriptions of the global homology groups.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris TrianglePeriodFamilyHomologyAlgebra

/-- The actual positive-degree attachment homology is the middle term
of the short complex induced by its genuine singular exact sequence. -/
def attachmentExtension (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    ShortComplex (ModuleCat.{0} ℤ) :=
  cokernelKernelShortComplex
    (originalAttachmentLeftHomologyMap s i (n + 1))
    (originalAttachmentRightHomologyMap s i (n + 1))
    (attachmentConnectingHomomorphism s i hi n)
    (originalAttachmentLeftHomologyMap s i n)
    (originalAttachment_exact_at_pair s i hi (n + 1))
    (originalAttachment_exact_at_ambient s i hi n)
    (originalAttachment_exact_at_intersection s i hi n)

@[simp] theorem attachmentExtension_middle
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    (attachmentExtension s i hi n).X₂ = StageHomology (insert i s) (n + 1) := rfl

theorem attachmentExtension_shortExact
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    (attachmentExtension s i hi n).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (originalAttachmentLeftHomologyMap s i (n + 1))
    (originalAttachmentRightHomologyMap s i (n + 1))
    (attachmentConnectingHomomorphism s i hi n)
    (originalAttachmentLeftHomologyMap s i n)
    (originalAttachment_exact_at_pair s i hi (n + 1))
    (originalAttachment_exact_at_ambient s i hi n)
    (originalAttachment_exact_at_intersection s i hi n)

/-- The terminal cokernel-to-kernel short complex has the actual global
integral singular homology as its middle object, in every positive degree. -/
def terminalExtension (i : Puncture) (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  cokernelKernelShortComplex
    (terminalLeftHomologyMap i (n + 1)) (terminalRightHomologyMap i (n + 1))
    (terminalConnectingHomomorphism i n) (terminalLeftHomologyMap i n)
    (terminal_exact_at_pair i (n + 1)) (terminal_exact_at_ambient i n)
    (terminal_exact_at_intersection i n)

@[simp] theorem terminalExtension_middle (i : Puncture) (n : ℕ) :
    (terminalExtension i n).X₂ = SingularHomology Space (n + 1) := rfl

/-- This short exact sequence is derived from the actual global
threefold cover, without assuming the values or matrices of its homology. -/
theorem terminalExtension_shortExact (i : Puncture) (n : ℕ) :
    (terminalExtension i n).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (terminalLeftHomologyMap i (n + 1)) (terminalRightHomologyMap i (n + 1))
    (terminalConnectingHomomorphism i n) (terminalLeftHomologyMap i n)
    (terminal_exact_at_pair i (n + 1)) (terminal_exact_at_ambient i n)
    (terminal_exact_at_intersection i n)

/-- On quotient representatives, the first short-exact map is exactly
the actual incoming singular-homology map. -/
@[simp] theorem terminalExtension_left_mk (i : Puncture) (n : ℕ)
    (a : StageHomology (Finset.univ.erase i) (n + 1) × OriginalFillingHomology i (n + 1)) :
    (terminalExtension i n).f.hom
        ((LinearMap.range (terminalLeftHomologyMap i (n + 1))).mkQ a) =
      terminalRightHomologyMap i (n + 1) a := rfl

/-- Forgetting the following kernel subtype recovers the actual
Mayer–Vietoris connecting homomorphism on every global class. -/
@[simp] theorem terminalExtension_right_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology Space (n + 1)) :
    (LinearMap.ker (terminalLeftHomologyMap i n)).subtype
      ((terminalExtension i n).g.hom a) =
      terminalConnectingHomomorphism i n a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
