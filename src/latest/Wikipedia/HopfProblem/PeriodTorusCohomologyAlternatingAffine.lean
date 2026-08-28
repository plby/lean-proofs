import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingPullback
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingAffineHomology
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDeckFixed

/-!
# Native alternating classes under the actual elliptic deck action

The actual affine generator is homotopic to its actual linear part.
Its proved integral homology marking therefore gives the native
cohomological pullback, including every integral twist.  For admissible
twists the all-deck invariant condition is exactly preservation of the
original alternating form by the actual lattice matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open Elliptic Elliptic.HigherHomology

/-- Every actual affine elliptic generator pulls back the native class by its verified matrix. -/
theorem alternatingClass_pullback_affineBiholomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2
        (alternatingClass p.val B) =
      alternatingClass p.val (B.compLinearMap j.matrix.mulVecLin) :=
  alternatingClass_pullback_of_exterior p.val p.val
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus))
    j.matrix.mulVecLin (periodTorusH2ExteriorEquiv_affineBiholomorph j p v) B

/-- The actual affine pullback in alternating-form coordinates, for every native class. -/
theorem cohomologyAlternatingEquiv_pullback_affineBiholomorph
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (a : SingularCohomology p.val.Torus 2) :
    cohomologyAlternatingEquiv p.val (singularCohomologyPullback
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2 a) =
      (cohomologyAlternatingEquiv p.val a).compLinearMap j.matrix.mulVecLin :=
  cohomologyAlternatingEquiv_pullback_of_exterior p.val p.val
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus))
    j.matrix.mulVecLin (periodTorusH2ExteriorEquiv_affineBiholomorph j p v) a

/-- The source's six-coefficient native classes retain their exact affine pullback rule. -/
theorem coefficientClass_pullback_affineBiholomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (E : Fin 6 → ℤ) :
    singularCohomologyPullback
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2
        (coefficientClass p.val E) =
      coefficientClass p.val (coefficientPullback j.matrix.mulVecLin E) :=
  coefficientClass_pullback_of_exterior p.val p.val
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus))
    j.matrix.mulVecLin (periodTorusH2ExteriorEquiv_affineBiholomorph j p v) E

/-- The genuine all-deck condition is equivalent to invariance of the actual alternating map. -/
theorem alternatingClass_mem_deckInvariants_iff (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    alternatingClass p.val B ∈ periodCohomologyInvariants j p v hv 2 ↔
      B.compLinearMap j.matrix.mulVecLin = B := by
  rw [mem_periodCohomologyInvariants_iff_affine]
  change singularCohomologyPullback
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2
      (alternatingClass p.val B) = alternatingClass p.val B ↔ _
  rw [alternatingClass_pullback_affineBiholomorph]
  exact (alternatingClass_bijective p.val).injective.eq_iff

/-- The genuine all-deck invariant submodule has the exact source-coordinate test. -/
theorem coefficientClass_mem_deckInvariants_iff (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (E : Fin 6 → ℤ) :
    coefficientClass p.val E ∈ periodCohomologyInvariants j p v hv 2 ↔
      coefficientPullback j.matrix.mulVecLin E = E := by
  rw [mem_periodCohomologyInvariants_iff_affine]
  change singularCohomologyPullback
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2
      (coefficientClass p.val E) = coefficientClass p.val E ↔ _
  rw [coefficientClass_pullback_affineBiholomorph]
  exact (coefficientClass_injective p.val).eq_iff

/-- Preserving the actual coefficient form fixes the actual class under every deck element. -/
theorem coefficientClass_deck_invariant_of_preserved (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (E : Fin 6 → ℤ)
    (hE : coefficientPullback j.matrix.mulVecLin E = E) (g : CyclicGroup j) :
    singularCohomologyPullback (surfaceDeckMap j p v hv g) 2 (coefficientClass p.val E) =
      coefficientClass p.val E := by
  apply (mem_periodCohomologyInvariants_iff j p v hv 2 _).mp
    ((coefficientClass_mem_deckInvariants_iff j p v hv E).mpr hE)

end Wikipedia.HopfProblem.PeriodTorusCohomology
