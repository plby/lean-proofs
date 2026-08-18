/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9NormalizedReplacement

/-!
# The initial Section 9.1 lattice presentation

After the Ruzsa covering step the source lattice is the direct product of
the normalized section lattice with one free integral coordinate for every
covering centre.  The new coordinate indexed by a centre `c` is sent to
`c`; the old section lattice is sent by its literal first coordinate.

This file constructs that homomorphism and proves that every point of `K`
has a lift.  It is the discrete presentation on which Section 9.2 performs
kernel descent.
-/

namespace Erdos186.CFP.Bilu.Section91InitialPresentation

open scoped BigOperators Pointwise
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
open Section9Replacement Section9ContainerIntegration
open Section91CoveringEnlargement Section9NormalizedReplacement
open SubspaceLattice

noncomputable section

variable {m r : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {a : Fin r → EuclideanSpace ℝ (Fin m)}
  {D : GeometricData B a}
  {K : Finset (Mahler.IntegralPoint m)} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

namespace InitialPresentation

variable (N : CoveredNormalizedReplacement (D := D) (K := K)
  (coverConstant := coverConstant) constant scale sigma)

/-- Integral coefficients in the adjoined covering-centre directions. -/
abbrev CenterCoefficients := N.cover.centers → ℤ

/-- The direct-product lattice used immediately after Section 9.1. -/
abbrev InitialLattice :=
  integralPoints (coordinateC0 D) × CenterCoefficients N

/-- The normalized old section lattice maps to its literal integral first
coordinate. -/
noncomputable def oldLatticeMap :
    integralPoints (coordinateC0 D) →+ Mahler.IntegralPoint m :=
  (latticeHead D).comp
    (coordinateLatticeEquiv D).symm.toLinearMap.toAddHom

/-- An integral coefficient family maps to the corresponding combination
of Ruzsa centres. -/
noncomputable def centersLinearCombination :
    CenterCoefficients N →+ Mahler.IntegralPoint m where
  toFun t := ∑ i, t i • (i : Mahler.IntegralPoint m)
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The initial appropriate map `Γ₀ ⊕ ℤ^ᴬ → ℤ^m`. -/
noncomputable def presentationMap :
    InitialLattice N →+ Mahler.IntegralPoint m where
  toFun q := oldLatticeMap (D := D) q.1 +
    centersLinearCombination N q.2
  map_zero' := by
    change oldLatticeMap (D := D) (0 : integralPoints (coordinateC0 D)) +
      centersLinearCombination N (0 : CenterCoefficients N) = 0
    rw [map_zero, map_zero, add_zero]
  map_add' x y := by
    change oldLatticeMap (D := D) (x.1 + y.1) +
        centersLinearCombination N (x.2 + y.2) = _
    rw [map_add, map_add]
    abel

@[simp] theorem oldLatticeMap_coordinateLatticeEquiv
    (z : D.latticePoints) :
    oldLatticeMap (D := D) (coordinateLatticeEquiv D z) =
      latticeHead D z := by
  change latticeHead D
    ((coordinateLatticeEquiv D).symm (coordinateLatticeEquiv D z)) = _
  rw [(coordinateLatticeEquiv D).symm_apply_apply]

@[simp] theorem centersLinearCombination_single
    (c : N.cover.centers) :
  centersLinearCombination N (Pi.single c 1) =
      (c : Mahler.IntegralPoint m) := by
  classical
  change (∑ i, (Pi.single c 1 : CenterCoefficients N) i •
    (i : Mahler.IntegralPoint m)) = _
  rw [Fintype.sum_eq_single c]
  · simp
  · intro b hbc
    simp [Pi.single, hbc]

/-- The explicit initial lift associated to a chosen centre and a chosen
section-lattice difference. -/
noncomputable def initialLift
    (c : N.cover.centers) (z : D.latticePoints) : InitialLattice N :=
  (coordinateLatticeEquiv D z, Pi.single c 1)

@[simp] theorem initialMap_initialLift
    (c : N.cover.centers) (z : D.latticePoints) :
    presentationMap (D := D) N (initialLift N c z) =
      latticeHead D z + (c : Mahler.IntegralPoint m) := by
  simp [presentationMap, initialLift, add_comm]

/-- Every point of `K` has a literal lift to the initial direct-product
lattice. -/
theorem exists_initialLift (x : Mahler.IntegralPoint m) (hx : x ∈ K) :
    ∃ q : InitialLattice N, presentationMap (D := D) N q = x := by
  obtain ⟨c, hc, u, v, hcover⟩ := N.cover_lift x hx
  let c' : N.cover.centers := ⟨c, hc⟩
  let z : D.latticePoints :=
    Section91CoveringEnlargement.Lemma45SectionSeed.differenceLift
      N.normalized.seed u v
  refine ⟨initialLift N c' z, ?_⟩
  rw [initialMap_initialLift]
  simpa only [z, c', add_comm] using hcover.symm

/-- The image of the initial lattice map contains all of `K`. -/
theorem subset_range_initialMap :
    (K : Set (Mahler.IntegralPoint m)) ⊆
      Set.range (presentationMap (D := D) N) := by
  intro x hx
  exact exists_initialLift N x hx

/-- The real rank of the direct-product presentation: the rank of the
section plus one free direction for every Ruzsa centre. -/
def initialRank : ℕ :=
  Module.finrank ℝ D.C0 + N.cover.centers.card

/-- Equation (9.3) and properness of `C₀` give the source rank bound for
the initial appropriate presentation. -/
theorem initialRank_le :
    initialRank N ≤
      (m + r - 1) + sigma * coverConstant := by
  rw [initialRank]
  apply Nat.add_le_add
  · have hlt := D.C0.finrank_lt D.proper
    have hambient : Module.finrank ℝ (Ambient m r) = m + r := by
      rw [(WithLp.linearEquiv 2 ℝ
      (EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin r))).finrank_eq]
      simp [Module.finrank_prod]
    rw [hambient] at hlt
    omega
  · exact N.centers_card

end InitialPresentation

end

end Erdos186.CFP.Bilu.Section91InitialPresentation

#print axioms Erdos186.CFP.Bilu.Section91InitialPresentation.InitialPresentation.exists_initialLift
#print axioms Erdos186.CFP.Bilu.Section91InitialPresentation.InitialPresentation.subset_range_initialMap
#print axioms Erdos186.CFP.Bilu.Section91InitialPresentation.InitialPresentation.initialRank_le
