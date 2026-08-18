/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9Replacement
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2Construction

/-!
# Bilu Section 9.1: lifting the Ruzsa cover to the section lattice

The finite set furnished by Lemma 4.5 lives in the section lattice
`C₀ ∩ (ℤ^m × ℤ^r)`, whereas the Ruzsa cover is a statement in `ℤ^m`.
This file supplies the missing integral first-coordinate homomorphism and
proves that every difference occurring in the cover is the first coordinate
of a literal section-lattice vector.  This is the algebraic input used when
the covering centres are adjoined as new box directions.
-/

namespace Erdos186.CFP.Bilu.Section91CoveringEnlargement

open scoped Pointwise
open Proposition75Data Proposition75Case2Construction
open Section9Replacement Section9ContainerIntegration
open SubspaceLattice

noncomputable section

variable {m r : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {a : Fin r → EuclideanSpace ℝ (Fin m)}

/-- The integral first coordinate of a point of the section lattice.

Existence follows from the literal definition of
`ambientProductIntegralPoints`.  The following characterization makes the
classical choice invisible to all consumers. -/
noncomputable def latticeHeadFun (D : GeometricData B a)
    (z : D.latticePoints) : Mahler.IntegralPoint m :=
  (mem_ambientProductIntegralPoints_iff.mp z.property).choose

/-- The chosen integral coordinate really is the first real coordinate. -/
theorem integralReal_latticeHeadFun (D : GeometricData B a)
    (z : D.latticePoints) :
    integralReal (latticeHeadFun D z) =
      head ((z : D.C0) : Ambient m r) := by
  exact congrArg head
    (mem_ambientProductIntegralPoints_iff.mp z.property).choose_spec.choose_spec

/-- The first-coordinate choice is additive. -/
noncomputable def latticeHead (D : GeometricData B a) :
    D.latticePoints →+ Mahler.IntegralPoint m where
  toFun := latticeHeadFun D
  map_zero' := by
    funext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ x i)
      (integralReal_latticeHeadFun D (0 : D.latticePoints))
    change (((latticeHeadFun D 0) i : ℤ) : ℝ) = 0 at hi
    exact_mod_cast hi
  map_add' z w := by
    funext i
    have hzw := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ x i)
      (integralReal_latticeHeadFun D (z + w))
    have hz := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ x i)
      (integralReal_latticeHeadFun D z)
    have hw := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ x i)
      (integralReal_latticeHeadFun D w)
    change (((latticeHeadFun D (z + w)) i : ℤ) : ℝ) =
      head (((z + w : D.latticePoints) : D.C0) : Ambient m r) i at hzw
    change (((latticeHeadFun D z) i : ℤ) : ℝ) =
      head ((z : D.latticePoints) : Ambient m r) i at hz
    change (((latticeHeadFun D w) i : ℤ) : ℝ) =
      head ((w : D.latticePoints) : Ambient m r) i at hw
    have hreal : (((latticeHeadFun D (z + w)) i : ℤ) : ℝ) =
        (((latticeHeadFun D z) i : ℤ) : ℝ) +
          (((latticeHeadFun D w) i : ℤ) : ℝ) := by
      rw [hzw, hz, hw]
      rfl
    exact_mod_cast hreal

/-- The chosen integral coordinate really is the first real coordinate. -/
@[simp] theorem integralReal_latticeHead (D : GeometricData B a)
    (z : D.latticePoints) :
    integralReal (latticeHead D z) =
      head ((z : D.C0) : Ambient m r) := by
  exact integralReal_latticeHeadFun D z

namespace Lemma45SectionSeed

variable {D : GeometricData B a}
  {K : Finset (Mahler.IntegralPoint m)} {coverConstant : ℕ}

/-- The section-lattice vector representing the difference of two points of
the large source slice. -/
noncomputable def differenceLift
    (S : Lemma45SectionSeed D K coverConstant)
    (x y : {x // x ∈ S.sourceSlice}) : D.latticePoints :=
  ⟨S.embed x - S.embed y, D.latticePoints.sub_mem
    (S.embed_lattice x) (S.embed_lattice y)⟩

/-- Projection of the lifted lattice difference is exactly the original
integer difference; the two occurrences of the translating base cancel. -/
theorem latticeHead_differenceLift
    (S : Lemma45SectionSeed D K coverConstant)
    (x y : {x // x ∈ S.sourceSlice}) :
    latticeHead D (differenceLift S x y) =
      (x : Mahler.IntegralPoint m) - y := by
  funext i
  have hhead := integralReal_latticeHead D (differenceLift S x y)
  have hi := congrArg (fun u : EuclideanSpace ℝ (Fin m) ↦ u i) hhead
  change ((((latticeHead D) (differenceLift S x y)) i : ℤ) : ℝ) =
    head (((S.embed x - S.embed y : D.C0) : Ambient m r)) i at hi
  have hx := congrArg (fun u : EuclideanSpace ℝ (Fin m) ↦ u i)
    (congrArg head (S.embed_apply x))
  have hy := congrArg (fun u : EuclideanSpace ℝ (Fin m) ↦ u i)
    (congrArg head (S.embed_apply y))
  change head ((S.embed x : D.C0) : Ambient m r) i =
    (((x : Mahler.IntegralPoint m) i : ℤ) : ℝ) -
      ((S.base i : ℤ) : ℝ) at hx
  change head ((S.embed y : D.C0) : Ambient m r) i =
    (((y : Mahler.IntegralPoint m) i : ℤ) : ℝ) -
      ((S.base i : ℤ) : ℝ) at hy
  have hreal : ((((latticeHead D) (differenceLift S x y)) i : ℤ) : ℝ) =
      (((x : Mahler.IntegralPoint m) i : ℤ) : ℝ) -
        (((y : Mahler.IntegralPoint m) i : ℤ) : ℝ) := by
    rw [hi]
    change head ((S.embed x : D.C0) : Ambient m r) i -
      head ((S.embed y : D.C0) : Ambient m r) i = _
    rw [hx, hy]
    ring
  exact_mod_cast hreal

/-- Section 9.1 in the form needed by the geometric enlargement.

The centres are bounded by equation (9.3), and every source point is a
centre plus the first coordinate of one literal vector of the section
lattice. -/
theorem exists_coveringEnlargement
    (S : Lemma45SectionSeed D K coverConstant)
    (sigma : ℕ)
    (hdouble : (K + K).card ≤ sigma * K.card) :
    ∃ C : CoveringCertificate K S.sourceSlice,
      C.centers.card ≤ sigma * coverConstant ∧
      ∀ z ∈ K, ∃ c ∈ C.centers,
        ∃ x : {x // x ∈ S.sourceSlice},
        ∃ y : {y // y ∈ S.sourceSlice},
          z = c + latticeHead D (differenceLift S x y) := by
  obtain ⟨C, hCcard⟩ := exists_coveringCertificate_with_card_bound
    K S.sourceSlice S.sourceSlice_nonempty S.sourceSlice_subset sigma
      coverConstant S.large hdouble
  refine ⟨C, hCcard, ?_⟩
  intro z hz
  obtain ⟨c, hc, u, hu, hzu⟩ := Finset.mem_add.mp (C.cover hz)
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hu
  refine ⟨c, hc, ⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  rw [latticeHead_differenceLift]
  exact hzu.symm

end Lemma45SectionSeed

end

end Erdos186.CFP.Bilu.Section91CoveringEnlargement

#print axioms Erdos186.CFP.Bilu.Section91CoveringEnlargement.integralReal_latticeHead
#print axioms Erdos186.CFP.Bilu.Section91CoveringEnlargement.Lemma45SectionSeed.exists_coveringEnlargement
