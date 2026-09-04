/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AnnularGapChildVector

/-!
# Concrete nested edge kernel for annular profiles

For one profile level, the offspring counts form a weak composition `g`.
Each parent gap retains its ordered vector of actual inner-boundary entrance
points.  This file canonically concatenates those parent vectors, in parent
order, into the global child vector consumed by the nested profile dynamic
program.

The main theorem is an exact finite disintegration: summing the concrete
global-vector edge kernel is the product of the literal endpoint-integrated
one-gap kernels.  Thus no intermediate child entrance is integrated before
the next-level continuation has been attached.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularProfileNestedEdge

open AnnularGapChildVector AnnularNestedProfileKernel
open AnnularOffspringKernel AnnularOffspringKernelRadial
open AnnularProfileClocks
open PathInsertion RealDiscFinite ThickPoint

noncomputable section

/-! ## Canonical parent-major indexing -/

/-- The canonical parent-major identification of all local offspring slots
with the global child slots of a weak composition. -/
noncomputable def gapChildIndexEquiv {a b : ℕ} (g : GapPattern a b) :
    ((i : Fin a) × Fin (gapMultiplicity g i)) ≃ Fin b :=
  finSigmaFinEquiv.trans (finCongr (sum_gapMultiplicity g))

/-- A global child vector is canonically the family of its parent-local
subvectors. -/
noncomputable def globalChildrenEquivParentVectors
    {a b : ℕ} (g : GapPattern a b) (S : Type*) :
    (Fin b → S) ≃ (∀ i : Fin a, Fin (gapMultiplicity g i) → S) :=
  (Equiv.arrowCongr (gapChildIndexEquiv g).symm (Equiv.refl S)).trans
    (Equiv.piCurry (fun _ _ ↦ S))

/-- The local child vector belonging to one parent in a global vector. -/
noncomputable def localChildrenOfGlobal
    {a b : ℕ} (g : GapPattern a b) {S : Type*}
    (children : Fin b → S) (i : Fin a) :
    Fin (gapMultiplicity g i) → S :=
  globalChildrenEquivParentVectors g S children i

@[simp] theorem localChildrenOfGlobal_apply
    {a b : ℕ} (g : GapPattern a b) {S : Type*}
    (children : Fin b → S) (i : Fin a)
    (j : Fin (gapMultiplicity g i)) :
    localChildrenOfGlobal g children i j =
      children (gapChildIndexEquiv g ⟨i, j⟩) :=
  rfl

/-- Finite Tonelli for the canonical global/local child-vector
identification. -/
theorem sum_globalChildVector_product_eq_product_sum
    {a b : ℕ} (g : GapPattern a b) {S : Type*} [Fintype S]
    (K : ∀ i : Fin a, (Fin (gapMultiplicity g i) → S) → ℝ≥0∞) :
    ∑ children : Fin b → S,
        ∏ i : Fin a, K i (localChildrenOfGlobal g children i) =
      ∏ i : Fin a,
        ∑ parentChildren : Fin (gapMultiplicity g i) → S,
          K i parentChildren := by
  calc
    ∑ children : Fin b → S,
          ∏ i : Fin a, K i (localChildrenOfGlobal g children i) =
        ∑ parentChildren : ∀ i : Fin a,
            Fin (gapMultiplicity g i) → S,
          ∏ i : Fin a, K i (parentChildren i) := by
      apply Fintype.sum_equiv (globalChildrenEquivParentVectors g S)
      intro children
      rfl
    _ = ∏ i : Fin a,
          ∑ parentChildren : Fin (gapMultiplicity g i) → S,
            K i parentChildren :=
      (Fintype.prod_sum K).symm

/-! ## Literal profile state and child-vector edge -/

/-- The boundary state used at nested depth `d` is the literal profile
boundary at radial level `d + 2`. -/
abbrev ProfileNestedState (n : ℕ) (center : Point) (depth : ℕ) : Type :=
  ProfileCycleMiddlePoint n (depth + 2) center

/-- The set-subtype and canonical finite-finset subtype of one literal
profile boundary are equivalent without changing the underlying point. -/
noncomputable def profileInnerBoundaryPointEquiv
    (n k : ℕ) (center : Point) :
    InnerBoundaryPoint (profileInnerBoundary n k center) ≃
      ProfileCycleMiddlePoint n k center where
  toFun z := ⟨z.1, mem_discBoundaryFinset.mpr (by
    simpa only [profileInnerBoundary] using z.2)⟩
  invFun z := ⟨z.1, by
    simpa only [profileInnerBoundary] using mem_discBoundaryFinset.mp z.2⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

/-- The parent-local child vector, converted from the nested finite state
to the literal set-subtype used by the stopped-event kernel. -/
noncomputable def literalProfileLocalChildren
    {n depth a b : ℕ} {center : Point} (g : GapPattern a b)
    (children : BoundaryVector (ProfileNestedState n center) (depth + 1) b)
    (i : Fin a) :
    Fin (gapMultiplicity g i) →
      InnerBoundaryPoint (profileInnerBoundary n (depth + 3) center) :=
  fun j ↦ (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
    (localChildrenOfGlobal g children i j)

/-- The actual one-level ENNReal edge kernel: a product over parent gaps of
literal stopped-event masses, retaining the global ordered child vector. -/
noncomputable def literalProfileNestedEdgeKernelENNReal
    (n : ℕ) (center : Point) :
    NestedEdgeKernelENNReal (ProfileNestedState n center) :=
  fun depth a _b g entrance children ↦
    ∏ i : Fin a,
      literalGapChildVectorKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center)
        (entrance i).1 (gapMultiplicity g i)
        (literalProfileLocalChildren g children i)

/-- Every concrete one-level edge mass is finite. -/
theorem literalProfileNestedEdgeKernelENNReal_ne_top
    (n : ℕ) (center : Point) (depth a b : ℕ) (g : GapPattern a b)
    (entrance : BoundaryVector (ProfileNestedState n center) depth a)
    (children : BoundaryVector (ProfileNestedState n center) (depth + 1) b) :
    literalProfileNestedEdgeKernelENNReal n center
      depth a b g entrance children ≠ ⊤ := by
  simp only [literalProfileNestedEdgeKernelENNReal,
    literalGapChildVectorKernel]
  exact ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top fairSteps _

/-- Summing one parent-local finite-state vector is exactly its literal
endpoint-integrated marked kernel. -/
theorem sum_literalProfileLocalChildrenKernel_eq_integratedMarkedKernel
    {n depth a b : ℕ} {center : Point} (g : GapPattern a b)
    (entrance : BoundaryVector (ProfileNestedState n center) depth a)
    (i : Fin a) :
    ∑ parentChildren : Fin (gapMultiplicity g i) →
        ProfileNestedState n center (depth + 1),
      literalGapChildVectorKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center)
        (entrance i).1 (gapMultiplicity g i)
        (fun j ↦
          (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
            (parentChildren j)) =
      literalGapIntegratedMarkedKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center)
        (entrance i).1 (gapMultiplicity g i) := by
  let : Fintype
      (InnerBoundaryPoint (profileInnerBoundary n (depth + 3) center)) :=
    Fintype.ofEquiv (ProfileCycleMiddlePoint n (depth + 3) center)
      (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
  let vectorEquiv := Equiv.arrowCongr
    (Equiv.refl (Fin (gapMultiplicity g i)))
    (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
  calc
    ∑ parentChildren : Fin (gapMultiplicity g i) →
          ProfileNestedState n center (depth + 1),
        literalGapChildVectorKernel
          (profileOuterBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 3) center)
          (entrance i).1 (gapMultiplicity g i)
          (fun j ↦
            (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
              (parentChildren j)) =
        ∑ parentChildren : Fin (gapMultiplicity g i) →
            InnerBoundaryPoint (profileInnerBoundary n (depth + 3) center),
          literalGapChildVectorKernel
            (profileOuterBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 3) center)
            (entrance i).1 (gapMultiplicity g i) parentChildren := by
      exact Equiv.sum_comp vectorEquiv _
    _ = ∑' parentChildren : Fin (gapMultiplicity g i) →
            InnerBoundaryPoint (profileInnerBoundary n (depth + 3) center),
          literalGapChildVectorKernel
            (profileOuterBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 3) center)
            (entrance i).1 (gapMultiplicity g i) parentChildren := by
      rw [tsum_fintype]
    _ = literalGapIntegratedMarkedKernel
          (profileOuterBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 3) center)
          (entrance i).1 (gapMultiplicity g i) :=
      tsum_literalGapChildVectorKernel_eq_integratedMarkedKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center)
        (entrance i).1 (gapMultiplicity g i)

/-- Exact whole-level marginal identity for the concrete nested edge.  The
global child vector is summed only after the product of all parent-gap
kernels has retained it. -/
theorem sum_literalProfileNestedEdgeKernelENNReal_eq_product_integrated
    {n depth a b : ℕ} {center : Point} (g : GapPattern a b)
    (entrance : BoundaryVector (ProfileNestedState n center) depth a) :
    ∑ children : BoundaryVector (ProfileNestedState n center) (depth + 1) b,
        literalProfileNestedEdgeKernelENNReal n center
          depth a b g entrance children =
      ∏ i : Fin a,
        literalGapIntegratedMarkedKernel
          (profileOuterBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 3) center)
          (entrance i).1 (gapMultiplicity g i) := by
  let K : ∀ i : Fin a,
      (Fin (gapMultiplicity g i) →
        ProfileNestedState n center (depth + 1)) → ℝ≥0∞ :=
    fun i parentChildren ↦
      literalGapChildVectorKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center)
        (entrance i).1 (gapMultiplicity g i)
        (fun j ↦
          (profileInnerBoundaryPointEquiv n (depth + 3) center).symm
            (parentChildren j))
  calc
    ∑ children : BoundaryVector (ProfileNestedState n center)
          (depth + 1) b,
        literalProfileNestedEdgeKernelENNReal n center
          depth a b g entrance children =
        ∑ children : Fin b → ProfileNestedState n center (depth + 1),
          ∏ i : Fin a, K i (localChildrenOfGlobal g children i) := rfl
    _ = ∏ i : Fin a,
          ∑ parentChildren : Fin (gapMultiplicity g i) →
              ProfileNestedState n center (depth + 1),
            K i parentChildren :=
      sum_globalChildVector_product_eq_product_sum g K
    _ = ∏ i : Fin a,
          literalGapIntegratedMarkedKernel
            (profileOuterBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 2) center)
            (profileInnerBoundary n (depth + 3) center)
            (entrance i).1 (gapMultiplicity g i) := by
      apply Fintype.prod_congr
      intro i
      exact sum_literalProfileLocalChildrenKernel_eq_integratedMarkedKernel
        g entrance i

end

end Erdos1165.AnnularProfileNestedEdge
