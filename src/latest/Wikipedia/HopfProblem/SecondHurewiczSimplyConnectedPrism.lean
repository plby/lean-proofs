import Wikipedia.HopfProblem.SecondHurewicz

/-!
# Actual prism chains for simplex-dependent homotopies

The homotopy used to straighten a singular simplex depends on that simplex;
it need not arise from a continuous self-map of the target space. The
identities below use the actual interval cross product and prove the full
boundary formula directly, including every side face.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

def timeSlice (H : C(I × A, X)) (t : I) : C(A, X) :=
  H.comp (crossInsertLeft t)

@[simp] theorem timeSlice_apply (H : C(I × A, X)) (t : I) (a : A) :
    timeSlice H t a = H (t, a) := rfl

theorem crossPoint_left (n : ℕ) (t : I) (c : Chains A n) :
    crossProductZeroLeft I A n (pointChain t) c =
      inducedChain (crossInsertLeft t) n c := by
  rw [pointChain, crossProductZeroLeft_simplex_left]
  rfl

theorem inducedChain_timeSlice (H : C(I × A, X)) (t : I) (n : ℕ) (c : Chains A n) :
    inducedChain H n (inducedChain (crossInsertLeft t) n c) =
      inducedChain (timeSlice H t) n c := by
  change ((inducedChain H n).comp (inducedChain (crossInsertLeft t) n)) c = _
  rw [← inducedChain_comp]
  rfl

/-- The actual singular prism, with its homotopy coordinate first. -/
def prismOperator (n : ℕ) (H : C(I × A, X)) : Chains A n →ₗ[ℤ] Chains X (n + 1) :=
  (inducedChain H (n + 1)).comp (crossProductEdge I A n intervalChain)

@[simp] theorem prismOperator_apply (n : ℕ) (H : C(I × A, X)) (c : Chains A n) :
    prismOperator n H c =
      inducedChain H (n + 1) (crossProductEdge I A n intervalChain c) := rfl

theorem prismOperator_boundary_zero (H : C(I × A, X)) (c : Chains A 0) :
    boundaryOne X (prismOperator 0 H c) =
      inducedChain (timeSlice H 1) 0 c - inducedChain (timeSlice H 0) 0 c := by
  change ((singularComplex X).d 1 0).hom (prismOperator 0 H c) = _
  rw [prismOperator_apply, ← inducedChain_boundary, crossProductEdge_boundary_zero]
  change inducedChain H 0 (crossProductZeroLeft I A 0 (boundaryOne I intervalChain) c) = _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply,
    crossPoint_left, inducedChain_timeSlice]

/-- The exact signed prism formula, before passing to any homology group. -/
theorem prismOperator_boundary (n : ℕ) (H : C(I × A, X)) (c : Chains A (n + 1)) :
    ((singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      inducedChain (timeSlice H 1) (n + 1) c -
        inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← inducedChain_boundary, crossProductEdge_boundary n]
  change inducedChain H (n + 1)
    (crossProductZeroLeft I A (n + 1) (boundaryOne I intervalChain) c -
      crossProductEdge I A n intervalChain (((singularComplex A).d (n + 1) n).hom c)) = _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply,
    crossPoint_left, inducedChain_timeSlice, prismOperator_apply]

/-- Restricting the homotopy in its spatial variable agrees with the actual chain map. -/
theorem prismOperator_domain (n : ℕ) (f : C(A, B)) (H : C(I × B, X)) (c : Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id I).prodMap f)) c =
      prismOperator n H (inducedChain f n c) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) f n intervalChain c
  rw [inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (inducedChain H (n + 1)) h

/-- The prism over the actual standard simplex generator. -/
def simplexPrism (n : ℕ) (H : C(I × Simplex n, X)) : Chains X (n + 1) :=
  prismOperator n H (simplexChain (Simplex n) n (ContinuousMap.id (Simplex n)))

theorem prismOperator_simplex (n : ℕ) (H : C(I × A, X)) (smp : SingularSimplex A n) :
    prismOperator n H (simplexChain A n smp) =
      simplexPrism n (H.comp ((ContinuousMap.id I).prodMap smp)) := by
  have h := prismOperator_domain n smp H
    (simplexChain (Simplex n) n (ContinuousMap.id (Simplex n)))
  rw [inducedChain_simplex, ContinuousMap.comp_id] at h
  exact h.symm

/-- Each side of a simplex-dependent prism is the prism of its actual face restriction. -/
theorem simplexPrism_boundary (n : ℕ) (H : C(I × Simplex (n + 1), X)) :
    ((singularComplex X).d (n + 2) (n + 1)).hom (simplexPrism (n + 1) H) =
      simplexChain X (n + 1) (timeSlice H 1) -
        simplexChain X (n + 1) (timeSlice H 0) -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          simplexPrism n (H.comp ((ContinuousMap.id I).prodMap (simplexFace n i))) := by
  rw [simplexPrism, prismOperator_boundary, inducedChain_simplex,
    inducedChain_simplex, ContinuousMap.comp_id, ContinuousMap.comp_id]
  rw [boundary_simplex, map_sum]
  simp only [map_zsmul, ContinuousMap.id_comp, prismOperator_simplex]

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
