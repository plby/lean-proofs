/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos223.Basic

/-!
# Witness graph for the odd cospherical construction

The vertices are a path of `k + 1` base points and three exceptional points:
the pole and the two supporting sphere points.  This file records the exact
`2 * k + 6` certified diameter pairs independently of their geometric
realization.
-/

open scoped Sym2

namespace Erdos223
namespace OddCosphericalConstruction

open SimpleGraph

abbrev OddVertex (k : ℕ) := Fin (k + 1) ⊕ Fin 3

abbrev OddEdgeIndex (k : ℕ) :=
  Fin k ⊕ (Fin (k + 1) ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)))

def pathLeft {k : ℕ} (i : Fin k) : Fin (k + 1) :=
  ⟨i, by omega⟩

def pathRight {k : ℕ} (i : Fin k) : Fin (k + 1) :=
  ⟨i + 1, by omega⟩

def firstBase (k : ℕ) : Fin (k + 1) := ⟨0, by omega⟩

def lastBase (k : ℕ) : Fin (k + 1) := ⟨k, by omega⟩

def secondBase {k : ℕ} (hk : 3 ≤ k) : Fin (k + 1) := ⟨1, by omega⟩

def penultimateBase {k : ℕ} (hk : 3 ≤ k) : Fin (k + 1) := ⟨k - 1, by omega⟩

def yBase {k : ℕ} (j : Fin 2) : Fin (k + 1) :=
  if (j : ℕ) = 0 then firstBase k else lastBase k

def zBase {k : ℕ} (hk : 3 ≤ k) (j : Fin 2) : Fin (k + 1) :=
  if (j : ℕ) = 0 then secondBase hk else penultimateBase hk

def oddEdgeMap {k : ℕ} (hk : 3 ≤ k) : OddEdgeIndex k → Sym2 (OddVertex k)
  | .inl i => s(Sum.inl (pathLeft i), Sum.inl (pathRight i))
  | .inr (.inl i) => s(Sum.inr (0 : Fin 3), Sum.inl i)
  | .inr (.inr (.inl j)) => s(Sum.inr (1 : Fin 3), Sum.inl (yBase j))
  | .inr (.inr (.inr (.inl j))) => s(Sum.inr (2 : Fin 3), Sum.inl (zBase hk j))
  | .inr (.inr (.inr (.inr _))) => s(Sum.inr (1 : Fin 3), Sum.inr (2 : Fin 3))

lemma yBase_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (@yBase k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [yBase, firstBase, lastBase] at hij ⊢ <;> omega

lemma zBase_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (zBase hk) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [zBase, secondBase, penultimateBase] at hij ⊢ <;> omega

lemma oddEdgeMap_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (oddEdgeMap hk) := by
  intro a b hab
  rcases a with i | (i | (i | (i | i))) <;>
    rcases b with j | (j | (j | (j | j))) <;>
    simp only [oddEdgeMap, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.isValue] at hab ⊢
  all_goals try { apply Fin.ext; omega }
  all_goals rw [Sym2.eq_iff] at hab
  all_goals rcases hab with hab | hab <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      and_false, Fin.isValue] at hab ⊢
  all_goals try { norm_num at hab }
  all_goals try {
    exfalso
    have hpole := congrArg Fin.val hab.1
    norm_num at hpole }
  · apply Fin.ext
    simpa [pathLeft] using congrArg Fin.val hab.1
  · exfalso
    have h₁ := congrArg Fin.val hab.1
    have h₂ := congrArg Fin.val hab.2
    simp [pathLeft, pathRight] at h₁ h₂
    omega
  · exact hab.2
  · exact yBase_injective hk hab.2
  · exact zBase_injective hk hab.2

def oddWitnessEdges {k : ℕ} (hk : 3 ≤ k) : Finset (Sym2 (OddVertex k)) :=
  Finset.univ.image (oddEdgeMap hk)

lemma card_oddWitnessEdges {k : ℕ} (hk : 3 ≤ k) :
    (oddWitnessEdges hk).card = 2 * k + 6 := by
  rw [oddWitnessEdges, Finset.card_image_of_injective _ (oddEdgeMap_injective hk)]
  simp [OddEdgeIndex]
  omega

def oddWitnessGraph {k : ℕ} (hk : 3 ≤ k) : SimpleGraph (OddVertex k) :=
  SimpleGraph.fromEdgeSet (oddWitnessEdges hk : Set (Sym2 (OddVertex k)))

noncomputable instance {k : ℕ} (hk : 3 ≤ k) : DecidableRel (oddWitnessGraph hk).Adj :=
  Classical.decRel _

lemma oddEdgeMap_not_diag {k : ℕ} (hk : 3 ≤ k) (i : OddEdgeIndex k) :
    oddEdgeMap hk i ∉ Sym2.diagSet := by
  rw [Sym2.mem_diagSet]
  rcases i with i | (i | (i | (i | i))) <;>
    simp [oddEdgeMap, pathLeft, pathRight]

theorem card_oddWitnessGraph {k : ℕ} (hk : 3 ≤ k) :
    (oddWitnessGraph hk).edgeFinset.card = 2 * k + 6 := by
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  rw [oddWitnessGraph, SimpleGraph.edgeSet_fromEdgeSet]
  have hdisj : Disjoint (oddWitnessEdges hk : Set (Sym2 (OddVertex k))) Sym2.diagSet := by
    rw [Set.disjoint_left]
    intro e he hdiag
    rw [oddWitnessEdges, Finset.mem_coe, Finset.mem_image] at he
    obtain ⟨i, -, rfl⟩ := he
    exact oddEdgeMap_not_diag hk i hdiag
  rw [sdiff_eq_left.mpr hdisj]
  simpa using card_oddWitnessEdges hk

end OddCosphericalConstruction
end Erdos223
