import Wikipedia.HopfProblem.OrbitPairSubdivisionMeanContraction

/-!
# Affine images of a subdivided simplex have smaller diameter

Convex combinations do not increase a pairwise diameter bound. Combined
with the nested-face estimate, this controls every pair of points in each
affine subdivided simplex, in an arbitrary real normed space.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz AffineCoordinates RealizationSimplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A B : Type*} [Fintype A] [Fintype B]

def affineValue (v : A → E) (t : stdSimplex ℝ A) : E := ∑ i, t i • v i

theorem affineValue_mem_convex (v : A → E) (t : stdSimplex ℝ A)
    (C : Set E) (hC : Convex ℝ C) (hv : ∀ i, v i ∈ C) : affineValue v t ∈ C :=
  hC.sum_mem (fun i _ ↦ stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t) (fun i _ ↦ hv i)

theorem affineValue_dist_le (v : A → E) (t : stdSimplex ℝ A) (x : E) (D : ℝ)
    (hv : ∀ i, dist (v i) x ≤ D) : dist (affineValue v t) x ≤ D :=
  affineValue_mem_convex v t (Metric.closedBall x D) (convex_closedBall x D) hv

theorem affineValues_dist_le (v : A → E) (t s : stdSimplex ℝ A) (D : ℝ)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) : dist (affineValue v t) (affineValue v s) ≤ D := by
  apply affineValue_dist_le v t
  intro i
  have h := affineValue_dist_le v s (v i) D (fun j ↦ hv j i)
  simpa only [dist_comm] using h

theorem affineValue_map (f : A → B) (v : B → E) (t : stdSimplex ℝ A) :
    affineValue v (stdSimplex.map f t) = affineValue (v ∘ f) t := by
  classical
  change (∑ j, FunOnFinite.linearMap ℝ ℝ f t j • v j) = ∑ i, t i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    _ = ∑ j : B, ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), t i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun i ↦ t i • v (f i))

theorem affineValue_weighted (v : B → E) (a : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) :
    affineValue v (weighted a t) = affineValue (fun i ↦ affineValue v (a i)) t := by
  simp only [affineValue, weighted_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem affineValue_chainBarycentre {n : ℕ} (v : Fin (n + 1) → E)
    (F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    affineValue v (chainBarycentre n F) = faceMean (fun i ↦ v i.down) F.finset := by
  classical
  let : Nonempty F.finset := F.nonempty.to_subtype
  change affineValue v (stdSimplex.map (fun i : F.finset ↦ i.val.down) stdSimplex.barycenter) = _
  rw [affineValue_map]
  change (∑ i : F.finset, (Fintype.card F.finset : ℝ)⁻¹ • v i.val.down) = _
  rw [← Finset.smul_sum, Fintype.card_coe]
  unfold faceMean
  congr 1
  exact Finset.sum_coe_sort F.finset (fun i ↦ v i.down)

theorem affineFaceMeans_dist_le_mesh {V : Type*} {k : ℕ}
    (v : V → E) (F : Finset V) (C : Fin (k + 1) → Finset V)
    (hC : Monotone C) (hne : ∀ j, (C j).Nonempty) (hCF : ∀ j, C j ⊆ F)
    (N : ℕ) (hcard : F.card ≤ N + 1) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ i ∈ F, ∀ j ∈ F, dist (v i) (v j) ≤ D) (t s : Simplex k) :
    dist (affineValue (fun j ↦ faceMean v (C j)) t)
      (affineValue (fun j ↦ faceMean v (C j)) s) ≤ ((N : ℝ) / (N + 1)) * D := by
  apply affineValues_dist_le
  intro i j
  rcases le_total i j with hij | hji
  · exact faceMeans_dist_le_mesh v (C i) (C j) (hne i) (hC hij) N
      ((Finset.card_le_card (hCF j)).trans hcard) D hD
      (fun a ha b hb ↦ hv a (hCF j ha) b (hCF j hb))
  · rw [dist_comm]
    exact faceMeans_dist_le_mesh v (C j) (C i) (hne j) (hC hji) N
      ((Finset.card_le_card (hCF i)).trans hcard) D hD
      (fun a ha b hb ↦ hv a (hCF i ha) b (hCF i hb))

end Wikipedia.HopfProblem.OrbitPair.Subdivision
