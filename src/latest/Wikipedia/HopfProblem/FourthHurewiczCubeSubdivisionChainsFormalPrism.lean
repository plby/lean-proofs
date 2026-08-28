import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism

/-!
# Literal shuffle prisms on ordered formal simplices

The standard prism is the alternating sum of the ordered shuffle simplices
`[0w₀, …, 0wᵢ, 1wᵢ, …, 1w_q]`. Splitting off the first shuffle gives a cone
recursion on the tail of the right-hand simplex. Every identity is in the
original free integral chain module, without a normalization quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris
open scoped BigOperators

variable {V W V' W' : Type*}

/-- The literal ordered vertices of the `i`-th prism shuffle. -/
def shufflePrismVertices {q : ℕ} (v : Fin 2 → V) (w : Fin (q + 1) → W)
    (i : Fin (q + 1)) : Fin (q + 2) → V × W :=
  fun k => (if k ≤ i.castSucc then v 0 else v 1, w (i.predAbove k))

@[simp] theorem shufflePrismVertices_first {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i 0 = (v 0, w 0) := by
  simp [shufflePrismVertices]

/-- The first shuffle consists of the initial source vertex and the whole target face. -/
theorem shufflePrismVertices_zero_index {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) :
    shufflePrismVertices v w 0 = Fin.cons (v 0, w 0) (fun j => (v 1, w j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices]

/-- Every later shuffle is the cone on the corresponding shuffle of the tail. -/
theorem shufflePrismVertices_succ_index {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i.succ =
      Fin.cons (v 0, w 0) (shufflePrismVertices v (Fin.tail w) i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices, Fin.tail, Fin.le_castSucc_iff]

/-- Prism shuffles are natural for arbitrary maps on both vertex sets. -/
theorem shufflePrismVertices_map {q : ℕ} (f : V → V') (g : W → W')
    (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    Prod.map f g ∘ shufflePrismVertices v w i =
      shufflePrismVertices (f ∘ v) (g ∘ w) i := by
  funext k
  simp only [shufflePrismVertices, Function.comp_apply, Prod.map_apply]
  split_ifs <;> rfl

/-- The alternating literal shuffle prism on an edge and an ordered simplex. -/
def standardPrism (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    FormalChains (V × W) (q + 2) :=
  ∑ i : Fin (q + 1), (-1 : ℤ) ^ i.val • formalSimplex (shufflePrismVertices v w i)

/-- In right degree zero the standard prism is the original ordered edge. -/
theorem standardPrism_zero (v : Fin 2 → V) (w : Fin 1 → W) :
    standardPrism 0 v w = formalSimplex (fun i => (v i, w 0)) := by
  rw [standardPrism, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.eq_zero j]
    rfl

/-- Splitting the first shuffle gives the exact cone recursion. -/
theorem standardPrism_succ (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    standardPrism (q + 1) v w =
      formalCone (v 0, w 0) (q + 2)
        (formalMap (fun z => (v 1, z)) (q + 2) (formalSimplex w) -
          standardPrism q v (Fin.tail w)) := by
  rw [standardPrism, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index,
    map_sub, formalMap_simplex, formalCone_simplex, standardPrism,
    map_sum, map_smul, formalCone_simplex]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    shufflePrismVertices_succ_index]

/-- The standard prism commutes with arbitrary maps on the two vertex sets. -/
theorem formalMap_standardPrism (f : V → V') (g : W → W') (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    formalMap (Prod.map f g) (q + 2) (standardPrism q v w) =
      standardPrism q (f ∘ v) (g ∘ w) := by
  simp only [standardPrism, map_sum, map_smul, formalMap_simplex,
    shufflePrismVertices_map]

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
