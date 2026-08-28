import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalNormalizedBasic
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalRecursion

/-!
# Normalized evaluation of the original coned period product

The original edge product contains degenerate cones. A normalized cochain
kills precisely those terms, leaving the usual ordered prism. The proof
works in every degree and retains the original formal cross product.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The ordered prism, with one simplex for each position of the period edge. -/
def normalizedPeriodPrism : (q : ℕ) → Lattice → (Fin (q + 1) → Lattice) →
    FormalChains Lattice (q + 2)
  | 0, x, w => formalSimplex ![w 0, x + w 0]
  | q + 1, x, w => formalCone (w 0) (q + 2)
      (formalSimplex (fun i => x + w i) - normalizedPeriodPrism q x (Fin.tail w))

/-- Normalized cochains evaluate the actual coned product as the ordered prism. -/
theorem formalPeriodProduct_normalized_evaluation : ∀ (q : ℕ) (x : Lattice)
    (w : Fin (q + 1) → Lattice) (f : (Fin (q + 2) → Lattice) → ℤ),
    IsNormalizedFormalCochain f →
      formalLift f (formalPeriodProduct q (formalPeriodEdge x) (formalSimplex w)) =
        formalLift f (normalizedPeriodPrism q x w) := by
  intro q
  induction q with
  | zero =>
      intro x w f _
      apply congrArg (formalLift f)
      simp only [normalizedPeriodPrism, formalPeriodProduct_apply, formalPeriodEdge,
        formalEdgeCrossProduct_zero_simplex_right, formalMap_simplex]
      apply congrArg formalSimplex
      funext i
      fin_cases i <;> simp [Function.comp_def]
  | succ q ih =>
      intro x w f hf
      let g : (Fin (q + 2) → Lattice) → ℤ := fun v => f (Fin.cons (w 0) v)
      have hg : IsNormalizedFormalCochain g := hf.cone (w 0)
      have hzero : g w = 0 := hf.first_repeat w
      have htail : w ∘ (0 : Fin (q + 2)).succAbove = Fin.tail w := rfl
      have hfaces :
          (∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
            formalLift g (formalPeriodProduct q (formalPeriodEdge x)
              (formalSimplex (w ∘ i.succAbove)))) =
            formalLift g (formalPeriodProduct q (formalPeriodEdge x)
              (formalSimplex (Fin.tail w))) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_smul, htail]
        suffices hrest :
            (∑ i : Fin (q + 1), (-1 : ℤ) ^ i.succ.val •
              formalLift g (formalPeriodProduct q (formalPeriodEdge x)
                (formalSimplex (w ∘ i.succ.succAbove)))) = 0 by
          rw [hrest, add_zero]
        apply Finset.sum_eq_zero
        intro i _
        have hfirst : (w ∘ i.succ.succAbove) 0 = w 0 := by
          simp only [Function.comp_apply, Fin.succ_succAbove_zero]
        obtain ⟨c, hc⟩ := formalPeriodProduct_edge_isCone q x (w ∘ i.succ.succAbove)
        have hz : formalLift g (formalPeriodProduct q (formalPeriodEdge x)
            (formalSimplex (w ∘ i.succ.succAbove))) = 0 := by
          rw [hc, hfirst]
          change formalLift (fun v : Fin (q + 2) → Lattice => f (Fin.cons (w 0) v))
            (formalCone (w 0) (q + 1) c) = 0
          rw [← formalLift_cone_apply]
          exact formalLift_doubleCone_eq_zero hf (w 0) c
        rw [hz, smul_zero]
      calc
        formalLift f (formalPeriodProduct (q + 1) (formalPeriodEdge x) (formalSimplex w)) =
            formalLift g (formalSimplex (fun i => x + w i) - formalSimplex w -
              ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
                formalPeriodProduct q (formalPeriodEdge x)
                  (formalSimplex (w ∘ i.succAbove))) := by
          rw [formalPeriodProduct_edge_succ, formalLift_cone_apply]
        _ = g (fun i => x + w i) - g w -
            ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
              formalLift g (formalPeriodProduct q (formalPeriodEdge x)
                (formalSimplex (w ∘ i.succAbove))) := by
          simp only [map_sub, map_sum, map_smul, formalLift_simplex]
        _ = g (fun i => x + w i) -
            formalLift g (formalPeriodProduct q (formalPeriodEdge x)
              (formalSimplex (Fin.tail w))) := by rw [hzero, sub_zero, hfaces]
        _ = g (fun i => x + w i) -
            formalLift g (normalizedPeriodPrism q x (Fin.tail w)) := by
          rw [ih x (Fin.tail w) g hg]
        _ = formalLift f (normalizedPeriodPrism (q + 1) x w) := by
          rw [normalizedPeriodPrism, formalLift_cone_apply, map_sub, formalLift_simplex]

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
