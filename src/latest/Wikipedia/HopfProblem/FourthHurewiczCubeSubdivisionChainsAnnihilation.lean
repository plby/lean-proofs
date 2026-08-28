import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsRealization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsBadSupport

/-!
# Signed cube realization annihilates the recursive prism correction

A missing interior right vertex gives identical affine simplices for a
pair of opposite-sign coordinate permutations. A missing last vertex or
a fixed initial time coordinate gives a genuine cube-boundary simplex.
Thus the entire correction submodule vanishes in actual singular chains,
in every right-cube dimension at least two.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] {x : X}

theorem orientedPrismRealization_left_zero {m n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).1 = 0) :
    orientedPrismRealization p.val m (formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
      p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨0, Or.inl (prismCubeSimplex_zero_of_left_zero e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem orientedPrismRealization_last_omitted {m n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 2)) :
    orientedPrismRealization p.val m (formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
      p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨(e (Fin.last (n + 1))).succ,
      Or.inl (prismCubeSimplex_zero_of_last_omitted e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem orientedPrismRealization_interior_omitted {m n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 1))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    orientedPrismRealization p.val m (formalSimplex v) = 0 := by
  rw [orientedPrismRealization_simplex]
  apply signed_sum_eq_zero_of_swap_invariant i.castSucc i.succ
    (by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega)
  intro e
  exact congrArg (fun f => simplexChain X m (p.val.comp f))
    (prismCubeSimplex_swap_of_omitted e i v hv).symm

theorem orientedPrismRealization_nonzero_omitted {m n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 3)) (hi : i ≠ 0)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i) :
    orientedPrismRealization p.val m (formalSimplex v) = 0 := by
  by_cases hlast : i = Fin.last (n + 2)
  · subst i
    exact orientedPrismRealization_last_omitted p v hv
  have hi0 : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hilast : i.val ≠ n + 2 := by
    intro h
    exact hlast (Fin.ext h)
  have hi_lt := i.isLt
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hj : j.succ.castSucc = i := by
    apply Fin.ext
    dsimp [j]
    omega
  apply orientedPrismRealization_interior_omitted p j v
  simpa only [hj] using hv

/-- The original singular-chain realization kills all recursive correction components. -/
theorem badPrism_le_ker_orientedPrismRealization {n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x) (m : ℕ) :
    badPrism (n + 2) (m + 1) ≤ LinearMap.ker (orientedPrismRealization p.val m) :=
  badPrism_le_ker _ (fun v hv => orientedPrismRealization_left_zero p v hv)
    (fun i hi v hv => orientedPrismRealization_nonzero_omitted p i hi v hv)

theorem orientedPrismRealization_canonicalPrismDiscrepancy {n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3) (canonicalPrismDiscrepancy (n + 2)) = 0 :=
  badPrism_le_ker_orientedPrismRealization p (n + 3)
    (canonicalPrismDiscrepancy_mem_badPrism (n + 2))

/-- The genuine recursive cross product and the shuffle prism have exactly
the same signed native cube realization, before passing to homology. -/
theorem orientedPrismRealization_edge_eq_standard {n : ℕ}
    (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3)
        (formalEdgeCrossProduct (n + 2) (formalSimplex (fun i : Fin 2 => i))
          (formalSimplex (fun j : Fin (n + 3) => j))) =
      orientedPrismRealization p.val (n + 3)
        (standardPrism (n + 2) (fun i : Fin 2 => i) (fun j : Fin (n + 3) => j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact orientedPrismRealization_canonicalPrismDiscrepancy p

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
