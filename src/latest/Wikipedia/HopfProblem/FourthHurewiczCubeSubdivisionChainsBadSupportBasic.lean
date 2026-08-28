import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalSupport

/-!
# Boundary-supported formal prism corrections

The bad-prism submodule consists of sums of chains supported at the initial
left endpoint and chains omitting one fixed noninitial right vertex. The
omitted vertex may differ between summands. This is a submodule of the
original ordered formal chains, not a normalization quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Initial-endpoint chains and chains omitting a noninitial right vertex. -/
def badPrism (q m : ℕ) : Submodule ℤ (FormalChains (Fin 2 × Fin (q + 1)) m) :=
  formalChainsSupported {z | z.1 = 0} m ⊔
    ⨆ i : {i : Fin (q + 1) // i ≠ 0}, formalChainsSupported {z | z.2 ≠ i.val} m

/-- Chains at the initial left endpoint belong to the correction submodule. -/
theorem mem_badPrism_of_left_zero {q m : ℕ}
    {c : FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ formalChainsSupported {z | z.1 = 0} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_left hc

/-- Omitting any one noninitial right vertex suffices. -/
theorem mem_badPrism_of_omit {q m : ℕ} (i : Fin (q + 1)) (hi : i ≠ 0)
    {c : FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ formalChainsSupported {z | z.2 ≠ i} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨i, hi⟩ hc)

/-- To contain the correction submodule, it suffices to contain each of its
vertex-supported components. -/
theorem badPrism_le {q m : ℕ} {P : Submodule ℤ (FormalChains (Fin 2 × Fin (q + 1)) m)}
    (hzero : formalChainsSupported {z | z.1 = 0} m ≤ P)
    (homit : ∀ i : Fin (q + 1), i ≠ 0 → formalChainsSupported {z | z.2 ≠ i} m ≤ P) :
    badPrism q m ≤ P :=
  sup_le hzero (iSup_le fun i => homit i.val i.property)

/-- A linear map kills the entire correction submodule if it kills its
initial-endpoint and omitted-vertex simplex generators. -/
theorem badPrism_le_ker {q m : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : FormalChains (Fin 2 × Fin (q + 1)) m →ₗ[ℤ] M)
    (hzero : ∀ v, (∀ j, (v j).1 = 0) → f (formalSimplex v) = 0)
    (homit : ∀ i : Fin (q + 1), i ≠ 0 →
      ∀ v, (∀ j, (v j).2 ≠ i) → f (formalSimplex v) = 0) :
    badPrism q m ≤ LinearMap.ker f := by
  apply badPrism_le
  · exact formalChainsSupported_le hzero
  · intro i hi
    exact formalChainsSupported_le (homit i hi)

/-- Coning to the initial pair preserves all the correction components. -/
theorem formalCone_mem_badPrism {q m : ℕ}
    {c : FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    formalCone (0, 0) m c ∈ badPrism q (m + 1) := by
  have hle : badPrism q m ≤
      (badPrism q (m + 1)).comap (formalCone (0, 0) m) := by
    apply badPrism_le
    · intro d hd
      exact mem_badPrism_of_left_zero
        (formalCone_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
          (a := (0, 0)) rfl hd)
    · intro i hi d hd
      exact mem_badPrism_of_omit i hi (formalCone_mem_supported (Ne.symm hi) hd)
  exact hle hc

/-- Shifting all right vertices to successors preserves the correction
condition; any previously omitted vertex remains noninitial. -/
theorem formalMap_succ_mem_badPrism {q m : ℕ}
    {c : FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m c ∈
      badPrism (q + 1) m := by
  have hle : badPrism q m ≤ (badPrism (q + 1) m).comap
      (formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m) := by
    apply badPrism_le
    · intro d hd
      apply mem_badPrism_of_left_zero
      exact formalMap_mem_supported
        (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
        (T := {z : Fin 2 × Fin (q + 2) | z.1 = 0})
        (Prod.map id Fin.succ) (fun _ hz => hz) hd
    · intro i hi d hd
      apply mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i)
      exact formalMap_mem_supported
        (S := {z : Fin 2 × Fin (q + 1) | z.2 ≠ i})
        (T := {z : Fin 2 × Fin (q + 2) | z.2 ≠ i.succ})
        (Prod.map id Fin.succ) (fun _ hz h => hz (Fin.succ_injective _ h)) hd
  exact hle hc

/-- The original recursive edge product preserves an omitted right vertex. -/
theorem formalEdgeCrossProduct_mem_badPrism_of_omit {q r : ℕ}
    (i : Fin (q + 1)) (hi : i ≠ 0) (c : FormalChains (Fin 2) 2)
    {d : FormalChains (Fin (q + 1)) (r + 1)}
    (hd : d ∈ formalChainsSupported {j | j ≠ i} (r + 1)) :
    formalEdgeCrossProduct r c d ∈ badPrism q (r + 2) := by
  apply mem_badPrism_of_omit i hi
  apply formalChainsSupported_mono
    (S := (Set.univ : Set (Fin 2)) ×ˢ {j : Fin (q + 1) | j ≠ i}) (fun _ hz => hz.2)
  exact formalEdgeCrossProduct_mem_supported r
    (S := Set.univ) (by simp) hd

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
