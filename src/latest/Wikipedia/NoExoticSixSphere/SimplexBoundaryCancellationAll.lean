import Wikipedia.NoExoticSixSphere.SimplexBoundaryCancellation

/-!
# Signed cancellation of coherent simplex-boundary maps in every degree

The two orders of deleting a pair of vertices give equal terms with
opposite signs. A bijection of the two index regions proves cancellation
without expanding a dimension-specific finite sum. The resulting chain
and homology identities use the original singular complexes.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexBoundaryChains

theorem alternating_sum (n : ℕ) {A : Type*} [AddCommGroup A]
    (v : Fin (n + 3) → Fin (n + 2) → A)
    (h : ∀ i j : Fin (n + 2), i ≤ j → v j.succ i = v i.castSucc j) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val •
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • v i j) = 0 := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' he
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congrArg Prod.snd he,
      by simpa [φ, Fin.castSucc_castLT] using!
        congrArg Fin.castSucc (congrArg Prod.fst he)⟩
  · rintro ⟨i, j⟩ hij
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij
    refine ⟨(j.pred ?_, Fin.castSucc i), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij
    · simpa [S] using! Nat.le_sub_one_of_lt hij
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    have hji : j.val ≤ i.val := (Finset.mem_filter.mp hij).2
    have he : v (φ (i, j) hij).2 (φ (i, j) hij).1 = v j i := by
      dsimp [φ]
      simpa only [Fin.castSucc_castLT] using
        h (j.castLT (lt_of_le_of_lt hji i.is_lt)) i hji
    dsimp only
    rw [he]
    simp only [φ, Fin.val_succ, Fin.val_castLT, smul_smul, ← neg_smul]
    congr 1
    ring

variable {X : Type} [TopologicalSpace X]

theorem chain_cancel (n : ℕ) (F : Fin (n + 3) → C(SimplexBoundary (n + 1), X))
    (h : ∀ i j : Fin (n + 2), i ≤ j →
      (F j.succ).comp (simplexFaceBoundary n i) =
        (F i.castSucc).comp (simplexFaceBoundary n j)) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • inducedChain (F i) n (chain n)) = 0 := by
  have hi (i : Fin (n + 3)) : inducedChain (F i) n (chain n) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        simplexChain X n ((F i).comp (simplexFaceBoundary n j)) := by
    rw [chain, map_sum]
    simp only [map_zsmul, inducedChain_simplex]
  simp_rw [hi]
  exact alternating_sum n (fun i j ↦ simplexChain X n ((F i).comp (simplexFaceBoundary n j)))
    (fun i j hij ↦ congrArg (simplexChain X n) (h i j hij))

theorem homology_cancel (n : ℕ) (F : Fin (n + 4) → C(SimplexBoundary (n + 2), X))
    (h : ∀ i j : Fin (n + 3), i ≤ j →
      (F j.succ).comp (simplexFaceBoundary (n + 1) i) =
        (F i.castSucc).comp (simplexFaceBoundary (n + 1) j)) :
    (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val • singularHomologyMap (F i) (n + 1)
      (ModuleHomology.cycleClass (singularComplex (SimplexBoundary (n + 2))) (n + 1)
        (cycle n))) = 0 := by
  have hc : (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val •
      ModuleHomology.mapCycles (singularChainMap (F i)) (n + 1) (cycle n)) = 0 := by
    apply Subtype.ext
    change (ModuleHomology.Cycle (singularComplex X) (n + 1)).subtype
      (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val •
        ModuleHomology.mapCycles (singularChainMap (F i)) (n + 1) (cycle n)) = 0
    simp only [map_sum, map_zsmul, Submodule.subtype_apply, ModuleHomology.mapCycles_val]
    exact chain_cancel (n + 1) F h
  have he := congrArg (ModuleHomology.cycleClass (singularComplex X) (n + 1)) hc
  simpa only [map_sum, map_zsmul, map_zero, ← ModuleHomology.homologyMap_cycleClass] using he

end NoExoticSixSphere.SimplexBoundaryChains
