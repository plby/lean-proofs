import ErdosProblems.Erdos421.MixedIntegerCounts

/-! # Splitting the variables without changing the integer solution count -/

namespace Erdos421

theorem mixedIntegerCount_univ_card {r N : ℕ} (A : Finset (Fin r → Fin N)) (s k : ℕ) :
    mixedIntegerCount A Finset.univ s k =
      ((vinogradovSolutions (r + s) k N 0).filter (fun z ↦
        (fun i : Fin r ↦ z.1 (Fin.castAdd s i)) ∈ A ∧
          (fun i : Fin r ↦ z.2 (Fin.castAdd s i)) ∈ A)).card := by
  classical
  let e := (Fin.appendEquiv r s : ((Fin r → Fin N) × (Fin s → Fin N)) ≃ (Fin (r + s) → Fin N))
  let E := Equiv.prodCongr e e
  unfold mixedIntegerCount
  rw [Fintype.piFinset_univ]
  apply Finset.card_bij (fun x _ ↦ E x)
  · intro x hx
    obtain ⟨hxD, heq⟩ := Finset.mem_filter.mp hx
    have hxA := (Finset.mem_product.mp (Finset.mem_product.mp hxD).1).1
    have hyA := (Finset.mem_product.mp (Finset.mem_product.mp hxD).2).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_, ?_⟩
    · change vinogradovSums k (Fin.append x.1.1 x.1.2) -
        vinogradovSums k (Fin.append x.2.1 x.2.2) = 0
      exact sub_eq_zero.mpr heq
    · change (fun i : Fin r ↦ Fin.append x.1.1 x.1.2 (Fin.castAdd s i)) ∈ A
      simpa only [Fin.append_left] using hxA
    · change (fun i : Fin r ↦ Fin.append x.2.1 x.2.2 (Fin.castAdd s i)) ∈ A
      simpa only [Fin.append_left] using hyA
  · intro x _ y _ h
    exact E.injective h
  · intro z hz
    obtain ⟨hzS, hzA⟩ := Finset.mem_filter.mp hz
    have heq := (Finset.mem_filter.mp hzS).2
    refine ⟨E.symm z, Finset.mem_filter.mpr ⟨?_, ?_⟩, E.apply_symm_apply z⟩
    · apply Finset.mem_product.mpr
      change ((fun i : Fin r ↦ z.1 (Fin.castAdd s i)),
          (fun i : Fin s ↦ z.1 (Fin.natAdd r i))) ∈ A ×ˢ Finset.univ ∧
        ((fun i : Fin r ↦ z.2 (Fin.castAdd s i)),
          (fun i : Fin s ↦ z.2 (Fin.natAdd r i))) ∈ A ×ˢ Finset.univ
      exact ⟨Finset.mem_product.mpr ⟨hzA.1, Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨hzA.2, Finset.mem_univ _⟩⟩
    · change vinogradovSums k (Fin.append (fun i ↦ z.1 (Fin.castAdd s i))
          (fun i ↦ z.1 (Fin.natAdd r i))) =
        vinogradovSums k (Fin.append (fun i ↦ z.2 (Fin.castAdd s i))
          (fun i ↦ z.2 (Fin.natAdd r i)))
      simpa only [Fin.append_castAdd_natAdd] using sub_eq_zero.mp heq

end Erdos421
