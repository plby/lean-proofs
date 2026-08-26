import ErdosProblems.Erdos421.VinogradovCounts

/-! # Interval monotonicity and the elementary upper bound for the counts -/

namespace Erdos421

theorem vinogradovCount_le_trivial (s k N : ℕ) : vinogradovCount s k N ≤ N ^ (2 * s) := by
  have h := Finset.card_filter_le
    (Finset.univ : Finset ((Fin s → Fin N) × (Fin s → Fin N)))
    (fun p ↦ vinogradovSums k p.1 - vinogradovSums k p.2 = 0)
  simpa only [vinogradovCount, vinogradovSolutions, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, ← pow_add, ← two_mul] using h

theorem vinogradovCount_mono {N M : ℕ} (hNM : N ≤ M) (s k : ℕ) :
    vinogradovCount s k N ≤ vinogradovCount s k M := by
  let F : ((Fin s → Fin N) × (Fin s → Fin N)) → ((Fin s → Fin M) × (Fin s → Fin M)) :=
    fun p ↦ (fun i ↦ Fin.castLE hNM (p.1 i), fun i ↦ Fin.castLE hNM (p.2 i))
  apply Finset.card_le_card_of_injOn F
  · intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change vinogradovSums k p.1 - vinogradovSums k p.2 = 0
    exact (Finset.mem_filter.mp hp).2
  · intro p _ t _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · funext i
      exact Fin.ext (congrArg (fun x : Fin M ↦ x.val) (congrFun h1 i))
    · funext i
      exact Fin.ext (congrArg (fun x : Fin M ↦ x.val) (congrFun h2 i))

end Erdos421
