/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The cleaned DRC reservoir produces a topological clique. -/

import ErdosProblems.Erdos717.ReservoirCleanup

open Function Set
open SimpleGraph

namespace Erdos717

/-- A cleaned DRC set can route every missing pair of any sufficiently small
branch set.  The numerical hypothesis `6m+2 ≤ L` absorbs the floor in
`L/2` and the three internal vertices used by each earlier route. -/
theorem containsCliqueSubdivision_of_clean_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G)
    (S T X U : Finset V) (L : ℕ)
    (hST : H.IsBipartiteWith (S : Set V) (T : Set V))
    (hXS : X ⊆ S) (hUX : U ⊆ X)
    (hXlarge : 20 ≤ X.card) (hLsmall : 5 * L ≤ X.card)
    (hUcard : U.card = X.card / 5)
    (hclean : ∀ v ∈ U,
      4 * (badNeighborFinset H X T L v).card < X.card)
    {r : ℕ} (branch : Fin r ↪ V)
    (hbranch : Set.range branch ⊆ (U : Set V))
    (hmissing : 6 * (Finset.univ.filter fun e : Erdos718.CliqueEdge r =>
      ¬G.Adj (branch e.1.1) (branch e.1.2)).card + 2 ≤ L) :
    Erdos718.ContainsCliqueSubdivision G r := by
  classical
  let missing : Finset (Erdos718.CliqueEdge r) :=
    Finset.univ.filter fun e => ¬G.Adj (branch e.1.1) (branch e.1.2)
  change 6 * missing.card + 2 ≤ L at hmissing
  have hbranchU (i : Fin r) : branch i ∈ U := hbranch ⟨i, rfl⟩
  have endpoint_ne (e : Erdos718.CliqueEdge r) :
      branch e.1.1 ≠ branch e.1.2 := by
    intro h
    exact (ne_of_lt e.2) (branch.injective h)
  have routeFamily (e : Erdos718.CliqueEdge r) :
      ∃ C : Finset (Finset V),
        C.card = L / 2 ∧
        (C : Set (Finset V)).Pairwise Disjoint ∧
        (∀ A ∈ C, A.card ≤ 3) ∧
        (∀ A ∈ C, Nonempty
          (ShortRoute H (branch e.1.1) (branch e.1.2) A)) ∧
        (∀ A ∈ C, Disjoint (A : Set V) (U : Set V)) := by
    let R := goodIntermediateFinset H X U T L (branch e.1.1) (branch e.1.2)
    have hRcard : L ≤ R.card := by
      have hfive := five_mul_card_goodIntermediate_ge H X U T L
        hXlarge hUcard (hbranchU e.1.1) (hbranchU e.1.2)
        (hclean _ (hbranchU e.1.1)) (hclean _ (hbranchU e.1.2))
      change X.card ≤ 5 * R.card at hfive
      omega
    have hhalf : L / 2 ≤ R.card := (Nat.div_le_self L 2).trans hRcard
    obtain ⟨Q, hQR, hQcard⟩ := Finset.exists_subset_card_eq hhalf
    have hQSU : Q ⊆ S \ U := by
      intro x hx
      have hxR := hQR hx
      have hbase := (Finset.mem_filter.mp hxR).1
      have hnotW := (Finset.mem_erase.mp hbase).1
      have hbase' := (Finset.mem_erase.mp hbase).2
      have hnotV := (Finset.mem_erase.mp hbase').1
      have hXU := Finset.mem_sdiff.mp (Finset.mem_erase.mp hbase').2
      exact Finset.mem_sdiff.mpr ⟨hXS hXU.1, hXU.2⟩
    have hQavoid : ∀ x ∈ Q, x ≠ branch e.1.1 ∧ x ≠ branch e.1.2 := by
      intro x hx
      have hxR := hQR hx
      have hbase := (Finset.mem_filter.mp hxR).1
      have hnotW := (Finset.mem_erase.mp hbase).1
      have hbase' := (Finset.mem_erase.mp hbase).2
      have hnotV := (Finset.mem_erase.mp hbase').1
      exact ⟨hnotV, hnotW⟩
    have hcodegLeft : ∀ x ∈ Q,
        L ≤ (commonNeighborFinset H T (branch e.1.1) x).card := by
      intro x hx
      have hxR := hQR hx
      exact (Finset.mem_filter.mp hxR).2.1
    have hcodegRight : ∀ x ∈ Q,
        L ≤ (commonNeighborFinset H T x (branch e.1.2)).card := by
      intro x hx
      have hxR := hQR hx
      exact (Finset.mem_filter.mp hxR).2.2
    obtain ⟨C, hCcard, hCpair, hCsmall, hCroute, hCavoid⟩ :=
      exists_short_route_reservoir H S T U Q
        (branch e.1.1) (branch e.1.2) L
        (Finset.disjoint_coe.mp hST.disjoint) (hUX.trans hXS) hQSU
        (hbranchU e.1.1) (hbranchU e.1.2) (endpoint_ne e)
        hQavoid hcodegLeft hcodegRight (by rw [hQcard]; omega)
    exact ⟨C, hCcard.trans hQcard, hCpair, hCsmall, hCroute, hCavoid⟩
  let C : Erdos718.CliqueEdge r → Finset (Finset V) := fun e =>
    Classical.choose (routeFamily e)
  have hCspec (e : Erdos718.CliqueEdge r) :
      (C e).card = L / 2 ∧
      (C e : Set (Finset V)).Pairwise Disjoint ∧
      (∀ A ∈ C e, A.card ≤ 3) ∧
      (∀ A ∈ C e, Nonempty
          (ShortRoute H (branch e.1.1) (branch e.1.2) A)) ∧
      (∀ A ∈ C e, Disjoint (A : Set V) (U : Set V)) :=
    Classical.choose_spec (routeFamily e)
  apply containsCliqueSubdivision_of_short_route_reservoir G branch C
  · intro e _he
    rw [(hCspec e).1]
    change 3 * missing.card < L / 2
    omega
  · intro e _he
    exact (hCspec e).2.1
  · intro e A hA
    exact (hCspec e).2.2.1 A hA
  · intro e _he A hA
    exact ((hCspec e).2.2.2.1 A hA).map fun R => R.mapLe hHG
  · intro e _he A hA
    apply Set.disjoint_of_subset_right hbranch
    exact (hCspec e).2.2.2.2 A hA

end Erdos717
