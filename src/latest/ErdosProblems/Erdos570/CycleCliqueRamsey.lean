/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueLevelProof
import ErdosProblems.Erdos570.CycleCode

/-!
# The EFRS polynomial cycle--clique Ramsey bound

The deletion lemma may return a disconnected expanding region.  Restricting
to any connected component preserves its expansion property, since every
neighbor of a vertex in that component remains in the same component.  The
ordered-level theorem can then be applied without any residual hypothesis.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- An expanding induced region in a cycle-free graph contains an independent
set of the EFRS size. -/
theorem efrs_expanding_region_forces_large_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m a n : ℕ} (hm : 3 ≤ m) (ha : 1 ≤ a)
    (hn : n ≤ a ^ ((m - 1) / 2))
    (U : Finset V) (hUne : U.Nonempty)
    (hexpand : ExpandsIndependentOn G ((m - 2) * (a + 2)) U)
    (hcycle : ¬ SimpleGraph.cycleGraph m ⊑ G) :
    ∃ I : Finset V, I ⊆ U ∧ G.IsIndepSet (I : Set V) ∧ n ≤ I.card := by
  classical
  let Q : SimpleGraph U := G.induce (U : Set V)
  let u : U := ⟨hUne.choose, hUne.choose_spec⟩
  let c : Q.ConnectedComponent := Q.connectedComponentMk u
  let R : SimpleGraph c := c.toSimpleGraph
  let : DecidableRel R.Adj := Classical.decRel _
  let e : c ↪ V :=
    ⟨fun z ↦ z.1.1, by
      intro z w h
      apply Subtype.ext
      apply Subtype.ext
      exact h⟩
  have hRconn : R.Connected := c.connected_toSimpleGraph
  let : Nonempty c := hRconn.nonempty
  have hRcycle : ¬ SimpleGraph.cycleGraph m ⊑ R := by
    intro h
    apply hcycle
    let hom : R →g G :=
      { toFun := e
        map_rel' := by intro z w hzw; exact hzw }
    exact h.trans ⟨hom.toCopy e.injective⟩
  have hRexpand : ExpandsIndependentOn R ((m - 2) * (a + 2)) Finset.univ := by
    intro X _hXuniv hXind
    let X₀ : Finset V := X.map e
    have hX₀U : X₀ ⊆ U := by
      intro v hv
      obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hv
      exact z.1.2
    have hX₀ind : G.IsIndepSet (X₀ : Set V) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro v hv w hw hvw hAdj
      obtain ⟨z, hzX, hzv⟩ := Finset.mem_map.mp hv
      obtain ⟨t, htX, htw⟩ := Finset.mem_map.mp hw
      subst v
      subst w
      apply hXind hzX htX
      · intro hzt
        exact hvw (congrArg e hzt)
      · exact hAdj
    have hExp := hexpand X₀ hX₀U hX₀ind
    let N₀ := relativeNeighborFinset G U X₀
    let liftNeighbor : ↑N₀ → c := fun y ↦
      ⟨⟨y.1, (mem_relativeNeighborFinset.mp y.2).1⟩, by
        obtain ⟨z₀, hz₀X, hz₀y⟩ :=
          (mem_relativeNeighborFinset.mp y.2).2
        obtain ⟨z, hzX, hzeq⟩ := Finset.mem_map.mp hz₀X
        have hzmem : z.1 ∈ c.supp := z.2
        have hAdjQ : Q.Adj z.1 ⟨y.1, (mem_relativeNeighborFinset.mp y.2).1⟩ := by
          rw [← hzeq] at hz₀y
          exact hz₀y
        exact c.mem_supp_of_adj_mem_supp hzmem hAdjQ⟩
    have hliftIn : ∀ y : ↑N₀,
        liftNeighbor y ∈ relativeNeighborFinset R Finset.univ X := by
      intro y
      apply mem_relativeNeighborFinset.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨z₀, hz₀X, hz₀y⟩ :=
        (mem_relativeNeighborFinset.mp y.2).2
      obtain ⟨z, hzX, hzeq⟩ := Finset.mem_map.mp hz₀X
      refine ⟨z, hzX, ?_⟩
      rw [← hzeq] at hz₀y
      exact hz₀y
    have hliftInj : Function.Injective liftNeighbor := by
      intro y z hyz
      apply Subtype.ext
      exact congrArg (fun w : c ↦ w.1.1) hyz
    have hNcard : N₀.card ≤
        (relativeNeighborFinset R Finset.univ X).card := by
      let mapN : ↑N₀ ↪ ↑(relativeNeighborFinset R Finset.univ X) :=
        ⟨fun y ↦ ⟨liftNeighbor y, hliftIn y⟩, fun y z h ↦
          hliftInj (congrArg Subtype.val h)⟩
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective mapN mapN.injective
    have hXcard : X₀.card = X.card := by simp [X₀]
    simpa only [hXcard, N₀] using hExp.trans hNcard
  obtain ⟨J, hJind, hnJ⟩ := efrs_expansion_forces_large_independent
    R hm ha hn hRconn (cycleLevelIndependent_of_connected R hRconn hm)
      hRcycle hRexpand
  let I : Finset V := J.map e
  refine ⟨I, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hv
    exact z.1.2
  · rw [SimpleGraph.isIndepSet_iff]
    intro v hv w hw hvw hAdj
    obtain ⟨z, hzJ, hzv⟩ := Finset.mem_map.mp hv
    obtain ⟨t, htJ, htw⟩ := Finset.mem_map.mp hw
    subst v
    subst w
    apply hJind hzJ htJ
    · intro hzt
      exact hvw (congrArg e hzt)
    · exact hAdj
  · simpa [I] using hnJ

/-- Explicit EFRS bound: if `n ≤ a^floor((m-1)/2)`, then
`R(C_m,K_n) ≤ ((m-2)(a+2)+1)(n-1)`. -/
theorem ramseyAt_cycle_complete_efrs
    {m a n : ℕ} (hm : 3 ≤ m) (ha : 1 ≤ a) (hn₂ : 2 ≤ n)
    (hn : n ≤ a ^ ((m - 1) / 2)) :
    RamseyAt (cycleCode m) (completeCode n)
      (((m - 2) * (a + 2) + 1) * (n - 1)) := by
  intro C
  classical
  let : DecidableRel C.Adj := Classical.decRel _
  by_cases hred : SimpleGraph.cycleGraph m ⊑ C
  · exact Or.inl (by simpa [cycleCode] using hred)
  · by_cases hblue : (⊤ : SimpleGraph (Fin n)) ⊑ Cᶜ
    · exact Or.inr (by simpa [completeCode] using hblue)
    have hfree : ∀ I : Finset (Fin (((m - 2) * (a + 2) + 1) * (n - 1))),
        I ⊆ Finset.univ → C.IsIndepSet (I : Set _) → I.card < n := by
      intro I _ hI
      by_contra hnot
      have hnI : n ≤ I.card := Nat.le_of_not_gt hnot
      obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hnI
      have hJind : C.IsIndepSet (J : Set _) := by
        intro x hx y hy hxy
        exact hI (hJI hx) (hJI hy) hxy
      have hClique : Cᶜ.IsNClique n J := by
        refine ⟨?_, hJcard⟩
        simpa using hJind
      have htop : (⊤ : SimpleGraph (Fin n)) ⊑ Cᶜ :=
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp
          hClique.not_cliqueFree
      exact hblue htop
    obtain ⟨U, -, hUne, hUexp⟩ :=
      exists_expanding_subregion_of_no_large_independent C
        (l := (m - 2) * (a + 2)) (n := n) Finset.univ hn₂ (by simp) hfree
    obtain ⟨I, -, hIind, hnI⟩ :=
      efrs_expanding_region_forces_large_independent C hm ha hn U hUne hUexp hred
    obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hnI
    have hJind : C.IsIndepSet (J : Set _) := by
      intro x hx y hy hxy
      exact hIind (hJI hx) (hJI hy) hxy
    have hClique : Cᶜ.IsNClique n J := by
      refine ⟨?_, hJcard⟩
      simpa using hJind
    exact hblue ((SimpleGraph.not_cliqueFree_iff_top_isContained n).mp
      hClique.not_cliqueFree) |>.elim

theorem graphRamseyNumber_cycle_complete_le_efrs
    {m a n : ℕ} (hm : 3 ≤ m) (ha : 1 ≤ a) (hn₂ : 2 ≤ n)
    (hn : n ≤ a ^ ((m - 1) / 2)) :
    graphRamseyNumber (cycleCode m) (completeCode n) ≤
      ((m - 2) * (a + 2) + 1) * (n - 1) :=
  graphRamseyNumber_le_of_ramseyAt
    (ramseyAt_cycle_complete_efrs hm ha hn₂ hn)

end Erdos570
