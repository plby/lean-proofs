import ErdosProblems.Erdos73.ControlledWallRows
import ErdosProblems.Erdos73.HavenRegions

/-! A terminal on each of many disjoint controlled rows meets every small-deletion haven region. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g n : ℕ}

theorem WallGridAnchor.row_terminals_meet_region
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    (hM : NoGridRowInHavenSmallSide h M) (hg : 2 ≤ g)
    (N : Finset V) (J : Finset (Fin g)) {u : ℕ} (hJ : u ≤ J.card)
    (hrows : ∀ r ∈ J, ∃ v ∈ N, v ∈ interiorWallRowSupport S hg r)
    (K : {X : Finset V // X.card < q}) (hK : K.val.card < u) :
    ∃ v ∈ N, v ∈ h.region K := by
  have hUg : u ≤ g := hJ.trans (by simpa only [Fintype.card_fin] using Finset.card_le_univ J)
  have hex : ∃ r ∈ J, Disjoint (interiorWallRowSupport S hg r) K.val := by
    by_contra hn
    push Not at hn
    have hhit : ∀ r ∈ J, ∃ v ∈ interiorWallRowSupport S hg r, v ∈ K.val := by
      intro r hr
      exact Finset.not_disjoint_iff.mp (hn r hr)
    have hbound := card_le_of_pairwise_disjoint_hits J (interiorWallRowSupport S hg) K.val
      (fun _ _ _ _ hrs => interiorWallRowSupport_disjoint S hg hrs) hhit
    omega
  obtain ⟨r, hr, hdis⟩ := hex
  have hsub : interiorWallRowSupport S hg r ⊆ h.region K :=
    h.controlled_connected_subset_region K (hK.trans_le hUg)
      (interiorWallRowSupport S hg r) (interiorWallRowSupport_connected S hg r) hdis
      (fun C D hCD hsmall hpoint => A.interiorRow_not_subset_smallSide hM hg hCD hsmall hpoint r)
  obtain ⟨v, hvN, hvr⟩ := hrows r hr
  exact ⟨v, hvN, hsub hvr⟩

end
end Erdos73
