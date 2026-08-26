import ErdosProblems.Erdos547.ShrubHostRoots
import ErdosProblems.Erdos547.ShrubHostMonotone
import ErdosProblems.Erdos547.ShrubRegularStep

/-!
# The common insertion step for the private-root and reservoir-root phases
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem step_from_root (E : H.State) (F F' : Finset ↥P.shrubs) (hFF : F' ⊆ F)
    (hEF : Disjoint E.placed F)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (hreserved : Disjoint E.occupied (H.reserved F'))
    (S : ↥P.shrubs) (hS : S ∉ E.placed) (j : I) (hj : H.IsTarget E S j)
    (hused : ((H.reservoir (H.head S) ∩ E.occupied).card : ℝ) ≤ 4 * H.ε * H.m)
    (v : V) (hv : v ∈ H.clusters (H.head S)) (hvbad : v ∉ E.occupied ∪ H.reserved F')
    (hvseed : G.Adj (H.seed (H.roots S).seed) v)
    (hroot : 2 * H.ε * H.m ≤ (degreeIn G (H.free E F j) v : ℝ))
    (p : Prop) [Decidable p] (hprimaryQ : v ∈ H.reservoir (H.head S) → p) :
    ∃ E' : H.State,
      E'.placed = insert S E.placed ∧ E'.tail = Function.update E.tail S j ∧
      E.occupied ⊆ E'.occupied ∧ Disjoint E'.occupied (H.reserved F') ∧
      (∀ a i, (E'.farLoad a i : ℝ) ≤ H.capacity a i) ∧
      ∀ i, (H.reservoir i ∩ E'.occupied).card ≤ (H.reservoir i ∩ E.occupied).card +
        (if H.head S = i ∧ p then 1 else 0) + (if (H.roots S).second.isSome then 1 else 0) := by
  classical
  obtain ⟨R, hR, hRbad, hRA, hvR, hRsize⟩ := H.secondary_for_state E F S v hused
  have hreg := H.target_regular E S j hj
  have hfutureSub : E.occupied ∪ H.reserved F' ⊆ E.occupied ∪ H.reserved F := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ (H.reserved_mono hFF hw)
  have hRcluster : R ⊆ H.clusters (H.head S) :=
    hR.trans ((H.secondary_sub S).trans (H.reservoir_sub _))
  have heq : (H.clusters (H.head S)).card = (H.clusters j).card := by rw [H.cluster_card, H.cluster_card]
  have hAsize : H.η * ((H.clusters (H.head S)).card : ℝ) ≤ (H.free E F (H.head S)).card := by
    simpa only [H.cluster_card] using H.free_size E F hEF hcap (H.head S)
  have hBsize : H.η * ((H.clusters (H.head S)).card : ℝ) ≤ (H.free E F j).card := by
    simpa only [H.cluster_card] using H.free_size E F hEF hcap j
  have hRsize' : 2 * H.ε * ((H.clusters (H.head S)).card : ℝ) ≤ R.card := by
    simpa only [H.cluster_card] using hRsize
  have hsmall : (S.val.card : ℝ) ≤ H.ε * (H.clusters (H.head S)).card := by
    simpa only [H.cluster_card] using H.shrub_small S
  have hroot' : 2 * H.ε * (H.clusters (H.head S)).card ≤ (degreeIn G (H.free E F j) v : ℝ) := by
    simpa only [H.cluster_card] using hroot
  obtain ⟨E', hplaced, htail, hmono, hreserved', hcount⟩ := E.exists_regular_insert
    S hS j (H.roots S) H.reservoir H.reservoir_sub H.cluster_disjoint
    (H.reserved F') (H.free E F (H.head S)) (H.free E F j) R hreserved
    hreg.1 hreg.2.1 heq hreg.2.2 H.η_nonneg H.degree_margin H.embedding_margin
    (H.free_sub E F (H.head S)) (H.free_sub E F j) hRcluster hRA
    hAsize hBsize hRsize' hsmall v hv hvR hroot' hvbad
    ((H.free_avoid_used_reserved E F (H.head S)).mono_right hfutureSub)
    ((H.free_avoid_used_reserved E F j).mono_right hfutureSub)
    (hRbad.mono_right hfutureSub)
    (H.free_avoid_reservoir E F (H.head S)) (H.free_avoid_reservoir E F j)
    hvseed (fun z hz w hw ↦ H.secondary_adj S z hz w (hR hw)) p hprimaryQ
  have hsmallcap : ((P.farPart S).card : ℝ) ≤
      H.slack / 4 * H.capacity (ShrubState.shrubGroup P H.head S) j :=
    (H.target_shrub_margin S).trans
      (mul_le_mul_of_nonneg_left hj.1 (div_nonneg H.slack_pos.le (by norm_num)))
  have hcap' := E.capacities_after_insert E' S hS j hplaced htail H.capacity H.slack hcap
    (H.targetFloor_pos.trans_le hj.1) H.slack_pos hj.2 hsmallcap
  exact ⟨E', hplaced, htail, hmono, hreserved', hcap', hcount⟩

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.step_from_root
