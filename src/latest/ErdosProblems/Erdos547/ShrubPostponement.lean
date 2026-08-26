import ErdosProblems.Erdos547.ShrubHostMonotone
import ErdosProblems.Erdos547.PostponedMass
import ErdosProblems.Erdos547.ShrubReservoirCount

/-!
# Failed private roots persist and bound the postponed near-class mass
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

def FailedAt (E : H.State) (F : Finset ↥P.shrubs) (S : ↥P.shrubs) : Prop :=
  ∀ j, H.IsTarget E S j → ∀ v ∈ H.privateSet S,
    (degreeIn G (H.free E F j) v : ℝ) < 2 * H.ε * H.m

theorem failedAt_after_release (E E' : H.State) (F : Finset ↥P.shrubs)
    (S A : ↥P.shrubs) (hhead : H.head S = H.head A)
    (hused : E.occupied ⊆ E'.occupied) (hload : ∀ a i, E.farLoad a i ≤ E'.farLoad a i)
    (hfailed : H.FailedAt E F A) : H.FailedAt E' (F.erase S) A := by
  intro j hj v hv
  have htarget := H.targets_shrink E E' hload A j hj
  have hdis : Disjoint (H.clusters j) (H.clusters (H.head S)) := by
    rw [hhead]
    exact (H.target_regular E' A j hj).2.1.symm
  have hfree := H.free_mono_after_release E E' F S j hused hdis
  have hdeg : (degreeIn G (H.free E' (F.erase S) j) v : ℝ) ≤
      (degreeIn G (H.free E F j) v : ℝ) := by exact_mod_cast degreeIn_mono G hfree v
  exact hdeg.trans_lt (hfailed j htarget v hv)

theorem failedAt_after_removal (E E' : H.State) (F L : Finset ↥P.shrubs)
    (i : I) (hhead : ∀ S ∈ L, H.head S = i) (A : ↥P.shrubs) (hA : H.head A = i)
    (hused : E.occupied ⊆ E'.occupied) (hload : ∀ a j, E.farLoad a j ≤ E'.farLoad a j)
    (hfailed : H.FailedAt E F A) : H.FailedAt E' (F \ L) A := by
  intro j hj v hv
  have htarget := H.targets_shrink E E' hload A j hj
  have hdis : Disjoint (H.clusters j) (H.clusters i) := by
    rw [← hA]
    exact (H.target_regular E' A j hj).2.1.symm
  have hfree := available_mono_away_from_released_set (H.clusters j) (H.clusters i)
    (H.reservoir j) E.occupied E'.occupied (H.reserved F) (H.reserved (F \ L))
    hdis hused (H.reserved_sdiff_release F L i hhead)
  have hdeg : (degreeIn G (H.free E' (F \ L) j) v : ℝ) ≤
      (degreeIn G (H.free E F j) v : ℝ) := by exact_mod_cast degreeIn_mono G hfree v
  exact hdeg.trans_lt (hfailed j htarget v hv)

theorem postponed_group_mass (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F) (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (B : Finset ↥P.shrubs) (S : ↥P.shrubs)
    (hgroup : ∀ A ∈ B, ShrubState.shrubGroup P H.head A = ShrubState.shrubGroup P H.head S)
    (hfailed : ∀ A ∈ B, H.FailedAt E F A) :
    (∑ A ∈ B, ((P.nearPart A).card : ℝ)) ≤ H.ε * H.m := by
  obtain ⟨j, hj⟩ := H.exists_target E S
  have hreg := H.target_regular E S j hj
  have hfree := H.target_free_room E F hEF hcap S j hj
  have hhead (A : ↥P.shrubs) (hA : A ∈ B) : H.head A = H.head S :=
    congrArg Prod.snd (hgroup A hA)
  have hRX (A : ↥P.shrubs) (hA : A ∈ B) : H.privateSet A ⊆ H.clusters (H.head S) := by
    rw [← hhead A hA]
    exact H.private_sub A
  have hfailed' (A : ↥P.shrubs) (hA : A ∈ B) (v : V) (hv : v ∈ H.privateSet A) :
      (degreeIn G (H.free E F j) v : ℝ) < 2 * H.ε * H.m := by
    apply hfailed A hA j _ v hv
    change H.targetFloor ≤ H.capacity (ShrubState.shrubGroup P H.head A) j ∧
      (E.farLoad (ShrubState.shrubGroup P H.head A) j : ℝ) <
        (1 - H.slack / 2) * H.capacity (ShrubState.shrubGroup P H.head A) j
    rw [hgroup A hA]
    exact hj
  have hh := postponed_private_mass_le G (H.clusters (H.head S)) (H.clusters j)
    (H.free E F j) H.ε (2 * H.ε * H.m) hreg.1 (H.free_sub E F j)
    (by simpa only [H.cluster_card] using hfree.1) hfree.2 B H.privateSet hRX
    (fun A _ A' _ hAA' ↦ H.private_disjoint A A' hAA') hfailed'
  simpa only [H.private_card, H.cluster_card, mul_comm H.ε] using hh

theorem postponed_group_count (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F) (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (B : Finset ↥P.shrubs) (S : ↥P.shrubs)
    (hgroup : ∀ A ∈ B, ShrubState.shrubGroup P H.head A = ShrubState.shrubGroup P H.head S)
    (hfailed : ∀ A ∈ B, H.FailedAt E F A) : (B.card : ℝ) ≤ H.ε * H.m := by
  have hn := card_postponed_le_near_mass B (fun A ↦ (P.nearPart A).card)
    (fun A _ ↦ (P.nearPart_nonempty A).card_pos)
  have hcast : (B.card : ℝ) ≤ ∑ A ∈ B, ((P.nearPart A).card : ℝ) := by exact_mod_cast hn
  exact hcast.trans (H.postponed_group_mass E F hEF hcap B S hgroup hfailed)

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.failedAt_after_release
#print axioms Erdos547.ShrubHostSetup.postponed_group_count
