import Arxiv.Arxiv2411_18291.CliqueCodegree
import Arxiv.Arxiv2411_18291.FiniteUnionOverlap

/-!
# Exact one-step clique removal and its overlap error

Deleting a selected clique discards every available clique sharing an
edge with it. The union of edge neighborhoods counts these discarded
cliques exactly; pair codegrees bound the error from multiple counting.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def cliqueNeighborhood (r : ℕ) (H : Finset (Block V q)) (Q : Block V q) : Finset (Block V q) :=
  (cliqueEdges r Q).biUnion fun e => H.filter fun P => e.val ⊆ P.val

def cliqueRemoval (r : ℕ) (H : Finset (Block V q)) (Q : Block V q) : Finset (Block V q) :=
  H \ cliqueNeighborhood r H Q

theorem mem_cliqueNeighborhood {H : Finset (Block V q)} {P Q : Block V q} :
    P ∈ cliqueNeighborhood r H Q ↔
      P ∈ H ∧ ∃ e : Block V r, e.val ⊆ Q.val ∧ e.val ⊆ P.val := by
  simp only [cliqueNeighborhood, mem_biUnion, mem_cliqueEdges, mem_filter]
  constructor
  · rintro ⟨e, heQ, hPH, heP⟩
    exact ⟨hPH, e, heQ, heP⟩
  · rintro ⟨hPH, e, heQ, heP⟩
    exact ⟨e, heQ, hPH, heP⟩

theorem cliqueNeighborhood_subset (H : Finset (Block V q)) (Q : Block V q) :
    cliqueNeighborhood r H Q ⊆ H := fun _ h => (mem_cliqueNeighborhood.mp h).1

theorem cliqueRemoval_subset (H : Finset (Block V q)) (Q : Block V q) :
    cliqueRemoval r H Q ⊆ H := sdiff_subset

theorem card_cliqueRemoval_add (H : Finset (Block V q)) (Q : Block V q) :
    (cliqueRemoval r H Q).card + (cliqueNeighborhood r H Q).card = H.card :=
  card_sdiff_add_card_eq_card (cliqueNeighborhood_subset H Q)

theorem mem_cliqueRemoval {H : Finset (Block V q)} {P Q : Block V q} :
    P ∈ cliqueRemoval r H Q ↔ P ∈ H ∧ Disjoint (cliqueEdges r P) (cliqueEdges r Q) := by
  simp only [cliqueRemoval, mem_sdiff, mem_cliqueNeighborhood]
  constructor
  · rintro ⟨hPH, hn⟩
    refine ⟨hPH, disjoint_left.mpr ?_⟩
    intro e heP heQ
    exact hn ⟨hPH, e, (mem_cliqueEdges _ _).mp heQ, (mem_cliqueEdges _ _).mp heP⟩
  · rintro ⟨hPH, hd⟩
    refine ⟨hPH, ?_⟩
    rintro ⟨_, e, heQ, heP⟩
    exact disjoint_left.mp hd ((mem_cliqueEdges _ _).mpr heP) ((mem_cliqueEdges _ _).mpr heQ)

theorem cliqueNeighborhood_card_le_sum (H : Finset (Block V q)) (Q : Block V q) :
    (cliqueNeighborhood r H Q).card ≤
      ∑ e ∈ cliqueEdges r Q, (H.filter fun P => e.val ⊆ P.val).card := card_biUnion_le

theorem cliqueNeighborhood_sum_le_card_add_error (hqr : r < q)
    (H : Finset (Block V q)) (Q : Block V q) :
    (∑ e ∈ cliqueEdges r Q, (H.filter fun P => e.val ⊆ P.val).card) ≤
      (cliqueNeighborhood r H Q).card + (q.choose r) ^ 2 * (Fintype.card V) ^ (q - r - 1) := by
  have hpair : ∀ e ∈ cliqueEdges r Q, ∀ f ∈ cliqueEdges r Q, e ≠ f →
      ((H.filter fun P => e.val ⊆ P.val) ∩ (H.filter fun P => f.val ⊆ P.val)).card ≤
        (Fintype.card V) ^ (q - r - 1) := by
    intro e _ f _ hef
    have heq : (H.filter fun P => e.val ⊆ P.val) ∩ (H.filter fun P => f.val ⊆ P.val) =
        H.filter fun P => e.val ⊆ P.val ∧ f.val ⊆ P.val := by
      ext P
      simp only [mem_inter, mem_filter]
      tauto
    rw [heq]
    exact clique_codegree_le_power hqr H e f hef
  simpa only [cliqueNeighborhood, card_cliqueEdges] using
    sum_card_le_biUnion_card_add_sq (cliqueEdges r Q)
      (fun e => H.filter fun P => e.val ⊆ P.val) ((Fintype.card V) ^ (q - r - 1)) hpair

end Arxiv2411_18291
