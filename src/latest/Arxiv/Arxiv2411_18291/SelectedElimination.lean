import Arxiv.Arxiv2411_18291.EliminationDisjointness

/-!
# Selecting elimination copies without changing the boundary

Disjoint replacement families let a selected set of exchange copies act on
sets of signed cliques. If neither root is repeated, the replacements have
exactly the boundary of the removed positive and negative roots.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem indicator_biUnion_of_disjoint {I K : Type*} [DecidableEq K]
    (s : Finset I) (T : I → Finset K)
    (hdis : (s : Set I).Pairwise fun i j => Disjoint (T i) (T j)) :
    indicator (s.biUnion T) = ∑ i ∈ s, indicator (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hid : Disjoint (T i) (s.biUnion T) := (disjoint_biUnion_right _ _ _).mpr (by
      intro j hj
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hi).symm)
    rw [biUnion_insert, indicator_union hid, sum_insert hi]
    rw [ih (fun _ hj _ hk hjk => hdis (mem_insert_of_mem hj) (mem_insert_of_mem hk) hjk)]

theorem indicator_image_of_injOn {I K : Type*} [DecidableEq K]
    (s : Finset I) (f : I → K) (hinj : Set.InjOn f s) :
    indicator (s.image f) = ∑ i ∈ s, indicator {f i} := by
  have hdis : (s : Set I).Pairwise fun i j => Disjoint ({f i} : Finset K) {f j} := by
    intro i hi j hj hij
    simpa only [disjoint_singleton] using fun h => hij (hinj hi hj h)
  simpa only [biUnion_singleton] using indicator_biUnion_of_disjoint s (fun i => {f i}) hdis

variable {W V I : Type*} [Fintype W] [Fintype V] [Fintype I]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

def EliminationFamily.selectedPositive (F : EliminationFamily S N B P Q θ) (s : Finset I) :=
  s.biUnion fun i => mapGraph (F.embedding i) (S.eliminationPositive N)

def EliminationFamily.selectedNegative (F : EliminationFamily S N B P Q θ) (s : Finset I) :=
  s.biUnion fun i => mapGraph (F.embedding i) S.eliminationNegative

theorem EliminationFamily.selectedPositive_subset (F : EliminationFamily S N B P Q θ)
    (s : Finset I) : F.selectedPositive s ⊆ F.positiveCliques :=
  biUnion_subset_biUnion_of_subset_left _ (subset_univ s)

theorem EliminationFamily.selectedNegative_subset (F : EliminationFamily S N B P Q θ)
    (s : Finset I) : F.selectedNegative s ⊆ F.negativeCliques :=
  biUnion_subset_biUnion_of_subset_left _ (subset_univ s)

theorem EliminationFamily.copy_boundary (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) :
    boundary (r + 1) (indicator (mapGraph (F.embedding i) (S.eliminationPositive N)) -
      indicator (mapGraph (F.embedding i) S.eliminationNegative)) =
      indicator (cliqueEdges (r + 1) (P i)) - indicator (cliqueEdges (r + 1) (Q i)) := by
  have hN : mapBlock (F.embedding i) N ∈ (S.map (F.embedding i)).negative :=
    (mem_mapGraph _ _ _).mpr ⟨N, hpair.negative_mem, rfl⟩
  have h := (S.map (F.embedding i)).boundary_elimination hN
  simpa only [ExchangeSystem.eliminationVector, ExchangeSystem.eliminationPositive,
    ExchangeSystem.eliminationNegative, ExchangeSystem.map, mapGraph_erase,
    F.positive_root, F.negative_root] using h

theorem EliminationFamily.selected_boundary (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (s : Finset I)
    (hP : Set.InjOn P s) (hQ : Set.InjOn Q s) :
    boundary (r + 1) (indicator (F.selectedPositive s) - indicator (F.selectedNegative s)) =
      boundary (r + 1) (indicator (s.image P) - indicator (s.image Q)) := by
  have hp : (s : Set I).Pairwise fun i j =>
      Disjoint (mapGraph (F.embedding i) (S.eliminationPositive N))
        (mapGraph (F.embedding j) (S.eliminationPositive N)) := by
    intro i _ j _ hij
    exact Disjoint.mono (mapGraph_mono _ subset_union_left)
      (mapGraph_mono _ subset_union_left) (F.copies_disjoint hpair hqr hij)
  have hn : (s : Set I).Pairwise fun i j =>
      Disjoint (mapGraph (F.embedding i) S.eliminationNegative)
        (mapGraph (F.embedding j) S.eliminationNegative) := by
    intro i _ j _ hij
    exact Disjoint.mono (mapGraph_mono _ subset_union_right)
      (mapGraph_mono _ subset_union_right) (F.copies_disjoint hpair hqr hij)
  rw [selectedPositive, selectedNegative, indicator_biUnion_of_disjoint _ _ hp,
    indicator_biUnion_of_disjoint _ _ hn, ← sum_sub_distrib, boundary_sum,
    indicator_image_of_injOn _ _ hP, indicator_image_of_injOn _ _ hQ,
    ← sum_sub_distrib, boundary_sum]
  apply sum_congr rfl
  intro i _
  rw [F.copy_boundary hpair, boundary_sub, boundary_indicator_singleton,
    boundary_indicator_singleton]

theorem EliminationFamily.selected_disjoint_previous (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (s : Finset I)
    (D : Finset (Block V q)) (hsupport : cliqueSupport (r + 1) D ⊆ B) :
    Disjoint (F.selectedPositive s ∪ F.selectedNegative s) D := by
  apply Disjoint.mono_left _ (F.cliques_disjoint_previous hpair hqr D hsupport)
  rw [F.cliques_eq_signs]
  exact union_subset_union (F.selectedPositive_subset s) (F.selectedNegative_subset s)

def EliminationFamily.replacePositive (F : EliminationFamily S N B P Q θ)
    (s : Finset I) (D : Finset (Block V q)) := (D \ s.image P) ∪ F.selectedPositive s

def EliminationFamily.replaceNegative (F : EliminationFamily S N B P Q θ)
    (s : Finset I) (D : Finset (Block V q)) := (D \ s.image Q) ∪ F.selectedNegative s

theorem EliminationFamily.replace_boundary (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (s : Finset I)
    (hP : Set.InjOn P s) (hQ : Set.InjOn Q s) (Dpos Dneg : Finset (Block V q))
    (hsupport : cliqueSupport (r + 1) (Dpos ∪ Dneg) ⊆ B)
    (hDP : s.image P ⊆ Dpos) (hDQ : s.image Q ⊆ Dneg) :
    boundary (r + 1) (indicator (F.replacePositive s Dpos) -
      indicator (F.replaceNegative s Dneg)) =
      boundary (r + 1) (indicator Dpos - indicator Dneg) := by
  have hsep := F.selected_disjoint_previous hpair hqr s (Dpos ∪ Dneg) hsupport
  have hp : Disjoint (Dpos \ s.image P) (F.selectedPositive s) :=
    Disjoint.mono (sdiff_subset.trans subset_union_left) subset_union_left hsep.symm
  have hn : Disjoint (Dneg \ s.image Q) (F.selectedNegative s) :=
    Disjoint.mono (sdiff_subset.trans subset_union_right) subset_union_right hsep.symm
  rw [replacePositive, replaceNegative, indicator_union hp, indicator_union hn,
    indicator_sdiff hDP, indicator_sdiff hDQ]
  simp only [boundary_sub, boundary_add]
  have h := F.selected_boundary hpair hqr s hP hQ
  rw [boundary_sub, boundary_sub] at h
  funext e
  have he := congrFun h e
  simp only [Pi.sub_apply, Pi.add_apply] at he ⊢
  omega

theorem EliminationFamily.replace_signs_disjoint (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (s : Finset I)
    (Dpos Dneg : Finset (Block V q)) (hsupport : cliqueSupport (r + 1) (Dpos ∪ Dneg) ⊆ B)
    (hD : Disjoint Dpos Dneg) :
    Disjoint (F.replacePositive s Dpos) (F.replaceNegative s Dneg) := by
  have hsep := F.selected_disjoint_previous hpair hqr s (Dpos ∪ Dneg) hsupport
  apply disjoint_left.mpr
  intro R hRp hRn
  rcases mem_union.mp hRp with hp | hp <;> rcases mem_union.mp hRn with hn | hn
  · exact disjoint_left.mp hD (mem_sdiff.mp hp).1 (mem_sdiff.mp hn).1
  · exact disjoint_left.mp hsep (mem_union_right _ hn)
      (mem_union_left _ (mem_sdiff.mp hp).1)
  · exact disjoint_left.mp hsep (mem_union_left _ hp)
      (mem_union_right _ (mem_sdiff.mp hn).1)
  · exact disjoint_left.mp (F.signs_disjoint hpair hqr)
      (F.selectedPositive_subset s hp) (F.selectedNegative_subset s hn)

end Arxiv2411_18291
