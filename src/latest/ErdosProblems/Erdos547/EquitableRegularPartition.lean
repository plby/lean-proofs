import ErdosProblems.Erdos547.ClusterCounting

/-!
# Equitable regular partitions with a bound for each cluster
-/

namespace Erdos547

open Finset SimpleGraph

variable {V I : Type*} [Fintype V] [DecidableEq V]

structure EquitableRegularPartition (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) where
  clusters : Finset (Finset V)
  clusterSize : ℕ
  positive_size : 1 ≤ clusterSize
  equal_size : ∀ X ∈ clusters, X.card = clusterSize
  disjoint : ∀ X ∈ clusters, ∀ Y ∈ clusters, X ≠ Y → Disjoint X Y
  discarded_bound : ((Finset.univ \ clusters.biUnion id).card : ℝ) ≤ ε * Fintype.card V
  irregular_bound : ∀ X ∈ clusters,
    ((clusters.filter (fun Y ↦ X ≠ Y ∧ ¬ G.IsUniform ε X Y)).card : ℝ) ≤ ε * clusters.card

open scoped Classical in
theorem regular_partition_of_equal_family [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (C : I → Finset V) (m : ℕ) (hm : 1 ≤ m)
    (hsize : ∀ i, (C i).card = m) (hdis : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hgarbage : ((Finset.univ \ Finset.univ.biUnion C).card : ℝ) ≤ ε * Fintype.card V)
    (hbad : ∀ i, (((Finset.univ : Finset I).filter
      (fun j ↦ i ≠ j ∧ ¬ G.IsUniform ε (C i) (C j))).card : ℝ) ≤ ε * Fintype.card I) :
    ∃ P : EquitableRegularPartition G ε,
      P.clusters.card = Fintype.card I ∧ P.clusterSize = m := by
  classical
  let F := (Finset.univ : Finset I).image C
  have hinj : Function.Injective C := by
    intro i j he
    by_contra hij
    have hne : (C i).Nonempty := Finset.card_pos.mp (by rw [hsize]; omega)
    obtain ⟨v, hv⟩ := hne
    exact Finset.disjoint_left.mp (hdis hij) hv (he ▸ hv)
  have hFcard : F.card = Fintype.card I := by
    simp only [F, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hfunion : F.biUnion id = (Finset.univ : Finset I).biUnion C := by
    ext v
    constructor
    · intro hv
      obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvX⟩
    · intro hv
      obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨C i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hvi⟩
  have hrow (X : Finset V) (hX : X ∈ F) :
      ((F.filter (fun Y ↦ X ≠ Y ∧ ¬ G.IsUniform ε X Y)).card : ℝ) ≤ ε * F.card := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
    let B := (Finset.univ : Finset I).filter (fun j ↦ i ≠ j ∧ ¬ G.IsUniform ε (C i) (C j))
    have hsub : F.filter (fun Y ↦ C i ≠ Y ∧ ¬ G.IsUniform ε (C i) Y) ⊆ B.image C := by
      intro Y hY
      obtain ⟨hYF, hne, hreg⟩ := Finset.mem_filter.mp hY
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hYF
      have hij : i ≠ j := fun he ↦ hne (congrArg C he)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hreg⟩, rfl⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
    have hc' : ((F.filter (fun Y ↦ C i ≠ Y ∧ ¬ G.IsUniform ε (C i) Y)).card : ℝ) ≤ B.card := by
      exact_mod_cast hc
    rw [hFcard]
    exact hc'.trans (hbad i)
  refine ⟨{
    clusters := F
    clusterSize := m
    positive_size := hm
    equal_size := ?_
    disjoint := ?_
    discarded_bound := ?_
    irregular_bound := hrow
  }, hFcard, rfl⟩
  · intro X hX
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
    exact hsize i
  · intro X hX Y hY hXY
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hY
    exact hdis (fun he ↦ hXY (congrArg C he))
  · rw [hfunion]
    exact hgarbage

end Erdos547

#print axioms Erdos547.regular_partition_of_equal_family
