/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Aggregate

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59FullOnline

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair

universe u
variable {B : Type u} [Fintype B] [DecidableEq B]

/-- Distinct level-one images, joined to the actual owner roots and typical
toward their assigned matching endpoints. -/
structure BranchRootSelection
    {r b C : ℕ} (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootImage : Fin r → B) (owner : Fin b → Fin r)
    (cluster : Fin C → Finset B) (assign : Fin b → Fin C)
    (endpoint : Fin b → Finset B) where
  image : Fin b → B
  injective : Function.Injective image
  mem_cluster : ∀ j, image j ∈ cluster (assign j)
  adj_owner : ∀ j, G.Adj (rootImage (owner j)) (image j)
  typical_endpoint : ∀ j,
    image j ∈ cleanedSide G rho (cluster (assign j)) (endpoint j)

namespace BranchRootSelector

variable {r b C : ℕ}
  (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
  (rootImage : Fin r → B) (owner : Fin b → Fin r)
  (cluster : Fin C → Finset B) (assign : Fin b → Fin C)
  (endpoint : Fin b → Finset B) (capacity : Fin C → ℕ)
  (hunif : ∀ j, G.IsUniform rho (cluster (assign j)) (endpoint j))
  (hrho : rho ≤ 1)
  (hrootDegree : ∀ j,
    (capacity (assign j) : ℝ) + rho * #(cluster (assign j)) ≤
      (#((cluster (assign j)).filter (G.Adj (rootImage (owner j)))) : ℝ))
  (hload : ∀ c : Fin C,
    #((Finset.univ : Finset (Fin b)).filter (assign · = c)) ≤ capacity c)
  (hclusterDisjoint : ∀ c d, c ≠ d → Disjoint (cluster c) (cluster d))

def choices (j : Fin b) : Finset B :=
  (cleanedSide G rho (cluster (assign j)) (endpoint j)).filter
    (G.Adj (rootImage (owner j)))

include hunif hrho hrootDegree in
theorem card_choices (j : Fin b) :
    capacity (assign j) ≤
      #(choices G rho rootImage owner cluster assign endpoint j) := by
  let bad := atypicalVertices G rho (cluster (assign j)) (endpoint j)
  have hbad : (#bad : ℝ) ≤ rho * #(cluster (assign j)) := by
    simpa [bad] using card_atypicalVertices_le G (hunif j) hrho
  have hreal : (capacity (assign j) : ℝ) + #bad ≤
      (#((cluster (assign j)).filter
        (G.Adj (rootImage (owner j)))) : ℝ) := by
    linarith [hrootDegree j]
  have hnat : capacity (assign j) + #bad ≤
      #((cluster (assign j)).filter (G.Adj (rootImage (owner j)))) := by
    exact_mod_cast hreal
  simpa [choices, cleanedSide, bad] using
    card_neighbors_cleaned_ge G (cluster (assign j)) bad
      (rootImage (owner j)) (capacity (assign j)) hnat

structure Realization (j : Fin b) where
  image : B
  mem_cluster : image ∈ cluster (assign j)
  adj_owner : G.Adj (rootImage (owner j)) image
  typical_endpoint : image ∈
    cleanedSide G rho (cluster (assign j)) (endpoint j)

structure Step (j : Fin b)
    (prior : ∀ k : Fin b, k.val < j.val →
      Realization G rho rootImage owner cluster assign endpoint k) where
  data : Realization G rho rootImage owner cluster assign endpoint j
  fresh : ∀ k (hk : k.val < j.val), data.image ≠ (prior k hk).image

include hunif hrho hrootDegree hload hclusterDisjoint

noncomputable def step (j : Fin b)
    (prior : ∀ k : Fin b, k.val < j.val →
      Realization G rho rootImage owner cluster assign endpoint k) :
    Step G rho rootImage owner cluster assign endpoint j prior := by
  classical
  let earlierSame : Finset (Fin b) :=
    (Finset.Iio j).filter (assign · = assign j)
  let used : Finset B := earlierSame.attach.image fun k =>
    (prior k.1 (by
      have hkIio : k.1 ∈ Finset.Iio j := (Finset.mem_filter.mp k.2).1
      exact Fin.mk_lt_mk.mp (Finset.mem_Iio.mp hkIio))).image
  have hjNotEarlier : j ∉ earlierSame := by simp [earlierSame]
  have hinsert : insert j earlierSame ⊆
      (Finset.univ : Finset (Fin b)).filter (assign · = assign j) := by
    intro k hk
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ k
    · rcases Finset.mem_insert.mp hk with rfl | hk
      · rfl
      · exact (Finset.mem_filter.mp hk).2
  have hearlier_lt : #earlierSame < capacity (assign j) := by
    have hcardInsert : #(insert j earlierSame) = #earlierSame + 1 := by
      rw [Finset.card_insert_of_notMem hjNotEarlier]
    have hle := Finset.card_le_card hinsert
    rw [hcardInsert] at hle
    have hcap := hload (assign j)
    omega
  have hused : #used ≤ #earlierSame := by
    calc
      #used ≤ #earlierSame.attach := Finset.card_image_le
      _ = #earlierSame := Finset.card_attach
  have husedChoices : #used <
      #(choices G rho rootImage owner cluster assign endpoint j) := by
    exact lt_of_le_of_lt hused
      (hearlier_lt.trans_le (card_choices G rho rootImage owner cluster assign
        endpoint capacity hunif hrho hrootDegree j))
  let hex : ∃ z ∈ choices G rho rootImage owner cluster assign endpoint j,
      z ∉ used := Finset.exists_mem_notMem_of_card_lt_card husedChoices
  let z : B := Classical.choose hex
  have hzChoices : z ∈ choices G rho rootImage owner cluster assign endpoint j :=
    (Classical.choose_spec hex).1
  have hzUnused : z ∉ used := (Classical.choose_spec hex).2
  have hzTypical : z ∈
      cleanedSide G rho (cluster (assign j)) (endpoint j) :=
    (Finset.mem_filter.mp hzChoices).1
  have hzCluster : z ∈ cluster (assign j) :=
    (Finset.mem_sdiff.mp hzTypical).1
  have hzAdj : G.Adj (rootImage (owner j)) z :=
    (Finset.mem_filter.mp hzChoices).2
  let data : Realization G rho rootImage owner cluster assign endpoint j :=
    { image := z
      mem_cluster := hzCluster
      adj_owner := hzAdj
      typical_endpoint := hzTypical }
  refine ⟨data, ?_⟩
  intro k hk hEq
  by_cases hgroup : assign k = assign j
  · apply hzUnused
    apply Finset.mem_image.mpr
    have hkSame : k ∈ earlierSame := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Iio.mpr (Fin.mk_lt_mk.mpr hk), hgroup⟩
    refine ⟨⟨k, hkSame⟩, Finset.mem_attach _ _, ?_⟩
    exact hEq.symm
  · have hkMem := (prior k hk).mem_cluster
    have hd := hclusterDisjoint (assign k) (assign j) hgroup
    exact (Finset.disjoint_left.mp hd) hkMem (hEq ▸ hzCluster)

noncomputable def realization (j : Fin b) :
    Realization G rho rootImage owner cluster assign endpoint j :=
  (step G rho rootImage owner cluster assign endpoint capacity hunif hrho
    hrootDegree hload hclusterDisjoint j
    (fun k _hk => realization k)).data
termination_by j.val

theorem realization_fresh (j k : Fin b) (hk : k.val < j.val) :
    (realization G rho rootImage owner cluster assign endpoint capacity hunif
      hrho hrootDegree hload hclusterDisjoint j).image ≠
    (realization G rho rootImage owner cluster assign endpoint capacity hunif
      hrho hrootDegree hload hclusterDisjoint k).image := by
  rw [realization.eq_def]
  exact (step G rho rootImage owner cluster assign endpoint capacity hunif hrho
    hrootDegree hload hclusterDisjoint j
    (fun k hk => realization G rho rootImage owner cluster assign endpoint
      capacity hunif hrho hrootDegree hload hclusterDisjoint k)).fresh k hk

end BranchRootSelector

/-- Sequential branch-root selection from actual uniform cluster-endpoint
pairs. The arbitrary owner-root degree is the only live-root premise;
typicality toward matching endpoints is derived. -/
theorem exists_branchRootSelection_of_uniform
    {r b C : ℕ}
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootImage : Fin r → B) (owner : Fin b → Fin r)
    (cluster : Fin C → Finset B) (assign : Fin b → Fin C)
    (endpoint : Fin b → Finset B) (capacity : Fin C → ℕ)
    (hunif : ∀ j, G.IsUniform rho (cluster (assign j)) (endpoint j))
    (hrho : rho ≤ 1)
    (hrootDegree : ∀ j,
      (capacity (assign j) : ℝ) + rho * #(cluster (assign j)) ≤
        (#((cluster (assign j)).filter
          (G.Adj (rootImage (owner j)))) : ℝ))
    (hload : ∀ c : Fin C,
      #((Finset.univ : Finset (Fin b)).filter (assign · = c)) ≤ capacity c)
    (hclusterDisjoint : ∀ c d, c ≠ d → Disjoint (cluster c) (cluster d)) :
    Nonempty (BranchRootSelection G rho rootImage owner cluster assign endpoint) := by
  classical
  let R := fun j => BranchRootSelector.realization G rho rootImage owner cluster
    assign endpoint capacity hunif hrho hrootDegree hload hclusterDisjoint j
  let image : Fin b → B := fun j => (R j).image
  have hinj : Function.Injective image := by
    intro j k hjk
    by_contra hne
    have hvalne : j.val ≠ k.val := by
      intro hval
      exact hne (Fin.ext hval)
    rcases lt_or_gt_of_ne hvalne with hjkVal | hkjVal
    · exact (BranchRootSelector.realization_fresh G rho rootImage owner cluster
        assign endpoint capacity hunif hrho hrootDegree hload
        hclusterDisjoint k j hjkVal) (by simpa [image, R] using hjk.symm)
    · exact (BranchRootSelector.realization_fresh G rho rootImage owner cluster
        assign endpoint capacity hunif hrho hrootDegree hload
        hclusterDisjoint j k hkjVal) (by simpa [image, R] using hjk)
  exact ⟨
    { image := image
      injective := hinj
      mem_cluster := fun j => (R j).mem_cluster
      adj_owner := fun j => (R j).adj_owner
      typical_endpoint := fun j => (R j).typical_endpoint }⟩

end Erdos547b.ZhaoLemma59FullOnline

#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_branchRootSelection_of_uniform
