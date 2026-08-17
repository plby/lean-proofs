/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerSampling

/-!
# Restricting a sampled triple system to its surviving vertices

This file transfers the finite sampling conclusion to the subtype of the
pruned vertex set.  Consequently the vertex count in the weighted lemma is
exactly the number of vertices which survived deletion.
-/

open scoped BigOperators

namespace Erdos1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

def subtypeEmbedding (Y : Finset V) : Y ↪ V := Function.Embedding.subtype _

def valMap (Y : Finset V) (I : Finset Y) : Finset V :=
  I.map (subtypeEmbedding Y)

@[simp] lemma card_valMap (Y : Finset V) (I : Finset Y) :
    (valMap Y I).card = I.card := by
  simp [valMap]

def restrictSystem (H : System V) (Y : Finset V) : System Y :=
  Finset.univ.powerset.filter fun e ↦ valMap Y e ∈ H

@[simp] lemma mem_restrictSystem {H : System V} {Y : Finset V}
    {e : Finset Y} : e ∈ restrictSystem H Y ↔ valMap Y e ∈ H := by
  rw [restrictSystem, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨Finset.subset_univ _, h⟩

lemma valMap_injective (Y : Finset V) : Function.Injective (valMap Y) := by
  exact Finset.map_injective _

lemma restrict_threeUniform {H : System V} (h3 : ThreeUniform H) (Y : Finset V) :
    ThreeUniform (restrictSystem H Y) := by
  intro e he
  rw [← card_valMap Y e]
  exact h3 _ (mem_restrictSystem.mp he)

lemma restrict_linear {H : System V} (hlin : Linear H) (Y : Finset V) :
    Linear (restrictSystem H Y) := by
  intro e he f hf hef
  have hmapne : valMap Y e ≠ valMap Y f := fun h ↦ hef (valMap_injective Y h)
  have h := hlin (mem_restrictSystem.mp he) (mem_restrictSystem.mp hf) hmapne
  rw [valMap, valMap, ← Finset.map_inter, Finset.card_map] at h
  exact h

lemma valMap_subset_Y (Y : Finset V) (I : Finset Y) : valMap Y I ⊆ Y := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hx
  exact v.property

lemma independent_restrict_iff {H : System V} {Y : Finset V}
    {I : Finset Y} :
    Independent (restrictSystem H Y) I ↔ Independent H (valMap Y I) := by
  classical
  constructor
  · intro hI e heH heSub
    have heY : ∀ x ∈ e, x ∈ Y := fun x hx ↦
      valMap_subset_Y Y I (heSub hx)
    let e' : Finset Y := e.subtype (· ∈ Y)
    have hmap : valMap Y e' = e := by
      exact Finset.subtype_map_of_mem heY
    have heR : e' ∈ restrictSystem H Y := by
      rw [mem_restrictSystem, hmap]
      exact heH
    apply hI heR
    apply Finset.map_subset_map.mp
    change valMap Y e' ⊆ valMap Y I
    rw [hmap]
    exact heSub
  · intro hI e heR heSub
    apply hI (mem_restrictSystem.mp heR)
    exact (Finset.map_subset_map.mpr heSub)

lemma restrict_triangleFree {H : System V} {Y : Finset V}
    (htri : TriangleFree (H.filter fun e ↦ e ⊆ Y)) :
    TriangleFree (restrictSystem H Y) := by
  rw [TriangleFree] at htri ⊢
  intro ht
  obtain ⟨e, he, f, hf, g, hg, hef, heg, hfg,
    hefCard, hegCard, hfgCard, hcommon⟩ := ht
  let E := valMap Y e
  let F := valMap Y f
  let G := valMap Y g
  have hEF : E ≠ F := fun h ↦ hef (valMap_injective Y h)
  have hEG : E ≠ G := fun h ↦ heg (valMap_injective Y h)
  have hFG : F ≠ G := fun h ↦ hfg (valMap_injective Y h)
  have hEFcard : (E ∩ F).card = 1 := by
    dsimp [E, F]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hefCard
  have hEGcard : (E ∩ G).card = 1 := by
    dsimp [E, G]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hegCard
  have hFGcard : (F ∩ G).card = 1 := by
    dsimp [F, G]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hfgCard
  have hcommonCard : (E ∩ F ∩ G).card = 0 := by
    dsimp [E, F, G]
    rw [valMap, valMap, valMap,
      ← Finset.map_inter, ← Finset.map_inter, Finset.card_map]
    exact hcommon
  apply htri
  exact ⟨E, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp he, valMap_subset_Y Y e⟩,
    F, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp hf, valMap_subset_Y Y f⟩,
    G, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp hg, valMap_subset_Y Y g⟩,
    hEF, hEG, hFG, hEFcard, hEGcard, hFGcard, hcommonCard⟩

lemma extensionCount_restrict_le {H : System V} {Y : Finset V}
    (h3 : ThreeUniform H) {B : ℕ} (v : Y) (Z : Finset Y) :
    truncatedExtension (restrictSystem H Y) B v Z ≤
      truncatedExtension H B v.1 (valMap Y Z) := by
  classical
  unfold truncatedExtension
  apply min_le_min_right
  rw [extensionCount_eq_card_pairsAt, extensionCount_eq_card_pairsAt]
  let emb : Finset Y ↪ Finset V :=
    (Finset.mapEmbedding (subtypeEmbedding Y)).toEmbedding
  have hsub : (pairsAt (restrictSystem H Y) v Z).map emb ⊆
      pairsAt H v.1 (valMap Y Z) := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    have haFilter := Finset.mem_filter.mp ha'
    obtain ⟨e, heR, hve, -, hea⟩ := mem_linkPairs.mp haFilter.1
    let E := valMap Y e
    have hE : E ∈ H := mem_restrictSystem.mp heR
    have hvE : v.1 ∈ E := by
      exact Finset.mem_map.mpr ⟨v, hve, rfl⟩
    have herase : E.erase v.1 = valMap Y (e.erase v) := by
      simpa [E, valMap, subtypeEmbedding] using
        (Finset.map_erase (subtypeEmbedding Y) e v).symm
    have hEN : E.erase v.1 ⊆ neighborhood H v.1 := by
      intro x hx
      have hxE := Finset.mem_of_mem_erase hx
      have hxv := (Finset.mem_erase.mp hx).1
      exact vertex_of_edge_neighborhood hE hvE hxE hxv
    have hlink : valMap Y a' ∈ linkPairs H v.1 (neighborhood H v.1) := by
      apply mem_linkPairs.mpr
      refine ⟨E, hE, hvE, hEN, ?_⟩
      rw [herase, hea]
    change valMap Y a' ∈ pairsAt H v.1 (valMap Y Z)
    apply Finset.mem_filter.mpr
    refine ⟨hlink, ?_⟩
    exact Finset.map_subset_map.mpr haFilter.2
  calc
    (pairsAt (restrictSystem H Y) v Z).card =
        ((pairsAt (restrictSystem H Y) v Z).map emb).card := by simp
    _ ≤ (pairsAt H v.1 (valMap Y Z)).card := Finset.card_le_card hsub

lemma map_univ_sdiff (Y : Finset V) (Z : Finset Y) :
    (Finset.univ \ Z).map (subtypeEmbedding Y) = Y \ valMap Y Z := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    have hv' := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨v.property, fun h ↦ by
      obtain ⟨w, hwZ, hw⟩ := Finset.mem_map.mp h
      have hwv : w = v := Subtype.ext hw
      exact hv'.2 (hwv ▸ hwZ)⟩
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    let v : Y := ⟨x, hx'.1⟩
    apply Finset.mem_map.mpr
    refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    intro hvZ
    exact hx'.2 (Finset.mem_map.mpr ⟨v, hvZ, rfl⟩)

theorem totalTruncatedExtension_restrict_le {H : System V} {Y : Finset V}
    (h3 : ThreeUniform H) (B : ℕ) (Z : Finset Y) :
    totalTruncatedExtension (restrictSystem H Y) B Z ≤
      ∑ v ∈ Y \ valMap Y Z, truncatedExtension H B v (valMap Y Z) := by
  classical
  unfold totalTruncatedExtension
  calc
    ∑ v ∈ Finset.univ \ Z,
        truncatedExtension (restrictSystem H Y) B v Z ≤
      ∑ v ∈ Finset.univ \ Z,
        truncatedExtension H B v.1 (valMap Y Z) := by
      exact Finset.sum_le_sum fun v _ ↦ extensionCount_restrict_le h3 v Z
    _ = ∑ v ∈ (Finset.univ \ Z).map (subtypeEmbedding Y),
        truncatedExtension H B v (valMap Y Z) := by
      rw [Finset.sum_map]
      simp [subtypeEmbedding]
    _ = _ := by rw [map_univ_sdiff]

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.totalTruncatedExtension_restrict_le
