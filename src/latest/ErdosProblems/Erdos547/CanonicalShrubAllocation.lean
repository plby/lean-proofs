import ErdosProblems.Erdos547.IndexedShrubSums
import ErdosProblems.Erdos547.GroupedBinAllocation

/-!
# A single head assignment with relative bounds for both shrub families
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U I : Type*} [Fintype U] [DecidableEq U] [Fintype I] [Nonempty I] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)}

open scoped Classical in
theorem exists_relative_shrub_heads (P : FineTreePartition T r ℓ col)
    (allowed : ↥P.shrubs → Finset I) (w : Fin 2 → I → ℝ) (A θ : Fin 2 → ℝ)
    (err : ℝ) (capacity margin : Fin 2 → Fin 2 → ℝ)
    (hw : ∀ c i, 0 ≤ w c i) (hA : ∀ c, 0 < A c) (herr : 0 ≤ err)
    (hallowed : ∀ S, A (P.shrubColour S) ≤ ∑ i ∈ allowed S, w (P.shrubColour S) i)
    (hweight : ∀ S i, i ∈ allowed S → θ (P.shrubColour S) ≤ w (P.shrubColour S) i)
    (hsmall : ∀ c, (ℓ : ℝ) * ((P.nearVertices c).card + (P.farVertices c).card) < err ^ 2)
    (hcapacity : ∀ c j, 0 ≤ capacity c j) (hmargin : ∀ c j, 0 ≤ margin c j)
    (hmeanNear : ∀ c, ((P.nearVertices c).card : ℝ) / A c + margin c 0 ≤ capacity c 0)
    (hmeanFar : ∀ c, ((P.farVertices c).card : ℝ) / A c + margin c 1 ≤ capacity c 1)
    (herror : ∀ c j, err ≤ θ c * margin c j) :
    ∃ head : ↥P.shrubs → I, (∀ S, head S ∈ allowed S) ∧ ∀ c i,
      (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
        (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.nearPart S).card : ℝ)) ≤ capacity c 0 * w c i ∧
      (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
        (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.farPart S).card : ℝ)) ≤ capacity c 1 * w c i := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  let u : ↥P.shrubs → Fin 2 → ℝ := fun S j ↦
    if j = 0 then (P.nearPart S).card else (P.farPart S).card
  have hu (S : ↥P.shrubs) (j : Fin 2) : 0 ≤ u S j ∧ u S j ≤ ℓ := by
    have hn : (P.nearPart S).card ≤ ℓ :=
      (Finset.card_filter_le _ _).trans (P.shrub_size S.val S.property)
    have hf : (P.farPart S).card ≤ ℓ :=
      (Finset.card_filter_le _ _).trans (P.shrub_size S.val S.property)
    dsimp [u]
    split_ifs
    · exact ⟨Nat.cast_nonneg _, by exact_mod_cast hn⟩
    · exact ⟨Nat.cast_nonneg _, by exact_mod_cast hf⟩
  have hnear (c : Fin 2) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c), u S 0) = (P.nearVertices c).card := by
    simp only [u, if_pos rfl]
    exact_mod_cast P.sum_nearPart_colour c
  have hfar (c : Fin 2) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c), u S 1) = (P.farVertices c).card := by
    simp only [u, if_neg h10]
    exact_mod_cast P.sum_farPart_colour c
  have hsmall' (c : Fin 2) : (ℓ : ℝ) * (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c), ∑ j, u S j) < err ^ 2 := by
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
    rw [hnear c, hfar c]
    exact hsmall c
  have hmean (c j : Fin 2) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c), u S j) / A c + margin c j ≤ capacity c j := by
    by_cases hj : j = 0
    · subst j
      rw [hnear c]
      exact hmeanNear c
    · have hj1 : j = 1 := by omega
      subst j
      rw [hfar c]
      exact hmeanFar c
  obtain ⟨head, hhead, hload⟩ := exists_grouped_relative_assignment
    (F := ↥P.shrubs) (I := I) (J := Fin 2) (K := Fin 2) P.shrubColour allowed w u
    A θ ℓ err capacity margin hw hA herr hallowed hweight hu hsmall' hcapacity hmargin hmean herror
  refine ⟨head, hhead, fun c i ↦ ⟨?_, ?_⟩⟩
  · simpa only [u, if_pos rfl] using hload c i 0
  · simpa only [u, if_neg h10] using hload c i 1

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_relative_shrub_heads
