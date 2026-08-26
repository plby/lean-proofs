import ErdosProblems.Erdos547.RelativeBinAllocation
import ErdosProblems.Erdos547.ClusterPrivateSets

/-!
# One assignment for objects with different group weight systems
-/

namespace Erdos547

open Finset
open scoped BigOperators

open scoped Classical in
theorem exists_grouped_relative_assignment {F I J K : Type*}
    [Fintype F] [Fintype I] [Nonempty I] [Fintype J] [DecidableEq K] [DecidableEq I]
    (group : F → K) (allowed : F → Finset I) (w : K → I → ℝ) (u : F → J → ℝ)
    (A θ : K → ℝ) (L err : ℝ) (capacity margin : K → J → ℝ)
    (hw : ∀ c i, 0 ≤ w c i) (hA : ∀ c, 0 < A c) (herr : 0 ≤ err)
    (hallowed : ∀ x, A (group x) ≤ ∑ i ∈ allowed x, w (group x) i)
    (hweight : ∀ x i, i ∈ allowed x → θ (group x) ≤ w (group x) i)
    (hu : ∀ x j, 0 ≤ u x j ∧ u x j ≤ L)
    (hsmall : ∀ c, L * (∑ x ∈ (Finset.univ : Finset F).filter (fun x ↦ group x = c),
      ∑ j, u x j) < err ^ 2)
    (hcapacity : ∀ c j, 0 ≤ capacity c j) (hmargin : ∀ c j, 0 ≤ margin c j)
    (hmean : ∀ c j, ((∑ x ∈ (Finset.univ : Finset F).filter (fun x ↦ group x = c), u x j) /
      A c) + margin c j ≤ capacity c j)
    (herror : ∀ c j, err ≤ θ c * margin c j) :
    ∃ f : F → I, (∀ x, f x ∈ allowed x) ∧
      ∀ c i j, (∑ x ∈ (Finset.univ : Finset F).filter
        (fun x ↦ group x = c ∧ f x = i), u x j) ≤ capacity c j * w c i := by
  classical
  let fiber (c : K) := (Finset.univ : Finset F).filter (fun x ↦ group x = c)
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hex (c : K) : ∃ f : F → I, (∀ x, group x = c → f x ∈ allowed x) ∧
      ∀ i j, (∑ x ∈ (fiber c).filter (fun x ↦ f x = i), u x j) ≤ capacity c j * w c i := by
    have hgroup (x : ↥(fiber c)) : group x.val = c := (Finset.mem_filter.mp x.property).2
    have ha (x : ↥(fiber c)) : A c ≤ ∑ i ∈ allowed x.val, w c i := by
      have hh := hallowed x.val
      rwa [hgroup x] at hh
    have ht (x : ↥(fiber c)) (i : I) (hi : i ∈ allowed x.val) : θ c ≤ w c i := by
      have hh := hweight x.val i hi
      rwa [hgroup x] at hh
    have hsmall' : L * (∑ x : ↥(fiber c), ∑ j, u x.val j) < err ^ 2 := by
      rw [Finset.sum_coe_sort (fiber c) (fun x ↦ ∑ j, u x j)]
      exact hsmall c
    have hmean' (j : J) : (∑ x : ↥(fiber c), u x.val j) / A c + margin c j ≤ capacity c j := by
      rw [Finset.sum_coe_sort (fiber c) (fun x ↦ u x j)]
      exact hmean c j
    obtain ⟨f, hf, hload⟩ := exists_relative_bin_assignment
      (fun x : ↥(fiber c) ↦ allowed x.val) (w c) (fun x j ↦ u x.val j)
      (A c) L err (θ c) (capacity c) (margin c) (hw c) (hA c) herr ha ht
      (fun x j ↦ hu x.val j) hsmall' (hcapacity c) (hmargin c) hmean' (herror c)
    let lift : F → I := fun x ↦ if hx : x ∈ fiber c then f ⟨x, hx⟩ else i₀
    refine ⟨lift, ?_, ?_⟩
    · intro x hx
      have hxf : x ∈ fiber c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      simpa only [lift, dif_pos hxf] using hf ⟨x, hxf⟩
    · intro i j
      have he : (∑ x ∈ (fiber c).filter (fun x ↦ lift x = i), u x j) =
          ∑ x ∈ (Finset.univ : Finset ↥(fiber c)).filter (fun x ↦ f x = i), u x.val j := by
        rw [← sum_filter_coe (fiber c) (fun x ↦ lift x = i) (fun x ↦ u x j)]
        apply Finset.sum_congr
        · ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hh : lift x.val = f x := by simp only [lift, dif_pos x.property]
          rw [hh]
        · intro x _
          rfl
      rw [he]
      exact hload i j
  choose f hf hload using hex
  let result : F → I := fun x ↦ f (group x) x
  refine ⟨result, fun x ↦ hf (group x) x rfl, ?_⟩
  intro c i j
  have he : (Finset.univ : Finset F).filter (fun x ↦ group x = c ∧ result x = i) =
      (fiber c).filter (fun x ↦ f c x = i) := by
    ext x
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : group x = c
    · simp only [hx, true_and, result]
    · simp only [hx, false_and]
  rw [he]
  exact hload c i j

end Erdos547

#print axioms Erdos547.exists_grouped_relative_assignment
