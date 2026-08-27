import ErdosProblems.Erdos587.NVDevelopment

/-! # Robust spanning, quotient images, and integer coordinate widths -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_robust_spanning_image {ι E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (s : Finset ι) (v : ι → E) (k : ℕ)
    (hspan : ∀ t ⊆ s, k ≤ t.card → Submodule.span ℝ (v '' (t : Set ι)) = ⊤)
    (q : E →ₗ[ℝ] F) (hq : Function.Surjective q) :
    ∀ t ⊆ s, k ≤ t.card → Submodule.span ℝ ((q ∘ v) '' (t : Set ι)) = ⊤ := by
  intro t hts hcard
  calc
    _ = (Submodule.span ℝ (v '' (t : Set ι))).map q := by
      rw [Submodule.map_span, Set.image_image]
      rfl
    _ = ⊤ := by rw [hspan t hts hcard, Submodule.map_top, LinearMap.range_eq_top.mpr hq]

theorem delta_nonzero_functional_card_of_robust_spanning {ι E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset ι) (v : ι → E) (k : ℕ)
    (hspan : ∀ t ⊆ s, k ≤ t.card → Submodule.span ℝ (v '' (t : Set ι)) = ⊤)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    s.card < (s.filter (fun i => ℓ (v i) ≠ 0)).card + k := by
  classical
  let Z := s.filter (fun i => ℓ (v i) = 0)
  have hZ : Z.card < k := by
    by_contra h
    have hsp := hspan Z (Finset.filter_subset _ _) (by omega)
    have hker : Submodule.span ℝ (v '' (Z : Set ι)) ≤ LinearMap.ker ℓ := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    rw [hsp] at hker
    exact hℓ (LinearMap.ker_eq_top.mp (top_le_iff.mp hker))
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun i => ℓ (v i) = 0)
  have hsplit' : Z.card + (s.filter (fun i => ℓ (v i) ≠ 0)).card = s.card := by
    simpa only [Z, ne_eq] using hsplit
  omega

lemma delta_nonzero_card_le_sum_natAbs {ι : Type*} (s : Finset ι) (z : ι → ℤ) :
    (s.filter (fun i => z i ≠ 0)).card ≤ ∑ i ∈ s, (z i).natAbs := by
  classical
  calc
    _ = ∑ i ∈ s.filter (fun i => z i ≠ 0), (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ s.filter (fun i => z i ≠ 0), (z i).natAbs := by
      apply Finset.sum_le_sum
      intro i hi
      exact Int.natAbs_pos.mpr (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ s, (z i).natAbs := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Erdos587.CFP
