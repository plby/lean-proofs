/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Reciprocal roots compare the total count with the two interior counts, up to the endpoints.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ReversalLaw

namespace Erdos521

theorem realRoot_ne_zero (ε : ℕ → ℝ) (n : ℕ) (hε : ε 0 ≠ 0)
    {x : ℝ} (hx : x ∈ realRoots ε n) : x ≠ 0 := by
  intro heq
  subst x
  have h := (mem_realRoots ε n hε 0).mp hx
  rw [← polynomial_eval, polynomial_eval_zero] at h
  exact hε h

theorem rootCount_reversal_bounds (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0) (hεn : ε n ≠ 0) :
    rootCount ε n ≤ interiorRootCount ε n + interiorRootCount (reversedCoefficients n ε) n ∧
      interiorRootCount ε n + interiorRootCount (reversedCoefficients n ε) n ≤ rootCount ε n + 2 := by
  classical
  let A := (realRoots ε n).filter (fun x ↦ x ∈ Set.Icc (-1 : ℝ) 1)
  let B₀ := (realRoots (reversedCoefficients n ε) n).filter (fun x ↦ x ∈ Set.Icc (-1 : ℝ) 1)
  let B := B₀.image (fun x ↦ x⁻¹)
  have hrev₀ : reversedCoefficients n ε 0 ≠ 0 := by rwa [reversedCoefficients_zero]
  have hBsub : B ⊆ realRoots ε n := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyroot := (Finset.mem_filter.mp hy).1
    have hy₀ := realRoot_ne_zero _ n hrev₀ hyroot
    apply (mem_realRoots_reversedCoefficients_inv n ε hε₀ hεn y⁻¹ (inv_ne_zero hy₀)).mp
    simpa only [inv_inv] using hyroot
  have hcover : A ∪ B = realRoots ε n := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (Finset.filter_subset _ _) hBsub
    · intro x hx
      by_cases hxi : |x| ≤ 1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, abs_le.mp hxi⟩))
      · have hx₀ := realRoot_ne_zero ε n hε₀ hx
        have hxpos : 0 < |x| := abs_pos.mpr hx₀
        have hinv : |x⁻¹| ≤ 1 := by
          rw [abs_inv]
          exact (inv_le_one₀ hxpos).mpr (lt_of_not_ge hxi).le
        apply Finset.mem_union.mpr (Or.inr _)
        exact Finset.mem_image.mpr ⟨x⁻¹, Finset.mem_filter.mpr
          ⟨(mem_realRoots_reversedCoefficients_inv n ε hε₀ hεn x hx₀).mpr hx, abs_le.mp hinv⟩,
          inv_inv x⟩
  have hinter : A ∩ B ⊆ ({1, -1} : Finset ℝ) := by
    intro x hx
    obtain ⟨hA, hB⟩ := Finset.mem_inter.mp hx
    have hxabs : |x| ≤ 1 := abs_le.mpr (Finset.mem_filter.mp hA).2
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hB
    have hyroot := (Finset.mem_filter.mp hy).1
    have hyabs : |y| ≤ 1 := abs_le.mpr (Finset.mem_filter.mp hy).2
    have hy₀ := realRoot_ne_zero _ n hrev₀ hyroot
    have hxabs' : 1 ≤ |x| := by
      rw [← hxy, abs_inv]
      exact (one_le_inv₀ (abs_pos.mpr hy₀)).mpr hyabs
    have hxend := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (le_antisymm hxabs hxabs')
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxend
  have hcard : (A ∩ B).card ≤ 2 := by
    have h := Finset.card_le_card hinter
    norm_num at h ⊢
    exact h
  have hBcard : B.card = interiorRootCount (reversedCoefficients n ε) n := by
    exact Finset.card_image_of_injective B₀ inv_injective
  have hid := Finset.card_union_add_card_inter A B
  rw [hcover, hBcard] at hid
  change rootCount ε n + (A ∩ B).card = interiorRootCount ε n +
    interiorRootCount (reversedCoefficients n ε) n at hid
  omega

theorem rootCount_reversal_lower (ε : ℕ → ℝ) (n : ℕ) (hε₀ : ε 0 ≠ 0) (hεn : ε n ≠ 0) :
    (interiorRootCount ε n : ℝ) + interiorRootCount (reversedCoefficients n ε) n - 2 ≤ rootCount ε n := by
  have h : (interiorRootCount ε n : ℝ) + interiorRootCount (reversedCoefficients n ε) n ≤
      rootCount ε n + 2 := by exact_mod_cast (rootCount_reversal_bounds ε n hε₀ hεn).2
  linarith

end Erdos521
