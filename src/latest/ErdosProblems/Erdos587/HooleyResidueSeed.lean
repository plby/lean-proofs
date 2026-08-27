import ErdosProblems.Erdos587.HooleyResiduePool
import ErdosProblems.Erdos587.DenseFiberBlocks

/-! # Completing a coarse seed to all points of the generated lattice -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

theorem delta_residue_pool_fills_lattice_box {α G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ}
    (φ : α → Fin d → ℤ) (f : (Fin d → ℤ) →+ G) (A : Finset G) (B : Finset α)
    (Δ : AddSubgroup (Fin d → ℤ)) [Δ.FiniteIndex] (r : ℕ) (hsize : Δ.index ≤ r + 1)
    (hstable : ∀ D ⊆ B, B.card ≤ D.card + r → generatedSubgroup φ D = generatedSubgroup φ B)
    (L R : Fin d → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hφ : ∀ a ∈ B, ∀ j, |(φ a j : ℝ)| ≤ L j)
    (c : Fin d → ℤ)
    (hseed : ∀ w ∈ Δ, (∀ j, |(w j : ℝ)| ≤ R j + (Δ.index : ℝ) * L j) →
      f (c + w) ∈ A.subsetSum)
    (hinj : Set.InjOn (fun a => f (φ a)) B)
    (hdisjoint : Disjoint A (B.image (fun a => f (φ a)))) :
    ∃ W ⊆ B, W.card ≤ Δ.index ^ 2 ∧
      ∀ x ∈ generatedSubgroup φ B, (∀ j, |(x j : ℝ)| ≤ R j) →
        f (c + x) ∈ (A ∪ W.image (fun a => f (φ a))).subsetSum := by
  classical
  obtain ⟨W, hWB, hWcard, hcover⟩ := delta_exists_uniform_residue_pool φ B Δ r hsize hstable
  have hdisjointW : Disjoint A (W.image (fun a => f (φ a))) :=
    hdisjoint.mono_right (Finset.image_mono _ hWB)
  refine ⟨W, hWB, hWcard, ?_⟩
  intro x hx hxbounds
  obtain ⟨S, hSW, hScard, hmod⟩ := hcover x hx
  let s : Fin d → ℤ := ∑ a ∈ S, φ a
  have hSB : S ⊆ B := hSW.trans hWB
  have hsumBound (j : Fin d) : |(s j : ℝ)| ≤ (Δ.index : ℝ) * L j := by
    calc
      _ = |∑ a ∈ S, (φ a j : ℝ)| := by simp only [s, Finset.sum_apply, Int.cast_sum]
      _ ≤ ∑ a ∈ S, |(φ a j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ S, L j := Finset.sum_le_sum (fun a ha => hφ a (hSB ha) j)
      _ = (S.card : ℝ) * L j := by simp
      _ ≤ (Δ.index : ℝ) * L j := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show S.card ≤ Δ.index by omega)) (hL j)
  have hnegmod : x - s ∈ Δ := by
    simpa only [neg_sub] using Δ.neg_mem hmod
  have hw (j : Fin d) : |((x - s) j : ℝ)| ≤ R j + (Δ.index : ℝ) * L j := by
    simp only [Pi.sub_apply, Int.cast_sub]
    exact (abs_sub _ _).trans (add_le_add (hxbounds j) (hsumBound j))
  have hcoarse := hseed (x - s) hnegmod hw
  have hsum : (∑ a ∈ S, f (φ a)) ∈ (W.image (fun a => f (φ a))).subsetSum := by
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨S.image (fun a => f (φ a)), Finset.image_mono _ hSW, ?_⟩
    exact Finset.sum_image (fun a ha b hb hab => hinj (hSB ha) (hSB hb) hab)
  have heq : f (c + x) = f (c + (x - s)) + ∑ a ∈ S, f (φ a) := by
    rw [← map_sum]
    change f (c + x) = f (c + (x - s)) + f s
    rw [← map_add]
    congr 1
    abel
  rw [heq]
  exact subsetSum_add_subset_union hdisjointW
    (Finset.mem_add.mpr ⟨f (c + (x - s)), hcoarse, ∑ a ∈ S, f (φ a), hsum, rfl⟩)

end Erdos587.CFP
