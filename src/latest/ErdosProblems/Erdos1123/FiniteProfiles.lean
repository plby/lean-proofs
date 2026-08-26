import ErdosProblems.Erdos1123.WeightedQuotient
import ErdosProblems.Erdos1123.FiniteSplitting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Finite distributions and their refinement by one new set -/

namespace Erdos1123
namespace WeightSequence

open scoped Classical

variable {α β ι : Type*}

theorem mass_finset (W : WeightSequence α) (n : ℕ) (s : Finset α)
    (hs : s ⊆ W.support n) : W.mass (s : Set α) n = ∑ x ∈ s, W.weight n x := by
  unfold mass
  simp only [Finset.mem_coe]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun hx => ⟨hs hx, hx⟩⟩

/-- The mass distribution of a finite labeling. -/
noncomputable def profile (W : WeightSequence α) (f : α → ι) (n : ℕ) (i : ι) : ℝ :=
  W.mass {x | f x = i} n

/-- Total variation without the conventional factor `1/2`. -/
noncomputable def profileDistance [Fintype ι] (W : WeightSequence α) (V : WeightSequence β)
    (f : α → ι) (g : β → ι) (n : ℕ) : ℝ :=
  ∑ i, |W.profile f n i - V.profile g n i|

theorem profile_eq_sum (W : WeightSequence α) (f : α → ι) (n : ℕ) (i : ι) :
    W.profile f n i = ∑ x ∈ (W.support n).filter (fun x => f x = i), W.weight n x := by
  simp [profile, mass, ← Finset.sum_filter]

/-- Append the membership bit of a new set to an old finite labeling. -/
noncomputable def splitLabel (f : α → ι) (A : Set α) (x : α) : ι × Bool :=
  (f x, decide (x ∈ A))

theorem profile_split_true (W : WeightSequence α) (f : α → ι) (A : Set α)
    (n : ℕ) (i : ι) :
    W.profile (splitLabel f A) n (i, true) = W.mass ({x | f x = i} ∩ A) n := by
  apply W.mass_congr
  intro x _
  simp [splitLabel, Prod.mk.injEq]

theorem profile_split_false (W : WeightSequence α) (f : α → ι) (A : Set α)
    (n : ℕ) (i : ι) :
    W.profile (splitLabel f A) n (i, false) =
      W.profile f n i - W.mass ({x | f x = i} ∩ A) n := by
  have h : W.profile (splitLabel f A) n (i, false) =
      W.mass ({x | f x = i} \ A) n := by
    apply W.mass_congr
    intro x _
    simp [splitLabel, Prod.mk.injEq]
  rw [h]
  have hsum := W.mass_inter_add_sdiff {x | f x = i} A n
  unfold profile
  linarith

/-- Independently chosen subsets of distinct label fibers do not interfere. -/
theorem fiber_inter_union {g : β → ι} {s : Finset β} (u : ι → Finset β)
    (hu : ∀ i, u i ⊆ s.filter (fun x => g x = i)) (i : ι) :
    {x | g x = i} ∩ (⋃ j, (u j : Set β)) = (u i : Set β) := by
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
    have hxj : g x = j := (Finset.mem_filter.mp (hu j hj)).2
    have hji : j = i := hxj.symm.trans hx
    simpa only [hji] using hj
  · intro hx
    exact ⟨(Finset.mem_filter.mp (hu i hx)).2, Set.mem_iUnion.mpr ⟨i, hx⟩⟩

theorem mass_preimage_eq_sum [Fintype ι] (W : WeightSequence α) (f : α → ι)
    (C : Set ι) (n : ℕ) :
    W.mass (f ⁻¹' C) n = ∑ i ∈ Finset.univ.filter (· ∈ C), W.profile f n i := by
  unfold profile mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Every Boolean event of the finite labels is controlled by their profile distance. -/
theorem abs_mass_preimage_sub_le [Fintype ι] (W : WeightSequence α)
    (V : WeightSequence β) (f : α → ι) (g : β → ι) (C : Set ι) (n : ℕ) :
    |W.mass (f ⁻¹' C) n - V.mass (g ⁻¹' C) n| ≤ W.profileDistance V f g n := by
  rw [W.mass_preimage_eq_sum, V.mass_preimage_eq_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro i _ _
  exact abs_nonneg _

/-- Refine matching finite labels by one new set. The error is bounded by the
old profile error and the largest atom of the target coordinate. -/
theorem exists_profile_refinement [Fintype ι] (W : WeightSequence α)
    (V : WeightSequence β) (f : α → ι) (g : β → ι) (A : Set α) (n : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hAtom : ∀ x ∈ V.support n, V.weight n x ≤ δ) :
    ∃ B : Set β, W.profileDistance V (splitLabel f A) (splitLabel g B) n ≤
      2 * W.profileDistance V f g n + 2 * (Fintype.card ι : ℝ) * δ := by
  have hex (i : ι) := exists_subset_two_errors
    ((V.support n).filter (fun x => g x = i)) (V.weight n) hδ
    (W.mass_nonneg ({x | f x = i} ∩ A) n)
    (W.mass_mono Set.inter_subset_left n)
    (fun x _ => V.nonneg n x)
    (fun x hx => hAtom x (Finset.mem_filter.mp hx).1)
  choose u hu hTrue hFalse using hex
  let B : Set β := ⋃ i, (u i : Set β)
  have hSelected (i : ι) : V.mass ({x | g x = i} ∩ B) n = ∑ x ∈ u i, V.weight n x := by
    rw [fiber_inter_union u hu i]
    exact V.mass_finset n (u i) ((hu i).trans (Finset.filter_subset _ _))
  have hErr (i : ι) :
      |W.profile (splitLabel f A) n (i, true) - V.profile (splitLabel g B) n (i, true)| +
      |W.profile (splitLabel f A) n (i, false) - V.profile (splitLabel g B) n (i, false)| ≤
        2 * (|W.profile f n i - V.profile g n i| + δ) := by
    rw [W.profile_split_true, V.profile_split_true, W.profile_split_false,
      V.profile_split_false, hSelected]
    have ht := hTrue i
    have hf := hFalse i
    rw [← V.profile_eq_sum g n i] at ht hf
    rw [abs_sub_comm] at ht hf
    exact (add_le_add ht hf).trans_eq (two_mul _).symm
  refine ⟨B, ?_⟩
  unfold profileDistance
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  calc
    _ ≤ ∑ i, 2 * (|W.profile f n i - V.profile g n i| + δ) :=
      Finset.sum_le_sum (fun i _ => hErr i)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp; ring

end WeightSequence
end Erdos1123
