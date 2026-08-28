import Wikipedia.HopfProblem.DegreeCollapseSurjectiveMiddleMatrix

/-!
# The sizes of the retained matrix are the intrinsic Morse counts

An exact equivalence counts the critical points in an interval of the
chronological enumeration. The constructed index-two prefix and index-three
block therefore have lengths equal to their actual intrinsic index counts.
-/

noncomputable section

open Set Function Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem nativeMorseCount_eq_interval_length (S : SurgeryWindows E f)
    (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ S.count)
    (hindex : ∀ i : Fin S.count, nativeMorseIndex E f (S.point i) = k ↔
      a ≤ i.val ∧ i.val < b) :
    nativeMorseCount E f k = b - a := by
  let K : Set M := {x | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = k}
  let u : Fin (b - a) → K :=
    fun j => ⟨(S.point ⟨a + j.val, by omega⟩).val,
      (S.point ⟨a + j.val, by omega⟩).property,
      (hindex ⟨a + j.val, by omega⟩).mpr
        (show a ≤ a + j.val ∧ a + j.val < b from ⟨by omega, by omega⟩)⟩
  have hu : Bijective u := by
    constructor
    · intro i j hij
      have hv : (u i).val = (u j).val := congrArg Subtype.val hij
      have hp : S.point ⟨a + i.val, by omega⟩ = S.point ⟨a + j.val, by omega⟩ :=
        Subtype.ext hv
      have he := congrArg Fin.val (S.point.injective hp)
      exact Fin.ext (by simpa only [Nat.add_left_cancel_iff] using he)
    · intro x
      let i := S.point.symm ⟨x.val, x.property.1⟩
      have hi : S.point i = ⟨x.val, x.property.1⟩ := S.point.apply_symm_apply _
      have hxi : nativeMorseIndex E f (S.point i) = k := by
        rw [hi]
        exact x.property.2
      have hib := (hindex i).mp hxi
      refine ⟨⟨i.val - a, by omega⟩, ?_⟩
      apply Subtype.ext
      change (S.point ⟨a + (i.val - a), _⟩).val = x.val
      have he : (⟨a + (i.val - a), by omega⟩ : Fin S.count) = i :=
        Fin.ext (show a + (i.val - a) = i.val by omega)
      rw [he, hi]
  have hc := (Nat.card_congr (Equiv.ofBijective u hu)).symm
  change K.ncard = b - a
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using hc

theorem native_middle_block_counts (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c)
    (hafter : ∀ i : Fin S.count, r + c < i.val →
      4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    nativeMorseCount E f 2 = r ∧ nativeMorseCount E f 3 = c := by
  have hn := S.count_pos hf
  have hi0 (i : Fin S.count) (hi : i.val = 0) : nativeMorseIndex E f (S.point i) = 0 := by
    have he : i = ⟨0, hn⟩ := Fin.ext hi
    rw [he]
    exact (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans
      (S.first_index_zero hf hn)
  have hi2 (i : Fin S.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
      nativeMorseIndex E f (S.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin S.count) (hri : r < i.val) (hic : i.val ≤ r + c) :
      nativeMorseIndex E f (S.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (hthree i hri hic)
  have hi4 (i : Fin S.count) (hic : r + c < i.val) :
      4 ≤ nativeMorseIndex E f (S.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    exact hafter i hic
  have hcases (i : Fin S.count) :
      (i.val = 0 ∧ nativeMorseIndex E f (S.point i) = 0) ∨
      (0 < i.val ∧ i.val ≤ r ∧ nativeMorseIndex E f (S.point i) = 2) ∨
      (r < i.val ∧ i.val ≤ r + c ∧ nativeMorseIndex E f (S.point i) = 3) ∨
      (r + c < i.val ∧ 4 ≤ nativeMorseIndex E f (S.point i)) := by
    by_cases hz : i.val = 0
    · exact Or.inl ⟨hz, hi0 i hz⟩
    by_cases hr : i.val ≤ r
    · exact Or.inr (Or.inl ⟨by omega, hr, hi2 i (by omega) hr⟩)
    by_cases hrc : i.val ≤ r + c
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hrc, hi3 i (by omega) hrc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hi4 i (by omega)⟩))
  constructor
  · have hh := nativeMorseCount_eq_interval_length S 2 1 (r + 1) (by omega) (by omega)
      (fun i => by have h := hcases i; omega)
    simpa only [Nat.add_sub_cancel_right] using hh
  · have hh := nativeMorseCount_eq_interval_length S 3 (r + 1) (r + c + 1)
      (by omega) (by omega) (fun i => by have h := hcases i; omega)
    have he : r + c + 1 - (r + 1) = c := by omega
    simpa only [he] using hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
