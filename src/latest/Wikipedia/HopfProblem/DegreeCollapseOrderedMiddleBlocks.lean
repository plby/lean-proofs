import Wikipedia.HopfProblem.DegreeCollapseOuterIndexElimination
import Wikipedia.SmoothSixDPoincare.OrderedMiddleMatrix

/-!
# Construct the actual index-two prefix and index-three block

Finite index ordering, the unique minimum, and the absence of index-one
points determine the consecutive middle blocks. Their endpoint remains
strictly below the final maximum, and every later handle has index at least
four. No block decomposition or matrix arrangement is assumed.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem native_indices_monotone
    (S : SurgeryWindows E f)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q) :
    Monotone (fun i : Fin S.count => nativeMorseIndex E f (S.point i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact horder _ _ (S.point_strictMono hlt)
  · exact le_rfl

open Classical in
theorem exists_middle_index_blocks
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ, S.HasIndexTwoPrefix r ∧
      ∃ hc : r + c < S.count, S.HasIndexThreeBlock r c ∧ r + c + 1 < S.count ∧
        ∀ i : Fin S.count, r + c < i.val →
          4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by
  have hn := S.count_pos hf
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hmono : Monotone index := native_indices_monotone S horder
  have hfirst : index ⟨0, hn⟩ = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hlast : index ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ = 6 :=
    (nativeMorseIndex_eq_chart (S.data (S.last hn)).chart).trans
      ((S.last_index_dimension hf hn).trans hdim)
  have hcut (k : ℕ) : ∃ j : Fin S.count, ∀ i : Fin S.count, i ≤ j ↔ index i ≤ k := by
    let K := Finset.univ.filter (fun i : Fin S.count => index i ≤ k)
    have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rw [hfirst]; exact Nat.zero_le k⟩⟩
    let j := K.max' hK
    have hj : index j ≤ k := (Finset.mem_filter.mp (K.max'_mem hK)).2
    refine ⟨j, fun i => ⟨fun hij => (hmono hij).trans hj, ?_⟩⟩
    intro hi
    exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨a, ha⟩ := hcut 2
  obtain ⟨b, hb⟩ := hcut 3
  have hab : a ≤ b := (hb a).mpr (((ha a).mp le_rfl).trans (by omega))
  have hbLast : b.val + 1 < S.count := by
    have hb3 := (hb b).mp le_rfl
    have hne : b ≠ ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      intro he
      rw [he, hlast] at hb3
      omega
    have hvalne : b.val ≠ S.count - 1 := fun he => hne (Fin.ext he)
    omega
  have hnonzero (i : Fin S.count) (hi : 0 < i.val) : index i ≠ 0 := by
    intro hz
    have he : S.point i = S.first hn := Subtype.ext
      (native_index_zero_point_unique S hf hn hzero _ (S.point i).property hz)
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have hnonone (i : Fin S.count) : index i ≠ 1 :=
    native_index_one_excluded S hone _ (S.point i).property
  refine ⟨a.val, b.val - a.val, ?_, by omega, ?_, by omega, ?_⟩
  · intro i hi hia
    have hi2 := (ha i).mp (show i ≤ a from hia)
    have hi0 := hnonzero i hi
    have hi1 := hnonone i
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 2
    omega
  · intro i hai hib
    have hi3 := (hb i).mp (show i ≤ b by change i.val ≤ b.val; omega)
    have hi2 : ¬index i ≤ 2 := fun he => (not_le_of_gt hai) ((ha i).mpr he)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    omega
  · intro i hbi
    have hi3 : ¬index i ≤ 3 := fun he => (by
      have hh : i.val ≤ b.val := (hb i).mpr he
      omega)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change 4 ≤ index i
    omega

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
