import Wikipedia.HopfProblem.DegreeCollapseThreeFourPresentation
import Wikipedia.HopfProblem.DegreeCollapseSublevelFirstTwoHandle

/-!
# Construct the actual three/four blocks below an untouched regular cut

Below-cut ordering, a unique minimum there, and the absence of all other
indices construct a first minimum, an index-three prefix, and the following
index-four block. Their endpoint is the last critical point below the cut.
The entire remaining band is proved regular, including the cut itself.
No global ordering or restrictions above the cut are required.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] in
open Classical in
theorem AdaptedSurgeryWindows.exists_three_four_blocks_below_cut
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hreg : ∀ y, f y = b → y ∉ criticalPoints E f)
    (horder : ∀ p q : criticalPoints E f, f q < b → f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hcut : ∀ p : criticalPoints E f, f p < b → A.toSurgeryWindows.upper p < b)
    (m : criticalPoints E f) (hmb : f m < b)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m)
    (hindices : ∀ p : criticalPoints E f, f p < b →
      nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨
        nativeMorseIndex E f p = 4) :
    ∃ r c : ℕ, ∃ hc : r + c < A.toSurgeryWindows.count,
      A.toSurgeryWindows.HasIndexThreeBlock 0 r ∧
      ThreeFourPresentation.HasIndexFourBlock A.toSurgeryWindows r c ∧
      A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩) < b ∧
      (∀ i : Fin A.toSurgeryWindows.count,
        f (A.toSurgeryWindows.point i) < b ↔ i.val ≤ r + c) ∧
      ∀ y, f y ∈ Icc
          (A.toSurgeryWindows.upper (A.toSurgeryWindows.point ⟨r + c, hc⟩)) b →
        y ∉ criticalPoints E f := by
  let _ : Nonempty M := ⟨m.val⟩
  let S := A.toSurgeryWindows
  have hn : 0 < S.count := S.count_pos hf
  let z : Fin S.count := ⟨0, hn⟩
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hfirst : index z = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hzb : f (S.point z) < b := (S.value_first_le hn m).trans_lt hmb
  have hzm : S.point z = m := hminimum _ hzb hfirst
  let K := Finset.univ.filter (fun i : Fin S.count => f (S.point i) < b)
  have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzb⟩
  have hK : K.Nonempty := ⟨z, hzK⟩
  let v := K.max' hK
  have hvb : f (S.point v) < b := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hv (i : Fin S.count) : f (S.point i) < b ↔ i ≤ v := by
    constructor
    · intro hi
      exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro hi
      exact (S.point_strictMono.monotone hi).trans_lt hvb
  let L := K.filter (fun i => index i ≤ 3)
  have hzL : z ∈ L := Finset.mem_filter.mpr ⟨hzK, by rw [hfirst]; decide⟩
  have hL : L.Nonempty := ⟨z, hzL⟩
  let u := L.max' hL
  have huK : u ∈ K := (Finset.mem_filter.mp (L.max'_mem hL)).1
  have hub : f (S.point u) < b := (Finset.mem_filter.mp huK).2
  have huindex : index u ≤ 3 := (Finset.mem_filter.mp (L.max'_mem hL)).2
  have huv : u ≤ v := (hv u).mp hub
  have hu (i : Fin S.count) (hib : f (S.point i) < b) : i ≤ u ↔ index i ≤ 3 := by
    constructor
    · intro hi
      rcases lt_or_eq_of_le hi with hlt | rfl
      · exact (horder _ _ hub (S.point_strictMono hlt)).trans huindex
      · exact huindex
    · intro hi
      exact L.le_max' i (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hib⟩, hi⟩)
  have hnonzero (i : Fin S.count) (hib : f (S.point i) < b) (hi : 0 < i.val) :
      index i ≠ 0 := by
    intro hzero
    have he := (hminimum _ hib hzero).trans hzm.symm
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have huc : u.val + (v.val - u.val) = v.val := by omega
  have hc : u.val + (v.val - u.val) < S.count := by omega
  have hlast : S.point ⟨u.val + (v.val - u.val), hc⟩ = S.point v := by
    congr 1
    exact Fin.ext huc
  refine ⟨u.val, v.val - u.val, hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hiu
    have hiu' : i ≤ u := by change i.val ≤ u.val; omega
    have hib := (hv i).mpr (hiu'.trans huv)
    have hi3 := (hu i hib).mp hiu'
    have hi0 := hnonzero i hib hi
    have hidx := hindices (S.point i) hib
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    change index i = 0 ∨ index i = 3 ∨ index i = 4 at hidx
    omega
  · intro i hui hiv
    have hiv' : i ≤ v := by change i.val ≤ v.val; omega
    have hib := (hv i).mpr hiv'
    have hi3 : ¬index i ≤ 3 := fun h => (not_le_of_gt hui) ((hu i hib).mpr h)
    have hidx := hindices (S.point i) hib
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 4
    change index i = 0 ∨ index i = 3 ∨ index i = 4 at hidx
    omega
  · change S.upper (S.point ⟨u.val + (v.val - u.val), hc⟩) < b
    rw [hlast]
    exact hcut _ hvb
  · intro i
    change f (S.point i) < b ↔ i.val ≤ u.val + (v.val - u.val)
    rw [huc]
    exact hv i
  · intro y hy hcrit
    have hyb : f y < b := lt_of_le_of_ne hy.2 (fun he => hreg y he hcrit)
    obtain ⟨i, hi⟩ := S.point.surjective ⟨y, hcrit⟩
    have hib : f (S.point i) < b := by rw [hi]; exact hyb
    have hle : f y ≤ f (S.point v) := by
      simpa only [hi] using S.point_strictMono.monotone ((hv i).mp hib)
    change S.upper (S.point ⟨u.val + (v.val - u.val), hc⟩) ≤ f y ∧ f y ≤ b at hy
    rw [hlast] at hy
    exact (hle.trans_lt (S.value_lt_upper (S.point v))).not_ge hy.1

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
