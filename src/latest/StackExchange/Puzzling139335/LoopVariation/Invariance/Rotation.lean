import StackExchange.Puzzling139335.LoopVariation.Invariance.Cyclic
import Mathlib.Topology.Piecewise

/-!
# Changing the starting point of an interval loop

The parameter is translated until it reaches the end of the interval, then
continues from its beginning. The two formulas agree after evaluation by a
closed loop. A finite increasing list splits at the wrap point; moving its
first block to the end restores increasing order without changing a cyclic score.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {X : Type*}

/-- The interval parameter translated to start at `q`, wrapping at `b`. -/
def shiftParameter (a b q t : ℝ) : ℝ :=
  if t < a + b - q then q + t - a else q + t - b

/-- Read a closed interval loop starting at the parameter `q`. -/
def rotateLoop (f : ℝ → X) (a b q : ℝ) : ℝ → X :=
  f ∘ shiftParameter a b q

theorem shiftParameter_mapsTo_Icc {a b q : ℝ} (hq : q ∈ Icc a b) :
    MapsTo (shiftParameter a b q) (Icc a b) (Icc a b) := by
  intro t ht
  unfold shiftParameter
  split_ifs with h
  · constructor <;> linarith [hq.1, hq.2, ht.1, ht.2]
  · constructor <;> linarith [hq.1, hq.2, ht.1, ht.2]

theorem shiftParameter_mapsTo_Ico {a b q : ℝ} (hq : q ∈ Icc a b) :
    MapsTo (shiftParameter a b q) (Ico a b) (Ico a b) := by
  intro t ht
  unfold shiftParameter
  split_ifs with h
  · constructor <;> linarith [hq.1, hq.2, ht.1, ht.2]
  · constructor <;> linarith [hq.1, hq.2, ht.1, ht.2]

theorem shiftParameter_injOn_Ico {a b q : ℝ} :
    InjOn (shiftParameter a b q) (Ico a b) := by
  intro t ht u hu heq
  unfold shiftParameter at heq
  split_ifs at heq <;> linarith [ht.1, ht.2, hu.1, hu.2]

theorem shiftParameter_double {a b q t : ℝ} (hq : q ∈ Icc a b) (ht : t ∈ Icc a b) :
    shiftParameter a b q (shiftParameter a b (a + b - q) t) =
      if t < b then t else a := by
  unfold shiftParameter
  split_ifs <;> linarith [ht.1, ht.2, hq.1, hq.2]

theorem rotateLoop_double_eqOn {f : ℝ → X} {a b q : ℝ}
    (hq : q ∈ Icc a b) (hclose : f a = f b) :
    EqOn (rotateLoop (rotateLoop f a b q) a b (a + b - q)) f (Icc a b) := by
  intro t ht
  simp only [rotateLoop, Function.comp_apply, shiftParameter_double hq ht]
  split_ifs with h
  · rfl
  · have ht' : t = b := le_antisymm ht.2 (le_of_not_gt h)
    simpa only [ht'] using hclose

theorem rotateLoop_start {f : ℝ → X} {a b q : ℝ} (hq : q ∈ Ico a b) :
    rotateLoop f a b q a = f q := by
  have h : a < a + b - q := by linarith [hq.2]
  simp only [rotateLoop, Function.comp_apply, shiftParameter, if_pos h,
    add_sub_cancel_right]

theorem rotateLoop_end {f : ℝ → X} {a b q : ℝ} (hq : q ∈ Icc a b) :
    rotateLoop f a b q b = f q := by
  have h : ¬ b < a + b - q := by linarith [hq.1]
  simp only [rotateLoop, Function.comp_apply, shiftParameter, if_neg h,
    add_sub_cancel_right]

theorem rotateLoop_closes {f : ℝ → X} {a b q : ℝ} (hq : q ∈ Ico a b) :
    rotateLoop f a b q a = rotateLoop f a b q b := by
  rw [rotateLoop_start hq, rotateLoop_end (Ico_subset_Icc_self hq)]

theorem rotateLoop_injOn_Ico {f : ℝ → X} {a b q : ℝ}
    (hq : q ∈ Icc a b) (hfi : InjOn f (Ico a b)) :
    InjOn (rotateLoop f a b q) (Ico a b) := by
  intro t ht u hu heq
  exact shiftParameter_injOn_Ico ht hu
    (hfi (shiftParameter_mapsTo_Ico hq ht) (shiftParameter_mapsTo_Ico hq hu) heq)

variable [PseudoMetricSpace X]

theorem rotateLoop_continuousOn {f : ℝ → X} {a b q : ℝ}
    (hq : q ∈ Icc a b) (hf : ContinuousOn f (Icc a b)) (hclose : f a = f b) :
    ContinuousOn (rotateLoop f a b q) (Icc a b) := by
  simp only [rotateLoop, Function.comp_def, shiftParameter, apply_ite]
  apply ContinuousOn.if
  · intro t ht
    have hcut : t = a + b - q := by
      have ht' : t ∈ frontier (Iio (a + b - q)) := ht.2
      simpa only [frontier_Iio, mem_singleton_iff] using ht'
    have h₁ : q + t - a = b := by linarith
    have h₂ : q + t - b = a := by linarith
    rw [h₁, h₂, hclose]
  · change ContinuousOn (fun t => f (q + t - a))
      (Icc a b ∩ closure (Iio (a + b - q)))
    rw [closure_Iio]
    apply hf.comp (by fun_prop)
    intro t ht
    have ht' : t ≤ a + b - q := ht.2
    constructor <;> linarith [ht.1.1, ht.1.2, hq.1, hq.2]
  · have hset : {t : ℝ | ¬ t < a + b - q} = Ici (a + b - q) := by
      ext t
      simp only [mem_ofPred_eq, mem_Ici, not_lt]
    rw [hset, isClosed_Ici.closure_eq]
    apply hf.comp (by fun_prop)
    intro t ht
    have ht' : a + b - q ≤ t := ht.2
    constructor <;> linarith [ht.1.1, ht.1.2, hq.1, hq.2]

omit [PseudoMetricSpace X] in
theorem rotateLoop_image_Icc {f : ℝ → X} {a b q : ℝ}
    (hq : q ∈ Icc a b) (hclose : f a = f b) :
    rotateLoop f a b q '' Icc a b = f '' Icc a b := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨shiftParameter a b q t, shiftParameter_mapsTo_Icc hq ht, rfl⟩
  · rintro z ⟨t, ht, rfl⟩
    have hq' : a + b - q ∈ Icc a b := by
      constructor <;> linarith [hq.1, hq.2]
    refine ⟨shiftParameter a b (a + b - q) t,
      shiftParameter_mapsTo_Icc hq' ht, ?_⟩
    exact rotateLoop_double_eqOn hq hclose ht

private theorem pairwise_split_lt {xs : List ℝ} (hxs : xs.Pairwise (· ≤ ·)) (m : ℝ) :
    ∃ lo hi : List ℝ, xs = lo ++ hi ∧
      (∀ t ∈ lo, t < m) ∧ (∀ t ∈ hi, m ≤ t) := by
  induction xs with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x xs ih =>
      by_cases hx : x < m
      · obtain ⟨lo, hi, hsplit, hlo, hhi⟩ := ih hxs.of_cons
        refine ⟨x :: lo, hi, by simp only [hsplit, List.cons_append], ?_, hhi⟩
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hx
        · exact hlo t ht
      · refine ⟨[], x :: xs, rfl, by simp, ?_⟩
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact le_of_not_gt hx
        · exact (le_of_not_gt hx).trans (List.rel_of_pairwise_cons hxs ht)

/-- Wrap an increasing parameter list and move its first block to its end.
This realizes its rotated-loop score as an ordinary increasing cyclic score. -/
theorem cycleScoresOn_rotateLoop_subset (ε : ℝ) (f : ℝ → X) {a b q : ℝ}
    (hq : q ∈ Icc a b) :
    cycleScoresOn ε (rotateLoop f a b q) (Icc a b) ⊆ cycleScoresOn ε f (Icc a b) := by
  rintro r ⟨xs, hxs, rfl⟩
  obtain ⟨lo, hi, rfl, hlo, hhi⟩ := pairwise_split_lt hxs.1 (a + b - q)
  have hlo_chain : IsChainOn (Icc a b) lo :=
    ⟨(List.pairwise_append.mp hxs.1).1,
      fun t ht => hxs.2 t (List.mem_append.mpr (Or.inl ht))⟩
  have hhi_chain : IsChainOn (Icc a b) hi :=
    ⟨(List.pairwise_append.mp hxs.1).2.1,
      fun t ht => hxs.2 t (List.mem_append.mpr (Or.inr ht))⟩
  have hlo_map : lo.map (shiftParameter a b q) = lo.map (fun t => q + t - a) := by
    apply List.map_congr_left
    intro t ht
    exact if_pos (hlo t ht)
  have hhi_map : hi.map (shiftParameter a b q) = hi.map (fun t => q + t - b) := by
    apply List.map_congr_left
    intro t ht
    exact if_neg (not_lt.mpr (hhi t ht))
  refine ⟨hi.map (fun t => q + t - b) ++ lo.map (fun t => q + t - a), ?_, ?_⟩
  · constructor
    · apply List.pairwise_append.mpr
      refine ⟨List.pairwise_map.mpr (hhi_chain.1.imp ?_),
        List.pairwise_map.mpr (hlo_chain.1.imp ?_), ?_⟩
      · intro u v huv
        linarith
      · intro u v huv
        linarith
      · intro u hu v hv
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
        linarith [(hhi_chain.2 t ht).2, (hlo_chain.2 s hs).1]
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
        have htI := hhi_chain.2 t ht
        have htm := hhi t ht
        constructor <;> linarith [htI.1, htI.2, hq.1, hq.2]
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
        have htI := hlo_chain.2 t ht
        have htm := hlo t ht
        constructor <;> linarith [htI.1, htI.2, hq.1, hq.2]
  · calc
      cycleScore ε (rotateLoop f a b q) (lo ++ hi) =
          cycleScore ε f ((lo ++ hi).map (shiftParameter a b q)) :=
        (cycleScore_map ε f (shiftParameter a b q) (lo ++ hi)).symm
      _ = cycleScore ε f (lo.map (fun t => q + t - a) ++
          hi.map (fun t => q + t - b)) := by rw [List.map_append, hlo_map, hhi_map]
      _ = cycleScore ε f (hi.map (fun t => q + t - b) ++
          lo.map (fun t => q + t - a)) := cycleScore_append_comm ε f _ _

/-- Changing the starting point of a closed loop preserves the exact set of
attainable cyclic finite-chain scores. -/
theorem cycleScoresOn_rotateLoop (ε : ℝ) (f : ℝ → X) {a b q : ℝ}
    (hq : q ∈ Icc a b) (hclose : f a = f b) :
    cycleScoresOn ε (rotateLoop f a b q) (Icc a b) = cycleScoresOn ε f (Icc a b) := by
  apply Subset.antisymm (cycleScoresOn_rotateLoop_subset ε f hq)
  have hq' : a + b - q ∈ Icc a b := by
    constructor <;> linarith [hq.1, hq.2]
  have h := cycleScoresOn_rotateLoop_subset ε (rotateLoop f a b q) hq'
  rw [cycleScoresOn_congr (rotateLoop_double_eqOn hq hclose)] at h
  exact h

theorem loopVariationOn_rotateLoop (ε : ℝ) (f : ℝ → X) {a b q : ℝ}
    (hq : q ∈ Icc a b) (hclose : f a = f b) :
    loopVariationOn ε (rotateLoop f a b q) (Icc a b) = loopVariationOn ε f (Icc a b) := by
  unfold loopVariationOn
  rw [cycleScoresOn_rotateLoop ε f hq hclose]

end

end Puzzling139335.LoopVariation
