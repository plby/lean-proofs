import Wikipedia.SmoothSixDPoincare.OrderedMorseSurgeries
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Wikipedia.SmoothSixDPoincare.MorseDiskPropagation
import Wikipedia.SmoothSixDPoincare.MorseNegation

/-!
# The endpoints of the constructed finite surgery sequence

Compactness and Fermat identify the first and last critical points with the
unique global extrema. The sequence begins with an empty sublevel and ends
with the whole manifold. Its actual first upper and last lower levels bound
standard disks on their respective sides.
-/

noncomputable section

open Set Filter Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

variable (S : SurgeryWindows E f)

def first (h : 0 < S.count) : criticalPoints E f := S.point ⟨0, h⟩

def last (h : 0 < S.count) : criticalPoints E f :=
  S.point ⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩

theorem value_first_le (h : 0 < S.count) (p : criticalPoints E f) :
    f (S.first h) ≤ f p := by
  have hle : (⟨0, h⟩ : Fin S.count) ≤ S.point.symm p := Nat.zero_le _
  simpa only [first, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

theorem value_le_last (h : 0 < S.count) (p : criticalPoints E f) :
    f p ≤ f (S.last h) := by
  have hle : S.point.symm p ≤ (⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩ : Fin S.count) :=
    Nat.le_sub_one_of_lt (S.point.symm p).isLt
  simpa only [last, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hf

theorem count_pos [Nonempty M] : 0 < S.count := by
  obtain ⟨p, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  have hp : p ∈ criticalPoints E f :=
    mem_criticalPoints_of_localMin hf (Eventually.of_forall (fun x => hmin (mem_univ x)))
  exact lt_of_le_of_lt (Nat.zero_le _) (S.point.symm ⟨p, hp⟩).isLt

theorem first_globalMin (h : 0 < S.count) (x : M) : f (S.first h) ≤ f x := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ criticalPoints E f :=
    mem_criticalPoints_of_localMin hf (Eventually.of_forall (fun y => hmin (mem_univ y)))
  exact (S.value_first_le h ⟨p, hp⟩).trans (hmin (mem_univ x))

theorem last_globalMax (h : 0 < S.count) (x : M) : f x ≤ f (S.last h) := by
  obtain ⟨p, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ criticalPoints E f :=
    mem_criticalPoints_of_localMax hf (Eventually.of_forall (fun y => hmax (mem_univ y)))
  exact (hmax (mem_univ x)).trans (S.value_le_last h ⟨p, hp⟩)

theorem unique_first (h : 0 < S.count) (x : M) (hx : f x ≤ f (S.first h)) :
    x = (S.first h).val := by
  have hxcrit : x ∈ criticalPoints E f := mem_criticalPoints_of_localMin hf
    (Eventually.of_forall (fun y => hx.trans (S.first_globalMin hf h y)))
  exact S.distinct hxcrit (S.first h).property (le_antisymm hx (S.first_globalMin hf h x))

theorem unique_last (h : 0 < S.count) (x : M) (hx : f (S.last h) ≤ f x) :
    x = (S.last h).val := by
  have hxcrit : x ∈ criticalPoints E f := mem_criticalPoints_of_localMax hf
    (Eventually.of_forall (fun y => (S.last_globalMax hf h y).trans hx))
  exact S.distinct hxcrit (S.last h).property (le_antisymm (S.last_globalMax hf h x) hx)

theorem first_lower_empty (h : 0 < S.count) :
    {x : M | f x ≤ S.lower (S.first h)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_le_of_gt (S.lower_lt_value (S.first h))) ((S.first_globalMin hf h x).trans hx)

theorem last_upper_univ (h : 0 < S.count) :
    {x : M | f x ≤ S.upper (S.last h)} = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (S.last_globalMax hf h x).trans (S.value_lt_upper (S.last h)).le

open Classical in
theorem first_index_zero (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.first h)).chart.NegativeCoordinates = 0 := by
  let := (S.data (S.first h)).chart.subsingleton_negative_of_localMin
    (Eventually.of_forall (S.first_globalMin hf h))
  exact Module.finrank_zero_of_subsingleton

open Classical in
theorem last_index_dimension (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.last h)).chart.NegativeCoordinates = Module.finrank ℝ E := by
  let := (S.data (S.last h)).chart.subsingleton_positive_of_localMax
    (Eventually.of_forall (S.last_globalMax hf h))
  have hz : Module.finrank ℝ (S.data (S.last h)).chart.PositiveCoordinates = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hz, add_zero] using (S.data (S.last h)).chart.finrank_negative_add_positive

theorem two_le_count [Nonempty M] (hdim : 0 < Module.finrank ℝ E) : 2 ≤ S.count := by
  have h := S.count_pos hf
  by_contra htwo
  have hcount : S.count = 1 := by omega
  have heq : S.first h = S.last h := by
    apply S.point.injective.eq_iff.mpr
    apply Fin.ext
    simp only [hcount]
    rfl
  have hi := S.first_index_zero hf h
  rw [heq, S.last_index_dimension hf h] at hi
  omega

variable [FiniteDimensional ℝ E] [T2Space M]

/-- The entire first upper sublevel is a standard disk with its actual level boundary. -/
theorem nonempty_firstSublevelDisk (h : 0 < S.count) :
    Nonempty (SublevelDisk (Module.finrank ℝ E) f (S.upper (S.first h))) := by
  apply (S.data (S.first h)).chart.nonempty_sublevelDisk_before_next_critical hf
    (S.unique_first hf h) (S.value_lt_upper (S.first h))
  intro x hxlo hxhi hxcrit
  have hxlower : S.lower (S.first h) ≤ f x :=
    (S.lower_lt_value (S.first h)).le.trans hxlo.le
  have hxp := S.isolated (S.first h) x hxcrit ⟨hxlower, hxhi⟩
  rw [hxp] at hxlo
  exact lt_irrefl _ hxlo

/-- The entire superlevel at the last lower endpoint is a boundary-compatible standard disk. -/
theorem nonempty_lastSuperlevelDisk (h : 0 < S.count) :
    Nonempty (SublevelDisk (Module.finrank ℝ E) (fun x => -f x) (-S.lower (S.last h))) := by
  apply (S.data (S.last h)).chart.neg.nonempty_sublevelDisk_before_next_critical hf.neg
    (fun x hx => S.unique_last hf h x (neg_le_neg_iff.mp hx))
    (neg_lt_neg (S.lower_lt_value (S.last h)))
  intro x hxlo hxhi hxcrit
  have hxcrit' : x ∈ criticalPoints E f := by
    rw [← criticalPoints_neg (E := E) f]
    exact hxcrit
  have hxlower : S.lower (S.last h) ≤ f x := neg_le_neg_iff.mp hxhi
  have hxupper : f x ≤ S.upper (S.last h) :=
    (neg_lt_neg_iff.mp hxlo).le.trans (S.value_lt_upper (S.last h)).le
  have hxp := S.isolated (S.last h) x hxcrit' ⟨hxlower, hxupper⟩
  rw [hxp] at hxlo
  exact lt_irrefl _ hxlo

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
