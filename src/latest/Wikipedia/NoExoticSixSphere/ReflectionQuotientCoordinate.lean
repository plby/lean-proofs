import Wikipedia.NoExoticSixSphere.InvolutionQuotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The nonnegative coordinate on an actual involution quotient

A real chart with invariant source and reflection action gives a
well-defined nonnegative coordinate on the quotient. Continuity at points
of the chart follows from the open quotient projection and the original
chart, without imposing any global continuity outside that chart.
-/

noncomputable section

open Set Function Filter Topology

namespace NoExoticSixSphere.InvolutionQuotient

variable {X : Type*} [TopologicalSpace X] {σ : X → X}

abbrev HalfLine := {t : ℝ // 0 ≤ t}

structure ReflectionChart (σ : X → X) where
  coord : OpenPartialHomeomorph X ℝ
  source_invariant : ∀ x ∈ coord.source, σ x ∈ coord.source
  coordinate_swap : ∀ x ∈ coord.source, coord (σ x) = -coord x

theorem ReflectionChart.mem_source_swap_iff (c : ReflectionChart σ) (hσ : Involutive σ)
    (x : X) : σ x ∈ c.coord.source ↔ x ∈ c.coord.source := by
  constructor
  · intro hx
    simpa only [hσ x] using c.source_invariant (σ x) hx
  · exact c.source_invariant x

def ReflectionChart.foldValue (c : ReflectionChart σ) (x : X) : ℝ := by
  classical
  exact if x ∈ c.coord.source then |c.coord x| else 0

theorem ReflectionChart.foldValue_nonneg (c : ReflectionChart σ) (x : X) :
    0 ≤ c.foldValue x := by
  unfold ReflectionChart.foldValue
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem ReflectionChart.foldValue_swap (c : ReflectionChart σ) (hσ : Involutive σ)
    (x : X) : c.foldValue (σ x) = c.foldValue x := by
  by_cases hx : x ∈ c.coord.source
  · simp only [ReflectionChart.foldValue, if_pos hx,
      if_pos (c.source_invariant x hx), c.coordinate_swap x hx, abs_neg]
  · have hs : σ x ∉ c.coord.source := (c.mem_source_swap_iff hσ x).not.mpr hx
    simp only [ReflectionChart.foldValue, if_neg hx, if_neg hs]

def ReflectionChart.quotientValue (c : ReflectionChart σ) (hσ : Involutive σ) :
    Orbit σ hσ → ℝ :=
  Quotient.lift c.foldValue (by
    intro x y h
    rcases h with rfl | rfl
    · rfl
    · exact (c.foldValue_swap hσ x).symm)

theorem ReflectionChart.quotientValue_nonneg (c : ReflectionChart σ) (hσ : Involutive σ)
    (q : Orbit σ hσ) : 0 ≤ c.quotientValue hσ q :=
  Quotient.inductionOn q (fun x ↦ c.foldValue_nonneg x)

def ReflectionChart.coordinate (c : ReflectionChart σ) (hσ : Involutive σ)
    (q : Orbit σ hσ) : HalfLine :=
  ⟨c.quotientValue hσ q, c.quotientValue_nonneg hσ q⟩

theorem ReflectionChart.coordinate_proj_val (c : ReflectionChart σ) (hσ : Involutive σ)
    {x : X} (hx : x ∈ c.coord.source) :
    (c.coordinate hσ (proj σ hσ x)).val = |c.coord x| := by
  change c.foldValue x = _
  simp only [ReflectionChart.foldValue, if_pos hx]

theorem ReflectionChart.abs_mem_target (c : ReflectionChart σ) {x : X}
    (hx : x ∈ c.coord.source) : |c.coord x| ∈ c.coord.target := by
  by_cases h : 0 ≤ c.coord x
  · rw [abs_of_nonneg h]
    exact c.coord.map_source hx
  · rw [abs_of_neg (lt_of_not_ge h), ← c.coordinate_swap x hx]
    exact c.coord.map_source (c.source_invariant x hx)

theorem ReflectionChart.continuousAt_coordinate (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) {x : X} (hx : x ∈ c.coord.source) :
    ContinuousAt (c.coordinate hσ) (proj σ hσ x) := by
  apply (isOpenQuotientMap_proj σ hσ hcont).continuousAt_comp_iff.mp
  apply IsInducing.subtypeVal.continuousAt_iff.mpr
  have hc := (c.coord.continuousOn.continuousAt (c.coord.open_source.mem_nhds hx)).abs
  apply hc.congr_of_eventuallyEq
  filter_upwards [c.coord.open_source.mem_nhds hx] with y hy
  exact c.coordinate_proj_val hσ hy

end NoExoticSixSphere.InvolutionQuotient
