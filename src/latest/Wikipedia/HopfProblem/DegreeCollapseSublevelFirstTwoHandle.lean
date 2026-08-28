import Wikipedia.HopfProblem.DegreeCollapseSublevelFirstOneHandle
import Wikipedia.HopfProblem.DegreeCollapseMinimumBeltDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseFirstPositiveTwoHandle

/-!
# The first below-cut two-handle has a native standard sphere below it

With no index-one point below the cut, the first index-two point has
only minima before it. If the below-cut minimum is unique, the entire
lower surgery level is the native first minimum belt transported across
a genuinely critical-point-free band. This constructs its standard
six-sphere diffeomorphism and hence its simple connectivity.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem AdaptedSurgeryWindows.exists_first_index_two_below_cut
    (S : AdaptedSurgeryWindows E f) (b : ℝ)
    (horder : ∀ p q : criticalPoints E f, f q < b → f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hnoone : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p ≠ 1)
    (q₀ : criticalPoints E f) (hq₀b : f q₀ < b) (hq₀ : nativeMorseIndex E f q₀ = 2) :
    ∃ q : criticalPoints E f, f q < b ∧ nativeMorseIndex E f q = 2 ∧
      ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0 := by
  classical
  let _ := S.finite.fintype
  let K := Finset.univ.filter (fun p : criticalPoints E f =>
    f p < b ∧ nativeMorseIndex E f p = 2)
  have hq₀K : q₀ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀b, hq₀⟩
  obtain ⟨q, hqK, hmin⟩ := K.exists_min_image (fun p : criticalPoints E f => f p) ⟨q₀, hq₀K⟩
  obtain ⟨hqb, hq⟩ := (Finset.mem_filter.mp hqK).2
  refine ⟨q, hqb, hq, ?_⟩
  intro p hp
  have hle := horder p q hqb hp
  have hne : nativeMorseIndex E f p ≠ 2 := by
    intro h
    have hpK : p ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.trans hqb, h⟩
    exact (not_le_of_gt hp) (hmin p hpK)
  have hn := hnoone p (hp.trans hqb)
  omega

theorem AdaptedSurgeryWindows.nonempty_lower_sphereDiffeomorph_of_first_two
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) {b : ℝ} (m q : criticalPoints E f)
    (hq : nativeMorseIndex E f q = 2) (hqb : f q < b)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m) :
    let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
    Nonempty (Diffeomorph (𝓡 6) 𝓘(ℝ, RegularLevel.Model E)
      (Hemisphere.Sphere 6) (S.data q).LowerLevel ∞) := by
  let _ : Nonempty M := ⟨q.val⟩
  have hcount : 0 < S.toSurgeryWindows.count := S.toSurgeryWindows.count_pos hf
  let p := S.toSurgeryWindows.first hcount
  have hneg : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 0 :=
    S.toSurgeryWindows.first_index_zero hf hcount
  have hpindex : nativeMorseIndex E f p = 0 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hneg
  have hpq : f p < f q := lt_of_le_of_ne (S.toSurgeryWindows.value_first_le hcount q)
    (fun he => by
      have hpqeq : p = q := Subtype.ext (S.distinct p.property q.property he)
      rw [hpqeq, hq] at hpindex
      contradiction)
  have hpm : p = m := hminimum p (hpq.trans hqb) hpindex
  have hgap : S.toSurgeryWindows.upper p < S.toSurgeryWindows.lower q := S.separated p q hpq
  have hband : ∀ y, f y ∈ Icc (S.toSurgeryWindows.upper p) (S.toSurgeryWindows.lower q) →
      y ∉ criticalPoints E f := by
    intro y hy hcrit
    let r : criticalPoints E f := ⟨y, hcrit⟩
    have hrq : f r < f q := hy.2.trans_lt (S.toSurgeryWindows.lower_lt_value q)
    have hrm : r = m := hminimum r (hrq.trans hqb) (hbefore r hrq)
    have hrp : r = p := hrm.trans hpm.symm
    have hv : f y = f p := congrArg (fun z : criticalPoints E f => f z) hrp
    rw [hv] at hy
    exact (S.toSurgeryWindows.value_lt_upper p).not_ge hy.1
  have hpositive : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 6 + 1 := by
    have hsum := (S.data p).chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 6 + 1) := ⟨hpositive⟩
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let D := (SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 6).trans
    (native_index_zero_beltDiffeomorph (S.data p) hf hneg 6 (S.belt_surjective_at_first hf hcount))
  obtain ⟨R⟩ := RegularLevel.nonempty_regularLevelDiffeomorph hf hgap.le hband
  exact ⟨D.trans R⟩

theorem AdaptedSurgeryWindows.lower_level_simplyConnected_of_first_two
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) {b : ℝ} (m q : criticalPoints E f)
    (hq : nativeMorseIndex E f q = 2) (hqb : f q < b)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m) :
    SimplyConnectedSpace (S.data q).LowerLevel := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨D⟩ := S.nonempty_lower_sphereDiffeomorph_of_first_two hf hdim m q hq hqb
    hbefore hminimum
  exact D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
