import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.FiniteValueWindows
import Wikipedia.SmoothSixDPoincare.MorseAttachingTransport

/-!
# Compatible native surgery windows for the whole finite critical set

Every critical point receives actual surgery data. Its closed critical
window contains no other critical point, and the windows are strictly
ordered by the original function values. Consecutive critical points then
have a constructed ambient regular-band bridge between their windows.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

open Classical in
/-- Actual native surgeries with mutually compatible critical-value windows. -/
structure SurgeryWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) where
  finite : (criticalPoints E f).Finite
  distinct : InjOn f (criticalPoints E f)
  data : ∀ p : criticalPoints E f, MorseSurgeryData E f p.val
  isolated : ∀ (p : criticalPoints E f) (x : M), x ∈ criticalPoints E f →
    f x ∈ Icc (f p - (data p).radius ^ 2) (f p + (data p).radius ^ 2) → x = p.val
  separated : ∀ p q : criticalPoints E f, f p < f q →
    f p + (data p).radius ^ 2 < f q - (data q).radius ^ 2

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

namespace SurgeryWindows

variable (S : SurgeryWindows E f)

def lower (p : criticalPoints E f) : ℝ := f p - (S.data p).radius ^ 2
def upper (p : criticalPoints E f) : ℝ := f p + (S.data p).radius ^ 2

theorem lower_lt_value (p : criticalPoints E f) : S.lower p < f p := by
  dsimp [lower]
  nlinarith [(S.data p).radius_pos]

theorem value_lt_upper (p : criticalPoints E f) : f p < S.upper p := by
  dsimp [upper]
  nlinarith [(S.data p).radius_pos]

theorem upper_lt_lower (p q : criticalPoints E f) (hpq : f p < f q) :
    S.upper p < S.lower q := S.separated p q hpq

/-- The actual band between consecutive critical windows contains no critical point. -/
theorem regular_between (p q : criticalPoints E f)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ x, f x ∈ Icc (S.upper p) (S.lower q) → x ∉ criticalPoints E f := by
  intro x hx hcrit
  exact hconsecutive ⟨x, hcrit⟩
    ⟨(S.value_lt_upper p).trans_le hx.1, hx.2.trans_lt (S.lower_lt_value q)⟩

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Consecutive windows have an actual ambient bridge, with its entire sublevel and level maps. -/
theorem exists_bandBridge
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper p} = {x : M | f x ≤ S.lower q} ∧
        ∀ x : (S.data p).UpperLevel, (b x : M) = D x :=
  (S.data p).exists_smoothBandBridge (S.data q) hf (S.upper_lt_lower p q hpq).le
    (S.regular_between p q hconsecutive)

end SurgeryWindows

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct compatible actual surgeries at every critical point
of the original excellent function. -/
theorem nonempty_surgeryWindows
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) : Nonempty (SurgeryWindows E f) := by
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex : ∀ p : criticalPoints E f, ∃ d : MorseSurgeryData E f p.val, d.radius < r p ∧
      ∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact exists_morseSurgeryData_lt hf hm p.property
      (fun x hx hfx => hinj hx p.property hfx) (hr p)
  choose d hd hisolated using hex
  refine ⟨{
    finite := finite_criticalPoints hf hm
    distinct := hinj
    data := d
    isolated := hisolated
    separated := ?_ }⟩
  intro p q hpq
  have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)
    nlinarith
  linarith [hgap p q hpq]

variable (E M) in
/-- The global Morse construction supplies a compatible finite native surgery system. -/
theorem exists_morse_function_with_surgeryWindows :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      Nonempty (SurgeryWindows E f) := by
  obtain ⟨f, hf, hm, _, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
  exact ⟨f, hf, hm, nonempty_surgeryWindows hf hm hinj⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
