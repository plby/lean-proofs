import Wikipedia.HopfProblem.DegreeCollapseSurgeryBlockField
import Wikipedia.SmoothSixDPoincare.MorseSurgeryWindows

/-!
# Constructing the finite surgery system and its common complete flow

Every excellent Morse function has actual separated native surgeries and
one smooth descending field agreeing with all their local models on
neighborhoods of the entire closed coordinate blocks. The field and its
complete flow are constructed, not supplied as compatibility assumptions.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Classical in
structure AdaptedSurgeryWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ)
    extends SurgeryWindows E f where
  field : (x : M) → TangentSpace 𝓘(ℝ, E) x
  flow : Flow ℝ M
  smooth : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, field x⟩ : TangentBundle 𝓘(ℝ, E) M))
  integral : ∀ x, IsMIntegralCurve (fun t => flow t x) field
  zero : ∀ x ∈ criticalPoints E f, field x = 0
  descent : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (field x) < 0
  model_germ : ∀ (p : criticalPoints E f) z,
    z ∈ closedBall (0 : (data p).chart.NegativeCoordinates) (2 * (data p).radius) ×ˢ
      closedBall (0 : (data p).chart.PositiveCoordinates) (2 * (data p).radius) →
      ∀ᶠ y in 𝓝 ((data p).chart.splitChart.symm z), field y = (data p).chart.descentField y

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

open Classical in
theorem nonempty_adaptedSurgeryWindows {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) : Nonempty (AdaptedSurgeryWindows E f) := by
  have hfinite := finite_criticalPoints hf hm
  letI : Finite (criticalPoints E f) := hfinite.to_subtype
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii hfinite hinj
  have hex : ∀ p : criticalPoints E f, ∃ d : MorseSurgeryData E f p.val,
      d.radius < r p / 3 ∧ ∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact exists_morseSurgeryData_lt hf hm p.property
      (fun x hx hfx => hinj hx p.property hfx) (div_pos (hr p) (by norm_num))
  choose d hd hisolated using hex
  have hsq (p : criticalPoints E f) : 9 * (d p).radius ^ 2 < (r p) ^ 2 := by
    have hsmall : 3 * (d p).radius < r p := by linarith [hd p]
    have hsum : 0 < r p + 3 * (d p).radius :=
      add_pos (hr p) (mul_pos (by norm_num) (d p).radius_pos)
    nlinarith [mul_pos (sub_pos.mpr hsmall) hsum]
  have hwide (p q : criticalPoints E f) (hpq : f p < f q) :
      f p + 9 * (d p).radius ^ 2 < f q - 9 * (d q).radius ^ 2 := by
    linarith [hgap p q hpq, hsq p, hsq q]
  have hintervals : Pairwise (fun p q : criticalPoints E f =>
      Disjoint (Icc (f p - 9 * (d p).radius ^ 2) (f p + 9 * (d p).radius ^ 2))
        (Icc (f q - 9 * (d q).radius ^ 2) (f q + 9 * (d q).radius ^ 2))) := by
    intro p q hpq
    have hne : f p ≠ f q := fun h => hpq (Subtype.ext (hinj p.property q.property h))
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [hwide p q hlt, hx.2, hy.1]
    · linarith [hwide q p hgt, hy.2, hx.1]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmodel⟩ :=
    exists_disjoint_surgery_block_field hf hm (fun p : criticalPoints E f => p.val)
      (fun p => p.property) (fun p => (d p).chart) (fun p => (d p).radius)
      (fun p => (d p).radius_pos) (fun p => (d p).block) hintervals
  refine ⟨{
    finite := hfinite
    distinct := hinj
    data := d
    isolated := hisolated
    separated := ?_
    field := V
    flow := F
    smooth := hV
    integral := hF
    zero := hzero
    descent := hdesc
    model_germ := hmodel }⟩
  intro p q hpq
  nlinarith [hwide p q hpq, sq_nonneg (d p).radius, sq_nonneg (d q).radius]

variable (E M) in
theorem exists_morse_function_with_adaptedSurgeryWindows :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      Nonempty (AdaptedSurgeryWindows E f) := by
  obtain ⟨f, hf, hm, _, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
  exact ⟨f, hf, hm, nonempty_adaptedSurgeryWindows hf hm hinj⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
