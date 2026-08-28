import Wikipedia.HopfProblem.DegreeCollapseMorseFiniteCells

/-!
# Actual regular Morse sublevels have finite homotopy cell constructions

Refine the genuine native cells so their bands remain disjoint and do
not cross a prescribed regular value. The last critical point below that
value supplies an already constructed finite cell sublevel; the remaining
regular band gives the actual flow homotopy equivalence. If there is no
critical point below the cut, the original sublevel is empty by Fermat.
This proves a finite homotopy cell type, not a smooth disk recognition.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCells

open Wikipedia.SmoothSixDPoincare ManifoldMorse FiniteCells

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Cell.band_subset_of_radius_le {f : M → ℝ} {p : M}
    (c d : Cell (E := E) f p) (h : c.radius ≤ d.radius) : c.band ⊆ d.band := by
  intro x hx
  change f p - c.radius ^ 2 ≤ x ∧ x ≤ f p + c.radius ^ 2 at hx
  change f p - d.radius ^ 2 ≤ x ∧ x ≤ f p + d.radius ^ 2
  have hsq := (sq_le_sq₀ c.radius_pos.le d.radius_pos.le).mpr h
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_disjoint_cells_below_regular_cut {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (a : ℝ)
    (hcut : ∀ p ∈ criticalPoints E f, f p ≠ a) :
    ∃ c : (p : criticalPoints E f) → Cell (E := E) f p.val,
      (∀ p q, p ≠ q → Disjoint (c p).band (c q).band) ∧
      ∀ p : criticalPoints E f, f p < a → f p + (c p).radius ^ 2 < a := by
  obtain ⟨c, hdis⟩ := exists_disjoint_cells hf hm hinj
  have hex (p : criticalPoints E f) : ∃ d : Cell (E := E) f p.val,
      d.radius < (c p).radius ∧ d.radius < 1 ∧ d.radius < |a - f p| := by
    have hgap : 0 < |a - f p| := abs_pos.mpr (sub_ne_zero.mpr (hcut p p.property).symm)
    obtain ⟨d, hd⟩ := exists_cell_lt hf hm p.property
      (fun x hx he ↦ hinj hx p.property he)
      (lt_min (c p).radius_pos (lt_min zero_lt_one hgap))
    exact ⟨d, hd.trans_le (min_le_left _ _),
      hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  choose d hdc hd1 hdgap using hex
  refine ⟨d, ?_, ?_⟩
  · intro p q hpq
    exact (hdis p q hpq).mono ((d p).band_subset_of_radius_le (c p) (hdc p).le)
      ((d q).band_subset_of_radius_le (c q) (hdc q).le)
  · intro p hp
    have hsq : (d p).radius ^ 2 < (d p).radius := by
      nlinarith [(d p).radius_pos, hd1 p]
    have h := hsq.trans (hdgap p)
    rw [abs_of_pos (sub_pos.mpr hp)] at h
    linarith

theorem built_regular_sublevel {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (a : ℝ)
    (hcut : ∀ p ∈ criticalPoints E f, f p ≠ a) :
    Built (Module.finrank ℝ E) {x : M // f x ≤ a} := by
  by_cases hbelow : (criticalPoints E f ∩ {x : M | f x ≤ a}).Nonempty
  · have hcompact : IsCompact (criticalPoints E f ∩ {x : M | f x ≤ a}) :=
      (criticalPoints_isClosed hf).isCompact.inter_right
        (isClosed_le hf.continuous continuous_const)
    obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hbelow hf.continuous.continuousOn
    obtain ⟨c, hdis, hupper⟩ := exists_disjoint_cells_below_regular_cut hf hm hinj a hcut
    let q : criticalPoints E f := ⟨p, hp.1⟩
    have hpa : f p < a := lt_of_le_of_ne hp.2 (hcut p hp.1)
    have hqa : f q + (c q).radius ^ 2 < a := hupper q hpa
    have hb := built_upper_sublevels hf hm hinj c hdis q
    obtain ⟨e, _⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf hqa.le (by
      intro x hx hcrit
      have hxp : f x ≤ f p := hmax ⟨hcrit, hx.2⟩
      have hpositive := sq_pos_of_pos (c q).radius_pos
      change f p + (c q).radius ^ 2 ≤ f x ∧ f x ≤ a at hx
      linarith [hx.1])
    exact Built.equiv e hb
  · let : IsEmpty {x : M // f x ≤ a} :=
      isEmpty_sublevel_of_no_critical hf (fun p hp hpa ↦ hbelow ⟨p, hp, hpa⟩)
    exact Built.empty _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCells
