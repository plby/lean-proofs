import Wikipedia.HopfProblem.DegreeCollapseMorseCellControl

/-!
# Pairwise disjoint native Morse cell bands

At every critical point first choose an isolating radius, then construct
the actual cell with less than half that radius. Distinct critical values
force the resulting closed bands to be disjoint. All attaching maps and
homotopy equivalences are retained in the cell data.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCells

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An actual native core cell and its genuine comparison with the upper sublevel. -/
structure Cell (f : M → ℝ) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : SignedMorseChart (E := E) f p
  block : closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
    closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆ chart.splitChart.target
  isolated : ∀ x ∈ criticalPoints E f,
    f x ∈ Icc (f p - radius ^ 2) (f p + radius ^ 2) → x = p
  dimension_le : Module.finrank ℝ chart.NegativeCoordinates ≤ Module.finrank ℝ E
  comparison : ClosedAttachment.Space {x : M | f x ≤ f p - radius ^ 2}
    {u : MorseHandle.UnitDisk chart.NegativeCoordinates | ‖(u : chart.NegativeCoordinates)‖ = 1}
    (coreCellMap chart radius radius_pos block) ≃ₕ {x : M // f x ≤ f p + radius ^ 2}

def Cell.band {f : M → ℝ} {p : M} (c : Cell (E := E) f p) : Set ℝ :=
  Icc (f p - c.radius ^ 2) (f p + c.radius ^ 2)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_cell_lt {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p)
    {R : ℝ} (hR : 0 < R) : ∃ c : Cell (E := E) f p, c.radius < R := by
  obtain ⟨ρ, hρ, hlt, c, hb, hi, hd, ⟨e⟩⟩ :=
    exists_morse_cell_attachment_lt hf hm hp hunique hR
  exact ⟨⟨ρ, hρ, c, hb, hi, hd, e⟩, hlt⟩

/-- All native cells can be chosen with disjoint closed critical bands. -/
theorem exists_disjoint_cells {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) :
    ∃ c : (p : criticalPoints E f) → Cell (E := E) f p.val,
      ∀ p q, p ≠ q → Disjoint (c p).band (c q).band := by
  have hR (p : criticalPoints E f) : ∃ R > (0 : ℝ),
      ∀ x ∈ criticalPoints E f, f x ∈ Icc (f p - R ^ 2) (f p + R ^ 2) → x = p := by
    obtain ⟨R, hR, _, hi⟩ := exists_isolating_radius (finite_criticalPoints hf hm) p.val
      (fun x hx heq => hinj hx p.property heq) zero_lt_one
    exact ⟨R, hR, hi⟩
  choose R hR hiso using hR
  have hc (p : criticalPoints E f) : ∃ c : Cell (E := E) f p.val, c.radius < R p / 2 :=
    exists_cell_lt hf hm p.property (fun x hx heq => hinj hx p.property heq) (half_pos (hR p))
  choose c hc using hc
  refine ⟨c, ?_⟩
  have hordered (p q : criticalPoints E f) (hpq : f p < f q) :
      Disjoint (c p).band (c q).band := by
    have hne : (p : M) ≠ q := fun he => (ne_of_lt hpq) (congrArg f he)
    have hp : (R p) ^ 2 < f q - f p := by
      by_contra h
      have he := hiso p q q.property
        (show f q ∈ Icc (f p - (R p) ^ 2) (f p + (R p) ^ 2) from
          ⟨by nlinarith [sq_nonneg (R p)], by linarith⟩)
      exact hne he.symm
    have hq : (R q) ^ 2 < f q - f p := by
      by_contra h
      have he := hiso q p p.property
        (show f p ∈ Icc (f q - (R q) ^ 2) (f q + (R q) ^ 2) from
          ⟨by linarith, by nlinarith [sq_nonneg (R q)]⟩)
      exact hne he
    have hsp : (c p).radius ^ 2 < (R p / 2) ^ 2 :=
      (sq_lt_sq₀ (c p).radius_pos.le (half_pos (hR p)).le).mpr (hc p)
    have hsq : (c q).radius ^ 2 < (R q / 2) ^ 2 :=
      (sq_lt_sq₀ (c q).radius_pos.le (half_pos (hR q)).le).mpr (hc q)
    apply Set.disjoint_left.mpr
    intro t htp htq
    change f p - (c p).radius ^ 2 ≤ t ∧ t ≤ f p + (c p).radius ^ 2 at htp
    change f q - (c q).radius ^ 2 ≤ t ∧ t ≤ f q + (c q).radius ^ 2 at htq
    nlinarith [htp.2, htq.1]
  intro p q hpq
  rcases lt_trichotomy (f p) (f q) with h | h | h
  · exact hordered p q h
  · exact (hpq (Subtype.ext (hinj p.property q.property h))).elim
  · exact (hordered q p h).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCells
