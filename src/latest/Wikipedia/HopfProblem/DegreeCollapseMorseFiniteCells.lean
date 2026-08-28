import Wikipedia.HopfProblem.DegreeCollapseFiniteCellType
import Wikipedia.HopfProblem.DegreeCollapseMorseCellBands
import Wikipedia.SmoothSixDPoincare.RegularSublevelDeformation
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Mathlib.Order.WellFounded

/-!
# A finite homotopy cell construction of a compact smooth manifold

Induct over the finite, ordered native critical set of an excellent Morse
function. Disjoint critical bands give genuine core-cell attachments; the
intervening regular bands give actual flow homotopy equivalences. Fermat's
theorem identifies the empty starting sublevel and the whole final sublevel.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCells

open Wikipedia.SmoothSixDPoincare ManifoldMorse FiniteCells

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

theorem upper_lt_lower_of_disjoint {p q : M}
    (c : Cell (E := E) f p) (d : Cell (E := E) f q)
    (h : Disjoint c.band d.band) (hpq : f p < f q) :
    f p + c.radius ^ 2 < f q - d.radius ^ 2 := by
  by_contra hn
  have hle : f q - d.radius ^ 2 ≤ f p + c.radius ^ 2 := le_of_not_gt hn
  let t := max (f p - c.radius ^ 2) (f q - d.radius ^ 2)
  have hc : t ∈ c.band := by
    exact ⟨le_max_left _ _, max_le (by nlinarith [sq_nonneg c.radius]) hle⟩
  have hd : t ∈ d.band := by
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · nlinarith [sq_nonneg c.radius, sq_nonneg d.radius]
    · nlinarith [sq_nonneg d.radius]
  exact Set.disjoint_left.mp h hc hd

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem isEmpty_sublevel_of_no_critical
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (h : ∀ p ∈ criticalPoints E f, ¬ f p ≤ a) : IsEmpty {x : M // f x ≤ a} := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, _, hmin⟩ := isCompact_univ.exists_isMinOn ⟨x.val, mem_univ _⟩
    hf.continuous.continuousOn
  have hp : p ∈ criticalPoints E f := mem_criticalPoints_of_localMin hf
    (Filter.Eventually.of_forall (fun y => hmin (mem_univ y)))
  exact h p hp ((hmin (mem_univ x.val)).trans x.property)

/-- Every upper critical sublevel has an actual finite homotopy cell construction. -/
theorem built_upper_sublevels
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    (c : (p : criticalPoints E f) → Cell (E := E) f p.val)
    (hdis : ∀ p q, p ≠ q → Disjoint (c p).band (c q).band)
    (p : criticalPoints E f) :
    Built (Module.finrank ℝ E) {x : M // f x ≤ f p + (c p).radius ^ 2} := by
  classical
  let K := criticalPoints E f
  let : Fintype K := (finite_criticalPoints hf hm).fintype
  let : LinearOrder K := LinearOrder.lift' (fun p : K => f p.val)
    (fun p q h => Subtype.ext (hinj p.property q.property h))
  have hstep (p : K) :
      Built (Module.finrank ℝ E) {x : M // f x ≤ f p + (c p).radius ^ 2} := by
    induction p using WellFoundedLT.induction with
    | ind p ih =>
      have hlower : Built (Module.finrank ℝ E)
          {x : M // f x ≤ f p - (c p).radius ^ 2} := by
        by_cases hex : ∃ q : K, q < p
        · let s : Finset K := Finset.univ.filter (fun q => q < p)
          have hs : s.Nonempty := by
            obtain ⟨q, hq⟩ := hex
            exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
          let q := s.max' hs
          have hqp : q < p := (Finset.mem_filter.mp (s.max'_mem hs)).2
          have hgap : f q + (c q).radius ^ 2 < f p - (c p).radius ^ 2 :=
            upper_lt_lower_of_disjoint (c q) (c p) (hdis q p (ne_of_lt hqp)) hqp
          obtain ⟨e, _⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf hgap.le
            (by
              intro x hx hcrit
              let r : K := ⟨x, hcrit⟩
              have hrp : r < p := by
                change f x < f p
                nlinarith [sq_pos_of_pos (c p).radius_pos, hx.2]
              have hrq : r ≤ q := s.le_max' r
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrp⟩)
              change f x ≤ f q at hrq
              nlinarith [sq_pos_of_pos (c q).radius_pos, hx.1])
          exact Built.equiv e (ih q hqp)
        · let : IsEmpty {x : M // f x ≤ f p - (c p).radius ^ 2} :=
            isEmpty_sublevel_of_no_critical hf (by
              intro x hx hle
              apply hex
              refine ⟨⟨x, hx⟩, ?_⟩
              change f x < f p
              nlinarith [sq_pos_of_pos (c p).radius_pos])
          exact Built.empty _
      apply Built.equiv (c p).comparison
      exact Built.attach _ (coreCellMap (c p).chart (c p).radius
        (c p).radius_pos (c p).block)
        (fun u hu => (coreCellMap_lower_iff (c p).chart (c p).radius
          (c p).radius_pos (c p).block u).mpr hu)
        (c p).dimension_le hlower
  exact hstep p

/-- Native Morse theory constructs a finite homotopy cell type in the actual model dimension. -/
theorem built_of_compact_smooth_manifold : Built (Module.finrank ℝ E) M := by
  classical
  cases isEmpty_or_nonempty M with
  | inl h => exact Built.empty _
  | inr h =>
    obtain ⟨f, hf, hm, _, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
    obtain ⟨c, hdis⟩ := exists_disjoint_cells hf hm hinj
    obtain ⟨p, _, hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
      hf.continuous.continuousOn
    have hp : p ∈ criticalPoints E f := mem_criticalPoints_of_localMax hf
      (Filter.Eventually.of_forall (fun y => hmax (mem_univ y)))
    let q : criticalPoints E f := ⟨p, hp⟩
    have hb := built_upper_sublevels hf hm hinj c hdis q
    have hfull : {x : M | f x ≤ f q + (c q).radius ^ 2} = univ := by
      apply Set.eq_univ_of_forall
      intro x
      change f x ≤ f p + (c q).radius ^ 2
      exact (hmax (mem_univ x)).trans (le_add_of_nonneg_right (sq_nonneg (c q).radius))
    exact Built.equiv ((Homeomorph.setCongr hfull).trans (Homeomorph.Set.univ M)).toHomotopyEquiv hb

end Wikipedia.HopfProblem.DegreeCollapse.MorseCells
