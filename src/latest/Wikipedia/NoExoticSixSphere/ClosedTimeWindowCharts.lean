import Wikipedia.NoExoticSixSphere.ZeroSlabHalfLineChart
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.CompactHalfLineBoundary

/-!
# Cutting actual curve charts by a closed time window

Interior charts retain their old boundary points. A genuine time chart at
either endpoint restricts to a half-line chart of the closed window. The
resulting boundary is exactly the old boundary together with the two time
fibers, not a presumed manifold-boundary identification.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.ClosedTimeWindow

open InvolutionQuotient

theorem exists_interval_end_chart (t : unitInterval) (ht : t.val = 0 ∨ t.val = 1) :
    ∃ d : OpenPartialHomeomorph unitInterval HalfLine, t ∈ d.source ∧
      ∀ s ∈ d.source, (d s).val = 0 ↔ s.val = 0 ∨ s.val = 1 := by
  rcases ht with ht | ht
  · refine ⟨ZeroSlab.initialIntervalChart, ?_, ?_⟩
    · change t.val < 1
      rw [ht]
      norm_num
    · intro s hs
      change s.val = 0 ↔ s.val = 0 ∨ s.val = 1
      exact ⟨Or.inl, fun h ↦ h.resolve_right (ne_of_lt hs)⟩
  · let d := unitInterval.symmHomeomorph.toOpenPartialHomeomorph.trans
      ZeroSlab.initialIntervalChart
    refine ⟨d, ⟨mem_univ _, ?_⟩, ?_⟩
    · change 1 - t.val < 1
      rw [ht]
      norm_num
    · intro s hs
      change 1 - s.val = 0 ↔ s.val = 0 ∨ s.val = 1
      have hpos : 1 - s.val < 1 := hs.2
      constructor
      · intro he
        exact Or.inr (by linarith)
      · rintro (he | he) <;> rw [he] <;> linarith

variable {X : Type*} [TopologicalSpace X] (τ : C(X, ℝ)) (B : Set X)

def space : Set X := τ ⁻¹' Icc (0 : ℝ) 1

def boundary : Set (space τ) := {q | q.val ∈ B ∨ τ q.val = 0 ∨ τ q.val = 1}

theorem exists_end_chart (q : space τ) (hqend : τ q.val = 0 ∨ τ q.val = 1)
    (c : OpenPartialHomeomorph X ℝ) (hqc : q.val ∈ c.source)
    (hc : ∀ x ∈ c.source, c x = τ x) (hdis : Disjoint c.source B) :
    ∃ d : OpenPartialHomeomorph (space τ) HalfLine, q ∈ d.source ∧
      ∀ r ∈ d.source, (d r).val = 0 ↔ r ∈ boundary τ B := by
  have hImage : c.IsImage (space τ) (Icc (0 : ℝ) 1) := by
    intro x hx
    change c x ∈ Icc (0 : ℝ) 1 ↔ τ x ∈ Icc (0 : ℝ) 1
    rw [hc x hx]
  let E := SubsetCoordinates.coordinates c hImage q (0 : unitInterval)
  have hE (r : space τ) (hr : r ∈ E.source) : (E r).val = τ r.val := by
    rw [SubsetCoordinates.coordinates_val c hImage q (0 : unitInterval) hr]
    exact hc r.val hr
  obtain ⟨k, hqk, hk⟩ := exists_interval_end_chart (E q) (by rwa [hE q hqc])
  refine ⟨E.trans k, ⟨hqc, hqk⟩, ?_⟩
  intro r hr
  change (k (E r)).val = 0 ↔ r.val ∈ B ∨ τ r.val = 0 ∨ τ r.val = 1
  rw [hk (E r) hr.2, hE r hr.1]
  exact ⟨Or.inr, fun h ↦ h.resolve_left ((disjoint_left.mp hdis) hr.1)⟩

theorem exists_interior_chart (q : space τ) (hqt : τ q.val ∈ Ioo (0 : ℝ) 1)
    (c : OpenPartialHomeomorph X HalfLine) (hqc : q.val ∈ c.source)
    (hc : ∀ x ∈ c.source, (c x).val = 0 ↔ x ∈ B) :
    ∃ d : OpenPartialHomeomorph (space τ) HalfLine, q ∈ d.source ∧
      ∀ r ∈ d.source, (d r).val = 0 ↔ r ∈ boundary τ B := by
  let U := τ ⁻¹' Ioo (0 : ℝ) 1
  have hU : IsOpen U := isOpen_Ioo.preimage τ.continuous
  let c' := c.restrOpen U hU
  have hImage : c'.IsImage (space τ) (univ : Set HalfLine) := by
    intro x hx
    exact ⟨fun _ ↦ Ioo_subset_Icc_self hx.2, fun _ ↦ mem_univ _⟩
  let E := SubsetCoordinates.coordinates c' hImage q ⟨c q.val, mem_univ _⟩
  let d := E.trans (Homeomorph.Set.univ HalfLine).toOpenPartialHomeomorph
  refine ⟨d, ⟨⟨hqc, hqt⟩, mem_univ _⟩, ?_⟩
  intro r hr
  change ((E r).val).val = 0 ↔ r.val ∈ B ∨ τ r.val = 0 ∨ τ r.val = 1
  rw [SubsetCoordinates.coordinates_val c' hImage q ⟨c q.val, mem_univ _⟩ hr.1]
  change (c r.val).val = 0 ↔ r.val ∈ B ∨ τ r.val = 0 ∨ τ r.val = 1
  rw [hc r.val hr.1.1]
  have ht : τ r.val ∈ Ioo (0 : ℝ) 1 := hr.1.2
  exact ⟨Or.inl, fun h ↦ h.resolve_right (fun h ↦
    h.elim (ne_of_gt ht.1) (ne_of_lt ht.2))⟩

theorem finite_even_boundary [T2Space X] (hcompact : IsCompact (space τ))
    (hinter : ∀ x, τ x ∈ Ioo (0 : ℝ) 1 →
      ∃ c : OpenPartialHomeomorph X HalfLine, x ∈ c.source ∧
        ∀ y ∈ c.source, (c y).val = 0 ↔ y ∈ B)
    (hends : ∀ x, τ x = 0 ∨ τ x = 1 →
      ∃ c : OpenPartialHomeomorph X ℝ, x ∈ c.source ∧
        (∀ y ∈ c.source, c y = τ y) ∧ Disjoint c.source B) :
    (boundary τ B).Finite ∧ Even (boundary τ B).ncard := by
  let : CompactSpace (space τ) := isCompact_iff_compactSpace.mp hcompact
  have hcharts (q : space τ) :
      ∃ d : OpenPartialHomeomorph (space τ) HalfLine, q ∈ d.source ∧
        ∀ r ∈ d.source, (d r).val = 0 ↔ r ∈ boundary τ B := by
    by_cases he : τ q.val = 0 ∨ τ q.val = 1
    · obtain ⟨c, hqc, hc, hdis⟩ := hends q.val he
      exact exists_end_chart τ B q he c hqc hc hdis
    · have hi : τ q.val ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne q.property.1 (fun h ↦ he (.inl h.symm)),
          lt_of_le_of_ne q.property.2 (fun h ↦ he (.inr h))⟩
      obtain ⟨c, hqc, hc⟩ := hinter q.val hi
      exact exists_interior_chart τ B q hi c hqc hc
  exact CurveDecomposition.finite_even_boundary_of_compact_atlas (boundary τ B)
    (fun q ↦ (hcharts q).choose) (fun q ↦ (hcharts q).choose_spec.1)
    (fun q ↦ (hcharts q).choose_spec.2)

end NoExoticSixSphere.ClosedTimeWindow
