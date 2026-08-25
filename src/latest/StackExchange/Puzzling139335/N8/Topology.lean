import StackExchange.Puzzling139335.N8.Topology.BoundaryFill
import StackExchange.Puzzling139335.ExteriorContact.JordanSpokes
import StackExchange.Puzzling139335.ExteriorContact.Nonplanarity

/-!
# Boundary contact obstructions in an arbitrary Jordan region

The third family of disjoint access arcs lies in the unbounded exterior of
the ambient Jordan region. No area or boundary-measure assumption is used.
-/

open Set

namespace Puzzling139335.N8

/-- Three distinct boundary contacts admit disjoint exterior spokes in the
complement of any closed Jordan region. -/
theorem exists_jordanRegion_exterior_spokes {S : Set Plane}
    (hS : IsJordanRegion S) (b : Fin 3 → Plane)
    (hb : ∀ i, b i ∈ frontier S) (hinj : Function.Injective b) :
    ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∉ S ∧
      (∀ i, Schoenflies.IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ Sᶜ) ∧
      ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  simpa only [outside_frontier_eq_compl hS, mem_compl_iff] using
    hS.frontier_isJordanCurve.exists_three_exterior_spokes b hb hinj

/-- Two Jordan subregions with disjoint interiors cannot share three distinct
points on the ambient Jordan frontier. -/
theorem jordan_regions_no_three_common_boundary_points {P Q S : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q) (hS : IsJordanRegion S)
    (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hdis : Disjoint (interior P) (interior Q))
    (b : Fin 3 → Plane) (hbP : ∀ j, b j ∈ P) (hbQ : ∀ j, b j ∈ Q)
    (hbS : ∀ j, b j ∈ frontier S) (hinj : Function.Injective b) : False := by
  let F : Fin 3 → Set Plane := ![P, Q, (interior S)ᶜ]
  let U : Fin 3 → Set Plane := ![interior P, interior Q, Sᶜ]
  have hIPQ : Disjoint (interior P) Q := hQ.disjoint_interior_left hdis
  have hIQP : Disjoint (interior Q) P := hP.disjoint_interior_left hdis.symm
  have hIPE : Disjoint (interior P) (interior S)ᶜ :=
    Set.disjoint_left.mpr fun _ hp he => he (interior_mono hPS hp)
  have hIQE : Disjoint (interior Q) (interior S)ᶜ :=
    Set.disjoint_left.mpr fun _ hq he => he (interior_mono hQS hq)
  have hIEP : Disjoint Sᶜ P :=
    Set.disjoint_left.mpr fun _ he hp => he (hPS hp)
  have hIEQ : Disjoint Sᶜ Q :=
    Set.disjoint_left.mpr fun _ he hq => he (hQS hq)
  have hUF : ∀ i, U i ⊆ F i := by
    intro i
    fin_cases i
    · exact interior_subset
    · exact interior_subset
    · exact fun _ hz hi => hz (interior_subset hi)
  have hdisUF : ∀ i j, i ≠ j → Disjoint (U i) (F j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hIPQ
      | exact hIQP
      | exact hIPE
      | exact hIQE
      | exact hIEP
      | exact hIEQ
  have hbAll : ∀ i j, b j ∈ F i := by
    intro i j
    fin_cases i
    · exact hbP j
    · exact hbQ j
    · exact (hbS j).2
  have hbPf : ∀ j, b j ∈ frontier P :=
    fun j => ⟨subset_closure (hbP j), fun hz => (hbS j).2 (interior_mono hPS hz)⟩
  have hbQf : ∀ j, b j ∈ frontier Q :=
    fun j => ⟨subset_closure (hbQ j), fun hz => (hbS j).2 (interior_mono hQS hz)⟩
  obtain ⟨xP, hxP⟩ := hP.interior_nonempty
  obtain ⟨AP, hAP, hAPint, hAPmeet⟩ :=
    hP.exists_disjoint_arcs_to_frontier hxP b hbPf hinj
  obtain ⟨xQ, hxQ⟩ := hQ.interior_nonempty
  obtain ⟨AQ, hAQ, hAQint, hAQmeet⟩ :=
    hQ.exists_disjoint_arcs_to_frontier hxQ b hbQf hinj
  obtain ⟨xE, AE, hxE, hAE, hAEint, hAEmeet⟩ :=
    exists_jordanRegion_exterior_spokes hS b hbS hinj
  apply no_three_common_points_of_disjoint_spokes F U hUF hdisUF b hbAll hinj
  intro i
  fin_cases i
  · exact ⟨xP, AP, hxP, hAP, hAPint, hAPmeet⟩
  · exact ⟨xQ, AQ, hxQ, hAQ, hAQint, hAQmeet⟩
  · exact ⟨xE, AE, hxE, hAE, hAEint, hAEmeet⟩

end Puzzling139335.N8
