import StackExchange.Puzzling139335.ExteriorContact.Square
import StackExchange.Puzzling139335.ExteriorContact.JordanSpokes
import StackExchange.Puzzling139335.ExteriorContact.Nonplanarity

/-!
# Two pieces have at most two common points on the square boundary

The third family of access arcs lies in the unbounded square exterior.  It is
constructed by inversion, not by asserting that the exterior is a bounded
Jordan region.
-/

open Set

namespace Puzzling139335

/-- Three distinct square-boundary points admit disjoint access spokes from
one common point outside the closed square. -/
theorem exists_unitSquare_exterior_spokes (b : Fin 3 → Plane)
    (hb : ∀ i, b i ∈ frontier unitSquare) (hinj : Function.Injective b) :
    ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∉ unitSquare ∧
      (∀ i, Schoenflies.IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ unitSquareᶜ) ∧
      ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  simpa only [outside_frontier_unitSquare, mem_compl_iff] using
    isJordanCurve_frontier_unitSquare.exists_three_exterior_spokes b hb hinj

/-- A point of a piece on the square boundary is also on the piece's
frontier. -/
theorem mem_frontier_piece_of_mem_square_frontier {P : Set Plane}
    (hPS : P ⊆ unitSquare) {z : Plane} (hzP : z ∈ P)
    (hzS : z ∈ frontier unitSquare) : z ∈ frontier P :=
  ⟨subset_closure hzP, fun hz => hzS.2 (interior_mono hPS hz)⟩

/-- Two Jordan regions inside the square, with disjoint interiors, cannot
share three distinct points on the square's frontier. -/
theorem jordan_regions_no_three_common_square_boundary_points {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (b : Fin 3 → Plane) (hbP : ∀ j, b j ∈ P) (hbQ : ∀ j, b j ∈ Q)
    (hbS : ∀ j, b j ∈ frontier unitSquare) (hinj : Function.Injective b) : False := by
  let S : Fin 3 → Set Plane := ![P, Q, (interior unitSquare)ᶜ]
  let U : Fin 3 → Set Plane := ![interior P, interior Q, unitSquareᶜ]
  have hIPQ : Disjoint (interior P) Q := hQ.disjoint_interior_left hdis
  have hIQP : Disjoint (interior Q) P := hP.disjoint_interior_left hdis.symm
  have hIPE : Disjoint (interior P) (interior unitSquare)ᶜ :=
    Set.disjoint_left.mpr fun _ hp he => he (interior_mono hPS hp)
  have hIQE : Disjoint (interior Q) (interior unitSquare)ᶜ :=
    Set.disjoint_left.mpr fun _ hq he => he (interior_mono hQS hq)
  have hIEP : Disjoint unitSquareᶜ P :=
    Set.disjoint_left.mpr fun _ he hp => he (hPS hp)
  have hIEQ : Disjoint unitSquareᶜ Q :=
    Set.disjoint_left.mpr fun _ he hq => he (hQS hq)
  have hUS : ∀ i, U i ⊆ S i := by
    intro i
    fin_cases i
    · exact interior_subset
    · exact interior_subset
    · exact fun _ hz hi => hz (interior_subset hi)
  have hdisUS : ∀ i j, i ≠ j → Disjoint (U i) (S j) := by
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
  have hbAll : ∀ i j, b j ∈ S i := by
    intro i j
    fin_cases i
    · exact hbP j
    · exact hbQ j
    · exact (hbS j).2
  obtain ⟨xP, hxP⟩ := hP.interior_nonempty
  obtain ⟨AP, hAP, hAPint, hAPmeet⟩ := hP.exists_disjoint_arcs_to_frontier hxP b
    (fun j => mem_frontier_piece_of_mem_square_frontier hPS (hbP j) (hbS j)) hinj
  obtain ⟨xQ, hxQ⟩ := hQ.interior_nonempty
  obtain ⟨AQ, hAQ, hAQint, hAQmeet⟩ := hQ.exists_disjoint_arcs_to_frontier hxQ b
    (fun j => mem_frontier_piece_of_mem_square_frontier hQS (hbQ j) (hbS j)) hinj
  obtain ⟨xE, AE, hxE, hAE, hAEint, hAEmeet⟩ :=
    exists_unitSquare_exterior_spokes b hbS hinj
  apply no_three_common_points_of_disjoint_spokes S U hUS hdisUS b hbAll hinj
  intro i
  fin_cases i
  · exact ⟨xP, AP, hxP, hAP, hAPint, hAPmeet⟩
  · exact ⟨xQ, AQ, hxQ, hAQ, hAQint, hAQmeet⟩
  · exact ⟨xE, AE, hxE, hAE, hAEint, hAEmeet⟩

/-- The common points on the outer boundary number at most two, including
an explicit extended-cardinality bound that rules out an infinite set. -/
theorem jordan_regions_square_boundary_intersection_encard_le_two {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) :
    (P ∩ Q ∩ frontier unitSquare).encard ≤ 2 := by
  classical
  let S := P ∩ Q ∩ frontier unitSquare
  have hnot (b : Fin 3 → Plane) (hb : ∀ i, b i ∈ S)
      (hinj : Function.Injective b) : False :=
    jordan_regions_no_three_common_square_boundary_points hP hQ hPS hQS hdis b
      (fun i => (hb i).1.1) (fun i => (hb i).1.2) (fun i => (hb i).2) hinj
  by_cases hs : S.Subsingleton
  · exact (encard_le_one_iff_subsingleton.mpr hs).trans (by norm_num)
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hs
  have hsub : S ⊆ {a, b} := by
    intro c hc
    by_contra hmem
    have hca : c ≠ a := fun h => hmem (Or.inl h)
    have hcb : c ≠ b := fun h => hmem (Or.inr h)
    apply hnot ![a, b, c]
    · intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  exact (encard_mono hsub).trans_eq (encard_pair hab)

theorem jordan_regions_square_boundary_intersection_finite {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) :
    (P ∩ Q ∩ frontier unitSquare).Finite :=
  finite_of_encard_le_coe
    (jordan_regions_square_boundary_intersection_encard_le_two hP hQ hPS hQS hdis)

theorem SquareDissection.pair_frontier_unitSquare_encard_le_two (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) :
    (d.piece i ∩ d.piece j ∩ frontier unitSquare).encard ≤ 2 :=
  jordan_regions_square_boundary_intersection_encard_le_two (d.jordan i) (d.jordan j)
    (d.piece_subset i) (d.piece_subset j) (d.disjoint_interiors hij)

theorem SquareDissection.pair_frontier_unitSquare_finite (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) :
    (d.piece i ∩ d.piece j ∩ frontier unitSquare).Finite :=
  finite_of_encard_le_coe (d.pair_frontier_unitSquare_encard_le_two hij)

end Puzzling139335
