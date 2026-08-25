import StackExchange.Puzzling139335.TranslationCancellation.Density

/-!
# The density of two adjacent regular regions

The possible failure of two-piece density additivity is localized to points
where both pieces meet the outer frontier. For a proper Jordan cut these are
its two endpoints. Keeping this null-set hypothesis explicit allows the
topological endpoint theorem to be connected separately.
-/

open Set MeasureTheory

namespace Puzzling139335

variable {X : Type*} [TopologicalSpace X]

/-- Two disjoint-interior regular regions have additive densities away from
their common points on the frontier of the union. -/
theorem weightedDensityReal_union_of_not_mem_outer_contact {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q)
    (hPreg : closure (interior P) = P) (hQreg : closure (interior Q) = Q)
    (hdisj : Disjoint (interior P) (interior Q)) {x : X}
    (hx : x ∉ P ∩ Q ∩ frontier (P ∪ Q)) :
    weightedDensityReal (P ∪ Q) x = weightedDensityReal P x + weightedDensityReal Q x := by
  have hdisP : Disjoint (interior P) Q := by
    rw [← hQreg]
    exact hdisj.closure_right isOpen_interior
  have hdisQ : Disjoint (interior Q) P := by
    rw [← hPreg]
    exact hdisj.symm.closure_right isOpen_interior
  by_cases hPi : x ∈ interior P
  · have hnotQ : x ∉ Q := fun h => disjoint_left.mp hdisP hPi h
    rw [weightedDensityReal_of_mem_interior (interior_mono subset_union_left hPi),
      weightedDensityReal_of_mem_interior hPi, weightedDensityReal_of_not_mem hQ hnotQ]
    simp
  by_cases hQi : x ∈ interior Q
  · have hnotP : x ∉ P := fun h => disjoint_left.mp hdisQ hQi h
    rw [weightedDensityReal_of_mem_interior (interior_mono subset_union_right hQi),
      weightedDensityReal_of_not_mem hP hnotP, weightedDensityReal_of_mem_interior hQi]
    simp
  by_cases hxP : x ∈ P
  · have hfP : x ∈ frontier P := (mem_frontier_iff_notMem_interior hxP).mpr hPi
    by_cases hxQ : x ∈ Q
    · have hfQ : x ∈ frontier Q := (mem_frontier_iff_notMem_interior hxQ).mpr hQi
      have hUnion : x ∈ interior (P ∪ Q) :=
        (mem_interior_iff_notMem_frontier (show x ∈ P ∪ Q from Or.inl hxP)).mpr
          (fun hf => hx ⟨⟨hxP, hxQ⟩, hf⟩)
      rw [weightedDensityReal_of_mem_interior hUnion,
        weightedDensityReal_of_mem_frontier hfP, weightedDensityReal_of_mem_frontier hfQ]
      norm_num
    · have hnotUnion : x ∉ interior (P ∪ Q) := by
        intro hUnion
        apply hPi
        apply interior_union_inter_interior_compl_right_subset
        exact ⟨hUnion, hQ.isOpen_compl.interior_eq.symm ▸ hxQ⟩
      have hfUnion : x ∈ frontier (P ∪ Q) :=
        (mem_frontier_iff_notMem_interior (show x ∈ P ∪ Q from Or.inl hxP)).mpr hnotUnion
      rw [weightedDensityReal_of_mem_frontier hfUnion,
        weightedDensityReal_of_mem_frontier hfP, weightedDensityReal_of_not_mem hQ hxQ]
      simp
  · by_cases hxQ : x ∈ Q
    · have hfQ : x ∈ frontier Q := (mem_frontier_iff_notMem_interior hxQ).mpr hQi
      have hnotUnion : x ∉ interior (P ∪ Q) := by
        intro hUnion
        apply hQi
        apply interior_union_inter_interior_compl_left_subset
        exact ⟨hUnion, hP.isOpen_compl.interior_eq.symm ▸ hxP⟩
      have hfUnion : x ∈ frontier (P ∪ Q) :=
        (mem_frontier_iff_notMem_interior (show x ∈ P ∪ Q from Or.inr hxQ)).mpr hnotUnion
      rw [weightedDensityReal_of_mem_frontier hfUnion,
        weightedDensityReal_of_not_mem hP hxP, weightedDensityReal_of_mem_frontier hfQ]
      simp
    · rw [weightedDensityReal_of_not_mem (hP.union hQ) (not_or.mpr ⟨hxP, hxQ⟩),
        weightedDensityReal_of_not_mem hP hxP, weightedDensityReal_of_not_mem hQ hxQ]
      simp

variable [MeasurableSpace X]

/-- A null set of common outer contacts is enough for almost-everywhere
two-piece density additivity, even if the internal interface has positive area. -/
theorem weightedDensityReal_union_ae {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q)
    (hPreg : closure (interior P) = P) (hQreg : closure (interior Q) = Q)
    (hdisj : Disjoint (interior P) (interior Q)) (μ : Measure X)
    (hcontact : μ (P ∩ Q ∩ frontier (P ∪ Q)) = 0) :
    weightedDensityReal (P ∪ Q) =ᵐ[μ]
      (fun x => weightedDensityReal P x + weightedDensityReal Q x) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hcontact] with x hx
  exact weightedDensityReal_union_of_not_mem_outer_contact hP hQ hPreg hQreg hdisj hx

/-- In particular, finitely many common outer contacts suffice for a
measure without atoms. -/
theorem weightedDensityReal_union_ae_of_finite {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q)
    (hPreg : closure (interior P) = P) (hQreg : closure (interior Q) = Q)
    (hdisj : Disjoint (interior P) (interior Q)) (μ : Measure X)
    [NullSingletonClass μ] (hcontact : (P ∩ Q ∩ frontier (P ∪ Q)).Finite) :
    weightedDensityReal (P ∪ Q) =ᵐ[μ]
      (fun x => weightedDensityReal P x + weightedDensityReal Q x) :=
  weightedDensityReal_union_ae hP hQ hPreg hQreg hdisj μ (hcontact.measure_zero μ)

end Puzzling139335
