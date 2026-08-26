import ErdosProblems.Erdos1038.EndpointNormalization

/-!
# Closing the simultaneous atomization reduction

The atomized sublevel set is contained in the old one.  Consequently a
connected component of the new set cannot join barycenters that came from
distinct old components.  Together with preservation of the total root sum,
this removes the auxiliary atomization hypotheses from endpoint
normalization.
-/

open Set Polynomial

namespace Erdos1038

noncomputable section

theorem empiricalRootMean_atomizedPolynomial {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    empiricalRootMean (atomizedPolynomial f) = empiricalRootMean f := by
  rw [empiricalRootMean, empiricalRootMean, roots_atomizedPolynomial,
    sum_atomizedRootMultiset, natDegree_atomizedPolynomial_eq hf]

theorem atomizedPolynomial_componentAtomized {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    IsComponentAtomized (atomizedPolynomial f) := by
  intro r s hr hs hcomponents
  rw [roots_atomizedPolynomial] at hr hs
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hs
  let p := atomizedPolynomial f
  have hru : componentBarycenter f u ∈ p.roots := by
    change componentBarycenter f u ∈ (atomizedPolynomial f).roots
    rw [roots_atomizedPolynomial]
    exact Multiset.mem_map.mpr ⟨u, hu, rfl⟩
  have hrv : componentBarycenter f v ∈ p.roots := by
    change componentBarycenter f v ∈ (atomizedPolynomial f).roots
    rw [roots_atomizedPolynomial]
    exact Multiset.mem_map.mpr ⟨v, hv, rfl⟩
  have hsubu : componentBarycenter f u ∈ sublevelSet p :=
    root_mem_sublevelSet hru
  have hsubv : componentBarycenter f v ∈ sublevelSet p :=
    root_mem_sublevelSet hrv
  have hvnew : componentBarycenter f v ∈
      sublevelComponent p (componentBarycenter f u) := by
    rw [hcomponents]
    exact mem_connectedComponentIn hsubv
  have hconnected : IsConnected
      (sublevelComponent p (componentBarycenter f u)) :=
    isConnected_connectedComponentIn_iff.mpr hsubu
  have hsubsetOld : sublevelComponent p (componentBarycenter f u) ⊆
      sublevelSet f :=
    (connectedComponentIn_subset _ _).trans
      (sublevelSet_atomized_subset hf)
  have hintoOld : sublevelComponent p (componentBarycenter f u) ⊆
      sublevelComponent f (componentBarycenter f u) :=
    hconnected.isPreconnected.subset_connectedComponentIn
      (mem_connectedComponentIn hsubu) hsubsetOld
  have hvold : componentBarycenter f v ∈
      sublevelComponent f (componentBarycenter f u) := hintoOld hvnew
  have holdComponents :
      sublevelComponent f (componentBarycenter f u) =
        sublevelComponent f (componentBarycenter f v) :=
    connectedComponentIn_eq hvold
  have huv : sublevelComponent f u = sublevelComponent f v := by
    rw [sublevelComponent_componentBarycenter hf hu,
      sublevelComponent_componentBarycenter hf hv] at holdComponents
    exact holdComponents
  exact componentBarycenter_eq_of_component_eq huv

/-- An oriented admissible polynomial can be atomized and immediately fed
to endpoint normalization, with no additional structural assumptions. -/
def EndpointNormalizationHypotheses.ofOrientedAtomization
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hmean : empiricalRootMean f ≤ 0) :
    EndpointNormalizationHypotheses (atomizedPolynomial f) where
  admissible := isAdmissible_atomizedPolynomial hf
  componentAtomized := atomizedPolynomial_componentAtomized hf
  mean_nonpos := by
    rw [empiricalRootMean_atomizedPolynomial hf]
    exact hmean

/-- Every admissible polynomial has an endpoint-normalizable atomized
representative whose sublevel volume is no larger. -/
theorem exists_endpointNormalization_le_of_admissible
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    ∃ g : Polynomial ℝ, Nonempty (EndpointNormalizationHypotheses g) ∧
      sublevelVolume g ≤ sublevelVolume f := by
  obtain ⟨g, _, hg, hgmean, hgvolume, _⟩ :=
    exists_oriented_admissible_same_sublevelVolume hf
  let h : EndpointNormalizationHypotheses (atomizedPolynomial g) :=
    EndpointNormalizationHypotheses.ofOrientedAtomization hg hgmean
  refine ⟨atomizedPolynomial g, ⟨h⟩, ?_⟩
  exact (sublevelVolume_atomized_le hg).trans_eq hgvolume

end

end Erdos1038
