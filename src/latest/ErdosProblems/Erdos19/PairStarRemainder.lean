import ErdosProblems.Erdos19.PairCompletion
import ErdosProblems.Erdos19.ColorCoverCounting
import ErdosProblems.Erdos19.LowIncidenceParameters

/-! # Degree and volume bounds after reserving pair stars -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem incident_degree_add_excess_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (v : V) :
    (H.incidentEdges v).ncard + H.incidentExcess v ≤ Fintype.card V - 1 := by
  classical
  calc
    _ = (∑ _e : H.incidentEdges v, 1) +
        ∑ e : H.incidentEdges v, (e.1.1.ncard - 2) := by
      simp [incidentExcess, Set.fintypeCard_eq_ncard]
    _ = ∑ e : H.incidentEdges v, (1 + (e.1.1.ncard - 2)) := sum_add_distrib.symm
    _ = ∑ e : H.incidentEdges v, (e.1.1.ncard - 1) := by
      apply sum_congr rfl
      intro e _
      have he := hmin e.1
      omega
    _ ≤ Fintype.card V - 1 := H.sum_incident_ncard_sub_one_le hlinear v

theorem twice_incident_degree_le_card_add_pair_degree (H : SetHypergraph V)
    (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard) (v : V) :
    2 * (H.incidentEdges v).ncard ≤
      Fintype.card V - 1 + (H.twoGraph.neighborSet v).ncard := by
  have hsplit := H.twoGraph_degree_add_largeDegree hmin v
  have hexcess := H.incident_degree_add_excess_le hlinear hmin v
  have hlarge := H.largeDegree_le_incidentExcess v
  omega

theorem incident_degree_mono {H J : SetHypergraph V} (hJH : J ⊆ H) (v : V) :
    (J.incidentEdges v).ncard ≤ (H.incidentEdges v).ncard := by
  let f : J.incidentEdges v → H.incidentEdges v :=
    fun e ↦ ⟨⟨e.1.1, hJH e.1.2⟩, e.2⟩
  have hinj : Function.Injective f := by
    intro e g h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H.incidentEdges v ↦ z.1.1) h))
  simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_injective f hinj

def pairStarRemainder (H : SetHypergraph V) (U : Set V) : SetHypergraph V :=
  {e | e ∈ H ∧ (e.ncard = 2 → ∀ v ∈ e, v ∉ U)}

theorem pairStarRemainder_subset (H : SetHypergraph V) (U : Set V) :
    H.pairStarRemainder U ⊆ H := fun _ he ↦ he.1

noncomputable def highPairVertices (H : SetHypergraph V) (k : ℕ) : Finset V := by
  classical
  exact univ.filter fun v ↦ k < (H.twoGraph.neighborSet v).ncard

theorem pairStarRemainder_degree_le (n s : ℕ) (hs : 2 ≤ s)
    (H : SetHypergraph (Fin n)) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (v : Fin n) :
    ((H.pairStarRemainder (H.highPairVertices (n - 2 * (n / s)))).incidentEdges v).ncard ≤
      n - n / s := by
  classical
  let U := H.highPairVertices (n - 2 * (n / s))
  let J := H.pairStarRemainder (U : Set (Fin n))
  have hJH : J ⊆ H := H.pairStarRemainder_subset _
  have hJlinear : J.IsLinear := hlinear.mono hJH
  have hhalf := near_full_degree_lower n s hs
  by_cases hvU : v ∈ U
  · have hlocal : ∀ e ∈ J.incidentEdges v, 3 ≤ e.1.ncard := by
      intro e he
      have hsize := hmin ⟨e.1, hJH e.2⟩
      change 2 ≤ e.1.ncard at hsize
      have hne : e.1.ncard ≠ 2 := fun h ↦ e.2.2 h v he hvU
      omega
    have h := J.incidentEdges_ncard_mul_sub_one_le hJlinear v 3 hlocal
    simp only [Fintype.card_fin, Nat.reduceSub] at h
    change (J.incidentEdges v).ncard ≤ _
    omega
  · have hvlow : (H.twoGraph.neighborSet v).ncard ≤ n - 2 * (n / s) := by
      have hnot : ¬n - 2 * (n / s) < (H.twoGraph.neighborSet v).ncard := by
        intro h
        exact hvU (mem_filter.mpr ⟨mem_univ _, h⟩)
      omega
    have h := H.twice_incident_degree_le_card_add_pair_degree hlinear hmin v
    simp only [Fintype.card_fin] at h
    have hmono := incident_degree_mono hJH v
    change (J.incidentEdges v).ncard ≤ _
    omega

theorem sum_incident_degrees (H : SetHypergraph V) :
    (∑ v : V, (H.incidentEdges v).ncard) = ∑ e : H, e.1.ncard := by
  calc
    _ = ∑ v : V, ∑ e : H, if v ∈ e.1 then 1 else 0 := by
      exact sum_congr rfl (fun v _ ↦ ncard_eq_sum_indicator (H.incidentEdges v))
    _ = ∑ e : H, ∑ v : V, if v ∈ e.1 then 1 else 0 := sum_comm
    _ = _ := sum_congr rfl (fun e _ ↦ (ncard_eq_sum_indicator e.1).symm)

theorem pair_degree_le_incident_degree (H J : SetHypergraph V)
    (hpairs : ∀ e ∈ H, e.ncard = 2 → e ∈ J) (v : V) :
    (H.twoGraph.neighborSet v).ncard ≤ (J.incidentEdges v).ncard := by
  classical
  let f : H.twoGraph.neighborSet v → J.incidentEdges v := fun w ↦
    ⟨⟨{v, w.1}, hpairs _ w.2.2 (Set.ncard_pair w.2.1)⟩, Or.inl rfl⟩
  have hinj : Function.Injective f := by
    intro w z h
    have hpair : ({v, w.1} : Set V) = {v, z.1} :=
      congrArg (fun e : J.incidentEdges v ↦ e.1.1) h
    have hw : w.1 ∈ ({v, z.1} : Set V) := hpair ▸ (by simp)
    rcases hw with hw | hw
    · exact (w.2.1 hw.symm).elim
    · exact Subtype.ext hw
  let _ : Fintype (H.twoGraph.neighborSet v) := Fintype.ofFinite _
  simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_injective f hinj

theorem highPairVertices_card_mul_le_incidence (H J : SetHypergraph V) (k : ℕ)
    (hpairs : ∀ e ∈ H, e.ncard = 2 → e ∈ J) :
    (H.highPairVertices k).card * (k + 1) ≤ ∑ e : J, e.1.ncard := by
  classical
  rw [← J.sum_incident_degrees]
  calc
    _ = ∑ _v ∈ H.highPairVertices k, (k + 1) := by simp
    _ ≤ ∑ v ∈ H.highPairVertices k, (H.twoGraph.neighborSet v).ncard := by
      apply sum_le_sum
      intro v hv
      exact (mem_filter.mp hv).2
    _ ≤ ∑ v ∈ H.highPairVertices k, (J.incidentEdges v).ncard :=
      sum_le_sum (fun v _ ↦ H.pair_degree_le_incident_degree J hpairs v)
    _ ≤ ∑ v : V, (J.incidentEdges v).ncard := sum_le_sum_of_subset (subset_univ _)

#print axioms pairStarRemainder_degree_le
#print axioms highPairVertices_card_mul_le_incidence

end Erdos19.SetHypergraph
