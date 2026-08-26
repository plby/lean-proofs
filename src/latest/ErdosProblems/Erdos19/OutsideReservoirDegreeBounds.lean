import ErdosProblems.Erdos19.SavingDegreeParameters
import ErdosProblems.Erdos19.PaletteCoverageCounts

/-! # Degree bounds after initializing the special palette -/

namespace Erdos19.SetHypergraph

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem outsideReservoir_degree_bounds (n k e d₀ dY slack : ℕ)
    (hk : 4 ≤ k) (he : 2 ≤ e)
    (H J : SetHypergraph (Fin n)) (hJH : J ⊆ H)
    (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (R : _root_.SimpleGraph (Fin n)) (hR : R ≤ H.twoGraph)
    (hres : ∀ v, (H.twoGraph.neighborSet v).ncard ≤ k * ((R.neighborSet v).ncard + e))
    (hload : ∀ v, ((J.twoGraph ⊓ R).neighborSet v).ncard ≤ 1)
    (m : ℕ) (color : J.EdgeColoring (Fin m)) (S : Finset (Fin m)) (bad : Fin m)
    (hcover : ∀ v, (H.twoGraph.neighborSet v)ᶜ.ncard ≤ d₀ →
      ∀ a ∈ S, a ≠ bad → v ∈ J.coveredVertices {e | color e = a})
    (hroom : S.card + n / k ≤ n) (hsmall : 4 * S.card ≤ d₀)
    (hYroom : 4 * (S.card + slack) ≤ dY) :
    (∀ v, ((H.outsideReservoir J R).incidentEdges v).ncard ≤ n - S.card - n / k + 2 * e) ∧
    ∀ v, dY ≤ (H.twoGraph.neighborSet v)ᶜ.ncard →
      ((H.outsideReservoir J R).incidentEdges v).ncard ≤
        (n - S.card - n / k + 2 * e) - slack := by
  have hn (v : Fin n) : 0 < n := Nat.zero_lt_of_lt v.isLt
  have hsum (v : Fin n) : (H.twoGraph.neighborSet v).ncard +
      (H.twoGraph.neighborSet v)ᶜ.ncard = n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Set.ncard_add_ncard_compl (H.twoGraph.neighborSet v)
  have hbudget (v : Fin n) :
      2 * (((H.outsideReservoir J R).incidentEdges v).ncard +
        (J.incidentEdges v).ncard + (R.neighborSet v).ncard) ≤
        n + (H.twoGraph.neighborSet v).ncard + 1 := by
    have h := H.outsideReservoir_degree_budget J hJH hlinear hmin R hR v 1 (hload v)
    simp only [Fintype.card_fin] at h
    have := hn v
    omega
  constructor
  · intro v
    by_cases hv : (H.twoGraph.neighborSet v)ᶜ.ncard ≤ d₀
    · have hspecial := J.special_palette_incident_lower color S bad v (hcover v hv)
      have h := reservoir_high_degree_bound n k (n / k) e _ _ _ _ S.card
        (by omega) (Nat.mul_div_le n k) (by have := hsum v; omega)
        (hres v) (hbudget v) hspecial
      omega
    · have h := reservoir_low_degree_bound n k (n / k) e _ _ _ _ S.card 0 d₀
        hk (Nat.mul_div_le n k) (by have := hsum v; omega) (hres v) (hbudget v)
        (by simpa only [Nat.add_zero] using hsmall)
      omega
  · intro v hv
    have h := reservoir_low_degree_bound n k (n / k) e _ _ _ _ S.card slack dY
      hk (Nat.mul_div_le n k) (by have := hsum v; omega) (hres v) (hbudget v) hYroom
    omega

#print axioms outsideReservoir_degree_bounds

end Erdos19.SetHypergraph
