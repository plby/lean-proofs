import ErdosProblems.Erdos547.RegularityTypical

/-!
# A common unsuccessful target bounds all postponed private sets
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

theorem postponed_private_mass_le {V F : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y B : Finset V) (ε threshold : ℝ) (hreg : G.IsUniform ε X Y)
    (hB : B ⊆ Y) (hBsize : (Y.card : ℝ) * ε ≤ B.card)
    (hthreshold : threshold ≤ ((G.edgeDensity X Y : ℝ) - ε) * B.card)
    (J : Finset F) (R : F → Finset V)
    (hRX : ∀ i ∈ J, R i ⊆ X)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (R i) (R j))
    (hfailed : ∀ i ∈ J, ∀ v ∈ R i, (degreeIn G B v : ℝ) < threshold) :
    (∑ i ∈ J, ((R i).card : ℝ)) ≤ (X.card : ℝ) * ε := by
  classical
  let bad := X.filter (fun v ↦ (degreeIn G B v : ℝ) <
    ((G.edgeDensity X Y : ℝ) - ε) * B.card)
  have hsub : J.biUnion R ⊆ bad := by
    intro v hv
    obtain ⟨i, hi, hvR⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_filter.mpr ⟨hRX i hi hvR, (hfailed i hi v hvR).trans_le hthreshold⟩
  have hcount : (J.biUnion R).card = ∑ i ∈ J, (R i).card :=
    Finset.card_biUnion (fun i hi j hj hij ↦ hdis i hi j hj hij)
  have hcount' : ((J.biUnion R).card : ℝ) = ∑ i ∈ J, ((R i).card : ℝ) := by
    exact_mod_cast hcount
  rw [← hcount']
  exact (show ((J.biUnion R).card : ℝ) ≤ bad.card by
    exact_mod_cast Finset.card_le_card hsub).trans (card_nonTypical_le G hreg hB hBsize)

end Erdos547

#print axioms Erdos547.postponed_private_mass_le
