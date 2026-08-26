import ErdosProblems.Erdos556.UniversalExtension

/-!
# Matching deficiency from Tutte's theorem

The universal-clique extension turns a bound on all odd-component deficits
into a matching with the corresponding number of uncovered vertices.
-/

namespace Erdos556

open SimpleGraph

open scoped Classical in
theorem matching_of_odd_components_bound {V : Type*} [Finite V]
    (G : SimpleGraph V) {d : ℕ} (hparity : Even (Nat.card V + d))
    (hbound : ∀ X : Set V,
      ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard ≤ X.ncard + d) :
    ∃ F, EdgeMatching G F ∧ Nat.card V ≤ 2 * F.card + d := by
  classical
  let H := universalExtension (W := Fin d) G
  have hTutte : ∀ Y, ¬ H.IsTutteViolator Y := by
    intro Y hY
    have hnew : ∀ w : Fin d, Sum.inr w ∈ Y :=
      universalExtension_violator_inr G (by simpa using hparity) hY
    have hcard := ncard_sum_set_of_all_inr Y hnew
    have hodd := isomorphic_oddComponents_ncard (universalExtension_deleteIso G Y hnew)
    have hB := hbound (Sum.inl ⁻¹' Y)
    have hviol : Y.ncard < ((⊤ : H.Subgraph).deleteVerts Y).coe.oddComponents.ncard := hY
    simp only [Nat.card_fin] at hcard
    change ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' Y)).coe.oddComponents.ncard =
      ((⊤ : H.Subgraph).deleteVerts Y).coe.oddComponents.ncard at hodd
    omega
  obtain ⟨M, hM⟩ := SimpleGraph.tutte.mpr hTutte
  obtain ⟨F, hF, hcard⟩ := matching_of_perfect_universalExtension G M hM
  exact ⟨F, hF, by simpa only [Nat.card_fin] using hcard⟩

end Erdos556
