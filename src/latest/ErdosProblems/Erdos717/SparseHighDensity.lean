/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The combinatorial high-density branch of the sparse induction. -/

import ErdosProblems.Erdos717.LocalIndependence

open Function Set
open SimpleGraph

namespace Erdos717

/-- Extract exactly `Q` vertices of local independence number at most `b`
from a low-pattern set. -/
theorem exists_exact_pattern_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I W U₀ : Finset V) (X0 b Q : ℕ)
    (hIP : I ⊆ P) (hWP : W ⊆ P)
    (hIind : G.IsIndepSet I) (hImax : IndepBoundOn G P I.card)
    (hIW : Disjoint I W)
    (hdegree : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b)
    (hU₀W : U₀ ⊆ W) (hU₀card : X0 / 5 ≤ U₀.card)
    (hQbase : Q ≤ X0 / 5)
    (hpatterns : I.card.choose b * Q ≤ U₀.card) :
    ∃ U : Finset V, U ⊆ U₀ ∧ U.card = Q ∧ IndepBoundOn G U b := by
  classical
  by_cases hsmall : I.card ≤ b
  · have hQU₀ : Q ≤ U₀.card := hQbase.trans hU₀card
    obtain ⟨U, hUU₀, hUcard⟩ := Finset.exists_subset_card_eq hQU₀
    refine ⟨U, hUU₀, hUcard, ?_⟩
    intro A hAU hAind
    exact (hImax A (hAU.trans (hUU₀.trans (hU₀W.trans hWP))) hAind).trans hsmall
  · have hbI : b ≤ I.card := by omega
    obtain ⟨U', hU'U₀, hU'card, hlocal⟩ :=
      exists_subset_indepBoundOn_of_neighborhood_pattern
        G P I U₀ b Q hIP (hU₀W.trans hWP) hIind hImax
        (hIW.mono_right hU₀W) hbI
        (fun v hv => hdegree v (hU₀W hv)) hpatterns
    obtain ⟨U, hUU', hUcard⟩ := Finset.exists_subset_card_eq hU'card
    refine ⟨U, hUU'.trans hU'U₀, hUcard, ?_⟩
    intro A hAU hAind
    exact hlocal A (hAU.trans hUU') hAind

/-- A short-path reservoir inside a low-neighbourhood-pattern set can be
thinned to independence number `b`, and then to a large topological clique.
The statement contains only exact natural-number side conditions. -/
theorem exists_large_cliqueSubdivision_of_patterned_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I W U₀ : Finset V) (X0 L R b Q : ℕ)
    (hIP : I ⊆ P) (hWP : W ⊆ P)
    (hIind : G.IsIndepSet I) (hImax : IndepBoundOn G P I.card)
    (hIW : Disjoint I W)
    (hdegree : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b)
    (hU₀W : U₀ ⊆ W) (hU₀card : X0 / 5 ≤ U₀.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U₀ : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (hb : 1 ≤ b) (hR : 1 ≤ R)
    (hQbase : Q ≤ X0 / 5)
    (hpatterns : I.card.choose b * Q ≤ U₀.card)
    (hroute : ∀ t : ℕ, t ≤ Q →
      6 * (t * t) + 2 * R ≤ L * R) :
    ∃ r : ℕ, Erdos718.ContainsCliqueSubdivision G r ∧
      Q ≤ R ^ (b - 1) * r := by
  classical
  by_cases hsmall : I.card ≤ b
  · have hlocal : IndepBoundOn G U₀ b := by
      intro A hAU hAind
      exact (hImax A (hAU.trans (hU₀W.trans hWP)) hAind).trans hsmall
    have hQU₀ : Q ≤ U₀.card := hQbase.trans hU₀card
    obtain ⟨U, hUU₀, hUcard⟩ := Finset.exists_subset_card_eq hQU₀
    have hlocalU : IndepBoundOn G U b := by
      intro A hAU hAind
      exact hlocal A (hAU.trans hUU₀) hAind
    have hreservoirU : ∀ {r : ℕ} (branch : Fin r ↪ V),
        Set.range branch ⊆ (U : Set V) →
        6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
          ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
        Erdos718.ContainsCliqueSubdivision G r := by
      intro r branch hrange hmissing
      exact hreservoir branch (hrange.trans (by exact_mod_cast hUU₀)) hmissing
    have hfiveQ : (5 * Q) / 5 ≤ U.card := by simp [hUcard]
    have hrouteU : ∀ t : ℕ, t ≤ U.card →
        6 * (t * t) + 2 * R ≤ L * R := by
      simpa only [hUcard] using hroute
    obtain ⟨r, hr, hrsize⟩ :=
      exists_large_cliqueSubdivision_of_local_reservoir
        G U (5 * Q) L R b hfiveQ hreservoirU hR hb hlocalU hrouteU
    exact ⟨r, hr, by simpa using hrsize⟩
  · have hbI : b ≤ I.card := by omega
    obtain ⟨U, hUU₀, hUcard, hlocal⟩ :=
      exists_subset_indepBoundOn_of_neighborhood_pattern
        G P I U₀ b Q hIP (hU₀W.trans hWP) hIind hImax
        (hIW.mono_right hU₀W) hbI
        (fun v hv => hdegree v (hU₀W hv)) hpatterns
    obtain ⟨U', hU'U, hU'card⟩ := Finset.exists_subset_card_eq hUcard
    have hlocal' : IndepBoundOn G U' b := by
      intro A hAU hAind
      exact hlocal A (hAU.trans hU'U) hAind
    have hreservoirU : ∀ {r : ℕ} (branch : Fin r ↪ V),
        Set.range branch ⊆ (U' : Set V) →
        6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
          ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
        Erdos718.ContainsCliqueSubdivision G r := by
      intro r branch hrange hmissing
      apply hreservoir branch
      · exact hrange.trans (by exact_mod_cast hU'U.trans hUU₀)
      · exact hmissing
    have hfiveQ : (5 * Q) / 5 ≤ U'.card := by simp [hU'card]
    have hrouteU : ∀ t : ℕ, t ≤ U'.card →
        6 * (t * t) + 2 * R ≤ L * R := by
      simpa only [hU'card] using hroute
    obtain ⟨r, hr, hrsize⟩ :=
      exists_large_cliqueSubdivision_of_local_reservoir
        G U' (5 * Q) L R b hfiveQ hreservoirU hR hb hlocal' hrouteU
    refine ⟨r, hr, ?_⟩
    simpa using hrsize

end Erdos717
