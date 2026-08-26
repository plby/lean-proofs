/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair
import Mathlib.Tactic

/-!
# Dynamic selected-branch embedding

This is the local online step needed for the selected `F0` branches in
Zhao's Lemma 5.9. The branch root is chosen in an external cluster `C`,
typical toward the appropriate endpoint of a matching pair, while every
nonroot vertex is embedded in the current residual subsets of that matching
pair. Thus the theorem combines the two genuinely different regular pairs
`C--X` and `X--Y`; it does not treat the selected root as a vertex of `X`.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59DynamicSelectedBranch

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma51DynamicRegularPair

universe u v

private theorem finTwoEquiv_zero_one (e : Equiv (Fin 2) (Fin 2)) :
    (e 0 = 0 ∧ e 1 = 1) ∨ (e 0 = 1 ∧ e 1 = 0) := by
  let a := e 0
  let b := e 1
  change (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
  have hab : a ≠ b := by
    intro h
    apply (by decide : (0 : Fin 2) ≠ 1)
    exact e.injective h
  have hav := a.isLt
  have hbv := b.isLt
  have habv : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  by_cases ha0 : a.val = 0
  · left
    constructor <;> apply Fin.ext <;> omega
  · right
    constructor <;> apply Fin.ext <;> omega

/-- Embed one selected rooted branch dynamically.

The root is selected in `rootAvailable ⊆ rootWhole` and is required to be
adjacent to the already embedded external parent `z`. Its typicality toward
the first matching endpoint is derived from the regular pair
`rootWhole--whole (orient 1)`. All later tree edges are realized inside the
regular matching pair `whole 0--whole 1` using the literal current sets
`available`.
-/
theorem exists_dynamic_selected_rooted_tree_copy
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (orient : Equiv (Fin 2) (Fin 2))
    (rootWhole rootAvailable : Finset B)
    (whole available : Fin 2 → Finset B)
    (rho rootDensity pairDensity : ℝ)
    (hunifRoot : G.IsUniform rho rootWhole (whole (orient 1)))
    (hunifPair : G.IsUniform rho (whole 0) (whole 1))
    (hrootSubset : rootAvailable ⊆ rootWhole)
    (havailable : ∀ c, available c ⊆ whole c)
    (hrootLarge :
      rho * (#rootWhole : ℝ) < (#rootAvailable : ℝ))
    (havailableLarge : ∀ c,
      rho * (#(whole c) : ℝ) ≤ (#(available c) : ℝ))
    (hrootDensity :
      rootDensity ≤ G.edgeDensity rootWhole (whole (orient 1)))
    (hpairDensity : pairDensity ≤ G.edgeDensity (whole 0) (whole 1))
    (hrootMargin :
      (Fintype.card A : ℝ) + rho * (#(whole (orient 1)) : ℝ) ≤
        (rootDensity - rho) * (#(available (orient 1)) : ℝ))
    (hpairMargin : ∀ c,
      (Fintype.card A : ℝ) + rho * (#(whole c) : ℝ) ≤
        (pairDensity - rho) * (#(available c) : ℝ))
    (hattach : ∀ w ∈ rootAvailable, G.Adj z w) :
    ∃ f : T.Copy G,
      G.Adj z (f root) ∧
      f root ∈ rootAvailable ∧
      ∀ a, a ≠ root →
        f a ∈ available (orient (hT.coloringTwoOfVert root a)) := by
  classical
  let W0 := whole (orient 0)
  let W1 := whole (orient 1)
  let A0 := available (orient 0)
  let A1 := available (orient 1)
  have hA0W0 : A0 ⊆ W0 := by
    simpa [A0, W0] using havailable (orient 0)
  have hA1W1 : A1 ⊆ W1 := by
    simpa [A1, W1] using havailable (orient 1)
  have hA0large : rho * (#W0 : ℝ) ≤ #A0 := by
    simpa [A0, W0] using havailableLarge (orient 0)
  have hA1large : rho * (#W1 : ℝ) ≤ #A1 := by
    simpa [A1, W1] using havailableLarge (orient 1)
  have hrootLargeLe : rho * (#rootWhole : ℝ) ≤ #rootAvailable :=
    hrootLarge.le
  have hunifPairO : G.IsUniform rho W0 W1 := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W0, W1, h.1, h.2] using hunifPair
    · simpa [W0, W1, h.1, h.2] using hunifPair.symm
  have hpairDensityO : pairDensity ≤ G.edgeDensity W0 W1 := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W0, W1, h.1, h.2] using hpairDensity
    · simpa [W0, W1, h.1, h.2, G.edgeDensity_comm] using hpairDensity
  have hrootDensityO : rootDensity ≤ G.edgeDensity rootWhole W1 := by
    simpa [W1] using hrootDensity
  have hrootMarginO :
      (Fintype.card A : ℝ) + rho * (#W1 : ℝ) ≤
        (rootDensity - rho) * #A1 := by
    simpa [W1, A1] using hrootMargin
  have hpairMargin0 :
      (Fintype.card A : ℝ) + rho * (#W0 : ℝ) ≤
        (pairDensity - rho) * #A0 := by
    simpa [W0, A0] using hpairMargin (orient 0)
  have hpairMargin1 :
      (Fintype.card A : ℝ) + rho * (#W1 : ℝ) ≤
        (pairDensity - rho) * #A1 := by
    simpa [W1, A1] using hpairMargin (orient 1)

  let bad0 := dynamicLowDegreeVertices G rho W0 W1 A0 A1
  let bad1 := dynamicLowDegreeVertices G rho W1 W0 A1 A0
  let rootBad :=
    dynamicLowDegreeVertices G rho rootWhole W1 rootAvailable A1
  let good0 := A0 \ bad0
  let good1 := A1 \ bad1
  have hbad0 : (#bad0 : ℝ) ≤ rho * #W0 := by
    simpa [bad0, dynamicLowDegreeVertices] using
      card_lowDegreeVertices_le G hunifPairO hA0W0 hA1W1
        hA0large hA1large
  have hbad1 : (#bad1 : ℝ) ≤ rho * #W1 := by
    simpa [bad1, dynamicLowDegreeVertices, G.edgeDensity_comm W0 W1] using
      card_lowDegreeVertices_le G hunifPairO.symm hA1W1 hA0W0
        hA1large hA0large
  have hrootBad : (#rootBad : ℝ) ≤ rho * #rootWhole := by
    simpa [rootBad, dynamicLowDegreeVertices] using
      card_lowDegreeVertices_le G hunifRoot hrootSubset hA1W1
        hrootLargeLe hA1large

  have hdegree0 (x : B) (hx : x ∈ good0) :
      (G.edgeDensity W0 W1 - rho) * #A1 ≤
        (#(A1.filter (G.Adj x)) : ℝ) := by
    have hxA : x ∈ A0 := (Finset.mem_sdiff.mp hx).1
    have hxbad : x ∉ bad0 := (Finset.mem_sdiff.mp hx).2
    apply le_of_not_gt
    intro hlt
    apply hxbad
    exact Finset.mem_filter.mpr ⟨hxA, hlt⟩
  have hdegree1 (x : B) (hx : x ∈ good1) :
      (G.edgeDensity W1 W0 - rho) * #A0 ≤
        (#(A0.filter (G.Adj x)) : ℝ) := by
    have hxA : x ∈ A1 := (Finset.mem_sdiff.mp hx).1
    have hxbad : x ∉ bad1 := (Finset.mem_sdiff.mp hx).2
    apply le_of_not_gt
    intro hlt
    apply hxbad
    exact Finset.mem_filter.mpr ⟨hxA, hlt⟩
  have hthreshold1 :
      (pairDensity - rho) * (#A1 : ℝ) ≤
        (G.edgeDensity W0 W1 - rho) * #A1 := by
    have hcard : (0 : ℝ) ≤ (#A1 : ℝ) := by positivity
    nlinarith
  have hthreshold0 :
      (pairDensity - rho) * (#A0 : ℝ) ≤
        (G.edgeDensity W1 W0 - rho) * #A0 := by
    have hdensity' : pairDensity ≤ G.edgeDensity W1 W0 := by
      simpa [G.edgeDensity_comm W0 W1] using hpairDensityO
    have hcard : (0 : ℝ) ≤ (#A0 : ℝ) := by positivity
    nlinarith

  have hrootBadltReal : (#rootBad : ℝ) < #rootAvailable := by linarith
  have hrootBadlt : #rootBad < #rootAvailable := by exact_mod_cast hrootBadltReal
  have hex : ∃ w ∈ rootAvailable, w ∉ rootBad := by
    by_contra! hall
    have hsub : rootAvailable ⊆ rootBad := by
      intro w hw
      exact hall w hw
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hrootBadlt
  obtain ⟨w, hwRoot, hwNotBad⟩ := hex
  have hwdegree :
      (G.edgeDensity rootWhole W1 - rho) * #A1 ≤
        (#(A1.filter (G.Adj w)) : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply hwNotBad
    exact Finset.mem_filter.mpr ⟨hwRoot, hlt⟩
  have hrootThreshold :
      (rootDensity - rho) * (#A1 : ℝ) ≤
        (G.edgeDensity rootWhole W1 - rho) * #A1 := by
    have hcard : (0 : ℝ) ≤ (#A1 : ℝ) := by positivity
    nlinarith
  have hrootReal :
      (Fintype.card A : ℝ) + #bad1 ≤
        (#(A1.filter (G.Adj w)) : ℝ) := by
    linarith
  have hrootNat : Fintype.card A + #bad1 ≤
      #(A1.filter (G.Adj w)) := by exact_mod_cast hrootReal
  have hrootClean : Fintype.card A ≤
      #((A1 \ bad1).filter (G.Adj w)) :=
    card_neighbors_cleaned_ge G A1 bad1 w (Fintype.card A) hrootNat
  have hcross01 (x : B) (hx : x ∈ good0) : Fintype.card A ≤
      #(good1.filter (G.Adj x)) := by
    have hxdeg := hdegree0 x hx
    have hreal : (Fintype.card A : ℝ) + #bad1 ≤
        (#(A1.filter (G.Adj x)) : ℝ) := by
      linarith
    have hnat : Fintype.card A + #bad1 ≤
        #(A1.filter (G.Adj x)) := by exact_mod_cast hreal
    exact card_neighbors_cleaned_ge G A1 bad1 x (Fintype.card A) hnat
  have hcross10 (x : B) (hx : x ∈ good1) : Fintype.card A ≤
      #(good0.filter (G.Adj x)) := by
    have hxdeg := hdegree1 x hx
    have hreal : (Fintype.card A : ℝ) + #bad0 ≤
        (#(A0.filter (G.Adj x)) : ℝ) := by
      linarith
    have hnat : Fintype.card A + #bad0 ≤
        #(A0.filter (G.Adj x)) := by exact_mod_cast hreal
    exact card_neighbors_cleaned_ge G A0 bad0 x (Fintype.card A) hnat

  let candidate : Fin 2 → Finset B := fun c => if c = 0 then good0 else good1
  have hcandidate0 : candidate 0 = good0 := by simp [candidate]
  have hcandidate1 : candidate 1 = good1 := by simp [candidate]
  have hcross : ∀ i j, i ≠ j → ∀ x ∈ candidate i,
      Fintype.card A ≤ #((candidate j).filter (G.Adj x)) := by
    intro i j hij x hx
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [hcandidate0, hcandidate1] using
        hcross01 x (by simpa [hcandidate0] using hx)
    · simpa [hcandidate0, hcandidate1] using
        hcross10 x (by simpa [hcandidate1] using hx)
    · exact False.elim (hij rfl)
  obtain ⟨f, hfroot, hfmem⟩ := exists_rooted_tree_copy T G hT root
    candidate w (by simpa [hcandidate1] using hrootClean) hcross
  have hcandidateSubset : ∀ c, candidate c ⊆ available (orient c) := by
    intro c
    fin_cases c
    · change candidate (0 : Fin 2) ⊆ available (orient (0 : Fin 2))
      rw [hcandidate0]
      change good0 ⊆ A0
      exact Finset.sdiff_subset
    · change candidate (1 : Fin 2) ⊆ available (orient (1 : Fin 2))
      rw [hcandidate1]
      change good1 ⊆ A1
      exact Finset.sdiff_subset
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hfroot]
    exact hattach w hwRoot
  · simpa [hfroot] using hwRoot
  · intro a ha
    exact hcandidateSubset _ (hfmem a ha)

end Erdos547b.ZhaoLemma59DynamicSelectedBranch

#print axioms Erdos547b.ZhaoLemma59DynamicSelectedBranch.exists_dynamic_selected_rooted_tree_copy
