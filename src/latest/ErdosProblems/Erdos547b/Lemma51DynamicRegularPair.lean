/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularPair
import Mathlib.Tactic

/-!
# Dynamic one-pair rooted-tree embedding

This is the local online step needed by the flexible Lemma 5.8 backend.
The regular pair is kept on the original whole clusters, while the copy is
embedded into arbitrary currently available subreservoirs.  The image of the
tree root is chosen adjacent to an already embedded external parent.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma51DynamicRegularPair

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair

universe u v

private theorem finTwoEquiv_zero_one (e : Fin 2 ≃ Fin 2) :
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
  by_cases ha₀ : a.val = 0
  · left
    constructor <;> apply Fin.ext <;> omega
  · right
    constructor <;> apply Fin.ext <;> omega

/-- Vertices of the current source reservoir which have too few neighbors
in the current target reservoir, with the threshold still measured using
the density of the original whole regular pair. -/
def dynamicLowDegreeVertices
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S U : Finset B) : Finset B :=
  {x ∈ S | (#(U.filter (G.Adj x)) : ℝ) <
    (G.edgeDensity C D - rho) * #U}

/-- A prescribed-external-parent version of the rooted regular-pair tree
embedding.  `orient` says which physical side receives each canonical
bipartition color of the source tree. -/
theorem exists_dynamic_rooted_tree_copy_of_uniform
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (orient : Fin 2 ≃ Fin 2)
    (whole available : Fin 2 → Finset B)
    (rho density : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (havailableLarge : ∀ c,
      rho * (#(whole c) : ℝ) ≤ (#(available c) : ℝ))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (_hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hparent : 1 + rho * (#(whole (orient 0)) : ℝ) ≤
      (#((available (orient 0)).filter (G.Adj z)) : ℝ))
    (hmargin : ∀ c,
      (Fintype.card A : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) * (#(available c) : ℝ)) :
    ∃ f : T.Copy G,
      G.Adj z (f root) ∧
      ∀ a, f a ∈ available (orient (hT.coloringTwoOfVert root a)) := by
  classical
  let W₀ := whole (orient 0)
  let W₁ := whole (orient 1)
  let A₀ := available (orient 0)
  let A₁ := available (orient 1)
  have hA₀W₀ : A₀ ⊆ W₀ := by
    simpa [A₀, W₀] using havailable (orient 0)
  have hA₁W₁ : A₁ ⊆ W₁ := by
    simpa [A₁, W₁] using havailable (orient 1)
  have hA₀large : rho * (#W₀ : ℝ) ≤ #A₀ := by
    simpa [A₀, W₀] using havailableLarge (orient 0)
  have hA₁large : rho * (#W₁ : ℝ) ≤ #A₁ := by
    simpa [A₁, W₁] using havailableLarge (orient 1)
  have hunifO : G.IsUniform rho W₀ W₁ := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W₀, W₁, h.1, h.2] using hunif
    · simpa [W₀, W₁, h.1, h.2] using hunif.symm
  have hdensityO : density ≤ G.edgeDensity W₀ W₁ := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W₀, W₁, h.1, h.2] using hdensity
    · simpa [W₀, W₁, h.1, h.2, G.edgeDensity_comm] using hdensity
  have hmargin₀ :
      (Fintype.card A : ℝ) + rho * (#W₀ : ℝ) + 1 ≤
        (density - rho) * #A₀ := by
    simpa [W₀, A₀] using hmargin (orient 0)
  have hmargin₁ :
      (Fintype.card A : ℝ) + rho * (#W₁ : ℝ) + 1 ≤
        (density - rho) * #A₁ := by
    simpa [W₁, A₁] using hmargin (orient 1)
  let bad₀ := dynamicLowDegreeVertices G rho W₀ W₁ A₀ A₁
  let bad₁ := dynamicLowDegreeVertices G rho W₁ W₀ A₁ A₀
  let good₀ := A₀ \ bad₀
  let good₁ := A₁ \ bad₁
  have hbad₀ : (#bad₀ : ℝ) ≤ rho * #W₀ := by
    simpa [bad₀, dynamicLowDegreeVertices] using
      card_lowDegreeVertices_le G hunifO hA₀W₀ hA₁W₁
        hA₀large hA₁large
  have hbad₁ : (#bad₁ : ℝ) ≤ rho * #W₁ := by
    simpa [bad₁, dynamicLowDegreeVertices, G.edgeDensity_comm W₀ W₁] using
      card_lowDegreeVertices_le G hunifO.symm hA₁W₁ hA₀W₀
        hA₁large hA₀large
  have hdegree₀ (v : B) (hv : v ∈ good₀) :
      (G.edgeDensity W₀ W₁ - rho) * #A₁ ≤
        (#(A₁.filter (G.Adj v)) : ℝ) := by
    have hvA : v ∈ A₀ := (Finset.mem_sdiff.mp hv).1
    have hvbad : v ∉ bad₀ := (Finset.mem_sdiff.mp hv).2
    apply le_of_not_gt
    intro hlt
    apply hvbad
    exact Finset.mem_filter.mpr ⟨hvA, hlt⟩
  have hdegree₁ (v : B) (hv : v ∈ good₁) :
      (G.edgeDensity W₁ W₀ - rho) * #A₀ ≤
        (#(A₀.filter (G.Adj v)) : ℝ) := by
    have hvA : v ∈ A₁ := (Finset.mem_sdiff.mp hv).1
    have hvbad : v ∉ bad₁ := (Finset.mem_sdiff.mp hv).2
    apply le_of_not_gt
    intro hlt
    apply hvbad
    exact Finset.mem_filter.mpr ⟨hvA, hlt⟩
  have hthreshold₁ : (density - rho) * (#A₁ : ℝ) ≤
      (G.edgeDensity W₀ W₁ - rho) * #A₁ := by
    have hcard : (0 : ℝ) ≤ (#A₁ : ℝ) := by positivity
    nlinarith
  have hthreshold₀ : (density - rho) * (#A₀ : ℝ) ≤
      (G.edgeDensity W₁ W₀ - rho) * #A₀ := by
    have hdensityO' : density ≤ G.edgeDensity W₁ W₀ := by
      simpa [G.edgeDensity_comm W₀ W₁] using hdensityO
    have hcard : (0 : ℝ) ≤ (#A₀ : ℝ) := by positivity
    nlinarith
  let N₀ := A₀.filter (G.Adj z)
  have hparentO : 1 + rho * (#W₀ : ℝ) ≤ (#N₀ : ℝ) := by
    simpa [N₀, A₀, W₀] using hparent
  have hbad₀ltReal : (#bad₀ : ℝ) < #N₀ := by linarith
  have hbad₀lt : #bad₀ < #N₀ := by exact_mod_cast hbad₀ltReal
  have hex : ∃ w ∈ N₀, w ∉ bad₀ := by
    by_contra! hall
    have hsub : N₀ ⊆ bad₀ := by
      intro w hw
      exact hall w hw
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hbad₀lt
  obtain ⟨w, hwN, hwbad⟩ := hex
  have hwA₀ : w ∈ A₀ := (Finset.mem_filter.mp hwN).1
  have hzw : G.Adj z w := (Finset.mem_filter.mp hwN).2
  have hwgood₀ : w ∈ good₀ := Finset.mem_sdiff.mpr ⟨hwA₀, hwbad⟩
  have hrootReal :
      (Fintype.card A : ℝ) + #bad₁ ≤
        (#(A₁.filter (G.Adj w)) : ℝ) := by
    have hwdeg := hdegree₀ w hwgood₀
    linarith
  have hrootNat : Fintype.card A + #bad₁ ≤
      #(A₁.filter (G.Adj w)) := by exact_mod_cast hrootReal
  have hrootClean : Fintype.card A ≤
      #((A₁ \ bad₁).filter (G.Adj w)) :=
    card_neighbors_cleaned_ge G A₁ bad₁ w (Fintype.card A) hrootNat
  have hcross₀₁ (v : B) (hv : v ∈ good₀) : Fintype.card A ≤
      #(good₁.filter (G.Adj v)) := by
    have hvdeg := hdegree₀ v hv
    have hreal : (Fintype.card A : ℝ) + #bad₁ ≤
        (#(A₁.filter (G.Adj v)) : ℝ) := by
      linarith
    have hnat : Fintype.card A + #bad₁ ≤
        #(A₁.filter (G.Adj v)) := by exact_mod_cast hreal
    exact card_neighbors_cleaned_ge G A₁ bad₁ v (Fintype.card A) hnat
  have hcross₁₀ (v : B) (hv : v ∈ good₁) : Fintype.card A ≤
      #(good₀.filter (G.Adj v)) := by
    have hvdeg := hdegree₁ v hv
    have hreal : (Fintype.card A : ℝ) + #bad₀ ≤
        (#(A₀.filter (G.Adj v)) : ℝ) := by
      linarith
    have hnat : Fintype.card A + #bad₀ ≤
        #(A₀.filter (G.Adj v)) := by exact_mod_cast hreal
    exact card_neighbors_cleaned_ge G A₀ bad₀ v (Fintype.card A) hnat
  let candidate : Fin 2 → Finset B := fun c ↦ if c = 0 then good₀ else good₁
  have hcandidate₀ : candidate 0 = good₀ := by simp [candidate]
  have hcandidate₁ : candidate 1 = good₁ := by simp [candidate]
  have hcross : ∀ i j, i ≠ j → ∀ v ∈ candidate i,
      Fintype.card A ≤ #((candidate j).filter (G.Adj v)) := by
    intro i j hij v hv
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [hcandidate₀, hcandidate₁] using
        hcross₀₁ v (by simpa [hcandidate₀] using hv)
    · simpa [hcandidate₀, hcandidate₁] using
        hcross₁₀ v (by simpa [hcandidate₁] using hv)
    · exact False.elim (hij rfl)
  obtain ⟨f, hfroot, hfmem⟩ := exists_rooted_tree_copy T G hT root
    candidate w (by simpa [hcandidate₁] using hrootClean) hcross
  have hcandidateSubset : ∀ c, candidate c ⊆ available (orient c) := by
    intro c
    fin_cases c
    · change candidate (0 : Fin 2) ⊆ available (orient (0 : Fin 2))
      rw [hcandidate₀]
      change good₀ ⊆ A₀
      exact Finset.sdiff_subset
    · change candidate (1 : Fin 2) ⊆ available (orient (1 : Fin 2))
      rw [hcandidate₁]
      change good₁ ⊆ A₁
      exact Finset.sdiff_subset
  refine ⟨f, ?_, ?_⟩
  · rw [hfroot]
    exact hzw
  · intro a
    by_cases ha : a = root
    · subst a
      rw [hfroot, coloringTwoOfVert_root]
      exact hcandidateSubset 0 (by simpa [hcandidate₀] using hwgood₀)
    · exact hcandidateSubset _ (hfmem a ha)

end Erdos547b.ZhaoLemma51DynamicRegularPair

#print axioms Erdos547b.ZhaoLemma51DynamicRegularPair.exists_dynamic_rooted_tree_copy_of_uniform
