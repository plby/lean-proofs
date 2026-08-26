/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair
import Mathlib.Tactic

/-!
# Dynamic regular-pair embedding with a separate root pool

This is the one-tree step used in Zhao's Appendix Corollary A.1.  The root is
chosen from a live reservoir such as `P*` or `Q*`, while all nonroot vertices
are embedded in independently specified current interior reservoirs.  In
particular, the root reservoir need not be disjoint from the interior
reservoir on the same side.

The uniformity witness is always for the original whole pair.  The current
root and interior reservoirs only have to be large enough for the usual
relative low-degree estimates.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma51DynamicRootPool

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma51DynamicRegularPair

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

/-- Embed one rooted tree in a uniform pair while choosing the root from a
separate live pool.  Only nonroot vertices are required to lie in
`interiorAvailable`.

The strict root-pool inequality is precisely what is needed to avoid the set
of vertices having atypically small degree into the opposite interior
reservoir.  No disjointness between `rootPool` and the same-side interior
reservoir is assumed: the rooted-copy constructor itself keeps the fixed root
image distinct from every subsequently chosen image. -/
theorem exists_dynamic_rooted_tree_copy_with_root_pool
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (orient : Fin 2 ≃ Fin 2)
    (whole interiorAvailable : Fin 2 → Finset B)
    (rootPool : Finset B)
    (rho density : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hinterior : ∀ c, interiorAvailable c ⊆ whole c)
    (hrootPool : rootPool ⊆ whole (orient 0))
    (hinteriorLarge : ∀ c,
      rho * (#(whole c) : ℝ) ≤ (#(interiorAvailable c) : ℝ))
    (hrootPoolLarge :
      rho * (#(whole (orient 0)) : ℝ) < (#rootPool : ℝ))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hmargin : ∀ c,
      (Fintype.card A : ℝ) + rho * (#(whole c) : ℝ) ≤
        (density - rho) * (#(interiorAvailable c) : ℝ)) :
    ∃ f : T.Copy G,
      f root ∈ rootPool ∧
      ∀ a, a ≠ root →
        f a ∈ interiorAvailable
          (orient (hT.coloringTwoOfVert root a)) := by
  classical
  let W₀ := whole (orient 0)
  let W₁ := whole (orient 1)
  let A₀ := interiorAvailable (orient 0)
  let A₁ := interiorAvailable (orient 1)
  have hA₀W₀ : A₀ ⊆ W₀ := by
    simpa [A₀, W₀] using hinterior (orient 0)
  have hA₁W₁ : A₁ ⊆ W₁ := by
    simpa [A₁, W₁] using hinterior (orient 1)
  have hA₀large : rho * (#W₀ : ℝ) ≤ #A₀ := by
    simpa [A₀, W₀] using hinteriorLarge (orient 0)
  have hA₁large : rho * (#W₁ : ℝ) ≤ #A₁ := by
    simpa [A₁, W₁] using hinteriorLarge (orient 1)
  have hrootW₀ : rootPool ⊆ W₀ := by
    simpa [W₀] using hrootPool
  have hrootLargeStrict :
      rho * (#W₀ : ℝ) < (#rootPool : ℝ) := by
    simpa [W₀] using hrootPoolLarge
  have hrootLarge : rho * (#W₀ : ℝ) ≤ (#rootPool : ℝ) :=
    hrootLargeStrict.le
  have hunifO : G.IsUniform rho W₀ W₁ := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W₀, W₁, h.1, h.2] using hunif
    · simpa [W₀, W₁, h.1, h.2] using hunif.symm
  have hdensityO : density ≤ G.edgeDensity W₀ W₁ := by
    rcases finTwoEquiv_zero_one orient with h | h
    · simpa [W₀, W₁, h.1, h.2] using hdensity
    · simpa [W₀, W₁, h.1, h.2, G.edgeDensity_comm] using hdensity
  have hmargin₀ :
      (Fintype.card A : ℝ) + rho * (#W₀ : ℝ) ≤
        (density - rho) * #A₀ := by
    simpa [W₀, A₀] using hmargin (orient 0)
  have hmargin₁ :
      (Fintype.card A : ℝ) + rho * (#W₁ : ℝ) ≤
        (density - rho) * #A₁ := by
    simpa [W₁, A₁] using hmargin (orient 1)

  let bad₀ := dynamicLowDegreeVertices G rho W₀ W₁ A₀ A₁
  let bad₁ := dynamicLowDegreeVertices G rho W₁ W₀ A₁ A₀
  let rootBad := dynamicLowDegreeVertices G rho W₀ W₁ rootPool A₁
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
  have hrootBad : (#rootBad : ℝ) ≤ rho * #W₀ := by
    simpa [rootBad, dynamicLowDegreeVertices] using
      card_lowDegreeVertices_le G hunifO hrootW₀ hA₁W₁
        hrootLarge hA₁large

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

  have hrootBadltReal : (#rootBad : ℝ) < #rootPool := by linarith
  have hrootBadlt : #rootBad < #rootPool := by exact_mod_cast hrootBadltReal
  have hex : ∃ w ∈ rootPool, w ∉ rootBad := by
    by_contra! hall
    have hsub : rootPool ⊆ rootBad := by
      intro w hw
      exact hall w hw
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hrootBadlt
  obtain ⟨w, hwPool, hwNotBad⟩ := hex
  have hwdegree :
      (G.edgeDensity W₀ W₁ - rho) * #A₁ ≤
        (#(A₁.filter (G.Adj w)) : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply hwNotBad
    exact Finset.mem_filter.mpr ⟨hwPool, hlt⟩
  have hrootReal :
      (Fintype.card A : ℝ) + #bad₁ ≤
        (#(A₁.filter (G.Adj w)) : ℝ) := by
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
  have hcandidateSubset : ∀ c, candidate c ⊆ interiorAvailable (orient c) := by
    intro c
    fin_cases c
    · change candidate (0 : Fin 2) ⊆ interiorAvailable (orient (0 : Fin 2))
      rw [hcandidate₀]
      change good₀ ⊆ A₀
      exact Finset.sdiff_subset
    · change candidate (1 : Fin 2) ⊆ interiorAvailable (orient (1 : Fin 2))
      rw [hcandidate₁]
      change good₁ ⊆ A₁
      exact Finset.sdiff_subset
  refine ⟨f, ?_, ?_⟩
  · rw [hfroot]
    exact hwPool
  · intro a ha
    exact hcandidateSubset _ (hfmem a ha)

/-- Attached form of `exists_dynamic_rooted_tree_copy_with_root_pool`.
The caller may take `rootPool` to be a live neighborhood of an already
embedded external parent. -/
theorem exists_dynamic_attached_rooted_tree_copy_with_root_pool
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (orient : Fin 2 ≃ Fin 2)
    (whole interiorAvailable : Fin 2 → Finset B)
    (rootPool : Finset B)
    (rho density : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hinterior : ∀ c, interiorAvailable c ⊆ whole c)
    (hrootPool : rootPool ⊆ whole (orient 0))
    (hinteriorLarge : ∀ c,
      rho * (#(whole c) : ℝ) ≤ (#(interiorAvailable c) : ℝ))
    (hrootPoolLarge :
      rho * (#(whole (orient 0)) : ℝ) < (#rootPool : ℝ))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hmargin : ∀ c,
      (Fintype.card A : ℝ) + rho * (#(whole c) : ℝ) ≤
        (density - rho) * (#(interiorAvailable c) : ℝ))
    (hattach : ∀ w ∈ rootPool, G.Adj z w) :
    ∃ f : T.Copy G,
      G.Adj z (f root) ∧
      f root ∈ rootPool ∧
      ∀ a, a ≠ root →
        f a ∈ interiorAvailable
          (orient (hT.coloringTwoOfVert root a)) := by
  obtain ⟨f, hfroot, hfinterior⟩ :=
    exists_dynamic_rooted_tree_copy_with_root_pool T hT root G orient
      whole interiorAvailable rootPool rho density hunif hinterior hrootPool
      hinteriorLarge hrootPoolLarge hdensity hmargin
  exact ⟨f, hattach _ hfroot, hfroot, hfinterior⟩

end Erdos547b.ZhaoLemma51DynamicRootPool

#print axioms Erdos547b.ZhaoLemma51DynamicRootPool.exists_dynamic_rooted_tree_copy_with_root_pool
#print axioms Erdos547b.ZhaoLemma51DynamicRootPool.exists_dynamic_attached_rooted_tree_copy_with_root_pool
