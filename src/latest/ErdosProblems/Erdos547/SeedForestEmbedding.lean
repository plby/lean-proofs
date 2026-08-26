import ErdosProblems.Erdos547.SeedTypicalPools
import ErdosProblems.Erdos547.ForestLabelledEmbedding

/-!
# Embedding all seeds with two external typicality conditions
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq V]

theorem exists_typical_seed_forest_copy
    (F : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hF : F.IsAcyclic) (col : U → Fin 2) (hcol : Function.Surjective col)
    (hproper : ∀ u v, F.Adj u v → col u ≠ col v)
    (ε δ d : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) (hεone : ε ≤ 1)
    (hclean : ε + 2 * δ < 1)
    (X : Fin 2 → Finset V) (m : ℕ) (hm : 0 < m) (hsize : ∀ i, (X i).card = m)
    (hdis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hXY : ∀ i j, i ≠ j → G.IsUniform ε (X i) (X j))
    (hdensity : ∀ i j, i ≠ j → d ≤ (G.edgeDensity (X i) (X j) : ℝ))
    (hsmall : (Fintype.card U : ℝ) ≤ (d - 2 * ε - 2 * δ) * m)
    (J : Fin 2 → Finset I) (C B Q : I → Finset V)
    (hreg : ∀ i l, l ∈ J i → G.IsUniform ε (X i) (C l))
    (hB : ∀ i l, l ∈ J i → B l ⊆ C l)
    (hQ : ∀ i l, l ∈ J i → Q l ⊆ C l)
    (hBsize : ∀ i l, l ∈ J i → ((C l).card : ℝ) * ε ≤ (B l).card)
    (hQsize : ∀ i l, l ∈ J i → ((C l).card : ℝ) * ε ≤ (Q l).card) :
    ∃ f : F.Copy G, ∀ u,
      f u ∈ X (col u) ∧
      ((nonTypicalPartners G ε (X (col u)) (J (col u)) C B (f u)).card : ℝ) ≤
        δ * (J (col u)).card ∧
      ((nonTypicalPartners G ε (X (col u)) (J (col u)) C Q (f u)).card : ℝ) ≤
        δ * (J (col u)).card := by
  classical
  have hflip (i j : Fin 2) (hij : i ≠ j) : flipTreeColour i = j := by
    fin_cases i <;> fin_cases j <;> simp_all [flipTreeColour]
  have hpool (i : Fin 2) := exists_seed_typical_pool G hδ hεδ hεone
    (X i) (X (flipTreeColour i))
    (hXY i (flipTreeColour i) (flipTreeColour_ne i).symm)
    (J i) C B Q (hreg i) (hB i) (hQ i) (hBsize i) (hQsize i)
  choose P hsub hloss htyp using hpool
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hPne (i : Fin 2) : (P i).Nonempty := by
    by_contra hn
    have he : P i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := hloss i
    simp only [he, Finset.sdiff_empty, hsize] at hh
    exact (not_le_of_gt (mul_lt_mul_of_pos_right hclean hm')) (by simpa using hh)
  have hPdis (i j : Fin 2) (hij : i ≠ j) : Disjoint (P i) (P j) :=
    (hdis i j hij).mono (hsub i) (hsub j)
  have hPdegree (i j : Fin 2) (hij : i ≠ j) (z : V) (hz : z ∈ P i) :
      Fintype.card U ≤ degreeIn G (P j) z := by
    have hh := (htyp i z hz).1
    rw [hflip i j hij, hsize] at hh
    have hdrop := hloss j
    rw [hsize] at hdrop
    have hremove : (degreeIn G (X j) z : ℝ) ≤
        (degreeIn G (P j) z : ℝ) + (X j \ P j).card := by
      exact_mod_cast degreeIn_le_add_removed G (X j) (P j) z
    have hden := mul_le_mul_of_nonneg_right (hdensity i j hij) hm'.le
    have hbound : (Fintype.card U : ℝ) ≤ degreeIn G (P j) z := by
      nlinarith only [hh, hdrop, hremove, hden, hsmall]
    exact_mod_cast hbound
  obtain ⟨r, _hr⟩ := hcol 0
  obtain ⟨z, hz⟩ := hPne (col r)
  obtain ⟨f, _hfr, hf⟩ := exists_copy_of_two_coloured_forest F G hF col hcol hproper
    P hPdis hPdegree r z hz
  exact ⟨f, fun u ↦ ⟨hsub (col u) (hf u), (htyp (col u) (f u) (hf u)).2⟩⟩

end Erdos547

#print axioms Erdos547.exists_typical_seed_forest_copy
