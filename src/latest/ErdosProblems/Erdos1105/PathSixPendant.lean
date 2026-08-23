import ErdosProblems.Erdos1105.EvenThreeClique
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph Finset

theorem path_six_pendant_rainbow_bound {V C : Type*} [Fintype V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) [DecidableRel R.Adj]
    (hR : Set.InjOn (extendColor c) R.edgeSet) (hn : 6 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hshape : PendantCliqueShape R 6) : R.edgeFinset.card ≤ pathFormula (Fintype.card V) 6 := by
  classical
  by_contra! hhigh
  obtain ⟨S, hS, u, hu, hpend⟩ := hshape
  have hS4 : S.card = 4 := hS
  let Q := threeCliqueJoin {u} (S.erase u)
  have hRQ : R ≤ Q := by
    intro x y hxy
    refine ⟨hxy.ne, ?_⟩
    by_cases hxu : x = u
    · exact Or.inl (mem_singleton.mpr hxu)
    by_cases hyu : y = u
    · exact Or.inr (Or.inl (mem_singleton.mpr hyu))
    have hxS : x ∈ S := by by_contra h; exact hyu (hpend x h y hxy)
    have hyS : y ∈ S := by by_contra h; exact hxu (hpend y h x hxy.symm)
    exact Or.inr (Or.inr ⟨mem_erase.mpr ⟨hxu, hxS⟩, mem_erase.mpr ⟨hyu, hyS⟩⟩)
  have hQshape : PendantCliqueShape Q 6 := by
    refine ⟨S, hS, u, hu, ?_⟩
    intro x hx y hxy
    rcases hxy.2 with hxU | hyU | hST
    · exact (hx ((mem_singleton.mp hxU) ▸ hu)).elim
    · exact mem_singleton.mp hyU
    · exact (hx (mem_erase.mp hST.1).2).elim
  have hQcount := hQshape.edge_bound (by omega) hn
  have hlinear : Fintype.card V + 1 < R.edgeFinset.card := by
    have h := (le_max_right _ _).trans_lt hhigh
    norm_num [pathFormula] at h
    omega
  have hQR : Q ≤ R := by
    have hcard : Q.edgeFinset.card ≤ R.edgeFinset.card := by
      norm_num [pathExtremalEdges, Nat.choose] at hQcount
      omega
    have heq := edgeFinset_inj.mp (eq_of_subset_of_card_le (edgeFinset_mono hRQ) hcard)
    exact heq.ge
  obtain ⟨f, hf⟩ := rainbow_path_of_threeCliqueJoin c hR (l := 2) (by omega) hn
    (A := {u}) (T := S.erase u)
    (by simp) (by simp) (by rw [card_erase_of_mem hu, hS4]) hQR
  exact hfree f hf

end Erdos1105

#print axioms Erdos1105.path_six_pendant_rainbow_bound
