import Arxiv.Arxiv2411_18291.ExchangeSeed

/-!
# The extra intersection condition needed for elimination

Elimination uses at most one common edge between opposite decomposition
cliques. The printed seed, translated by zero on the distinguished parts
and one elsewhere, need not have this property. Its all-one positive
clique meets the designated negative clique in `q-r` vertices.

We retain that seed and record the issue explicitly. A degree-`r`
polynomial translation will supply the stronger seed separately.
-/

open Finset Polynomial

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ}

def IsCrossSimple (r : ℕ) (P N : Finset (Block V q)) : Prop :=
  ∀ Q ∈ P, ∀ R ∈ N, (Q.val ∩ R.val).card ≤ r

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem exchangeShift_one_inter (I : Block (Fin q) r) :
    (graphClique (fun _ : Fin q => (1 : F))).val ∩ (graphClique (exchangeShift I)).val =
      (univ \ I.val).map ⟨fun i => (i, (1 : F)), fun _ _ h => congrArg Prod.fst h⟩ := by
  ext ⟨i, x⟩
  constructor
  · intro h
    have hx := (mem_graphClique _ i x).mp (mem_inter.mp h).1
    have hx' := (mem_graphClique _ i x).mp (mem_inter.mp h).2
    refine mem_map.mpr ⟨i, mem_sdiff.mpr ⟨mem_univ _, ?_⟩, Prod.ext rfl hx.symm⟩
    intro hi
    have hx0 : x = 0 := by simpa [exchangeShift, hi] using hx'
    exact one_ne_zero (hx.symm.trans hx0)
  · intro h
    obtain ⟨j, hj, hjx⟩ := mem_map.mp h
    have hji : j = i := congrArg Prod.fst hjx
    have hx : (1 : F) = x := congrArg Prod.snd hjx
    subst j
    refine mem_inter.mpr ⟨(mem_graphClique _ _ _).mpr hx.symm, ?_⟩
    simpa [exchangeShift, (mem_sdiff.mp hj).2] using hx.symm

omit [Fintype F] in
theorem exchangeShift_one_inter_card (I : Block (Fin q) r) :
    ((graphClique (fun _ : Fin q => (1 : F))).val ∩
      (graphClique (exchangeShift I)).val).card = q - r := by
  rw [exchangeShift_one_inter, card_map, card_sdiff_of_subset (subset_univ I.val)]
  simp only [card_univ, Fintype.card_fin, I.property]

theorem fieldExchangeSeed_large_opposite_inter (y : Fin q → F) (hy : Function.Injective y)
    (hr : 0 < r) (hlarge : 2 * r < q) (I : Block (Fin q) r) :
    ∃ P ∈ (fieldExchangeSeed y hy (by omega) I).positive.erase
      (fieldExchangeSeed y hy (by omega) I).positiveClique,
      r < (P.val ∩ (fieldExchangeSeed y hy (by omega) I).negativeClique.val).card := by
  let P := graphClique (fun _ : Fin q => (1 : F))
  have hP : P ∈ polynomialDecomposition r y 0 := by
    apply (mem_polynomialDecomposition _ _ _).mpr
    refine ⟨1, ?_, ?_⟩
    · simpa using (WithBot.coe_lt_coe.mpr hr : (0 : WithBot ℕ) < (r : WithBot ℕ))
    · simp [P]
  have hPne : P ≠ graphClique (fun _ : Fin q => (0 : F)) := by
    intro h
    have heq := congrFun (graphClique_injective h) (⟨0, by omega⟩ : Fin q)
    exact one_ne_zero heq
  refine ⟨P, mem_erase.mpr ⟨hPne, hP⟩, ?_⟩
  change r < ((graphClique (fun _ : Fin q => (1 : F))).val ∩
    (graphClique (exchangeShift I)).val).card
  rw [exchangeShift_one_inter_card]
  omega

end Arxiv2411_18291
