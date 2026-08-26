import ErdosProblems.Erdos547.CoatedTree

/-!
# The two padding centres and their indexed arms
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*}

def coatingSeed (r : U) (m : ℕ) (i : Fin 2) : CoatedVertex U m :=
  Sum.inl (Sum.inl (if i = 0 then Sum.inl r else Sum.inr ()))

def coatingMiddle {m : ℕ} (i : Fin 2) (j : Fin m) : CoatedVertex U m := Sum.inl (Sum.inr (i, j))

def coatingEnd {m : ℕ} (i : Fin 2) (j : Fin m) : CoatedVertex U m := Sum.inr (i, j)

theorem coatingMiddle_injective {m : ℕ} (i : Fin 2) :
    Function.Injective (coatingMiddle (U := U) i : Fin m → CoatedVertex U m) := by
  intro j k h
  exact congrArg Prod.snd (Sum.inr.inj (Sum.inl.inj h))

theorem coatingEnd_injective {m : ℕ} (i : Fin 2) :
    Function.Injective (coatingEnd (U := U) i : Fin m → CoatedVertex U m) := by
  intro j k h
  exact congrArg Prod.snd (Sum.inr.inj h)

theorem coatingSeed_ne_end (r : U) (m : ℕ) (i : Fin 2) (j : Fin m) :
    coatingSeed r m i ≠ coatingEnd (U := U) i j := Sum.inl_ne_inr

theorem coatedTree_adj_seed_middle (T : SimpleGraph U) (r : U) (m : ℕ)
    (i : Fin 2) (j : Fin m) :
    (coatedTree T r m).Adj (coatingSeed r m i) (coatingMiddle i j) := by
  fin_cases i <;> simp [coatedTree, attachTwoPaths, attachLeaves, coatingSeed,
    coatingMiddle, coatingParent]

theorem coatedTree_adj_middle_end (T : SimpleGraph U) (r : U) (m : ℕ)
    (i : Fin 2) (j : Fin m) :
    (coatedTree T r m).Adj (coatingMiddle i j) (coatingEnd i j) := rfl

theorem coatedTreeColour_seed {T : SimpleGraph U} (col : T.Coloring (Fin 2))
    (r : U) (hr : col r = 0) (m : ℕ) (i : Fin 2) :
    coatedTreeColour col r m (coatingSeed r m i) = i := by
  fin_cases i
  · change col r = 0
    exact hr
  · change flipTreeColour (col r) = 1
    simp [hr, flipTreeColour]

open scoped Classical in
theorem coatingSeed_degree_lower [Fintype U] [DecidableEq U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (r : U) (m : ℕ) (i : Fin 2) :
    m ≤ (coatedTree T r m).degree (coatingSeed r m i) := by
  classical
  let G := coatedTree T r m
  have hsub : (Finset.univ : Finset (Fin m)).image (coatingMiddle (U := U) i) ⊆
      G.neighborFinset (coatingSeed r m i) := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (G.mem_neighborFinset _ _).mpr (coatedTree_adj_seed_middle T r m i j)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (coatingMiddle_injective i), Finset.card_univ,
    Fintype.card_fin, G.card_neighborFinset_eq_degree] at hh
  exact hh

end Erdos547

#print axioms Erdos547.coatingSeed_degree_lower
