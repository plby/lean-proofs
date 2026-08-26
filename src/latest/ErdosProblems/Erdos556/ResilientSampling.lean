import ErdosProblems.Erdos556.Sampling
import ErdosProblems.Erdos556.DisjointPacking

/-!
# Sampling with bounded forbidden sets

Greedy disjoint packings are split into groups. Sampling captures one set
from each group, so deleting at most `a` vertices cannot spoil all `a + 1`
captured sets. The only numerical hypothesis is the displayed finite
failure bound.
-/

namespace Erdos556

open Finset

theorem exists_small_set_of_avoidance {E I : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] (P : I → Finset E → Prop) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (L b m a : ℕ) (hbound : ((a + 1) * m) * L ≤ b)
    (havoid : ∀ i S, S.card ≤ b →
      ∃ T : Finset E, P i T ∧ T.card ≤ L ∧ Disjoint S T)
    (hfail : (Fintype.card I : ℝ) * (a + 1) * (1 - q ^ L) ^ m < 1 / 2)
    (hE : 0 < Fintype.card E) :
    ∃ S : Finset E, (S.card : ℝ) ≤ 2 * q * Fintype.card E ∧
      ∀ i T, T.card ≤ a → ∃ U : Finset E,
        U ⊆ S ∧ P i U ∧ U.card ≤ L ∧ Disjoint T U := by
  classical
  have hpacks (i : I) := exists_disjoint_family (P i) L b ((a + 1) * m)
    hbound (havoid i)
  choose R hR hD using hpacks
  let Q (i : I × Fin (a + 1)) (j : Fin m) : Finset E :=
    R i.1 (finProdFinEquiv (i.2, j))
  have hQD (i : I × Fin (a + 1)) :
      (Set.univ : Set (Fin m)).Pairwise fun j k => Disjoint (Q i j) (Q i k) := by
    intro j _ k _ hjk
    apply hD i.1
    intro heq
    exact hjk (congrArg Prod.snd (finProdFinEquiv.injective heq))
  have hQS (i : I × Fin (a + 1)) (j : Fin m) : (Q i j).card ≤ L :=
    (hR i.1 (finProdFinEquiv (i.2, j))).2
  have hfailure : (Fintype.card (I × Fin (a + 1)) : ℝ) *
      (1 - q ^ L) ^ m < 1 / 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one] using hfail
  obtain ⟨S, hS, hhit⟩ := Bernoulli.exists_small_set_hitting_families
    q hq0 hq1 L m Q hQD hQS hfailure hE
  refine ⟨S, hS, ?_⟩
  intro i T hT
  have hg (g : Fin (a + 1)) : ∃ j, Q (i, g) j ⊆ S := hhit (i, g)
  choose j hj using hg
  let F (g : Fin (a + 1)) : Finset E := Q (i, g) (j g)
  have hFD : Pairwise (fun g h => Disjoint (F g) (F h)) := by
    intro g h hgh
    apply hD i
    intro heq
    exact hgh (congrArg Prod.fst (finProdFinEquiv.injective heq))
  obtain ⟨g, hgT⟩ := exists_disjoint_of_card_lt F T hFD
    (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hT)
  exact ⟨F g, hj g, (hR i (finProdFinEquiv (g, j g))).1, hQS (i, g) (j g), hgT⟩

#print axioms exists_small_set_of_avoidance

end Erdos556
