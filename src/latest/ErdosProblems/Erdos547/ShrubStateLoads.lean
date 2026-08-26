import ErdosProblems.Erdos547.ShrubReservations
import ErdosProblems.Erdos547.RoutedCapacity

/-!
# Routed far-class capacities control the free space of a shrub state
-/

namespace Erdos547.ShrubState

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}

noncomputable def shrubGroup (P : FineTreePartition T r ℓ col) (head : ↥P.shrubs → I)
    (S : ↥P.shrubs) : Fin 2 × I := (P.shrubColour S, head S)

noncomputable def farLoad (E : ShrubState P G C head seed) (a : Fin 2 × I) (i : I) : ℕ :=
  routedLoad E.placed (shrubGroup P head) E.tail (fun S ↦ (P.farPart S).card) a i

theorem sum_farLoad (E : ShrubState P G C head seed) (i : I) :
    (∑ a, E.farLoad a i) = E.farUsed i :=
  routedLoad_sum_groups E.placed (shrubGroup P head) E.tail (fun S ↦ (P.farPart S).card) i

theorem available_from_capacities (E : ShrubState P G C head seed)
    (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (capacity : (Fin 2 × I) → I → ℝ)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ capacity a i)
    (F : Finset ↥P.shrubs) (hEF : Disjoint E.placed F) (R : ↥P.shrubs → Finset V)
    (hR : ∀ S ∈ F, R S ⊆ C (head S))
    (hRsize : ∀ S ∈ F, (R S).card ≤ (P.nearPart S).card)
    (i : I) (Q : Finset V) (m m₀ q : ℕ)
    (hm : (C i).card = m) (hQ : Q.card = q) (hmain : m₀ + 2 * q = m)
    (hseed : 2 * P.seeds.card ≤ q)
    (hbudget : (∑ S, if head S = i then ((P.nearPart S).card : ℝ) else 0) +
      (∑ a, capacity a i) ≤ m₀) :
    (q : ℝ) / 2 ≤ ((C i \ (Q ∪ E.occupied ∪ F.biUnion R)).card : ℝ) := by
  have hfar : (E.farUsed i : ℝ) ≤ ∑ a, capacity a i := by
    rw [← E.sum_farLoad i, Nat.cast_sum]
    exact Finset.sum_le_sum fun a _ ↦ hcap a i
  have hload : (∑ S, if head S = i then (P.nearPart S).card else 0) + E.farUsed i ≤ m₀ := by
    have hh : (∑ S, if head S = i then ((P.nearPart S).card : ℝ) else 0) +
        (E.farUsed i : ℝ) ≤ m₀ := by linarith only [hfar, hbudget]
    exact_mod_cast hh
  exact E.available_from_loads hC F hEF R hR hRsize i Q m m₀ q hm hQ hmain hseed hload

theorem exists_target (E : ShrubState P G C head seed) (a : Fin 2 × I)
    (capacity : (Fin 2 × I) → I → ℝ) (s L : ℝ)
    (hs : 0 < s) (hsone : s ≤ 1) (hL : 0 ≤ L)
    (hpositive : 0 < ∑ i, capacity a i)
    (hdemand : (∑ S, if shrubGroup P head S = a then ((P.farPart S).card : ℝ) else 0) ≤
      (1 - s) * ∑ i, capacity a i)
    (hsmall : L * Fintype.card I ≤ s / 4 * ∑ i, capacity a i) :
    ∃ i, L ≤ capacity a i ∧ (E.farLoad a i : ℝ) < (1 - s / 2) * capacity a i :=
  exists_routed_target E.placed (shrubGroup P head) E.tail (fun S ↦ (P.farPart S).card)
    a (capacity a) s L hs hsone hL hpositive hdemand hsmall

theorem capacities_after_insert (E E' : ShrubState P G C head seed)
    (S : ↥P.shrubs) (hS : S ∉ E.placed) (j : I)
    (hplaced : E'.placed = insert S E.placed) (htail : E'.tail = Function.update E.tail S j)
    (capacity : (Fin 2 × I) → I → ℝ) (s : ℝ)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ capacity a i)
    (hpositive : 0 < capacity (shrubGroup P head S) j) (hs : 0 < s)
    (htarget : (E.farLoad (shrubGroup P head S) j : ℝ) <
      (1 - s / 2) * capacity (shrubGroup P head S) j)
    (hsmall : ((P.farPart S).card : ℝ) ≤ s / 4 * capacity (shrubGroup P head S) j) :
    ∀ a i, (E'.farLoad a i : ℝ) ≤ capacity a i := by
  intro a i
  unfold farLoad
  rw [hplaced, htail]
  exact routed_capacity_preserved E.placed (shrubGroup P head) E.tail
    (fun S ↦ (P.farPart S).card) capacity S hS j s hcap hpositive hs htarget hsmall a i

end Erdos547.ShrubState

#print axioms Erdos547.ShrubState.available_from_capacities
#print axioms Erdos547.ShrubState.capacities_after_insert
