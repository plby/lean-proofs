import ErdosProblems.Erdos117.Compression
import ErdosProblems.Erdos117.InteractionSpaces
import Mathlib.Data.Nat.Log

/-!
# Index budgets for interaction restrictions

Each exact centralizer costs at most one conjugacy-class bound. Kernel
indices and centralizer indices multiply when the restrictions are combined.
-/

namespace Erdos117

open scoped BigOperators

variable {G : Type*} [Group G]

theorem centralizer_subgroup_index_le [Finite G] (A : Subgroup G) (x : G) :
    ((Subgroup.centralizer ({x} : Set G)).subgroupOf A).index ≤ centralizerIndex x := by
  let C := Subgroup.centralizer ({x} : Set G)
  change C.relIndex A ≤ C.index
  rw [← C.relIndex_top_right]
  apply Subgroup.relIndex_le_of_le_right le_top
  rw [Subgroup.relIndex_top_right]
  exact Subgroup.index_ne_zero_of_finite

def simultaneousCentralizer (A : Subgroup G) {ι : Type*} (a : ι → G) : Subgroup A :=
  ⨅ i, (Subgroup.centralizer ({a i} : Set G)).subgroupOf A

theorem mem_simultaneousCentralizer (A : Subgroup G) {ι : Type*} (a : ι → G) (x : A) :
    x ∈ simultaneousCentralizer A a ↔ ∀ i, Commute (a i) (x : G) := by
  constructor
  · intro hx i
    exact (Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.mem_iInf.mp hx) i)).symm
  · intro hx
    exact Subgroup.mem_iInf.mpr (fun i =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hx i).symm.eq)

theorem simultaneousCentralizer_index_le [Finite G]
    (A : Subgroup G) {ι : Type*} [Fintype ι] (a : ι → G)
    {B : ℕ} (hB : ∀ x : G, centralizerIndex x ≤ B) :
    (simultaneousCentralizer A a).index ≤ B ^ Fintype.card ι := by
  calc
    (simultaneousCentralizer A a).index ≤
        ∏ i, ((Subgroup.centralizer ({a i} : Set G)).subgroupOf A).index :=
      Subgroup.index_iInf_le _
    _ ≤ ∏ _i : ι, B := Finset.prod_le_prod' (fun i _ =>
      (centralizer_subgroup_index_le A (a i)).trans (hB (a i)))
    _ = B ^ Fintype.card ι := by simp

theorem index_iInf_le_pow_sum {ι : Type*} [Fintype ι] (H : ι → Subgroup G)
    (p : ℕ) (c : ι → ℕ) (hH : ∀ i, (H i).index ≤ p ^ c i) :
    (⨅ i, H i).index ≤ p ^ ∑ i, c i := by
  calc
    (⨅ i, H i).index ≤ ∏ i, (H i).index := Subgroup.index_iInf_le H
    _ ≤ ∏ i, p ^ c i := Finset.prod_le_prod' (fun i _ => hH i)
    _ = p ^ ∑ i, c i := Finset.prod_pow_eq_pow_sum _ _ _

theorem simultaneousCentralizer_index_le_pow [Finite G]
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) {ι : Type*} [Fintype ι] (a : ι → G)
    {B : ℕ} (hB : ∀ x : G, centralizerIndex x ≤ B) :
    (simultaneousCentralizer A a).index ≤
      p ^ (Fintype.card ι * Nat.clog p B) := by
  calc
    (simultaneousCentralizer A a).index ≤ B ^ Fintype.card ι :=
      simultaneousCentralizer_index_le A a hB
    _ ≤ (p ^ Nat.clog p B) ^ Fintype.card ι :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (Fact.out : p.Prime).one_lt B) _
    _ = p ^ (Fintype.card ι * Nat.clog p B) := by rw [← pow_mul, Nat.mul_comm]

end Erdos117
