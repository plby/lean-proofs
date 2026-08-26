import ErdosProblems.Erdos117.CentralRecursion
import ErdosProblems.Erdos117.InteractionProduct
import Mathlib.Algebra.BigOperators.Fin

/-!
# Scalar data along a central branch

The branch selected by the cover-tree theorem is indexed by its depth.
Its scalar forms, ranks, and interaction dimensions are actual constructed
objects, and the interaction-product estimates apply to those objects.
-/

namespace Erdos117

open scoped commutatorElement BigOperators

variable {G : Type*} [Group G] {p : ℕ}

theorem CentralChain.term_le_of_le (D : CentralChain G p) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ D.length) : D.term j ≤ D.term i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
    exact (D.step_le (i + k) (by omega)).trans (ih (by omega))

structure CentralBranch (D : CentralChain G p) where
  length : ℕ
  length_eq : length = D.length
  group : Fin length → Subgroup G
  antitone : Antitone group
  halfRank : Fin length → ℕ
  derived_le : ∀ j, ⁅group j, group j⁆ ≤ D.term j
  halfRank_eq : ∀ j, Module.finrank (ZMod p)
    (subgroupCentralBicharacter (group j) (D.term j) (derived_le j) (D.central j)
      (D.character ⟨j, by rw [← length_eq]; exact j.2⟩)).rowSpace = 2 * halfRank j

namespace CentralBranch

variable {D : CentralChain G p} (B : CentralBranch D)

def pairing (j : Fin B.length) : AlternatingBicharacter (B.group j) p :=
  subgroupCentralBicharacter (B.group j) (D.term j) (B.derived_le j) (D.central j)
    (D.character ⟨j, by rw [← B.length_eq]; exact j.2⟩)

theorem pairing_dimension (j : Fin B.length) :
    Module.finrank (ZMod p) (B.pairing j).rowSpace = 2 * B.halfRank j := B.halfRank_eq j

theorem pairing_half_dimension (j : Fin B.length) :
    Module.finrank (ZMod p) (B.pairing j).rowSpace / 2 = B.halfRank j := by
  rw [B.pairing_dimension]
  omega

theorem pairing_zero_iff (j : Fin B.length) (x y : B.group j) :
    (B.pairing j).toFun x y = 0 ↔ ⁅(x : G), (y : G)⁆ ∈ D.term (j + 1) :=
  subgroupCentralBicharacter_zero_iff _ _ _ _ _ _ (D.character_ker _) x y

theorem pairing_commute (j : Fin B.length) (x y : B.group j) (hxy : Commute x y) :
    (B.pairing j).toFun x y = 0 := by
  have hc : Commute (x : G) (y : G) := hxy.map (B.group j).subtype
  rw [B.pairing_zero_iff, hc.commutator_eq]
  exact Subgroup.one_mem _

noncomputable def interactionRank (j k : Fin B.length) : ℕ :=
  Module.finrank (ZMod p) (subgroupImageSpace (p := p)
    (B.pairing j).rowMonoidHom ((B.group k).subgroupOf (B.group j)))

theorem later_derived_le {j k : Fin B.length} (hjk : j < k) :
    ⁅B.group k, B.group k⁆ ≤ D.term (j + 1) := by
  apply (B.derived_le k).trans
  apply D.term_le_of_le (by simpa using hjk)
  rw [← B.length_eq]
  exact Nat.le_of_lt k.2

theorem scalar_credit_bound [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n) (j : Fin B.length) :
    scalarCreditRate p * B.halfRank j ≤ n - 1 + scalarDefect p := by
  have h := (B.pairing j).scalar_credit_bound (hn.subgroup (B.group j)) (B.pairing_commute j)
  rwa [B.pairing_half_dimension] at h

theorem product_inequality [Finite G] [Fact p.Prime]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    {j k : Fin B.length} (hjk : j < k) {d : ℕ} (hd : d ≤ B.interactionRank j k) :
    ∃ c : ℕ, scalarCreditRate p * B.halfRank k ≤
        c + scalarDefect p + scalarCreditRate p * ((d + 1) * Nat.clog p ((2 * n) ^ 2)) ∧
      (d + 1) * (c + 1) ≤ n := by
  have h := interaction_product_inequality hG hn (B.group j) (B.group k) (D.term (j + 1))
    (B.later_derived_le hjk) (B.pairing j) (B.pairing k)
    (B.pairing_zero_iff j) (B.pairing_commute k) hd
  rwa [B.pairing_half_dimension] at h

theorem expensive_interaction [Finite G] [Fact p.Prime]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    {j k : Fin B.length} (hjk : j < k) (hm : 0 < B.halfRank k)
    (hexpensive : 128 * n * Nat.clog p ((2 * n) ^ 2) ≤
      scalarCreditRate p * B.halfRank k * B.halfRank k) :
    B.interactionRank j k * (scalarCreditRate p * B.halfRank k) ≤ 4 * n := by
  have h := expensive_stage_interaction hG hn (B.group j) (B.group k) (D.term (j + 1))
    (B.later_derived_le hjk) (B.pairing j) (B.pairing k)
    (B.pairing_zero_iff j) (B.pairing_commute k)
    (by rwa [B.pairing_half_dimension]) (by rwa [B.pairing_half_dimension])
  rwa [B.pairing_half_dimension] at h

end CentralBranch

/-- A branch controlling the cover, now with depth-indexed scalar and
interaction data suitable for the quantitative estimates. -/
theorem exists_indexed_branch_cover [Finite G] [Fact p.Prime]
    (hP : IsPGroup p G) (hcentral : commutator G ≤ Subgroup.center G) :
    ∃ (D : CentralChain G p) (B : CentralBranch D),
      D.term 0 = commutator G ∧ Nat.card (commutator G) = p ^ B.length ∧
      HasAbelianCover G (2 ^ B.length * p ^ ∑ j, B.halfRank j) := by
  classical
  obtain ⟨D, b, hD0, hcard, hlen, hanti, hrank, hcover⟩ :=
    exists_class_two_branch_cover hP hcentral
  choose hj hderived hdim using hrank
  let B : CentralBranch D := {
    length := b.length
    length_eq := hlen
    group := fun j => (b.get j).1
    antitone := hanti
    halfRank := fun j => (b.get j).2
    derived_le := hderived
    halfRank_eq := hdim }
  have hsum : (∑ j : Fin b.length, (b.get j).2) = (b.map Prod.snd).sum := by
    rw [← List.sum_ofFn]
    congr 1
    rw [← Function.comp_def, ← List.map_ofFn, List.ofFn_get]
  refine ⟨D, B, hD0, ?_, ?_⟩
  · change Nat.card (commutator G) = p ^ b.length
    rwa [hlen]
  · change HasAbelianCover G (2 ^ b.length * p ^ ∑ j : Fin b.length, (b.get j).2)
    rwa [hsum, hlen]

end Erdos117
