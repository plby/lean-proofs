import ErdosProblems.Erdos117.InteractionIndex
import ErdosProblems.Erdos117.DirectProducts
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Reduction to class two by centralizing triples

A noncentral commutator in a subgroup cannot be cancelled by a commutator
from its centralizer: the latter commutes with the witnessing third element.
This permits doubling a clique in the common centralizer.
-/

namespace Erdos117

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem not_commute_mul_of_noncentral_commutator (K : Subgroup G) (a b z : K)
    (hz : ¬Commute (⁅(a : G), (b : G)⁆) (z : G))
    (u v : Subgroup.centralizer (K : Set G)) :
    ¬Commute ((a : G) * u) ((b : G) * v) := by
  let C := Subgroup.centralizer (K : Set G)
  let m : K × C →* G := K.subtype.noncommCoprod C.subtype (fun x y =>
    Subgroup.mem_centralizer_iff.mp y.property x x.property)
  intro hc
  have hprod : (⁅a, b⁆ : K).val * (⁅u, v⁆ : C).val = 1 := by
    change m ⁅(a, u), (b, v)⁆ = 1
    rw [map_commutatorElement]
    exact hc.commutator_eq
  have heq : (⁅a, b⁆ : K).val = (⁅u, v⁆ : C).val⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hprod
  have hmem : ⁅(a : G), (b : G)⁆ ∈ C := by
    change (⁅a, b⁆ : K).val ∈ C
    rw [heq]
    exact C.inv_mem (⁅u, v⁆ : C).property
  exact hz (Subgroup.mem_centralizer_iff.mp hmem z z.property).symm

theorem commute_same_left_centralizer_iff (K : Subgroup G) (a : K)
    (u v : Subgroup.centralizer (K : Set G)) :
    Commute ((a : G) * u) ((a : G) * v) ↔ Commute u v := by
  let C := Subgroup.centralizer (K : Set G)
  let m : K × C →* G := K.subtype.noncommCoprod C.subtype (fun x y =>
    Subgroup.mem_centralizer_iff.mp y.property x x.property)
  have heq : ⁅(a : G) * u, (a : G) * v⁆ = (⁅u, v⁆ : C).val := by
    change ⁅m (a, u), m (a, v)⁆ = _
    rw [← map_commutatorElement]
    change (⁅a, a⁆ : K).val * (⁅u, v⁆ : C).val = _
    rw [commutatorElement_self]
    exact one_mul _
  rw [← commutatorElement_eq_one_iff_commute, heq,
    ← commutatorElement_eq_one_iff_commute]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg (fun x : C => (x : G)) h

/-- A noncentral commutator doubles every clique in the centralizer of the
subgroup containing its two entries and a witness to noncentrality. -/
theorem noncommutingBound_centralizer_half {n : ℕ} (hn : NoncommutingBound G n)
    (K : Subgroup G) (a b z : K)
    (hz : ¬Commute (⁅(a : G), (b : G)⁆) (z : G)) :
    NoncommutingBound (Subgroup.centralizer (K : Set G)) (n / 2) := by
  classical
  let C := Subgroup.centralizer (K : Set G)
  intro s hs
  let f : Bool × s → G := fun t => (if t.1 then (a : G) else (b : G)) * t.2.val
  have hsame (c : K) (u v : s) (huv : (false, u) ≠ (false, v)) :
      ¬Commute ((c : G) * u.val) ((c : G) * v.val) := by
    intro h
    have h' := (commute_same_left_centralizer_iff K c u.val v.val).mp h
    apply hs u.property v.property ?_ h'
    intro heq
    exact huv (congrArg (fun w : s => (false, w)) (Subtype.ext heq))
  have hf : ∀ i j, i ≠ j → ¬Commute (f i) (f j) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ hij
    cases i <;> cases j
    · exact hsame b u v hij
    · intro h
      exact not_commute_mul_of_noncentral_commutator K a b z hz v.val u.val h.symm
    · exact not_commute_mul_of_noncentral_commutator K a b z hz u.val v.val
    · apply hsame a u v
      intro heq
      apply hij
      exact congrArg (fun w : s => (true, w)) (Prod.mk.inj heq).2
  have hcard := hn.card_le hf
  have hdouble : 2 * s.card ≤ n := by simpa only [Fintype.card_prod,
    Fintype.card_bool, Fintype.card_coe] using hcard
  omega

theorem class_two_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (hG : commutator G ≤ Subgroup.center G) :
    commutator H ≤ Subgroup.center H := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  apply Subgroup.mem_center_iff.mpr
  intro z
  have hc : Commute (e.symm z) ⁅e.symm x, e.symm y⁆ :=
    Subgroup.mem_center_iff.mp
      (hG (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))) _
  have h := hc.map e
  simpa only [map_commutatorElement, e.apply_symm_apply] using h.eq

/-- Centralizing the three entries of a noncentral commutator costs at most
three centralizer indices. -/
theorem centralizer_triple_index_le [Finite G] (a b z : G) {B : ℕ}
    (hB : ∀ x : G, centralizerIndex x ≤ B) :
    (Subgroup.centralizer (Subgroup.closure ({a, b, z} : Set G) : Set G)).index ≤ B ^ 3 := by
  have heq : Subgroup.centralizer (Subgroup.closure ({a, b, z} : Set G) : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓
        (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [Subgroup.centralizer_closure]
    ext x
    simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, Subgroup.mem_inf]
  rw [heq]
  calc
    _ ≤ (Subgroup.centralizer ({a} : Set G)).index *
        (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)).index :=
      Subgroup.index_inf_le
    _ ≤ B * (B * B) := Nat.mul_le_mul (hB a)
      (Subgroup.index_inf_le.trans (Nat.mul_le_mul (hB b) (hB z)))
    _ = B ^ 3 := by ring

/-- Repeated centralization of noncentral-commutator triples reaches a
class-two subgroup after at most `log₂ n` steps. This avoids any estimate on
the order of the derived subgroup of the original group. -/
theorem exists_class_two_subgroup_small_index [Finite G] {n B : ℕ}
    (hn : NoncommutingBound G n) (hB : ∀ x : G, centralizerIndex x ≤ B) :
    ∃ (d : ℕ) (F : Subgroup G), 2 ^ d ≤ n ∧
      commutator F ≤ Subgroup.center F ∧ F.index ≤ B ^ (3 * d) := by
  classical
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    have hn1 := one_le_of_noncommutingBound hn
    by_cases hG : commutator G ≤ Subgroup.center G
    · refine ⟨0, ⊤, by simpa using hn1, class_two_subgroup hG ⊤, ?_⟩
      simp
    have hex : ∃ a b z : G, ¬Commute ⁅a, b⁆ z := by
      by_contra! h
      apply hG
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      apply Subgroup.mem_center_iff.mpr
      intro z
      exact (h a b z).symm.eq
    obtain ⟨a, b, z, hz⟩ := hex
    let K := Subgroup.closure ({a, b, z} : Set G)
    let C := Subgroup.centralizer (K : Set G)
    have haK : a ∈ K := Subgroup.subset_closure (by simp)
    have hbK : b ∈ K := Subgroup.subset_closure (by simp)
    have hzK : z ∈ K := Subgroup.subset_closure (by simp)
    have hhalf : NoncommutingBound C (n / 2) :=
      noncommutingBound_centralizer_half hn K ⟨a, haK⟩ ⟨b, hbK⟩ ⟨z, hzK⟩ hz
    have hBC : ∀ x : C, centralizerIndex x ≤ B := by
      intro x
      have heq : Subgroup.centralizer ({x} : Set C) =
          (Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf C := by
        ext y
        simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
        exact Subtype.ext_iff
      change (Subgroup.centralizer ({x} : Set C)).index ≤ B
      rw [heq]
      exact (centralizer_subgroup_index_le C x).trans (hB x)
    obtain ⟨d, F, hd, hF, hidx⟩ := ih (n / 2) (by omega) hhalf hBC
    let e := F.equivMapOfInjective C.subtype C.subtype_injective
    refine ⟨d + 1, F.map C.subtype, ?_, class_two_of_mulEquiv e hF, ?_⟩
    · rw [pow_succ]
      omega
    · rw [Subgroup.index_map_subtype]
      have hC : C.index ≤ B ^ 3 := centralizer_triple_index_le a b z hB
      calc
        F.index * C.index ≤ B ^ (3 * d) * B ^ 3 := Nat.mul_le_mul hidx hC
        _ = B ^ (3 * (d + 1)) := by rw [← pow_add]; congr 1

end Erdos117
