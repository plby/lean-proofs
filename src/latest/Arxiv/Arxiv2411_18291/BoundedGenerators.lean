import Arxiv.Arxiv2411_18291.FiniteGroupGrowth
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log

/-!
# Generating all unsaturated elements with bounded loads

Choose a family with bounded incidence counts and with exponential subgroup
growth. A maximal such family generates every element whose incident tests
are still unsaturated. Its size is at most the base-two logarithm of the
ambient group order. This is the deterministic selection step in `lem:KSG`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I T A : Type*} [AddGroup A] [Finite A]

theorem exists_generating_subfamily_with_caps (F : Finset I) (f : I → A)
    (incidence : I → T → Prop) [DecidableRel incidence] (cap : T → ℕ) :
    ∃ G : Finset I, G ⊆ F ∧
      (∀ t, (G.filter fun i => incidence i t).card ≤ cap t) ∧
      2 ^ G.card ≤ Nat.card (generatedSubgroup f G) ∧
      G.card ≤ Nat.log 2 (Nat.card A) ∧
      ∀ i ∈ F, (∀ t, incidence i t → (G.filter fun j => incidence j t).card < cap t) →
        f i ∈ generatedSubgroup f G := by
  classical
  let candidates := F.powerset.filter fun G =>
    (∀ t, (G.filter fun i => incidence i t).card ≤ cap t) ∧
      2 ^ G.card ≤ Nat.card (generatedSubgroup f G)
  have hempty : (∅ : Finset I) ∈ candidates := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (empty_subset F), ?_, ?_⟩
    · simp only [filter_empty, card_empty, Nat.zero_le, implies_true]
    · simp only [card_empty, pow_zero]
      exact Nat.succ_le_iff.mpr Nat.card_pos
  obtain ⟨G, hG, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hempty⟩
  obtain ⟨hGF, hdegree, hpow⟩ := mem_filter.mp hG
  have hambient : Nat.card (generatedSubgroup f G) ≤ Nat.card A :=
    Nat.card_le_card_of_injective (fun x : generatedSubgroup f G => x.val) Subtype.coe_injective
  refine ⟨G, mem_powerset.mp hGF, hdegree, hpow,
    Nat.le_log_of_pow_le (by decide) (hpow.trans hambient), ?_⟩
  intro i hiF hunsaturated
  by_contra hi
  have hiG : i ∉ G := fun h => hi (mem_generatedSubgroup f h)
  have hdegrees (t : T) : ((insert i G).filter fun j => incidence j t).card ≤ cap t := by
    rw [filter_insert]
    by_cases ht : incidence i t
    · rw [if_pos ht, card_insert_of_notMem (fun h => hiG (mem_filter.mp h).1)]
      exact Nat.succ_le_iff.mpr (hunsaturated t ht)
    · rw [if_neg ht]
      exact hdegree t
  have hpow' : 2 ^ (insert i G).card ≤ Nat.card (generatedSubgroup f (insert i G)) := by
    rw [card_insert_of_notMem hiG, pow_succ]
    calc
      2 ^ G.card * 2 ≤ 2 * Nat.card (generatedSubgroup f G) := by omega
      _ ≤ _ := generatedSubgroup_card_insert f G i hi
  have hnew : insert i G ∈ candidates :=
    mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hiF (mem_powerset.mp hGF)), hdegrees, hpow'⟩
  have hcard := hmax (insert i G) hnew
  rw [card_insert_of_notMem hiG] at hcard
  omega

theorem exists_bounded_generating_subfamily (F : Finset I) (f : I → A)
    (incidence : I → T → Prop) [DecidableRel incidence] (cap : ℕ) :
    ∃ G : Finset I, G ⊆ F ∧
      (∀ t, (G.filter fun i => incidence i t).card ≤ cap) ∧
      2 ^ G.card ≤ Nat.card (generatedSubgroup f G) ∧
      G.card ≤ Nat.log 2 (Nat.card A) ∧
      ∀ i ∈ F, (∀ t, incidence i t → (G.filter fun j => incidence j t).card < cap) →
        f i ∈ generatedSubgroup f G :=
  exists_generating_subfamily_with_caps F f incidence (fun _ => cap)

end Arxiv2411_18291
