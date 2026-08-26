import ErdosProblems.Erdos117.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Reduction through the centralizer of the derived subgroup

The subgroup is normal and has nilpotency class at most two. Its index is
controlled by automorphisms of the derived subgroup; the latter are determined
by the images of a small generating set.
-/

namespace Erdos117

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The derived subgroup of `C_G(G')` lies in its center. -/
theorem commutator_centralizer_derived_le_center :
    commutator (Subgroup.centralizer (commutator G : Set G)) ≤
      Subgroup.center (Subgroup.centralizer (commutator G : Set G)) := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  change (z : G) * ⁅(x : G), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * (z : G)
  exact (z.2 _ (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))).symm

theorem nilpotent_centralizer_derived :
    Group.IsNilpotent (Subgroup.centralizer (commutator G : Set G)) := by
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨2, ?_⟩
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
    Subgroup.commutator_top_right_eq_bot_iff_le_center]
  exact commutator_centralizer_derived_le_center

/-- A greedy generating sequence doubles the generated subgroup at each step. -/
theorem exists_generating_extension [Finite G] (H : Subgroup G) :
    ∃ s : Finset G, H ⊔ Subgroup.closure (s : Set G) = ⊤ ∧ 2 ^ s.card ≤ H.index := by
  classical
  induction H using WellFoundedGT.induction with
  | ind H ih =>
    by_cases hH : H = ⊤
    · exact ⟨∅, by simp [hH], by simp [hH]⟩
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
    let K := H ⊔ Subgroup.closure ({x} : Set G)
    have hxK : x ∈ K := (le_sup_right : Subgroup.closure ({x} : Set G) ≤ K)
      (Subgroup.subset_closure (Set.mem_singleton x))
    have hHK : H < K := lt_of_le_of_ne le_sup_left (fun h => hx.2 (h ▸ hxK))
    obtain ⟨s, hs, hcard⟩ := ih K hHK
    refine ⟨insert x s, ?_, ?_⟩
    · simpa only [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, sup_assoc, K] using hs
    · have hrelpos : 0 < H.relIndex K := Nat.pos_of_ne_zero
        (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf K))
      have hrelne : H.relIndex K ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        exact not_le_of_gt hHK
      have hrel : 2 ≤ H.relIndex K := by omega
      calc
        2 ^ (insert x s).card ≤ 2 ^ (s.card + 1) :=
          Nat.pow_le_pow_right (by decide) (Finset.card_insert_le _ _)
        _ = 2 * 2 ^ s.card := by rw [pow_succ, Nat.mul_comm]
        _ ≤ H.relIndex K * K.index := Nat.mul_le_mul hrel hcard
        _ = H.index := Subgroup.relIndex_mul_index hHK.le

/-- Every finite group has a generating set with at most `log₂ |G|` elements,
stated without real logarithms. -/
theorem exists_small_generating_set [Finite G] :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧ 2 ^ s.card ≤ Nat.card G := by
  simpa using exists_generating_extension (⊥ : Subgroup G)

/-- An automorphism is determined by its values on a generating set. -/
theorem card_mulAut_le_pow_generating_set [Finite G] {s : Finset G}
    (hs : Subgroup.closure (s : Set G) = ⊤) :
    Nat.card (MulAut G) ≤ Nat.card G ^ s.card := by
  let f : MulAut G → s → G := fun e x => e x
  have hf : Function.Injective f := by
    intro e e' h
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense hs
    intro x hx
    exact congrFun h ⟨x, hx⟩
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective f hf

theorem ker_conjNormal (N : Subgroup G) [N.Normal] :
    (MulAut.conjNormal : G →* MulAut N).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  change (MulAut.conjNormal g : MulAut N) = 1 ↔ ∀ x ∈ N, x * g = g * x
  constructor
  · intro h x hx
    have heq := congrArg (fun e : MulAut N => (e ⟨x, hx⟩ : G)) h
    change g * x * g⁻¹ = x at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  · intro h
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = (x : G)
    exact (show Commute g (x : G) from (h x x.2).symm).mul_inv_cancel

/-- Conjugation embeds the quotient by the centralizer into the automorphism
group of a finite normal subgroup. -/
theorem centralizerIndex_le_card_mulAut (N : Subgroup G) [N.Normal] [Finite N] :
    (Subgroup.centralizer (N : Set G)).index ≤ Nat.card (MulAut N) := by
  rw [← ker_conjNormal, Subgroup.index_ker]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The logarithmic form is `log₂ [G:C_G(N)] ≤ (log₂ |N|)^2`.
This discrete estimate does not assume a bound on the order of `N`. -/
theorem centralizerIndex_le_small_power (N : Subgroup G) [N.Normal] [Finite N] :
    ∃ d : ℕ, 2 ^ d ≤ Nat.card N ∧
      (Subgroup.centralizer (N : Set G)).index ≤ Nat.card N ^ d := by
  obtain ⟨s, hs, hcard⟩ := exists_small_generating_set (G := N)
  exact ⟨s.card, hcard, (centralizerIndex_le_card_mulAut N).trans
    (card_mulAut_le_pow_generating_set hs)⟩

/-- A ceiling-logarithm form of the automorphism bound. -/
theorem centralizerIndex_le_two_pow_clog_sq (N : Subgroup G) [N.Normal] [Finite N] :
    (Subgroup.centralizer (N : Set G)).index ≤ 2 ^ ((Nat.clog 2 (Nat.card N)) ^ 2) := by
  obtain ⟨d, hd, hindex⟩ := centralizerIndex_le_small_power N
  have hcard := Nat.le_pow_clog (by decide : 1 < 2) (Nat.card N)
  have hdq : d ≤ Nat.clog 2 (Nat.card N) :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hd.trans hcard)
  calc
    _ ≤ Nat.card N ^ d := hindex
    _ ≤ (2 ^ Nat.clog 2 (Nat.card N)) ^ d := Nat.pow_le_pow_left hcard d
    _ = 2 ^ (Nat.clog 2 (Nat.card N) * d) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide)
      (by simpa only [pow_two] using Nat.mul_le_mul_left (Nat.clog 2 (Nat.card N)) hdq)

end Erdos117
