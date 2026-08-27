/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedPairSourceTail
import ErdosProblems.Erdos207.SelectedCountCover

/-! # Pair-threat tails for the entire finite union of fixed source orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedPair_selectedCount_le_sigma_source
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell : ℕ}
    (W : Vortex V ell) (F : I → ForbiddenFamilyOn V) (order : I → ℕ)
    (J : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V)
    (available old selected : TripleSystemOn V) (e : Sym2 V)
    (he : ¬ e.IsDiag) (heP : e.toFinset = P.1)
    (huniform : ∀ i E, E ∈ F i → E.card = order i - 2)
    (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hdis : Disjoint available old)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old) :
    selectedCount (fun u : PairTwoAwayThreatWitness V J T P ↦ pairTwoAwayThreatRemainder u) selected ≤
      selectedCount (fun u : Σ i, sourcePinnedEdgeCodes W (F i) T (order i) e ↦ u.2.1.2)
        (old ∪ selected) := by
  classical
  let decode := fun u : Σ i, sourcePinnedEdgeCodes W (F i) T (order i) e ↦
    (u.2.1.1 \ old, sourceNibbleRemaining T u.2.1)
  let encode := fun u : PairTwoAwayThreatWitness V J T P ↦
    (u.1.1.1, ({u.1.1.2} : TripleSystemOn V))
  have hinj : Function.Injective encode := by
    intro u v huv
    have hc := congrArg (fun x : TripleSystemOn V × TripleSystemOn V ↦ x.1) huv
    have hu := congrArg (fun x : TripleSystemOn V × TripleSystemOn V ↦ x.2) huv
    exact Subtype.ext (Subtype.ext (Prod.ext hc (singleton_injective hu)))
  apply selectedCount_le_of_decoded_cover _ _ encode decode selected (old ∪ selected) hinj
  intro u hu
  obtain ⟨hCA, i, E, hE, hCE, hOld⟩ := hJ u.1.1.1 u.1.2.1
  have hU := u.1.2.2.1
  have hT := u.1.2.2.2.1
  have hne := u.1.2.2.2.2
  have hpair : e ∈ tripleEdgeFinset u.1.1.2 := by
    apply (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e u.1.1.2 he).mpr
    rw [heP]
    exact u.2.1
  have hcode := localizedPair_source_code W (F i) T u.1.1.2 E e hE (huniform i E hE)
    (hCE hT) (hCE hU) hne (hterm _ (hCA hU)) hpair
  refine ⟨⟨i, ⟨(E, (E.erase u.1.1.2).erase T), hcode⟩⟩, ?_, ?_⟩
  · intro R hR
    have hm := mem_erase.mp hR
    have hm' := mem_erase.mp hm.2
    by_cases hRC : R ∈ u.1.1.1
    · exact mem_union_right _ (hu (mem_erase.mpr ⟨hm.1, mem_erase.mpr ⟨hm'.1, hRC⟩⟩))
    · exact mem_union_left _ (hOld (mem_sdiff.mpr ⟨hm'.2, hRC⟩))
  · exact Prod.ext (localization_eq_sdiff_old hdis hCA hCE hOld)
      (sourceNibbleRemaining_erase_two E T u.1.1.2 (hCE hU) hne)

theorem localizedPair_source_orders_tail_additive
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q s : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (T : TripleOn V) (P : PairOn V)
    (w : ℝ≥0) (hw : 1 ≤ w) (L : FiniteLaw Ω) (J : Ω → ForbiddenFamilyOn V)
    (available old selected : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧ Disjoint (available x) (old x) ∧
      ∀ C ∈ J x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (q - 4) →
      L.probability (fun x ↦ H ⊆ old x ∪ selected x) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    let kappa := ∑ i, sourceNibbleMomentCoefficient ell (order i) w * z i
    let countBound := ∑ i, (2 : ℝ≥0) ^ order i * (Fintype.card V + 1 : ℝ≥0) ^ (3 * order i)
    L.probability (fun x ↦ K ≤ selectedCount
      (fun u : PairTwoAwayThreatWitness V (J x) T P ↦ pairTwoAwayThreatRemainder u) (selected x)) ≤
      A * (((boundedIntersectionMomentCoefficient (q - 4) s : ℝ≥0) * kappa) / K) ^ s +
        epsilon * (countBound / K) ^ s := by
  classical
  dsimp only
  obtain ⟨e, he, heP⟩ := pairOn_exists_nondiagonal_edge P
  let rem := fun u : Σ i, sourcePinnedEdgeCodes W (F i) T (order i) e ↦ u.2.1.2
  let chosen := fun x ↦ old x ∪ selected x
  let X := fun x ↦ selectedCount
    (fun u : PairTwoAwayThreatWitness V (J x) T P ↦ pairTwoAwayThreatRemainder u) (selected x)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (chosen x)) := by
    intro x hx
    have hs := hstate x hx
    exact localizedPair_selectedCount_le_sigma_source W F order (J x) T P
      (available x) (old x) (selected x) e he heP (fun i E hE ↦ ((hF i).uniform E hE).1)
      hs.1 hs.2.1 hs.2.2
  have hcard : ∀ u, (rem u).card ≤ q - 4 := by
    intro u
    exact ((sourceNibbleCode_data (mem_filter.mp u.2.2).1).2.2.2.1.le).trans
      (Nat.sub_le_sub_right (horder u.1) 4)
  have hkappa := hasExtensionBound_sigma_sum
    (fun i (u : sourcePinnedEdgeCodes W (F i) T (order i) e) ↦ u.1.2)
    (vortexTripleWeight W w) (fun i ↦ sourceNibbleMomentCoefficient ell (order i) w * z i)
    (fun i ↦ (hF i).pinned_edge_hasExtensionBound T e w hw)
  apply (dominatedConfigurationTailBound_additive L rem chosen X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard hkappa hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  rw [Fintype.card_sigma, Nat.cast_sum]
  apply sum_le_sum
  intro i _hi
  rw [Fintype.card_coe]
  exact_mod_cast card_sourcePinnedEdgeCodes_le_polynomial W (F i) T (order i) e
    (fun E hE ↦ ((hF i).uniform E hE).1)

end

end Erdos207
