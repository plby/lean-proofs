/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZBoundedOverlapHistorySummation
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSingleDeletionAtom
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaCreationSlots

/-!
# Bounded overlap of one-base deletion atoms

At a fixed raised path, a pointed source history is determined by whether
the exposed base survived and by that base itself.  The latter ranges over
the represented external dominoes, so histories with a common retained-count
bound have overlap at most twice that bound plus two.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairSingleDeletionOverlap

open HLOZPathEvents
open HLOZPositiveInterfacePairSingleDeletionAtom
open HLOZPositiveInterfacePairSupportActualDeltaAtom
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfaceSupportSelector
open HLOZSourceOrientedThetaCreationSlots
open LazyDecomposition
open TilingLazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- An exact adjacent-pair history pointed at one represented coordinate. -/
abbrev PositiveInterfaceExternalPairPointedIndex
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :=
  Σ eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell,
    PositiveInterfaceExternalPairCoordinate eta

/-- The observable label of a pointed source at a raised path: whether the
full support survived, and the exposed domino base. -/
noncomputable def singleDeletionLabel
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ} (delta : ℕ) (s : WalkPath)
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell) : Bool × Point :=
  (if s ∈ positiveInterfaceExternalPairRankAtom t o m k externalThreshold
      width shell delta p.1 then true else false, p.2.1.1)

/-- The endpoint-normalized observable label used with the Proposition 4.4
candidate family. -/
noncomputable def singleDeletionEndpointLabel
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ} (delta : ℕ) (s : WalkPath)
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell) : Bool × Point :=
  (if s ∈ positiveInterfaceExternalPairRankAtom t o m k externalThreshold
      width shell delta p.1 then true else false,
    orientedDominoEndpoint t o p.2.1.1)

private theorem pointedIndex_ext
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    {p q : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell}
    (heta : p.1 = q.1) (hbase : p.2.1.1 = q.2.1.1) :
    p = q := by
  rcases p with ⟨eta, b⟩
  rcases q with ⟨eta', b'⟩
  dsimp only at heta hbase ⊢
  subst eta'
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact hbase

private theorem pointed_code_eq_of_mem_singleDeletionRankAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell delta : ℕ} {s : WalkPath}
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell)
    (hs : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta p.1 p.2) :
    p.1.1.1 = fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (k + delta) s) s := by
  rw [positiveInterfaceExternalPairSingleDeletionRankAtom,
    Set.mem_union] at hs
  rcases hs with hs | hs
  · rw [positiveInterfaceExternalPairRankAtom,
      orientedExternalAllCreationSupportTraceAtom_eq] at hs
    exact hs.2.2.1.symm
  · rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
    exact hs.2.2.1.symm

private theorem pointed_base_mem_code_of_mem_singleDeletionRankAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell delta : ℕ} {s : WalkPath}
    (p : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell)
    (hs : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta p.1 p.2) :
    p.2.1.1 ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m (k + delta) s) s).start
      (fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m (k + delta) s) s).retained := by
  have hcode := pointed_code_eq_of_mem_singleDeletionRankAtom p hs
  rw [← hcode]
  exact p.2.1.2

/-- Equal observable labels on a common deletion atom force equality of the
underlying pointed exact histories. -/
theorem pointedIndex_eq_of_mem_singleDeletionRankAtom_of_label_eq
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell delta : ℕ} {s : WalkPath}
    {p q : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell}
    (hp : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta p.1 p.2)
    (hq : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta q.1 q.2)
    (hlabel : singleDeletionLabel delta s p =
      singleDeletionLabel delta s q) :
    p = q := by
  classical
  have hcode : p.1.1.1 = q.1.1.1 :=
    (pointed_code_eq_of_mem_singleDeletionRankAtom p hp).trans
      (pointed_code_eq_of_mem_singleDeletionRankAtom q hq).symm
  have hbase : p.2.1.1 = q.2.1.1 :=
    congrArg Prod.snd hlabel
  have hbP : p.2.1.1 ∈ p.1.1.2 :=
    (away_mem_support_iff t p.1.1.1.start p.1.1.1.retained p.1.1.2
      p.2.1).1 p.2.2
  have hbQ : q.2.1.1 ∈ q.1.1.2 :=
    (away_mem_support_iff t q.1.1.1.start q.1.1.1.retained q.1.1.2
      q.2.1).1 q.2.2
  by_cases hpFull : s ∈ positiveInterfaceExternalPairRankAtom t o m k
      externalThreshold width shell delta p.1
  · have hqFull : s ∈ positiveInterfaceExternalPairRankAtom t o m k
        externalThreshold width shell delta q.1 := by
      by_contra hqNot
      have hbranch := congrArg Prod.fst hlabel
      simp only [singleDeletionLabel, if_pos hpFull, if_neg hqNot] at hbranch
      exact Bool.noConfusion hbranch
    rw [positiveInterfaceExternalPairRankAtom,
      orientedExternalAllCreationSupportTraceAtom_eq] at hpFull hqFull
    have hsupport : p.1.1.2 = q.1.1.2 :=
      hpFull.2.2.2.symm.trans hqFull.2.2.2
    have heta : p.1 = q.1 := by
      apply Subtype.ext
      exact Prod.ext hcode hsupport
    exact pointedIndex_ext heta hbase
  · have hqNotFull : ¬s ∈ positiveInterfaceExternalPairRankAtom t o m k
        externalThreshold width shell delta q.1 := by
      intro hqFull
      have hbranch := congrArg Prod.fst hlabel
      simp only [singleDeletionLabel, if_neg hpFull, if_pos hqFull] at hbranch
      exact Bool.noConfusion hbranch
    have hpDeleted : s ∈ orientedExternalAllCreationSupportTraceAtom t o m
        (k + delta)
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        p.1.1.1 (p.1.1.2.erase p.2.1.1) := by
      rw [positiveInterfaceExternalPairSingleDeletionRankAtom,
        Set.mem_union] at hp
      exact hp.resolve_left hpFull
    have hqDeleted : s ∈ orientedExternalAllCreationSupportTraceAtom t o m
        (k + delta)
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        q.1.1.1 (q.1.1.2.erase q.2.1.1) := by
      rw [positiveInterfaceExternalPairSingleDeletionRankAtom,
        Set.mem_union] at hq
      exact hq.resolve_left hqNotFull
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hpDeleted hqDeleted
    have herase : p.1.1.2.erase p.2.1.1 =
        q.1.1.2.erase p.2.1.1 := by
      have hraw := hpDeleted.2.2.2.symm.trans hqDeleted.2.2.2
      simpa only [hbase] using hraw
    have hsupport : p.1.1.2 = q.1.1.2 := by
      calc
        p.1.1.2 = insert p.2.1.1 (p.1.1.2.erase p.2.1.1) :=
          (Finset.insert_erase hbP).symm
        _ = insert p.2.1.1 (q.1.1.2.erase p.2.1.1) := by rw [herase]
        _ = q.1.1.2 := by
          rw [hbase]
          exact Finset.insert_erase hbQ
    have heta : p.1 = q.1 := by
      apply Subtype.ext
      exact Prod.ext hcode hsupport
    exact pointedIndex_ext heta hbase

/-- Endpoint normalization loses no information about the canonical tiling
base, so the endpoint label is also injective on a common deletion atom. -/
theorem pointedIndex_eq_of_mem_singleDeletionRankAtom_of_endpointLabel_eq
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell delta : ℕ} {s : WalkPath}
    {p q : PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell}
    (hp : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta p.1 p.2)
    (hq : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta q.1 q.2)
    (hlabel : singleDeletionEndpointLabel delta s p =
      singleDeletionEndpointLabel delta s q) :
    p = q := by
  have hbase : p.2.1.1 = q.2.1.1 := by
    have hendpoint : orientedDominoEndpoint t o p.2.1.1 =
        orientedDominoEndpoint t o q.2.1.1 := by
      simpa only [singleDeletionEndpointLabel] using congrArg Prod.snd hlabel
    have hpBaseEq : tilingBase t p.2.1.1 = p.2.1.1 :=
      tilingExternalDomino_is_base t _ _ p.2.1
    have hqBaseEq : tilingBase t q.2.1.1 = q.2.1.1 :=
      tilingExternalDomino_is_base t _ _ q.2.1
    have hpBase : IsTilingBase t p.2.1.1 :=
      isTilingBase_of_tilingBase_eq_self t p.2.1.1 hpBaseEq
    have hqBase : IsTilingBase t q.2.1.1 :=
      isTilingBase_of_tilingBase_eq_self t q.2.1.1 hqBaseEq
    calc
      p.2.1.1 = tilingBase t (orientedDominoEndpoint t o p.2.1.1) :=
        (tilingBase_orientedDominoEndpoint t o p.2.1.1 hpBase).symm
      _ = tilingBase t (orientedDominoEndpoint t o q.2.1.1) := by rw [hendpoint]
      _ = q.2.1.1 :=
        tilingBase_orientedDominoEndpoint t o q.2.1.1 hqBase
  have hraw : singleDeletionLabel delta s p =
      singleDeletionLabel delta s q := by
    apply Prod.ext
    · simpa only [singleDeletionEndpointLabel, singleDeletionLabel] using
        congrArg Prod.fst hlabel
    · exact hbase
  exact pointedIndex_eq_of_mem_singleDeletionRankAtom_of_label_eq hp hq hraw

/-- A family of pointed source histories with retained-count at most `R`
has pointwise overlap at most `2 * (R + 1)` after one-base deletion. -/
theorem singleDeletionRankAtom_fiber_encard_le
    {History : Type*}
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (index : History → PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell)
    (hindex : Function.Injective index) (R : ℕ)
    (hretained : ∀ h, (index h).1.1.1.retainedCount ≤ R)
    (delta : ℕ) (s : WalkPath) :
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard ≤
        (2 * (R + 1) : ℕ) := by
  classical
  let fiber : Set History :=
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}
  let z := fixedOrientedTypedExternalWordCode t o
    (creationTimeNat m (k + delta) s) s
  let target : Set (Bool × Point) :=
    Set.univ ×ˢ (tilingExternalDominoBases t z.start z.retained : Set Point)
  by_cases hempty : fiber = ∅
  · simp only [fiber] at hempty ⊢
    rw [hempty, Set.encard_empty]
    exact bot_le
  obtain ⟨h0, hh0⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have hh0' : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom
      t o m k externalThreshold width shell delta
      (index h0).1 (index h0).2 := hh0
  have hcode := pointed_code_eq_of_mem_singleDeletionRankAtom (index h0) hh0'
  have hzRetained : z.retainedCount ≤ R := by
    change (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (k + delta) s) s).retainedCount ≤ R
    rw [← hcode]
    exact hretained h0
  have hbaseCard : (tilingExternalDominoBases t z.start z.retained).card ≤
      R + 1 := by
    calc
      (tilingExternalDominoBases t z.start z.retained).card ≤
          (Finset.univ : Finset (Fin (z.retainedCount + 1))).card := by
        exact Finset.card_image_le
      _ = z.retainedCount + 1 := by simp
      _ ≤ R + 1 := Nat.add_le_add_right hzRetained 1
  have hmaps : Set.MapsTo (fun h => singleDeletionLabel delta s (index h))
      fiber target := by
    intro h hh
    refine ⟨Set.mem_univ _, ?_⟩
    exact pointed_base_mem_code_of_mem_singleDeletionRankAtom (index h) hh
  have hinj : Set.InjOn (fun h => singleDeletionLabel delta s (index h))
      fiber := by
    intro h hh h' hh' heq
    apply hindex
    exact pointedIndex_eq_of_mem_singleDeletionRankAtom_of_label_eq hh hh' heq
  calc
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard =
        fiber.encard := rfl
    _ ≤ target.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = (2 : ℕ∞) *
        ((tilingExternalDominoBases t z.start z.retained).card : ℕ∞) := by
      simp only [target, Set.encard_prod, Set.encard_univ,
        Set.encard_coe_eq_coe_finsetCard]
      norm_num
    _ ≤ (2 * (R + 1) : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hbaseCard

/-- If every pointed base belongs to a code-local candidate family of size at
most `B`, then the one-deletion history overlap is at most `2 * B`.  The
candidate family is evaluated at the retained creation word, so membership
and its cardinal bound are preserved when the common raised atom identifies
the external word code. -/
theorem singleDeletionRankAtom_candidate_fiber_encard_le
    {History : Type*}
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (index : History → PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell)
    (hindex : Function.Injective index) (B : ℕ)
    (hcandidate : ∀ h,
      (index h).2.1.1 ∈ orientedThetaCodeCandidateSites44 t o m
        (index h).1.1.1)
    (hcard : ∀ h,
      (orientedThetaCodeCandidateSites44 t o m (index h).1.1.1).card ≤ B)
    (delta : ℕ) (s : WalkPath) :
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard ≤
        (2 * B : ℕ) := by
  classical
  let fiber : Set History :=
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}
  let z := fixedOrientedTypedExternalWordCode t o
    (creationTimeNat m (k + delta) s) s
  let target : Set (Bool × Point) :=
    Set.univ ×ˢ (orientedThetaCodeCandidateSites44 t o m z : Set Point)
  by_cases hempty : fiber = ∅
  · simp only [fiber] at hempty ⊢
    rw [hempty, Set.encard_empty]
    exact bot_le
  obtain ⟨h0, hh0⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have hh0' : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom
      t o m k externalThreshold width shell delta
      (index h0).1 (index h0).2 := hh0
  have hcode := pointed_code_eq_of_mem_singleDeletionRankAtom (index h0) hh0'
  have hcandidateCard :
      (orientedThetaCodeCandidateSites44 t o m z).card ≤ B := by
    simpa only [z, ← hcode] using hcard h0
  have hmaps : Set.MapsTo (fun h => singleDeletionLabel delta s (index h))
      fiber target := by
    intro h hh
    refine ⟨Set.mem_univ _, ?_⟩
    have hcand := hcandidate h
    have hcodeh :=
      pointed_code_eq_of_mem_singleDeletionRankAtom (index h) hh
    change (index h).2.1.1 ∈ orientedThetaCodeCandidateSites44 t o m z
    simpa only [z, ← hcodeh] using hcand
  have hinj : Set.InjOn (fun h => singleDeletionLabel delta s (index h))
      fiber := by
    intro h hh h' hh' heq
    apply hindex
    exact pointedIndex_eq_of_mem_singleDeletionRankAtom_of_label_eq hh hh' heq
  calc
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard =
        fiber.encard := rfl
    _ ≤ target.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = (2 : ℕ∞) *
        ((orientedThetaCodeCandidateSites44 t o m z).card : ℕ∞) := by
      simp only [target, Set.encard_prod, Set.encard_univ,
        Set.encard_coe_eq_coe_finsetCard]
      norm_num
    _ ≤ (2 * B : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hcandidateCard

/-- Endpoint-normalized version of the candidate-family overlap bound. -/
theorem singleDeletionRankAtom_endpointCandidate_fiber_encard_le
    {History : Type*}
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (index : History → PositiveInterfaceExternalPairPointedIndex t o m k
      externalThreshold width shell)
    (hindex : Function.Injective index) (B : ℕ)
    (hcandidate : ∀ h,
      orientedDominoEndpoint t o (index h).2.1.1 ∈
        orientedThetaCodeEndpointCandidateSites44 t o m (index h).1.1.1)
    (hcard : ∀ h,
      (orientedThetaCodeEndpointCandidateSites44 t o m
        (index h).1.1.1).card ≤ B)
    (delta : ℕ) (s : WalkPath) :
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard ≤
        (2 * B : ℕ) := by
  classical
  let fiber : Set History :=
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}
  let z := fixedOrientedTypedExternalWordCode t o
    (creationTimeNat m (k + delta) s) s
  let target : Set (Bool × Point) := Set.univ ×ˢ
    (orientedThetaCodeEndpointCandidateSites44 t o m z : Set Point)
  by_cases hempty : fiber = ∅
  · simp only [fiber] at hempty ⊢
    rw [hempty, Set.encard_empty]
    exact bot_le
  obtain ⟨h0, hh0⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have hh0' : s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom
      t o m k externalThreshold width shell delta
      (index h0).1 (index h0).2 := hh0
  have hcode := pointed_code_eq_of_mem_singleDeletionRankAtom (index h0) hh0'
  have hcandidateCard :
      (orientedThetaCodeEndpointCandidateSites44 t o m z).card ≤ B := by
    simpa only [z, ← hcode] using hcard h0
  have hmaps : Set.MapsTo
      (fun h => singleDeletionEndpointLabel delta s (index h)) fiber target := by
    intro h hh
    refine ⟨Set.mem_univ _, ?_⟩
    have hcand := hcandidate h
    have hcodeh :=
      pointed_code_eq_of_mem_singleDeletionRankAtom (index h) hh
    change orientedDominoEndpoint t o (index h).2.1.1 ∈
      orientedThetaCodeEndpointCandidateSites44 t o m z
    simpa only [z, ← hcodeh] using hcand
  have hinj : Set.InjOn
      (fun h => singleDeletionEndpointLabel delta s (index h)) fiber := by
    intro h hh h' hh' heq
    apply hindex
    exact pointedIndex_eq_of_mem_singleDeletionRankAtom_of_endpointLabel_eq
      hh hh' heq
  calc
    {h | s ∈ positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta (index h).1 (index h).2}.encard =
        fiber.encard := rfl
    _ ≤ target.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = (2 : ℕ∞) *
        ((orientedThetaCodeEndpointCandidateSites44 t o m z).card : ℕ∞) := by
      simp only [target, Set.encard_prod, Set.encard_univ,
        Set.encard_coe_eq_coe_finsetCard]
      norm_num
    _ ≤ (2 * B : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hcandidateCard

end

end Erdos1165.HLOZPositiveInterfacePairSingleDeletionOverlap
