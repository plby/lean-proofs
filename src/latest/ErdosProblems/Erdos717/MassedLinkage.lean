/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Completion of the eight-massed Thomas--Wollan linkage theorem. -/

import ErdosProblems.Erdos717.DenseNeighborhood
import ErdosProblems.Erdos717.EmbeddedLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed
namespace MassedCounterexample

variable {k : ℕ}

/-- Attach the distinguished set to a `k`-linked embedded subgraph.  A
minimum failed attachment cut would itself be a forbidden rigid
separation. -/
theorem isLinkedSet_of_kLinkedSubgraph_of_noSmallRigid
    (C : MassedCounterexample k) (J : ThomasWollan.KLinkedSubgraph C.G k)
    (hnoRigid : C.HasNoSmallRigidSeparation) :
    Erdos718.IsLinkedSet C.G (C.X : Set C.V) := by
  classical
  let A : Set C.V := (C.X : Set C.V)
  let B : Set C.V := Set.range J.inclusion
  have hBlinked : Erdos718.IsKLinked (C.G.induce B) k :=
    isKLinked_induce_range_of_embedding J.inclusion J.linked
  obtain ⟨P₀, T, hP₀, hTcover, hcard, _hmax, hTmin⟩ :=
    Erdos718.finite_pathHypergraph_minmax C.G A B
  have hTsep : Erdos599.Separates C.G A B T :=
    Erdos599.isCover_pathHypergraph_iff.mp hTcover
  by_cases hlarge : C.X.card ≤ T.ncard
  · have hall : ∀ U, Erdos599.Separates C.G A B U →
        C.X.card ≤ U.ncard := by
      intro U hUsep
      exact hlarge.trans (hTmin U
        (Erdos599.isCover_pathHypergraph_iff.mpr hUsep))
    obtain ⟨P⟩ := Erdos718.exists_abLinkage_of_forall_separator_ncard_ge
      C.G A B C.X.card hall
    have P' : Erdos718.ABLinkage C.G A B A.ncard := by
      simpa only [A, Set.ncard_coe_finset] using P
    exact isLinkedSet_of_full_abLinkage_to_kLinked_target
      C.X.finite_toSet (by simpa only [A, Set.ncard_coe_finset] using C.card_le)
      P' hBlinked
  · have hTsmall : T.ncard < C.X.card := Nat.lt_of_not_ge hlarge
    obtain ⟨t, hAtLeft, hBtRight, htCard⟩ :=
      exists_separation_of_path_separator_with_sides hTsep
    have htSmall : t.separator.card < C.X.card := htCard.trans_lt hTsmall
    let Y : Set (t.right : Set C.V) :=
      (rightSeparator t : Set (t.right : Set C.V))
    let D : Set (t.right : Set C.V) := {x | (x : C.V) ∈ B}
    let K := C.G.induce (t.right : Set C.V)
    have hcutLower : ∀ U, Erdos599.Separates K Y D U →
        t.separator.card ≤ U.ncard := by
      intro U hUsep
      obtain ⟨u, hYuLeft, hDuRight, huCard⟩ :=
        exists_separation_of_path_separator_with_sides hUsep
      have hYfin : rightSeparator t ⊆ u.left := by
        intro x hx
        exact hYuLeft hx
      let q := composeRight t u hYfin
      have hAq : A ⊆ (q.left : Set C.V) := by
        intro a ha
        have haT : a ∈ t.left := hAtLeft ha
        by_cases haR : a ∈ t.right
        · let aR : (t.right : Set C.V) := ⟨a, haR⟩
          have haY : aR ∈ rightSeparator t := by
            rw [mem_rightSeparator]
            exact Finset.mem_inter.mpr ⟨haT, haR⟩
          exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_map.mpr ⟨aR, hYfin haY, rfl⟩))
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_sdiff.mpr ⟨haT, haR⟩))
      have hBq : B ⊆ (q.right : Set C.V) := by
        intro b hb
        have hbR : b ∈ t.right := hBtRight hb
        let bR : (t.right : Set C.V) := ⟨b, hbR⟩
        have hbD : bR ∈ D := hb
        exact Finset.mem_map.mpr ⟨bR, hDuRight hbD, rfl⟩
      have hqSep : Erdos599.Separates C.G A B
          (q.separator : Set C.V) :=
        separation_separator_separates_of_subsets q hAq hBq
      have hmin := hTmin (q.separator : Set C.V)
        (Erdos599.isCover_pathHypergraph_iff.mpr hqSep)
      rw [Set.ncard_coe_finset, composeRight_separator_card,
        huCard] at hmin
      rw [htCard]
      exact hmin
    obtain ⟨P⟩ := Erdos718.exists_abLinkage_of_forall_separator_ncard_ge
      K Y D t.separator.card hcutLower
    let fD : C.G.induce B ↪g K := {
      toFun := fun x => ⟨(x : C.V), hBtRight x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        change (x : C.V) = (y : C.V)
        exact congrArg (fun z : (t.right : Set C.V) => (z : C.V)) h
      map_rel_iff' := by
        intro x y
        rfl
    }
    have hfDRange : Set.range fD = D := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact z.property
      · intro hx
        let z : B := ⟨(x : C.V), hx⟩
        refine ⟨z, Subtype.ext rfl⟩
    have hDlinked : Erdos718.IsKLinked (K.induce D) k := by
      have h := isKLinked_induce_range_of_embedding fD hBlinked
      rw [hfDRange] at h
      exact h
    have hYcard : Y.ncard = t.separator.card := by
      simp only [Y, Set.ncard_coe_finset, rightSeparator_card]
    let P' : Erdos718.ABLinkage K Y D Y.ncard := by
      rw [hYcard]
      exact P
    have hYbound : Y.ncard ≤ 2 * k := by
      rw [hYcard]
      exact htSmall.le.trans C.card_le
    have hYlinked : Erdos718.IsLinkedSet K Y :=
      isLinkedSet_of_full_abLinkage_to_kLinked_target
        (Set.toFinite Y) hYbound P' hDlinked
    have htLinked : Erdos718.IsLinkedSet K
        (rightSeparator t : Set (t.right : Set C.V)) := by
      exact hYlinked
    have hBcard : 2 * k ≤ B.ncard := by
      change 2 * k ≤ (Set.range J.inclusion).ncard
      rw [Set.ncard_range_of_injective J.inclusion.injective]
      simpa only [Nat.card_eq_fintype_card] using J.enough_vertices
    have htStrictRight : (t.right \ t.left).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hBsep : B ⊆ (t.separator : Set C.V) := by
        intro b hb
        have hbR := hBtRight hb
        have hbL : b ∈ t.left := by
          by_contra hbL
          have : b ∈ t.right \ t.left :=
            Finset.mem_sdiff.mpr ⟨hbR, hbL⟩
          simpa [hempty] using this
        exact Finset.mem_inter.mpr ⟨hbL, hbR⟩
      have hcards := Set.ncard_le_ncard hBsep
      rw [Set.ncard_coe_finset] at hcards
      have hXbound := C.card_le
      omega
    have htRigid : C.IsRigidSeparation t :=
      ⟨by
        intro x hx
        exact hAtLeft hx,
        htStrictRight, htLinked⟩
    have hlargeOrder := hnoRigid t htRigid
    omega

/-- Thomas--Wollan's eight-massed linkage theorem in the exact finite form
needed by the density argument. -/
theorem isLinkedSet_of_isEightKMassed
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (hcard : X.card ≤ 2 * k) (hmassed : IsEightKMassed G X k) :
    Erdos718.IsLinkedSet G (X : Set V) := by
  by_contra hnot
  let C₀ : MassedCounterexample k := {
    V := V
    fintypeV := inferInstance
    decEqV := inferInstance
    G := G
    decAdj := inferInstance
    X := X
    card_le := hcard
    massed := hmassed
    not_linked := hnot
  }
  obtain ⟨C, hlex⟩ := exists_lexMinimal (k := k) ⟨C₀⟩
  obtain ⟨F⟩ := C.exists_failedPairing
  have hnoRigid := hasNoSmallRigidSeparation_of_lexMinimal C hlex
  have hcond := C.contractConditionTwo_of_noSmallRigidSeparation hlex hnoRigid
  have hnoiso := C.noIsolatedOutside_of_lexMinimal hlex
  obtain ⟨J⟩ := C.exists_kLinkedSubgraph_of_contractConditionTwo
    hk hlex F hcond hnoiso
  exact C.not_linked
    (C.isLinkedSet_of_kLinkedSubgraph_of_noSmallRigid J hnoRigid)

end MassedCounterexample
end ThomasWollanMassed
end Erdos717
