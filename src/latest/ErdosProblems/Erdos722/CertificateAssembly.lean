import ErdosProblems.Erdos722.Core
import ErdosProblems.Erdos722.Assembly
import ErdosProblems.Erdos722.RotationAbundance

namespace Erdos722

open Finset
open Erdos722.RootedEmbedding
open Erdos722.ExchangePattern
open Erdos722.SpecialCliqueCandidates

noncomputable section

theorem hasExchangeFocusing_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (hchoiceE : ∀ request : RootRequest
        (ExchangeEmbedding.fullExchangeData hrk).v n
        (ExchangeEmbedding.fullExchangeData hrk).pattern.root,
      ∃ t : Fin bankCount,
        ∃ phi : Fin (ExchangeEmbedding.fullExchangeData hrk).v ↪ Fin n,
          ExtendsRequest
              (ExchangeEmbedding.fullExchangeData hrk).pattern.root request phi ∧
          ∀ i, Erdos722.Rotations.rotateEdge (choiceE t i).symm
              (mapEdge phi
                (((ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges
                  ).equivFin.symm i).1) ∈ D.Kstar) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let host := (Finset.univ : Finset Base).biUnion fun c ↦
      Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
    HasExchangeFocusing n k r E (almostSupportedBlocks n k r host) := by
  dsimp only
  apply hasExchangeFocusing_almostSupported
  intro Q hQ
  have hQcard : Q.card = k := mem_completeUniform.mp hQ
  have : Nonempty (Fin n) := by
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨hQne.choose⟩
  obtain ⟨request, hrequest⟩ :=
    CoverClique.exists_rootRequest_with_image
      (ExchangeEmbedding.fullExchangeData hrk).pattern.root Q
      ((ExchangeEmbedding.fullExchangeData hrk).root_card.trans hQcard.symm)
  obtain ⟨t, phi, hextends, hfree⟩ := hchoiceE request
  refine ⟨phi,
    (mapEdge_root_eq_requestImage_of_extends _ request phi hextends).trans
      hrequest, ?_⟩
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
  let i : Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card :=
    (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.equivFin ⟨a, ha⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨exchangeBaseCoord t i, Finset.mem_univ _, ?_⟩
  apply Erdos722.Rotations.mem_rotateFamily.mpr
  simpa [focusingBasePerm, exchangeBaseCoord, i] using hfree i

theorem auxiliaryFocusing_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (hchoiceA : ∀ request : RootRequest k n (CoverClique.coverRoot k r),
      ∀ J : Finset (Fin n), J.card ≤ 2 * k →
        ∃ (t : Fin bankCount) (phi : Fin k ↪ Fin n),
          phi ∈ Erdos722.RotationAbundance.successfulRootedEmbeddings
            (CoverClique.coverRoot k r) request D.Kstar
            (fun i ↦ ((CoverClique.coverPattern k r).freeEdges.equivFin.symm i).1)
            (choiceA t) ∧
          ¬ OutsideRootTouches (CoverClique.coverRoot k r) J phi) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let host := (Finset.univ : Finset Base).biUnion fun c ↦
      Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
    ∀ g ∈ completeUniform n r,
      ∀ forbiddenVertices : Finset (Fin n), g ⊆ forbiddenVertices →
        forbiddenVertices.card ≤ 2 * k →
        ∃ Q ∈ blockCandidates n k,
          Q.powersetCard r \ {g} ⊆ host ∧ Q ∩ forbiddenVertices = g := by
  dsimp only
  intro g hg forbidden hgf hforbidden
  have hgcard : g.card = r := mem_completeUniform.mp hg
  have hgNonempty : g.Nonempty := Finset.card_pos.mp (by omega)
  let : Nonempty (Fin n) := ⟨hgNonempty.choose⟩
  obtain ⟨request, hrequest⟩ :=
    CoverClique.exists_rootRequest_with_image (CoverClique.coverRoot k r) g
      (by rw [CoverClique.card_coverRoot hrk.le, hgcard])
  obtain ⟨t, phi, hphi, havoid⟩ := hchoiceA request forbidden hforbidden
  have hphiData := Finset.mem_filter.mp hphi
  have hextends := mem_rootedEmbeddings.mp hphiData.1
  have hsuccess := Erdos722.Rotations.mem_rootedRotationSuccess.mp hphiData.2
  let Q := mapEdge phi Finset.univ
  have hQcard : Q.card = k := by simp [Q, mapEdge]
  have hrootMap : mapEdge phi (CoverClique.coverRoot k r) = g :=
    (mapEdge_root_eq_requestImage_of_extends _ request phi hextends).trans
      hrequest
  refine ⟨Q, mem_completeUniform.mpr hQcard, ?_, ?_⟩
  · have hfreeEq := CoverClique.imageFreeEdges_coverPattern_eq_spill
      hrk.le request g Q phi hextends hrequest (by simp [Q, mapEdge])
    have hfreeEq' : imageFreeEdges (CoverClique.coverPattern k r) phi =
        Q.powersetCard r \ {g} := by
      simpa [Reserve.cliqueEdges] using hfreeEq
    rw [← hfreeEq']
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    let i : Fin (CoverClique.coverPattern k r).freeEdges.card :=
      (CoverClique.coverPattern k r).freeEdges.equivFin ⟨a₀, ha₀⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨auxiliaryBaseCoord t i, Finset.mem_univ _, ?_⟩
    apply Erdos722.Rotations.mem_rotateFamily.mpr
    simpa [focusingBasePerm, auxiliaryBaseCoord, i] using hsuccess i
  · apply Finset.Subset.antisymm
    · intro y hy
      have hyQ := (Finset.mem_inter.mp hy).1
      have hyForbidden := (Finset.mem_inter.mp hy).2
      obtain ⟨x, _hx, hxy⟩ := Finset.mem_map.mp hyQ
      by_cases hxRoot : x ∈ CoverClique.coverRoot k r
      · rw [← hrootMap]
        exact Finset.mem_map.mpr ⟨x, hxRoot, hxy⟩
      · exfalso
        apply havoid
        refine ⟨x, ?_, ?_⟩
        · simpa [outsideRoot] using hxRoot
        · simpa [hxy] using hyForbidden
    · intro y hy
      apply Finset.mem_inter.mpr
      refine ⟨?_, hgf hy⟩
      rw [← hrootMap] at hy
      exact Finset.map_subset_map.mpr
        (Finset.subset_univ (CoverClique.coverRoot k r)) hy

theorem eliminationFocusing_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (hchoiceX : ∀ request : RootRequest
        (ExchangeEmbedding.fullExchangeData hrk).v n
        ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
          (ExchangeEmbedding.fullExchangeRootEdge hrk)).root,
      ∃ t : Fin bankCount,
        ∃ phi : Fin (ExchangeEmbedding.fullExchangeData hrk).v ↪ Fin n,
          ExtendsRequest
              ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
                (ExchangeEmbedding.fullExchangeRootEdge hrk)).root request phi ∧
          ∀ i, Erdos722.Rotations.rotateEdge (choiceX t i).symm
              (mapEdge phi
                ((((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
                  (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges
                  ).equivFin.symm i).1) ∈ D.Kstar) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern e₀).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let host := (Finset.univ : Finset Base).biUnion fun c ↦
      Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
    ∀ P : ExchangeEliminationEmbedding.EliminationPair n k r,
      ∃ psi : Fin E.v ↪ Fin n,
        mapEdge psi E.pattern.root = P.positive ∧
        mapEdge psi (E.special e₀) = P.negative ∧
        imageFreeEdges (E.eliminationPattern e₀) psi ⊆ host := by
  dsimp only
  intro P
  have hpositiveNonempty : P.positive.Nonempty :=
    Finset.card_pos.mp (P.positive_card.trans_gt (by omega))
  let : Nonempty (Fin n) := ⟨hpositiveNonempty.choose⟩
  obtain ⟨request, _hrequestRoot, hrequestPos, hrequestNeg⟩ :=
    ExchangeEliminationEmbedding.exists_eliminationRootRequest
      (ExchangeEmbedding.fullExchangeData hrk) (by omega) hrk
      (ExchangeEmbedding.fullExchangeRootEdge hrk) P
  obtain ⟨t, phi, hextends, hfree⟩ := hchoiceX request
  refine ⟨phi, ?_, ?_, ?_⟩
  · rw [ExchangeEliminationEmbedding.mapEdge_eq_requestImage_of_extends_of_subset
        (Finset.subset_union_left :
          (ExchangeEmbedding.fullExchangeData hrk).pattern.root ⊆
            ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
              (ExchangeEmbedding.fullExchangeRootEdge hrk)).root)
        request phi hextends]
    exact hrequestPos
  · rw [ExchangeEliminationEmbedding.mapEdge_eq_requestImage_of_extends_of_subset
        (Finset.subset_union_right :
          (ExchangeEmbedding.fullExchangeData hrk).special
              (ExchangeEmbedding.fullExchangeRootEdge hrk) ⊆
            ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
              (ExchangeEmbedding.fullExchangeRootEdge hrk)).root)
        request phi hextends]
    exact hrequestNeg
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
    let i : Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card :=
      ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.equivFin ⟨a, ha⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨eliminationBaseCoord t i, Finset.mem_univ _, ?_⟩
    apply Erdos722.Rotations.mem_rotateFamily.mpr
    simpa [focusingBasePerm, eliminationBaseCoord, i] using hfree i

noncomputable def reserveFocusing_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (reserve : Finset (Finset (Fin n)))
    (hreserveUniform : ∀ e ∈ reserve, e.card = r)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (A : Cover.CoverAssignment n k r reserve
      (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choiceR \ reserve)) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let host := (Finset.univ : Finset Base).biUnion fun c ↦
      Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
    SeparatedReserveFocusingFamily n k r reserve host := by
  dsimp only
  have hdisjoint : Disjoint reserve
      (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choiceR \
        reserve) := by
    rw [Finset.disjoint_left]
    intro e he hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 he
  let F0 := separatedReserveFocusingFamilyOfCoverAssignment
    hreserveUniform hdisjoint A
  refine {
    block := F0.block
    block_card := F0.block_card
    root_subset := F0.root_subset
    spill_subset := ?_
    reserve_unique := F0.reserve_unique
    spill_pairwise := F0.spill_pairwise }
  intro e he g hg
  have hgOld := F0.spill_subset e he hg
  have hgUnion := (Finset.mem_sdiff.mp hgOld).1
  obtain ⟨t, _ht, hgroup⟩ := Finset.mem_biUnion.mp hgUnion
  obtain ⟨i, _hi, hrot⟩ := Finset.mem_biUnion.mp hgroup
  apply Finset.mem_biUnion.mpr
  refine ⟨reserveBaseCoord t i, Finset.mem_univ _, ?_⟩
  simpa [focusingBasePerm, reserveBaseCoord] using hrot

theorem rainbowFocusing_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (fresh : Fin bankCount →
      Fin (remainingBlocks (ExchangeEmbedding.fullExchangeData hrk)).card →
        Equiv.Perm (Fin n))
    (hchoiceE : ∀ request : RootRequest
        (ExchangeEmbedding.fullExchangeData hrk).v n
        (ExchangeEmbedding.fullExchangeData hrk).pattern.root,
      ∃ t : Fin bankCount,
        ∃ phi : Fin (ExchangeEmbedding.fullExchangeData hrk).v ↪ Fin n,
          ExtendsRequest
              (ExchangeEmbedding.fullExchangeData hrk).pattern.root request phi ∧
          ∀ i, Erdos722.Rotations.rotateEdge (choiceE t i).symm
              (mapEdge phi
                (((ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges
                  ).equivFin.symm i).1) ∈ D.Kstar) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern e₀).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let Color := FocusingColor bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern e₀).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (remainingBlocks E).card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
    let colorEquiv : Color ≃ Fin (Fintype.card Color) := Fintype.equivFin Color
    let sigmaRoot : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
      fun i ↦ rootPerm (colorEquiv.symm i)
    let Kstar : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
      fun i ↦ D.rotatedKstar sigmaRoot i
    let host := (Finset.univ : Finset Base).biUnion fun c ↦
      Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
    ∀ Q ∈ fullySupportedBlocks n k r host,
      ∃ phi : Fin E.v ↪ Fin n,
        mapEdge phi E.pattern.root = Q ∧
        ExchangeEmbedding.mappedPositive E phi \ {Q} ⊆
          rainbowBlocks (Fintype.card Color) n k r Kstar ∧
        ExchangeEmbedding.mappedNegative E phi ⊆
          rainbowBlocks (Fintype.card Color) n k r Kstar := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
  let Color := FocusingColor bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (remainingBlocks E).card
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
  let colorEquiv : Color ≃ Fin (Fintype.card Color) := Fintype.equivFin Color
  let sigmaRoot : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
    fun i ↦ rootPerm (colorEquiv.symm i)
  let Kstar : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
    fun i ↦ D.rotatedKstar sigmaRoot i
  let host := (Finset.univ : Finset Base).biUnion fun c ↦
    Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
  change ∀ Q ∈ fullySupportedBlocks n k r host,
      ∃ phi : Fin E.v ↪ Fin n,
        mapEdge phi E.pattern.root = Q ∧
        ExchangeEmbedding.mappedPositive E phi \ {Q} ⊆
          rainbowBlocks (Fintype.card Color) n k r Kstar ∧
        ExchangeEmbedding.mappedNegative E phi ⊆
          rainbowBlocks (Fintype.card Color) n k r Kstar
  intro Q hQ
  have hQdata := mem_fullySupportedBlocks.mp hQ
  have hQnonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
  let : Nonempty (Fin n) := ⟨hQnonempty.choose⟩
  obtain ⟨request, hrequest⟩ := CoverClique.exists_rootRequest_with_image
    E.pattern.root Q (E.root_card.trans hQdata.1.symm)
  obtain ⟨t, phi, hextends, hfree⟩ := hchoiceE request
  have hroot : mapEdge phi E.pattern.root = Q :=
    (mapEdge_root_eq_requestImage_of_extends _ request phi hextends).trans
      hrequest
  have hrootHost : ∀ e : Exchange.RootEdge k r,
      requestedRootEdge E request e ∈ host := by
    intro e
    apply hQdata.2
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, requestedRootEdge_card E request e⟩
    rw [← hrequest]
    exact requestedRootEdge_subset_requestImage E request e
  let rootCoord : Exchange.RootEdge k r → Base := fun e ↦
    Classical.choose (Finset.mem_biUnion.mp (hrootHost e))
  have hrootCoordMem : ∀ e : Exchange.RootEdge k r,
      requestedRootEdge E request e ∈
        Erdos722.Rotations.rotateFamily (basePerm (rootCoord e)) D.Kstar := by
    intro e
    exact (Classical.choose_spec
      (Finset.mem_biUnion.mp (hrootHost e))).2
  let rootColor : Exchange.RootEdge k r → Fin (Fintype.card Color) :=
    fun e ↦ colorEquiv (rootAliasColor (rootCoord e))
  let freeColor : ↑E.pattern.freeEdges → Fin (Fintype.card Color) :=
    fun a ↦ colorEquiv (freeAliasColor
      (exchangeBaseCoord t (E.pattern.freeEdges.equivFin a)))
  let : Nonempty (Fin (Fintype.card Color)) :=
    ⟨colorEquiv (rootAliasColor identityBaseCoord)⟩
  have hfreeColor : Function.Injective freeColor := by
    intro a b hab
    have hab' := colorEquiv.injective hab
    change freeAliasColor
        (exchangeBaseCoord t (E.pattern.freeEdges.equivFin a)) =
      freeAliasColor
        (exchangeBaseCoord t (E.pattern.freeEdges.equivFin b)) at hab'
    have h₁ := Sum.inl.inj hab'
    have h₂ := Sum.inr.inj h₁
    have h₃ := Sum.inr.inj h₂
    have hpair := Sum.inl.inj h₃
    have hi : E.pattern.freeEdges.equivFin a =
        E.pattern.freeEdges.equivFin b := congrArg Prod.snd hpair
    exact E.pattern.freeEdges.equivFin.injective hi
  have hcolorsDisjoint : ∀ e a, rootColor e ≠ freeColor a := by
    intro e a heq
    have heq' := colorEquiv.injective heq
    change rootAliasColor (rootCoord e) = freeAliasColor
      (exchangeBaseCoord t (E.pattern.freeEdges.equivFin a)) at heq'
    unfold rootAliasColor freeAliasColor at heq'
    simp at heq'
  have hrootMem : ∀ e, mapEdge phi
      (Exchange.mappedRootEdge E.rootEmbedding e.1) ∈ Kstar (rootColor e) := by
    intro e
    have heq : mapEdge phi (Exchange.mappedRootEdge E.rootEmbedding e.1) =
        requestedRootEdge E request e := by
      unfold requestedRootEdge mapEdge
      rw [Finset.map_eq_image]
      apply Finset.image_congr
      intro x hx
      exact hextends x
        (by
          rw [E.root_eq]
          exact Exchange.mappedRootEdge_subset_mappedRoot
            E.rootEmbedding e.1 hx)
    rw [heq]
    simpa [Kstar, Erdos722.Rotations.TwoCapPrunedData.rotatedKstar,
      sigmaRoot, rootColor, rootPerm, focusingRootPerm,
      focusingRootSupport, rootAliasColor] using hrootCoordMem e
  have hfreeMem : ∀ a : ↑E.pattern.freeEdges,
      mapEdge phi a.1 ∈ Kstar (freeColor a) := by
    intro a
    let i := E.pattern.freeEdges.equivFin a
    have hi := hfree i
    change Erdos722.Rotations.rotateEdge (choiceE t i).symm
      (mapEdge phi ((E.pattern.freeEdges.equivFin.symm i).1)) ∈ D.Kstar at hi
    rw [show E.pattern.freeEdges.equivFin.symm i = a by simp [i]] at hi
    have hrot : mapEdge phi a.1 ∈
        Erdos722.Rotations.rotateFamily (choiceE t i) D.Kstar := by
      apply Erdos722.Rotations.mem_rotateFamily.mpr
      exact hi
    simpa [Kstar, Erdos722.Rotations.TwoCapPrunedData.rotatedKstar,
      sigmaRoot, freeColor, rootPerm, focusingRootPerm,
      focusingRootSupport, freeAliasColor, basePerm, focusingBasePerm,
      exchangeBaseCoord, i] using hrot
  refine ⟨phi, hroot, ?_, ?_⟩
  · intro B hB
    have hBdata := Finset.mem_sdiff.mp hB
    obtain ⟨B₀, hB₀, hmap⟩ :=
      Transversal.mem_mapFamily.mp hBdata.1
    have hB₀ne : B₀ ≠ E.pattern.root := by
      intro hEq
      apply hBdata.2
      rw [← hmap, hEq]
      change mapEdge phi E.pattern.root ∈ {Q}
      simp [hroot]
    rw [← hmap]
    apply mappedRemaining_mem_rainbowBlocks E phi Kstar freeColor
      hfreeColor hfreeMem
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hB₀ne, hB₀⟩)
  · intro B hB
    obtain ⟨B₀, hB₀, hmap⟩ := Transversal.mem_mapFamily.mp hB
    rw [← hmap]
    by_cases hspecial : B₀ ∈ specialBlocks E
    · obtain ⟨e, _he, heq⟩ := Finset.mem_image.mp hspecial
      rw [← heq]
      exact mappedSpecial_mem_rainbowBlocks E phi Kstar rootColor freeColor
        hfreeColor hcolorsDisjoint hrootMem hfreeMem e
    · apply mappedRemaining_mem_rainbowBlocks E phi Kstar freeColor
        hfreeColor hfreeMem
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hB₀, hspecial⟩)

theorem rainbowSpan_of_rotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (fresh : Fin bankCount →
      Fin (remainingBlocks (ExchangeEmbedding.fullExchangeData hrk)).card →
        Equiv.Perm (Fin n))
    (hfresh :
      let E := ExchangeEmbedding.fullExchangeData hrk
      let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
      let Color := FocusingColor bankCount E.pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (remainingBlocks E).card
      let basePerm : Base → Equiv.Perm (Fin n) :=
        focusingBasePerm choiceE choiceA choiceX choiceR
      let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
      ∀ (request : RootRequest E.v n E.pattern.root)
        (color : Exchange.RootEdge k r → Color),
        (∀ e, requestedRootEdge E request e ∈
          Erdos722.Rotations.rotateFamily (rootPerm (color e)) D.Kstar) →
        ∃ (t : Fin bankCount) (phi : Fin E.v ↪ Fin n),
          ExtendsRequest E.pattern.root request phi ∧
          (∀ e, mapEdge phi (E.special e) ∈
            Erdos722.Rotations.rotateFamily (rootPerm (color e))
              (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)) ∧
          ∀ i, Erdos722.Rotations.rotateEdge (fresh t i).symm
              (mapEdge phi (((remainingBlocks E).equivFin.symm i).1)) ∈
            Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
    let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern e₀).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
    let Color := FocusingColor bankCount E.pattern.freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (E.eliminationPattern e₀).freeEdges.card
      (CoverClique.coverPattern k r).freeEdges.card
      (remainingBlocks E).card
    let basePerm : Base → Equiv.Perm (Fin n) :=
      focusingBasePerm choiceE choiceA choiceX choiceR
    let generatorPerm : Color → Equiv.Perm (Fin n) :=
      focusingGeneratorPerm basePerm fresh
    let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
    let colorEquiv : Color ≃ Fin (Fintype.card Color) := Fintype.equivFin Color
    let sigmaGenerator : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
      fun i ↦ generatorPerm (colorEquiv.symm i)
    let sigmaRoot : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
      fun i ↦ rootPerm (colorEquiv.symm i)
    let K : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
      fun i ↦ D.rotatedK sigmaGenerator i
    let Kstar : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
      fun i ↦ D.rotatedKstar sigmaRoot i
    let selected : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
      fun i ↦ D.rotatedSelected sigmaGenerator i
    ∀ B ∈ rainbowBlocks (Fintype.card Color) n k r Kstar,
      Generators.InModularSpan N n r
        (coloredModularGenerators (Fintype.card Color) n selected)
        (Generators.modCliqueBoundary N n r B) := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
  let Color := FocusingColor bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (remainingBlocks E).card
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  let generatorPerm : Color → Equiv.Perm (Fin n) :=
    focusingGeneratorPerm basePerm fresh
  let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
  let colorEquiv : Color ≃ Fin (Fintype.card Color) := Fintype.equivFin Color
  let sigmaGenerator : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
    fun i ↦ generatorPerm (colorEquiv.symm i)
  let sigmaRoot : Fin (Fintype.card Color) → Equiv.Perm (Fin n) :=
    fun i ↦ rootPerm (colorEquiv.symm i)
  let K : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
    fun i ↦ D.rotatedK sigmaGenerator i
  let Kstar : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
    fun i ↦ D.rotatedKstar sigmaRoot i
  let selected : Fin (Fintype.card Color) → Finset (Finset (Fin n)) :=
    fun i ↦ D.rotatedSelected sigmaGenerator i
  change ∀ B ∈ rainbowBlocks (Fintype.card Color) n k r Kstar,
      Generators.InModularSpan N n r
        (coloredModularGenerators (Fintype.card Color) n selected)
        (Generators.modCliqueBoundary N n r B)
  intro B hB
  obtain ⟨hBcard, color, _hcolorInjective, hcolorMem⟩ :=
    mem_rainbowBlocks.mp hB
  have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  let : Nonempty (Fin n) := ⟨hBnonempty.choose⟩
  obtain ⟨request, hrequest⟩ := CoverClique.exists_rootRequest_with_image
    E.pattern.root B (E.root_card.trans hBcard.symm)
  let actualColor : Exchange.RootEdge k r → Color := fun e ↦
    colorEquiv.symm (color (requestedRootEdge E request e))
  have hrequestedPowerset : ∀ e : Exchange.RootEdge k r,
      requestedRootEdge E request e ∈ B.powersetCard r := by
    intro e
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, requestedRootEdge_card E request e⟩
    rw [← hrequest]
    exact requestedRootEdge_subset_requestImage E request e
  have hrootColors : ∀ e, requestedRootEdge E request e ∈
      Erdos722.Rotations.rotateFamily (rootPerm (actualColor e)) D.Kstar := by
    intro e
    have hm := hcolorMem (requestedRootEdge E request e)
      (hrequestedPowerset e)
    simpa [Kstar, Erdos722.Rotations.TwoCapPrunedData.rotatedKstar,
      sigmaRoot, actualColor] using hm
  obtain ⟨t, phi, hextends, hspecial, hremaining⟩ :=
    hfresh request actualColor hrootColors
  have hroot : mapEdge phi E.pattern.root = B :=
    (mapEdge_root_eq_requestImage_of_extends _ request phi hextends).trans
      hrequest
  have hglobal : ∀ (z : Color) (Q : Finset (Fin n)),
      Q ∈ Erdos722.Rotations.rotateFamily (generatorPerm z)
          (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D) →
      Generators.InModularSpan N n r
        (coloredModularGenerators (Fintype.card Color) n selected)
        (Generators.modCliqueBoundary N n r Q) := by
    intro z Q hQ
    let i := colorEquiv z
    have hperm : sigmaGenerator i = generatorPerm z := by simp [i, sigmaGenerator]
    have hQunsat : Q ∈ IntegralGenerators.twoCapUnsaturatedCliques
        n k r faceCap edgeCap (D.rotatedK sigmaGenerator i)
          (D.rotatedSelected sigmaGenerator i) := by
      rw [Erdos722.Rotations.TwoCapPrunedData.rotatedK,
        Erdos722.Rotations.TwoCapPrunedData.rotatedSelected, hperm,
        ← Erdos722.Rotations.rotateFamily_twoCapUnsaturatedCliques]
      simpa [Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques]
        using hQ
    have hrestricted := D.rotated_selected_span sigmaGenerator i Q hQunsat
    have hlocal := Prune.inModularSpan_of_inRestrictedModularSpan
      (D.rotatedSelected_subset sigmaGenerator i)
      ((IntegralGenerators.mem_twoCapUnsaturatedCliques.mp hQunsat).1)
      hrestricted
    apply hlocal.mono
    intro C hC
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hC⟩
  apply modCliqueBoundary_mem_span_of_specialExchange E phi hroot
  · intro e
    let z : Color := rootAliasColor (focusingRootSupport (actualColor e))
    apply hglobal z
    simpa [z, generatorPerm, focusingGeneratorPerm, rootPerm,
      focusingRootPerm, rootAliasColor] using hspecial e
  · intro Q hQ
    let i : Fin (remainingBlocks E).card :=
      (remainingBlocks E).equivFin ⟨Q, hQ⟩
    have hi := hremaining i
    have hiQ : ((remainingBlocks E).equivFin.symm i).1 = Q := by simp [i]
    rw [hiQ] at hi
    let z : Color := freshGeneratorColor t i
    apply hglobal z
    apply Erdos722.Rotations.mem_rotateFamily.mpr
    simpa [z, generatorPerm, focusingGeneratorPerm, freshGeneratorColor]
      using hi

/-- The deterministic finite assembly underlying Keevash's Lemma 6.3. -/
noncomputable def focusingHostOfRotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n)) :
    Finset (Finset (Fin n)) :=
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  (Finset.univ : Finset Base).biUnion fun c ↦
    Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar

lemma focusingBaseCoord_card_le
    {bankCount mE mA mX mR : ℕ} (hbank : 0 < bankCount) :
    Fintype.card (FocusingBaseCoord bankCount mE mA mX mR) ≤
      (1 + mE + mA + mX + mR) * bankCount := by
  simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_prod, Fintype.card_fin]
  calc
    1 + (bankCount * mE + (bankCount * mA +
        (bankCount * mX + bankCount * mR))) =
      1 + bankCount * (mE + mA + mX + mR) := by ring
    _ ≤ bankCount + bankCount * (mE + mA + mX + mR) := by
      gcongr
      omega
    _ = (1 + mE + mA + mX + mR) * bankCount := by ring

theorem focusingHost_localDegree_le_mul_maxLowerDegree
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    localDegree (focusingHostOfRotationBanks hrk D
      choiceE choiceA choiceX choiceR) J ≤
      Fintype.card (FocusingBaseCoord bankCount
        (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
          (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card) *
          maxLowerDegree n r D.K := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  have hone (c : Base) : localDegree
      (Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar) J ≤
        maxLowerDegree n r D.K := by
    have hmono : localDegree
        (Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar) J ≤
          localDegree (Erdos722.Rotations.rotateFamily (basePerm c) D.K) J := by
      simpa only [localDegree, blockIncidenceCount] using
        blockIncidenceCount_mono
          (Erdos722.Rotations.rotateFamily_mono
            (basePerm c) D.Kstar_subset) J
    let J₀ := Erdos722.Rotations.rotateEdge (basePerm c).symm J
    have hcard : J₀.card = r - 1 := by simpa [J₀] using hJ
    have heq : localDegree
        (Erdos722.Rotations.rotateFamily (basePerm c) D.K) J =
          localDegree D.K J₀ := by
      simpa [localDegree, Generators.counterLoad, J₀] using
        (Erdos722.Rotations.counterLoad_rotateFamily (basePerm c) D.K J₀)
    exact hmono.trans (heq.le.trans
      (localDegree_le_maxLowerDegree D.K J₀ hcard))
  have hsum := blockIncidenceCount_biUnion_le_sum
    (Finset.univ : Finset Base)
    (fun c ↦ Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar) J
  calc
    localDegree (focusingHostOfRotationBanks hrk D
        choiceE choiceA choiceX choiceR) J ≤
        ∑ c ∈ (Finset.univ : Finset Base),
          localDegree (Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar) J := by
      simpa only [focusingHostOfRotationBanks, localDegree,
        blockIncidenceCount] using hsum
    _ ≤ ∑ _c ∈ (Finset.univ : Finset Base),
        maxLowerDegree n r D.K :=
      Finset.sum_le_sum fun c _hc ↦ hone c
    _ = Fintype.card Base * maxLowerDegree n r D.K := by simp

noncomputable def rainbowTwoCapFocusingCertificateOfRotationBanks
    {N n k r faceCap edgeCap bankCount threshold Mface Medge : ℕ}
    (hr : 1 < r) (hrk : r < k)
    (D : Erdos722.Rotations.TwoCapPrunedData N n k r
      faceCap edgeCap threshold Mface Medge)
    (reserve : Finset (Finset (Fin n)))
    (hreserveUniform : ∀ e ∈ reserve, e.card = r)
    (choiceE : Fin bankCount →
      Fin (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card →
        Equiv.Perm (Fin n))
    (hchoiceE : ∀ request : RootRequest
        (ExchangeEmbedding.fullExchangeData hrk).v n
        (ExchangeEmbedding.fullExchangeData hrk).pattern.root,
      ∃ t : Fin bankCount,
        ∃ phi : Fin (ExchangeEmbedding.fullExchangeData hrk).v ↪ Fin n,
          ExtendsRequest
              (ExchangeEmbedding.fullExchangeData hrk).pattern.root request phi ∧
          ∀ i, Erdos722.Rotations.rotateEdge (choiceE t i).symm
              (mapEdge phi
                (((ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges
                  ).equivFin.symm i).1) ∈ D.Kstar)
    (choiceA : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (hchoiceA : ∀ request : RootRequest k n (CoverClique.coverRoot k r),
      ∀ J : Finset (Fin n), J.card ≤ 2 * k →
        ∃ (t : Fin bankCount) (phi : Fin k ↪ Fin n),
          phi ∈ Erdos722.RotationAbundance.successfulRootedEmbeddings
            (CoverClique.coverRoot k r) request D.Kstar
            (fun i ↦ ((CoverClique.coverPattern k r).freeEdges.equivFin.symm i).1)
            (choiceA t) ∧
          ¬ OutsideRootTouches (CoverClique.coverRoot k r) J phi)
    (choiceX : Fin bankCount →
      Fin ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
        (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card →
        Equiv.Perm (Fin n))
    (hchoiceX : ∀ request : RootRequest
        (ExchangeEmbedding.fullExchangeData hrk).v n
        ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
          (ExchangeEmbedding.fullExchangeRootEdge hrk)).root,
      ∃ t : Fin bankCount,
        ∃ phi : Fin (ExchangeEmbedding.fullExchangeData hrk).v ↪ Fin n,
          ExtendsRequest
              ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
                (ExchangeEmbedding.fullExchangeRootEdge hrk)).root request phi ∧
          ∀ i, Erdos722.Rotations.rotateEdge (choiceX t i).symm
              (mapEdge phi
                ((((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
                  (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges
                  ).equivFin.symm i).1) ∈ D.Kstar)
    (choiceR : Fin bankCount →
      Fin (CoverClique.coverPattern k r).freeEdges.card → Equiv.Perm (Fin n))
    (A : Cover.CoverAssignment n k r reserve
      (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choiceR \ reserve))
    (fresh : Fin bankCount →
      Fin (remainingBlocks (ExchangeEmbedding.fullExchangeData hrk)).card →
        Equiv.Perm (Fin n))
    (hfresh :
      let E := ExchangeEmbedding.fullExchangeData hrk
      let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
      let Color := FocusingColor bankCount E.pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (E.eliminationPattern (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (remainingBlocks E).card
      let basePerm : Base → Equiv.Perm (Fin n) :=
        focusingBasePerm choiceE choiceA choiceX choiceR
      let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
      ∀ (request : RootRequest E.v n E.pattern.root)
        (color : Exchange.RootEdge k r → Color),
        (∀ e, requestedRootEdge E request e ∈
          Erdos722.Rotations.rotateFamily (rootPerm (color e)) D.Kstar) →
        ∃ (t : Fin bankCount) (phi : Fin E.v ↪ Fin n),
          ExtendsRequest E.pattern.root request phi ∧
          (∀ e, mapEdge phi (E.special e) ∈
            Erdos722.Rotations.rotateFamily (rootPerm (color e))
              (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)) ∧
          ∀ i, Erdos722.Rotations.rotateEdge (fresh t i).symm
              (mapEdge phi (((remainingBlocks E).equivFin.symm i).1)) ∈
            Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D) :
    { C : RainbowTwoCapFocusingCertificate N n k r faceCap edgeCap
      (Fintype.card (FocusingColor bankCount
        (ExchangeEmbedding.fullExchangeData hrk).pattern.freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        ((ExchangeEmbedding.fullExchangeData hrk).eliminationPattern
          (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card
        (CoverClique.coverPattern k r).freeEdges.card
        (remainingBlocks (ExchangeEmbedding.fullExchangeData hrk)).card))
      hrk reserve // C.host = focusingHostOfRotationBanks hrk D
        choiceE choiceA choiceX choiceR } := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let Base := FocusingBaseCoord bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
  let Color := FocusingColor bankCount E.pattern.freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (E.eliminationPattern e₀).freeEdges.card
    (CoverClique.coverPattern k r).freeEdges.card
    (remainingBlocks E).card
  let u := Fintype.card Color
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  let generatorPerm : Color → Equiv.Perm (Fin n) :=
    focusingGeneratorPerm basePerm fresh
  let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
  let colorEquiv : Color ≃ Fin u := Fintype.equivFin Color
  let sigmaGenerator : Fin u → Equiv.Perm (Fin n) :=
    fun i ↦ generatorPerm (colorEquiv.symm i)
  let sigmaRoot : Fin u → Equiv.Perm (Fin n) :=
    fun i ↦ rootPerm (colorEquiv.symm i)
  let host := (Finset.univ : Finset Base).biUnion fun c ↦
    Erdos722.Rotations.rotateFamily (basePerm c) D.Kstar
  let K : Fin u → Finset (Finset (Fin n)) := fun i ↦
    D.rotatedK sigmaGenerator i
  let Kstar : Fin u → Finset (Finset (Fin n)) := fun i ↦
    D.rotatedKstar sigmaRoot i
  let selected : Fin u → Finset (Finset (Fin n)) := fun i ↦
    D.rotatedSelected sigmaGenerator i
  have hexchange : HasExchangeFocusing n k r E
      (almostSupportedBlocks n k r host) := by
    simpa [E, e₀, Base, basePerm, host] using
      hasExchangeFocusing_of_rotationBanks hr hrk D choiceE choiceA choiceX
        choiceR hchoiceE
  have hauxiliary : ∀ g ∈ completeUniform n r,
      ∀ forbiddenVertices : Finset (Fin n), g ⊆ forbiddenVertices →
        forbiddenVertices.card ≤ 2 * k →
        ∃ Q ∈ blockCandidates n k,
          Q.powersetCard r \ {g} ⊆ host ∧ Q ∩ forbiddenVertices = g := by
    simpa [E, e₀, Base, basePerm, host] using
      auxiliaryFocusing_of_rotationBanks hr hrk D choiceE choiceA choiceX
        choiceR hchoiceA
  have helimination : ∀ P : ExchangeEliminationEmbedding.EliminationPair n k r,
      ∃ psi : Fin E.v ↪ Fin n,
        mapEdge psi E.pattern.root = P.positive ∧
        mapEdge psi (E.special e₀) = P.negative ∧
        imageFreeEdges (E.eliminationPattern e₀) psi ⊆ host := by
    simpa [E, e₀, Base, basePerm, host] using
      eliminationFocusing_of_rotationBanks hr hrk D choiceE choiceA choiceX
        choiceR hchoiceX
  let reserveFocus : SeparatedReserveFocusingFamily n k r reserve host := by
    simpa [E, e₀, Base, basePerm, host] using
      reserveFocusing_of_rotationBanks hrk D reserve hreserveUniform choiceE
        choiceA choiceX choiceR A
  have hrainbowFocus : ∀ Q ∈ fullySupportedBlocks n k r host,
      ∃ phi : Fin E.v ↪ Fin n,
        mapEdge phi E.pattern.root = Q ∧
        ExchangeEmbedding.mappedPositive E phi \ {Q} ⊆
          rainbowBlocks u n k r Kstar ∧
        ExchangeEmbedding.mappedNegative E phi ⊆
          rainbowBlocks u n k r Kstar := by
    simpa [E, e₀, Base, Color, u, basePerm, rootPerm, colorEquiv,
      sigmaRoot, Kstar, host] using
      rainbowFocusing_of_rotationBanks hr hrk D choiceE choiceA choiceX
        choiceR fresh hchoiceE
  have hrainbowSpan : ∀ B ∈ rainbowBlocks u n k r Kstar,
      Generators.InModularSpan N n r
        (coloredModularGenerators u n selected)
        (Generators.modCliqueBoundary N n r B) := by
    simpa [E, e₀, Base, Color, u, basePerm, generatorPerm, rootPerm,
      colorEquiv, sigmaGenerator, sigmaRoot, K, Kstar, selected] using
      rainbowSpan_of_rotationBanks hr hrk D choiceE choiceA choiceX choiceR
        fresh hfresh
  refine ⟨{
    host := host
    K := K
    Kstar := Kstar
    selected := selected
    selected_subset := ?_
    selected_span := ?_
    face_load := ?_
    edge_load := ?_
    reserveFocus := reserveFocus
    rainbow_span := hrainbowSpan
    rainbow_focus := ?_
    exchange_focus := ?_
    auxiliary_focus := hauxiliary
    elimination_focus := ?_ }, ?_⟩
  · intro i
    exact D.rotatedSelected_subset sigmaGenerator i
  · intro i B hB
    exact D.rotated_selected_span sigmaGenerator i B hB
  · intro i J hJ
    exact D.rotated_face_load sigmaGenerator i J hJ
  · intro i e he
    exact D.rotated_edge_load sigmaGenerator i e he
  · exact hrainbowFocus
  · exact hexchange
  · exact helimination
  · rfl

end

end Erdos722
