/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.LeafObstructionSequence
import ErdosProblems.Erdos570.LeafCycle
import ErdosProblems.Erdos570.LeafEmbedding
import ErdosProblems.Erdos570.FiniteSelection

/-!
# The leaf-obstruction endgame

Several large unused red neighborhoods have a large common part outside the
fixed set `S`.  A red edge between the first and last unused neighborhoods
would close an alternating odd cycle.  Hence, after removing the selected
parents, those two neighborhoods are blue-complete to one another.  Their
large intersection hosts the non-leaf core and their union hosts the leaves.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Intersection of all members of a finite indexed family, restricted to
the ambient finite set `T`. -/
def commonPart {W : Type*} [DecidableEq W] {t : ℕ}
    (U : Fin t → Finset W) (T : Finset W) : Finset W :=
  T.filter fun x ↦ ∀ i, x ∈ U i

theorem commonPart_subset {W : Type*} [DecidableEq W] {t : ℕ}
    (U : Fin t → Finset W) (T : Finset W) (i : Fin t) :
    commonPart U T ⊆ U i := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2 i

theorem commonPart_subset_ambient {W : Type*} [DecidableEq W] {t : ℕ}
    (U : Fin t → Finset W) (T : Finset W) :
    commonPart U T ⊆ T := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- If every `U i` misses at most `d` points of `T`, their common part
misses at most `t*d` points. -/
theorem commonPart_card_ge
    {W : Type*} [Fintype W] [DecidableEq W] {t d : ℕ}
    (U : Fin t → Finset W) (T : Finset W)
    (hlarge : ∀ i, T.card - d ≤ ((U i) ∩ T).card) :
    T.card - t * d ≤ (commonPart U T).card := by
  classical
  let missing : Fin t → Finset W := fun i ↦ T \ U i
  have hmissing (i : Fin t) : (missing i).card ≤ d := by
    have hsplit := Finset.card_sdiff_add_card_inter T (U i)
    have hinter : (T ∩ U i).card = ((U i) ∩ T).card := by
      rw [Finset.inter_comm]
    rw [hinter] at hsplit
    dsimp only [missing]
    by_cases hdT : d ≤ T.card
    · calc
        (T \ U i).card = T.card - (T ∩ U i).card := by omega
        _ ≤ T.card - (T.card - d) :=
          Nat.sub_le_sub_left (by
            simpa [Finset.inter_comm] using hlarge i) T.card
        _ = d := by omega
    · omega
  let bad : Finset W := T \ commonPart U T
  let allMissing : Finset W := Finset.univ.biUnion missing
  have hbadSubset : bad ⊆ allMissing := by
    intro x hx
    have hxT := (Finset.mem_sdiff.mp hx).1
    have hxnot := (Finset.mem_sdiff.mp hx).2
    have hnotall : ¬∀ i, x ∈ U i := by
      intro hall
      exact hxnot (Finset.mem_filter.mpr ⟨hxT, hall⟩)
    push_neg at hnotall
    obtain ⟨i, hi⟩ := hnotall
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hxT, hi⟩⟩
  have hallMissingCard : allMissing.card ≤ t * d := by
    calc
      allMissing.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)),
          (missing i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), d :=
        Finset.sum_le_sum fun i _ ↦ hmissing i
      _ = t * d := by simp
  have hbadCard : bad.card ≤ t * d :=
    (Finset.card_le_card hbadSubset).trans hallMissingCard
  have hcommonSubset : commonPart U T ⊆ T := commonPart_subset_ambient U T
  have hsplit := Finset.card_sdiff_add_card_eq_card hcommonSubset
  have hbadEq : T \ commonPart U T = bad := rfl
  rw [hbadEq] at hsplit
  calc
    T.card - t * d ≤ T.card - bad.card :=
      Nat.sub_le_sub_left hbadCard T.card
    _ = (commonPart U T).card := by omega

/-- The first and last obstruction neighborhoods are blue-complete after
the parent vertices are removed. -/
theorem leafObstruction_blue_complete
    {W : Type*} [Fintype W] [DecidableEq W]
    {C : SimpleGraph W} {S T : Finset W} {q r g : ℕ}
    (F : LeafObstructionFamily C S T q g (r + 1))
    (hcommon : r + 2 ≤ (commonPart F.unused T).card)
    (hnoCycle : ¬SimpleGraph.cycleGraph (2 * r + 3) ⊑ C) :
    let P := Finset.univ.image F.parent
    let A := F.unused 0 \ P
    let B := F.unused (Fin.last r) \ P
    ∀ a ∈ A, ∀ b ∈ B, a ≠ b → Cᶜ.Adj a b := by
  classical
  dsimp only
  intro a ha b hb hab
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, ?_⟩
  intro habRed
  obtain ⟨w, hw, hw0, hwlast, hwmid⟩ :=
    exists_injective_sequence_with_middle hab hcommon
  have hparentRange (i : Fin (r + 1)) :
      F.parent i ∈ Finset.univ.image F.parent := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have haNotParent := (Finset.mem_sdiff.mp ha).2
  have hbNotParent := (Finset.mem_sdiff.mp hb).2
  have hdisj : ∀ i j, F.parent i ≠ w j := by
    intro i j heq
    induction j using Fin.cases with
    | zero =>
        apply haNotParent
        rw [← hw0, ← heq]
        exact hparentRange i
    | succ j =>
        induction j using Fin.lastCases with
        | last =>
            apply hbNotParent
            have hidx : (Fin.last r).succ = Fin.last (r + 1) := Fin.ext rfl
            rw [← hwlast, ← hidx, ← heq]
            exact hparentRange i
        | cast j =>
            have hwmem : w j.succ.castSucc ∈ F.unused i :=
              commonPart_subset F.unused T i (hwmid j)
            exact (F.red_neighborhood i _ hwmem).ne heq
  have hleft : ∀ i, C.Adj (F.parent i) (w i.castSucc) := by
    intro i
    induction i using Fin.cases with
    | zero =>
        have haU := (Finset.mem_sdiff.mp ha).1
        simpa [hw0] using F.red_neighborhood 0 a haU
    | succ j =>
        have hmem : w j.succ.castSucc ∈ F.unused j.succ :=
          commonPart_subset F.unused T j.succ (hwmid j)
        exact hmem |> F.red_neighborhood j.succ _
  have hright : ∀ i, C.Adj (F.parent i) (w i.succ) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
        have hbU := (Finset.mem_sdiff.mp hb).1
        simpa [hwlast] using F.red_neighborhood (Fin.last r) b hbU
    | cast i =>
        have hidx : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        rw [hidx]
        have hmem : w i.succ.castSucc ∈ F.unused i.castSucc :=
          commonPart_subset F.unused T i.castSucc (hwmid i)
        exact hmem |> F.red_neighborhood i.castSucc _
  apply hnoCycle
  exact cycleGraph_odd_isContained_of_consecutive_cross
    F.parent w F.parent_injective hw hdisj hleft hright (by
      simpa [hw0, hwlast] using habRed)

/-- The two endpoint obstructions force a blue copy of the original target
when a twice-as-large leaf set is available. -/
theorem isContained_compl_of_leafObstructionFamily
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (L₂ : Finset (Fin H.vertexCount))
    (hL₂ : ∀ v ∈ L₂, H.graph.degree v = 1)
    {C : SimpleGraph W} {S T : Finset W} {r : ℕ}
    (hTS : T = Sᶜ) (hScard : S.card = H.vertexCount)
    (hLpos : 1 ≤ L.card)
    (hL₂card : L₂.card = 2 * L.card)
    (hhost : 2 * H.edgeCount + (r + 1) ≤ Fintype.card W)
    (hcommonRoom : (r + 1) * (L.card - 1) + (r + 2) ≤ T.card)
    (F : LeafObstructionFamily C S T L.card
      (Fintype.card W - (H.vertexCount - 1)) (r + 1))
    (hnoCycle : ¬SimpleGraph.cycleGraph (2 * r + 3) ⊑ C) :
    H.graph ⊑ Cᶜ := by
  classical
  have hnEdge : H.vertexCount ≤ H.edgeCount + 1 := by
    simpa [GraphCode.edgeCount] using hconn.card_vert_le_card_edgeSet_add_one
  let P : Finset W := Finset.univ.image F.parent
  have hPcard : P.card = r + 1 := by
    dsimp only [P]
    rw [Finset.card_image_of_injective _ F.parent_injective]
    simp
  let i₀ : Fin (r + 1) := 0
  let i₁ : Fin (r + 1) := Fin.last r
  let A : Finset W := F.unused i₀ \ P
  let B : Finset W := F.unused i₁ \ P
  have hparentNotUnused (i : Fin (r + 1)) : F.parent i ∉ F.unused i := by
    intro hi
    exact (F.red_neighborhood i _ hi).ne rfl
  have hinterP (i : Fin (r + 1)) :
      ((F.unused i) ∩ P).card ≤ r := by
    have hproper : (F.unused i) ∩ P ⊂ P := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro heq
      have hp : F.parent i ∈ P :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have : F.parent i ∈ (F.unused i) ∩ P := by
        rw [heq]
        exact hp
      exact hparentNotUnused i (Finset.mem_inter.mp this).1
    have hc := Finset.card_lt_card hproper
    rw [hPcard] at hc
    omega
  have hABcard (i : Fin (r + 1)) :
      H.vertexCount ≤ (F.unused i \ P).card := by
    have hglobal := F.global_large i
    have hsplit := Finset.card_sdiff_add_card_inter (F.unused i) P
    have hinter := hinterP i
    omega
  have hAcard : H.vertexCount ≤ A.card := by simpa [A, i₀] using hABcard i₀
  have hBcard : H.vertexCount ≤ B.card := by simpa [B, i₁] using hABcard i₁
  have hcommonCard : r + 2 ≤ (commonPart F.unused T).card := by
    have hsub : r + 2 ≤ T.card - (r + 1) * (L.card - 1) := by
      apply Nat.le_sub_of_add_le
      simpa [add_comm] using hcommonRoom
    exact hsub.trans (commonPart_card_ge F.unused T F.outside_large)
  have hblueCross : ∀ a ∈ A, ∀ b ∈ B, a ≠ b → Cᶜ.Adj a b := by
    simpa [A, B, P, i₀, i₁] using
      leafObstruction_blue_complete F hcommonCard hnoCycle
  let Kraw : Finset W := (F.unused i₀ ∩ F.unused i₁) ∩ T
  have hKrawEq : Kraw =
      ((F.unused i₀ ∩ T) ∩ (F.unused i₁ ∩ T)) := by
    ext x
    simp [Kraw, and_assoc, and_left_comm, and_comm]
  have hKrawCard : H.vertexCount - 2 * L.card + (r + 1) ≤ Kraw.card := by
    let V : Fin 2 → Finset W := fun i ↦ if i = 0 then F.unused i₀ else F.unused i₁
    have hVlarge : ∀ i, T.card - (L.card - 1) ≤ ((V i) ∩ T).card := by
      intro i
      fin_cases i
      · simpa [V] using F.outside_large i₀
      · simpa [V] using F.outside_large i₁
    have hVcommon : commonPart V T = Kraw := by
      ext x
      simp only [commonPart, Finset.mem_filter]
      constructor
      · rintro ⟨hxT, hall⟩
        have hx0 := hall (0 : Fin 2)
        have hx1 := hall (1 : Fin 2)
        simp only [V, if_pos rfl] at hx0
        have hone : (1 : Fin 2) ≠ 0 := by decide
        simp only [V, if_neg hone] at hx1
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨hx0, hx1⟩, hxT⟩
      · intro hx
        have hx' := Finset.mem_inter.mp hx
        refine ⟨hx'.2, ?_⟩
        intro i
        fin_cases i
        · simpa [V] using (Finset.mem_inter.mp hx'.1).1
        · simpa [V] using (Finset.mem_inter.mp hx'.1).2
    have hbase := commonPart_card_ge V T hVlarge
    rw [show (2 : ℕ) * (L.card - 1) = 2 * (L.card - 1) by rfl,
      hVcommon] at hbase
    have hTcard : T.card + H.vertexCount = Fintype.card W := by
      rw [hTS]
      simpa [hScard, add_comm] using Finset.card_add_card_compl S
    have hL₂le : L₂.card ≤ H.vertexCount :=
      by simpa using Finset.card_le_card (Finset.subset_univ L₂)
    have htwoL : 2 * L.card ≤ H.vertexCount := by omega
    have hTlower : H.vertexCount + r - 1 ≤ T.card := by omega
    have hpay : H.vertexCount - 2 * L.card + (r + 1) +
        2 * (L.card - 1) ≤ T.card := by
      have heq : H.vertexCount - 2 * L.card + (r + 1) +
          2 * (L.card - 1) = H.vertexCount + r - 1 := by omega
      rw [heq]
      exact hTlower
    exact (Nat.le_sub_of_add_le hpay).trans hbase
  let K : Finset W := Kraw \ P
  have hKcard : H.vertexCount - L₂.card ≤ K.card := by
    have hsplit := Finset.card_sdiff_add_card_inter Kraw P
    have hinter : (Kraw ∩ P).card ≤ r + 1 := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hPcard
    dsimp only [K]
    rw [hL₂card]
    omega
  have hKA : K ⊆ A := by
    intro x hx
    have hxraw := (Finset.mem_sdiff.mp hx).1
    have hxnotP := (Finset.mem_sdiff.mp hx).2
    exact Finset.mem_sdiff.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hxraw).1).1, hxnotP⟩
  have hKB : K ⊆ B := by
    intro x hx
    have hxraw := (Finset.mem_sdiff.mp hx).1
    have hxnotP := (Finset.mem_sdiff.mp hx).2
    exact Finset.mem_sdiff.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hxraw).1).2, hxnotP⟩
  let U : Finset W := A ∪ B
  have hKU : K ⊆ U := hKA.trans Finset.subset_union_left
  have hUcard : H.vertexCount ≤ U.card :=
    hAcard.trans (Finset.card_le_card Finset.subset_union_left)
  have hKclique : Cᶜ.IsClique (K : Set W) := by
    intro x hx y hy hxy
    exact hblueCross x (hKA hx) y (hKB hy) hxy
  have hKcross : ∀ x ∈ K, ∀ y ∈ U, x ≠ y → Cᶜ.Adj x y := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hy with hyA | hyB
    · exact (hblueCross y hyA x (hKB hx) hxy.symm).symm
    · exact hblueCross x (hKA hx) y hyB hxy
  exact isContained_of_leaf_core_clique_cross H hconn hn L₂ hL₂ Cᶜ
    U K hKU hKclique hKcross hUcard hKcard

end Erdos570
