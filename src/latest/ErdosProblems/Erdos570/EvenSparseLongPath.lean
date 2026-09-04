/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseLongPath
import ErdosProblems.Erdos570.EvenEndpointPath

/-!
# The long suspended-path branch for even cycles

The compression and regrowth argument is parity-independent.  In the
terminal, endpoint-unextendable case, the unused vertices and the retained
long path directly form a forbidden complementary even cycle.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

def evenStarterInternal (r : ℕ) : ℕ := oddStarterInternal (r + 1)

theorem evenStarterInternal_add_two (r : ℕ) :
    evenStarterInternal r + 2 = 5 * (r + 3) := by
  unfold evenStarterInternal oddStarterInternal
  omega

theorem ramseyAt_evenBudget_of_long_suspendedPath
    {r B : ℕ} (H : GraphCode) [DecidableRel H.graph.Adj] (hH : NoIsolated H)
    (hconn : H.graph.Connected)
    {t : ℕ} {p : Fin (t + 2) → Fin H.vertexCount}
    (hp : IsSuspendedPath H.graph p)
    (htlong : 5 * (r + 3) ≤ t)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
        oddBudget B (r + 1) Q.edgeCount) :
    RamseyAt (cycleCode (2 * r + 4)) H
      (oddBudget B (r + 1) H.edgeCount) := by
  classical
  let ℓ := evenStarterInternal r
  have hℓt : ℓ + 1 ≤ t := by
    have hℓ := evenStarterInternal_add_two r
    omega
  have hℓtwo : ℓ + 2 = 5 * (r + 3) := evenStarterInternal_add_two r
  have htpos : 1 ≤ t := by omega
  let Q := compressSuspendedCode H.graph hp ℓ
  have hQno : NoIsolated Q :=
    compressSuspendedCode_noIsolated hp hH ℓ
  have hQedge := compressSuspendedCode_edgeCount_le hp htpos hℓt
  have hdelta : 1 ≤ t - (ℓ + 1) := by omega
  have hQlt : Q.edgeCount < H.edgeCount := by
    have hQedge' : Q.edgeCount + (t - (ℓ + 1)) ≤ H.edgeCount := by
      simpa only [Q, ← GraphCode.edgeCount_eq_card_edgeFinset] using hQedge
    omega
  have hQram := hIH Q hQno hQlt
  have hQbudget : graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
      oddBudget B (r + 1) H.edgeCount :=
    hQram.trans (oddBudget_mono hQlt.le)
  intro C
  let : DecidableRel C.Adj := Classical.decRel _
  by_cases hred : (cycleCode (2 * r + 4)).graph ⊑ C
  · exact Or.inl hred
  have hramQ : RamseyAt (cycleCode (2 * r + 4)) Q
      (oddBudget B (r + 1) H.edgeCount) :=
    ramseyAt_of_graphRamseyNumber_le hQbudget
  have hblueQ : Q.graph ⊑ Cᶜ := (hramQ C).resolve_left hred
  have hblueCompressed : compressSuspendedGraph H.graph hp ℓ ⊑ Cᶜ :=
    (recodeGraph_isContained_iff _ _).mp hblueQ
  obtain ⟨copy⟩ := hblueCompressed
  let A := compressedAvailable hp copy
  let D : SimpleGraph A := Cᶜ.induce (A : Set _)
  let base : Fin (ℓ + 2) → A := availableCopiedCompressedPath hp copy
  have hbase : IsEndpointPath D base :=
    availableCopiedCompressedPath_isEndpointPath hp copy
  have hbase0 : base 0 =
      ⟨copy (Sum.inl (suspendedLeft hp)),
        copiedCompressedPath_mem_available hp copy 0⟩ := by
    apply Subtype.ext
    exact copiedCompressedPath_zero hp copy
  have hbaseLast : base (Fin.last (ℓ + 1)) =
      ⟨copy (Sum.inl (suspendedRight hp)),
        (by
          rw [← copiedCompressedPath_last hp copy]
          exact copiedCompressedPath_mem_available hp copy (Fin.last (ℓ + 1)))⟩ := by
    apply Subtype.ext
    exact copiedCompressedPath_last hp copy
  have hℓle : ℓ ≤ t := by omega
  have hgrow := exists_endpointPath_extension_or_unextendable
    base hbase hbase0 hbaseLast (t - ℓ)
  have hsum : ℓ + (t - ℓ) = t := Nat.add_sub_of_le hℓle
  rw [hsum] at hgrow
  rcases hgrow with hfull | hstop
  · obtain ⟨q, hq, hq0, hqlast⟩ := hfull
    let qW : Fin (t + 2) → Fin (oddBudget B (r + 1) H.edgeCount) :=
      fun i ↦ (q i).1
    have hqWinj : Function.Injective qW := by
      intro i j hij
      exact hq.injective (Subtype.ext hij)
    have hqWadj : ∀ i j : Fin (t + 2), i.val + 1 = j.val →
        Cᶜ.Adj (qW i) (qW j) := by
      intro i j hij
      exact hq.adj i j hij
    have hqWleft : qW 0 = copy (Sum.inl (suspendedLeft hp)) :=
      congrArg Subtype.val hq0
    have hqWright : qW (suspendedLastIndex t) =
        copy (Sum.inl (suspendedRight hp)) := by
      change (q (Fin.last (t + 1))).1 = _
      exact congrArg Subtype.val hqlast
    have hqWmem : ∀ i, qW i ∈ compressedAvailable hp copy :=
      fun i ↦ (q i).2
    have hfresh := available_path_fresh_from_retained hp copy qW hqWinj
      hqWmem hqWleft hqWright
    exact Or.inr (isContained_of_compressSuspended_copy_and_path hp copy qW
      hqWinj hqWadj hqWleft hqWright hfresh)
  · obtain ⟨n, hℓn, hnt, q, hq, _hq0, _hqlast, hmax⟩ := hstop
    let pathImage : Finset A := Finset.univ.image q
    let U : Finset A := Finset.univ \ pathImage
    have hpathImage : pathImage.card = n + 2 := by
      change (Finset.univ.image q).card = n + 2
      rw [Finset.card_image_of_injective _ hq.injective]
      simp
    have hUcardEq : U.card + (n + 2) = Fintype.card A := by
      have hsplit := Finset.card_sdiff_add_card_eq_card
        (show pathImage ⊆ (Finset.univ : Finset A) from Finset.subset_univ _)
      rw [hpathImage] at hsplit
      simpa [U] using hsplit
    have hpCard : t + 2 ≤ H.vertexCount := by
      simpa using Fintype.card_le_of_injective p hp.injective
    have hconnCard : H.vertexCount ≤ H.edgeCount + 1 := by
      simpa [GraphCode.edgeCount] using hconn.card_vert_le_card_edgeSet_add_one
    have hNlower : 2 * H.edgeCount + (r + 1) ≤
        oddBudget B (r + 1) H.edgeCount := by
      unfold oddBudget
      omega
    have hAcard : Fintype.card A =
        oddBudget B (r + 1) H.edgeCount - (H.vertexCount - t - 2) := by
      rw [Fintype.card_coe]
      change (compressedAvailable hp copy).card = _
      simpa using compressedAvailable_card hp copy
    have hUlarge : H.vertexCount ≤ U.card := by
      rw [hAcard] at hUcardEq
      omega
    have hrU : r + 2 ≤ U.card := by
      have : r + 2 ≤ H.vertexCount := by omega
      exact this.trans hUlarge
    have hcycleD : ¬ SimpleGraph.cycleGraph (2 * (r + 2)) ⊑ Dᶜ := by
      intro hcycle
      apply hred
      have hcomp : Dᶜ = C.induce (A : Set _) := by
        ext x y
        simp only [D, SimpleGraph.compl_adj, SimpleGraph.induce_adj]
        rw [Subtype.val_injective.ne_iff]
        constructor
        · rintro ⟨hxy, hnot⟩
          by_contra hn
          exact hnot ⟨hxy, hn⟩
        · intro h
          exact ⟨(fun hxy ↦ h.ne (congrArg Subtype.val hxy)),
            fun hn ↦ hn.2 h⟩
      rw [hcomp] at hcycle
      have hk : 2 * (r + 2) = 2 * r + 4 := by ring
      rw [hk] at hcycle
      exact hcycle.trans
        (SimpleGraph.Embedding.induce (G := C) (A : Set _)).isContained
    have hlongD : 5 * (r + 2) + 1 ≤ n + 2 := by
      have hbaseLength : 5 * (r + 3) ≤ ℓ + 2 := by rw [hℓtwo]
      omega
    have hout : ∀ x ∈ U, x ∉ Set.range q := by
      intro x hxU hxrange
      obtain ⟨i, rfl⟩ := hxrange
      have hqi : q i ∈ pathImage := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      exact (Finset.mem_sdiff.mp hxU).2 hqi
    have hsmall := endpointPath_outside_card_lt_of_evenCycle_free
      (G := D) (h := r + 2) (by omega) hq hmax hlongD hcycleD hout
    omega

end Erdos570
