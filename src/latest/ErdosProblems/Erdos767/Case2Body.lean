import ErdosProblems.Erdos767.Case2TailData
import ErdosProblems.Erdos767.SplicePath

open Finset Set
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The upper handle interval, oriented from the lollipop tip back to the
second ear. -/
def Case2TailData.returnPath {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    G.Walk B.terminal D.E₂.b :=
  S.T.reverse.copy rfl D.b₂_eq.symm

lemma Case2TailData.returnPath_isPath {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    S.returnPath.IsPath := by
  simpa [Case2TailData.returnPath, Walk.support_copy] using S.T_isPath.reverse

lemma Case2TailData.returnPath_support_indices
    {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    ∀ v, v ∈ S.returnPath.support →
      ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧ B.tail.getVert t = v := by
  intro v hv
  apply S.T_support_indices
  simpa [Case2TailData.returnPath, Walk.support_copy, Walk.support_reverse] using hv

private lemma tail_index_eq_of_getVert_eq {B : BestLollipop G}
    {i j : ℕ} (hi : i ≤ B.tail.length) (hj : j ≤ B.tail.length)
    (h : B.tail.getVert i = B.tail.getVert j) : i = j :=
  B.tail_isPath.getVert_injOn hi hj h

/-- The open five-piece route in Case 2 is a simple path. -/
theorem Case2FanData.spliceBody_isPath
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D) :
    (Erdos767DiracCase2.spliceBody
      D.E₁.path S.A S.chord S.returnPath D.E₂.path).IsPath := by
  have hj₁le : j₁ ≤ B.tail.length := D.j₁_le_j₂.trans D.j₂_le
  have hj₁ltell : j₁ < B.tail.length :=
    lt_of_lt_of_le D.j₁_lt_j₂ D.j₂_le
  have hR₁A : ∀ w, w ∈ D.E₁.path.support → w ∈ S.A.support →
      w = D.E₁.b := by
    intro w hwR hwA
    obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
    have htell : t ≤ B.tail.length :=
      htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
    have hwY : w ∈ (B.tail.drop j₁).support := by
      rw [← htw]
      exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
        hj₁le htell).mpr hj₁t
    exact D.E₁.meet_B w hwR (List.mem_toFinset.mpr hwY)
  have hyR₁ : B.terminal ∉ D.E₁.path.support := by
    intro hyR
    have hyY : B.terminal ∈ (B.tail.drop j₁).support :=
      (B.tail.drop j₁).end_mem_support
    have hyb := D.E₁.meet_B B.terminal hyR (List.mem_toFinset.mpr hyY)
    have hget : B.tail.getVert B.tail.length = B.tail.getVert j₁ := by
      simpa [D.b₁_eq] using hyb
    have := tail_index_eq_of_getVert_eq (B := B) (i := B.tail.length)
      (j := j₁) le_rfl hj₁le hget
    omega
  have hyA : B.terminal ∉ S.A.support := by
    intro hyA
    obtain ⟨t, hj₁t, htj', hty⟩ := S.A_support_indices _ hyA
    have htell : t ≤ B.tail.length :=
      htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
    have hget : B.tail.getVert t = B.tail.getVert B.tail.length := by
      simpa using hty
    have heq := tail_index_eq_of_getVert_eq (B := B) htell le_rfl hget
    have hj'ltell : S.j' < B.tail.length := S.j'_lt.trans_le D.j₂_le
    omega
  have hpreU : ∀ w,
      w ∈ ((D.E₁.path.append S.A).concat S.chord).support →
      w ∈ S.returnPath.support → w = B.terminal := by
    intro w hwpre hwU
    obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
    rw [Walk.support_concat] at hwpre
    rcases List.mem_append.mp hwpre with hwRA | hwY
    · rw [Walk.mem_support_append_iff] at hwRA
      rcases hwRA with hwR | hwA
      · have hwY' : w ∈ (B.tail.drop j₁).support := by
          rw [← htw]
          exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
            hj₁le htell).mpr (D.j₁_le_j₂.trans hj₂t)
        have hwb := D.E₁.meet_B w hwR (List.mem_toFinset.mpr hwY')
        have hget : B.tail.getVert t = B.tail.getVert j₁ := by
          simpa [D.b₁_eq] using htw.trans hwb
        have heq := tail_index_eq_of_getVert_eq (B := B) htell hj₁le hget
        have hj₁ltj₂ := D.j₁_lt_j₂
        omega
      · obtain ⟨r, hj₁r, hrj', hrw⟩ := S.A_support_indices w hwA
        have hrle : r ≤ B.tail.length :=
          hrj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
        have hget : B.tail.getVert r = B.tail.getVert t := hrw.trans htw.symm
        have heq := tail_index_eq_of_getVert_eq (B := B) hrle htell hget
        have hrj₂ : r < D.j₂ := hrj'.trans_lt S.j'_lt
        omega
    · simpa using hwY
  have hallR₂ : ∀ w,
      w ∈ (((D.E₁.path.append S.A).concat S.chord).append
        S.returnPath).support →
      w ∈ D.E₂.path.reverse.support → w = D.E₂.b := by
    intro w hwAll hwR₂rev
    have hwR₂ : w ∈ D.E₂.path.support := by
      simpa [Walk.support_reverse] using hwR₂rev
    rw [Walk.mem_support_append_iff] at hwAll
    rcases hwAll with hwpre | hwU
    · rw [Walk.support_concat] at hwpre
      rcases List.mem_append.mp hwpre with hwRA | hwTip
      · rw [Walk.mem_support_append_iff] at hwRA
        rcases hwRA with hwR₁ | hwA
        · have hwF₁ := D.E₁.support_subset w hwR₁
          have hwF₂ := D.E₂.support_subset w hwR₂
          have hwroot := D.F.meet_eq_start hwF₁ hwF₂
          have hrootX : (BestLollipop.rootedCycle B).snd ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            have hxF : (BestLollipop.rootedCycle B).snd ∈
                (BestLollipop.rootedCycle B).support.toFinset :=
              List.mem_toFinset.mpr (BestLollipop.reference_start_mem_cycle B)
            rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
              (BestLollipop.rootedCycle_isCycle B)] at hxF
            exact hxF
          have ha₁ : w = D.E₁.a :=
            D.E₁.meet_A w hwR₁ (hwroot ▸ hrootX)
          have ha₂ : w = D.E₂.a :=
            D.E₂.meet_A w hwR₂ (hwroot ▸ hrootX)
          exact (D.a_ne hpos (ha₁.symm.trans ha₂)).elim
        · obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
          have htell : t ≤ B.tail.length :=
            htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
          have hwY : w ∈ (B.tail.drop j₁).support := by
            rw [← htw]
            exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
              hj₁le htell).mpr hj₁t
          exact D.E₂.meet_B w hwR₂ (List.mem_toFinset.mpr hwY)
      · have hwy : w = B.terminal := by simpa using hwTip
        have hyY : B.terminal ∈ (B.tail.drop j₁).support :=
          (B.tail.drop j₁).end_mem_support
        have hwY : w ∈ (B.tail.drop j₁).support.toFinset := by
          rw [hwy]
          exact List.mem_toFinset.mpr hyY
        exact D.E₂.meet_B w hwR₂ hwY
    · obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
      have hwY : w ∈ (B.tail.drop j₁).support := by
        rw [← htw]
        exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
          hj₁le htell).mpr (D.j₁_le_j₂.trans hj₂t)
      exact D.E₂.meet_B w hwR₂ (List.mem_toFinset.mpr hwY)
  exact spliceBody_isPath_of_successive_meets
    D.E₁.path S.A S.chord S.returnPath D.E₂.path
    D.E₁.isPath S.A_isPath S.returnPath_isPath D.E₂.isPath
    hR₁A hyR₁ hyA hpreU hallR₂

/-- Every cycle vertex of the open Case-2 body is one of its two endpoints. -/
theorem Case2FanData.spliceBody_meets_cycle
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D) :
    ∀ w,
      w ∈ (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = D.E₁.a ∨ w = D.E₂.a := by
  intro w hwBody hwCycle
  have hwCycleOrig : w ∈ B.cycle.support := by
    apply B.mem_cycle_of_mem_rotatedCycle
    exact List.mem_of_mem_dropLast (List.mem_toFinset.mp hwCycle)
  change w ∈ ((((D.E₁.path.append S.A).concat S.chord).append
    S.returnPath).append D.E₂.path.reverse).support at hwBody
  rw [Walk.mem_support_append_iff] at hwBody
  rcases hwBody with hwBody | hwR₂rev
  · rw [Walk.mem_support_append_iff] at hwBody
    rcases hwBody with hwPre | hwU
    · rw [Walk.support_concat] at hwPre
      rcases List.mem_append.mp hwPre with hwRA | hwy
      · rw [Walk.mem_support_append_iff] at hwRA
        rcases hwRA with hwR₁ | hwA
        · exact Or.inl (D.E₁.meet_A w hwR₁ hwCycle)
        · obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
          have htell : t ≤ B.tail.length :=
            htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
          have hwTail : w ∈ B.tail.support := by
            rw [← htw]
            exact B.tail.getVert_mem_support t
          have hwStart : w = B.start := B.cycle_tail_inter hwCycleOrig hwTail
          have hget : B.tail.getVert t = B.tail.getVert 0 := by
            simpa [hwStart] using htw
          have ht0 := tail_index_eq_of_getVert_eq (B := B) htell (by omega) hget
          have hj₁0 : j₁ = 0 := by omega
          have hbStart : D.E₁.b = B.start := by
            rw [D.b₁_eq, hj₁0]
            simp
          have hsCycle : B.start ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            have hsFull : B.start ∈
                (BestLollipop.rootedCycle B).support.toFinset :=
              List.mem_toFinset.mpr
                (BestLollipop.rootedCycle B).start_mem_support
            rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
              (BestLollipop.rootedCycle_isCycle B)] at hsFull
            exact hsFull
          have hbCycle : D.E₁.b ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            simpa [hbStart] using hsCycle
          have hba : D.E₁.b = D.E₁.a :=
            D.E₁.meet_A _ D.E₁.path.end_mem_support hbCycle
          exact Or.inl (hwStart.trans (hbStart.symm.trans hba))
      · have hyCycleOrig : B.terminal ∈ B.cycle.support := by
          have hwy' : w = B.terminal := by simpa using hwy
          rw [← hwy']
          exact hwCycleOrig
        exact (B.toLollipop.terminal_not_mem_cycle hpos hyCycleOrig).elim
    · obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
      have hwTail : w ∈ B.tail.support := by
        rw [← htw]
        exact B.tail.getVert_mem_support t
      have hwStart : w = B.start := B.cycle_tail_inter hwCycleOrig hwTail
      have hget : B.tail.getVert t = B.tail.getVert 0 := by
        simpa [hwStart] using htw
      have ht0 := tail_index_eq_of_getVert_eq (B := B) htell (by omega) hget
      have hj₂pos : 0 < D.j₂ := lt_of_le_of_lt (Nat.zero_le j₁) D.j₁_lt_j₂
      omega
  · have hwR₂ : w ∈ D.E₂.path.support := by
      simpa [Walk.support_reverse] using hwR₂rev
    exact Or.inr (D.E₂.meet_A w hwR₂ hwCycle)

/-- The selected long cycle arc and the open Case-2 body have disjoint tails,
the exact hypothesis needed to close them to a simple cycle. -/
theorem Case2FanData.longArc_disjoint_spliceBody
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D)
    (Q : G.Walk D.E₂.a D.E₁.a) (hQ : Q.IsPath)
    (hQcycle : ∀ v, v ∈ Q.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset) :
    Q.support.tail.Disjoint
      (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).support.tail := by
  rw [List.disjoint_left]
  intro w hwQ hwBody
  have hwQs : w ∈ Q.support := List.mem_of_mem_tail hwQ
  have hwBs : w ∈ (Erdos767DiracCase2.spliceBody
      D.E₁.path S.A S.chord S.returnPath D.E₂.path).support :=
    List.mem_of_mem_tail hwBody
  rcases D.spliceBody_meets_cycle hpos S w hwBs (hQcycle w hwQs) with
    hw1 | hw2
  · have hBodyPath := D.spliceBody_isPath hpos S
    have hstartNot : D.E₁.a ∉
        (Erdos767DiracCase2.spliceBody
          D.E₁.path S.A S.chord S.returnPath D.E₂.path).support.tail := by
      have hn := hBodyPath.support_nodup
      rw [← (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).cons_tail_support,
        List.nodup_cons] at hn
      exact hn.1
    exact hstartNot (hw1 ▸ hwBody)
  · have hstartNot : D.E₂.a ∉ Q.support.tail := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact hn.1
    exact hstartNot (hw2 ▸ hwQ)

end

end E767DiracBuild

