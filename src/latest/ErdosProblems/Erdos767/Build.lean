import ErdosProblems.Erdos767.Aligned
import ErdosProblems.Erdos767.Lollipop
import ErdosProblems.Erdos767.NoConsecutive
import ErdosProblems.Erdos767.WalkIndex
import ErdosProblems.Erdos58.CycleArcs

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

lemma BestLollipop.neighbor_mem_cycle_or_tail (B : BestLollipop G)
    {w : V} (hw : G.Adj B.terminal w) :
    w ∈ B.cycle.support ∨ w ∈ B.tail.support := by
  by_contra hout
  push_neg at hout
  let L : Lollipop G :=
    { cycleBase := B.cycleBase
      cycle := B.cycle
      cycle_isCycle := B.cycle_isCycle
      start := B.start
      terminal := w
      tail := B.tail.concat hw
      tail_isPath := B.tail_isPath.concat hout.2 hw
      start_mem_cycle := B.start_mem_cycle
      cycle_tail_inter := by
        intro v hvC hvP
        simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hvP
        rcases hvP with hvP | rfl
        · exact B.cycle_tail_inter hvC hvP
        · exact (hout.1 hvC).elim }
  have hle := B.tail_maximal L rfl
  simp [L] at hle

/-- Rotate the longest cycle of a best lollipop to the handle attachment. -/
def BestLollipop.rootedCycle (B : BestLollipop G) : G.Walk B.start B.start :=
  B.cycle.rotate B.start B.start_mem_cycle

lemma BestLollipop.rootedCycle_isCycle (B : BestLollipop G) :
    (rootedCycle B).IsCycle :=
  B.cycle_isCycle.rotate B.start_mem_cycle

@[simp] lemma BestLollipop.rootedCycle_length (B : BestLollipop G) :
    (rootedCycle B).length = B.cycle.length := by
  simp [BestLollipop.rootedCycle]

lemma BestLollipop.rootedCycle_support_iff (B : BestLollipop G) (v : V) :
    v ∈ (rootedCycle B).support ↔ v ∈ B.cycle.support := by
  exact Walk.mem_support_rotate_iff _ _ _

lemma BestLollipop.rooted_meet (B : BestLollipop G) {v : V}
    (hvC : v ∈ (rootedCycle B).support) (hvP : v ∈ B.tail.support) :
    v = B.start := by
  exact B.cycle_tail_inter ((rootedCycle_support_iff B v).mp hvC) hvP

/-- Close the lollipop handle with either oriented arc from its attachment
to a cycle vertex adjacent to the tip. -/
lemma BestLollipop.exists_cycle_tail_append_arc (B : BestLollipop G)
    (htail : 0 < B.tail.length) {v : V}
    (hvC : v ∈ (rootedCycle B).support) (hvs : v ≠ B.start)
    (htv : G.Adj B.terminal v)
    (q : G.Walk B.start v) (hq : q.IsPath)
    (hqC : ∀ x, x ∈ q.support → x ∈ (rootedCycle B).support) :
    ∃ d : G.Walk B.start B.start,
      d.IsCycle ∧ d.length = B.tail.length + 1 + q.length := by
  have hvTail : v ∉ B.tail.support := by
    intro hv
    exact hvs (rooted_meet B hvC hv)
  let p : G.Walk B.start v := B.tail.concat htv
  have hp : p.IsPath := B.tail_isPath.concat hvTail htv
  have hdisj : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxq' : x ∈ q.support := by
      have : x ∈ q.reverse.support := List.mem_of_mem_tail hxq
      simpa [Walk.support_reverse] using this
    have hxC := hqC x hxq'
    have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
    simp only [p, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hxp'
    rcases hxp' with hxTail | rfl
    · have hxs : x = B.start := rooted_meet B hxC hxTail
      have hstartNot : B.start ∉ p.support.tail := by
        have hn := hp.support_nodup
        rw [← p.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hstartNot (hxs ▸ hxp)
    · have hvNot : x ∉ q.reverse.support.tail := by
        have hn := hq.reverse.support_nodup
        rw [← q.reverse.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hvNot hxq
  let d : G.Walk B.start B.start := p.append q.reverse
  have hd : d.IsCycle := by
    apply hp.isCycle_append hq.reverse hdisj
    left
    simp [p]
    omega
  refine ⟨d, hd, ?_⟩
  simp [d, p, Walk.length_append, Walk.length_concat]

/-- A subpath of a given route going from its last visit to `A` before its
first visit to `B`.  Its internal vertices avoid both endpoint blocks. -/
structure BlockEar {x y : V} (r : G.Walk x y) (A B : Finset V) where
  a : V
  b : V
  path : G.Walk a b
  isPath : path.IsPath
  a_mem : a ∈ A
  b_mem : b ∈ B
  support_subset : ∀ v, v ∈ path.support → v ∈ r.support
  meet_A : ∀ v, v ∈ path.support → v ∈ A → v = a
  meet_B : ∀ v, v ∈ path.support → v ∈ B → v = b

/-- Extract the last-`A`/first-`B` subpath of a simple route. -/
theorem exists_blockEar {x y : V} {r : G.Walk x y} (hr : r.IsPath)
    (A B : Finset V) (hx : x ∈ A) (hy : y ∈ B) :
    Nonempty (BlockEar r A B) := by
  have hB : {v ∈ B | v ∈ r.support}.Nonempty := by
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, r.end_mem_support⟩⟩
  obtain ⟨b, hbB, hbR, hbFirst⟩ :=
    r.exists_mem_support_forall_mem_support_imp_eq B hB
  let pre : G.Walk x b := r.takeUntil b hbR
  have hpre : pre.IsPath := hr.takeUntil hbR
  have hxpre : x ∈ pre.support := pre.start_mem_support
  have hA : {v ∈ A | v ∈ pre.reverse.support}.Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simpa [Walk.support_reverse] using hxpre
  obtain ⟨a, haA, haRev, haFirst⟩ :=
    pre.reverse.exists_mem_support_forall_mem_support_imp_eq A hA
  let qrev : G.Walk b a := pre.reverse.takeUntil a haRev
  let q : G.Walk a b := qrev.reverse
  have hq : q.IsPath := (hpre.reverse.takeUntil haRev).reverse
  refine ⟨{
    a := a
    b := b
    path := q
    isPath := hq
    a_mem := haA
    b_mem := hbB
    support_subset := ?_
    meet_A := ?_
    meet_B := ?_ }⟩
  · intro v hvq
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    have hvpreRev : v ∈ pre.reverse.support :=
      pre.reverse.support_takeUntil_subset_support haRev hvrev
    have hvpre : v ∈ pre.support := by
      simpa [Walk.support_reverse] using hvpreRev
    exact r.support_takeUntil_subset_support hbR hvpre
  · intro v hvq hvA
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    exact haFirst v hvA hvrev
  · intro v hvq hvB
    apply hbFirst v hvB
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    have hvpreRev : v ∈ pre.reverse.support :=
      pre.reverse.support_takeUntil_subset_support haRev hvrev
    have hvpre : v ∈ pre.support := by
      simpa [Walk.support_reverse] using hvpreRev
    exact hvpre

/-- The reference path used in the aligned-fan part of Dirac's lollipop
argument: open the rooted cycle at its first edge, then traverse the handle. -/
def BestLollipop.referencePath (B : BestLollipop G) :
    G.Walk (rootedCycle B).snd B.terminal :=
  (rootedCycle B).tail.append B.tail

lemma BestLollipop.referencePath_isPath (B : BestLollipop G) :
    (referencePath B).IsPath := by
  let C := rootedCycle B
  have hC : C.IsCycle := rootedCycle_isCycle B
  have hD : C.tail.IsPath := hC.isPath_tail
  apply E767AlignedAlt.isPath_append_of_disjoint_tail hD B.tail_isPath
  rw [List.disjoint_left]
  intro v hvC hvP
  have hvCycle : v ∈ C.support := by
    have hvC' : v ∈ C.support.tail := by
      rw [← C.support_tail_of_not_nil hC.not_nil]
      exact hvC
    exact List.tail_subset C.support hvC'
  have hvTail : v ∈ B.tail.support := List.mem_of_mem_tail hvP
  have hvr : v = B.start := rooted_meet B hvCycle hvTail
  subst v
  have hn := B.tail_isPath.support_nodup
  rw [← B.tail.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hvP

lemma BestLollipop.reference_start_mem_cycle (B : BestLollipop G) :
    (rootedCycle B).snd ∈ (rootedCycle B).support := by
  let C := rootedCycle B
  exact List.tail_subset C.support
    (C.snd_mem_tail_support (rootedCycle_isCycle B).not_nil)

lemma BestLollipop.tail_support_subset_reference (B : BestLollipop G) :
    ∀ v, v ∈ B.tail.support → v ∈ (referencePath B).support := by
  intro v hv
  rw [referencePath, Walk.mem_support_append_iff]
  exact Or.inr hv

/-- Alignment preserves the order from any common vertex to the terminal
vertex of the aligned path. -/
lemma aligned_idxOf_le_end {x y a b : V}
    {W : G.Walk x y} {R : G.Walk a b}
    (hW : W.IsPath) (hR : R.IsPath) (hal : E767AlignedAlt.Aligned W R)
    {v : V} (hvR : v ∈ R.support) (hvW : v ∈ W.support)
    (hbW : b ∈ W.support) :
    W.support.idxOf v ≤ W.support.idxOf b := by
  let rel : V → V → Prop := fun s t ↦
    W.support.idxOf s ≤ W.support.idxOf t
  have hpairW : W.support.Pairwise rel := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    let fi : Fin W.support.length := ⟨i, hi⟩
    let fj : Fin W.support.length := ⟨j, hj⟩
    dsimp [rel]
    change W.support.idxOf (W.support.get fi) ≤
      W.support.idxOf (W.support.get fj)
    rw [List.get_idxOf hW.support_nodup fi,
      List.get_idxOf hW.support_nodup fj]
    exact Nat.le_of_lt hij
  let L := R.support.filter fun w ↦ w ∈ W.support
  have hsub : L.Sublist W.support := by
    exact hal
  have hpairL : L.Pairwise rel := hpairW.sublist hsub
  have hvL : v ∈ L := by
    simp [L, hvR, hvW]
  have hbL : b ∈ L := by
    simp [L, R.end_mem_support, hbW]
  have hdecomp : R.support = R.support.dropLast ++ [b] := by
    simpa [R.getLast_support] using
      (List.dropLast_append_getLast R.support_ne_nil).symm
  let L₀ := R.support.dropLast.filter fun w ↦ w ∈ W.support
  have hLeq : L = L₀ ++ [b] := by
    change (R.support.filter fun w ↦ w ∈ W.support) =
      (R.support.dropLast.filter fun w ↦ w ∈ W.support) ++ [b]
    calc
      (R.support.filter fun w ↦ w ∈ W.support) =
          ((R.support.dropLast ++ [b]).filter fun w ↦ w ∈ W.support) := by
            exact congrArg (fun l : List V ↦
              l.filter fun w ↦ w ∈ W.support) hdecomp
      _ = (R.support.dropLast.filter fun w ↦ w ∈ W.support) ++ [b] := by
        rw [List.filter_append]
        simp [hbW]
  by_cases hvb : v = b
  · subst v
    exact le_rfl
  have hvL₀ : v ∈ L₀ := by
    rw [hLeq] at hvL
    simp only [List.mem_append, List.mem_singleton] at hvL
    exact hvL.resolve_right hvb
  have hpairAppend : (L₀ ++ [b]).Pairwise rel := by
    rw [← hLeq]
    exact hpairL
  exact (List.pairwise_append.mp hpairAppend).2.2 v hvL₀ b (by simp)

lemma BestLollipop.reference_idxOf_tail_getVert (B : BestLollipop G)
    {j : ℕ} (hj : j ≤ B.tail.length) :
    (referencePath B).support.idxOf (B.tail.getVert j) =
      (rootedCycle B).tail.length + j := by
  let D := (rootedCycle B).tail
  let W := referencePath B
  have hW : W.IsPath := referencePath_isPath B
  have hjW : D.length + j ≤ W.length := by
    simp [W, referencePath, D, Walk.length_append]
    omega
  have hget : W.getVert (D.length + j) = B.tail.getVert j := by
    simp [W, referencePath, D, Walk.getVert_append]
  rw [← hget]
  exact E767WalkIndex.path_idxOf_getVert hW hjW

lemma exists_tail_index_of_mem_drop {x y : V} (P : G.Walk x y)
    {j : ℕ} (hj : j ≤ P.length) {v : V}
    (hv : v ∈ (P.drop j).support) :
    ∃ t : ℕ, j ≤ t ∧ t ≤ P.length ∧ P.getVert t = v := by
  obtain ⟨k, hkv, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  refine ⟨j + k, by omega, ?_, ?_⟩
  · rw [Walk.drop_length] at hk
    omega
  · simpa [Walk.drop_getVert] using hkv

/-- The checked data extracted from the aligned fan in lollipop Case 2. -/
structure Case2FanData (B : BestLollipop G) (j₁ : ℕ) where
  j₁_min : ∀ i, i ∈ E767WalkIndex.endNeighborIndices B.tail → j₁ ≤ i
  F : E767AlignedAlt.AlignedFan
    (z := B.tail.getVert j₁) (BestLollipop.referencePath B)
  E₁ : BlockEar F.toZ (BestLollipop.rootedCycle B).support.dropLast.toFinset
    (B.tail.drop j₁).support.toFinset
  E₂ : BlockEar F.toY (BestLollipop.rootedCycle B).support.dropLast.toFinset
    (B.tail.drop j₁).support.toFinset
  b₁_eq : E₁.b = B.tail.getVert j₁
  j₂ : ℕ
  j₁_le_j₂ : j₁ ≤ j₂
  j₂_le : j₂ ≤ B.tail.length
  b₂_eq : E₂.b = B.tail.getVert j₂

theorem BestLollipop.exists_case2FanData
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length) :
    ∃ j₁ : ℕ, j₁ ∈ E767WalkIndex.endNeighborIndices B.tail ∧
      Nonempty (Case2FanData B j₁) := by
  let J := E767WalkIndex.endNeighborIndices B.tail
  have hJ : J.Nonempty := by
    let i := B.tail.length - 1
    refine ⟨i, ?_⟩
    rw [E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath]
    constructor
    · dsimp [i]
      omega
    · have hadj := B.tail.adj_getVert_succ (i := i) (by dsimp [i]; omega)
      have hi : i + 1 = B.tail.length := by dsimp [i]; omega
      rw [hi, B.tail.getVert_length] at hadj
      exact hadj.symm
  let j₁ := J.min' hJ
  have hj₁J : j₁ ∈ J := Finset.min'_mem J hJ
  have hj₁lt : j₁ < B.tail.length :=
    (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp hj₁J |>.1
  let z := B.tail.getVert j₁
  let W := referencePath B
  have hzTail : z ∈ B.tail.support := B.tail.getVert_mem_support j₁
  have hzW : z ∈ W.support := tail_support_subset_reference B z hzTail
  have hzy : z ≠ B.terminal := by
    intro hzy
    have hjend := (B.tail_isPath.getVert_eq_end_iff hj₁lt.le).mp hzy
    omega
  obtain ⟨F⟩ := E767AlignedAlt.exists_alignedFan hTwo W
    (referencePath_isPath B) hzW hzy
  let X := (rootedCycle B).support.dropLast.toFinset
  let Y := (B.tail.drop j₁).support.toFinset
  have hxX : (rootedCycle B).snd ∈ X := by
    have hxF : (rootedCycle B).snd ∈ (rootedCycle B).support.toFinset :=
      List.mem_toFinset.mpr (reference_start_mem_cycle B)
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      (rootedCycle_isCycle B)] at hxF
    exact hxF
  have hzY : z ∈ Y := by
    change z ∈ (B.tail.drop j₁).support.toFinset
    exact List.mem_toFinset.mpr (by simpa [z] using
      (B.tail.drop j₁).start_mem_support)
  have hyY : B.terminal ∈ Y := by
    exact List.mem_toFinset.mpr (B.tail.drop j₁).end_mem_support
  obtain ⟨E₁⟩ := exists_blockEar F.toZ_isPath X Y hxX hzY
  obtain ⟨E₂⟩ := exists_blockEar F.toY_isPath X Y hxX hyY
  have hE₁bY : E₁.b ∈ (B.tail.drop j₁).support :=
    List.mem_toFinset.mp E₁.b_mem
  obtain ⟨t₁, hj₁t₁, ht₁le, ht₁eq⟩ :=
    exists_tail_index_of_mem_drop B.tail hj₁lt.le hE₁bY
  have hE₁bF : E₁.b ∈ F.toZ.support :=
    E₁.support_subset E₁.b E₁.path.end_mem_support
  have hE₁bW : E₁.b ∈ W.support := by
    rw [← ht₁eq]
    exact tail_support_subset_reference B _ (B.tail.getVert_mem_support t₁)
  have hidx₁ := aligned_idxOf_le_end (referencePath_isPath B)
    F.toZ_isPath F.toZ_aligned hE₁bF hE₁bW hzW
  have ht₁j₁ : t₁ ≤ j₁ := by
    rw [← ht₁eq, reference_idxOf_tail_getVert B ht₁le,
      reference_idxOf_tail_getVert B hj₁lt.le] at hidx₁
    omega
  have ht₁ : t₁ = j₁ := by omega
  have hb₁ : E₁.b = B.tail.getVert j₁ := by
    rw [← ht₁eq, ht₁]
  have hE₂bY : E₂.b ∈ (B.tail.drop j₁).support :=
    List.mem_toFinset.mp E₂.b_mem
  obtain ⟨j₂, hj₁j₂, hj₂le, hb₂⟩ :=
    exists_tail_index_of_mem_drop B.tail hj₁lt.le hE₂bY
  refine ⟨j₁, hj₁J, ⟨{
    j₁_min := fun i hi ↦ Finset.min'_le J i hi
    F := F
    E₁ := E₁
    E₂ := E₂
    b₁_eq := hb₁
    j₂ := j₂
    j₁_le_j₂ := hj₁j₂
    j₂_le := hj₂le
    b₂_eq := hb₂.symm }⟩⟩

lemma Case2FanData.j₁_lt_j₂ {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) : j₁ < D.j₂ := by
  have hb₁F : D.E₁.b ∈ D.F.toZ.support :=
    D.E₁.support_subset _ D.E₁.path.end_mem_support
  have hb₂F : D.E₂.b ∈ D.F.toY.support :=
    D.E₂.support_subset _ D.E₂.path.end_mem_support
  by_contra h
  have hj : D.j₂ = j₁ :=
    Nat.le_antisymm (Nat.le_of_not_gt h) D.j₁_le_j₂
  have hbb : D.E₁.b = D.E₂.b := by
    rw [D.b₁_eq, D.b₂_eq, hj]
  have hbx : D.E₁.b = (BestLollipop.rootedCycle B).snd := by
    exact D.F.meet_eq_start hb₁F (hbb ▸ hb₂F)
  have hxTail : (BestLollipop.rootedCycle B).snd ∈ B.tail.support := by
    rw [← hbx, D.b₁_eq]
    exact B.tail.getVert_mem_support j₁
  have hxs : (BestLollipop.rootedCycle B).snd = B.start :=
    BestLollipop.rooted_meet B
      (BestLollipop.reference_start_mem_cycle B) hxTail
  have hadj := (BestLollipop.rootedCycle B).adj_snd
    (BestLollipop.rootedCycle_isCycle B).not_nil
  exact hadj.ne hxs.symm

end

end E767DiracBuild

