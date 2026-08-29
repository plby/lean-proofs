/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroStream
import ErdosProblems.Erdos599.AlternatingMacroProvenance
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Tagged edge provenance for the flattened macro stream

An edge in macro block `n` belongs either to the initial forward `Z` walk or
to the following reversed `Y` walk.  The cumulative block locator and the
offset within its block make that tag canonical, including when the same
ambient directed edge happens to belong to both warps.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace MacroChain

variable {Z Y : Set Γ.DPath} (C : MacroChain Z Y)

abbrev EdgeTag := Sum ℕ ℕ

noncomputable def streamEdgeBlock
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) : ℕ :=
  (C.streamBlocks hZ hY hZfin hYfin hroot).locateBlock k

noncomputable def streamEdgeOffset
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) : ℕ :=
  (C.streamBlocks hZ hY hZfin hYfin hroot).blockOffset k

noncomputable def streamEdgeTag
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) : EdgeTag :=
  let n := C.streamEdgeBlock hZ hY hZfin hYfin hroot k
  let j := C.streamEdgeOffset hZ hY hZfin hYfin hroot k
  if j < (C.zFinite hZfin n).walk.length then .inl n else .inr n

def edgeTagColour : EdgeTag → Direction
  | .inl _ => .forward
  | .inr _ => .backward

def edgeTagCarrier : EdgeTag → Γ.DPath
  | .inl n => (C.z n).1
  | .inr n => (C.y n).1

theorem streamEdgeBlock_eq_iff
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k n : ℕ) :
    C.streamEdgeBlock hZ hY hZfin hYfin hroot k = n ↔
      C.streamBoundary hZ hY hZfin hYfin hroot n ≤ k ∧
        k < C.streamBoundary hZ hY hZfin hYfin hroot (n + 1) := by
  exact (C.streamBlocks hZ hY hZfin hYfin hroot).locateBlock_eq_iff k n

theorem streamBoundary_add_streamEdgeOffset
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) :
    C.streamBoundary hZ hY hZfin hYfin hroot
        (C.streamEdgeBlock hZ hY hZfin hYfin hroot k) +
      C.streamEdgeOffset hZ hY hZfin hYfin hroot k = k := by
  exact (C.streamBlocks hZ hY hZfin hYfin hroot).boundary_add_blockOffset k

theorem streamEdgeBlock_mono
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {i j : ℕ} (hij : i ≤ j) :
    C.streamEdgeBlock hZ hY hZfin hYfin hroot i ≤
      C.streamEdgeBlock hZ hY hZfin hYfin hroot j := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  change B.locateBlock i ≤ B.locateBlock j
  by_contra hnot
  have hi := B.boundary_locateBlock_le i
  have hj := B.lt_boundary_succ_locateBlock j
  have hblock : B.locateBlock j + 1 ≤ B.locateBlock i := by omega
  have hb := B.boundary_strictMono.monotone hblock
  exact (Nat.not_lt_of_ge ((hb.trans hi).trans hij)) hj

theorem streamEdgeTag_convex
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hik : C.streamEdgeTag hZ hY hZfin hYfin hroot i =
      C.streamEdgeTag hZ hY hZfin hYfin hroot k) :
    C.streamEdgeTag hZ hY hZfin hYfin hroot j =
      C.streamEdgeTag hZ hY hZfin hYfin hroot i := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  let bi := C.streamEdgeBlock hZ hY hZfin hYfin hroot i
  let bj := C.streamEdgeBlock hZ hY hZfin hYfin hroot j
  let bk := C.streamEdgeBlock hZ hY hZfin hYfin hroot k
  let oi := C.streamEdgeOffset hZ hY hZfin hYfin hroot i
  let oj := C.streamEdgeOffset hZ hY hZfin hYfin hroot j
  let ok := C.streamEdgeOffset hZ hY hZfin hYfin hroot k
  have hbik : bi = bk := by
    have hbik' :
        C.streamEdgeBlock hZ hY hZfin hYfin hroot i =
          C.streamEdgeBlock hZ hY hZfin hYfin hroot k := by
      dsimp only [streamEdgeTag] at hik
      split at hik <;> split at hik <;> simp_all
    simpa [bi, bk] using hbik'
  have hbij : bi = bj := by
    apply Nat.le_antisymm
    · exact C.streamEdgeBlock_mono hZ hY hZfin hYfin hroot hij
    · rw [hbik]
      exact C.streamEdgeBlock_mono hZ hY hZfin hYfin hroot hjk
  have hoffij : oi ≤ oj := by
    have hi := C.streamBoundary_add_streamEdgeOffset hZ hY hZfin hYfin hroot i
    have hj := C.streamBoundary_add_streamEdgeOffset hZ hY hZfin hYfin hroot j
    change B.boundary bi + oi = i at hi
    change B.boundary bj + oj = j at hj
    rw [← hbij] at hj
    omega
  have hoffjk : oj ≤ ok := by
    have hj := C.streamBoundary_add_streamEdgeOffset hZ hY hZfin hYfin hroot j
    have hk := C.streamBoundary_add_streamEdgeOffset hZ hY hZfin hYfin hroot k
    change B.boundary bj + oj = j at hj
    change B.boundary bk + ok = k at hk
    rw [← hbik, hbij] at hk
    omega
  dsimp only [streamEdgeTag] at hik ⊢
  change (if oi < (C.zFinite hZfin bi).walk.length then Sum.inl bi else Sum.inr bi) =
    (if ok < (C.zFinite hZfin bk).walk.length then Sum.inl bk else Sum.inr bk) at hik
  change (if oj < (C.zFinite hZfin bj).walk.length then Sum.inl bj else Sum.inr bj) =
    (if oi < (C.zFinite hZfin bi).walk.length then Sum.inl bi else Sum.inr bi)
  rw [← hbik] at hik
  rw [← hbij]
  by_cases hi : oi < (C.zFinite hZfin bi).walk.length
  · have hk : ok < (C.zFinite hZfin bi).walk.length := by
      by_contra hk
      simp [hi, hk] at hik
    have hj : oj < (C.zFinite hZfin bi).walk.length := by omega
    simp [hi, hj]
  · have hk : ¬ok < (C.zFinite hZfin bi).walk.length := by
      intro hk
      simp [hi, hk] at hik
    have hj : ¬oj < (C.zFinite hZfin bi).walk.length := by omega
    simp [hi, hj]

/-- The same macro-block support, split at the colour boundary: the forward
support without its last vertex, followed by the complete reversed backward
support. -/
theorem support_blockWalk_colour_split
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (n : ℕ) :
    (C.blockWalk hZfin hYfin n).support =
      (C.zFinite hZfin n).walk.support.dropLast ++
        (C.yFinite hYfin n).walk.support.reverse := by
  let zs := (C.zFinite hZfin n).walk.support
  let ys := (C.yFinite hYfin n).walk.support
  have hzs : zs ≠ [] := (C.zFinite hZfin n).walk.support_ne_nil
  have hys : ys ≠ [] := (C.yFinite hYfin n).walk.support_ne_nil
  have hyr : ys.reverse ≠ [] := by simpa using hys
  have hzf : (C.zFinite hZfin n).finish = C.terminal n := by
    have h := C.z_terminal n
    rw [C.z_eq_zFinite hZfin n] at h
    exact Option.some.inj h
  have hyf : (C.yFinite hYfin n).finish = C.terminal n := by
    have h := C.y_terminal n
    rw [C.y_eq_yFinite hYfin n] at h
    exact Option.some.inj h
  have hhead : ys.reverse.head hyr = zs.getLast hzs := by
    rw [List.head_reverse]
    change (C.yFinite hYfin n).walk.support.getLast _ =
      (C.zFinite hZfin n).walk.support.getLast _
    rw [(C.yFinite hYfin n).walk.getLast_support,
      (C.zFinite hZfin n).walk.getLast_support, hyf, hzf]
  rw [C.support_blockWalk]
  change zs ++ ys.reverse.tail = zs.dropLast ++ ys.reverse
  calc
    zs ++ ys.reverse.tail =
        (zs.dropLast ++ [zs.getLast hzs]) ++ ys.reverse.tail := by
      rw [List.dropLast_append_getLast hzs]
    _ = zs.dropLast ++ (ys.reverse.head hyr :: ys.reverse.tail) := by
      rw [List.append_assoc]
      simp only [List.singleton_append]
      rw [hhead]
    _ = zs.dropLast ++ ys.reverse := by
      rw [List.cons_head_tail hyr]

theorem streamEdge_mem_forward
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ)
    (hcolour : edgeTagColour
      (C.streamEdgeTag hZ hY hZfin hYfin hroot k) = .forward) :
    (C.rawMacroVertex hZ hY hZfin hYfin hroot k,
      C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1)) ∈
        (C.edgeTagCarrier
          (C.streamEdgeTag hZ hY hZfin hYfin hroot k)).edgeSet := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  let n := C.streamEdgeBlock hZ hY hZfin hYfin hroot k
  let j := C.streamEdgeOffset hZ hY hZfin hYfin hroot k
  have hj : j < (C.zFinite hZfin n).walk.length := by
    change edgeTagColour
      (if j < (C.zFinite hZfin n).walk.length then .inl n else .inr n) =
        .forward at hcolour
    by_contra hnot
    simp [hnot, edgeTagColour] at hcolour
  have hk : k = C.streamBoundary hZ hY hZfin hYfin hroot n + j :=
    (C.streamBoundary_add_streamEdgeOffset
      hZ hY hZfin hYfin hroot k).symm
  have hjblock : j < B.edgeLength n := by
    have hlen : (C.zFinite hZfin n).walk.length < B.edgeLength n + 1 := by
      have htwo := B.length_pos n
      rw [B.edgeLength_add_one]
      change (C.zFinite hZfin n).walk.length <
        (C.blockWalk hZfin hYfin n).support.length
      rw [C.support_blockWalk_stream hZfin hYfin]
      rw [List.length_append, Walk.support_length_eq]
      omega
    omega
  have hraw0' := C.rawMacroVertex_block_interval
    hZ hY hZfin hYfin hroot n j (Nat.le_of_lt hjblock)
  have hraw1' := C.rawMacroVertex_block_interval
    hZ hY hZfin hYfin hroot n (j + 1) (by omega : j + 1 ≤ B.edgeLength n)
  have hraw0 := hraw0'
  rw [← hk] at hraw0
  have hraw1 := hraw1'
  rw [show C.streamBoundary hZ hY hZfin hYfin hroot n + (j + 1) =
      k + 1 by omega] at hraw1
  have hj0 : j < (C.zFinite hZfin n).walk.support.length := by
    rw [Walk.support_length_eq]
    omega
  have hj1 : j + 1 < (C.zFinite hZfin n).walk.support.length := by
    rw [Walk.support_length_eq]
    omega
  have hzedge :
      ((C.zFinite hZfin n).walk.support[j]'hj0,
        (C.zFinite hZfin n).walk.support[j + 1]'hj1) ∈
          (C.zFinite hZfin n).walk.edgeSet := by
    rw [Walk.mem_edgeSet_iff_exists_getVert]
    exact ⟨j, hj, hj1, rfl⟩
  have hpair :
      (C.rawMacroVertex hZ hY hZfin hYfin hroot k,
        C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1)) =
      ((C.zFinite hZfin n).walk.support[j]'hj0,
        (C.zFinite hZfin n).walk.support[j + 1]'hj1) := by
    apply Prod.ext
    · change C.rawMacroVertex hZ hY hZfin hYfin hroot k = _
      calc
        _ = (C.blockWalk hZfin hYfin n).support.get _ := hraw0
        _ = ((C.zFinite hZfin n).walk.support ++
              (C.yFinite hYfin n).walk.support.dropLast.reverse).get
              ⟨j, by rw [List.length_append]; omega⟩ :=
          OmegaBlocks.listGet_congr _ _
            (C.support_blockWalk_stream hZfin hYfin n) rfl
        _ = _ := by
          rw [List.get_eq_getElem, List.getElem_append_left hj0]
    · change C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1) = _
      calc
        _ = (C.blockWalk hZfin hYfin n).support.get _ := hraw1
        _ = ((C.zFinite hZfin n).walk.support ++
              (C.yFinite hYfin n).walk.support.dropLast.reverse).get
              ⟨j + 1, by rw [List.length_append]; omega⟩ :=
          OmegaBlocks.listGet_congr _ _
            (C.support_blockWalk_stream hZfin hYfin n) rfl
        _ = _ := by
          rw [List.get_eq_getElem, List.getElem_append_left hj1]
  change (C.rawMacroVertex hZ hY hZfin hYfin hroot k,
      C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1)) ∈
    (C.edgeTagCarrier
      (if j < (C.zFinite hZfin n).walk.length then .inl n else .inr n)).edgeSet
  rw [if_pos hj]
  change _ ∈ (C.z n).1.edgeSet
  rw [C.z_eq_zFinite hZfin n]
  exact hpair ▸ hzedge

theorem streamEdge_mem_backward
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ)
    (hcolour : edgeTagColour
      (C.streamEdgeTag hZ hY hZfin hYfin hroot k) = .backward) :
    (C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1),
      C.rawMacroVertex hZ hY hZfin hYfin hroot k) ∈
        (C.edgeTagCarrier
          (C.streamEdgeTag hZ hY hZfin hYfin hroot k)).edgeSet := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  let n := C.streamEdgeBlock hZ hY hZfin hYfin hroot k
  let j := C.streamEdgeOffset hZ hY hZfin hYfin hroot k
  let lz := (C.zFinite hZfin n).walk.length
  let r := j - lz
  have hj : ¬lz > j := by
    change edgeTagColour (if j < lz then .inl n else .inr n) = .backward at hcolour
    intro h
    simp [h, edgeTagColour] at hcolour
  have hlzj : lz ≤ j := Nat.le_of_not_gt hj
  have hk : k = C.streamBoundary hZ hY hZfin hYfin hroot n + j :=
    (C.streamBoundary_add_streamEdgeOffset
      hZ hY hZfin hYfin hroot k).symm
  have hjblock : j < B.edgeLength n := by
    exact B.blockOffset_lt_edgeLength k
  have hraw0' := C.rawMacroVertex_block_interval
    hZ hY hZfin hYfin hroot n j (Nat.le_of_lt hjblock)
  have hraw1' := C.rawMacroVertex_block_interval
    hZ hY hZfin hYfin hroot n (j + 1) (by omega : j + 1 ≤ B.edgeLength n)
  have hraw0 := hraw0'
  rw [← hk] at hraw0
  have hraw1 := hraw1'
  rw [show C.streamBoundary hZ hY hZfin hYfin hroot n + (j + 1) =
      k + 1 by omega] at hraw1
  have hzdrop : (C.zFinite hZfin n).walk.support.dropLast.length = lz := by
    simp [lz, Walk.support_length_eq]
  have hblockLen :
      (C.blockWalk hZfin hYfin n).support.length =
        (C.zFinite hZfin n).walk.support.dropLast.length +
          (C.yFinite hYfin n).walk.support.reverse.length := by
    rw [C.support_blockWalk_colour_split hZfin hYfin n, List.length_append]
  have hj1block : j + 1 < (C.blockWalk hZfin hYfin n).support.length := by
    have he := B.edgeLength_add_one n
    change B.edgeLength n + 1 =
      (C.blockWalk hZfin hYfin n).support.length at he
    omega
  have hr0 : r < (C.yFinite hYfin n).walk.support.reverse.length := by
    dsimp only [r]
    omega
  have hr1 : r + 1 < (C.yFinite hYfin n).walk.support.reverse.length := by
    dsimp only [r]
    omega
  have hrawY0 :
      C.rawMacroVertex hZ hY hZfin hYfin hroot k =
        (C.yFinite hYfin n).walk.support.reverse[r]'hr0 := by
    calc
      _ = (C.blockWalk hZfin hYfin n).support.get _ := hraw0
      _ = ((C.zFinite hZfin n).walk.support.dropLast ++
            (C.yFinite hYfin n).walk.support.reverse).get
            ⟨j, by rw [List.length_append, hzdrop]; omega⟩ :=
        OmegaBlocks.listGet_congr _ _
          (C.support_blockWalk_colour_split hZfin hYfin n) rfl
      _ = _ := by
        have happ :
            (C.zFinite hZfin n).walk.support.dropLast.length ≤ j := by
          omega
        rw [List.get_eq_getElem, List.getElem_append_right happ]
        congr 1
        dsimp only [r]
        omega
  have hrawY1 :
      C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1) =
        (C.yFinite hYfin n).walk.support.reverse[r + 1]'hr1 := by
    calc
      _ = (C.blockWalk hZfin hYfin n).support.get _ := hraw1
      _ = ((C.zFinite hZfin n).walk.support.dropLast ++
            (C.yFinite hYfin n).walk.support.reverse).get
            ⟨j + 1, by rw [List.length_append, hzdrop]; omega⟩ :=
        OmegaBlocks.listGet_congr _ _
          (C.support_blockWalk_colour_split hZfin hYfin n) rfl
      _ = _ := by
        have happ :
            (C.zFinite hZfin n).walk.support.dropLast.length ≤ j + 1 := by
          omega
        rw [List.get_eq_getElem, List.getElem_append_right happ]
        congr 1
        dsimp only [r]
        omega
  have hry : r < (C.yFinite hYfin n).walk.length := by
    rw [List.length_reverse, Walk.support_length_eq] at hr1
    omega
  have hrevEdge :
      ((C.yFinite hYfin n).walk.support.reverse[r]'hr0,
        (C.yFinite hYfin n).walk.support.reverse[r + 1]'hr1) ∈
          (C.yFinite hYfin n).reverse.edgeSet := by
    change ((C.yFinite hYfin n).walk.support.reverse[r]'hr0,
        (C.yFinite hYfin n).walk.support.reverse[r + 1]'hr1) ∈
      (C.yFinite hYfin n).reverse.walk.edgeSet
    rw [Walk.mem_edgeSet_iff_exists_getVert]
    refine ⟨r, ?_, ?_, ?_⟩
    · change r < (C.yFinite hYfin n).walk.reverse.length
      simpa using hry
    · simpa [FinitePath.reverse] using hr1
    · simp [FinitePath.reverse]
  have hyedge :
      ((C.yFinite hYfin n).walk.support.reverse[r + 1]'hr1,
        (C.yFinite hYfin n).walk.support.reverse[r]'hr0) ∈
          (C.yFinite hYfin n).edgeSet :=
    (_root_.Erdos599.Alternating.SwitchingCore.FinitePath.mem_edgeSet_reverse_iff
      (C.yFinite hYfin n)).mp hrevEdge
  change (C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1),
      C.rawMacroVertex hZ hY hZfin hYfin hroot k) ∈
    (C.edgeTagCarrier (if j < lz then .inl n else .inr n)).edgeSet
  rw [if_neg hj]
  change _ ∈ (C.y n).1.edgeSet
  rw [C.y_eq_yFinite hYfin n]
  simpa [hrawY0, hrawY1] using hyedge

theorem edgeTagCarrier_injective_on_colour
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {a b : EdgeTag}
    (hcolour : edgeTagColour a = edgeTagColour b)
    (hcarrier : C.edgeTagCarrier a = C.edgeTagCarrier b) :
    a = b := by
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          have hij : i = j :=
            C.z_injective hZ hY hroot (Subtype.ext hcarrier)
          simpa [hij]
      | inr j => simp [edgeTagColour] at hcolour
  | inr i =>
      cases b with
      | inl j => simp [edgeTagColour] at hcolour
      | inr j =>
          have hij : i = j :=
            C.y_injective hZ hY hroot (Subtype.ext hcarrier)
          simpa [hij]

theorem edgeTagCarrier_mem_forward (a : EdgeTag)
    (hcolour : edgeTagColour a = .forward) :
    C.edgeTagCarrier a ∈ Z := by
  cases a with
  | inl n => exact (C.z n).2
  | inr n => simp [edgeTagColour] at hcolour

theorem edgeTagCarrier_mem_backward (a : EdgeTag)
    (hcolour : edgeTagColour a = .backward) :
    C.edgeTagCarrier a ∈ Y := by
  cases a with
  | inl n => simp [edgeTagColour] at hcolour
  | inr n => exact (C.y n).2

/-- The complete path-owner certificate for the raw macro stream. -/
noncomputable def streamEdgeProvenance
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) :
    (C.streamBlocks hZ hY hZfin hYfin hroot).EdgeProvenance Z Y EdgeTag where
  member := C.streamEdgeTag hZ hY hZfin hYfin hroot
  colour := edgeTagColour
  carrier := C.edgeTagCarrier
  carrier_injective_on_colour := by
    intro a b hc hp
    exact C.edgeTagCarrier_injective_on_colour hZ hY hroot hc hp
  carrier_mem_forward := C.edgeTagCarrier_mem_forward
  carrier_mem_backward := C.edgeTagCarrier_mem_backward
  edge_mem_forward := by
    intro k hc
    change (C.rawMacroVertex hZ hY hZfin hYfin hroot k,
      C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1)) ∈ _
    exact C.streamEdge_mem_forward hZ hY hZfin hYfin hroot k hc
  edge_mem_backward := by
    intro k hc
    change (C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1),
      C.rawMacroVertex hZ hY hZfin hYfin hroot k) ∈ _
    exact C.streamEdge_mem_backward hZ hY hZfin hYfin hroot k hc
  member_convex := by
    intro i j k hij hjk hik
    exact C.streamEdgeTag_convex hZ hY hZfin hYfin hroot hij hjk hik

/-- The uncovered root occurs in the flattened macro stream only at time
zero.  Warp disjointness first forces its block to be block zero; path
simplicity then forces its offset inside the forward carrier to be zero. -/
theorem rawMacroVertex_eq_root_iff
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) :
    C.rawMacroVertex hZ hY hZfin hYfin hroot k = (C.z 0).1.initial ↔
      k = 0 := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  let n := B.locateBlock k
  let j := B.blockOffset k
  constructor
  · intro hkroot
    have hjedge : j < B.edgeLength n := B.blockOffset_lt_edgeLength k
    have htime : B.boundary n + j = k := B.boundary_add_blockOffset k
    have hraw' := C.rawMacroVertex_block_interval
      hZ hY hZfin hYfin hroot n j (Nat.le_of_lt hjedge)
    change C.rawMacroVertex hZ hY hZfin hYfin hroot (B.boundary n + j) =
      (C.blockWalk hZfin hYfin n).support.get _ at hraw'
    have hraw := hraw'
    rw [htime] at hraw
    have hgetRoot :
        (C.blockWalk hZfin hYfin n).support.get
            ⟨j, by
              have htwo := B.length_pos n
              change 2 ≤ (C.blockWalk hZfin hYfin n).support.length at htwo
              have he := B.edgeLength_add_one n
              change B.edgeLength n + 1 =
                (C.blockWalk hZfin hYfin n).support.length at he
              omega⟩ =
          (C.z 0).1.initial := by
      exact hraw.symm.trans hkroot
    have hmemBlock :
        (C.z 0).1.initial ∈ (C.blockWalk hZfin hYfin n).support := by
      rw [← hgetRoot]
      exact List.get_mem _ _
    have hzy := C.mem_z_or_y_of_mem_blockWalk_stream hZfin hYfin hmemBlock
    have hmemZ : (C.z 0).1.initial ∈ (C.z n).1.support := by
      rcases hzy with hz | hy
      · exact hz
      · exfalso
        apply hroot
        rw [DWeb.mem_vertexSet]
        exact ⟨(C.y n).1, (C.y n).2, hy⟩
    have hn : n = 0 := by
      apply C.z_injective hZ hY hroot
      apply Subtype.ext
      exact DWeb.IsWarp.eq_of_mem_support hZ (C.z n).2 (C.z 0).2 hmemZ
        (C.z 0).1.initial_mem_support
    have hsplitLen :
        ((C.zFinite hZfin n).walk.support ++
          (C.yFinite hYfin n).walk.support.dropLast.reverse).length =
        (C.blockWalk hZfin hYfin n).support.length := by
      exact congrArg List.length
        (C.support_blockWalk_stream hZfin hYfin n).symm
    have hgetSplit :
        ((C.zFinite hZfin n).walk.support ++
          (C.yFinite hYfin n).walk.support.dropLast.reverse).get
            ⟨j, by
              have he := B.edgeLength_add_one n
              change B.edgeLength n + 1 =
                (C.blockWalk hZfin hYfin n).support.length at he
              omega⟩ =
          (C.z 0).1.initial := by
      calc
        _ = (C.blockWalk hZfin hYfin n).support.get
              ⟨j, by
                have he := B.edgeLength_add_one n
                change B.edgeLength n + 1 =
                  (C.blockWalk hZfin hYfin n).support.length at he
                omega⟩ :=
          OmegaBlocks.listGet_congr _ _
            (C.support_blockWalk_stream hZfin hYfin n).symm rfl
        _ = _ := hgetRoot
    have hjz : j < (C.zFinite hZfin n).walk.support.length := by
      by_contra hnot
      have hle : (C.zFinite hZfin n).walk.support.length ≤ j :=
        Nat.le_of_not_gt hnot
      rw [List.get_eq_getElem, List.getElem_append_right hle] at hgetSplit
      have hmemRev : (C.z 0).1.initial ∈
          (C.yFinite hYfin n).walk.support.dropLast.reverse := by
        rw [← hgetSplit]
        exact List.getElem_mem _
      have hmemYFinite : (C.z 0).1.initial ∈
          (C.yFinite hYfin n).walk.support := by
        apply List.mem_of_mem_dropLast
        simpa using hmemRev
      apply hroot
      rw [DWeb.mem_vertexSet]
      refine ⟨(C.y n).1, (C.y n).2, ?_⟩
      rw [C.y_eq_yFinite hYfin n]
      exact hmemYFinite
    have hgetZ :
        (C.zFinite hZfin n).walk.support[j]'hjz = (C.z 0).1.initial := by
      rw [List.get_eq_getElem, List.getElem_append_left hjz] at hgetSplit
      exact hgetSplit
    have hzstart : (C.zFinite hZfin n).start = (C.z n).1.initial := by
      exact congrArg Path.initial (C.z_eq_zFinite hZfin n).symm
    have hzero :
        (C.zFinite hZfin n).walk.support[0]'
            (List.length_pos_iff.mpr (C.zFinite hZfin n).walk.support_ne_nil) =
          (C.z n).1.initial := by
      exact (List.getElem_zero _).trans
        ((C.zFinite hZfin n).walk.head_support.trans hzstart)
    have hgetEq :
        (C.zFinite hZfin n).walk.support[j]'hjz =
          (C.zFinite hZfin n).walk.support[0]'
            (List.length_pos_iff.mpr (C.zFinite hZfin n).walk.support_ne_nil) := by
      rw [hgetZ, hzero, hn]
    have hj0 : j = 0 :=
      (C.zFinite hZfin n).isPath.getElem_inj_iff.mp hgetEq
    rw [hn, hj0] at htime
    simpa [OmegaBlocks.boundary] using htime.symm
  · rintro rfl
    have hboundary := C.rawMacroVertex_boundary
      hZ hY hZfin hYfin hroot 0
    simpa [streamBoundary, OmegaBlocks.boundary] using hboundary

theorem rawMacroVertex_root_unique
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ)
    (hk : C.rawMacroVertex hZ hY hZfin hYfin hroot k =
      C.rawMacroVertex hZ hY hZfin hYfin hroot 0) :
    k = 0 := by
  apply (C.rawMacroVertex_eq_root_iff hZ hY hZfin hYfin hroot k).mp
  rw [hk]
  exact (C.rawMacroVertex_eq_root_iff hZ hY hZfin hYfin hroot 0).mpr rfl

end MacroChain

end Alternating
end Erdos599
