/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceTheorem66Case1
import ErdosProblems.Erdos916.AHTSourceTheorem66Case3CardDeleted

/-!
# Deleted-centre adapters for AHT Theorem 6.6

The Watkins--Mesner splitter used in Theorem 6.6 lives in `G - center`.
This file contains the type-safe passage from its subtype-valued terminal
components to the ambient objects consumed by claims (3), (6), and Lemma
6.4.  In particular, no splitter on `G` itself is introduced.
-/

namespace Erdos916

open _root_.SimpleGraph
open AHTClaim3CardinalityCertificateDeleted

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## A generic terminal-component adapter -/

/-- Map one terminal component of a splitter in `G - center` to the local
ambient certificate used in AHT claim (6).  The last hypothesis is exactly
the centre-neighbour calculation; the three specializations below derive it
from the three pairwise-disjoint terminal components. -/
noncomputable def ahtTerminalComponentLocal_of_deleted
    {center : V}
    {part aSet bSet : Finset {v : V // v ≠ center}}
    {terminal boundaryA boundaryB : {v : V // v ≠ center}}
    (hcomponent : IsComponentAfterDeleting (deleteVertex G center)
      (aSet ∪ bSet) part)
    (hterminal : terminal ∈ part)
    (hattA : IsUniqueAttachment (deleteVertex G center) part aSet boundaryA)
    (hattB : IsUniqueAttachment (deleteVertex G center) part bSet boundaryB)
    (hAB : Disjoint aSet bSet)
    (hcenterAdj : G.Adj center terminal.1)
    (hcenterUnique : ∀ w ∈ part, G.Adj w.1 center → w = terminal) :
    AHTTerminalComponentLocal G where
  part := ahtDeletedFinsetVal part
  terminal := terminal.1
  boundaryA := boundaryA.1
  boundaryB := boundaryB.1
  center := center
  terminal_mem := val_mem_ahtDeletedFinsetVal.mpr hterminal
  boundaryA_not_mem := by
    intro hmem
    have hpart : boundaryA ∈ part := val_mem_ahtDeletedFinsetVal.mp hmem
    exact Finset.disjoint_left.mp hcomponent.2.1 hpart
      (Finset.mem_union_left _ hattA.1)
  boundaryB_not_mem := by
    intro hmem
    have hpart : boundaryB ∈ part := val_mem_ahtDeletedFinsetVal.mp hmem
    exact Finset.disjoint_left.mp hcomponent.2.1 hpart
      (Finset.mem_union_right _ hattB.1)
  center_not_mem := center_not_mem_ahtDeletedFinsetVal part
  boundary_ne := by
    intro hval
    have hsub : boundaryA = boundaryB := Subtype.ext hval
    exact Finset.disjoint_left.mp hAB hattA.1 (hsub ▸ hattB.1)
  center_adj_terminal := hcenterAdj
  neighbor_location := by
    intro w q hw hWQ
    obtain ⟨w', hw'part, hw'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hw
    by_cases hqcenter : q = center
    · exact Or.inr (Or.inr (Or.inr hqcenter))
    · let q' : {v : V // v ≠ center} := ⟨q, hqcenter⟩
      have hdel : (deleteVertex G center).Adj w' q' :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hw'val] using hWQ)
      by_cases hqA : q' ∈ aSet
      · have heq := hattA.2.2 w' hw'part q' hqA hdel
        exact Or.inr (Or.inl (congrArg Subtype.val heq))
      · by_cases hqB : q' ∈ bSet
        · have heq := hattB.2.2 w' hw'part q' hqB hdel
          exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val heq)))
        · have hqsep : q' ∉ aSet ∪ bSet := by simp [hqA, hqB]
          have hqpart := hcomponent.2.2.2 w' hw'part q' hqsep hdel
          exact Or.inl (by
            change q ∈ ahtDeletedFinsetVal part
            exact val_mem_ahtDeletedFinsetVal.mpr hqpart)
  center_neighbor_eq_terminal := by
    intro w hw hWCenter
    obtain ⟨w', hw'part, hw'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hw
    have heq := hcenterUnique w' hw'part (by simpa [hw'val] using hWCenter)
    exact hw'val.symm.trans (congrArg Subtype.val heq)

/-! ## The three source terminal components -/

section TerminalComponents

variable {center : V} {x y z : {v : V // v ≠ center}}
variable (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)

namespace WatkinsMesnerSplitter

/-- The mapped `X` component, with `center` as its unique ambient centre
neighbour. -/
noncomputable def xTerminalLocal
    (hcx : G.Adj center x.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    AHTTerminalComponentLocal G :=
  ahtTerminalComponentLocal_of_deleted
    S.X_component S.x_mem_X S.X_A_attachment S.X_B_attachment
    S.A_disjoint_B hcx (by
      intro w hwX hwc
      rcases hcenterNeighbors hwc.symm with hx | hy | hz
      · exact Subtype.ext hx
      · have hwy : w = y := Subtype.ext hy
        exact False.elim (Finset.disjoint_left.mp S.X_disjoint_Y hwX
          (hwy ▸ S.y_mem_Y))
      · have hwz : w = z := Subtype.ext hz
        exact False.elim (Finset.disjoint_left.mp S.X_disjoint_Z hwX
          (hwz ▸ S.z_mem_Z)))

/-- The mapped `Y` component used by the corrected claim-(3) certificate. -/
noncomputable def yTerminalLocal
    (hcy : G.Adj center y.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    AHTTerminalComponentLocal G :=
  ahtTerminalComponentLocal_of_deleted
    S.Y_component S.y_mem_Y S.Y_A_attachment S.Y_B_attachment
    S.A_disjoint_B hcy (by
      intro w hwY hwc
      rcases hcenterNeighbors hwc.symm with hx | hy | hz
      · have hwx : w = x := Subtype.ext hx
        exact False.elim (Finset.disjoint_left.mp S.X_disjoint_Y
          (hwx ▸ S.x_mem_X) hwY)
      · exact Subtype.ext hy
      · have hwz : w = z := Subtype.ext hz
        exact False.elim (Finset.disjoint_left.mp S.Y_disjoint_Z hwY
          (hwz ▸ S.z_mem_Z)))

/-- The mapped `Z` component used by the corrected claim-(3) certificate. -/
noncomputable def zTerminalLocal
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    AHTTerminalComponentLocal G :=
  ahtTerminalComponentLocal_of_deleted
    S.Z_component S.z_mem_Z S.Z_A_attachment S.Z_B_attachment
    S.A_disjoint_B hcz (by
      intro w hwZ hwc
      rcases hcenterNeighbors hwc.symm with hx | hy | hz
      · have hwx : w = x := Subtype.ext hx
        exact False.elim (Finset.disjoint_left.mp S.X_disjoint_Z
          (hwx ▸ S.x_mem_X) hwZ)
      · have hwy : w = y := Subtype.ext hy
        exact False.elim (Finset.disjoint_left.mp S.Y_disjoint_Z
          (hwy ▸ S.y_mem_Y) hwZ)
      · exact Subtype.ext hz)

@[simp] theorem yTerminalLocal_part
    (hcy : G.Adj center y.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    (S.yTerminalLocal hcy hcenterNeighbors).part =
      ahtDeletedFinsetVal S.yPart := rfl

@[simp] theorem zTerminalLocal_part
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    (S.zTerminalLocal hcz hcenterNeighbors).part =
      ahtDeletedFinsetVal S.zPart := rfl

/-! ## The concrete `X` fragment -/

/-- The source fragment retained in the recursive graph `G_X`: its interior
is the mapped terminal component `X`, and its boundary is exactly
`{center,x_A,x_B}`. -/
noncomputable def xThreeFragment
    (hcx : G.Adj center x.1) : AHTThreeFragment G where
  verts := ahtDeletedFinsetVal S.xPart
  a := center
  b := S.xA.1
  c := S.xB.1
  ab := S.xA.2.symm
  ac := S.xB.2.symm
  bc := by
    intro hval
    have hsub : S.xA = S.xB := Subtype.ext hval
    exact Finset.disjoint_left.mp S.A_disjoint_B S.X_A_attachment.1
      (hsub ▸ S.X_B_attachment.1)
  boundary_disjoint := by
    apply Finset.disjoint_right.mpr
    intro q hqBoundary hqX
    have hqcenter : q ≠ center := by
      intro h
      exact center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hqX)
    let q' : {v : V // v ≠ center} := ⟨q, hqcenter⟩
    have hqX' : q' ∈ S.xPart :=
      val_mem_ahtDeletedFinsetVal.mp (by simpa [q'] using hqX)
    have hqcases : q = center ∨ q = S.xA.1 ∨ q = S.xB.1 := by
      simpa using hqBoundary
    rcases hqcases with h | h | h
    · exact hqcenter h
    · have hqA : q' ∈ S.aSet := by
        have hqsub : q' = S.xA :=
          Subtype.ext (by simpa [q'] using h)
        simpa [hqsub] using S.X_A_attachment.1
      exact Finset.disjoint_left.mp S.X_component.2.1 hqX'
        (Finset.mem_union_left _ hqA)
    · have hqB : q' ∈ S.bSet := by
        have hqsub : q' = S.xB :=
          Subtype.ext (by simpa [q'] using h)
        simpa [hqsub] using S.X_B_attachment.1
      exact Finset.disjoint_left.mp S.X_component.2.1 hqX'
        (Finset.mem_union_right _ hqB)
  nonempty := ⟨x.1, val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X⟩
  outside_nonempty := by
    have hyX : y ∉ S.xPart := by
      intro hy
      exact Finset.disjoint_left.mp S.X_disjoint_Y hy S.y_mem_Y
    have hyA : y ∉ S.aSet := by
      intro hy
      exact Finset.disjoint_left.mp S.Y_component.2.1 S.y_mem_Y
        (Finset.mem_union_left _ hy)
    have hyB : y ∉ S.bSet := by
      intro hy
      exact Finset.disjoint_left.mp S.Y_component.2.1 S.y_mem_Y
        (Finset.mem_union_right _ hy)
    have hyxA : y.1 ≠ S.xA.1 := by
      intro h
      have hysub : y = S.xA := Subtype.ext h
      exact hyA (by simpa [hysub] using S.X_A_attachment.1)
    have hyxB : y.1 ≠ S.xB.1 := by
      intro h
      have hysub : y = S.xB := Subtype.ext h
      exact hyB (by simpa [hysub] using S.X_B_attachment.1)
    refine ⟨y.1, Finset.mem_sdiff.mpr ⟨by simp, ?_⟩⟩
    simp [val_mem_ahtDeletedFinsetVal, hyX, y.2, hyxA, hyxB]
  boundary_exact := by
    intro q hqX
    constructor
    · rintro ⟨w, hwX, hqw⟩
      obtain ⟨w', hw'X, hw'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal hwX
      by_cases hqcenter : q = center
      · exact Or.inl hqcenter
      · let q' : {v : V // v ≠ center} := ⟨q, hqcenter⟩
        have hdel : (deleteVertex G center).Adj w' q' :=
          (deleteVertex_adj (G := G)).mpr (by simpa [hw'val] using hqw.symm)
        by_cases hqA : q' ∈ S.aSet
        · have heq := S.X_A_attachment.2.2 w' hw'X q' hqA hdel
          exact Or.inr (Or.inl (congrArg Subtype.val heq))
        · by_cases hqB : q' ∈ S.bSet
          · have heq := S.X_B_attachment.2.2 w' hw'X q' hqB hdel
            exact Or.inr (Or.inr (congrArg Subtype.val heq))
          · have hqsep : q' ∉ S.aSet ∪ S.bSet := by simp [hqA, hqB]
            have hq'X := S.X_component.2.2.2 w' hw'X q' hqsep hdel
            exact False.elim (hqX (val_mem_ahtDeletedFinsetVal.mpr hq'X))
    · intro hq
      rcases hq with rfl | hq | hq
      · exact ⟨x.1, val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X, hcx⟩
      · obtain ⟨w, hwX, hw⟩ := S.X_A_attachment.2.1
        exact ⟨w.1, val_mem_ahtDeletedFinsetVal.mpr hwX, by
          simpa [hq] using hw.symm⟩
      · obtain ⟨w, hwX, hw⟩ := S.X_B_attachment.2.1
        exact ⟨w.1, val_mem_ahtDeletedFinsetVal.mpr hwX, by
          simpa [hq] using hw.symm⟩

@[simp] theorem xThreeFragment_verts
    (hcx : G.Adj center x.1) :
    (S.xThreeFragment hcx).verts = ahtDeletedFinsetVal S.xPart := rfl

@[simp] theorem xThreeFragment_boundary
    (hcx : G.Adj center x.1) :
    (S.xThreeFragment hcx).boundaryFinset =
      {center, S.xA.1, S.xB.1} := rfl

/-- The centre boundary of `G_X` has exactly one neighbour in the retained
fragment, namely `x`.  Consequently the prepared graph never introduces a
fresh pin at boundary index `0`. -/
theorem xThreeFragment_not_needsFreshPin_zero
    (hcx : G.Adj center x.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    ¬(S.xThreeFragment hcx).NeedsFreshPin 0 := by
  let F := S.xThreeFragment hcx
  have hyX : y ∉ S.xPart := by
    intro hy
    exact Finset.disjoint_left.mp S.X_disjoint_Y hy S.y_mem_Y
  have hzX : z ∉ S.xPart := by
    intro hz
    exact Finset.disjoint_left.mp S.X_disjoint_Z hz S.z_mem_Z
  have hinside : F.insideNeighborFinset 0 = {x.1} := by
    ext q
    constructor
    · intro hq
      have hq' := Finset.mem_inter.mp hq
      have hqAdjF : G.Adj F.a q := by
        exact (G.mem_neighborFinset F.a q).mp hq'.1
      have hqAdj : G.Adj center q := by
        change G.Adj center q at hqAdjF
        exact hqAdjF
      have hqX : q ∈ ahtDeletedFinsetVal S.xPart := by
        simpa [F, AHTThreeFragment.insideNeighborFinset] using hq'.2
      rcases hcenterNeighbors hqAdj with h | h | h
      · simpa [h]
      · have : y ∈ S.xPart := by
          apply val_mem_ahtDeletedFinsetVal.mp
          simpa [h] using hqX
        exact False.elim (hyX this)
      · have : z ∈ S.xPart := by
          apply val_mem_ahtDeletedFinsetVal.mp
          simpa [h] using hqX
        exact False.elim (hzX this)
    · intro hq
      have hqx : q = x.1 := by simpa using hq
      subst q
      apply Finset.mem_inter.mpr
      exact ⟨by
          change x.1 ∈ G.neighborFinset center
          simpa using hcx,
        by simpa [F, AHTThreeFragment.insideNeighborFinset] using
          val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X⟩
  intro hneeds
  rw [AHTThreeFragment.NeedsFreshPin, hinside] at hneeds
  simpa using hneeds

/-! ## A tagged realization of the concrete replacement graph -/

end WatkinsMesnerSplitter

namespace ConcreteGX

noncomputable section

abbrev Fragment (hcx : G.Adj center x.1) := S.xThreeFragment hcx

abbrev RawVertex (hcx : G.Adj center x.1) :=
  (Fragment S hcx).PreparedVertex ⊕ Fin 2

/-- Four tags suffice: the first two are used for optional boundary pins in
the coarse cases, while the last two are the deliberately added false-twin
pair. -/
abbrev CodeVertex := V ⊕ Fin 4

def oldVertexEmbedding : V ↪ CodeVertex (V := V) :=
  Function.Embedding.inl

def Refined : Prop :=
  S.yPart.card = 1 ∧ S.zPart.card = 1 ∧ S.aSet.card = 3

instance : Decidable (Refined S) := by
  unfold Refined
  infer_instance

private theorem a_attachment_ne_of_card_three
    (hA : S.aSet.card = 3) :
    S.xA ≠ S.yA ∧ S.xA ≠ S.zA ∧ S.yA ≠ S.zA := by
  have hEq := S.A_eq
  constructor
  · intro hxy
    have hsub : S.aSet ⊆ ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxy] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yA, S.zA} : Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  constructor
  · intro hxz
    have hsub : S.aSet ⊆ ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yA, S.zA} : Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  · intro hyz
    have hsub : S.aSet ⊆ ({S.xA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hyz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.xA, S.zA} : Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega

private theorem yA_not_mem_fragment_base
    (hcx : G.Adj center x.1) (hA : S.aSet.card = 3) :
    S.yA.1 ∉ (Fragment S hcx).verts ∪
      ({center, S.xA.1, S.xB.1} : Finset V) := by
  have hne := a_attachment_ne_of_card_three S hA
  have hyX : S.yA ∉ S.xPart := by
    intro hy
    exact Finset.disjoint_left.mp S.X_component.2.1 hy
      (Finset.mem_union_left _ S.Y_A_attachment.1)
  have hyB : S.yA ≠ S.xB := by
    intro h
    exact Finset.disjoint_left.mp S.A_disjoint_B S.Y_A_attachment.1
      (h ▸ S.X_B_attachment.1)
  have hyxA : S.yA.1 ≠ S.xA.1 := by
    intro h
    exact hne.1 (Subtype.ext h.symm)
  have hyxB : S.yA.1 ≠ S.xB.1 := by
    intro h
    exact hyB (Subtype.ext h)
  simp [Fragment, val_mem_ahtDeletedFinsetVal, hyX, S.yA.2,
    hyxA, hyxB]

private theorem zA_not_mem_fragment_base
    (hcx : G.Adj center x.1) (hA : S.aSet.card = 3) :
    S.zA.1 ∉ (Fragment S hcx).verts ∪
      ({center, S.xA.1, S.xB.1} : Finset V) := by
  have hne := a_attachment_ne_of_card_three S hA
  have hzX : S.zA ∉ S.xPart := by
    intro hz
    exact Finset.disjoint_left.mp S.X_component.2.1 hz
      (Finset.mem_union_left _ S.Z_A_attachment.1)
  have hzB : S.zA ≠ S.xB := by
    intro h
    exact Finset.disjoint_left.mp S.A_disjoint_B S.Z_A_attachment.1
      (h ▸ S.X_B_attachment.1)
  have hzxA : S.zA.1 ≠ S.xA.1 := by
    intro h
    exact hne.2.1 (Subtype.ext h.symm)
  have hzxB : S.zA.1 ≠ S.xB.1 := by
    intro h
    exact hzB (Subtype.ext h)
  simp [Fragment, val_mem_ahtDeletedFinsetVal, hzX, S.zA.2,
    hzxA, hzxB]

private theorem freshPin_eq_one_or_two
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (i : (Fragment S hcx).FreshPin) :
    i.1 = (1 : Fin 3) ∨ i.1 = (2 : Fin 3) := by
  rcases i with ⟨i, hi⟩
  fin_cases i
  · exact False.elim (hnoZero hi)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Encoding of the two possible optional pins.  In the refined cardinality
case the unused ambient vertices `y_A,z_A` serve as their codes; in every
other case the first two external tags are used. -/
noncomputable def freshCode
    (hcx : G.Adj center x.1)
    (i : (Fragment S hcx).FreshPin) : CodeVertex (V := V) :=
  if h : Refined S then
    if i.1 = (1 : Fin 3) then .inl S.yA.1 else .inl S.zA.1
  else
    if i.1 = (1 : Fin 3) then .inr 0 else .inr 1

noncomputable def rawCode
    (hcx : G.Adj center x.1) :
    RawVertex S hcx → CodeVertex (V := V)
  | .inl (.inl p) => .inl p.1
  | .inl (.inr i) => freshCode S hcx i
  | .inr j => .inr ⟨j.1 + 2, by omega⟩

private theorem rawCode_injective
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    Function.Injective (rawCode S hcx) := by
  intro p q hpq
  rcases p with p | i <;> rcases q with q | j
  · rcases p with p | i <;> rcases q with q | j
    · have hpq' : p.1 = q.1 := Sum.inl.inj hpq
      exact congrArg Sum.inl (congrArg Sum.inl (Subtype.ext hpq'))
    · by_cases href : Refined S
      · have hA := href.2.2
        have hj := freshPin_eq_one_or_two S hcx hnoZero j
        rcases hj with hj | hj
        · have heq : p.1 = S.yA.1 := by
            simpa [rawCode, freshCode, href, hj] using hpq
          exact False.elim
            (yA_not_mem_fragment_base S hcx hA (heq ▸ p.2))
        · have heq : p.1 = S.zA.1 := by
            simpa [rawCode, freshCode, href, hj] using hpq
          exact False.elim
            (zA_not_mem_fragment_base S hcx hA (heq ▸ p.2))
      · have hj := freshPin_eq_one_or_two S hcx hnoZero j
        rcases hj with hj | hj <;>
          simp [rawCode, freshCode, href, hj] at hpq
    · by_cases href : Refined S
      · have hA := href.2.2
        have hi := freshPin_eq_one_or_two S hcx hnoZero i
        rcases hi with hi | hi
        · have heq : S.yA.1 = q.1 := by
            simpa [rawCode, freshCode, href, hi] using hpq
          exact False.elim
            (yA_not_mem_fragment_base S hcx hA (heq.symm ▸ q.2))
        · have heq : S.zA.1 = q.1 := by
            simpa [rawCode, freshCode, href, hi] using hpq
          exact False.elim
            (zA_not_mem_fragment_base S hcx hA (heq.symm ▸ q.2))
      · have hi := freshPin_eq_one_or_two S hcx hnoZero i
        rcases hi with hi | hi <;>
          simp [rawCode, freshCode, href, hi] at hpq
    · have hi := freshPin_eq_one_or_two S hcx hnoZero i
      have hj := freshPin_eq_one_or_two S hcx hnoZero j
      by_cases href : Refined S
      · have hne := a_attachment_ne_of_card_three S href.2.2
        rcases hi with hi | hi <;> rcases hj with hj | hj
        · exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext (hi.trans hj.symm)))
        · have : S.yA.1 = S.zA.1 := by
            simpa [rawCode, freshCode, href, hi, hj] using hpq
          exact False.elim (hne.2.2 (Subtype.ext this))
        · have : S.zA.1 = S.yA.1 := by
            simpa [rawCode, freshCode, href, hi, hj] using hpq
          exact False.elim (hne.2.2 (Subtype.ext this.symm))
        · exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext (hi.trans hj.symm)))
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext (hi.trans hj.symm)))
        · simp [rawCode, freshCode, href, hi, hj] at hpq
        · simp [rawCode, freshCode, href, hi, hj] at hpq
        · exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext (hi.trans hj.symm)))
  · rcases p with p | i
    · simp [rawCode] at hpq
    · have hi := freshPin_eq_one_or_two S hcx hnoZero i
      by_cases href : Refined S
      · rcases hi with hi | hi <;>
          simp [rawCode, freshCode, href, hi] at hpq
      · rcases hi with hi | hi <;>
          fin_cases j <;> simp [rawCode, freshCode, href, hi] at hpq
  · rcases q with q | j
    · simp [rawCode] at hpq
    · have hj := freshPin_eq_one_or_two S hcx hnoZero j
      by_cases href : Refined S
      · rcases hj with hj | hj <;>
          simp [rawCode, freshCode, href, hj] at hpq
      · rcases hj with hj | hj <;>
          fin_cases i <;> simp [rawCode, freshCode, href, hj] at hpq
  · have hij : i.1 = j.1 := by
      have : i.1 + 2 = j.1 + 2 := by
        exact congrArg Fin.val (Sum.inr.inj hpq)
      omega
    exact congrArg Sum.inr (Fin.ext hij)

noncomputable def rawCodeEmbedding
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    RawVertex S hcx ↪ CodeVertex (V := V) where
  toFun := rawCode S hcx
  inj' := rawCode_injective S hcx hnoZero

@[simp] theorem rawCodeEmbedding_apply
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (q : RawVertex S hcx) :
    rawCodeEmbedding S hcx hnoZero q = rawCode S hcx q := rfl

noncomputable def verts
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    Finset (CodeVertex (V := V)) :=
  Finset.univ.map (rawCodeEmbedding S hcx hnoZero)

noncomputable def decode
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (q : verts S hcx hnoZero) : RawVertex S hcx :=
  Classical.choose (Finset.mem_map.mp q.2)

private theorem decode_spec
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (q : verts S hcx hnoZero) :
    rawCode S hcx (decode S hcx hnoZero q) = q.1 := by
  exact (Classical.choose_spec (Finset.mem_map.mp q.2)).2

/-- The exact equivalence between the concrete replacement vertex type and
its tagged image. -/
noncomputable def rawEquivVerts
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    RawVertex S hcx ≃ verts S hcx hnoZero where
  toFun q := ⟨rawCode S hcx q,
    Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩
  invFun := decode S hcx hnoZero
  left_inv := by
    intro q
    apply (rawCode_injective S hcx hnoZero)
    exact decode_spec S hcx hnoZero _
  right_inv := by
    intro q
    exact Subtype.ext (decode_spec S hcx hnoZero q)

/-- `gxGraph` is not an abstract graph of the right cardinality: it is the
literal fragment replacement transported to the tagged image. -/
noncomputable def graph
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    SimpleGraph (verts S hcx hnoZero) :=
  (Fragment S hcx).replacementGraph.comap
    (rawEquivVerts S hcx hnoZero).symm

noncomputable def graphEquivReplacement
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    graph S hcx hnoZero ≃g (Fragment S hcx).replacementGraph where
  toEquiv := (rawEquivVerts S hcx hnoZero).symm
  map_rel_iff' := by intro p q; rfl

def yPrime : CodeVertex (V := V) := .inr 0
def zPrime : CodeVertex (V := V) := .inr 1
def xAPrime : CodeVertex (V := V) := .inr 2
def xBPrime : CodeVertex (V := V) := .inr 3

private theorem old_code_mem_cover_four
    (hcx : G.Adj center x.1)
    (p : (Fragment S hcx).BaseVertex) :
    rawCode S hcx (.inl (.inl p)) ∈
      (((ahtDeletedFinsetVal S.aSet ∪
          ahtDeletedFinsetVal S.bSet ∪
          ahtDeletedFinsetVal S.xPart ∪ {center}).map
          (oldVertexEmbedding (V := V)))) := by
  apply Finset.mem_map.mpr
  refine ⟨p.1, ?_, rfl⟩
  rcases Finset.mem_union.mp p.2 with hpX | hpBoundary
  · have hpX' : p.1 ∈ ahtDeletedFinsetVal S.xPart := by
      change p.1 ∈ ahtDeletedFinsetVal S.xPart at hpX
      exact hpX
    simp [hpX']
  · have hpCases : p.1 = center ∨ p.1 = S.xA.1 ∨ p.1 = S.xB.1 := by
      change p.1 ∈ ({center, S.xA.1, S.xB.1} : Finset V) at hpBoundary
      simpa using hpBoundary
    rcases hpCases with h | h | h
    · simp [h]
    · have hpA : p.1 ∈ ahtDeletedFinsetVal S.aSet := by
        rw [h]
        exact val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1
      simp [hpA]
    · have hpB : p.1 ∈ ahtDeletedFinsetVal S.bSet := by
        rw [h]
        exact val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1
      simp [hpB]

theorem verts_cover_four
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0) :
    verts S hcx hnoZero ⊆
      (((ahtDeletedFinsetVal S.aSet ∪
          ahtDeletedFinsetVal S.bSet ∪
          ahtDeletedFinsetVal S.xPart ∪ {center}).map
          (oldVertexEmbedding (V := V))) ∪
        {yPrime (V := V), zPrime (V := V),
          xAPrime (V := V), xBPrime (V := V)}) := by
  intro q hq
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hq
  rcases r with r | j
  · rcases r with p | i
    · exact Finset.mem_union_left _ (old_code_mem_cover_four S hcx p)
    · have hi := freshPin_eq_one_or_two S hcx hnoZero i
      by_cases href : Refined S
      · rcases hi with hi | hi
        · apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨S.yA.1, ?_, by simp [rawCode, freshCode, href, hi,
            oldVertexEmbedding]⟩
          simp [val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1]
        · apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨S.zA.1, ?_, by simp [rawCode, freshCode, href, hi,
            oldVertexEmbedding]⟩
          simp [val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1]
      · rcases hi with hi | hi
        · apply Finset.mem_union_right
          simp [rawCode, freshCode, href, hi, yPrime]
        · apply Finset.mem_union_right
          simp [rawCode, freshCode, href, hi, zPrime]
  · fin_cases j
    · apply Finset.mem_union_right
      simp [rawCode, xAPrime]
    · apply Finset.mem_union_right
      simp [rawCode, xBPrime]

private theorem old_code_mem_cover_large
    (hcx : G.Adj center x.1)
    (p : (Fragment S hcx).BaseVertex) :
    rawCode S hcx (.inl (.inl p)) ∈
      (((ahtDeletedFinsetVal S.xPart ∪
          {S.xA.1, S.xB.1, center}).map
          (oldVertexEmbedding (V := V)))) := by
  apply Finset.mem_map.mpr
  refine ⟨p.1, ?_, rfl⟩
  rcases Finset.mem_union.mp p.2 with hpX | hpBoundary
  · have hpX' : p.1 ∈ ahtDeletedFinsetVal S.xPart := by
      change p.1 ∈ ahtDeletedFinsetVal S.xPart at hpX
      exact hpX
    simp [hpX']
  · have hpCases : p.1 = center ∨ p.1 = S.xA.1 ∨ p.1 = S.xB.1 := by
      change p.1 ∈ ({center, S.xA.1, S.xB.1} : Finset V) at hpBoundary
      simpa using hpBoundary
    rcases hpCases with h | h | h <;> simp [h]

theorem verts_cover_of_large_terminal
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (hlarge : 2 ≤ S.yPart.card ∨ 2 ≤ S.zPart.card) :
    verts S hcx hnoZero ⊆
      (((ahtDeletedFinsetVal S.xPart ∪
          {S.xA.1, S.xB.1, center}).map
          (oldVertexEmbedding (V := V))) ∪
        {yPrime (V := V), zPrime (V := V),
          xAPrime (V := V), xBPrime (V := V)}) := by
  have hnref : ¬Refined S := by
    intro href
    rcases href with ⟨hy, hz, -⟩
    rcases hlarge with hlarge | hlarge <;> omega
  intro q hq
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hq
  rcases r with r | j
  · rcases r with p | i
    · exact Finset.mem_union_left _ (old_code_mem_cover_large S hcx p)
    · have hi := freshPin_eq_one_or_two S hcx hnoZero i
      rcases hi with hi | hi
      · apply Finset.mem_union_right
        simp [rawCode, freshCode, hnref, hi, yPrime]
      · apply Finset.mem_union_right
        simp [rawCode, freshCode, hnref, hi, zPrime]
  · fin_cases j
    · apply Finset.mem_union_right
      simp [rawCode, xAPrime]
    · apply Finset.mem_union_right
      simp [rawCode, xBPrime]

private theorem old_code_mem_cover_refined
    (hcx : G.Adj center x.1)
    (p : (Fragment S hcx).BaseVertex) :
    rawCode S hcx (.inl (.inl p)) ∈
      (((ahtDeletedFinsetVal S.aSet ∪
          ahtDeletedFinsetVal S.xPart ∪
          {S.xB.1, center}).map
          (oldVertexEmbedding (V := V)))) := by
  apply Finset.mem_map.mpr
  refine ⟨p.1, ?_, rfl⟩
  rcases Finset.mem_union.mp p.2 with hpX | hpBoundary
  · have hpX' : p.1 ∈ ahtDeletedFinsetVal S.xPart := by
      change p.1 ∈ ahtDeletedFinsetVal S.xPart at hpX
      exact hpX
    simp [hpX']
  · have hpCases : p.1 = center ∨ p.1 = S.xA.1 ∨ p.1 = S.xB.1 := by
      change p.1 ∈ ({center, S.xA.1, S.xB.1} : Finset V) at hpBoundary
      simpa using hpBoundary
    rcases hpCases with h | h | h
    · simp [h]
    · have hpA : p.1 ∈ ahtDeletedFinsetVal S.aSet := by
        rw [h]
        exact val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1
      simp [hpA]
    · simp [h]

theorem verts_cover_of_refined
    (hcx : G.Adj center x.1)
    (hnoZero : ¬(Fragment S hcx).NeedsFreshPin 0)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hA : S.aSet.card = 3) :
    verts S hcx hnoZero ⊆
      (((ahtDeletedFinsetVal S.aSet ∪
          ahtDeletedFinsetVal S.xPart ∪
          {S.xB.1, center}).map
          (oldVertexEmbedding (V := V))) ∪
        {xAPrime (V := V), xBPrime (V := V)}) := by
  have href : Refined S := ⟨hy, hz, hA⟩
  intro q hq
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hq
  rcases r with r | j
  · rcases r with p | i
    · exact Finset.mem_union_left _ (old_code_mem_cover_refined S hcx p)
    · have hi := freshPin_eq_one_or_two S hcx hnoZero i
      rcases hi with hi | hi
      · apply Finset.mem_union_left
        apply Finset.mem_map.mpr
        refine ⟨S.yA.1, ?_, by simp [rawCode, freshCode, href, hi,
          oldVertexEmbedding]⟩
        simp [val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1]
      · apply Finset.mem_union_left
        apply Finset.mem_map.mpr
        refine ⟨S.zA.1, ?_, by simp [rawCode, freshCode, href, hi,
          oldVertexEmbedding]⟩
        simp [val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1]
  · fin_cases j
    · apply Finset.mem_union_right
      simp [rawCode, xAPrime]
    · apply Finset.mem_union_right
      simp [rawCode, xBPrime]

/-- The corrected claim-(3) certificate for the literal `X` fragment
replacement.  All three cover fields are proved above from the tagged
realization; none is a cardinality assumption. -/
noncomputable def claim3Certificate
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (horiented : S.yA = S.zA → S.yB = S.zB) :
    AHTClaim3CardinalityCertificateDeleted G center x y z
      (CodeVertex (V := V)) := by
  let hnoZero := S.xThreeFragment_not_needsFreshPin_zero hcx hcenterNeighbors
  exact {
    splitter := S
    yLocal := S.yTerminalLocal hcy hcenterNeighbors
    zLocal := S.zTerminalLocal hcz hcenterNeighbors
    yLocal_part := rfl
    yLocal_terminal := rfl
    yLocal_boundaryA := rfl
    yLocal_boundaryB := rfl
    yLocal_center := rfl
    zLocal_part := rfl
    zLocal_terminal := rfl
    zLocal_boundaryA := rfl
    zLocal_boundaryB := rfl
    zLocal_center := rfl
    center_adj_x := hcx
    center_adj_y := hcy
    center_adj_z := hcz
    center_neighbor_location := hcenterNeighbors
    center_not_close := hnotClose
    oldVertex := oldVertexEmbedding (V := V)
    gxVerts := verts S hcx hnoZero
    gxGraph := graph S hcx hnoZero
    yPrime := yPrime (V := V)
    zPrime := zPrime (V := V)
    xAPrime := xAPrime (V := V)
    xBPrime := xBPrime (V := V)
    gx_cover_four := verts_cover_four S hcx hnoZero
    gx_cover_of_large_terminal := by
      intro hlarge
      exact verts_cover_of_large_terminal S hcx hnoZero hlarge
    gx_cover_of_singletons_A := by
      intro hy hz hA
      exact verts_cover_of_refined S hcx hnoZero hy hz hA
    oriented := horiented }

/-- The strict claim-(3) inequality transferred back from the tagged image
to the actual fragment replacement vertex type. -/
theorem replacement_card_lt
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hnotClose : ¬IsCloseToAHTTwin G center)
    (horiented : S.yA = S.zA → S.yB = S.zB)
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    Fintype.card (RawVertex S hcx) < Fintype.card V := by
  let hnoZero := S.xThreeFragment_not_needsFreshPin_zero hcx hcenterNeighbors
  let C := claim3Certificate S hcx hcy hcz hcenterNeighbors hnotClose horiented
  rw [Fintype.card_congr (rawEquivVerts S hcx hnoZero)]
  change Fintype.card C.GXVertex < Fintype.card V
  exact C.gx_card_lt hthree halmost

end

end ConcreteGX

namespace WatkinsMesnerSplitter

/-! ## The concrete claim-(7) classification -/

/-- Minimality gives two pairs in the concrete replacement.  One pair
avoiding the deliberately added double pins is either an ambient pair inside
`X`, or a pair of distinguished pins; the latter is exactly the two-gate
branch and forces `X` to be a singleton. -/
theorem xThreeFragment_singleton_or_twinPair
    (hcx : G.Adj center x.1)
    (T : TwoDisjointDegreeThreeFalseTwinPairs
      (S.xThreeFragment hcx).replacementGraph)
    (hthree : IsThreeConnected (S.xThreeFragment hcx).replacementGraph) :
    S.xPart.card = 1 ∨
      ∃ p ∈ ahtDeletedFinsetVal S.xPart,
        ∃ q ∈ ahtDeletedFinsetVal S.xPart, AHTTwinPair G p q := by
  let F := S.xThreeFragment hcx
  obtain ⟨p, q, hpq, hclass⟩ :=
    ahtDoublePinReplacement_twoPairs_classification (T := T)
  rcases hclass with hnonpin | hpin
  · right
    simpa [F] using
      F.exists_ambient_twinPair_of_replacement_old_nonpin
        hpq hnonpin.1 hnonpin.2.1
  · left
    have hpqNe : p ≠ q := fun heq ↦ hpq.falseTwins.1
      (congrArg Sum.inl heq)
    have hcard : F.verts.card = 1 := by
      rcases hpin.1 with rfl | rfl | rfl <;>
        rcases hpin.2.1 with rfl | rfl | rfl
      · exact (hpqNe rfl).elim
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact (hpqNe rfl).elim
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact F.verts_card_eq_one_of_pin_twinPair
          (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
      · exact (hpqNe rfl).elim
    simpa [F] using hcard

end WatkinsMesnerSplitter

end TerminalComponents

end Erdos916
