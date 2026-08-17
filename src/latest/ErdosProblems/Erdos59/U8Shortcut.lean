import ErdosProblems.Erdos59.U8Direct

/-!
# A direct wedge injection for the nondegenerate U8 charge

This file replaces the quadrilateral-component classification in the
nondegenerate half of FNV Lemma 8.1.  A path occurrence is encoded by its
oriented outside edge, followed by its varying middle vertex.  Hexagon
freeness makes this code injective.
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Erdos59

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

private theorem false_of_six_cycle_shortcut (hC6 : WalkC6Free G)
    {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hpair : [a, b, c, d, e, f].Nodup) : False := by
  let q : G.Walk a a :=
    .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  have hq : q.IsCycle := by
    simp only [q, Walk.cons_isCycle_iff]
    simp_all [Walk.isPath_def, List.nodup_cons, eq_comm]
  exact hC6 a q hq (by simp [q])

/-- A path occurrence belonging to a nondegenerate exceptional endpoint
pair. -/
abbrev NondegenerateOccurrence :=
  Σ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
    {p // p ∈ pathFiber G pi.1}

namespace NondegenerateOccurrence

variable {G}

def pair (o : NondegenerateOccurrence G) : EndpointPair V := o.1.1

def pair_mem (o : NondegenerateOccurrence G) :
    o.pair ∈ nondegenerateExceptionalPairs G := o.1.2

def path (o : NondegenerateOccurrence G) : Path3 G := o.2.1

def path_mem (o : NondegenerateOccurrence G) :
    o.path ∈ pathFiber G o.pair := o.2.2

noncomputable def centre (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  nondegenerateStarCentre G hC6 o.pair o.pair_mem

def onLeft (hC6 : WalkC6Free G) (o : NondegenerateOccurrence G) : Prop :=
  nondegenerateStarOnLeft G hC6 o.pair o.pair_mem

noncomputable def outside (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.pair.1.1 else o.pair.1.2

noncomputable def far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.pair.1.2 else o.pair.1.1

noncomputable def varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.path.vertex 2 else o.path.vertex 1

theorem varying_mem (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.varying hC6 ∈
      nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [varying, onLeft, if_pos hl, nondegenerateOtherMiddles, if_pos hl]
    exact Finset.mem_image.mpr ⟨o.path, o.path_mem, rfl⟩
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [varying, onLeft, if_neg hl, nondegenerateOtherMiddles, if_neg hl]
    exact Finset.mem_image.mpr ⟨o.path, o.path_mem, rfl⟩

theorem centre_mem_base (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.centre hC6 ∈ nondegenerateBaseSide G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [centre, nondegenerateBaseSide, if_pos hl]
    simp
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [centre, nondegenerateBaseSide, if_neg hl]
    simp

theorem far_mem_base (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.far hC6 ∈ nondegenerateBaseSide G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [far, onLeft, if_pos hl, nondegenerateBaseSide, if_pos hl]
    simp
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [far, onLeft, if_neg hl, nondegenerateBaseSide, if_neg hl]
    simp

theorem centre_adj_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) {x : V}
    (hx : x ∈ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem) :
    G.Adj (o.centre hC6) x :=
  nondegenerateBaseOther_adj G hC6 o.pair o.pair_mem
    (o.centre_mem_base hC6) hx

theorem far_adj_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) {x : V}
    (hx : x ∈ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem) :
    G.Adj (o.far hC6) x :=
  nondegenerateBaseOther_adj G hC6 o.pair o.pair_mem
    (o.far_mem_base hC6) hx

theorem centre_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.centre hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  exact Finset.disjoint_left.mp
    (disjoint_nondegenerateBaseOther G hC6 o.pair o.pair_mem)
    (o.centre_mem_base hC6)

theorem far_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.far hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  exact Finset.disjoint_left.mp
    (disjoint_nondegenerateBaseOther G hC6 o.pair o.pair_mem)
    (o.far_mem_base hC6)

theorem centre_ne_far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : o.centre hC6 ≠ o.far hC6 := by
  intro heq
  have hcard := card_nondegenerateBaseSide G hC6 o.pair o.pair_mem
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    change nondegenerateStarCentre G hC6 o.pair o.pair_mem =
      (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then o.pair.1.2
       else o.pair.1.1) at heq
    rw [if_pos hl] at heq
    rw [nondegenerateBaseSide, if_pos hl, heq] at hcard
    simp at hcard
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    change nondegenerateStarCentre G hC6 o.pair o.pair_mem =
      (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then o.pair.1.2
       else o.pair.1.1) at heq
    rw [if_neg hl] at heq
    rw [nondegenerateBaseSide, if_neg hl, heq] at hcard
    simp at hcard

theorem outside_adj_centre (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.outside hC6) (o.centre hC6) := by
  have hend := (mem_pathFiber (G := G)).mp o.path_mem
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have h0 : o.path.vertex 0 = o.pair.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    rw [outside, onLeft, if_pos hl, centre, ← h0, hl o.path o.path_mem]
    exact o.path.adj_zero_one
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have h3 : o.path.vertex 3 = o.pair.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    rw [outside, onLeft, if_neg hl, centre, ← h3,
      nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hl
        o.path o.path_mem]
    exact o.path.adj_two_three.symm

theorem centre_adj_varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.centre hC6) (o.varying hC6) :=
  o.centre_adj_other hC6 (o.varying_mem hC6)

theorem far_adj_varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.far hC6) (o.varying hC6) :=
  o.far_adj_other hC6 (o.varying_mem hC6)

theorem outside_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.outside hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [nondegenerateOtherMiddles, if_pos hl]
    intro hout
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hout
    have hend := (mem_pathFiber (G := G)).mp hp
    have h0 : p.vertex 0 = o.pair.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    apply p.injective.ne (show (0 : Fin 4) ≠ 2 by decide)
    have hout_eq : o.outside hC6 = o.pair.1.1 := by
      rw [outside, onLeft, if_pos hl]
    exact h0.trans (hout_eq.symm.trans heq.symm)
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [nondegenerateOtherMiddles, if_neg hl]
    intro hout
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hout
    have hend := (mem_pathFiber (G := G)).mp hp
    have h3 : p.vertex 3 = o.pair.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    apply p.injective.ne (show (3 : Fin 4) ≠ 1 by decide)
    have hout_eq : o.outside hC6 = o.pair.1.2 := by
      rw [outside, onLeft, if_neg hl]
    exact h3.trans (hout_eq.symm.trans heq.symm)

/-- The far endpoint is not adjacent to the common star centre.  Otherwise
that centre's closed neighbourhood would contain every path in the fibre,
contrary to nondegeneracy. -/
theorem not_adj_centre_far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    ¬ G.Adj (o.centre hC6) (o.far hC6) := by
  intro hfar
  apply nondegenerateExceptional_not_central G o.pair_mem
  refine ⟨o.centre hC6, ?_⟩
  intro p hp i
  rw [mem_closedNeighborFinset]
  have hend := (mem_pathFiber (G := G)).mp hp
  have h0 : p.vertex 0 = o.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hend
  have h3 : p.vertex 3 = o.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hend
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have hs := hl p hp
    unfold centre at hfar ⊢
    fin_cases i
    · right
      change G.Adj (nondegenerateStarCentre G hC6 o.pair o.pair_mem)
        (p.vertex (0 : Fin 4))
      rw [hs]
      exact p.adj_zero_one.symm
    · exact Or.inl hs.symm
    · right
      rw [hs]
      exact p.adj_one_two
    · right
      rw [far, onLeft, if_pos hl, ← h3] at hfar
      exact hfar
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have hs := nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hl p hp
    unfold centre at hfar ⊢
    fin_cases i
    · right
      rw [far, onLeft, if_neg hl, ← h0] at hfar
      exact hfar
    · right
      rw [hs]
      exact p.adj_one_two.symm
    · exact Or.inl hs.symm
    · right
      change G.Adj (nondegenerateStarCentre G hC6 o.pair o.pair_mem)
        (p.vertex (3 : Fin 4))
      rw [hs]
      exact p.adj_two_three

/-- A multiplicity-two ordinary exceptional pair has adjacent endpoints. -/
theorem outside_adj_far_of_multiplicity_eq_two (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G)
    (hmul : pathMultiplicity G o.pair = 2) :
    G.Adj (o.outside hC6) (o.far hC6) := by
  have hord : o.pair ∈ ordinaryExceptionalPairs G :=
    (Finset.mem_sdiff.mp o.pair_mem).1
  rcases (Finset.mem_filter.mp hord).2 with hadj | hthree
  · by_cases hl : o.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
      rw [outside, far, onLeft, if_pos hl, if_pos hl]
      exact hadj.2
    · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
      rw [outside, far, onLeft, if_neg hl, if_neg hl]
      exact hadj.2.symm
  · omega

/-- Two nondegenerate occurrences with the same outside endpoint, star
centre, and varying middle vertex have the same far endpoint.  The proof is
the two-hexagon collision argument behind the wedge injection. -/
theorem far_eq_of_code (hC6 : WalkC6Free G)
    {o r : NondegenerateOccurrence G}
    (ha : o.outside hC6 = r.outside hC6)
    (hw : o.centre hC6 = r.centre hC6)
    (hx : o.varying hC6 = r.varying hC6) :
    o.far hC6 = r.far hC6 := by
  by_contra hfar
  let X := nondegenerateOtherMiddles G hC6 o.pair o.pair_mem
  let Y := nondegenerateOtherMiddles G hC6 r.pair r.pair_mem
  have hxX : o.varying hC6 ∈ X := o.varying_mem hC6
  have hxY : r.varying hC6 ∈ Y := r.varying_mem hC6
  have hcardX : 2 ≤ X.card := by
    rw [card_nondegenerateOtherMiddles G hC6 o.pair o.pair_mem]
    exact nondegenerateExceptional_two_le G o.pair_mem
  have hcardY : 2 ≤ Y.card := by
    rw [card_nondegenerateOtherMiddles G hC6 r.pair r.pair_mem]
    exact nondegenerateExceptional_two_le G r.pair_mem
  obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne (by omega) (o.varying hC6)
  obtain ⟨z, hz, hzx⟩ := Y.exists_mem_ne (by omega) (r.varying hC6)
  have halternates : ∀ {y z : V}, y ∈ X → y ≠ o.varying hC6 →
      z ∈ Y → z ≠ r.varying hC6 → y = z := by
    intro y z hy' hyx' hz' hzx'
    by_contra hyz
    have hboz : o.far hC6 ≠ z := by
      intro e
      apply o.not_adj_centre_far hC6
      rw [e, hw]
      exact r.centre_adj_other hC6 hz'
    have hbry : r.far hC6 ≠ y := by
      intro e
      apply r.not_adj_centre_far hC6
      rw [e, ← hw]
      exact o.centre_adj_other hC6 hy'
    have hboy : o.far hC6 ≠ y := by
      intro e
      apply o.far_not_mem_other hC6
      rw [e]
      exact hy'
    have hbow : o.far hC6 ≠ o.centre hC6 := (o.centre_ne_far hC6).symm
    have hbox : o.far hC6 ≠ o.varying hC6 := by
      intro e
      apply o.far_not_mem_other hC6
      rw [e]
      exact hxX
    have hyw : y ≠ o.centre hC6 := by
      intro e
      apply o.centre_not_mem_other hC6
      rw [← e]
      exact hy'
    have hyxo : y ≠ o.varying hC6 := hyx'
    have hwz : o.centre hC6 ≠ z := by
      intro e
      apply r.centre_not_mem_other hC6
      rw [← hw, e]
      exact hz'
    have hwbr : o.centre hC6 ≠ r.far hC6 := by
      rw [hw]
      exact r.centre_ne_far hC6
    have hwx : o.centre hC6 ≠ o.varying hC6 := by
      intro e
      apply o.centre_not_mem_other hC6
      rw [e]
      exact hxX
    have hzbr : z ≠ r.far hC6 := by
      intro e
      apply r.far_not_mem_other hC6
      rw [← e]
      exact hz'
    have hzx_o : z ≠ o.varying hC6 := by
      intro e
      exact hzx' (e.trans hx)
    have hbrx : r.far hC6 ≠ o.varying hC6 := by
      intro e
      apply r.far_not_mem_other hC6
      rw [e, hx]
      exact hxY
    apply false_of_six_cycle_shortcut G hC6
      (o.far_adj_other hC6 hy')
      (o.centre_adj_other hC6 hy').symm
      (by rw [hw]; exact r.centre_adj_other hC6 hz')
      (r.far_adj_other hC6 hz').symm
      (by rw [hx]; exact r.far_adj_varying hC6)
      (o.far_adj_varying hC6).symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    aesop
  have hyz : y = z := halternates hy hyx hz hzx
  have hsubX : X ⊆ {o.varying hC6, y} := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases htx : t = o.varying hC6
    · exact Or.inl htx
    · exact Or.inr ((halternates ht htx hz hzx).trans hyz.symm)
  have hsubY : Y ⊆ {r.varying hC6, y} := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases htx : t = r.varying hC6
    · exact Or.inl htx
    · exact Or.inr (halternates hy hyx ht htx).symm
  have hcardX' : X.card = 2 := by
    have hle := Finset.card_le_card hsubX
    have hp : ({o.varying hC6, y} : Finset V).card = 2 :=
      Finset.card_pair hyx.symm
    omega
  have hcardY' : Y.card = 2 := by
    have hle := Finset.card_le_card hsubY
    have hp : ({r.varying hC6, y} : Finset V).card = 2 := by
      apply Finset.card_pair
      intro e
      apply hyx
      rw [← e, ← hx]
    omega
  have hmulO : pathMultiplicity G o.pair = 2 := by
    rw [← card_nondegenerateOtherMiddles G hC6 o.pair o.pair_mem]
    exact hcardX'
  have hmulR : pathMultiplicity G r.pair = 2 := by
    rw [← card_nondegenerateOtherMiddles G hC6 r.pair r.pair_mem]
    exact hcardY'
  have hyY : y ∈ Y := by rw [hyz]; exact hz
  have ha_bo := o.outside_adj_far_of_multiplicity_eq_two hC6 hmulO
  have ha_br : G.Adj (o.outside hC6) (r.far hC6) := by
    rw [ha]
    exact r.outside_adj_far_of_multiplicity_eq_two hC6 hmulR
  have habo : o.outside hC6 ≠ o.far hC6 := ha_bo.ne
  have hax : o.outside hC6 ≠ o.varying hC6 := by
    intro e
    apply o.outside_not_mem_other hC6
    rw [e]
    exact hxX
  have habr : o.outside hC6 ≠ r.far hC6 := ha_br.ne
  have hay : o.outside hC6 ≠ y := by
    intro e
    apply o.outside_not_mem_other hC6
    rw [e]
    exact hy
  have haw : o.outside hC6 ≠ o.centre hC6 := (o.outside_adj_centre hC6).ne
  have hbox : o.far hC6 ≠ o.varying hC6 := by
    intro e
    apply o.far_not_mem_other hC6
    rw [e]
    exact hxX
  have hboy : o.far hC6 ≠ y := by
    intro e
    apply o.far_not_mem_other hC6
    rw [e]
    exact hy
  have hbow : o.far hC6 ≠ o.centre hC6 := (o.centre_ne_far hC6).symm
  have hxbr : o.varying hC6 ≠ r.far hC6 := by
    intro e
    apply r.far_not_mem_other hC6
    rw [← e, hx]
    exact hxY
  have hxy : o.varying hC6 ≠ y := hyx.symm
  have hxw : o.varying hC6 ≠ o.centre hC6 := by
    intro e
    apply o.centre_not_mem_other hC6
    rw [← e]
    exact hxX
  have hbry : r.far hC6 ≠ y := by
    intro e
    apply r.far_not_mem_other hC6
    rw [e]
    exact hyY
  have hbrw : r.far hC6 ≠ o.centre hC6 := by
    rw [hw]
    exact (r.centre_ne_far hC6).symm
  have hyw : y ≠ o.centre hC6 := by
    intro e
    apply o.centre_not_mem_other hC6
    rw [← e]
    exact hy
  apply false_of_six_cycle_shortcut G hC6
    ha_bo (o.far_adj_varying hC6)
    (by rw [hx]; exact (r.far_adj_varying hC6).symm)
    (r.far_adj_other hC6 hyY)
    (o.centre_adj_other hC6 hy).symm
    (o.outside_adj_centre hC6).symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or]
  aesop

end NondegenerateOccurrence

/-- The finite universe of oriented length-two wedges. -/
abbrev OrientedWedge :=
  Σ w : V, (↥(G.neighborFinset w)) × (↥(G.neighborFinset w))

/-- The outside edge followed by the varying middle vertex. -/
noncomputable def nondegenerateWedgeCode (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : OrientedWedge G :=
  ⟨o.centre hC6,
    (⟨o.outside hC6, (G.mem_neighborFinset _ _).mpr (o.outside_adj_centre hC6).symm⟩,
     ⟨o.varying hC6, (G.mem_neighborFinset _ _).mpr (o.centre_adj_varying hC6)⟩)⟩

private theorem occurrence_eq_of_code_data (hC6 : WalkC6Free G)
    {o r : NondegenerateOccurrence G}
    (ha : o.outside hC6 = r.outside hC6)
    (hw : o.centre hC6 = r.centre hC6)
    (hx : o.varying hC6 = r.varying hC6)
    (hb : o.far hC6 = r.far hC6) : o = r := by
  have hendo := (mem_pathFiber (G := G)).mp o.path_mem
  have hendr := (mem_pathFiber (G := G)).mp r.path_mem
  have ho0 : o.path.vertex 0 = o.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hendo
  have ho3 : o.path.vertex 3 = o.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hendo
  have hr0 : r.path.vertex 0 = r.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hendr
  have hr3 : r.path.vertex 3 = r.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hendr
  by_cases hlo : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hlo
    by_cases hlr : r.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.1 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_pos hlo, if_pos hlr] at ha
        exact ha
      have hb' : o.pair.1.2 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_pos hlo, if_pos hlr] at hb
        exact hb
      have hpair : o.pair = r.pair := Subtype.ext (Prod.ext ha' hb')
      have hpath : o.path = r.path := by
        apply Subtype.ext
        funext i
        fin_cases i
        · exact ho0.trans (ha'.trans hr0.symm)
        · exact (hlo o.path o.path_mem).symm.trans
            (hw.trans (hlr r.path r.path_mem))
        · change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
            o.path.vertex 2 else o.path.vertex 1) =
            (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
              r.path.vertex 2 else r.path.vertex 1) at hx
          rw [if_pos hlo, if_pos hlr] at hx
          exact hx
        · exact ho3.trans (hb'.trans hr3.symm)
      rcases o with ⟨⟨opi, ohpi⟩, ⟨op, ohp⟩⟩
      rcases r with ⟨⟨rpi, rhpi⟩, ⟨rp, rhp⟩⟩
      change opi = rpi at hpair
      change op = rp at hpath
      subst rpi
      subst rp
      rfl
    · change ¬ nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.1 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_pos hlo, if_neg hlr] at ha
        exact ha
      have hb' : o.pair.1.2 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_pos hlo, if_neg hlr] at hb
        exact hb
      exfalso
      have hrev : o.pair.1.2 < o.pair.1.1 := by
        calc
          o.pair.1.2 = r.pair.1.1 := hb'
          _ < r.pair.1.2 := r.pair.2
          _ = o.pair.1.1 := ha'.symm
      exact (lt_asymm o.pair.2 hrev).elim
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hlo
    by_cases hlr : r.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.2 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_neg hlo, if_pos hlr] at ha
        exact ha
      have hb' : o.pair.1.1 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_neg hlo, if_pos hlr] at hb
        exact hb
      exfalso
      have hrev : o.pair.1.2 < o.pair.1.1 := by
        calc
          o.pair.1.2 = r.pair.1.1 := ha'
          _ < r.pair.1.2 := r.pair.2
          _ = o.pair.1.1 := hb'.symm
      exact (lt_asymm o.pair.2 hrev).elim
    · change ¬ nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.2 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_neg hlo, if_neg hlr] at ha
        exact ha
      have hb' : o.pair.1.1 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_neg hlo, if_neg hlr] at hb
        exact hb
      have hpair : o.pair = r.pair := Subtype.ext (Prod.ext hb' ha')
      have hso := nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hlo
      have hsr := nondegenerateStarCentre_spec_right G hC6 r.pair r.pair_mem hlr
      have hpath : o.path = r.path := by
        apply Subtype.ext
        funext i
        fin_cases i
        · exact ho0.trans (hb'.trans hr0.symm)
        · change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
            o.path.vertex 2 else o.path.vertex 1) =
            (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
              r.path.vertex 2 else r.path.vertex 1) at hx
          rw [if_neg hlo, if_neg hlr] at hx
          exact hx
        · exact (hso o.path o.path_mem).symm.trans
            (hw.trans (hsr r.path r.path_mem))
        · exact ho3.trans (ha'.trans hr3.symm)
      rcases o with ⟨⟨opi, ohpi⟩, ⟨op, ohp⟩⟩
      rcases r with ⟨⟨rpi, rhpi⟩, ⟨rp, rhp⟩⟩
      change opi = rpi at hpair
      change op = rp at hpath
      subst rpi
      subst rp
      rfl

theorem nondegenerateWedgeCode_injective (hC6 : WalkC6Free G) :
    Function.Injective (nondegenerateWedgeCode G hC6) := by
  intro o r hcode
  have hw : o.centre hC6 = r.centre hC6 :=
    congrArg Sigma.fst hcode
  have ha : o.outside hC6 = r.outside hC6 :=
    congrArg (fun z : OrientedWedge G ↦ z.2.1.1) hcode
  have hx : o.varying hC6 = r.varying hC6 :=
    congrArg (fun z : OrientedWedge G ↦ z.2.2.1) hcode
  exact occurrence_eq_of_code_data G hC6 ha hw hx
    (NondegenerateOccurrence.far_eq_of_code hC6 ha hw hx)

theorem card_nondegenerateOccurrence_eq_multiplicitySum :
    Fintype.card (NondegenerateOccurrence G) =
      multiplicitySum G (nondegenerateExceptionalPairs G) := by
  calc
    Fintype.card (NondegenerateOccurrence G) =
        ∑ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
          Fintype.card {p // p ∈ pathFiber G pi.1} := by
      simp only [NondegenerateOccurrence, Fintype.card_sigma]
    _ = ∑ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
          (pathFiber G pi.1).card := by
      simp only [Fintype.card_coe]
    _ = multiplicitySum G (nondegenerateExceptionalPairs G) := by
      unfold multiplicitySum pathMultiplicity
      have hatt : (nondegenerateExceptionalPairs G).attach =
          (Finset.univ : Finset
            {pi // pi ∈ nondegenerateExceptionalPairs G}) := by
        ext pi
        simp
      have hs := Finset.sum_attach (nondegenerateExceptionalPairs G)
        (fun pi : EndpointPair V ↦ (pathFiber G pi).card)
      rw [hatt] at hs
      exact hs

theorem card_orientedWedge_eq_sum_degree_sq :
    Fintype.card (OrientedWedge G) = ∑ v, G.degree v * G.degree v := by
  simp only [OrientedWedge, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_coe, G.card_neighborFinset_eq_degree]

/-- The U1-free nondegenerate half: every occurrence injects into an
oriented wedge, of which there are at most `2 * Δ * e`. -/
theorem nondegenerate_multiplicity_bound_shortcut (hC6 : WalkC6Free G) :
    multiplicitySum G (nondegenerateExceptionalPairs G) ≤
      2 * G.maxDegree * G.edgeFinset.card := by
  have hinj : Fintype.card (NondegenerateOccurrence G) ≤
      Fintype.card (OrientedWedge G) :=
    Fintype.card_le_of_injective (nondegenerateWedgeCode G hC6)
      (nondegenerateWedgeCode_injective G hC6)
  have hsquares : (∑ v, G.degree v * G.degree v) ≤
      ∑ v, G.maxDegree * G.degree v := by
    exact Finset.sum_le_sum fun v _ ↦
      Nat.mul_le_mul_right (G.degree v) (G.degree_le_maxDegree v)
  rw [card_nondegenerateOccurrence_eq_multiplicitySum G,
    card_orientedWedge_eq_sum_degree_sq G] at hinj
  calc
    multiplicitySum G (nondegenerateExceptionalPairs G)
        ≤ ∑ v, G.degree v * G.degree v := hinj
    _ ≤ ∑ v, G.maxDegree * G.degree v := hsquares
    _ = G.maxDegree * (∑ v, G.degree v) := by rw [Finset.mul_sum]
    _ = G.maxDegree * (2 * G.edgeFinset.card) := by
      rw [G.sum_degrees_eq_twice_card_edges]
    _ = 2 * G.maxDegree * G.edgeFinset.card := by ring

/-- Unconditional FNV U8.  The wedge injection gives the stronger constant
`27`; the displayed `35` is the traditional statement consumed downstream. -/
theorem fnvU8Direct (hC6 : WalkC6Free G) :
    multiplicitySum G (generalExceptionalPairs G) ≤
      35 * G.maxDegree * G.edgeFinset.card := by
  have hd := degenerate_multiplicity_bound_direct G hC6
  have hn := nondegenerate_multiplicity_bound_shortcut G hC6
  unfold multiplicitySum at hd hn ⊢
  rw [generalExceptionalPairs_eq G]
  rw [Finset.sum_union (degenerate_disjoint_nondegenerate G)]
  calc
    (∑ pi ∈ degeneratePairs G, pathMultiplicity G pi) +
          ∑ pi ∈ nondegenerateExceptionalPairs G, pathMultiplicity G pi
        ≤ 25 * G.maxDegree * G.edgeFinset.card +
          2 * G.maxDegree * G.edgeFinset.card := Nat.add_le_add hd hn
    _ = 27 * (G.maxDegree * G.edgeFinset.card) := by ring
    _ ≤ 35 * (G.maxDegree * G.edgeFinset.card) :=
      Nat.mul_le_mul_right (G.maxDegree * G.edgeFinset.card) (by omega)
    _ = 35 * G.maxDegree * G.edgeFinset.card := by ring

end

end Erdos59
