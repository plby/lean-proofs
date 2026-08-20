import ErdosProblems.Erdos814.Basic

/-!
# Erdős 814: shadows

This file formalizes the closure construction called a *shadow* in Sauermann's proof.  The
ambient vertex type is fixed; `U` is the vertex set of the graph currently under consideration.
The protected blocks are pairwise disjoint, lie in `U`, consist of vertices of degree at least
`k`, and have incident-edge count at most `(k-1)|D|+1`.

The shadow is selected from the terminal outputs of the finite saturation procedure.  The
minimality theorem below shows that the selected terminal output is independent of this choice.
-/

open Finset SimpleGraph
open scoped Sym2

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A family of protected blocks with the two numerical properties used by the shadow proof. -/
structure ProtectedFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) where
  blocks : Finset (Finset V)
  nonempty : ∀ D ∈ blocks, D.Nonempty
  subset_ambient : ∀ D ∈ blocks, D ⊆ U
  pairwise_disjoint : ∀ D ∈ blocks, ∀ E ∈ blocks, D ≠ E → Disjoint D E
  high_degree : ∀ D ∈ blocks, ∀ x ∈ D, k ≤ degreeOn G U x
  incident_le : ∀ D ∈ blocks,
    incidentCount G U D ≤ (k - 1) * D.card + 1

namespace ProtectedFamily

variable {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {k : ℕ}

/-- A vertex which is in no protected block. -/
def Free (C : ProtectedFamily G U k) (x : V) : Prop :=
  ∀ D ∈ C.blocks, x ∉ D

/-- A set contains every protected block that it meets. -/
def WholeBlocks (C : ProtectedFamily G U k) (Y : Finset V) : Prop :=
  ∀ D ∈ C.blocks, D ⊆ Y ∨ Disjoint D Y

lemma free_of_degree_lt (C : ProtectedFamily G U k) {x : V}
    (hx : degreeOn G U x < k) : C.Free x := by
  intro D hD hxD
  exact (not_le_of_gt hx) (C.high_degree D hD x hxD)

lemma wholeBlocks_singleton (C : ProtectedFamily G U k) {w : V}
    (hw : degreeOn G U w < k) : C.WholeBlocks {w} := by
  intro D hD
  right
  rw [Finset.disjoint_singleton_right]
  exact C.free_of_degree_lt hw D hD

end ProtectedFamily

variable {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {k : ℕ}

/-- The four closure properties in the definition of a shadow. -/
structure ShadowClosed (C : ProtectedFamily G U k) (w : V) (Y : Finset V) : Prop where
  subset_ambient : Y ⊆ U
  root_mem : w ∈ Y
  whole_blocks : C.WholeBlocks Y
  residual_degree : ∀ x ∈ U \ Y, AdjacentSets G {x} Y → k ≤ degreeOn G (U \ Y) x
  adjacent_blocks : ∀ D ∈ C.blocks, AdjacentSets G D Y → D ⊆ Y

/-- One legal operation of the finite shadow-saturation procedure. -/
inductive ShadowStep (C : ProtectedFamily G U k) : Finset V → Finset V → Prop
  | vertex (Y : Finset V) (x : V)
      (hxU : x ∈ U) (hxY : x ∉ Y) (hfree : C.Free x)
      (hadj : AdjacentSets G {x} Y) (hdeg : degreeOn G (U \ Y) x ≤ k - 1) :
      ShadowStep C Y (Y ∪ {x})
  | block (Y D : Finset V) (hD : D ∈ C.blocks) (hdisj : Disjoint D Y)
      (hadj : AdjacentSets G D Y) :
      ShadowStep C Y (Y ∪ D)

/-- Reflexive-transitive reachability by legal shadow steps. -/
abbrev ShadowReachable (C : ProtectedFamily G U k) (Y Z : Finset V) : Prop :=
  Relation.ReflTransGen (ShadowStep C) Y Z

/-- No further operation of the shadow procedure is possible. -/
def ShadowTerminal (C : ProtectedFamily G U k) (Y : Finset V) : Prop :=
  ¬ ∃ Z, ShadowStep C Y Z

lemma ShadowStep.subset {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowStep C Y Z) : Y ⊆ Z := by
  cases h <;> simp

lemma ShadowStep.subset_ambient {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) : Z ⊆ U := by
  cases h with
  | vertex x hxU => simpa using union_subset hYU (singleton_subset_iff.mpr hxU)
  | block D hD => exact union_subset hYU (C.subset_ambient D hD)

lemma ShadowStep.card_lt {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowStep C Y Z) : Y.card < Z.card := by
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hdisj : Disjoint Y {x} := Finset.disjoint_singleton_right.mpr hxY
      rw [card_union_of_disjoint hdisj, card_singleton]
      omega
  | block D hD hdisj hadj =>
      rw [card_union_of_disjoint hdisj.symm]
      have hpos : 0 < D.card := card_pos.mpr (C.nonempty D hD)
      omega

lemma ShadowStep.wholeBlocks {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hY : C.WholeBlocks Y) (h : ShadowStep C Y Z) : C.WholeBlocks Z := by
  intro D hD
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      rcases hY D hD with hDY | hDY
      · exact Or.inl (hDY.trans subset_union_left)
      · right
        rw [Finset.disjoint_union_right]
        exact ⟨hDY, by simpa [Finset.disjoint_singleton_right] using hfree D hD⟩
  | block E hE hEY hadj =>
      by_cases hDE : D = E
      · subst E
        exact Or.inl subset_union_right
      · rcases hY D hD with hDY | hDY
        · exact Or.inl (hDY.trans subset_union_left)
        · right
          rw [Finset.disjoint_union_right]
          exact ⟨hDY, C.pairwise_disjoint D hD E hE hDE⟩

lemma shadowReachable_subset_ambient {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowReachable C Y Z) : Z ⊆ U := by
  induction h with
  | refl => exact hYU
  | tail hreach hstep ih => exact hstep.subset_ambient ih

lemma shadowReachable_wholeBlocks {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hY : C.WholeBlocks Y) (h : ShadowReachable C Y Z) : C.WholeBlocks Z := by
  induction h with
  | refl => exact hY
  | tail hreach hstep ih => exact hstep.wholeBlocks ih

lemma shadowReachable_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowReachable C Y Z) : Y ⊆ Z := by
  induction h with
  | refl => exact Subset.rfl
  | tail hreach hstep ih => exact ih.trans hstep.subset

/-- Follow arbitrary legal steps until none remains.  Termination is by strict growth of the
current finite set. -/
noncomputable def shadowSaturate (C : ProtectedFamily G U k) (Y : Finset V) : Finset V := by
  classical
  by_cases h : ∃ Z, ShadowStep C Y Z
  · exact shadowSaturate C (Classical.choose h)
  · exact Y
termination_by Fintype.card V - Y.card
decreasing_by
  have hlt := (Classical.choose_spec h).card_lt
  have hle : (Classical.choose h).card ≤ Fintype.card V := by
    simpa using card_le_card (show Classical.choose h ⊆ (univ : Finset V) by simp)
  omega

lemma shadowSaturate_terminal (C : ProtectedFamily G U k) (Y : Finset V) :
    ShadowTerminal C (shadowSaturate C Y) := by
  rw [shadowSaturate]
  split
  · rename_i h
    exact shadowSaturate_terminal C (Classical.choose h)
  · rename_i h
    exact h
termination_by Fintype.card V - Y.card
decreasing_by
  have hex : ∃ Z, ShadowStep C Y Z := by assumption
  have hlt := (Classical.choose_spec hex).card_lt
  have hle : (Classical.choose hex).card ≤ Fintype.card V := by
    simpa using card_le_card
      (show Classical.choose hex ⊆ (univ : Finset V) by simp)
  omega

lemma shadowSaturate_reachable (C : ProtectedFamily G U k) (Y : Finset V) :
    ShadowReachable C Y (shadowSaturate C Y) := by
  rw [shadowSaturate]
  split
  · rename_i h
    exact (Relation.ReflTransGen.single (Classical.choose_spec h)).trans
      (shadowSaturate_reachable C (Classical.choose h))
  · exact Relation.ReflTransGen.refl
termination_by Fintype.card V - Y.card
decreasing_by
  have hex : ∃ Z, ShadowStep C Y Z := by assumption
  have hlt := (Classical.choose_spec hex).card_lt
  have hle : (Classical.choose hex).card ≤ Fintype.card V := by
    simpa using card_le_card
      (show Classical.choose hex ⊆ (univ : Finset V) by simp)
  omega

/-- The shadow obtained by the finite saturation procedure. -/
noncomputable def shadow (C : ProtectedFamily G U k) (w : V) : Finset V :=
  shadowSaturate C {w}

lemma shadow_reachable (C : ProtectedFamily G U k) (w : V) :
    ShadowReachable C {w} (shadow C w) :=
  shadowSaturate_reachable C {w}

lemma shadow_terminal (C : ProtectedFamily G U k) (w : V) :
    ShadowTerminal C (shadow C w) :=
  shadowSaturate_terminal C {w}

lemma ShadowStep.subset_of_closed {C : ProtectedFamily G U k} {w : V}
    {Y Z W : Finset V} (hk : 1 ≤ k) (hYW : Y ⊆ W) (hW : ShadowClosed C w W)
    (hstep : ShadowStep C Y Z) : Z ⊆ W := by
  cases hstep with
  | vertex x hxU hxY hfree hadj hdeg =>
      apply union_subset hYW
      rw [singleton_subset_iff]
      by_contra hxW
      have hxUW : x ∈ U \ W := mem_sdiff.mpr ⟨hxU, hxW⟩
      have hadjW : AdjacentSets G {x} W := by
        rcases hadj with ⟨a, ha, y, hy, hay⟩
        exact ⟨a, ha, y, hYW hy, hay⟩
      have hres := hW.residual_degree x hxUW hadjW
      have hsub : U \ W ⊆ U \ Y := by
        intro z hz
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,
          fun hzY ↦ (mem_sdiff.mp hz).2 (hYW hzY)⟩
      have hmono := degreeOn_mono G hsub x
      omega
  | block D hD hdisj hadj =>
      apply union_subset hYW
      apply hW.adjacent_blocks D hD
      rcases hadj with ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, hx, y, hYW hy, hxy⟩

lemma shadowReachable_subset_of_closed {C : ProtectedFamily G U k} {w : V}
    {Y Z W : Finset V} (hk : 1 ≤ k) (hYW : Y ⊆ W) (hW : ShadowClosed C w W)
    (hreach : ShadowReachable C Y Z) : Z ⊆ W := by
  induction hreach with
  | refl => exact hYW
  | tail hreach hstep ih => exact hstep.subset_of_closed hk ih hW

lemma terminal_shadowClosed (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) (hterm : ShadowTerminal C Y) :
    ShadowClosed C w Y := by
  have hYsub : Y ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
  have hwhole : C.WholeBlocks Y :=
    shadowReachable_wholeBlocks (C.wholeBlocks_singleton (by omega)) hreach
  refine ⟨hYsub, ?_, hwhole, ?_, ?_⟩
  · exact shadowReachable_mono hreach (by simp)
  · intro x hxUY hadj
    by_contra hnot
    have hdegcontra : degreeOn G (U \ Y) x ≤ k - 1 := by omega
    have hfree : C.Free x := by
      intro D hD hxD
      rcases hwhole D hD with hDY | hDY
      · exact (mem_sdiff.mp hxUY).2 (hDY hxD)
      · have hadjDY : AdjacentSets G D Y := by
          rcases hadj with ⟨a, ha, y, hy, hay⟩
          have hax : a = x := by simpa using ha
          subst a
          exact ⟨x, hxD, y, hy, hay⟩
        exact hterm ⟨Y ∪ D, ShadowStep.block Y D hD hDY hadjDY⟩
    exact hterm ⟨Y ∪ {x}, ShadowStep.vertex Y x (mem_sdiff.mp hxUY).1
      (mem_sdiff.mp hxUY).2 hfree hadj hdegcontra⟩
  · intro D hD hadj
    rcases hwhole D hD with hDY | hDY
    · exact hDY
    · exact False.elim (hterm ⟨Y ∪ D, ShadowStep.block Y D hD hDY hadj⟩)

lemma shadow_closed (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    ShadowClosed C w (shadow C w) :=
  terminal_shadowClosed C hk hwU hwdeg (shadow_reachable C w) (shadow_terminal C w)

/-- The shadow is the least set satisfying the four closure properties. -/
lemma shadow_minimal (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    {Y : Finset V} (hY : ShadowClosed C w Y) : shadow C w ⊆ Y := by
  exact shadowReachable_subset_of_closed hk (by simpa using hY.root_mem) hY
    (shadow_reachable C w)

/-- Every terminal run has the same output. -/
lemma shadow_choice_independent (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) (hterm : ShadowTerminal C Y) :
    Y = shadow C w := by
  apply Subset.antisymm
  · have hwsh : w ∈ shadow C w :=
      shadowReachable_mono (shadow_reachable C w) (by simp)
    have hroot : {w} ⊆ shadow C w := singleton_subset_iff.mpr hwsh
    exact shadowReachable_subset_of_closed hk hroot
      (shadow_closed C hk hwU hwdeg) hreach
  · exact shadow_minimal C hk hwU hwdeg
      (terminal_shadowClosed C hk hwU hwdeg hreach hterm)

lemma shadow_subset_ambient (C : ProtectedFamily G U k) {w : V}
    (hwU : w ∈ U) : shadow C w ⊆ U :=
  shadowReachable_subset_ambient (by simpa) (shadow_reachable C w)

lemma root_mem_shadow (C : ProtectedFamily G U k) (w : V) : w ∈ shadow C w :=
  shadowReachable_mono (shadow_reachable C w) (by simp)

/-! ## Numerical shadow accounting -/

/-- The total low-degree deficit contributed by the vertices of `X`, with degrees always
measured in the original ambient set `U`. -/
def lowDefect (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U X : Finset V) : ℕ :=
  ∑ x ∈ X, if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0

/-- The incident edges of a singleton are its neighbours in the ambient induced graph.  This
local version keeps the shadow layer dependent only on `Basic`. -/
private lemma shadow_incidentCount_singleton {A : Finset V} {v : V} (hv : v ∈ A) :
    incidentCount G A {v} = degreeOn G A v := by
  unfold incidentCount incidentEdges degreeOn
  symm
  refine Finset.card_bij (fun w _ ↦ s(v, w)) ?_ ?_ ?_
  · intro w hw
    rcases mem_inter.mp hw with ⟨hvw, hwA⟩
    refine mem_sdiff.mpr ⟨mem_edgeOn.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset] using hvw
    · intro z hz
      have hz' : z = v ∨ z = w := by
        simpa [Sym2.toFinset_mk_eq] using hz
      rcases hz' with rfl | rfl
      · exact hv
      · exact hwA
    · intro hres
      have hvend : v ∈ s(v, w).toFinset := by simp [Sym2.toFinset_mk_eq]
      have hvres := (mem_edgeOn.mp hres).2 hvend
      exact (mem_sdiff.mp hvres).2 (by simp)
  · intro w₁ hw₁ w₂ hw₂ heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact h.2
    · have hadj : G.Adj v w₁ := by
        simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hw₁).1
      have hvw₁ : v ≠ w₁ := by
        intro hvw
        subst w₁
        exact G.loopless.irrefl v hadj
      exact (hvw₁ h.2.symm).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rcases mem_sdiff.mp he with ⟨heA, hnot⟩
        have hxy : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
            (mem_edgeOn.mp heA).1
        have hsub := (mem_edgeOn.mp heA).2
        have hxA : x ∈ A := hsub (by simp)
        have hyA : y ∈ A := hsub (by simp)
        have hvxy : x = v ∨ y = v := by
          by_contra h
          have hxv : x ≠ v := fun hxv ↦ h (Or.inl hxv)
          have hyv : y ≠ v := fun hyv ↦ h (Or.inr hyv)
          apply hnot
          apply mem_edgeOn.mpr
          refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
          intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact mem_sdiff.mpr ⟨hxA, by simpa using hxv⟩
          · exact mem_sdiff.mpr ⟨hyA, by simpa using hyv⟩
        rcases hvxy with rfl | rfl
        · refine ⟨y, ?_, rfl⟩
          exact mem_inter.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxy, hyA⟩
        · refine ⟨x, ?_, Sym2.eq_swap⟩
          exact mem_inter.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxy.symm, hxA⟩

/-- Exact incidence increment when one new vertex is appended to a deletion set. -/
private lemma shadow_incidentCount_insert {A Y : Finset V} {x : V}
    (hx : x ∈ A \ Y) :
    incidentCount G A (insert x Y) =
      incidentCount G A Y + degreeOn G (A \ Y) x := by
  have h₁ := edgeCount_sdiff_add_incidentCount G A Y
  have h₂ := edgeCount_sdiff_add_incidentCount G (A \ Y) {x}
  have h₃ := edgeCount_sdiff_add_incidentCount G A (insert x Y)
  have hsingle := shadow_incidentCount_singleton (G := G) hx
  have hs : (A \ Y) \ {x} = A \ insert x Y := by
    ext z
    simp only [mem_sdiff, mem_singleton, mem_insert]
    tauto
  rw [hs, hsingle] at h₂
  omega

/-- A neighbour already lying in `Y` contributes the one degree lost on deleting `Y`. -/
private lemma degreeOn_sdiff_add_one_le_of_adjacent
    {A Y : Finset V} {x : V} (hYA : Y ⊆ A)
    (hadj : AdjacentSets G {x} Y) :
    degreeOn G (A \ Y) x + 1 ≤ degreeOn G A x := by
  unfold degreeOn
  apply Nat.succ_le_iff.mpr
  apply card_lt_card
  constructor
  · intro z hz
    exact mem_inter.mpr ⟨(mem_inter.mp hz).1, (mem_sdiff.mp (mem_inter.mp hz).2).1⟩
  · intro hreverse
    rcases hadj with ⟨a, ha, y, hy, hay⟩
    have hax : a = x := by simpa using ha
    subst a
    have hybig : y ∈ G.neighborFinset x ∩ A := by
      exact mem_inter.mpr ⟨by simpa [SimpleGraph.mem_neighborFinset], hYA hy⟩
    have hysmall := hreverse hybig
    exact (mem_sdiff.mp (mem_inter.mp hysmall).2).2 hy

/-- If `Y ⊆ A` has no edge from `x`, deleting `Y` does not change the degree of `x`. -/
lemma degreeOn_sdiff_eq_of_not_adjacent {A Y : Finset V} {x : V}
    (hYA : Y ⊆ A) (hnot : ¬ AdjacentSets G {x} Y) :
    degreeOn G (A \ Y) x = degreeOn G A x := by
  apply Nat.le_antisymm
  · exact degreeOn_mono G sdiff_subset x
  · unfold degreeOn
    apply card_le_card
    intro y hy
    rcases mem_inter.mp hy with ⟨hxy, hyA⟩
    refine mem_inter.mpr ⟨hxy, mem_sdiff.mpr ⟨hyA, ?_⟩⟩
    intro hyY
    apply hnot
    exact ⟨x, by simp, y, hyY, by simpa [SimpleGraph.mem_neighborFinset] using hxy⟩

/-- One legal shadow step cannot decrease the deletion potential. -/
lemma ShadowStep.potential_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) :
    deletionPotential k G U Y ≤ deletionPotential k G U Z := by
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
      have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
      have hinc := shadow_incidentCount_insert (G := G) hx
      simp only [union_singleton] at hinc ⊢
      unfold deletionPotential
      rw [hcard, hinc]
      push_cast
      have hdegZ : (degreeOn G (U \ Y) x : ℤ) ≤ (k - 1 : ℕ) := by
        exact_mod_cast hdeg
      ring_nf
      omega
  | block D hD hdisj hadj =>
      have hDU := C.subset_ambient D hD
      have hcard : (Y ∪ D).card = Y.card + D.card := by
        rw [card_union_of_disjoint hdisj.symm]
      have hadjCount := incidentCount_union_add_one_le_of_adjacent G hYU hDU hadj.symm
      have hincD := C.incident_le D hD
      have hinc : incidentCount G U (Y ∪ D) ≤
          incidentCount G U Y + (k - 1) * D.card := by
        omega
      unfold deletionPotential
      rw [hcard]
      push_cast
      have hincZ : (incidentCount G U (Y ∪ D) : ℤ) ≤
          (incidentCount G U Y : ℤ) + ((k - 1) * D.card : ℕ) := by
        exact_mod_cast hinc
      push_cast at hincZ
      ring_nf at hincZ ⊢
      omega

/-- The low-defect increase in a legal step is paid for by its potential increase. -/
lemma ShadowStep.lowDefect_growth_le {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) :
    (lowDefect k G U Z : ℤ) - (lowDefect k G U Y : ℤ) ≤
      deletionPotential k G U Z - deletionPotential k G U Y := by
  have hpot := h.potential_mono hYU
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
      have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
      have hinc := shadow_incidentCount_insert (G := G) hx
      have hdegree := degreeOn_sdiff_add_one_le_of_adjacent (G := G) hYU hadj
      simp only [union_singleton] at hinc ⊢
      unfold lowDefect deletionPotential
      rw [sum_insert hxY, hcard, hinc]
      by_cases hlow : degreeOn G U x ≤ k - 1
      · simp only [hlow, if_true]
        push_cast
        have hlt : degreeOn G U x < k := by omega
        rw [Nat.cast_sub hlt.le]
        push_cast
        ring_nf
        omega
      · simp only [hlow, if_false]
        push_cast
        ring_nf
        have hd : (degreeOn G (U \ Y) x : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by
          exact_mod_cast hdeg
        omega
  | block D hD hdisj hadj =>
      have hDU := C.subset_ambient D hD
      have hzero : ∀ x ∈ D,
          (if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) = 0 := by
        intro x hxD
        have hxhigh := C.high_degree D hD x hxD
        by_cases hlow : degreeOn G U x ≤ k - 1
        · simp [hlow, Nat.sub_eq_zero_of_le hxhigh]
        · simp [hlow]
      have hdef : lowDefect k G U (Y ∪ D) = lowDefect k G U Y := by
        unfold lowDefect
        rw [sum_union hdisj.symm]
        have hsum : ∑ x ∈ D,
            (if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) = 0 := by
          apply sum_eq_zero
          intro x hxD
          exact hzero x hxD
        rw [hsum, add_zero]
      rw [hdef]
      simp only [sub_self]
      exact sub_nonneg.mpr hpot

/-- Potential monotonicity along an arbitrary finite run. -/
lemma shadowReachable_potential_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (hreach : ShadowReachable C Y Z) :
    deletionPotential k G U Y ≤ deletionPotential k G U Z := by
  induction hreach with
  | refl => exact le_rfl
  | tail hreach hstep ih =>
      exact ih.trans (hstep.potential_mono (shadowReachable_subset_ambient hYU hreach))

/-- The combined accounting invariant for every set in a shadow run. -/
lemma shadowReachable_accounting (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) :
    0 ≤ deletionPotential k G U Y ∧
      (lowDefect k G U Y : ℤ) ≤ deletionPotential k G U Y + 1 := by
  have hstartDef : lowDefect k G U {w} = k - degreeOn G U w := by
    simp [lowDefect, hwdeg]
  have hstartInc : incidentCount G U {w} = degreeOn G U w :=
    shadow_incidentCount_singleton (G := G) hwU
  have hstartEq : (lowDefect k G U {w} : ℤ) =
      deletionPotential k G U {w} + 1 := by
    rw [hstartDef]
    unfold deletionPotential
    rw [hstartInc]
    simp only [card_singleton]
    have hdeglt : degreeOn G U w < k := by omega
    rw [Nat.cast_sub hdeglt.le]
    push_cast
    omega
  have hstartNonneg : 0 ≤ deletionPotential k G U {w} := by
    unfold deletionPotential
    rw [hstartInc]
    simp only [card_singleton]
    push_cast
    have hd : (degreeOn G U w : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hwdeg
    simpa using hd
  induction hreach with
  | refl => exact ⟨hstartNonneg, hstartEq.le⟩
  | tail hreach hstep ih =>
      have hYU : _ ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
      have hpot := hstep.potential_mono hYU
      have hgrowth := hstep.lowDefect_growth_le hYU
      constructor
      · exact ih.1.trans hpot
      · omega

/-- The shadow has nonnegative deletion potential. -/
theorem shadow_potential_nonneg (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    0 ≤ deletionPotential k G U (shadow C w) :=
  (shadowReachable_accounting C hk hwU hwdeg (shadow_reachable C w)).1

/-- Sauermann's exact shadow-deficit estimate, including the indispensable `+ 1`. -/
theorem lowDefect_shadow_le (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    (lowDefect k G U (shadow C w) : ℤ) ≤
      deletionPotential k G U (shadow C w) + 1 :=
  (shadowReachable_accounting C hk hwU hwdeg (shadow_reachable C w)).2

/-- In the positive-potential case the `+ 1` is absorbed by integrality. -/
theorem lowDefect_shadow_le_two_mul (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hpos : 0 < deletionPotential k G U (shadow C w)) :
    (lowDefect k G U (shadow C w) : ℤ) ≤
      2 * deletionPotential k G U (shadow C w) := by
  have hle := lowDefect_shadow_le C hk hwU hwdeg
  omega

/-- At potential zero the root is the unique old low-degree vertex in its shadow, and its
degree is exactly `k - 1`. -/
theorem shadow_zero_unique_low (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    (∀ s ∈ shadow C w, degreeOn G U s ≤ k - 1 → s = w) ∧
      degreeOn G U w = k - 1 := by
  have hle := lowDefect_shadow_le C hk hwU hwdeg
  rw [hzero] at hle
  have hdef : lowDefect k G U (shadow C w) ≤ 1 := by
    exact_mod_cast hle
  have hwsh : w ∈ shadow C w := root_mem_shadow C w
  constructor
  · intro s hs hslow
    by_contra hsw
    have hpair : {w, s} ⊆ shadow C w := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hwsh
      · exact hs
    have hpairsum :
        (∑ x ∈ {w, s},
          if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) ≤
          lowDefect k G U (shadow C w) := by
      unfold lowDefect
      exact sum_le_sum_of_subset hpair
    have hwpos : 1 ≤ k - degreeOn G U w := by omega
    have hspos : 1 ≤ k - degreeOn G U s := by omega
    have hwn : w ∉ ({s} : Finset V) := by
      simp only [mem_singleton]
      intro hws
      exact hsw hws.symm
    have htwo : 2 ≤
        ∑ x ∈ {w, s},
          if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0 := by
      rw [sum_insert hwn, sum_singleton]
      simp only [hwdeg, hslow, if_true]
      omega
    omega
  · have hwle :
        (if degreeOn G U w ≤ k - 1 then k - degreeOn G U w else 0) ≤
          lowDefect k G U (shadow C w) := by
      unfold lowDefect
      exact single_le_sum
        (f := fun x ↦ if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0)
        (fun _ _ ↦ Nat.zero_le _) hwsh
    have hwterm :
        (if degreeOn G U w ≤ k - 1 then k - degreeOn G U w else 0) =
          k - degreeOn G U w := by simp [hwdeg]
    rw [hwterm] at hwle
    omega

/-- Deleting a shadow can only decrease signed shortage. -/
theorem shortage_delete_shadow_le (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    shortage k G (U \ shadow C w) ≤ shortage k G U := by
  rw [shortage_sdiff k G (shadow_subset_ambient C hwU)]
  have hpot := shadow_potential_nonneg C hk hwU hwdeg
  omega

/-- A zero-potential shadow may be deleted without changing signed shortage. -/
theorem shortage_delete_shadow_eq (C : ProtectedFamily G U k) {w : V}
    (hwU : w ∈ U)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shortage k G (U \ shadow C w) = shortage k G U := by
  rw [shortage_sdiff k G (shadow_subset_ambient C hwU), hzero, sub_zero]

/-- A low-degree vertex left after deleting a shadow was already low in the old graph and is
not the root. -/
theorem low_degree_after_delete_shadow (C : ProtectedFamily G U k) {w x : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hx : x ∈ U \ shadow C w)
    (hxlow : degreeOn G (U \ shadow C w) x ≤ k - 1) :
    degreeOn G U x ≤ k - 1 ∧ x ≠ w := by
  have hclosed := shadow_closed C hk hwU hwdeg
  have hnot : ¬ AdjacentSets G {x} (shadow C w) := by
    intro hadj
    have hhigh := hclosed.residual_degree x hx hadj
    omega
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G)
    (shadow_subset_ambient C hwU) hnot
  constructor
  · rwa [heq] at hxlow
  · intro hxw
    subst x
    exact (mem_sdiff.mp hx).2 (root_mem_shadow C w)

/-- If the root is the only old low-degree vertex and its shadow is proper, the complement is
a nonempty induced subgraph of minimum degree at least `k`. -/
theorem shadow_complement_minDegree_of_unique_low
    (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hproper : shadow C w ≠ U)
    (hunique : ∀ x ∈ U, degreeOn G U x ≤ k - 1 → x = w) :
    HasMinDegreeOn G (U \ shadow C w) k := by
  have hsub := shadow_subset_ambient C hwU
  have hnonempty : (U \ shadow C w).Nonempty := by
    by_contra hempty
    have hUsub : U ⊆ shadow C w := by
      intro x hxU
      by_contra hxsh
      exact hempty ⟨x, mem_sdiff.mpr ⟨hxU, hxsh⟩⟩
    exact hproper (Subset.antisymm hsub hUsub)
  refine ⟨hnonempty, ?_⟩
  intro x hx
  by_contra hnot
  have hxlow : degreeOn G (U \ shadow C w) x ≤ k - 1 := by omega
  have hold := low_degree_after_delete_shadow C hk hwU hwdeg hx hxlow
  exact hold.2 (hunique x (mem_sdiff.mp hx).1 hold.1)

/-! ## Transporting protected families -/

/-- Enlarging the ambient vertex set can only enlarge the set of incident edges of a fixed
deletion set. -/
lemma incidentCount_ambient_mono {A B X : Finset V} (hAB : A ⊆ B) :
    incidentCount G A X ≤ incidentCount G B X := by
  unfold incidentCount
  apply card_le_card
  intro e he
  rcases mem_sdiff.mp he with ⟨heA, hnotA⟩
  refine mem_sdiff.mpr ⟨edgeOn_mono G hAB heA, ?_⟩
  intro heBX
  apply hnotA
  apply mem_edgeOn.mpr
  refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
  intro x hx
  exact mem_sdiff.mpr
    ⟨(mem_edgeOn.mp heA).2 hx, (mem_sdiff.mp ((mem_edgeOn.mp heBX).2 hx)).2⟩

/-- If an extension adds no edge from its new vertices to `D ⊆ U`, then the number of
edges incident with `D` is unchanged. -/
lemma incidentCount_extension_eq {A D : Finset V} (hUA : U ⊆ A) (hDU : D ⊆ U)
    (hanti : ¬ AdjacentSets G (A \ U) D) :
    incidentCount G A D = incidentCount G U D := by
  apply Nat.le_antisymm
  · unfold incidentCount
    apply card_le_card
    intro e he
    rcases mem_sdiff.mp he with ⟨heA, hnotAD⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
            (mem_edgeOn.mp heA).1
        have hsubA := (mem_edgeOn.mp heA).2
        have hxA : x ∈ A := hsubA (by simp [Sym2.toFinset_mk_eq])
        have hyA : y ∈ A := hsubA (by simp [Sym2.toFinset_mk_eq])
        have hxyD : x ∈ D ∨ y ∈ D := by
          by_contra hnone
          have hxD : x ∉ D := fun hx ↦ hnone (Or.inl hx)
          have hyD : y ∉ D := fun hy ↦ hnone (Or.inr hy)
          apply hnotAD
          apply mem_edgeOn.mpr
          refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
          intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact mem_sdiff.mpr ⟨hxA, hxD⟩
          · exact mem_sdiff.mpr ⟨hyA, hyD⟩
        have hxU : x ∈ U := by
          rcases hxyD with hxD | hyD
          · exact hDU hxD
          · by_contra hxU
            apply hanti
            exact ⟨x, mem_sdiff.mpr ⟨hxA, hxU⟩, y, hyD, hxy⟩
        have hyU : y ∈ U := by
          rcases hxyD with hxD | hyD
          · by_contra hyU
            apply hanti
            exact ⟨y, mem_sdiff.mpr ⟨hyA, hyU⟩, x, hxD, hxy.symm⟩
          · exact hDU hyD
        refine mem_sdiff.mpr ⟨mem_edgeOn.mpr ⟨(mem_edgeOn.mp heA).1, ?_⟩, ?_⟩
        · intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact hxU
          · exact hyU
        · intro heUD
          apply hnotAD
          have hsub : U \ D ⊆ A \ D := by
            intro z hz
            exact mem_sdiff.mpr ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
          exact edgeOn_mono G hsub heUD
  · exact incidentCount_ambient_mono (G := G) hUA

/-- Promote a protected family to an induced extension whose new vertices are anticomplete to
every protected block. -/
noncomputable def ProtectedFamily.extendAmbient (C : ProtectedFamily G U k)
    {A : Finset V} (hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D) :
    ProtectedFamily G A k where
  blocks := C.blocks
  nonempty := C.nonempty
  subset_ambient := by
    intro D hD
    exact (C.subset_ambient D hD).trans hUA
  pairwise_disjoint := C.pairwise_disjoint
  high_degree := by
    intro D hD x hxD
    exact (C.high_degree D hD x hxD).trans
      (degreeOn_mono G hUA x)
  incident_le := by
    intro D hD
    rw [incidentCount_extension_eq (G := G) hUA (C.subset_ambient D hD) (hnew D hD)]
    exact C.incident_le D hD

@[simp] lemma ProtectedFamily.extendAmbient_blocks
    (C : ProtectedFamily G U k) {A : Finset V} (hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D) :
    (C.extendAmbient hUA hnew).blocks = C.blocks := by
  rfl

/-! ## Comparison with an induced extension -/

/-- A neighbour in the genuinely new part witnesses strict degree growth, even after deleting
an old set `Y`. -/
private lemma degreeOn_extension_sdiff_add_one_le
    {A Y : Finset V} {x : V} (hUA : U ⊆ A) (hYU : Y ⊆ U)
    (hadj : AdjacentSets G {x} (A \ U)) :
    degreeOn G (U \ Y) x + 1 ≤ degreeOn G (A \ Y) x := by
  unfold degreeOn
  apply Nat.succ_le_iff.mpr
  apply card_lt_card
  constructor
  · intro z hz
    rcases mem_inter.mp hz with ⟨hxz, hz⟩
    exact mem_inter.mpr ⟨hxz, mem_sdiff.mpr
      ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩⟩
  · intro hreverse
    rcases hadj with ⟨a, ha, y, hy, hay⟩
    have hax : a = x := by simpa using ha
    subst a
    have hyA := (mem_sdiff.mp hy).1
    have hyU := (mem_sdiff.mp hy).2
    have hyY : y ∉ Y := fun hyin ↦ hyU (hYU hyin)
    have hybig : y ∈ G.neighborFinset x ∩ (A \ Y) := by
      exact mem_inter.mpr
        ⟨by simpa [SimpleGraph.mem_neighborFinset] using hay,
          mem_sdiff.mpr ⟨hyA, hyY⟩⟩
    have hysmall := hreverse hybig
    exact hyU (mem_sdiff.mp (mem_inter.mp hysmall).2).1

/-- If a singleton step has one full unit of degree slack, it raises potential by at least one. -/
private lemma vertex_step_potential_add_one_le
    {Y : Finset V} {x : V} (hxU : x ∈ U) (hxY : x ∉ Y)
    (hdeg : degreeOn G (U \ Y) x + 1 ≤ k - 1) :
    deletionPotential k G U Y + 1 ≤ deletionPotential k G U (Y ∪ {x}) := by
  have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
  have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
  have hinc := shadow_incidentCount_insert (G := G) hx
  simp only [union_singleton] at hinc ⊢
  unfold deletionPotential
  rw [hcard, hinc]
  push_cast
  have hdegZ : (degreeOn G (U \ Y) x : ℤ) + 1 ≤ ((k - 1 : ℕ) : ℤ) := by
    exact_mod_cast hdeg
  ring_nf
  omega

/-- If the terminal shadow has potential zero, every intermediate set in every legal run has
potential zero as well. -/
lemma potential_eq_zero_of_shadowReachable
    (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (hreach : ShadowReachable C {w} Y) :
    deletionPotential k G U Y = 0 := by
  have hnonneg := (shadowReachable_accounting C hk hwU hwdeg hreach).1
  have hsat := shadowSaturate_reachable C Y
  have hrootSat : ShadowReachable C {w} (shadowSaturate C Y) := hreach.trans hsat
  have heq : shadowSaturate C Y = shadow C w :=
    shadow_choice_independent C hk hwU hwdeg hrootSat (shadowSaturate_terminal C Y)
  have hYU : Y ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
  have hmono := shadowReachable_potential_mono hYU hsat
  rw [heq, hzero] at hmono
  omega

/-- Every run of the extension shadow can be simulated in the old graph; at potential zero it
never acquires an edge to a genuinely new vertex. -/
lemma shadowReachable_extension_simulation
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    {Y : Finset V}
    (hreachA : ShadowReachable (C.extendAmbient hUA hnew) {w} Y) :
    ShadowReachable C {w} Y ∧ ¬ AdjacentSets G Y (A \ U) := by
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hwexact := (shadow_zero_unique_low C hk hwU hwdeg hzero).2
  induction hreachA with
  | refl =>
      refine ⟨Relation.ReflTransGen.refl, ?_⟩
      intro hadj
      have hstrict := degreeOn_extension_sdiff_add_one_le
        (G := G) hUA (empty_subset U) hadj
      simp only [sdiff_empty] at hstrict
      omega
  | @tail Ycur Zcur hreachA hstep ih =>
      rcases ih with ⟨hreachOld, hantiY⟩
      cases hstep with
      | vertex x hxA hxY hfreeA hadj hdegA =>
          have hxU : x ∈ U := by
            by_contra hxU
            apply hantiY
            rcases hadj with ⟨a, ha, y, hy, hay⟩
            have hax : a = x := by simpa using ha
            subst a
            exact ⟨y, hy, x, mem_sdiff.mpr ⟨hxA, hxU⟩, hay.symm⟩
          have hfree : C.Free x := by
            intro D hD hxD
            exact hfreeA D (by simpa using hD) hxD
          have hsub : U \ Ycur ⊆ A \ Ycur := by
            intro z hz
            exact mem_sdiff.mpr ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
          have hdegOld : degreeOn G (U \ Ycur) x ≤ k - 1 :=
            (degreeOn_mono G hsub x).trans hdegA
          have hstepOld : ShadowStep C Ycur (Ycur ∪ {x}) :=
            ShadowStep.vertex Ycur x hxU hxY hfree hadj hdegOld
          have hreachOld' := Relation.ReflTransGen.tail hreachOld hstepOld
          refine ⟨hreachOld', ?_⟩
          intro hadjNew
          rcases hadjNew with ⟨z, hz, a, ha, hza⟩
          rcases mem_union.mp hz with hzY | hzx
          · exact hantiY ⟨z, hzY, a, ha, hza⟩
          · have hzx' : z = x := by simpa using hzx
            subst z
            have hcross : AdjacentSets G {x} (A \ U) :=
              ⟨x, by simp, a, ha, hza⟩
            have hstrictDeg := degreeOn_extension_sdiff_add_one_le
              (G := G) hUA (shadowReachable_subset_ambient (by simpa) hreachOld) hcross
            have hslack : degreeOn G (U \ Ycur) x + 1 ≤ k - 1 :=
              hstrictDeg.trans hdegA
            have hstrictPot := vertex_step_potential_add_one_le
              (G := G) hxU hxY hslack
            have hpotY := potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hreachOld
            have hpotZ := potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hreachOld'
            rw [hpotY, hpotZ] at hstrictPot
            omega
      | block D hD hdisj hadj =>
          have hDold : D ∈ C.blocks := by simpa using hD
          have hstepOld : ShadowStep C Ycur (Ycur ∪ D) :=
            ShadowStep.block Ycur D hDold hdisj hadj
          refine ⟨Relation.ReflTransGen.tail hreachOld hstepOld, ?_⟩
          intro hadjNew
          rcases hadjNew with ⟨z, hz, a, ha, hza⟩
          rcases mem_union.mp hz with hzY | hzD
          · exact hantiY ⟨z, hzY, a, ha, hza⟩
          · exact hnew D hDold ⟨a, ha, z, hzD, hza.symm⟩

/-- Shadow comparison in an induced extension (Sauermann's shadow-extension lemma). -/
theorem shadow_stable_in_extension
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shadow (C.extendAmbient hUA hnew) w ⊆ shadow C w ∧
      ¬ AdjacentSets G (shadow (C.extendAmbient hUA hnew) w) (A \ U) := by
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hsim := shadowReachable_extension_simulation C hk hUA hwU hwlowA hnew hzero
    (shadow_reachable (C.extendAmbient hUA hnew) w)
  refine ⟨?_, hsim.2⟩
  exact shadowReachable_subset_of_closed hk
    (singleton_subset_iff.mpr (root_mem_shadow C w))
    (shadow_closed C hk hwU hwdeg) hsim.1

/-- The extension shadow in the comparison lemma also has zero potential in the extension. -/
theorem extension_shadow_potential_eq_zero
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    deletionPotential k G A (shadow (C.extendAmbient hUA hnew) w) = 0 := by
  let W := shadow (C.extendAmbient hUA hnew) w
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hsim := shadowReachable_extension_simulation C hk hUA hwU hwlowA hnew hzero
    (shadow_reachable (C.extendAmbient hUA hnew) w)
  have hWU : W ⊆ U := shadowReachable_subset_ambient (by simpa) hsim.1
  have hanti : ¬ AdjacentSets G (A \ U) W := by
    intro hadj
    exact hsim.2 hadj.symm
  have hinc : incidentCount G A W = incidentCount G U W :=
    incidentCount_extension_eq (G := G) hUA hWU hanti
  have hpotOld : deletionPotential k G U W = 0 :=
    potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hsim.1
  unfold deletionPotential at hpotOld ⊢
  rw [hinc]
  exact hpotOld

/-- Consequently, deleting the extension shadow preserves the extension's signed shortage. -/
theorem shortage_delete_extension_shadow_eq
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shortage k G (A \ shadow (C.extendAmbient hUA hnew) w) = shortage k G A := by
  have hWA : shadow (C.extendAmbient hUA hnew) w ⊆ A :=
    shadow_subset_ambient (C.extendAmbient hUA hnew) (hUA hwU)
  rw [shortage_sdiff k G hWA,
    extension_shadow_potential_eq_zero C hk hUA hwU hwlowA hnew hzero, sub_zero]

/-- A protected block that is retained outside the shadow has no edge to the shadow. -/
lemma shadow_anticomplete_block_of_disjoint (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    {D : Finset V} (hD : D ∈ C.blocks) (hdisj : Disjoint D (shadow C w)) :
    ¬ AdjacentSets G D (shadow C w) := by
  intro hadj
  have hinside := (shadow_closed C hk hwU hwdeg).adjacent_blocks D hD hadj
  obtain ⟨x, hxD⟩ := C.nonempty D hD
  exact (Finset.disjoint_left.mp hdisj) hxD (hinside hxD)

/-- Every block retained in the complement of a shadow remains a protected block there. -/
noncomputable def ProtectedFamily.restrictShadowComplement (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    ProtectedFamily G (U \ shadow C w) k where
  blocks := C.blocks.filter fun D ↦ D ⊆ U \ shadow C w
  nonempty := by
    intro D hD
    exact C.nonempty D (mem_filter.mp hD).1
  subset_ambient := by
    intro D hD
    exact (mem_filter.mp hD).2
  pairwise_disjoint := by
    intro D hD E hE hne
    exact C.pairwise_disjoint D (mem_filter.mp hD).1 E (mem_filter.mp hE).1 hne
  high_degree := by
    intro D hD x hxD
    have hDold := (mem_filter.mp hD).1
    have hDsub := (mem_filter.mp hD).2
    have hdisj : Disjoint D (shadow C w) := by
      rw [Finset.disjoint_left]
      intro y hyD hysh
      exact (mem_sdiff.mp (hDsub hyD)).2 hysh
    have hanti := shadow_anticomplete_block_of_disjoint C hk hwU hwdeg hDold hdisj
    have hnotx : ¬ AdjacentSets G {x} (shadow C w) := by
      intro hadj
      apply hanti
      rcases hadj with ⟨a, ha, y, hy, hay⟩
      have hax : a = x := by simpa using ha
      subst a
      exact ⟨x, hxD, y, hy, hay⟩
    rw [degreeOn_sdiff_eq_of_not_adjacent (G := G)
      (shadow_subset_ambient C hwU) hnotx]
    exact C.high_degree D hDold x hxD
  incident_le := by
    intro D hD
    exact (incidentCount_ambient_mono (G := G) sdiff_subset).trans
      (C.incident_le D (mem_filter.mp hD).1)

@[simp] lemma ProtectedFamily.mem_restrictShadowComplement_blocks
    (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    {D : Finset V} :
    D ∈ (C.restrictShadowComplement hk hwU hwdeg).blocks ↔
      D ∈ C.blocks ∧ D ⊆ U \ shadow C w := by
  simp [ProtectedFamily.restrictShadowComplement]

end Erdos814
