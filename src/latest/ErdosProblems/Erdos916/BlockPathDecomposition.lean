/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.ThreeTerminalCut
import ErdosProblems.Erdos916.Torso
import ErdosProblems.Erdos916.WatkinsMesner
import ErdosProblems.Erdos916.CircuitTwins
import ErdosProblems.Erdos916.ThreeTerminalPath

/-!
# Recursive block certificates for three-terminal paths

This file contains the block-tree bookkeeping behind the three-terminal
path alternative.  The recursion is binary at a cut vertex: one component
of `G - d`, with `d` restored, is split from its complementary cut piece.
If a recursive call returns a block certificate, the peeled piece is added
as one further block.  The exact edge and vertex equations come from
`CutDensity`.

Unlike the false single-cut formulation, this construction records
successive cuts.  Thus examples with a central block and three pendant
terminal branches are represented by three or more blocks.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace BlockCountCertificate

/-- The one-block certificate consisting of the whole vertex set. -/
def whole (G : SimpleGraph V) [DecidableRel G.Adj]
    (htwo : 2 ≤ Fintype.card V) : BlockCountCertificate G 1 where
  blocks := fun _ => Finset.univ
  two_le_card := fun _ => by simpa
  vertex_sum_add_one := by simp
  edge_sum := by
    simp only [Fin.sum_univ_one]
    have h := G.card_filter_edgeFinset_toFinset_subset (Finset.univ : Finset V)
    rw [G.filter_edgeFinset_toFinset_subset] at h
    simpa using h.symm

namespace Lift

variable (G)

/-- Image in the ambient vertex type of a finset in an induced graph. -/
def block {P : Finset V} (B : Finset P) : Finset V :=
  B.image Subtype.val

@[simp] theorem card_block {P : Finset V} (B : Finset P) :
    (block B).card = B.card := by
  exact Finset.card_image_of_injective B Subtype.val_injective

@[simp] theorem coe_block {P : Finset V} (B : Finset P) :
    ((block B : Finset V) : Set V) = Subtype.val '' (B : Set P) := by
  ext x
  simp [block]

/-- Inducing inside an induced graph agrees, up to the evident subtype
isomorphism, with inducing on the ambient image of the inner vertex set. -/
noncomputable def induceIso {P : Finset V} (B : Finset P) :
    (G.induce (P : Set V)).induce (B : Set P) ≃g
      G.induce (block B : Set V) := by
  let e : {x : P // x ∈ (B : Set P)} ≃
      {x : V // x ∈ (block B : Set V)} := by
    let f : {x : P // x ∈ (B : Set P)} →
        {x : V // x ∈ (block B : Set V)} :=
      fun x => ⟨x.1.1, by simp [block, x.2]⟩
    refine Equiv.ofBijective f ?_
    · constructor
      · intro x y h
        have hval : x.1.1 = y.1.1 :=
          congrArg (fun z : {x : V // x ∈ (block B : Set V)} => z.1) h
        apply Subtype.ext
        exact Subtype.ext hval
      · rintro ⟨x, hx⟩
        simp only [block, Finset.mem_coe, Finset.mem_image] at hx
        obtain ⟨y, hyB, hyx⟩ := hx
        subst x
        exact ⟨⟨y, hyB⟩, rfl⟩
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro x y
      rfl }

theorem card_edges_block {P : Finset V} (B : Finset P) :
    ((G.induce (P : Set V)).induce (B : Set P)).edgeFinset.card =
      (G.induce (block B : Set V)).edgeFinset.card := by
  exact (induceIso G B).card_edgeFinset_eq

end Lift

/-- Adjoin the selected component piece as one new block to a block
certificate for the complementary cut piece. -/
noncomputable def adjoinPiece
    {d : V} (hd : IsCutVertex G d)
    (K : (deleteVertex G d).ConnectedComponent) {k : ℕ}
    (D : BlockCountCertificate
      (G.induce (CutDensity.remainder G d K : Set V)) k) :
    BlockCountCertificate G (k + 1) := by
  classical
  let P := CutDensity.piece G d K
  let R := CutDensity.remainder G d K
  let lifted : Fin k → Finset V := fun i => Lift.block (D.blocks i)
  have hPtwo : 2 ≤ P.card := by
    have hdP : d ∈ P := CutDensity.cut_mem_piece G d K
    obtain ⟨x, hx⟩ := ComponentEndBlock.side_nonempty (G := G) d K
    have hxP : x ∈ P := (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hx)
    have hxd : x ≠ d := by
      intro h
      subst x
      exact ComponentEndBlock.cut_not_mem_side (G := G) d K hx
    exact Finset.one_lt_card_iff.mpr ⟨d, x, hdP, hxP, hxd.symm⟩
  have hblocksCard : ∀ i, (lifted i).card = (D.blocks i).card := by
    intro i
    exact Lift.card_block (D.blocks i)
  have hedgeLift (i : Fin k) :
      ((G.induce (R : Set V)).induce (D.blocks i : Set R)).edgeFinset.card =
        (G.induce (lifted i : Set V)).edgeFinset.card := by
    exact Lift.card_edges_block G (D.blocks i)
  exact {
    blocks := Fin.cases P lifted
    two_le_card := by
      intro i
      refine Fin.cases hPtwo (fun j => ?_) i
      change 2 ≤ (lifted j).card
      rw [hblocksCard]
      exact D.two_le_card j
    vertex_sum_add_one := by
      rw [Fin.sum_univ_succ]
      change P.card + (∑ i : Fin k, (lifted i).card) + 1 = _
      have hsumCard : (∑ i : Fin k, (lifted i).card) =
          ∑ i : Fin k, (D.blocks i).card := by
        apply Finset.sum_congr rfl
        intro i _
        exact hblocksCard i
      rw [hsumCard]
      have hD := D.vertex_sum_add_one
      have hcut := CutDensity.card_piece_add_card_remainder (G := G) d K
      have hRcard :
          Fintype.card {x : V // x ∈
            (CutDensity.remainder G d K : Set V)} =
              (CutDensity.remainder G d K).card := by
        rw [Set.fintypeCard_eq_ncard]
        exact Set.ncard_coe_finset _
      rw [hRcard] at hD
      dsimp only [P, R]
      omega
    edge_sum := by
      rw [Fin.sum_univ_succ]
      change (G.induce (P : Set V)).edgeFinset.card +
        (∑ i : Fin k, (G.induce (lifted i : Set V)).edgeFinset.card) = _
      have hsumEdges :
          (∑ i : Fin k,
              (G.induce (lifted i : Set V)).edgeFinset.card) =
            (G.induce (R : Set V)).edgeFinset.card := by
        rw [← D.edge_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (hedgeLift i).symm
      rw [hsumEdges]
      have hcut := CutDensity.card_edges_piece_add_card_edges_remainder
        (G := G) d K
      dsimp only [P, R]
      omega }

/-- Every genuine cut gives the two-block counting certificate associated
to either one component of the deleted graph and its complement. -/
noncomputable def ofCut
    {d : V} (hd : IsCutVertex G d)
    (K : (deleteVertex G d).ConnectedComponent) :
    BlockCountCertificate G 2 := by
  classical
  let R := CutDensity.remainder G d K
  have hRtwo : 2 ≤ R.card := by
    have hproper : CutDensity.piece G d K ≠ Finset.univ :=
      CutDensity.piece_ne_univ (G := G) hd K
    obtain ⟨x, hxP⟩ : ∃ x : V, x ∉ CutDensity.piece G d K := by
      by_contra h
      push_neg at h
      exact hproper (Finset.eq_univ_of_forall h)
    have hxR : x ∈ R := by
      apply (CutDensity.mem_remainder_iff (G := G)).mpr
      intro hxside
      exact hxP ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hxside))
    have hdR : d ∈ R := CutDensity.cut_mem_remainder (G := G) d K
    have hdx : d ≠ x := by
      intro h
      subst x
      exact hxP (CutDensity.cut_mem_piece (G := G) d K)
    exact Finset.one_lt_card_iff.mpr ⟨d, x, hdR, hxR, hdx⟩
  have hRcard : 2 ≤ Fintype.card R := by simpa using hRtwo
  simpa using
    (adjoinPiece (G := G) hd K
      (whole (G.induce (R : Set V)) hRcard))

/-- The symmetric lifting operation: adjoin the complementary cut piece to
a certificate on the selected component piece. -/
noncomputable def adjoinRemainder
    {d : V} (hd : IsCutVertex G d)
    (K : (deleteVertex G d).ConnectedComponent) {k : ℕ}
    (D : BlockCountCertificate
      (G.induce (CutDensity.piece G d K : Set V)) k) :
    BlockCountCertificate G (k + 1) := by
  classical
  let P := CutDensity.piece G d K
  let R := CutDensity.remainder G d K
  let lifted : Fin k → Finset V := fun i => Lift.block (D.blocks i)
  have hRtwo : 2 ≤ R.card := by
    have hproper : P ≠ Finset.univ :=
      CutDensity.piece_ne_univ (G := G) hd K
    obtain ⟨x, hxP⟩ : ∃ x : V, x ∉ P := by
      by_contra h
      push Not at h
      exact hproper (Finset.eq_univ_of_forall h)
    have hxR : x ∈ R := by
      apply (CutDensity.mem_remainder_iff (G := G)).mpr
      intro hxside
      exact hxP ((CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hxside))
    have hdR : d ∈ R := CutDensity.cut_mem_remainder (G := G) d K
    have hdx : d ≠ x := by
      intro h
      subst x
      exact hxP (CutDensity.cut_mem_piece (G := G) d K)
    exact Finset.one_lt_card_iff.mpr ⟨d, x, hdR, hxR, hdx⟩
  have hblocksCard : ∀ i, (lifted i).card = (D.blocks i).card := by
    intro i
    exact Lift.card_block (D.blocks i)
  have hedgeLift (i : Fin k) :
      ((G.induce (P : Set V)).induce (D.blocks i : Set P)).edgeFinset.card =
        (G.induce (lifted i : Set V)).edgeFinset.card := by
    exact Lift.card_edges_block G (D.blocks i)
  exact {
    blocks := Fin.cases R lifted
    two_le_card := by
      intro i
      refine Fin.cases hRtwo (fun j => ?_) i
      change 2 ≤ (lifted j).card
      rw [hblocksCard]
      exact D.two_le_card j
    vertex_sum_add_one := by
      rw [Fin.sum_univ_succ]
      change R.card + (∑ i : Fin k, (lifted i).card) + 1 = _
      have hsumCard : (∑ i : Fin k, (lifted i).card) =
          ∑ i : Fin k, (D.blocks i).card := by
        apply Finset.sum_congr rfl
        intro i _
        exact hblocksCard i
      rw [hsumCard]
      have hD := D.vertex_sum_add_one
      have hcut := CutDensity.card_piece_add_card_remainder (G := G) d K
      have hPcard : Fintype.card {x : V // x ∈
          (CutDensity.piece G d K : Set V)} =
          (CutDensity.piece G d K).card := by
        rw [Set.fintypeCard_eq_ncard]
        exact Set.ncard_coe_finset _
      rw [hPcard] at hD
      dsimp only [P, R]
      omega
    edge_sum := by
      rw [Fin.sum_univ_succ]
      change (G.induce (R : Set V)).edgeFinset.card +
        (∑ i : Fin k, (G.induce (lifted i : Set V)).edgeFinset.card) = _
      have hsumEdges :
          (∑ i : Fin k, (G.induce (lifted i : Set V)).edgeFinset.card) =
            (G.induce (P : Set V)).edgeFinset.card := by
        rw [← D.edge_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (hedgeLift i).symm
      rw [hsumEdges]
      have hcut := CutDensity.card_edges_piece_add_card_edges_remainder
        (G := G) d K
      dsimp only [P, R]
      omega }

end BlockCountCertificate

namespace ThreeWayCut

variable (T : ThreeWayCut G)

private theorem liftedPieces_pairwise_intersections :
    T.leftPiece ∩ T.middlePiece = {T.cut} ∧
      T.leftPiece ∩ T.rightPiece = {T.cut} ∧
      T.middlePiece ∩ T.rightPiece = {T.cut} := by
  constructor
  · ext x
    simp only [ThreeWayCut.leftPiece, ThreeWayCut.middlePiece,
      Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact hx
      · exact hx
      · exact hy
      · exact False.elim
          (Finset.disjoint_left.mp T.left_disjoint_middle hx hy)
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩
  constructor
  · ext x
    simp only [ThreeWayCut.leftPiece, ThreeWayCut.rightPiece,
      Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact hx
      · exact hx
      · exact hy
      · exact False.elim
          (Finset.disjoint_left.mp T.left_disjoint_right hx hy)
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩
  · ext x
    simp only [ThreeWayCut.middlePiece, ThreeWayCut.rightPiece,
      Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact hx
      · exact hx
      · exact hy
      · exact False.elim
          (Finset.disjoint_left.mp T.middle_disjoint_right hx hy)
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩

private theorem edgeFilters_disjoint (P Q : Finset V)
    (hPQ : P ∩ Q = {T.cut}) :
    Disjoint (G.edgeFinset ∩ P.sym2) (G.edgeFinset ∩ Q.sym2) := by
  rw [Finset.disjoint_left]
  intro e heP heQ
  cases e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
        Finset.mk_mem_sym2_iff] at heP heQ
      have hx : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨heP.2.1, heQ.2.1⟩
      have hy : y ∈ P ∩ Q := Finset.mem_inter.mpr ⟨heP.2.2, heQ.2.2⟩
      rw [hPQ] at hx hy
      simp only [Finset.mem_singleton] at hx hy
      subst x
      subst y
      exact G.loopless.irrefl T.cut heP.1

private theorem edge_mem_piece {x y : V} (hxy : G.Adj x y) :
    (x ∈ T.leftPiece ∧ y ∈ T.leftPiece) ∨
      (x ∈ T.middlePiece ∧ y ∈ T.middlePiece) ∨
      (x ∈ T.rightPiece ∧ y ∈ T.rightPiece) := by
  have hcL : T.cut ∈ T.leftPiece := by simp [ThreeWayCut.leftPiece]
  have hcM : T.cut ∈ T.middlePiece := by simp [ThreeWayCut.middlePiece]
  have hcR : T.cut ∈ T.rightPiece := by simp [ThreeWayCut.rightPiece]
  have hxall : x ∈ insert T.cut (T.left ∪ T.middle ∪ T.right) := by
    rw [T.cover]
    exact Finset.mem_univ x
  have hyall : y ∈ insert T.cut (T.left ∪ T.middle ∪ T.right) := by
    rw [T.cover]
    exact Finset.mem_univ y
  simp only [Finset.mem_insert, Finset.mem_union] at hxall hyall
  rcases hxall with hx | ((hxL | hxM) | hxR)
  · subst x
    rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y; exact False.elim (G.loopless.irrefl T.cut hxy)
    · exact Or.inl ⟨hcL, Finset.mem_insert_of_mem hyL⟩
    · exact Or.inr (Or.inl ⟨hcM, Finset.mem_insert_of_mem hyM⟩)
    · exact Or.inr (Or.inr ⟨hcR, Finset.mem_insert_of_mem hyR⟩)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y; exact Or.inl ⟨Finset.mem_insert_of_mem hxL, hcL⟩
    · exact Or.inl ⟨Finset.mem_insert_of_mem hxL,
        Finset.mem_insert_of_mem hyL⟩
    · exact False.elim (T.not_adj_left_middle x hxL y hyM hxy)
    · exact False.elim (T.not_adj_left_right x hxL y hyR hxy)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact Or.inr (Or.inl ⟨Finset.mem_insert_of_mem hxM, hcM⟩)
    · exact False.elim (T.not_adj_left_middle y hyL x hxM hxy.symm)
    · exact Or.inr (Or.inl ⟨Finset.mem_insert_of_mem hxM,
        Finset.mem_insert_of_mem hyM⟩)
    · exact False.elim (T.not_adj_middle_right x hxM y hyR hxy)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact Or.inr (Or.inr ⟨Finset.mem_insert_of_mem hxR, hcR⟩)
    · exact False.elim (T.not_adj_left_right y hyL x hxR hxy.symm)
    · exact False.elim (T.not_adj_middle_right y hyM x hxR hxy.symm)
    · exact Or.inr (Or.inr ⟨Finset.mem_insert_of_mem hxR,
        Finset.mem_insert_of_mem hyR⟩)

private theorem edgeFilters_union :
    ((G.edgeFinset ∩ T.leftPiece.sym2) ∪
      (G.edgeFinset ∩ T.middlePiece.sym2)) ∪
      (G.edgeFinset ∩ T.rightPiece.sym2) = G.edgeFinset := by
  ext e
  constructor
  · simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro he
    cases e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := by simpa using he
      rcases T.edge_mem_piece hxy with hL | hM | hR
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inl (Or.inl ⟨hxy, hL⟩)
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inl (Or.inr ⟨hxy, hM⟩)
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inr ⟨hxy, hR⟩

/-- A three-way cut supplies the corresponding three-block counting
certificate, with no maximal-block theory required. -/
noncomputable def toBlockCountCertificate : BlockCountCertificate G 3 := by
  classical
  let pieces : Fin 3 → Finset V
    | 0 => T.leftPiece
    | 1 => T.middlePiece
    | 2 => T.rightPiece
  have hLcard : T.leftPiece.card = T.left.card + 1 := by
    simp [ThreeWayCut.leftPiece, T.cut_not_left]
  have hMcard : T.middlePiece.card = T.middle.card + 1 := by
    simp [ThreeWayCut.middlePiece, T.cut_not_middle]
  have hRcard : T.rightPiece.card = T.right.card + 1 := by
    simp [ThreeWayCut.rightPiece, T.cut_not_right]
  have htwoL : 2 ≤ T.leftPiece.card := by
    obtain ⟨x, hx⟩ := T.left_nonempty
    have hxcard : 1 ≤ T.left.card := Finset.one_le_card.mpr ⟨x, hx⟩
    rw [hLcard]
    omega
  have htwoM : 2 ≤ T.middlePiece.card := by
    obtain ⟨x, hx⟩ := T.middle_nonempty
    have hxcard : 1 ≤ T.middle.card := Finset.one_le_card.mpr ⟨x, hx⟩
    rw [hMcard]
    omega
  have htwoR : 2 ≤ T.rightPiece.card := by
    obtain ⟨x, hx⟩ := T.right_nonempty
    have hxcard : 1 ≤ T.right.card := Finset.one_le_card.mpr ⟨x, hx⟩
    rw [hRcard]
    omega
  have hsideCard :
      T.left.card + T.middle.card + T.right.card + 1 = Fintype.card V := by
    have hcoverCard := congrArg Finset.card T.cover
    have hLMR : Disjoint (T.left ∪ T.middle) T.right :=
      Finset.disjoint_union_left.mpr
        ⟨T.left_disjoint_right, T.middle_disjoint_right⟩
    rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint hLMR,
      Finset.card_union_of_disjoint T.left_disjoint_middle,
      Finset.card_univ] at hcoverCard
    · omega
    · simp only [Finset.mem_union]
      rintro ((hL | hM) | hR)
      · exact T.cut_not_left hL
      · exact T.cut_not_middle hM
      · exact T.cut_not_right hR
  refine {
    blocks := pieces
    two_le_card := ?_
    vertex_sum_add_one := ?_
    edge_sum := ?_ }
  · intro i
    fin_cases i
    · exact htwoL
    · exact htwoM
    · exact htwoR
  · simp only [Fin.sum_univ_three]
    change T.leftPiece.card + T.middlePiece.card + T.rightPiece.card + 1 = _
    omega
  · simp only [Fin.sum_univ_three]
    change (G.induce (T.leftPiece : Set V)).edgeFinset.card +
      (G.induce (T.middlePiece : Set V)).edgeFinset.card +
      (G.induce (T.rightPiece : Set V)).edgeFinset.card = _
    have hinter := T.liftedPieces_pairwise_intersections
    have hLM := T.edgeFilters_disjoint T.leftPiece T.middlePiece hinter.1
    have hLR := T.edgeFilters_disjoint T.leftPiece T.rightPiece hinter.2.1
    have hMR := T.edgeFilters_disjoint T.middlePiece T.rightPiece hinter.2.2
    have hLMR : Disjoint
        ((G.edgeFinset ∩ T.leftPiece.sym2) ∪
          (G.edgeFinset ∩ T.middlePiece.sym2))
        (G.edgeFinset ∩ T.rightPiece.sym2) :=
      Finset.disjoint_union_left.mpr ⟨hLR, hMR⟩
    have hcards := congrArg Finset.card T.edgeFilters_union
    rw [Finset.card_union_of_disjoint hLMR,
      Finset.card_union_of_disjoint hLM] at hcards
    have hL := G.card_filter_edgeFinset_toFinset_subset T.leftPiece
    have hM := G.card_filter_edgeFinset_toFinset_subset T.middlePiece
    have hR := G.card_filter_edgeFinset_toFinset_subset T.rightPiece
    rw [G.filter_edgeFinset_toFinset_subset] at hL hM hR
    omega

end ThreeWayCut

namespace HasThreeTerminalPath

/-- An `a`--`b` path through `c` is already endpoint-normalized. -/
theorem of_path_between_through {a b c : V} (hab : a ≠ b)
    {p : G.Walk a b} (hp : p.IsPath) (hc : c ∈ p.support) :
    HasThreeTerminalPath G a b c := by
  exact ⟨a, b, by simp, by simp, hab, p, hp,
    p.start_mem_support, p.end_mem_support, hc⟩

/-- A terminal path in an induced graph maps to an ambient terminal path. -/
theorem map_induce {S : Set V} {a b c : S}
    (h : HasThreeTerminalPath (G.induce S) a b c) :
    HasThreeTerminalPath G a.1 b.1 c.1 := by
  rcases h with ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
  let inc : G.induce S →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := S)).toHom
  let q : G.Walk x.1 y.1 := p.map inc
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hx' : x.1 ∈ ({a.1, b.1, c.1} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hy' : y.1 ∈ ({a.1, b.1, c.1} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have ha' : a.1 ∈ q.support := by
    change a.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hb' : b.1 ∈ q.support := by
    change b.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hc' : c.1 ∈ q.support := by
    change c.1 ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  exact ⟨x.1, y.1, hx', hy', fun h => hxy (Subtype.ext h),
    q, hq, ha', hb', hc'⟩

theorem swap_left {a b c : V} (h : HasThreeTerminalPath G a b c) :
    HasThreeTerminalPath G b a c := by
  rcases h with ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
  refine ⟨x, y, ?_, ?_, hxy, p, hp, hb, ha, hc⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto

theorem swap_right {a b c : V} (h : HasThreeTerminalPath G a b c) :
    HasThreeTerminalPath G a c b := by
  rcases h with ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
  refine ⟨x, y, ?_, ?_, hxy, p, hp, ha, hc, hb⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto

theorem rotate {a b c : V} (h : HasThreeTerminalPath G a b c) :
    HasThreeTerminalPath G b c a := by
  rcases h with ⟨x, y, hx, hy, hxy, p, hp, ha, hb, hc⟩
  refine ⟨x, y, ?_, ?_, hxy, p, hp, hb, hc, ha⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto

end HasThreeTerminalPath

namespace CutPath

/-- A path from a vertex of a component of `G-d` to `d`, staying in that
component except for its final vertex. -/
theorem exists_path_to_cut_in_component
    (hconn : G.Connected) (d : V)
    (K : (deleteVertex G d).ConnectedComponent) {x : V}
    (hx : x ∈ ComponentEndBlock.side (G := G) d K) :
    ∃ p : G.Walk x d, p.IsPath ∧
      ∀ z, z ∈ p.support →
        z = d ∨ z ∈ ComponentEndBlock.side (G := G) d K := by
  classical
  let S := ComponentEndBlock.verts (G := G) d K
  have hxS : x ∈ S := Set.mem_insert_iff.mpr (Or.inr hx)
  have hdS : d ∈ S := Set.mem_insert d _
  obtain ⟨q, hq⟩ :=
    ((ComponentEndBlock.verts_connected hconn K)
      ⟨x, hxS⟩ ⟨d, hdS⟩).exists_isPath
  let inc : G.induce S →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := S)).toHom
  let p : G.Walk x d := q.map inc
  refine ⟨p, hq.map Subtype.val_injective, ?_⟩
  intro z hz
  change z ∈ (q.map inc).support at hz
  rw [Walk.support_map] at hz
  obtain ⟨w, -, hw⟩ := List.mem_map.mp hz
  have hzS : z ∈ S := by
    have : (w : V) = z := by simpa [inc] using hw
    simpa [this] using w.2
  simpa only [S, ComponentEndBlock.verts, Set.mem_insert_iff] using hzS

theorem component_side_disjoint {d : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L) :
    Disjoint (ComponentEndBlock.side (G := G) d K)
      (ComponentEndBlock.side (G := G) d L) := by
  rw [Set.disjoint_left]
  intro x hxK hxL
  obtain ⟨_, hxK'⟩ := hxK
  obtain ⟨_, hxL'⟩ := hxL
  exact Set.disjoint_left.mp
    (pairwise_disjoint_supp_connectedComponent (deleteVertex G d) hKL)
      hxK' hxL'

/-- Join a component-to-cut path to a rooted path lying in a different
component piece. -/
theorem hasThreeTerminalPath_of_rootedPath_in_component
    (hconn : G.Connected) {d x y z : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L)
    (hx : x ∈ ComponentEndBlock.side (G := G) d K)
    (hz : z ∈ ComponentEndBlock.side (G := G) d L)
    (q : G.Walk d z) (hq : q.IsPath) (hyq : y ∈ q.support)
    (hqside : ∀ w, w ∈ q.support →
      w = d ∨ w ∈ ComponentEndBlock.side (G := G) d L) :
    HasThreeTerminalPath G x y z := by
  obtain ⟨p, hp, hpside⟩ :=
    exists_path_to_cut_in_component hconn d K hx
  let r : G.Walk x z := p.append q
  have hr : r.IsPath := by
    apply Walk.IsPath.append_of_support_inter_eq_endpoint hp hq
    intro w hwp hwq
    rcases hpside w hwp with hwd | hwK
    · exact hwd
    · rcases hqside w hwq with hwd | hwL
      · exact False.elim (ComponentEndBlock.cut_not_mem_side
          (G := G) d K (hwd ▸ hwK))
      · exact False.elim
          (Set.disjoint_left.mp (component_side_disjoint hKL) hwK hwL)
  refine ⟨x, z, by simp, by simp, ?_, r, hr, ?_, ?_, ?_⟩
  · intro hxz
    exact Set.disjoint_left.mp (component_side_disjoint hKL) hx (hxz ▸ hz)
  · exact r.start_mem_support
  · exact Walk.mem_support_append_of_mem_right p q hyq
  · exact r.end_mem_support

/-- Lift a rooted path from a component piece and splice it to a terminal in
a different component. -/
theorem hasThreeTerminalPath_of_induced_rootedPath
    (hconn : G.Connected) {d x y z : V}
    {K L : (deleteVertex G d).ConnectedComponent} (hKL : K ≠ L)
    (hx : x ∈ ComponentEndBlock.side (G := G) d K)
    (hy : y ∈ ComponentEndBlock.side (G := G) d L)
    (hz : z ∈ ComponentEndBlock.side (G := G) d L)
    (q : (G.induce (CutDensity.piece G d L : Set V)).Walk
      ⟨d, CutDensity.cut_mem_piece (G := G) d L⟩
      ⟨z, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hz)⟩)
    (hq : q.IsPath)
    (hyq : (⟨y, (CutDensity.mem_piece_iff (G := G)).mpr (Or.inr hy)⟩ :
      {w : V // w ∈ (CutDensity.piece G d L : Set V)}) ∈ q.support) :
    HasThreeTerminalPath G x y z := by
  let inc : G.induce (CutDensity.piece G d L : Set V) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := (CutDensity.piece G d L : Set V))).toHom
  let qG : G.Walk d z := q.map inc
  have hqG : qG.IsPath := hq.map Subtype.val_injective
  have hyqG : y ∈ qG.support := by
    change y ∈ (q.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨_, hyq, rfl⟩
  have hqside : ∀ w, w ∈ qG.support →
      w = d ∨ w ∈ ComponentEndBlock.side (G := G) d L := by
    intro w hw
    change w ∈ (q.map inc).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨t, -, htw⟩ := List.mem_map.mp hw
    have hwPiece : w ∈ CutDensity.piece G d L := by
      have : (t : V) = w := by simpa [inc] using htw
      change w ∈ (CutDensity.piece G d L : Set V)
      rw [← this]
      exact t.2
    exact (CutDensity.mem_piece_iff (G := G)).mp hwPiece
  exact hasThreeTerminalPath_of_rootedPath_in_component
    hconn hKL hx hz qG hqG hyqG hqside

end CutPath

/-- Either a finite connected graph has the prescribed rooted path, or it
has a genuine cut vertex.  The non-cut case is the three-point path theorem. -/
theorem rootedPath_or_cut
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hconn : H.Connected) {r a b : W}
    (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b) :
    (∃ p : H.Walk r b, p.IsPath ∧ a ∈ p.support) ∨
      ∃ d : W, IsCutVertex H d := by
  classical
  by_cases hcut : ∃ d : W, IsCutVertex H d
  · exact Or.inr hcut
  · left
    have hdelete : ∀ d : W,
        (H.induce fun w : W => w ≠ d).Connected := by
      intro d
      have hpre : (deleteVertex H d).Preconnected :=
        not_not.mp (not_exists.mp hcut d)
      letI : Nonempty {w : W // w ≠ d} := by
        by_cases hdr : r = d
        · exact ⟨⟨a, fun h => hra (hdr.trans h.symm)⟩⟩
        · exact ⟨⟨r, hdr⟩⟩
      change (deleteVertex H d).Connected
      exact SimpleGraph.Connected.mk hpre
    exact exists_rooted_three_path hra hrb hab hconn hdelete

/-- If three distinct terminals of a finite connected graph lie on no
common simple path, the successive cut decomposition has at least three
blocks. -/
theorem exists_threeBlocks_of_no_threeTerminalPath
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hconn : H.Connected) {a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬HasThreeTerminalPath H a b c) :
    ∃ k : ℕ, 3 ≤ k ∧ Nonempty (BlockCountCertificate H k) := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h n ih =>
      by_cases hcut : ∃ d : W, IsCutVertex H d
      · obtain ⟨d, hd⟩ := hcut
        have recurse (K : (deleteVertex H d).ConnectedComponent)
            (ha : a ∈ CutDensity.piece H d K)
            (hb : b ∈ CutDensity.piece H d K)
            (hc : c ∈ CutDensity.piece H d K) :
            ∃ k : ℕ, 3 ≤ k ∧ Nonempty (BlockCountCertificate H k) := by
          let P := CutDensity.piece H d K
          let aP : {w : W // w ∈ (P : Set W)} := ⟨a, ha⟩
          let bP : {w : W // w ∈ (P : Set W)} := ⟨b, hb⟩
          let cP : {w : W // w ∈ (P : Set W)} := ⟨c, hc⟩
          have hproper : P ≠ Finset.univ :=
            CutDensity.piece_ne_univ (G := H) hd K
          have hlt : Fintype.card {w : W // w ∈ (P : Set W)} < n := by
            rw [← hn]
            rw [Set.fintypeCard_eq_ncard]
            rw [Set.ncard_coe_finset]
            exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
          have hconnP : (H.induce (P : Set W)).Connected :=
            CutDensity.piece_connected (G := H) hconn d K
          have habP : aP ≠ bP := fun h => hab (congrArg Subtype.val h)
          have hacP : aP ≠ cP := fun h => hac (congrArg Subtype.val h)
          have hbcP : bP ≠ cP := fun h => hbc (congrArg Subtype.val h)
          have hnoP : ¬HasThreeTerminalPath
              (H.induce (P : Set W)) aP bP cP := by
            intro hp
            exact hno hp.map_induce
          obtain ⟨k, hk, ⟨D⟩⟩ :=
            ih _ hlt (H.induce (P : Set W)) hconnP
              habP hacP hbcP hnoP rfl
          exact ⟨k + 1, by omega,
            ⟨BlockCountCertificate.adjoinRemainder (G := H) hd K D⟩⟩
        have pairCertificate {x y z : W}
            {K L : (deleteVertex H d).ConnectedComponent}
            (hKL : K ≠ L)
            (hx : x ∈ ComponentEndBlock.side (G := H) d K)
            (hy : y ∈ ComponentEndBlock.side (G := H) d L)
            (hz : z ∈ ComponentEndBlock.side (G := H) d L)
            (hdy : d ≠ y) (hdz : d ≠ z) (hyz : y ≠ z)
            (hnoXYZ : ¬HasThreeTerminalPath H x y z) :
            ∃ k : ℕ, 3 ≤ k ∧ Nonempty (BlockCountCertificate H k) := by
          let P := CutDensity.piece H d L
          let dP : {w : W // w ∈ (P : Set W)} :=
            ⟨d, CutDensity.cut_mem_piece (G := H) d L⟩
          let yP : {w : W // w ∈ (P : Set W)} :=
            ⟨y, (CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hy)⟩
          let zP : {w : W // w ∈ (P : Set W)} :=
            ⟨z, (CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hz)⟩
          have hdpy : dP ≠ yP := fun h => hdy (congrArg Subtype.val h)
          have hdpz : dP ≠ zP := fun h => hdz (congrArg Subtype.val h)
          have hypz : yP ≠ zP := fun h => hyz (congrArg Subtype.val h)
          have hconnP : (H.induce (P : Set W)).Connected :=
            CutDensity.piece_connected (G := H) hconn d L
          rcases rootedPath_or_cut (H.induce (P : Set W)) hconnP
              hdpy hdpz hypz with hpath | ⟨e, he⟩
          · obtain ⟨q, hq, hyq⟩ := hpath
            exfalso
            apply hnoXYZ
            exact CutPath.hasThreeTerminalPath_of_induced_rootedPath
              hconn hKL hx hy hz q hq hyq
          · obtain ⟨u, v, huv⟩ :=
              (isCutVertex_iff_exists_not_reachable
                (H.induce (P : Set W)) e).mp he
            let M := (deleteVertex (H.induce (P : Set W)) e).connectedComponentMk u
            let D₂ : BlockCountCertificate (H.induce (P : Set W)) 2 :=
              BlockCountCertificate.ofCut (G := H.induce (P : Set W)) he M
            let D₃ : BlockCountCertificate H 3 := by
              simpa using
                (BlockCountCertificate.adjoinRemainder (G := H) hd L D₂)
            exact ⟨3, by omega, ⟨D₃⟩⟩
        by_cases hda : d = a
        · subst d
          let b' : {w : W // w ≠ a} := ⟨b, hab.symm⟩
          let c' : {w : W // w ≠ a} := ⟨c, hac.symm⟩
          let B := (deleteVertex H a).connectedComponentMk b'
          let C := (deleteVertex H a).connectedComponentMk c'
          have hbB : b ∈ ComponentEndBlock.side (G := H) a B := by
            refine ⟨hab.symm, ?_⟩
            simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
          have hcC : c ∈ ComponentEndBlock.side (G := H) a C := by
            refine ⟨hac.symm, ?_⟩
            simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
          by_cases hBC : B = C
          · have hcB : c ∈ ComponentEndBlock.side (G := H) a B := by
              simpa [hBC] using hcC
            exact recurse B (CutDensity.cut_mem_piece (G := H) a B)
              ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hbB))
              ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hcB))
          · obtain ⟨q, hq, hqside⟩ :=
              CutPath.exists_path_to_cut_in_component hconn a C hcC
            have hp : HasThreeTerminalPath H b a c :=
              CutPath.hasThreeTerminalPath_of_rootedPath_in_component
                hconn hBC hbB hcC q.reverse hq.reverse
                  q.reverse.start_mem_support (by
                    intro w hw
                    have hw' : w ∈ q.support := by
                      simpa [Walk.support_reverse] using hw
                    exact hqside w hw')
            exact False.elim (hno hp.swap_left)
        · by_cases hdb : d = b
          · subst d
            let a' : {w : W // w ≠ b} := ⟨a, hab⟩
            let c' : {w : W // w ≠ b} := ⟨c, hbc.symm⟩
            let A := (deleteVertex H b).connectedComponentMk a'
            let C := (deleteVertex H b).connectedComponentMk c'
            have haA : a ∈ ComponentEndBlock.side (G := H) b A := by
              refine ⟨hab, ?_⟩
              simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
            have hcC : c ∈ ComponentEndBlock.side (G := H) b C := by
              refine ⟨hbc.symm, ?_⟩
              simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
            by_cases hAC : A = C
            · have hcA : c ∈ ComponentEndBlock.side (G := H) b A := by
                simpa [hAC] using hcC
              exact recurse A
                ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr haA))
                (CutDensity.cut_mem_piece (G := H) b A)
                ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hcA))
            · obtain ⟨q, hq, hqside⟩ :=
                CutPath.exists_path_to_cut_in_component hconn b C hcC
              exact False.elim (hno
                (CutPath.hasThreeTerminalPath_of_rootedPath_in_component
                  hconn hAC haA hcC q.reverse hq.reverse
                    q.reverse.start_mem_support (by
                      intro w hw
                      have hw' : w ∈ q.support := by
                        simpa [Walk.support_reverse] using hw
                      exact hqside w hw')))
          · by_cases hdc : d = c
            · subst d
              let a' : {w : W // w ≠ c} := ⟨a, hac⟩
              let b' : {w : W // w ≠ c} := ⟨b, hbc⟩
              let A := (deleteVertex H c).connectedComponentMk a'
              let B := (deleteVertex H c).connectedComponentMk b'
              have haA : a ∈ ComponentEndBlock.side (G := H) c A := by
                refine ⟨hac, ?_⟩
                simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hbB : b ∈ ComponentEndBlock.side (G := H) c B := by
                refine ⟨hbc, ?_⟩
                simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
              by_cases hAB : A = B
              · have hbA : b ∈ ComponentEndBlock.side (G := H) c A := by
                  simpa [hAB] using hbB
                exact recurse A
                  ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr haA))
                  ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hbA))
                  (CutDensity.cut_mem_piece (G := H) c A)
              · obtain ⟨q, hq, hqside⟩ :=
                  CutPath.exists_path_to_cut_in_component hconn c B hbB
                have hp : HasThreeTerminalPath H a c b :=
                  CutPath.hasThreeTerminalPath_of_rootedPath_in_component
                    hconn hAB haA hbB q.reverse hq.reverse
                      q.reverse.start_mem_support (by
                        intro w hw
                        have hw' : w ∈ q.support := by
                          simpa [Walk.support_reverse] using hw
                        exact hqside w hw')
                exact False.elim (hno hp.swap_right)
            · let a' : {w : W // w ≠ d} := ⟨a, Ne.symm hda⟩
              let b' : {w : W // w ≠ d} := ⟨b, Ne.symm hdb⟩
              let c' : {w : W // w ≠ d} := ⟨c, Ne.symm hdc⟩
              let A := (deleteVertex H d).connectedComponentMk a'
              let B := (deleteVertex H d).connectedComponentMk b'
              let C := (deleteVertex H d).connectedComponentMk c'
              have haA : a ∈ ComponentEndBlock.side (G := H) d A := by
                refine ⟨Ne.symm hda, ?_⟩
                simp [A, a', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hbB : b ∈ ComponentEndBlock.side (G := H) d B := by
                refine ⟨Ne.symm hdb, ?_⟩
                simp [B, b', SimpleGraph.ConnectedComponent.mem_supp_iff]
              have hcC : c ∈ ComponentEndBlock.side (G := H) d C := by
                refine ⟨Ne.symm hdc, ?_⟩
                simp [C, c', SimpleGraph.ConnectedComponent.mem_supp_iff]
              by_cases hAB : A = B
              · have hbA : b ∈ ComponentEndBlock.side (G := H) d A := by
                  simpa [hAB] using hbB
                by_cases hAC : A = C
                · have hcA : c ∈ ComponentEndBlock.side (G := H) d A := by
                    simpa [hAC] using hcC
                  exact recurse A
                    ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr haA))
                    ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hbA))
                    ((CutDensity.mem_piece_iff (G := H)).mpr (Or.inr hcA))
                · have hno' : ¬HasThreeTerminalPath H c a b := by
                    intro hp
                    exact hno hp.rotate
                  exact pairCertificate (Ne.symm hAC) hcC haA hbA
                    hda hdb hab hno'
              · by_cases hAC : A = C
                · have hcA : c ∈ ComponentEndBlock.side (G := H) d A := by
                    simpa [hAC] using hcC
                  have hno' : ¬HasThreeTerminalPath H b a c := by
                    intro hp
                    exact hno hp.swap_left
                  exact pairCertificate (Ne.symm hAB) hbB haA hcA
                    hda hdc hac hno'
                · by_cases hBC : B = C
                  · have hcB : c ∈ ComponentEndBlock.side (G := H) d B := by
                      simpa [hBC] using hcC
                    exact pairCertificate hAB haA hbB hcB
                      hdb hdc hbc hno
                  · obtain ⟨T⟩ := threeWayCut_of_three_components
                      d A B C hAB hAC hBC
                    exact ⟨3, by omega, ⟨T.toBlockCountCertificate⟩⟩
      · have hdelete : ∀ d : W,
            (H.induce fun w : W => w ≠ d).Connected := by
          intro d
          have hpre : (deleteVertex H d).Preconnected :=
            not_not.mp (not_exists.mp hcut d)
          letI : Nonempty {w : W // w ≠ d} := by
            by_cases hda : a = d
            · exact ⟨⟨b, fun h => hab (hda.trans h.symm)⟩⟩
            · exact ⟨⟨a, hda⟩⟩
          change (deleteVertex H d).Connected
          exact SimpleGraph.Connected.mk hpre
        obtain ⟨p, hp, hcp⟩ :=
          exists_rooted_three_path hac hab hbc.symm hconn hdelete
        exact False.elim (hno
          (HasThreeTerminalPath.of_path_between_through hab hp hcp))

/-- Endpoint-normalized path versus block-count certificate. -/
theorem threeTerminalPath_or_threeBlocks
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hconn : H.Connected) {a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    HasThreeTerminalPath H a b c ∨
      ∃ k : ℕ, 3 ≤ k ∧ Nonempty (BlockCountCertificate H k) := by
  classical
  by_cases hp : HasThreeTerminalPath H a b c
  · exact Or.inl hp
  · exact Or.inr
      (exists_threeBlocks_of_no_threeTerminalPath H hconn hab hac hbc hp)

/-- Degree-three false twins in a `(2,3)` circuit force a wheel.  Delete the
twins, apply the three-terminal path/block alternative to their three common
neighbours, and discharge either branch with the circuit adapter. -/
theorem Is23Circuit.hasWheelWitness_of_falseTwins
    (hcircuit : Is23Circuit G) {u v : V}
    (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3) :
    HasWheelWitness G := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hNu, -⟩ :=
    exists_common_neighbors_three_of_falseTwins htwin hdeg
  have ha : G.Adj u a := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  have hb : G.Adj u b := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  have hc : G.Adj u c := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  have haD := common_neighbor_mem_deletePair htwin ha
  have hbD := common_neighbor_mem_deletePair htwin hb
  have hcD := common_neighbor_mem_deletePair htwin hc
  have habD :
      (⟨a, haD⟩ : {w : V // w ∈ (({u, v} : Set V)ᶜ)}) ≠ ⟨b, hbD⟩ := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hacD :
      (⟨a, haD⟩ : {w : V // w ∈ (({u, v} : Set V)ᶜ)}) ≠ ⟨c, hcD⟩ := by
    intro h
    exact hac (congrArg Subtype.val h)
  have hbcD :
      (⟨b, hbD⟩ : {w : V // w ∈ (({u, v} : Set V)ᶜ)}) ≠ ⟨c, hcD⟩ := by
    intro h
    exact hbc (congrArg Subtype.val h)
  have hpath_or_blocks := threeTerminalPath_or_threeBlocks
    (deletePair G u v) (hcircuit.deletePair_connected htwin hdeg)
      habD hacD hbcD
  exact hcircuit.hasWheelWitness_of_falseTwins_of_path_or_threeBlocks
    htwin hdeg hab hac hbc ha hb hc hpath_or_blocks

end Erdos916
