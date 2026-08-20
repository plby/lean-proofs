/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Claim 2.3: small rigid separations control safe contractions. -/

import ErdosProblems.Erdos717.RigidSeparation
import ErdosProblems.Erdos717.RestrictLinkage

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

open DenseMinor ContractLinkage

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The quotient map on vertices for contraction of the edge `ab`. -/
def contractProjection {G : SimpleGraph V} {a b : V} (hab : G.Adj a b) :
    V → {z : V // z ≠ b} := fun x =>
  if hx : x = b then ⟨a, hab.ne⟩ else ⟨x, hx⟩

@[simp] lemma contractProjection_b {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    contractProjection hab b = ⟨a, hab.ne⟩ := by
  simp [contractProjection]

@[simp] lemma contractProjection_of_ne {G : SimpleGraph V} {a b x : V}
    (hab : G.Adj a b) (hx : x ≠ b) :
    contractProjection hab x = ⟨x, hx⟩ := by
  simp [contractProjection, hx]

@[simp] lemma contractProjection_a {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    contractProjection hab a = ⟨a, hab.ne⟩ := by
  exact contractProjection_of_ne hab hab.ne

lemma contractAt_adj_projection_of_ne {G : SimpleGraph V} {a b x y : V}
    (hab : G.Adj a b) (hxy : G.Adj x y)
    (hne : contractProjection hab x ≠ contractProjection hab y) :
    (contractAt G a b).Adj (contractProjection hab x)
      (contractProjection hab y) := by
  refine ⟨hne, ?_⟩
  by_cases hx : x = b
  · subst x
    have hy : y ≠ b := by
      intro hy
      exact hxy.ne hy.symm
    rw [contractProjection_b, contractProjection_of_ne hab hy]
    exact Or.inr (Or.inl ⟨rfl, hxy⟩)
  · by_cases hy : y = b
    · subst y
      have hxb : x ≠ b := hx
      rw [contractProjection_of_ne hab hx, contractProjection_b]
      exact Or.inr (Or.inr ⟨rfl, hxy.symm⟩)
    · rw [contractProjection_of_ne hab hx,
        contractProjection_of_ne hab hy]
      exact Or.inl hxy

/-- Lift both endpoints represented by the contracted vertex to the same
sides of a separation. -/
def liftContractSeparation {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (s : Erdos718.Separation (contractAt G a b)) :
    Erdos718.Separation G where
  left := Finset.univ.filter fun x => contractProjection hab x ∈ s.left
  right := Finset.univ.filter fun x => contractProjection hab x ∈ s.right
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact s.mem_left_or_mem_right (contractProjection hab x)
  not_adj := by
    intro x y hxL hxR hyR hyL hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxL hxR hyR hyL
    have hne : contractProjection hab x ≠ contractProjection hab y := by
      intro heq
      exact hxR (heq ▸ hyR)
    exact s.not_adj hxL hxR hyR hyL
      (contractAt_adj_projection_of_ne hab hxy hne)

@[simp] lemma mem_liftContractSeparation_left {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) (x : V) :
    x ∈ (liftContractSeparation hab s).left ↔
      contractProjection hab x ∈ s.left := by
  simp [liftContractSeparation]

@[simp] lemma mem_liftContractSeparation_right {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) (x : V) :
    x ∈ (liftContractSeparation hab s).right ↔
      contractProjection hab x ∈ s.right := by
  simp [liftContractSeparation]

@[simp] lemma mem_liftContractSeparation_separator {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) (x : V) :
    x ∈ (liftContractSeparation hab s).separator ↔
      contractProjection hab x ∈ s.separator := by
  simp [Erdos718.Separation.separator]

@[simp] lemma mem_liftContractSeparation_strictRight {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) (x : V) :
    x ∈ (liftContractSeparation hab s).right \
        (liftContractSeparation hab s).left ↔
      contractProjection hab x ∈ s.right \ s.left := by
  simp [Finset.mem_sdiff]

lemma contractProjection_injective_away_b {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) : Set.InjOn (contractProjection hab) {x | x ≠ b} := by
  intro x hx y hy hxy
  rw [contractProjection_of_ne hab hx,
    contractProjection_of_ne hab hy] at hxy
  exact congrArg Subtype.val hxy

/-- A lifted separator gains at most the second endpoint of the contracted
edge. -/
lemma card_separator_liftContractSeparation_le_add_one
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) :
    (liftContractSeparation hab s).separator.card ≤
      s.separator.card + 1 := by
  classical
  let T := (liftContractSeparation hab s).separator
  have hmaps : Set.MapsTo (contractProjection hab) (T.erase b) s.separator := by
    intro x hx
    have hxT := Finset.mem_of_mem_erase hx
    exact (mem_liftContractSeparation_separator hab s x).mp hxT
  have hinj : Set.InjOn (contractProjection hab) (T.erase b) := by
    apply (contractProjection_injective_away_b hab).mono
    intro x hx
    exact Finset.ne_of_mem_erase hx
  have hcardErase : (T.erase b).card ≤ s.separator.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcardT : T.card ≤ (T.erase b).card + 1 := by
    by_cases hbT : b ∈ T
    · rw [Finset.card_erase_add_one hbT]
    · simp [Finset.erase_eq_of_notMem hbT]
  exact hcardT.trans (Nat.add_le_add_right hcardErase 1)

/-- Away from the contracted vertex, lifting preserves the strict-right
cardinality exactly. -/
lemma card_strictRight_liftContractSeparation_of_not_mem
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b))
    (ha : (⟨a, hab.ne⟩ : {z : V // z ≠ b}) ∉ s.right \ s.left) :
    ((liftContractSeparation hab s).right \
      (liftContractSeparation hab s).left).card =
      (s.right \ s.left).card := by
  classical
  let f : {z : V // z ≠ b} ↪ V := Function.Embedding.subtype _
  have hfinset :
      (liftContractSeparation hab s).right \
          (liftContractSeparation hab s).left =
        (s.right \ s.left).map f := by
    ext x
    rw [mem_liftContractSeparation_strictRight]
    constructor
    · intro hx
      by_cases hxb : x = b
      · subst x
        simp only [contractProjection_b] at hx
        exact (ha hx).elim
      · exact Finset.mem_map.mpr ⟨⟨x, hxb⟩, by
            simpa [contractProjection_of_ne hab hxb] using hx, rfl⟩
    · rintro hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
      have hne : (z : V) ≠ b := z.property
      have hzx' : (z : V) = x := hzx
      subst x
      have hp : contractProjection hab (z : V) = z := by
        rw [contractProjection_of_ne hab hne]
      change contractProjection hab (z : V) ∈ s.right \ s.left
      rwa [hp]
  rw [hfinset, Finset.card_map]

lemma card_separator_liftContractSeparation_of_not_mem
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b))
    (ha : (⟨a, hab.ne⟩ : {z : V // z ≠ b}) ∉ s.separator) :
    (liftContractSeparation hab s).separator.card = s.separator.card := by
  classical
  let f : {z : V // z ≠ b} ↪ V := Function.Embedding.subtype _
  have hfinset : (liftContractSeparation hab s).separator =
      s.separator.map f := by
    ext x
    rw [mem_liftContractSeparation_separator]
    constructor
    · intro hx
      by_cases hxb : x = b
      · subst x
        simp only [contractProjection_b] at hx
        exact (ha hx).elim
      · exact Finset.mem_map.mpr ⟨⟨x, hxb⟩, by
            simpa [contractProjection_of_ne hab hxb] using hx, rfl⟩
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
      have hzx' : (z : V) = x := hzx
      subst x
      change contractProjection hab (z : V) ∈ s.separator
      simpa only [contractProjection_of_ne hab z.property] using hz
  rw [hfinset, Finset.card_map]

/-- If the contracted vertex lies in the strict right side, then the lifted
separation is proper on the right. -/
lemma strictRight_liftContractSeparation_nonempty_of_mem
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b))
    (ha : (⟨a, hab.ne⟩ : {z : V // z ≠ b}) ∈ s.right \ s.left) :
    ((liftContractSeparation hab s).right \
      (liftContractSeparation hab s).left).Nonempty := by
  exact ⟨a, (mem_liftContractSeparation_strictRight hab s a).mpr (by
    simpa using ha)⟩

/-! ### Incident edges under contraction -/

/-- Full inverse image of a contracted vertex finset. -/
def contractPreimageFinset {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (S : Finset {z : V // z ≠ b}) : Finset V :=
  Finset.univ.filter fun x => contractProjection hab x ∈ S

@[simp] lemma mem_contractPreimageFinset {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (S : Finset {z : V // z ≠ b}) (x : V) :
    x ∈ contractPreimageFinset hab S ↔ contractProjection hab x ∈ S := by
  simp [contractPreimageFinset]

/-- Every edge of the contracted graph has an original edge above it. -/
lemma exists_original_edge_of_contract_edge {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b) (e : Sym2 {z : V // z ≠ b})
    (he : e ∈ (contractAt G a b).edgeSet) :
    ∃ E : Sym2 V, E ∈ G.edgeSet ∧
      Sym2.map (contractProjection hab) E = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      change (contractAt G a b).Adj x y at he
      rcases he.2 with hxy | hxy | hxy
      · refine ⟨s((x : V), (y : V)), hxy, ?_⟩
        rw [Sym2.map_pair_eq, contractProjection_of_ne hab x.property,
          contractProjection_of_ne hab y.property]
      · refine ⟨s(b, (y : V)), hxy.2, ?_⟩
        rw [Sym2.map_pair_eq, contractProjection_b,
          contractProjection_of_ne hab y.property]
        rw [Sym2.eq_iff]
        exact Or.inl ⟨Subtype.ext hxy.1.symm, rfl⟩
      · refine ⟨s((x : V), b), hxy.2.symm, ?_⟩
        rw [Sym2.map_pair_eq, contractProjection_of_ne hab x.property,
          contractProjection_b]
        rw [Sym2.eq_iff]
        exact Or.inl ⟨rfl, Subtype.ext hxy.1.symm⟩

/-- Incidence is preserved when an edge is pulled back along the contraction
projection. -/
lemma contract_edge_incident_lift {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (S : Finset {z : V // z ≠ b})
    {e : Sym2 {z : V // z ≠ b}} {E : Sym2 V}
    (hmap : Sym2.map (contractProjection hab) E = e)
    (hinc : ¬e.toFinset ⊆ Finset.univ \ S) :
    ¬E.toFinset ⊆ Finset.univ \ contractPreimageFinset hab S := by
  induction E using Sym2.inductionOn with
  | _ x y =>
      subst e
      rw [Sym2.map_pair_eq, not_pair_subset_compl_iff] at hinc
      rw [not_pair_subset_compl_iff]
      exact hinc.imp
        (fun hx => (mem_contractPreimageFinset hab S x).mpr hx)
        (fun hy => (mem_contractPreimageFinset hab S y).mpr hy)

/-- Contracting an edge cannot increase the number of edges incident with a
set after that set is replaced by its full inverse image. -/
lemma incidentEdges_contract_le_preimage {G : SimpleGraph V}
    [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b)
    (S : Finset {z : V // z ≠ b}) :
    incidentEdges (contractAt G a b) S ≤
      incidentEdges G (contractPreimageFinset hab S) := by
  classical
  let source := ((contractAt G a b).edgeFinset.filter fun e =>
    ¬e.toFinset ⊆ Finset.univ \ S)
  let target := (G.edgeFinset.filter fun E =>
    ¬E.toFinset ⊆ Finset.univ \ contractPreimageFinset hab S)
  have hex (e : source) : ∃ E : Sym2 V,
      E ∈ target ∧ Sym2.map (contractProjection hab) E = (e : Sym2 _) := by
    have he : (e : Sym2 _) ∈ (contractAt G a b).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using
        (Finset.mem_filter.mp e.property).1
    obtain ⟨E, hEG, hmap⟩ := exists_original_edge_of_contract_edge hab e he
    refine ⟨E, ?_, hmap⟩
    rw [Finset.mem_filter]
    exact ⟨(by simpa only [SimpleGraph.mem_edgeFinset] using hEG),
      contract_edge_incident_lift hab S hmap
      (Finset.mem_filter.mp e.property).2⟩
  choose lift hliftMem hliftMap using hex
  have hinj : Function.Injective lift := by
    intro e f hef
    apply Subtype.ext
    rw [← hliftMap e, ← hliftMap f]
    exact congrArg (Sym2.map (contractProjection hab)) hef
  let liftSub : source → target := fun e => ⟨lift e, hliftMem e⟩
  have hinjSub : Function.Injective liftSub := by
    intro e f hef
    apply hinj
    exact congrArg Subtype.val hef
  have hcard : source.card ≤ target.card := by
    exact Finset.card_le_card_of_injective hinjSub
  exact hcard

/-- The strict right side of the lifted separation is the full inverse image
of the old strict right side. -/
lemma strictRight_liftContractSeparation_eq_preimage
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) :
    (liftContractSeparation hab s).right \
        (liftContractSeparation hab s).left =
      contractPreimageFinset hab (s.right \ s.left) := by
  ext x
  simp [Finset.mem_sdiff]

lemma incidentEdges_contract_le_liftStrictRight
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b)) :
    incidentEdges (contractAt G a b) (s.right \ s.left) ≤
      incidentEdges G
        ((liftContractSeparation hab s).right \
          (liftContractSeparation hab s).left) := by
  rw [strictRight_liftContractSeparation_eq_preimage]
  exact incidentEdges_contract_le_preimage hab _

/-! ### Linkedness of the lifted right side -/

/-- When the contracted vertex is in the strict right side, linkedness of
the contracted separator lifts to linkedness of the separator after the two
endpoints are split apart. -/
theorem linked_liftContractSeparation_of_mem_strictRight
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (s : Erdos718.Separation (contractAt G a b))
    (ha : (⟨a, hab.ne⟩ : {z : V // z ≠ b}) ∈ s.right \ s.left)
    (hlinked : Erdos718.IsLinkedSet
      ((contractAt G a b).induce (s.right : Set {z : V // z ≠ b}))
      (rightSeparator s : Set (s.right : Set {z : V // z ≠ b}))) :
    Erdos718.IsLinkedSet
      (G.induce ((liftContractSeparation hab s).right : Set V))
      (rightSeparator (liftContractSeparation hab s) :
        Set ((liftContractSeparation hab s).right : Set V)) := by
  classical
  let t := liftContractSeparation hab s
  intro I inst terminal hrange
  letI : Fintype I := inst
  let terminalV : Sum I I ↪ V :=
    terminal.trans (Function.Embedding.subtype (t.right : Set V))
  have hterminalSep : Set.range terminalV ⊆ (t.separator : Set V) := by
    rintro x ⟨q, rfl⟩
    have hq := hrange ⟨q, rfl⟩
    exact (mem_rightSeparator t (terminal q)).mp hq
  have hbSep : b ∉ t.separator := by
    intro hb
    have hbProjSep := (mem_liftContractSeparation_separator hab s b).mp hb
    rw [Erdos718.Separation.separator, Finset.mem_inter] at hbProjSep
    have ha' := Finset.mem_sdiff.mp ha
    exact ha'.2 (by simpa only [contractProjection_b] using hbProjSep.1)
  have hbRange : b ∉ Set.range terminalV := by
    intro hbR
    exact hbSep (hterminalSep hbR)
  let terminalW : Sum I I ↪ {z : V // z ≠ b} :=
    ContractLinkage.contractTerminal (G := G) (a := a) terminalV hbRange
  have hterminalRight : Set.range terminalW ⊆
      (s.right : Set {z : V // z ≠ b}) := by
    rintro _ ⟨q, rfl⟩
    have hright : (terminal q : V) ∈ t.right := (terminal q).property
    have hp := (mem_liftContractSeparation_right hab s (terminal q : V)).mp hright
    have hne : (terminal q : V) ≠ b := by
      intro heq
      apply hbRange
      exact ⟨q, by
        change (terminal q : V) = b
        exact heq⟩
    have hproj : contractProjection hab (terminal q : V) = terminalW q := by
      rw [contractProjection_of_ne hab hne]
      apply Subtype.ext
      rfl
    rwa [hproj] at hp
  have hterminalSeparator : Set.range terminalW ⊆
      (s.separator : Set {z : V // z ≠ b}) := by
    rintro _ ⟨q, rfl⟩
    have hsep : (terminal q : V) ∈ t.separator :=
      hterminalSep ⟨q, rfl⟩
    have hp := (mem_liftContractSeparation_separator hab s
      (terminal q : V)).mp hsep
    have hne : (terminal q : V) ≠ b := by
      intro heq
      exact hbRange ⟨q, heq⟩
    have hproj : contractProjection hab (terminal q : V) = terminalW q := by
      rw [contractProjection_of_ne hab hne]
      apply Subtype.ext
      rfl
    rwa [hproj] at hp
  let terminalB := terminalIntoSet
    (s.right : Set {z : V // z ≠ b}) terminalW hterminalRight
  have hrangeB : Set.range terminalB ⊆
      (rightSeparator s : Set (s.right : Set {z : V // z ≠ b})) := by
    rintro _ ⟨q, rfl⟩
    change terminalB q ∈ rightSeparator s
    rw [mem_rightSeparator]
    exact hterminalSeparator ⟨q, rfl⟩
  obtain ⟨LB⟩ := hlinked I terminalB hrangeB
  have hsepSet :
      ((rightSeparator s : Finset (s.right : Set {z : V // z ≠ b})) :
          Set (s.right : Set {z : V // z ≠ b})) =
        {z : (s.right : Set {z : V // z ≠ b}) |
          (z : {z : V // z ≠ b}) ∈ (s.separator : Set _)} := by
    ext z
    exact mem_rightSeparator s z
  rw [hsepSet] at LB
  let LW : Erdos718.PairLinkage (contractAt G a b)
      (s.separator : Set {z : V // z ≠ b}) terminalW :=
    Erdos718.PairLinkage.liftInduce hterminalRight LB
  have hcontractSet :
      ContractLinkage.contractSet (t.separator : Set V) =
        (s.separator : Set {z : V // z ≠ b}) := by
    ext z
    change (z : V) ∈ t.separator ↔ z ∈ s.separator
    rw [mem_liftContractSeparation_separator]
    have hne : (z : V) ≠ b := z.property
    rw [contractProjection_of_ne hab hne]
  let LW' : Erdos718.PairLinkage (contractAt G a b)
      (ContractLinkage.contractSet (t.separator : Set V)) terminalW := {
    path := LW.path
    isPath := LW.isPath
    avoids := by
      intro i
      rw [hcontractSet]
      exact LW.avoids i
    disjoint := LW.disjoint
  }
  let LG : Erdos718.PairLinkage G (t.separator : Set V) terminalV :=
    Erdos718.PairLinkage.liftContractOfSubset hab terminalV
      hterminalSep hbSep LW'
  have hLWsupport (i : I) {z : {z : V // z ≠ b}}
      (hz : z ∈ (LW'.path i).support) : z ∈ s.right := by
    have hpath : LW'.path i = LW.path i := by rfl
    rw [hpath] at hz
    exact Erdos718.PairLinkage.support_liftInduce_subset
      hterminalRight LB i (by simpa only [LW] using hz)
  have hLGsupport (i : I) (z : V) (hz : z ∈ (LG.path i).support) :
      z ∈ t.right := by
    dsimp only [LG, Erdos718.PairLinkage.liftContractOfSubset] at hz
    rw [Walk.support_copy] at hz
    have hzLift : z ∈
        (ContractLinkage.liftContractWalk G hab (LW'.path i)).support :=
      Walk.support_toPath_subset_support _ hz
    rcases ContractLinkage.support_liftContractWalk hab (LW'.path i) hzLift with
      hbcase | hw
    · rw [hbcase.1]
      apply (mem_liftContractSeparation_right hab s b).mpr
      have haR := (Finset.mem_sdiff.mp ha).1
      simpa only [contractProjection_b] using haR
    · obtain ⟨w, hwSupp, hwz⟩ := hw
      have hwRight := hLWsupport i hwSupp
      apply (mem_liftContractSeparation_right hab s z).mpr
      have hne : (w : V) ≠ b := w.property
      have hp : contractProjection hab (w : V) = w := by
        rw [contractProjection_of_ne hab hne]
      rw [← hwz, hp]
      exact hwRight
  have hterminalTRight : Set.range terminalV ⊆ (t.right : Set V) := by
    rintro _ ⟨q, rfl⟩
    exact (terminal q).property
  let LR := Erdos718.PairLinkage.restrictInduce LG hLGsupport hterminalTRight
  have hrightSepSet :
      {z : (t.right : Set V) | (z : V) ∈ (t.separator : Set V)} =
        (rightSeparator t : Set (t.right : Set V)) := by
    ext z
    exact (mem_rightSeparator t z).symm
  have hterminalBack : terminalIntoSet (t.right : Set V) terminalV
      hterminalTRight = terminal := by
    ext q
    rfl
  rw [hrightSepSet, hterminalBack] at LR
  exact ⟨LR⟩

namespace MassedCounterexample

variable {k : ℕ}

/-- Claim 2.3's structural part: absence of rigid separations of order at
most `|X|` forces the second mass condition to survive every contraction
whose deleted endpoint is outside `X`. -/
theorem contractConditionTwo_of_noSmallRigidSeparation
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal)
    (hnoRigid : C.HasNoSmallRigidSeparation) :
    C.ContractConditionTwo := by
  classical
  intro a b hab hb s hXleft horder
  by_contra hbound
  let Xc := contractFinset C.X b
  have hbad : ∃ q : Erdos718.Separation (contractAt C.G a b),
      ViolatesSecondFor (contractAt C.G a b) Xc k q := by
    refine ⟨s, hXleft, horder, ?_⟩
    exact Nat.lt_of_not_ge hbound
  obtain ⟨s₀, hs₀, hminimal⟩ :=
    exists_minimal_violatesSecondFor (contractAt C.G a b) Xc k hbad
  have hmassedRight :=
    isEightKMassed_induce_right_of_minimal_violationFor
      (contractAt C.G a b) Xc k s₀ hs₀ hminimal
  have hlinkedRight : Erdos718.IsLinkedSet
      ((contractAt C.G a b).induce
        (s₀.right : Set {z : C.V // z ≠ b}))
      (rightSeparator s₀ : Set (s₀.right : Set {z : C.V // z ≠ b})) := by
    by_contra hnot
    let D : MassedCounterexample k := {
      V := (s₀.right : Set {z : C.V // z ≠ b})
      fintypeV := inferInstance
      decEqV := inferInstance
      G := (contractAt C.G a b).induce
        (s₀.right : Set {z : C.V // z ≠ b})
      decAdj := inferInstance
      X := rightSeparator s₀
      card_le := by
        rw [rightSeparator_card]
        exact hs₀.2.1.le.trans ((card_contractFinset hb).trans_le C.card_le)
      massed := hmassedRight
      not_linked := hnot
    }
    have hleftStrict : (s₀.left \ s₀.right).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hleftSub : s₀.left ⊆ s₀.right := by
        intro z hzL
        by_contra hzR
        have hz : z ∈ s₀.left \ s₀.right :=
          Finset.mem_sdiff.mpr ⟨hzL, hzR⟩
        simpa [hempty] using hz
      have hXSep : Xc ⊆ s₀.separator := by
        intro z hz
        exact Finset.mem_inter.mpr ⟨hs₀.1 hz, hleftSub (hs₀.1 hz)⟩
      have hcard := Finset.card_le_card hXSep
      exact (Nat.not_le_of_lt hs₀.2.1) hcard
    have hrightContract : s₀.right.card <
        Fintype.card {z : C.V // z ≠ b} := by
      have hproper : s₀.right ⊂
          (Finset.univ : Finset {z : C.V // z ≠ b}) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        obtain ⟨z, hz⟩ := hleftStrict
        rw [Finset.mem_sdiff] at hz
        exact hz.2 (heq ▸ Finset.mem_univ z)
      simpa using Finset.card_lt_card hproper
    have hcontractCard : Fintype.card {z : C.V // z ≠ b} <
        Fintype.card C.V := by
      have hpos : 0 < Fintype.card C.V := Fintype.card_pos_iff.mpr ⟨b⟩
      simp
      omega
    have hDcard : Fintype.card D.V = s₀.right.card := by simp [D]
    have hvertices := (hlex D).1
    unfold vertexCount at hvertices
    rw [hDcard] at hvertices
    exact (Nat.not_le_of_lt (hrightContract.trans hcontractCard)) hvertices
  let t := liftContractSeparation hab s₀
  have hXcard : Xc.card = C.X.card := card_contractFinset hb
  have hXt : C.X ⊆ t.left := by
    intro x hx
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    apply (mem_liftContractSeparation_left hab s₀ x).mpr
    have hxC : (⟨x, hxb⟩ : {z : C.V // z ≠ b}) ∈ Xc :=
      mem_contractFinset.mpr hx
    have := hs₀.1 hxC
    simpa [contractProjection_of_ne hab hxb] using this
  have htOrder : t.separator.card ≤ C.X.card := by
    have hsep := card_separator_liftContractSeparation_le_add_one hab s₀
    have hsep' : t.separator.card ≤ s₀.separator.card + 1 := by
      simpa only [t] using hsep
    have horder₀ := hs₀.2.1
    rw [hXcard] at horder₀
    omega
  have hleftStrict₀ : (s₀.left \ s₀.right).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hleftSub : s₀.left ⊆ s₀.right := by
      intro z hzL
      by_contra hzR
      have hz : z ∈ s₀.left \ s₀.right :=
        Finset.mem_sdiff.mpr ⟨hzL, hzR⟩
      simpa [hempty] using hz
    have hXSep : Xc ⊆ s₀.separator := by
      intro z hz
      exact Finset.mem_inter.mpr ⟨hs₀.1 hz, hleftSub (hs₀.1 hz)⟩
    have hcard := Finset.card_le_card hXSep
    exact (Nat.not_le_of_lt hs₀.2.1) hcard
  have htLeftStrict : (t.left \ t.right).Nonempty := by
    obtain ⟨z, hz⟩ := hleftStrict₀
    refine ⟨(z : C.V), ?_⟩
    rw [Finset.mem_sdiff]
    exact ⟨(mem_liftContractSeparation_left hab s₀ _).mpr (by
        simpa only [contractProjection_of_ne hab z.property] using
          (Finset.mem_sdiff.mp hz).1),
      fun h => (Finset.mem_sdiff.mp hz).2 (by
        have := (mem_liftContractSeparation_right hab s₀ _).mp h
        simpa only [contractProjection_of_ne hab z.property] using this)⟩
  have hrightStrict₀ : (s₀.right \ s₀.left).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hdense := hs₀.2.2
    rw [hempty, incidentEdges_empty] at hdense
    simp at hdense
  let abar : {z : C.V // z ≠ b} := ⟨a, hab.ne⟩
  by_cases haR : abar ∈ s₀.right
  · by_cases haL : abar ∈ s₀.left
    · have haNotStrict : abar ∉ s₀.right \ s₀.left := by
        intro h
        exact (Finset.mem_sdiff.mp h).2 haL
      have hstrictCard :=
        card_strictRight_liftContractSeparation_of_not_mem hab s₀ haNotStrict
      have hinc := incidentEdges_contract_le_liftStrictRight hab s₀
      have hcardEq : (t.right \ t.left).card =
          (s₀.right \ s₀.left).card := by
        simpa only [t] using hstrictCard
      have hinc' : incidentEdges (contractAt C.G a b)
            (s₀.right \ s₀.left) ≤
          incidentEdges C.G (t.right \ t.left) := by
        simpa only [t] using hinc
      have hdense : 8 * k * (t.right \ t.left).card <
          incidentEdges C.G (t.right \ t.left) := by
        calc
          8 * k * (t.right \ t.left).card =
              8 * k * (s₀.right \ s₀.left).card := by rw [hcardEq]
          _ < incidentEdges (contractAt C.G a b)
              (s₀.right \ s₀.left) := hs₀.2.2
          _ ≤ incidentEdges C.G (t.right \ t.left) := hinc'
      have hlinkedT := linked_induce_right_of_dense_boundary
        C hlex t hXt htOrder hdense htLeftStrict
      have hrigid : C.IsRigidSeparation t := by
        refine ⟨hXt, ?_, hlinkedT⟩
        obtain ⟨z, hz⟩ := hrightStrict₀
        refine ⟨(z : C.V), ?_⟩
        apply (mem_liftContractSeparation_strictRight hab s₀ _).mpr
        simpa only [contractProjection_of_ne hab z.property] using hz
      exact (Nat.not_lt_of_ge htOrder) (hnoRigid t hrigid)
    · have haStrict : abar ∈ s₀.right \ s₀.left :=
        Finset.mem_sdiff.mpr ⟨haR, haL⟩
      have hlinkedT := linked_liftContractSeparation_of_mem_strictRight
        hab s₀ haStrict hlinkedRight
      have hrigid : C.IsRigidSeparation t :=
        ⟨hXt, strictRight_liftContractSeparation_nonempty_of_mem
          hab s₀ haStrict, hlinkedT⟩
      exact (Nat.not_lt_of_ge htOrder) (hnoRigid t hrigid)
  · have haNotSep : abar ∉ s₀.separator := by
      intro h
      exact haR (Finset.mem_inter.mp h).2
    have htOrderLt : t.separator.card < C.X.card := by
      rw [card_separator_liftContractSeparation_of_not_mem hab s₀ haNotSep]
      simpa only [hXcard] using hs₀.2.1
    have haNotStrict : abar ∉ s₀.right \ s₀.left := by
      intro h
      exact haR (Finset.mem_sdiff.mp h).1
    have hstrictCard :=
      card_strictRight_liftContractSeparation_of_not_mem hab s₀ haNotStrict
    have hinc := incidentEdges_contract_le_liftStrictRight hab s₀
    have hcardEq : (t.right \ t.left).card =
        (s₀.right \ s₀.left).card := by
      simpa only [t] using hstrictCard
    have hinc' : incidentEdges (contractAt C.G a b)
          (s₀.right \ s₀.left) ≤
        incidentEdges C.G (t.right \ t.left) := by
      simpa only [t] using hinc
    have hdense : 8 * k * (t.right \ t.left).card <
        incidentEdges C.G (t.right \ t.left) := by
      calc
        8 * k * (t.right \ t.left).card =
            8 * k * (s₀.right \ s₀.left).card := by rw [hcardEq]
        _ < incidentEdges (contractAt C.G a b)
            (s₀.right \ s₀.left) := hs₀.2.2
        _ ≤ incidentEdges C.G (t.right \ t.left) := hinc'
    have hmass := C.massed.2 t hXt htOrderLt
    exact (Nat.not_lt_of_ge hmass) hdense

end MassedCounterexample

end ThomasWollanMassed
end Erdos717
