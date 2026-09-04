/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Numerical bookkeeping for contracting an edge outside a distinguished
terminal set in a Thomas--Wollan minimal counterexample.
-/

import ErdosProblems.Erdos717.MinimalMassed

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

open DenseMinor ContractLinkage

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Delete one specified edge. -/
def deleteOne (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u, v) ≠ s(a, b)
  symm.symm u v h := ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩

instance deleteOne.instDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) : DecidableRel (deleteOne G a b).Adj :=
  inferInstanceAs <| DecidableRel fun u v : V =>
    G.Adj u v ∧ s(u, v) ≠ s(a, b)

lemma deleteOne_adj_iff {G : SimpleGraph V} {a b u v : V} :
    (deleteOne G a b).Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(a, b) := by
  rfl

lemma deleteOne_le (G : SimpleGraph V) (a b : V) :
    deleteOne G a b ≤ G :=
  fun _ _ h => h.1

lemma deleteOne_comm (G : SimpleGraph V) (a b : V) :
    deleteOne G a b = deleteOne G b a := by
  ext u v
  simp only [deleteOne_adj_iff, and_congr_right_iff]
  intro _
  rw [Sym2.eq_swap (a := a) (b := b)]

lemma edgeFinset_deleteOne (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) :
    (deleteOne G a b).edgeFinset = G.edgeFinset \ {s(a, b)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff,
    Finset.mem_singleton]
  induction e using Sym2.inductionOn with
  | _ u v => rfl

lemma incidentEdges_deleteOne_add_one (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) {a b : V}
    (hab : G.Adj a b) (hout : a ∉ X ∨ b ∉ X) :
    incidentEdges (deleteOne G a b) (Finset.univ \ X) + 1 =
      incidentEdges G (Finset.univ \ X) := by
  classical
  unfold incidentEdges
  rw [edgeFinset_deleteOne]
  have hfilter :
      ((G.edgeFinset \ {s(a, b)}).filter fun e =>
          ¬e.toFinset ⊆ Finset.univ \ (Finset.univ \ X)) =
        (G.edgeFinset.filter fun e =>
          ¬e.toFinset ⊆ Finset.univ \ (Finset.univ \ X)) \ {s(a, b)} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    tauto
  rw [hfilter, Finset.sdiff_singleton_eq_erase]
  apply Finset.card_erase_add_one
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    Sym2.toFinset_mk_eq]
  refine ⟨hab, ?_⟩
  intro hsubset
  have hcomp : Finset.univ \ (Finset.univ \ X) = X := by
    ext x
    simp
  rw [hcomp] at hsubset
  rcases hout with ha | hb
  · exact ha (hsubset (by simp))
  · exact hb (hsubset (by simp))

lemma incidentEdges_mono {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (S : Finset V) :
    incidentEdges G S ≤ incidentEdges H S := by
  unfold incidentEdges
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he ⊢
  have hedge : e ∈ G.edgeSet := he.1
  have hhedge : e ∈ H.edgeSet := by
    induction e using Sym2.inductionOn with
    | _ u v =>
        change G.Adj u v at hedge
        change H.Adj u v
        exact hGH hedge
  exact ⟨hhedge, he.2⟩

lemma commonNeighborFinset_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) :
    commonNeighborFinset G a b = commonNeighborFinset G b a := by
  simp [commonNeighborFinset, Finset.inter_comm]

lemma deleteOne_adj_left_common {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b z : V}
    (hab : G.Adj a b) (hz : z ∈ commonNeighborFinset G a b) :
    (deleteOne G a b).Adj a z := by
  rw [deleteOne_adj_iff]
  have haz : G.Adj a z := by
    simpa [commonNeighborFinset, G.mem_neighborFinset] using
      (Finset.mem_inter.mp hz).1
  refine ⟨haz, ?_⟩
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with heq | heq
  · have hzb := heq.2
    have hbz : G.Adj b z := by
      simpa [commonNeighborFinset, G.mem_neighborFinset] using
        (Finset.mem_inter.mp hz).2
    exact hbz.ne hzb.symm
  · exact hab.ne heq.1

lemma deleteOne_adj_right_common {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b z : V}
    (hab : G.Adj a b) (hz : z ∈ commonNeighborFinset G a b) :
    (deleteOne G a b).Adj b z := by
  rw [deleteOne_adj_iff]
  have hbz : G.Adj b z := by
    simpa [commonNeighborFinset, G.mem_neighborFinset] using
      (Finset.mem_inter.mp hz).2
  refine ⟨hbz, ?_⟩
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with heq | heq
  · exact hab.ne heq.1.symm
  · have hza := heq.2
    have haz : G.Adj a z := by
      simpa [commonNeighborFinset, G.mem_neighborFinset] using
        (Finset.mem_inter.mp hz).1
    exact haz.ne hza.symm

/-- If the deleted edge crosses a separation, all its common neighbors lie
in the separator. -/
lemma commonNeighborFinset_subset_separator
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (s : Erdos718.Separation (deleteOne G a b))
    (haL : a ∈ s.left) (haR : a ∉ s.right)
    (hbR : b ∈ s.right) (hbL : b ∉ s.left) :
    commonNeighborFinset G a b ⊆ s.separator := by
  intro z hz
  have hzside := s.mem_left_or_mem_right z
  rw [Erdos718.Separation.separator, Finset.mem_inter]
  rcases hzside with hzL | hzR
  · refine ⟨hzL, ?_⟩
    by_contra hzNotR
    exact s.not_adj hzL hzNotR hbR hbL
      (deleteOne_adj_right_common hab hz).symm
  · refine ⟨?_, hzR⟩
    by_contra hzNotL
    exact s.not_adj haL haR hzR hzNotL
      (deleteOne_adj_left_common hab hz)

/-- The distinguished finset transported to the contracted vertex type. -/
def contractFinset (X : Finset V) (b : V) :
    Finset {z : V // z ≠ b} :=
  Finset.univ.filter fun z => (z : V) ∈ X

@[simp] lemma mem_contractFinset {X : Finset V} {b : V}
    {z : {z : V // z ≠ b}} :
    z ∈ contractFinset X b ↔ (z : V) ∈ X := by
  simp [contractFinset]

lemma card_contractFinset {X : Finset V} {b : V} (hb : b ∉ X) :
    (contractFinset X b).card = X.card := by
  let f : X ↪ {z : V // z ≠ b} := {
    toFun := fun x => ⟨x, fun h => hb (h ▸ x.property)⟩
    inj' := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {z : V // z ≠ b} => (z : V)) h
  }
  have hmap : contractFinset X b = Finset.univ.map f := by
    ext z
    constructor
    · intro hz
      have hzX : (z : V) ∈ X := mem_contractFinset.mp hz
      let x : X := ⟨z, hzX⟩
      exact Finset.mem_map.mpr ⟨x, Finset.mem_univ _, Subtype.ext rfl⟩
    · rintro hz
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
      exact mem_contractFinset.mpr x.property
  rw [hmap, Finset.card_map, Finset.card_univ]
  simp

/-- Pull the contracted graph back to the original distinguished subtype. -/
def pullContractOn (G : SimpleGraph V) (X : Finset V)
    (a b : V) (hb : b ∉ X) : SimpleGraph X :=
  (contractAt G a b).comap fun x : X =>
    (⟨x, fun h => hb (h ▸ x.property)⟩ : {z : V // z ≠ b})

instance pullContractOn.instDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) (a b : V) (hb : b ∉ X) :
    DecidableRel (pullContractOn G X a b hb).Adj :=
  inferInstanceAs <| DecidableRel fun x y : X =>
    (contractAt G a b).Adj
      ⟨x, fun h => hb (h ▸ x.property)⟩
      ⟨y, fun h => hb (h ▸ y.property)⟩

lemma pullContractOn_adj {G : SimpleGraph V} {X : Finset V}
    {a b : V} (hb : b ∉ X) {x y : X} :
    (pullContractOn G X a b hb).Adj x y ↔
      (contractAt G a b).Adj
        ⟨x, fun h => hb (h ▸ x.property)⟩
        ⟨y, fun h => hb (h ▸ y.property)⟩ :=
  Iff.rfl

/-- The original distinguished subtype is equivalent to the induced
contracted distinguished subtype. -/
def contractFinsetEquiv (X : Finset V) {b : V} (hb : b ∉ X) :
    X ≃ (contractFinset X b : Set {z : V // z ≠ b}) where
  toFun x := ⟨⟨x, fun h => hb (h ▸ x.property)⟩,
    mem_contractFinset.mpr x.property⟩
  invFun z := ⟨z.1.1, mem_contractFinset.mp z.2⟩
  left_inv x := Subtype.ext rfl
  right_inv z := Subtype.ext (Subtype.ext rfl)

lemma edgesOn_contract_eq_pullContractOn_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) {a b : V} (hb : b ∉ X) :
    Erdos718.MaderPrototype.edgesOn (contractAt G a b)
        (contractFinset X b) =
      (pullContractOn G X a b hb).edgeFinset.card := by
  rw [Erdos718.MaderPrototype.edgesOn_eq_induce]
  let e := contractFinsetEquiv X hb
  let K := (contractAt G a b).induce
    (contractFinset X b : Set {z : V // z ≠ b})
  have hiso : pullContractOn G X a b hb ≃g K := by
    have hgraph : pullContractOn G X a b hb = K.comap e := by
      ext x y
      rfl
    rw [hgraph]
    exact SimpleGraph.Iso.comap e K
  exact hiso.card_edgeFinset_eq.symm

namespace MassedCounterexample

variable {k : ℕ}

/-- The second mass condition survives every contraction whose deleted
endpoint is outside the distinguished set.  Claim 2.3 of Thomas--Wollan
derives this property from the absence of small rigid separations. -/
def ContractConditionTwo (C : MassedCounterexample k) : Prop :=
  ∀ (a b : C.V) (hab : C.G.Adj a b) (hb : b ∉ C.X),
    ∀ s : Erdos718.Separation (contractAt C.G a b),
      contractFinset C.X b ⊆ s.left →
      s.separator.card < (contractFinset C.X b).card →
      incidentEdges (contractAt C.G a b) (s.right \ s.left) ≤
        8 * k * (s.right \ s.left).card

/-- Every genuinely new edge inside `X` after contracting `ab` is the
unique prescribed pair edge incident with `a`. -/
lemma extra_pullContract_edge_star
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) {a b : C.V} (hab : C.G.Adj a b)
    (hb : b ∉ C.X) {e : Sym2 C.X}
    (heK : e ∈ (pullContractOn C.G C.X a b hb).edgeFinset)
    (heG : e ∉ (C.G.induce (C.X : Set C.V)).edgeFinset) :
    ∃ aa z : C.X, (aa : C.V) = a ∧ e = s(aa, z) ∧
      ArePaired F.terminal a z := by
  rw [SimpleGraph.mem_edgeFinset] at heK
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heG
      change ¬C.G.Adj x y at heG
      change (contractAt C.G a b).Adj
        ⟨x, fun h => hb (h ▸ x.property)⟩
        ⟨y, fun h => hb (h ▸ y.property)⟩ at heK
      rcases heK.2 with hxy | hxa | hya
      · exact (heG hxy).elim
      · have hxa' : (x : C.V) = a := hxa.1
        have hne : (x : C.V) ≠ (y : C.V) := by
          intro h
          apply heK.1
          exact Subtype.ext h
        have hpaired : ArePaired F.terminal a y := by
          by_contra hnp
          apply heG
          have hnp' : ¬ArePaired F.terminal (x : C.V) y := by
            simpa only [hxa'] using hnp
          exact adjacent_of_lexMinimal_of_terminal_notPaired C hmin F
            x.property y.property hne hnp'
        exact ⟨x, y, hxa', rfl, hpaired⟩
      · have hya' : (y : C.V) = a := hya.1
        have hne : (y : C.V) ≠ (x : C.V) := by
          intro h
          apply heK.1
          exact Subtype.ext h.symm
        have hpaired : ArePaired F.terminal a x := by
          by_contra hnp
          apply heG
          have hnp' : ¬ArePaired F.terminal (y : C.V) x := by
            simpa only [hya'] using hnp
          exact (adjacent_of_lexMinimal_of_terminal_notPaired C hmin F
            y.property x.property hne hnp').symm
        exact ⟨y, x, hya', Sym2.eq_swap, hpaired⟩

/-- At most one new edge appears inside the distinguished set under a safe
contraction. -/
lemma card_extra_pullContract_le_one
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) {a b : C.V} (hab : C.G.Adj a b)
    (hb : b ∉ C.X) :
    ((pullContractOn C.G C.X a b hb).edgeFinset \
      (C.G.induce (C.X : Set C.V)).edgeFinset).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  have heK := (Finset.mem_sdiff.mp he).1
  have heG := (Finset.mem_sdiff.mp he).2
  have hfK := (Finset.mem_sdiff.mp hf).1
  have hfG := (Finset.mem_sdiff.mp hf).2
  obtain ⟨ae, ze, hae, heq, hpe⟩ :=
    extra_pullContract_edge_star C hmin F hab hb heK heG
  obtain ⟨af, zf, haf, hfq, hpf⟩ :=
    extra_pullContract_edge_star C hmin F hab hb hfK hfG
  have haa : ae = af := Subtype.ext (hae.trans haf.symm)
  subst af
  have hzval : (ze : C.V) = zf :=
    arePaired_left_unique hpe hpf
  have hz : ze = zf := Subtype.ext hzval
  subst zf
  exact heq.trans hfq.symm

/-- Contracting an edge outside `X` creates at most one new edge inside
`X`. -/
lemma edgesOn_contract_le_add_one
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) {a b : C.V} (hab : C.G.Adj a b)
    (hb : b ∉ C.X) :
    Erdos718.MaderPrototype.edgesOn (contractAt C.G a b)
        (contractFinset C.X b) ≤ C.insideEdges + 1 := by
  rw [edgesOn_contract_eq_pullContractOn_card C.G C.X hb]
  unfold insideEdges
  rw [Erdos718.MaderPrototype.edgesOn_eq_induce]
  let K := pullContractOn C.G C.X a b hb
  let H := C.G.induce (C.X : Set C.V)
  have hsplit := Finset.card_sdiff_add_card_inter K.edgeFinset H.edgeFinset
  have hextra := card_extra_pullContract_le_one C hmin F hab hb
  have hinter : (K.edgeFinset ∩ H.edgeFinset).card ≤ H.edgeFinset.card :=
    Finset.card_le_card Finset.inter_subset_right
  dsimp only [K, H] at hsplit hextra hinter ⊢
  omega

/-- Consequently the number of outside-incident edges drops by at most
two plus the number of common neighbors. -/
lemma incidentEdges_le_contract_add_common
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) {a b : C.V} (hab : C.G.Adj a b)
    (hb : b ∉ C.X) :
    incidentEdges C.G (Finset.univ \ C.X) ≤
      incidentEdges (contractAt C.G a b)
          (Finset.univ \ contractFinset C.X b) + 2 +
        (commonNeighborFinset C.G a b).card := by
  rw [incidentEdges_univ_sdiff C.G C.X,
    incidentEdges_univ_sdiff (contractAt C.G a b)
      (contractFinset C.X b)]
  have htotal := card_contractAt_ge C.G hab
  have hinside := edgesOn_contract_le_add_one C hmin F hab hb
  have hinsideG : Erdos718.MaderPrototype.edgesOn C.G C.X ≤
      C.G.edgeFinset.card := by
    unfold Erdos718.MaderPrototype.edgesOn
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hinsideC :
      Erdos718.MaderPrototype.edgesOn (contractAt C.G a b)
          (contractFinset C.X b) ≤
        (contractAt C.G a b).edgeFinset.card := by
    unfold Erdos718.MaderPrototype.edgesOn
    exact Finset.card_le_card (Finset.filter_subset _ _)
  unfold insideEdges at hinside
  omega

/-- If the contraction satisfies its second mass condition, minimality
forces the first condition to fail, and hence every eligible edge has at
least `8k-1` common neighbors. -/
theorem commonNeighbor_card_ge_sub_one_of_contractConditionTwo
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) (hk : 1 ≤ k)
    (hstable : C.ContractConditionTwo)
    {a b : C.V} (hab : C.G.Adj a b) (hb : b ∉ C.X) :
    8 * k - 1 ≤ (commonNeighborFinset C.G a b).card := by
  classical
  let Gc := contractAt C.G a b
  let Xc := contractFinset C.X b
  have hXcard : Xc.card = C.X.card := card_contractFinset hb
  have hbSet : b ∉ (C.X : Set C.V) := hb
  have hnotLinked : ¬Erdos718.IsLinkedSet Gc (Xc : Set _) := by
    intro hlinked
    apply C.not_linked
    intro ι inst terminal hterminal
    let : Fintype ι := inst
    have hbRange : b ∉ Set.range terminal := fun hbR =>
      hbSet (hterminal hbR)
    let terminalc := ContractLinkage.contractTerminal
      (G := C.G) (a := a) terminal hbRange
    have hrange : Set.range terminalc ⊆ (Xc : Set _) := by
      rintro z ⟨t, rfl⟩
      change terminalc t ∈ Xc
      rw [mem_contractFinset]
      exact hterminal ⟨t, rfl⟩
    have hLc : Nonempty (Erdos718.PairLinkage Gc (Xc : Set _) terminalc) :=
      hlinked ι terminalc hrange
    have hseteq : ContractLinkage.contractSet (C.X : Set C.V) =
        (Xc : Set {z : C.V // z ≠ b}) := by
      ext z
      simp [ContractLinkage.contractSet, Xc]
    rw [← hseteq] at hLc
    exact ContractLinkage.nonempty_pairLinkage_of_contract_of_subset
      hab terminal hterminal hbSet hLc
  have hfirstFails :
      ¬(8 * k * (Fintype.card {z : C.V // z ≠ b} - Xc.card) <
        incidentEdges Gc (Finset.univ \ Xc)) := by
    intro hfirst
    let D : MassedCounterexample k := {
      V := {z : C.V // z ≠ b}
      fintypeV := inferInstance
      decEqV := inferInstance
      G := Gc
      decAdj := inferInstance
      X := Xc
      card_le := by simpa only [hXcard] using C.card_le
      massed := ⟨hfirst, hstable a b hab hb⟩
      not_linked := hnotLinked
    }
    have hvertices := (hmin D).1
    unfold vertexCount at hvertices
    dsimp only [D] at hvertices
    have hcardContract : Fintype.card {z : C.V // z ≠ b} + 1 =
        Fintype.card C.V := by
      have hpos : 0 < Fintype.card C.V := Fintype.card_pos_iff.mpr ⟨b⟩
      simp
      omega
    omega
  have hcontractUpper :
      incidentEdges Gc (Finset.univ \ Xc) ≤
        8 * k * (Fintype.card {z : C.V // z ≠ b} - Xc.card) :=
    Nat.le_of_not_gt hfirstFails
  have houtsideCard : C.X.card < Fintype.card C.V := by
    have hbUniv : b ∈ (Finset.univ : Finset C.V) := Finset.mem_univ b
    have hproper : C.X ⊂ (Finset.univ : Finset C.V) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun heq =>
        hb (heq ▸ hbUniv)⟩
    exact Finset.card_lt_card hproper
  have hcardContract : Fintype.card {z : C.V // z ≠ b} + 1 =
      Fintype.card C.V := by
    have hpos : 0 < Fintype.card C.V := Fintype.card_pos_iff.mpr ⟨b⟩
    simp
    omega
  have houtsideStep :
      (Fintype.card {z : C.V // z ≠ b} - Xc.card) + 1 =
        Fintype.card C.V - C.X.card := by
    rw [hXcard]
    omega
  have hloss := incidentEdges_le_contract_add_common C hmin F hab hb
  have horiginal := C.massed.1
  change incidentEdges (contractAt C.G a b)
      (Finset.univ \ contractFinset C.X b) ≤
    8 * k * (Fintype.card {z : C.V // z ≠ b} -
      (contractFinset C.X b).card) at hcontractUpper
  have hscaled :
      8 * k * (Fintype.card {z : C.V // z ≠ b} - Xc.card) + 8 * k =
        8 * k * (Fintype.card C.V - C.X.card) := by
    calc
      8 * k * (Fintype.card {z : C.V // z ≠ b} - Xc.card) + 8 * k =
          8 * k * ((Fintype.card {z : C.V // z ≠ b} - Xc.card) + 1) := by
            ring
      _ = 8 * k * (Fintype.card C.V - C.X.card) := by rw [houtsideStep]
  change 8 * k * (Fintype.card {z : C.V // z ≠ b} -
      (contractFinset C.X b).card) + 8 * k =
    8 * k * (Fintype.card C.V - C.X.card) at hscaled
  omega

/-- The common-neighbor estimate prevents a newly created low-order
separation after deleting one outside-incident edge. -/
theorem delete_conditionTwo_of_contractConditionTwo
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) (hk : 1 ≤ k)
    (hstable : C.ContractConditionTwo)
    {a b : C.V} (hab : C.G.Adj a b)
    (hout : a ∉ C.X ∨ b ∉ C.X) :
    ∀ s : Erdos718.Separation (deleteOne C.G a b),
      C.X ⊆ s.left → s.separator.card < C.X.card →
      incidentEdges (deleteOne C.G a b) (s.right \ s.left) ≤
        8 * k * (s.right \ s.left).card := by
  have hcommon : 8 * k - 1 ≤
      (commonNeighborFinset C.G a b).card := by
    rcases hout with ha | hb
    · have h := commonNeighbor_card_ge_sub_one_of_contractConditionTwo
        C hmin F hk hstable hab.symm ha
      rw [commonNeighborFinset_comm C.G b a] at h
      exact h
    · exact commonNeighbor_card_ge_sub_one_of_contractConditionTwo
        C hmin F hk hstable hab hb
  intro s hXleft horder
  let t : Erdos718.Separation C.G := {
    left := s.left
    right := s.right
    cover := s.cover
    not_adj := by
      intro u v huL huR hvR hvL huv
      have hedge : s(u, v) = s(a, b) := by
        by_contra hne
        exact s.not_adj huL huR hvR hvL
          ((deleteOne_adj_iff).mpr ⟨huv, hne⟩)
      rw [Sym2.eq_iff] at hedge
      rcases hedge with hedge | hedge
      · have hu : u = a := hedge.1
        have hv : v = b := hedge.2
        subst u
        subst v
        have hsub := commonNeighborFinset_subset_separator hab s
          huL huR hvR hvL
        have hcard := Finset.card_le_card hsub
        have hXbound := C.card_le
        omega
      · have hu : u = b := hedge.1
        have hv : v = a := hedge.2
        subst u
        subst v
        have hba : deleteOne C.G b a ≤ deleteOne C.G a b := by
          rw [deleteOne_comm C.G b a]
        let s' : Erdos718.Separation (deleteOne C.G b a) := {
          left := s.left
          right := s.right
          cover := s.cover
          not_adj := by
            intro x y hxL hxR hyR hyL hxy
            exact s.not_adj hxL hxR hyR hyL (hba hxy)
        }
        have hsub' := commonNeighborFinset_subset_separator hab.symm s'
          huL huR hvR hvL
        have hsub : commonNeighborFinset C.G b a ⊆ s.separator := by
          unfold Erdos718.Separation.separator at hsub' ⊢
          change commonNeighborFinset C.G b a ⊆ s.left ∩ s.right at hsub'
          exact hsub'
        have hcard := Finset.card_le_card hsub
        rw [commonNeighborFinset_comm C.G b a] at hcard
        have hXbound := C.card_le
        omega
  }
  have hG := C.massed.2 t hXleft horder
  have hmono := incidentEdges_mono (deleteOne_le C.G a b)
    (s.right \ s.left)
  exact hmono.trans hG

/-- Edge-minimality now yields the global upper bound on the number of
outside-incident edges. -/
theorem outsideEdges_le_mass_add_one
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) (hk : 1 ≤ k)
    (hstable : C.ContractConditionTwo)
    {a b : C.V} (hab : C.G.Adj a b)
    (hout : a ∉ C.X ∨ b ∉ C.X) :
    C.outsideEdges ≤ 8 * k * (Fintype.card C.V - C.X.card) + 1 := by
  classical
  have hsecond := delete_conditionTwo_of_contractConditionTwo
    C hmin F hk hstable hab hout
  have hfirstFails :
      ¬(8 * k * (Fintype.card C.V - C.X.card) <
        incidentEdges (deleteOne C.G a b) (Finset.univ \ C.X)) := by
    intro hfirst
    have hnotLinked :
        ¬Erdos718.IsLinkedSet (deleteOne C.G a b) (C.X : Set C.V) := by
      intro hlinked
      exact C.not_linked
        (hlinked.mono (deleteOne_le C.G a b))
    let D : MassedCounterexample k := {
      V := C.V
      fintypeV := C.fintypeV
      decEqV := C.decEqV
      G := deleteOne C.G a b
      decAdj := deleteOne.instDecidableRel C.G a b
      X := C.X
      card_le := C.card_le
      massed := ⟨hfirst, hsecond⟩
      not_linked := hnotLinked
    }
    have hminimal := (hmin D).2.1 (by rfl)
    have hdrop := incidentEdges_deleteOne_add_one C.G C.X hab hout
    unfold outsideEdges at hminimal
    dsimp only [D] at hminimal
    omega
  have hupper : incidentEdges (deleteOne C.G a b)
      (Finset.univ \ C.X) ≤
      8 * k * (Fintype.card C.V - C.X.card) :=
    Nat.le_of_not_gt hfirstFails
  have hdrop := incidentEdges_deleteOne_add_one C.G C.X hab hout
  unfold outsideEdges
  omega

end MassedCounterexample

end ThomasWollanMassed
end Erdos717
