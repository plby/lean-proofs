import Mathlib

namespace BasisSubset

open scoped Pointwise

/-- The coordinate model of `ℝ^n`. -/
abbrev RealSpace (n : ℕ) : Type :=
  Fin n → ℝ

/-- The `2n - 1` test labels from the normalized standard-basis proof:
`2eᵢ` for every `i`, and `eᵢ₀ + eᵢ` for `i ≠ i₀`. -/
abbrev StdLabelIndex {n : ℕ} (i₀ : Fin n) : Type :=
  Fin n ⊕ {i : Fin n // i ≠ i₀}

/-- The label vectors used in the forest argument. -/
noncomputable def stdLabel {n : ℕ} (i₀ : Fin n) : StdLabelIndex i₀ → RealSpace n
  | Sum.inl i => Pi.basisFun ℝ (Fin n) i + Pi.basisFun ℝ (Fin n) i
  | Sum.inr i => Pi.basisFun ℝ (Fin n) i₀ + Pi.basisFun ℝ (Fin n) i

lemma stdLabel_mem_standardBasis_add {n : ℕ} (i₀ : Fin n) (t : StdLabelIndex i₀) :
    stdLabel i₀ t ∈
      (Set.range (Pi.basisFun ℝ (Fin n)) : Set (RealSpace n)) +
        Set.range (Pi.basisFun ℝ (Fin n)) := by
  cases t with
  | inl i =>
      exact Set.mem_add.mpr
        ⟨_, ⟨i, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
  | inr i =>
      exact Set.mem_add.mpr
        ⟨_, ⟨i₀, rfl⟩, _, ⟨i, rfl⟩, rfl⟩

lemma stdLabel_inl_apply {n : ℕ} (i₀ i k : Fin n) :
    stdLabel i₀ (Sum.inl i) k = (if i = k then (2 : ℝ) else 0) := by
  by_cases hik : i = k
  · norm_num [stdLabel, Pi.basisFun_apply, hik]
  · simp [stdLabel, Pi.basisFun_apply, hik]

lemma stdLabel_inr_apply {n : ℕ} (i₀ k : Fin n) (i : {i : Fin n // i ≠ i₀}) :
    stdLabel i₀ (Sum.inr i) k =
      (if i₀ = k then (1 : ℝ) else 0) + if i = k then (1 : ℝ) else 0 := by
  by_cases h0 : i₀ = k <;> by_cases hi : (i : Fin n) = k <;>
    simp [stdLabel, Pi.basisFun_apply, h0, hi]

lemma stdLabel_injective {n : ℕ} (i₀ : Fin n) : Function.Injective (stdLabel i₀) := by
  intro t u htu
  cases t with
  | inl i =>
      cases u with
      | inl j =>
          congr
          by_contra hij
          have hcoord := congrFun htu i
          rw [stdLabel_inl_apply, stdLabel_inl_apply] at hcoord
          simp [Ne.symm hij] at hcoord
      | inr j =>
          exfalso
          by_cases hi0 : i = i₀
          · have hcoord := congrFun htu j
            rw [stdLabel_inl_apply, stdLabel_inr_apply] at hcoord
            simp [hi0, Ne.symm j.2] at hcoord
          · have hcoord := congrFun htu i
            rw [stdLabel_inl_apply, stdLabel_inr_apply] at hcoord
            by_cases hji : (j : Fin n) = i
            · simp [Ne.symm hi0, hji] at hcoord
            · simp [Ne.symm hi0, hji] at hcoord
  | inr i =>
      cases u with
      | inl j =>
          exfalso
          have hsymm := htu.symm
          by_cases hj0 : j = i₀
          · have hcoord := congrFun hsymm i
            rw [stdLabel_inl_apply, stdLabel_inr_apply] at hcoord
            simp [hj0, Ne.symm i.2] at hcoord
          · have hcoord := congrFun hsymm j
            rw [stdLabel_inl_apply, stdLabel_inr_apply] at hcoord
            by_cases hij : (i : Fin n) = j
            · simp [Ne.symm hj0, hij] at hcoord
            · simp [Ne.symm hj0, hij] at hcoord
      | inr j =>
          congr
          by_contra hij
          have hcoord := congrFun htu i
          rw [stdLabel_inr_apply, stdLabel_inr_apply] at hcoord
          simp [Ne.symm i.2] at hcoord
          exact hij (Subtype.ext hcoord.symm)

lemma fintype_card_stdLabelIndex_add_one {n : ℕ} (i₀ : Fin n) :
    Fintype.card (StdLabelIndex i₀) + 1 = 2 * n := by
  have hcard_ne : Fintype.card {i : Fin n // i ≠ i₀} = n - 1 := by
    exact (Set.card_ne_eq i₀).trans (by rw [Fintype.card_fin])
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
  change Fintype.card (Fin n ⊕ {i : Fin n // i ≠ i₀}) + 1 = 2 * n
  rw [Fintype.card_sum, Fintype.card_fin, hcard_ne]
  omega

/-- Vertices of the auxiliary bipartite graph: a disjoint left copy of `Set.range a` and
a disjoint right copy of `Set.range b`. -/
abbrev StdDecompVertex {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n) : Type :=
  Set.range a ⊕ Set.range b

/-- The left endpoint of the edge indexed by `t`. -/
def stdDecompLeft {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (t : StdLabelIndex i₀) : StdDecompVertex a b :=
  Sum.inl ⟨a t, t, rfl⟩

/-- The right endpoint of the edge indexed by `t`. -/
def stdDecompRight {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (t : StdLabelIndex i₀) : StdDecompVertex a b :=
  Sum.inr ⟨b t, t, rfl⟩

/-- The label-indexed bipartite graph associated to decompositions `stdLabel i₀ t = a t + b t`.

The vertex type is already restricted to vertices that are used by at least one chosen edge. -/
def stdDecompGraph {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n) :
    SimpleGraph (StdDecompVertex a b) where
  Adj v w :=
    ∃ t, (v = stdDecompLeft a b t ∧ w = stdDecompRight a b t) ∨
      (v = stdDecompRight a b t ∧ w = stdDecompLeft a b t)
  symm := ⟨by
    rintro v w ⟨t, h | h⟩
    · exact ⟨t, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨t, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    rintro v ⟨t, h | h⟩
    · cases h.1
      cases h.2
    · cases h.1
      cases h.2⟩

lemma stdDecompGraph_adj {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n) (t : StdLabelIndex i₀) :
    (stdDecompGraph a b).Adj (stdDecompLeft a b t) (stdDecompRight a b t) :=
  ⟨t, Or.inl ⟨rfl, rfl⟩⟩

lemma nat_card_stdDecompVertex {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n) :
    Nat.card (StdDecompVertex a b) = (Set.range a).ncard + (Set.range b).ncard := by
  rw [StdDecompVertex, Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq]

/-- Distinct label-indices give distinct graph edges. -/
lemma nat_card_edgeSet_stdDecompGraph
    {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t)) :
    Nat.card (stdDecompGraph a b).edgeSet = Fintype.card (StdLabelIndex i₀) := by
  let edgeOf : StdLabelIndex i₀ → (stdDecompGraph a b).edgeSet := fun t =>
    ⟨s(stdDecompLeft a b t, stdDecompRight a b t), by
      rw [SimpleGraph.mem_edgeSet]
      exact stdDecompGraph_adj a b t⟩
  have hedgeOf_bij : Function.Bijective edgeOf := by
    constructor
    · intro t u htu
      have hsym2 :
          s(stdDecompLeft a b t, stdDecompRight a b t) =
            s(stdDecompLeft a b u, stdDecompRight a b u) :=
        Subtype.ext_iff.mp htu
      rw [Sym2.eq_iff] at hsym2
      rcases hsym2 with ⟨hleft, hright⟩ | ⟨hcross, _⟩
      · apply hchosenEdge_injective
        rw [stdDecompLeft, stdDecompLeft] at hleft
        rw [stdDecompRight, stdDecompRight] at hright
        exact Prod.ext (congrArg Subtype.val (Sum.inl.inj hleft))
          (congrArg Subtype.val (Sum.inr.inj hright))
      · cases hcross
    · rintro ⟨e, he⟩
      revert he
      refine e.ind ?_
      intro v w he
      rw [SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨t, h | h⟩
      · refine ⟨t, Subtype.ext ?_⟩
        change s(stdDecompLeft a b t, stdDecompRight a b t) = s(v, w)
        rw [h.1, h.2]
      · refine ⟨t, Subtype.ext ?_⟩
        change s(stdDecompLeft a b t, stdDecompRight a b t) = s(v, w)
        rw [h.1, h.2, Sym2.eq_swap]
  letI := Fintype.ofBijective edgeOf hedgeOf_bij
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (Equiv.ofBijective edgeOf hedgeOf_bij)).symm

/-- The graph edge selected by a label index. -/
def stdDecompEdgeOf {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n) (t : StdLabelIndex i₀) :
    Sym2 (StdDecompVertex a b) :=
  s(stdDecompLeft a b t, stdDecompRight a b t)

lemma stdDecompGraph_adj_iff_edgeOf
    {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    {v w : StdDecompVertex a b} {t : StdLabelIndex i₀} :
    s(v, w) = stdDecompEdgeOf a b t ↔
      (v = stdDecompLeft a b t ∧ w = stdDecompRight a b t) ∨
        (v = stdDecompRight a b t ∧ w = stdDecompLeft a b t) := by
  rw [stdDecompEdgeOf, Sym2.eq_iff]

/-- The label index carried by a dart of the decomposition graph. -/
noncomputable def stdDecompDartIndex {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    (d : (stdDecompGraph a b).Dart) : StdLabelIndex i₀ :=
  Classical.choose d.adj

lemma stdDecompDart_edge_eq_edgeOf {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    (d : (stdDecompGraph a b).Dart) :
    d.edge = stdDecompEdgeOf a b (stdDecompDartIndex d) := by
  let t := stdDecompDartIndex d
  change d.edge = stdDecompEdgeOf a b t
  have ht : ((d.fst = stdDecompLeft a b t ∧ d.snd = stdDecompRight a b t) ∨
      (d.fst = stdDecompRight a b t ∧ d.snd = stdDecompLeft a b t)) := by
    simpa [t, stdDecompDartIndex] using Classical.choose_spec d.adj
  rw [SimpleGraph.Dart.edge, stdDecompGraph_adj_iff_edgeOf]
  exact ht

/-- Orientation sign of a decomposition dart: `1` from the left copy to the right copy and
`-1` in the reverse direction. -/
noncomputable def stdDecompDartSign {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    (d : (stdDecompGraph a b).Dart) : ℤ :=
  if d.fst = stdDecompLeft a b (stdDecompDartIndex d) then 1 else -1

/-- The signed contribution of one dart is its standard label. -/
lemma stdDecompDart_signed_label {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (d : (stdDecompGraph a b).Dart) :
    (stdDecompDartSign d : ℝ) • stdLabel i₀ (stdDecompDartIndex d) =
      match d.fst, d.snd with
      | Sum.inl x, Sum.inr y => x.1 + y.1
      | Sum.inr y, Sum.inl x => -(x.1 + y.1)
      | _, _ => 0 := by
  let t := stdDecompDartIndex d
  have ht : ((d.fst = stdDecompLeft a b t ∧ d.snd = stdDecompRight a b t) ∨
      (d.fst = stdDecompRight a b t ∧ d.snd = stdDecompLeft a b t)) := by
    simpa [t, stdDecompDartIndex] using Classical.choose_spec d.adj
  rcases ht with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · have hsign : stdDecompDartSign d = 1 := by
      simp [stdDecompDartSign, t, hfst]
    rw [hfst, hsnd, hsign]
    simp [t, stdDecompLeft, stdDecompRight, hab]
  · have hsign : stdDecompDartSign d = -1 := by
      have hnot : d.fst ≠ stdDecompLeft a b (stdDecompDartIndex d) := by
        rw [hfst]
        simp [stdDecompLeft, stdDecompRight]
      simp [stdDecompDartSign, hnot]
    rw [hfst, hsnd, hsign]
    simp [t, stdDecompLeft, stdDecompRight, hab]

/-- The potential whose differences telescope around a walk.  The right copy is negated, so
crossing a label edge from left to right contributes `a + b`. -/
noncomputable def stdDecompVertexPotential {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n} :
    StdDecompVertex a b → RealSpace n
  | Sum.inl x => x.1
  | Sum.inr y => -y.1

lemma stdDecompDart_signed_label_eq_potential_sub {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (d : (stdDecompGraph a b).Dart) :
    (stdDecompDartSign d : ℝ) • stdLabel i₀ (stdDecompDartIndex d) =
      stdDecompVertexPotential d.fst - stdDecompVertexPotential d.snd := by
  let t := stdDecompDartIndex d
  have ht : ((d.fst = stdDecompLeft a b t ∧ d.snd = stdDecompRight a b t) ∨
      (d.fst = stdDecompRight a b t ∧ d.snd = stdDecompLeft a b t)) := by
    simpa [t, stdDecompDartIndex] using Classical.choose_spec d.adj
  rcases ht with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · rw [stdDecompDart_signed_label a b hab d, hfst, hsnd]
    simp [stdDecompVertexPotential, stdDecompLeft, stdDecompRight]
  · rw [stdDecompDart_signed_label a b hab d, hfst, hsnd]
    simp [stdDecompVertexPotential, stdDecompLeft, stdDecompRight, sub_eq_add_neg]

/-- The signed incidence vector of the labels traversed by a walk. -/
noncomputable def stdDecompWalkCoeff {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    {u v : StdDecompVertex a b} :
    (stdDecompGraph a b).Walk u v → StdLabelIndex i₀ → ℤ
  | SimpleGraph.Walk.nil => fun _ => 0
  | @SimpleGraph.Walk.cons _ _ u w v h q => fun t =>
      let d : (stdDecompGraph a b).Dart := ⟨⟨u, w⟩, h⟩
      (if stdDecompDartIndex d = t then stdDecompDartSign d else 0) +
        stdDecompWalkCoeff q t

lemma stdDecompWalkCoeff_relation {n : ℕ} {i₀ : Fin n}
    (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    {u v : StdDecompVertex a b} (p : (stdDecompGraph a b).Walk u v) :
    (∑ t : StdLabelIndex i₀,
        (stdDecompWalkCoeff p t : ℝ) • stdLabel i₀ t) =
      stdDecompVertexPotential u - stdDecompVertexPotential v := by
  induction p with
  | nil =>
      simp [stdDecompWalkCoeff]
  | @cons u w v h q ih =>
      let d : (stdDecompGraph a b).Dart := ⟨⟨u, w⟩, h⟩
      have hsingle :
          (∑ t : StdLabelIndex i₀,
              (((if stdDecompDartIndex d = t then stdDecompDartSign d else 0) : ℤ) : ℝ) •
                stdLabel i₀ t) =
            (stdDecompDartSign d : ℝ) • stdLabel i₀ (stdDecompDartIndex d) := by
        classical
        rw [Finset.sum_eq_single (stdDecompDartIndex d)]
        · simp
        · intro t _ ht
          simp [if_neg ht.symm]
        · intro ht
          exact (ht (Finset.mem_univ _)).elim
      simp only [stdDecompWalkCoeff]
      simp_rw [Int.cast_add, add_smul]
      rw [Finset.sum_add_distrib, hsingle, ih,
        stdDecompDart_signed_label_eq_potential_sub a b hab d]
      simp [d]

lemma stdDecompDartSign_eq_one_or_neg_one {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    (d : (stdDecompGraph a b).Dart) :
    stdDecompDartSign d = 1 ∨ stdDecompDartSign d = -1 := by
  unfold stdDecompDartSign
  split <;> simp

lemma stdDecompWalkCoeff_eq_zero_of_edge_notMem {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    {u v : StdDecompVertex a b} (p : (stdDecompGraph a b).Walk u v)
    (t : StdLabelIndex i₀) (ht : stdDecompEdgeOf a b t ∉ p.edges) :
    stdDecompWalkCoeff p t = 0 := by
  induction p with
  | nil =>
      simp [stdDecompWalkCoeff]
  | @cons u w v h q ih =>
      let d : (stdDecompGraph a b).Dart := ⟨⟨u, w⟩, h⟩
      rw [SimpleGraph.Walk.edges_cons] at ht
      simp only [List.mem_cons, not_or] at ht
      have hidx : stdDecompDartIndex d ≠ t := by
        intro hidx
        apply ht.1
        change stdDecompEdgeOf a b t = d.edge
        rw [stdDecompDart_edge_eq_edgeOf d, hidx]
      simp [stdDecompWalkCoeff, d, hidx, ih ht.2]

lemma stdDecompWalkCoeff_eq_neg_one_or_zero_or_one_of_isTrail {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    {u v : StdDecompVertex a b} (p : (stdDecompGraph a b).Walk u v)
    (hp : p.IsTrail) (t : StdLabelIndex i₀) :
    stdDecompWalkCoeff p t = -1 ∨ stdDecompWalkCoeff p t = 0 ∨
      stdDecompWalkCoeff p t = 1 := by
  revert t
  induction p with
  | nil =>
      intro t
      simp [stdDecompWalkCoeff]
  | @cons u w v h q ih =>
      intro t
      let d : (stdDecompGraph a b).Dart := ⟨⟨u, w⟩, h⟩
      rw [SimpleGraph.Walk.isTrail_cons] at hp
      by_cases hidx : stdDecompDartIndex d = t
      · have htail_not : stdDecompEdgeOf a b t ∉ q.edges := by
          intro hmem
          exact hp.2 (by
            change d.edge ∈ q.edges
            rw [stdDecompDart_edge_eq_edgeOf d, hidx]
            exact hmem)
        have htail_zero := stdDecompWalkCoeff_eq_zero_of_edge_notMem q t htail_not
        have hsign := stdDecompDartSign_eq_one_or_neg_one d
        rcases hsign with hsign | hsign
        · right; right
          simp [stdDecompWalkCoeff, d, hidx, htail_zero, hsign]
        · left
          simp [stdDecompWalkCoeff, d, hidx, htail_zero, hsign]
      · have htail_bound := ih hp.1 t
        simpa [stdDecompWalkCoeff, d, hidx] using htail_bound

lemma stdDecompWalkCoeff_nonzero_of_isCycle {n : ℕ} {i₀ : Fin n}
    {a b : StdLabelIndex i₀ → RealSpace n}
    {v : StdDecompVertex a b} (p : (stdDecompGraph a b).Walk v v)
    (hp : p.IsCycle) :
    ∃ t : StdLabelIndex i₀, stdDecompWalkCoeff p t ≠ 0 := by
  cases p with
  | nil =>
      exact (SimpleGraph.Walk.not_isCycle_nil hp).elim
  | @cons v w _ h q =>
      let d : (stdDecompGraph a b).Dart := ⟨⟨v, w⟩, h⟩
      refine ⟨stdDecompDartIndex d, ?_⟩
      have htrail_cons : (SimpleGraph.Walk.cons h q).IsTrail := hp.isTrail
      rw [SimpleGraph.Walk.isTrail_cons] at htrail_cons
      have htail_zero :
          stdDecompWalkCoeff q (stdDecompDartIndex d) = 0 := by
        apply stdDecompWalkCoeff_eq_zero_of_edge_notMem
        intro hmem
        exact htrail_cons.2 (by
          change d.edge ∈ q.edges
          rw [stdDecompDart_edge_eq_edgeOf d]
          exact hmem)
      have hsign := stdDecompDartSign_eq_one_or_neg_one d
      rcases hsign with hsign | hsign
      · simp [stdDecompWalkCoeff, d, htail_zero, hsign]
      · simp [stdDecompWalkCoeff, d, htail_zero, hsign]

lemma int_signed_eq_zero_of_two_mul_add_eq_zero
    {a b : ℤ} (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (h : 2 * (a : ℝ) + (b : ℝ) = 0) :
    a = 0 ∧ b = 0 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    norm_num at h
  norm_num

lemma stdLabel_signed_relation_coord_ne_base
    {n : ℕ} (i₀ : Fin n) (coeff : StdLabelIndex i₀ → ℤ)
    (hsum : (∑ t : StdLabelIndex i₀, (coeff t : ℝ) • stdLabel i₀ t) = 0)
    (i : {i : Fin n // i ≠ i₀}) :
    2 * (coeff (Sum.inl (i : Fin n)) : ℝ) + (coeff (Sum.inr i) : ℝ) = 0 := by
  classical
  have hcoord := congrFun hsum (i : Fin n)
  simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord
  rw [Fintype.sum_eq_single (i : Fin n)] at hcoord
  · rw [Fintype.sum_eq_single i] at hcoord
    · simpa [stdLabel_inl_apply, stdLabel_inr_apply, Ne.symm i.2, add_comm,
        add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hcoord
    · intro j hij
      have hji : (j : Fin n) ≠ (i : Fin n) := fun h => hij (Subtype.ext h)
      simp [stdLabel_inr_apply, Ne.symm i.2, hji]
  · intro j hij
    simp [stdLabel_inl_apply, hij]

lemma stdLabel_signed_relation_nonbase_coeffs_eq_zero
    {n : ℕ} (i₀ : Fin n) (coeff : StdLabelIndex i₀ → ℤ)
    (hcoeff : ∀ t, coeff t = -1 ∨ coeff t = 0 ∨ coeff t = 1)
    (hsum : (∑ t : StdLabelIndex i₀, (coeff t : ℝ) • stdLabel i₀ t) = 0)
    (i : {i : Fin n // i ≠ i₀}) :
    coeff (Sum.inl (i : Fin n)) = 0 ∧ coeff (Sum.inr i) = 0 := by
  exact int_signed_eq_zero_of_two_mul_add_eq_zero (hcoeff (Sum.inl (i : Fin n)))
    (hcoeff (Sum.inr i)) (stdLabel_signed_relation_coord_ne_base i₀ coeff hsum i)

lemma stdLabel_signed_relation_base_coeff_eq_zero
    {n : ℕ} (i₀ : Fin n) (coeff : StdLabelIndex i₀ → ℤ)
    (hsum : (∑ t : StdLabelIndex i₀, (coeff t : ℝ) • stdLabel i₀ t) = 0)
    (hinr_zero : ∀ i : {i : Fin n // i ≠ i₀}, coeff (Sum.inr i) = 0) :
    coeff (Sum.inl i₀) = 0 := by
  classical
  have hcoord := congrFun hsum i₀
  have hcoord' : 2 * (coeff (Sum.inl i₀) : ℝ) = 0 := by
    simpa [Fintype.sum_sum_type, stdLabel_inl_apply, stdLabel_inr_apply,
      Pi.smul_apply, Pi.zero_apply, hinr_zero, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hcoord
  have hreal : (coeff (Sum.inl i₀) : ℝ) = 0 := by
    linarith
  exact_mod_cast hreal

/-- The standard labels have no nontrivial linear relation whose coefficients are all
`-1`, `0`, or `1`. -/
lemma stdLabel_no_nontrivial_signed_relation
    {n : ℕ} (i₀ : Fin n) (coeff : StdLabelIndex i₀ → ℤ)
    (hcoeff : ∀ t, coeff t = -1 ∨ coeff t = 0 ∨ coeff t = 1)
    (hsum : (∑ t : StdLabelIndex i₀, (coeff t : ℝ) • stdLabel i₀ t) = 0) :
    ∀ t, coeff t = 0 := by
  intro t
  cases t with
  | inl i =>
      by_cases hi : i = i₀
      · simpa [hi] using
          (stdLabel_signed_relation_base_coeff_eq_zero i₀ coeff hsum fun i =>
            (stdLabel_signed_relation_nonbase_coeffs_eq_zero i₀ coeff hcoeff hsum i).2)
      · exact (stdLabel_signed_relation_nonbase_coeffs_eq_zero i₀ coeff hcoeff hsum
          ⟨i, hi⟩).1
  | inr i =>
      exact (stdLabel_signed_relation_nonbase_coeffs_eq_zero i₀ coeff hcoeff hsum i).2

/-- A cycle in the auxiliary graph gives a nonzero signed relation among the standard labels.

This is the formal version of telescoping
`(a₁+b₁)-(a₂+b₁)+(a₂+b₂)-⋯-(a₁+bₘ)=0` around the cycle. -/
lemma stdDecompGraph_cycle_gives_stdLabel_relation
    {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (_hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t))
    {v : StdDecompVertex a b} (p : (stdDecompGraph a b).Walk v v) (hp : p.IsCycle) :
    ∃ coeff : StdLabelIndex i₀ → ℤ,
      (∀ t, coeff t = -1 ∨ coeff t = 0 ∨ coeff t = 1) ∧
      (∃ t, coeff t ≠ 0) ∧
      (∑ t : StdLabelIndex i₀, (coeff t : ℝ) • stdLabel i₀ t) = 0 := by
  let coeff : StdLabelIndex i₀ → ℤ := stdDecompWalkCoeff p
  refine ⟨coeff, ?_, ?_, ?_⟩
  · intro t
    exact stdDecompWalkCoeff_eq_neg_one_or_zero_or_one_of_isTrail p hp.isTrail t
  · exact stdDecompWalkCoeff_nonzero_of_isCycle p hp
  · have hrel := stdDecompWalkCoeff_relation a b hab p
    simpa [coeff] using hrel

/-- The auxiliary graph is acyclic.  This is the formal target for the alternating-sum
contradiction on a cycle. -/
lemma stdDecompGraph_isAcyclic
    {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t)) :
    (stdDecompGraph a b).IsAcyclic := by
  intro v p hp
  obtain ⟨coeff, hcoeff, hnonzero, hsum⟩ :=
    stdDecompGraph_cycle_gives_stdLabel_relation a b hab hchosenEdge_injective p hp
  obtain ⟨t, ht⟩ := hnonzero
  exact ht (stdLabel_no_nontrivial_signed_relation i₀ coeff hcoeff hsum t)

/-- A finite acyclic graph has at most `vertices - 1` edges, phrased in the direction needed
for the proof. -/
lemma card_edgeSet_add_one_le_nat_card_of_isAcyclic
    {V : Type*} (G : SimpleGraph V) [Finite V]
    (hG : G.IsAcyclic) (hG_nonempty : Nonempty V) :
    Nat.card G.edgeSet + 1 ≤ Nat.card V := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  letI : Nonempty V := hG_nonempty
  obtain ⟨T, hGT, _hTtop, hT⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (G := ⊤) (H := G) le_top hG
  calc
    Nat.card G.edgeSet + 1 = G.edgeFinset.card + 1 := by
      rw [show Nat.card G.edgeSet = Fintype.card G.edgeSet by
        exact Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ ≤ T.edgeFinset.card + 1 :=
      Nat.add_le_add_right (Finset.card_mono (SimpleGraph.edgeFinset_mono hGT)) 1
    _ = Fintype.card V := hT.card_edgeFinset
    _ = Nat.card V := (Nat.card_eq_fintype_card : Nat.card V = Fintype.card V).symm

/-- The graph-theoretic counting result for the auxiliary graph. -/
lemma stdDecompGraph_forest_count
    {n : ℕ} {i₀ : Fin n} (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t)) :
    Fintype.card (StdLabelIndex i₀) + 1 ≤ Nat.card (StdDecompVertex a b) := by
  rw [← nat_card_edgeSet_stdDecompGraph a b hchosenEdge_injective]
  exact card_edgeSet_add_one_le_nat_card_of_isAcyclic (stdDecompGraph a b)
    (stdDecompGraph_isAcyclic a b hab hchosenEdge_injective)
    ⟨stdDecompLeft a b (Sum.inl i₀)⟩

/-- The remaining forest-counting core.  Given one decomposition of each test label as
`a t + b t`, the used left and right vertices have total cardinality at least `2n`.

The informal proof builds the bipartite graph with left vertices `Set.range a`, right vertices
`Set.range b`, and label-indexed edges `(a t, b t)`.  A graph cycle would produce an alternating
signed zero-sum of the corresponding `stdLabel`s, but these labels admit no nontrivial
`{-1, 0, 1}` relation.  Thus the graph is a forest, so `edges + 1 ≤ vertices`. -/
lemma stdLabel_decomposition_range_cardinality_bound
    {n : ℕ} (i₀ : Fin n) (a b : StdLabelIndex i₀ → RealSpace n)
    (hab : ∀ t, a t + b t = stdLabel i₀ t)
    (hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t)) :
    2 * n ≤ (Set.range a).ncard + (Set.range b).ncard := by
  rw [← fintype_card_stdLabelIndex_add_one i₀]
  have hforest := stdDecompGraph_forest_count a b hab hchosenEdge_injective
  rwa [nat_card_stdDecompVertex a b] at hforest

/-- The finite standard-coordinate theorem in positive dimension. -/
theorem normalized_standardBasis_sumset_cardinality_bound
    {n : ℕ} (i₀ : Fin n) (A B : Set (RealSpace n))
    (hA : A.Finite) (hB : B.Finite)
    (hcontains :
      (Set.range (Pi.basisFun ℝ (Fin n)) : Set (RealSpace n)) +
        Set.range (Pi.basisFun ℝ (Fin n)) ⊆ A + B) :
    2 * n ≤ A.ncard + B.ncard := by
  classical
  choose a ha b hb hab using
    fun t : StdLabelIndex i₀ => Set.mem_add.mp (hcontains (stdLabel_mem_standardBasis_add i₀ t))
  let AV : Set (RealSpace n) := Set.range a
  let BV : Set (RealSpace n) := Set.range b
  have hAV_sub_A : AV ⊆ A := by
    rintro _ ⟨t, rfl⟩
    exact ha t
  have hBV_sub_B : BV ⊆ B := by
    rintro _ ⟨t, rfl⟩
    exact hb t
  have hvertices_le_sets : AV.ncard + BV.ncard ≤ A.ncard + B.ncard :=
    add_le_add (Set.ncard_le_ncard hAV_sub_A hA) (Set.ncard_le_ncard hBV_sub_B hB)
  have hchosenEdge_injective : Function.Injective fun t : StdLabelIndex i₀ => (a t, b t) := by
    intro t u htu
    apply stdLabel_injective i₀
    calc
      stdLabel i₀ t = a t + b t := (hab t).symm
      _ = a u + b u := by
        have haeq : a t = a u := congrArg Prod.fst htu
        have hbeq : b t = b u := congrArg Prod.snd htu
        rw [haeq, hbeq]
      _ = stdLabel i₀ u := hab u
  have hforest_count : 2 * n ≤ AV.ncard + BV.ncard := by
    exact stdLabel_decomposition_range_cardinality_bound i₀ a b hab hchosenEdge_injective
  exact hforest_count.trans hvertices_le_sets

/-- The desired bound after reducing the basis to the standard coordinate basis. -/
theorem finite_standardBasis_sumset_cardinality_bound
    (n : ℕ) (A B : Set (RealSpace n)) (hA : A.Finite) (hB : B.Finite)
    (hcontains :
      (Set.range (Pi.basisFun ℝ (Fin n)) : Set (RealSpace n)) +
        Set.range (Pi.basisFun ℝ (Fin n)) ⊆ A + B) :
    2 * n ≤ A.ncard + B.ncard := by
  match n with
  | 0 => omega
  | n + 1 =>
      exact normalized_standardBasis_sumset_cardinality_bound (n := n + 1) 0 A B hA hB
        hcontains

/-- The desired bound after reducing the basis to the standard coordinate basis. -/
theorem standardBasis_sumset_cardinality_bound
    (n : ℕ) (A B : Set (RealSpace n))
    (hcontains :
      (Set.range (Pi.basisFun ℝ (Fin n)) : Set (RealSpace n)) +
        Set.range (Pi.basisFun ℝ (Fin n)) ⊆ A + B) :
    (2 * n : ℕ∞) ≤ A.encard + B.encard := by
  by_cases hAtop : A.encard = ⊤
  · simp [hAtop]
  by_cases hBtop : B.encard = ⊤
  · simp [hBtop]
  have hA : A.Finite := Set.encard_ne_top_iff.mp hAtop
  have hB : B.Finite := Set.encard_ne_top_iff.mp hBtop
  have hfinite := finite_standardBasis_sumset_cardinality_bound n A B hA hB hcontains
  rw [← hA.cast_ncard_eq, ← hB.cast_ncard_eq, ← Nat.cast_add]
  norm_cast

/-- If `A + B` contains `S + S` for an arbitrary basis `S` of `ℝ^n`, then
`|A| + |B| ≥ 2n`.

Cardinalities are stated in `ℕ∞`, so the statement also covers the case where one of the
summand sets is infinite. -/
theorem basis_sumset_cardinality_bound
    (n : ℕ) (S : Module.Basis (Fin n) ℝ (RealSpace n)) (A B : Set (RealSpace n))
    (hcontains : (Set.range S + Set.range S : Set (RealSpace n)) ⊆ A + B) :
    (2 * n : ℕ∞) ≤ A.encard + B.encard := by
  let e : RealSpace n ≃ₗ[ℝ] RealSpace n := S.equivFun
  let A' : Set (RealSpace n) := e '' A
  let B' : Set (RealSpace n) := e '' B
  have hcontains' :
      (Set.range (Pi.basisFun ℝ (Fin n)) : Set (RealSpace n)) +
        Set.range (Pi.basisFun ℝ (Fin n)) ⊆ A' + B' := by
    intro x hx
    rcases Set.mem_add.mp hx with ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    have hmem : S i + S j ∈ (Set.range S + Set.range S : Set (RealSpace n)) :=
      Set.mem_add.mpr ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    rcases Set.mem_add.mp (hcontains hmem) with ⟨a, ha, b, hb, hab⟩
    refine Set.mem_add.mpr ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_⟩
    rw [← map_add, hab]
    simp [e, Pi.basisFun_apply, Finsupp.single_eq_pi_single]
  have hstd := standardBasis_sumset_cardinality_bound n A' B' hcontains'
  simpa [A', B', (LinearEquiv.injective e).encard_image A,
    (LinearEquiv.injective e).encard_image B] using hstd

end BasisSubset

#print axioms BasisSubset.basis_sumset_cardinality_bound
-- 'BasisSubset.basis_sumset_cardinality_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
