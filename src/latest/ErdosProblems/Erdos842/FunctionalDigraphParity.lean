import ErdosProblems.Erdos842.OddTransversal

/-!
# Functional-digraph fibres in Petrov's parity argument

A function `g : I → I` encodes an outdegree-at-most-one directed graph by
treating its fixed points as vertices with no outgoing arc.  This file proves
the even-fibre step in Petrov's argument: if the underlying nonloop graph has
a leaf `p`, all constraints involving `p` reduce to one bipartite-neighbour
condition, hence every fibre has even cardinality.
-/

open scoped BigOperators

namespace Erdos842.FunctionalDigraphParity

open OddTransversal

universe u v

variable {I : Type u} (X : I → Type v)

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A transversal realizes `g` when every nonloop arc `i → g i` is an edge
of the chosen cross relation.  Fixed points encode absent arcs. -/
abbrev Realizes (cross : CrossRel X) (g : I → I) (f : ∀ i, X i) : Prop :=
  OddTransversal.Realizes X cross g f

/-- The finite type of transversals realizing one functional-digraph pattern. -/
abbrev Realizer [Fintype I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) : Type _ :=
  {f : ∀ i, X i // Realizes X cross g f}

/-- `p` is a leaf with unique distinct neighbour `q` in the undirected graph
underlying the nonloop arcs of `g`. -/
def IsLeaf (g : I → I) (p q : I) : Prop :=
  p ≠ q ∧
    (g p = q ∨ g q = p) ∧
    ∀ i, i ≠ g i → (i = p ∨ g i = p) →
      (i = p ∧ g i = q) ∨ (i = q ∧ g i = p)

/-- The undirected simple graph obtained from the nonloop arcs of `g`. -/
abbrev functionGraph (g : I → I) : SimpleGraph I :=
  OddTransversal.functionGraph g

@[simp] theorem functionGraph_adj (g : I → I) (i j : I) :
    (functionGraph g).Adj i j ↔ i ≠ j ∧ (g i = j ∨ g j = i) := by
  exact OddTransversal.functionGraph_adj g i j

/-- A degree-one vertex of a functional graph supplies exactly the leaf
witness used by `even_card_realizer_of_leaf`. -/
theorem exists_isLeaf_of_degree_eq_one [Fintype I] [DecidableEq I]
    (g : I → I) {p : I} (hdegree : (functionGraph g).degree p = 1) :
    ∃ q, IsLeaf g p q := by
  classical
  obtain ⟨q, hpq, huniq⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
  have hpq' := (functionGraph_adj g p q).mp hpq
  refine ⟨q, hpq'.1, hpq'.2, ?_⟩
  intro i hi hinc
  rcases hinc with rfl | htarget
  · have hadj : (functionGraph g).Adj i (g i) :=
      (functionGraph_adj g i (g i)).mpr ⟨hi, Or.inl rfl⟩
    exact Or.inl ⟨rfl, huniq (g i) hadj⟩
  · have hip : i ≠ p := by simpa [htarget] using hi
    have hadj : (functionGraph g).Adj p i :=
      (functionGraph_adj g p i).mpr ⟨hip.symm, Or.inr htarget⟩
    exact Or.inr ⟨huniq i hadj, htarget⟩

/-- Dependent assignments away from one distinguished index. -/
abbrev Away (p : I) := ∀ i : {i : I // i ≠ p}, X i

/-- Extend an assignment away from `p` by a chosen value at `p`. -/
noncomputable def extendAway (p : I) (rest : Away X p) (xp : X p) : ∀ i, X i :=
  fun i ↦ if h : i = p then h.symm ▸ xp else rest ⟨i, h⟩

@[simp] theorem extendAway_same (p : I) (rest : Away X p) (xp : X p) :
    extendAway X p rest xp p = xp := by
  simp [extendAway]

@[simp] theorem extendAway_ne (p : I) (rest : Away X p) (xp : X p)
    {i : I} (hi : i ≠ p) :
    extendAway X p rest xp i = rest ⟨i, hi⟩ := by
  simp [extendAway, hi]

/-- The part of the realization condition supported completely away from `p`. -/
def RealizesAway (cross : CrossRel X) (g : I → I) (p : I) (rest : Away X p) : Prop :=
  ∀ i (hi : i ≠ g i) (hip : i ≠ p) (hgp : g i ≠ p),
    cross i (g i) (rest ⟨i, hip⟩) (rest ⟨g i, hgp⟩)

/-- At a leaf, realizing the whole pattern is exactly the conjunction of the
constraints away from the leaf and one cross-edge condition. -/
theorem realizes_extendAway_iff
    (cross : CrossRel X) (hsymm : OddTransversal.Symmetric X cross)
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q)
    (rest : Away X p) (xp : X p) :
    Realizes X cross g (extendAway X p rest xp) ↔
      RealizesAway X cross g p rest ∧
        cross p q xp (rest ⟨q, hleaf.1.symm⟩) := by
  classical
  constructor
  · intro hreal
    constructor
    · intro i hi hip hgp
      simpa [extendAway, hip, hgp] using hreal i hi
    · rcases hleaf.2.1 with hpq | hqp
      · have hpn : p ≠ g p := by simpa [hpq] using hleaf.1
        have hr := hreal p hpn
        rw [hpq] at hr
        rw [extendAway_same, extendAway_ne X p rest xp hleaf.1.symm] at hr
        exact hr
      · have hqn : q ≠ g q := by simpa [hqp] using hleaf.1.symm
        have hcross := hreal q hqn
        rw [hqp] at hcross
        rw [extendAway_ne X p rest xp hleaf.1.symm, extendAway_same] at hcross
        have hs := (hsymm q p
          (rest ⟨q, hleaf.1.symm⟩) xp).mp hcross
        exact hs
  · rintro ⟨haway, hpqCross⟩ i hi
    by_cases hip : i = p
    · subst i
      have hinc := hleaf.2.2 p hi (Or.inl rfl)
      rcases hinc with h | h
      · have hg : g p = q := h.2
        rw [hg]
        rw [extendAway_same, extendAway_ne X p rest xp hleaf.1.symm]
        exact hpqCross
      · exact (hleaf.1 h.1).elim
    · by_cases hgp : g i = p
      · have hinc := hleaf.2.2 i hi (Or.inr hgp)
        rcases hinc with h | h
        · exact (hip h.1).elim
        · have hiq : i = q := h.1
          subst i
          have hs := (hsymm p q xp (rest ⟨q, hleaf.1.symm⟩)).mp hpqCross
          rw [hgp]
          rw [extendAway_ne X p rest xp hleaf.1.symm, extendAway_same]
          exact hs
      · simpa [extendAway, hip, hgp] using haway i hi hip hgp

/-- The fibre over a fixed assignment away from a leaf has even cardinality. -/
theorem even_leaf_fiber
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsymm : OddTransversal.Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q) (rest : Away X p) :
    Even (Fintype.card
      {xp : X p // Realizes X cross g (extendAway X p rest xp)}) := by
  classical
  by_cases haway : RealizesAway X cross g p rest
  · have hpred : ∀ xp : X p,
        Realizes X cross g (extendAway X p rest xp) ↔
          cross q p (rest ⟨q, hleaf.1.symm⟩) xp := by
      intro xp
      rw [realizes_extendAway_iff X cross hsymm g hleaf rest xp]
      rw [and_iff_right haway]
      exact hsymm p q xp (rest ⟨q, hleaf.1.symm⟩)
    rw [Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter fun xp : X p ↦
          Realizes X cross g (extendAway X p rest xp)) =
        Finset.univ.filter fun xp : X p ↦
          cross q p (rest ⟨q, hleaf.1.symm⟩) xp := by
      ext xp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred xp
    change Even ((Finset.univ.filter fun xp : X p ↦
      Realizes X cross g (extendAway X p rest xp)).card)
    rw [hfilter]
    exact heven q p (rest ⟨q, hleaf.1.symm⟩) hleaf.1.symm
  · haveI : IsEmpty {xp : X p // Realizes X cross g (extendAway X p rest xp)} :=
      ⟨fun xp ↦ haway
        ((realizes_extendAway_iff X cross hsymm g hleaf rest xp.1).mp xp.2).1⟩
    simp

/-- Split a dependent transversal into its value at `p` and its restriction
away from `p`. -/
noncomputable def piEquivSigmaAway (p : I) :
    (∀ i, X i) ≃ Σ rest : Away X p, X p where
  toFun f := ⟨fun i ↦ f i, f p⟩
  invFun z := extendAway X p z.1 z.2
  left_inv f := by
    funext i
    by_cases hi : i = p
    · subst i
      simp
    · simp [extendAway, hi]
  right_inv z := by
    rcases z with ⟨rest, xp⟩
    apply Sigma.ext
    · funext i
      exact extendAway_ne X p rest xp i.property
    · simp

/-- Regroup a subtype of a sigma type as a sigma type of subtypes. -/
noncomputable def subtypeSigmaRealizesEquiv [Fintype I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) (p : I) :
    {z : Σ rest : Away X p, X p //
      Realizes X cross g (extendAway X p z.1 z.2)} ≃
      Σ rest : Away X p,
        {xp : X p // Realizes X cross g (extendAway X p rest xp)} where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Realizers split as a sigma type of leaf-value fibres over assignments
away from the leaf. -/
noncomputable def realizerEquivSigmaFiber [Fintype I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) (p : I) :
    Realizer X cross g ≃
      Σ rest : Away X p,
        {xp : X p // Realizes X cross g (extendAway X p rest xp)} := by
  let e := piEquivSigmaAway X p
  let eSub : Realizer X cross g ≃
      {z : Σ rest : Away X p, X p //
        Realizes X cross g (extendAway X p z.1 z.2)} :=
    e.subtypeEquiv fun f ↦ by
      have heq : extendAway X p (e f).1 (e f).2 = f := e.symm_apply_apply f
      rw [heq]
  exact eSub.trans (subtypeSigmaRealizesEquiv X cross g p)

/-- Petrov's nonempty-pattern fibre is even whenever the functional digraph
has a leaf and all cross-part degrees are even. -/
theorem even_card_realizer_of_leaf
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsymm : OddTransversal.Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p q : I} (hleaf : IsLeaf g p q) :
    Even (Fintype.card (Realizer X cross g)) := by
  classical
  rw [Fintype.card_congr (realizerEquivSigmaFiber X cross g p), Fintype.card_sigma]
  have hsum : ∀ s : Finset (Away X p),
      (∀ rest ∈ s, Even (Fintype.card
        {xp : X p // Realizes X cross g (extendAway X p rest xp)})) →
      Even (∑ rest ∈ s, Fintype.card
        {xp : X p // Realizes X cross g (extendAway X p rest xp)}) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert rest s hrest ih =>
        rw [Finset.sum_insert hrest]
        exact (hs rest (by simp)).add (ih fun r hr ↦ hs r (by simp [hr]))
  exact hsum Finset.univ fun rest _ ↦
    even_leaf_fiber X cross hsymm heven g hleaf rest

/-- `patternWeight` is the cardinality of the realizing-transversal subtype,
reduced modulo two. -/
theorem patternWeight_eq_cast_card_realizer
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (g : I → I) :
    OddTransversal.patternWeight X cross g =
      (Fintype.card (Realizer X cross g) : ZMod 2) := by
  classical
  letI : Fintype (∀ i, X i) := Pi.instFintype
  unfold OddTransversal.patternWeight Realizer
  rw [Fintype.card_subtype]
  simp

/-- The exact leaf case needed by Petrov's functional-graph expansion: a
degree-one vertex forces the pattern weight to vanish in `ZMod 2`. -/
theorem patternWeight_eq_zero_of_degree_eq_one
    [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)]
    (cross : CrossRel X) (hsymm : OddTransversal.Symmetric X cross)
    (heven : ∀ i j (xi : X i), i ≠ j → Even (crossDegree X cross i j xi))
    (g : I → I) {p : I} (hdegree : (OddTransversal.functionGraph g).degree p = 1) :
    OddTransversal.patternWeight X cross g = 0 := by
  obtain ⟨q, hleaf⟩ := exists_isLeaf_of_degree_eq_one g hdegree
  rw [patternWeight_eq_cast_card_realizer X cross g]
  exact (OddTransversal.even_iff_cast_zmod_two_eq_zero _).mp
    (even_card_realizer_of_leaf X cross hsymm heven g hleaf)

end Erdos842.FunctionalDigraphParity
