/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Removing isolated vertices outside a minimal massed terminal set. -/

import ErdosProblems.Erdos717.InduceLinkage

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma sym2Map_incident_iff {W : Type*} [Fintype W] [DecidableEq W]
    (f : V ↪ W) (S : Finset V) (e : Sym2 V) :
    ¬(f.sym2Map e).toFinset ⊆ Finset.univ \ S.map f ↔
      ¬e.toFinset ⊆ Finset.univ \ S := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
        Sym2.toFinset_mk_eq]
      simp [Finset.subset_iff]

/-- If every edge of `G` is supported on `A`, inducing on `A` preserves
the number of edges incident with every corresponding vertex set. -/
lemma incidentEdges_induce_of_support_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    [DecidablePred (· ∈ A)]
    (hA : G.support ⊆ A) (S : Finset A) :
    incidentEdges (G.induce A) S =
      incidentEdges G (S.map (Function.Embedding.subtype A)) := by
  classical
  let f : A ↪ V := Function.Embedding.subtype A
  have hedge := G.map_edgeFinset_induce_of_support_subset hA
  change (G.induce A).edgeFinset.map f.sym2Map = G.edgeFinset at hedge
  unfold incidentEdges
  rw [← Finset.card_map f.sym2Map]
  congr 1
  ext e
  constructor
  · intro he
    rw [Finset.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    rw [Finset.mem_filter] at he₀ ⊢
    refine ⟨?_, ?_⟩
    · rw [← hedge]
      exact Finset.mem_map.mpr ⟨e₀, he₀.1, rfl⟩
    · exact (sym2Map_incident_iff f S e₀).mpr he₀.2
  · intro he
    rw [Finset.mem_filter] at he
    have hemap : e ∈ (G.induce A).edgeFinset.map f.sym2Map := by
      rw [hedge]
      exact he.1
    rw [Finset.mem_map] at hemap
    obtain ⟨e₀, he₀, heeq⟩ := hemap
    subst e
    rw [Finset.mem_map]
    refine ⟨e₀, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨he₀, (sym2Map_incident_iff f S e₀).mp he.2⟩

namespace MassedCounterexample

variable {k : ℕ}

/-- The inclusion of a finset known to lie in an induced vertex set. -/
def restrictEmbedding (A : Set V) (X : Finset V)
    (hX : (X : Set V) ⊆ A) : {x // x ∈ X} ↪ A where
  toFun x := ⟨x, hX x.property⟩
  inj' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    exact congrArg (fun z : A => (z : V)) h

/-- The copy of `X` in an induced subtype known to contain it. -/
def restrictFinset (A : Set V) (X : Finset V) (hX : (X : Set V) ⊆ A) :
    Finset A := X.attach.map (restrictEmbedding A X hX)

lemma map_restrictFinset (A : Set V) (X : Finset V)
    (hX : (X : Set V) ⊆ A) :
    (restrictFinset A X hX).map (Function.Embedding.subtype A) = X := by
  classical
  ext x
  simp only [restrictFinset, Finset.mem_map]
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨y, hy, hya⟩ := ha
    have hyx : (y : V) = x :=
      (congrArg (fun z : A => (z : V)) hya).trans hax
    rw [← hyx]
    exact y.property
  · intro hx
    let y : {z // z ∈ X} := ⟨x, hx⟩
    let a : A := restrictEmbedding A X hX y
    refine ⟨a, ?_, rfl⟩
    exact ⟨y, Finset.mem_attach X y, rfl⟩

lemma mem_restrictFinset (A : Set V) (X : Finset V)
    (hX : (X : Set V) ⊆ A) (a : A) :
    a ∈ restrictFinset A X hX ↔ (a : V) ∈ X := by
  constructor
  · intro ha
    have hm : (a : V) ∈
        (restrictFinset A X hX).map (Function.Embedding.subtype A) :=
      Finset.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [map_restrictFinset A X hX] at hm
  · intro ha
    have hm : (a : V) ∈
        (restrictFinset A X hX).map (Function.Embedding.subtype A) := by
      rw [map_restrictFinset A X hX]
      exact ha
    rw [Finset.mem_map] at hm
    obtain ⟨b, hb, hba⟩ := hm
    have : b = a := (Function.Embedding.subtype A).injective hba
    simpa [this] using hb

lemma card_restrictFinset (A : Set V) (X : Finset V)
    (hX : (X : Set V) ⊆ A) :
    (restrictFinset A X hX).card = X.card := by
  simp [restrictFinset]

/-- Lift a separation from the complement of an isolated vertex, placing
the removed vertex only on the left. -/
def liftRemoveIsolated (G : SimpleGraph V) {v : V}
    (hiso : G.IsIsolated v)
    (s : Erdos718.Separation (G.induce {x | x ≠ v})) :
    Erdos718.Separation G where
  left := s.left.map (Function.Embedding.subtype _) ∪ {v}
  right := s.right.map (Function.Embedding.subtype _)
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_singleton,
      Finset.mem_univ, iff_true]
    by_cases hx : x = v
    · exact Or.inl (Or.inr hx)
    · have hxsub : (⟨x, hx⟩ : {x : V | x ≠ v}) ∈ s.left ∪ s.right := by
        rw [s.cover]
        exact Finset.mem_univ _
      rcases Finset.mem_union.mp hxsub with hxL | hxR
      · exact Or.inl (Or.inl ⟨⟨x, hx⟩, hxL, rfl⟩)
      · exact Or.inr ⟨⟨x, hx⟩, hxR, rfl⟩
  not_adj := by
    intro a b haL haR hbR hbL hab
    by_cases hav : a = v
    · subst a
      exact hiso b hab
    have hbv : b ≠ v := by
      intro h
      subst b
      simpa using hbR
    have haLs : (⟨a, hav⟩ : {x : V | x ≠ v}) ∈ s.left := by
      have : a ∈ s.left.map (Function.Embedding.subtype _) := by
        simpa [hav] using haL
      rw [Finset.mem_map] at this
      obtain ⟨z, hz, hza⟩ := this
      have hzeq : z = ⟨a, hav⟩ := by
        apply Subtype.ext
        exact hza
      simpa [hzeq] using hz
    have haRs : (⟨a, hav⟩ : {x : V | x ≠ v}) ∉ s.right := by
      intro h
      apply haR
      exact Finset.mem_map.mpr ⟨⟨a, hav⟩, h, rfl⟩
    have hbRs : (⟨b, hbv⟩ : {x : V | x ≠ v}) ∈ s.right := by
      rw [Finset.mem_map] at hbR
      obtain ⟨z, hz, hzb⟩ := hbR
      have hzeq : z = ⟨b, hbv⟩ := by
        apply Subtype.ext
        exact hzb
      simpa [hzeq] using hz
    have hbLs : (⟨b, hbv⟩ : {x : V | x ≠ v}) ∉ s.left := by
      intro h
      apply hbL
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_map.mpr ⟨⟨b, hbv⟩, h, rfl⟩))
    exact s.not_adj haLs haRs hbRs hbLs hab

lemma separator_liftRemoveIsolated (G : SimpleGraph V) {v : V}
    (hiso : G.IsIsolated v)
      (s : Erdos718.Separation (G.induce {x | x ≠ v})) :
    (liftRemoveIsolated G hiso s).separator =
      s.separator.map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [Erdos718.Separation.separator, liftRemoveIsolated,
    Finset.mem_inter, Finset.mem_union, Finset.mem_map,
    Finset.mem_singleton]
  constructor
  · rintro ⟨(⟨a, ha, hax⟩ | hxv), ⟨b, hb, hbx⟩⟩
    · have hab : a = b := by
        apply Subtype.ext
        exact hax.trans hbx.symm
      subst b
      exact ⟨a, ⟨ha, hb⟩, hax⟩
    · subst x
      exact (b.property hbx).elim
  · rintro ⟨a, ha, hax⟩
    exact ⟨Or.inl ⟨a, ha.1, hax⟩, ⟨a, ha.2, hax⟩⟩

lemma strictRight_liftRemoveIsolated (G : SimpleGraph V) {v : V}
    (hiso : G.IsIsolated v)
    (s : Erdos718.Separation (G.induce {x | x ≠ v})) :
    (liftRemoveIsolated G hiso s).right \
        (liftRemoveIsolated G hiso s).left =
      (s.right \ s.left).map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [liftRemoveIsolated, Finset.mem_sdiff, Finset.mem_map,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, haR, hax⟩, hnot⟩
    have hax' : (a : V) = x := hax
    have haL : a ∉ s.left := by
      intro h
      exact hnot (Or.inl ⟨a, h, hax⟩)
    exact ⟨a, ⟨haR, haL⟩, hax'⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro (⟨b, hb, hba⟩ | hav)
    · have hab : a = b := Subtype.ext hba.symm
      subst b
      exact ha.2 hb
    · exact a.property hav

/-- A lexicographically minimal massed counterexample has no isolated
vertex outside its terminal set. -/
theorem noIsolatedOutside_of_lexMinimal
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal) :
    C.NoIsolatedOutside := by
  classical
  intro v hvX
  by_contra hno
  have hiso : C.G.IsIsolated v := by
    intro u hvu
    exact hno ⟨u, hvu.symm⟩
  let A : Set C.V := {x | x ≠ v}
  have hXA : (C.X : Set C.V) ⊆ A := by
    intro x hx hxv
    subst x
    exact hvX hx
  let X' : Finset A := restrictFinset A C.X hXA
  have hXcard : X'.card = C.X.card := card_restrictFinset A C.X hXA
  have hsupport : C.G.support ⊆ A := by
    intro x hx hxv
    subst x
    exact (C.G.notMem_support_iff_isIsolated.mpr hiso) hx
  have hinc (S : Finset A) :
      incidentEdges (C.G.induce A) S =
        incidentEdges C.G (S.map (Function.Embedding.subtype A)) :=
    incidentEdges_induce_of_support_subset C.G A hsupport S
  have houtsideMap :
      (Finset.univ \ X').map (Function.Embedding.subtype A) =
        (Finset.univ \ C.X) \ {v} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun hxX => ha ((mem_restrictFinset A C.X hXA a).mpr hxX),
        a.property⟩
    · rintro ⟨hxX, hxv⟩
      refine ⟨⟨x, hxv⟩, ?_, rfl⟩
      exact fun ha => hxX ((mem_restrictFinset A C.X hXA _).mp ha)
  have houtsideIncident :
      incidentEdges (C.G.induce A) (Finset.univ \ X') =
        incidentEdges C.G (Finset.univ \ C.X) := by
    rw [hinc, houtsideMap]
    unfold incidentEdges
    congr 1
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨he, htouch⟩
      refine ⟨he, ?_⟩
      intro hsub
      apply htouch
      intro x hx
      have hxnotO := (Finset.mem_sdiff.mp (hsub hx)).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO =>
        hxnotO (Finset.mem_sdiff.mp hxO).1⟩
    · rintro ⟨he, htouch⟩
      refine ⟨he, ?_⟩
      intro hsub
      apply htouch
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hxO
      have hxnotSmall := (Finset.mem_sdiff.mp (hsub hx)).2
      have hxv : x = v := by
        by_contra hxne
        exact hxnotSmall (Finset.mem_sdiff.mpr ⟨hxO, by simpa using hxne⟩)
      subst x
      have hvSupp : v ∈ C.G.support := by
        induction e using Sym2.inductionOn with
        | _ a b =>
            change C.G.Adj a b at he
            rw [Sym2.toFinset_mk_eq] at hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨b, he⟩
            · have : v = b := Finset.mem_singleton.mp hx
              subst b
              exact ⟨a, he.symm⟩
      exact (C.G.notMem_support_iff_isIsolated.mpr hiso) hvSupp
  have hcardA : Fintype.card A = Fintype.card C.V - 1 := by
    calc
      Fintype.card A = Fintype.card {x : C.V // ¬x = v} := by rfl
      _ = Fintype.card C.V - Fintype.card {x : C.V // x = v} :=
        Fintype.card_subtype_compl (fun x : C.V => x = v)
      _ = Fintype.card C.V - 1 := by simp
  have hmassed : IsEightKMassed (C.G.induce A) X' k := by
    constructor
    · rw [houtsideIncident, hXcard, hcardA]
      have hproper : C.X ⊂ (Finset.univ : Finset C.V) := by
        refine ⟨Finset.subset_univ C.X, ?_⟩
        intro hrev
        apply hvX
        exact hrev (Finset.mem_univ v)
      have hXlt : C.X.card < Fintype.card C.V := by
        simpa using Finset.card_lt_card hproper
      exact (Nat.mul_le_mul_left (8 * k)
        (Nat.sub_le_sub_right (Nat.sub_le _ 1) C.X.card)).trans_lt C.massed.1
    · intro s hXleft horder
      let t := liftRemoveIsolated C.G hiso s
      have hXleft' : C.X ⊆ t.left := by
        intro x hx
        have hxA : x ∈ A := hXA hx
        have hxX' : (⟨x, hxA⟩ : A) ∈ X' := by
          exact (mem_restrictFinset A C.X hXA _).mpr hx
        have hxsL := hXleft hxX'
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_map.mpr ⟨⟨x, hxA⟩, hxsL, rfl⟩))
      have horder' : t.separator.card < C.X.card := by
        rw [separator_liftRemoveIsolated C.G hiso s, Finset.card_map]
        exact horder.trans_le hXcard.le
      have ht := C.massed.2 t hXleft' horder'
      rw [strictRight_liftRemoveIsolated C.G hiso s] at ht
      rw [Finset.card_map] at ht
      rw [hinc]
      have hmapEq :
          (s.right \ s.left).map
              (Function.Embedding.subtype
                (fun x : C.V => x ∈ ({y : C.V | y ≠ v} : Set C.V))) =
            (s.right \ s.left).map (Function.Embedding.subtype A) := by
        ext x
        simp only [Finset.mem_map]
        constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
      rw [hmapEq] at ht
      exact ht
  have hnotLinked : ¬Erdos718.IsLinkedSet
      (C.G.induce A) (X' : Set A) := by
    intro hlinked
    apply C.not_linked
    apply isLinkedSet_of_induce hXA
    have hcoe : (X' : Set A) = {a : A | (a : C.V) ∈ C.X} := by
      ext a
      exact mem_restrictFinset A C.X hXA a
    rwa [hcoe] at hlinked
  let D : MassedCounterexample k := {
    V := A
    fintypeV := inferInstance
    decEqV := inferInstance
    G := C.G.induce A
    decAdj := inferInstance
    X := X'
    card_le := hXcard.trans_le C.card_le
    massed := hmassed
    not_linked := hnotLinked
  }
  have hminimal := (hmin D).1
  change Fintype.card C.V ≤ Fintype.card A at hminimal
  rw [hcardA] at hminimal
  have hpos : 0 < Fintype.card C.V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

end MassedCounterexample
end ThomasWollanMassed
end Erdos717
