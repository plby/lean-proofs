/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Edge-mass bookkeeping for the left torso of a separation. -/

import ErdosProblems.Erdos717.TorsoExpansion

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Delete all edges touching a prescribed vertex set, without changing the
ambient vertex type. -/
def avoidVertices (G : SimpleGraph V) (R : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ R ∧ y ∉ R
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩

instance avoidVertices.instDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset V) :
    DecidableRel (avoidVertices G R).Adj :=
  inferInstanceAs <| DecidableRel fun x y => G.Adj x y ∧ x ∉ R ∧ y ∉ R

lemma avoidVertices_le (G : SimpleGraph V) (R : Finset V) :
    avoidVertices G R ≤ G := fun _ _ h => h.1

/-- Partition edges incident with `S` according to whether they touch `R`.
The part avoiding `R` is counted in `avoidVertices G R`. -/
lemma incidentEdges_le_avoidVertices_add
    (G : SimpleGraph V) [DecidableRel G.Adj] (S R : Finset V) :
    incidentEdges G S ≤
      incidentEdges (avoidVertices G R) S + incidentEdges G R := by
  classical
  unfold incidentEdges
  let E := G.edgeFinset.filter fun e =>
    ¬e.toFinset ⊆ Finset.univ \ S
  let E₀ := (avoidVertices G R).edgeFinset.filter fun e =>
    ¬e.toFinset ⊆ Finset.univ \ S
  let ER := G.edgeFinset.filter fun e =>
    ¬e.toFinset ⊆ Finset.univ \ R
  have hsubset : E ⊆ E₀ ∪ ER := by
    intro e he
    simp only [E, E₀, ER, Finset.mem_union, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.inductionOn with
    | _ a b =>
        rw [not_pair_subset_compl_iff] at he ⊢
        by_cases hR : a ∈ R ∨ b ∈ R
        · exact Or.inr ⟨he.1,
            (not_pair_subset_compl_iff R a b).2 hR⟩
        · push_neg at hR
          exact Or.inl ⟨⟨he.1, hR.1, hR.2⟩, he.2⟩
  calc
    E.card ≤ (E₀ ∪ ER).card := Finset.card_le_card hsubset
    _ ≤ E₀.card + ER.card := Finset.card_union_le E₀ ER

/-- Every surviving edge after deleting the strict right side is supported
on the left side. -/
lemma support_avoidStrictRight_subset_left
    {G : SimpleGraph V} (s : Erdos718.Separation G) :
    (avoidVertices G (s.right \ s.left)).support ⊆
      (s.left : Set V) := by
  intro x hx
  obtain ⟨y, hxy⟩ := (avoidVertices G (s.right \ s.left)).mem_support.mp hx
  rcases s.mem_left_or_mem_right x with hxL | hxR
  · exact hxL
  · by_contra hxL
    exact hxy.2.1 (Finset.mem_sdiff.mpr ⟨hxR, hxL⟩)

/-- Inducing a graph supported on `A` and restricting the distinguished set
preserves the count of edges incident outside that set. -/
lemma incidentEdges_induce_compl_restrict
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) [Fintype A] [DecidableEq A]
    (hA : G.support ⊆ A) (X : Finset V) (hX : (X : Set V) ⊆ A) :
    incidentEdges (G.induce A)
        (Finset.univ \ MassedCounterexample.restrictFinset A X hX) =
      incidentEdges G (Finset.univ \ X) := by
  classical
  let f : A ↪ V := Function.Embedding.subtype A
  have hedge : (G.induce A).edgeFinset.map f.sym2Map = G.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_map] at he
      obtain ⟨e₀, he₀, rfl⟩ := he
      simp only [SimpleGraph.mem_edgeFinset] at he₀ ⊢
      induction e₀ using Sym2.inductionOn with
      | _ a b => exact he₀
    · intro he
      simp only [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.inductionOn with
      | _ a b =>
          have haA : a ∈ A := hA he.mem_support_left
          have hbA : b ∈ A := hA he.mem_support_right
          let a' : A := ⟨a, haA⟩
          let b' : A := ⟨b, hbA⟩
          refine Finset.mem_map.mpr ⟨s(a', b'), ?_, rfl⟩
          simp only [SimpleGraph.mem_edgeFinset]
          change G.Adj (a : V) (b : V)
          exact he
  unfold incidentEdges
  rw [← Finset.card_map f.sym2Map]
  congr 1
  ext e
  constructor
  · intro he
    rw [Finset.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he₀ ⊢
    induction e₀ using Sym2.inductionOn with
    | _ a b =>
        rw [not_pair_subset_compl_iff] at he₀
        change G.Adj (a : V) (b : V) ∧
          ¬s((a : V), (b : V)).toFinset ⊆
            Finset.univ \ (Finset.univ \ X)
        rw [not_pair_subset_compl_iff]
        refine ⟨he₀.1, ?_⟩
        exact he₀.2.imp
          (fun ha => by
            rw [Finset.mem_sdiff] at ha ⊢
            exact ⟨Finset.mem_univ _, fun hmem =>
              ha.2 ((MassedCounterexample.mem_restrictFinset
                A X hX a).2 hmem)⟩)
          (fun hb => by
            rw [Finset.mem_sdiff] at hb ⊢
            exact ⟨Finset.mem_univ _, fun hmem =>
              hb.2 ((MassedCounterexample.mem_restrictFinset
                A X hX b).2 hmem)⟩)
  · intro he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
        rw [not_pair_subset_compl_iff] at he
        have haA : a ∈ A := hA he.1.mem_support_left
        have hbA : b ∈ A := hA he.1.mem_support_right
        let a' : A := ⟨a, haA⟩
        let b' : A := ⟨b, hbA⟩
        refine Finset.mem_map.mpr ⟨s(a', b'), ?_, rfl⟩
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
        rw [not_pair_subset_compl_iff]
        refine ⟨he.1, ?_⟩
        exact he.2.imp
          (fun ha => by
            rw [Finset.mem_sdiff] at ha ⊢
            exact ⟨Finset.mem_univ _, fun hmem =>
              ha.2 ((MassedCounterexample.mem_restrictFinset
                A X hX a').1 hmem)⟩)
          (fun hb => by
            rw [Finset.mem_sdiff] at hb ⊢
            exact ⟨Finset.mem_univ _, fun hmem =>
              hb.2 ((MassedCounterexample.mem_restrictFinset
                A X hX b').1 hmem)⟩)

/-- The surviving induced graph embeds edgewise into the completed left
torso. -/
lemma induce_avoidStrictRight_le_leftTorso
    {G : SimpleGraph V} (s : Erdos718.Separation G) :
    (avoidVertices G (s.right \ s.left)).induce (s.left : Set V) ≤
      leftTorso s := by
  intro x y hxy
  exact Or.inl hxy.1

lemma card_left_add_card_strictRight
    {G : SimpleGraph V} (s : Erdos718.Separation G) :
    s.left.card + (s.right \ s.left).card = Fintype.card V := by
  have hdisj : Disjoint s.left (s.right \ s.left) := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxR
    exact (Finset.mem_sdiff.mp hxR).2 hxL
  have hunion : s.left ∪ (s.right \ s.left) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
      iff_true]
    rcases s.mem_left_or_mem_right x with hx | hx
    · exact Or.inl hx
    · by_cases hxL : x ∈ s.left
      · exact Or.inl hxL
      · exact Or.inr ⟨hx, hxL⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

/-- The first mass condition descends to the completed left torso whenever
the original mass condition bounds the strict right side. -/
theorem leftTorso_first_mass
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s : Erdos718.Separation G) (X : Finset V)
    (hX : X ⊆ s.left) (k : ℕ)
    (hglobal : 8 * k * (Fintype.card V - X.card) <
      incidentEdges G (Finset.univ \ X))
    (hright : incidentEdges G (s.right \ s.left) ≤
      8 * k * (s.right \ s.left).card) :
    8 * k *
        (Fintype.card (s.left : Set V) -
          (MassedCounterexample.restrictFinset
            (s.left : Set V) X hX).card) <
      incidentEdges (leftTorso s)
        (Finset.univ \ MassedCounterexample.restrictFinset
          (s.left : Set V) X hX) := by
  classical
  have hleftCard₀ : Fintype.card (s.left : Set V) = s.left.card := by simp
  let H := avoidVertices G (s.right \ s.left)
  let Xl := MassedCounterexample.restrictFinset (s.left : Set V) X hX
  have hpartition := incidentEdges_le_avoidVertices_add G
    (Finset.univ \ X) (s.right \ s.left)
  have hinduce : incidentEdges (H.induce (s.left : Set V))
      (Finset.univ \ Xl) = incidentEdges H (Finset.univ \ X) := by
    exact incidentEdges_induce_compl_restrict H (s.left : Set V)
      (support_avoidStrictRight_subset_left s) X hX
  have hmono : incidentEdges (H.induce (s.left : Set V))
      (Finset.univ \ Xl) ≤ incidentEdges (leftTorso s)
        (Finset.univ \ Xl) :=
    incidentEdges_mono (induce_avoidStrictRight_le_leftTorso s) _
  have hXcard : Xl.card = X.card := by
    exact MassedCounterexample.card_restrictFinset _ _ _
  have hXleLeft : X.card ≤ s.left.card := Finset.card_le_card hX
  have hdecomp := card_left_add_card_strictRight s
  have houtsideDecomp :
      Fintype.card V - X.card =
        (s.left.card - X.card) + (s.right \ s.left).card := by
    omega
  have hmassDecomp :
      8 * k * (Fintype.card V - X.card) =
        8 * k * (s.left.card - X.card) +
          8 * k * (s.right \ s.left).card := by
    rw [houtsideDecomp, mul_add]
  have hraw : 8 * k * (s.left.card - X.card) <
      incidentEdges (leftTorso s) (Finset.univ \ Xl) := by
    dsimp only [H, Xl] at hinduce hmono
    dsimp only [Xl]
    omega
  change 8 * k * (Fintype.card (s.left : Set V) - Xl.card) <
    incidentEdges (leftTorso s) (Finset.univ \ Xl)
  calc
    8 * k * (Fintype.card (s.left : Set V) - Xl.card) =
        8 * k * (s.left.card - X.card) := by
          rw [hleftCard₀, hXcard]
    _ < incidentEdges (leftTorso s) (Finset.univ \ Xl) := hraw

end ThomasWollanMassed
end Erdos717
