import ErdosProblems.Erdos88.Foundations
import ErdosProblems.Erdos636.Structural
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Edge-count identities for the Kwan--Sudakov augmentation

This file records the exact finite bookkeeping used in the augmentation
argument for Erdős problem 636.  `crossingEdges G S T` is the unordered edge
family represented by Mathlib's oriented `G.interedges S T`.  When `S` and
`T` are disjoint, the orientation from `S` to `T` is unique, so its
cardinality is exactly the number of crossing edges.

The final theorem is the signed replacement identity behind equation (8.2)
in the mathematical proof.  It is stated in `ℤ`, where subtraction really is
the signed change of an edge count.
-/

open SimpleGraph

namespace Erdos636

open Erdos88

universe u

section

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The unordered edges of `G` with one displayed endpoint in `S` and the
other displayed endpoint in `T`.  If the cells overlap, the two possible
orientations are deliberately identified. -/
def crossingEdges (S T : Finset V) : Finset (Sym2 V) :=
  (G.interedges S T).image fun p ↦ s(p.1, p.2)

omit [Fintype V] in
lemma mem_crossingEdges_iff {S T : Finset V} {e : Sym2 V} :
    e ∈ crossingEdges G S T ↔
      ∃ x ∈ S, ∃ y ∈ T, G.Adj x y ∧ e = s(x, y) := by
  simp only [crossingEdges, Finset.mem_image, SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨p, ⟨hpS, hpT, hpG⟩, rfl⟩
    exact ⟨p.1, hpS, p.2, hpT, hpG, rfl⟩
  · rintro ⟨x, hxS, y, hyT, hxy, rfl⟩
    exact ⟨(x, y), ⟨hxS, hyT, hxy⟩, rfl⟩

omit [Fintype V] in
/-- For disjoint vertex cells, orienting a crossing edge from the first cell
to the second is unique. -/
lemma card_crossingEdges_of_disjoint {S T : Finset V} (hST : Disjoint S T) :
    (crossingEdges G S T).card = (G.interedges S T).card := by
  rw [crossingEdges, Finset.card_image_iff.mpr]
  intro p hp q hq hpq
  rcases Sym2.mk_eq_mk_iff.mp hpq with hpq | hpq
  · exact hpq
  · exfalso
    have hp := (G.mem_interedges_iff).mp hp
    have hq := (G.mem_interedges_iff).mp hq
    apply (Finset.disjoint_left.mp hST hp.1)
    simpa [hpq] using hq.2.1

/-- The edge finset internal to a vertex finset. -/
def internalEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_internalEdges (S : Finset V) :
    (internalEdges G S).card = inducedEdges G S := by
  rw [internalEdges, inducedEdges_eq_card_filter]

lemma internalEdges_union_eq {S T : Finset V} (_hST : Disjoint S T) :
    internalEdges G (S ∪ T) =
      (internalEdges G S ∪ internalEdges G T) ∪ crossingEdges G S T := by
  ext e
  constructor
  · intro he
    have heG := (Finset.mem_filter.mp he).1
    have hsub := (Finset.mem_filter.mp he).2
    obtain ⟨x, y⟩ := e
    have hx : x ∈ S ∪ T := hsub (by simp [Sym2.toFinset_mk_eq])
    have hy : y ∈ S ∪ T := hsub (by simp [Sym2.toFinset_mk_eq])
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp heG
    rcases Finset.mem_union.mp hx with hxS | hxT <;>
      rcases Finset.mem_union.mp hy with hyS | hyT
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨heG, by
          simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using
            And.intro hxS hyS⟩))
    · exact Finset.mem_union_right _ ((mem_crossingEdges_iff (G := G)).mpr
        ⟨x, hxS, y, hyT, hxy, rfl⟩)
    · exact Finset.mem_union_right _ ((mem_crossingEdges_iff (G := G)).mpr
        ⟨y, hyS, x, hxT, (G.symm.iff x y).mp hxy, Sym2.eq_swap⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨heG, by
          simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using
            And.intro hxT hyT⟩))
  · intro he
    rcases Finset.mem_union.mp he with heInternal | heCross
    · rcases Finset.mem_union.mp heInternal with heS | heT
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heS).1,
          (Finset.mem_filter.mp heS).2.trans (Finset.subset_union_left)⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heT).1,
          (Finset.mem_filter.mp heT).2.trans (Finset.subset_union_right)⟩
    · rcases (mem_crossingEdges_iff (G := G)).mp heCross with
        ⟨a, haS, b, hbT, hab, heq⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [heq]
        exact SimpleGraph.mem_edgeFinset.mpr hab
      · rw [heq, Sym2.toFinset_mk_eq]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_union_left _ haS, Finset.mem_union_right _ hbT⟩

lemma disjoint_internalEdges_left_crossingEdges {S T : Finset V}
    (hST : Disjoint S T) :
    Disjoint (internalEdges G S) (crossingEdges G S T) := by
  rw [Finset.disjoint_left]
  intro e heS heCross
  obtain ⟨x, y⟩ := e
  have heS' := (Finset.mem_filter.mp heS).2
  have hcross := (mem_crossingEdges_iff (G := G)).mp heCross
  rcases hcross with ⟨a, haS, b, hbT, _hab, heq⟩
  have hbS : b ∈ S := by
    apply heS'
    rw [heq, Sym2.toFinset_mk_eq]
    simp
  exact (Finset.disjoint_left.mp hST hbS) hbT

lemma disjoint_internalEdges_right_crossingEdges {S T : Finset V}
    (hST : Disjoint S T) :
    Disjoint (internalEdges G T) (crossingEdges G S T) := by
  rw [Finset.disjoint_left]
  intro e heT heCross
  have heT' := (Finset.mem_filter.mp heT).2
  rcases (mem_crossingEdges_iff (G := G)).mp heCross with
    ⟨a, haS, b, hbT, _hab, heq⟩
  have haT : a ∈ T := by
    apply heT'
    rw [heq, Sym2.toFinset_mk_eq]
    simp
  exact (Finset.disjoint_left.mp hST haS) haT

lemma disjoint_internalEdges_of_disjoint {S T : Finset V}
    (hST : Disjoint S T) :
    Disjoint (internalEdges G S) (internalEdges G T) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  obtain ⟨x, y⟩ := e
  have heS' := (Finset.mem_filter.mp heS).2
  have heT' := (Finset.mem_filter.mp heT).2
  have hxS : x ∈ S := by
    apply heS'
    simp [Sym2.toFinset_mk_eq]
  have hxT : x ∈ T := by
    apply heT'
    simp [Sym2.toFinset_mk_eq]
  exact (Finset.disjoint_left.mp hST hxS) hxT

/-- Exact decomposition of the induced edge count of two disjoint cells. -/
theorem inducedEdges_union_of_disjoint {S T : Finset V} (hST : Disjoint S T) :
    inducedEdges G (S ∪ T) =
      inducedEdges G S + inducedEdges G T + (G.interedges S T).card := by
  rw [← card_internalEdges, internalEdges_union_eq G hST,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint, card_internalEdges, card_internalEdges,
      card_crossingEdges_of_disjoint G hST]
    exact disjoint_internalEdges_of_disjoint G hST
  · exact Finset.disjoint_union_left.mpr
      ⟨disjoint_internalEdges_left_crossingEdges G hST,
        disjoint_internalEdges_right_crossingEdges G hST⟩

omit [Fintype V] in
/-- Crossing edges split additively over a disjoint union in the right cell. -/
theorem card_interedges_union_right_of_disjoint
    (S : Finset V) {T U : Finset V} (hTU : Disjoint T U) :
    (G.interedges S (T ∪ U)).card =
      (G.interedges S T).card + (G.interedges S U).card := by
  have hEq : G.interedges S (T ∪ U) = G.interedges S T ∪ G.interedges S U := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    aesop
  rw [hEq, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_right S hTU

omit [Fintype V] in
/-- Crossing edges split additively over a disjoint union in the left cell. -/
theorem card_interedges_union_left_of_disjoint
    {S T : Finset V} (hST : Disjoint S T) (U : Finset V) :
    (G.interedges (S ∪ T) U).card =
      (G.interedges S U).card + (G.interedges T U).card := by
  have hEq : G.interedges (S ∪ T) U = G.interedges S U ∪ G.interedges T U := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    aesop
  rw [hEq, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_left hST U

omit [DecidableRel G.Adj] in
/-- The multiset degree of a matching cell into two disjoint vertex cells is
additive.  This uses the exact `degreeInto` convention of `Structural.lean`:
neighbours are summed with multiplicity over the vertices of `x`. -/
theorem degreeInto_union_of_disjoint
    {S T x : Finset V} (hST : Disjoint S T) :
    degreeInto G (S ∪ T) x = degreeInto G S x + degreeInto G T x := by
  simp only [degreeInto, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  have hEq : Erdos88.neighborsIn G v (S ∪ T) =
      Erdos88.neighborsIn G v S ∪ Erdos88.neighborsIn G v T := by
    ext w
    simp only [Erdos88.mem_neighborsIn, Finset.mem_union]
    aesop
  rw [hEq, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro w hwS hwT
  exact (Finset.disjoint_left.mp hST
    (Erdos88.mem_neighborsIn.mp hwS).1)
    (Erdos88.mem_neighborsIn.mp hwT).1

/-- Natural subtraction form of degree additivity. -/
theorem degreeInto_union_sub_left_of_disjoint
    {S T x : Finset V} (hST : Disjoint S T) :
    degreeInto G (S ∪ T) x - degreeInto G S x = degreeInto G T x := by
  rw [degreeInto_union_of_disjoint G hST]
  omega

/-- Deleting `D` from `U₀` subtracts exactly the degree into `D`. -/
theorem degreeInto_sdiff_of_subset
    {U₀ D x : Finset V} (hDU : D ⊆ U₀) :
    degreeInto G (U₀ \ D) x = degreeInto G U₀ x - degreeInto G D x := by
  have hdisj : Disjoint (U₀ \ D) D := Finset.sdiff_disjoint
  have hunion : (U₀ \ D) ∪ D = U₀ := Finset.sdiff_union_of_subset hDU
  have hadd := degreeInto_union_of_disjoint G hdisj (x := x)
  rw [hunion] at hadd
  omega

/-- Signed form of deletion, convenient when a switch increment is viewed in
`ℤ`. -/
theorem degreeInto_sdiff_int_of_subset
    {U₀ D x : Finset V} (hDU : D ⊆ U₀) :
    (degreeInto G (U₀ \ D) x : ℤ) =
      degreeInto G U₀ x - degreeInto G D x := by
  have hdisj : Disjoint (U₀ \ D) D := Finset.sdiff_disjoint
  have hunion : (U₀ \ D) ∪ D = U₀ := Finset.sdiff_union_of_subset hDU
  have hadd := degreeInto_union_of_disjoint G hdisj (x := x)
  rw [hunion] at hadd
  omega

/-- The incidence-sum definition of `degreeInto` is exactly the cardinality
of Mathlib's oriented crossing-edge finset. -/
theorem degreeInto_eq_card_interedges (U x : Finset V) :
    degreeInto G U x = (G.interedges x U).card := by
  induction x using Finset.induction_on with
  | empty => simp [degreeInto]
  | @insert v x hv ih =>
      have hdisj : Disjoint ({v} : Finset V) x := by simp [hv]
      have hsingle : (G.interedges {v} U).card =
          (Erdos88.neighborsIn G v U).card := by
        have hEq : G.interedges {v} U =
            ({v} : Finset V) ×ˢ Erdos88.neighborsIn G v U := by
          ext ⟨a, b⟩
          simp only [SimpleGraph.mem_interedges_iff, Finset.mem_singleton,
            Finset.mem_product, Erdos88.mem_neighborsIn]
          aesop
        rw [hEq, Finset.card_product]
        simp
      rw [degreeInto, Finset.sum_insert hv]
      rw [show insert v x = ({v} : Finset V) ∪ x by simp,
        card_interedges_union_left_of_disjoint G hdisj U,
        hsingle]
      simpa [degreeInto] using ih

/-- The structural `crossEdges` count agrees with the standard oriented
crossing-edge count. -/
theorem crossEdges_eq_card_interedges (A B : Finset V) :
    crossEdges G A B = (G.interedges A B).card := by
  exact degreeInto_eq_card_interedges G B A

/-- Exact six-term edge count for three pairwise disjoint vertex cells. -/
theorem inducedEdges_union_three
    {D W Z : Finset V}
    (hDW : Disjoint D W) (hDZ : Disjoint D Z) (hWZ : Disjoint W Z) :
    inducedEdges G ((D ∪ W) ∪ Z) =
      inducedEdges G D + inducedEdges G W + inducedEdges G Z +
        (G.interedges D W).card + (G.interedges D Z).card +
        (G.interedges W Z).card := by
  have hDWZ : Disjoint (D ∪ W) Z := Finset.disjoint_union_left.mpr ⟨hDZ, hWZ⟩
  rw [inducedEdges_union_of_disjoint G hDWZ,
    inducedEdges_union_of_disjoint G hDW,
    card_interedges_union_left_of_disjoint G hDW Z]
  omega

/-- Augmentation form of the three-cell identity: the edge count of the base
`W ∪ U` is kept together, and the contribution of `Z` is displayed as its
internal edges plus its two crossing terms. -/
theorem inducedEdges_augmentation_state
    {W U Z : Finset V}
    (hWU : Disjoint W U) (hWZ : Disjoint W Z) (hUZ : Disjoint U Z) :
    inducedEdges G ((W ∪ U) ∪ Z) =
      inducedEdges G (W ∪ U) + inducedEdges G Z +
        (G.interedges W Z).card + (G.interedges U Z).card := by
  have hWUZ : Disjoint (W ∪ U) Z := Finset.disjoint_union_left.mpr ⟨hWZ, hUZ⟩
  rw [inducedEdges_union_of_disjoint G hWUZ,
    card_interedges_union_left_of_disjoint G hWU Z]
  omega

/-- Adding a disjoint augmentation cell contributes its internal edges and
all edges from the old base into that cell. -/
theorem inducedEdges_add_disjoint_cell
    {B Z : Finset V} (hBZ : Disjoint B Z) :
    inducedEdges G (B ∪ Z) = inducedEdges G B +
      (inducedEdges G Z + (G.interedges B Z).card) := by
  rw [inducedEdges_union_of_disjoint G hBZ]
  omega

/-- Natural-number increment form of `inducedEdges_add_disjoint_cell`. -/
theorem inducedEdges_union_sub_of_disjoint
    {B Z : Finset V} (hBZ : Disjoint B Z) :
    inducedEdges G (B ∪ Z) - inducedEdges G B =
      inducedEdges G Z + (G.interedges B Z).card := by
  rw [inducedEdges_union_of_disjoint G hBZ]
  omega

omit [DecidableEq V] in
/-- A graph induced on `S` has at most `|S|²` edges.  The deliberately coarse
square bound is the convenient form for uniform matching cells. -/
theorem inducedEdges_le_card_sq (S : Finset V) :
    inducedEdges G S ≤ S.card ^ 2 := by
  rw [inducedEdges_eq_card_edgeFinset_induce]
  calc
    (G.induce (S : Set V)).edgeFinset.card ≤
        (Fintype.card (S : Set V)).choose 2 :=
      (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
    _ = S.card.choose 2 := by simp
    _ ≤ S.card ^ 2 := Nat.choose_le_pow S.card 2

/-- If `X` is one `K`-bounded matching cell and `R` is the union of at most
`nS - 1` such cells, then the internal-plus-crossing contribution of adding
`X` to `R` is at most `K² nS`. -/
theorem matchingCellIncrement_le
    {R X : Finset V} {K nS : ℕ}
    (hnS : 1 ≤ nS) (hR : R.card ≤ K * (nS - 1)) (hX : X.card ≤ K) :
    inducedEdges G X + (G.interedges R X).card ≤ K ^ 2 * nS := by
  have hedge : inducedEdges G X ≤ X.card ^ 2 := inducedEdges_le_card_sq G X
  have hcross : (G.interedges R X).card ≤ R.card * X.card :=
    G.card_interedges_le_mul R X
  calc
    inducedEdges G X + (G.interedges R X).card ≤
        X.card ^ 2 + R.card * X.card := Nat.add_le_add hedge hcross
    _ ≤ K ^ 2 + (K * (nS - 1)) * K := by gcongr
    _ = K ^ 2 * ((nS - 1) + 1) := by ring
    _ = K ^ 2 * nS := by rw [Nat.sub_add_cancel hnS]

/-- Coarse bound for the internal part of a one-cell switch.  The common
union is `R`; `X` and `Y` are respectively the incoming and outgoing cells.
This is the finite `K² nS` estimate used to absorb the last term of (8.2). -/
theorem abs_internal_switch_contribution_le
    {R X Y : Finset V} {K nS : ℕ}
    (hnS : 1 ≤ nS) (hR : R.card ≤ K * (nS - 1))
    (hX : X.card ≤ K) (hY : Y.card ≤ K)
    (hRX : Disjoint R X) (hRY : Disjoint R Y) :
    |(inducedEdges G (R ∪ X) : ℤ) - inducedEdges G (R ∪ Y)| ≤
      (K ^ 2 * nS : ℕ) := by
  let a : ℕ := inducedEdges G X + (G.interedges R X).card
  let b : ℕ := inducedEdges G Y + (G.interedges R Y).card
  let M : ℕ := K ^ 2 * nS
  have ha : a ≤ M := matchingCellIncrement_le G hnS hR hX
  have hb : b ≤ M := matchingCellIncrement_le G hnS hR hY
  have hdiff :
      (inducedEdges G (R ∪ X) : ℤ) - inducedEdges G (R ∪ Y) =
        (a : ℤ) - b := by
    rw [inducedEdges_union_of_disjoint G hRX,
      inducedEdges_union_of_disjoint G hRY]
    simp only [a, b]
    push_cast
    ring
  rw [hdiff]
  have haZ : (a : ℤ) ≤ M := by exact_mod_cast ha
  have hbZ : (b : ℤ) ≤ M := by exact_mod_cast hb
  rw [abs_le]
  constructor <;> omega

/-- Add one disjoint matching cell `X` to a state consisting of a fixed base
`B` and a previously selected union `R`. -/
theorem inducedEdges_add_matching_cell
    {B R X : Finset V}
    (hBR : Disjoint B R) (hBX : Disjoint B X) (hRX : Disjoint R X) :
    inducedEdges G (B ∪ (R ∪ X)) =
      inducedEdges G (B ∪ R) + inducedEdges G X +
        (G.interedges B X).card + (G.interedges R X).card := by
  have hBRX : Disjoint B (R ∪ X) := Finset.disjoint_union_right.mpr ⟨hBR, hBX⟩
  rw [inducedEdges_union_of_disjoint G hBRX,
    inducedEdges_union_of_disjoint G hRX,
    card_interedges_union_right_of_disjoint G B hRX,
    inducedEdges_union_of_disjoint G hBR]
  omega

/-- Signed replacement identity.  Here `R` is the common part of two
successive matching states, `X` is inserted, `Y` is removed, and `B` is the
fixed base.  This is the exact finite version of equation (8.2). -/
theorem inducedEdges_switch_difference
    {B R X Y : Finset V}
    (hBR : Disjoint B R) (hBX : Disjoint B X) (hBY : Disjoint B Y)
    (hRX : Disjoint R X) (hRY : Disjoint R Y) :
    (inducedEdges G (B ∪ (R ∪ X)) : ℤ) -
        inducedEdges G (B ∪ (R ∪ Y)) =
      ((G.interedges B X).card : ℤ) - (G.interedges B Y).card +
        ((inducedEdges G (R ∪ X) : ℤ) - inducedEdges G (R ∪ Y)) := by
  have hBRX : Disjoint B (R ∪ X) := Finset.disjoint_union_right.mpr ⟨hBR, hBX⟩
  have hBRY : Disjoint B (R ∪ Y) := Finset.disjoint_union_right.mpr ⟨hBR, hBY⟩
  rw [inducedEdges_union_of_disjoint G hBRX,
    inducedEdges_union_of_disjoint G hBRY,
    card_interedges_union_right_of_disjoint G B hRX,
    card_interedges_union_right_of_disjoint G B hRY]
  push_cast
  ring

end

section MatchingUnion

variable {α : Type*} [DecidableEq α]

/-- The union of `m` pairwise-disjoint `k`-sets has exactly `m*k` vertices.
This is the cardinality identity used for unions of matching hyperedges. -/
theorem card_matching_biUnion_eq_mul
    {M : Finset (Finset α)} {k : ℕ}
    (hdisj : (M : Set (Finset α)).PairwiseDisjoint id)
    (huniform : ∀ x ∈ M, x.card = k) :
    (M.biUnion id).card = M.card * k := by
  rw [Finset.card_biUnion hdisj]
  exact Finset.sum_const_nat huniform

end MatchingUnion

end Erdos636
