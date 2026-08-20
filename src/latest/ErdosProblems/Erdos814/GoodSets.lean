import ErdosProblems.Erdos814.Basic
import ErdosProblems.Erdos814.Arithmetic
import ErdosProblems.Erdos814.Threshold
import ErdosProblems.Erdos814.Connectivity
import ErdosProblems.Erdos814.Pruning
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

/-!
# Good sets in Sauermann's proof of Erdős Problem 814

This file formalizes Definition 2.3 and the elementary consequences used by
the dyadic-block and coloring arguments.  The ambient vertex set remains
fixed throughout.  In particular, `incidentCount G A D` is Sauermann's
`\bar e_G(D)` inside `G[A]`.
-/

open Finset SimpleGraph BigOperators

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The local deletion inequality furnished by the outer minimal-counterexample
induction (Sauermann's Claim 2.1). -/
def LocalExpansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Prop :=
  ∀ X, X.Nonempty → X ⊆ A → X.card ≤ A.card - k + 1 →
    (k - 1) * X.card + 1 ≤ incidentCount G A X

/-- Sauermann's good sets (Definition 2.3), relative to the fixed ambient set
`A`. -/
inductive Good (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V → Prop
  | singleton {v : V} (hv : v ∈ A) (hdeg : degreeOn G A v = k) :
      Good G A k {v}
  | insert {D : Finset V} {v : V} (hD : Good G A k D)
      (hv : v ∈ A \ D) (hdeg : degreeOn G (A \ D) v ≤ k - 1) :
      Good G A k (insert v D)
  | union_inter {D E : Finset V} (hD : Good G A k D)
      (hE : Good G A k E) (hne : (D ∩ E).Nonempty) :
      Good G A k (D ∪ E)
  | union_adj {D E : Finset V} (hD : Good G A k D)
      (hE : Good G A k E) (hadj : AdjacentSets G D E) :
      Good G A k (D ∪ E)

namespace Good

lemma subset {A D : Finset V} {k : ℕ} (hD : Good G A k D) : D ⊆ A := by
  induction hD with
  | singleton hv _ => simpa using hv
  | insert hD hv _ ih =>
      exact insert_subset (mem_sdiff.mp hv).1 ih
  | union_inter _ _ _ ihD ihE => exact union_subset ihD ihE
  | union_adj _ _ _ ihD ihE => exact union_subset ihD ihE

lemma nonempty {A D : Finset V} {k : ℕ} (hD : Good G A k D) : D.Nonempty := by
  induction hD with
  | singleton => simp
  | insert => simp
  | union_inter _ _ _ ihD _ => exact ihD.mono subset_union_left
  | union_adj _ _ _ ihD _ => exact ihD.mono subset_union_left

end Good

/-! ## Incidence identities -/

/-- Exact incidence increment when a new vertex is added to a deletion set. -/
lemma incidentCount_insert {A D : Finset V} {v : V}
    (hv : v ∈ A \ D) :
    incidentCount G A (insert v D) =
      incidentCount G A D + degreeOn G (A \ D) v := by
  have h₁ := edgeCount_sdiff_add_incidentCount G A D
  have h₂ := edgeCount_sdiff_add_incidentCount G (A \ D) {v}
  have h₃ := edgeCount_sdiff_add_incidentCount G A (insert v D)
  have hsingle := incidentCount_singleton G (A \ D) hv
  have hs : (A \ D) \ {v} = A \ insert v D := by
    ext x
    simp only [mem_sdiff, mem_singleton, mem_insert]
    tauto
  rw [hs, hsingle] at h₂
  omega

/-- Incidence is submodular as a function of the deleted vertex set. -/
lemma incidentCount_union_add_inter_le (A D E : Finset V) :
    incidentCount G A (D ∪ E) + incidentCount G A (D ∩ E) ≤
      incidentCount G A D + incidentCount G A E := by
  have hsub : incidentEdges G A (D ∩ E) ⊆
      incidentEdges G A D ∩ incidentEdges G A E := by
    intro e he
    exact mem_inter.mpr
      ⟨incidentEdges_mono G A inter_subset_left he,
       incidentEdges_mono G A inter_subset_right he⟩
  have hcard : incidentCount G A (D ∩ E) ≤
      #(incidentEdges G A D ∩ incidentEdges G A E) := by
    exact card_le_card hsub
  calc
    incidentCount G A (D ∪ E) + incidentCount G A (D ∩ E) ≤
        incidentCount G A (D ∪ E) +
          #(incidentEdges G A D ∩ incidentEdges G A E) :=
      Nat.add_le_add_left hcard _
    _ = incidentCount G A D + incidentCount G A E :=
      incidentCount_union_add_inter G A D E

private lemma card_inter_le_card_union {D E : Finset V} :
    (D ∩ E).card ≤ (D ∪ E).card :=
  card_le_card (inter_subset_left.trans subset_union_left)

/-- Lemma 2.4: a good set in the range where local expansion is available
has incident-edge count at most `(k-1)|D|+1`. -/
lemma Good.incidentCount_le_of_card_le
    {A D : Finset V} {k : ℕ} (hlocal : LocalExpansion G A k)
    (hD : Good G A k D) (hcard : D.card ≤ A.card - k + 1) :
    incidentCount G A D ≤ (k - 1) * D.card + 1 := by
  induction hD with
  | singleton hv hdeg =>
      rw [incidentCount_singleton G A hv, hdeg]
      simp only [card_singleton, mul_one]
      omega
  | @insert D v hD hv hdeg ih =>
      have hDcard : D.card ≤ A.card - k + 1 :=
        (card_le_card (subset_insert v D)).trans hcard
      have hi := ih hDcard
      rw [incidentCount_insert G hv]
      have hvD : v ∉ D := (mem_sdiff.mp hv).2
      rw [card_insert_of_notMem hvD]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
  | @union_inter D E hD hE hne ihD ihE =>
      have hDcard : D.card ≤ A.card - k + 1 :=
        (card_le_card subset_union_left).trans hcard
      have hEcard : E.card ≤ A.card - k + 1 :=
        (card_le_card subset_union_right).trans hcard
      have hIcard : (D ∩ E).card ≤ A.card - k + 1 :=
        card_inter_le_card_union.trans hcard
      have hIlower := hlocal (D ∩ E) hne
        ((inter_subset_left.trans hD.subset)) hIcard
      have hsub := incidentCount_union_add_inter_le G A D E
      have hc := card_union_add_card_inter D E
      nlinarith [ihD hDcard, ihE hEcard]
  | @union_adj D E hD hE hadj ihD ihE =>
      by_cases hne : (D ∩ E).Nonempty
      · have hDcard : D.card ≤ A.card - k + 1 :=
          (card_le_card subset_union_left).trans hcard
        have hEcard : E.card ≤ A.card - k + 1 :=
          (card_le_card subset_union_right).trans hcard
        have hIcard : (D ∩ E).card ≤ A.card - k + 1 :=
          card_inter_le_card_union.trans hcard
        have hIlower := hlocal (D ∩ E) hne
          ((inter_subset_left.trans hD.subset)) hIcard
        have hsub := incidentCount_union_add_inter_le G A D E
        have hc := card_union_add_card_inter D E
        nlinarith [ihD hDcard, ihE hEcard]
      · have hdisj : Disjoint D E := Finset.disjoint_left.mpr (by
          intro x hxD hxE
          exact hne ⟨x, mem_inter.mpr ⟨hxD, hxE⟩⟩)
        have hDcard : D.card ≤ A.card - k + 1 := by
          exact (card_le_card subset_union_left).trans hcard
        have hEcard : E.card ≤ A.card - k + 1 := by
          exact (card_le_card subset_union_right).trans hcard
        have hadjCount := incidentCount_union_add_one_le_of_adjacent G
          hD.subset hE.subset hadj
        rw [card_union_of_disjoint hdisj]
        nlinarith [ihD hDcard, ihE hEcard]

/-! ## The complement core and the size of a good set -/

/-- Every nonsingleton good set contains a proper good subset having at
least half its cardinality.  This formulation avoids choosing a derivation
of minimum height: if a union rule was redundant, we recursively descend
through the parent which already equals the union. -/
lemma Good.exists_proper_subgood_of_one_lt
    {A D : Finset V} {k : ℕ} (hD : Good G A k D) (hone : 1 < D.card) :
    ∃ E, Good G A k E ∧ E ⊂ D ∧ D.card ≤ 2 * E.card := by
  induction hD with
  | singleton hv hdeg => simp at hone
  | @insert D v hD hv hdeg ih =>
      have hvD : v ∉ D := (mem_sdiff.mp hv).2
      refine ⟨D, hD, ?_, ?_⟩
      · exact ssubset_insert hvD
      · rw [card_insert_of_notMem hvD]
        have hne := (Good.nonempty G hD).card_pos
        omega
  | @union_inter D E hD hE hne ihD ihE =>
      by_cases hDall : D = D ∪ E
      · rw [← hDall] at hone ⊢
        exact ihD hone
      · by_cases hEall : E = D ∪ E
        · rw [← hEall] at hone ⊢
          exact ihE hone
        · have hDss : D ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, hDall⟩
          have hEss : E ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, hEall⟩
          have hcard := card_union_le D E
          by_cases hle : E.card ≤ D.card
          · exact ⟨D, hD, hDss, by omega⟩
          · exact ⟨E, hE, hEss, by omega⟩
  | @union_adj D E hD hE hadj ihD ihE =>
      by_cases hDall : D = D ∪ E
      · rw [← hDall] at hone ⊢
        exact ihD hone
      · by_cases hEall : E = D ∪ E
        · rw [← hEall] at hone ⊢
          exact ihE hone
        · have hDss : D ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, hDall⟩
          have hEss : E ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, hEall⟩
          have hcard := card_union_le D E
          by_cases hle : E.card ≤ D.card
          · exact ⟨D, hD, hDss, by omega⟩
          · exact ⟨E, hE, hEss, by omega⟩

/-- Claim 2.5 in the exact Problem 814 normalization: deleting a good set
in the range of the local-expansion inequality leaves a nonempty induced
subgraph of minimum degree at least `k`. -/
theorem Good.exists_core_in_complement
    {A D : Finset V} {k : ℕ} (hk : 2 ≤ k)
    (hcardA : k - 1 ≤ A.card)
    (hlocal : LocalExpansion G A k)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A)
    (hD : Good G A k D) (hcard : D.card ≤ A.card - k + 1) :
    ∃ U ⊆ A \ D, HasMinDegreeOn G U k := by
  have hDA := Good.subset G hD
  have hinc := Good.incidentCount_le_of_card_le G hlocal hD hcard
  have hsplit := edgeCount_sdiff_add_incidentCount G A D
  have hremcard : (A \ D).card = A.card - D.card :=
    card_sdiff_of_subset hDA
  have hAfeasible :=
    card_ge_succ_of_edgeThreshold_le G k hk hcardA hedge
  have hremLower : k - 1 ≤ (A \ D).card := by
    rw [hremcard]
    have hDpos := (Good.nonempty G hD).card_pos
    omega
  apply exists_core_of_efrsThreshold_le G k hk hremLower
  rw [hremcard]
  simp only [edgeThreshold] at hedge
  have harg :
      A.card + 2 - k = (A.card - D.card + 2 - k) + D.card := by
    have hDpos := (Good.nonempty G hD).card_pos
    omega
  have hdecomp :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 + 1 =
        ((k - 1) * (A.card - D.card + 2 - k) + (k - 2).choose 2) +
          ((k - 1) * D.card + 1) := by
    rw [harg, Nat.mul_add]
    omega
  rw [hdecomp] at hedge
  have hinc' :
      ((k - 1) * (A.card - D.card + 2 - k) + (k - 2).choose 2) +
          incidentCount G A D ≤ edgeCount G A :=
    (Nat.add_le_add_left hinc _).trans hedge
  rw [← hsplit] at hinc'
  omega

/-- If no core of relative size `1 - 1 / q` exists and `q ≥ 2k`, every
good set occupies at most a `1/k` fraction of the ambient vertices.

The proof selects an inclusion-minimal oversized good set.  Its structural
predecessor is at least half as large and is no longer oversized; Claim 2.5
then produces a forbidden core in its complement. -/
theorem Good.card_mul_le_of_noSmallCoreOn
    {A D : Finset V} {k q : ℕ} (hk : 2 ≤ k) (hq : 2 * k ≤ q)
    (hcardA : k - 1 ≤ A.card)
    (hlocal : LocalExpansion G A k)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A)
    (hnosmall : NoSmallCoreOn G A k q)
    (hD : Good G A k D) :
    k * D.card ≤ A.card := by
  classical
  by_contra hbad
  have hbad' : A.card < k * D.card := by omega
  let candidates : Finset (Finset V) :=
    A.powerset.filter fun E ↦ Good G A k E ∧ A.card < k * E.card
  have hDmem : D ∈ candidates := by
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨Good.subset G hD, hD, hbad'⟩
  obtain ⟨M, hMmax⟩ := candidates.exists_minimal ⟨D, hDmem⟩
  have hMmem := hMmax.1
  have hMdata : Good G A k M ∧ A.card < k * M.card := by
    exact (mem_filter.mp hMmem).2
  have hMone : 1 < M.card := by
    have hAfeasible := card_ge_succ_of_edgeThreshold_le G k hk hcardA hedge
    have hMne := Good.nonempty G hMdata.1
    by_contra h
    have : M.card = 1 := by
      have := hMne.card_pos
      omega
    rw [this] at hMdata
    omega
  obtain ⟨E, hEgood, hEss, hhalf⟩ :=
    Good.exists_proper_subgood_of_one_lt G hMdata.1 hMone
  have hEnotmem : E ∉ candidates := by
    intro hEmem
    exact hEss.ne (Subset.antisymm hEss.subset (hMmax.2 hEmem hEss.subset))
  have hEnotbad : ¬ A.card < k * E.card := by
    intro hEbad
    apply hEnotmem
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨Good.subset G hEgood, hEgood, hEbad⟩
  have hEsmall : k * E.card ≤ A.card := by omega
  have hEcard : E.card ≤ A.card - k + 1 := by
    have hEpos := (Good.nonempty G hEgood).card_pos
    have hEk : E.card + k ≤ A.card + 1 := by
      nlinarith
    omega
  obtain ⟨U, hUcomp, hUcore⟩ :=
    Good.exists_core_in_complement G hk hcardA hlocal hedge hEgood hEcard
  have hUA : U ⊆ A := hUcomp.trans sdiff_subset
  have hsum : U.card + E.card ≤ A.card := by
    have hUcard := card_le_card hUcomp
    rw [card_sdiff_of_subset (Good.subset G hEgood)] at hUcard
    omega
  have hAM : A.card < 2 * k * E.card := by nlinarith
  have hAEq : A.card ≤ q * E.card := by nlinarith
  have hmul := Nat.mul_le_mul_left q hsum
  have hkey : q * U.card + A.card ≤ q * A.card := by nlinarith
  have hqpos : 1 ≤ q := by omega
  have hqsplit : q = (q - 1) + 1 := by omega
  have hsmall : q * U.card ≤ (q - 1) * A.card := by
    exact (Nat.add_le_add_iff_right).mp <| by
      calc
        q * U.card + A.card ≤ q * A.card := hkey
        _ = (q - 1) * A.card + A.card := by
          calc
            q * A.card = ((q - 1) + 1) * A.card :=
              congrArg (fun r : ℕ ↦ r * A.card) hqsplit
            _ = (q - 1) * A.card + A.card := by
              rw [add_mul, one_mul]
  exact hnosmall ⟨U, hUA, hUcore, hsmall⟩

/-! ## Maximal good sets -/

/-- Inclusion-maximality among good subsets of the fixed ambient set. -/
def MaximalGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (D : Finset V) : Prop :=
  Good G A k D ∧ ∀ E, Good G A k E → D ⊆ E → E ⊆ D

/-- The finite family of all maximal good sets. -/
noncomputable def maxGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact A.powerset.filter (MaximalGood G A k)

@[simp] lemma mem_maxGood {A D : Finset V} {k : ℕ} :
    D ∈ maxGood G A k ↔ MaximalGood G A k D := by
  classical
  rw [maxGood]
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G h.1), h⟩

/-- Every good set is contained in a maximal good set. -/
lemma Good.exists_maximalGood_superset
    {A D : Finset V} {k : ℕ} (hD : Good G A k D) :
    ∃ M ∈ maxGood G A k, D ⊆ M := by
  classical
  let goods : Finset (Finset V) := A.powerset.filter (Good G A k)
  have hDmem : D ∈ goods := by
    exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G hD), hD⟩
  obtain ⟨M, hDM, hMmax⟩ := goods.exists_le_maximal hDmem
  refine ⟨M, (mem_maxGood (G := G)).mpr ⟨?_, ?_⟩, hDM⟩
  · exact (mem_filter.mp hMmax.1).2
  · intro E hE hME
    apply hMmax.2
    · exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G hE), hE⟩
    · exact hME

/-- Distinct maximal good sets are disjoint. -/
theorem maxGood_pairwiseDisjoint {A : Finset V} {k : ℕ} :
    ((maxGood G A k : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  intro D hD E hE hDE
  have hD' : MaximalGood G A k D := (mem_maxGood (G := G)).mp (by simpa using hD)
  have hE' : MaximalGood G A k E := (mem_maxGood (G := G)).mp (by simpa using hE)
  apply Finset.disjoint_left.mpr
  intro v hvD hvE
  have hne : (D ∩ E).Nonempty := ⟨v, mem_inter.mpr ⟨hvD, hvE⟩⟩
  have hU : Good G A k (D ∪ E) := Good.union_inter hD'.1 hE'.1 hne
  have hUD := hD'.2 (D ∪ E) hU subset_union_left
  have hEU : E ⊆ D := subset_union_right.trans hUD
  have hDU := hE'.2 (D ∪ E) hU subset_union_right
  have hDE' : D ⊆ E := subset_union_left.trans hDU
  exact hDE (Subset.antisymm hDE' hEU)

/-- Distinct maximal good sets have no edge between them. -/
theorem maxGood_pairwise_not_adjacent {A : Finset V} {k : ℕ}
    {D E : Finset V} (hD : D ∈ maxGood G A k)
    (hE : E ∈ maxGood G A k) (hDE : D ≠ E) :
    ¬ AdjacentSets G D E := by
  have hD' := (mem_maxGood (G := G)).mp hD
  have hE' := (mem_maxGood (G := G)).mp hE
  intro hadj
  have hU : Good G A k (D ∪ E) := Good.union_adj hD'.1 hE'.1 hadj
  have hUD := hD'.2 (D ∪ E) hU subset_union_left
  have hEU : E ⊆ D := subset_union_right.trans hUD
  have hDU := hE'.2 (D ∪ E) hU subset_union_right
  have hDE' : D ⊆ E := subset_union_left.trans hDU
  exact hDE (Subset.antisymm hDE' hEU)

/-- Every degree-`k` vertex belongs to a maximal good set. -/
theorem degreeEq_subset_biUnion_maxGood {A : Finset V} {k : ℕ} :
    degreeEq G A k ⊆ (maxGood G A k).biUnion id := by
  intro v hv
  have hvdata := mem_degreeEq.mp hv
  have hsingle : Good G A k {v} := Good.singleton hvdata.1 hvdata.2
  obtain ⟨M, hM, hvM⟩ := hsingle.exists_maximalGood_superset
  exact mem_biUnion.mpr ⟨M, hM, hvM (mem_singleton_self v)⟩

/-- The complement of a maximal good set has minimum degree at least `k`
whenever it is nonempty. -/
theorem maximalGood_complement_hasMinDegreeOn
    {A D : Finset V} {k : ℕ} (hD : MaximalGood G A k D)
    (hne : (A \ D).Nonempty) : HasMinDegreeOn G (A \ D) k := by
  refine ⟨hne, ?_⟩
  intro v hv
  by_contra hdeg
  have hle : degreeOn G (A \ D) v ≤ k - 1 := by omega
  have hins : Good G A k (insert v D) := Good.insert hD.1 hv hle
  have hback := hD.2 (insert v D) hins (subset_insert v D)
  exact (mem_sdiff.mp hv).2 (hback (mem_insert_self v D))

/-- The degree-`k` supply is no larger than the total maximal-good-set mass. -/
theorem card_degreeEq_le_maxGood_mass {A : Finset V} {k : ℕ} :
    (degreeEq G A k).card ≤ ∑ D ∈ maxGood G A k, D.card := by
  calc
    (degreeEq G A k).card ≤ #((maxGood G A k).biUnion id) :=
      card_le_card (degreeEq_subset_biUnion_maxGood (G := G))
    _ = ∑ D ∈ maxGood G A k, D.card :=
      card_biUnion (maxGood_pairwiseDisjoint (G := G))

end Erdos814
