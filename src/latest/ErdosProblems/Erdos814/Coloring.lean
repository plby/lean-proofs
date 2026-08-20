import ErdosProblems.Erdos814.GoodSets
import ErdosProblems.Erdos814.Dyadic
import ErdosProblems.Erdos814.Extension
import ErdosProblems.Erdos814.GreedyColoring
import Mathlib

/-!
# The colouring argument for Erdős Problem 814

This file formalizes Sauermann's appropriate-colouring induction (Lemma 2.11)
and its final pigeonhole argument.  Dyadic levels are numbered from zero, as in
`Dyadic.lean`; consequently the first `ell` levels occupy the list positions
strictly below `Dyadic.levelStart ell`.
-/

open Finset SimpleGraph BigOperators

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The maximal good sets, sorted by nonincreasing cardinality. -/
noncomputable def orderedMaxGood
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : List (Finset V) :=
  (maxGood G A k).toList.mergeSort fun D E ↦ decide (E.card ≤ D.card)

@[simp] lemma length_orderedMaxGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) :
    (orderedMaxGood G A k).length = (maxGood G A k).card := by
  simp [orderedMaxGood, List.length_mergeSort]

lemma mem_orderedMaxGood_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (D : Finset V) :
    D ∈ orderedMaxGood G A k ↔ D ∈ maxGood G A k := by
  simpa [orderedMaxGood] using
    (List.Perm.mem_iff (List.mergeSort_perm (maxGood G A k).toList
      (fun D E ↦ decide (E.card ≤ D.card))))

lemma orderedMaxGood_nodup (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : (orderedMaxGood G A k).Nodup := by
  unfold orderedMaxGood
  exact (List.Perm.nodup_iff (List.mergeSort_perm (maxGood G A k).toList
    (fun D E ↦ decide (E.card ≤ D.card)))).2 (Finset.nodup_toList _)

lemma orderedMaxGood_nonincreasing (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) :
    Dyadic.Nonincreasing (orderedMaxGood G A k) := by
  intro i j hij hj
  by_cases hEq : i = j
  · subst j
    exact le_rfl
  have hlt : i < j := lt_of_le_of_ne hij hEq
  have hp : List.Pairwise (fun D E : Finset V ↦ E.card ≤ D.card)
      (orderedMaxGood G A k) := by
    exact List.pairwise_mergeSort' _ _
  have hi : i < (orderedMaxGood G A k).length := hlt.trans hj
  have hrel := hp.rel_get_of_lt
    (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hlt)
  rw [Dyadic.cardAt, Dyadic.cardAt,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact hrel

/-- The dyadic block system used by the colouring induction.  Its fields are
exactly the graph-theoretic and numerical conclusions of Claims 2.5--2.9. -/
structure ColoringSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℤ)
    (C : List (Finset V)) (J0 J : ℕ) : Prop where
  hk : 2 ≤ k
  hJ0 : 0 < J0
  hJ : J0 ≤ J
  complete : Dyadic.CompleteThrough C J
  nonincreasing : Dyadic.Nonincreasing C
  nodup : C.Nodup
  block_nonempty : ∀ r < Dyadic.levelStart J, (C.getD r ∅).Nonempty
  block_subset : ∀ r < Dyadic.levelStart J, C.getD r ∅ ⊆ A
  block_incident : ∀ r < Dyadic.levelStart J,
    incidentCount G A (C.getD r ∅) ≤ (k - 1) * (C.getD r ∅).card + 1
  block_complement_minDegree : ∀ r < Dyadic.levelStart J,
    HasMinDegreeOn G (A \ C.getD r ∅) k
  blocks_disjoint : ∀ r < Dyadic.levelStart J, ∀ s < Dyadic.levelStart J,
    r ≠ s → Disjoint (C.getD r ∅) (C.getD s ∅)
  blocks_anticomplete : ∀ r < Dyadic.levelStart J, ∀ s < Dyadic.levelStart J,
    r ≠ s → Anticomplete G (C.getD r ∅) (C.getD s ∅)
  minDegree : HasMinDegreeOn G A k
  connected : ConnectedOn G A
  noSmallCore : NoSmallCoreOn G A k (uniformDen k)
  shortage_le : shortage k G A ≤ t
  power : t < (2 ^ J0 : ℕ)
  early_mass : A.card ≤ 100 * k * Dyadic.retainedMass C J0
  cutoff_level : 50 * k * Dyadic.levelMass C (J0 - 1) < A.card
  late_mass : A.card < 8 * k * Dyadic.betweenMass C J0 J

namespace ColoringSystem

variable {A : Finset V} {k : ℕ} {t : ℤ}
variable {C : List (Finset V)} {J0 J : ℕ}

lemma block_index_lt_length (S : ColoringSystem G A k t C J0 J)
    {r : ℕ} (hr : r < Dyadic.levelStart J) : r < C.length :=
  hr.trans_le S.complete

lemma block_eq_getElem (S : ColoringSystem G A k t C J0 J)
    {r : ℕ} (hr : r < Dyadic.levelStart J) :
    C.getD r ∅ = C[r]'(S.block_index_lt_length hr) := by
  exact List.getD_eq_getElem _ _ (S.block_index_lt_length hr)

lemma blocks_disjoint_set (S : ColoringSystem G A k t C J0 J) :
    (↑(Finset.range (Dyadic.levelStart J)) : Set ℕ).PairwiseDisjoint
      (fun r ↦ C.getD r ∅) := by
  intro r hr s hs hrs
  exact S.blocks_disjoint r (mem_range.mp hr) s (mem_range.mp hs) hrs

end ColoringSystem

/-- The palette of `401 k` colours used in Sauermann's proof. -/
abbrev Color (k : ℕ) := Fin (401 * k)

/-- A partial colouring.  `none` means uncoloured. -/
abbrev PartialColoring (V : Type*) (k : ℕ) := V → Option (Color k)

/-- The vertices of `A` carrying colour `i`. -/
def colorClass (A : Finset V) (phi : PartialColoring V k) (i : Color k) : Finset V :=
  A.filter fun v ↦ phi v = some i

/-- Every vertex of a block is uncoloured. -/
def BlockUncolored (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∀ v ∈ D, phi v = none

/-- Every vertex of a block has the indicated colour. -/
def Monochromatic (phi : PartialColoring V k) (D : Finset V) (i : Color k) : Prop :=
  ∀ v ∈ D, phi v = some i

/-- A block is monochromatic in some colour. -/
def IsMonochromatic (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∃ i, Monochromatic phi D i

/-- Number of uncoloured blocks in zero-based level `j`. -/
noncomputable def uncoloredBlockCount (C : List (Finset V))
    (phi : PartialColoring V k) (j : ℕ) : ℕ := by
  classical
  exact ((Dyadic.levelIndices j).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)).card

/-- Number of monochromatic blocks of colour `i` among the first `ell`
complete dyadic levels. -/
noncomputable def monochromaticBlockCount (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) (i : Color k) : ℕ := by
  classical
  exact ((Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    Monochromatic phi (C.getD r ∅) i).card

/-- All neighbours in `A` of the block `D` are uncoloured. -/
def UncoloredNeighborhood (G : SimpleGraph V) (A : Finset V)
    (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∀ v ∈ D, ∀ w ∈ A, G.Adj v w → phi w = none

/-- Sauermann's seven invariants.  Partial functions make uniqueness of a
colour automatic; the first field says that no vertex outside the ambient
graph is coloured. -/
structure Appropriate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi : PartialColoring V k) : Prop where
  /-- (i) The colouring is supported on the ambient vertex set. -/
  support : ∀ v, v ∉ A → phi v = none
  /-- (ii) Every retained block is monochromatic or completely uncoloured. -/
  blocks : ∀ r < Dyadic.levelStart J,
    IsMonochromatic phi (C.getD r ∅) ∨ BlockUncolored phi (C.getD r ∅)
  /-- (iii) The incidence budget of every colour class. -/
  incidence : ∀ i,
    incidentCount G A (colorClass A phi i) ≤
      (k - 1) * (colorClass A phi i).card + monochromaticBlockCount C phi ell i
  /-- (iv) Deleting any one colour class leaves a nonempty `k`-core. -/
  minDegree : ∀ i, HasMinDegreeOn G (A \ colorClass A phi i) k
  /-- (v) Blocks in the first `J0` levels remain uncoloured. -/
  early : ∀ r < Dyadic.levelStart J0, BlockUncolored phi (C.getD r ∅)
  /-- (vi) In every processed late level, at most one quarter of the blocks
  remain uncoloured. -/
  processed : ∀ j, J0 ≤ j → j < ell → 4 * uncoloredBlockCount C phi j ≤ 2 ^ j
  /-- (vii) An uncoloured block in a future level has only uncoloured
  neighbours. -/
  future : ∀ r, Dyadic.levelStart ell ≤ r → r < Dyadic.levelStart J →
    BlockUncolored phi (C.getD r ∅) →
      UncoloredNeighborhood G A phi (C.getD r ∅)

@[simp] lemma colorClass_uncolored (A : Finset V) (i : Color k) :
    colorClass A (fun _ ↦ none) i = ∅ := by
  ext v
  simp [colorClass]

@[simp] lemma blockUncolored_uncolored (D : Finset V) :
    BlockUncolored (k := k) (fun _ ↦ none) D := by
  simp [BlockUncolored]

/-- The all-uncoloured colouring is the base of the induction. -/
lemma appropriate_uncolored
    {A : Finset V} {k J0 J : ℕ} {C : List (Finset V)}
    (hmin : HasMinDegreeOn G A k) :
    Appropriate G A k C J0 J0 J (fun _ ↦ none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro r hr
    exact Or.inr (blockUncolored_uncolored _)
  · intro i
    rw [colorClass_uncolored]
    simpa [incidentCount, incidentEdges, edgeOn] using
      (Nat.zero_le (monochromaticBlockCount C (fun _ ↦ none) J0 i))
  · intro i
    simpa using hmin
  · intro r hr
    exact blockUncolored_uncolored _
  · intro j hj hlt
    omega
  · intro r hr hR hu
    simp [UncoloredNeighborhood]

lemma monochromaticBlockCount_mono_ell
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) (i : Color k) :
    monochromaticBlockCount C phi ell i ≤
      monochromaticBlockCount C phi (ell + 1) i := by
  classical
  unfold monochromaticBlockCount
  apply card_le_card
  intro r hr
  rw [mem_filter] at hr ⊢
  exact ⟨mem_range.mpr ((mem_range.mp hr.1).trans_le (Dyadic.levelStart_le_succ ell)), hr.2⟩

/-- If the next level already has at most one quarter uncoloured blocks,
the old colouring is also appropriate one level later. -/
lemma Appropriate.advance_without_change
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hquarter : 4 * uncoloredBlockCount C phi ell ≤ 2 ^ ell) :
    Appropriate G A k C J0 (ell + 1) J phi := by
  refine ⟨hphi.support, hphi.blocks, ?_, hphi.minDegree, hphi.early, ?_, ?_⟩
  · intro i
    exact hphi.incidence i |>.trans <|
      Nat.add_le_add_left (monochromaticBlockCount_mono_ell C phi ell i) _
  · intro j hj hje
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hje) with hjell | rfl
    · exact hphi.processed j hj hjell
    · exact hquarter
  · intro r hr hJ hu
    exact hphi.future r (Dyadic.levelStart_le_succ ell |>.trans hr) hJ hu

/-- Exact telescoping of incidence counts under two successive deletions. -/
lemma incidentCount_union_eq_add_restricted
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) =
      incidentCount G A X + incidentCount G (A \ X) Y := by
  have hAll := edgeCount_sdiff_add_incidentCount G A (X ∪ Y)
  have hX := edgeCount_sdiff_add_incidentCount G A X
  have hY := edgeCount_sdiff_add_incidentCount G (A \ X) Y
  have hs : A \ (X ∪ Y) = (A \ X) \ Y := by
    ext v
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hs] at hAll
  omega

/-- An extension never turns an already-coloured vertex into another colour
or back into an uncoloured vertex. -/
def Extends (phi rho : PartialColoring V k) : Prop :=
  ∀ v i, phi v = some i → rho v = some i

lemma Extends.blockUncolored {phi rho : PartialColoring V k}
    (h : Extends phi rho) {D : Finset V}
    (hD : BlockUncolored rho D) : BlockUncolored phi D := by
  intro v hv
  cases hphi : phi v with
  | none => rfl
  | some i =>
      have hrho := h v i hphi
      rw [hD v hv] at hrho
      contradiction

lemma Extends.uncoloredBlockCount_le {phi rho : PartialColoring V k}
    (h : Extends phi rho) (C : List (Finset V)) (j : ℕ) :
    uncoloredBlockCount C rho j ≤ uncoloredBlockCount C phi j := by
  classical
  unfold uncoloredBlockCount
  apply card_le_card
  intro r hr
  simp only [mem_filter] at hr ⊢
  exact ⟨hr.1, h.blockUncolored hr.2⟩

/-- A set of vertices is coloured when it carries some palette colour. -/
def coloredVertices (A : Finset V) (phi : PartialColoring V k) : Finset V :=
  A.filter fun v ↦ (phi v).isSome

lemma mem_coloredVertices_iff {A : Finset V} {phi : PartialColoring V k} {v : V} :
    v ∈ coloredVertices A phi ↔ v ∈ A ∧ ∃ i, phi v = some i := by
  simp [coloredVertices, Option.isSome_iff_exists]

lemma colorClass_subset_coloredVertices
    (A : Finset V) (phi : PartialColoring V k) (i : Color k) :
    colorClass A phi i ⊆ coloredVertices A phi := by
  intro v hv
  have hv' : v ∈ A ∧ phi v = some i := by simpa [colorClass] using hv
  exact mem_coloredVertices_iff.mpr ⟨hv'.1, i, hv'.2⟩

lemma coloredVertices_eq_biUnion_colorClass
    (A : Finset V) (phi : PartialColoring V k) :
    coloredVertices A phi = Finset.univ.biUnion (colorClass A phi) := by
  ext v
  rw [mem_coloredVertices_iff]
  simp [colorClass]

lemma pairwise_disjoint_colorClass
    (A : Finset V) (phi : PartialColoring V k) :
    (↑(Finset.univ : Finset (Color k)) : Set (Color k)).PairwiseDisjoint
      (colorClass A phi) := by
  intro i hi j hj hij
  change Disjoint (colorClass A phi i) (colorClass A phi j)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  simp only [colorClass, mem_filter] at hvi hvj
  exact hij (Option.some.inj (hvi.2.symm.trans hvj.2))

/-- Uncoloured block indices among the first `ell` complete levels. -/
noncomputable def uncoloredPrefixIndices (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

/-- Union of the uncoloured blocks among the first `ell` levels. -/
noncomputable def uncoloredPrefixUnion (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset V := by
  classical
  exact (uncoloredPrefixIndices C phi ell).biUnion fun r ↦ C.getD r ∅

/-- The deficit graph (5.13), expressed as its ambient vertex set. -/
noncomputable def deficitResidual (A : Finset V) (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset V :=
  A \ (coloredVertices A phi ∪ uncoloredPrefixUnion C phi ell)

/-- Uncoloured indices in the single current level. -/
noncomputable def uncoloredCurrentIndices (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

lemma incidentCount_biUnion_le_sum
    {ι : Type*} [DecidableEq ι]
    (A : Finset V) (s : Finset ι) (D : ι → Finset V) :
    incidentCount G A (s.biUnion D) ≤
      ∑ i ∈ s, incidentCount G A (D i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [biUnion_insert]
      calc
        incidentCount G A (D a ∪ s.biUnion D) ≤
            incidentCount G A (D a) + incidentCount G A (s.biUnion D) :=
          incidentCount_union_le G A (D a) (s.biUnion D)
        _ ≤ incidentCount G A (D a) + ∑ i ∈ s, incidentCount G A (D i) :=
          Nat.add_le_add_left ih _
        _ = ∑ i ∈ insert a s, incidentCount G A (D i) := by simp [ha]

lemma shortage_sdiff_biUnion_le_add_sum
    {ι : Type*} [DecidableEq ι]
    {A : Finset V} {k : ℕ}
    (s : Finset ι) (D : ι → Finset V) (b : ι → ℕ)
    (hsubset : ∀ i ∈ s, D i ⊆ A)
    (hdisj : (s : Set ι).PairwiseDisjoint D)
    (hincident : ∀ i ∈ s,
      incidentCount G A (D i) ≤ (k - 1) * (D i).card + b i) :
    shortage k G (A \ s.biUnion D) ≤
      shortage k G A + ((∑ i ∈ s, b i : ℕ) : ℤ) := by
  let X : Finset V := s.biUnion D
  have hXA : X ⊆ A := by
    intro x hx
    rw [mem_biUnion] at hx
    obtain ⟨i, his, hxi⟩ := hx
    exact hsubset i his hxi
  have hincNat :
      incidentCount G A X ≤
        (k - 1) * X.card + ∑ i ∈ s, b i := by
    calc
      incidentCount G A X ≤ ∑ i ∈ s, incidentCount G A (D i) := by
        simpa [X] using incidentCount_biUnion_le_sum (G := G) A s D
      _ ≤ ∑ i ∈ s, ((k - 1) * (D i).card + b i) :=
        sum_le_sum fun i hi ↦ hincident i hi
      _ = (k - 1) * (∑ i ∈ s, (D i).card) + ∑ i ∈ s, b i := by
        rw [sum_add_distrib, mul_sum]
      _ = (k - 1) * X.card + ∑ i ∈ s, b i := by
        rw [card_biUnion hdisj]
  have hincZ :
      (incidentCount G A X : ℤ) ≤
        ((k - 1 : ℕ) : ℤ) * (X.card : ℤ) +
          ((∑ i ∈ s, b i : ℕ) : ℤ) := by
    exact_mod_cast hincNat
  rw [shortage_sdiff k G hXA]
  unfold deletionPotential
  omega

lemma monochromaticBlockCount_add_uncoloredPrefix
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell ≤ J)
    (hnonempty : ∀ r < Dyadic.levelStart ell, (C.getD r ∅).Nonempty) :
    (∑ i : Color k, monochromaticBlockCount C phi ell i) +
        (uncoloredPrefixIndices C phi ell).card =
      Dyadic.levelStart ell := by
  classical
  have hblocks : ∀ r < Dyadic.levelStart ell,
      IsMonochromatic phi (C.getD r ∅) ∨
        BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    exact hphi.blocks r (hr.trans_le (Dyadic.levelStart_mono hellJ))
  have hone : ∀ r < Dyadic.levelStart ell,
      (∑ i : Color k, if Monochromatic phi (C.getD r ∅) i then 1 else 0) +
          (if BlockUncolored phi (C.getD r ∅) then 1 else 0) = 1 := by
    intro r hr
    rcases hblocks r hr with hm | hu
    · obtain ⟨i, hi⟩ := hm
      have hnotu : ¬ BlockUncolored phi (C.getD r ∅) := by
        intro hU
        obtain ⟨v, hv⟩ := hnonempty r hr
        have := (hi v hv).symm.trans (hU v hv)
        simp at this
      have hiff : ∀ j : Color k,
          Monochromatic phi (C.getD r ∅) j ↔ j = i := by
        intro j
        constructor
        · intro hj
          obtain ⟨v, hv⟩ := hnonempty r hr
          exact Option.some.inj ((hj v hv).symm.trans (hi v hv))
        · intro hji
          subst j
          exact hi
      have hsum :
          (∑ j : Color k,
            if Monochromatic phi (C.getD r ∅) j then 1 else 0) = 1 := by
        simp_rw [hiff]
        simp
      rw [hsum, if_neg hnotu]
    · have hnotm : ∀ i : Color k,
          ¬ Monochromatic phi (C.getD r ∅) i := by
        intro i hi
        obtain ⟨v, hv⟩ := hnonempty r hr
        have := (hi v hv).symm.trans (hu v hv)
        simp at this
      have hsum :
          (∑ i : Color k,
            if Monochromatic phi (C.getD r ∅) i then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg (hnotm i)]
      rw [hsum, if_pos hu]
  calc
    (∑ i : Color k, monochromaticBlockCount C phi ell i) +
        (uncoloredPrefixIndices C phi ell).card =
      (∑ i : Color k, ∑ r ∈ Finset.range (Dyadic.levelStart ell),
          if Monochromatic phi (C.getD r ∅) i then 1 else 0) +
        ∑ r ∈ Finset.range (Dyadic.levelStart ell),
          if BlockUncolored phi (C.getD r ∅) then 1 else 0 := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i hi
              simp [monochromaticBlockCount]
            · simp [uncoloredPrefixIndices]
    _ = ∑ r ∈ Finset.range (Dyadic.levelStart ell),
        ((∑ x : Color k, if Monochromatic phi (C.getD r ∅) x then 1 else 0) +
          if BlockUncolored phi (C.getD r ∅) then 1 else 0) := by
            rw [Finset.sum_comm]
            rw [← Finset.sum_add_distrib]
    _ = ∑ _r ∈ Finset.range (Dyadic.levelStart ell), 1 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hone r (Finset.mem_range.mp hr)
    _ = Dyadic.levelStart ell := by simp

lemma uncoloredPrefixIndices_card_succ
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) :
    (uncoloredPrefixIndices C phi (ell + 1)).card =
      (uncoloredPrefixIndices C phi ell).card +
        uncoloredBlockCount C phi ell := by
  classical
  let f : ℕ → ℕ := fun r ↦
    if BlockUncolored phi (C.getD r ∅) then 1 else 0
  have hsplit := Finset.sum_range_add_sum_Ico f
    (Dyadic.levelStart_le_succ ell)
  change
    ((Finset.range (Dyadic.levelStart (ell + 1))).filter fun r ↦
      BlockUncolored phi (C.getD r ∅)).card =
      ((Finset.range (Dyadic.levelStart ell)).filter fun r ↦
        BlockUncolored phi (C.getD r ∅)).card +
        ((Finset.Ico (Dyadic.levelStart ell)
          (Dyadic.levelStart (ell + 1))).filter fun r ↦
            BlockUncolored phi (C.getD r ∅)).card
  simpa [f] using hsplit.symm

lemma shortage_deficitResidual_le
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J) :
    shortage k G (deficitResidual A C phi (ell + 1)) ≤
      t + (Dyadic.levelStart ell : ℕ) + uncoloredBlockCount C phi ell := by
  classical
  let U : Finset V := coloredVertices A phi
  let R : Finset ℕ := uncoloredPrefixIndices C phi (ell + 1)
  let B : Finset V := A \ U
  let blocks : ℕ → Finset V := fun r ↦ C.getD r ∅
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hcolorRaw := shortage_sdiff_biUnion_le_add_sum (G := G)
    (A := A) (k := k) (s := (Finset.univ : Finset (Color k)))
    (D := colorClass A phi) (b := monochromaticBlockCount C phi ell)
    (fun _ _ ↦ filter_subset _ _)
    (pairwise_disjoint_colorClass A phi)
    (fun i _ ↦ hphi.incidence i)
  have hcolor :
      shortage k G B ≤ shortage k G A +
        ((∑ i : Color k, monochromaticBlockCount C phi ell i : ℕ) : ℤ) := by
    simpa [B, U, coloredVertices_eq_biUnion_colorClass] using hcolorRaw
  have hRsubset : ∀ r ∈ R, blocks r ⊆ B := by
    intro r hr v hv
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by
      simpa [R] using hr
    have hrData : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hrlt : r < Dyadic.levelStart J :=
      (Finset.mem_range.mp hrData.1).trans_le
        (Dyadic.levelStart_mono hellSuccJ)
    refine mem_sdiff.mpr ⟨S.block_subset r hrlt hv, ?_⟩
    intro hvU
    rw [mem_coloredVertices_iff] at hvU
    obtain ⟨hvA, i, hi⟩ := hvU
    have hnone := hrData.2 v hv
    rw [hnone] at hi
    contradiction
  have hRdisj : (R : Set ℕ).PairwiseDisjoint blocks := by
    intro r hr s hs hrs
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hr
    have hs' : s ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hs
    have hrAll : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hsAll : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hs'
    have hrData := hrAll.1
    have hsData := hsAll.1
    exact S.blocks_disjoint r ((mem_range.mp hrData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)) s ((mem_range.mp hsData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)) hrs
  have hRincident : ∀ r ∈ R,
      incidentCount G B (blocks r) ≤ (k - 1) * (blocks r).card + 1 := by
    intro r hr
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hr
    have hrAll : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hrData := hrAll.1
    have hrlt : r < Dyadic.levelStart J := (mem_range.mp hrData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)
    exact (incidentCount_ambient_mono (G := G) (A := B) (B := A)
      sdiff_subset).trans (S.block_incident r hrlt)
  have hblockRaw := shortage_sdiff_biUnion_le_add_sum (G := G)
    (A := B) (k := k) R blocks (fun _ ↦ 1)
    hRsubset hRdisj hRincident
  have hblock :
      shortage k G (B \ R.biUnion blocks) ≤
        shortage k G B + (R.card : ℤ) := by simpa using hblockRaw
  have hshape :
      B \ R.biUnion blocks = deficitResidual A C phi (ell + 1) := by
    ext v
    simp [B, U, R, blocks, deficitResidual, uncoloredPrefixUnion]
    tauto
  rw [hshape] at hblock
  have hRcard : R.card = (uncoloredPrefixIndices C phi (ell + 1)).card := rfl
  rw [hRcard] at hblock
  have hellLeJ : ell ≤ J := hellJ.le
  have hbook := monochromaticBlockCount_add_uncoloredPrefix
    (G := G) hphi hellLeJ fun r hr ↦
      S.block_nonempty r (hr.trans_le (Dyadic.levelStart_mono hellLeJ))
  have hsplit := uncoloredPrefixIndices_card_succ C phi ell
  have hshort := S.shortage_le
  omega

lemma shortage_deficitResidual_le_twelve
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (hquarter : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    shortage k G (deficitResidual A C phi (ell + 1)) ≤
      12 * uncoloredBlockCount C phi ell := by
  have hdt := shortage_deficitResidual_le S hphi hJ0ell hellJ
  have hmono : 2 ^ J0 ≤ 2 ^ ell := Nat.pow_le_pow_right (by omega) hJ0ell
  have htell : t < (2 ^ ell : ℕ) :=
    lt_of_lt_of_le S.power (by exact_mod_cast hmono)
  have hstart : Dyadic.levelStart ell <
      4 * uncoloredBlockCount C phi ell := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) hquarter
  have ht4 : t < (4 * uncoloredBlockCount C phi ell : ℕ) :=
    lt_of_lt_of_le htell (by exact_mod_cast hquarter.le)
  omega

/-- Abstract output of the hard part of Sauermann's successor construction.

`Z i` is the union of the newly coloured level blocks of colour `i`, and
`X i` is the key-lemma deletion set `X'_i`.  Its fields are exactly
(5.31)--(5.35) and (K1)--(K4). -/
structure SuccessorData
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi rho : PartialColoring V k) where
  Z : Color k → Finset V
  X : Color k → Finset V
  newBlockCount : Color k → ℕ
  refines : Extends phi rho
  support : ∀ v, v ∉ A → rho v = none
  block_status : ∀ r < Dyadic.levelStart J,
    IsMonochromatic rho (C.getD r ∅) ∨ BlockUncolored rho (C.getD r ∅)
  class_eq : ∀ i,
    colorClass A rho i = colorClass A phi i ∪ (Z i ∪ X i)
  class_card : ∀ i,
    (colorClass A rho i).card =
      (colorClass A phi i).card + (Z i).card + (X i).card
  block_incidence : ∀ i,
    incidentCount G (A \ colorClass A phi i) (Z i) ≤
      (k - 1) * (Z i).card + newBlockCount i
  removed_incidence : ∀ i,
    incidentCount G ((A \ colorClass A phi i) \ Z i) (X i) ≤
      (k - 1) * (X i).card
  block_count_gain : ∀ i,
    monochromaticBlockCount C phi ell i + newBlockCount i ≤
      monochromaticBlockCount C rho (ell + 1) i
  retained_core : ∀ i, HasMinDegreeOn G (A \ colorClass A rho i) k
  early : ∀ r < Dyadic.levelStart J0, BlockUncolored rho (C.getD r ∅)
  quarter : 4 * uncoloredBlockCount C rho ell ≤ 2 ^ ell
  future_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J →
    BlockUncolored rho (C.getD r ∅) → ∀ i,
      ¬ AdjacentSets G (C.getD r ∅) (Z i ∪ X i)

/-- The bookkeeping successor theorem: `SuccessorData` implies all seven
appropriate-colouring clauses at the next level. -/
theorem Appropriate.succ_of_data
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi rho : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (d : SuccessorData G A k C J0 ell J phi rho) :
    Appropriate G A k C J0 (ell + 1) J rho := by
  refine ⟨d.support, d.block_status, ?_, d.retained_core, d.early, ?_, ?_⟩
  · intro i
    let O := colorClass A phi i
    have hsplit1 := incidentCount_union_eq_add_restricted G A O (d.Z i ∪ d.X i)
    have hsplit2 := incidentCount_union_eq_add_restricted G (A \ O) (d.Z i) (d.X i)
    calc
      incidentCount G A (colorClass A rho i) =
          incidentCount G A (O ∪ (d.Z i ∪ d.X i)) := by rw [d.class_eq i]
      _ = incidentCount G A O + incidentCount G (A \ O) (d.Z i ∪ d.X i) :=
        hsplit1
      _ = incidentCount G A O +
          (incidentCount G (A \ O) (d.Z i) +
            incidentCount G ((A \ O) \ d.Z i) (d.X i)) := by rw [hsplit2]
      _ ≤ ((k - 1) * O.card + monochromaticBlockCount C phi ell i) +
          (((k - 1) * (d.Z i).card + d.newBlockCount i) +
            ((k - 1) * (d.X i).card)) := by
        exact Nat.add_le_add (hphi.incidence i)
          (Nat.add_le_add (d.block_incidence i) (d.removed_incidence i))
      _ = (k - 1) * (colorClass A rho i).card +
          (monochromaticBlockCount C phi ell i + d.newBlockCount i) := by
        rw [d.class_card i]
        ring
      _ ≤ (k - 1) * (colorClass A rho i).card +
          monochromaticBlockCount C rho (ell + 1) i :=
        Nat.add_le_add_left (d.block_count_gain i) _
  · intro j hj0 hj
    have hjle : j ≤ ell := Nat.lt_succ_iff.mp hj
    rcases Nat.lt_or_eq_of_le hjle with hjell | rfl
    · exact (Nat.mul_le_mul_left 4 (d.refines.uncoloredBlockCount_le C j)).trans
        (hphi.processed j hj0 hjell)
    · exact d.quarter
  · intro r hr hJ hrun
    have hrunOld : BlockUncolored phi (C.getD r ∅) :=
      d.refines.blockUncolored hrun
    have hrOld : Dyadic.levelStart ell ≤ r :=
      (Dyadic.levelStart_le_succ ell).trans hr
    have hOldNeighborhood := hphi.future r hrOld hJ hrunOld
    intro v hv w hwA hvw
    cases hrho : rho w with
    | none => rfl
    | some i =>
        have hwClass : w ∈ colorClass A rho i := by
          simp [colorClass, hwA, hrho]
        rw [d.class_eq i] at hwClass
        rcases mem_union.mp hwClass with hwOld | hwNew
        · have hphiwi : phi w = some i := (mem_filter.mp hwOld).2
          have hphinone := hOldNeighborhood v hv w hwA hvw
          rw [hphinone] at hphiwi
          contradiction
        · exact False.elim <| d.future_anticomplete r hr hJ hrun i
            ⟨v, hv, w, hwNew, hvw⟩

theorem appropriateColoring_succ
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrepair : ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho)) :
    ∃ rho, Appropriate G A k C J0 (ell + 1) J rho := by
  obtain ⟨rho, ⟨d⟩⟩ := hrepair
  exact ⟨rho, hphi.succ_of_data d⟩

/-- Equation (5.32), extracted from the signed-shortage clause of an
extension conclusion. -/
lemma incidentCount_deleted_le_of_shortage_le
    {A U' : Finset V} {k : ℕ}
    (hsub : U' ⊆ A) (hshort : shortage k G U' ≤ shortage k G A) :
    incidentCount G A (A \ U') ≤ (k - 1) * (A \ U').card := by
  have hcomp : A \ (A \ U') = U' := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxA, hx⟩
      by_contra hxU'
      exact hx ⟨hxA, hxU'⟩
    · intro hxU'
      exact ⟨hsub hxU', fun hx ↦ hx.2 hxU'⟩
  have hs := shortage_sdiff k G (show A \ U' ⊆ A from sdiff_subset)
  rw [hcomp] at hs
  have hpot : 0 ≤ deletionPotential k G A (A \ U') := by omega
  unfold deletionPotential at hpot
  exact_mod_cast (sub_nonneg.mp hpot)

lemma card_coloredVertices
    (A : Finset V) (phi : PartialColoring V k) :
    (coloredVertices A phi).card =
      ∑ i : Color k, (colorClass A phi i).card := by
  rw [coloredVertices_eq_biUnion_colorClass]
  exact Finset.card_biUnion (pairwise_disjoint_colorClass A phi)

/-! ## The final dyadic mass count -/

noncomputable def uncoloredLevelMass (C : List (Finset V))
    (phi : PartialColoring V k) (j : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Dyadic.levelIndices j,
    if BlockUncolored phi (C.getD r ∅) then Dyadic.cardAt C r else 0

noncomputable def uncoloredBetweenMass (C : List (Finset V))
    (phi : PartialColoring V k) (J0 J : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J),
    if BlockUncolored phi (C.getD r ∅) then Dyadic.cardAt C r else 0

noncomputable def coloredBlockMass (C : List (Finset V))
    (phi : PartialColoring V k) (J0 J : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J),
    if BlockUncolored phi (C.getD r ∅) then 0 else Dyadic.cardAt C r

private lemma sum_le_card_mul' {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, f i ≤ b) : s.sum f ≤ s.card * b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_le : f a ≤ b := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, f i ≤ b := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      nlinarith

private lemma card_mul_le_sum' {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, b ≤ f i) : s.card * b ≤ s.sum f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_ge : b ≤ f a := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, b ≤ f i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      nlinarith

lemma uncoloredLevelMass_le_count_mul
    (C : List (Finset V)) (phi : PartialColoring V k) {j J : ℕ}
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hjJ : j < J) :
    uncoloredLevelMass C phi j ≤
      uncoloredBlockCount C phi j * Dyadic.cardAt C (Dyadic.levelStart j) := by
  classical
  rw [uncoloredLevelMass, ← Finset.sum_filter]
  apply sum_le_card_mul'
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [Dyadic.mem_levelIndices] at hr
  apply hord hr.1.1
  exact hr.1.2.trans_le
    ((Dyadic.levelStart_mono (Nat.succ_le_of_lt hjJ)).trans hcomplete)

lemma prevLevel_card_mul_le_mass
    (C : List (Finset V)) {j J : ℕ}
    (hj : 0 < j) (hjJ : j < J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J) :
    2 ^ (j - 1) * Dyadic.cardAt C (Dyadic.levelStart j) ≤
      Dyadic.levelMass C (j - 1) := by
  have hstart_lt : Dyadic.levelStart j < C.length := by
    have hlt : Dyadic.levelStart j < Dyadic.levelStart (j + 1) := by
      rw [Dyadic.levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hlt.trans_le
      ((Dyadic.levelStart_mono (Nat.succ_le_of_lt hjJ)).trans hcomplete)
  have hsum : (Dyadic.levelIndices (j - 1)).card *
      Dyadic.cardAt C (Dyadic.levelStart j) ≤ Dyadic.levelMass C (j - 1) := by
    apply card_mul_le_sum'
    intro r hr
    rw [Dyadic.mem_levelIndices] at hr
    apply hord (Nat.le_of_lt ?_) hstart_lt
    simpa [show j - 1 + 1 = j by omega] using hr.2
  simpa using hsum

lemma two_mul_uncoloredLevelMass_le_prev
    (C : List (Finset V)) (phi : PartialColoring V k) {j J : ℕ}
    (hj : 0 < j) (hjJ : j < J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : 4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredLevelMass C phi j ≤ Dyadic.levelMass C (j - 1) := by
  have hu := uncoloredLevelMass_le_count_mul C phi hord hcomplete hjJ
  have hp := prevLevel_card_mul_le_mass C hj hjJ hord hcomplete
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    calc
      2 ^ j = 2 ^ ((j - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := Nat.mul_comm _ _
  rw [hpow] at hprocessed
  have hcount : 2 * uncoloredBlockCount C phi j ≤ 2 ^ (j - 1) := by omega
  calc
    2 * uncoloredLevelMass C phi j ≤
        2 * (uncoloredBlockCount C phi j * Dyadic.cardAt C (Dyadic.levelStart j)) :=
      Nat.mul_le_mul_left 2 hu
    _ = (2 * uncoloredBlockCount C phi j) * Dyadic.cardAt C (Dyadic.levelStart j) := by
      ring
    _ ≤ 2 ^ (j - 1) * Dyadic.cardAt C (Dyadic.levelStart j) :=
      Nat.mul_le_mul_right _ hcount
    _ ≤ Dyadic.levelMass C (j - 1) := hp

lemma uncoloredBetweenMass_succ
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 j : ℕ}
    (hJ0j : J0 ≤ j) :
    uncoloredBetweenMass C phi J0 (j + 1) =
      uncoloredBetweenMass C phi J0 j + uncoloredLevelMass C phi j := by
  classical
  unfold uncoloredBetweenMass uncoloredLevelMass Dyadic.levelIndices
  exact (Finset.sum_Ico_consecutive _ (Dyadic.levelStart_mono hJ0j)
    (Dyadic.levelStart_le_succ j)).symm

lemma betweenMass_succ
    (C : List (Finset V)) {J0 j : ℕ} (hJ0j : J0 ≤ j) :
    Dyadic.betweenMass C J0 (j + 1) =
      Dyadic.betweenMass C J0 j + Dyadic.levelMass C j := by
  unfold Dyadic.betweenMass Dyadic.levelMass Dyadic.levelIndices
  exact (Finset.sum_Ico_consecutive _ (Dyadic.levelStart_mono hJ0j)
    (Dyadic.levelStart_le_succ j)).symm

lemma two_mul_uncoloredBetweenMass_add_last_le
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 J : ℕ}
    (hJ0 : 0 < J0) (hJ0J : J0 ≤ J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : ∀ j, J0 ≤ j → j < J →
      4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredBetweenMass C phi J0 J + Dyadic.levelMass C (J - 1) ≤
      Dyadic.levelMass C (J0 - 1) + Dyadic.betweenMass C J0 J := by
  induction J, hJ0J using Nat.le_induction with
  | base => simp [uncoloredBetweenMass, Dyadic.betweenMass]
  | @succ j hj ih =>
      rw [uncoloredBetweenMass_succ C phi hj, betweenMass_succ C hj]
      have hjpos : 0 < j := hJ0.trans_le hj
      have hcompj : Dyadic.CompleteThrough C (j + 1) := hcomplete
      have hcompPrev : Dyadic.CompleteThrough C j :=
        (Dyadic.levelStart_mono (Nat.le_succ j)).trans hcomplete
      have ih' := ih hcompPrev
        (fun j' hj' hj'lt ↦ hprocessed j' hj'
          (hj'lt.trans (Nat.lt_succ_self j)))
      have hlev := two_mul_uncoloredLevelMass_le_prev C phi hjpos
        (Nat.lt_succ_self j) hord hcompj
        (hprocessed j hj (Nat.lt_succ_self j))
      have hjm : j + 1 - 1 = j := by omega
      rw [hjm]
      omega

lemma two_mul_uncoloredBetweenMass_le
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 J : ℕ}
    (hJ0 : 0 < J0) (hJ0J : J0 ≤ J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : ∀ j, J0 ≤ j → j < J →
      4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredBetweenMass C phi J0 J ≤
      Dyadic.levelMass C (J0 - 1) + Dyadic.betweenMass C J0 J := by
  exact (Nat.le_add_right _ _).trans
    (two_mul_uncoloredBetweenMass_add_last_le C phi hJ0 hJ0J hord hcomplete hprocessed)

lemma betweenMass_eq_uncolored_add_colored
    (C : List (Finset V)) (phi : PartialColoring V k) (J0 J : ℕ) :
    Dyadic.betweenMass C J0 J =
      uncoloredBetweenMass C phi J0 J + coloredBlockMass C phi J0 J := by
  classical
  unfold Dyadic.betweenMass uncoloredBetweenMass coloredBlockMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : BlockUncolored phi (C[r]?.getD ∅) <;> simp [h]

lemma coloredBlockMass_le_coloredVertices
    {A : Finset V} {k : ℕ} {t : ℤ} {C : List (Finset V)}
    {J0 J : ℕ} {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 J J phi) :
    coloredBlockMass C phi J0 J ≤ (coloredVertices A phi).card := by
  classical
  let s := (Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J)).filter fun r ↦
    ¬ BlockUncolored phi (C.getD r ∅)
  have hsrange : ∀ r ∈ s, r < Dyadic.levelStart J := by
    intro r hr
    simp only [s, Finset.mem_filter] at hr
    exact (Finset.mem_Ico.mp hr.1).2
  have hdisj : (s : Set ℕ).PairwiseDisjoint fun r ↦ C.getD r ∅ := by
    intro r hr s' hs' hrs
    exact S.blocks_disjoint r (hsrange r hr) s' (hsrange s' hs') hrs
  have hunion : s.biUnion (fun r ↦ C.getD r ∅) ⊆ coloredVertices A phi := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨r, hrs, hvr⟩
    have hrs' : r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J) ∧
        ¬ BlockUncolored phi (C.getD r ∅) := by
      simpa only [s, Finset.mem_filter] using hrs
    have hrIco := Finset.mem_Ico.mp hrs'.1
    have hvA := S.block_subset r hrIco.2 hvr
    have hmono : IsMonochromatic phi (C.getD r ∅) :=
      (hphi.blocks r hrIco.2).resolve_right hrs'.2
    rcases hmono with ⟨i, hi⟩
    exact mem_coloredVertices_iff.mpr ⟨hvA, i, hi v hvr⟩
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_biUnion hdisj] at hcard
  have heq : coloredBlockMass C phi J0 J =
      ∑ r ∈ s, Dyadic.cardAt C r := by
    unfold coloredBlockMass
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : BlockUncolored phi (C.getD r ∅) <;> simp [h]
  rw [heq]
  exact hcard

/-- Equation (6.3): a final appropriate coloring colors more than
`|A|/(20k)` vertices. -/
lemma final_colored_mass
    {A : Finset V} {k : ℕ} {t : ℤ} {C : List (Finset V)}
    {J0 J : ℕ} {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 J J phi) :
    A.card < 20 * k * (coloredVertices A phi).card := by
  have hu := two_mul_uncoloredBetweenMass_le C phi S.hJ0 S.hJ
    S.nonincreasing S.complete hphi.processed
  have hsplit := betweenMass_eq_uncolored_add_colored C phi J0 J
  have hcm := coloredBlockMass_le_coloredVertices S hphi
  nlinarith [S.late_mass, S.cutoff_level]

/-- Pigeonhole estimate corresponding to (6.4). -/
lemma exists_large_colorClass
    {A : Finset V} {k : ℕ} {phi : PartialColoring V k}
    (hk : 0 < k)
    (hcolored : A.card < 20 * k * (coloredVertices A phi).card) :
    ∃ i : Color k, A.card < 10000 * k ^ 2 * (colorClass A phi i).card := by
  by_contra h
  push_neg at h
  have hsum :
      10000 * k ^ 2 * (∑ i : Color k, (colorClass A phi i).card) ≤
        (401 * k) * A.card := by
    calc
      10000 * k ^ 2 * (∑ i : Color k, (colorClass A phi i).card) =
          ∑ i : Color k, 10000 * k ^ 2 * (colorClass A phi i).card := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _i : Color k, A.card := Finset.sum_le_sum fun i _ ↦ h i
      _ = (401 * k) * A.card := by simp
  rw [← card_coloredVertices] at hsum
  have hposA : 0 < A.card := by
    by_contra hA
    have hAz : A.card = 0 := Nat.eq_zero_of_not_pos hA
    have hsub : (coloredVertices A phi).card ≤ A.card :=
      card_le_card (filter_subset _ _)
    have hcz : (coloredVertices A phi).card = 0 := by omega
    rw [hAz, hcz] at hcolored
    simp at hcolored
  have hchain : 500 * k * A.card < 401 * k * A.card := by
    calc
      500 * k * A.card = (500 * k) * A.card := rfl
      _ < (500 * k) * (20 * k * (coloredVertices A phi).card) :=
        Nat.mul_lt_mul_of_pos_left hcolored (by positivity)
      _ = 10000 * k ^ 2 * (coloredVertices A phi).card := by ring
      _ ≤ 401 * k * A.card := hsum
  have hback : 401 * k * A.card < 500 * k * A.card := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (by decide : 401 < 500) hk) hposA
  exact (Nat.lt_asymm hchain hback).elim

/-- A sufficiently large colour class gives the exact integral form of the
`(1-1/(10000 k^3))` bound. -/
lemma smallCore_of_appropriate_and_colored
    {A : Finset V} {k J0 J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hk : 2 ≤ k) (hphi : Appropriate G A k C J0 J J phi)
    (hcolored : A.card < 20 * k * (coloredVertices A phi).card) :
    ∃ W, IsSmallCoreOn G A k (uniformDen k) W := by
  obtain ⟨i, hi⟩ := exists_large_colorClass (A := A) (phi := phi)
    (by omega : 0 < k) hcolored
  refine ⟨A \ colorClass A phi i, sdiff_subset, hphi.minDegree i, ?_⟩
  have hclass : (colorClass A phi i).card ≤ A.card :=
    card_le_card (filter_subset _ _)
  have hcard : (A \ colorClass A phi i).card =
      A.card - (colorClass A phi i).card := by
    exact card_sdiff_of_subset (filter_subset _ _)
  have hden : A.card ≤ uniformDen k * (colorClass A phi i).card := by
    have hkle : 10000 * k ^ 2 ≤ uniformDen k := by
      simp only [uniformDen]
      nlinarith
    exact hi.le.trans (Nat.mul_le_mul_right _ hkle)
  have hdenpos := uniformDen_pos k hk
  rw [hcard]
  rw [Nat.mul_sub_left_distrib]
  calc
    uniformDen k * A.card - uniformDen k * (colorClass A phi i).card ≤
        uniformDen k * A.card - A.card := Nat.sub_le_sub_left hden _
    _ = (uniformDen k - 1) * A.card := by
      rw [Nat.sub_mul]
      simp

lemma exists_maximalComplete (C : List (Finset V)) :
    ∃ J, Dyadic.MaximalComplete C J := by
  let J := Nat.findGreatest (fun j => Dyadic.levelStart j ≤ C.length) C.length
  have hcomp : Dyadic.levelStart J ≤ C.length := by
    simpa [J] using
      (Nat.findGreatest_spec (P := fun j => Dyadic.levelStart j ≤ C.length)
        (m := 0) (Nat.zero_le C.length) (by simp [Dyadic.levelStart]))
  refine ⟨J, hcomp, ?_⟩
  by_contra hn
  have hp : Dyadic.levelStart (J + 1) ≤ C.length := Nat.le_of_not_gt hn
  have hb : J + 1 ≤ C.length := by
    have hpow := (J + 1).lt_two_pow_self
    simp only [Dyadic.levelStart] at hp
    omega
  exact (Nat.findGreatest_is_greatest
    (P := fun j => Dyadic.levelStart j ≤ C.length)
    (n := C.length) (by omega) hb) hp

theorem exists_coloringSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t)
    (hlocal : LocalExpansion G A k)
    (hmin : HasMinDegreeOn G A k)
    (hconn : ConnectedOn G A)
    (hno : NoSmallCoreOn G A k (uniformDen k)) :
    ∃ C J0 J, ColoringSystem G A k t C J0 J := by
  classical
  let C := orderedMaxGood G A k
  obtain ⟨J, hJmax⟩ := exists_maximalComplete C
  have hCnoninc : Dyadic.Nonincreasing C := by
    dsimp only [C]
    exact orderedMaxGood_nonincreasing G A k
  have hCnodup : C.Nodup := by
    simpa [C] using orderedMaxGood_nodup G A k
  have htprob : t ≤ problemT k := by
    simp only [problemT, Tmax] at ht ⊢
    omega
  have hshortprob : shortage k G A ≤ problemT k := hshort.trans htprob
  have hedge : edgeThreshold k A.card ≤ edgeCount G A := by
    have hcast := edgeThreshold_cast_eq k A.card hk hcard
    have hcastle : (edgeThreshold k A.card : ℤ) ≤ (edgeCount G A : ℤ) := by
      rw [hcast]
      simpa [shortage, add_comm] using hshortprob
    exact_mod_cast hcastle
  have hden2k : 2 * k ≤ uniformDen k := by
    have hk2pos : 1 ≤ k ^ 2 := by nlinarith
    have hcoef : 2 ≤ 10000 * k ^ 2 := by nlinarith
    calc
      2 * k ≤ (10000 * k ^ 2) * k := Nat.mul_le_mul_right k hcoef
      _ = uniformDen k := by simp only [uniformDen]; ring
  have hden27 : 27 * k ^ 2 ≤ uniformDen k := by
    have hcoef : 27 ≤ 10000 * k := by nlinarith
    calc
      27 * k ^ 2 ≤ (10000 * k) * k ^ 2 := Nat.mul_le_mul_right (k ^ 2) hcoef
      _ = uniformDen k := by simp only [uniformDen]; ring
  have hden27pos : 1 ≤ 27 * k ^ 2 := by
    have : 0 < 27 * k ^ 2 := by positivity
    omega
  have hno27 : NoSmallCoreOn G A k (27 * k ^ 2) :=
    hno.anti_den hden27pos hden27
  have hnoSupply : ¬ ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
    simpa only [NoSmallCoreOn, IsSmallCoreOn] using hno27
  have hsupply : A.card ≤ 3 * k * (degreeEq G A k).card :=
    many_degree_eq_k_of_counterexample G A k hk hmin hnoSupply
  have hdegmass : (degreeEq G A k).card ≤
      ∑ D ∈ maxGood G A k, D.card :=
    card_degreeEq_le_maxGood_mass (G := G)
  have htotal : Dyadic.totalMass C = ∑ D ∈ maxGood G A k, D.card := by
    rw [Dyadic.totalMass_eq_sum_card]
    have hp := (List.mergeSort_perm (maxGood G A k).toList
      (fun D E : Finset V ↦ decide (E.card ≤ D.card))).map Finset.card
    have hs := hp.sum_eq
    simpa only [C, orderedMaxGood] using hs.trans (by simp)
  have hmassTotal : A.card ≤ 3 * k * Dyadic.totalMass C := by
    rw [htotal]
    exact hsupply.trans (Nat.mul_le_mul_left (3 * k) hdegmass)
  have hmassRet : A.card ≤ 6 * k * Dyadic.retainedMass C J := by
    have htail := Dyadic.two_mul_retainedMass_ge_totalMass C J hCnoninc hJmax
    calc
      A.card ≤ 3 * k * Dyadic.totalMass C := hmassTotal
      _ ≤ 3 * k * (2 * Dyadic.retainedMass C J) :=
        Nat.mul_le_mul_left (3 * k) htail
      _ = 6 * k * Dyadic.retainedMass C J := by ring
  have hreachJ : A.card ≤ 100 * k * Dyadic.retainedMass C J := by
    calc
      A.card ≤ 6 * k * Dyadic.retainedMass C J := hmassRet
      _ ≤ 100 * k * Dyadic.retainedMass C J := by nlinarith
  let P : ℕ → Prop := fun j ↦ A.card ≤ 100 * k * Dyadic.retainedMass C j
  have hPex : ∃ j, P j := ⟨J, hreachJ⟩
  let J0 := Nat.find hPex
  have hreach0 : A.card ≤ 100 * k * Dyadic.retainedMass C J0 := by
    exact Nat.find_spec hPex
  have hApos : 0 < A.card := hmin.1.card_pos
  have hJ0pos : 0 < J0 := by
    by_contra hn
    have hzero : J0 = 0 := Nat.eq_zero_of_not_pos hn
    have hretzero : Dyadic.retainedMass C J0 = 0 := by
      rw [hzero]
      simp [Dyadic.retainedMass, Dyadic.levelStart]
    rw [hretzero] at hreach0
    omega
  have hJ0J : J0 ≤ J := Nat.find_min' hPex hreachJ
  have hprev : 100 * k * Dyadic.retainedMass C (J0 - 1) < A.card := by
    by_contra hn
    have hp : P (J0 - 1) := Nat.le_of_not_gt hn
    have := Nat.find_min' hPex hp
    omega
  have hgetMax : ∀ r, r < Dyadic.levelStart J →
      MaximalGood G A k (C.getD r ∅) := by
    intro r hr
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hmemC : C.getD r ∅ ∈ C := by
      rw [List.getD_eq_getElem _ _ hrlen]
      exact List.get_mem C ⟨r, hrlen⟩
    have hmemOrd : C.getD r ∅ ∈ orderedMaxGood G A k := by
      simpa only [C] using hmemC
    exact (mem_maxGood (G := G)).mp
      ((mem_orderedMaxGood_iff G A k _).mp hmemOrd)
  have hgetGood : ∀ r, r < Dyadic.levelStart J → Good G A k (C.getD r ∅) :=
    fun r hr ↦ (hgetMax r hr).1
  have hgetNonempty : ∀ r, r < Dyadic.levelStart J → (C.getD r ∅).Nonempty :=
    fun r hr ↦ Good.nonempty G (hgetGood r hr)
  have hgetSubset : ∀ r, r < Dyadic.levelStart J → C.getD r ∅ ⊆ A :=
    fun r hr ↦ Good.subset G (hgetGood r hr)
  have hgetMul : ∀ r, r < Dyadic.levelStart J →
      k * (C.getD r ∅).card ≤ A.card := by
    intro r hr
    exact Good.card_mul_le_of_noSmallCoreOn G hk hden2k hcard hlocal hedge hno
      (hgetGood r hr)
  have hgetCardRange : ∀ r, r < Dyadic.levelStart J →
      (C.getD r ∅).card ≤ A.card - k + 1 := by
    intro r hr
    have hpos := (hgetNonempty r hr).card_pos
    have hmul := hgetMul r hr
    have hprod : 0 ≤ (k - 1) * ((C.getD r ∅).card - 1) := Nat.zero_le _
    have hsum : (C.getD r ∅).card + k ≤ A.card + 1 := by
      nlinarith
    omega
  have hgetIncident : ∀ r, r < Dyadic.levelStart J →
      incidentCount G A (C.getD r ∅) ≤
        (k - 1) * (C.getD r ∅).card + 1 := by
    intro r hr
    exact Good.incidentCount_le_of_card_le G hlocal (hgetGood r hr)
      (hgetCardRange r hr)
  have hgetComplement : ∀ r, r < Dyadic.levelStart J →
      HasMinDegreeOn G (A \ C.getD r ∅) k := by
    intro r hr
    apply maximalGood_complement_hasMinDegreeOn G (hgetMax r hr)
    have hpos := (hgetNonempty r hr).card_pos
    have hmul := hgetMul r hr
    have hlt : (C.getD r ∅).card < A.card := by nlinarith
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    exact fun hsub ↦ (not_le_of_gt hlt) (card_le_card hsub)
  have hgetLarge : ∀ r, r < Dyadic.levelStart J →
      uniformDen k * (C.getD r ∅).card < A.card := by
    intro r hr
    by_contra hn
    have hAle : A.card ≤ uniformDen k * (C.getD r ∅).card :=
      Nat.le_of_not_gt hn
    apply hno
    refine ⟨A \ C.getD r ∅, sdiff_subset, hgetComplement r hr, ?_⟩
    rw [card_sdiff_of_subset (hgetSubset r hr), Nat.mul_sub_left_distrib,
      Nat.sub_mul]
    simpa only [one_mul] using Nat.sub_le_sub_left hAle (uniformDen k * A.card)
  have hdisjoint : ∀ r, r < Dyadic.levelStart J →
      ∀ s, s < Dyadic.levelStart J → r ≠ s →
        Disjoint (C.getD r ∅) (C.getD s ∅) := by
    intro r hr s hs hrs
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hslen : s < C.length := hs.trans_le hJmax.1
    have hne : C.getD r ∅ ≠ C.getD s ∅ := by
      intro heq
      rw [List.getD_eq_getElem _ _ hrlen, List.getD_eq_getElem _ _ hslen] at heq
      have hi := (hCnodup.get_inj_iff (i := ⟨r, hrlen⟩) (j := ⟨s, hslen⟩)).mp heq
      exact hrs (Fin.ext_iff.mp hi)
    have hrmem : C.getD r ∅ ∈ maxGood G A k :=
      (mem_maxGood (G := G)).mpr (hgetMax r hr)
    have hsmem : C.getD s ∅ ∈ maxGood G A k :=
      (mem_maxGood (G := G)).mpr (hgetMax s hs)
    exact maxGood_pairwiseDisjoint (G := G) hrmem hsmem hne
  have hanti : ∀ r, r < Dyadic.levelStart J →
      ∀ s, s < Dyadic.levelStart J → r ≠ s →
        Anticomplete G (C.getD r ∅) (C.getD s ∅) := by
    intro r hr s hs hrs
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hslen : s < C.length := hs.trans_le hJmax.1
    have hne : C.getD r ∅ ≠ C.getD s ∅ := by
      intro heq
      rw [List.getD_eq_getElem _ _ hrlen, List.getD_eq_getElem _ _ hslen] at heq
      have hi := (hCnodup.get_inj_iff (i := ⟨r, hrlen⟩) (j := ⟨s, hslen⟩)).mp heq
      exact hrs (Fin.ext_iff.mp hi)
    exact maxGood_pairwise_not_adjacent (G := G)
      ((mem_maxGood (G := G)).mpr (hgetMax r hr))
      ((mem_maxGood (G := G)).mpr (hgetMax s hs)) hne
  have hJ0one : 1 < J0 := by
    by_contra hn
    have heq : J0 = 1 := by omega
    have hzeroJ : 0 < Dyadic.levelStart J := by
      have hJpos : 0 < J := hJ0pos.trans_le hJ0J
      simp only [Dyadic.levelStart]
      have := Nat.one_lt_pow hJpos.ne' (by omega : 1 < (2 : ℕ))
      omega
    have hlarge0 := hgetLarge 0 hzeroJ
    have hmass0 : Dyadic.retainedMass C J0 = (C.getD 0 ∅).card := by
      simp [heq, Dyadic.retainedMass, Dyadic.levelStart, Dyadic.cardAt]
    rw [hmass0] at hreach0
    have hcoef : 100 * k ≤ uniformDen k := by
      simp only [uniformDen]
      nlinarith
    have : A.card ≤ uniformDen k * (C.getD 0 ∅).card :=
      hreach0.trans (Nat.mul_le_mul_right _ hcoef)
    omega
  have hcutLevel : 50 * k * Dyadic.levelMass C (J0 - 1) < A.card := by
    have hcomplete0 : Dyadic.CompleteThrough C J0 :=
      hJmax.1.trans' (Dyadic.levelStart_mono hJ0J)
    have hidx : J0 - 2 + 1 = J0 - 1 := by omega
    have hc : Dyadic.CompleteThrough C (J0 - 2 + 2) := by
      convert hcomplete0 using 1 <;> omega
    have hlevel2 := Dyadic.levelMass_succ_le_two_mul C (J0 - 2) hCnoninc hc
    rw [hidx] at hlevel2
    have hprevMass : Dyadic.levelMass C (J0 - 2) ≤
        Dyadic.retainedMass C (J0 - 1) := by
      have hadd := Dyadic.retainedMass_succ C (J0 - 2)
      rw [hidx] at hadd
      omega
    calc
      50 * k * Dyadic.levelMass C (J0 - 1) ≤
          50 * k * (2 * Dyadic.levelMass C (J0 - 2)) :=
        Nat.mul_le_mul_left (50 * k) hlevel2
      _ = 100 * k * Dyadic.levelMass C (J0 - 2) := by ring
      _ ≤ 100 * k * Dyadic.retainedMass C (J0 - 1) :=
        Nat.mul_le_mul_left (100 * k) hprevMass
      _ < A.card := hprev
  have hprefix : 100 * k * Dyadic.retainedMass C J0 < 3 * A.card := by
    rw [show J0 = (J0 - 1) + 1 by omega, Dyadic.retainedMass_succ]
    have hlevscaled : 100 * k * Dyadic.levelMass C (J0 - 1) < 2 * A.card := by
      have hh := (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr hcutLevel
      convert hh using 1 <;> ring
    calc
      100 * k * (Dyadic.retainedMass C (J0 - 1) +
          Dyadic.levelMass C (J0 - 1)) =
          100 * k * Dyadic.retainedMass C (J0 - 1) +
            100 * k * Dyadic.levelMass C (J0 - 1) := by ring
      _ < A.card + 2 * A.card := Nat.add_lt_add hprev hlevscaled
      _ = 3 * A.card := by ring
  have hlate : A.card < 8 * k * Dyadic.betweenMass C J0 J := by
    have hadd := Dyadic.retained_add_between (C := C) hJ0J
    by_contra hn
    have hB : 8 * k * Dyadic.betweenMass C J0 J ≤ A.card :=
      Nat.le_of_not_gt hn
    have hBscaled : 100 * k * Dyadic.betweenMass C J0 J ≤ 13 * A.card := by
      calc
        100 * k * Dyadic.betweenMass C J0 J ≤
            13 * (8 * k * Dyadic.betweenMass C J0 J) := by
              calc
                100 * k * Dyadic.betweenMass C J0 J =
                    100 * (k * Dyadic.betweenMass C J0 J) := by ring
                _ ≤ 104 * (k * Dyadic.betweenMass C J0 J) :=
                  Nat.mul_le_mul_right _ (by omega)
                _ = 13 * (8 * k * Dyadic.betweenMass C J0 J) := by ring
        _ ≤ 13 * A.card := Nat.mul_le_mul_left 13 hB
    have hRupper : 100 * k * Dyadic.retainedMass C J < 16 * A.card := by
      calc
        100 * k * Dyadic.retainedMass C J =
            100 * k * Dyadic.retainedMass C J0 +
              100 * k * Dyadic.betweenMass C J0 J := by rw [← hadd]; ring
        _ < 3 * A.card + 13 * A.card :=
          Nat.add_lt_add_of_lt_of_le hprefix hBscaled
        _ = 16 * A.card := by ring
    have hRlower : 50 * A.card ≤ 300 * k * Dyadic.retainedMass C J := by
      have := Nat.mul_le_mul_left 50 hmassRet
      convert this using 1 <;> ring
    have hRupper' : 300 * k * Dyadic.retainedMass C J < 48 * A.card := by
      have := (Nat.mul_lt_mul_left (by omega : 0 < 3)).mpr hRupper
      convert this using 1 <;> ring
    omega
  have hpower : t < (2 ^ J0 : ℕ) := by
    have hJpos : 0 < J := hJ0pos.trans_le hJ0J
    have hzeroJ : 0 < Dyadic.levelStart J := by
      simp only [Dyadic.levelStart]
      have := Nat.one_lt_pow hJpos.ne' (by omega : 1 < (2 : ℕ))
      omega
    have hlarge0 := hgetLarge 0 hzeroJ
    have htT : t ≤ Tmax k := by omega
    have htK : t ≤ (k ^ 2 : ℕ) := htT.trans (Tmax_le_sq k)
    have hkmass : k ^ 2 * (Dyadic.cardAt C 0) < Dyadic.retainedMass C J0 := by
      have hchain : 100 * k * (100 * k ^ 2 * Dyadic.cardAt C 0) <
          100 * k * Dyadic.retainedMass C J0 := by
        calc
          100 * k * (100 * k ^ 2 * Dyadic.cardAt C 0) =
              uniformDen k * (C.getD 0 ∅).card := by
                simp only [uniformDen, Dyadic.cardAt]; ring
          _ < A.card := hlarge0
          _ ≤ 100 * k * Dyadic.retainedMass C J0 := hreach0
      have hcanceled : 100 * k ^ 2 * Dyadic.cardAt C 0 <
          Dyadic.retainedMass C J0 := Nat.lt_of_mul_lt_mul_left hchain
      have hcard0pos : 0 < Dyadic.cardAt C 0 := by
        simpa only [Dyadic.cardAt] using (hgetNonempty 0 hzeroJ).card_pos
      have hk2pos : 0 < k ^ 2 := by positivity
      have hcoefmul : k ^ 2 < 100 * k ^ 2 := by
        calc
          k ^ 2 = 1 * k ^ 2 := by simp
          _ < 100 * k ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) hk2pos
      exact (Nat.mul_lt_mul_of_pos_right hcoefmul hcard0pos).trans hcanceled
    have hforbid : t * (Dyadic.cardAt C 0 : ℤ) <
        (Dyadic.retainedMass C J0 : ℕ) := by
      have hnonneg : (0 : ℤ) ≤ Dyadic.cardAt C 0 := by positivity
      have htKz : t ≤ (k ^ 2 : ℕ) := htK
      have hmulz : t * (Dyadic.cardAt C 0 : ℤ) ≤
          ((k ^ 2 : ℕ) : ℤ) * (Dyadic.cardAt C 0 : ℤ) :=
        mul_le_mul_of_nonneg_right htKz hnonneg
      have hkmassz : ((k ^ 2 : ℕ) : ℤ) * (Dyadic.cardAt C 0 : ℤ) <
          (Dyadic.retainedMass C J0 : ℤ) := by exact_mod_cast hkmass
      exact hmulz.trans_lt hkmassz
    exact Dyadic.signed_shortage_lt_two_pow
      (C := C) (q := Dyadic.retainedMass C J0) (J := J0) (t := t)
      hJ0pos hCnoninc
      (hJmax.1.trans' (Dyadic.levelStart_mono hJ0J)) le_rfl hforbid
  refine ⟨C, J0, J, ?_⟩
  exact
    { hk := hk
      hJ0 := hJ0pos
      hJ := hJ0J
      complete := hJmax.1
      nonincreasing := hCnoninc
      nodup := hCnodup
      block_nonempty := hgetNonempty
      block_subset := hgetSubset
      block_incident := hgetIncident
      block_complement_minDegree := hgetComplement
      blocks_disjoint := hdisjoint
      blocks_anticomplete := hanti
      minDegree := hmin
      connected := hconn
      noSmallCore := hno
      shortage_le := hshort
      power := hpower
      early_mass := hreach0
      cutoff_level := hcutLevel
      late_mass := hlate }

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Selected current-level blocks carrying one fixed colour. -/
def redBlockIndices (U : Finset ℕ) (blockColor : ℕ → Option I)
    (i : I) : Finset ℕ :=
  U.filter fun r ↦ blockColor r = some i

/-- The union `Z_i` in (5.24)--(5.26). -/
def redBlockUnion (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) : Finset V :=
  (redBlockIndices U blockColor i).biUnion fun r ↦ C.getD r ∅

/-- An edge to `Z_i` selects an actual block of colour `i`. -/
lemma adjacent_block_of_adjacent_redBlockUnion
    (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) {v : V}
    (h : AdjacentSets G {v} (redBlockUnion C U blockColor i)) :
    ∃ r ∈ U, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  rw [redBlockUnion, mem_biUnion] at hy
  obtain ⟨r, hr, hyr⟩ := hy
  rw [redBlockIndices, mem_filter] at hr
  exact ⟨r, hr.1, hr.2, v, by simp, y, hyr, hxy⟩

/-- A vertex which becomes low only after deleting `Z` must see `Z`.
This is the degree-drop step in (5.27) and (5.29). -/
lemma adjacent_of_low_after_delete
    {B Z : Finset V} {k : ℕ} {v : V}
    (hk : 2 ≤ k) (hZB : Z ⊆ B) (hv : v ∈ B \ Z)
    (hhigh : k ≤ degreeOn G B v)
    (hlow : degreeOn G (B \ Z) v ≤ k - 1) :
    AdjacentSets G {v} Z := by
  by_contra hnot
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hnot
  rw [heq] at hlow
  omega

/-- Abstract (5.27).  In the application, `P` is the union of the
previously removed uncoloured blocks.  The future-neighbour invariant says
that neighbours of `Z` are uncoloured, and block anticompleteness says that
no vertex of `P` sees `Z`. -/
lemma lowVertices_after_red_delete_subset_residual
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix_anti : ∀ v ∈ P, ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · exact hprefix_anti v hvP hadj

/-- The output of applying one extension certificate simultaneously for every
colour.  This packages (5.30)--(5.33) and (K1)--(K4), including the
pairwise-disjointness argument for the sets `X'_i`. -/
structure PerColorExtensionConclusion
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (Atilde : I → Finset V) where
  retained : I → Finset V
  X : I → Finset V
  deleted_eq : ∀ i, X i = Atilde i \ retained i
  retained_eq : ∀ i, retained i = Atilde i \ X i
  X_subset_H : ∀ i, X i ⊆ H
  X_subset_reserves : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k
  incidence : ∀ i,
    incidentCount G (Atilde i) (X i) ≤ (k - 1) * (X i).card
  minDegree : ∀ i, HasMinDegreeOn G (retained i) k
  whole_blocks_deleted : ∀ i D, D ∈ C.blocks →
    D ⊆ X i ∨ Disjoint D (X i)
  retained_blocks_anticomplete : ∀ i D, D ∈ C.blocks →
    Disjoint D (X i) → Anticomplete G D (X i)
  disjoint_from_old : ∀ D, Disjoint D H → ∀ i, Disjoint D (X i)
  low_index_description : ∀ i x, x ∈ X i →
    ∃ v ∈ lowVertices G (Atilde i) k,
      x ∈ E.reserve v
  pairwise_X : ∀ i j, i ≠ j → Disjoint (X i) (X j)

/-- The reusable per-colour application of Sauermann's extension lemma.

`hinside` is (5.27).  `hprotect` is the consequence of (G1)--(G2) saying
that the selected vertices `S` retain degree at least `k`.  `hred` is
(5.29): a low vertex sees a selected current-level block, and every such
block has the current colour.  Thus `hinside` and `hprotect` prove (5.28),
while `hred` makes the reserve sets used for distinct colours disjoint. -/
theorem apply_extension_per_color
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks →
      Anticomplete G (Atilde i \ H) D)
    (selectedBlocks : Finset (Finset V))
    (blockColor : Finset V → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ D ∈ selectedBlocks, AdjacentSets G {v} D) ∧
      (∀ D ∈ selectedBlocks, AdjacentSets G {v} D →
        blockColor D = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V, ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hindex_unique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j := by
    intro i j v hvi hvj
    obtain ⟨D, hDB, hvD⟩ := (hred i v hvi).1
    have hi := (hred i v hvi).2 D hDB hvD
    have hj := (hred j v hvj).2 D hDB hvD
    exact Option.some.inj (hi.symm.trans hj)
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hindex_unique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

/-- Upgrade (K1) from the residual protected family to the original block
family.  This is the exact last step used in the paper: a whole block is
either contained in `H`, when the certificate applies, or disjoint from
`H`, when `X'_i ⊆ H` applies. -/
lemma PerColorExtensionConclusion.whole_blocks_deleted_of_restriction
    {A H : Finset V} {k : ℕ}
    {C : ProtectedFamily G H k} {E : ExtensionCertificate G H k C}
    {Atilde : I → Finset V}
    (R : PerColorExtensionConclusion C E Atilde)
    (C₀ : ProtectedFamily G A k)
    (hwhole : C₀.WholeBlocks H)
    (hblocks : ∀ D, D ∈ C.blocks ↔ D ∈ C₀.blocks ∧ D ⊆ H) :
    ∀ i D, D ∈ C₀.blocks → D ⊆ R.X i ∨ Disjoint D (R.X i) := by
  intro i D hD
  rcases hwhole D hD with hDH | hDH
  · exact R.whole_blocks_deleted i D ((hblocks D).2 ⟨hD, hDH⟩)
  · exact Or.inr (hDH.mono_right (R.X_subset_H i))

section PopularScratch

variable {V Block Scope : Type*}
variable [Fintype V] [DecidableEq V]
variable [DecidableEq Block]
variable [DecidableEq Scope]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! The current uncoloured block indices at level `ell`. -/

noncomputable def currentUncoloredIndices
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

@[simp] lemma card_currentUncoloredIndices
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) :
    (currentUncoloredIndices C phi ell).card =
      uncoloredBlockCount C phi ell := by
  rfl

/-! Scope selection.  `adjacent U blocks s` is the set of target blocks
adjacent to `s`; the chosen scope has exactly the smaller of its cardinality
and the residual need. -/

def blockIndicesAdjacentTo
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V)) (U : Finset ℕ) (s : V) : Finset ℕ :=
  U.filter fun r ↦ ∃ v ∈ C.getD r ∅, G.Adj s v

def scopeNeed (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (k : ℕ) (s : V) : ℕ :=
  k + 1 - degreeOn G H s

lemma scopeNeed_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (k : ℕ) (s : V) : scopeNeed G H k s ≤ k + 1 := by
  exact Nat.sub_le _ _

noncomputable def selectedScope
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (s : Scope) : Finset Block := by
  classical
  exact Classical.choose
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))

lemma selectedScope_subset
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    selectedScope adjacent need s ⊆ adjacent s := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))).1

lemma card_selectedScope
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    (selectedScope adjacent need s).card = min (adjacent s).card (need s) := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))).2

lemma card_selectedScope_le_need
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    (selectedScope adjacent need s).card ≤ need s := by
  rw [card_selectedScope]
  exact Nat.min_le_right _ _

lemma selectedScope_eq_adjacent_of_card_lt_need
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope)
    (h : (adjacent s).card < need s) :
    selectedScope adjacent need s = adjacent s := by
  classical
  apply Finset.eq_of_subset_of_card_le (selectedScope_subset adjacent need s)
  rw [card_selectedScope, Nat.min_eq_left (Nat.le_of_lt h)]

/-! Popularity and double counting. -/

def scopeFrequency (S : Finset Scope) (scope : Scope → Finset Block)
    (D : Block) : ℕ :=
  (S.filter fun s ↦ D ∈ scope s).card

def IsPopular (S : Finset Scope) (scope : Scope → Finset Block)
    (D : Block) : Prop :=
  200 < scopeFrequency S scope D

instance instDecidablePredIsPopular
    (S : Finset Scope) (scope : Scope → Finset Block) :
    DecidablePred (IsPopular S scope) := by
  intro D
  unfold IsPopular scopeFrequency
  infer_instance

def popularBlocks (U : Finset Block) (S : Finset Scope)
    (scope : Scope → Finset Block) : Finset Block :=
  U.filter fun D ↦ IsPopular S scope D

def nonpopularBlocks (U : Finset Block) (S : Finset Scope)
    (scope : Scope → Finset Block) : Finset Block :=
  U \ popularBlocks U S scope

lemma sum_card_scope_eq_sum_frequency
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (hscope : ∀ s ∈ S, scope s ⊆ U) :
    ∑ s ∈ S, (scope s).card =
      ∑ D ∈ U, scopeFrequency S scope D := by
  classical
  calc
    ∑ s ∈ S, (scope s).card =
        ∑ s ∈ S, ∑ D ∈ U, if D ∈ scope s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      have hi : U ∩ scope s = scope s :=
        Finset.inter_eq_right.mpr (hscope s hs)
      simp [hi]
    _ = ∑ D ∈ U, ∑ s ∈ S, if D ∈ scope s then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ U, scopeFrequency S scope D := by
      apply Finset.sum_congr rfl
      intro D hDU
      rw [← Finset.sum_filter]
      simp [scopeFrequency]

lemma popular_frequency_lower
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block) :
    201 * (popularBlocks U S scope).card ≤
      ∑ D ∈ U, scopeFrequency S scope D := by
  classical
  calc
    201 * (popularBlocks U S scope).card =
        ∑ D ∈ popularBlocks U S scope, 201 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ D ∈ popularBlocks U S scope, scopeFrequency S scope D := by
      apply Finset.sum_le_sum
      intro D hD
      have hp : IsPopular S scope D := by
        exact (Finset.mem_filter.mp (by simpa [popularBlocks] using hD)).2
      exact Nat.succ_le_iff.mpr hp
    _ ≤ ∑ D ∈ U, scopeFrequency S scope D := by
      apply Finset.sum_le_sum_of_subset
      intro D hD
      exact (Finset.mem_filter.mp (by simpa [popularBlocks] using hD)).1

lemma four_mul_card_popular_le
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (hscope : ∀ s ∈ S, scope s ⊆ U)
    (hsum : ∑ s ∈ S, (scope s).card ≤ 48 * U.card) :
    4 * (popularBlocks U S scope).card ≤ U.card := by
  have hlower := popular_frequency_lower U S scope
  rw [← sum_card_scope_eq_sum_frequency U S scope hscope] at hlower
  omega

lemma sum_card_selectedScope_le
    (U : Finset Block) (S' S : Finset Scope)
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (hS : S' ⊆ S)
    (hneed : ∑ s ∈ S, need s ≤ 48 * U.card) :
    ∑ s ∈ S', (selectedScope adjacent need s).card ≤ 48 * U.card := by
  calc
    ∑ s ∈ S', (selectedScope adjacent need s).card ≤
        ∑ s ∈ S', need s := by
      exact Finset.sum_le_sum fun s hs ↦ card_selectedScope_le_need adjacent need s
    _ ≤ ∑ s ∈ S, need s := by
      exact Finset.sum_le_sum_of_subset hS
    _ ≤ 48 * U.card := hneed

def activeScopes (S : Finset Scope) (adjacent : Scope → Finset Block) :
    Finset Scope :=
  S.filter fun s ↦ (adjacent s).Nonempty

lemma activeScopes_subset (S : Finset Scope) (adjacent : Scope → Finset Block) :
    activeScopes S adjacent ⊆ S :=
  Finset.filter_subset _ _

theorem four_mul_card_popular_selectedScope_le
    (U : Finset Block) (S' S : Finset Scope)
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (hS : S' ⊆ S)
    (hadjacent : ∀ s ∈ S', adjacent s ⊆ U)
    (hneed : ∑ s ∈ S, need s ≤ 48 * U.card) :
    4 * (popularBlocks U S' (selectedScope adjacent need)).card ≤ U.card := by
  apply four_mul_card_popular_le U S' (selectedScope adjacent need)
  · intro s hs
    exact (selectedScope_subset adjacent need s).trans (hadjacent s hs)
  · exact sum_card_selectedScope_le U S' S adjacent need hS hneed

/-! The graph-specialized names used in the successor construction. -/

noncomputable def activeDeficitVertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V)) (U : Finset ℕ)
    (S : Finset V) : Finset V :=
  activeScopes S (blockIndicesAdjacentTo G C U)

noncomputable def vertexScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : Finset ℕ :=
  selectedScope (blockIndicesAdjacentTo G C U) (scopeNeed G H k) s

lemma vertexScope_subset_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) :
    vertexScope G H C U k s ⊆ blockIndicesAdjacentTo G C U s :=
  selectedScope_subset _ _ _

lemma vertexScope_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : vertexScope G H C U k s ⊆ U := by
  exact (vertexScope_subset_adjacent G H C U k s).trans (Finset.filter_subset _ _)

lemma card_vertexScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) :
    (vertexScope G H C U k s).card =
      min (blockIndicesAdjacentTo G C U s).card (scopeNeed G H k s) :=
  card_selectedScope _ _ _

lemma card_vertexScope_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : (vertexScope G H C U k s).card ≤ k + 1 := by
  exact (card_selectedScope_le_need _ _ _).trans (scopeNeed_le G H k s)

lemma vertexScope_eq_adjacent_of_card_lt_need
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V)
    (h : (blockIndicesAdjacentTo G C U s).card < scopeNeed G H k s) :
    vertexScope G H C U k s = blockIndicesAdjacentTo G C U s :=
  selectedScope_eq_adjacent_of_card_lt_need _ _ _ h

/-! Neighbor-colour avoid lists. -/

def neighborColors (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (phi : PartialColoring V k) (s : V) : Finset (Color k) :=
  Finset.univ.filter fun i ↦ ∃ v ∈ A, G.Adj s v ∧ phi v = some i

noncomputable def selectedNeighborColors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) : Finset (Color k) := by
  classical
  exact Classical.choose
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))

lemma selectedNeighborColors_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    selectedNeighborColors G A phi s ⊆ neighborColors G A phi s := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).1

lemma card_selectedNeighborColors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    (selectedNeighborColors G A phi s).card =
      min (neighborColors G A phi s).card k := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).2

lemma card_selectedNeighborColors_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    (selectedNeighborColors G A phi s).card ≤ k := by
  classical
  rw [card_selectedNeighborColors]
  exact Nat.min_le_right _ _

lemma selectedNeighborColors_eq_of_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) (h : (neighborColors G A phi s).card ≤ k) :
    selectedNeighborColors G A phi s = neighborColors G A phi s := by
  classical
  apply Finset.eq_of_subset_of_card_le (selectedNeighborColors_subset G A phi s)
  rw [selectedNeighborColors]
  have hs := (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).2
  rw [hs, Nat.min_eq_left h]

/-! Restrict scopes to the subtype of nonpopular target blocks and apply the
pre-existing greedy theorem. -/

section FiniteGreedy

variable [Fintype Block] [Fintype Scope]

def nonpopularScope
    (P : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (s : Scope) : Finset {D // D ∈ P} :=
  Finset.univ.filter fun D ↦ s ∈ S ∧ (D : Block) ∈ scope s

lemma card_nonpopularScope_le
    (P : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (s : Scope) :
    (nonpopularScope P S scope s).card ≤ (scope s).card := by
  classical
  let f : {D // D ∈ P} → Block := fun D ↦ D
  have hinj : Set.InjOn f (nonpopularScope P S scope s : Set {D // D ∈ P}) :=
    fun _ _ _ _ h ↦ Subtype.ext h
  have hcard : (nonpopularScope P S scope s).card =
      ((nonpopularScope P S scope s).image f).card := by
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact Subtype.ext hxy
  rw [hcard]
  apply Finset.card_le_card
  intro D hD
  rw [Finset.mem_image] at hD
  obtain ⟨x, hx, rfl⟩ := hD
  exact (Finset.mem_filter.mp hx).2.2

theorem exists_nonpopular_scope_coloring
    {k : ℕ} (hk : 0 < k)
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (avoid : Scope → Finset (Color k))
    (hscopeU : ∀ s ∈ S, scope s ⊆ U)
    (hscope : ∀ s ∈ S, (scope s).card ≤ k + 1)
    (havoid : ∀ s, (avoid s).card ≤ k) :
    ∃ color : {D // D ∈ nonpopularBlocks U S scope} → Color k,
      (∀ s : Scope, Set.InjOn color
        (nonpopularScope (nonpopularBlocks U S scope) S scope s :
          Set {D // D ∈ nonpopularBlocks U S scope})) ∧
      (∀ s : Scope, ∀ D ∈
        nonpopularScope (nonpopularBlocks U S scope) S scope s,
        color D ∉ avoid s) := by
  classical
  apply exists_erdos814_scope_coloring hk
  · intro D
    have hnonpop : ¬ IsPopular S scope (D : Block) := by
      have hD := D.property
      change (D : Block) ∈ U \ popularBlocks U S scope at hD
      rw [Finset.mem_sdiff] at hD
      exact fun hp ↦ hD.2 (by
        simpa [popularBlocks] using (Finset.mem_filter.mpr ⟨hD.1, hp⟩))
    have heq :
        (Finset.univ.filter fun s : Scope ↦
          D ∈ nonpopularScope (nonpopularBlocks U S scope) S scope s) =
        S.filter fun s ↦ (D : Block) ∈ scope s := by
      ext s
      simp [nonpopularScope]
    rw [heq]
    simpa [IsPopular, scopeFrequency] using (Nat.le_of_not_gt hnonpop)
  · intro s
    by_cases hs : s ∈ S
    · exact (card_nonpopularScope_le _ _ _ s).trans (hscope s hs)
    · simp [nonpopularScope, hs]
  · exact havoid

theorem exists_nonpopular_scope_coloring_with_neighbor_lists
    {k : ℕ} (hk : 0 < k)
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (A : Finset V) (phi : PartialColoring V k) (atVertex : Scope → V)
    (hscopeU : ∀ s ∈ S, scope s ⊆ U)
    (hscope : ∀ s ∈ S, (scope s).card ≤ k + 1) :
    ∃ color : {D // D ∈ nonpopularBlocks U S scope} → Color k,
      (∀ s : Scope, Set.InjOn color
        (nonpopularScope (nonpopularBlocks U S scope) S scope s :
          Set {D // D ∈ nonpopularBlocks U S scope})) ∧
      (∀ s : Scope, ∀ D ∈
        nonpopularScope (nonpopularBlocks U S scope) S scope s,
        color D ∉ selectedNeighborColors G A phi (atVertex s)) := by
  exact exists_nonpopular_scope_coloring hk U S scope
    (fun s ↦ selectedNeighborColors G A phi (atVertex s))
    hscopeU hscope (fun s ↦ card_selectedNeighborColors_le G A phi (atVertex s))

end FiniteGreedy

end PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adjacent_cut_of_connectedOn
    {A D : Finset V} (hconn : ConnectedOn G A)
    (hD : D.Nonempty) (hDA : D ⊆ A) (hcomp : (A \ D).Nonempty) :
    AdjacentSets G D (A \ D) := by
  classical
  obtain ⟨u, huD⟩ := hD
  obtain ⟨v, hvAD⟩ := hcomp
  have huA : u ∈ A := hDA huD
  have hvA : v ∈ A := (mem_sdiff.mp hvAD).1
  let uA : (↑A : Set V) := ⟨u, huA⟩
  let vA : (↑A : Set V) := ⟨v, hvA⟩
  change (G.induce (↑A : Set V)).Connected at hconn
  obtain ⟨p⟩ := hconn.preconnected uA vA
  obtain ⟨d, _hdp, hdD, hdnotD⟩ :=
    p.exists_boundary_dart {x : (↑A : Set V) | (x : V) ∈ D}
      (by simpa [uA] using huD) (by simpa [vA] using (mem_sdiff.mp hvAD).2)
  refine ⟨(d.toProd.1 : V), hdD, (d.toProd.2 : V), ?_, ?_⟩
  · exact mem_sdiff.mpr ⟨d.toProd.2.property, hdnotD⟩
  · exact d.adj

lemma deficitResidual_nonempty
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    (deficitResidual A C phi (ell + 1)).Nonempty := by
  classical
  have hpow : 0 < 2 ^ ell := pow_pos (by omega) ell
  have hcount : 0 < uncoloredBlockCount C phi ell := by omega
  have hindices : (uncoloredCurrentIndices C phi ell).Nonempty := by
    simpa [uncoloredCurrentIndices, uncoloredBlockCount] using hcount
  obtain ⟨r, hrU⟩ := hindices
  have hrData : r ∈ Dyadic.levelIndices ell ∧
      BlockUncolored phi (C.getD r ∅) := by
    simpa [uncoloredCurrentIndices] using hrU
  have hrRange := (Dyadic.mem_levelIndices.mp hrData.1)
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hrJ : r < Dyadic.levelStart J :=
    hrRange.2.trans_le (Dyadic.levelStart_mono hellSuccJ)
  let D := C.getD r ∅
  have hDne : D.Nonempty := S.block_nonempty r hrJ
  have hDA : D ⊆ A := S.block_subset r hrJ
  have hcomp : (A \ D).Nonempty := (S.block_complement_minDegree r hrJ).1
  obtain ⟨v, hvD, w, hwAD, hvw⟩ :=
    adjacent_cut_of_connectedOn (G := G) S.connected hDne hDA hcomp
  have hwA : w ∈ A := (mem_sdiff.mp hwAD).1
  have hwD : w ∉ D := (mem_sdiff.mp hwAD).2
  have hwnone : phi w = none :=
    hphi.future r hrRange.1 hrJ hrData.2 v hvD w hwA hvw
  refine ⟨w, mem_sdiff.mpr ⟨hwA, ?_⟩⟩
  rw [mem_union]
  push_neg
  constructor
  · intro hwColored
    rw [mem_coloredVertices_iff] at hwColored
    obtain ⟨_, i, hi⟩ := hwColored
    rw [hwnone] at hi
    contradiction
  · intro hwPrefix
    rw [uncoloredPrefixUnion, mem_biUnion] at hwPrefix
    obtain ⟨s, hsPrefix, hws⟩ := hwPrefix
    have hsData : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hsPrefix
    have hsJ : s < Dyadic.levelStart J :=
      (mem_range.mp hsData.1).trans_le (Dyadic.levelStart_mono hellSuccJ)
    by_cases hrs : r = s
    · subst s
      exact hwD hws
    · exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨v, hvD, w, hws, hvw⟩

noncomputable def residualFutureIndices
    (A : Finset V) (C : List (Finset V))
    (phi : PartialColoring V k) (ell J : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (Dyadic.levelStart (ell + 1)) (Dyadic.levelStart J)).filter
    fun r ↦ C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)

lemma blockUncolored_of_subset_deficitResidual
    {A D : Finset V} {C : List (Finset V)} {phi : PartialColoring V k}
    {ell : ℕ} (hD : D ⊆ deficitResidual A C phi (ell + 1)) :
    BlockUncolored phi D := by
  intro v hv
  have hvH := hD hv
  have hvA : v ∈ A := (mem_sdiff.mp hvH).1
  have hvnotColored : v ∉ coloredVertices A phi := by
    intro hvColored
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvColored)
  cases hphi : phi v with
  | none => rfl
  | some i =>
      exact False.elim <| hvnotColored <|
        mem_coloredVertices_iff.mpr ⟨hvA, i, hphi⟩

lemma future_block_neighbor_closed_in_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrStart : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hD : C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)) :
    ∀ {x}, x ∈ C.getD r ∅ → ∀ {y}, y ∈ A → G.Adj x y →
      y ∈ deficitResidual A C phi (ell + 1) := by
  classical
  have hrun : BlockUncolored phi (C.getD r ∅) :=
    blockUncolored_of_subset_deficitResidual hD
  intro x hx y hyA hxy
  have hynone : phi y = none :=
    hphi.future r (Dyadic.levelStart_le_succ ell |>.trans hrStart) hrJ hrun
      x hx y hyA hxy
  refine mem_sdiff.mpr ⟨hyA, ?_⟩
  rw [mem_union]
  push_neg
  constructor
  · intro hyColored
    rw [mem_coloredVertices_iff] at hyColored
    obtain ⟨_, i, hi⟩ := hyColored
    rw [hynone] at hi
    contradiction
  · intro hyPrefix
    rw [uncoloredPrefixUnion, mem_biUnion] at hyPrefix
    obtain ⟨s, hsPrefix, hys⟩ := hyPrefix
    have hsData : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hsPrefix
    have hslt : s < Dyadic.levelStart (ell + 1) := mem_range.mp hsData.1
    have hsJ : s < Dyadic.levelStart J :=
      hslt.trans_le (hrStart.trans hrJ.le)
    have hrs : r ≠ s := by omega
    exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨x, hx, y, hys, hxy⟩

noncomputable def residualProtectedFamily
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ProtectedFamily G (deficitResidual A C phi (ell + 1)) k := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let R := residualFutureIndices A C phi ell J
  let block : ℕ → Finset V := fun r ↦ C.getD r ∅
  refine
    { blocks := R.image block
      nonempty := ?_
      subset_ambient := ?_
      pairwise_disjoint := ?_
      high_degree := ?_
      incident_le := ?_ }
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco : r ∈ Finset.Ico (Dyadic.levelStart (ell + 1))
        (Dyadic.levelStart J) := (mem_filter.mp hrR).1
    exact S.block_nonempty r (mem_Ico.mp hrIco).2
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    exact (mem_filter.mp hrR).2
  · intro D hD E hE hDE
    rw [mem_image] at hD hE
    obtain ⟨r, hrR, rfl⟩ := hD
    obtain ⟨s, hsR, rfl⟩ := hE
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    have hsIco := mem_Ico.mp (mem_filter.mp hsR).1
    have hrs : r ≠ s := by
      intro hrs
      subst s
      exact hDE rfl
    exact S.blocks_disjoint r hrIco.2 s hsIco.2 hrs
  · intro D hD x hx
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    have hDsub : C.getD r ∅ ⊆ H := (mem_filter.mp hrR).2
    have hclosed : ∀ {z}, z ∈ C.getD r ∅ → ∀ {y}, y ∈ A → G.Adj z y → y ∈ H :=
      future_block_neighbor_closed_in_deficitResidual
        S hphi hrIco.1 hrIco.2 hDsub
    have hdegEq : degreeOn G H x = degreeOn G A x := by
      unfold degreeOn
      congr 1
      ext y
      simp only [mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hxy, hyH⟩
        exact ⟨hxy, sdiff_subset hyH⟩
      · rintro ⟨hxy, hyA⟩
        exact ⟨hxy, hclosed hx hyA hxy⟩
    change k ≤ degreeOn G H x
    rw [hdegEq]
    exact S.minDegree.2 x (sdiff_subset (hDsub hx))
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    exact (incidentCount_ambient_mono (G := G) (A := H) (B := A)
      sdiff_subset).trans (S.block_incident r hrIco.2)


variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The union of selected current-level blocks assigned colour `i`. -/
def selectedBlockUnion (C : List (Finset V)) (N : Finset ℕ)
    (psi : ℕ → Color k) (i : Color k) : Finset V :=
  (N.filter fun r ↦ psi r = i).biUnion fun r ↦ C.getD r ∅

/-- The set newly assigned colour `i`, before turning the sets into a partial
colouring. -/
def assembledNewClass (C : List (Finset V)) (N : Finset ℕ)
    (psi : ℕ → Color k) (X : Color k → Finset V) (i : Color k) : Finset V :=
  selectedBlockUnion C N psi i ∪ X i

/-- Extend `phi` by the pairwise-disjoint sets `assembledNewClass`.
The uniqueness proof is deliberately not part of the definition; it is used
below to identify the arbitrary witness chosen here. -/
noncomputable def assembleColoring (phi : PartialColoring V k)
    (C : List (Finset V)) (N : Finset ℕ) (psi : ℕ → Color k)
    (X : Color k → Finset V) : PartialColoring V k :=
  fun v ↦
    if (phi v).isSome then phi v
    else if h : ∃ i, v ∈ assembledNewClass C N psi X i then
      some (Classical.choose h)
    else none

@[simp] lemma assembleColoring_eq_some_of_old
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (h : phi v = some i) : assembleColoring phi C N psi X v = some i := by
  simp [assembleColoring, h]

lemma assembleColoring_eq_none_of_old_none_of_new
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V}
    (hphi : phi v = none)
    (hnew : ∀ i, v ∉ assembledNewClass C N psi X i) :
    assembleColoring phi C N psi X v = none := by
  simp [assembleColoring, hphi, hnew]

lemma assembleColoring_eq_some_of_new
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (hphi : phi v = none)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j))
    (hv : v ∈ assembledNewClass C N psi X i) :
    assembleColoring phi C N psi X v = some i := by
  have hex : ∃ j, v ∈ assembledNewClass C N psi X j := ⟨i, hv⟩
  have hvj : v ∈ assembledNewClass C N psi X (Classical.choose hex) :=
    Classical.choose_spec hex
  have hchoice : Classical.choose hex = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hpair (Classical.choose hex) i hne)) hvj hv
  simp [assembleColoring, hphi, hex, hchoice]

lemma assembleColoring_eq_some_iff
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j))
    (huncolored : ∀ i, ∀ v ∈ assembledNewClass C N psi X i, phi v = none) :
    assembleColoring phi C N psi X v = some i ↔
      phi v = some i ∨ (phi v = none ∧ v ∈ assembledNewClass C N psi X i) := by
  constructor
  · intro hrho
    by_cases hp : phi v = none
    · right
      refine ⟨hp, ?_⟩
      by_cases h : ∃ j, v ∈ assembledNewClass C N psi X j
      · have hchoice : Classical.choose h = i := by
          have hs : some (Classical.choose h) = some i := by
            simpa [assembleColoring, hp, h] using hrho
          exact Option.some.inj hs
        simpa [hchoice] using Classical.choose_spec h
      · simp [assembleColoring, hp, h] at hrho
    · left
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hp
      have hji : j = i := by
        have hs : some j = some i := by simpa [assembleColoring, hj] using hrho
        exact Option.some.inj hs
      simpa [hji] using hj
  · rintro (hold | ⟨hnone, hnew⟩)
    · exact assembleColoring_eq_some_of_old hold
    · exact assembleColoring_eq_some_of_new hnone hpair hnew

lemma selectedBlock_subset_selectedBlockUnion
    {C : List (Finset V)} {N : Finset ℕ} {psi : ℕ → Color k}
    {r : ℕ} (hr : r ∈ N) :
    C.getD r ∅ ⊆ selectedBlockUnion C N psi (psi r) := by
  intro v hv
  rw [selectedBlockUnion, mem_biUnion]
  exact ⟨r, mem_filter.mpr ⟨hr, rfl⟩, hv⟩

lemma selectedBlock_mono_assembleColoring
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {r : ℕ}
    (hr : r ∈ N)
    (hphi : BlockUncolored phi (C.getD r ∅))
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j)) :
    Monochromatic (assembleColoring phi C N psi X) (C.getD r ∅) (psi r) := by
  intro v hv
  apply assembleColoring_eq_some_of_new (hphi v hv) hpair
  exact mem_union_left _ (selectedBlock_subset_selectedBlockUnion hr hv)

/-- Abstract hypotheses needed only for the finite-set bookkeeping that turns
the block colouring and the per-colour extension outputs into
`SuccessorData`.  Graph-specific work (popularity, the key lemma, and the
definition of the residual graph) is intentionally upstream of this
structure. -/
structure AssemblyInput
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi : PartialColoring V k) where
  Uidx : Finset ℕ
  N : Finset ℕ
  psi : ℕ → Color k
  X : Color k → Finset V
  Uidx_eq : Uidx = uncoloredCurrentIndices C phi ell
  N_subset_Uidx : N ⊆ Uidx
  selected_nonempty : ∀ r ∈ N, (C.getD r ∅).Nonempty
  new_pairwise : ∀ i j, i ≠ j →
    Disjoint (assembledNewClass C N psi X i)
      (assembledNewClass C N psi X j)
  new_subset : ∀ i, assembledNewClass C N psi X i ⊆ A
  new_uncolored : ∀ i, ∀ v ∈ assembledNewClass C N psi X i,
    phi v = none
  Z_X_disjoint : ∀ i, Disjoint (selectedBlockUnion C N psi i) (X i)
  whole_X : ∀ r < Dyadic.levelStart J, ∀ i,
    C.getD r ∅ ⊆ X i ∨ Disjoint (C.getD r ∅) (X i)
  unselected_disjoint_Z : ∀ r < Dyadic.levelStart J, r ∉ N → ∀ i,
    Disjoint (C.getD r ∅) (selectedBlockUnion C N psi i)
  early_disjoint_new : ∀ r < Dyadic.levelStart J0, ∀ i,
    Disjoint (C.getD r ∅) (assembledNewClass C N psi X i)
  quarter_bound : 4 * (Uidx.card - N.card) ≤ 2 ^ ell
  block_incidence : ∀ i,
    incidentCount G (A \ colorClass A phi i) (selectedBlockUnion C N psi i) ≤
      (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card
  removed_incidence : ∀ i,
    incidentCount G ((A \ colorClass A phi i) \ selectedBlockUnion C N psi i)
        (X i) ≤ (k - 1) * (X i).card
  retained_core : ∀ i,
    HasMinDegreeOn G (A \ (colorClass A phi i ∪
      (selectedBlockUnion C N psi i ∪ X i))) k
  future_Z_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      ¬ AdjacentSets G (C.getD r ∅) (selectedBlockUnion C N psi i)
  future_X_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      BlockUncolored phi (C.getD r ∅) →
      Disjoint (C.getD r ∅) (X i) →
        ¬ AdjacentSets G (C.getD r ∅) (X i)

namespace AssemblyInput

variable {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
variable {phi : PartialColoring V k}

abbrev Z (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) : Finset V :=
  selectedBlockUnion C d.N d.psi i

abbrev newClass (d : AssemblyInput G A k C J0 ell J phi)
    (i : Color k) : Finset V := assembledNewClass C d.N d.psi d.X i

abbrev rho (d : AssemblyInput G A k C J0 ell J phi) : PartialColoring V k :=
  assembleColoring phi C d.N d.psi d.X

lemma refines (d : AssemblyInput G A k C J0 ell J phi) :
    Extends phi d.rho := by
  intro v i hvi
  exact assembleColoring_eq_some_of_old hvi

lemma rho_eq_some_iff (d : AssemblyInput G A k C J0 ell J phi)
    {v : V} {i : Color k} :
    d.rho v = some i ↔ phi v = some i ∨ (phi v = none ∧ v ∈ d.newClass i) :=
  assembleColoring_eq_some_iff d.new_pairwise d.new_uncolored

lemma class_eq (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    colorClass A d.rho i = colorClass A phi i ∪ (d.Z i ∪ d.X i) := by
  ext v
  simp only [colorClass, mem_filter, mem_union]
  constructor
  · rintro ⟨hvA, hv⟩
    rw [d.rho_eq_some_iff] at hv
    rcases hv with hold | ⟨_, hnew⟩
    · exact Or.inl ⟨hvA, hold⟩
    · right
      simpa [newClass, assembledNewClass, Z] using hnew
  · rintro (hold | hnew)
    · exact ⟨hold.1, assembleColoring_eq_some_of_old hold.2⟩
    · have hnew' : v ∈ d.newClass i := by
        simpa [newClass, assembledNewClass, Z] using hnew
      have hvA := d.new_subset i hnew'
      have hvnone := d.new_uncolored i v hnew'
      exact ⟨hvA, assembleColoring_eq_some_of_new hvnone d.new_pairwise hnew'⟩

lemma old_disjoint_new (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    Disjoint (colorClass A phi i) (d.newClass i) := by
  rw [Finset.disjoint_left]
  intro v hvold hvnew
  have hold : phi v = some i := (mem_filter.mp hvold).2
  have hnone : phi v = none := d.new_uncolored i v hvnew
  rw [hnone] at hold
  contradiction

lemma class_card (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    (colorClass A d.rho i).card =
      (colorClass A phi i).card + (d.Z i).card + (d.X i).card := by
  rw [d.class_eq i]
  change (colorClass A phi i ∪ d.newClass i).card =
    (colorClass A phi i).card + (d.Z i).card + (d.X i).card
  rw [Finset.card_union_of_disjoint (d.old_disjoint_new i)]
  have hzx : (d.newClass i).card = (d.Z i).card + (d.X i).card := by
    change (d.Z i ∪ d.X i).card = (d.Z i).card + (d.X i).card
    exact Finset.card_union_of_disjoint (d.Z_X_disjoint i)
  omega

lemma support (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ v, v ∉ A → d.rho v = none := by
  intro v hvA
  apply assembleColoring_eq_none_of_old_none_of_new (hphi.support v hvA)
  intro i hvi
  exact hvA (d.new_subset i hvi)

lemma selected_mono (d : AssemblyInput G A k C J0 ell J phi)
    {r : ℕ} (hr : r ∈ d.N) :
    Monochromatic d.rho (C.getD r ∅) (d.psi r) := by
  classical
  have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
    rw [← d.Uidx_eq]
    exact d.N_subset_Uidx hr
  have hrun : BlockUncolored phi (C.getD r ∅) := by
    exact (mem_filter.mp hrU).2
  exact selectedBlock_mono_assembleColoring hr hrun d.new_pairwise

lemma block_status (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ r < Dyadic.levelStart J,
      IsMonochromatic d.rho (C.getD r ∅) ∨ BlockUncolored d.rho (C.getD r ∅) := by
  intro r hr
  rcases hphi.blocks r hr with ⟨i, hi⟩ | hu
  · left
    exact ⟨i, fun v hv ↦ d.refines v i (hi v hv)⟩
  · by_cases hrN : r ∈ d.N
    · exact Or.inl ⟨d.psi r, d.selected_mono hrN⟩
    · by_cases hcontained : ∃ i, C.getD r ∅ ⊆ d.X i
      · obtain ⟨i, hi⟩ := hcontained
        left
        refine ⟨i, ?_⟩
        intro v hv
        apply assembleColoring_eq_some_of_new (hu v hv) d.new_pairwise
        exact mem_union_right _ (hi hv)
      · right
        intro v hv
        apply assembleColoring_eq_none_of_old_none_of_new (hu v hv)
        intro i hvi
        rcases mem_union.mp hvi with hviZ | hviX
        · exact (Finset.disjoint_left.mp (d.unselected_disjoint_Z r hr hrN i)) hv hviZ
        · have hdisj : Disjoint (C.getD r ∅) (d.X i) :=
            (d.whole_X r hr i).resolve_left (fun hsub ↦ hcontained ⟨i, hsub⟩)
          exact (Finset.disjoint_left.mp hdisj) hv hviX

lemma early (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ r < Dyadic.levelStart J0, BlockUncolored d.rho (C.getD r ∅) := by
  intro r hr v hv
  apply assembleColoring_eq_none_of_old_none_of_new (hphi.early r hr v hv)
  intro i hvi
  exact (Finset.disjoint_left.mp (d.early_disjoint_new r hr i)) hv hvi

lemma quarter (d : AssemblyInput G A k C J0 ell J phi) :
    4 * uncoloredBlockCount C d.rho ell ≤ 2 ^ ell := by
  classical
  let R := (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored d.rho (C.getD r ∅)
  have hsub : R ⊆ d.Uidx \ d.N := by
    intro r hr
    have hrdata := mem_filter.mp hr
    have hOld : BlockUncolored phi (C.getD r ∅) :=
      d.refines.blockUncolored hrdata.2
    have hrU : r ∈ d.Uidx := by
      rw [d.Uidx_eq]
      exact mem_filter.mpr ⟨hrdata.1, hOld⟩
    refine mem_sdiff.mpr ⟨hrU, ?_⟩
    intro hrN
    obtain ⟨v, hv⟩ := d.selected_nonempty r hrN
    have hm := d.selected_mono hrN v hv
    have hu := hrdata.2 v hv
    rw [hu] at hm
    contradiction
  have hc : R.card ≤ d.Uidx.card - d.N.card := by
    have := card_le_card hsub
    rwa [card_sdiff_of_subset d.N_subset_Uidx] at this
  have hfinal := (Nat.mul_le_mul_left 4 hc).trans d.quarter_bound
  simpa [R, uncoloredBlockCount] using hfinal

lemma block_count_gain (d : AssemblyInput G A k C J0 ell J phi)
    (i : Color k) :
    monochromaticBlockCount C phi ell i + (d.N.filter fun r ↦ d.psi r = i).card ≤
      monochromaticBlockCount C d.rho (ell + 1) i := by
  classical
  let M := (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    Monochromatic phi (C.getD r ∅) i
  let P := d.N.filter fun r ↦ d.psi r = i
  let M' := (Finset.range (Dyadic.levelStart (ell + 1))).filter fun r ↦
    Monochromatic d.rho (C.getD r ∅) i
  have hdisj : Disjoint M P := by
    rw [Finset.disjoint_left]
    intro r hrM hrP
    have hrM' := by
      simpa only [M] using (mem_filter.mp (show r ∈
        (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
          Monochromatic phi (C.getD r ∅) i from hrM))
    have hrN : r ∈ d.N := (mem_filter.mp hrP).1
    have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
      rw [← d.Uidx_eq]
      exact d.N_subset_Uidx hrN
    have hrlev := (mem_filter.mp hrU).1
    have hrlower := (Dyadic.mem_levelIndices.mp hrlev).1
    exact (Nat.not_lt_of_ge hrlower) (mem_range.mp hrM'.1)
  have hsub : M ∪ P ⊆ M' := by
    intro r hr
    rcases mem_union.mp hr with hrM | hrP
    · have hrM' := by
        simpa only [M] using (mem_filter.mp (show r ∈
          (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
            Monochromatic phi (C.getD r ∅) i from hrM))
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact mem_range.mpr ((mem_range.mp hrM'.1).trans_le
          (Dyadic.levelStart_le_succ ell))
      · intro v hv
        exact d.refines v i (hrM'.2 v hv)
    · have hrP' := mem_filter.mp hrP
      have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
        rw [← d.Uidx_eq]
        exact d.N_subset_Uidx hrP'.1
      have hrlev := (mem_filter.mp hrU).1
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact mem_range.mpr (Dyadic.mem_levelIndices.mp hrlev).2
      · simpa [hrP'.2] using d.selected_mono hrP'.1
  have hcard : M.card + P.card ≤ M'.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact card_le_card hsub
  simpa [M, P, M', monochromaticBlockCount] using hcard

lemma future_anticomplete (d : AssemblyInput G A k C J0 ell J phi) :
    ∀ r, Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J →
      BlockUncolored d.rho (C.getD r ∅) → ∀ i,
        ¬ AdjacentSets G (C.getD r ∅) (d.Z i ∪ d.X i) := by
  intro r hr hJ hrun i hadj
  have hrunOld : BlockUncolored phi (C.getD r ∅) :=
    d.refines.blockUncolored hrun
  have hdisjX : Disjoint (C.getD r ∅) (d.X i) := by
    rcases d.whole_X r hJ i with hsub | hdisj
    · obtain ⟨v, hv⟩ : (C.getD r ∅).Nonempty := by
        -- Future blocks that remain uncoloured must be nonempty.  This follows
        -- already if one supplies `selected_nonempty` only on `N`; hence this
        -- fact is requested locally from `hadj` below when needed.
        obtain ⟨v, hv, w, hw, hvw⟩ := hadj
        exact ⟨v, hv⟩
      have hm : d.rho v = some i :=
        assembleColoring_eq_some_of_new (hrunOld v hv) d.new_pairwise
          (mem_union_right _ (hsub hv))
      rw [hrun v hv] at hm
      contradiction
    · exact hdisj
  obtain ⟨v, hv, w, hw, hvw⟩ := hadj
  rcases mem_union.mp hw with hwZ | hwX
  · exact d.future_Z_anticomplete r hr hJ i ⟨v, hv, w, hwZ, hvw⟩
  · exact d.future_X_anticomplete r hr hJ i hrunOld hdisjX
      ⟨v, hv, w, hwX, hvw⟩

/-- The fully assembled successor datum.  This is the reusable endpoint for
the nontrivial successor construction. -/
noncomputable def toSuccessorData
    (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    SuccessorData G A k C J0 ell J phi d.rho where
  Z := d.Z
  X := d.X
  newBlockCount := fun i ↦ (d.N.filter fun r ↦ d.psi r = i).card
  refines := d.refines
  support := d.support hphi
  block_status := d.block_status hphi
  class_eq := d.class_eq
  class_card := d.class_card
  block_incidence := d.block_incidence
  removed_incidence := d.removed_incidence
  block_count_gain := d.block_count_gain
  retained_core := fun i ↦ by simpa [d.class_eq i] using d.retained_core i
  early := d.early hphi
  quarter := d.quarter
  future_anticomplete := d.future_anticomplete

end AssemblyInput

end


namespace PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def chooseMinSubset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : Finset α :=
  Classical.choose (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))

lemma chooseMinSubset_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : chooseMinSubset s d ⊆ s :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))).1

lemma card_chooseMinSubset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : (chooseMinSubset s d).card = min s.card d :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))).2

noncomputable def adjacentBlockIndices (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (s : V) : Finset ℕ := by
  classical
  exact Uidx.filter fun r => AdjacentSets G {s} (C.getD r ∅)

noncomputable def selectedScope (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V)
    (C : List (Finset V)) (Uidx : Finset ℕ) (k : ℕ) (s : V) : Finset ℕ := by
  classical
  exact chooseMinSubset (adjacentBlockIndices G C Uidx s)
    (k + 1 - degreeOn G H s)

lemma selectedScope_subset_adjacentBlockIndices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    selectedScope G H C Uidx k s ⊆ adjacentBlockIndices G C Uidx s := by
  classical
  exact chooseMinSubset_subset _ _

lemma selectedScope_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    selectedScope G H C Uidx k s ⊆ Uidx := by
  classical
  apply (selectedScope_subset_adjacentBlockIndices G H C Uidx k s).trans
  intro r hr
  exact (Finset.mem_filter.mp hr).1

lemma mem_selectedScope_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) {r : ℕ}
    (hr : r ∈ selectedScope G H C Uidx k s) :
    AdjacentSets G {s} (C.getD r ∅) := by
  classical
  have hr' := selectedScope_subset_adjacentBlockIndices G H C Uidx k s hr
  change r ∈ Uidx.filter (fun r => AdjacentSets G {s} (C.getD r ∅)) at hr'
  exact (Finset.mem_filter.mp hr').2

lemma card_selectedScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    (selectedScope G H C Uidx k s).card =
      min (adjacentBlockIndices G C Uidx s).card (k + 1 - degreeOn G H s) := by
  classical
  exact card_chooseMinSubset _ _

lemma selectedScope_eq_adjacent_of_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V)
    (hcard : (adjacentBlockIndices G C Uidx s).card ≤
      k + 1 - degreeOn G H s) :
    selectedScope G H C Uidx k s = adjacentBlockIndices G C Uidx s := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (selectedScope_subset_adjacentBlockIndices G H C Uidx k s)
  rw [card_selectedScope, Nat.min_eq_left hcard]

noncomputable def selectedVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun s => (adjacentBlockIndices G C Uidx s).Nonempty

lemma selectedVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (S : Finset V) : selectedVertices G C Uidx S ⊆ S := by
  classical
  exact Finset.filter_subset _ _

lemma certificate_deficit_sum_le_twenty_four
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.sum (fun s => k - degreeOn G H s) ≤ 24 * Uidx.card := by
  have h := E.deficit_le
  have hcast : ((E.S.sum (fun s => k - degreeOn G H s) : ℕ) : ℤ) ≤
      ((24 * Uidx.card : ℕ) : ℤ) := by
    calc
      ((E.S.sum (fun s => k - degreeOn G H s) : ℕ) : ℤ) ≤
          2 * shortage k G H := h
      _ ≤ 2 * ((12 * Uidx.card : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hshort (by norm_num)
      _ = ((24 * Uidx.card : ℕ) : ℤ) := by push_cast; ring
  exact_mod_cast hcast

lemma certificate_card_le_twenty_four
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.card ≤ 24 * Uidx.card := by
  calc
    E.S.card = E.S.sum (fun _ => 1) := by simp
    _ ≤ E.S.sum (fun s => k - degreeOn G H s) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsLow := E.S_subset_low hs
      rw [mem_lowVertices] at hsLow
      omega
    _ ≤ 24 * Uidx.card := certificate_deficit_sum_le_twenty_four E Uidx hshort

lemma certificate_scope_budget
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.sum (fun s => k + 1 - degreeOn G H s) ≤ 48 * Uidx.card := by
  have hdef := certificate_deficit_sum_le_twenty_four E Uidx hshort
  have hcard := certificate_card_le_twenty_four E Uidx hk hshort
  have heq : E.S.sum (fun s => k + 1 - degreeOn G H s) =
      E.S.sum (fun s => k - degreeOn G H s) + E.S.card := by
    calc
      E.S.sum (fun s => k + 1 - degreeOn G H s) =
          E.S.sum (fun s => (k - degreeOn G H s) + 1) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsLow := E.S_subset_low hs
        rw [mem_lowVertices] at hsLow
        omega
      _ = E.S.sum (fun s => k - degreeOn G H s) +
          E.S.sum (fun _ => 1) := Finset.sum_add_distrib
      _ = E.S.sum (fun s => k - degreeOn G H s) + E.S.card := by simp
  rw [heq]
  omega

lemma selectedScope_total_le
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    (selectedVertices G C Uidx E.S).sum
      (fun s => (selectedScope G H C Uidx k s).card) ≤ 48 * Uidx.card := by
  calc
    (selectedVertices G C Uidx E.S).sum
        (fun s => (selectedScope G H C Uidx k s).card) ≤
        (selectedVertices G C Uidx E.S).sum
          (fun s => k + 1 - degreeOn G H s) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [card_selectedScope]
      exact Nat.min_le_right _ _
    _ ≤ E.S.sum (fun s => k + 1 - degreeOn G H s) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (selectedVertices_subset G C Uidx E.S) (by simp)
    _ ≤ 48 * Uidx.card := certificate_scope_budget E Uidx hk hshort

def scopeFrequency (S : Finset V) (scope : V -> Finset ℕ) (r : ℕ) : ℕ :=
  (S.filter fun s => r ∈ scope s).card

def popularIndices (Uidx : Finset ℕ) (S : Finset V)
    (scope : V -> Finset ℕ) : Finset ℕ :=
  Uidx.filter fun r => 200 < scopeFrequency S scope r

lemma sum_scopeFrequency_eq
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx) :
    Uidx.sum (scopeFrequency S scope) = S.sum fun s => (scope s).card := by
  induction S using Finset.induction_on with
  | empty => simp [scopeFrequency]
  | @insert s S hs ih =>
      have hscopeS : ∀ x ∈ S, scope x ⊆ Uidx := by
        intro x hx
        exact hscope x (Finset.mem_insert_of_mem hx)
      have hscopes : scope s ⊆ Uidx := hscope s (Finset.mem_insert_self s S)
      have hfreq : ∀ r,
          scopeFrequency (insert s S) scope r =
            scopeFrequency S scope r + if r ∈ scope s then 1 else 0 := by
        intro r
        by_cases hrs : r ∈ scope s
        · rw [scopeFrequency, scopeFrequency, Finset.filter_insert, if_pos hrs,
            Finset.card_insert_of_notMem]
          · simp only [if_pos hrs]
          · simp [hs]
        · rw [scopeFrequency, scopeFrequency, Finset.filter_insert, if_neg hrs]
          simp only [if_neg hrs, add_zero]
      have hindicator : Uidx.sum (fun r => if r ∈ scope s then 1 else 0) =
          (scope s).card := by
        rw [← Finset.sum_filter]
        have hfilter : Uidx.filter (fun r => r ∈ scope s) = scope s := by
          ext r
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hscopes h, h⟩
        rw [hfilter]
        simp
      rw [Finset.sum_insert hs, ← ih hscopeS]
      calc
        Uidx.sum (scopeFrequency (insert s S) scope) =
            Uidx.sum (fun r => scopeFrequency S scope r +
              if r ∈ scope s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hfreq r
        _ = Uidx.sum (scopeFrequency S scope) +
            Uidx.sum (fun r => if r ∈ scope s then 1 else 0) :=
          Finset.sum_add_distrib
        _ = (scope s).card + Uidx.sum (scopeFrequency S scope) := by
          rw [hindicator, Nat.add_comm]

lemma popular_double_count
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx) :
    201 * (popularIndices Uidx S scope).card ≤ S.sum fun s => (scope s).card := by
  rw [← sum_scopeFrequency_eq Uidx S scope hscope]
  calc
    201 * (popularIndices Uidx S scope).card =
        (popularIndices Uidx S scope).sum (fun _ => 201) := by
      simp [Nat.mul_comm]
    _ ≤ (popularIndices Uidx S scope).sum (scopeFrequency S scope) := by
      apply Finset.sum_le_sum
      intro r hr
      have := (Finset.mem_filter.mp hr).2
      omega
    _ ≤ Uidx.sum (scopeFrequency S scope) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (by simp)

lemma four_mul_popular_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx)
    (hbudget : S.sum (fun s => (scope s).card) ≤ 48 * Uidx.card) :
    4 * (popularIndices Uidx S scope).card ≤ Uidx.card := by
  have hdc := (popular_double_count Uidx S scope hscope).trans hbudget
  omega

lemma selectedPopular_quarter
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    let S' := selectedVertices G C Uidx E.S
    let scope := fun s : V => selectedScope G H C Uidx k s
    4 * (popularIndices Uidx S' scope).card ≤ Uidx.card := by
  classical
  dsimp only
  apply four_mul_popular_le
  · intro s hs
    exact selectedScope_subset G H C Uidx k s
  · exact selectedScope_total_le E C Uidx hk hshort

lemma nonpopular_frequency_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ) {r : ℕ}
    (hrU : r ∈ Uidx) (hr : r ∉ popularIndices Uidx S scope) :
    scopeFrequency S scope r ≤ 200 := by
  simp only [popularIndices, Finset.mem_filter, hrU, true_and] at hr
  omega

/-! A fully specialized interface to the existing finite greedy theorem. -/

def nonpopularIndices (Uidx : Finset ℕ) (S : Finset V)
    (scope : V -> Finset ℕ) : Finset ℕ :=
  Uidx \ popularIndices Uidx S scope

noncomputable def restrictedScope
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (s : {s // s ∈ S}) : Finset {r // r ∈ nonpopularIndices Uidx S scope} := by
  classical
  exact Finset.univ.filter fun r => (r : ℕ) ∈ scope (s : V)

noncomputable def neighborColorSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) : Finset (Color k) := by
  classical
  exact Finset.univ.filter fun i => ∃ v ∈ A, G.Adj s v ∧ phi v = some i

noncomputable def neighborColorList (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) : Finset (Color k) :=
  chooseMinSubset (neighborColorSet G A phi s) k

lemma neighborColorList_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) :
    neighborColorList G A phi s ⊆ neighborColorSet G A phi s :=
  chooseMinSubset_subset _ _

lemma neighborColorList_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) :
    (neighborColorList G A phi s).card ≤ k := by
  rw [neighborColorList, card_chooseMinSubset]
  exact Nat.min_le_right _ _

lemma restrictedScope_card_le_scope
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (s : {s // s ∈ S}) :
    (restrictedScope Uidx S scope s).card ≤ (scope (s : V)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun r :
    {r // r ∈ nonpopularIndices Uidx S scope} => (r : ℕ))
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro r hr q hq heq
    exact Subtype.ext heq

lemma restrictedScope_frequency_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx)
    (r : {r // r ∈ nonpopularIndices Uidx S scope}) :
    ((Finset.univ.filter fun s : {s // s ∈ S} =>
      r ∈ restrictedScope Uidx S scope s).card) ≤ 200 := by
  classical
  have hcard :
      (Finset.univ.filter fun s : {s // s ∈ S} =>
        r ∈ restrictedScope Uidx S scope s).card ≤
      (S.filter fun s => (r : ℕ) ∈ scope s).card := by
    apply Finset.card_le_card_of_injOn (fun s : {s // s ∈ S} => (s : V))
    · intro s hs
      have hsScope : (r : ℕ) ∈ scope (s : V) := by
        have hrRestricted := (Finset.mem_filter.mp hs).2
        simpa only [restrictedScope, Finset.mem_filter, Finset.mem_univ, true_and]
          using hrRestricted
      exact Finset.mem_filter.mpr ⟨s.property, hsScope⟩
    · intro s hs q hq heq
      exact Subtype.ext heq
  have hrData := Finset.mem_sdiff.mp r.property
  exact hcard.trans (nonpopular_frequency_le Uidx S scope hrData.1 hrData.2)

theorem exists_selected_scope_coloring
    {H A : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (phi : PartialColoring V k) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    let S' := selectedVertices G C Uidx E.S
    let scope := fun s : V => selectedScope G H C Uidx k s
    let NP := nonpopularIndices Uidx S' scope
    ∃ color : {r // r ∈ NP} -> Color k,
      (∀ s : {s // s ∈ S'},
        Set.InjOn color (restrictedScope Uidx S' scope s :
          Set {r // r ∈ NP})) ∧
      (∀ s : {s // s ∈ S'}, ∀ r ∈ restrictedScope Uidx S' scope s,
        color r ∉ neighborColorList G A phi (s : V)) := by
  classical
  dsimp only
  let S' := selectedVertices G C Uidx E.S
  let scope : V -> Finset ℕ := fun s => selectedScope G H C Uidx k s
  let NP := nonpopularIndices Uidx S' scope
  let ScopeT := {s // s ∈ S'}
  let ItemT := {r // r ∈ NP}
  let scopeT : ScopeT -> Finset ItemT := fun s => restrictedScope Uidx S' scope s
  let avoidT : ScopeT -> Finset (Color k) :=
    fun s => neighborColorList G A phi (s : V)
  have hscopeSub : ∀ s ∈ S', scope s ⊆ Uidx := by
    intro s hs
    exact selectedScope_subset G H C Uidx k s
  have hfrequency : ∀ r : ItemT,
      (Finset.univ.filter fun s : ScopeT => r ∈ scopeT s).card ≤ 200 := by
    intro r
    exact restrictedScope_frequency_le Uidx S' scope hscopeSub r
  have hscopeCard : ∀ s : ScopeT, (scopeT s).card ≤ k + 1 := by
    intro s
    calc
      (scopeT s).card ≤ (scope (s : V)).card :=
        restrictedScope_card_le_scope Uidx S' scope s
      _ ≤ k + 1 := by
        dsimp [scope]
        rw [card_selectedScope]
        exact (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have havoid : ∀ s : ScopeT, (avoidT s).card ≤ k := by
    intro s
    exact neighborColorList_card_le G A phi (s : V)
  have hkpos : 0 < k := by omega
  simpa [S', scope, NP, ScopeT, ItemT, scopeT, avoidT] using
    (exists_erdos814_scope_coloring (Item := ItemT) (Scope := ScopeT)
      hkpos scopeT avoidT hfrequency hscopeCard havoid)


end PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma residual_card_add_earlyMass_le
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    (deficitResidual A C phi (ell + 1)).card +
        Dyadic.retainedMass C J0 ≤ A.card := by
  classical
  let R := Finset.range (Dyadic.levelStart J0)
  let block : ℕ → Finset V := fun r ↦ C.getD r ∅
  let E := R.biUnion block
  let H := deficitResidual A C phi (ell + 1)
  have hJ0succ : J0 ≤ ell + 1 := hJ0ell.trans (Nat.le_succ ell)
  have hRprefix : R ⊆ uncoloredPrefixIndices C phi (ell + 1) := by
    intro r hr
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hr
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (hr0.trans_le (Dyadic.levelStart_mono hJ0succ)),
      hphi.early r hr0⟩
  have hEprefix : E ⊆ uncoloredPrefixUnion C phi (ell + 1) := by
    intro v hv
    rw [show E = R.biUnion block by rfl, mem_biUnion] at hv
    obtain ⟨r, hrR, hvr⟩ := hv
    rw [uncoloredPrefixUnion, mem_biUnion]
    exact ⟨r, hRprefix hrR, hvr⟩
  have hEA : E ⊆ A := by
    intro v hv
    rw [show E = R.biUnion block by rfl, mem_biUnion] at hv
    obtain ⟨r, hrR, hvr⟩ := hv
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hrR
    exact S.block_subset r
      (hr0.trans_le (Dyadic.levelStart_mono S.hJ)) hvr
  have hHA : H ⊆ A := sdiff_subset
  have hdisj : Disjoint H E := by
    rw [Finset.disjoint_left]
    intro v hvH hvE
    have hvprefix := hEprefix hvE
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
  have hpair : (R : Set ℕ).PairwiseDisjoint block := by
    intro r hr s hs hrs
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hr
    have hs0 : s < Dyadic.levelStart J0 := mem_range.mp hs
    exact S.blocks_disjoint r
      (hr0.trans_le (Dyadic.levelStart_mono S.hJ)) s
      (hs0.trans_le (Dyadic.levelStart_mono S.hJ)) hrs
  have hEcard : E.card = Dyadic.retainedMass C J0 := by
    rw [show E = R.biUnion block by rfl, Finset.card_biUnion hpair]
    rfl
  have hunion : H ∪ E ⊆ A := union_subset hHA hEA
  have hc := card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, hEcard] at hc
  exact hc

lemma noCore_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    ∀ X : Finset V, X ⊆ deficitResidual A C phi (ell + 1) →
      ¬ HasMinDegreeOn G X k := by
  intro X hXH hmin
  apply S.noSmallCore
  refine ⟨X, ?_⟩
  have hXA : X ⊆ A := hXH.trans sdiff_subset
  have hmass := residual_card_add_earlyMass_le S hphi hJ0ell
  have hXcard : X.card ≤ (deficitResidual A C phi (ell + 1)).card :=
    card_le_card hXH
  let q : ℕ := 100 * k
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Nat.mul_pos (by decide) (lt_of_lt_of_le (by decide) S.hk)
  have hsmallq : q * X.card ≤ (q - 1) * A.card := by
    have hearly := S.early_mass
    have hqX : q * X.card ≤ q * (deficitResidual A C phi (ell + 1)).card :=
      Nat.mul_le_mul_left q hXcard
    have hmul := Nat.mul_le_mul_left q hmass
    rw [Nat.mul_add] at hmul
    have hchain : q * (deficitResidual A C phi (ell + 1)).card + A.card ≤
        q * A.card := by
      calc
        q * (deficitResidual A C phi (ell + 1)).card + A.card ≤
            q * (deficitResidual A C phi (ell + 1)).card +
              q * Dyadic.retainedMass C J0 := by
                exact Nat.add_le_add_left (by simpa [q] using hearly) _
        _ ≤ q * A.card := hmul
    have hdecomp : q * A.card = (q - 1) * A.card + A.card := by
      calc
        q * A.card = ((q - 1) + 1) * A.card := by rw [Nat.sub_add_cancel hq]
        _ = (q - 1) * A.card + A.card := by ring
    rw [hdecomp] at hchain
    omega
  have hqD : q ≤ uniformDen k := by
    have hk0 : k ≠ 0 := by omega
    have hkk : 1 ≤ k * k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hk0 hk0)
    have hkpow : k ≤ k ^ 3 := by
      calc
        k = k * 1 := by simp
        _ ≤ k * (k * k) := Nat.mul_le_mul_left k hkk
        _ = k ^ 3 := by ring
    dsimp [q]
    simp only [uniformDen]
    calc
      100 * k ≤ 10000 * k := Nat.mul_le_mul_right k (by decide)
      _ ≤ 10000 * k ^ 3 := Nat.mul_le_mul_left 10000 hkpow
  exact (IsSmallCoreOn.mono_den hq hqD ⟨hXA, hmin, hsmallq⟩)

theorem exists_residualExtensionCertificate
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    Nonempty (ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi)) :=
  exists_extensionCertificate (residualProtectedFamily S hphi) S.hk
    (noCore_deficitResidual S hphi hJ0ell)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private lemma sum_scopeNeed_certificate_le'
    {H : Finset V} {k u : ℕ} {CF : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k CF) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * u : ℕ)) :
    ∑ s ∈ E.S, (k + 1 - degreeOn G H s) ≤ 48 * u := by
  have hdeg : ∀ s ∈ E.S, degreeOn G H s ≤ k - 1 := by
    intro s hs
    exact (mem_lowVertices.mp (E.S_subset_low hs)).2
  have hsplit :
      (∑ s ∈ E.S, (k + 1 - degreeOn G H s)) =
        E.S.card + ∑ s ∈ E.S, (k - degreeOn G H s) := by
    calc
      (∑ s ∈ E.S, (k + 1 - degreeOn G H s)) =
          ∑ s ∈ E.S, (1 + (k - degreeOn G H s)) := by
            apply Finset.sum_congr rfl
            intro s hs
            have := hdeg s hs
            omega
      _ = E.S.card + ∑ s ∈ E.S, (k - degreeOn G H s) := by
            simp [Finset.sum_add_distrib]
  have hcard : E.S.card ≤ ∑ s ∈ E.S, (k - degreeOn G H s) := by
    calc
      E.S.card = ∑ _s ∈ E.S, 1 := by simp
      _ ≤ ∑ s ∈ E.S, (k - degreeOn G H s) := by
        apply Finset.sum_le_sum
        intro s hs
        have := hdeg s hs
        omega
  have hdef := E.deficit_le
  have hdefnonneg : 0 ≤ shortage k G H := by
    have hsum_nonneg :
        (0 : ℤ) ≤ ((E.S.sum fun s ↦ k - degreeOn G H s : ℕ) : ℤ) := by omega
    omega
  have hgoalZ :
      (((∑ s ∈ E.S, (k + 1 - degreeOn G H s)) : ℕ) : ℤ) ≤
        ((48 * u : ℕ) : ℤ) := by
    rw [hsplit, Nat.cast_add]
    have hcardZ :
        (E.S.card : ℤ) ≤
          ((∑ s ∈ E.S, (k - degreeOn G H s) : ℕ) : ℤ) := by
      exact_mod_cast hcard
    have hshortZ : shortage k G H ≤ (12 * u : ℕ) := hshort
    omega
  exact_mod_cast hgoalZ

structure GreedyLevelData
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A H : Finset V) (k : ℕ) (C : List (Finset V))
    (phi : PartialColoring V k) (Eset : Finset V) (ell : ℕ) where
  Uidx : Finset ℕ
  active : Finset V
  scope : V → Finset ℕ
  N : Finset ℕ
  psi : ℕ → Color k
  Uidx_eq : Uidx = uncoloredCurrentIndices C phi ell
  active_eq : active = PopularScratch.selectedVertices G C Uidx Eset
  scope_eq : scope = fun s ↦ PopularScratch.selectedScope G H C Uidx k s
  N_eq : N = PopularScratch.nonpopularIndices Uidx active scope
  N_subset : N ⊆ Uidx
  quarter : 4 * (Uidx.card - N.card) ≤ 2 ^ ell
  injective_scope : ∀ s ∈ active, ∀ r ∈ scope s, r ∈ N →
    ∀ q ∈ scope s, q ∈ N → psi r = psi q → r = q
  avoids : ∀ s ∈ active, ∀ r ∈ scope s, r ∈ N →
    psi r ∉ PopularScratch.neighborColorList G A phi s

theorem exists_greedyLevelData
    {A H : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {CF : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k CF)
    (hk : 2 ≤ k)
    (hshort : shortage k G H ≤
      (12 * uncoloredBlockCount C phi ell : ℕ)) :
    Nonempty (GreedyLevelData G A H k C phi E.S ell) := by
  classical
  let U := currentUncoloredIndices C phi ell
  let Sact := PopularScratch.selectedVertices G C U E.S
  let scope : V → Finset ℕ := fun s ↦
    PopularScratch.selectedScope G H C U k s
  let N := PopularScratch.nonpopularIndices U Sact scope
  have hshortU : shortage k G H ≤ (12 * U.card : ℕ) := by
    simpa [U] using hshort
  obtain ⟨color, hinj, havoid⟩ :=
    PopularScratch.exists_selected_scope_coloring
      (G := G) E C U phi hk hshortU
  let fallback : Color k := ⟨0, by
    have hkpos : 0 < k := by omega
    exact Nat.mul_pos (by decide) hkpos⟩
  let psi : ℕ → Color k := fun r ↦
    if hr : r ∈ N then color ⟨r, hr⟩ else fallback
  have hNsub : N ⊆ U := sdiff_subset
  have hpopular := PopularScratch.selectedPopular_quarter
    (G := G) E C U hk hshortU
  have hquarter : 4 * (U.card - N.card) ≤ 2 ^ ell := by
    have hNcard : U.card - N.card =
        (PopularScratch.popularIndices U Sact scope).card := by
      change U.card - (U \ PopularScratch.popularIndices U Sact scope).card =
        (PopularScratch.popularIndices U Sact scope).card
      unfold PopularScratch.popularIndices
      have hpopularCard :
          (U.filter fun r ↦ 200 < PopularScratch.scopeFrequency Sact scope r).card ≤
            U.card := card_le_card (Finset.filter_subset _ _)
      rw [card_sdiff_of_subset (Finset.filter_subset _ _)]
      omega
    rw [hNcard]
    have hpopU : 4 * (PopularScratch.popularIndices U Sact scope).card ≤ U.card := by
      simpa [Sact, scope] using hpopular
    have hUlevel : U.card ≤ 2 ^ ell := by
      dsimp [U]
      rw [card_currentUncoloredIndices]
      unfold uncoloredBlockCount
      simpa only [Dyadic.card_levelIndices] using
        card_le_card (Finset.filter_subset
          (fun r ↦ BlockUncolored phi (C.getD r ∅)) (Dyadic.levelIndices ell))
    exact hpopU.trans hUlevel
  refine ⟨{
    Uidx := U
    active := Sact
    scope := scope
    N := N
    psi := psi
    Uidx_eq := rfl
    active_eq := rfl
    scope_eq := rfl
    N_eq := rfl
    N_subset := hNsub
    quarter := hquarter
    injective_scope := ?_
    avoids := ?_ }⟩
  · intro s hs r hrs hrN q hqs hqN heq
    let ss : {s // s ∈ Sact} := ⟨s, hs⟩
    let rr : {r // r ∈ N} := ⟨r, hrN⟩
    let qq : {r // r ∈ N} := ⟨q, hqN⟩
    have hrr : rr ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [rr, ss, PopularScratch.restrictedScope, hrs]
    have hqq : qq ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [qq, ss, PopularScratch.restrictedScope, hqs]
    have hc : color rr = color qq := by
      simpa [psi, hrN, hqN, rr, qq] using heq
    exact congrArg Subtype.val (hinj ss hrr hqq hc)
  · intro s hs r hrs hrN
    let ss : {s // s ∈ Sact} := ⟨s, hs⟩
    let rr : {r // r ∈ N} := ⟨r, hrN⟩
    have hrr : rr ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [rr, ss, PopularScratch.restrictedScope, hrs]
    simpa [psi, hrN, rr, ss] using havoid ss rr hrr

end


namespace ExtensionApplyScratch

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Selected current-level blocks carrying one fixed colour. -/
def redBlockIndices (U : Finset ℕ) (blockColor : ℕ → Option I)
    (i : I) : Finset ℕ :=
  U.filter fun r ↦ blockColor r = some i

/-- The union `Z_i` of the selected current-level blocks of colour `i`. -/
def redBlockUnion (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) : Finset V :=
  (redBlockIndices U blockColor i).biUnion fun r ↦ C.getD r ∅

/-- An edge to `Z_i` selects an actual current-level block of colour `i`. -/
lemma adjacent_block_of_adjacent_redBlockUnion
    (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) {v : V}
    (h : AdjacentSets G {v} (redBlockUnion C U blockColor i)) :
    ∃ r ∈ U, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  rw [redBlockUnion, mem_biUnion] at hy
  obtain ⟨r, hr, hyr⟩ := hy
  rw [redBlockIndices, mem_filter] at hr
  exact ⟨r, hr.1, hr.2, v, by simp, y, hyr, hxy⟩

/-- A vertex which becomes low only after deleting `Z` must see `Z`. -/
lemma adjacent_of_low_after_delete
    {B Z : Finset V} {k : ℕ} {v : V}
    (hk : 2 ≤ k) (hZB : Z ⊆ B) (hv : v ∈ B \ Z)
    (hhigh : k ≤ degreeOn G B v)
    (hlow : degreeOn G (B \ Z) v ≤ k - 1) :
    AdjacentSets G {v} Z := by
  by_contra hnot
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hnot
  rw [heq] at hlow
  omega

/-- Semantic form of (5.27). -/
lemma lowVertices_after_red_delete_subset_residual
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix_anti : ∀ v ∈ P, ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · exact hprefix_anti v hvP hadj

/-- Variant of the preceding lemma which permits `P` to contain the deleted
set `Z` itself.  This is the form needed for the exact residual (5.13),
which deletes the whole current level, including the red blocks. -/
lemma lowVertices_after_red_delete_subset_residual'
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix : ∀ v ∈ P,
      v ∈ Z ∨ ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hvnotZ : v ∉ Z := (mem_sdiff.mp hvdata.1).2
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · rcases hprefix v hvP with hvZ | hanti
    · exact hvnotZ hvZ
    · exact hanti hadj

/-- Concrete (5.27) for the current dyadic level.  Here `N` is any set of
selected uncoloured current-level blocks (in the application, the
non-popular ones), and `blockColor` is `none` off `N`. -/
lemma lowVertices_currentColor_subset_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    lowVertices G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k ⊆
      deficitResidual A C phi ell := by
  classical
  let Z := redBlockUnion C N blockColor i
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have selected_data : ∀ r, r ∈ N →
      Dyadic.levelStart ell ≤ r ∧
      r < Dyadic.levelStart (ell + 1) ∧
      BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    have hr' := hN hr
    rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hr'
    exact ⟨hr'.1.1, hr'.1.2, hr'.2⟩
  have selected_lt_J : ∀ r, r ∈ N → r < Dyadic.levelStart J := by
    intro r hr
    exact (selected_data r hr).2.1.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hZA : Z ⊆ A \ colorClass A phi i := by
    intro v hv
    change v ∈ redBlockUnion C N blockColor i at hv
    rw [redBlockUnion, mem_biUnion] at hv
    obtain ⟨r, hr, hvr⟩ := hv
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hrlt := selected_lt_J r hrN
    have hvA := S.block_subset r hrlt hvr
    refine mem_sdiff.mpr ⟨hvA, ?_⟩
    intro hvclass
    have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
    have hvnone := (selected_data r hrN).2.2 v hvr
    rw [hvnone] at hvcolor
    contradiction
  have hneigh : ∀ v ∈ A, AdjacentSets G {v} Z → phi v = none := by
    intro v hvA hvZ
    obtain ⟨r, hrN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hd := selected_data r hrN
    have hfut := hphi.future r hd.1 (selected_lt_J r hrN) hd.2.2
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact hfut y hy v hvA hxy.symm
  have hprefix : ∀ v ∈ uncoloredPrefixUnion C phi ell,
      ¬ AdjacentSets G {v} Z := by
    intro v hvP hvZ
    rw [uncoloredPrefixUnion, mem_biUnion] at hvP
    obtain ⟨r, hrP, hvr⟩ := hvP
    have hrP' : r ∈ Finset.range (Dyadic.levelStart ell) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hrP
    have hrltell : r < Dyadic.levelStart ell := mem_range.mp hrP'.1
    obtain ⟨s, hsN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hsdata := selected_data s hsN
    have hrs : r ≠ s := by omega
    have hrJ : r < Dyadic.levelStart J :=
      hrltell.trans_le (Dyadic.levelStart_mono hellJ.le)
    have hsJ := selected_lt_J s hsN
    apply S.blocks_anticomplete r hrJ s hsJ hrs
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact ⟨v, hvr, y, hy, hxy⟩
  have hres := lowVertices_after_red_delete_subset_residual
    (G := G) phi S.hk hZA (hphi.minDegree i) hneigh hprefix
  simpa [Z, deficitResidual] using hres

/-- Exact (5.27): the residual deletes all uncoloured blocks through the
current level, so its `deficitResidual` index is `ell + 1`. -/
lemma lowVertices_currentColor_subset_deficitResidual_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    lowVertices G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k ⊆
      deficitResidual A C phi (ell + 1) := by
  classical
  let Z := redBlockUnion C N blockColor i
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have selected_data : ∀ r, r ∈ N →
      Dyadic.levelStart ell ≤ r ∧
      r < Dyadic.levelStart (ell + 1) ∧
      BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    have hr' := hN hr
    rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hr'
    exact ⟨hr'.1.1, hr'.1.2, hr'.2⟩
  have selected_lt_J : ∀ r, r ∈ N → r < Dyadic.levelStart J := by
    intro r hr
    exact (selected_data r hr).2.1.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hZA : Z ⊆ A \ colorClass A phi i := by
    intro v hv
    change v ∈ redBlockUnion C N blockColor i at hv
    rw [redBlockUnion, mem_biUnion] at hv
    obtain ⟨r, hr, hvr⟩ := hv
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hvA := S.block_subset r (selected_lt_J r hrN) hvr
    refine mem_sdiff.mpr ⟨hvA, ?_⟩
    intro hvclass
    have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
    have hvnone := (selected_data r hrN).2.2 v hvr
    rw [hvnone] at hvcolor
    contradiction
  have hneigh : ∀ v ∈ A, AdjacentSets G {v} Z → phi v = none := by
    intro v hvA hvZ
    obtain ⟨r, hrN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hd := selected_data r hrN
    have hfut := hphi.future r hd.1 (selected_lt_J r hrN) hd.2.2
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact hfut y hy v hvA hxy.symm
  have hprefix : ∀ v ∈ uncoloredPrefixUnion C phi (ell + 1),
      v ∈ Z ∨ ¬ AdjacentSets G {v} Z := by
    intro v hvP
    rw [uncoloredPrefixUnion, mem_biUnion] at hvP
    obtain ⟨r, hrP, hvr⟩ := hvP
    have hrP' : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hrP
    by_cases hvZ : v ∈ Z
    · exact Or.inl hvZ
    · right
      intro hadj
      obtain ⟨s, hsN, hcolor, hadjS⟩ :=
        adjacent_block_of_adjacent_redBlockUnion C N blockColor i hadj
      have hrs : r ≠ s := by
        intro hrs
        subst s
        apply hvZ
        change v ∈ redBlockUnion C N blockColor i
        rw [redBlockUnion, mem_biUnion]
        refine ⟨r, ?_, hvr⟩
        rw [redBlockIndices, mem_filter]
        exact ⟨hsN, hcolor⟩
      have hrJ : r < Dyadic.levelStart J :=
        (mem_range.mp hrP'.1).trans_le (Dyadic.levelStart_mono hellSuccJ)
      have hsJ := selected_lt_J s hsN
      apply S.blocks_anticomplete r hrJ s hsJ hrs
      rcases hadjS with ⟨x, hx, y, hy, hxy⟩
      have hxv : x = v := by simpa using hx
      subst x
      exact ⟨v, hvr, y, hy, hxy⟩
  have hres := lowVertices_after_red_delete_subset_residual'
    (G := G) phi S.hk hZA (hphi.minDegree i) hneigh hprefix
  simpa [Z, deficitResidual] using hres

/-- The selected current-level union is part of the prefix deleted in the
exact deficit residual. -/
lemma redBlockUnion_subset_uncoloredPrefixUnion_succ
    {k ell : ℕ} {C : List (Finset V)} {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option I) (i : I) :
    redBlockUnion C N blockColor i ⊆
      uncoloredPrefixUnion C phi (ell + 1) := by
  classical
  intro v hv
  rw [redBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN : r ∈ N := (mem_filter.mp hr).1
  have hrU := hN hrN
  rw [uncoloredCurrentIndices, mem_filter] at hrU
  rw [uncoloredPrefixUnion, mem_biUnion]
  refine ⟨r, ?_, hvr⟩
  rw [uncoloredPrefixIndices, mem_filter]
  exact ⟨mem_range.mpr ((Dyadic.mem_levelIndices.mp hrU.1).2), hrU.2⟩

/-- Equation (5.13) implies `H ⊆ H̃_i`: the residual contains no old
coloured vertex and no selected current-level block. -/
lemma deficitResidual_subset_currentColorAmbient
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    deficitResidual A C phi (ell + 1) ⊆
      (A \ colorClass A phi i) \ redBlockUnion C N blockColor i := by
  classical
  intro v hv
  rw [deficitResidual, mem_sdiff] at hv
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hv.1, ?_⟩, ?_⟩
  · intro hvclass
    apply hv.2
    exact mem_union_left _ (colorClass_subset_coloredVertices A phi i hvclass)
  · intro hvZ
    apply hv.2
    exact mem_union_right _
      (redBlockUnion_subset_uncoloredPrefixUnion_succ
        N hN blockColor i hvZ)

/-- Selected blocks were uncoloured in `phi`, hence are disjoint from every
old colour class. -/
lemma redBlockUnion_subset_oldColorComplement
    {A : Finset V} {k ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {t : ℤ} {J0 : ℕ}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    redBlockUnion C N blockColor i ⊆ A \ colorClass A phi i := by
  classical
  intro v hv
  rw [redBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN : r ∈ N := (mem_filter.mp hr).1
  have hrU := hN hrN
  rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hrU
  have hrJ : r < Dyadic.levelStart J := hrU.1.2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hvA := S.block_subset r hrJ hvr
  refine mem_sdiff.mpr ⟨hvA, ?_⟩
  intro hvclass
  have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
  have hvnone := hrU.2 v hvr
  rw [hvnone] at hvcolor
  contradiction

/-- A future uncoloured block has all its ambient neighbours in the exact
deficit residual.  This is the vertexwise form of the final extension
hypothesis preceding the application of Lemma 3.1. -/
lemma futureBlock_neighbor_mem_deficitResidual_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hu : BlockUncolored phi (C.getD r ∅))
    {x v : V} (hx : x ∈ C.getD r ∅) (hvA : v ∈ A)
    (hxv : G.Adj x v) :
    v ∈ deficitResidual A C phi (ell + 1) := by
  classical
  have hrell : Dyadic.levelStart ell ≤ r :=
    (Dyadic.levelStart_le_succ ell).trans hr
  have hvnone : phi v = none := hphi.future r hrell hrJ hu x hx v hvA hxv
  rw [deficitResidual, mem_sdiff]
  refine ⟨hvA, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvprefix
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
    obtain ⟨s, hs, hvs⟩ := hvprefix
    have hs' : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hs
    have hslt : s < Dyadic.levelStart (ell + 1) := mem_range.mp hs'.1
    have hsr : s ≠ r := by omega
    have hsJ : s < Dyadic.levelStart J := (hslt.trans_le hr).trans hrJ
    apply S.blocks_anticomplete s hsJ r hrJ hsr
    exact ⟨v, hvs, x, hx, hxv.symm⟩

/-- Every extension vertex is anticomplete to a protected future block,
provided that block is represented by an uncoloured future index. -/
lemma extensionDiff_anticomplete_futureBlock
    {A Atilde H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hAtilde : Atilde ⊆ A)
    (hH : H = deficitResidual A C phi (ell + 1))
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hu : BlockUncolored phi (C.getD r ∅)) :
    Anticomplete G (Atilde \ H) (C.getD r ∅) := by
  intro hadj
  rcases hadj with ⟨v, hv, x, hx, hvx⟩
  have hvres := futureBlock_neighbor_mem_deficitResidual_succ
    S hphi hr hrJ hu hx (hAtilde (mem_sdiff.mp hv).1) hvx.symm
  exact (mem_sdiff.mp hv).2 (by simpa [hH] using hvres)

/-- Family-level bridge for the `hnew` premise of
`apply_extension_per_color`. -/
lemma extensionDiff_anticomplete_protectedFutureFamily
    {A H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (CH : ProtectedFamily G H k)
    (hH : H = deficitResidual A C phi (ell + 1))
    (Atilde : I → Finset V) (hAtilde : ∀ i, Atilde i ⊆ A)
    (hfuture : ∀ D ∈ CH.blocks, ∃ r,
      Dyadic.levelStart (ell + 1) ≤ r ∧
      r < Dyadic.levelStart J ∧
      BlockUncolored phi (C.getD r ∅) ∧ D = C.getD r ∅) :
    ∀ i D, D ∈ CH.blocks → Anticomplete G (Atilde i \ H) D := by
  intro i D hD
  obtain ⟨r, hr, hrJ, hu, rfl⟩ := hfuture D hD
  exact extensionDiff_anticomplete_futureBlock S hphi (hAtilde i) hH
    hr hrJ hu

/-! ### Degree protection for the certificate set `S`

The next three lemmas isolate the finite-cardinality work in the
G1/G2/avoid case split.  They let the greedy-construction layer hand the
extension layer actual surviving blocks or old colours, without repeating
neighbor-set arithmetic. -/

/-- A supply of new neighbours outside `H` adds to all neighbours already
present in `H`. -/
lemma degreeOn_add_card_le_of_external_neighbor_supply
    {H A W : Finset V} {s : V}
    (hHA : H ⊆ A) (hWA : W ⊆ A) (hWH : Disjoint W H)
    (hWnbr : ∀ w ∈ W, G.Adj s w) :
    degreeOn G H s + W.card ≤ degreeOn G A s := by
  classical
  let NH := G.neighborFinset s ∩ H
  have hNHcard : NH.card = degreeOn G H s := rfl
  have hdisj : Disjoint NH W := by
    rw [Finset.disjoint_left]
    intro x hxNH hxW
    exact Finset.disjoint_left.mp hWH hxW (mem_inter.mp hxNH).2
  have hsub : NH ∪ W ⊆ G.neighborFinset s ∩ A := by
    intro x hx
    rcases mem_union.mp hx with hxNH | hxW
    · exact mem_inter.mpr ⟨(mem_inter.mp hxNH).1,
        hHA (mem_inter.mp hxNH).2⟩
    · exact mem_inter.mpr ⟨by simpa using hWnbr x hxW, hWA hxW⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hNHcard] at hc
  exact hc

/-- Pairwise-disjoint adjacent blocks have distinct neighbor
representatives. -/
lemma exists_neighborRepresentatives_of_pairwiseDisjoint
    {Q : Finset ℕ} {block : ℕ → Finset V} {s : V}
    (hpair : (Q : Set ℕ).PairwiseDisjoint block)
    (hadj : ∀ r ∈ Q, AdjacentSets G {s} (block r)) :
    ∃ W : Finset V, W.card = Q.card ∧
      W ⊆ Q.biUnion block ∧ ∀ w ∈ W, G.Adj s w := by
  classical
  have hex : ∀ r : ℕ, r ∈ Q → ∃ w ∈ block r, G.Adj s w := by
    intro r hr
    rcases hadj r hr with ⟨x, hx, w, hw, hxw⟩
    have hxs : x = s := by simpa using hx
    subst x
    exact ⟨w, hw, hxw⟩
  let pick : {r // r ∈ Q} → V := fun r ↦ Classical.choose (hex r r.property)
  have pick_mem : ∀ r : {r // r ∈ Q}, pick r ∈ block r := by
    intro r
    exact (Classical.choose_spec (hex r r.property)).1
  have pick_adj : ∀ r : {r // r ∈ Q}, G.Adj s (pick r) := by
    intro r
    exact (Classical.choose_spec (hex r r.property)).2
  have hinj : Function.Injective pick := by
    intro r q heq
    apply Subtype.ext
    by_contra hrq
    have hd := hpair r.property q.property hrq
    exact Finset.disjoint_left.mp hd (pick_mem r) (heq ▸ pick_mem q)
  refine ⟨Q.attach.image pick, ?_, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (fun r _ q _ h ↦ hinj h)]
    exact Finset.card_attach
  · intro w hw
    rw [mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact mem_biUnion.mpr ⟨r, r.property, pick_mem r⟩
  · intro w hw
    rw [mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact pick_adj r

/-- Distinct colours give distinct old coloured neighbor representatives. -/
lemma colorSet_card_le_degreeOn
    {A : Finset V} {k : ℕ} (phi : PartialColoring V k)
    {L : Finset (Color k)} {s : V}
    (hneigh : ∀ i ∈ L, ∃ v ∈ A, G.Adj s v ∧ phi v = some i) :
    L.card ≤ degreeOn G A s := by
  classical
  have hex : ∀ i : Color k, i ∈ L →
      ∃ v ∈ A, G.Adj s v ∧ phi v = some i := hneigh
  let pick : {i // i ∈ L} → V := fun i ↦ Classical.choose (hex i i.property)
  have pick_mem : ∀ i : {i // i ∈ L}, pick i ∈ A := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).1
  have pick_adj : ∀ i : {i // i ∈ L}, G.Adj s (pick i) := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).2.1
  have pick_color : ∀ i : {i // i ∈ L}, phi (pick i) = some i := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).2.2
  have hinj : Function.Injective pick := by
    intro i j heq
    apply Subtype.ext
    exact Option.some.inj ((pick_color i).symm.trans (heq ▸ pick_color j))
  have himage : L.attach.image pick ⊆ G.neighborFinset s ∩ A := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact mem_inter.mpr ⟨by simpa using pick_adj i, pick_mem i⟩
  have hc := card_le_card himage
  rw [Finset.card_image_iff.mpr (fun i _ j _ h ↦ hinj h), Finset.card_attach] at hc
  exact hc

lemma degreeOn_eq_of_adjacent_membership_iff
    {A B : Finset V} {s : V}
    (h : ∀ v, G.Adj s v → (v ∈ A ↔ v ∈ B)) :
    degreeOn G A s = degreeOn G B s := by
  unfold degreeOn
  congr 1
  ext v
  simp only [mem_inter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hsv, hvA⟩
    exact ⟨hsv, (h v hsv).mp hvA⟩
  · rintro ⟨hsv, hvB⟩
    exact ⟨hsv, (h v hsv).mpr hvB⟩

lemma PopularScratch.neighborColorList_eq_of_card_le
    {A : Finset V} {k : ℕ} (phi : PartialColoring V k) (s : V)
    (hcard : (PopularScratch.neighborColorSet G A phi s).card ≤ k) :
    PopularScratch.neighborColorList G A phi s =
      PopularScratch.neighborColorSet G A phi s := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (PopularScratch.neighborColorList_subset G A phi s)
  rw [PopularScratch.neighborColorList,
    PopularScratch.card_chooseMinSubset, Nat.min_eq_left hcard]

/-- The exact four-way `S`-protection case split used after greedy
colouring: no red block; full selected scope (G1); `k` old colours avoiding
red (G2); or the short-list case reduced to the known core after one
block. -/
lemma certificateVertex_degree_ge_of_greedy_cases
    {H B Z Atilde : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k) (hHtilde : H ⊆ Atilde) (hZB : Z ⊆ B)
    (hAtilde : Atilde = B \ Z) (hminB : HasMinDegreeOn G B k)
    {s : V} (hsH : s ∈ H) (hslow : degreeOn G H s ≤ k - 1)
    (hcases :
      ¬ AdjacentSets G {s} Z ∨
      (∃ W : Finset V, W ⊆ Atilde ∧ Disjoint W H ∧
        (∀ w ∈ W, G.Adj s w) ∧
        k - degreeOn G H s ≤ W.card) ∨
      (∃ L : Finset (Color k), k ≤ L.card ∧
        ∀ i ∈ L, ∃ v ∈ Atilde, G.Adj s v ∧
          phi v = some i) ∨
      (∃ AminusD : Finset V, s ∈ AminusD ∧
        HasMinDegreeOn G AminusD k ∧
        degreeOn G Atilde s = degreeOn G AminusD s)) :
    k ≤ degreeOn G Atilde s := by
  rcases hcases with hno | hfull | hold | hshort
  · have hsAtilde : s ∈ Atilde := hHtilde hsH
    have hsBZ : s ∈ B \ Z := by simpa [hAtilde] using hsAtilde
    have hsB : s ∈ B := (mem_sdiff.mp hsBZ).1
    have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hno
    rw [hAtilde, heq]
    exact hminB.2 s hsB
  · obtain ⟨W, hWA, hWH, hWnbr, hcard⟩ := hfull
    have hsupply := degreeOn_add_card_le_of_external_neighbor_supply
      (G := G) hHtilde hWA hWH hWnbr
    omega
  · obtain ⟨L, hLcard, hL⟩ := hold
    have hc : L.card ≤ degreeOn G Atilde s := by
      apply colorSet_card_le_degreeOn (G := G) (phi := phi)
      intro i hi
      exact hL i hi
    omega
  · obtain ⟨AminusD, hsD, hminD, heq⟩ := hshort
    rw [heq]
    exact hminD.2 s hsD

/-- Exact index form of (5.29).  A low vertex of `H̃_i` sees a selected
red block, and every uncoloured current-level block it sees is red. -/
lemma lowVertex_currentBlock_color_description
    {A H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k))
    (CH : ProtectedFamily G H k)
    (E : ExtensionCertificate G H k CH)
    (hH : H = deficitResidual A C phi (ell + 1))
    (hprotect : ∀ i s, s ∈ E.S →
      s ∈ ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) →
      k ≤ degreeOn G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) s)
    (i : Color k) (v : V)
    (hv : v ∈ lowVertices G
      ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k) :
    (∃ r ∈ N, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅)) ∧
    (∀ q ∈ uncoloredCurrentIndices C phi ell,
      AdjacentSets G {v} (C.getD q ∅) → blockColor q = some i) := by
  classical
  let Z := redBlockUnion C N blockColor i
  let B := A \ colorClass A phi i
  let At := B \ Z
  have hZB : Z ⊆ B := by
    simpa [Z, B] using redBlockUnion_subset_oldColorComplement
      S N hN hellJ blockColor i
  have hvdata : v ∈ At ∧ degreeOn G At v ≤ k - 1 := by
    simpa [At, B, Z] using (mem_lowVertices.mp hv)
  have hadjZ : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) S.hk hZB hvdata.1
      (by simpa [B] using
        (hphi.minDegree i).2 v (mem_sdiff.mp hvdata.1).1) hvdata.2
  have hfirst : ∃ r ∈ N, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
    exact adjacent_block_of_adjacent_redBlockUnion C N blockColor i hadjZ
  refine ⟨hfirst, ?_⟩
  have hinside := lowVertices_currentColor_subset_deficitResidual_succ
    S hphi hellJ N hN blockColor i hv
  have hvH : v ∈ H := by simpa [hH] using hinside
  have hHAt : H ⊆ At := by
    intro x hx
    have hx' : x ∈ deficitResidual A C phi (ell + 1) := by simpa [hH] using hx
    simpa [At, B, Z] using
      (deficitResidual_subset_currentColorAmbient N hN blockColor i hx')
  have hdegHle : degreeOn G H v ≤ k - 1 :=
    (degreeOn_mono G hHAt v).trans hvdata.2
  have hvnotS : v ∉ E.S := by
    intro hvS
    have hhigh := hprotect i v hvS (by simpa [At, B, Z] using hvdata.1)
    change k ≤ degreeOn G At v at hhigh
    have hlow := hvdata.2
    have hbad : k ≤ k - 1 := hhigh.trans hlow
    have hk := S.hk
    omega
  have hdegH : degreeOn G H v = k - 1 := by
    have hnvery : v ∉ veryLowVertices G H k := by
      intro hvery
      exact hvnotS (E.veryLow_subset_S hvery)
    have hlower : k - 1 ≤ degreeOn G H v := by
      by_contra hnot
      apply hnvery
      rw [mem_veryLowVertices]
      exact ⟨hvH, by omega⟩
    omega
  have hdegAt : degreeOn G At v = k - 1 := by
    have hmono := degreeOn_mono G hHAt v
    omega
  intro q hqU hadjq
  by_contra hqcolor
  have hqData : q ∈ Dyadic.levelIndices ell ∧
      BlockUncolored phi (C.getD q ∅) := by
    simpa [uncoloredCurrentIndices] using hqU
  have hqRange := Dyadic.mem_levelIndices.mp hqData.1
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hqJ : q < Dyadic.levelStart J := hqRange.2.trans_le
    (Dyadic.levelStart_mono hellSuccJ)
  rcases hadjq with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  have hyAt : y ∈ At := by
    have hyA := S.block_subset q hqJ hy
    have hyB : y ∈ B := by
      refine mem_sdiff.mpr ⟨hyA, ?_⟩
      intro hyclass
      have hycolor : phi y = some i := (mem_filter.mp hyclass).2
      have hynone := hqData.2 y hy
      rw [hynone] at hycolor
      contradiction
    refine mem_sdiff.mpr ⟨hyB, ?_⟩
    intro hyZ
    change y ∈ redBlockUnion C N blockColor i at hyZ
    rw [redBlockUnion, mem_biUnion] at hyZ
    obtain ⟨r, hr, hyr⟩ := hyZ
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hrcolor : blockColor r = some i := (mem_filter.mp hr).2
    have hrU := hN hrN
    have hrData : r ∈ Dyadic.levelIndices ell ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredCurrentIndices] using hrU
    have hrRange := Dyadic.mem_levelIndices.mp hrData.1
    have hrJ : r < Dyadic.levelStart J := hrRange.2.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
    by_cases hqr : q = r
    · subst r
      exact hqcolor hrcolor
    · exact Finset.disjoint_left.mp
        (S.blocks_disjoint q hqJ r hrJ hqr) hy hyr
  have hyNotH : y ∉ H := by
    intro hyH
    have hyRes : y ∈ deficitResidual A C phi (ell + 1) := by simpa [hH] using hyH
    rw [deficitResidual, mem_sdiff] at hyRes
    apply hyRes.2
    apply mem_union_right
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨q, ?_, hy⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr hqRange.2, hqData.2⟩
  have hsupply : degreeOn G H v + 1 ≤ degreeOn G At v := by
    have h := degreeOn_add_card_le_of_external_neighbor_supply
      (G := G) hHAt (W := {y}) (A := At)
      (by simpa using hyAt)
      (by simp [hyNotH])
      (by
        intro w hw
        have hwy : w = y := by simpa using hw
        subst w
        exact hxy)
    simpa using h
  omega

/-- The output of applying one extension certificate simultaneously for every
colour.  This packages (5.30)--(5.33) and (K1)--(K4), including the
pairwise-disjointness argument for the sets `X'_i`. -/
structure PerColorExtensionConclusion
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (Atilde : I → Finset V) where
  retained : I → Finset V
  X : I → Finset V
  deleted_eq : ∀ i, X i = Atilde i \ retained i
  retained_eq : ∀ i, retained i = Atilde i \ X i
  X_subset_H : ∀ i, X i ⊆ H
  X_subset_reserves : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k
  incidence : ∀ i,
    incidentCount G (Atilde i) (X i) ≤ (k - 1) * (X i).card
  minDegree : ∀ i, HasMinDegreeOn G (retained i) k
  whole_blocks_deleted : ∀ i D, D ∈ C.blocks →
    D ⊆ X i ∨ Disjoint D (X i)
  retained_blocks_anticomplete : ∀ i D, D ∈ C.blocks →
    Disjoint D (X i) → Anticomplete G D (X i)
  disjoint_from_old : ∀ D, Disjoint D H → ∀ i, Disjoint D (X i)
  low_index_description : ∀ i x, x ∈ X i →
    ∃ v ∈ lowVertices G (Atilde i) k,
      x ∈ E.reserve v
  pairwise_X : ∀ i j, i ≠ j → Disjoint (X i) (X j)

/-- The reusable per-colour application of Sauermann's extension lemma.

`hinside` is (5.27).  `hprotect` is the consequence of (G1)--(G2) saying
that the selected vertices `S` retain degree at least `k`.  `hred` is
(5.29): a low vertex sees a selected current-level block, and every such
block has the current colour.  Thus `hinside` and `hprotect` prove (5.28),
while `hred` makes the reserve sets used for distinct colours disjoint. -/
theorem apply_extension_per_color
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks →
      Anticomplete G (Atilde i \ H) D)
    (selectedBlocks : Finset (Finset V))
    (blockColor : Finset V → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ D ∈ selectedBlocks, AdjacentSets G {v} D) ∧
      (∀ D ∈ selectedBlocks, AdjacentSets G {v} D →
        blockColor D = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V, ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hindex_unique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j := by
    intro i j v hvi hvj
    obtain ⟨D, hDB, hvD⟩ := (hred i v hvi).1
    have hi := (hred i v hvi).2 D hDB hvD
    have hj := (hred j v hvj).2 D hDB hvD
    exact Option.some.inj (hi.symm.trans hj)
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hindex_unique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

/-- The extension application only uses (5.29) through uniqueness of the
colour attached to a low vertex.  This factored form is convenient when
blocks are indexed rather than stored as a finset of finsets. -/
theorem apply_extension_per_color_of_unique
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks → Anticomplete G (Atilde i \ H) D)
    (hunique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V,
      ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hunique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

/-- Index-valued form of the per-colour application, matching the dyadic
block representation used by the successor construction. -/
theorem apply_extension_per_color_indices
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k) (blocks : List (Finset V))
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks → Anticomplete G (Atilde i \ H) D)
    (Uidx : Finset ℕ) (blockColor : ℕ → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ r ∈ Uidx, blockColor r = some i ∧
        AdjacentSets G {v} (blocks.getD r ∅)) ∧
      (∀ r ∈ Uidx, AdjacentSets G {v} (blocks.getD r ∅) →
        blockColor r = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  apply apply_extension_per_color_of_unique C E hk Atilde hH hproper hinside
    hprotect hnew
  intro i j v hvi hvj
  obtain ⟨⟨r, hr, hri, hadj⟩, halli⟩ := hred i v hvi
  have hrj := (hred j v hvj).2 r hr hadj
  exact Option.some.inj (hri.symm.trans hrj)

/-- Upgrade (K1) from the residual protected family to the original block
family.  This is the exact last step used in the paper: a whole block is
either contained in `H`, when the certificate applies, or disjoint from
`H`, when `X'_i ⊆ H` applies. -/
lemma PerColorExtensionConclusion.whole_blocks_deleted_of_restriction
    {A H : Finset V} {k : ℕ}
    {C : ProtectedFamily G H k} {E : ExtensionCertificate G H k C}
    {Atilde : I → Finset V}
    (R : PerColorExtensionConclusion C E Atilde)
    (C₀ : ProtectedFamily G A k)
    (hwhole : C₀.WholeBlocks H)
    (hblocks : ∀ D, D ∈ C.blocks ↔ D ∈ C₀.blocks ∧ D ⊆ H) :
    ∀ i D, D ∈ C₀.blocks → D ⊆ R.X i ∨ Disjoint D (R.X i) := by
  intro i D hD
  rcases hwhole D hD with hDH | hDH
  · exact R.whole_blocks_deleted i D ((hblocks D).2 ⟨hD, hDH⟩)
  · exact Or.inr (hDH.mono_right (R.X_subset_H i))


end ExtensionApplyScratch

noncomputable section

lemma selectedBlockUnion_incidence
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    incidentCount G (A \ colorClass A phi i)
        (selectedBlockUnion C N psi i) ≤
      (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card := by
  classical
  let R := N.filter fun r ↦ psi r = i
  let D : ℕ → Finset V := fun r ↦ C.getD r ∅
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hrJ : ∀ r ∈ R, r < Dyadic.levelStart J := by
    intro r hr
    have hrN := hN (mem_filter.mp hr).1
    have hrlev : r ∈ Dyadic.levelIndices ell := by
      simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
    exact (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hpair : (R : Set ℕ).PairwiseDisjoint D := by
    intro r hr s hs hrs
    exact S.blocks_disjoint r (hrJ r hr) s (hrJ s hs) hrs
  have hsum := incidentCount_biUnion_le_sum (G := G)
    (A \ colorClass A phi i) R D
  calc
    incidentCount G (A \ colorClass A phi i)
        (selectedBlockUnion C N psi i) =
        incidentCount G (A \ colorClass A phi i) (R.biUnion D) := by rfl
    _ ≤ ∑ r ∈ R, incidentCount G (A \ colorClass A phi i) (D r) := hsum
    _ ≤ ∑ r ∈ R, ((k - 1) * (D r).card + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact (incidentCount_ambient_mono (G := G)
        (A := A \ colorClass A phi i) (B := A) sdiff_subset).trans
          (S.block_incident r (hrJ r hr))
    _ = (k - 1) * (R.biUnion D).card + R.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.card_biUnion hpair]
      simp
    _ = (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card := by rfl

lemma selectedBlockUnion_subset_A
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    selectedBlockUnion C N psi i ⊆ A := by
  classical
  intro v hv
  rw [selectedBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN := hN (mem_filter.mp hr).1
  have hrlev : r ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
  have hrJ := (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  exact S.block_subset r hrJ hvr

lemma selectedBlockUnion_uncolored
    {k ell : ℕ} {C : List (Finset V)} {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    ∀ v ∈ selectedBlockUnion C N psi i, phi v = none := by
  classical
  intro v hv
  rw [selectedBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN := hN (mem_filter.mp hr).1
  exact (mem_filter.mp hrN).2 v hvr

lemma selectedBlockUnion_pairwise
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) :
    ∀ i j, i ≠ j →
      Disjoint (selectedBlockUnion C N psi i)
        (selectedBlockUnion C N psi j) := by
  classical
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [selectedBlockUnion, mem_biUnion] at hvi hvj
  obtain ⟨r, hr, hvr⟩ := hvi
  obtain ⟨s, hs, hvs⟩ := hvj
  have hrN := hN (mem_filter.mp hr).1
  have hsN := hN (mem_filter.mp hs).1
  have hrlev : r ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
  have hslev : s ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hsN).1
  have hrJ := (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hsJ := (Dyadic.mem_levelIndices.mp hslev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  by_cases hrs : r = s
  · subst s
    exact hij ((mem_filter.mp hr).2.symm.trans (mem_filter.mp hs).2)
  · exact Finset.disjoint_left.mp
      (S.blocks_disjoint r hrJ s hsJ hrs) hvr hvs

lemma selectedBlockUnion_disjoint_residual
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    Disjoint (selectedBlockUnion C N psi i)
      (deficitResidual A C phi (ell + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvZ hvH
  have hvPrefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
    rw [selectedBlockUnion, mem_biUnion] at hvZ
    obtain ⟨r, hr, hvr⟩ := hvZ
    have hrU := hN (mem_filter.mp hr).1
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨r, ?_, hvr⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (Dyadic.mem_levelIndices.mp (mem_filter.mp hrU).1).2,
      (mem_filter.mp hrU).2⟩
  exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvPrefix)

lemma block_whole_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrJ : r < Dyadic.levelStart J) :
    C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1) ∨
      Disjoint (C.getD r ∅) (deficitResidual A C phi (ell + 1)) := by
  classical
  rcases hphi.blocks r hrJ with ⟨i, hmono⟩ | hun
  · right
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have hvA := S.block_subset r hrJ hvD
    have hvcol : v ∈ coloredVertices A phi :=
      mem_coloredVertices_iff.mpr ⟨hvA, i, hmono v hvD⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
  · by_cases hr : r < Dyadic.levelStart (ell + 1)
    · right
      rw [Finset.disjoint_left]
      intro v hvD hvH
      have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
        rw [uncoloredPrefixUnion, mem_biUnion]
        refine ⟨r, ?_, hvD⟩
        rw [uncoloredPrefixIndices, mem_filter]
        exact ⟨mem_range.mpr hr, hun⟩
      exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
    · left
      intro v hvD
      have hvA := S.block_subset r hrJ hvD
      refine mem_sdiff.mpr ⟨hvA, ?_⟩
      intro hvbad
      rcases mem_union.mp hvbad with hvcol | hvprefix
      · rw [mem_coloredVertices_iff] at hvcol
        obtain ⟨_, i, hi⟩ := hvcol
        have hn := hun v hvD
        rw [hn] at hi
        contradiction
      · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
        obtain ⟨s, hs, hvs⟩ := hvprefix
        have hsData : s < Dyadic.levelStart (ell + 1) := by
          rw [uncoloredPrefixIndices, mem_filter] at hs
          exact mem_range.mp hs.1
        have hsJ : s < Dyadic.levelStart J :=
          (hsData.trans_le (Nat.le_of_not_gt hr)).trans hrJ
        have hrs : r ≠ s := by omega
        exact Finset.disjoint_left.mp
          (S.blocks_disjoint r hrJ s hsJ hrs) hvD hvs

lemma future_uncolored_block_subset_residual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hun : BlockUncolored phi (C.getD r ∅)) :
    C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1) := by
  classical
  intro v hvD
  have hvA := S.block_subset r hrJ hvD
  refine mem_sdiff.mpr ⟨hvA, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcol | hvprefix
  · rw [mem_coloredVertices_iff] at hvcol
    obtain ⟨_, i, hi⟩ := hvcol
    have hn := hun v hvD
    rw [hn] at hi
    contradiction
  · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
    obtain ⟨s, hs, hvs⟩ := hvprefix
    have hslt : s < Dyadic.levelStart (ell + 1) := by
      rw [uncoloredPrefixIndices, mem_filter] at hs
      exact mem_range.mp hs.1
    have hsJ : s < Dyadic.levelStart J := hslt.trans_le (hr.trans hrJ.le)
    have hrs : r ≠ s := by omega
    exact Finset.disjoint_left.mp
      (S.blocks_disjoint r hrJ s hsJ hrs) hvD hvs

lemma block_subset_residual_is_future
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrJ : r < Dyadic.levelStart J)
    (hsub : C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)) :
    Dyadic.levelStart (ell + 1) ≤ r := by
  classical
  by_contra hnot
  have hr : r < Dyadic.levelStart (ell + 1) := Nat.lt_of_not_ge hnot
  obtain ⟨v, hv⟩ := S.block_nonempty r hrJ
  have hvH := hsub hv
  rcases hphi.blocks r hrJ with ⟨i, hmono⟩ | hun
  · have hvA := S.block_subset r hrJ hv
    have hvcol : v ∈ coloredVertices A phi :=
      mem_coloredVertices_iff.mpr ⟨hvA, i, hmono v hv⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
  · have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
      rw [uncoloredPrefixUnion, mem_biUnion]
      refine ⟨r, ?_, hv⟩
      rw [uncoloredPrefixIndices, mem_filter]
      exact ⟨mem_range.mpr hr, hun⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)

lemma unselectedBlock_disjoint_selectedBlockUnion
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hrJ : r < Dyadic.levelStart J) (hrN : r ∉ N)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    Disjoint (C.getD r ∅) (selectedBlockUnion C N psi i) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvr hvZ
  rw [selectedBlockUnion, mem_biUnion] at hvZ
  obtain ⟨s, hs, hvs⟩ := hvZ
  have hsN := (mem_filter.mp hs).1
  have hsU := hN hsN
  have hslev : s ∈ Dyadic.levelIndices ell := (mem_filter.mp hsU).1
  have hsJ := (Dyadic.mem_levelIndices.mp hslev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hrs : r ≠ s := fun hrs ↦ hrN (hrs ▸ hsN)
  exact Finset.disjoint_left.mp (S.blocks_disjoint r hrJ s hsJ hrs) hvr hvs

lemma futureBlock_anticomplete_selectedBlockUnion
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J) (hellJ : ell < J)
    (psi : ℕ → Color k) (i : Color k) :
    Anticomplete G (C.getD r ∅) (selectedBlockUnion C N psi i) := by
  classical
  intro hadj
  rcases hadj with ⟨v, hvr, w, hwZ, hvw⟩
  rw [selectedBlockUnion, mem_biUnion] at hwZ
  obtain ⟨s, hs, hws⟩ := hwZ
  have hsN := (mem_filter.mp hs).1
  have hsU := hN hsN
  have hslev : s ∈ Dyadic.levelIndices ell := (mem_filter.mp hsU).1
  have hsrange := Dyadic.mem_levelIndices.mp hslev
  have hsJ := hsrange.2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hrs : r ≠ s := by omega
  exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨v, hvr, w, hws, hvw⟩

lemma deficitResidual_ssubset_selectedColorAmbient
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    deficitResidual A C phi (ell + 1) ⊂
      (A \ colorClass A phi i) \ selectedBlockUnion C N psi i := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let Z := selectedBlockUnion C N psi i
  let B := (A \ colorClass A phi i) \ Z
  have hHB : H ⊆ B := by
    intro v hvH
    have hvA := (mem_sdiff.mp hvH).1
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
    · intro hvclass
      exact (mem_sdiff.mp hvH).2 (mem_union_left _
        (colorClass_subset_coloredVertices A phi i hvclass))
    · intro hvZ
      exact Finset.disjoint_left.mp
        (selectedBlockUnion_disjoint_residual N hN psi i) hvZ hvH
  have hellpos : 0 < ell := S.hJ0.trans_le hJ0ell
  have hzeroJ : 0 < Dyadic.levelStart J := by
    have hJne : J ≠ 0 := Nat.ne_of_gt (hellpos.trans hellJ)
    simp [Dyadic.levelStart, hJne]
  obtain ⟨v, hvD⟩ := S.block_nonempty 0 hzeroJ
  have hvA := S.block_subset 0 hzeroJ hvD
  have hzeroEarly : 0 < Dyadic.levelStart J0 := by
    have hJ0ne : J0 ≠ 0 := Nat.ne_of_gt S.hJ0
    simp [Dyadic.levelStart, hJ0ne]
  have hvnone := hphi.early 0 hzeroEarly v hvD
  have hzeroN : 0 ∉ N := by
    intro hzN
    have hzU := hN hzN
    have hzlev : 0 ∈ Dyadic.levelIndices ell := (mem_filter.mp hzU).1
    have hzlow := (Dyadic.mem_levelIndices.mp hzlev).1
    have : 0 < Dyadic.levelStart ell := by
      have hellne : ell ≠ 0 := Nat.ne_of_gt hellpos
      simp [Dyadic.levelStart, hellne]
    omega
  have hDZ : Disjoint (C.getD 0 ∅) Z := by
    exact unselectedBlock_disjoint_selectedBlockUnion S N hN hzeroJ
      hzeroN hellJ psi i
  have hvB : v ∈ B := by
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
    · intro hvclass
      have hi := (mem_filter.mp hvclass).2
      rw [hvnone] at hi
      contradiction
    · exact fun hvZ ↦ Finset.disjoint_left.mp hDZ hvD hvZ
  have hvNotH : v ∉ H := by
    intro hvH
    have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
      rw [uncoloredPrefixUnion, mem_biUnion]
      refine ⟨0, ?_, hvD⟩
      rw [uncoloredPrefixIndices, mem_filter]
      exact ⟨mem_range.mpr (hzeroEarly.trans_le
        (Dyadic.levelStart_mono (hJ0ell.trans (Nat.le_succ ell)))),
        hphi.early 0 hzeroEarly⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hHB, ?_⟩
  intro heq
  have hvH : v ∈ H := by
    change v ∈ deficitResidual A C phi (ell + 1)
    rw [heq]
    simpa [B, Z] using hvB
  exact hvNotH hvH

theorem successorData_of_greedy_and_extensions
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell)
    (R : ExtensionApplyScratch.PerColorExtensionConclusion
      (residualProtectedFamily S hphi) E
      (fun i ↦ (A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i)) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let CH := residualProtectedFamily S hphi
  let At : Color k → Finset V := fun i ↦
    (A \ colorClass A phi i) \ selectedBlockUnion C d.N d.psi i
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hZX : ∀ i,
      Disjoint (selectedBlockUnion C d.N d.psi i) (R.X i) := by
    intro i
    exact (selectedBlockUnion_disjoint_residual d.N hN d.psi i).mono_right
      (R.X_subset_H i)
  have hnewPair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C d.N d.psi R.X i)
        (assembledNewClass C d.N d.psi R.X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rcases mem_union.mp hvi with hviZ | hviX
    · rcases mem_union.mp hvj with hvjZ | hvjX
      · exact Finset.disjoint_left.mp
          (selectedBlockUnion_pairwise S d.N hN hellJ d.psi i j hij) hviZ hvjZ
      · exact Finset.disjoint_left.mp
          ((selectedBlockUnion_disjoint_residual d.N hN d.psi i).mono_right
            (R.X_subset_H j)) hviZ hvjX
    · rcases mem_union.mp hvj with hvjZ | hvjX
      · exact Finset.disjoint_left.mp
          (((selectedBlockUnion_disjoint_residual d.N hN d.psi j).mono_right
            (R.X_subset_H i)).symm) hviX hvjZ
      · exact Finset.disjoint_left.mp (R.pairwise_X i j hij) hviX hvjX
  have hwholeX : ∀ r < Dyadic.levelStart J, ∀ i,
      C.getD r ∅ ⊆ R.X i ∨ Disjoint (C.getD r ∅) (R.X i) := by
    intro r hrJ i
    rcases block_whole_deficitResidual S hphi hrJ with hDH | hdisj
    · have hrfuture := block_subset_residual_is_future S hphi hrJ hDH
      have hrR : r ∈ residualFutureIndices A C phi ell J := by
        rw [residualFutureIndices, mem_filter, mem_Ico]
        exact ⟨⟨hrfuture, hrJ⟩, hDH⟩
      have hmem : C.getD r ∅ ∈ CH.blocks := by
        change C.getD r ∅ ∈
          (residualFutureIndices A C phi ell J).image (fun q ↦ C.getD q ∅)
        exact mem_image.mpr ⟨r, hrR, rfl⟩
      exact R.whole_blocks_deleted i _ hmem
    · exact Or.inr (hdisj.mono_right (R.X_subset_H i))
  have hnewSubset : ∀ i, assembledNewClass C d.N d.psi R.X i ⊆ A := by
    intro i v hv
    rcases mem_union.mp hv with hvZ | hvX
    · exact selectedBlockUnion_subset_A S d.N hN hellJ d.psi i hvZ
    · exact sdiff_subset (R.X_subset_H i hvX)
  have hnewUncolored : ∀ i, ∀ v ∈ assembledNewClass C d.N d.psi R.X i,
      phi v = none := by
    intro i v hv
    rcases mem_union.mp hv with hvZ | hvX
    · exact selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
    · have hvH := R.X_subset_H i hvX
      have hvNotColored : v ∉ coloredVertices A phi := by
        intro hvcol
        exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
      cases hp : phi v with
      | none => rfl
      | some j =>
          exact False.elim (hvNotColored
            (mem_coloredVertices_iff.mpr
              ⟨(mem_sdiff.mp hvH).1, j, hp⟩))
  have hearlyDisj : ∀ r < Dyadic.levelStart J0, ∀ i,
      Disjoint (C.getD r ∅) (assembledNewClass C d.N d.psi R.X i) := by
    intro r hr0 i
    have hrJ : r < Dyadic.levelStart J :=
      hr0.trans_le (Dyadic.levelStart_mono S.hJ)
    have hrN : r ∉ d.N := by
      intro hrN
      have hrU := hN hrN
      have hrlower := (Dyadic.mem_levelIndices.mp (mem_filter.mp hrU).1).1
      exact (Nat.not_lt_of_ge
        (Dyadic.levelStart_mono hJ0ell |>.trans hrlower)) hr0
    have hDZ := unselectedBlock_disjoint_selectedBlockUnion S d.N hN
      hrJ hrN hellJ d.psi i
    have hDH : Disjoint (C.getD r ∅) H := by
      rcases block_whole_deficitResidual S hphi hrJ with hsub | hdisj
      · have hfut := block_subset_residual_is_future S hphi hrJ hsub
        exact False.elim ((Nat.not_lt_of_ge
          ((Dyadic.levelStart_mono (hJ0ell.trans (Nat.le_succ ell))).trans hfut)) hr0)
      · exact hdisj
    rw [Finset.disjoint_left]
    intro v hvD hvnew
    rcases mem_union.mp hvnew with hvZ | hvX
    · exact Finset.disjoint_left.mp hDZ hvD hvZ
    · exact Finset.disjoint_left.mp
        (hDH.mono_right (R.X_subset_H i)) hvD hvX
  have hfutureX : ∀ r,
      Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      BlockUncolored phi (C.getD r ∅) → Disjoint (C.getD r ∅) (R.X i) →
        ¬ AdjacentSets G (C.getD r ∅) (R.X i) := by
    intro r hr hrJ i hun hdisj
    have hDH := future_uncolored_block_subset_residual S hphi hr hrJ hun
    have hrR : r ∈ residualFutureIndices A C phi ell J := by
      rw [residualFutureIndices, mem_filter, mem_Ico]
      exact ⟨⟨hr, hrJ⟩, hDH⟩
    have hmem : C.getD r ∅ ∈ CH.blocks := by
      change C.getD r ∅ ∈
        (residualFutureIndices A C phi ell J).image (fun q ↦ C.getD q ∅)
      exact mem_image.mpr ⟨r, hrR, rfl⟩
    exact R.retained_blocks_anticomplete i _ hmem hdisj
  let ai : AssemblyInput G A k C J0 ell J phi :=
    { Uidx := d.Uidx
      N := d.N
      psi := d.psi
      X := R.X
      Uidx_eq := d.Uidx_eq
      N_subset_Uidx := d.N_subset
      selected_nonempty := by
        intro r hr
        have hrU := hN hr
        have hrlev := (mem_filter.mp hrU).1
        exact S.block_nonempty r
          ((Dyadic.mem_levelIndices.mp hrlev).2.trans_le
            (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ)))
      new_pairwise := hnewPair
      new_subset := hnewSubset
      new_uncolored := hnewUncolored
      Z_X_disjoint := hZX
      whole_X := hwholeX
      unselected_disjoint_Z := by
        intro r hrJ hrN i
        exact unselectedBlock_disjoint_selectedBlockUnion S d.N hN
          hrJ hrN hellJ d.psi i
      early_disjoint_new := hearlyDisj
      quarter_bound := d.quarter
      block_incidence := fun i ↦
        selectedBlockUnion_incidence S d.N hN hellJ d.psi i
      removed_incidence := fun i ↦ by
        simpa [At] using R.incidence i
      retained_core := fun i ↦ by
        have hmin := R.minDegree i
        rw [R.retained_eq i] at hmin
        have heq : At i \ R.X i =
            A \ (colorClass A phi i ∪
              (selectedBlockUnion C d.N d.psi i ∪ R.X i)) := by
          ext v
          simp [At]
          tauto
        rwa [heq] at hmin
      future_Z_anticomplete := by
        intro r hr hrJ i
        exact futureBlock_anticomplete_selectedBlockUnion S d.N hN
          hr hrJ hellJ d.psi i
      future_X_anticomplete := hfutureX }
  exact ⟨ai.rho, ⟨ai.toSuccessorData hphi⟩⟩

lemma currentUncoloredBlock_disjoint_deficitResidual
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {r : ℕ}
    (hr : r ∈ uncoloredCurrentIndices C phi ell) :
    Disjoint (C.getD r ∅) (deficitResidual A C phi (ell + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvD hvH
  have hvPrefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨r, ?_, hvD⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (Dyadic.mem_levelIndices.mp (mem_filter.mp hr).1).2,
      (mem_filter.mp hr).2⟩
  exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvPrefix)

lemma currentUncoloredBlock_subset_selectedColorAmbient
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k)
    (hrU : r ∈ uncoloredCurrentIndices C phi ell)
    (hrSurvives : ¬ (r ∈ N ∧ psi r = i)) :
    C.getD r ∅ ⊆
      (A \ colorClass A phi i) \ selectedBlockUnion C N psi i := by
  classical
  have hrLev : r ∈ Dyadic.levelIndices ell := (mem_filter.mp hrU).1
  have hrJ : r < Dyadic.levelStart J :=
    (Dyadic.mem_levelIndices.mp hrLev).2.trans_le
      (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  intro v hvD
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨S.block_subset r hrJ hvD, ?_⟩, ?_⟩
  · intro hvclass
    have hvColor := (mem_filter.mp hvclass).2
    have hvNone := (mem_filter.mp hrU).2 v hvD
    rw [hvNone] at hvColor
    contradiction
  · intro hvZ
    rw [selectedBlockUnion, mem_biUnion] at hvZ
    obtain ⟨q, hq, hvq⟩ := hvZ
    have hqN : q ∈ N := (mem_filter.mp hq).1
    have hqU := hN hqN
    have hqLev : q ∈ Dyadic.levelIndices ell := (mem_filter.mp hqU).1
    have hqJ : q < Dyadic.levelStart J :=
      (Dyadic.mem_levelIndices.mp hqLev).2.trans_le
        (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
    by_cases hrq : r = q
    · subst q
      exact hrSurvives ⟨hqN, (mem_filter.mp hq).2⟩
    · exact Finset.disjoint_left.mp
        (S.blocks_disjoint r hrJ q hqJ hrq) hvD hvq

lemma greedyLevel_certificate_protected
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    ∀ i s, s ∈ E.S →
      s ∈ ((A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i) →
      k ≤ degreeOn G ((A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i) s := by
  classical
  intro i s hsS hsAt
  let H := deficitResidual A C phi (ell + 1)
  let B := A \ colorClass A phi i
  let Z := selectedBlockUnion C d.N d.psi i
  let At := B \ Z
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hHAt : H ⊆ At :=
    (deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i).subset
  have hZB : Z ⊆ B := by
    intro v hvZ
    exact mem_sdiff.mpr ⟨selectedBlockUnion_subset_A S d.N hN hellJ d.psi i hvZ,
      fun hvclass ↦ by
        have hvColor := (mem_filter.mp hvclass).2
        have hvNone := selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
        rw [hvNone] at hvColor
        contradiction⟩
  have hsH : s ∈ H := (mem_lowVertices.mp (E.S_subset_low hsS)).1
  have hsLow : degreeOn G H s ≤ k - 1 :=
    (mem_lowVertices.mp (E.S_subset_low hsS)).2
  apply ExtensionApplyScratch.certificateVertex_degree_ge_of_greedy_cases
    (G := G) phi S.hk hHAt hZB rfl (hphi.minDegree i) hsH hsLow
  change s ∈ At at hsAt
  by_cases hno : ¬ AdjacentSets G {s} Z
  · exact Or.inl hno
  right
  have hred : ∃ r ∈ d.N, d.psi r = i ∧
      AdjacentSets G {s} (C.getD r ∅) := by
    have hadj : AdjacentSets G {s} Z := Classical.not_not.mp hno
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxs : x = s := by simpa using hx
    subst x
    change y ∈ selectedBlockUnion C d.N d.psi i at hy
    rw [selectedBlockUnion, mem_biUnion] at hy
    obtain ⟨r, hr, hyr⟩ := hy
    exact ⟨r, (mem_filter.mp hr).1, (mem_filter.mp hr).2,
      s, by simp, y, hyr, hxy⟩
  obtain ⟨rred, hrredN, hrredColor, hrredAdj⟩ := hred
  have hrredU := hN hrredN
  have hsActive : s ∈ d.active := by
    rw [d.active_eq, PopularScratch.selectedVertices, mem_filter]
    refine ⟨hsS, ?_⟩
    refine ⟨rred, ?_⟩
    rw [PopularScratch.adjacentBlockIndices, mem_filter]
    exact ⟨by rw [d.Uidx_eq]; exact hrredU, hrredAdj⟩
  let Adj := PopularScratch.adjacentBlockIndices G C d.Uidx s
  let need := k + 1 - degreeOn G H s
  by_cases hfull : need ≤ Adj.card
  · left
    have hscopeCard : (d.scope s).card = need := by
      rw [congrFun d.scope_eq s, PopularScratch.card_selectedScope]
      exact Nat.min_eq_right hfull
    by_cases hex : ∃ q ∈ d.scope s, q ∈ d.N ∧ d.psi q = i
    · obtain ⟨qred, hqredScope, hqredN, hqredColor⟩ := hex
      let Q := (d.scope s).erase qred
      have hQcard : Q.card = need - 1 := by
        dsimp [Q]
        rw [Finset.card_erase_of_mem hqredScope, hscopeCard]
      have hQsurvive : ∀ q ∈ Q, ¬ (q ∈ d.N ∧ d.psi q = i) := by
        intro q hqQ hqbad
        have hqScope := (mem_erase.mp hqQ).2
        have heq := d.injective_scope s hsActive q hqScope hqbad.1
          qred hqredScope hqredN (hqbad.2.trans hqredColor.symm)
        exact (mem_erase.mp hqQ).1 heq
      have hQpair : (Q : Set ℕ).PairwiseDisjoint (fun q ↦ C.getD q ∅) := by
        intro q hqQ p hpQ hqp
        have hqScope := (mem_erase.mp hqQ).2
        have hpScope := (mem_erase.mp hpQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hpU : p ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hpScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hpScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        have hpU' : p ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hpU
        have hqJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hqU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        have hpJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hpU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.blocks_disjoint q hqJ p hpJ hqp
      have hQadj : ∀ q ∈ Q, AdjacentSets G {s} (C.getD q ∅) := by
        intro q hqQ
        have hqScope := (mem_erase.mp hqQ).2
        rw [congrFun d.scope_eq s] at hqScope
        exact PopularScratch.mem_selectedScope_adjacent G H C d.Uidx k s hqScope
      obtain ⟨W, hWcard, hWsub, hWadj⟩ :=
        ExtensionApplyScratch.exists_neighborRepresentatives_of_pairwiseDisjoint
          (G := G) hQpair hQadj
      refine ⟨W, ?_, ?_, hWadj, ?_⟩
      · intro w hw
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hw)
        have hqScope := (mem_erase.mp hqQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact currentUncoloredBlock_subset_selectedColorAmbient S d.N hN hellJ
          d.psi i hqU' (hQsurvive q hqQ) hwq
      · rw [Finset.disjoint_left]
        intro w hwW hwH
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hwW)
        have hqScope := (mem_erase.mp hqQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hqU') hwq hwH
      · rw [hWcard, hQcard]
        dsimp [need]
        omega
    · let Q := d.scope s
      have hQsurvive : ∀ q ∈ Q, ¬ (q ∈ d.N ∧ d.psi q = i) := by
        intro q hqQ hqbad
        exact hex ⟨q, hqQ, hqbad⟩
      have hQpair : (Q : Set ℕ).PairwiseDisjoint (fun q ↦ C.getD q ∅) := by
        intro q hqQ p hpQ hqp
        change q ∈ d.scope s at hqQ
        change p ∈ d.scope s at hpQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hpU : p ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hpQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hpQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        have hpU' : p ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hpU
        have hqJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hqU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        have hpJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hpU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.blocks_disjoint q hqJ p hpJ hqp
      have hQadj : ∀ q ∈ Q, AdjacentSets G {s} (C.getD q ∅) := by
        intro q hqQ
        change q ∈ d.scope s at hqQ
        rw [congrFun d.scope_eq s] at hqQ
        exact PopularScratch.mem_selectedScope_adjacent G H C d.Uidx k s hqQ
      obtain ⟨W, hWcard, hWsub, hWadj⟩ :=
        ExtensionApplyScratch.exists_neighborRepresentatives_of_pairwiseDisjoint
          (G := G) hQpair hQadj
      refine ⟨W, ?_, ?_, hWadj, ?_⟩
      · intro w hw
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hw)
        change q ∈ d.scope s at hqQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact currentUncoloredBlock_subset_selectedColorAmbient S d.N hN hellJ
          d.psi i hqU' (hQsurvive q hqQ) hwq
      · rw [Finset.disjoint_left]
        intro w hwW hwH
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hwW)
        change q ∈ d.scope s at hqQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hqU') hwq hwH
      · rw [hWcard]
        change k - degreeOn G H s ≤ (d.scope s).card
        rw [hscopeCard]
        dsimp [need]
        omega
  · right
    have hAdjLe : Adj.card ≤ need := Nat.le_of_lt (Nat.lt_of_not_ge hfull)
    have hscopeEq : d.scope s = Adj := by
      rw [congrFun d.scope_eq s]
      exact PopularScratch.selectedScope_eq_adjacent_of_card_le
        G H C d.Uidx k s hAdjLe
    have hrredScope : rred ∈ d.scope s := by
      rw [hscopeEq]
      change rred ∈
        (d.Uidx.filter fun r ↦ AdjacentSets G {s} (C.getD r ∅))
      rw [mem_filter]
      exact ⟨by rw [d.Uidx_eq]; exact hrredU, hrredAdj⟩
    have hiAvoid : i ∉ PopularScratch.neighborColorList G A phi s := by
      have := d.avoids s hsActive rred hrredScope hrredN
      simpa [hrredColor] using this
    by_cases hmany : k ≤ (PopularScratch.neighborColorSet G A phi s).card
    · left
      let L := PopularScratch.neighborColorList G A phi s
      have hLcard : k ≤ L.card := by
        change k ≤ (PopularScratch.neighborColorList G A phi s).card
        rw [PopularScratch.neighborColorList,
          PopularScratch.card_chooseMinSubset, Nat.min_eq_right hmany]
      refine ⟨L, hLcard, ?_⟩
      intro j hj
      have hjSet := PopularScratch.neighborColorList_subset G A phi s hj
      rw [PopularScratch.neighborColorSet, mem_filter] at hjSet
      obtain ⟨v, hvA, hsv, hvColor⟩ := hjSet.2
      refine ⟨v, ?_, hsv, hvColor⟩
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
      · intro hvI
        have : j = i := Option.some.inj (hvColor.symm.trans (mem_filter.mp hvI).2)
        subst j
        exact hiAvoid hj
      · intro hvZ
        have hvNone := selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
        rw [hvNone] at hvColor
        contradiction
    · right
      refine ⟨A \ C.getD rred ∅, ?_, ?_, ?_⟩
      · have hsA : s ∈ A := (mem_sdiff.mp (mem_sdiff.mp hsAt).1).1
        refine mem_sdiff.mpr ⟨hsA, ?_⟩
        intro hsD
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hrredU) hsD hsH
      · have hrLev := (mem_filter.mp hrredU).1
        have hrJ := (Dyadic.mem_levelIndices.mp hrLev).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.block_complement_minDegree rred hrJ
      · apply ExtensionApplyScratch.degreeOn_eq_of_adjacent_membership_iff
        intro v hsv
        constructor
        · intro hvAt
          change v ∈ (A \ colorClass A phi i) \
            selectedBlockUnion C d.N d.psi i at hvAt
          have hvB : v ∈ A \ colorClass A phi i := (mem_sdiff.mp hvAt).1
          have hvA : v ∈ A := (mem_sdiff.mp hvB).1
          refine mem_sdiff.mpr ⟨hvA, ?_⟩
          intro hvRed
          have hvZ : v ∈ Z := by
            change v ∈ selectedBlockUnion C d.N d.psi i
            rw [selectedBlockUnion, mem_biUnion]
            exact ⟨rred, mem_filter.mpr ⟨hrredN, hrredColor⟩, hvRed⟩
          exact (mem_sdiff.mp hvAt).2 hvZ
        · intro hvComp
          have hvA := (mem_sdiff.mp hvComp).1
          refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
          · intro hvClass
            have hiOld : i ∈ PopularScratch.neighborColorSet G A phi s := by
              rw [PopularScratch.neighborColorSet, mem_filter]
              exact ⟨by simp, v, hvA, hsv, (mem_filter.mp hvClass).2⟩
            have hcardLe : (PopularScratch.neighborColorSet G A phi s).card ≤ k := by
              omega
            have hlistEq := ExtensionApplyScratch.PopularScratch.neighborColorList_eq_of_card_le
              (G := G) phi s hcardLe
            exact hiAvoid (hlistEq.symm ▸ hiOld)
          · intro hvZ
            change v ∈ selectedBlockUnion C d.N d.psi i at hvZ
            rw [selectedBlockUnion, mem_biUnion] at hvZ
            obtain ⟨q, hq, hvq⟩ := hvZ
            have hqN := (mem_filter.mp hq).1
            have hqColor := (mem_filter.mp hq).2
            have hqU := hN hqN
            have hqAdj : AdjacentSets G {s} (C.getD q ∅) :=
              ⟨s, by simp, v, hvq, hsv⟩
            have hqScope : q ∈ d.scope s := by
              rw [hscopeEq]
              change q ∈
                (d.Uidx.filter fun r ↦ AdjacentSets G {s} (C.getD r ∅))
              rw [mem_filter]
              exact ⟨by rw [d.Uidx_eq]; exact hqU, hqAdj⟩
            have hqr := d.injective_scope s hsActive q hqScope hqN
              rred hrredScope hrredN (hqColor.trans hrredColor.symm)
            subst q
            exact (mem_sdiff.mp hvComp).2 hvq

theorem exists_perColorExtensionConclusion_of_greedyLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    Nonempty (ExtensionApplyScratch.PerColorExtensionConclusion
      (residualProtectedFamily S hphi) E
      (fun i ↦ (A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i)) := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let CH := residualProtectedFamily S hphi
  let blockColor : ℕ → Option (Color k) := fun r ↦ some (d.psi r)
  let At : Color k → Finset V := fun i ↦
    (A \ colorClass A phi i) \ selectedBlockUnion C d.N d.psi i
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hZeq : ∀ i, ExtensionApplyScratch.redBlockUnion C d.N blockColor i =
      selectedBlockUnion C d.N d.psi i := by
    intro i
    ext v
    simp only [ExtensionApplyScratch.redBlockUnion,
      ExtensionApplyScratch.redBlockIndices, selectedBlockUnion,
      mem_biUnion, mem_filter]
    constructor
    · rintro ⟨r, ⟨hrN, hrColor⟩, hvr⟩
      exact ⟨r, ⟨hrN, Option.some.inj hrColor⟩, hvr⟩
    · rintro ⟨r, ⟨hrN, hrColor⟩, hvr⟩
      exact ⟨r, ⟨hrN, congrArg some hrColor⟩, hvr⟩
  have hHAt : ∀ i, H ⊆ At i := by
    intro i
    exact (deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i).subset
  have hproper : ∀ i, H ⊂ At i := by
    intro i
    exact deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i
  have hinside : ∀ i, lowVertices G (At i) k ⊆ H := by
    intro i
    have h := ExtensionApplyScratch.lowVertices_currentColor_subset_deficitResidual_succ
      S hphi hellJ d.N hN blockColor i
    simpa [At, H, hZeq i] using h
  have hprotect : ∀ i s, s ∈ E.S → s ∈ At i →
      k ≤ degreeOn G (At i) s := by
    intro i s hsS hsAt
    exact greedyLevel_certificate_protected S hphi hJ0ell hellJ E d i s hsS
      (by simpa [At] using hsAt)
  have hAtA : ∀ i, At i ⊆ A := by
    intro i
    exact sdiff_subset.trans sdiff_subset
  have hfuture : ∀ D ∈ CH.blocks, ∃ r,
      Dyadic.levelStart (ell + 1) ≤ r ∧
      r < Dyadic.levelStart J ∧
      BlockUncolored phi (C.getD r ∅) ∧ D = C.getD r ∅ := by
    intro D hD
    change D ∈
      (residualFutureIndices A C phi ell J).image (fun r ↦ C.getD r ∅) at hD
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hD
    have hrIco := mem_Ico.mp (mem_filter.mp hr).1
    have hrSub := (mem_filter.mp hr).2
    exact ⟨r, hrIco.1, hrIco.2,
      blockUncolored_of_subset_deficitResidual hrSub, rfl⟩
  have hnew : ∀ i D, D ∈ CH.blocks → Anticomplete G (At i \ H) D :=
    ExtensionApplyScratch.extensionDiff_anticomplete_protectedFutureFamily
      S hphi CH rfl At hAtA hfuture
  have hred : ∀ i v, v ∈ lowVertices G (At i) k →
      (∃ r ∈ uncoloredCurrentIndices C phi ell,
        blockColor r = some i ∧ AdjacentSets G {v} (C.getD r ∅)) ∧
      (∀ r ∈ uncoloredCurrentIndices C phi ell,
        AdjacentSets G {v} (C.getD r ∅) → blockColor r = some i) := by
    intro i v hv
    have hraw := ExtensionApplyScratch.lowVertex_currentBlock_color_description
      S hphi hellJ d.N hN blockColor CH E rfl
      (by
        intro j s hsS hsMem
        have hp := hprotect j s hsS
        have hsAt : s ∈ At j := by simpa [At, hZeq j] using hsMem
        simpa [At, hZeq j] using hp hsAt)
      i v
      (by simpa [At, hZeq i] using hv)
    refine ⟨?_, hraw.2⟩
    obtain ⟨r, hrN, hrColor, hrAdj⟩ := hraw.1
    exact ⟨r, hN hrN, hrColor, hrAdj⟩
  have hR := ExtensionApplyScratch.apply_extension_per_color_indices
    CH E S.hk C At hHAt hproper hinside hprotect hnew
    (uncoloredCurrentIndices C phi ell) blockColor hred
  simpa [At] using hR

theorem successorData_of_greedyLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  obtain ⟨R⟩ := exists_perColorExtensionConclusion_of_greedyLevel
    S hphi hJ0ell hellJ E d
  exact successorData_of_greedy_and_extensions S hphi hJ0ell hellJ E d R

theorem exists_successorData_of_large_uncoloredLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  obtain ⟨E⟩ := exists_residualExtensionCertificate S hphi hJ0ell
  have hshort := shortage_deficitResidual_le_twelve
    S hphi hJ0ell hellJ hlarge
  obtain ⟨d⟩ := exists_greedyLevelData E S.hk hshort
  exact successorData_of_greedyLevel S hphi hJ0ell hellJ E d


end

/-- Every appropriate colouring extends through the next dyadic level. -/
theorem exists_appropriateColoring_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J) :
    ∃ rho, Appropriate G A k C J0 (ell + 1) J rho := by
  by_cases hquarter :
      4 * uncoloredBlockCount C phi ell ≤ 2 ^ ell
  · exact ⟨phi, hphi.advance_without_change hquarter⟩
  · have hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell := by omega
    exact appropriateColoring_succ hphi
      (exists_successorData_of_large_uncoloredLevel
        S hphi hJ0ell hellJ hlarge)

/-- Iterating the successor construction gives an appropriate colouring
through every retained dyadic level. -/
theorem exists_finalAppropriate
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 J : ℕ}
    (S : ColoringSystem G A k t C J0 J) :
    ∃ phi, Appropriate G A k C J0 J J phi := by
  let P : (ell : ℕ) → J0 ≤ ell → Prop := fun ell _ ↦
    ell ≤ J → ∃ phi, Appropriate G A k C J0 ell J phi
  have hbase : P J0 (Nat.le_refl J0) := by
    intro _
    exact ⟨fun _ ↦ none, appropriate_uncolored S.minDegree⟩
  have hstep : ∀ (ell : ℕ) (hJ0ell : J0 ≤ ell), P ell hJ0ell →
      P (ell + 1) (Nat.le_succ_of_le hJ0ell) := by
    intro ell hJ0ell ih hell1J
    have hellJ : ell ≤ J := (Nat.le_succ ell).trans hell1J
    have hellLtJ : ell < J := Nat.lt_of_succ_le hell1J
    obtain ⟨phi, hphi⟩ := ih hellJ
    exact exists_appropriateColoring_succ S hphi hJ0ell hellLtJ
  exact Nat.le_induction (P := P) hbase hstep J S.hJ (Nat.le_refl J)

/-- Sauermann's local-expansion step: an ambient counterexample necessarily
contains the prescribed smaller nonempty induced subgraph of minimum degree
at least (k). -/
theorem exists_small_core_of_localExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t)
    (hlocal : LocalExpansion G A k)
    (hmin : HasMinDegreeOn G A k)
    (hconn : ConnectedOn G A) :
    ∃ W, IsSmallCoreOn G A k (uniformDen k) W := by
  classical
  by_contra hno
  have hno' : NoSmallCoreOn G A k (uniformDen k) := hno
  obtain ⟨C, J0, J, S⟩ := exists_coloringSystem G k t hk ht A hcard
    hshort hlocal hmin hconn hno'
  obtain ⟨phi, hphi⟩ := exists_finalAppropriate S
  exact hno' (smallCore_of_appropriate_and_colored hk hphi
    (final_colored_mass S hphi))

end Erdos814
