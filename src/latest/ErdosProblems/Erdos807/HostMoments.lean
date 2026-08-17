/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos807.Overlap
import ErdosProblems.Erdos807.Probability
import ErdosProblems.Erdos807.SecondMoment
import ErdosProblems.Erdos807.HostFamily
import ErdosProblems.Erdos807.SlotEdges

/-!
# Intersection expansion for host-family witness counts

The second moment of a count of witnesses supported on `k`-subsets is an
ordered-pair sum.  This file first proves that fact for an arbitrary finite
uniform probability space, and then partitions the ordered pairs exactly by
the size of their intersection.  The graph-specific estimates for the
canonical ABH host family are developed below this reusable core.
-/

open scoped BigOperators

namespace Erdos807
namespace HostMoments

open Finset
open FiniteUniform

variable {Omega alpha : Type*} [Fintype Omega] [Nonempty Omega]
variable [DecidableEq alpha]

/-- The number of members of a finite family whose event occurs. -/
noncomputable def eventCount {I : Type*} (S : Finset I)
    (P : I → Omega → Prop) (omega : Omega) : ℕ := by
  classical
  exact (S.filter fun i => P i omega).card

/-- A natural-valued event count is the corresponding sum of real indicators. -/
lemma eventCount_cast_eq_indicatorCount {I : Type*} (S : Finset I)
    (P : I → Omega → Prop) (omega : Omega) :
    (eventCount S P omega : ℝ) = indicatorCount S P omega := by
  classical
  unfold eventCount indicatorCount
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp [indicator]

/-- Exact ordered-pair expansion of the second moment of a finite event count. -/
theorem natSecondMoment_eventCount {I : Type*} (S : Finset I)
    (P : I → Omega → Prop) :
    natSecondMoment (eventCount S P) =
      ∑ i ∈ S, ∑ j ∈ S, probability (fun omega ↦ P i omega ∧ P j omega) := by
  have hfun : (fun omega ↦ (eventCount S P omega : ℝ)) = indicatorCount S P := by
    funext omega
    exact eventCount_cast_eq_indicatorCount S P omega
  change secondMoment (fun omega ↦ (eventCount S P omega : ℝ)) = _
  rw [hfun]
  exact secondMoment_indicatorCount S P

/-- Exact first moment of a natural-valued finite event count. -/
theorem natExpectation_eventCount {I : Type*} (S : Finset I)
    (P : I → Omega → Prop) :
    natExpectation (eventCount S P) = ∑ i ∈ S, probability (P i) := by
  have hfun : (fun omega ↦ (eventCount S P omega : ℝ)) = indicatorCount S P := by
    funext omega
    exact eventCount_cast_eq_indicatorCount S P omega
  change expectation (fun omega ↦ (eventCount S P omega : ℝ)) = _
  rw [hfun]
  exact expectation_indicatorCount S P

/-- The contribution from ordered pairs of `k`-sets meeting in exactly `i` points. -/
noncomputable def intersectionContribution (s : Finset alpha) (k i : Nat)
    (P : Finset alpha → Omega → Prop) : ℝ :=
  ∑ AB ∈ Overlap.pairs s k i,
    probability (fun omega ↦ P AB.1 omega ∧ P AB.2 omega)

/-- The ordered-pair sum over all `k`-sets is exactly the sum of the
intersection strata `0, ..., k`. -/
theorem sum_pairProbability_eq_sum_intersectionContribution
    (s : Finset alpha) (k : Nat) (P : Finset alpha → Omega → Prop) :
    (∑ A ∈ s.powersetCard k, ∑ B ∈ s.powersetCard k,
        probability (fun omega ↦ P A omega ∧ P B omega)) =
      ∑ i ∈ range (k + 1), intersectionContribution s k i P := by
  classical
  let S := s.powersetCard k
  let f : Finset alpha × Finset alpha → ℝ := fun AB ↦
    probability (fun omega ↦ P AB.1 omega ∧ P AB.2 omega)
  have hinter (AB : Finset alpha × Finset alpha) (hAB : AB ∈ S ×ˢ S) :
      (AB.1 ∩ AB.2).card < k + 1 := by
    have hleft : AB.1.card = k := (mem_powersetCard.mp (mem_product.mp hAB).1).2
    have hle : (AB.1 ∩ AB.2).card ≤ AB.1.card := card_le_card inter_subset_left
    omega
  calc
    (∑ A ∈ s.powersetCard k, ∑ B ∈ s.powersetCard k,
        probability (fun omega ↦ P A omega ∧ P B omega)) =
        ∑ AB ∈ S ×ˢ S, f AB := by
          simp only [S, sum_product, f]
    _ = ∑ AB ∈ S ×ˢ S,
          ∑ i ∈ range (k + 1), if (AB.1 ∩ AB.2).card = i then f AB else 0 := by
          apply sum_congr rfl
          intro AB hAB
          simpa [eq_comm, hinter AB hAB] using
            (sum_ite_eq' (range (k + 1)) (AB.1 ∩ AB.2).card (fun _ ↦ f AB))
    _ = ∑ i ∈ range (k + 1),
          ∑ AB ∈ S ×ˢ S, if (AB.1 ∩ AB.2).card = i then f AB else 0 := by
          rw [sum_comm]
    _ = ∑ i ∈ range (k + 1), intersectionContribution s k i P := by
          apply sum_congr rfl
          intro i hi
          simp only [intersectionContribution, Overlap.pairs, sum_filter, S, f]

/-- Exact second moment of a count of `k`-set witnesses, grouped by
intersection size. -/
theorem natSecondMoment_eventCount_eq_sum_intersectionContribution
    (s : Finset alpha) (k : Nat) (P : Finset alpha → Omega → Prop) :
    natSecondMoment (eventCount (s.powersetCard k) P) =
      ∑ i ∈ range (k + 1), intersectionContribution s k i P := by
  rw [natSecondMoment_eventCount]
  exact sum_pairProbability_eq_sum_intersectionContribution s k P

/-! ## Uniform bounds for an intersection stratum -/

/-- Bounding every ordered pair in a stratum by the same number bounds the
whole contribution by the cardinality of the stratum times that number. -/
theorem intersectionContribution_le_card_mul
    (s : Finset alpha) (k i : ℕ) (P : Finset alpha → Omega → Prop) (q : ℝ)
    (hq : ∀ AB ∈ Overlap.pairs s k i,
      probability (fun omega ↦ P AB.1 omega ∧ P AB.2 omega) ≤ q) :
    intersectionContribution s k i P ≤ (#(Overlap.pairs s k i) : ℝ) * q := by
  classical
  rw [intersectionContribution]
  calc
    (∑ AB ∈ Overlap.pairs s k i,
        probability (fun omega ↦ P AB.1 omega ∧ P AB.2 omega)) ≤
        ∑ _AB ∈ Overlap.pairs s k i, q :=
      sum_le_sum fun AB hAB ↦ hq AB hAB
    _ = (#(Overlap.pairs s k i) : ℝ) * q := by simp

/-- Closed form of the preceding stratum estimate. -/
theorem intersectionContribution_le_choose_mul
    (s : Finset alpha) (k i : ℕ) (hik : i ≤ k)
    (P : Finset alpha → Omega → Prop) (q : ℝ)
    (hq : ∀ AB ∈ Overlap.pairs s k i,
      probability (fun omega ↦ P AB.1 omega ∧ P AB.2 omega) ≤ q) :
    intersectionContribution s k i P ≤
      (Nat.choose #s k * Nat.choose k i * Nat.choose (#s - k) (k - i) : ℕ) * q := by
  rw [← Overlap.card_pairs s k i hik]
  exact intersectionContribution_le_card_mul s k i P q hq

/-! ## Relating the two finite-uniform probability presentations -/

/-- `FiniteUniform.probability` and the edge-coordinate probability from
`Probability.lean` are definitionally the same uniform measure on labelled
graphs. -/
theorem finiteUniform_probability_eq_randomGraph_probability
    (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    FiniteUniform.probability P = RandomGraph.probability n P := by
  classical
  have hnum : Nat.card {omega // P omega} = RandomGraph.eventCard n P := by
    rw [Nat.card_eq_fintype_card, RandomGraph.eventCard, Set.ncard_eq_toFinset_card',
      Set.toFinset_ofPred]
    exact Fintype.card_subtype P
  rw [FiniteUniform.probability, RandomGraph.probability, hnum,
    RandomGraph.card_simpleGraph]

/-! ## Prescriptions on two overlapping coordinate sets -/

/-- Two consistent edge prescriptions imply their union prescription.  No
separate compatibility hypothesis is needed: incompatibility simply makes
the conjunction empty. -/
theorem prescribed_and_prescribed_imp_union {n : ℕ}
    {A B C D : Finset (RandomGraph.Edge n)}
    {G : SimpleGraph (Fin n)}
    (hAB : RandomGraph.Prescribed A B G)
    (hCD : RandomGraph.Prescribed C D G) :
    RandomGraph.Prescribed (A ∪ C) (B ∪ D) G := by
  unfold RandomGraph.Prescribed at hAB hCD ⊢
  unfold Erdos565.RandomGraph.restrict at hAB hCD ⊢
  rw [Finset.inter_union_distrib_left, hAB, hCD]

/-- The joint probability of two consistent prescriptions is at most the
probability of prescribing every coordinate in their union. -/
theorem probability_prescribed_and_le {n : ℕ}
    {A B C D : Finset (RandomGraph.Edge n)}
    (hB : B ⊆ A) (hD : D ⊆ C) :
    RandomGraph.probability n (fun G ↦
        RandomGraph.Prescribed A B G ∧ RandomGraph.Prescribed C D G) ≤
      (1 / 2 : ℝ) ^ (A ∪ C).card := by
  calc
    RandomGraph.probability n (fun G ↦
        RandomGraph.Prescribed A B G ∧ RandomGraph.Prescribed C D G) ≤
        RandomGraph.probability n (RandomGraph.Prescribed (A ∪ C) (B ∪ D)) := by
      apply RandomGraph.probability_mono
      intro G hG
      exact prescribed_and_prescribed_imp_union hG.1 hG.2
    _ = (1 / 2 : ℝ) ^ (A ∪ C).card :=
      RandomGraph.probability_prescribed (Finset.union_subset_union hB hD)

/-! ## Bucketed host choices -/

/-- A host choice selects one vertex from each of `k` labelled buckets, each
of size `q`. -/
abbrev HostChoice (k q : ℕ) := Fin k → Fin q

/-- The set of slots in which two host choices agree.  Because buckets are
disjoint, this is also the vertex intersection of the two embedded hosts. -/
def equalSlotSet {k q : ℕ} (c d : HostChoice k q) : Finset (Fin k) :=
  Finset.univ.filter fun s ↦ c s = d s

/-- The number of common selected vertices of two bucketed hosts. -/
def slotOverlap {k q : ℕ} (c d : HostChoice k q) : ℕ :=
  (equalSlotSet c d).card

/-- Ordered host-choice pairs having exactly `i` common slots. -/
def choicePairs (k q i : ℕ) : Finset (HostChoice k q × HostChoice k q) :=
  (Finset.univ ×ˢ Finset.univ).filter fun cd ↦ slotOverlap cd.1 cd.2 = i

@[simp] theorem mem_choicePairs {k q i : ℕ} {c d : HostChoice k q} :
    (c, d) ∈ choicePairs k q i ↔ slotOverlap c d = i := by
  simp [choicePairs]

/-- Allowed values at a slot when the equality set with `c` is required to
be exactly `S`. -/
def allowedAt {k q : ℕ} (c : HostChoice k q) (S : Finset (Fin k))
    (s : Fin k) : Finset (Fin q) :=
  if s ∈ S then {c s} else Finset.univ.erase (c s)

theorem mem_piFinset_allowedAt_iff_equalSlotSet_eq {k q : ℕ}
    (c d : HostChoice k q) (S : Finset (Fin k)) :
    d ∈ Fintype.piFinset (allowedAt c S) ↔ equalSlotSet c d = S := by
  classical
  rw [Fintype.mem_piFinset]
  constructor
  · intro hd
    ext s
    by_cases hs : s ∈ S
    · have hds := hd s
      simp [allowedAt, hs] at hds
      simp [equalSlotSet, hs, hds.symm]
    · have hds := hd s
      simp [allowedAt, hs] at hds
      simp [equalSlotSet, hs, Ne.symm hds]
  · intro heq s
    have hs : s ∈ equalSlotSet c d ↔ s ∈ S := by rw [heq]
    by_cases hS : s ∈ S
    · have hcd : c s = d s := by simpa [equalSlotSet, hS] using hs.mpr hS
      simp [allowedAt, hS, hcd.symm]
    · have hcd : c s ≠ d s := by
        intro h
        exact hS (hs.mp (by simp [equalSlotSet, h]))
      simp [allowedAt, hS, Ne.symm hcd]

/-- The choices whose equality set with `c` is exactly `S` form the product
of the singleton/everything-but-`c` coordinate sets. -/
theorem filter_equalSlotSet_eq (c : HostChoice k q) (S : Finset (Fin k)) :
    (Finset.univ.filter fun d : HostChoice k q ↦ equalSlotSet c d = S) =
      Fintype.piFinset (allowedAt c S) := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_piFinset_allowedAt_iff_equalSlotSet_eq c d S).symm

/-- For a fixed equality set `S`, every non-equal slot has exactly `q-1`
choices. -/
theorem card_filter_equalSlotSet_eq (c : HostChoice k q) (S : Finset (Fin k)) :
    #((Finset.univ : Finset (HostChoice k q)).filter fun d ↦
        equalSlotSet c d = S) = (q - 1) ^ (k - S.card) := by
  classical
  rw [filter_equalSlotSet_eq, Fintype.card_piFinset]
  have hcard (s : Fin k) : #(allowedAt c S s) = if s ∈ S then 1 else q - 1 := by
    by_cases hs : s ∈ S
    · simp [allowedAt, hs]
    · simp [allowedAt, hs]
  simp_rw [hcard]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  calc
    #{s : Fin k | s ∉ S} = #Sᶜ := by congr 1; ext s; simp
    _ = Fintype.card (Fin k) - #S := by
      simpa using (Finset.card_compl (s := S))
    _ = k - #S := by simp

/-- For a fixed host choice, the number of choices agreeing with it in
exactly `i` slots is `choose k i * (q-1)^(k-i)`. -/
theorem card_fixed_left_choice (c : HostChoice k q) (i : ℕ) :
    #((Finset.univ : Finset (HostChoice k q)).filter fun d ↦
        slotOverlap c d = i) = Nat.choose k i * (q - 1) ^ (k - i) := by
  classical
  let D := (Finset.univ : Finset (HostChoice k q)).filter fun d ↦
    slotOverlap c d = i
  let T := (Finset.univ : Finset (Fin k)).powersetCard i
  have hmap : Set.MapsTo (equalSlotSet c) (D : Set (HostChoice k q)) T := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hd.2⟩
  rw [show (Finset.univ.filter fun d : HostChoice k q ↦ slotOverlap c d = i) = D
      from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ S ∈ T, #{d ∈ D | equalSlotSet c d = S}) =
        ∑ S ∈ T, (q - 1) ^ (k - S.card) := by
      apply sum_congr rfl
      intro S hS
      have hSi : S.card = i := (Finset.mem_powersetCard.mp hS).2
      rw [show (D.filter fun d ↦ equalSlotSet c d = S) =
          (Finset.univ.filter fun d : HostChoice k q ↦ equalSlotSet c d = S) by
        ext d
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h ↦ h.2
        · intro h
          refine ⟨?_, h⟩
          change slotOverlap c d = i
          rw [slotOverlap, h, hSi]
        ]
      exact card_filter_equalSlotSet_eq c S
    _ = ∑ _S ∈ T, (q - 1) ^ (k - i) := by
      apply sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = Nat.choose k i * (q - 1) ^ (k - i) := by simp [T]

/-- Exact cardinality of the ordered intersection-`i` stratum of bucketed
host choices. -/
theorem card_choicePairs (k q i : ℕ) :
    #(choicePairs k q i) =
      q ^ k * (Nat.choose k i * (q - 1) ^ (k - i)) := by
  classical
  let C := (Finset.univ : Finset (HostChoice k q))
  have hmap : Set.MapsTo Prod.fst
      (choicePairs k q i : Set (HostChoice k q × HostChoice k q))
      (C : Set (HostChoice k q)) := by
    intro cd hcd
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ c ∈ C, #{cd ∈ choicePairs k q i | cd.1 = c}) =
        ∑ c ∈ C, Nat.choose k i * (q - 1) ^ (k - i) := by
      apply sum_congr rfl
      intro c hc
      rw [← card_fixed_left_choice c i]
      symm
      apply Finset.card_bij (fun d _ ↦ (c, d))
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        simp [choicePairs, hd]
      · intro d hd
        rintro d' hd' heq
        exact congrArg Prod.snd heq
      · intro cd hcd
        refine ⟨cd.2, ?_, ?_⟩
        · have hp := (Finset.mem_filter.mp hcd).1
          have hfirst := (Finset.mem_filter.mp hcd).2
          have hi := mem_choicePairs.mp hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [hfirst] using hi
        · apply Prod.ext
          · exact (Finset.mem_filter.mp hcd).2.symm
          · rfl
    _ = q ^ k * (Nat.choose k i * (q - 1) ^ (k - i)) := by
      simp [C, Fintype.card_fun]

/-- The probability contribution of an exact slot-overlap stratum. -/
noncomputable def choiceIntersectionContribution (k q i : ℕ)
    (P : HostChoice k q → Omega → Prop) : ℝ :=
  ∑ cd ∈ choicePairs k q i,
    probability (fun omega ↦ P cd.1 omega ∧ P cd.2 omega)

/-- Exact second moment of a bucketed-host witness count, grouped by the
number of common slots. -/
theorem natSecondMoment_choiceCount_eq_sum_intersectionContribution
    (k q : ℕ) (P : HostChoice k q → Omega → Prop) :
    natSecondMoment (eventCount Finset.univ P) =
      ∑ i ∈ range (k + 1), choiceIntersectionContribution k q i P := by
  classical
  rw [natSecondMoment_eventCount]
  let C := (Finset.univ : Finset (HostChoice k q))
  let f : HostChoice k q × HostChoice k q → ℝ := fun cd ↦
    probability (fun omega ↦ P cd.1 omega ∧ P cd.2 omega)
  have hoverlap (c d : HostChoice k q) : slotOverlap c d < k + 1 := by
    unfold slotOverlap
    have hle : (equalSlotSet c d).card ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    simpa using (Nat.lt_succ_of_le hle)
  calc
    (∑ c ∈ (Finset.univ : Finset (HostChoice k q)),
        ∑ d ∈ (Finset.univ : Finset (HostChoice k q)),
          probability (fun omega ↦ P c omega ∧ P d omega)) =
        ∑ cd ∈ C ×ˢ C, f cd := by rw [sum_product]
    _ = ∑ cd ∈ C ×ˢ C, ∑ i ∈ range (k + 1),
          if slotOverlap cd.1 cd.2 = i then f cd else 0 := by
      apply sum_congr rfl
      intro cd hcd
      simpa [eq_comm, hoverlap cd.1 cd.2] using
        (sum_ite_eq' (range (k + 1)) (slotOverlap cd.1 cd.2) (fun _ ↦ f cd))
    _ = ∑ i ∈ range (k + 1), ∑ cd ∈ C ×ˢ C,
          if slotOverlap cd.1 cd.2 = i then f cd else 0 := by rw [sum_comm]
    _ = ∑ i ∈ range (k + 1), choiceIntersectionContribution k q i P := by
      apply sum_congr rfl
      intro i hi
      simp only [choiceIntersectionContribution, choicePairs, sum_filter, C, f]

/-- A uniform pair-event estimate bounds a whole choice intersection
stratum, with its exact combinatorial multiplicity. -/
theorem choiceIntersectionContribution_le
    (k q i : ℕ) (P : HostChoice k q → Omega → Prop) (p : ℝ)
    (hp : ∀ cd ∈ choicePairs k q i,
      probability (fun omega ↦ P cd.1 omega ∧ P cd.2 omega) ≤ p) :
    choiceIntersectionContribution k q i P ≤
      (q ^ k * (Nat.choose k i * (q - 1) ^ (k - i)) : ℕ) * p := by
  classical
  rw [choiceIntersectionContribution]
  calc
    (∑ cd ∈ choicePairs k q i,
        probability (fun omega ↦ P cd.1 omega ∧ P cd.2 omega)) ≤
        ∑ _cd ∈ choicePairs k q i, p := sum_le_sum fun cd hcd ↦ hp cd hcd
    _ = (#(choicePairs k q i) : ℝ) * p := by simp
    _ = (q ^ k * (Nat.choose k i * (q - 1) ^ (k - i)) : ℕ) * p := by
      rw [card_choicePairs]

/-! ## The canonical large-overlap matrix code -/

open StructuredFamily

/-- Slots at which two bucket choices differ. -/
def differingSlots {k q : ℕ} (c d : HostChoice k q) : Finset (Fin k) :=
  Finset.univ.filter fun s ↦ c s ≠ d s

/-- The increasing enumeration of the differing slots. -/
noncomputable def differingSlotAt {k q j : ℕ} (c d : HostChoice k q)
    (hdiff : (differingSlots c d).card = j) (t : Fin j) : Fin k :=
  ((differingSlots c d).orderIsoOfFin hdiff t).1

theorem differingSlotAt_mem {k q j : ℕ} (c d : HostChoice k q)
    (hdiff : (differingSlots c d).card = j) (t : Fin j) :
    differingSlotAt c d hdiff t ∈ differingSlots c d :=
  ((differingSlots c d).orderIsoOfFin hdiff t).2

theorem exists_differingSlotAt_eq {k q j : ℕ} (c d : HostChoice k q)
    (hdiff : (differingSlots c d).card = j) {s : Fin k}
    (hs : s ∈ differingSlots c d) :
    ∃ t : Fin j, differingSlotAt c d hdiff t = s := by
  let s' : differingSlots c d := ⟨s, hs⟩
  obtain ⟨t, ht⟩ := (differingSlots c d).orderIsoOfFin hdiff |>.surjective s'
  exact ⟨t, congrArg Subtype.val ht⟩

/-- Split a right-vertex index into one of ten chunks and an index inside a
chunk of size `9r`. -/
noncomputable def rightChunkEquiv (r : ℕ) :
    Fin 10 × Fin (9 * r) ≃ Fin (90 * r) :=
  finProdFinEquiv.trans (Equiv.cast (by congr 1 <;> omega))

/-- The `10*r*j` Boolean coordinates which suffice to reconstruct a
compatible matrix when `j` slots of the host choice change. -/
abbrev LargeOverlapCode (r j : ℕ) :=
  ((Fin r × Fin j) → Bool) × ((Fin (9 * r) × Fin j) → Bool)

theorem card_largeOverlapCode (r j : ℕ) :
    Fintype.card (LargeOverlapCode r j) = 2 ^ (10 * r * j) := by
  simp only [LargeOverlapCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  ring

/-- Matrix agreement forced by the edges visible in the common slots. -/
def MatrixCompatible {q : ℕ} (c : HostChoice (100 * r) q) (M : Matrix r)
    (d : HostChoice (100 * r) q) (N : Matrix r) : Prop :=
  ∀ i a b,
    c (leftVertex r i a) = d (leftVertex r i a) →
    c (rightVertex r b) = d (rightVertex r b) →
    M i b = N i b

/-- The canonical free-coordinate code.  Its first part records matrix
entries at missing right slots.  Its second part splits the `90r` right
indices into ten chunks and records a chunk at each missing left slot. -/
noncomputable def matrixExtensionCode {q j : ℕ}
    (c d : HostChoice (100 * r) q)
    (hdiff : (differingSlots c d).card = j) (N : Matrix r) :
    LargeOverlapCode r j :=
  (fun it ↦
      match (vertexEquiv r).symm (differingSlotAt c d hdiff it.2) with
      | Sum.inl _ => false
      | Sum.inr b => N it.1 b,
    fun ut ↦
      match (vertexEquiv r).symm (differingSlotAt c d hdiff ut.2) with
      | Sum.inl (i, a) => N i (rightChunkEquiv r (a, ut.1))
      | Sum.inr _ => false)

/-- Compatible extensions inject into the `10*r*j`-bit canonical code. -/
theorem matrixExtensionCode_injOn {q j : ℕ}
    (c d : HostChoice (100 * r) q)
    (hdiff : (differingSlots c d).card = j) (M : Matrix r)
    (F : Finset (Matrix r))
    (hF : ∀ N ∈ F, MatrixCompatible c M d N) :
    (F : Set (Matrix r)).InjOn (matrixExtensionCode c d hdiff) := by
  classical
  intro N₁ hN₁ N₂ hN₂ hcode
  have hcomp₁ := hF N₁ hN₁
  have hcomp₂ := hF N₂ hN₂
  funext i b
  by_cases hright : c (rightVertex r b) = d (rightVertex r b)
  · by_cases hleft : ∃ a : Fin 10,
        c (leftVertex r i a) = d (leftVertex r i a)
    · obtain ⟨a, ha⟩ := hleft
      exact (hcomp₁ i a b ha hright).symm.trans (hcomp₂ i a b ha hright)
    · let p := (rightChunkEquiv r).symm b
      have hslot : leftVertex r i p.1 ∈ differingSlots c d := by
        simp only [differingSlots, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h ↦ hleft ⟨p.1, h⟩
      obtain ⟨t, ht⟩ := exists_differingSlotAt_eq c d hdiff hslot
      have hraw : (vertexEquiv r).symm (differingSlotAt c d hdiff t) =
          Sum.inl (i, p.1) := by
        rw [ht]
        simp [leftVertex]
      have hcomponent := congrFun (congrArg Prod.snd hcode) (p.2, t)
      simpa [matrixExtensionCode, hraw, p] using hcomponent
  · have hslot : rightVertex r b ∈ differingSlots c d := by
      simp [differingSlots, hright]
    obtain ⟨t, ht⟩ := exists_differingSlotAt_eq c d hdiff hslot
    have hraw : (vertexEquiv r).symm (differingSlotAt c d hdiff t) =
        Sum.inr b := by
      rw [ht]
      simp [rightVertex]
    have hcomponent := congrFun (congrArg Prod.fst hcode) (i, t)
    simpa [matrixExtensionCode, hraw] using hcomponent

/-- At most `2^(10*r*j)` matrices can be compatible with a fixed matrix on
two choices differing in `j` slots. -/
noncomputable def compatibleMatrices {q : ℕ}
    (c : HostChoice (100 * r) q) (M : Matrix r)
    (d : HostChoice (100 * r) q) : Finset (Matrix r) := by
  classical
  exact Finset.univ.filter fun N ↦ MatrixCompatible c M d N

theorem card_matrixExtensions_le {q j : ℕ}
    (c d : HostChoice (100 * r) q)
    (hdiff : (differingSlots c d).card = j) (M : Matrix r) :
    #(compatibleMatrices c M d) ≤
      2 ^ (10 * r * j) := by
  classical
  let F := compatibleMatrices c M d
  calc
    #F ≤ #(Finset.univ : Finset (LargeOverlapCode r j)) :=
      Finset.card_le_card_of_injOn (matrixExtensionCode c d hdiff)
        (fun _ _ ↦ Finset.mem_univ _)
        (matrixExtensionCode_injOn c d hdiff M F (by
          intro N hN
          exact (Finset.mem_filter.mp hN).2))
    _ = Fintype.card (LargeOverlapCode r j) := Finset.card_univ
    _ = 2 ^ (10 * r * j) := card_largeOverlapCode r j

/-! ## Concrete moments of `HostFamily.witnessCount` -/

/-- The host-family count is the generic event count over all bucket choices. -/
theorem host_witnessCount_eq_eventCount (n r : ℕ) :
    HostFamily.witnessCount n r =
      eventCount (Finset.univ : Finset (HostFamily.Choice n r))
        HostFamily.FixedChoiceEvent := by
  funext G
  rfl

/-- Exact first moment of the stable-slot host count. -/
theorem natExpectation_host_witnessCount (n r : ℕ) :
    natExpectation (HostFamily.witnessCount n r) =
      (HostFamily.bucketSize n r ^ HostFamily.templateOrder r : ℕ) *
        ((2 : ℝ) ^ (90 * r * r) *
          (1 / 2 : ℝ) ^ (HostFamily.templateOrder r).choose 2) := by
  rw [host_witnessCount_eq_eventCount, natExpectation_eventCount]
  simp_rw [finiteUniform_probability_eq_randomGraph_probability,
    HostFamily.probability_fixedChoiceEvent]
  simp [HostFamily.card_choice]

/-- The exact contribution from pairs of stable choices with `i` common
slots. -/
noncomputable def hostIntersectionContribution (n r i : ℕ) : ℝ :=
  choiceIntersectionContribution (HostFamily.templateOrder r)
    (HostFamily.bucketSize n r) i HostFamily.FixedChoiceEvent

/-- Exact second moment of the host-family witness count, grouped by common
slots. -/
theorem natSecondMoment_host_witnessCount (n r : ℕ) :
    natSecondMoment (HostFamily.witnessCount n r) =
      ∑ i ∈ range (HostFamily.templateOrder r + 1),
        hostIntersectionContribution n r i := by
  rw [host_witnessCount_eq_eventCount]
  exact natSecondMoment_choiceCount_eq_sum_intersectionContribution
    (HostFamily.templateOrder r) (HostFamily.bucketSize n r)
      HostFamily.FixedChoiceEvent

/-! ## Pair-event probability bounds -/

/-- Two matrix events occurring in one host graph force agreement of their
matrix entries whenever both endpoint slots are common. -/
theorem slotMatrixEvents_imp_matrixCompatible {n r : ℕ}
    {c d : HostFamily.Choice n r} {M N : Matrix r}
    {G : SimpleGraph (Fin n)}
    (hM : HostFamily.SlotMatrixEvent c M G)
    (hN : HostFamily.SlotMatrixEvent d N G) :
    MatrixCompatible c M d N := by
  intro i a b hleft hright
  have hleftEmb : HostFamily.slotEmbedding c (leftVertex r i a) =
      HostFamily.slotEmbedding d (leftVertex r i a) :=
    (HostFamily.slotEmbedding_eq_iff c d _ _).2 ⟨rfl, hleft⟩
  have hrightEmb : HostFamily.slotEmbedding c (rightVertex r b) =
      HostFamily.slotEmbedding d (rightVertex r b) :=
    (HostFamily.slotEmbedding_eq_iff c d _ _).2 ⟨rfl, hright⟩
  apply Bool.eq_iff_iff.mpr
  calc
    M i b = true ↔ (graph M).Adj (leftVertex r i a) (rightVertex r b) :=
      (graph_adj_left_right_iff M i a b).symm
    _ ↔ (G.comap (HostFamily.slotEmbedding c)).Adj
        (leftVertex r i a) (rightVertex r b) := by rw [hM]
    _ ↔ G.Adj (HostFamily.slotEmbedding c (leftVertex r i a))
        (HostFamily.slotEmbedding c (rightVertex r b)) := Iff.rfl
    _ ↔ G.Adj (HostFamily.slotEmbedding d (leftVertex r i a))
        (HostFamily.slotEmbedding d (rightVertex r b)) := by
      rw [hleftEmb, hrightEmb]
    _ ↔ (G.comap (HostFamily.slotEmbedding d)).Adj
        (leftVertex r i a) (rightVertex r b) := Iff.rfl
    _ ↔ (graph N).Adj (leftVertex r i a) (rightVertex r b) := by rw [hN]
    _ ↔ N i b = true := graph_adj_left_right_iff N i a b

/-- Joint probability of two specified matrices.  The two events prescribe
all edge coordinates in the union of the two host edge blocks. -/
theorem probability_slotMatrixEvent_and_le {n r : ℕ}
    (c d : HostFamily.Choice n r) (M N : Matrix r) :
    RandomGraph.probability n (fun G ↦
        HostFamily.SlotMatrixEvent c M G ∧ HostFamily.SlotMatrixEvent d N G) ≤
      (1 / 2 : ℝ) ^
        (2 * (HostFamily.templateOrder r).choose 2 -
          (HostFamily.agreementSlots c d).card.choose 2) := by
  let A := HostFamily.embeddingEdges (HostFamily.slotEmbedding c)
  let B := HostFamily.fixedEdges (HostFamily.slotEmbedding c) (graph M)
  let C := HostFamily.embeddingEdges (HostFamily.slotEmbedding d)
  let D := HostFamily.fixedEdges (HostFamily.slotEmbedding d) (graph N)
  calc
    RandomGraph.probability n (fun G ↦
        HostFamily.SlotMatrixEvent c M G ∧ HostFamily.SlotMatrixEvent d N G) =
        RandomGraph.probability n (fun G ↦
          RandomGraph.Prescribed A B G ∧ RandomGraph.Prescribed C D G) := by
      congr 1
      funext G
      apply propext
      exact and_congr (HostFamily.slotMatrixEvent_iff_prescribed c M G)
        (HostFamily.slotMatrixEvent_iff_prescribed d N G)
    _ ≤ (1 / 2 : ℝ) ^ (A ∪ C).card :=
      probability_prescribed_and_le
        (HostFamily.fixedEdges_subset_embeddingEdges _ _)
        (HostFamily.fixedEdges_subset_embeddingEdges _ _)
    _ = (1 / 2 : ℝ) ^
        (2 * (HostFamily.templateOrder r).choose 2 -
          (HostFamily.agreementSlots c d).card.choose 2) := by
      rw [HostFamily.card_embeddingEdges_union]

/-- Crude pair bound: ignore compatibility and sum over both free matrices. -/
theorem probability_fixedChoiceEvent_and_le {n r : ℕ}
    (c d : HostFamily.Choice n r) :
    RandomGraph.probability n (fun G ↦
        HostFamily.FixedChoiceEvent c G ∧ HostFamily.FixedChoiceEvent d G) ≤
      (2 ^ (90 * r * r) : ℕ) ^ 2 *
        (1 / 2 : ℝ) ^
          (2 * (HostFamily.templateOrder r).choose 2 -
            (HostFamily.agreementSlots c d).card.choose 2) := by
  classical
  have hmatrix : Fintype.card (Matrix r) = 2 ^ (90 * r * r) :=
    StructuredFamily.card_matrix r
  let p := (1 / 2 : ℝ) ^
    (2 * (HostFamily.templateOrder r).choose 2 -
      (HostFamily.agreementSlots c d).card.choose 2)
  calc
    RandomGraph.probability n (fun G ↦
        HostFamily.FixedChoiceEvent c G ∧ HostFamily.FixedChoiceEvent d G) ≤
        RandomGraph.probability n (fun G ↦
          ∃ MN ∈ (Finset.univ : Finset (Matrix r × Matrix r)),
            HostFamily.SlotMatrixEvent c MN.1 G ∧
              HostFamily.SlotMatrixEvent d MN.2 G) := by
      apply RandomGraph.probability_mono
      rintro G ⟨⟨M, hM⟩, ⟨N, hN⟩⟩
      exact ⟨(M, N), Finset.mem_univ _, hM, hN⟩
    _ ≤ ∑ MN ∈ (Finset.univ : Finset (Matrix r × Matrix r)),
          RandomGraph.probability n (fun G ↦
            HostFamily.SlotMatrixEvent c MN.1 G ∧
              HostFamily.SlotMatrixEvent d MN.2 G) :=
      RandomGraph.probability_exists_le_sum _ _
    _ ≤ ∑ _MN ∈ (Finset.univ : Finset (Matrix r × Matrix r)), p := by
      apply sum_le_sum
      intro MN hMN
      exact probability_slotMatrixEvent_and_le c d MN.1 MN.2
    _ = (2 ^ (90 * r * r) : ℕ) ^ 2 * p := by
      simp only [sum_const, Finset.card_univ, Fintype.card_prod, hmatrix,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
      ring

/-- Large-overlap pair bound.  After the first matrix is fixed, only the
`10*r*j` free extension bits remain for the second matrix. -/
theorem probability_fixedChoiceEvent_and_le_large {n r j : ℕ}
    (c d : HostFamily.Choice n r)
    (hdiff : (differingSlots c d).card = j) :
    RandomGraph.probability n (fun G ↦
        HostFamily.FixedChoiceEvent c G ∧ HostFamily.FixedChoiceEvent d G) ≤
      (2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) *
        (1 / 2 : ℝ) ^
          (2 * (HostFamily.templateOrder r).choose 2 -
            (HostFamily.agreementSlots c d).card.choose 2) := by
  classical
  have hmatrix : Fintype.card (Matrix r) = 2 ^ (90 * r * r) :=
    StructuredFamily.card_matrix r
  let p := (1 / 2 : ℝ) ^
    (2 * (HostFamily.templateOrder r).choose 2 -
      (HostFamily.agreementSlots c d).card.choose 2)
  calc
    RandomGraph.probability n (fun G ↦
        HostFamily.FixedChoiceEvent c G ∧ HostFamily.FixedChoiceEvent d G) ≤
        RandomGraph.probability n (fun G ↦
          ∃ M ∈ (Finset.univ : Finset (Matrix r)),
            ∃ N ∈ compatibleMatrices c M d,
              HostFamily.SlotMatrixEvent c M G ∧
                HostFamily.SlotMatrixEvent d N G) := by
      apply RandomGraph.probability_mono
      rintro G ⟨⟨M, hM⟩, ⟨N, hN⟩⟩
      refine ⟨M, Finset.mem_univ _, N, ?_, hM, hN⟩
      simp only [compatibleMatrices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact slotMatrixEvents_imp_matrixCompatible hM hN
    _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix r)),
          RandomGraph.probability n (fun G ↦
            ∃ N ∈ compatibleMatrices c M d,
              HostFamily.SlotMatrixEvent c M G ∧
                HostFamily.SlotMatrixEvent d N G) :=
      RandomGraph.probability_exists_le_sum _ _
    _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix r)),
          ∑ N ∈ compatibleMatrices c M d,
            RandomGraph.probability n (fun G ↦
              HostFamily.SlotMatrixEvent c M G ∧
                HostFamily.SlotMatrixEvent d N G) := by
      apply sum_le_sum
      intro M hM
      exact RandomGraph.probability_exists_le_sum _ _
    _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix r)),
          (#(compatibleMatrices c M d) : ℝ) * p := by
      apply sum_le_sum
      intro M hM
      calc
        (∑ N ∈ compatibleMatrices c M d,
            RandomGraph.probability n (fun G ↦
              HostFamily.SlotMatrixEvent c M G ∧
                HostFamily.SlotMatrixEvent d N G)) ≤
            ∑ _N ∈ compatibleMatrices c M d, p := by
          apply sum_le_sum
          intro N hN
          exact probability_slotMatrixEvent_and_le c d M N
        _ = (#(compatibleMatrices c M d) : ℝ) * p := by simp
    _ ≤ ∑ _M ∈ (Finset.univ : Finset (Matrix r)),
          (2 ^ (10 * r * j) : ℕ) * p := by
      apply sum_le_sum
      intro M hM
      gcongr
      exact_mod_cast card_matrixExtensions_le c d hdiff M
    _ = (2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) * p := by
      simp only [sum_const, Finset.card_univ, hmatrix, nsmul_eq_mul, Nat.cast_pow]
      ring

/-! ## Concrete bounds for exact overlap strata -/

/-- In the stable bucket model the generic equality-set definition is
literally the set of agreeing host slots. -/
theorem equalSlotSet_eq_agreementSlots {n r : ℕ}
    (c d : HostFamily.Choice n r) :
    equalSlotSet c d = HostFamily.agreementSlots c d := rfl

/-- Agreeing and differing slots partition the full set of host slots. -/
theorem card_differingSlots_add_card_agreementSlots {n r : ℕ}
    (c d : HostFamily.Choice n r) :
    (differingSlots c d).card + (HostFamily.agreementSlots c d).card =
      HostFamily.templateOrder r := by
  simpa [differingSlots, HostFamily.agreementSlots, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (HostFamily.templateOrder r))))
      (p := fun s ↦ c s = d s))

/-- The crude two-family estimate, multiplied by the exact number of
ordered stable-choice pairs in overlap stratum `i`. -/
theorem hostIntersectionContribution_le_crude (n r i : ℕ) :
    hostIntersectionContribution n r i ≤
      (HostFamily.bucketSize n r ^ HostFamily.templateOrder r *
          (Nat.choose (HostFamily.templateOrder r) i *
            (HostFamily.bucketSize n r - 1) ^
              (HostFamily.templateOrder r - i)) : ℕ) *
        ((2 ^ (90 * r * r) : ℕ) ^ 2 *
          (1 / 2 : ℝ) ^
            (2 * (HostFamily.templateOrder r).choose 2 - i.choose 2)) := by
  apply choiceIntersectionContribution_le
  intro cd hcd
  rw [finiteUniform_probability_eq_randomGraph_probability]
  have hi : (HostFamily.agreementSlots cd.1 cd.2).card = i := by
    simpa [slotOverlap, equalSlotSet_eq_agreementSlots] using
      (mem_choicePairs.mp hcd)
  simpa [hi] using probability_fixedChoiceEvent_and_le cd.1 cd.2

/-- The canonical free-extension estimate, multiplied by the exact number
of ordered pairs differing in exactly `j` slots. -/
theorem hostIntersectionContribution_le_large (n r j : ℕ)
    (hj : j ≤ HostFamily.templateOrder r) :
    hostIntersectionContribution n r (HostFamily.templateOrder r - j) ≤
      (HostFamily.bucketSize n r ^ HostFamily.templateOrder r *
          (Nat.choose (HostFamily.templateOrder r)
              (HostFamily.templateOrder r - j) *
            (HostFamily.bucketSize n r - 1) ^ j) : ℕ) *
        ((2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) *
          (1 / 2 : ℝ) ^
            (2 * (HostFamily.templateOrder r).choose 2 -
              (HostFamily.templateOrder r - j).choose 2)) := by
  unfold hostIntersectionContribution
  have hpoint : ∀ cd ∈ choicePairs (HostFamily.templateOrder r)
      (HostFamily.bucketSize n r) (HostFamily.templateOrder r - j),
      FiniteUniform.probability (fun G ↦
        HostFamily.FixedChoiceEvent cd.1 G ∧ HostFamily.FixedChoiceEvent cd.2 G) ≤
        (2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) *
          (1 / 2 : ℝ) ^
            (2 * (HostFamily.templateOrder r).choose 2 -
              (HostFamily.templateOrder r - j).choose 2) := by
    intro cd hcd
    rw [finiteUniform_probability_eq_randomGraph_probability]
    have hagree : (HostFamily.agreementSlots cd.1 cd.2).card =
        HostFamily.templateOrder r - j := by
      simpa [slotOverlap, equalSlotSet_eq_agreementSlots] using
        (mem_choicePairs.mp hcd)
    have hdiff : (differingSlots cd.1 cd.2).card = j := by
      have hpartition := card_differingSlots_add_card_agreementSlots cd.1 cd.2
      omega
    simpa [hagree] using
      probability_fixedChoiceEvent_and_le_large cd.1 cd.2 hdiff
  simpa [show HostFamily.templateOrder r -
      (HostFamily.templateOrder r - j) = j by omega] using
    (choiceIntersectionContribution_le
      (HostFamily.templateOrder r) (HostFamily.bucketSize n r)
      (HostFamily.templateOrder r - j) HostFamily.FixedChoiceEvent
      ((2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) *
        (1 / 2 : ℝ) ^
          (2 * (HostFamily.templateOrder r).choose 2 -
            (HostFamily.templateOrder r - j).choose 2)) hpoint)

end HostMoments
end Erdos807
