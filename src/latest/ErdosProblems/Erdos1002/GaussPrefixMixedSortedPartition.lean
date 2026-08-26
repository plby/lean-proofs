import ErdosProblems.Erdos1002.GaussHeterogeneousMovingScaleLimit
import ErdosProblems.Erdos1002.GaussPrefixMixedChronology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical chronological partition of labeled mixed depth tuples

Mixed factorial expansions are indexed label by label.  Analytic mixing,
however, is applied after all selected depths have been put in one strict
chronological order.  This module supplies a canonical sorting operation
and a disjoint finite partition by the resulting occurrence order.

The construction is entirely deterministic.  Cross-label collisions are
removed by passing to the subtype of globally injective mixed tuples; the
existing disjoint-cell lemma shows that the omitted terms are identically
zero in the marked expansion.
-/

open Filter Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixMixedSortedPartitionPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-- The finite subtype of labeled mixed tuples with no collision between
any two labeled occurrences. -/
def GloballyInjectiveMixedDepthTuple
    (N : ℕ) (k : ι → ℕ) :=
  {F : GaussPrefixMixedDepthTuple N k //
    IsGloballyInjectiveMixedDepthTuple N k F}

noncomputable instance globallyInjectiveMixedDepthTupleFintype
    (N : ℕ) (k : ι → ℕ) :
    Fintype (GloballyInjectiveMixedDepthTuple N k) := by
  unfold GloballyInjectiveMixedDepthTuple
  infer_instance

/-- Number of occurrences in the flattened mixed factorial order. -/
abbrev MixedOccurrenceCount (k : ι → ℕ) :=
  Fintype.card (GaussPrefixMixedOccurrence k)

/-- Canonical increasing enumeration of all occurrences in one globally
injective mixed tuple.  It is obtained by ordering the finite range of the
depth map, so no arbitrary choice among admissible orders remains. -/
noncomputable def canonicalMixedOccurrenceOrder
    (N : ℕ) (k : ι → ℕ)
    (F : GloballyInjectiveMixedDepthTuple N k) :
    Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k := by
  let depth : GaussPrefixMixedOccurrence k → ℕ :=
    fun z ↦ (F.1 z.1 z.2 : ℕ)
  let rangeEquiv : GaussPrefixMixedOccurrence k ≃ Set.range depth :=
    Equiv.ofInjective depth F.2
  let hcard : Fintype.card (Set.range depth) =
      MixedOccurrenceCount k :=
    (Fintype.card_congr rangeEquiv).symm
  exact
    (Fintype.orderIsoFinOfCardEq (Set.range depth) hcard).toEquiv.trans
      rangeEquiv.symm

/-- The canonical enumeration is strictly increasing in actual depth. -/
theorem strictMono_canonicalMixedOccurrenceOrder
    (N : ℕ) (k : ι → ℕ)
    (F : GloballyInjectiveMixedDepthTuple N k) :
    StrictMono (fun j ↦
      (F.1 (canonicalMixedOccurrenceOrder N k F j).1
        (canonicalMixedOccurrenceOrder N k F j).2 : ℕ)) := by
  let depth : GaussPrefixMixedOccurrence k → ℕ :=
    fun z ↦ (F.1 z.1 z.2 : ℕ)
  let rangeEquiv : GaussPrefixMixedOccurrence k ≃ Set.range depth :=
    Equiv.ofInjective depth F.2
  let hcard : Fintype.card (Set.range depth) =
      MixedOccurrenceCount k :=
    (Fintype.card_congr rangeEquiv).symm
  let eRange :=
    Fintype.orderIsoFinOfCardEq (Set.range depth) hcard
  have heRange : StrictMono eRange := eRange.strictMono
  intro a b hab
  have hrange : eRange a < eRange b := heRange hab
  have ha :
      depth (rangeEquiv.symm (eRange a)) = (eRange a : ℕ) :=
    congrArg Subtype.val (rangeEquiv.apply_symm_apply (eRange a))
  have hb :
      depth (rangeEquiv.symm (eRange b)) = (eRange b : ℕ) :=
    congrArg Subtype.val (rangeEquiv.apply_symm_apply (eRange b))
  change depth (rangeEquiv.symm (eRange a)) <
    depth (rangeEquiv.symm (eRange b))
  rw [ha, hb]
  exact hrange

/-- Flatten one labeled tuple according to a fixed occurrence order. -/
def fixedOrderMixedTimes
    (N : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k) :
    Fin (MixedOccurrenceCount k) → ℕ :=
  fun j ↦ (F.1 (e j).1 (e j).2 : ℕ)

/-- A fixed occurrence order remembers every component of the original
labeled tuple, hence flattening is injective. -/
theorem fixedOrderMixedTimes_injective
    (N : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Function.Injective (fixedOrderMixedTimes N k e) := by
  intro F G hFG
  apply Subtype.ext
  funext i
  apply Function.Embedding.ext
  intro j
  apply Subtype.ext
  let z : GaussPrefixMixedOccurrence k := ⟨i, j⟩
  let a : Fin (MixedOccurrenceCount k) := e.symm z
  have ha := congrFun hFG a
  change
    (F.1 (e a).1 (e a).2 : ℕ) =
      (G.1 (e a).1 (e a).2 : ℕ) at ha
  have hea : e a = z := by
    dsimp only [a]
    exact e.apply_symm_apply z
  rw [hea] at ha
  exact ha

/-- Class of globally injective tuples having one prescribed canonical
occurrence order.  These classes form a literal disjoint partition. -/
def canonicalMixedOrderClass
    (N : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (GloballyInjectiveMixedDepthTuple N k) := by
  classical
  exact Finset.univ.filter fun F ↦
    canonicalMixedOccurrenceOrder N k F = e

@[simp] theorem mem_canonicalMixedOrderClass_iff
    {N : ℕ} {k : ι → ℕ}
    {e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k}
    {F : GloballyInjectiveMixedDepthTuple N k} :
    F ∈ canonicalMixedOrderClass N k e ↔
      canonicalMixedOccurrenceOrder N k F = e := by
  classical
  simp [canonicalMixedOrderClass]

/-- The natural-valued chronological tuple family obtained from one order
class, with optional coordinatewise finite boxes and prescribed parity. -/
def canonicalMixedOrderParityBoxTimes
    (N : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) := by
  classical
  exact
    ((canonicalMixedOrderClass N k e).filter fun F ↦
      ∀ j, fixedOrderMixedTimes N k e F j ∈ boxes (e j) ∧
        fixedOrderMixedTimes N k e F j % 2 = (parity (e j)).1).image
      (fixedOrderMixedTimes N k e)

theorem mem_canonicalMixedOrderParityBoxTimes_iff
    {N : ℕ} {k : ι → ℕ}
    {e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k}
    {boxes : GaussPrefixMixedOccurrence k → Finset ℕ}
    {parity : GaussPrefixMixedOccurrence k → Fin 2}
    {t : Fin (MixedOccurrenceCount k) → ℕ} :
    t ∈ canonicalMixedOrderParityBoxTimes N k e boxes parity ↔
      ∃ F : GloballyInjectiveMixedDepthTuple N k,
        canonicalMixedOccurrenceOrder N k F = e ∧
          (∀ j, fixedOrderMixedTimes N k e F j ∈ boxes (e j) ∧
            fixedOrderMixedTimes N k e F j % 2 =
              (parity (e j)).1) ∧
          fixedOrderMixedTimes N k e F = t := by
  classical
  unfold canonicalMixedOrderParityBoxTimes
  simp only [Finset.mem_image, Finset.mem_filter,
    mem_canonicalMixedOrderClass_iff]
  constructor
  · rintro ⟨F, ⟨horder, hbox⟩, rfl⟩
    exact ⟨F, horder, hbox, rfl⟩
  · rintro ⟨F, horder, hbox, rfl⟩
    exact ⟨F, ⟨horder, hbox⟩, rfl⟩

/-- Every tuple in one canonical order class is strictly chronological. -/
theorem canonicalMixedOrderParityBoxTimes_chronological
    {N : ℕ} {k : ι → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalMixedOrderParityBoxTimes N k e boxes parity) :
    IsChronologicalNatTuple t := by
  obtain ⟨F, horder, _hbox, hFt⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp ht
  subst t
  have hstrict := strictMono_canonicalMixedOccurrenceOrder N k F
  rw [horder] at hstrict
  intro i j hij
  have hlt :
      fixedOrderMixedTimes N k e F i <
        fixedOrderMixedTimes N k e F j := by
    simpa only [fixedOrderMixedTimes] using! hstrict hij
  omega

/-- The parity attached to each chronological coordinate is exactly the
parity of the corresponding labeled occurrence. -/
theorem canonicalMixedOrderParityBoxTimes_parity
    {N : ℕ} {k : ι → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalMixedOrderParityBoxTimes N k e boxes parity)
    (j : Fin (MixedOccurrenceCount k)) :
    t j % 2 = (parity (e j)).1 := by
  obtain ⟨F, _horder, hbox, hFt⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp ht
  rw [← hFt]
  exact (hbox j).2

/-- The finite image has exactly the cardinality of its labeled order
class with the box/parity restriction; no multiplicity is lost. -/
theorem card_canonicalMixedOrderParityBoxTimes
    (N : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    (canonicalMixedOrderParityBoxTimes N k e boxes parity).card =
      ((canonicalMixedOrderClass N k e).filter fun F ↦
        ∀ j, fixedOrderMixedTimes N k e F j ∈ boxes (e j) ∧
          fixedOrderMixedTimes N k e F j % 2 =
            (parity (e j)).1).card := by
  classical
  unfold canonicalMixedOrderParityBoxTimes
  rw [Finset.card_image_iff.mpr
    (fun F _hF G _hG hFG ↦
      fixedOrderMixedTimes_injective N k e hFG)]

end

end Erdos1002
