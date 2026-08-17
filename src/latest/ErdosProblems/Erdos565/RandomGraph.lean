import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Tactic

/-!
# A finite uniform random-graph model

For the use of the probabilistic method in the proof of Erdős problem 565 it is
convenient to avoid measure-theoretic bookkeeping.  A sample is simply a
subset of a finite set of independent Boolean coordinates.  Graph coordinates
are the non-diagonal unordered pairs of vertices.

Besides connecting this model to `SimpleGraph`, this file proves exact fibre
counts for restriction and product formulas for events supported on disjoint
coordinate blocks.  The latter are the finite counting form of independence.
-/

open scoped BigOperators

namespace Erdos565
namespace RandomGraph

/-! ## Boolean coordinate spaces -/

section Coordinates

variable {α : Type*} [DecidableEq α]

/-- All Boolean samples on the finite coordinate set `U`. -/
def samples (U : Finset α) : Finset (Finset α) := U.powerset

/-- Restriction of a Boolean sample to a coordinate block. -/
def restrict (D S : Finset α) : Finset α := S ∩ D

/-- The number of samples on `U` satisfying a predicate. -/
def count (U : Finset α) (P : Finset α → Prop) [DecidablePred P] : ℕ :=
  (samples U).filter P |>.card

/-- The samples satisfying a proposition, with classical decidability hidden
inside the construction.  This is useful for finite conjunctions of an
indexed family of events. -/
noncomputable def eventSamples (U : Finset α) (P : Finset α → Prop) :
    Finset (Finset α) := by
  classical
  exact U.powerset.filter P

@[simp] theorem card_samples (U : Finset α) : (samples U).card = 2 ^ U.card := by
  simp [samples]

@[simp] theorem restrict_subset_right (D S : Finset α) : restrict D S ⊆ D := by
  simp [restrict]

@[simp] theorem restrict_subset_left (D S : Finset α) : restrict D S ⊆ S := by
  simp [restrict]

theorem restrict_eq_self {D S : Finset α} (hS : S ⊆ D) : restrict D S = S := by
  exact Finset.inter_eq_left.mpr hS

theorem restrict_restrict_of_subset {D E S : Finset α} (hDE : D ⊆ E) :
    restrict D (restrict E S) = restrict D S := by
  ext x
  simp only [restrict, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hxS, _hxE⟩, hxD⟩
    exact ⟨hxS, hxD⟩
  · rintro ⟨hxS, hxD⟩
    exact ⟨⟨hxS, hDE hxD⟩, hxD⟩

/-- A sample has the prescribed restriction `A` precisely when it is `A`
together with an arbitrary sample on the coordinates outside `D`. -/
theorem filter_restrict_eq (U D A : Finset α) (hD : D ⊆ U) (hA : A ⊆ D) :
    U.powerset.filter (fun S ↦ restrict D S = A) =
      (U \ D).powerset.image (fun B ↦ A ∪ B) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hSU, hSD⟩
    refine ⟨S \ D, ?_, ?_⟩
    · exact Finset.sdiff_subset_sdiff hSU (fun _ h ↦ h)
    · rw [← hSD]
      simp only [restrict]
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
  · rintro ⟨B, hB, rfl⟩
    have hAU : A ⊆ U := hA.trans hD
    have hBU : B ⊆ U := hB.trans (Finset.sdiff_subset)
    refine ⟨Finset.union_subset hAU hBU, ?_⟩
    simp only [restrict]
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hA]
    have hBD : Disjoint B D := Finset.disjoint_left.2 fun b hbB hbD ↦
      (Finset.mem_sdiff.1 (hB hbB)).2 hbD
    rw [Finset.disjoint_iff_inter_eq_empty.mp hBD]
    simp

/-- Exact restriction-fibre count.  Thus restriction of the uniform sample on
`U` is uniform on every coordinate block `D ⊆ U`. -/
theorem card_restrict_fiber (U D A : Finset α) (hD : D ⊆ U) (hA : A ⊆ D) :
    (U.powerset.filter (fun S ↦ restrict D S = A)).card = 2 ^ (U.card - D.card) := by
  rw [filter_restrict_eq U D A hD hA, Finset.card_image_iff.mpr]
  · rw [Finset.card_powerset, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hD]
  · intro B hB C hC hEq
    have hBA : Disjoint B A := by
      refine Finset.disjoint_left.2 fun x hxB hxA ↦ ?_
      exact (Finset.mem_sdiff.1 ((Finset.mem_powerset.1 hB) hxB)).2 (hA hxA)
    have hCA : Disjoint C A := by
      refine Finset.disjoint_left.2 fun x hxC hxA ↦ ?_
      exact (Finset.mem_sdiff.1 ((Finset.mem_powerset.1 hC) hxC)).2 (hA hxA)
    ext x
    have hxBnotA : x ∈ B → x ∉ A := fun hxB hxA ↦
      Finset.disjoint_left.1 hBA hxB hxA
    have hxCnotA : x ∈ C → x ∉ A := fun hxC hxA ↦
      Finset.disjoint_left.1 hCA hxC hxA
    have hx := congrArg (fun T : Finset α ↦ x ∈ T) hEq
    simp only [Finset.mem_union] at hx
    by_cases hxA : x ∈ A
    · constructor <;> intro hxmem
      · exact (hxBnotA hxmem hxA).elim
      · exact (hxCnotA hxmem hxA).elim
    · simpa [hxA] using hx

/-- The preimage of any event under restriction has the expected exact
cardinality. -/
theorem card_restrict_event (U D : Finset α) (hD : D ⊆ U)
    (P : Finset α → Prop) [DecidablePred P] :
    (U.powerset.filter fun S ↦ P (restrict D S)).card =
      2 ^ (U.card - D.card) * (D.powerset.filter P).card := by
  classical
  let F := U.powerset.filter fun S ↦ P (restrict D S)
  calc
    F.card = ∑ A ∈ D.powerset.filter P,
        (U.powerset.filter fun S ↦ restrict D S = A).card := by
      have hsum := Finset.sum_fiberwise_of_maps_to
        (s := F) (t := D.powerset.filter P) (g := restrict D)
        (fun S hS ↦ by
          exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (restrict_subset_right D S),
            (Finset.mem_filter.1 hS).2⟩)
        (fun _ ↦ (1 : ℕ))
      have hsum' : F.card = ∑ A ∈ D.powerset.filter P,
          (F.filter fun S ↦ restrict D S = A).card := by
        simpa using hsum.symm
      rw [hsum']
      apply Finset.sum_congr rfl
      intro A hA
      congr 1
      ext S
      simp only [F, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨hSU, _hP⟩, hres⟩
        exact ⟨hSU, hres⟩
      · rintro ⟨hSU, hres⟩
        exact ⟨⟨hSU, by simpa [hres] using (Finset.mem_filter.1 hA).2⟩, hres⟩
    _ = ∑ _A ∈ D.powerset.filter P, 2 ^ (U.card - D.card) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact card_restrict_fiber U D A hD
        (Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1)
    _ = 2 ^ (U.card - D.card) * (D.powerset.filter P).card := by
      simp [mul_comm]

/-- Splitting a sample between two disjoint blocks is a bijection.  This is
the exact finite counting form of independence for two events. -/
theorem card_disjoint_events (D E : Finset α) (hDE : Disjoint D E)
    (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    ((D ∪ E).powerset.filter fun S ↦
        P (restrict D S) ∧ Q (restrict E S)).card =
      (D.powerset.filter P).card * (E.powerset.filter Q).card := by
  classical
  let source := (D ∪ E).powerset.filter fun S ↦
    P (restrict D S) ∧ Q (restrict E S)
  let target := (D.powerset.filter P).product (E.powerset.filter Q)
  have hcard : source.card = target.card := by
    apply Finset.card_bij
      (fun S _ ↦ (restrict D S, restrict E S))
    · intro S hS
      rcases Finset.mem_filter.1 hS with ⟨_hsub, hP, hQ⟩
      exact Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (restrict_subset_right D S), hP⟩,
          Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (restrict_subset_right E S), hQ⟩⟩
    · intro S hS T hT hEq
      have hSD : restrict D S = restrict D T := congrArg Prod.fst hEq
      have hSE : restrict E S = restrict E T := congrArg Prod.snd hEq
      apply Finset.ext
      intro x
      have hSsub := Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1
      have hTsub := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
      have hxS : x ∈ S ↔ x ∈ restrict D S ∨ x ∈ restrict E S := by
        simp only [restrict, Finset.mem_inter]
        constructor
        · intro hx
          rcases Finset.mem_union.1 (hSsub hx) with hxD | hxE
          · exact Or.inl ⟨hx, hxD⟩
          · exact Or.inr ⟨hx, hxE⟩
        · rintro (hx | hx) <;> exact hx.1
      have hxT : x ∈ T ↔ x ∈ restrict D T ∨ x ∈ restrict E T := by
        simp only [restrict, Finset.mem_inter]
        constructor
        · intro hx
          rcases Finset.mem_union.1 (hTsub hx) with hxD | hxE
          · exact Or.inl ⟨hx, hxD⟩
          · exact Or.inr ⟨hx, hxE⟩
        · rintro (hx | hx) <;> exact hx.1
      rw [hxS, hxT, hSD, hSE]
    · rintro ⟨A, B⟩ hAB
      rcases Finset.mem_product.1 hAB with ⟨hA, hB⟩
      have hAD := Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1
      have hBE := Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1
      refine ⟨A ∪ B, ?_, ?_⟩
      · apply Finset.mem_filter.2
        refine ⟨Finset.mem_powerset.2 (Finset.union_subset
          (hAD.trans Finset.subset_union_left) (hBE.trans Finset.subset_union_right)), ?_, ?_⟩
        · have hBD : Disjoint B D :=
            Disjoint.mono hBE (fun _ h ↦ h) hDE.symm
          have hres : restrict D (A ∪ B) = A := by
            ext x
            simp only [restrict, Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxA | hxB, hxD⟩
              · exact hxA
              · exact (Finset.disjoint_left.1 hBD hxB hxD).elim
            · intro hxA
              exact ⟨Or.inl hxA, hAD hxA⟩
          simpa [hres] using (Finset.mem_filter.1 hA).2
        · have hAE : Disjoint A E := Disjoint.mono hAD (fun _ h ↦ h) hDE
          have hres : restrict E (A ∪ B) = B := by
            ext x
            simp only [restrict, Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxA | hxB, hxE⟩
              · exact (Finset.disjoint_left.1 hAE hxA hxE).elim
              · exact hxB
            · intro hxB
              exact ⟨Or.inr hxB, hBE hxB⟩
          simpa [hres] using (Finset.mem_filter.1 hB).2
      · apply Prod.ext
        · have hBD : Disjoint B D :=
            Disjoint.mono hBE (fun _ h ↦ h) hDE.symm
          ext x
          simp only [restrict, Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxA | hxB, hxD⟩
            · exact hxA
            · exact (Finset.disjoint_left.1 hBD hxB hxD).elim
          · intro hxA
            exact ⟨Or.inl hxA, hAD hxA⟩
        · have hAE : Disjoint A E := Disjoint.mono hAD (fun _ h ↦ h) hDE
          ext x
          simp only [restrict, Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxA | hxB, hxE⟩
            · exact (Finset.disjoint_left.1 hAE hxA hxE).elim
            · exact hxB
          · intro hxB
            exact ⟨Or.inr hxB, hBE hxB⟩
  simpa [source, target, Finset.card_product] using hcard

/-- Events supported on two disjoint blocks remain independent inside a
larger uniform coordinate space; the leading power of two counts the unused
coordinates. -/
theorem card_two_block_event (U D E : Finset α) (hDE : Disjoint D E)
    (hU : D ∪ E ⊆ U) (P Q : Finset α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (U.powerset.filter fun S ↦ P (restrict D S) ∧ Q (restrict E S)).card =
      2 ^ (U.card - (D ∪ E).card) *
        (D.powerset.filter P).card * (E.powerset.filter Q).card := by
  let R : Finset α → Prop := fun T ↦ P (restrict D T) ∧ Q (restrict E T)
  calc
    (U.powerset.filter fun S ↦ P (restrict D S) ∧ Q (restrict E S)).card =
        (U.powerset.filter fun S ↦ R (restrict (D ∪ E) S)).card := by
      have hDres (S : Finset α) :
          restrict D (restrict (D ∪ E) S) = restrict D S := by
        ext x
        simp only [restrict, Finset.mem_inter, Finset.mem_union]
        tauto
      have hEres (S : Finset α) :
          restrict E (restrict (D ∪ E) S) = restrict E S := by
        ext x
        simp only [restrict, Finset.mem_inter, Finset.mem_union]
        tauto
      simp [R, hDres, hEres]
    _ = 2 ^ (U.card - (D ∪ E).card) *
        (((D ∪ E).powerset.filter fun S ↦
          P (restrict D S) ∧ Q (restrict E S)).card) :=
      card_restrict_event U (D ∪ E) hU R
    _ = 2 ^ (U.card - (D ∪ E).card) *
        (D.powerset.filter P).card * (E.powerset.filter Q).card := by
      rw [card_disjoint_events D E hDE P Q]
      simp [Nat.mul_assoc]

/-! ### Arbitrarily many disjoint blocks -/

/-- Union of a finite indexed family of coordinate blocks. -/
def blockUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (D : ι → Finset α) :
    Finset α := I.biUnion D

/-- The conjunction of the events supported on an indexed family of blocks. -/
def supportedEvents {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (D : ι → Finset α) (P : ι → Finset α → Prop) (S : Finset α) : Prop :=
  ∀ i ∈ I, P i (restrict (D i) S)

theorem subset_blockUnion {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {D : ι → Finset α} {i : ι} (hi : i ∈ I) :
    D i ⊆ blockUnion I D := by
  intro x hx
  exact Finset.mem_biUnion.2 ⟨i, hi, hx⟩

@[simp] theorem blockUnion_empty {ι : Type*} [DecidableEq ι] (D : ι → Finset α) :
    blockUnion ∅ D = ∅ := by
  simp [blockUnion]

@[simp] theorem blockUnion_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (I : Finset ι) (D : ι → Finset α) :
    blockUnion (insert a I) D = D a ∪ blockUnion I D := by
  simp [blockUnion]

@[simp] theorem supportedEvents_empty {ι : Type*} [DecidableEq ι]
    (D : ι → Finset α) (P : ι → Finset α → Prop) (S : Finset α) :
    supportedEvents ∅ D P S := by
  simp [supportedEvents]

@[simp] theorem supportedEvents_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (I : Finset ι) (D : ι → Finset α)
    (P : ι → Finset α → Prop) (S : Finset α) :
    supportedEvents (insert a I) D P S ↔
      P a (restrict (D a) S) ∧ supportedEvents I D P S := by
  simp [supportedEvents]

/-- Exact product formula for finitely many events supported on pairwise
disjoint coordinate blocks. -/
theorem card_pairwise_disjoint_events {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (D : ι → Finset α) (P : ι → Finset α → Prop)
    [∀ i, DecidablePred (P i)]
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j)) :
    (eventSamples (blockUnion I D) (supportedEvents I D P)).card =
      ∏ i ∈ I, (eventSamples (D i) (P i)).card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have htrue : supportedEvents (∅ : Finset ι) D P = fun _ ↦ True := by
        funext S
        simp [supportedEvents]
      rw [htrue]
      simp [eventSamples, blockUnion]
  | @insert a I ha ih =>
      have hdisI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j) := by
        intro i hi j hj hij
        exact hdis i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hdisUnion : Disjoint (D a) (blockUnion I D) := by
        rw [Finset.disjoint_left]
        intro x hxa hxU
        rcases Finset.mem_biUnion.1 hxU with ⟨j, hj, hxj⟩
        exact Finset.disjoint_left.1
          (hdis a (Finset.mem_insert_self a I) j (Finset.mem_insert_of_mem hj)
            (fun haj ↦ ha (haj ▸ hj))) hxa hxj
      let Q : Finset α → Prop := supportedEvents I D P
      have hraw := card_disjoint_events (D a) (blockUnion I D)
        hdisUnion (P a) Q
      have hbinary :
          (eventSamples (D a ∪ blockUnion I D) fun S ↦
            P a (restrict (D a) S) ∧ Q (restrict (blockUnion I D) S)).card =
            (eventSamples (D a) (P a)).card *
              (eventSamples (blockUnion I D) Q).card := by
        calc
          (eventSamples (D a ∪ blockUnion I D) fun S ↦
              P a (restrict (D a) S) ∧ Q (restrict (blockUnion I D) S)).card =
              (((D a ∪ blockUnion I D).powerset.filter fun S ↦
                P a (restrict (D a) S) ∧ Q (restrict (blockUnion I D) S))).card := by
            congr 1
            ext S
            simp [eventSamples]
          _ = ((D a).powerset.filter (P a)).card *
              ((blockUnion I D).powerset.filter Q).card := hraw
          _ = (eventSamples (D a) (P a)).card *
              (eventSamples (blockUnion I D) Q).card := by
            congr 1 <;> congr 1 <;> ext S <;> simp [eventSamples]
      have hfilter :
          (eventSamples (blockUnion (insert a I) D)
              (supportedEvents (insert a I) D P)).card =
            (eventSamples (D a ∪ blockUnion I D) (fun S ↦
              P a (restrict (D a) S) ∧
                Q (restrict (blockUnion I D) S))).card := by
        rw [blockUnion_insert]
        congr 1
        ext S
        simp only [eventSamples, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨hSsub, hAll⟩
          rcases (supportedEvents_insert a I D P S).1 hAll with ⟨hPa, hPI⟩
          refine ⟨hSsub, hPa, ?_⟩
          intro j hj
          simpa [Q, supportedEvents,
            restrict_restrict_of_subset (subset_blockUnion hj)] using hPI j hj
        · rintro ⟨hSsub, hPa, hPI⟩
          refine ⟨hSsub, (supportedEvents_insert a I D P S).2 ⟨hPa, ?_⟩⟩
          intro j hj
          simpa [Q, supportedEvents,
            restrict_restrict_of_subset (subset_blockUnion hj)] using hPI j hj
      rw [hfilter, hbinary, ih hdisI]
      simp [Finset.prod_insert, ha, Q, eventSamples]

/-- The corresponding formula inside a larger uniform coordinate space. -/
theorem card_family_event (U : Finset α) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (D : ι → Finset α) (P : ι → Finset α → Prop)
    [∀ i, DecidablePred (P i)]
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j))
    (hU : blockUnion I D ⊆ U) :
    (eventSamples U (supportedEvents I D P)).card =
      2 ^ (U.card - (blockUnion I D).card) *
        ∏ i ∈ I, (eventSamples (D i) (P i)).card := by
  classical
  let Q : Finset α → Prop := supportedEvents I D P
  calc
    (eventSamples U (supportedEvents I D P)).card =
        (eventSamples U fun S ↦ Q (restrict (blockUnion I D) S)).card := by
      congr 1
      simp only [eventSamples]
      apply Finset.filter_congr
      intro S _hS
      constructor
      · intro h i hi
        simpa [Q, supportedEvents,
          restrict_restrict_of_subset (subset_blockUnion hi)] using h i hi
      · intro h i hi
        simpa [Q, supportedEvents,
          restrict_restrict_of_subset (subset_blockUnion hi)] using h i hi
    _ = 2 ^ (U.card - (blockUnion I D).card) *
        (eventSamples (blockUnion I D) Q).card := by
      simpa [eventSamples] using card_restrict_event U (blockUnion I D) hU Q
    _ = 2 ^ (U.card - (blockUnion I D).card) *
        ∏ i ∈ I, (eventSamples (D i) (P i)).card := by
      rw [card_pairwise_disjoint_events I D P hdis]

/-- Exact conditional-independence count after a separate coordinate block
has been fixed.  The local fixed-block event has cardinality one, so it drops
out of the product. -/
theorem card_fixed_and_family_event (U F T : Finset α)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (D : ι → Finset α)
    (P : ι → Finset α → Prop) [∀ i, DecidablePred (P i)]
    (hT : T ⊆ F)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j))
    (hFdis : Disjoint F (blockUnion I D))
    (hU : F ∪ blockUnion I D ⊆ U) :
    (eventSamples U fun S ↦
      restrict F S = T ∧ supportedEvents I D P S).card =
      2 ^ (U.card - (F ∪ blockUnion I D).card) *
        ∏ i ∈ I, (eventSamples (D i) (P i)).card := by
  classical
  let Q : Finset α → Prop := supportedEvents I D P
  have hraw := card_two_block_event U F (blockUnion I D) hFdis hU
    (fun R ↦ R = T) Q
  have hleft :
      (eventSamples U fun S ↦ restrict F S = T ∧ supportedEvents I D P S).card =
        (U.powerset.filter fun S ↦
          restrict F S = T ∧ Q (restrict (blockUnion I D) S)).card := by
    congr 1
    ext S
    simp only [eventSamples, Finset.mem_filter, Finset.mem_powerset]
    refine and_congr_right fun _hSU ↦ and_congr_right fun _hfix ↦ ?_
    constructor
    · intro h i hi
      simpa [Q, supportedEvents,
        restrict_restrict_of_subset (subset_blockUnion hi)] using h i hi
    · intro h i hi
      simpa [Q, supportedEvents,
        restrict_restrict_of_subset (subset_blockUnion hi)] using h i hi
  have hfixed : (F.powerset.filter fun R ↦ R = T).card = 1 := by
    have heq : F.powerset.filter (fun R ↦ R = T) = {T} := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · exact fun h ↦ h.2
      · intro hRT
        subst R
        exact ⟨hT, rfl⟩
    rw [heq]
    simp
  have hfamily : ((blockUnion I D).powerset.filter Q).card =
      ∏ i ∈ I, (eventSamples (D i) (P i)).card := by
    calc
      ((blockUnion I D).powerset.filter Q).card =
          (eventSamples (blockUnion I D) Q).card := by
        congr 1
      _ = ∏ i ∈ I, (eventSamples (D i) (P i)).card :=
        card_pairwise_disjoint_events I D P hdis
  rw [hleft, hraw, hfixed, hfamily]
  simp

end Coordinates

/-! ## Graph coordinates -/

/-- A possible edge: a non-diagonal unordered pair of vertices. -/
abbrev Edge (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

section Graphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of all possible graph edges. -/
def edgeUniverse (V : Type*) [Fintype V] [DecidableEq V] : Finset (Edge V) :=
  Finset.univ

/-- Turn a finite set of non-diagonal unordered pairs into a simple graph. -/
def graphOfEdges (S : Finset (Edge V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (S : Set (Edge V)))

@[simp] theorem mem_graphOfEdges_edgeSet {S : Finset (Edge V)} {e : Edge V} :
    e.1 ∈ (graphOfEdges S).edgeSet ↔ e ∈ S := by
  simp [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet, e.property]

/-- Recover the finite coordinate set of a finite graph. -/
noncomputable def edgesOfGraph (G : SimpleGraph V) : Finset (Edge V) := by
  classical
  exact Finset.univ.filter fun e ↦ e.1 ∈ G.edgeSet

@[simp] theorem mem_edgesOfGraph {G : SimpleGraph V} {e : Edge V} :
    e ∈ edgesOfGraph G ↔ e.1 ∈ G.edgeSet := by
  classical
  simp [edgesOfGraph]

@[simp] theorem edgesOfGraph_graphOfEdges (S : Finset (Edge V)) :
    edgesOfGraph (graphOfEdges S) = S := by
  classical
  ext e
  simp

@[simp] theorem graphOfEdges_edgesOfGraph (G : SimpleGraph V) :
    graphOfEdges (edgesOfGraph G) = G := by
  classical
  apply SimpleGraph.edgeSet_injective
  ext e
  change e ∈ (SimpleGraph.fromEdgeSet
    (Subtype.val '' (edgesOfGraph G : Set (Edge V)))).edgeSet ↔ e ∈ G.edgeSet
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro he
    rcases he.1 with ⟨e', he', rfl⟩
    simpa using he'
  · intro he
    have hnd : ¬e.IsDiag := G.edgeSet_subset_compl_diagSet he
    exact ⟨⟨⟨e, hnd⟩, by simp [edgesOfGraph, he]⟩, hnd⟩

/-- Finite edge sets and simple graphs are equivalent. -/
noncomputable def edgeSetEquivGraph : Finset (Edge V) ≃ SimpleGraph V where
  toFun := graphOfEdges
  invFun := edgesOfGraph
  left_inv := edgesOfGraph_graphOfEdges
  right_inv := graphOfEdges_edgesOfGraph

@[simp] theorem card_edgeUniverse : (edgeUniverse V).card = (Fintype.card V).choose 2 := by
  classical
  rw [edgeUniverse, Finset.card_univ]
  change Fintype.card {e : Sym2 V // ¬e.IsDiag} = (Fintype.card V).choose 2
  exact Sym2.card_diagSet_compl

/-- The number of labelled simple graphs on `V`. -/
theorem card_simpleGraph : Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
  classical
  rw [← Fintype.card_congr edgeSetEquivGraph]
  change Fintype.card (Finset (Edge V)) = _
  rw [Fintype.card_finset]
  congr 1
  exact card_edgeUniverse (V := V)

/-! ## Independent stars -/

/-- The edge joining a fixed root to a vertex in `W`. -/
private def starEdge (u : V) (W : Finset V) (hu : u ∉ W) (w : W) : Edge V :=
  ⟨s(u, w.1), by
    rw [Sym2.mk_isDiag_iff]
    intro huw
    apply hu
    simpa [huw] using w.2⟩

/-- The coordinate block formed by all edges from `u` to `W`.

The proof `u ∉ W` is included so every displayed unordered pair is
non-diagonal. -/
def starEdges (u : V) (W : Finset V) (hu : u ∉ W) : Finset (Edge V) :=
  W.attach.image (starEdge u W hu)

theorem mem_starEdges_iff {u : V} {W : Finset V} {hu : u ∉ W} {e : Edge V} :
    e ∈ starEdges u W hu ↔ ∃ w ∈ W, e.1 = s(u, w) := by
  constructor
  · intro he
    rcases Finset.mem_image.1 he with ⟨w, _hw, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, he⟩
    apply Finset.mem_image.2
    refine ⟨⟨w, hw⟩, by simp, ?_⟩
    apply Subtype.ext
    exact he.symm

@[simp] theorem card_starEdges (u : V) (W : Finset V) (hu : u ∉ W) :
    (starEdges u W hu).card = W.card := by
  rw [starEdges, Finset.card_image_iff.mpr]
  · simp
  · intro w _ z _ hwz
    apply Subtype.ext
    apply Sym2.congr_right.mp
    exact congrArg Subtype.val hwz

theorem starEdges_subset_edgeUniverse (u : V) (W : Finset V) (hu : u ∉ W) :
    starEdges u W hu ⊆ edgeUniverse V := by
  simp [edgeUniverse]

/-- Stars with distinct roots outside the common target set use disjoint edge
coordinates. -/
theorem disjoint_starEdges {u v : V} {W : Finset V}
    (huv : u ≠ v) (hu : u ∉ W) (hv : v ∉ W) :
    Disjoint (starEdges u W hu) (starEdges v W hv) := by
  rw [Finset.disjoint_left]
  intro e heu hev
  rcases mem_starEdges_iff.1 heu with ⟨w, hwW, hew⟩
  rcases mem_starEdges_iff.1 hev with ⟨z, hzW, hez⟩
  have hpair : s(u, w) = s(v, z) := hew.symm.trans hez
  rcases Sym2.eq_iff.1 hpair with h | h
  · exact huv h.1
  · apply hu
    simpa [h.1] using hzW

/-- Exact count for an event depending only on one star in the uniform random
graph. -/
theorem card_uniform_star_event (u : V) (W : Finset V) (hu : u ∉ W)
    (P : Finset (Edge V) → Prop) [DecidablePred P] :
    ((edgeUniverse V).powerset.filter fun S ↦
        P (restrict (starEdges u W hu) S)).card =
      2 ^ ((Fintype.card V).choose 2 - W.card) *
        ((starEdges u W hu).powerset.filter P).card := by
  simpa [card_edgeUniverse (V := V)] using
    card_restrict_event (edgeUniverse V) (starEdges u W hu)
      (starEdges_subset_edgeUniverse u W hu) P

/-- Exact product count for two star-supported events in the uniform random
graph.  This is the form used when multiplying two extension-event counts. -/
theorem card_uniform_two_star_event {u v : V} {W : Finset V}
    (huv : u ≠ v) (hu : u ∉ W) (hv : v ∉ W)
    (P Q : Finset (Edge V) → Prop) [DecidablePred P] [DecidablePred Q] :
    ((edgeUniverse V).powerset.filter fun S ↦
        P (restrict (starEdges u W hu) S) ∧
          Q (restrict (starEdges v W hv) S)).card =
      2 ^ ((Fintype.card V).choose 2 - 2 * W.card) *
        ((starEdges u W hu).powerset.filter P).card *
          ((starEdges v W hv).powerset.filter Q).card := by
  have hdis := disjoint_starEdges huv hu hv
  have hunion : (starEdges u W hu ∪ starEdges v W hv).card = 2 * W.card := by
    rw [Finset.card_union_of_disjoint hdis, card_starEdges, card_starEdges]
    omega
  simpa [card_edgeUniverse (V := V), hunion] using
    card_two_block_event (edgeUniverse V) (starEdges u W hu) (starEdges v W hv)
      hdis (Finset.union_subset
        (starEdges_subset_edgeUniverse u W hu)
        (starEdges_subset_edgeUniverse v W hv)) P Q

/-! ### The complete bipartite coordinate block `A × W` -/

private theorem root_not_mem_of_disjoint {A W : Finset V}
    (hAW : Disjoint A W) (a : A) : a.1 ∉ W := by
  intro haW
  exact Finset.disjoint_left.1 hAW a.2 haW

/-- The star at `a`, viewed as a block indexed by the subtype `A`. -/
def indexedStarEdges (A W : Finset V) (hAW : Disjoint A W) (a : A) :
    Finset (Edge V) :=
  starEdges a.1 W (root_not_mem_of_disjoint hAW a)

/-- All edge coordinates with one endpoint in `A` and the other in `W`.
This is expressed as the disjoint union of the stars rooted in `A`. -/
def crossStarEdges (A W : Finset V) (hAW : Disjoint A W) : Finset (Edge V) :=
  blockUnion Finset.univ (indexedStarEdges A W hAW)

theorem pairwiseDisjoint_indexedStarEdges (A W : Finset V)
    (hAW : Disjoint A W) :
    (Set.univ : Set A).PairwiseDisjoint (indexedStarEdges A W hAW) := by
  intro a _ha b _hb hab
  apply disjoint_starEdges
  · intro hav
    exact hab (Subtype.ext hav)

@[simp] theorem card_indexedStarEdges (A W : Finset V)
    (hAW : Disjoint A W) (a : A) :
    (indexedStarEdges A W hAW a).card = W.card := by
  simp [indexedStarEdges]

/-- There are exactly `|A| |W|` unordered pairs between two disjoint vertex
sets. -/
@[simp] theorem card_crossStarEdges (A W : Finset V) (hAW : Disjoint A W) :
    (crossStarEdges A W hAW).card = A.card * W.card := by
  have hpair : (↑(Finset.univ : Finset A) : Set A).PairwiseDisjoint
      (indexedStarEdges A W hAW) := by
    simpa using pairwiseDisjoint_indexedStarEdges A W hAW
  rw [crossStarEdges, blockUnion, Finset.card_biUnion hpair]
  rw [Finset.sum_const_nat (fun a _ha ↦ card_indexedStarEdges A W hAW a)]
  simp

theorem crossStarEdges_subset_edgeUniverse (A W : Finset V)
    (hAW : Disjoint A W) :
    crossStarEdges A W hAW ⊆ edgeUniverse V := by
  intro e he
  exact Finset.mem_univ e

/-! ### Fixing the graph induced by `W` -/

/-- Embed an edge whose endpoints lie in the subtype `W` into the ambient
vertex type. -/
private def liftInternalEdge (W : Finset V) (e : Edge W) : Edge V :=
  ⟨Sym2.map Subtype.val e.1, by
    intro hdiag
    exact e.2 ((Sym2.isDiag_map Subtype.val_injective).1 hdiag)⟩

private theorem liftInternalEdge_injective (W : Finset V) :
    Function.Injective (liftInternalEdge W) := by
  intro e f hef
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  exact congrArg Subtype.val hef

/-- The edge-coordinate block of the graph induced by `W`. -/
def internalEdges (W : Finset V) : Finset (Edge V) :=
  (edgeUniverse W).image (liftInternalEdge W)

@[simp] theorem card_internalEdges (W : Finset V) :
    (internalEdges W).card = W.card.choose 2 := by
  rw [internalEdges, Finset.card_image_iff.mpr]
  · simpa using card_edgeUniverse (V := W)
  · intro e _he f _hf
    intro hef
    exact liftInternalEdge_injective W hef

theorem internalEdges_subset_edgeUniverse (W : Finset V) :
    internalEdges W ⊆ edgeUniverse V := by
  intro e he
  exact Finset.mem_univ e

private theorem endpoint_mem_map_subtype (W : Finset V)
    {z : Sym2 W} {x : V} (hx : x ∈ Sym2.map Subtype.val z) : x ∈ W := by
  induction z using Sym2.inductionOn with
  | _ p q =>
      rw [Sym2.map_mk, Sym2.mem_iff] at hx
      rcases hx with hxp | hxq
      · simpa [hxp] using p.2
      · simpa [hxq] using q.2

private theorem endpoint_mem_of_mem_liftInternalEdge (W : Finset V)
    (e : Edge W) {x : V} (hx : x ∈ (liftInternalEdge W e).1) : x ∈ W :=
  endpoint_mem_map_subtype W hx

theorem disjoint_internalEdges_indexedStarEdges (A W : Finset V)
    (hAW : Disjoint A W) (a : A) :
    Disjoint (internalEdges W) (indexedStarEdges A W hAW a) := by
  rw [Finset.disjoint_left]
  intro e heInt heStar
  rcases Finset.mem_image.1 heInt with ⟨f, _hf, rfl⟩
  rcases mem_starEdges_iff.1 heStar with ⟨w, hwW, heq⟩
  apply root_not_mem_of_disjoint hAW a
  apply endpoint_mem_of_mem_liftInternalEdge W f
  rw [heq]
  exact Sym2.mem_mk_left _ _

theorem disjoint_internalEdges_crossStarEdges (A W : Finset V)
    (hAW : Disjoint A W) :
    Disjoint (internalEdges W) (crossStarEdges A W hAW) := by
  rw [Finset.disjoint_left]
  intro e heInt heCross
  rcases Finset.mem_biUnion.1 heCross with ⟨a, _ha, hea⟩
  exact Finset.disjoint_left.1
    (disjoint_internalEdges_indexedStarEdges A W hAW a) heInt hea

/-- Exact product formula for one extension event per vertex of `A`.  The
events see precisely, and only, the edge coordinates from their root to `W`.
Thus the theorem can be used after the graph induced by `W` has been fixed. -/
theorem card_uniform_star_family_event (A W : Finset V)
    (hAW : Disjoint A W) (P : A → Finset (Edge V) → Prop)
    [∀ a, DecidablePred (P a)] :
    (eventSamples (edgeUniverse V)
      (supportedEvents Finset.univ (indexedStarEdges A W hAW) P)).card =
      2 ^ ((Fintype.card V).choose 2 - A.card * W.card) *
        ∏ a : A, (eventSamples (indexedStarEdges A W hAW a) (P a)).card := by
  have hdis : ∀ a ∈ (Finset.univ : Finset A), ∀ b ∈ (Finset.univ : Finset A),
      a ≠ b → Disjoint (indexedStarEdges A W hAW a)
        (indexedStarEdges A W hAW b) := by
    intro a _ha b _hb hab
    exact pairwiseDisjoint_indexedStarEdges A W hAW (Set.mem_univ a)
      (Set.mem_univ b) hab
  have h := card_family_event (edgeUniverse V) (Finset.univ : Finset A)
    (indexedStarEdges A W hAW) P hdis
    (crossStarEdges_subset_edgeUniverse A W hAW)
  have hcard : (blockUnion (Finset.univ : Finset A)
      (indexedStarEdges A W hAW)).card = A.card * W.card := by
    simpa [crossStarEdges] using card_crossStarEdges A W hAW
  rw [hcard] at h
  simpa [card_edgeUniverse (V := V)] using h

/-- Conditional product count after the complete induced graph on `W` has
been fixed to `fixed`.  This is the exact finite replacement for saying that,
conditional on `G[W]`, the stars from the vertices of `A` to `W` remain
independent and uniform. -/
theorem card_uniform_fixed_internal_star_family_event (A W : Finset V)
    (hAW : Disjoint A W) (fixed : Finset (Edge V))
    (hfixed : fixed ⊆ internalEdges W)
    (P : A → Finset (Edge V) → Prop) [∀ a, DecidablePred (P a)] :
    (eventSamples (edgeUniverse V) fun S ↦
      restrict (internalEdges W) S = fixed ∧
        supportedEvents Finset.univ (indexedStarEdges A W hAW) P S).card =
      2 ^ ((Fintype.card V).choose 2 - (W.card.choose 2 + A.card * W.card)) *
        ∏ a : A, (eventSamples (indexedStarEdges A W hAW a) (P a)).card := by
  have hdis : ∀ a ∈ (Finset.univ : Finset A), ∀ b ∈ (Finset.univ : Finset A),
      a ≠ b → Disjoint (indexedStarEdges A W hAW a)
        (indexedStarEdges A W hAW b) := by
    intro a _ha b _hb hab
    exact pairwiseDisjoint_indexedStarEdges A W hAW (Set.mem_univ a)
      (Set.mem_univ b) hab
  have hFdis : Disjoint (internalEdges W)
      (blockUnion (Finset.univ : Finset A) (indexedStarEdges A W hAW)) := by
    simpa [crossStarEdges] using disjoint_internalEdges_crossStarEdges A W hAW
  have hU : internalEdges W ∪
      blockUnion (Finset.univ : Finset A) (indexedStarEdges A W hAW) ⊆
        edgeUniverse V := by
    exact Finset.union_subset (internalEdges_subset_edgeUniverse W)
      (crossStarEdges_subset_edgeUniverse A W hAW)
  have h := card_fixed_and_family_event (edgeUniverse V) (internalEdges W) fixed
    (Finset.univ : Finset A) (indexedStarEdges A W hAW) P hfixed hdis hFdis hU
  have hcross : (blockUnion (Finset.univ : Finset A)
      (indexedStarEdges A W hAW)).card = A.card * W.card := by
    simpa [crossStarEdges] using card_crossStarEdges A W hAW
  have hunion : (internalEdges W ∪ blockUnion (Finset.univ : Finset A)
      (indexedStarEdges A W hAW)).card = W.card.choose 2 + A.card * W.card := by
    rw [Finset.card_union_of_disjoint hFdis, card_internalEdges, hcross]
  rw [hunion] at h
  simpa [card_edgeUniverse (V := V)] using h

end Graphs

end RandomGraph
end Erdos565
