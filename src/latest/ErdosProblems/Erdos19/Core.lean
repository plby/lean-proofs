/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos19.FiniteBoundedDifferences

/-!
# Erdős Problem 19 (Erdős--Faber--Lovász)

This file formalizes the exact finite graph statement and the elementary part of
the reduction.

The published theorem of Kang--Kelly--Kühn--Methuku--Osthus proves
`EventuallyEFL`, i.e. `EFLAt n` for all sufficiently large `n`.  A proof of
that deep result is not currently present in Mathlib.
-/

namespace Erdos19

open scoped ENat

universe u v

/-! ## A finite partial-injection extension lemma -/

/-- An injection prescribed on a subtype of a finite domain extends to the
whole domain whenever the codomain has at least as many elements.  The proof
first chooses any embedding of the whole domain and then permutes the codomain
so that it agrees with the prescribed map. -/
lemma exists_injective_extension {A B : Type*} [Fintype A] [Fintype B]
    (p : A → Prop) (f : {a // p a} → B) (hf : Function.Injective f)
    (hcard : Fintype.card A ≤ Fintype.card B) :
    ∃ g : A → B, Function.Injective g ∧ ∀ a (ha : p a), g a = f ⟨a, ha⟩ := by
  classical
  obtain ⟨g₀ : A ↪ B⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : {a // p a} ↦ g₀ a.1) f
    (g₀.injective.comp Subtype.val_injective) hf
  refine ⟨fun a ↦ σ (g₀ a), σ.injective.comp g₀.injective, ?_⟩
  intro a ha
  exact hσ ⟨a, ha⟩

/-- A deliberately strong finite system-of-distinct-representatives lemma.
If every member of an indexed family contains at least as many elements as
there are indices, then the family has distinct representatives. -/
lemma exists_injective_mem_of_card_le {I A : Type*} [Fintype I] [Fintype A]
    (S : I → Finset A) (hcard : ∀ i, Fintype.card I ≤ (S i).card) :
    ∃ f : I → A, Function.Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp
  intro T
  by_cases hT : T.Nonempty
  · obtain ⟨i, hi⟩ := hT
    calc
      T.card ≤ Fintype.card I := Finset.card_le_univ T
      _ ≤ (S i).card := hcard i
      _ ≤ (T.biUnion S).card :=
        Finset.card_le_card (Finset.subset_biUnion_of_mem S hi)
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hT]

/-- Finite union-bound form of the probabilistic method.  If the total
cardinality of a finite family of bad sets is smaller than the sample space,
some sample avoids every bad set. -/
lemma exists_avoiding_of_sum_ncard_lt_card {Ω I : Type*}
    [Fintype Ω] [Fintype I] (bad : I → Set Ω)
    (hbad : (∑ i : I, (bad i).ncard) < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i, ω ∉ bad i := by
  by_contra hnone
  push_neg at hnone
  have hunion : (⋃ i, bad i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨i, hi⟩ := hnone ω
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hcover : Fintype.card Ω ≤ ∑ i : I, (bad i).ncard := by
    calc
      Fintype.card Ω = (Set.univ : Set Ω).ncard := by simp
      _ = (⋃ i, bad i).ncard := by rw [hunion]
      _ ≤ ∑ i : I, (bad i).ncard := Set.ncard_iUnion_le_of_fintype bad
  omega

/-! ### A finite-cardinality local lemma

The locally sparse coloring input used later in the published proof is
probabilistic.  The following denominator-free local lemma isolates its first
general dependency.  `avoidingBad bad S` is the finite sample set on which all
events indexed by `S` are avoided. -/

/-- Assignments which avoid every bad event with an index in `S`. -/
noncomputable def avoidingBad {Ω I : Type*} [Fintype Ω]
    (bad : I → Set Ω) (S : Finset I) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ bad i

@[simp]
lemma mem_avoidingBad {Ω I : Type*} [Fintype Ω]
    (bad : I → Set Ω) (S : Finset I) (ω : Ω) :
    ω ∈ avoidingBad bad S ↔ ∀ i ∈ S, ω ∉ bad i := by
  classical
  simp [avoidingBad]

/-- The elements of a set in a finite ambient type, without requiring a
separate `Fintype` instance on the subtype in theorem statements. -/
noncomputable def eventFinset {Ω : Type*} [Fintype Ω] (s : Set Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω ↦ ω ∈ s

@[simp]
lemma mem_eventFinset {Ω : Type*} [Fintype Ω] (s : Set Ω) (ω : Ω) :
    ω ∈ eventFinset s ↔ ω ∈ s := by
  classical
  simp [eventFinset]

lemma card_eventFinset_eq_ncard {Ω : Type*} [Fintype Ω] (s : Set Ω) :
    (eventFinset s).card = s.ncard := by
  classical
  let hs : s.Finite := Set.toFinite s
  have heq : eventFinset s = hs.toFinset := by
    ext x
    simp
  rw [heq, ← Set.ncard_eq_toFinset_card s hs]

lemma avoidingBad_mono {Ω I : Type*} [Fintype Ω]
    (bad : I → Set Ω) {S T : Finset I} (hST : S ⊆ T) :
    avoidingBad bad T ⊆ avoidingBad bad S := by
  classical
  intro ω hω
  rw [mem_avoidingBad] at hω ⊢
  exact fun i hi ↦ hω i (hST hi)

lemma avoidingBad_insert {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq I]
    (bad : I → Set Ω) (i : I) (S : Finset I) :
    avoidingBad bad (insert i S) = avoidingBad bad S \ eventFinset (bad i) := by
  classical
  ext ω
  simp [mem_avoidingBad, and_comm]

/-- A symmetric Lovász-local-lemma criterion stated entirely with finite
cardinalities.  `dep i j` records the events on which event `i` may depend.
The last hypothesis says that, after conditioning on the avoidance of any
family of nondependencies, event `i` has conditional probability at most
`1 / (4D)`.  If each event has at most `D` dependencies, all bad events can be
avoided simultaneously.

This conditional formulation is particularly convenient for product sample
spaces: independence proves the last inequality by cancelling the number of
assignments on the coordinates outside the support of event `i`. -/
theorem finite_local_lemma_of_conditional_card
    {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty Ω]
    [DecidableEq Ω] [DecidableEq I]
    (bad : I → Set Ω) (dep : I → I → Prop) [DecidableRel dep]
    (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ i,
      ((Finset.univ : Finset I).filter (dep i)).card ≤ D)
    (hfar : ∀ i (S : Finset I),
      (∀ j ∈ S, ¬dep i j) →
        4 * D * (eventFinset (bad i) ∩ avoidingBad bad S).card ≤
          (avoidingBad bad S).card) :
    ∃ ω : Ω, ∀ i, ω ∉ bad i := by
  classical
  have hconditional : ∀ (T : Finset I) (i : I), i ∉ T →
      2 * D * (eventFinset (bad i) ∩ avoidingBad bad T).card ≤
        (avoidingBad bad T).card := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro i hiT
      let near : Finset I := T.filter (dep i)
      let far : Finset I := T.filter fun j ↦ ¬dep i j
      have hfarSub : far ⊆ T := Finset.filter_subset _ _
      have hnearSub : near ⊆ T := Finset.filter_subset _ _
      have hfarCondition : ∀ j ∈ far, ¬dep i j := by
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      by_cases hnearEmpty : near = ∅
      · have hTfar : T = far := by
          ext j
          constructor
          · intro hjT
            have hjnot : ¬dep i j := by
              intro hjdep
              have : j ∈ near := Finset.mem_filter.mpr ⟨hjT, hjdep⟩
              simpa [hnearEmpty] using this
            exact Finset.mem_filter.mpr ⟨hjT, hjnot⟩
          · intro hj
            exact hfarSub hj
        have hstrong := hfar i far hfarCondition
        have hfactor : 2 * D ≤ 4 * D := Nat.mul_le_mul_right D (by omega)
        rw [hTfar]
        exact (Nat.mul_le_mul_right _ hfactor).trans hstrong
      · have hnearNonempty : near.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnearEmpty
        obtain ⟨j₀, hj₀near⟩ := hnearNonempty
        have hj₀T : j₀ ∈ T := hnearSub hj₀near
        have hj₀notFar : j₀ ∉ far := by
          intro hjfar
          exact (Finset.mem_filter.mp hjfar).2 (Finset.mem_filter.mp hj₀near).2
        have hfarProper : far ⊂ T :=
          (Finset.ssubset_iff_of_subset hfarSub).mpr ⟨j₀, hj₀T, hj₀notFar⟩
        have hnearCard : near.card ≤ D := by
          apply (Finset.card_le_card ?_).trans (hdegree i)
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩
        have hfarAvoidSub : avoidingBad bad T ⊆ avoidingBad bad far :=
          avoidingBad_mono bad hfarSub
        let lost := avoidingBad bad far \ avoidingBad bad T
        let witnesses : I → Finset Ω := fun j ↦
          eventFinset (bad j) ∩ avoidingBad bad far
        have hlostSub : lost ⊆ near.biUnion witnesses := by
          intro ω hω
          have hωfar : ω ∈ avoidingBad bad far :=
            (Finset.mem_sdiff.mp hω).1
          have hωnotT : ω ∉ avoidingBad bad T :=
            (Finset.mem_sdiff.mp hω).2
          have hex : ∃ j ∈ T, ω ∈ bad j := by
            by_contra hnone
            apply hωnotT
            rw [mem_avoidingBad]
            intro j hjT hjbad
            apply hnone
            exact ⟨j, hjT, hjbad⟩
          obtain ⟨j, hjT, hjbad⟩ := hex
          have hjnear : j ∈ near := by
            apply Finset.mem_filter.mpr
            refine ⟨hjT, ?_⟩
            by_contra hjnot
            have hjfar : j ∈ far := Finset.mem_filter.mpr ⟨hjT, hjnot⟩
            exact (mem_avoidingBad bad far ω).mp hωfar j hjfar hjbad
          apply Finset.mem_biUnion.mpr
          refine ⟨j, hjnear, ?_⟩
          exact Finset.mem_inter.mpr
            ⟨(mem_eventFinset (bad j) ω).mpr hjbad, hωfar⟩
        have hlostCard : lost.card ≤ ∑ j ∈ near, (witnesses j).card := by
          exact (Finset.card_le_card hlostSub).trans Finset.card_biUnion_le
        have hsum : 2 * (∑ j ∈ near, (witnesses j).card) ≤
            (avoidingBad bad far).card := by
          have hmul : (2 * D) * (∑ j ∈ near, (witnesses j).card) ≤
              D * (avoidingBad bad far).card := by
            calc
              (2 * D) * (∑ j ∈ near, (witnesses j).card) =
                  ∑ j ∈ near, (2 * D) * (witnesses j).card := by
                    rw [Finset.mul_sum]
              _ ≤ ∑ _j ∈ near, (avoidingBad bad far).card := by
                apply Finset.sum_le_sum
                intro j hj
                apply ih far hfarProper j
                intro hjfar
                exact (Finset.mem_filter.mp hjfar).2 (Finset.mem_filter.mp hj).2
              _ = near.card * (avoidingBad bad far).card := by simp
              _ ≤ D * (avoidingBad bad far).card :=
                Nat.mul_le_mul_right _ hnearCard
          apply Nat.le_of_mul_le_mul_left
          · simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
          · exact hD
        have hlostTwice : 2 * lost.card ≤ (avoidingBad bad far).card :=
          (Nat.mul_le_mul_left 2 hlostCard).trans hsum
        have hfarCard : (avoidingBad bad far).card ≤
            2 * (avoidingBad bad T).card := by
          have hcardEq := Finset.card_sdiff_add_card_eq_card hfarAvoidSub
          change lost.card + (avoidingBad bad T).card =
            (avoidingBad bad far).card at hcardEq
          omega
        have hbadSub :
            eventFinset (bad i) ∩ avoidingBad bad T ⊆
              eventFinset (bad i) ∩ avoidingBad bad far := by
          intro ω hω
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hω).1,
              hfarAvoidSub (Finset.mem_inter.mp hω).2⟩
        have hstrong := hfar i far hfarCondition
        have hfour : 4 * D *
              (eventFinset (bad i) ∩ avoidingBad bad T).card ≤
            2 * (avoidingBad bad T).card :=
          ((Nat.mul_le_mul_left (4 * D) (Finset.card_le_card hbadSub)).trans
            hstrong).trans hfarCard
        have hcancel :
            2 * (2 * D * (eventFinset (bad i) ∩ avoidingBad bad T).card) ≤
              2 * (avoidingBad bad T).card := by
          calc
            2 * (2 * D * (eventFinset (bad i) ∩ avoidingBad bad T).card) =
                4 * D * (eventFinset (bad i) ∩ avoidingBad bad T).card := by ring
            _ ≤ 2 * (avoidingBad bad T).card := hfour
        exact Nat.le_of_mul_le_mul_left hcancel (by omega)
  have hall : ∀ S : Finset I, (avoidingBad bad S).Nonempty := by
    intro S
    induction S using Finset.induction with
    | empty =>
        simpa [avoidingBad] using (Finset.univ_nonempty :
          (Finset.univ : Finset Ω).Nonempty)
    | @insert i S hi ih =>
        have hbound := hconditional S i hi
        have hinterLt : (eventFinset (bad i) ∩ avoidingBad bad S).card <
            (avoidingBad bad S).card := by
          have hpos : 0 < (avoidingBad bad S).card := Finset.card_pos.mpr ih
          have htwo : 2 ≤ 2 * D := by omega
          by_contra hnot
          have hreverse : (avoidingBad bad S).card ≤
              (eventFinset (bad i) ∩ avoidingBad bad S).card := by omega
          have htwice : 2 * (avoidingBad bad S).card ≤
              (avoidingBad bad S).card := by
            calc
              2 * (avoidingBad bad S).card ≤
                  (2 * D) * (avoidingBad bad S).card :=
                Nat.mul_le_mul_right _ htwo
              _ ≤ (2 * D) *
                  (eventFinset (bad i) ∩ avoidingBad bad S).card :=
                Nat.mul_le_mul_left _ hreverse
              _ ≤ (avoidingBad bad S).card := hbound
          omega
        rw [avoidingBad_insert]
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff]
        omega
  obtain ⟨ω, hω⟩ := hall (Finset.univ : Finset I)
  refine ⟨ω, ?_⟩
  intro i hi
  exact (mem_avoidingBad bad Finset.univ ω).mp hω i (Finset.mem_univ i) hi

/-- Usual independence form of the finite local lemma.  The bad-event bound
is unconditional, and the displayed cross-multiplication says that event `i`
is independent of avoiding any family of its nondependencies. -/
theorem finite_local_lemma_of_card_independence
    {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty Ω]
    [DecidableEq Ω] [DecidableEq I]
    (bad : I → Set Ω) (dep : I → I → Prop) [DecidableRel dep]
    (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ i,
      ((Finset.univ : Finset I).filter (dep i)).card ≤ D)
    (hbad : ∀ i,
      4 * D * (eventFinset (bad i)).card ≤ Fintype.card Ω)
    (hindependent : ∀ i (S : Finset I),
      (∀ j ∈ S, ¬dep i j) →
        (eventFinset (bad i) ∩ avoidingBad bad S).card * Fintype.card Ω =
          (eventFinset (bad i)).card * (avoidingBad bad S).card) :
    ∃ ω : Ω, ∀ i, ω ∉ bad i := by
  apply finite_local_lemma_of_conditional_card bad dep D hD hdegree
  intro i S hfar
  have hind := hindependent i S hfar
  apply Nat.le_of_mul_le_mul_right
  · calc
      (4 * D * (eventFinset (bad i) ∩ avoidingBad bad S).card) *
            Fintype.card Ω =
          4 * D *
            ((eventFinset (bad i) ∩ avoidingBad bad S).card *
              Fintype.card Ω) := by ring
      _ = 4 * D *
            ((eventFinset (bad i)).card * (avoidingBad bad S).card) := by
              rw [hind]
      _ = (4 * D * (eventFinset (bad i)).card) *
            (avoidingBad bad S).card := by ring
      _ ≤ Fintype.card Ω * (avoidingBad bad S).card :=
        Nat.mul_le_mul_right _ (hbad i)
      _ = (avoidingBad bad S).card * Fintype.card Ω := by ring
  · exact Fintype.card_pos

/-! ### Independence from disjoint coordinate supports -/

/-- An event in a finite product depends only on the coordinates in `S` if
changing all coordinates outside `S` does not change membership. -/
def EventDependsOn {A K : Type*} (E : Set (A → K)) (S : Set A) : Prop :=
  ∀ f g, (∀ x ∈ S, f x = g x) → (f ∈ E ↔ g ∈ E)

/-- Events depending on complementary coordinate sets are independent in the
uniform finite product space.  The proof is an explicit switching bijection:
from `(f,g) ∈ E × F`, take the `S`-coordinates from `f` and the complementary
coordinates from `g` to obtain a point in `E ∩ F`; the unused coordinates form
an arbitrary second assignment. -/
lemma ncard_inter_mul_of_complementary_coordinate_dependence
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]
    (S : Set A) (E F : Set (A → K))
    (hE : EventDependsOn E S) (hF : EventDependsOn F Sᶜ) :
    (E ∩ F).ncard * Fintype.card (A → K) = E.ncard * F.ncard := by
  classical
  let splice (f g : A → K) : A → K := fun x ↦ if x ∈ S then f x else g x
  have splice_same (f g : A → K) :
      splice (splice f g) (splice g f) = f := by
    funext x
    by_cases hx : x ∈ S <;> simp [splice, hx]
  have splice_mem_E (f : E) (g : F) : splice f g ∈ E := by
    apply (hE f (splice f g) ?_).mp f.2
    intro x hx
    simp [splice, hx]
  have splice_mem_F (f : E) (g : F) : splice f g ∈ F := by
    apply (hF g (splice f g) ?_).mp g.2
    intro x hx
    have hxnot : x ∉ S := by simpa using hx
    simp [splice, hxnot]
  have splice_from_inter_mem_E (h : ↥(E ∩ F)) (l : A → K) :
      splice h l ∈ E := by
    apply (hE h (splice h l) ?_).mp h.2.1
    intro x hx
    simp [splice, hx]
  have splice_from_inter_mem_F (h : ↥(E ∩ F)) (l : A → K) :
      splice l h ∈ F := by
    apply (hF h (splice l h) ?_).mp h.2.2
    intro x hx
    have hxnot : x ∉ S := by simpa using hx
    simp [splice, hxnot]
  let switchEquiv : E × F ≃ ↥(E ∩ F) × (A → K) := {
    toFun p :=
      (⟨splice p.1 p.2, splice_mem_E p.1 p.2, splice_mem_F p.1 p.2⟩,
        splice p.2 p.1)
    invFun p :=
      (⟨splice p.1 p.2, splice_from_inter_mem_E p.1 p.2⟩,
        ⟨splice p.2 p.1, splice_from_inter_mem_F p.1 p.2⟩)
    left_inv p := by
      rcases p with ⟨f, g⟩
      apply Prod.ext
      · apply Subtype.ext
        exact splice_same f g
      · apply Subtype.ext
        exact splice_same g f
    right_inv p := by
      rcases p with ⟨h, l⟩
      apply Prod.ext
      · apply Subtype.ext
        exact splice_same h l
      · exact splice_same l h
  }
  have hcard := Fintype.card_congr switchEquiv
  simpa only [Fintype.card_prod, Set.fintypeCard_eq_ncard] using hcard.symm

/-- Finset-cardinality version of complementary-support independence, in the
exact cross-multiplied form consumed by
`finite_local_lemma_of_card_independence`. -/
lemma eventFinset_inter_card_mul_of_complementary_coordinate_dependence
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]
    (S : Set A) (E F : Set (A → K))
    (hE : EventDependsOn E S) (hF : EventDependsOn F Sᶜ) :
    (eventFinset E ∩ eventFinset F).card * Fintype.card (A → K) =
      (eventFinset E).card * (eventFinset F).card := by
  classical
  have hset :=
    ncard_inter_mul_of_complementary_coordinate_dependence S E F hE hF
  have hinter : eventFinset (E ∩ F) = eventFinset E ∩ eventFinset F := by
    ext f
    simp
  have hcard (T : Set (A → K)) : (eventFinset T).card = T.ncard := by
    let hT : T.Finite := Set.toFinite T
    have heq : eventFinset T = hT.toFinset := by
      ext f
      simp
    rw [heq, ← Set.ncard_eq_toFinset_card T hT]
  rw [← hinter, hcard, hcard, hcard]
  exact hset

/-- Product-space local lemma.  Each bad event is supplied with a coordinate
support, and nondependent events have disjoint supports.  The switching
bijection above supplies exactly the independence equation required by the
finite local lemma. -/
theorem exists_avoiding_of_local_product_events
    {A K I : Type*} [Fintype A] [Fintype K] [Nonempty K] [Fintype I]
    [DecidableEq A] [DecidableEq K] [DecidableEq I]
    (bad : I → Set (A → K)) (support : I → Set A)
    (dep : I → I → Prop) [DecidableRel dep]
    (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ i,
      ((Finset.univ : Finset I).filter (dep i)).card ≤ D)
    (hdepends : ∀ i, EventDependsOn (bad i) (support i))
    (hdisjoint : ∀ {i j}, ¬dep i j → Disjoint (support i) (support j))
    (hbad : ∀ i,
      4 * D * (eventFinset (bad i)).card ≤ Fintype.card (A → K)) :
    ∃ assignment : A → K, ∀ i, assignment ∉ bad i := by
  classical
  apply finite_local_lemma_of_card_independence bad dep D hD hdegree hbad
  intro i T hfar
  let avoidEvent : Set (A → K) := ↑(avoidingBad bad T)
  have havoidDepends : EventDependsOn avoidEvent (support i)ᶜ := by
    intro f g hagree
    have hmem (hfg : ∀ x ∈ (support i)ᶜ, f x = g x) :
        f ∈ avoidEvent ↔ g ∈ avoidEvent := by
      change f ∈ avoidingBad bad T ↔ g ∈ avoidingBad bad T
      rw [mem_avoidingBad, mem_avoidingBad]
      constructor
      · intro hf j hjT hjbad
        have hijDisjoint : Disjoint (support i) (support j) :=
          hdisjoint (hfar j hjT)
        have hagreeJ : ∀ x ∈ support j, f x = g x := by
          intro x hxj
          apply hfg x
          have hxnot : x ∉ support i := by
            intro hxi
            exact Set.disjoint_left.mp hijDisjoint hxi hxj
          simpa using hxnot
        have hiff := hdepends j f g hagreeJ
        exact hf j hjT (hiff.mpr hjbad)
      · intro hg j hjT hjbad
        have hijDisjoint : Disjoint (support i) (support j) :=
          hdisjoint (hfar j hjT)
        have hagreeJ : ∀ x ∈ support j, f x = g x := by
          intro x hxj
          apply hfg x
          have hxnot : x ∉ support i := by
            intro hxi
            exact Set.disjoint_left.mp hijDisjoint hxi hxj
          simpa using hxnot
        have hiff := hdepends j f g hagreeJ
        exact hg j hjT (hiff.mp hjbad)
    exact hmem hagree
  have havoidFinset : eventFinset avoidEvent = avoidingBad bad T := by
    ext f
    simp [avoidEvent]
  rw [← havoidFinset]
  exact eventFinset_inter_card_mul_of_complementary_coordinate_dependence
    (support i) (bad i) avoidEvent (hdepends i) havoidDepends

/-- Every finite family of nonnegative integer weights has a partition into
capacity-`A` bins (singletons are allowed to exceed the capacity) which is
minimal among such partitions.  In a minimal partition, at most one bin has
weight at most `A / 2`: two such bins could otherwise be merged.  This is the
finite bin-packing fact used in Proposition 6.8(ii). -/
lemma exists_capacity_partition_with_at_most_one_small
    {S : Type*} [Fintype S] [DecidableEq S] (weight : S → ℕ) (A : ℕ) :
    ∃ P : Finpartition (Finset.univ : Finset S),
      (∀ p ∈ P.parts,
        p.card ≤ 1 ∨ (∑ x ∈ p, weight x) ≤ A) ∧
      (P.parts.filter fun p ↦ (∑ x ∈ p, weight x) ≤ A / 2).card ≤ 1 := by
  classical
  let Good (P : Finpartition (Finset.univ : Finset S)) : Prop :=
    ∀ p ∈ P.parts, p.card ≤ 1 ∨ (∑ x ∈ p, weight x) ≤ A
  have hbot : Good (⊥ : Finpartition (Finset.univ : Finset S)) := by
    intro p hp
    left
    rw [Finpartition.mem_bot_iff] at hp
    obtain ⟨x, _hx, rfl⟩ := hp
    simp
  let candidates :=
    (Finset.univ : Finset (Finpartition (Finset.univ : Finset S))).filter Good
  have hcandidates : candidates.Nonempty := by
    refine ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbot⟩⟩
  obtain ⟨P, hPcand, hminimal⟩ :=
    Finset.exists_min_image candidates (fun Q ↦ Q.parts.card) hcandidates
  have hPgood : Good P := (Finset.mem_filter.mp hPcand).2
  refine ⟨P, hPgood, ?_⟩
  let small := P.parts.filter fun p ↦ (∑ x ∈ p, weight x) ≤ A / 2
  by_contra hsmall
  change ¬small.card ≤ 1 at hsmall
  have hsmallTwo : 2 ≤ small.card := by omega
  have hsmallNonempty : small.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpSmall⟩ := hsmallNonempty
  have hpSmallMem : p ∈ small := hpSmall
  have herasePos : 0 < (small.erase p).card := by
    rw [Finset.card_erase_of_mem hpSmallMem]
    omega
  obtain ⟨q, hqErase⟩ := Finset.card_pos.mp herasePos
  have hqSmall : q ∈ small := Finset.mem_of_mem_erase hqErase
  have hpq : p ≠ q := by
    exact fun hpqeq ↦ (Finset.ne_of_mem_erase hqErase) hpqeq.symm
  have hpP : p ∈ P.parts := (Finset.mem_filter.mp hpSmallMem).1
  have hqP : q ∈ P.parts := (Finset.mem_filter.mp hqSmall).1
  have hpWeight : (∑ x ∈ p, weight x) ≤ A / 2 :=
    (Finset.mem_filter.mp hpSmallMem).2
  have hqWeight : (∑ x ∈ q, weight x) ≤ A / 2 :=
    (Finset.mem_filter.mp hqSmall).2
  have hpqDisjoint : Disjoint p q := P.disjoint hpP hqP hpq
  let mergedParts : Finset (Finset S) :=
    insert (p ∪ q) ((P.parts.erase p).erase q)
  have hpartsSubset : ∀ t ∈ mergedParts, t ⊆ (Finset.univ : Finset S) := by
    intro t _ht
    exact Finset.subset_univ t
  have hunionNonempty : (p ∪ q).Nonempty := by
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hpP
    exact ⟨x, Finset.mem_union_left q hx⟩
  have hexistsUnique :
      ∀ x ∈ (Finset.univ : Finset S), ∃! t ∈ mergedParts, x ∈ t := by
    intro x _hx
    by_cases hxpq : x ∈ p ∨ x ∈ q
    · have hpqMerged : p ∪ q ∈ mergedParts := by
        dsimp only [mergedParts]
        exact Finset.mem_insert_self (p ∪ q) ((P.parts.erase p).erase q)
      refine ⟨p ∪ q,
        ⟨hpqMerged, Finset.mem_union.mpr hxpq⟩, ?_⟩
      intro t ht
      have htmem := ht.1
      have hxt := ht.2
      rcases Finset.mem_insert.mp htmem with ht | ht
      · exact ht
      · have htEraseQ : t ∈ (P.parts.erase p).erase q := ht
        have htEraseP : t ∈ P.parts.erase p := Finset.mem_of_mem_erase htEraseQ
        have htP : t ∈ P.parts := Finset.mem_of_mem_erase htEraseP
        have htnp : t ≠ p := Finset.ne_of_mem_erase htEraseP
        have htnq : t ≠ q := Finset.ne_of_mem_erase htEraseQ
        rcases hxpq with hxp | hxq
        · exact (Finset.disjoint_left.mp (P.disjoint htP hpP htnp) hxt hxp).elim
        · exact (Finset.disjoint_left.mp (P.disjoint htP hqP htnq) hxt hxq).elim
    · let t := P.part x
      have htP : t ∈ P.parts := P.part_mem.mpr (Finset.mem_univ x)
      have hxt : x ∈ t := P.mem_part (Finset.mem_univ x)
      have htnp : t ≠ p := by
        intro htp
        apply hxpq
        left
        simpa [htp] using hxt
      have htnq : t ≠ q := by
        intro htq
        apply hxpq
        right
        simpa [htq] using hxt
      have htMerged : t ∈ mergedParts := by
        apply Finset.mem_insert.mpr
        right
        exact Finset.mem_erase.mpr ⟨htnq, Finset.mem_erase.mpr ⟨htnp, htP⟩⟩
      refine ⟨t, ⟨htMerged, hxt⟩, ?_⟩
      intro u hu
      have humem := hu.1
      have hxu := hu.2
      rcases Finset.mem_insert.mp humem with hu | hu
      · subst u
        exact (hxpq (Finset.mem_union.mp hxu)).elim
      · have huEraseQ : u ∈ (P.parts.erase p).erase q := hu
        have huP : u ∈ P.parts :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huEraseQ)
        exact P.eq_of_mem_parts huP htP hxu hxt
  have hmergedEmpty : ∅ ∉ mergedParts := by
    intro hempty
    rcases Finset.mem_insert.mp hempty with hempty | hempty
    · apply hunionNonempty.ne_empty
      exact hempty.symm
    · have hemptyP : ∅ ∈ P.parts :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hempty)
      exact P.empty_notMem_parts hemptyP
  let Q : Finpartition (Finset.univ : Finset S) :=
    Finpartition.ofExistsUnique mergedParts hpartsSubset hexistsUnique hmergedEmpty
  have hQgood : Good Q := by
    intro t ht
    change t ∈ mergedParts at ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · right
      subst t
      rw [Finset.sum_union hpqDisjoint]
      omega
    · have htP : t ∈ P.parts :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
      exact hPgood t htP
  have hqMem : q ∈ P.parts.erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, hqP⟩
  have hunionNotMem : p ∪ q ∉ (P.parts.erase p).erase q := by
    intro hu
    have huEraseP : p ∪ q ∈ P.parts.erase p := Finset.mem_of_mem_erase hu
    have huP : p ∪ q ∈ P.parts := Finset.mem_of_mem_erase huEraseP
    have hunionNeP : p ∪ q ≠ p := Finset.ne_of_mem_erase huEraseP
    obtain ⟨x, hxp⟩ := P.nonempty_of_mem_parts hpP
    exact Finset.disjoint_left.mp (P.disjoint huP hpP hunionNeP) 
      (Finset.mem_union_left q hxp) hxp
  have hQcard : Q.parts.card < P.parts.card := by
    change mergedParts.card < P.parts.card
    rw [Finset.card_insert_of_notMem hunionNotMem,
      Finset.card_erase_of_mem hqMem, Finset.card_erase_of_mem hpP]
    have hPtwo : 2 ≤ P.parts.card := by
      have hqEraseP : q ∈ P.parts.erase p := hqMem
      rw [Finset.mem_erase] at hqEraseP
      exact Finset.one_lt_card.mpr ⟨p, hpP, q, hqEraseP.2, hpq⟩
    omega
  have hQcand : Q ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQgood⟩
  have hminQ := hminimal Q hQcand
  omega

/-- Quantitative form of `exists_capacity_partition_with_at_most_one_small`.
All but at most one part have weight at least `A / 2 + 1`, so their number is
controlled by the total weight. -/
lemma exists_capacity_partition_card_bound
    {S : Type*} [Fintype S] [DecidableEq S] (weight : S → ℕ) (A : ℕ) :
    ∃ P : Finpartition (Finset.univ : Finset S),
      (∀ p ∈ P.parts,
        p.card ≤ 1 ∨ (∑ x ∈ p, weight x) ≤ A) ∧
      (P.parts.card - 1) * (A / 2 + 1) ≤ ∑ x : S, weight x := by
  classical
  obtain ⟨P, hcapacity, hsmall⟩ :=
    exists_capacity_partition_with_at_most_one_small weight A
  let isSmall : Finset S → Prop :=
    fun p ↦ (∑ x ∈ p, weight x) ≤ A / 2
  let small := P.parts.filter isSmall
  let large := P.parts.filter fun p ↦ ¬isSmall p
  have hsmall' : small.card ≤ 1 := by
    simpa only [small, isSmall] using hsmall
  have hsplit : small.card + large.card = P.parts.card := by
    simpa only [small, large] using
      (Finset.card_filter_add_card_filter_not (s := P.parts) isSmall)
  have hlargeCard : P.parts.card - 1 ≤ large.card := by omega
  have hlargeWeight : ∀ p ∈ large, A / 2 + 1 ≤ ∑ x ∈ p, weight x := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    change ¬(∑ x ∈ p, weight x) ≤ A / 2 at hp'
    omega
  refine ⟨P, hcapacity, ?_⟩
  calc
    (P.parts.card - 1) * (A / 2 + 1) ≤
        large.card * (A / 2 + 1) :=
      Nat.mul_le_mul_right _ hlargeCard
    _ = ∑ _p ∈ large, (A / 2 + 1) := by simp
    _ ≤ ∑ p ∈ large, ∑ x ∈ p, weight x := by
      apply Finset.sum_le_sum
      intro p hp
      exact hlargeWeight p hp
    _ ≤ ∑ p ∈ P.parts, ∑ x ∈ p, weight x := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ x ∈ P.parts.biUnion id, weight x := by
      symm
      simpa only [id_eq] using
        (Finset.sum_biUnion (f := weight) P.supIndep.pairwiseDisjoint)
    _ = ∑ x : S, weight x := by
      rw [P.biUnion_parts]

/-- Exact cardinality of a two-coordinate collision cylinder in the uniform
assignment space.  This is the basic counting replacement for the statement
that two independent uniform colors agree with probability `1/k`. -/
lemma card_fun_eq_at {A : Type*} [Fintype A] (k : ℕ) {x y : A}
    (hxy : x ≠ y) :
    Nat.card {f : A → Fin k // f x = f y} =
      k ^ (Fintype.card A - 1) := by
  classical
  let B := {z : A // z ≠ y}
  let collisionEquiv : {f : A → Fin k // f x = f y} ≃ (B → Fin k) := {
    toFun f z := f.1 z.1
    invFun g :=
      ⟨fun z ↦ if hz : z = y then g ⟨x, hxy⟩ else g ⟨z, hz⟩, by
        simp only [hxy, ↓reduceDIte]⟩
    left_inv f := by
      apply Subtype.ext
      funext z
      by_cases hz : z = y
      · subst z
        simp [hxy, f.2]
      · simp [hz]
    right_inv g := by
      funext z
      simp [z.2]
  }
  have hB : Fintype.card B = Fintype.card A - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun z : A ↦ z = y)]
    simp
  calc
    Nat.card {f : A → Fin k // f x = f y} = Nat.card (B → Fin k) :=
      Nat.card_congr collisionEquiv
    _ = k ^ Fintype.card B := by simp [Nat.card_eq_fintype_card]
    _ = k ^ (Fintype.card A - 1) := by rw [hB]

/-- Exact number of assignments in which three distinct coordinates receive
one common, freely chosen value. -/
lemma card_fun_eq_at_three {A : Type*} [Fintype A] (k : ℕ) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Nat.card {f : A → Fin k // f x = f y ∧ f x = f z} =
      k ^ (Fintype.card A - 2) := by
  classical
  let T : Finset A := {y, z}
  let B := {u : A // u ∉ T}
  have hxT : x ∉ T := by simp [T, hxy, hxz]
  let tripleEquiv : {f : A → Fin k // f x = f y ∧ f x = f z} ≃
      (B → Fin k) := {
    toFun f u := f.1 u.1
    invFun g :=
      ⟨fun u ↦ if hu : u ∈ T then g ⟨x, hxT⟩ else g ⟨u, hu⟩, by
        constructor <;> simp [T, hxy, hxz, hyz]⟩
    left_inv f := by
      apply Subtype.ext
      funext u
      by_cases huy : u = y
      · subst u
        simp [T, hxT, f.2.1]
      by_cases huz : u = z
      · subst u
        simp [T, hxT, f.2.2]
      · simp [T, huy, huz]
    right_inv g := by
      funext u
      simp [u.2]
  }
  have hTcard : T.card = 2 := by
    dsimp only [T]
    exact Finset.card_pair hyz
  have hBcard : Fintype.card B = Fintype.card A - 2 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun u : A ↦ u ∈ T)]
    have hmem : Fintype.card {u : A // u ∈ T} = T.card := by
      simpa using Fintype.card_coe T
    rw [hmem, hTcard]
  calc
    Nat.card {f : A → Fin k // f x = f y ∧ f x = f z} =
        Nat.card (B → Fin k) := Nat.card_congr tripleEquiv
    _ = k ^ Fintype.card B := by simp [Nat.card_eq_fintype_card]
    _ = k ^ (Fintype.card A - 2) := by rw [hBcard]

/-- Exact cardinality of a cylinder in a finite product space.  Prescribing
the values on a finite coordinate set `S` leaves exactly
`|K| ^ (|A| - |S|)` assignments. -/
lemma card_fun_restrict_eq {A K : Type*} [Fintype A] [Fintype K]
    (S : Finset A) (g : S → K) :
    Nat.card {f : A → K // ∀ x : S, f x.1 = g x} =
      Fintype.card K ^ (Fintype.card A - S.card) := by
  classical
  let B := {x : A // x ∉ S}
  let cylinderEquiv : {f : A → K // ∀ x : S, f x.1 = g x} ≃ (B → K) := {
    toFun f x := f.1 x.1
    invFun h :=
      ⟨fun x ↦ if hx : x ∈ S then g ⟨x, hx⟩ else h ⟨x, hx⟩, by
        intro x
        simp [x.2]⟩
    left_inv f := by
      apply Subtype.ext
      funext x
      by_cases hx : x ∈ S
      · simpa [hx] using (f.2 ⟨x, hx⟩).symm
      · simp [hx]
    right_inv h := by
      funext x
      simp [x.2]
  }
  have hB : Fintype.card B = Fintype.card A - S.card := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun x : A ↦ x ∈ S)]
    have hmem : Fintype.card {x : A // x ∈ S} = S.card := by
      simpa using Fintype.card_coe S
    rw [hmem]
  calc
    Nat.card {f : A → K // ∀ x : S, f x.1 = g x} = Nat.card (B → K) :=
      Nat.card_congr cylinderEquiv
    _ = Fintype.card K ^ Fintype.card B := by
      simp [Nat.card_eq_fintype_card]
    _ = Fintype.card K ^ (Fintype.card A - S.card) := by rw [hB]

/-- If an event in a finite product depends only on the coordinates in `S`,
its cardinality is the cardinality of the restricted event times the common
number of extensions of one restricted assignment. -/
lemma card_eventFinset_eq_mul_of_restriction
    {A K : Type*} [Fintype A] [Fintype K]
    (S : Finset A) (P : (S → K) → Prop) (E : Set (A → K))
    (hE : ∀ f, f ∈ E ↔ P (fun x : S ↦ f x.1)) :
    E.ncard =
      Set.ncard {g : S → K | P g} *
        Fintype.card K ^ (Fintype.card A - S.card) := by
  classical
  letI : Fintype (A → K) := Fintype.ofFinite _
  letI : Fintype (S → K) := Fintype.ofFinite _
  let L := {g : S → K // P g}
  let Fiber (g : L) := {f : A → K // ∀ x : S, f x.1 = g.1 x}
  let equiv : E ≃ Σ g : L, Fiber g := {
    toFun f := by
      let g : S → K := fun x ↦ f.1 x.1
      exact ⟨⟨g, (hE f.1).mp f.2⟩, ⟨f.1, fun _x ↦ rfl⟩⟩
    invFun z := ⟨z.2.1, (hE z.2.1).mpr (by
      have hrest : (fun x : S ↦ z.2.1 x.1) = z.1.1 := by
        funext x
        exact z.2.2 x
      rw [hrest]
      exact z.1.2)⟩
    left_inv f := by rfl
    right_inv z := by
      rcases z with ⟨⟨g, hg⟩, ⟨f, hf⟩⟩
      have hgf : (fun x : S ↦ f x.1) = g := by
        funext x
        exact hf x
      subst g
      rfl
  }
  have hfiber (g : L) :
      Fintype.card (Fiber g) =
        Fintype.card K ^ (Fintype.card A - S.card) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fun_restrict_eq S g.1
  have hlocal : Fintype.card L = Set.ncard {g : S → K | P g} :=
    Set.fintypeCard_eq_ncard _
  calc
    E.ncard = Fintype.card E := (Set.fintypeCard_eq_ncard E).symm
    _ = Fintype.card (Σ g : L, Fiber g) := Fintype.card_congr equiv
    _ = ∑ g : L, Fintype.card (Fiber g) := Fintype.card_sigma
    _ = ∑ _g : L,
        Fintype.card K ^ (Fintype.card A - S.card) := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact hfiber g
    _ = Set.ncard {g : S → K | P g} *
        Fintype.card K ^ (Fintype.card A - S.card) := by
      simp [hlocal]

/-- A statistic depending only on coordinates in `S` has total sum equal to
its restricted total sum times the common number of extensions. -/
lemma sum_eq_mul_of_restriction
    {A K : Type*} [Fintype A] [Fintype K]
    (S : Finset A) [Fintype (A → K)] [Fintype (S → K)]
    (X : (S → K) → ℕ) :
    (∑ f : A → K, X (fun x : S ↦ f x.1)) =
      (∑ g : S → K, X g) *
        Fintype.card K ^ (Fintype.card A - S.card) := by
  classical
  let Fiber (g : S → K) :=
    {f : A → K // ∀ x : S, f x.1 = g x}
  let equiv : (A → K) ≃ Σ g : S → K, Fiber g := {
    toFun f := ⟨(fun x ↦ f x.1), ⟨f, fun _x ↦ rfl⟩⟩
    invFun z := z.2.1
    left_inv f := rfl
    right_inv z := by
      rcases z with ⟨g, ⟨f, hf⟩⟩
      have hgf : (fun x : S ↦ f x.1) = g := by
        funext x
        exact hf x
      subst g
      rfl
  }
  have hfiber (g : S → K) :
      Fintype.card (Fiber g) =
        Fintype.card K ^ (Fintype.card A - S.card) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fun_restrict_eq S g
  calc
    (∑ f : A → K, X (fun x : S ↦ f x.1)) =
        ∑ z : Σ g : S → K, Fiber g, X z.1 := by
      exact equiv.sum_comp (fun z ↦ X z.1)
    _ = ∑ g : S → K, ∑ _h : Fiber g, X g := by
      rw [Fintype.sum_sigma]
    _ = ∑ g : S → K,
        Fintype.card K ^ (Fintype.card A - S.card) * X g := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_const, Finset.card_univ, hfiber]
      simp
    _ = (∑ g : S → K, X g) *
        Fintype.card K ^ (Fintype.card A - S.card) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _hg
      exact Nat.mul_comm _ _

/-- Restriction to finitely many relevant coordinates preserves the uniform
average of a statistic that depends only on those coordinates. -/
lemma finiteAverage_eq_of_restriction
    {A K : Type*} [Fintype A] [Fintype K] [Nonempty K]
    (S : Finset A) [Fintype (A → K)] [Fintype (S → K)]
    (X : (S → K) → ℕ) :
    finiteAverage (fun g : S → K ↦ (X g : ℝ)) =
      (∑ f : A → K, (X (fun x : S ↦ f x.1) : ℝ)) /
        Fintype.card (A → K) := by
  classical
  have hsumNat := sum_eq_mul_of_restriction S X
  have hsumReal :
      (∑ f : A → K, (X (fun x : S ↦ f x.1) : ℝ)) =
        (∑ g : S → K, (X g : ℝ)) *
          Fintype.card K ^ (Fintype.card A - S.card) := by
    exact_mod_cast hsumNat
  have hS : S.card ≤ Fintype.card A := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hpow :
      Fintype.card K ^ S.card *
          Fintype.card K ^ (Fintype.card A - S.card) =
        Fintype.card K ^ Fintype.card A := by
    rw [← pow_add]
    congr 1
    omega
  have hcardFull :
      Fintype.card (A → K) = Fintype.card K ^ Fintype.card A := by
    calc
      Fintype.card (A → K) = Nat.card (A → K) :=
        (Nat.card_eq_fintype_card :
          Nat.card (A → K) = Fintype.card (A → K)).symm
      _ = Nat.card K ^ Nat.card A := Nat.card_fun
      _ = Fintype.card K ^ Fintype.card A := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcardLocal :
      Fintype.card (S → K) = Fintype.card K ^ S.card := by
    calc
      Fintype.card (S → K) = Nat.card (S → K) :=
        (Nat.card_eq_fintype_card :
          Nat.card (S → K) = Fintype.card (S → K)).symm
      _ = Nat.card K ^ Nat.card S := Nat.card_fun
      _ = Fintype.card K ^ S.card := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_coe S ▸ rfl
  have hK : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  unfold finiteAverage
  rw [hsumReal]
  rw [hcardFull, hcardLocal]
  push_cast
  have hpowReal :
      (Fintype.card K : ℝ) ^ S.card *
          (Fintype.card K : ℝ) ^ (Fintype.card A - S.card) =
        (Fintype.card K : ℝ) ^ Fintype.card A := by
    exact_mod_cast hpow
  rw [← hpowReal]
  field_simp [hK]

/-- The normalized cardinality of a cylinder event is the normalized
cardinality of its restriction to the relevant coordinates. -/
lemma eventRatio_eq_of_restriction
    {A K : Type*} [Fintype A] [Fintype K] [Nonempty K]
    (S : Finset A) [Fintype (A → K)] [Fintype (S → K)]
    (P : (S → K) → Prop) (E : Set (A → K))
    (hE : ∀ f, f ∈ E ↔ P (fun x : S ↦ f x.1)) :
    (E.ncard : ℝ) / Fintype.card (A → K) =
      (Set.ncard {g : S → K | P g} : ℝ) /
        Fintype.card (S → K) := by
  classical
  have hcard := card_eventFinset_eq_mul_of_restriction S P E hE
  have hS : S.card ≤ Fintype.card A := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hpow :
      Fintype.card K ^ S.card *
          Fintype.card K ^ (Fintype.card A - S.card) =
        Fintype.card K ^ Fintype.card A := by
    rw [← pow_add]
    congr 1
    omega
  have hcardFull :
      Fintype.card (A → K) = Fintype.card K ^ Fintype.card A := by
    calc
      Fintype.card (A → K) = Nat.card (A → K) :=
        (Nat.card_eq_fintype_card :
          Nat.card (A → K) = Fintype.card (A → K)).symm
      _ = Nat.card K ^ Nat.card A := Nat.card_fun
      _ = Fintype.card K ^ Fintype.card A := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcardLocal :
      Fintype.card (S → K) = Fintype.card K ^ S.card := by
    calc
      Fintype.card (S → K) = Nat.card (S → K) :=
        (Nat.card_eq_fintype_card :
          Nat.card (S → K) = Fintype.card (S → K)).symm
      _ = Nat.card K ^ Nat.card S := Nat.card_fun
      _ = Fintype.card K ^ S.card := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_coe S ▸ rfl
  have hK : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  rw [hcard, hcardFull, hcardLocal]
  push_cast
  have hpowReal :
      (Fintype.card K : ℝ) ^ S.card *
          (Fintype.card K : ℝ) ^ (Fintype.card A - S.card) =
        (Fintype.card K : ℝ) ^ Fintype.card A := by
    exact_mod_cast hpow
  rw [← hpowReal]
  field_simp [hK]

/-- Reindexing a finite sample space preserves the cardinality of every
predicate-defined event. -/
lemma ncard_setOf_comp_equiv
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    Set.ncard {a : A | P (e a)} = Set.ncard {b : B | P b} := by
  classical
  let restrictedEquiv : {a : A // P (e a)} ≃ {b : B // P b} := {
    toFun a := ⟨e a.1, a.2⟩
    invFun b := ⟨e.symm b.1, by simpa using b.2⟩
    left_inv a := by ext; simp
    right_inv b := by ext; simp
  }
  calc
    Set.ncard {a : A | P (e a)} = Fintype.card {a : A // P (e a)} :=
      (Set.fintypeCard_eq_ncard _).symm
    _ = Fintype.card {b : B // P b} := Fintype.card_congr restrictedEquiv
    _ = Set.ncard {b : B | P b} := Set.fintypeCard_eq_ncard _

/-- Uniform finite averages are invariant under a reindexing equivalence. -/
lemma finiteAverage_comp_equiv
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : B → ℝ) :
    finiteAverage (fun a ↦ f (e a)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

/-- Exact mixed cylinder count.  Prescribing one color at two distinct
coordinates and forbidding that color on a disjoint finite coordinate set
leaves `(C-1)^|S| * C^(|A|-|S|-2)` assignments.  This is the counting core of
the Molloy--Reed retained-pair expectation estimate. -/
lemma card_fun_eq_two_avoid_finset {A : Type*} [Fintype A]
    {C : ℕ} (a : Fin C) (S : Finset A) {p q : A}
    (hpq : p ≠ q) (hpS : p ∉ S) (hqS : q ∉ S) :
    Nat.card {f : A → Fin C //
      f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} =
      (C - 1) ^ S.card * C ^ (Fintype.card A - S.card - 2) := by
  classical
  let B := {b : Fin C // b ≠ a}
  let T : Finset A := insert p (insert q S)
  let R := {x : A // x ∉ T}
  let mixedEquiv :
      {f : A → Fin C // f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} ≃
        (S → B) × (R → Fin C) := {
    toFun f :=
      (fun x ↦ ⟨f.1 x.1, f.2.2.2 x.1 x.2⟩,
        fun x ↦ f.1 x.1)
    invFun g :=
      ⟨fun x ↦
        if hxp : x = p then a
        else if hxq : x = q then a
        else if hxS : x ∈ S then g.1 ⟨x, hxS⟩
        else g.2 ⟨x, by simp [T, hxp, hxq, hxS]⟩,
       by
        constructor
        · simp [hpq]
        constructor
        · simp [hpq]
        · intro x hxS
          have hxp : x ≠ p := by
            intro h
            subst x
            exact hpS hxS
          have hxq : x ≠ q := by
            intro h
            subst x
            exact hqS hxS
          simp only [hxp, hxq, hxS, ↓reduceIte]
          exact (g.1 ⟨x, hxS⟩).2⟩
    left_inv f := by
      apply Subtype.ext
      funext x
      by_cases hxp : x = p
      · subst x
        simp [hpq, f.2.1]
      by_cases hxq : x = q
      · subst x
        simp [hpq, f.2.2.1]
      by_cases hxS : x ∈ S
      · simp [hxp, hxq, hxS]
      · simp [hxp, hxq, hxS]
    right_inv g := by
      apply Prod.ext
      · funext x
        apply Subtype.ext
        have hxp : x.1 ≠ p := by
          intro h
          exact hpS (by simpa [h] using x.2)
        have hxq : x.1 ≠ q := by
          intro h
          exact hqS (by simpa [h] using x.2)
        simp [hxp, hxq, x.2]
      · funext x
        have hxp : x.1 ≠ p := by
          intro h
          exact x.2 (by simp [T, h])
        have hxq : x.1 ≠ q := by
          intro h
          exact x.2 (by simp [T, h])
        have hxS : x.1 ∉ S := by
          intro hx
          exact x.2 (by simp [T, hx])
        simp [hxp, hxq, hxS]
  }
  have hBcard : Fintype.card B = C - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun b : Fin C ↦ b = a)]
    simp
  have hTcard : T.card = S.card + 2 := by
    dsimp only [T]
    have hpnot : p ∉ insert q S := by simp [hpq, hpS]
    rw [Finset.card_insert_of_notMem hpnot,
      Finset.card_insert_of_notMem hqS]
  have hRcard : Fintype.card R = Fintype.card A - S.card - 2 := by
    dsimp only [R]
    rw [Fintype.card_subtype_compl (fun x : A ↦ x ∈ T)]
    have hmem : Fintype.card {x : A // x ∈ T} = T.card := by
      simpa using Fintype.card_coe T
    rw [hmem, hTcard]
    omega
  calc
    Nat.card {f : A → Fin C //
        f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} =
        Nat.card ((S → B) × (R → Fin C)) := Nat.card_congr mixedEquiv
    _ = (Fintype.card B) ^ Fintype.card S *
        C ^ Fintype.card R := by simp [Nat.card_eq_fintype_card]
    _ = (C - 1) ^ S.card *
        C ^ (Fintype.card A - S.card - 2) := by
      rw [hBcard, hRcard, Fintype.card_coe]

/-- Type-generic two-coordinate avoidance cylinder count.  It is needed for
the diluted coloring round, whose one-coordinate sample consists of an
activation coin together with a tentative color. -/
lemma card_fun_eq_two_avoid_finset_generic
    {A K : Type*} [Fintype A] [Fintype K]
    (a : K) (S : Finset A) {p q : A}
    (hpq : p ≠ q) (hpS : p ∉ S) (hqS : q ∉ S) :
    Nat.card {f : A → K //
      f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} =
      (Fintype.card K - 1) ^ S.card *
        Fintype.card K ^ (Fintype.card A - S.card - 2) := by
  classical
  let B := {b : K // b ≠ a}
  let T : Finset A := insert p (insert q S)
  let R := {x : A // x ∉ T}
  let mixedEquiv :
      {f : A → K // f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} ≃
        (S → B) × (R → K) := {
    toFun f :=
      (fun x ↦ ⟨f.1 x.1, f.2.2.2 x.1 x.2⟩,
        fun x ↦ f.1 x.1)
    invFun g :=
      ⟨fun x ↦
        if hxp : x = p then a
        else if hxq : x = q then a
        else if hxS : x ∈ S then g.1 ⟨x, hxS⟩
        else g.2 ⟨x, by simp [T, hxp, hxq, hxS]⟩,
       by
        constructor
        · simp [hpq]
        constructor
        · simp [hpq]
        · intro x hxS
          have hxp : x ≠ p := by
            intro h
            subst x
            exact hpS hxS
          have hxq : x ≠ q := by
            intro h
            subst x
            exact hqS hxS
          simp only [hxp, hxq, hxS, ↓reduceIte]
          exact (g.1 ⟨x, hxS⟩).2⟩
    left_inv f := by
      apply Subtype.ext
      funext x
      by_cases hxp : x = p
      · subst x
        simp [hpq, f.2.1]
      by_cases hxq : x = q
      · subst x
        simp [hpq, f.2.2.1]
      by_cases hxS : x ∈ S
      · simp [hxp, hxq, hxS]
      · simp [hxp, hxq, hxS]
    right_inv g := by
      apply Prod.ext
      · funext x
        apply Subtype.ext
        have hxp : x.1 ≠ p := by
          intro h
          exact hpS (by simpa [h] using x.2)
        have hxq : x.1 ≠ q := by
          intro h
          exact hqS (by simpa [h] using x.2)
        simp [hxp, hxq, x.2]
      · funext x
        have hxp : x.1 ≠ p := by
          intro h
          exact x.2 (by simp [T, h])
        have hxq : x.1 ≠ q := by
          intro h
          exact x.2 (by simp [T, h])
        have hxS : x.1 ∉ S := by
          intro hx
          exact x.2 (by simp [T, hx])
        simp [hxp, hxq, hxS]
  }
  have hBcard : Fintype.card B = Fintype.card K - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun b : K ↦ b = a)]
    simp
  have hTcard : T.card = S.card + 2 := by
    dsimp only [T]
    have hpnot : p ∉ insert q S := by simp [hpq, hpS]
    rw [Finset.card_insert_of_notMem hpnot,
      Finset.card_insert_of_notMem hqS]
  have hRcard : Fintype.card R = Fintype.card A - S.card - 2 := by
    dsimp only [R]
    rw [Fintype.card_subtype_compl (fun x : A ↦ x ∈ T)]
    have hmem : Fintype.card {x : A // x ∈ T} = T.card := by
      simpa using Fintype.card_coe T
    rw [hmem, hTcard]
    omega
  calc
    Nat.card {f : A → K //
        f p = a ∧ f q = a ∧ ∀ x ∈ S, f x ≠ a} =
        Nat.card ((S → B) × (R → K)) := Nat.card_congr mixedEquiv
    _ = (Fintype.card B) ^ Fintype.card S *
        Fintype.card K ^ Fintype.card R := by
      simp [Nat.card_eq_fintype_card]
    _ = (Fintype.card K - 1) ^ S.card *
        Fintype.card K ^ (Fintype.card A - S.card - 2) := by
      rw [hBcard, hRcard, Fintype.card_coe]

/-- Enlarging the avoidance set can only decrease the normalized mixed
cylinder count, provided both prescribed coordinates remain outside it.  This
is the subtraction-safe arithmetic form needed to replace an actual support
size by a uniform upper bound. -/
lemma mixed_cylinder_count_anti_mono {C N s m : ℕ}
    (hsm : s ≤ m) (hmN : m + 2 ≤ N) :
    (C - 1) ^ m * C ^ (N - m - 2) ≤
      (C - 1) ^ s * C ^ (N - s - 2) := by
  have hm : m = s + (m - s) := by omega
  have hN : N - s - 2 = (N - m - 2) + (m - s) := by omega
  have hpowm : (C - 1) ^ m =
      (C - 1) ^ s * (C - 1) ^ (m - s) :=
    (congrArg (fun z ↦ (C - 1) ^ z) hm).trans (pow_add _ _ _)
  have hpowN : C ^ (N - s - 2) =
      C ^ (N - m - 2) * C ^ (m - s) := by rw [hN, pow_add]
  rw [hpowm, hpowN]
  calc
    ((C - 1) ^ s * (C - 1) ^ (m - s)) * C ^ (N - m - 2) =
        (C - 1) ^ s * C ^ (N - m - 2) * (C - 1) ^ (m - s) := by ring
    _ ≤ (C - 1) ^ s * C ^ (N - m - 2) * C ^ (m - s) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le C 1) _)
    _ = (C - 1) ^ s * (C ^ (N - m - 2) * C ^ (m - s)) := by ring

/-- Coordinate-cylinder count in an indexed form.  Along an injective map of
`I` coordinates into `A`, prescribing an arbitrary value at every indexed
coordinate leaves `|K| ^ (|A| - |I|)` assignments. -/
lemma card_fun_comp_eq_of_injective {A I K : Type*}
    [Fintype A] [Fintype I] [Fintype K]
    (e : I → A) (he : Function.Injective e) (g : I → K) :
    Nat.card {f : A → K // ∀ i, f (e i) = g i} =
      Fintype.card K ^ (Fintype.card A - Fintype.card I) := by
  classical
  let S : Finset A := Finset.univ.image e
  have hSCard : S.card = Fintype.card I := by
    dsimp only [S]
    rw [Finset.card_image_iff.mpr he.injOn]
    simp
  have exists_preimage (x : S) : ∃ i : I, e i = x.1 := by
    obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp x.2
    exact ⟨i, hix⟩
  let preimage (x : S) : I := Classical.choose (exists_preimage x)
  have preimage_spec (x : S) : e (preimage x) = x.1 :=
    Classical.choose_spec (exists_preimage x)
  let gS : S → K := fun x ↦ g (preimage x)
  let indexedCylinderEquiv :
      {f : A → K // ∀ i, f (e i) = g i} ≃
        {f : A → K // ∀ x : S, f x.1 = gS x} := {
    toFun f := ⟨f.1, by
      intro x
      rw [← preimage_spec x]
      exact f.2 (preimage x)⟩
    invFun f := ⟨f.1, by
      intro i
      have hei : e i ∈ S := by
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ _, rfl⟩
      let x : S := ⟨e i, hei⟩
      have hpre : preimage x = i := by
        apply he
        exact preimage_spec x
      simpa [gS, x, hpre] using f.2 x⟩
    left_inv f := rfl
    right_inv f := rfl
  }
  calc
    Nat.card {f : A → K // ∀ i, f (e i) = g i} =
        Nat.card {f : A → K // ∀ x : S, f x.1 = gS x} :=
      Nat.card_congr indexedCylinderEquiv
    _ = Fintype.card K ^ (Fintype.card A - S.card) :=
      card_fun_restrict_eq S gS
    _ = Fintype.card K ^ (Fintype.card A - Fintype.card I) := by rw [hSCard]

/-- A fixed pattern of `t` pairwise disjoint collisions in prescribed colors
has exactly `k ^ (|A| - 2t)` realizations in the assignment space
`A → Fin k`. -/
lemma card_fun_fixed_collision_pairs {A : Type*} [Fintype A]
    (k t : ℕ) (left right : Fin t → A)
    (hendpoints : Function.Injective (Sum.elim left right))
    (pairColor : Fin t → Fin k) :
    Nat.card {f : A → Fin k //
      ∀ i, f (left i) = pairColor i ∧ f (right i) = pairColor i} =
      k ^ (Fintype.card A - 2 * t) := by
  let endpoint : Fin t ⊕ Fin t → A := Sum.elim left right
  let prescribed : Fin t ⊕ Fin t → Fin k := Sum.elim pairColor pairColor
  let cylinderEquiv :
      {f : A → Fin k // ∀ i, f (left i) = pairColor i ∧
        f (right i) = pairColor i} ≃
      {f : A → Fin k // ∀ a, f (endpoint a) = prescribed a} := {
    toFun f := ⟨f.1, by
      intro a
      rcases a with i | i
      · exact (f.2 i).1
      · exact (f.2 i).2⟩
    invFun f := ⟨f.1, fun i ↦ ⟨f.2 (Sum.inl i), f.2 (Sum.inr i)⟩⟩
    left_inv f := rfl
    right_inv f := rfl
  }
  calc
    Nat.card {f : A → Fin k //
        ∀ i, f (left i) = pairColor i ∧ f (right i) = pairColor i} =
      Nat.card {f : A → Fin k // ∀ a, f (endpoint a) = prescribed a} :=
        Nat.card_congr cylinderEquiv
    _ = k ^ (Fintype.card A - Fintype.card (Fin t ⊕ Fin t)) :=
      by
        simpa using
          (card_fun_comp_eq_of_injective endpoint hendpoints prescribed)
    _ = k ^ (Fintype.card A - 2 * t) := by simp [two_mul]

/-- A fixed family of pairwise coordinate-disjoint triples, each prescribed
one particular color, has exactly `k ^ (|A| - 3|I|)` realizations.  This is
the cylinder count used for direct upper tails of the deletion variable. -/
lemma card_fun_fixed_collision_triples
    {A I : Type*} [Fintype A] [Fintype I]
    (k : ℕ) (first second third : I → A)
    (hendpoints : Function.Injective
      (Sum.elim first (Sum.elim second third) : I ⊕ (I ⊕ I) → A))
    (tripleColor : I → Fin k) :
    Nat.card {f : A → Fin k // ∀ i,
      f (first i) = tripleColor i ∧
      f (second i) = tripleColor i ∧
      f (third i) = tripleColor i} =
      k ^ (Fintype.card A - 3 * Fintype.card I) := by
  let endpoint : I ⊕ (I ⊕ I) → A :=
    Sum.elim first (Sum.elim second third)
  let prescribed : I ⊕ (I ⊕ I) → Fin k :=
    Sum.elim tripleColor (Sum.elim tripleColor tripleColor)
  let cylinderEquiv :
      {f : A → Fin k // ∀ i,
        f (first i) = tripleColor i ∧
        f (second i) = tripleColor i ∧
        f (third i) = tripleColor i} ≃
      {f : A → Fin k // ∀ a, f (endpoint a) = prescribed a} := {
    toFun f := ⟨f.1, by
      intro a
      rcases a with i | i
      · exact (f.2 i).1
      · rcases i with i | i
        · exact (f.2 i).2.1
        · exact (f.2 i).2.2⟩
    invFun f := ⟨f.1, fun i ↦
      ⟨f.2 (Sum.inl i), f.2 (Sum.inr (Sum.inl i)),
        f.2 (Sum.inr (Sum.inr i))⟩⟩
    left_inv f := rfl
    right_inv f := rfl
  }
  calc
    Nat.card {f : A → Fin k // ∀ i,
        f (first i) = tripleColor i ∧
        f (second i) = tripleColor i ∧
        f (third i) = tripleColor i} =
        Nat.card {f : A → Fin k //
          ∀ a, f (endpoint a) = prescribed a} :=
      Nat.card_congr cylinderEquiv
    _ = k ^ (Fintype.card A - Fintype.card (I ⊕ (I ⊕ I))) := by
      simpa [endpoint] using
        (card_fun_comp_eq_of_injective endpoint hendpoints prescribed)
    _ = k ^ (Fintype.card A - 3 * Fintype.card I) := by
      congr 2
      simp
      ring

/-- Restricting a finite map to a subset cannot increase the loss
`|domain| - |range|`.  This elementary deficiency monotonicity is the
cardinality bridge used to turn explicit same-colour pairs into a lower bound
on the palette saving of a partial colouring. -/
lemma finset_card_sub_range_card_ge {A B : Type*} [Fintype A]
    [DecidableEq B]
    (f : A → B) (P : Finset A) :
    P.card - (P.image f).card ≤
      Fintype.card A - Nat.card (Set.range f) := by
  classical
  let Q : Finset A := Finset.univ \ P
  have hpartition : P ∪ Q = Finset.univ := by
    ext a
    simp [Q]
  have hdisjoint : Disjoint P Q := by
    exact Finset.disjoint_sdiff
  have hdomain : Fintype.card A = P.card + Q.card := by
    rw [← Finset.card_univ, ← hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hrange : Nat.card (Set.range f) = (Finset.univ.image f).card := by
    calc
      Nat.card (Set.range f) = (Set.range f).ncard :=
        by
          rw [Nat.card_eq_fintype_card]
          exact Set.fintypeCard_eq_ncard _
      _ = (Finset.univ.image f).card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext b
        simp
  have himage : Finset.univ.image f = P.image f ∪ Q.image f := by
    rw [← Finset.image_union, hpartition]
  have hrange_le : Nat.card (Set.range f) ≤ (P.image f).card + Q.card := by
    rw [hrange, himage]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_image_le _)
  omega

/-- If a finite map identifies `t` disjoint pairs and the resulting `t`
values are distinct, then its domain exceeds its range by at least `t`.
This is the exact finite certificate underlying the repeated-neighbour-colour
saving in the locally sparse graph-colouring step. -/
lemma card_sub_range_card_ge_of_disjoint_collision_pairs
    {A B : Type*} [Fintype A] (f : A → B) (t : ℕ)
    (left right : Fin t → A)
    (hendpoints : Function.Injective (Sum.elim left right))
    (hcollision : ∀ i, f (left i) = f (right i))
    (hcolors : Function.Injective (fun i ↦ f (left i))) :
    t ≤ Fintype.card A - Nat.card (Set.range f) := by
  classical
  let endpoint : Fin t ⊕ Fin t → A := Sum.elim left right
  let P : Finset A := Finset.univ.image endpoint
  have hPcard : P.card = 2 * t := by
    dsimp only [P]
    rw [Finset.card_image_iff.mpr hendpoints.injOn]
    simp [two_mul]
  have hPimage : P.image f = Finset.univ.image (fun i ↦ f (left i)) := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp haP
      rcases i with i | i
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by
          simpa [endpoint] using congrArg f hi⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by
          have hfi := hcollision i
          dsimp only [endpoint] at hi
          rw [← hi]
          exact hfi⟩
    · intro hb
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hb
      apply Finset.mem_image.mpr
      refine ⟨left i, ?_, rfl⟩
      apply Finset.mem_image.mpr
      exact ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
  have hPimageCard : (P.image f).card = t := by
    rw [hPimage, Finset.card_image_iff.mpr hcolors.injOn]
    simp
  have hdef := finset_card_sub_range_card_ge f P
  rw [hPcard, hPimageCard] at hdef
  omega

/-- Finite bipartite incidence double counting.  A lower degree `q` on the
right and an upper degree `k` on the left imply `|T|q ≤ |S|k`. -/
lemma finset_card_mul_le_of_bipartite_degrees {A B : Type*}
    (S : Finset A) (T : Finset B) (R : A → B → Prop) [DecidableRel R]
    (q k : ℕ)
    (hleft : ∀ b ∈ T, q ≤ (S.filter fun a ↦ R a b).card)
    (hright : ∀ a ∈ S, (T.filter fun b ↦ R a b).card ≤ k) :
    T.card * q ≤ S.card * k := by
  classical
  calc
    T.card * q = ∑ _b ∈ T, q := by simp
    _ ≤ ∑ b ∈ T, (S.filter fun a ↦ R a b).card := by
      apply Finset.sum_le_sum
      intro b hb
      exact hleft b hb
    _ = ∑ b ∈ T, ∑ a ∈ S, if R a b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ = ∑ a ∈ S, ∑ b ∈ T, if R a b then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ S, (T.filter fun b ↦ R a b).card := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ ≤ ∑ _a ∈ S, k := by
      apply Finset.sum_le_sum
      intro a ha
      exact hright a ha
    _ = S.card * k := by simp

/-! ## Generic finite matching utilities -/

/-- Every finite simple graph has a matching of maximum cardinality. -/
lemma exists_maximum_matching {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  let matchings : Finset G.Subgraph :=
    Finset.univ.filter SimpleGraph.Subgraph.IsMatching
  have hbottom : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  have hnonempty : matchings.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [matchings, hbottom]
  obtain ⟨M, hMmem, hmax⟩ :=
    Finset.exists_max_image matchings (fun N ↦ N.edgeSet.ncard) hnonempty
  refine ⟨M, (Finset.mem_filter.mp hMmem).2, ?_⟩
  intro N hN
  exact hmax N (by simp [matchings, hN])

/-- Choose and orient any prescribed number of edges from a graph matching.
All chosen endpoints are distinct. -/
lemma exists_injective_endpoints_of_matching {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) {t : ℕ}
    (ht : t ≤ M.edgeSet.ncard) :
    ∃ left right : Fin t → V,
      Function.Injective (Sum.elim left right) ∧
        ∀ i, G.Adj (left i) (right i) := by
  classical
  let _ : Fintype M.edgeSet := Fintype.ofFinite M.edgeSet
  have hcard : Fintype.card (Fin t) ≤ Fintype.card M.edgeSet := by
    simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using ht
  obtain ⟨pick : Fin t ↪ M.edgeSet⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  let left (i : Fin t) : V := (pick i).1.out.1
  let right (i : Fin t) : V := (pick i).1.out.2
  have hadjM (i : Fin t) : M.Adj (left i) (right i) := by
    apply SimpleGraph.Subgraph.mem_edgeSet.mp
    change s((pick i).1.out.1, (pick i).1.out.2) ∈ M.edgeSet
    have hout : s((pick i).1.out.1, (pick i).1.out.2) = (pick i).1 :=
      (pick i).1.out_eq
    exact hout.symm ▸ (pick i).2
  have htoLeft (i : Fin t) :
      hM.toEdge ⟨left i, (hadjM i).fst_mem⟩ = pick i := by
    rw [hM.toEdge_eq_of_adj (hadjM i)]
    apply Subtype.ext
    change s((pick i).1.out.1, (pick i).1.out.2) = (pick i).1
    exact (pick i).1.out_eq
  have htoRight (i : Fin t) :
      hM.toEdge ⟨right i, (hadjM i).snd_mem⟩ = pick i := by
    rw [hM.toEdge_eq_of_adj (hadjM i).symm]
    apply Subtype.ext
    change s((pick i).1.out.2, (pick i).1.out.1) = (pick i).1
    rw [Sym2.eq_swap]
    exact (pick i).1.out_eq
  have hendpoints : Function.Injective (Sum.elim left right) := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · have hpick : pick i = pick j := by
        rw [← htoLeft i, ← htoLeft j]
        congr 1
        exact Subtype.ext hab
      exact congrArg Sum.inl (pick.injective hpick)
    · have hpick : pick i = pick j := by
        rw [← htoLeft i, ← htoRight j]
        congr 1
        exact Subtype.ext hab
      have hij := pick.injective hpick
      subst j
      exact ((hadjM i).ne hab).elim
    · have hpick : pick i = pick j := by
        rw [← htoRight i, ← htoLeft j]
        congr 1
        exact Subtype.ext hab
      have hij := pick.injective hpick
      subst j
      exact ((hadjM i).ne hab.symm).elim
    · have hpick : pick i = pick j := by
        rw [← htoRight i, ← htoRight j]
        congr 1
        exact Subtype.ext hab
      exact congrArg Sum.inr (pick.injective hpick)
  exact ⟨left, right, hendpoints, fun i ↦ M.adj_sub (hadjM i)⟩

/-- A finite graph matching has exactly twice as many incident vertices as
edges. -/
lemma matching_verts_ncard_generic {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  let _ : Fintype M.verts := Fintype.ofFinite M.verts
  let _ : Fintype M.edgeSet := Fintype.ofFinite M.edgeSet
  have hfiber (y : M.edgeSet) :
      ((Finset.univ : Finset M.verts).filter (fun x ↦ hM.toEdge x = y)).card = 2 := by
    rcases y with ⟨⟨u, v⟩, huv⟩
    have hadj : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp huv
    have hpre := hM.toEdge_preimage_singleton hadj
    have hfilter :
        (Finset.univ : Finset M.verts).filter
            (fun x ↦ hM.toEdge x = ⟨s(u, v), huv⟩) =
          {⟨u, hadj.fst_mem⟩, ⟨v, hadj.snd_mem⟩} := by
      ext w
      have hw := Set.ext_iff.mp hpre w
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_insert_iff] using hw
    rw [hfilter]
    simp [Subtype.ext_iff, hadj.ne]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset M.verts))
    (t := (Finset.univ : Finset M.edgeSet))
    (f := hM.toEdge) (fun _ _ ↦ Finset.mem_univ _)
  calc
    M.verts.ncard = Fintype.card M.verts := (Set.fintypeCard_eq_ncard _).symm
    _ = (Finset.univ : Finset M.verts).card := by simp
    _ = ∑ y ∈ (Finset.univ : Finset M.edgeSet),
        ((Finset.univ : Finset M.verts).filter (fun x ↦ hM.toEdge x = y)).card := hsum
    _ = ∑ _y ∈ (Finset.univ : Finset M.edgeSet), 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact hfiber y
    _ = 2 * Fintype.card M.edgeSet := by simp [Nat.mul_comm]
    _ = 2 * M.edgeSet.ncard := by rw [Set.fintypeCard_eq_ncard]

/-- The uncovered vertices of a maximum matching form an independent set. -/
lemma maximum_matching_unmatched_pairwise_not_adj {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.vertsᶜ.Pairwise fun v w ↦ ¬ G.Adj v w := by
  classical
  intro v hv w hw hvw hadj
  let P := G.subgraphOfAdj hadj
  have hP : P.IsMatching := SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hadj
  have hsupports : Disjoint M.support P.support := by
    rw [hM.support_eq_verts, show P.support = {v, w} by
      simpa [P] using SimpleGraph.Subgraph.support_subgraphOfAdj hadj]
    rw [Set.disjoint_left]
    intro x hxM hxpair
    rcases hxpair with (rfl | rfl)
    · exact hv hxM
    · exact hw hxM
  let N := M ⊔ P
  have hN : N.IsMatching := hM.sup hP hsupports
  have hnew : s(v, w) ∉ M.edgeSet := by
    intro hedge
    have hMadj : M.Adj v w := SimpleGraph.Subgraph.mem_edgeSet.mp hedge
    exact hv (M.edge_vert hMadj)
  have hNcard : N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    rw [show N.edgeSet = M.edgeSet ∪ P.edgeSet from
      SimpleGraph.Subgraph.edgeSet_sup]
    rw [show P.edgeSet = {s(v, w)} by
      simpa [P] using SimpleGraph.Subgraph.edgeSet_subgraphOfAdj hadj]
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hnew]
  have := hmax N hN
  omega

/-- A maximum matching in a finite graph with maximum degree `D` contains
enough edges to cover the graph's edge set: every graph edge has an endpoint
covered by the matching, and the incidence sets of the covered vertices have
total size at most `2 |M| D`. -/
lemma card_edgeFinset_le_two_mul_maximumMatching_mul_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching →
      N.edgeSet.ncard ≤ M.edgeSet.ncard)
    (D : ℕ) (hdegree : ∀ v, (G.neighborSet v).ncard ≤ D) :
    G.edgeSet.ncard ≤ 2 * M.edgeSet.ncard * D := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI (v : V) : Fintype (G.neighborSet v) := Fintype.ofFinite _
  let covered : Finset V := M.verts.toFinset
  have hunmatched := maximum_matching_unmatched_pairwise_not_adj M hM hmax
  have hcover : G.edgeFinset ⊆
      covered.biUnion (fun v ↦ G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj : G.Adj u v := by
          exact G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)
        by_cases hu : u ∈ M.verts
        · apply Finset.mem_biUnion.mpr
          refine ⟨u, Set.mem_toFinset.mpr hu, ?_⟩
          rw [G.mem_incidenceFinset]
          exact G.mk'_mem_incidenceSet_left_iff.mpr hadj
        · have hv : v ∈ M.verts := by
            by_contra hv
            have hnot := hunmatched (by simpa) (by simpa) hadj.ne hadj
            exact hnot
          apply Finset.mem_biUnion.mpr
          refine ⟨v, Set.mem_toFinset.mpr hv, ?_⟩
          rw [G.mem_incidenceFinset]
          exact G.mk'_mem_incidenceSet_right_iff.mpr hadj
  have hcoveredCard : covered.card = 2 * M.edgeSet.ncard := by
    dsimp only [covered]
    rw [← Set.ncard_eq_toFinset_card', matching_verts_ncard_generic M hM]
  have hedgeCard : G.edgeSet.ncard = G.edgeFinset.card := by
    calc
      G.edgeSet.ncard = Fintype.card G.edgeSet :=
        (Set.fintypeCard_eq_ncard _).symm
      _ = G.edgeFinset.card := G.card_edgeSet
  have hincidenceCard (v : V) :
      (G.incidenceFinset v).card = (G.neighborSet v).ncard := by
    calc
      (G.incidenceFinset v).card = G.degree v :=
        G.card_incidenceFinset_eq_degree v
      _ = Fintype.card (G.neighborSet v) :=
        (G.card_neighborSet_eq_degree v).symm
      _ = (G.neighborSet v).ncard := Set.fintypeCard_eq_ncard _
  rw [hedgeCard]
  calc
    G.edgeFinset.card ≤
        (covered.biUnion (fun v ↦ G.incidenceFinset v)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ v ∈ covered, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ covered, (G.neighborSet v).ncard := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hincidenceCard v
    _ ≤ ∑ _v ∈ covered, D := by
      apply Finset.sum_le_sum
      intro v _hv
      exact hdegree v
    _ = covered.card * D := by simp
    _ = 2 * M.edgeSet.ncard * D := by rw [hcoveredCard]

/-- Cardinal form of the elementary maximal-matching lower bound.  If a
finite graph of maximum degree `D` has at least `2 t D` edges, it contains a
matching of size at least `t`. -/
lemma exists_matching_of_two_mul_mul_le_edgeSet_ncard
    {V : Type*} [Fintype V] (G : SimpleGraph V) (t D : ℕ)
    (hD : 0 < D)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ D)
    (hedges : 2 * t * D ≤ G.edgeSet.ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ t ≤ M.edgeSet.ncard := by
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching G
  refine ⟨M, hM, ?_⟩
  have hcover :=
    card_edgeFinset_le_two_mul_maximumMatching_mul_degree G M hM hmax D hdegree
  have hmul : (2 * t) * D ≤ (2 * M.edgeSet.ncard) * D :=
    hedges.trans hcover
  have htwo : 2 * t ≤ 2 * M.edgeSet.ncard :=
    Nat.le_of_mul_le_mul_right hmul hD
  exact Nat.le_of_mul_le_mul_left htwo (by norm_num : 0 < 2)

/-- A graph whose complement has at least `2t|V|` edges has `t` disjoint
nonedges.  This supplies the endpoint-disjoint part of the collision
certificate in a sparse neighborhood. -/
lemma exists_disjoint_nonedge_pairs_of_compl_edge_count
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) (t : ℕ)
    (hedges : 2 * t * Fintype.card V ≤ Gᶜ.edgeSet.ncard) :
    ∃ left right : Fin t → V,
      Function.Injective (Sum.elim left right) ∧
        ∀ i, left i ≠ right i ∧ ¬G.Adj (left i) (right i) := by
  have hdegree : ∀ v, (Gᶜ.neighborSet v).ncard ≤ Fintype.card V := by
    intro v
    calc
      (Gᶜ.neighborSet v).ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = Fintype.card V := by simp
  obtain ⟨M, hM, hMcard⟩ :=
    exists_matching_of_two_mul_mul_le_edgeSet_ncard Gᶜ t (Fintype.card V)
      Fintype.card_pos hdegree hedges
  obtain ⟨left, right, hinjective, hadj⟩ :=
    exists_injective_endpoints_of_matching M hM hMcard
  refine ⟨left, right, hinjective, fun i ↦ ?_⟩
  simpa only [SimpleGraph.compl_adj] using hadj i

/-- The edges and nonedges of a finite simple graph partition all unordered
pairs of distinct vertices. -/
lemma edgeSet_ncard_add_compl_edgeSet_ncard {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    G.edgeSet.ncard + Gᶜ.edgeSet.ncard = (Fintype.card V).choose 2 := by
  classical
  have hdisjoint : Disjoint G.edgeSet Gᶜ.edgeSet := by
    rw [SimpleGraph.disjoint_edgeSet]
    exact disjoint_compl_right
  have hunion : G.edgeSet ∪ Gᶜ.edgeSet = (⊤ : SimpleGraph V).edgeSet := by
    rw [← SimpleGraph.edgeSet_sup, sup_compl_eq_top]
  calc
    G.edgeSet.ncard + Gᶜ.edgeSet.ncard =
        (G.edgeSet ∪ Gᶜ.edgeSet).ncard :=
      (Set.ncard_union_eq hdisjoint).symm
    _ = (⊤ : SimpleGraph V).edgeSet.ncard := by rw [hunion]
    _ = (⊤ : SimpleGraph V).edgeFinset.card := by
      calc
        (⊤ : SimpleGraph V).edgeSet.ncard =
            Fintype.card (⊤ : SimpleGraph V).edgeSet :=
          (Set.fintypeCard_eq_ncard _).symm
        _ = (⊤ : SimpleGraph V).edgeFinset.card :=
          SimpleGraph.card_edgeSet
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

/-! ## The projective-plane scale -/

lemma exists_projectiveScale (n : ℕ) : ∃ k : ℕ, n ≤ k * k + k + 1 := by
  refine ⟨n, ?_⟩
  omega

/-- The least `k` for which `n ≤ k²+k+1`, chosen explicitly rather than
using the paper's informal `k ≈ √n` notation. -/
noncomputable def projectiveScale (n : ℕ) : ℕ :=
  Nat.find (exists_projectiveScale n)

lemma le_projectiveScale_sq_add (n : ℕ) :
    n ≤ projectiveScale n * projectiveScale n + projectiveScale n + 1 :=
  Nat.find_spec (exists_projectiveScale n)

lemma projectiveScale_pos {n : ℕ} (hn : 2 ≤ n) : 0 < projectiveScale n := by
  have hupper := le_projectiveScale_sq_add n
  by_contra h
  have hk : projectiveScale n = 0 := Nat.eq_zero_of_not_pos h
  rw [hk] at hupper
  omega

/-- Minimality gives the exact predecessor quadratic lower bound.  For
positive `k` this is the paper's `k²-k+2 ≤ n`, written without truncated
subtraction. -/
lemma projectiveScale_pred_sq_add_le {n : ℕ} (hn : 2 ≤ n) :
    (projectiveScale n - 1) * (projectiveScale n - 1) +
        (projectiveScale n - 1) + 2 ≤ n := by
  have hklt : projectiveScale n - 1 < projectiveScale n := by
    have := projectiveScale_pos hn
    omega
  have hminimal := Nat.find_min (exists_projectiveScale n) hklt
  omega

lemma sqrt_le_projectiveScale_add_one (n : ℕ) :
    n.sqrt ≤ projectiveScale n + 1 := by
  have hsq : n ≤ (projectiveScale n + 1) * (projectiveScale n + 1) := by
    calc
      n ≤ projectiveScale n * projectiveScale n + projectiveScale n + 1 :=
        le_projectiveScale_sq_add n
      _ ≤ (projectiveScale n + 1) * (projectiveScale n + 1) := by
        simp only [Nat.add_mul, Nat.mul_add]
        omega
  calc
    n.sqrt ≤ ((projectiveScale n + 1) * (projectiveScale n + 1)).sqrt :=
      Nat.sqrt_le_sqrt hsq
    _ = projectiveScale n + 1 := Nat.sqrt_eq _

lemma projectiveScale_le_sqrt_add_one {n : ℕ} (hn : 2 ≤ n) :
    projectiveScale n ≤ n.sqrt + 1 := by
  have hpredsq :
      (projectiveScale n - 1) * (projectiveScale n - 1) ≤ n :=
    calc
      (projectiveScale n - 1) * (projectiveScale n - 1) ≤
          (projectiveScale n - 1) * (projectiveScale n - 1) +
            (projectiveScale n - 1) + 2 := by omega
      _ ≤ n := projectiveScale_pred_sq_add_le hn
  have hpred : projectiveScale n - 1 ≤ n.sqrt := Nat.le_sqrt.mpr hpredsq
  have hkpos := projectiveScale_pos hn
  omega

lemma two_le_projectiveScale {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ projectiveScale n := by
  have hkpos := projectiveScale_pos (n := n) (by omega)
  have hupper := le_projectiveScale_sq_add n
  by_contra h
  have hk : projectiveScale n = 1 := by omega
  simp [hk] at hupper
  omega

/-- The numerical estimate in case (i) of Proposition 5.5, expressed with an
integral lower edge-size parameter `r`.  The hypothesis
`k+1 ≤ 2(r-1)` is a convenient exact consequence of `r = (1-o(1))√n`
and `k = √n+O(1)`. -/
lemma projectiveScale_case_one_arith {n r : ℕ} (hn : 4 ≤ n)
    (hr : projectiveScale n + 1 ≤ 2 * (r - 1)) :
    (projectiveScale n - 1) * (projectiveScale n - 2) +
        (n - 1) / (r - 1) - 2 ≤ n - 2 := by
  let k := projectiveScale n
  have hk2 : 2 ≤ k := two_le_projectiveScale hn
  have hnupper : n - 1 ≤ k * k + k := by
    have h := le_projectiveScale_sq_add n
    dsimp only [k]
    omega
  have hquotient : (n - 1) / (r - 1) ≤ 2 * k := by
    apply Nat.div_le_of_le_mul
    calc
      n - 1 ≤ k * k + k := hnupper
      _ = k * (k + 1) := by ring
      _ ≤ k * (2 * (r - 1)) := by
        exact Nat.mul_le_mul_left k (by simpa [k] using hr)
      _ = (r - 1) * (2 * k) := by ring
  have hidentity :
      (k - 1) * (k - 2) + 2 * k =
        (k - 1) * (k - 1) + (k - 1) + 2 := by
    let j := k - 2
    have hkj : k = j + 2 := by
      dsimp only [j]
      omega
    rw [hkj]
    simp
    ring
  have htotal : (k - 1) * (k - 2) + (n - 1) / (r - 1) ≤ n := by
    calc
      (k - 1) * (k - 2) + (n - 1) / (r - 1) ≤
          (k - 1) * (k - 2) + 2 * k :=
        Nat.add_le_add_left hquotient _
      _ = (k - 1) * (k - 1) + (k - 1) + 2 := hidentity
      _ ≤ n := projectiveScale_pred_sq_add_le (by omega)
  exact Nat.sub_le_sub_right htotal 2

/-- The natural-number calculation behind Proposition 5.5(ii).  The first
inequality is the two-tier incidence budget.  The second is the exact integral
form of the paper's estimates `m ≤ 1/(3δ)` and
`r ≥ (1-δ)√n`: it says that the loss caused by the `m` small incident edges
fits inside the available projective-plane slack. -/
lemma two_tier_degree_arith {n r k q d m : ℕ}
    (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k)
    (hmle : m ≤ d) (hmq : m ≤ q)
    (hbudget : (d - m) * (k - 1) + m * (r - 1) ≤ n - 1)
    (hsq : (k - 1) * (k - 1) ≤ n)
    (hslack : n - 1 + q * (k - r) ≤
      (n - (k - 1) * (k - 1)) * (k - 1)) :
    (k - 1) * (k - 1) + d - 2 ≤ n - 2 := by
  have hkpos : 0 < k - 1 := by omega
  have hsplit : k - 1 = (r - 1) + (k - r) := by omega
  have hd : d = (d - m) + m := by omega
  have hdecomp :
      d * (k - 1) =
        ((d - m) * (k - 1) + m * (r - 1)) + m * (k - r) := by
    calc
      d * (k - 1) = ((d - m) + m) * (k - 1) := by rw [← hd]
      _ = (d - m) * (k - 1) + m * (k - 1) := by ring
      _ = (d - m) * (k - 1) + m * ((r - 1) + (k - r)) := by rw [← hsplit]
      _ = ((d - m) * (k - 1) + m * (r - 1)) + m * (k - r) := by ring
  have hdmul : d * (k - 1) ≤
      (n - (k - 1) * (k - 1)) * (k - 1) := by
    rw [hdecomp]
    calc
      ((d - m) * (k - 1) + m * (r - 1)) + m * (k - r) ≤
          (n - 1) + q * (k - r) :=
        Nat.add_le_add hbudget (Nat.mul_le_mul_right (k - r) hmq)
      _ ≤ (n - (k - 1) * (k - 1)) * (k - 1) := hslack
  have hdtarget : d ≤ n - (k - 1) * (k - 1) :=
    Nat.le_of_mul_le_mul_right hdmul hkpos
  have htotal : (k - 1) * (k - 1) + d ≤ n := by
    calc
      (k - 1) * (k - 1) + d ≤
          (k - 1) * (k - 1) + (n - (k - 1) * (k - 1)) :=
        Nat.add_le_add_left hdtarget _
      _ = n := Nat.add_sub_of_le hsq
  exact Nat.sub_le_sub_right htotal 2

/-- Minimality of the projective-plane scale supplies exactly `k-2` units of
slack in the two-tier degree estimate.  This subtraction-free proof is useful
because the paper writes the same calculation with real fractions. -/
lemma quadratic_slack {n k extra : ℕ} (hk : 2 ≤ k)
    (hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hextra : extra ≤ k - 2) :
    n - 1 + extra ≤ (n - (k - 1) * (k - 1)) * (k - 1) := by
  have hsq : (k - 1) * (k - 1) ≤ n := by omega
  let A := n - (k - 1) * (k - 1)
  have hn : n = (k - 1) * (k - 1) + A := by
    dsimp only [A]
    exact (Nat.add_sub_of_le hsq).symm
  have hA : k + 1 ≤ A := by
    rw [hn] at hlow
    omega
  have hcore :
      (k - 1) * (k - 1) + A - 1 + (k - 2) ≤ A * (k - 1) := by
    let j := k - 2
    have hkj : k = j + 2 := by
      dsimp only [j]
      omega
    rw [hkj] at hA ⊢
    have hj1 : j + 2 - 1 = j + 1 := by omega
    have hj0 : j + 2 - 2 = j := by omega
    rw [hj1, hj0]
    have hA' : j + 3 ≤ A := by omega
    let B := A - (j + 3)
    have hAB : A = B + (j + 3) := by
      dsimp only [B]
      omega
    rw [hAB]
    ring_nf
    omega
  calc
    n - 1 + extra ≤ n - 1 + (k - 2) := Nat.add_le_add_left hextra _
    _ = (k - 1) * (k - 1) + A - 1 + (k - 2) := by rw [hn]
    _ ≤ A * (k - 1) := hcore
    _ = (n - (k - 1) * (k - 1)) * (k - 1) := by rfl

lemma projectiveScale_case_two_slack {n r q : ℕ} (hn : 4 ≤ n)
    (hdefect : q * (projectiveScale n - r) ≤ projectiveScale n - 2) :
    n - 1 + q * (projectiveScale n - r) ≤
      (n - (projectiveScale n - 1) * (projectiveScale n - 1)) *
        (projectiveScale n - 1) :=
  quadratic_slack (two_le_projectiveScale hn)
    (projectiveScale_pred_sq_add_le (n := n) (by omega)) hdefect

/-- A subtraction-safe numerical certificate for the last branch of
Lemma 5.1 in the particularly useful integral regime where every edge has
size at least `k-1`.  The two divisions in the conclusion are exactly the
bad-vertex and heavy-edge bounds furnished by (5.11) and (5.12). -/
lemma near_projectiveScale_floor_density {n k a p t : ℕ}
    (hk : 4096 ≤ k)
    (hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hup : n ≤ k * k + k + 1)
    (ha : k - 1 ≤ a)
    (hnotBalance :
      (n - 1) * a < 4 *
        (a * (n - 1 - (k - 1) * (k - 2)) +
          p * (n - 1 - k * (k - 1))))
    (hsurplus :
      (n - 1) * t ≤
        a * (n - 1 - (k - 1) * (k - 2)) +
          p * (n - 1 - k * (k - 1))) :
    n <
      (p -
          ((a * (k - 1) / (k - 1)) * ((n - 1) / (k - 1)) /
            (k / 4)) -
          4 * (t - 1)) * (k + 1 - k / 4) := by
  have hkpos : 0 < k := by omega
  have hk1pos : 0 < k - 1 := by omega
  have hnpos : 0 < n := by omega
  have hR : (k - 1) * (k - 2) ≤ n - 1 := by
    have hprod : (k - 1) * (k - 2) ≤ (k - 1) * (k - 1) :=
      Nat.mul_le_mul_left (k - 1) (by omega)
    omega
  have hK : k * (k - 1) ≤ n - 1 := by
    have hkid : k * (k - 1) =
        (k - 1) * (k - 1) + (k - 1) := by
      let j := k - 1
      have hkj : k = j + 1 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hkid]
    omega
  let lossR := n - 1 - (k - 1) * (k - 2)
  let lossK := n - 1 - k * (k - 1)
  have hlossR : lossR ≤ 4 * k := by
    dsimp only [lossR]
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hk2 : 2 ≤ k := by omega
    have hid : (k - 1) * (k - 2) + (4 * k - 2) = k * k + k := by
      let j := k - 2
      have hkj : k = j + 2 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hj1 : j + 2 - 1 = j + 1 := by omega
      have hj2 : j + 2 - 2 = j := by omega
      rw [hj1, hj2]
      have hsub : 4 * (j + 2) - 2 = 4 * j + 6 := by omega
      rw [hsub]
      ring
    omega
  have hlossK : lossK ≤ 2 * k := by
    dsimp only [lossK]
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * (k - 1) + 2 * k = k * k + k := by
      let j := k - 1
      have hkj : k = j + 1 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    omega
  have hDlower : k * (k - 1) ≤ n - 1 := hK
  have hnotBalance' :
      (n - 1) * a < 4 * (a * lossR + p * lossK) := by
    simpa only [lossR, lossK] using hnotBalance
  have hright : 4 * (a * lossR + p * lossK) ≤
      k * (16 * a + 8 * p) := by
    calc
      4 * (a * lossR + p * lossK) ≤
          4 * (a * (4 * k) + p * (2 * k)) := by
        exact Nat.mul_le_mul_left 4
          (Nat.add_le_add (Nat.mul_le_mul_left a hlossR)
            (Nat.mul_le_mul_left p hlossK))
      _ = k * (16 * a + 8 * p) := by ring
  have hleft : k * ((k - 1) * a) ≤ (n - 1) * a := by
    calc
      k * ((k - 1) * a) = (k * (k - 1)) * a := by ring
      _ ≤ (n - 1) * a := Nat.mul_le_mul_right a hDlower
  have hcancel : (k - 1) * a < 16 * a + 8 * p := by
    have hmul : k * ((k - 1) * a) < k * (16 * a + 8 * p) :=
      hleft.trans_lt (hnotBalance'.trans_le hright)
    exact (Nat.mul_lt_mul_left hkpos).mp hmul
  have ha8 : 8 * a ≤ p := by
    have h80 : 80 * a ≤ (k - 1) * a := by
      exact Nat.mul_le_mul_right a (by omega)
    omega
  have hsurplus' :
      (n - 1) * t ≤ a * lossR + p * lossK := by
    simpa only [lossR, lossK] using hsurplus
  have hsurplusBound : (n - 1) * t ≤ 4 * k * a + 2 * k * p := by
    apply hsurplus'.trans
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.add_le_add (Nat.mul_le_mul_left a hlossR)
        (Nat.mul_le_mul_left p hlossK)
  have hforty : 40 * k ≤ n - 1 := by
    have h40k : 40 * k ≤ k * (k - 1) := by
      have : 40 ≤ k - 1 := by omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k this
    exact h40k.trans hDlower
  have ht16 : 16 * t ≤ p := by
    have hscaled : 16 * ((n - 1) * t) ≤
        16 * (4 * k * a + 2 * k * p) := Nat.mul_le_mul_left 16 hsurplusBound
    have hscaled' : 16 * ((n - 1) * t) ≤ 40 * k * p := by
      calc
        16 * ((n - 1) * t) ≤ 16 * (4 * k * a + 2 * k * p) := hscaled
        _ = 64 * k * a + 32 * k * p := by ring
        _ ≤ 8 * k * p + 32 * k * p := by
          have h := Nat.mul_le_mul_left (8 * k) ha8
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
        _ = 40 * k * p := by ring
    have hDp : 40 * k * p ≤ (n - 1) * p :=
      Nat.mul_le_mul_right p hforty
    have hmul : (16 * t) * (n - 1) ≤ p * (n - 1) := by
      calc
        (16 * t) * (n - 1) = 16 * ((n - 1) * t) := by ring
        _ ≤ 40 * k * p := hscaled'
        _ ≤ (n - 1) * p := hDp
        _ = p * (n - 1) := by ring
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  let s := k / 4
  have hs1024 : 1024 ≤ s := by
    dsimp only [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by omega)
  have hspos : 0 < s := by omega
  have hk_le_four_s_add : k ≤ 4 * s + 3 := by
    have hmod := Nat.mod_lt k (by norm_num : 0 < 4)
    have hdecomp := Nat.div_add_mod k 4
    dsimp only [s]
    omega
  have hdegree : (n - 1) / (k - 1) ≤ k + 3 := by
    apply Nat.div_le_of_le_mul
    have hpoly : n - 1 ≤ k * k + k := by omega
    calc
      n - 1 ≤ k * k + k := hpoly
      _ ≤ (k - 1) * (k + 3) := by
        have hid : k * k + k + (k - 3) = (k - 1) * (k + 3) := by
          let j := k - 3
          have hkj : k = j + 3 := by
            dsimp only [j]
            omega
          rw [hkj]
          have hj1 : j + 3 - 1 = j + 2 := by omega
          have hj3 : j + 3 - 3 = j := by omega
          rw [hj1, hj3]
          ring
        omega
  have hfive : k + 3 ≤ 5 * s := by omega
  have hbadExact : a * (k - 1) / (k - 1) = a := by
    simpa [Nat.mul_comm] using Nat.mul_div_right a hk1pos
  have hheavy :
      (a * (k - 1) / (k - 1)) * ((n - 1) / (k - 1)) / s ≤ 5 * a := by
    rw [hbadExact]
    apply Nat.div_le_of_le_mul
    calc
      a * ((n - 1) / (k - 1)) ≤ a * (k + 3) :=
        Nat.mul_le_mul_left a hdegree
      _ ≤ a * (5 * s) := Nat.mul_le_mul_left a hfive
      _ = s * (5 * a) := by ring
  let heavyBound :=
    (a * (k - 1) / (k - 1)) * ((n - 1) / (k - 1)) / s
  have hremoved8 : 8 * (heavyBound + 4 * (t - 1)) ≤ 7 * p := by
    have hh8 : 8 * heavyBound ≤ 5 * p := by
      calc
        8 * heavyBound ≤ 8 * (5 * a) := Nat.mul_le_mul_left 8 hheavy
        _ = 5 * (8 * a) := by ring
        _ ≤ 5 * p := Nat.mul_le_mul_left 5 ha8
    have ht32 : 32 * (t - 1) ≤ 2 * p := by
      have : 32 * (t - 1) ≤ 32 * t := Nat.mul_le_mul_left 32 (Nat.sub_le _ _)
      calc
        32 * (t - 1) ≤ 32 * t := this
        _ = 2 * (16 * t) := by ring
        _ ≤ 2 * p := Nat.mul_le_mul_left 2 ht16
    calc
      8 * (heavyBound + 4 * (t - 1)) =
          8 * heavyBound + 32 * (t - 1) := by ring
      _ ≤ 5 * p + 2 * p := Nat.add_le_add hh8 ht32
      _ = 7 * p := by ring
  let residual := p - heavyBound - 4 * (t - 1)
  have hresidual : p / 8 ≤ residual := by
    have hrem : heavyBound + 4 * (t - 1) ≤ p := by
      have hp7 : 7 * p ≤ 8 * p := by omega
      have h8 := hremoved8.trans hp7
      exact Nat.le_of_mul_le_mul_left h8 (by norm_num : 0 < 8)
    have hsum8 : 8 * (p / 8 + (heavyBound + 4 * (t - 1))) ≤ 8 * p := by
      calc
        8 * (p / 8 + (heavyBound + 4 * (t - 1))) =
            8 * (p / 8) + 8 * (heavyBound + 4 * (t - 1)) := by ring
        _ ≤ p + 7 * p :=
          Nat.add_le_add (Nat.mul_div_le p 8) hremoved8
        _ = 8 * p := by ring
    have hsum : p / 8 + (heavyBound + 4 * (t - 1)) ≤ p :=
      Nat.le_of_mul_le_mul_left hsum8 (by norm_num : 0 < 8)
    dsimp only [residual]
    omega
  have hrelation : (k - 17) * a < 8 * p := by
    have hid : (k - 1) * a = (k - 17) * a + 16 * a := by
      let j := k - 17
      have hkj : k = j + 17 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hsub1 : j + 17 - 1 = j + 16 := by omega
      have hsub17 : j + 17 - 17 = j := by omega
      rw [hsub1, hsub17]
      ring
    rw [hid] at hcancel
    omega
  have hksqP : k * k < 32 * p := by
    have hkhalf : k ≤ 2 * (k - 17) := by omega
    have hkA : k ≤ 2 * a := by omega
    have hprod : k * k ≤ 4 * ((k - 17) * a) := by
      calc
        k * k ≤ (2 * (k - 17)) * (2 * a) := Nat.mul_le_mul hkhalf hkA
        _ = 4 * ((k - 17) * a) := by ring
    have hfour : 4 * ((k - 17) * a) < 32 * p := by
      have h := (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hrelation
      calc
        4 * ((k - 17) * a) < 4 * (8 * p) := h
        _ = 32 * p := by ring
    exact hprod.trans_lt hfour
  let d := p / 8
  have hdpos : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    have hp : p < 8 := by
      by_contra hpnot
      have h8p : 8 ≤ p := by omega
      have hone : 1 ≤ p / 8 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2 (by simpa using h8p)
      dsimp only [d] at hd0'
      omega
    have hsmall : 32 * p < k * k := by
      calc
        32 * p < 32 * 8 :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 32)).2 hp
        _ < 4096 * 4096 := by decide
        _ ≤ k * k := Nat.mul_le_mul hk hk
    omega
  have hp_upper : p ≤ 8 * d + 7 := by
    have hmod := Nat.mod_lt p (by norm_num : 0 < 8)
    have hdecomp := Nat.div_add_mod p 8
    dsimp only [d]
    omega
  have hksq_d : k * k ≤ 512 * d := by
    have hpre : k * k < 256 * d + 224 := by
      calc
        k * k < 32 * p := hksqP
        _ ≤ 32 * (8 * d + 7) := Nat.mul_le_mul_left 32 hp_upper
        _ = 256 * d + 224 := by ring
    have h224 : 224 ≤ 256 * d := by
      have : 256 ≤ 256 * d := by
        simpa using Nat.mul_le_mul_left 256 hdpos
      omega
    omega
  let half := k / 2
  have hhalf : 1024 < half := by
    dsimp only [half]
    apply (Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)).2
    omega
  have hq : half ≤ k + 1 - s := by
    have hs_le : s ≤ half := by
      dsimp only [s]
      apply Nat.div_le_of_le_mul
      have hmod := Nat.mod_lt k (by norm_num : 0 < 2)
      have hdecomp := Nat.div_add_mod k 2
      dsimp only [half]
      omega
    omega
  have hn_two_sq : n ≤ 2 * (k * k) := by
    have hkplus : k + 1 ≤ k * k := by
      have h2k : 2 * k ≤ k * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : 2 ≤ k)
      omega
    calc
      n ≤ k * k + k + 1 := hup
      _ ≤ 2 * (k * k) := by omega
  have hlarge : n < d * half := by
    have htwo : 2 * (k * k) ≤ 1024 * d := by
      calc
        2 * (k * k) ≤ 2 * (512 * d) := Nat.mul_le_mul_left 2 hksq_d
        _ = 1024 * d := by ring
    have hstrict : 1024 * d < half * d :=
      (Nat.mul_lt_mul_right hdpos).2 hhalf
    calc
      n ≤ 2 * (k * k) := hn_two_sq
      _ ≤ 1024 * d := htwo
      _ < half * d := hstrict
      _ = d * half := by ring
  have hdensity : n < residual * (k + 1 - s) := by
    calc
      n < d * half := hlarge
      _ ≤ residual * (k + 1 - s) :=
        Nat.mul_le_mul (by simpa only [d] using hresidual) hq
  simpa only [s, heavyBound, residual] using hdensity

/-- The fixed-fraction analogue of `near_projectiveScale_floor_density`.
Here the minimum edge size is `k - k / 1024`; the bad-degree threshold is
`513`, and a projective-scale edge is heavy when it contains at least `k / 8`
bad vertices.  All constants are deliberately generous so the conclusion is
an exact natural-number inequality, not an asymptotic abbreviation. -/
lemma fixedFraction_projectiveScale_floor_density {n k a p t : ℕ}
    (hk : 65536 ≤ k)
    (hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hup : n ≤ k * k + k + 1)
    (ha : 513 ≤ a)
    (hnotBalance :
      (n - 1) * a < 4 *
        (a * (n - 1 - (k - k / 1024) * (k - k / 1024 - 1)) +
          p * (n - 1 - k * (k - 1))))
    (hsurplus :
      (n - 1) * t ≤
        a * (n - 1 - (k - k / 1024) * (k - k / 1024 - 1)) +
          p * (n - 1 - k * (k - 1))) :
    n <
      (p -
          ((a * (k - 1) / 513) * ((n - 1) / (k - 1)) / (k / 8)) -
          4 * (t - 1)) * (k + 1 - k / 8) := by
  let u := k / 1024
  let r := k - u
  let lossR := n - 1 - r * (r - 1)
  let lossK := n - 1 - k * (k - 1)
  have hkpos : 0 < k := by omega
  have hk1pos : 0 < k - 1 := by omega
  have hu_mul : 1024 * u ≤ k := by
    dsimp only [u]
    exact Nat.mul_div_le k 1024
  have hu_le : u ≤ k := by
    have h1024 : 1 ≤ 1024 := by norm_num
    have hu : u ≤ 1024 * u := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left u h1024
    exact hu.trans hu_mul
  have hku : k = r + u := by
    dsimp only [r]
    omega
  have hrlarge : 2 ≤ r := by
    have hu_quarter : 4 * u ≤ k := by
      calc
        4 * u ≤ 1024 * u := Nat.mul_le_mul_right u (by decide : 4 ≤ 1024)
        _ ≤ k := hu_mul
    dsimp only [r]
    omega
  have hR : r * (r - 1) ≤ n - 1 := by
    have hrk : r ≤ k := by dsimp only [r]; omega
    have hprod : r * (r - 1) ≤ k * (k - 1) :=
      Nat.mul_le_mul hrk (Nat.sub_le_sub_right hrk 1)
    have hK : k * (k - 1) ≤ n - 1 := by
      have hid : k * (k - 1) =
          (k - 1) * (k - 1) + (k - 1) := by
        let j := k - 1
        have hkj : k = j + 1 := by dsimp only [j]; omega
        rw [hkj]
        have hj : j + 1 - 1 = j := by omega
        rw [hj]
        ring
      rw [hid]
      omega
    exact hprod.trans hK
  have hK : k * (k - 1) ≤ n - 1 := by
    have hid : k * (k - 1) =
        (k - 1) * (k - 1) + (k - 1) := by
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hlossK : lossK ≤ 2 * k := by
    dsimp only [lossK]
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * (k - 1) + 2 * k = k * k + k := by
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    omega
  have hlossR : lossR ≤ 2 * k * u + 2 * k := by
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * k + k + (u * u + u) =
        r * (r - 1) + (2 * k * u + 2 * k) := by
      let j := r - 1
      have hrj : r = j + 1 := by dsimp only [j]; omega
      have hkj : k = j + 1 + u := by omega
      rw [hrj, hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    have hsum : n - 1 ≤ r * (r - 1) + (2 * k * u + 2 * k) := by
      calc
        n - 1 ≤ k * k + k := hpoly
        _ ≤ k * k + k + (u * u + u) := Nat.le_add_right _ _
        _ = r * (r - 1) + (2 * k * u + 2 * k) := hid
    dsimp only [lossR]
    omega
  have hlossR32 : 32 * lossR ≤ n - 1 := by
    have hu256 : 256 * u ≤ k := by
      exact (Nat.mul_le_mul_right u (by decide : 256 ≤ 1024)).trans hu_mul
    have h256ku : 256 * k * u ≤ k * k := by
      calc
        256 * k * u = k * (256 * u) := by ring
        _ ≤ k * k := Nat.mul_le_mul_left k hu256
    have h256k : 256 * k ≤ k * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : 256 ≤ k)
    have hfour : 4 * (64 * k * u + 64 * k) ≤
        2 * (k * k) := by
      calc
        4 * (64 * k * u + 64 * k) = 256 * k * u + 256 * k := by ring
        _ ≤ k * k + k * k := Nat.add_le_add h256ku h256k
        _ = 2 * (k * k) := by ring
    have htwo : 2 * (k * k) ≤ 4 * (k * (k - 1)) := by
      have h2k : 2 * k ≤ 4 * (k - 1) := by omega
      calc
        2 * (k * k) = k * (2 * k) := by ring
        _ ≤ k * (4 * (k - 1)) := Nat.mul_le_mul_left k h2k
        _ = 4 * (k * (k - 1)) := by ring
    have hbase : 64 * k * u + 64 * k ≤ k * (k - 1) := by
      have := hfour.trans htwo
      exact Nat.le_of_mul_le_mul_left this (by norm_num : 0 < 4)
    calc
      32 * lossR ≤ 32 * (2 * k * u + 2 * k) :=
        Nat.mul_le_mul_left 32 hlossR
      _ = 64 * k * u + 64 * k := by ring
      _ ≤ k * (k - 1) := hbase
      _ ≤ n - 1 := hK
  have hnotBalance' : (n - 1) * a <
      4 * (a * lossR + p * lossK) := by
    simpa only [lossR, lossK, r, u] using hnotBalance
  have hrelationD : 28 * ((n - 1) * a) < 256 * k * p := by
    have hscaled : 32 * ((n - 1) * a) <
        128 * (a * lossR + p * lossK) := by
      have h := (Nat.mul_lt_mul_left (by norm_num : 0 < 32)).2 hnotBalance'
      calc
        32 * ((n - 1) * a) < 32 * (4 * (a * lossR + p * lossK)) := h
        _ = 128 * (a * lossR + p * lossK) := by ring
    have hright : 128 * (a * lossR + p * lossK) ≤
        4 * ((n - 1) * a) + 256 * k * p := by
      calc
        128 * (a * lossR + p * lossK) =
            4 * (a * (32 * lossR)) + 128 * (p * lossK) := by ring
        _ ≤ 4 * (a * (n - 1)) + 128 * (p * (2 * k)) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left a hlossR32))
            (Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left p hlossK))
        _ = 4 * ((n - 1) * a) + 256 * k * p := by ring
    have hsum : 32 * ((n - 1) * a) <
        4 * ((n - 1) * a) + 256 * k * p := hscaled.trans_le hright
    omega
  have hrelation : 7 * ((k - 1) * a) < 64 * p := by
    have hleft : 28 * (k * ((k - 1) * a)) ≤
        28 * ((n - 1) * a) := by
      exact Nat.mul_le_mul_left 28 (by
        calc
          k * ((k - 1) * a) = (k * (k - 1)) * a := by ring
          _ ≤ (n - 1) * a := Nat.mul_le_mul_right a hK)
    have hmul : 28 * (k * ((k - 1) * a)) < 256 * k * p :=
      hleft.trans_lt hrelationD
    have hmul' : k * (28 * ((k - 1) * a)) < k * (256 * p) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hcancel : 28 * ((k - 1) * a) < 256 * p :=
      (Nat.mul_lt_mul_left hkpos).mp hmul'
    have hfour : 4 * (7 * ((k - 1) * a)) < 4 * (64 * p) := by
      calc
        4 * (7 * ((k - 1) * a)) = 28 * ((k - 1) * a) := by ring
        _ < 256 * p := hcancel
        _ = 4 * (64 * p) := by ring
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mp hfour
  have hp : 0 < p := by
    by_contra hp0
    have : p = 0 := Nat.eq_zero_of_not_pos hp0
    rw [this] at hrelation
    simp at hrelation
  have hak : a * k ≤ 19 * p := by
    have hkpred : k ≤ 2 * (k - 1) := by omega
    have hseven : 7 * (a * k) ≤ 14 * ((k - 1) * a) := by
      calc
        7 * (a * k) = 7 * (k * a) := by ring
        _ ≤ 7 * ((2 * (k - 1)) * a) :=
          Nat.mul_le_mul_left 7 (Nat.mul_le_mul_right a hkpred)
        _ = 14 * ((k - 1) * a) := by ring
    have hrel2 : 14 * ((k - 1) * a) < 128 * p := by
      have h := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hrelation
      calc
        14 * ((k - 1) * a) = 2 * (7 * ((k - 1) * a)) := by ring
        _ < 2 * (64 * p) := h
        _ = 128 * p := by ring
    have h7 : 7 * (a * k) < 128 * p := hseven.trans_lt hrel2
    omega
  have hsurplus' : (n - 1) * t ≤ a * lossR + p * lossK := by
    simpa only [lossR, lossK, r, u] using hsurplus
  have ht32 : 32 * t ≤ p := by
    have hscaled : 32 * ((n - 1) * t) ≤
        32 * (a * lossR + p * lossK) := Nat.mul_le_mul_left 32 hsurplus'
    have hbound : 32 * (a * lossR + p * lossK) ≤
        (n - 1) * a + 64 * k * p := by
      calc
        32 * (a * lossR + p * lossK) =
            a * (32 * lossR) + 32 * (p * lossK) := by ring
        _ ≤ a * (n - 1) + 32 * (p * (2 * k)) :=
          Nat.add_le_add (Nat.mul_le_mul_left a hlossR32)
            (Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left p hlossK))
        _ = (n - 1) * a + 64 * k * p := by ring
    have hDa : (n - 1) * a ≤ 10 * k * p := by
      have h7 : 7 * ((n - 1) * a) < 64 * k * p := by
        have hfour : 4 * (7 * ((n - 1) * a)) <
            4 * (64 * k * p) := by
          calc
            4 * (7 * ((n - 1) * a)) = 28 * ((n - 1) * a) := by ring
            _ < 256 * k * p := hrelationD
            _ = 4 * (64 * k * p) := by ring
        exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mp hfour
      have h64_70 : 64 * k * p ≤ 7 * (10 * k * p) := by
        have hcoef : 64 ≤ 70 := by omega
        have h := Nat.mul_le_mul_right (k * p) hcoef
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
      have h7' : 7 * ((n - 1) * a) < 7 * (10 * k * p) :=
        h7.trans_le h64_70
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 7)).mp h7' |>.le
    have h74 : 32 * ((n - 1) * t) ≤ 74 * k * p := by
      calc
        32 * ((n - 1) * t) ≤ 32 * (a * lossR + p * lossK) := hscaled
        _ ≤ (n - 1) * a + 64 * k * p := hbound
        _ ≤ 10 * k * p + 64 * k * p := Nat.add_le_add_right hDa _
        _ = 74 * k * p := by ring
    have h74D : 74 * k ≤ n - 1 := by
      have h74 : 74 ≤ k - 1 := by omega
      calc
        74 * k ≤ k * (k - 1) := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h74
        _ ≤ n - 1 := hK
    have hmul : (32 * t) * (n - 1) ≤ p * (n - 1) := by
      calc
        (32 * t) * (n - 1) = 32 * ((n - 1) * t) := by ring
        _ ≤ 74 * k * p := h74
        _ ≤ (n - 1) * p := Nat.mul_le_mul_right p h74D
        _ = p * (n - 1) := by ring
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  let s := k / 8
  have hspos : 0 < s := by
    dsimp only [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2 (by omega)
  have hslarge : 8 ≤ s := by
    dsimp only [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2 (by omega)
  have hk_s : k ≤ 8 * s + 7 := by
    have hmod := Nat.mod_lt k (by norm_num : 0 < 8)
    have hdecomp := Nat.div_add_mod k 8
    dsimp only [s]
    omega
  have hdegree : (n - 1) / (k - 1) ≤ k + 3 := by
    apply Nat.div_le_of_le_mul
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * k + k + (k - 3) = (k - 1) * (k + 3) := by
      let j := k - 3
      have hkj : k = j + 3 := by dsimp only [j]; omega
      rw [hkj]
      have hj1 : j + 3 - 1 = j + 2 := by omega
      have hj3 : j + 3 - 3 = j := by omega
      rw [hj1, hj3]
      ring
    omega
  have hdegree_s : (n - 1) / (k - 1) ≤ 9 * s := by
    have : k + 3 ≤ 9 * s := by omega
    exact hdegree.trans this
  let badBound := a * (k - 1) / 513
  let heavyBound := badBound * ((n - 1) / (k - 1)) / s
  have hbadMul : 513 * badBound ≤ a * (k - 1) := by
    dsimp only [badBound]
    have h := Nat.div_mul_le_self (a * (k - 1)) 513
    simpa [Nat.mul_comm] using h
  have hheavyBad : heavyBound ≤ 9 * badBound := by
    dsimp only [heavyBound]
    apply Nat.div_le_of_le_mul
    calc
      badBound * ((n - 1) / (k - 1)) ≤ badBound * (9 * s) :=
        Nat.mul_le_mul_left badBound hdegree_s
      _ = s * (9 * badBound) := by ring
  have hheavy3 : 3 * heavyBound ≤ p := by
    have h513 : 513 * badBound ≤ 19 * p := by
      calc
        513 * badBound ≤ a * (k - 1) := hbadMul
        _ ≤ a * k := Nat.mul_le_mul_left a (Nat.sub_le k 1)
        _ ≤ 19 * p := hak
    have h27 : 27 * badBound ≤ p := by
      have h19 : 19 * (27 * badBound) ≤ 19 * p := by
        calc
          19 * (27 * badBound) = 513 * badBound := by ring
          _ ≤ 19 * p := h513
      exact Nat.le_of_mul_le_mul_left h19 (by norm_num : 0 < 19)
    calc
      3 * heavyBound ≤ 3 * (9 * badBound) := Nat.mul_le_mul_left 3 hheavyBad
      _ = 27 * badBound := by ring
      _ ≤ p := h27
  let removed := heavyBound + 4 * (t - 1)
  have hremoved2 : 2 * removed ≤ p := by
    have hh24 : 24 * heavyBound ≤ 8 * p := by
      calc
        24 * heavyBound = 8 * (3 * heavyBound) := by ring
        _ ≤ 8 * p := Nat.mul_le_mul_left 8 hheavy3
    have ht96 : 96 * (t - 1) ≤ 3 * p := by
      calc
        96 * (t - 1) ≤ 96 * t := Nat.mul_le_mul_left 96 (Nat.sub_le _ _)
        _ = 3 * (32 * t) := by ring
        _ ≤ 3 * p := Nat.mul_le_mul_left 3 ht32
    have h24 : 24 * removed ≤ 11 * p := by
      calc
        24 * removed = 24 * heavyBound + 96 * (t - 1) := by
          dsimp only [removed]
          ring
        _ ≤ 8 * p + 3 * p := Nat.add_le_add hh24 ht96
        _ = 11 * p := by ring
    have h24' : 24 * removed ≤ 12 * p := h24.trans (by omega)
    have h12 : 12 * (2 * removed) ≤ 12 * p := by
      calc
        12 * (2 * removed) = 24 * removed := by ring
        _ ≤ 12 * p := h24'
    exact Nat.le_of_mul_le_mul_left h12 (by norm_num : 0 < 12)
  let residual := p - heavyBound - 4 * (t - 1)
  have hresidual : p / 2 ≤ residual := by
    have hsum2 : 2 * (p / 2 + removed) ≤ 2 * p := by
      calc
        2 * (p / 2 + removed) = 2 * (p / 2) + 2 * removed := by ring
        _ ≤ p + p := Nat.add_le_add (Nat.mul_div_le p 2) hremoved2
        _ = 2 * p := by ring
    have hsum : p / 2 + removed ≤ p :=
      Nat.le_of_mul_le_mul_left hsum2 (by norm_num : 0 < 2)
    dsimp only [residual, removed]
    omega
  have hp32k : 32 * k < p := by
    have hbase : 2048 * k ≤ 7 * ((k - 1) * a) := by
      have ha' : 513 ≤ a := ha
      have hmul : 7 * ((k - 1) * 513) ≤ 7 * ((k - 1) * a) :=
        Nat.mul_le_mul_left 7 (Nat.mul_le_mul_left (k - 1) ha')
      have hconst : 2048 * k ≤ 7 * ((k - 1) * 513) := by
        have hid : 7 * ((k - 1) * 513) = 3591 * (k - 1) := by ring
        rw [hid]
        omega
      exact hconst.trans hmul
    have h64 : 2048 * k < 64 * p := hbase.trans_lt hrelation
    have h64' : 64 * (32 * k) < 64 * p := by
      calc
        64 * (32 * k) = 2048 * k := by ring
        _ < 64 * p := h64
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 64)).mp h64'
  let half := k / 2
  have hhalf_ge_third : k / 3 ≤ half := by
    apply Nat.div_le_of_le_mul
    have hmod := Nat.mod_lt k (by norm_num : 0 < 3)
    have hdecomp := Nat.div_add_mod k 3
    dsimp only [half]
    have hhalf_lower : k ≤ 2 * (k / 2) + 1 := by
      have hm := Nat.mod_lt k (by norm_num : 0 < 2)
      have hd := Nat.div_add_mod k 2
      omega
    omega
  have hq : half ≤ k + 1 - s := by
    have hs_le : s ≤ half := by
      apply Nat.div_le_of_le_mul
      have hm := Nat.mod_lt k (by norm_num : 0 < 2)
      have hd := Nat.div_add_mod k 2
      dsimp only [s, half]
      omega
    omega
  have hpHalf : 16 * k ≤ p / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    omega
  have hkThird : k ≤ 4 * (k / 3) := by
    have hm := Nat.mod_lt k (by norm_num : 0 < 3)
    have hd := Nat.div_add_mod k 3
    have hthird : 2 ≤ k / 3 := by
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by omega)
    omega
  have hn2sq : n ≤ 2 * (k * k) := by
    have hkplus : k + 1 ≤ k * k := by
      have h2k : 2 * k ≤ k * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : 2 ≤ k)
      omega
    omega
  have hdensity : n < residual * (k + 1 - s) := by
    have hbig : 2 * (k * k) < (16 * k) * (k / 3) := by
      have hkpos' : 0 < k * k := Nat.mul_pos hkpos hkpos
      calc
        2 * (k * k) < 4 * (k * k) :=
          (Nat.mul_lt_mul_right hkpos').2 (by decide : 2 < 4)
        _ ≤ 16 * k * (k / 3) := by
          have := Nat.mul_le_mul_left (4 * k) hkThird
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
        _ = (16 * k) * (k / 3) := by ring
    calc
      n ≤ 2 * (k * k) := hn2sq
      _ < (16 * k) * (k / 3) := hbig
      _ ≤ (p / 2) * half := Nat.mul_le_mul hpHalf hhalf_ge_third
      _ ≤ residual * (k + 1 - s) := Nat.mul_le_mul hresidual hq
  simpa only [u, r, s, badBound, heavyBound, residual] using hdensity

/-- If one part of a weighted partition contributes at least `R` per object
and the other contributes at least `n`, the global budget `n(n-1)` controls
the excess number of objects over `n`.  This is the integral rearrangement
behind (5.6) and (5.8). -/
lemma partition_surplus_mul_le {n a b R : ℕ}
    (hR : R ≤ n)
    (hweight : a * R + b * n ≤ n * (n - 1)) :
    n * (a + b - n) ≤ a * (n - R) := by
  obtain rfl | hnpos := n.eq_zero_or_pos
  · simp
  by_cases htotal : a + b ≤ n
  · simp [Nat.sub_eq_zero_of_le htotal]
  · let s := a + b - n
    have hab : a + b = n + s := by
      dsimp only [s]
      omega
    have h1 : a * R + (a + b) * n ≤ n * (n - 1) + a * n := by
      calc
        a * R + (a + b) * n = (a * R + b * n) + a * n := by ring
        _ ≤ n * (n - 1) + a * n := Nat.add_le_add_right hweight _
    rw [hab] at h1
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    have hnn : n * (n - 1) + n = n * n := by
      calc
        n * (n - 1) + n = n * ((n - 1) + 1) := by ring
        _ = n * n := by rw [hpred]
    have h2 : n * n + (n * s + n + a * R) ≤ n * n + a * n := by
      calc
        n * n + (n * s + n + a * R) = (a * R + (n + s) * n) + n := by ring
        _ ≤ (n * (n - 1) + a * n) + n := Nat.add_le_add_right h1 _
        _ = n * n + a * n := by
          calc
            (n * (n - 1) + a * n) + n =
                (n * (n - 1) + n) + a * n := by omega
            _ = n * n + a * n := by rw [hnn]
    have h3 : n * s + n + a * R ≤ a * n := Nat.le_of_add_le_add_left h2
    have hnR : n = R + (n - R) := by omega
    have han : a * n = a * R + a * (n - R) := by
      conv_lhs => rw [hnR]
      ring
    have h3' : a * R + (n * s + n) ≤ a * R + a * (n - R) := by
      calc
        a * R + (n * s + n) = n * s + n + a * R := by ring
        _ ≤ a * n := h3
        _ = a * R + a * (n - R) := han
    have h4 : n * s + n ≤ a * (n - R) := Nat.le_of_add_le_add_left h3'
    have h5 : n * s ≤ a * (n - R) := (Nat.le_add_right _ _).trans h4
    dsimp only [s] at h5
    exact h5

lemma partition_surplus_le_quarter {n a b R : ℕ} (hn : 0 < n)
    (hR : R ≤ n) (hquarter : 4 * (n - R) ≤ n)
    (hweight : a * R + b * n ≤ n * (n - 1)) :
    a + b - n ≤ a / 4 := by
  let s := a + b - n
  let c := n - R
  change s ≤ a / 4
  have hsurplus : n * s ≤ a * c := partition_surplus_mul_le hR hweight
  by_cases hc : c = 0
  · have hs : s = 0 := by
      by_contra hs0
      have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      have hpos : 0 < n * s := Nat.mul_pos hn hspos
      rw [hc] at hsurplus
      simp at hsurplus
      omega
    simp [hs]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hmul : (4 * s) * c ≤ a * c := by
      calc
        (4 * s) * c = (4 * c) * s := by ring
        _ ≤ n * s := Nat.mul_le_mul_right s hquarter
        _ ≤ a * c := hsurplus
    have hfour : 4 * s ≤ a := Nat.le_of_mul_le_mul_right hmul hcpos
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [Nat.mul_comm] using hfour

/-- A version of `partition_surplus_mul_le` with a separate target count `N`
and high-part volume unit `D`.  In Lemma 5.1 the latter is `n-1`. -/
lemma weighted_partition_surplus_mul_le {N D a b R : ℕ}
    (hR : R ≤ D) (hweight : a * R + b * D ≤ N * D) :
    D * (a + b - N) ≤ a * (D - R) := by
  by_cases htotal : a + b ≤ N
  · simp [Nat.sub_eq_zero_of_le htotal]
  · let s := a + b - N
    have hab : a + b = N + s := by
      dsimp only [s]
      omega
    have h1 : a * R + (a + b) * D ≤ N * D + a * D := by
      calc
        a * R + (a + b) * D = (a * R + b * D) + a * D := by ring
        _ ≤ N * D + a * D := Nat.add_le_add_right hweight _
    rw [hab] at h1
    have h2 : N * D + (s * D + a * R) ≤ N * D + a * D := by
      calc
        N * D + (s * D + a * R) = a * R + (N + s) * D := by ring
        _ ≤ N * D + a * D := h1
    have h3 : s * D + a * R ≤ a * D := Nat.le_of_add_le_add_left h2
    have hDR : D = R + (D - R) := by omega
    have haD : a * D = a * R + a * (D - R) := by
      conv_lhs => rw [hDR]
      ring
    have h4 : a * R + s * D ≤ a * R + a * (D - R) := by
      calc
        a * R + s * D = s * D + a * R := by ring
        _ ≤ a * D := h3
        _ = a * R + a * (D - R) := haD
    have hs : s * D ≤ a * (D - R) := Nat.le_of_add_le_add_left h4
    dsimp only [s] at hs
    simpa [Nat.mul_comm] using hs

lemma weighted_partition_surplus_le_quarter {N D a b R : ℕ} (hD : 0 < D)
    (hR : R ≤ D) (hquarter : 4 * (D - R) ≤ D)
    (hweight : a * R + b * D ≤ N * D) :
    a + b - N ≤ a / 4 := by
  let s := a + b - N
  let c := D - R
  change s ≤ a / 4
  have hsurplus : D * s ≤ a * c :=
    weighted_partition_surplus_mul_le hR hweight
  by_cases hc : c = 0
  · have hs : s = 0 := by
      by_contra hs0
      have hpos : 0 < D * s := Nat.mul_pos hD (Nat.pos_of_ne_zero hs0)
      rw [hc] at hsurplus
      simp at hsurplus
      omega
    simp [hs]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hmul : (4 * s) * c ≤ a * c := by
      calc
        (4 * s) * c = (4 * c) * s := by ring
        _ ≤ D * s := Nat.mul_le_mul_right s hquarter
        _ ≤ a * c := hsurplus
    have hfour : 4 * s ≤ a := Nat.le_of_mul_le_mul_right hmul hcpos
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [Nat.mul_comm] using hfour

/-- Three-class form of the volume-deficit calculation.  It retains the
separate deficits of edges below and exactly at the projective scale. -/
lemma weighted_three_surplus_mul_le {N D a b c R K : ℕ}
    (hR : R ≤ D) (hK : K ≤ D)
    (hweight : a * R + b * K + c * D ≤ N * D) :
    D * (a + b + c - N) ≤ a * (D - R) + b * (D - K) := by
  by_cases htotal : a + b + c ≤ N
  · simp [Nat.sub_eq_zero_of_le htotal]
  · let s := a + b + c - N
    have habc : a + b + c = N + s := by
      dsimp only [s]
      omega
    have h1 : a * R + b * K + (a + b + c) * D ≤
        N * D + a * D + b * D := by
      calc
        a * R + b * K + (a + b + c) * D =
            (a * R + b * K + c * D) + a * D + b * D := by ring
        _ ≤ N * D + a * D + b * D := by
          exact Nat.add_le_add_right (Nat.add_le_add_right hweight _) _
    rw [habc] at h1
    have h2 : N * D + (s * D + (a * R + b * K)) ≤
        N * D + (a * D + b * D) := by
      calc
        N * D + (s * D + (a * R + b * K)) =
            a * R + b * K + (N + s) * D := by ring
        _ ≤ N * D + a * D + b * D := h1
        _ = N * D + (a * D + b * D) := by omega
    have h3 : s * D + (a * R + b * K) ≤ a * D + b * D :=
      Nat.le_of_add_le_add_left h2
    have hDR : D = R + (D - R) := by omega
    have hDK : D = K + (D - K) := by omega
    have haD : a * D = a * R + a * (D - R) := by
      conv_lhs => rw [hDR]
      ring
    have hbD : b * D = b * K + b * (D - K) := by
      conv_lhs => rw [hDK]
      ring
    have hrhs : a * D + b * D =
        (a * R + b * K) + (a * (D - R) + b * (D - K)) := by
      rw [haD, hbD]
      ring
    have h4 : (a * R + b * K) + s * D ≤
        (a * R + b * K) + (a * (D - R) + b * (D - K)) := by
      calc
        (a * R + b * K) + s * D = s * D + (a * R + b * K) := by ring
        _ ≤ a * D + b * D := h3
        _ = _ := hrhs
    have hs := Nat.le_of_add_le_add_left h4
    dsimp only [s] at hs
    simpa [Nat.mul_comm] using hs

lemma weighted_three_surplus_le_quarter {N D a b c R K : ℕ}
    (hD : 0 < D) (hR : R ≤ D) (hK : K ≤ D)
    (hweight : a * R + b * K + c * D ≤ N * D)
    (hbalance : 4 * (a * (D - R) + b * (D - K)) ≤ D * a) :
    a + b + c - N ≤ a / 4 := by
  let s := a + b + c - N
  let loss := a * (D - R) + b * (D - K)
  change s ≤ a / 4
  have hs : D * s ≤ loss := weighted_three_surplus_mul_le hR hK hweight
  have hmul : (4 * s) * D ≤ a * D := by
    calc
      (4 * s) * D = 4 * (D * s) := by ring
      _ ≤ 4 * loss := Nat.mul_le_mul_left 4 hs
      _ ≤ D * a := hbalance
      _ = a * D := by ring
  have hfour : 4 * s ≤ a := Nat.le_of_mul_le_mul_right hmul hD
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  simpa [Nat.mul_comm] using hfour

/-! ## Extending a partial graph coloring -/

/-- Colors already seen by `v` on a precolored vertex set `S`. -/
def fixedNeighborColors {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (S : Set V) (c : S → Fin k) (v : V) : Set (Fin k) :=
  {a | ∃ x : S, G.Adj v x.1 ∧ c x = a}

/-- Neighbors of `v` that do not belong to the precolored vertex set. -/
def uncoloredNeighborSet {V : Type*} (G : SimpleGraph V)
    (S : Set V) (v : V) : Set V :=
  {w | w ∉ S ∧ G.Adj v w}

/-- A partial proper coloring extends greedily if, at every uncolored vertex,
the number of colors forbidden by precolored neighbors plus the total number
of uncolored neighbors is smaller than the palette.  This is the deterministic
completion endpoint for the random partial-coloring proof of a locally sparse
graph-coloring saving. -/
theorem SimpleGraph.colorable_of_partialColoring [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (S : Set V) (c : S → Fin k)
    (hc : ∀ ⦃x y : S⦄, G.Adj x.1 y.1 → c x ≠ c y)
    (hbudget : ∀ v, v ∉ S →
      (fixedNeighborColors G S c v).ncard +
          (uncoloredNeighborSet G S v).ncard < k) :
    G.Colorable k := by
  classical
  let fallback : Fin k := ⟨0, hk⟩
  let U : Finset V := Sᶜ.toFinset
  have aux (T : Finset V) (hTU : T ⊆ U) :
      ∃ d : V → Fin k,
        (∀ x (hx : x ∈ S), d x = c ⟨x, hx⟩) ∧
        ∀ ⦃x y : V⦄, (x ∈ S ∨ x ∈ T) → (y ∈ S ∨ y ∈ T) →
          G.Adj x y → d x ≠ d y := by
    induction T using Finset.strongInductionOn
    next T ih =>
      obtain rfl | hT := T.eq_empty_or_nonempty
      · let d : V → Fin k := fun x ↦
          if hx : x ∈ S then c ⟨x, hx⟩ else fallback
        refine ⟨d, ?_, ?_⟩
        · intro x hx
          simp [d, hx]
        · intro x y hx hy hxy
          simp only [Finset.notMem_empty, or_false] at hx hy
          simpa [d, hx, hy] using hc (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hxy
      · obtain ⟨v, hvT⟩ := hT
        let T₀ := T.erase v
        have hT₀T : T₀ ⊂ T := Finset.erase_ssubset hvT
        have hT₀U : T₀ ⊆ U := hT₀T.le.trans hTU
        obtain ⟨d, hdS, hdvalid⟩ := ih T₀ hT₀T hT₀U
        have hvU : v ∈ U := hTU hvT
        have hvS : v ∉ S := by
          have : v ∈ Sᶜ := Set.mem_toFinset.mp hvU
          simpa using this
        let fixed : Finset (Fin k) := (fixedNeighborColors G S c v).toFinset
        let flexible : Finset (Fin k) :=
          (T₀.filter fun w ↦ G.Adj v w).image d
        let used : Finset (Fin k) := fixed ∪ flexible
        have hflexCard : flexible.card ≤
            (uncoloredNeighborSet G S v).ncard := by
          calc
            flexible.card ≤ (T₀.filter fun w ↦ G.Adj v w).card :=
              Finset.card_image_le
            _ = (↑(T₀.filter fun w ↦ G.Adj v w) : Set V).ncard :=
              (Set.ncard_coe_finset _).symm
            _ ≤ (uncoloredNeighborSet G S v).ncard := by
              apply Set.ncard_le_ncard
              · intro w hw
                have hw' := Finset.mem_filter.mp hw
                have hwU : w ∈ U := hT₀U hw'.1
                have hwS : w ∉ S := by
                  have : w ∈ Sᶜ := Set.mem_toFinset.mp hwU
                  simpa using this
                exact ⟨hwS, hw'.2⟩
              · exact Set.toFinite _
        have hused : used.card < k := by
          calc
            used.card ≤ fixed.card + flexible.card := by
              dsimp only [used]
              exact Finset.card_union_le fixed flexible
            _ ≤ (fixedNeighborColors G S c v).ncard +
                (uncoloredNeighborSet G S v).ncard := by
              apply Nat.add_le_add
              · dsimp only [fixed]
                rw [Set.ncard_eq_toFinset_card']
              · exact hflexCard
            _ < k := hbudget v hvS
        obtain ⟨a, _hauniv, haused⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card
            (s := used) (t := Finset.univ) (by simpa using hused)
        let d' : V → Fin k := Function.update d v a
        have hnew (w : V) (hw : w ∈ S ∨ w ∈ T₀) (hvw : G.Adj v w) :
            a ≠ d w := by
          intro haw
          apply haused
          dsimp only [used]
          rw [Finset.mem_union]
          rcases hw with hwS | hwT₀
          · left
            dsimp only [fixed]
            rw [Set.mem_toFinset]
            refine ⟨⟨w, hwS⟩, hvw, ?_⟩
            rw [← hdS w hwS, haw]
          · right
            dsimp only [flexible]
            apply Finset.mem_image.mpr
            exact ⟨w, Finset.mem_filter.mpr ⟨hwT₀, hvw⟩, haw.symm⟩
        refine ⟨d', ?_, ?_⟩
        · intro x hxS
          have hxv : x ≠ v := fun hxv ↦ hvS (hxv ▸ hxS)
          simp [d', hxv, hdS x hxS]
        · intro x y hx hy hxy
          by_cases hxv : x = v
          · subst x
            have hyv : y ≠ v := hxy.ne.symm
            have hy₀ : y ∈ S ∨ y ∈ T₀ := by
              rcases hy with hyS | hyT
              · exact Or.inl hyS
              · exact Or.inr (Finset.mem_erase.mpr ⟨hyv, hyT⟩)
            simpa [d', hyv] using hnew y hy₀ hxy
          · by_cases hyv : y = v
            · subst y
              have hx₀ : x ∈ S ∨ x ∈ T₀ := by
                rcases hx with hxS | hxT
                · exact Or.inl hxS
                · exact Or.inr (Finset.mem_erase.mpr ⟨hxv, hxT⟩)
              have hax := hnew x hx₀ hxy.symm
              simpa [d', hxv] using hax.symm
            · have hx₀ : x ∈ S ∨ x ∈ T₀ := by
                rcases hx with hxS | hxT
                · exact Or.inl hxS
                · exact Or.inr (Finset.mem_erase.mpr ⟨hxv, hxT⟩)
              have hy₀ : y ∈ S ∨ y ∈ T₀ := by
                rcases hy with hyS | hyT
                · exact Or.inl hyS
                · exact Or.inr (Finset.mem_erase.mpr ⟨hyv, hyT⟩)
              simpa [d', hxv, hyv] using hdvalid hx₀ hy₀ hxy
  obtain ⟨d, _hdS, hdvalid⟩ := aux U (fun _ h ↦ h)
  refine ⟨SimpleGraph.Coloring.mk d ?_⟩
  intro x y hxy
  have hxmem : x ∈ S ∨ x ∈ U := by
    by_cases hx : x ∈ S
    · exact Or.inl hx
    · exact Or.inr (Set.mem_toFinset.mpr (by simpa using hx))
  have hymem : y ∈ S ∨ y ∈ U := by
    by_cases hy : y ∈ S
    · exact Or.inl hy
    · exact Or.inr (Set.mem_toFinset.mpr (by simpa using hy))
  exact hdvalid hxmem hymem hxy

/-- Neighbors of `v` that belong to the precolored set. -/
def coloredNeighborSet {V : Type*} (G : SimpleGraph V)
    (S : Set V) (v : V) : Set V :=
  {w | w ∈ S ∧ G.Adj v w}

/-- The colored and uncolored neighbors partition the full neighborhood. -/
lemma SimpleGraph.coloredNeighbor_ncard_add_uncoloredNeighbor_ncard [Fintype V]
    (G : SimpleGraph V) (S : Set V) (v : V) :
    (coloredNeighborSet G S v).ncard +
        (uncoloredNeighborSet G S v).ncard = (G.neighborSet v).ncard := by
  have hcolored : coloredNeighborSet G S v = G.neighborSet v ∩ S := by
    ext w
    simp only [coloredNeighborSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      G.mem_neighborSet]
    tauto
  have huncolored : uncoloredNeighborSet G S v = G.neighborSet v \ S := by
    ext w
    simp only [uncoloredNeighborSet, Set.mem_setOf_eq, Set.mem_sdiff,
      G.mem_neighborSet]
    tauto
  rw [hcolored, huncolored,
    Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v) S]

/-- The colors visible on the precolored neighbors are no more numerous than
the precolored neighbors themselves. -/
lemma fixedNeighborColors_ncard_le_coloredNeighborSet_ncard [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (S : Set V) (c : S → Fin k) (v : V) :
    (fixedNeighborColors G S c v).ncard ≤
      (coloredNeighborSet G S v).ncard := by
  classical
  let colorOn : coloredNeighborSet G S v → Fin k := fun x ↦
    c ⟨x.1, x.2.1⟩
  have hrange : fixedNeighborColors G S c v = Set.range colorOn := by
    ext a
    constructor
    · rintro ⟨x, hvx, hcx⟩
      refine ⟨⟨x.1, x.2, hvx⟩, ?_⟩
      exact hcx
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.1, x.2.1⟩, x.2.2, rfl⟩
  rw [hrange]
  calc
    (Set.range colorOn).ncard = Fintype.card (Set.range colorOn) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ ≤ Fintype.card (coloredNeighborSet G S v) :=
      Fintype.card_range_le colorOn
    _ = (coloredNeighborSet G S v).ncard :=
      Set.fintypeCard_eq_ncard _

/-- Savings formulation of `colorable_of_partialColoring`.  A repeated color
on precolored neighbors saves one unit relative to greedy coloring.  If every
uncolored vertex has enough such savings to bridge the gap from maximum
degree `Δ` to the target palette `k`, the partial coloring extends. -/
theorem SimpleGraph.colorable_of_partialColoring_savings [Fintype V]
    (G : SimpleGraph V) {k Δ : ℕ} (hk : 0 < k)
    (S : Set V) (c : S → Fin k)
    (hc : ∀ ⦃x y : S⦄, G.Adj x.1 y.1 → c x ≠ c y)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hsavings : ∀ v, v ∉ S →
      Δ + 1 - k ≤ (coloredNeighborSet G S v).ncard -
        (fixedNeighborColors G S c v).ncard) :
    G.Colorable k := by
  apply SimpleGraph.colorable_of_partialColoring G hk S c hc
  intro v hvS
  have hpartition :=
    Erdos19.SimpleGraph.coloredNeighbor_ncard_add_uncoloredNeighbor_ncard G S v
  have hcolors := fixedNeighborColors_ncard_le_coloredNeighborSet_ncard G S c v
  have hsave := hsavings v hvS
  have hdeg := hdegree v
  omega

/-- Certificate form of the partial-colouring extension theorem.  At every
uncoloured vertex, it is enough to exhibit `t` pairwise endpoint-disjoint
pairs of coloured neighbours, one pair in each of `t` distinct colours.  The
two members of a pair need not be adjacent (and in a proper partial colouring
they automatically are not); their repeated colour supplies one unit of the
required greedy saving. -/
theorem SimpleGraph.colorable_of_partialColoring_collisionPairs [Fintype V]
    (G : SimpleGraph V) {k Δ t : ℕ} (hk : 0 < k)
    (S : Set V) (c : S → Fin k)
    (hc : ∀ ⦃x y : S⦄, G.Adj x.1 y.1 → c x ≠ c y)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hpairs : ∀ v, v ∉ S →
      ∃ left right : Fin t → coloredNeighborSet G S v,
        Function.Injective (Sum.elim left right) ∧
        (∀ i, c ⟨(left i).1, (left i).2.1⟩ =
          c ⟨(right i).1, (right i).2.1⟩) ∧
        Function.Injective (fun i ↦ c ⟨(left i).1, (left i).2.1⟩)) :
    G.Colorable k := by
  apply SimpleGraph.colorable_of_partialColoring_savings G hk S c hc hdegree
  intro v hvS
  letI : Fintype (coloredNeighborSet G S v) := Fintype.ofFinite _
  letI : Fintype (fixedNeighborColors G S c v) := Fintype.ofFinite _
  obtain ⟨left, right, hendpoints, hcollision, hcolors⟩ := hpairs v hvS
  let colorOn : coloredNeighborSet G S v → Fin k := fun x ↦
    c ⟨x.1, x.2.1⟩
  have hdeficiency :
      t ≤ Fintype.card (coloredNeighborSet G S v) -
        Nat.card (Set.range colorOn) :=
    card_sub_range_card_ge_of_disjoint_collision_pairs colorOn t left right
      hendpoints hcollision hcolors
  have hrange : Set.range colorOn = fixedNeighborColors G S c v := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.1, x.2.1⟩, x.2.2, rfl⟩
    · rintro ⟨x, hvx, hcx⟩
      exact ⟨⟨x.1, x.2, hvx⟩, hcx⟩
  have hcoloredCard :
      Fintype.card (coloredNeighborSet G S v) =
        (coloredNeighborSet G S v).ncard :=
    Set.fintypeCard_eq_ncard _
  have hrangeCard : Nat.card (Set.range colorOn) =
      (fixedNeighborColors G S c v).ncard := by
    rw [hrange, Nat.card_eq_fintype_card]
    exact Set.fintypeCard_eq_ncard _
  rw [hcoloredCard, hrangeCard] at hdeficiency
  exact hgap.trans hdeficiency

/-! ### Random partial-coloring interface for locally sparse graphs -/

/-- Vertices retained by the standard one-round random partial-coloring
experiment.  A sample records an activation bit and a tentative color at each
vertex.  An active vertex is retained exactly when no active neighbor chose
the same tentative color. -/
def randomRetainedSet {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) : Set V :=
  {v | (sample v).1 = true ∧
    ∀ w, G.Adj v w → (sample w).1 = true → (sample w).2 ≠ (sample v).2}

/-- The Molloy--Reed experiment assigns every vertex a tentative color; it
has no separate activation coin.  This map realizes that experiment inside
the more general activation-bit interface by declaring every vertex active. -/
def alwaysActiveSample {V : Type*} {C : ℕ}
    (sample : V → Fin C) : V → Bool × Fin C :=
  fun v ↦ (true, sample v)

/-- A tunable-density version of the random partial-coloring sample.  One
distinguished value of the first coordinate means active, so under the
uniform product measure the activation probability is exactly one over A. -/
def dilutedSample {V : Type*} {A C : ℕ} (active : Fin A)
    (sample : V → Fin A × Fin C) : V → Bool × Fin C :=
  fun v ↦ (decide ((sample v).1 = active), (sample v).2)

@[simp]
lemma dilutedSample_active_iff {V : Type*} {A C : ℕ} (active : Fin A)
    (sample : V → Fin A × Fin C) (v : V) :
    (dilutedSample active sample v).1 = true ↔ (sample v).1 = active := by
  simp [dilutedSample]

@[simp]
lemma dilutedSample_color {V : Type*} {A C : ℕ} (active : Fin A)
    (sample : V → Fin A × Fin C) (v : V) :
    (dilutedSample active sample v).2 = (sample v).2 :=
  rfl

@[simp]
lemma dilutedSample_of_eq_activeColor {V : Type*} {A C : ℕ}
    (active : Fin A) (sample : V → Fin A × Fin C) (v : V) (a : Fin C)
    (h : sample v = (active, a)) :
    dilutedSample active sample v = (true, a) := by
  simp [dilutedSample, h]

/-- The graph of unordered nonedges inside the neighborhood of `v`.  Its
edges are precisely the pairs which can create a tentative color saving at
`v`. -/
def nonadjacentNeighborPairGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph V where
  Adj p q := p ≠ q ∧ G.Adj v p ∧ G.Adj v q ∧ ¬G.Adj p q
  symm := ⟨by
    rintro p q ⟨hpq, hvp, hvq, hpqNonadj⟩
    exact ⟨hpq.symm, hvq, hvp, fun h ↦ hpqNonadj h.symm⟩⟩
  loopless := ⟨by
    intro p hp
    exact hp.1 rfl⟩

/-- The coordinates which are required to avoid a fixed color in the
retained-pair cylinder for `p,q ∈ N(v)`: all other neighbors of `v`, and all
neighbors of either endpoint. -/
noncomputable def mrPairForbiddenFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v p q : V) : Finset V := by
  classical
  exact (((eventFinset (G.neighborSet v)).erase p).erase q) ∪
    eventFinset (G.neighborSet p) ∪ eventFinset (G.neighborSet q)

/-- A source-faithful retained-pair cylinder.  Exactly the two selected
neighbors receive `a` inside `N(v)`, and the color is absent from the
neighborhoods of both endpoints. -/
def mrRetainedPairEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (v p q : V) (a : Fin C) :
    Set (V → Fin C) :=
  {sample | sample p = a ∧ sample q = a ∧
    ∀ x ∈ mrPairForbiddenFinset G v p q, sample x ≠ a}

/-- A sample realizes the retained-pair cylinder indexed by the unordered
nonedge `e` and color `a`. -/
def mrRetainedPairWitness {V : Type*} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (v : V)
    (sample : V → Fin C) (a : Fin C)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet) : Prop :=
  sample ∈ mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a

/-- The finite set of pair cylinders realized by one sample and one color. -/
noncomputable def mrRetainedPairWitnessFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V)
    (sample : V → Fin C) (a : Fin C) :
    Finset (nonadjacentNeighborPairGraph G v).edgeSet := by
  classical
  exact Finset.univ.filter (mrRetainedPairWitness G v sample a)

/-- The endpoints selected from the nonedge graph satisfy all four defining
properties. -/
lemma nonadjacentNeighborPairGraph_edge_out
    {V : Type*} (G : SimpleGraph V) (v : V)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet) :
    e.1.out.1 ≠ e.1.out.2 ∧
      G.Adj v e.1.out.1 ∧ G.Adj v e.1.out.2 ∧
        ¬G.Adj e.1.out.1 e.1.out.2 := by
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
    change Quot.mk _ (e.1.out.1, e.1.out.2) = e.1
    rw [Prod.eta]
    exact e.1.out_eq
  have hedge : s(e.1.out.1, e.1.out.2) ∈
      (nonadjacentNeighborPairGraph G v).edgeSet := by
    rw [hout]
    exact e.2
  simpa [nonadjacentNeighborPairGraph] using
    ((nonadjacentNeighborPairGraph G v).mem_edgeSet.mp hedge)

/-- Repackaging the quotient representative chosen by `Sym2.out`. -/
lemma sym2_mk_out_eq {A : Type*} (e : Sym2 A) :
    s(e.out.1, e.out.2) = e := by
  change Quot.mk _ (e.out.1, e.out.2) = e
  rw [Prod.eta]
  exact e.out_eq

lemma left_notMem_mrPairForbiddenFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v p q : V)
    (hpq : p ≠ q) (hnonadj : ¬G.Adj p q) :
    p ∉ mrPairForbiddenFinset G v p q := by
  classical
  have hnonadj' : ¬G.Adj q p := fun h ↦ hnonadj h.symm
  simp [mrPairForbiddenFinset, G.loopless, hnonadj, hnonadj', hpq]

lemma right_notMem_mrPairForbiddenFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v p q : V)
    (hpq : p ≠ q) (hnonadj : ¬G.Adj p q) :
    q ∉ mrPairForbiddenFinset G v p q := by
  classical
  simp [mrPairForbiddenFinset, G.loopless, hnonadj, hpq]

/-- Exact cardinality of a retained-pair cylinder. -/
lemma card_mrRetainedPairEvent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ}
    (v p q : V) (a : Fin C) (hpq : p ≠ q) (hnonadj : ¬G.Adj p q) :
    (eventFinset (mrRetainedPairEvent G v p q a)).card =
      (C - 1) ^ (mrPairForbiddenFinset G v p q).card *
        C ^ (Fintype.card V - (mrPairForbiddenFinset G v p q).card - 2) := by
  classical
  rw [card_eventFinset_eq_ncard]
  change ({sample : V → Fin C |
    sample p = a ∧ sample q = a ∧
      ∀ x ∈ mrPairForbiddenFinset G v p q, sample x ≠ a} : Set _).ncard = _
  rw [← Set.fintypeCard_eq_ncard]
  change Fintype.card {sample : V → Fin C //
    sample p = a ∧ sample q = a ∧
      ∀ x ∈ mrPairForbiddenFinset G v p q, sample x ≠ a} = _
  simpa [mrRetainedPairEvent, Nat.card_eq_fintype_card] using
    (card_fun_eq_two_avoid_finset a (mrPairForbiddenFinset G v p q) hpq
      (left_notMem_mrPairForbiddenFinset G v p q hpq hnonadj)
      (right_notMem_mrPairForbiddenFinset G v p q hpq hnonadj))

/-- Under a maximum-degree bound `Δ`, a retained-pair cylinder forbids at
most `3Δ-2` coordinates.  The two-unit saving records that the prescribed
endpoints have been removed from `N(v)`. -/
lemma mrPairForbiddenFinset_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ : ℕ)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (v p q : V) (hpq : p ≠ q)
    (hvp : G.Adj v p) (hvq : G.Adj v q) :
    (mrPairForbiddenFinset G v p q).card ≤ 3 * Δ - 2 := by
  let Nv := eventFinset (G.neighborSet v)
  let Np := eventFinset (G.neighborSet p)
  let Nq := eventFinset (G.neighborSet q)
  have hpNv : p ∈ Nv := by simpa [Nv] using hvp
  have hqNv : q ∈ Nv := by simpa [Nv] using hvq
  have hqErase : q ∈ Nv.erase p := by simp [hqNv, hpq.symm]
  have hNvTwo : ((Nv.erase p).erase q).card = Nv.card - 2 := by
    rw [Finset.card_erase_of_mem hqErase, Finset.card_erase_of_mem hpNv]
    omega
  have hNv : Nv.card ≤ Δ := by
    simpa [Nv, card_eventFinset_eq_ncard] using hdegree v
  have hNp : Np.card ≤ Δ := by
    simpa [Np, card_eventFinset_eq_ncard] using hdegree p
  have hNq : Nq.card ≤ Δ := by
    simpa [Nq, card_eventFinset_eq_ncard] using hdegree q
  have hΔ : 2 ≤ Δ := by
    have htwo : 2 ≤ Nv.card :=
      (Finset.one_lt_card.mpr ⟨p, hpNv, q, hqNv, hpq⟩)
    exact htwo.trans hNv
  calc
    (mrPairForbiddenFinset G v p q).card =
        (((Nv.erase p).erase q) ∪ Np ∪ Nq).card := by
      congr 1
      ext x
      simp [mrPairForbiddenFinset, Nv, Np, Nq]
    _ ≤ ((Nv.erase p).erase q).card + Np.card + Nq.card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ = (Nv.card - 2) + Np.card + Nq.card := by rw [hNvTwo]
    _ ≤ (Δ - 2) + Δ + Δ := by omega
    _ = 3 * Δ - 2 := by omega

/-- Uniform lower bound for every retained-pair cylinder whose forbidden
support is bounded by `m`. -/
lemma mixed_cylinder_le_card_mrRetainedPairEvent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C m : ℕ}
    (v p q : V) (a : Fin C) (hpq : p ≠ q) (hnonadj : ¬G.Adj p q)
    (hcard : (mrPairForbiddenFinset G v p q).card ≤ m)
    (hmV : m + 2 ≤ Fintype.card V) :
    (C - 1) ^ m * C ^ (Fintype.card V - m - 2) ≤
      (eventFinset (mrRetainedPairEvent G v p q a)).card := by
  rw [card_mrRetainedPairEvent G v p q a hpq hnonadj]
  exact mixed_cylinder_count_anti_mono hcard hmV

/-- A concrete saving certificate at `v`: `t` endpoint-disjoint pairs of
retained neighbors have equal tentative colors within each pair, and those
`t` common colors are distinct. -/
def HasRandomCollisionCertificate {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (t : ℕ) (v : V) : Prop :=
  ∃ left right : Fin t → V,
    Function.Injective (Sum.elim left right) ∧
    (∀ i,
      left i ∈ randomRetainedSet G sample ∧
      right i ∈ randomRetainedSet G sample ∧
      G.Adj v (left i) ∧ G.Adj v (right i)) ∧
    (∀ i, (sample (left i)).2 = (sample (right i)).2) ∧
    Function.Injective (fun i ↦ (sample (left i)).2)

/-- Retained neighbors of `v` carrying the tentative color `a`. -/
def retainedNeighborColorFiber {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) (a : Fin k) : Set V :=
  {w | w ∈ randomRetainedSet G sample ∧ G.Adj v w ∧ (sample w).2 = a}

/-- Colors occurring on at least two distinct retained neighbors of `v`.
Every such color supplies one endpoint-disjoint collision pair, because the
retained partial coloring is proper and different colors have disjoint
fibers. -/
def retainedCollisionColors {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) : Set (Fin k) :=
  {a | ∃ x y : V, x ≠ y ∧
    x ∈ retainedNeighborColorFiber G sample v a ∧
    y ∈ retainedNeighborColorFiber G sample v a}

/-- Active neighbors of `v` carrying tentative color `a`, before conflicts
are erased. -/
def tentativeNeighborColorFiber {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) (a : Fin k) : Set V :=
  {w | (sample w).1 = true ∧ G.Adj v w ∧ (sample w).2 = a}

/-- Tentative colors appearing on a nonadjacent pair of active neighbors of
`v`.  These are the initially created color savings in the Molloy--Reed
one-round experiment. -/
def tentativeCollisionColors {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) : Set (Fin k) :=
  {a | ∃ x y : V, x ≠ y ∧ ¬G.Adj x y ∧
    x ∈ tentativeNeighborColorFiber G sample v a ∧
    y ∈ tentativeNeighborColorFiber G sample v a}

/-- Tentative collision colors that do not survive conflict erasure. -/
def spoiledCollisionColors {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) : Set (Fin k) :=
  tentativeCollisionColors G sample v \ retainedCollisionColors G sample v

@[simp]
lemma mem_randomRetainedSet_alwaysActive {V : Type*} (G : SimpleGraph V)
    {C : ℕ} (sample : V → Fin C) (w : V) :
    w ∈ randomRetainedSet G (alwaysActiveSample sample) ↔
      ∀ z, G.Adj w z → sample z ≠ sample w := by
  simp [randomRetainedSet, alwaysActiveSample]

@[simp]
lemma mem_tentativeNeighborColorFiber_alwaysActive
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    (sample : V → Fin C) (v w : V) (a : Fin C) :
    w ∈ tentativeNeighborColorFiber G (alwaysActiveSample sample) v a ↔
      G.Adj v w ∧ sample w = a := by
  simp [tentativeNeighborColorFiber, alwaysActiveSample]

@[simp]
lemma mem_retainedNeighborColorFiber_alwaysActive
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    (sample : V → Fin C) (v w : V) (a : Fin C) :
    w ∈ retainedNeighborColorFiber G (alwaysActiveSample sample) v a ↔
      (∀ z, G.Adj w z → sample z ≠ sample w) ∧
        G.Adj v w ∧ sample w = a := by
  simp [retainedNeighborColorFiber, alwaysActiveSample]

/-- Every assignment in a retained-pair cylinder really contributes its
selected color to the retained collision set. -/
lemma mrRetainedPairEvent_subset_retainedCollisionColors
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v p q : V) (a : Fin C)
    (hpq : p ≠ q) (hnonadj : ¬G.Adj p q)
    (hvp : G.Adj v p) (hvq : G.Adj v q) :
    mrRetainedPairEvent G v p q a ⊆
      {sample | a ∈ retainedCollisionColors G (alwaysActiveSample sample) v} := by
  intro sample hsample
  refine ⟨p, q, hpq, ?_, ?_⟩
  · rw [mem_retainedNeighborColorFiber_alwaysActive]
    refine ⟨?_, hvp, hsample.1⟩
    intro z hpz
    have hzS : z ∈ mrPairForbiddenFinset G v p q := by
      simp [mrPairForbiddenFinset, hpz]
    have hza := hsample.2.2 z hzS
    simpa [hsample.1] using hza
  · rw [mem_retainedNeighborColorFiber_alwaysActive]
    refine ⟨?_, hvq, hsample.2.1⟩
    intro z hqz
    have hzS : z ∈ mrPairForbiddenFinset G v p q := by
      simp [mrPairForbiddenFinset, hqz]
    have hza := hsample.2.2 z hzS
    simpa [hsample.2.1] using hza

/-- A retained-pair cylinder pins down the selected unordered pair exactly as
the vertices in `N(v)` carrying its color.  The explicit exclusion of all
other neighbors is what prevents overcounting in the expectation sum. -/
lemma mem_pair_iff_adj_and_color_of_mrRetainedPairWitness
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) (a : Fin C)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet)
    (h : mrRetainedPairWitness G v sample a e) (x : V) :
    x ∈ e.1 ↔ G.Adj v x ∧ sample x = a := by
  let p := e.1.out.1
  let q := e.1.out.2
  have he := nonadjacentNeighborPairGraph_edge_out G v e
  change sample p = a ∧ sample q = a ∧
    ∀ z ∈ mrPairForbiddenFinset G v p q, sample z ≠ a at h
  have hout : s(p, q) = e.1 := sym2_mk_out_eq e.1
  constructor
  · intro hx
    rw [← hout, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨he.2.1, h.1⟩
    · exact ⟨he.2.2.1, h.2.1⟩
  · rintro ⟨hvx, hxa⟩
    rw [← hout, Sym2.mem_iff]
    by_cases hxp : x = p
    · exact Or.inl hxp
    by_cases hxq : x = q
    · exact Or.inr hxq
    exfalso
    have hxS : x ∈ mrPairForbiddenFinset G v p q := by
      simp [mrPairForbiddenFinset, hvx, hxp, hxq]
    exact (h.2.2 x hxS) hxa

/-- For a fixed sample and color, two realized pair cylinders have the same
unordered pair. -/
lemma mrRetainedPairWitness_unique
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) (a : Fin C)
    {e f : (nonadjacentNeighborPairGraph G v).edgeSet}
    (he : mrRetainedPairWitness G v sample a e)
    (hf : mrRetainedPairWitness G v sample a f) : e = f := by
  apply Subtype.ext
  apply Sym2.ext
  intro x
  rw [mem_pair_iff_adj_and_color_of_mrRetainedPairWitness
        G v sample a e he x,
      mem_pair_iff_adj_and_color_of_mrRetainedPairWitness
        G v sample a f hf x]

/-- Hence the realized-pair fiber at a fixed sample and color has cardinality
at most one. -/
lemma card_mrRetainedPairWitnessFinset_le_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) (a : Fin C) :
    (mrRetainedPairWitnessFinset G v sample a).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro e he f hf
  rw [mrRetainedPairWitnessFinset, Finset.mem_filter] at he hf
  exact mrRetainedPairWitness_unique G v sample a he.2 hf.2

/-- Every realized pair cylinder produces an actual retained collision color. -/
lemma retainedCollision_of_mrRetainedPairWitness
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) (a : Fin C)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet)
    (h : mrRetainedPairWitness G v sample a e) :
    a ∈ retainedCollisionColors G (alwaysActiveSample sample) v := by
  have he := nonadjacentNeighborPairGraph_edge_out G v e
  exact mrRetainedPairEvent_subset_retainedCollisionColors
    G v e.1.out.1 e.1.out.2 a he.1 he.2.2.2 he.2.1 he.2.2.1 h

/-- Summing realized retained-pair cylinders over colors does not exceed the
number of retained collision colors in the sample. -/
lemma sum_card_mrRetainedPairWitnessFinset_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) :
    (∑ a : Fin C, (mrRetainedPairWitnessFinset G v sample a).card) ≤
      (retainedCollisionColors G (alwaysActiveSample sample) v).ncard := by
  classical
  let R := retainedCollisionColors G (alwaysActiveSample sample) v
  calc
    (∑ a : Fin C, (mrRetainedPairWitnessFinset G v sample a).card) ≤
        ∑ a : Fin C, if a ∈ R then 1 else 0 := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases haR : a ∈ R
      · simpa [haR] using card_mrRetainedPairWitnessFinset_le_one G v sample a
      · have hempty : mrRetainedPairWitnessFinset G v sample a = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨e, he⟩
          apply haR
          apply retainedCollision_of_mrRetainedPairWitness G v sample a e
          exact (Finset.mem_filter.mp he).2
        simp [haR, hempty]
    _ = (eventFinset R).card := by simp [eventFinset]
    _ = R.ncard := card_eventFinset_eq_ncard R

/-- Double-counting all retained-pair cylinders.  On the left they are
grouped by color and unordered nonedge; on the right they are grouped by
sample.  The uniqueness lemma bounds the latter multiplicity by the number
of retained collision colors. -/
lemma sum_card_mrRetainedPairEvent_le_sum_retainedCollisionColors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : ℕ} (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj] :
    (∑ a : Fin C,
      ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
        (eventFinset
          (mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a)).card) ≤
      ∑ sample : V → Fin C,
        (retainedCollisionColors G (alwaysActiveSample sample) v).ncard := by
  classical
  have hcard (a : Fin C)
      (e : (nonadjacentNeighborPairGraph G v).edgeSet) :
      (eventFinset
          (mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a)).card =
        ∑ sample : V → Fin C,
          if mrRetainedPairWitness G v sample a e then 1 else 0 := by
    change ((Finset.univ : Finset (V → Fin C)).filter
      (mrRetainedPairWitness G v · a e)).card = _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ a : Fin C,
      ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
        (eventFinset
          (mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a)).card) =
        ∑ a : Fin C,
          ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
            ∑ sample : V → Fin C,
              if mrRetainedPairWitness G v sample a e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro e _he
      exact hcard a e
    _ = ∑ a : Fin C,
          ∑ sample : V → Fin C,
            ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
              if mrRetainedPairWitness G v sample a e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ sample : V → Fin C,
          ∑ a : Fin C,
            ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
              if mrRetainedPairWitness G v sample a e then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ sample : V → Fin C,
          ∑ a : Fin C,
            (mrRetainedPairWitnessFinset G v sample a).card := by
      apply Finset.sum_congr rfl
      intro sample _hsample
      apply Finset.sum_congr rfl
      intro a _ha
      unfold mrRetainedPairWitnessFinset
      rw [Finset.sum_boole (R := ℕ)
        (mrRetainedPairWitness G v sample a)
        (Finset.univ : Finset
          (nonadjacentNeighborPairGraph G v).edgeSet)]
      apply congrArg Finset.card
      ext e
      simp
    _ ≤ ∑ sample : V → Fin C,
          (retainedCollisionColors G (alwaysActiveSample sample) v).ncard := by
      apply Finset.sum_le_sum
      intro sample _hsample
      exact sum_card_mrRetainedPairWitnessFinset_le G v sample

/-- Cross-multiplied expectation lower bound from any uniform upper bound
`m` on the forbidden support of the retained-pair cylinders. -/
lemma retainedCollisionColors_expectation_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C m : ℕ} (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj]
    (hsupport : ∀ e : (nonadjacentNeighborPairGraph G v).edgeSet,
      (mrPairForbiddenFinset G v e.1.out.1 e.1.out.2).card ≤ m)
    (hmV : m + 2 ≤ Fintype.card V) :
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
        ((C - 1) ^ m * C ^ (Fintype.card V - m - 2)) ≤
      ∑ sample : V → Fin C,
        (retainedCollisionColors G (alwaysActiveSample sample) v).ncard := by
  classical
  let q := (C - 1) ^ m * C ^ (Fintype.card V - m - 2)
  have hlower (a : Fin C)
      (e : (nonadjacentNeighborPairGraph G v).edgeSet) :
      q ≤ (eventFinset
        (mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a)).card := by
    have he := nonadjacentNeighborPairGraph_edge_out G v e
    exact mixed_cylinder_le_card_mrRetainedPairEvent
      G v e.1.out.1 e.1.out.2 a he.1 he.2.2.2
      (hsupport e) hmV
  calc
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * q =
        ∑ a : Fin C,
          ∑ _e : (nonadjacentNeighborPairGraph G v).edgeSet, q := by
      rw [← Set.fintypeCard_eq_ncard
        (nonadjacentNeighborPairGraph G v).edgeSet]
      simp [Nat.mul_assoc]
    _ ≤ ∑ a : Fin C,
          ∑ e : (nonadjacentNeighborPairGraph G v).edgeSet,
            (eventFinset
              (mrRetainedPairEvent G v e.1.out.1 e.1.out.2 a)).card := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro e _he
      exact hlower a e
    _ ≤ ∑ sample : V → Fin C,
          (retainedCollisionColors G (alwaysActiveSample sample) v).ncard :=
      sum_card_mrRetainedPairEvent_le_sum_retainedCollisionColors G v

/-- The preceding expectation estimate with the graph-theoretic support bound
`3Δ-2` discharged from a maximum-degree hypothesis. -/
lemma retainedCollisionColors_expectation_lower_bound_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C Δ : ℕ} (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj]
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (hambient : (3 * Δ - 2) + 2 ≤ Fintype.card V) :
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
        ((C - 1) ^ (3 * Δ - 2) *
          C ^ (Fintype.card V - (3 * Δ - 2) - 2)) ≤
      ∑ sample : V → Fin C,
        (retainedCollisionColors G (alwaysActiveSample sample) v).ncard := by
  apply retainedCollisionColors_expectation_lower_bound G v
  · intro e
    have he := nonadjacentNeighborPairGraph_edge_out G v e
    exact mrPairForbiddenFinset_card_le G Δ hdegree
      v e.1.out.1 e.1.out.2 he.1 he.2.1 he.2.2.1
  · exact hambient

/-- Two product assignments agree away from one distinguished coordinate. -/
def AgreeAwayFrom {A K : Type*} (f g : A → K) (x : A) : Prop :=
  ∀ y, y ≠ x → f y = g y

lemma AgreeAwayFrom.symm {A K : Type*} {f g : A → K} {x : A}
    (h : AgreeAwayFrom f g x) : AgreeAwayFrom g f x := by
  intro y hy
  exact (h y hy).symm

/-- Changing one vertex color cannot affect whether an unrelated color is a
tentative collision color. -/
lemma mem_tentativeCollisionColors_iff_of_agreeAwayFrom
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} {x v : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ sample x) (ha' : a ≠ sample' x) :
    a ∈ tentativeCollisionColors G (alwaysActiveSample sample) v ↔
      a ∈ tentativeCollisionColors G (alwaysActiveSample sample') v := by
  have transfer (s s' : V → Fin C) (hss' : AgreeAwayFrom s s' x)
      (hax : a ≠ s x)
      (hmem : a ∈ tentativeCollisionColors G (alwaysActiveSample s) v) :
      a ∈ tentativeCollisionColors G (alwaysActiveSample s') v := by
    obtain ⟨p, q, hpq, hnonadj, hp, hq⟩ := hmem
    rw [mem_tentativeNeighborColorFiber_alwaysActive] at hp hq
    have hpx : p ≠ x := by
      intro h
      subst p
      exact hax hp.2.symm
    have hqx : q ≠ x := by
      intro h
      subst q
      exact hax hq.2.symm
    refine ⟨p, q, hpq, hnonadj,
      (mem_tentativeNeighborColorFiber_alwaysActive G s' v p a).mpr
        ⟨hp.1, (hss' p hpx).symm.trans hp.2⟩,
      (mem_tentativeNeighborColorFiber_alwaysActive G s' v q a).mpr
        ⟨hq.1, (hss' q hqx).symm.trans hq.2⟩⟩
  constructor
  · exact transfer sample sample' heq ha
  · exact transfer sample' sample heq.symm ha'

/-- The one-coordinate switching lemma for arbitrary activation-bit samples.
Only the old and new tentative colors can change their collision indicator. -/
lemma mem_tentativeCollisionColors_iff_of_agreeAwayFrom_general
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Bool × Fin C} {x v : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ (sample x).2) (ha' : a ≠ (sample' x).2) :
    a ∈ tentativeCollisionColors G sample v ↔
      a ∈ tentativeCollisionColors G sample' v := by
  have transfer (s s' : V → Bool × Fin C)
      (hss' : AgreeAwayFrom s s' x) (hax : a ≠ (s x).2)
      (hmem : a ∈ tentativeCollisionColors G s v) :
      a ∈ tentativeCollisionColors G s' v := by
    obtain ⟨p, q, hpq, hnonadj, hp, hq⟩ := hmem
    have hpx : p ≠ x := by
      intro h
      subst p
      exact hax hp.2.2.symm
    have hqx : q ≠ x := by
      intro h
      subst q
      exact hax hq.2.2.symm
    have heqp := hss' p hpx
    have heqq := hss' q hqx
    refine ⟨p, q, hpq, hnonadj, ?_, ?_⟩
    · exact ⟨by simpa [heqp] using hp.1, hp.2.1,
        by simpa [heqp] using hp.2.2⟩
    · exact ⟨by simpa [heqq] using hq.1, hq.2.1,
        by simpa [heqq] using hq.2.2⟩
  constructor
  · exact transfer sample sample' heq ha
  · exact transfer sample' sample heq.symm ha'

/-- Tentative collisions inspect only the sample on the open neighborhood of
the center, for arbitrary activation-bit samples. -/
lemma tentativeCollisionColors_eq_of_eqOn_neighborSet_general
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Bool × Fin C} (v : V)
    (h : ∀ w, G.Adj v w → sample w = sample' w) :
    tentativeCollisionColors G sample v =
      tentativeCollisionColors G sample' v := by
  ext a
  constructor
  · rintro ⟨p, q, hpq, hnonadj, hp, hq⟩
    refine ⟨p, q, hpq, hnonadj, ?_, ?_⟩
    · change (sample' p).1 = true ∧ G.Adj v p ∧ (sample' p).2 = a
      rw [← h p hp.2.1]
      exact hp
    · change (sample' q).1 = true ∧ G.Adj v q ∧ (sample' q).2 = a
      rw [← h q hq.2.1]
      exact hq
  · rintro ⟨p, q, hpq, hnonadj, hp, hq⟩
    refine ⟨p, q, hpq, hnonadj, ?_, ?_⟩
    · change (sample p).1 = true ∧ G.Adj v p ∧ (sample p).2 = a
      rw [h p hp.2.1]
      exact hp
    · change (sample q).1 = true ∧ G.Adj v q ∧ (sample q).2 = a
      rw [h q hq.2.1]
      exact hq

/-- Changing one vertex color cannot affect retention in an unrelated color
fiber. -/
lemma mem_retainedNeighborColorFiber_iff_of_agreeAwayFrom
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} {x v w : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ sample x) (ha' : a ≠ sample' x) :
    w ∈ retainedNeighborColorFiber G (alwaysActiveSample sample) v a ↔
      w ∈ retainedNeighborColorFiber G (alwaysActiveSample sample') v a := by
  have transfer (s s' : V → Fin C) (hss' : AgreeAwayFrom s s' x)
      (hax : a ≠ s x) (hax' : a ≠ s' x)
      (hmem : w ∈ retainedNeighborColorFiber G (alwaysActiveSample s) v a) :
      w ∈ retainedNeighborColorFiber G (alwaysActiveSample s') v a := by
    rw [mem_retainedNeighborColorFiber_alwaysActive] at hmem ⊢
    have hwx : w ≠ x := by
      intro h
      subst w
      exact hax hmem.2.2.symm
    refine ⟨?_, hmem.2.1, (hss' w hwx).symm.trans hmem.2.2⟩
    intro z hwz
    by_cases hzx : z = x
    · subst z
      intro hsame
      apply hax'
      exact (hsame.trans ((hss' w hwx).symm.trans hmem.2.2)).symm
    · have hneq := hmem.1 z hwz
      intro hsame
      apply hneq
      exact (hss' z hzx).trans (hsame.trans (hss' w hwx).symm)
  constructor
  · exact transfer sample sample' heq ha ha'
  · exact transfer sample' sample heq.symm ha' ha

/-- Changing one coordinate cannot affect whether an unrelated color occurs
twice on retained neighbors. -/
lemma mem_retainedCollisionColors_iff_of_agreeAwayFrom
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} {x v : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ sample x) (ha' : a ≠ sample' x) :
    a ∈ retainedCollisionColors G (alwaysActiveSample sample) v ↔
      a ∈ retainedCollisionColors G (alwaysActiveSample sample') v := by
  have hfiber (w : V) :=
    mem_retainedNeighborColorFiber_iff_of_agreeAwayFrom
      G (x := x) (v := v) (w := w) heq ha ha'
  constructor
  · rintro ⟨p, q, hpq, hp, hq⟩
    exact ⟨p, q, hpq, (hfiber p).mp hp, (hfiber q).mp hq⟩
  · rintro ⟨p, q, hpq, hp, hq⟩
    exact ⟨p, q, hpq, (hfiber p).mpr hp, (hfiber q).mpr hq⟩

/-- The spoiled-color indicator for any color other than the old and new
coordinate colors is unchanged by a one-coordinate modification. -/
lemma mem_spoiledCollisionColors_iff_of_agreeAwayFrom
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} {x v : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ sample x) (ha' : a ≠ sample' x) :
    a ∈ spoiledCollisionColors G (alwaysActiveSample sample) v ↔
      a ∈ spoiledCollisionColors G (alwaysActiveSample sample') v := by
  change
    (a ∈ tentativeCollisionColors G (alwaysActiveSample sample) v ∧
      a ∉ retainedCollisionColors G (alwaysActiveSample sample) v) ↔
    (a ∈ tentativeCollisionColors G (alwaysActiveSample sample') v ∧
      a ∉ retainedCollisionColors G (alwaysActiveSample sample') v)
  rw [
    mem_tentativeCollisionColors_iff_of_agreeAwayFrom G heq ha ha',
    mem_retainedCollisionColors_iff_of_agreeAwayFrom G heq ha ha']

/-- Molloy--Reed's certifiable deletion variable.  A color is counted when it
appears on a nonadjacent pair in `N(v)` and one member of that pair lies on a
monochromatic edge.  This is a (possibly strict) superset of tentative colors
that fail to leave two retained occurrences, which is exactly what the
deterministic estimate needs. -/
def mrDeletedCollisionColors {V : Type*} (G : SimpleGraph V) {C : ℕ}
    (sample : V → Fin C) (v : V) : Set (Fin C) :=
  {a | ∃ p q z : V,
    p ≠ q ∧ ¬G.Adj p q ∧
    G.Adj v p ∧ G.Adj v q ∧
    sample p = a ∧ sample q = a ∧
    G.Adj p z ∧ sample z = a}

/-- Structural deletion witnesses at `v`, before a sample is chosen.  We use
ordered triples because the definition distinguishes the endpoint `p` whose
monochromatic neighbor is exposed. -/
noncomputable def mrDeletionWitnessTriples
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Finset ((V × V) × V) := by
  classical
  exact Finset.univ.filter fun t ↦
    t.1.1 ≠ t.1.2 ∧ ¬G.Adj t.1.1 t.1.2 ∧
      G.Adj v t.1.1 ∧ G.Adj v t.1.2 ∧ G.Adj t.1.1 t.2

@[simp]
lemma mem_mrDeletionWitnessTriples
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (t : (V × V) × V) :
    t ∈ mrDeletionWitnessTriples G v ↔
      t.1.1 ≠ t.1.2 ∧ ¬G.Adj t.1.1 t.1.2 ∧
        G.Adj v t.1.1 ∧ G.Adj v t.1.2 ∧ G.Adj t.1.1 t.2 := by
  classical
  simp [mrDeletionWitnessTriples]

/-- Structural deletion witnesses whose three coordinates received one common
color in `sample`. -/
noncomputable def mrRealizedDeletionWitnessFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) : Finset ((V × V) × V) := by
  classical
  exact (mrDeletionWitnessTriples G v).filter fun t ↦
    sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2

/-- A selected deletion color injects into the realized structural witnesses:
distinct colors cannot choose the same triple because the color is read off at
its first coordinate. -/
lemma mrDeletedCollisionColors_ncard_le_realizedWitnesses
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ}
    (v : V) (sample : V → Fin C) :
    (mrDeletedCollisionColors G sample v).ncard ≤
      (mrRealizedDeletionWitnessFinset G v sample).card := by
  classical
  let D := mrDeletedCollisionColors G sample v
  have hexists (a : D) : ∃ p q z : V,
      p ≠ q ∧ ¬G.Adj p q ∧ G.Adj v p ∧ G.Adj v q ∧
        sample p = a.1 ∧ sample q = a.1 ∧ G.Adj p z ∧ sample z = a.1 :=
    a.2
  let p (a : D) := Classical.choose (hexists a)
  let q (a : D) := Classical.choose (Classical.choose_spec (hexists a))
  let z (a : D) := Classical.choose
    (Classical.choose_spec (Classical.choose_spec (hexists a)))
  have hspec (a : D) :
      p a ≠ q a ∧ ¬G.Adj (p a) (q a) ∧
        G.Adj v (p a) ∧ G.Adj v (q a) ∧
        sample (p a) = a.1 ∧ sample (q a) = a.1 ∧
        G.Adj (p a) (z a) ∧ sample (z a) = a.1 :=
    Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hexists a)))
  let witness (a : D) : mrRealizedDeletionWitnessFinset G v sample :=
    ⟨((p a, q a), z a), by
      simp only [mrRealizedDeletionWitnessFinset, Finset.mem_filter]
      constructor
      · simp only [mrDeletionWitnessTriples, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨(hspec a).1, (hspec a).2.1, (hspec a).2.2.1,
          (hspec a).2.2.2.1, (hspec a).2.2.2.2.2.2.1⟩
      · exact ⟨(hspec a).2.2.2.2.1.trans
          (hspec a).2.2.2.2.2.1.symm,
          (hspec a).2.2.2.2.1.trans
            (hspec a).2.2.2.2.2.2.2.symm⟩⟩
  have hwitness : Function.Injective witness := by
    intro a b hab
    apply Subtype.ext
    have hpab : p a = p b := by
      have hval := congrArg (fun t : ((V × V) × V) ↦ t.1.1)
        (congrArg Subtype.val hab)
      exact hval
    calc
      a.1 = sample (p a) := (hspec a).2.2.2.2.1.symm
      _ = sample (p b) := by rw [hpab]
      _ = b.1 := (hspec b).2.2.2.2.1
  calc
    D.ncard = Fintype.card D := (Set.fintypeCard_eq_ncard D).symm
    _ ≤ Fintype.card (mrRealizedDeletionWitnessFinset G v sample) :=
      Fintype.card_le_of_injective witness hwitness
    _ = (mrRealizedDeletionWitnessFinset G v sample).card :=
      Fintype.card_coe _

/-- The three coordinates of a structural deletion witness are pairwise
distinct.  The first two are required to be different and nonadjacent, while
the first and third are adjacent. -/
lemma mrDeletionWitnessTriples_pairwiseDistinct
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (t : (V × V) × V) (ht : t ∈ mrDeletionWitnessTriples G v) :
    t.1.1 ≠ t.1.2 ∧ t.1.1 ≠ t.2 ∧ t.1.2 ≠ t.2 := by
  classical
  rw [mrDeletionWitnessTriples, Finset.mem_filter] at ht
  have hpq : t.1.1 ≠ t.1.2 := ht.2.1
  have hnonadj : ¬G.Adj t.1.1 t.1.2 := ht.2.2.1
  have hpz : G.Adj t.1.1 t.2 := ht.2.2.2.2.2
  refine ⟨hpq, hpz.ne, ?_⟩
  intro hqz
  apply hnonadj
  simpa [hqz] using hpz

/-- A fixed structural deletion triple is realized by exactly
`C ^ (|V| - 2)` samples: its three distinct coordinates must receive one
freely chosen common color. -/
lemma card_mrDeletionTripleEvent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V)
    (t : (V × V) × V) (ht : t ∈ mrDeletionWitnessTriples G v) :
    (eventFinset {sample : V → Fin C |
      sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2}).card =
      C ^ (Fintype.card V - 2) := by
  classical
  obtain ⟨hpq, hpz, hqz⟩ :=
    mrDeletionWitnessTriples_pairwiseDistinct G v t ht
  rw [card_eventFinset_eq_ncard, ← Set.fintypeCard_eq_ncard]
  change Fintype.card {sample : V → Fin C //
    sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2} = _
  simpa [Nat.card_eq_fintype_card] using
    (card_fun_eq_at_three C hpq hpz hqz)

/-- Certificate data for the event that at least `s` distinct deletion colors
occur: choose the `s` colors and one structural witness triple for each. -/
abbrev MRDeletionCertificateIndex
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (C s : ℕ) :=
  Σ S : {S : Finset (Fin C) // S.card = s},
    S.1 → {t // t ∈ mrDeletionWitnessTriples G v}

/-- The cylinder determined by fixed deletion-certificate data. -/
def mrDeletionCertificateEvent
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {C s : ℕ} (v : V) (d : MRDeletionCertificateIndex G v C s) :
    Set (V → Fin C) :=
  {sample | ∀ a : d.1.1,
    sample (d.2 a).1.1.1 = a.1 ∧
    sample (d.2 a).1.1.2 = a.1 ∧
    sample (d.2 a).1.2 = a.1}

/-- There are `C choose s` choices of the selected colors and, independently,
one of `|W_v|` structural triples for each selected color. -/
lemma card_MRDeletionCertificateIndex
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (C s : ℕ) :
    Fintype.card (MRDeletionCertificateIndex G v C s) =
      C.choose s * (mrDeletionWitnessTriples G v).card ^ s := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ S : {S : Finset (Fin C) // S.card = s},
        Fintype.card (S.1 → {t // t ∈ mrDeletionWitnessTriples G v})) =
        ∑ _S : {S : Finset (Fin C) // S.card = s},
          (mrDeletionWitnessTriples G v).card ^ s := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe, S.2]
    _ = Fintype.card {S : Finset (Fin C) // S.card = s} *
        (mrDeletionWitnessTriples G v).card ^ s := by simp
    _ = C.choose s * (mrDeletionWitnessTriples G v).card ^ s := by
      rw [Fintype.card_finset_len]
      simp

/-- If a fixed deletion certificate is realizable, its `3s` prescribed
coordinates are all distinct: an overlap between witnesses for different
colors would force those colors equal, while the three coordinates within one
witness are pairwise distinct. -/
lemma mrDeletionCertificate_endpoint_injective_of_mem
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {C s : ℕ} (v : V) (d : MRDeletionCertificateIndex G v C s)
    (sample : V → Fin C) (hsample : sample ∈ mrDeletionCertificateEvent G v d) :
    Function.Injective
      (Sum.elim
        (fun a : d.1.1 ↦ (d.2 a).1.1.1)
        (Sum.elim
          (fun a : d.1.1 ↦ (d.2 a).1.1.2)
          (fun a : d.1.1 ↦ (d.2 a).1.2)) :
        d.1.1 ⊕ (d.1.1 ⊕ d.1.1) → V) := by
  have hcert (a : d.1.1) := hsample a
  have hdistinct (a : d.1.1) :
      (d.2 a).1.1.1 ≠ (d.2 a).1.1.2 ∧
      (d.2 a).1.1.1 ≠ (d.2 a).1.2 ∧
      (d.2 a).1.1.2 ≠ (d.2 a).1.2 :=
    mrDeletionWitnessTriples_pairwiseDistinct G v (d.2 a).1 (d.2 a).2
  have color_eq {a b : d.1.1} {x y : V}
      (hxa : sample x = a.1) (hyb : sample y = b.1) (hxy : x = y) : a = b := by
    apply Subtype.ext
    calc
      a.1 = sample x := hxa.symm
      _ = sample y := by rw [hxy]
      _ = b.1 := hyb
  intro x y hxy
  rcases x with a | a | a <;> rcases y with b | b | b
  · have hab := color_eq (hcert a).1 (hcert b).1 hxy
    subst b
    rfl
  · have hab := color_eq (hcert a).1 (hcert b).2.1 hxy
    subst b
    exact ((hdistinct a).1 hxy).elim
  · have hab := color_eq (hcert a).1 (hcert b).2.2 hxy
    subst b
    exact ((hdistinct a).2.1 hxy).elim
  · have hab := color_eq (hcert a).2.1 (hcert b).1 hxy
    subst b
    exact ((hdistinct a).1 hxy.symm).elim
  · have hab := color_eq (hcert a).2.1 (hcert b).2.1 hxy
    subst b
    rfl
  · have hab := color_eq (hcert a).2.1 (hcert b).2.2 hxy
    subst b
    exact ((hdistinct a).2.2 hxy).elim
  · have hab := color_eq (hcert a).2.2 (hcert b).1 hxy
    subst b
    exact ((hdistinct a).2.1 hxy.symm).elim
  · have hab := color_eq (hcert a).2.2 (hcert b).2.1 hxy
    subst b
    exact ((hdistinct a).2.2 hxy.symm).elim
  · have hab := color_eq (hcert a).2.2 (hcert b).2.2 hxy
    subst b
    rfl

/-- Every fixed deletion certificate cylinder has at most
`C ^ (|V| - 3s)` samples.  If it is nonempty, the preceding injectivity lemma
and the exact prescribed-triple count give equality. -/
lemma card_mrDeletionCertificateEvent_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C s : ℕ} (v : V)
    (d : MRDeletionCertificateIndex G v C s) :
    (eventFinset (mrDeletionCertificateEvent G v d)).card ≤
      C ^ (Fintype.card V - 3 * s) := by
  classical
  by_cases hne : (mrDeletionCertificateEvent G v d).Nonempty
  · obtain ⟨sample, hsample⟩ := hne
    have hinj := mrDeletionCertificate_endpoint_injective_of_mem
      G v d sample hsample
    unfold mrDeletionCertificateEvent
    rw [card_eventFinset_eq_ncard, ← Set.fintypeCard_eq_ncard]
    change Fintype.card {sample : V → Fin C // ∀ a : d.1.1,
      sample (d.2 a).1.1.1 = a.1 ∧
      sample (d.2 a).1.1.2 = a.1 ∧
      sample (d.2 a).1.2 = a.1} ≤ _
    have hcount := card_fun_fixed_collision_triples C
      (fun a : d.1.1 ↦ (d.2 a).1.1.1)
      (fun a : d.1.1 ↦ (d.2 a).1.1.2)
      (fun a : d.1.1 ↦ (d.2 a).1.2)
      hinj (fun a : d.1.1 ↦ a.1)
    rw [Nat.card_eq_fintype_card] at hcount
    rw [hcount]
    rw [Fintype.card_coe, d.1.2]
  · have hempty : mrDeletionCertificateEvent G v d = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp [eventFinset]

/-- All samples realizing some fixed certificate of `s` deletion colors. -/
noncomputable def mrDeletionCertificateUnionFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V) (s : ℕ) :
    Finset (V → Fin C) := by
  classical
  exact Finset.univ.biUnion fun d : MRDeletionCertificateIndex G v C s ↦
    eventFinset (mrDeletionCertificateEvent G v d)

/-- If at least `s` deletion colors occur, selecting any `s` of them and one
witness for each places the sample in the certificate union. -/
lemma mrDeletionHighEvent_subset_certificateUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V) (s : ℕ) :
    eventFinset {sample : V → Fin C |
      s ≤ (mrDeletedCollisionColors G sample v).ncard} ⊆
      mrDeletionCertificateUnionFinset G v s := by
  classical
  intro sample hsample
  rw [mem_eventFinset] at hsample
  let D := mrDeletedCollisionColors G sample v
  let Df := eventFinset D
  have hDfcard : s ≤ Df.card := by
    rw [show Df.card = D.ncard from card_eventFinset_eq_ncard D]
    exact hsample
  obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hDfcard
  let S' : {S : Finset (Fin C) // S.card = s} := ⟨S, hScard⟩
  have hdata (a : S'.1) : ∃ p q z : V,
      p ≠ q ∧ ¬G.Adj p q ∧ G.Adj v p ∧ G.Adj v q ∧
        sample p = a.1 ∧ sample q = a.1 ∧
        G.Adj p z ∧ sample z = a.1 := by
    have haDf : a.1 ∈ Df := hSD a.2
    have haD : a.1 ∈ D := (mem_eventFinset D a.1).mp haDf
    exact haD
  choose p q z hspec using hdata
  let witness (a : S'.1) : {t // t ∈ mrDeletionWitnessTriples G v} :=
    ⟨((p a, q a), z a), (mem_mrDeletionWitnessTriples G v _).mpr
      ⟨(hspec a).1, (hspec a).2.1, (hspec a).2.2.1,
        (hspec a).2.2.2.1, (hspec a).2.2.2.2.2.2.1⟩⟩
  let d : MRDeletionCertificateIndex G v C s := ⟨S', witness⟩
  have hcert : sample ∈ mrDeletionCertificateEvent G v d := by
    intro a
    exact ⟨(hspec a).2.2.2.2.1, (hspec a).2.2.2.2.2.1,
      (hspec a).2.2.2.2.2.2.2⟩
  unfold mrDeletionCertificateUnionFinset
  exact Finset.mem_biUnion.mpr
    ⟨d, Finset.mem_univ _, (mem_eventFinset _ sample).mpr hcert⟩

/-- Direct finite upper tail for the certifiable deletion variable.  This is
the exact union bound over selected color sets and their structural witness
triples. -/
lemma card_mrDeletionHighEvent_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V) (s : ℕ) :
    (eventFinset {sample : V → Fin C |
      s ≤ (mrDeletedCollisionColors G sample v).ncard}).card ≤
      (C.choose s * (mrDeletionWitnessTriples G v).card ^ s) *
        C ^ (Fintype.card V - 3 * s) := by
  classical
  let I := MRDeletionCertificateIndex G v C s
  let U := mrDeletionCertificateUnionFinset (C := C) G v s
  let q := C ^ (Fintype.card V - 3 * s)
  calc
    (eventFinset {sample : V → Fin C |
        s ≤ (mrDeletedCollisionColors G sample v).ncard}).card ≤
        U.card := Finset.card_le_card
          (mrDeletionHighEvent_subset_certificateUnion G v s)
    _ ≤ ∑ d ∈ (Finset.univ : Finset I),
        (eventFinset (mrDeletionCertificateEvent G v d)).card := by
      dsimp only [U]
      unfold mrDeletionCertificateUnionFinset
      exact Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ (Finset.univ : Finset I), q := by
      apply Finset.sum_le_sum
      intro d _hd
      exact card_mrDeletionCertificateEvent_le G v d
    _ = Fintype.card I * q := by simp
    _ = (C.choose s * (mrDeletionWitnessTriples G v).card ^ s) *
        C ^ (Fintype.card V - 3 * s) := by
      rw [card_MRDeletionCertificateIndex]

/-- Exact double count of all realized deletion triples, first by samples and
then by structural triples. -/
lemma sum_card_mrRealizedDeletionWitnessFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V) :
    (∑ sample : V → Fin C,
      (mrRealizedDeletionWitnessFinset G v sample).card) =
      (mrDeletionWitnessTriples G v).card *
        C ^ (Fintype.card V - 2) := by
  classical
  let T := mrDeletionWitnessTriples G v
  have hsample (sample : V → Fin C) :
      (mrRealizedDeletionWitnessFinset G v sample).card =
        ∑ t ∈ T,
          if sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2
          then 1 else 0 := by
    unfold mrRealizedDeletionWitnessFinset
    change (T.filter fun t ↦
      sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2).card = _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ sample : V → Fin C,
        (mrRealizedDeletionWitnessFinset G v sample).card) =
        ∑ sample : V → Fin C,
          ∑ t ∈ T,
            if sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2
            then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro sample _hsample
      exact hsample sample
    _ = ∑ t ∈ T,
          ∑ sample : V → Fin C,
            if sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2
            then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ T,
          (eventFinset {sample : V → Fin C |
            sample t.1.1 = sample t.1.2 ∧
              sample t.1.1 = sample t.2}).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.sum_boole (R := ℕ)
        (fun sample : V → Fin C ↦
          sample t.1.1 = sample t.1.2 ∧ sample t.1.1 = sample t.2)
        (Finset.univ : Finset (V → Fin C))]
      apply congrArg Finset.card
      ext sample
      simp
    _ = ∑ _t ∈ T, C ^ (Fintype.card V - 2) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact card_mrDeletionTripleEvent G v t ht
    _ = T.card * C ^ (Fintype.card V - 2) := by simp

/-- Cross-multiplied expectation upper bound for the certifiable deletion
variable in terms of the number of structural witness triples. -/
lemma mrDeletedCollisionColors_expectation_upper_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ} (v : V) :
    (∑ sample : V → Fin C,
      (mrDeletedCollisionColors G sample v).ncard) ≤
      (mrDeletionWitnessTriples G v).card *
        C ^ (Fintype.card V - 2) := by
  classical
  calc
    (∑ sample : V → Fin C,
        (mrDeletedCollisionColors G sample v).ncard) ≤
        ∑ sample : V → Fin C,
          (mrRealizedDeletionWitnessFinset G v sample).card := by
      apply Finset.sum_le_sum
      intro sample _hsample
      exact mrDeletedCollisionColors_ncard_le_realizedWitnesses G v sample
    _ = (mrDeletionWitnessTriples G v).card *
        C ^ (Fintype.card V - 2) :=
      sum_card_mrRealizedDeletionWitnessFinset G v

/-- The structural deletion triples are bounded by the oriented nonedges in
`N(v)` times the maximum degree.  Each unordered nonedge has two orientations,
and after its distinguished first endpoint is fixed there are at most `Δ`
choices for the monochromatic neighbor witness. -/
lemma mrDeletionWitnessTriples_card_le
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) {Δ : ℕ}
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ) :
    (mrDeletionWitnessTriples G v).card ≤
      2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ := by
  classical
  let H := nonadjacentNeighborPairGraph G v
  let f : {t // t ∈ mrDeletionWitnessTriples G v} →
      Σ d : H.Dart, G.neighborSet d.fst := fun t ↦ by
    have ht := (mem_mrDeletionWitnessTriples G v t.1).mp t.2
    let d : H.Dart := ⟨(t.1.1.1, t.1.1.2), by
      change t.1.1.1 ≠ t.1.1.2 ∧ G.Adj v t.1.1.1 ∧
        G.Adj v t.1.1.2 ∧ ¬G.Adj t.1.1.1 t.1.1.2
      exact ⟨ht.1, ht.2.2.1, ht.2.2.2.1, ht.2.1⟩⟩
    exact ⟨d, ⟨t.1.2, ht.2.2.2.2⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hdart := congrArg (fun x ↦ x.1.toProd) hab
    have hz := congrArg (fun x ↦ x.2.1) hab
    dsimp only [f] at hdart hz
    exact Prod.ext hdart hz
  have hsigma :
      Fintype.card (Σ d : H.Dart, G.neighborSet d.fst) ≤
        Fintype.card H.Dart * Δ := by
    rw [Fintype.card_sigma]
    calc
      (∑ d : H.Dart, Fintype.card (G.neighborSet d.fst)) ≤
          ∑ _d : H.Dart, Δ := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [Set.fintypeCard_eq_ncard]
        exact hdegree d.fst
      _ = Fintype.card H.Dart * Δ := by simp
  have hedgeCard : H.edgeSet.ncard = H.edgeFinset.card := by
    calc
      H.edgeSet.ncard = Fintype.card H.edgeSet :=
        (Set.fintypeCard_eq_ncard H.edgeSet).symm
      _ = H.edgeFinset.card := H.card_edgeSet
  calc
    (mrDeletionWitnessTriples G v).card =
        Fintype.card {t // t ∈ mrDeletionWitnessTriples G v} :=
      (Fintype.card_coe (mrDeletionWitnessTriples G v)).symm
    _ ≤ Fintype.card (Σ d : H.Dart, G.neighborSet d.fst) :=
      Fintype.card_le_of_injective f hf
    _ ≤ Fintype.card H.Dart * Δ := hsigma
    _ = (2 * H.edgeFinset.card) * Δ := by
      rw [H.dart_card_eq_twice_card_edges]
    _ = 2 * H.edgeSet.ncard * Δ := by rw [hedgeCard]

/-- The deletion expectation in the graph-theoretic form used by the
Molloy--Reed argument. -/
lemma mrDeletedCollisionColors_expectation_upper_bound_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C Δ : ℕ} (v : V)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ) :
    (∑ sample : V → Fin C,
      (mrDeletedCollisionColors G sample v).ncard) ≤
      (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) *
        C ^ (Fintype.card V - 2) := by
  calc
    (∑ sample : V → Fin C,
        (mrDeletedCollisionColors G sample v).ncard) ≤
        (mrDeletionWitnessTriples G v).card *
          C ^ (Fintype.card V - 2) :=
      mrDeletedCollisionColors_expectation_upper_bound G v
    _ ≤ (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) *
        C ^ (Fintype.card V - 2) :=
      Nat.mul_le_mul_right _ (mrDeletionWitnessTriples_card_le G v hdegree)

/-- The direct deletion upper tail with structural witnesses replaced by the
graph parameters `B_v` and `Δ`. -/
lemma card_mrDeletionHighEvent_le_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C Δ : ℕ} (v : V) (s : ℕ)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ) :
    (eventFinset {sample : V → Fin C |
      s ≤ (mrDeletedCollisionColors G sample v).ncard}).card ≤
      (C.choose s *
        (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^ s) *
        C ^ (Fintype.card V - 3 * s) := by
  have hw := mrDeletionWitnessTriples_card_le G v hdegree
  calc
    (eventFinset {sample : V → Fin C |
        s ≤ (mrDeletedCollisionColors G sample v).ncard}).card ≤
        (C.choose s * (mrDeletionWitnessTriples G v).card ^ s) *
          C ^ (Fintype.card V - 3 * s) :=
      card_mrDeletionHighEvent_le G v s
    _ ≤ (C.choose s *
          (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^ s) *
        C ^ (Fintype.card V - 3 * s) := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw s))

/-- Failure of retention in the all-active experiment has a monochromatic
neighbor witness. -/
lemma exists_sameColor_neighbor_of_not_retained
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    (sample : V → Fin C) (w : V)
    (hw : w ∉ randomRetainedSet G (alwaysActiveSample sample)) :
    ∃ z, G.Adj w z ∧ sample z = sample w := by
  rw [mem_randomRetainedSet_alwaysActive] at hw
  push Not at hw
  exact hw

/-- Every tentative color that fails to survive twice has a certifiable
deletion witness. -/
lemma spoiledCollisionColors_subset_mrDeletedCollisionColors
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    (sample : V → Fin C) (v : V) :
    spoiledCollisionColors G (alwaysActiveSample sample) v ⊆
      mrDeletedCollisionColors G sample v := by
  intro a ha
  have htent := ha.1
  have hnotret := ha.2
  obtain ⟨p, q, hpq, hnonadj, hp, hq⟩ := htent
  rw [mem_tentativeNeighborColorFiber_alwaysActive] at hp hq
  by_cases hpRet : p ∈ randomRetainedSet G (alwaysActiveSample sample)
  · have hqNot : q ∉ randomRetainedSet G (alwaysActiveSample sample) := by
      intro hqRet
      apply hnotret
      refine ⟨p, q, hpq, ?_, ?_⟩
      · exact (mem_retainedNeighborColorFiber_alwaysActive
          G sample v p a).mpr ⟨
            (mem_randomRetainedSet_alwaysActive G sample p).mp hpRet,
            hp.1, hp.2⟩
      · exact (mem_retainedNeighborColorFiber_alwaysActive
          G sample v q a).mpr ⟨
            (mem_randomRetainedSet_alwaysActive G sample q).mp hqRet,
            hq.1, hq.2⟩
    obtain ⟨z, hqz, hzcolor⟩ :=
      exists_sameColor_neighbor_of_not_retained G sample q hqNot
    exact ⟨q, p, z, hpq.symm,
      (fun h ↦ hnonadj h.symm), hq.1, hp.1,
      hq.2, hp.2, hqz, hzcolor.trans hq.2⟩
  · obtain ⟨z, hpz, hzcolor⟩ :=
      exists_sameColor_neighbor_of_not_retained G sample p hpRet
    exact ⟨p, q, z, hpq, hnonadj, hp.1, hq.1,
      hp.2, hq.2, hpz, hzcolor.trans hp.2⟩

/-- A one-coordinate change preserves the deletion indicator of every color
except the old and new coordinate colors. -/
lemma mem_mrDeletedCollisionColors_iff_of_agreeAwayFrom
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} {x v : V} {a : Fin C}
    (heq : AgreeAwayFrom sample sample' x)
    (ha : a ≠ sample x) (ha' : a ≠ sample' x) :
    a ∈ mrDeletedCollisionColors G sample v ↔
      a ∈ mrDeletedCollisionColors G sample' v := by
  have transfer (s s' : V → Fin C) (hss' : AgreeAwayFrom s s' x)
      (hax : a ≠ s x)
      (hmem : a ∈ mrDeletedCollisionColors G s v) :
      a ∈ mrDeletedCollisionColors G s' v := by
    obtain ⟨p, q, z, hpq, hnonadj, hvp, hvq,
      hpcolor, hqcolor, hpz, hzcolor⟩ := hmem
    have hpx : p ≠ x := by
      intro h
      subst p
      exact hax hpcolor.symm
    have hqx : q ≠ x := by
      intro h
      subst q
      exact hax hqcolor.symm
    have hzx : z ≠ x := by
      intro h
      subst z
      exact hax hzcolor.symm
    exact ⟨p, q, z, hpq, hnonadj, hvp, hvq,
      (hss' p hpx).symm.trans hpcolor,
      (hss' q hqx).symm.trans hqcolor,
      hpz, (hss' z hzx).symm.trans hzcolor⟩
  constructor
  · exact transfer sample sample' heq ha
  · exact transfer sample' sample heq.symm ha'

/-- If membership in two finite sets agrees outside two exceptional points,
then either set has cardinality at most the other's cardinality plus two. -/
lemma ncard_le_ncard_add_two_of_mem_iff_outside
    {A : Type*} [Fintype A] (S T : Set A) (p q : A)
    (hiff : ∀ a, a ≠ p → a ≠ q → (a ∈ S ↔ a ∈ T)) :
    S.ncard ≤ T.ncard + 2 := by
  have hsubset : S ⊆ T ∪ {p, q} := by
    intro a ha
    by_cases hap : a = p
    · exact Or.inr (by simp [hap])
    by_cases haq : a = q
    · exact Or.inr (by simp [haq])
    · exact Or.inl ((hiff a hap haq).mp ha)
  have hpair : ({p, q} : Set A).ncard ≤ 2 := by
    by_cases hpq : p = q
    · simp [hpq]
    · exact le_of_eq (Set.ncard_pair hpq)
  calc
    S.ncard ≤ (T ∪ {p, q}).ncard := Set.ncard_le_ncard hsubset
    _ ≤ T.ncard + ({p, q} : Set A).ncard := Set.ncard_union_le _ _
    _ ≤ T.ncard + 2 := Nat.add_le_add_left hpair _

/-- A natural-valued statistic on a product is `c`-Lipschitz when changing
one coordinate changes its value by at most `c`. -/
def CoordinateLipschitz {A K : Type*}
    (X : (A → K) → ℕ) (c : ℕ) : Prop :=
  ∀ sample sample' x, AgreeAwayFrom sample sample' x →
    Nat.dist (X sample) (X sample') ≤ c

/-- The tentative-collision count in the diluted experiment is still
two-Lipschitz under a one-coordinate change. -/
lemma dilutedTentativeCollisionColors_ncard_coordinateLipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) {A C : ℕ}
    (active : Fin A) (v : V) :
    CoordinateLipschitz
      (fun sample : V → Fin A × Fin C ↦
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard) 2 := by
  intro sample sample' x heq
  have hlift :
      AgreeAwayFrom (dilutedSample active sample)
        (dilutedSample active sample') x := by
    intro y hy
    simp [dilutedSample, heq y hy]
  have hforward :
      (tentativeCollisionColors G (dilutedSample active sample) v).ncard ≤
        (tentativeCollisionColors G (dilutedSample active sample') v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha ha'
    exact mem_tentativeCollisionColors_iff_of_agreeAwayFrom_general
      G hlift ha ha'
  have hbackward :
      (tentativeCollisionColors G (dilutedSample active sample') v).ncard ≤
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha' ha
    exact mem_tentativeCollisionColors_iff_of_agreeAwayFrom_general
      G hlift.symm ha' ha
  change Nat.dist
    (tentativeCollisionColors G (dilutedSample active sample) v).ncard
    (tentativeCollisionColors G (dilutedSample active sample') v).ncard ≤ 2
  unfold Nat.dist
  omega

/-- Finite-product form of Talagrand certifiability.  If `X sample ≥ s`, at
most `r*s` coordinates can be exposed so that every assignment agreeing on
those coordinates still has value at least `s`. -/
def CoordinateCertifiable {A K : Type*} [Fintype A]
    (X : (A → K) → ℕ) (r : ℕ) : Prop :=
  ∀ sample s, s ≤ X sample →
    ∃ Q : Finset A, Q.card ≤ r * s ∧
      ∀ sample', (∀ x ∈ Q, sample' x = sample x) → s ≤ X sample'

/-- Replace the coordinates in `Q` of `base` by those of `source`. -/
def patchAssignment {A K : Type*} [DecidableEq A]
    (Q : Finset A) (base source : A → K) : A → K :=
  fun x ↦ if x ∈ Q then source x else base x

@[simp]
lemma patchAssignment_apply_mem {A K : Type*} [DecidableEq A]
    {Q : Finset A} {base source : A → K} {x : A} (hx : x ∈ Q) :
    patchAssignment Q base source x = source x := by
  simp [patchAssignment, hx]

@[simp]
lemma patchAssignment_apply_notMem {A K : Type*} [DecidableEq A]
    {Q : Finset A} {base source : A → K} {x : A} (hx : x ∉ Q) :
    patchAssignment Q base source x = base x := by
  simp [patchAssignment, hx]

/-- A one-coordinate Lipschitz bound telescopes over a finite set of patched
coordinates. -/
lemma CoordinateLipschitz.dist_patchAssignment_le
    {A K : Type*} [DecidableEq A]
    {X : (A → K) → ℕ} {c : ℕ}
    (hX : CoordinateLipschitz X c)
    (Q : Finset A) (base source : A → K) :
    Nat.dist (X base) (X (patchAssignment Q base source)) ≤ c * Q.card := by
  induction Q using Finset.induction_on with
  | empty =>
      have hempty : patchAssignment ∅ base source = base := by
        funext x
        simp [patchAssignment]
      rw [hempty, Nat.dist_self]
      simp
  | @insert x Q hx ih =>
      let middle := patchAssignment Q base source
      let final := patchAssignment (insert x Q) base source
      have hagree : AgreeAwayFrom middle final x := by
        intro y hy
        simp [middle, final, patchAssignment, hy]
      have hstep : Nat.dist (X middle) (X final) ≤ c := hX middle final x hagree
      have htriangle : Nat.dist (X base) (X final) ≤
          Nat.dist (X base) (X middle) + Nat.dist (X middle) (X final) :=
        Nat.dist.triangle_inequality _ _ _
      change Nat.dist (X base) (X final) ≤ c * (insert x Q).card
      have hmiddle : Nat.dist (X base) (X middle) ≤ c * Q.card := ih
      calc
        Nat.dist (X base) (X final) ≤
            Nat.dist (X base) (X middle) + Nat.dist (X middle) (X final) :=
          htriangle
        _ ≤ c * Q.card + c := Nat.add_le_add hmiddle hstep
        _ = c * (insert x Q).card := by
          rw [Finset.card_insert_of_notMem hx]
          ring

/-- Certifiability plus Lipschitz continuity separates a low outcome from a
high outcome on the high outcome's certificate: if their statistic values
are separated by `t`, then the certificate contains enough changed
coordinates to pay at least `t/c`. -/
lemma exists_certificate_with_lipschitz_separation
    {A K : Type*} [Fintype A] [DecidableEq A]
    {X : (A → K) → ℕ} {c r : ℕ}
    (hLip : CoordinateLipschitz X c)
    (hCert : CoordinateCertifiable X r)
    (low high : A → K) {s t : ℕ}
    (hhigh : s ≤ X high) (hlow : X low + t ≤ s) :
    ∃ Q : Finset A, Q.card ≤ r * s ∧ t ≤ c * Q.card ∧
      ∀ sample', (∀ x ∈ Q, sample' x = high x) → s ≤ X sample' := by
  obtain ⟨Q, hQcard, hQcert⟩ := hCert high s hhigh
  refine ⟨Q, hQcard, ?_, hQcert⟩
  let patched := patchAssignment Q low high
  have hpatched : s ≤ X patched := by
    apply hQcert patched
    intro x hx
    exact patchAssignment_apply_mem hx
  have hdistLower : t ≤ Nat.dist (X low) (X patched) := by
    have hle : X low ≤ X patched := by omega
    rw [Nat.dist_eq_sub_of_le hle]
    omega
  exact hdistLower.trans (hLip.dist_patchAssignment_le Q low high)

/-- The number of tentative collision colors is `2`-Lipschitz, exactly as in
the bounded-difference half of Molloy--Reed Lemma 10.7. -/
lemma mrTentativeCollisionColors_ncard_coordinateLipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V) :
    CoordinateLipschitz
      (fun sample : V → Fin C ↦
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard) 2 := by
  intro sample sample' x heq
  have hforward :
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard ≤
        (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha ha'
    exact mem_tentativeCollisionColors_iff_of_agreeAwayFrom G heq ha ha'
  have hbackward :
      (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard ≤
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha' ha
    exact mem_tentativeCollisionColors_iff_of_agreeAwayFrom
      G heq.symm ha' ha
  change Nat.dist
    (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard
    (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard ≤ 2
  unfold Nat.dist
  omega

/-- Tentative collision colors only inspect the colors on `N(v)`. -/
lemma tentativeCollisionColors_eq_of_eqOn_neighborSet
    {V : Type*} (G : SimpleGraph V) {C : ℕ}
    {sample sample' : V → Fin C} (v : V)
    (h : ∀ w, G.Adj v w → sample w = sample' w) :
    tentativeCollisionColors G (alwaysActiveSample sample) v =
      tentativeCollisionColors G (alwaysActiveSample sample') v := by
  ext a
  constructor
  · rintro ⟨p, q, hpq, hnonadj, hp, hq⟩
    rw [mem_tentativeNeighborColorFiber_alwaysActive] at hp hq
    exact ⟨p, q, hpq, hnonadj,
      (mem_tentativeNeighborColorFiber_alwaysActive G sample' v p a).mpr
        ⟨hp.1, (h p hp.1).symm.trans hp.2⟩,
      (mem_tentativeNeighborColorFiber_alwaysActive G sample' v q a).mpr
        ⟨hq.1, (h q hq.1).symm.trans hq.2⟩⟩
  · rintro ⟨p, q, hpq, hnonadj, hp, hq⟩
    rw [mem_tentativeNeighborColorFiber_alwaysActive] at hp hq
    exact ⟨p, q, hpq, hnonadj,
      (mem_tentativeNeighborColorFiber_alwaysActive G sample v p a).mpr
        ⟨hp.1, h p hp.1 |>.trans hp.2⟩,
      (mem_tentativeNeighborColorFiber_alwaysActive G sample v q a).mpr
        ⟨hq.1, h q hq.1 |>.trans hq.2⟩⟩

/-- Extend an assignment on `N(v)` to all vertices, using `default` outside
the neighborhood. -/
noncomputable def extendNeighborAssignment
    {V K : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] (default : K)
    (assignment : G.neighborFinset v → K) : V → K :=
  by
    classical
    exact fun x ↦ if hx : G.Adj v x then
      assignment ⟨x, by simpa using hx⟩ else default

@[simp]
lemma extendNeighborAssignment_apply_of_adj
    {V K : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] (default : K)
    (assignment : G.neighborFinset v → K) {x : V} (hx : G.Adj v x) :
    extendNeighborAssignment G v default assignment x =
      assignment ⟨x, by simpa using hx⟩ := by
  simp [extendNeighborAssignment, hx]

/-- Reindex neighborhood assignments by `Fin |N(v)|`; this is the exact
finite product to which the bounded-differences theorem is applied. -/
noncomputable def mrTentativeFinStatistic
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    (v : V) [Fintype (G.neighborSet v)] (default : Fin C) :
    (Fin (Fintype.card (G.neighborFinset v)) → Fin C) → ℕ :=
  fun z ↦
    (tentativeCollisionColors G
      (alwaysActiveSample
        (extendNeighborAssignment G v default
          (fun x ↦ z (Fintype.equivFin (G.neighborFinset v) x)))) v).ncard

/-- Restricting a full assignment to `N(v)` and extending it with an arbitrary
outside default does not change its tentative collision count. -/
lemma mrTentativeFinStatistic_restrict
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    (v : V) [Fintype (G.neighborSet v)]
    (default : Fin C) (sample : V → Fin C) :
    mrTentativeFinStatistic G v default
        (fun i ↦ sample ((Fintype.equivFin (G.neighborFinset v)).symm i).1) =
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard := by
  classical
  unfold mrTentativeFinStatistic
  apply congrArg Set.ncard
  apply tentativeCollisionColors_eq_of_eqOn_neighborSet G v
  intro w hw
  simp [extendNeighborAssignment, hw]

/-- The neighborhood-reindexed tentative statistic is real-valued
`2`-Lipschitz. -/
lemma mrTentativeFinStatistic_realCoordinateLipschitz
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    (v : V) [Fintype (G.neighborSet v)] (default : Fin C) :
    RealCoordinateLipschitzFin
      (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)) 2 := by
  classical
  intro z z' i hzz'
  let e := Fintype.equivFin (G.neighborFinset v)
  let sample := extendNeighborAssignment G v default (fun x ↦ z (e x))
  let sample' := extendNeighborAssignment G v default (fun x ↦ z' (e x))
  have hagree : AgreeAwayFrom sample sample' (e.symm i).1 := by
    intro x hx
    by_cases hxv : G.Adj v x
    · have hmem : x ∈ G.neighborFinset v := by simpa using hxv
      simp only [sample, sample', extendNeighborAssignment_apply_of_adj
          G v default _ hxv]
      apply hzz' (e ⟨x, hmem⟩)
      intro hei
      apply hx
      have hsub : (⟨x, hmem⟩ : G.neighborFinset v) = e.symm i := by
        apply e.injective
        simpa using hei
      exact congrArg Subtype.val hsub
    · simp [sample, sample', extendNeighborAssignment, hxv]
  have hnat :=
    mrTentativeCollisionColors_ncard_coordinateLipschitz G v
      sample sample' (e.symm i).1 hagree
  change |(mrTentativeFinStatistic G v default z : ℝ) -
    (mrTentativeFinStatistic G v default z' : ℝ)| ≤ 2
  change |((tentativeCollisionColors G (alwaysActiveSample sample) v).ncard : ℝ) -
    ((tentativeCollisionColors G (alwaysActiveSample sample') v).ncard : ℝ)| ≤ 2
  change Nat.dist
    (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard
    (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard ≤ 2 at hnat
  have hforward :
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard ≤
        (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard + 2 := by
    unfold Nat.dist at hnat
    omega
  have hbackward :
      (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard ≤
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard + 2 := by
    unfold Nat.dist at hnat
    omega
  have hforwardReal :
      ((tentativeCollisionColors G (alwaysActiveSample sample) v).ncard : ℝ) ≤
        (tentativeCollisionColors G (alwaysActiveSample sample') v).ncard + 2 := by
    exact_mod_cast hforward
  have hbackwardReal :
      ((tentativeCollisionColors G (alwaysActiveSample sample') v).ncard : ℝ) ≤
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard + 2 := by
    exact_mod_cast hbackward
  rw [abs_le]
  constructor <;> linarith

/-- The neighborhood-reindexed tentative statistic for the diluted random
round. -/
noncomputable def dilutedTentativeFinStatistic
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A C : ℕ} (active : Fin A) (v : V) [Fintype (G.neighborSet v)]
    (default : Fin A × Fin C) :
    (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) → ℕ :=
  fun z ↦
    (tentativeCollisionColors G
      (dilutedSample active
        (extendNeighborAssignment G v default
          (fun x ↦ z (Fintype.equivFin (G.neighborFinset v) x)))) v).ncard

/-- Restriction to the neighborhood preserves the diluted tentative
collision count. -/
lemma dilutedTentativeFinStatistic_restrict
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A C : ℕ} (active : Fin A) (v : V) [Fintype (G.neighborSet v)]
    (default : Fin A × Fin C) (sample : V → Fin A × Fin C) :
    dilutedTentativeFinStatistic G active v default
        (fun i ↦ sample ((Fintype.equivFin (G.neighborFinset v)).symm i).1) =
      (tentativeCollisionColors G (dilutedSample active sample) v).ncard := by
  classical
  unfold dilutedTentativeFinStatistic
  apply congrArg Set.ncard
  apply tentativeCollisionColors_eq_of_eqOn_neighborSet_general G v
  intro w hw
  simp [extendNeighborAssignment, dilutedSample, hw]

/-- The reindexed diluted tentative statistic is real-valued
two-Lipschitz. -/
lemma dilutedTentativeFinStatistic_realCoordinateLipschitz
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A C : ℕ} (active : Fin A) (v : V) [Fintype (G.neighborSet v)]
    (default : Fin A × Fin C) :
    RealCoordinateLipschitzFin
      (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ)) 2 := by
  classical
  intro z z' i hzz'
  let e := Fintype.equivFin (G.neighborFinset v)
  let sample := extendNeighborAssignment G v default (fun x ↦ z (e x))
  let sample' := extendNeighborAssignment G v default (fun x ↦ z' (e x))
  have hagree : AgreeAwayFrom sample sample' (e.symm i).1 := by
    intro x hx
    by_cases hxv : G.Adj v x
    · have hmem : x ∈ G.neighborFinset v := by simpa using hxv
      simp only [sample, sample', extendNeighborAssignment_apply_of_adj
          G v default _ hxv]
      apply hzz' (e ⟨x, hmem⟩)
      intro hei
      apply hx
      have hsub : (⟨x, hmem⟩ : G.neighborFinset v) = e.symm i := by
        apply e.injective
        simpa using hei
      exact congrArg Subtype.val hsub
    · simp [sample, sample', extendNeighborAssignment, hxv]
  have hnat :=
    dilutedTentativeCollisionColors_ncard_coordinateLipschitz G active v
      sample sample' (e.symm i).1 hagree
  change |(dilutedTentativeFinStatistic G active v default z : ℝ) -
    (dilutedTentativeFinStatistic G active v default z' : ℝ)| ≤ 2
  change |((tentativeCollisionColors G
      (dilutedSample active sample) v).ncard : ℝ) -
    ((tentativeCollisionColors G
      (dilutedSample active sample') v).ncard : ℝ)| ≤ 2
  change Nat.dist
    (tentativeCollisionColors G (dilutedSample active sample) v).ncard
    (tentativeCollisionColors G (dilutedSample active sample') v).ncard ≤ 2 at hnat
  have hforward :
      (tentativeCollisionColors G (dilutedSample active sample) v).ncard ≤
        (tentativeCollisionColors G (dilutedSample active sample') v).ncard + 2 := by
    unfold Nat.dist at hnat
    omega
  have hbackward :
      (tentativeCollisionColors G (dilutedSample active sample') v).ncard ≤
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard + 2 := by
    unfold Nat.dist at hnat
    omega
  have hforwardReal :
      ((tentativeCollisionColors G (dilutedSample active sample) v).ncard : ℝ) ≤
        (tentativeCollisionColors G
          (dilutedSample active sample') v).ncard + 2 := by
    exact_mod_cast hforward
  have hbackwardReal :
      ((tentativeCollisionColors G
          (dilutedSample active sample') v).ncard : ℝ) ≤
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard + 2 := by
    exact_mod_cast hbackward
  rw [abs_le]
  constructor <;> linarith

/-- Finite McDiarmid lower tail for the neighborhood-reindexed tentative
collision statistic.  A mean margin of `ε` above the integral threshold `a`
makes every strict shortfall assignment part of the McDiarmid lower tail. -/
lemma card_mrTentativeFinStatistic_shortfall_le_exp
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    [Nonempty (Fin C)] (v : V) [Fintype (G.neighborSet v)]
    (hneighbor : 0 < Fintype.card (G.neighborFinset v))
    (default : Fin C) (a : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (a : ℝ) + ε ≤
      finiteAverage (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ))) :
    ((Finset.univ.filter fun z :
        Fin (Fintype.card (G.neighborFinset v)) → Fin C ↦
          mrTentativeFinStatistic G v default z < a).card : ℝ) /
        Fintype.card
          (Fin (Fintype.card (G.neighborFinset v)) → Fin C) ≤
      Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  classical
  let f :
      (Fin (Fintype.card (G.neighborFinset v)) → Fin C) → ℝ :=
    fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)
  have htail := finite_boundedDifferences_lowerTail
    (Fintype.card (G.neighborFinset v)) f
    (c := (2 : ℝ)) (ε := ε) (by norm_num) hε hneighbor
    (mrTentativeFinStatistic_realCoordinateLipschitz G v default)
  have hsubset :
      (Finset.univ.filter fun z :
        Fin (Fintype.card (G.neighborFinset v)) → Fin C ↦
          mrTentativeFinStatistic G v default z < a) ⊆
        finiteLowerTail f ε := by
    intro z hz
    have hzlt : mrTentativeFinStatistic G v default z < a :=
      (Finset.mem_filter.mp hz).2
    have hzltReal :
        (mrTentativeFinStatistic G v default z : ℝ) < a := by
      exact_mod_cast hzlt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [f]
    linarith
  have hcard := Finset.card_le_card hsubset
  have hden :
      (0 : ℝ) < Fintype.card
        (Fin (Fintype.card (G.neighborFinset v)) → Fin C) := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le).trans htail

/-- The same McDiarmid bound on the original full product sample space.  The
tentative statistic depends only on `N(v)`, so the outside-coordinate cylinder
factor cancels exactly from numerator and denominator. -/
lemma card_mrTentativeCollisionShortfallSet_le_exp
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    [Nonempty (Fin C)] (v : V) [Fintype (G.neighborSet v)]
    (hneighbor : 0 < Fintype.card (G.neighborFinset v))
    (default : Fin C) (a : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (a : ℝ) + ε ≤
      finiteAverage (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ))) :
    ((eventFinset {sample : V → Fin C |
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a}).card : ℝ) /
        Fintype.card (V → Fin C) ≤
      Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  classical
  let S := G.neighborFinset v
  let e := Fintype.equivFin S
  let assignmentEquiv :
      (S → Fin C) ≃
        (Fin (Fintype.card (G.neighborFinset v)) → Fin C) := {
    toFun g := fun i ↦ g (e.symm i)
    invFun z := fun x ↦ z (e x)
    left_inv g := by funext x; simp
    right_inv z := by funext i; simp
  }
  let P : (S → Fin C) → Prop := fun g ↦
    mrTentativeFinStatistic G v default (assignmentEquiv g) < a
  let E : Set (V → Fin C) :=
    {sample |
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a}
  have hE (sample : V → Fin C) :
      sample ∈ E ↔ P (fun x : S ↦ sample x.1) := by
    change
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a ↔
        mrTentativeFinStatistic G v default
          (fun i ↦ sample (e.symm i).1) < a
    rw [mrTentativeFinStatistic_restrict]
  have hratio := eventRatio_eq_of_restriction S P E hE
  have hlocalCard :
      Set.ncard {g : S → Fin C | P g} =
        (Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin C ↦
            mrTentativeFinStatistic G v default z < a).card := by
    calc
      Set.ncard {g : S → Fin C | P g} =
          Set.ncard {z :
            Fin (Fintype.card (G.neighborFinset v)) → Fin C |
              mrTentativeFinStatistic G v default z < a} := by
        simpa only [P] using ncard_setOf_comp_equiv assignmentEquiv
          (fun z ↦ mrTentativeFinStatistic G v default z < a)
      _ = (Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin C ↦
            mrTentativeFinStatistic G v default z < a).card := by
        rw [Set.ncard_eq_toFinset_card']
        congr 1
        ext z
        simp
  have hlocalTail := card_mrTentativeFinStatistic_shortfall_le_exp
    G v hneighbor default a hε hmargin
  calc
    ((eventFinset {sample : V → Fin C |
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a}).card : ℝ) /
        Fintype.card (V → Fin C) =
        (E.ncard : ℝ) / Fintype.card (V → Fin C) := by
      rw [card_eventFinset_eq_ncard]
    _ = (Set.ncard {g : S → Fin C | P g} : ℝ) /
        Fintype.card (S → Fin C) := hratio
    _ = ((Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin C ↦
            mrTentativeFinStatistic G v default z < a).card : ℝ) /
        Fintype.card
          (Fin (Fintype.card (G.neighborFinset v)) → Fin C) := by
      rw [hlocalCard]
      congr 1
      exact_mod_cast Fintype.card_congr assignmentEquiv
    _ ≤ Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := hlocalTail

/-- Finite McDiarmid lower tail for the neighborhood-reindexed diluted
tentative statistic. -/
lemma card_dilutedTentativeFinStatistic_shortfall_le_exp
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A C : ℕ} [Nonempty (Fin A × Fin C)] (active : Fin A)
    (v : V) [Fintype (G.neighborSet v)]
    (hneighbor : 0 < Fintype.card (G.neighborFinset v))
    (default : Fin A × Fin C) (a : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (a : ℝ) + ε ≤
      finiteAverage
        (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ))) :
    ((Finset.univ.filter fun z :
        Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C ↦
          dilutedTentativeFinStatistic G active v default z < a).card : ℝ) /
        Fintype.card
          (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) ≤
      Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  classical
  let f :
      (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) → ℝ :=
    fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ)
  have htail := finite_boundedDifferences_lowerTail
    (Fintype.card (G.neighborFinset v)) f
    (c := (2 : ℝ)) (ε := ε) (by norm_num) hε hneighbor
    (dilutedTentativeFinStatistic_realCoordinateLipschitz
      G active v default)
  have hsubset :
      (Finset.univ.filter fun z :
        Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C ↦
          dilutedTentativeFinStatistic G active v default z < a) ⊆
        finiteLowerTail f ε := by
    intro z hz
    have hzlt : dilutedTentativeFinStatistic G active v default z < a :=
      (Finset.mem_filter.mp hz).2
    have hzltReal :
        (dilutedTentativeFinStatistic G active v default z : ℝ) < a := by
      exact_mod_cast hzlt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [f]
    linarith
  have hcard := Finset.card_le_card hsubset
  have hden :
      (0 : ℝ) < Fintype.card
        (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le).trans htail

/-- The diluted McDiarmid bound on the original full product sample space.
The outside-coordinate cylinder factor cancels exactly. -/
lemma card_dilutedTentativeCollisionShortfallSet_le_exp
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {A C : ℕ} [Nonempty (Fin A × Fin C)] (active : Fin A)
    (v : V) [Fintype (G.neighborSet v)]
    (hneighbor : 0 < Fintype.card (G.neighborFinset v))
    (default : Fin A × Fin C) (a : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (a : ℝ) + ε ≤
      finiteAverage
        (fun z ↦ (dilutedTentativeFinStatistic G active v default z : ℝ))) :
    ((eventFinset {sample : V → Fin A × Fin C |
        (tentativeCollisionColors G
          (dilutedSample active sample) v).ncard < a}).card : ℝ) /
        Fintype.card (V → Fin A × Fin C) ≤
      Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  classical
  let S := G.neighborFinset v
  let e := Fintype.equivFin S
  let assignmentEquiv :
      (S → Fin A × Fin C) ≃
        (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) := {
    toFun g := fun i ↦ g (e.symm i)
    invFun z := fun x ↦ z (e x)
    left_inv g := by funext x; simp
    right_inv z := by funext i; simp
  }
  let P : (S → Fin A × Fin C) → Prop := fun g ↦
    dilutedTentativeFinStatistic G active v default (assignmentEquiv g) < a
  let E : Set (V → Fin A × Fin C) :=
    {sample |
      (tentativeCollisionColors G
        (dilutedSample active sample) v).ncard < a}
  have hE (sample : V → Fin A × Fin C) :
      sample ∈ E ↔ P (fun x : S ↦ sample x.1) := by
    change
      (tentativeCollisionColors G
        (dilutedSample active sample) v).ncard < a ↔
        dilutedTentativeFinStatistic G active v default
          (fun i ↦ sample (e.symm i).1) < a
    rw [dilutedTentativeFinStatistic_restrict]
  have hratio := eventRatio_eq_of_restriction S P E hE
  have hlocalCard :
      Set.ncard {g : S → Fin A × Fin C | P g} =
        (Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C ↦
            dilutedTentativeFinStatistic G active v default z < a).card := by
    calc
      Set.ncard {g : S → Fin A × Fin C | P g} =
          Set.ncard {z :
            Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C |
              dilutedTentativeFinStatistic G active v default z < a} := by
        simpa only [P] using ncard_setOf_comp_equiv assignmentEquiv
          (fun z ↦ dilutedTentativeFinStatistic G active v default z < a)
      _ = (Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C ↦
            dilutedTentativeFinStatistic G active v default z < a).card := by
        rw [Set.ncard_eq_toFinset_card']
        congr 1
        ext z
        simp
  have hlocalTail := card_dilutedTentativeFinStatistic_shortfall_le_exp
    G active v hneighbor default a hε hmargin
  calc
    ((eventFinset {sample : V → Fin A × Fin C |
        (tentativeCollisionColors G
          (dilutedSample active sample) v).ncard < a}).card : ℝ) /
        Fintype.card (V → Fin A × Fin C) =
        (E.ncard : ℝ) / Fintype.card (V → Fin A × Fin C) := by
      rw [card_eventFinset_eq_ncard]
    _ = (Set.ncard {g : S → Fin A × Fin C | P g} : ℝ) /
        Fintype.card (S → Fin A × Fin C) := hratio
    _ = ((Finset.univ.filter fun z :
          Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C ↦
            dilutedTentativeFinStatistic G active v default z < a).card : ℝ) /
        Fintype.card
          (Fin (Fintype.card (G.neighborFinset v)) → Fin A × Fin C) := by
      rw [hlocalCard]
      congr 1
      exact_mod_cast Fintype.card_congr assignmentEquiv
    _ ≤ Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := hlocalTail

/-- The mean of the neighborhood-reindexed tentative statistic is exactly the
uniform mean on the original product sample space. -/
lemma mrTentativeFinStatistic_finiteAverage_eq
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {C : ℕ}
    [Nonempty (Fin C)] (v : V) [Fintype (G.neighborSet v)]
    (default : Fin C) :
    finiteAverage (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)) =
      (∑ sample : V → Fin C,
        ((tentativeCollisionColors G
          (alwaysActiveSample sample) v).ncard : ℝ)) /
        Fintype.card (V → Fin C) := by
  classical
  let S := G.neighborFinset v
  let e := Fintype.equivFin S
  let assignmentEquiv :
      (S → Fin C) ≃
        (Fin (Fintype.card (G.neighborFinset v)) → Fin C) := {
    toFun g := fun i ↦ g (e.symm i)
    invFun z := fun x ↦ z (e x)
    left_inv g := by funext x; simp
    right_inv z := by funext i; simp
  }
  let X : (S → Fin C) → ℕ := fun g ↦
    mrTentativeFinStatistic G v default (assignmentEquiv g)
  have hrestrict := finiteAverage_eq_of_restriction S X
  calc
    finiteAverage (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)) =
        finiteAverage (fun g : S → Fin C ↦ (X g : ℝ)) := by
      symm
      simpa only [X] using finiteAverage_comp_equiv assignmentEquiv
        (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ))
    _ = (∑ sample : V → Fin C,
          (X (fun x : S ↦ sample x.1) : ℝ)) /
        Fintype.card (V → Fin C) := hrestrict
    _ = (∑ sample : V → Fin C,
          ((tentativeCollisionColors G
            (alwaysActiveSample sample) v).ncard : ℝ)) /
        Fintype.card (V → Fin C) := by
      congr 1
      apply Finset.sum_congr rfl
      intro sample _hsample
      change
        (mrTentativeFinStatistic G v default
          (fun i ↦ sample (e.symm i).1) : ℝ) = _
      rw [mrTentativeFinStatistic_restrict]

/-- The tentative-collision count is `2`-certifiable: expose the two
nonadjacent neighbors witnessing each selected color. -/
lemma mrTentativeCollisionColors_ncard_coordinateCertifiable
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V) :
    CoordinateCertifiable
      (fun sample : V → Fin C ↦
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard) 2 := by
  classical
  intro sample s hs
  have hcard : Fintype.card (Fin s) ≤
      Fintype.card
        (tentativeCollisionColors G (alwaysActiveSample sample) v) := by
    simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hs
  obtain ⟨colors : Fin s ↪
      tentativeCollisionColors G (alwaysActiveSample sample) v⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  have hwitness (i : Fin s) : ∃ p q : V,
      p ≠ q ∧ ¬G.Adj p q ∧
      p ∈ tentativeNeighborColorFiber G (alwaysActiveSample sample) v (colors i).1 ∧
      q ∈ tentativeNeighborColorFiber G (alwaysActiveSample sample) v (colors i).1 :=
    (colors i).2
  choose p q hdata using hwitness
  let Q : Finset V := Finset.univ.biUnion fun i : Fin s ↦ {p i, q i}
  have hpair (i : Fin s) : ({p i, q i} : Finset V).card ≤ 2 := by
    calc
      ({p i, q i} : Finset V).card ≤ ({q i} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hQcard : Q.card ≤ 2 * s := by
    calc
      Q.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin s)),
          ({p i, q i} : Finset V).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin s)), 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hpair i
      _ = 2 * s := by simp [Nat.mul_comm]
  refine ⟨Q, hQcard, ?_⟩
  intro sample' hagree
  let selected : Fin s → Fin C := fun i ↦ (colors i).1
  have hselectedInjective : Function.Injective selected := by
    intro i j hij
    apply colors.injective
    exact Subtype.ext hij
  have hselected (i : Fin s) :
      selected i ∈
        tentativeCollisionColors G (alwaysActiveSample sample') v := by
    rcases hdata i with ⟨hpq, hnonadj, hp, hq⟩
    rw [mem_tentativeNeighborColorFiber_alwaysActive] at hp hq
    have hpQ : p i ∈ Q := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    have hqQ : q i ∈ Q := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    exact ⟨p i, q i, hpq, hnonadj,
      (mem_tentativeNeighborColorFiber_alwaysActive
        G sample' v (p i) (selected i)).mpr
          ⟨hp.1, (hagree (p i) hpQ).trans hp.2⟩,
      (mem_tentativeNeighborColorFiber_alwaysActive
        G sample' v (q i) (selected i)).mpr
          ⟨hq.1, (hagree (q i) hqQ).trans hq.2⟩⟩
  have hrange : Set.range selected ⊆
      tentativeCollisionColors G (alwaysActiveSample sample') v := by
    rintro a ⟨i, rfl⟩
    exact hselected i
  calc
    s = (Set.range selected).ncard := by
      rw [Set.ncard_range_of_injective hselectedInjective]
      exact (Nat.card_fin s).symm
    _ ≤ (tentativeCollisionColors G
        (alwaysActiveSample sample') v).ncard :=
      Set.ncard_le_ncard hrange

/-- The number of spoiled collision colors is also `2`-Lipschitz: one changed
coordinate can affect only its old and new colors. -/
lemma mrSpoiledCollisionColors_ncard_coordinateLipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V) :
    CoordinateLipschitz
      (fun sample : V → Fin C ↦
        (spoiledCollisionColors G (alwaysActiveSample sample) v).ncard) 2 := by
  intro sample sample' x heq
  have hforward :
      (spoiledCollisionColors G (alwaysActiveSample sample) v).ncard ≤
        (spoiledCollisionColors G (alwaysActiveSample sample') v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha ha'
    exact mem_spoiledCollisionColors_iff_of_agreeAwayFrom G heq ha ha'
  have hbackward :
      (spoiledCollisionColors G (alwaysActiveSample sample') v).ncard ≤
        (spoiledCollisionColors G (alwaysActiveSample sample) v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha' ha
    exact mem_spoiledCollisionColors_iff_of_agreeAwayFrom
      G heq.symm ha' ha
  change Nat.dist
    (spoiledCollisionColors G (alwaysActiveSample sample) v).ncard
    (spoiledCollisionColors G (alwaysActiveSample sample') v).ncard ≤ 2
  unfold Nat.dist
  omega

/-- Molloy--Reed's actual deletion variable is `2`-Lipschitz. -/
lemma mrDeletedCollisionColors_ncard_coordinateLipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V) :
    CoordinateLipschitz
      (fun sample : V → Fin C ↦
        (mrDeletedCollisionColors G sample v).ncard) 2 := by
  intro sample sample' x heq
  have hforward :
      (mrDeletedCollisionColors G sample v).ncard ≤
        (mrDeletedCollisionColors G sample' v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha ha'
    exact mem_mrDeletedCollisionColors_iff_of_agreeAwayFrom G heq ha ha'
  have hbackward :
      (mrDeletedCollisionColors G sample' v).ncard ≤
        (mrDeletedCollisionColors G sample v).ncard + 2 := by
    apply ncard_le_ncard_add_two_of_mem_iff_outside
    intro a ha' ha
    exact mem_mrDeletedCollisionColors_iff_of_agreeAwayFrom
      G heq.symm ha' ha
  change Nat.dist
    (mrDeletedCollisionColors G sample v).ncard
    (mrDeletedCollisionColors G sample' v).ncard ≤ 2
  unfold Nat.dist
  omega

/-- The deletion variable is `3`-certifiable.  Each counted color is witnessed
by two nonadjacent neighbors carrying that color and one same-colored conflict
neighbor. -/
lemma mrDeletedCollisionColors_ncard_coordinateCertifiable
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C : ℕ} (v : V) :
    CoordinateCertifiable
      (fun sample : V → Fin C ↦
        (mrDeletedCollisionColors G sample v).ncard) 3 := by
  classical
  intro sample s hs
  have hcard : Fintype.card (Fin s) ≤
      Fintype.card (mrDeletedCollisionColors G sample v) := by
    simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hs
  obtain ⟨colors : Fin s ↪ mrDeletedCollisionColors G sample v⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  have hwitness (i : Fin s) : ∃ p q z : V,
      p ≠ q ∧ ¬G.Adj p q ∧
      G.Adj v p ∧ G.Adj v q ∧
      sample p = (colors i).1 ∧ sample q = (colors i).1 ∧
      G.Adj p z ∧ sample z = (colors i).1 :=
    (colors i).2
  choose p q z hdata using hwitness
  let Q : Finset V := Finset.univ.biUnion fun i : Fin s ↦ {p i, q i, z i}
  have htriple (i : Fin s) : ({p i, q i, z i} : Finset V).card ≤ 3 := by
    calc
      ({p i, q i, z i} : Finset V).card ≤
          ({q i, z i} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (({z i} : Finset V).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  have hQcard : Q.card ≤ 3 * s := by
    calc
      Q.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin s)),
          ({p i, q i, z i} : Finset V).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin s)), 3 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact htriple i
      _ = 3 * s := by simp [Nat.mul_comm]
  refine ⟨Q, hQcard, ?_⟩
  intro sample' hagree
  let selected : Fin s → Fin C := fun i ↦ (colors i).1
  have hselectedInjective : Function.Injective selected := by
    intro i j hij
    apply colors.injective
    exact Subtype.ext hij
  have hselected (i : Fin s) :
      selected i ∈ mrDeletedCollisionColors G sample' v := by
    rcases hdata i with ⟨hpq, hnonadj, hvp, hvq,
      hpcolor, hqcolor, hpz, hzcolor⟩
    have hpQ : p i ∈ Q := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    have hqQ : q i ∈ Q := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    have hzQ : z i ∈ Q := by
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    exact ⟨p i, q i, z i, hpq, hnonadj, hvp, hvq,
      (hagree (p i) hpQ).trans hpcolor,
      (hagree (q i) hqQ).trans hqcolor,
      hpz, (hagree (z i) hzQ).trans hzcolor⟩
  have hrange : Set.range selected ⊆ mrDeletedCollisionColors G sample' v := by
    rintro a ⟨i, rfl⟩
    exact hselected i
  calc
    s = (Set.range selected).ncard := by
      rw [Set.ncard_range_of_injective hselectedInjective]
      exact (Nat.card_fin s).symm
    _ ≤ (mrDeletedCollisionColors G sample' v).ncard :=
      Set.ncard_le_ncard hrange

/-- Every repeated retained color was already a tentative collision color.
The two retained witnesses cannot be adjacent, since the retained coloring is
proper. -/
lemma retainedCollisionColors_subset_tentativeCollisionColors
    {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) :
    retainedCollisionColors G sample v ⊆
      tentativeCollisionColors G sample v := by
  rintro a ⟨x, y, hxy, hx, hy⟩
  have hnonadj : ¬G.Adj x y := by
    intro hadj
    have hneq := hx.1.2 y hadj hy.1.1
    exact hneq ((hy.2.2).trans (hx.2.2).symm)
  exact ⟨x, y, hxy, hnonadj,
    ⟨hx.1.1, hx.2.1, hx.2.2⟩,
    ⟨hy.1.1, hy.2.1, hy.2.2⟩⟩

/-- The retained-cylinder calculation is therefore also a lower bound for
the source's tentative-collision statistic. -/
lemma tentativeCollisionColors_expectation_lower_bound_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C Δ : ℕ} (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj]
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (hambient : (3 * Δ - 2) + 2 ≤ Fintype.card V) :
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
        ((C - 1) ^ (3 * Δ - 2) *
          C ^ (Fintype.card V - (3 * Δ - 2) - 2)) ≤
      ∑ sample : V → Fin C,
        (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard := by
  have hretained := retainedCollisionColors_expectation_lower_bound_of_degree
    (C := C) (Δ := Δ) G v hdegree hambient
  apply hretained.trans
  apply Finset.sum_le_sum
  intro sample _hsample
  exact Set.ncard_le_ncard
    (retainedCollisionColors_subset_tentativeCollisionColors
      G (alwaysActiveSample sample) v)
    (Set.toFinite _)

/-- The retained-pair cylinder count, normalized by the full product size,
is a lower bound for the mean of the neighborhood-reindexed tentative
statistic. -/
lemma mrTentativeFinStatistic_finiteAverage_lower_bound_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C Δ : ℕ} [Nonempty (Fin C)] (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj]
    [Fintype (G.neighborSet v)] (default : Fin C)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (hambient : (3 * Δ - 2) + 2 ≤ Fintype.card V) :
    ((C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
        ((C - 1) ^ (3 * Δ - 2) *
          C ^ (Fintype.card V - (3 * Δ - 2) - 2)) : ℕ) : ℝ) /
        Fintype.card (V → Fin C) ≤
      finiteAverage
        (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)) := by
  have hsum := tentativeCollisionColors_expectation_lower_bound_of_degree
    (C := C) (Δ := Δ) G v hdegree hambient
  have hsumReal :
      (((C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
          ((C - 1) ^ (3 * Δ - 2) *
            C ^ (Fintype.card V - (3 * Δ - 2) - 2)) : ℕ) : ℝ)) ≤
        ∑ sample : V → Fin C,
          ((tentativeCollisionColors G
            (alwaysActiveSample sample) v).ncard : ℝ) := by
    exact_mod_cast hsum
  rw [mrTentativeFinStatistic_finiteAverage_eq G v default]
  have hden : (0 : ℝ) ≤ Fintype.card (V → Fin C) := by positivity
  exact div_le_div_of_nonneg_right hsumReal hden

/-- Tentative collisions split disjointly into retained and spoiled colors. -/
lemma spoiledCollisionColors_ncard_add_retainedCollisionColors_ncard
    {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (sample : V → Bool × Fin k) (v : V) :
    (spoiledCollisionColors G sample v).ncard +
        (retainedCollisionColors G sample v).ncard =
      (tentativeCollisionColors G sample v).ncard := by
  exact Set.ncard_sdiff_add_ncard_of_subset
    (retainedCollisionColors_subset_tentativeCollisionColors G sample v)

/-- The existential repeated-color certificate is equivalent to the simple
cardinality condition that at least `t` colors occur twice on retained
neighbors.  This is the exact deterministic bridge used by the later
concentration estimate. -/
lemma hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    {V : Type*} [Fintype V] (G : SimpleGraph V) {k t : ℕ}
    (sample : V → Bool × Fin k) (v : V) :
    HasRandomCollisionCertificate G sample t v ↔
      t ≤ (retainedCollisionColors G sample v).ncard := by
  classical
  constructor
  · rintro ⟨left, right, hendpoints, hretained, hcollision, hcolors⟩
    let color : Fin t → Fin k := fun i ↦ (sample (left i)).2
    have hcolorInjective : Function.Injective color := hcolors
    have hcolorMem (i : Fin t) :
        color i ∈ retainedCollisionColors G sample v := by
      have hlr : left i ≠ right i := by
        intro hlr
        have hsum : (Sum.inl i : Fin t ⊕ Fin t) = Sum.inr i :=
          hendpoints hlr
        exact Sum.inl_ne_inr hsum
      refine ⟨left i, right i, hlr, ?_, ?_⟩
      · exact ⟨(hretained i).1, (hretained i).2.2.1, rfl⟩
      · exact ⟨(hretained i).2.1, (hretained i).2.2.2,
          (hcollision i).symm⟩
    have hsubset : Set.range color ⊆ retainedCollisionColors G sample v := by
      rintro a ⟨i, rfl⟩
      exact hcolorMem i
    calc
      t = (Set.range color).ncard := by
        rw [Set.ncard_range_of_injective hcolorInjective]
        exact (Nat.card_fin t).symm
      _ ≤ (retainedCollisionColors G sample v).ncard :=
        Set.ncard_le_ncard hsubset
  · intro hcard
    have hcard' : Fintype.card (Fin t) ≤
        Fintype.card (retainedCollisionColors G sample v) := by
      simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hcard
    obtain ⟨colors : Fin t ↪ retainedCollisionColors G sample v⟩ :=
      Function.Embedding.nonempty_of_card_le hcard'
    have hwitness (i : Fin t) :
        ∃ x y : V, x ≠ y ∧
          x ∈ retainedNeighborColorFiber G sample v (colors i).1 ∧
          y ∈ retainedNeighborColorFiber G sample v (colors i).1 :=
      (colors i).2
    choose left right hne hleft hright using hwitness
    have hleftColor (i : Fin t) :
        (sample (left i)).2 = (colors i).1 := (hleft i).2.2
    have hrightColor (i : Fin t) :
        (sample (right i)).2 = (colors i).1 := (hright i).2.2
    have hindex_of_colors_eq {i j : Fin t}
        (hij : (colors i).1 = (colors j).1) : i = j := by
      apply colors.injective
      exact Subtype.ext hij
    have hendpoints : Function.Injective (Sum.elim left right) := by
      intro p q hpq
      rcases p with i | i <;> rcases q with j | j
      all_goals simp only [Sum.elim_inl, Sum.elim_inr] at hpq
      · have hij : i = j := hindex_of_colors_eq (by
          rw [← hleftColor i, ← hleftColor j, hpq])
        exact congrArg Sum.inl hij
      · have hij : i = j := hindex_of_colors_eq (by
          rw [← hleftColor i, ← hrightColor j, hpq])
        subst j
        exact (hne i hpq).elim
      · have hij : i = j := hindex_of_colors_eq (by
          rw [← hrightColor i, ← hleftColor j, hpq])
        subst j
        exact (hne i hpq.symm).elim
      · have hij : i = j := hindex_of_colors_eq (by
          rw [← hrightColor i, ← hrightColor j, hpq])
        exact congrArg Sum.inr hij
    refine ⟨left, right, hendpoints, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(hleft i).1, (hright i).1,
        (hleft i).2.1, (hright i).2.1⟩
    · intro i
      exact (hleftColor i).trans (hrightColor i).symm
    · intro i j hij
      apply hindex_of_colors_eq
      rw [← hleftColor i, ← hleftColor j]
      exact hij

/-- The local bad event for the random partial-coloring experiment: `v` is
not itself retained and does not have the collision certificate needed for
the later greedy extension. -/
def localColoringBadEvent {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (t : ℕ) (v : V) : Set (V → Bool × Fin k) :=
  {sample | v ∉ randomRetainedSet G sample ∧
    ¬HasRandomCollisionCertificate G sample t v}

/-- The pure lower-tail event for the number of repeated retained colors at
`v`.  It contains `localColoringBadEvent`; dropping the additional condition
that `v` itself is unretained makes this the convenient concentration target. -/
def retainedCollisionShortfallEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (t : ℕ) (v : V) :
    Set (V → Bool × Fin k) :=
  {sample | (retainedCollisionColors G sample v).ncard < t}

/-- Lower-tail event for tentative collision colors, before conflict
erasure. -/
def tentativeCollisionShortfallEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (a : ℕ) (v : V) :
    Set (V → Bool × Fin k) :=
  {sample | (tentativeCollisionColors G sample v).ncard < a}

/-- Upper-tail event for tentative collision colors spoiled by conflict
erasure. -/
def spoiledCollisionExcessEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (b : ℕ) (v : V) :
    Set (V → Bool × Fin k) :=
  {sample | b < (spoiledCollisionColors G sample v).ncard}

/-- Source-faithful retained-collision lower-tail event.  Its sample space is
the uniform product `V → Fin C` used in Molloy--Reed Theorem 10.5: every
vertex receives one of the `C` tentative colors, with no activation bit. -/
def mrRetainedCollisionShortfallEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (t : ℕ) (v : V) :
    Set (V → Fin C) :=
  {sample |
    (retainedCollisionColors G (alwaysActiveSample sample) v).ncard < t}

/-- Source-faithful lower-tail event for the number of tentative colors that
occur on a nonadjacent pair in `N(v)`. -/
def mrTentativeCollisionShortfallEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (a : ℕ) (v : V) :
    Set (V → Fin C) :=
  {sample |
    (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a}

/-- Source-faithful upper-tail event for tentative collision colors destroyed
when all monochromatic edges are uncolored. -/
def mrSpoiledCollisionExcessEvent {V : Type*} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (b : ℕ) (v : V) :
    Set (V → Fin C) :=
  {sample |
    b < (mrDeletedCollisionColors G sample v).ncard}

/-- Explicit full-product lower-tail estimate for the tentative-collision bad
event, with its mean margin discharged by the retained-pair cylinder count. -/
lemma card_mrTentativeCollisionShortfallEvent_le_exp_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C Δ : ℕ} (hC : 0 < C) (a : ℕ) (v : V)
    [DecidableRel (nonadjacentNeighborPairGraph G v).Adj]
    [Fintype (G.neighborSet v)]
    (hneighbor : 0 < Fintype.card (G.neighborFinset v))
    (default : Fin C) {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ)
    (hambient : (3 * Δ - 2) + 2 ≤ Fintype.card V)
    (hmargin : (a : ℝ) + ε ≤
      ((C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
          ((C - 1) ^ (3 * Δ - 2) *
            C ^ (Fintype.card V - (3 * Δ - 2) - 2)) : ℕ) : ℝ) /
        Fintype.card (V → Fin C)) :
    ((eventFinset
        (mrTentativeCollisionShortfallEvent (C := C) G a v)).card : ℝ) /
        Fintype.card (V → Fin C) ≤
      Real.exp (-ε ^ 2 /
        (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) := by
  letI : Nonempty (Fin C) := Fin.pos_iff_nonempty.mp hC
  have hmean := mrTentativeFinStatistic_finiteAverage_lower_bound_of_degree
    (C := C) (Δ := Δ) G v default hdegree hambient
  have hmarginMean : (a : ℝ) + ε ≤
      finiteAverage
        (fun z ↦ (mrTentativeFinStatistic G v default z : ℝ)) :=
    hmargin.trans hmean
  simpa only [mrTentativeCollisionShortfallEvent] using
    card_mrTentativeCollisionShortfallSet_le_exp
      G v hneighbor default a hε hmarginMean

/-- Direct finite upper-tail estimate for the actual spoiled-collision bad
event.  The threshold `b + 1` is certified by that many distinct colors and
their pairwise coordinate-disjoint deletion-witness triples. -/
lemma card_mrSpoiledCollisionExcessEvent_le_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C Δ : ℕ} (b : ℕ) (v : V)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ) :
    (eventFinset (mrSpoiledCollisionExcessEvent (C := C) G b v)).card ≤
      (C.choose (b + 1) *
        (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^ (b + 1)) *
        C ^ (Fintype.card V - 3 * (b + 1)) := by
  simpa only [mrSpoiledCollisionExcessEvent, Nat.lt_iff_add_one_le] using
    card_mrDeletionHighEvent_le_of_degree G v (b + 1) hdegree

/-- Deterministic Molloy--Reed split.  If at least `a` tentative collision
colors are created and at most `b` are spoiled, then at least `t` survive
whenever `t+b ≤ a`. -/
lemma retainedCollisionShortfallEvent_subset_tentative_union_spoiled
    {V : Type*} [Fintype V] (G : SimpleGraph V) {k t a b : ℕ}
    (hab : t + b ≤ a) (v : V) :
    retainedCollisionShortfallEvent (k := k) G t v ⊆
      tentativeCollisionShortfallEvent (k := k) G a v ∪
        spoiledCollisionExcessEvent (k := k) G b v := by
  intro sample hshort
  change (retainedCollisionColors G sample v).ncard < t at hshort
  change
    (tentativeCollisionColors G sample v).ncard < a ∨
      b < (spoiledCollisionColors G sample v).ncard
  by_cases htent : (tentativeCollisionColors G sample v).ncard < a
  · exact Or.inl htent
  · right
    have hpartition :=
      spoiledCollisionColors_ncard_add_retainedCollisionColors_ncard
        G sample v
    omega

/-- The same deterministic split on the exact Molloy--Reed sample space. -/
lemma mrRetainedCollisionShortfallEvent_subset_tentative_union_spoiled
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C t a b : ℕ}
    (hab : t + b ≤ a) (v : V) :
    mrRetainedCollisionShortfallEvent (C := C) G t v ⊆
      mrTentativeCollisionShortfallEvent (C := C) G a v ∪
        mrSpoiledCollisionExcessEvent (C := C) G b v := by
  intro sample hsample
  change (retainedCollisionColors G (alwaysActiveSample sample) v).ncard < t
    at hsample
  change
    (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a ∨
      b < (mrDeletedCollisionColors G sample v).ncard
  by_cases htent :
      (tentativeCollisionColors G (alwaysActiveSample sample) v).ncard < a
  · exact Or.inl htent
  · right
    have hpartition :=
      spoiledCollisionColors_ncard_add_retainedCollisionColors_ncard
        G (alwaysActiveSample sample) v
    have hdeleted :
        (spoiledCollisionColors G (alwaysActiveSample sample) v).ncard ≤
          (mrDeletedCollisionColors G sample v).ncard :=
      Set.ncard_le_ncard
        (spoiledCollisionColors_subset_mrDeletedCollisionColors G sample v)
    omega

lemma mem_localColoringBadEvent_iff_retainedCollisionColors_ncard_lt
    {V : Type*} [Fintype V] (G : SimpleGraph V) {k t : ℕ}
    (sample : V → Bool × Fin k) (v : V) :
    sample ∈ localColoringBadEvent G t v ↔
      v ∉ randomRetainedSet G sample ∧
        (retainedCollisionColors G sample v).ncard < t := by
  rw [show sample ∈ localColoringBadEvent G t v ↔
      v ∉ randomRetainedSet G sample ∧
        ¬HasRandomCollisionCertificate G sample t v from Iff.rfl,
    hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard]
  simp only [not_le]

lemma localColoringBadEvent_subset_retainedCollisionShortfallEvent
    {V : Type*} [Fintype V] (G : SimpleGraph V) {k t : ℕ} (v : V) :
    localColoringBadEvent (k := k) G t v ⊆
      retainedCollisionShortfallEvent (k := k) G t v := by
  intro sample hsample
  exact (mem_localColoringBadEvent_iff_retainedCollisionColors_ncard_lt
    G sample v).mp hsample |>.2

/-- The coordinates within graph distance at most two from `v`, written
without importing a graph-distance API.  The bad event at `v` only inspects
these coordinates. -/
def twoStepSupport {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {x | x = v ∨ G.Adj v x ∨ ∃ w, G.Adj v w ∧ G.Adj w x}

/-- If one sample avoids every local bad event, its retained vertices and
tentative colors form a proper partial coloring with enough repeated-color
certificates to extend to a total coloring. -/
theorem SimpleGraph.colorable_of_no_localColoringBadEvents [Fintype V]
    (G : SimpleGraph V) {k Δ t : ℕ} (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (sample : V → Bool × Fin k)
    (havoid : ∀ v, sample ∉ localColoringBadEvent G t v) :
    G.Colorable k := by
  classical
  let S := randomRetainedSet G sample
  let c : S → Fin k := fun v ↦ (sample v.1).2
  have hc : ∀ ⦃x y : S⦄, G.Adj x.1 y.1 → c x ≠ c y := by
    intro x y hxy hsame
    have hneq := x.2.2 y.1 hxy y.2.1
    exact hneq hsame.symm
  apply SimpleGraph.colorable_of_partialColoring_collisionPairs
    G hk S c hc hdegree hgap
  intro v hvS
  have hcert : HasRandomCollisionCertificate G sample t v := by
    by_contra hnot
    exact havoid v ⟨hvS, hnot⟩
  obtain ⟨left, right, hendpoints, hretained, hcollision, hcolors⟩ := hcert
  let left' : Fin t → coloredNeighborSet G S v := fun i ↦
    ⟨left i, hretained i |>.1, hretained i |>.2.2.1⟩
  let right' : Fin t → coloredNeighborSet G S v := fun i ↦
    ⟨right i, hretained i |>.2.1, hretained i |>.2.2.2⟩
  refine ⟨left', right', ?_, ?_, ?_⟩
  · intro p q hpq
    rcases p with p | p <;> rcases q with q | q
    all_goals
      apply hendpoints
      simpa [left', right'] using congrArg Subtype.val hpq
  · intro i
    exact hcollision i
  · intro i j hij
    exact hcolors hij

/-- Source-faithful deterministic Molloy--Reed extension step.  The random
round uses only `C` tentative colors, while the final greedy coloring may use
the larger palette `Fin k`.  Retained tentative colors are embedded into that
larger palette, and `t` repeated retained colors at every vertex supply the
savings needed to complete the coloring. -/
theorem SimpleGraph.colorable_of_mr_collision_certificates [Fintype V]
    (G : SimpleGraph V) {C k Δ t : ℕ} (hk : 0 < k) (hCk : C ≤ k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (sample : V → Fin C)
    (hcert : ∀ v,
      HasRandomCollisionCertificate G (alwaysActiveSample sample) t v) :
    G.Colorable k := by
  classical
  let S := randomRetainedSet G (alwaysActiveSample sample)
  let emb : Fin C ↪ Fin k := Fin.castLEEmb hCk
  let c : S → Fin k := fun v ↦ emb (sample v.1)
  have hc : ∀ ⦃x y : S⦄, G.Adj x.1 y.1 → c x ≠ c y := by
    intro x y hxy hsame
    have hneq := x.2.2 y.1 hxy y.2.1
    apply hneq
    exact emb.injective hsame |>.symm
  apply SimpleGraph.colorable_of_partialColoring_collisionPairs
    G hk S c hc hdegree hgap
  intro v _hvS
  obtain ⟨left, right, hendpoints, hretained, hcollision, hcolors⟩ := hcert v
  let left' : Fin t → coloredNeighborSet G S v := fun i ↦
    ⟨left i, (hretained i).1, (hretained i).2.2.1⟩
  let right' : Fin t → coloredNeighborSet G S v := fun i ↦
    ⟨right i, (hretained i).2.1, (hretained i).2.2.2⟩
  refine ⟨left', right', ?_, ?_, ?_⟩
  · intro p q hpq
    rcases p with p | p <;> rcases q with q | q
    all_goals
      apply hendpoints
      simpa [left', right'] using congrArg Subtype.val hpq
  · intro i
    apply congrArg emb
    exact hcollision i
  · intro i j hij
    apply hcolors
    exact emb.injective hij

/-- Retention of `w = v` or a neighbor `w` of `v` is determined by the sample
coordinates in `twoStepSupport G v`. -/
lemma randomRetainedSet_mem_iff_of_eqOn_twoStep
    {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (sample sample' : V → Bool × Fin k) (v w : V)
    (hw : w = v ∨ G.Adj v w)
    (heq : ∀ x ∈ twoStepSupport G v, sample x = sample' x) :
    w ∈ randomRetainedSet G sample ↔
      w ∈ randomRetainedSet G sample' := by
  have hwSupport : w ∈ twoStepSupport G v := by
    rcases hw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have heqw := heq w hwSupport
  constructor
  · rintro ⟨hactive, hproper⟩
    refine ⟨by simpa [heqw] using hactive, ?_⟩
    intro x hwx hxactive
    have hxSupport : x ∈ twoStepSupport G v := by
      rcases hw with h | h
      · subst w
        exact Or.inr (Or.inl hwx)
      · exact Or.inr (Or.inr ⟨w, h, hwx⟩)
    have heqx := heq x hxSupport
    have hxactive' : (sample x).1 = true := by
      simpa [heqx] using hxactive
    have hneq := hproper x hwx hxactive'
    simpa [heqx, heqw] using hneq
  · rintro ⟨hactive, hproper⟩
    refine ⟨by simpa [heqw] using hactive, ?_⟩
    intro x hwx hxactive
    have hxSupport : x ∈ twoStepSupport G v := by
      rcases hw with h | h
      · subst w
        exact Or.inr (Or.inl hwx)
      · exact Or.inr (Or.inr ⟨w, h, hwx⟩)
    have heqx := heq x hxSupport
    have hxactive' : (sample' x).1 = true := by
      simpa [heqx] using hxactive
    have hneq := hproper x hwx hxactive'
    simpa [heqx, heqw] using hneq

/-- Existence of the repeated-color certificate at `v` is determined by the
same radius-two coordinate support. -/
lemma hasRandomCollisionCertificate_iff_of_eqOn_twoStep
    {V : Type*} (G : SimpleGraph V) {k t : ℕ}
    (sample sample' : V → Bool × Fin k) (v : V)
    (heq : ∀ x ∈ twoStepSupport G v, sample x = sample' x) :
    HasRandomCollisionCertificate G sample t v ↔
      HasRandomCollisionCertificate G sample' t v := by
  have transfer (a b : V → Bool × Fin k)
      (hab : ∀ x ∈ twoStepSupport G v, a x = b x)
      (hcert : HasRandomCollisionCertificate G a t v) :
      HasRandomCollisionCertificate G b t v := by
    obtain ⟨left, right, hendpoints, hretained, hcollision, hcolors⟩ := hcert
    refine ⟨left, right, hendpoints, ?_, ?_, ?_⟩
    · intro i
      have hleft := randomRetainedSet_mem_iff_of_eqOn_twoStep
        G a b v (left i) (Or.inr (hretained i).2.2.1) hab
      have hright := randomRetainedSet_mem_iff_of_eqOn_twoStep
        G a b v (right i) (Or.inr (hretained i).2.2.2) hab
      exact ⟨hleft.mp (hretained i).1,
        hright.mp (hretained i).2.1,
        (hretained i).2.2.1, (hretained i).2.2.2⟩
    · intro i
      have hleft := hab (left i) (Or.inr (Or.inl (hretained i).2.2.1))
      have hright := hab (right i) (Or.inr (Or.inl (hretained i).2.2.2))
      simpa [hleft, hright] using hcollision i
    · intro i j hij
      apply hcolors
      have hlefti := hab (left i) (Or.inr (Or.inl (hretained i).2.2.1))
      have hleftj := hab (left j) (Or.inr (Or.inl (hretained j).2.2.1))
      simpa [hlefti, hleftj] using hij
  constructor
  · exact transfer sample sample' heq
  · exact transfer sample' sample (fun x hx ↦ (heq x hx).symm)

/-- The local bad event in the one-round partial-coloring experiment depends
only on coordinates within two graph steps of its vertex. -/
lemma localColoringBadEvent_dependsOn_twoStep
    {V : Type*} (G : SimpleGraph V) {k t : ℕ} (v : V) :
    EventDependsOn (localColoringBadEvent (k := k) G t v)
      (twoStepSupport G v) := by
  intro sample sample' heq
  have hv := randomRetainedSet_mem_iff_of_eqOn_twoStep
    G sample sample' v v (Or.inl rfl) heq
  have hcert := hasRandomCollisionCertificate_iff_of_eqOn_twoStep
    (t := t) G sample sample' v heq
  change
    (v ∉ randomRetainedSet G sample ∧
      ¬HasRandomCollisionCertificate G sample t v) ↔
    (v ∉ randomRetainedSet G sample' ∧
      ¬HasRandomCollisionCertificate G sample' t v)
  rw [hv, hcert]

/-- The exact Molloy--Reed retained-collision lower-tail event is also local
to the radius-two product coordinates. -/
lemma mrRetainedCollisionShortfallEvent_dependsOn_twoStep
    {V : Type*} [Fintype V] (G : SimpleGraph V) {C t : ℕ} (v : V) :
    EventDependsOn (mrRetainedCollisionShortfallEvent (C := C) G t v)
      (twoStepSupport G v) := by
  intro sample sample' heq
  have hlift : ∀ x ∈ twoStepSupport G v,
      alwaysActiveSample sample x = alwaysActiveSample sample' x := by
    intro x hx
    simp [alwaysActiveSample, heq x hx]
  have hcert := hasRandomCollisionCertificate_iff_of_eqOn_twoStep
    (t := t) G (alwaysActiveSample sample) (alwaysActiveSample sample') v hlift
  have hleft := hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    (t := t) G (alwaysActiveSample sample) v
  have hright := hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    (t := t) G (alwaysActiveSample sample') v
  change
    (retainedCollisionColors G (alwaysActiveSample sample) v).ncard < t ↔
      (retainedCollisionColors G (alwaysActiveSample sample') v).ncard < t
  simp only [← not_le]
  exact not_congr (hleft.symm.trans (hcert.trans hright))

/-- A vertex together with its graph neighbors, as a finset. -/
noncomputable def closedNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset V :=
  insert v (eventFinset (G.neighborSet v))

@[simp]
lemma mem_closedNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v x : V) :
    x ∈ closedNeighborFinset G v ↔ x = v ∨ G.Adj v x := by
  simp [closedNeighborFinset]

/-- Radius-two coordinates, represented as a finite union of closed
neighborhoods. -/
noncomputable def twoStepFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset V :=
  (closedNeighborFinset G v).biUnion (closedNeighborFinset G)

lemma mem_twoStepFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v x : V) :
    x ∈ twoStepFinset G v ↔ x ∈ twoStepSupport G v := by
  rw [twoStepFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hx⟩
    rw [mem_closedNeighborFinset] at hw hx
    rcases hw with rfl | hvw
    · rcases hx with rfl | hvx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hvx)
    · rcases hx with rfl | hwx
      · exact Or.inr (Or.inl hvw)
      · exact Or.inr (Or.inr ⟨w, hvw, hwx⟩)
  · intro hx
    rcases hx with rfl | hvx | ⟨w, hvw, hwx⟩
    · exact ⟨x, by simp, by simp⟩
    · exact ⟨v, by simp, by simp [hvx]⟩
    · exact ⟨w, by simp [hvw], by simp [hwx]⟩

/-- The radius-two relation is symmetric in an undirected graph. -/
lemma mem_twoStepSupport_comm {V : Type*} (G : SimpleGraph V) (v x : V) :
    x ∈ twoStepSupport G v ↔ v ∈ twoStepSupport G x := by
  constructor
  · intro h
    rcases h with rfl | hvx | ⟨w, hvw, hwx⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hvx.symm)
    · exact Or.inr (Or.inr ⟨w, hwx.symm, hvw.symm⟩)
  · intro h
    rcases h with rfl | hxv | ⟨w, hxw, hwv⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hxv.symm)
    · exact Or.inr (Or.inr ⟨w, hwv.symm, hxw.symm⟩)

lemma closedNeighborFinset_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ : ℕ)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ) (v : V) :
    (closedNeighborFinset G v).card ≤ Δ + 1 := by
  have hneighbor : (eventFinset (G.neighborSet v)).card ≤ Δ := by
    rw [card_eventFinset_eq_ncard]
    exact hdegree v
  calc
    (closedNeighborFinset G v).card ≤
        1 + (eventFinset (G.neighborSet v)).card := by
      simpa [closedNeighborFinset, Nat.add_comm] using
        Finset.card_insert_le v (eventFinset (G.neighborSet v))
    _ ≤ 1 + Δ := Nat.add_le_add_left hneighbor 1
    _ = Δ + 1 := by omega

/-- A maximum-degree bound `Δ` gives the crude but sufficient radius-two
support bound `(Δ+1)^2`. -/
lemma twoStepFinset_card_le_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ : ℕ)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ) (v : V) :
    (twoStepFinset G v).card ≤ (Δ + 1) ^ 2 := by
  calc
    (twoStepFinset G v).card ≤
        ∑ w ∈ closedNeighborFinset G v, (closedNeighborFinset G w).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ closedNeighborFinset G v, (Δ + 1) := by
      apply Finset.sum_le_sum
      intro w _hw
      exact closedNeighborFinset_card_le G Δ hdegree w
    _ = (closedNeighborFinset G v).card * (Δ + 1) := by simp
    _ ≤ (Δ + 1) * (Δ + 1) :=
      Nat.mul_le_mul_right _ (closedNeighborFinset_card_le G Δ hdegree v)
    _ = (Δ + 1) ^ 2 := by ring

/-- Vertices whose radius-two support overlaps the radius-two support of `v`.
These are precisely the possible dependency indices for the local bad event at
`v`. -/
noncomputable def twoStepDependencyFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w ↦
    ¬Disjoint (twoStepSupport G v) (twoStepSupport G w)

/-- Radius-two support overlap has at most `(Δ+1)^4` possible indices.  If the
supports at `v` and `w` meet at `x`, symmetry puts `w` in the radius-two ball
of `x`, while `x` lies in the radius-two ball of `v`. -/
lemma twoStepDependencyFinset_card_le_pow_four
    {V : Type*} [Fintype V] (G : SimpleGraph V) (Δ : ℕ)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ) (v : V) :
    (twoStepDependencyFinset G v).card ≤ (Δ + 1) ^ 4 := by
  classical
  let fourStep : Finset V :=
    (twoStepFinset G v).biUnion (twoStepFinset G)
  have hsubset : twoStepDependencyFinset G v ⊆ fourStep := by
    intro w hw
    have hnotDisjoint := (Finset.mem_filter.mp hw).2
    obtain ⟨x, hxv, hxw⟩ := Set.not_disjoint_iff.mp hnotDisjoint
    apply Finset.mem_biUnion.mpr
    refine ⟨x, (mem_twoStepFinset G v x).mpr hxv, ?_⟩
    apply (mem_twoStepFinset G x w).mpr
    exact (mem_twoStepSupport_comm G w x).mp hxw
  calc
    (twoStepDependencyFinset G v).card ≤ fourStep.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ x ∈ twoStepFinset G v, (twoStepFinset G x).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ twoStepFinset G v, (Δ + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      exact twoStepFinset_card_le_sq G Δ hdegree x
    _ = (twoStepFinset G v).card * (Δ + 1) ^ 2 := by simp
    _ ≤ (Δ + 1) ^ 2 * (Δ + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (twoStepFinset_card_le_sq G Δ hdegree v)
    _ = (Δ + 1) ^ 4 := by ring

/-- Finite, denominator-free reduction of the one-round locally sparse
coloring argument.  Once every radius-two bad event has cardinality at most
`1 / (4(Δ+1)^4)` of the product sample space, the product local lemma supplies
a sample avoiding every bad event, and the retained partial coloring extends
greedily. -/
theorem SimpleGraph.colorable_of_localColoringBadEvent_card_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k Δ t : ℕ}
    (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hbad : ∀ v,
      4 * (Δ + 1) ^ 4 *
          (eventFinset (localColoringBadEvent (k := k) G t v)).card ≤
        Fintype.card (V → Bool × Fin k)) :
    G.Colorable k := by
  classical
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let dep : V → V → Prop := fun v w ↦
    ¬Disjoint (twoStepSupport G v) (twoStepSupport G w)
  have hdepDegree (v : V) :
      ((Finset.univ : Finset V).filter (dep v)).card ≤ (Δ + 1) ^ 4 := by
    simpa [dep, twoStepDependencyFinset] using
      twoStepDependencyFinset_card_le_pow_four G Δ hdegree v
  have hdisjoint {v w : V} (hvw : ¬dep v w) :
      Disjoint (twoStepSupport G v) (twoStepSupport G w) := by
    simpa [dep] using hvw
  obtain ⟨sample, hsample⟩ :=
    exists_avoiding_of_local_product_events
      (fun v ↦ localColoringBadEvent (k := k) G t v)
      (twoStepSupport G) dep ((Δ + 1) ^ 4)
      (Nat.pow_pos (by omega)) hdepDegree
      (localColoringBadEvent_dependsOn_twoStep G)
      hdisjoint hbad
  exact SimpleGraph.colorable_of_no_localColoringBadEvents G
    hk hdegree hgap sample hsample

/-- Concentration-facing version of the finite locally sparse coloring
reduction.  It is enough to bound the larger event that fewer than `t`
retained colors are repeated in the neighborhood, whether or not the center
vertex is itself retained. -/
theorem SimpleGraph.colorable_of_retainedCollisionShortfall_card_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k Δ t : ℕ}
    (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hshort : ∀ v,
      4 * (Δ + 1) ^ 4 *
          (eventFinset
            (retainedCollisionShortfallEvent (k := k) G t v)).card ≤
        Fintype.card (V → Bool × Fin k)) :
    G.Colorable k := by
  apply SimpleGraph.colorable_of_localColoringBadEvent_card_bound
    G hk hdegree hgap
  intro v
  have hsubset :
      eventFinset (localColoringBadEvent (k := k) G t v) ⊆
        eventFinset (retainedCollisionShortfallEvent (k := k) G t v) := by
    intro sample hsample
    rw [mem_eventFinset] at hsample ⊢
    exact localColoringBadEvent_subset_retainedCollisionShortfallEvent
      G v hsample
  exact (Nat.mul_le_mul_left (4 * (Δ + 1) ^ 4)
    (Finset.card_le_card hsubset)).trans (hshort v)

/-- Final two-tail interface for the one-round sparse-neighborhood argument.
It suffices to prove a lower-tail bound for the number of tentative collision
colors and an upper-tail bound for the number spoiled by conflict erasure. -/
theorem SimpleGraph.colorable_of_tentative_and_spoiled_tail_card_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k Δ t a b : ℕ}
    (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hab : t + b ≤ a)
    (htails : ∀ v,
      4 * (Δ + 1) ^ 4 *
          ((eventFinset
              (tentativeCollisionShortfallEvent (k := k) G a v)).card +
            (eventFinset
              (spoiledCollisionExcessEvent (k := k) G b v)).card) ≤
        Fintype.card (V → Bool × Fin k)) :
    G.Colorable k := by
  apply SimpleGraph.colorable_of_retainedCollisionShortfall_card_bound
    G hk hdegree hgap
  intro v
  have hsubset :
      eventFinset (retainedCollisionShortfallEvent (k := k) G t v) ⊆
        eventFinset (tentativeCollisionShortfallEvent (k := k) G a v) ∪
          eventFinset (spoiledCollisionExcessEvent (k := k) G b v) := by
    intro sample hsample
    rw [mem_eventFinset] at hsample
    rw [Finset.mem_union, mem_eventFinset, mem_eventFinset]
    exact retainedCollisionShortfallEvent_subset_tentative_union_spoiled
      G hab v hsample
  have hcard :
      (eventFinset
          (retainedCollisionShortfallEvent (k := k) G t v)).card ≤
        (eventFinset
            (tentativeCollisionShortfallEvent (k := k) G a v)).card +
          (eventFinset
            (spoiledCollisionExcessEvent (k := k) G b v)).card := by
    exact (Finset.card_le_card hsubset).trans
      (Finset.card_union_le _ _)
  exact (Nat.mul_le_mul_left (4 * (Δ + 1) ^ 4) hcard).trans (htails v)

/-- Exact finite-product local-lemma reduction for the Molloy--Reed random
round.  The round uses `C` colors uniformly, those colors are injected into a
possibly larger final palette of size `k`, and the remaining vertices are
colored greedily. -/
theorem SimpleGraph.colorable_of_mr_retainedCollisionShortfall_card_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C k Δ t : ℕ}
    (hC : 0 < C) (hk : 0 < k) (hCk : C ≤ k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hshort : ∀ v,
      4 * (Δ + 1) ^ 4 *
          (eventFinset
            (mrRetainedCollisionShortfallEvent (C := C) G t v)).card ≤
        Fintype.card (V → Fin C)) :
    G.Colorable k := by
  classical
  letI : Nonempty (Fin C) := Fin.pos_iff_nonempty.mp hC
  let dep : V → V → Prop := fun v w ↦
    ¬Disjoint (twoStepSupport G v) (twoStepSupport G w)
  have hdepDegree (v : V) :
      ((Finset.univ : Finset V).filter (dep v)).card ≤ (Δ + 1) ^ 4 := by
    simpa [dep, twoStepDependencyFinset] using
      twoStepDependencyFinset_card_le_pow_four G Δ hdegree v
  have hdisjoint {v w : V} (hvw : ¬dep v w) :
      Disjoint (twoStepSupport G v) (twoStepSupport G w) := by
    simpa [dep] using hvw
  obtain ⟨sample, hsample⟩ :=
    exists_avoiding_of_local_product_events
      (fun v ↦ mrRetainedCollisionShortfallEvent (C := C) G t v)
      (twoStepSupport G) dep ((Δ + 1) ^ 4)
      (Nat.pow_pos (by omega)) hdepDegree
      (mrRetainedCollisionShortfallEvent_dependsOn_twoStep G)
      hdisjoint hshort
  apply SimpleGraph.colorable_of_mr_collision_certificates
    G hk hCk hdegree hgap sample
  intro v
  apply (hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    (t := t) G (alwaysActiveSample sample) v).mpr
  have hnot := hsample v
  change ¬(retainedCollisionColors G (alwaysActiveSample sample) v).ncard < t at hnot
  omega

/-- Final source-faithful two-tail interface.  This is the exact deterministic
target of Molloy--Reed Lemmas 10.6 and 10.7: a lower tail for tentative
collision colors and an upper tail for spoiled colors imply the desired
`k`-coloring. -/
theorem SimpleGraph.colorable_of_mr_tentative_and_spoiled_tail_card_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C k Δ t a b : ℕ}
    (hC : 0 < C) (hk : 0 < k) (hCk : C ≤ k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t)
    (hab : t + b ≤ a)
    (htails : ∀ v,
      4 * (Δ + 1) ^ 4 *
          ((eventFinset
              (mrTentativeCollisionShortfallEvent (C := C) G a v)).card +
            (eventFinset
              (mrSpoiledCollisionExcessEvent (C := C) G b v)).card) ≤
        Fintype.card (V → Fin C)) :
    G.Colorable k := by
  apply SimpleGraph.colorable_of_mr_retainedCollisionShortfall_card_bound
    G hC hk hCk hdegree hgap
  intro v
  have hsubset :
      eventFinset (mrRetainedCollisionShortfallEvent (C := C) G t v) ⊆
        eventFinset (mrTentativeCollisionShortfallEvent (C := C) G a v) ∪
          eventFinset (mrSpoiledCollisionExcessEvent (C := C) G b v) := by
    intro sample hsample
    rw [mem_eventFinset] at hsample
    rw [Finset.mem_union, mem_eventFinset, mem_eventFinset]
    exact mrRetainedCollisionShortfallEvent_subset_tentative_union_spoiled
      G hab v hsample
  have hcard :
      (eventFinset
          (mrRetainedCollisionShortfallEvent (C := C) G t v)).card ≤
        (eventFinset
            (mrTentativeCollisionShortfallEvent (C := C) G a v)).card +
          (eventFinset
            (mrSpoiledCollisionExcessEvent (C := C) G b v)).card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  exact (Nat.mul_le_mul_left (4 * (Δ + 1) ^ 4) hcard).trans (htails v)

/-- A fully numerical version of the Molloy--Reed one-round argument.  The
tentative lower tail is supplied by finite McDiarmid, the spoiled upper tail
by the direct union bound over deletion certificates, and the displayed real
inequality is exactly the remaining arithmetic needed by the finite local
lemma.  Keeping this statement denominator-free on its conclusion makes it a
convenient bridge to the combinatorial coloring theorem above. -/
theorem SimpleGraph.colorable_of_mr_exp_and_certificate_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C k Δ t a b : ℕ}
    (hC : 0 < C) (hk : 0 < k) (hCk : C ≤ k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hgap : Δ + 1 - k ≤ t) (hab : t + b ≤ a)
    (hneighbor : ∀ v, 0 < Fintype.card (G.neighborFinset v))
    (hambient : (3 * Δ - 2) + 2 ≤ Fintype.card V)
    (ε : V → ℝ) (hε : ∀ v, 0 ≤ ε v)
    (hmargin : ∀ v,
      (a : ℝ) + ε v ≤
        ((C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
            ((C - 1) ^ (3 * Δ - 2) *
              C ^ (Fintype.card V - (3 * Δ - 2) - 2)) : ℕ) : ℝ) /
          Fintype.card (V → Fin C))
    (hnumeric : ∀ v,
      ((4 * (Δ + 1) ^ 4 : ℕ) : ℝ) *
          (Real.exp (-(ε v) ^ 2 /
              (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) *
              Fintype.card (V → Fin C) +
            (((C.choose (b + 1) *
                (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^
                  (b + 1)) *
                C ^ (Fintype.card V - 3 * (b + 1)) : ℕ) : ℝ)) ≤
        Fintype.card (V → Fin C)) :
    G.Colorable k := by
  classical
  letI : Nonempty (Fin C) := Fin.pos_iff_nonempty.mp hC
  apply SimpleGraph.colorable_of_mr_tentative_and_spoiled_tail_card_bounds
    G hC hk hCk hdegree hgap hab
  intro v
  let q : ℕ := Fintype.card (V → Fin C)
  let M : ℕ := 4 * (Δ + 1) ^ 4
  let T : ℕ :=
    (eventFinset
      (mrTentativeCollisionShortfallEvent (C := C) G a v)).card
  let S : ℕ :=
    (eventFinset
      (mrSpoiledCollisionExcessEvent (C := C) G b v)).card
  let D : ℕ :=
    (C.choose (b + 1) *
        (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^ (b + 1)) *
      C ^ (Fintype.card V - 3 * (b + 1))
  let E : ℝ :=
    Real.exp (-(ε v) ^ 2 /
      (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2))
  have hqposNat : 0 < q := by
    dsimp only [q]
    exact Fintype.card_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have htentRatio : (T : ℝ) / q ≤ E := by
    dsimp only [T, E, q]
    exact card_mrTentativeCollisionShortfallEvent_le_exp_of_degree
      G hC a v (hneighbor v) ⟨0, hC⟩ (hε v) hdegree hambient (hmargin v)
  have htent : (T : ℝ) ≤ E * q := by
    exact (div_le_iff₀ hqpos).mp htentRatio
  have hspoiledNat : S ≤ D := by
    dsimp only [S, D]
    exact card_mrSpoiledCollisionExcessEvent_le_of_degree G b v hdegree
  have hspoiled : (S : ℝ) ≤ D := by exact_mod_cast hspoiledNat
  have hsum : ((T + S : ℕ) : ℝ) ≤ E * q + D := by
    push_cast
    exact add_le_add htent hspoiled
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hproduct : ((M * (T + S) : ℕ) : ℝ) ≤ (q : ℝ) := by
    calc
      ((M * (T + S) : ℕ) : ℝ) = (M : ℝ) * ((T + S : ℕ) : ℝ) := by
        norm_num
      _ ≤ (M : ℝ) * (E * q + D) := mul_le_mul_of_nonneg_left hsum hMnonneg
      _ ≤ (q : ℝ) := by
        dsimp only [M, E, D, q]
        exact hnumeric v
  have hproductNat : M * (T + S) ≤ q := by exact_mod_cast hproduct
  simpa only [M, T, S, q] using hproductNat

/-- The complete graph on the vertices belonging to `s`, with every vertex
outside `s` isolated. -/
def cliqueGraph {V : Type u} (s : Set V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ s ∧ y ∈ s
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

@[simp]
lemma cliqueGraph_adj {V : Type u} {s : Set V} {x y : V} :
    (cliqueGraph s).Adj x y ↔ x ≠ y ∧ x ∈ s ∧ y ∈ s :=
  Iff.rfl

/-- Two complete graphs have disjoint edge sets exactly when their vertex sets
meet in at most one point. -/
lemma disjoint_cliqueGraph_iff {V : Type u} {s t : Set V} :
    Disjoint (cliqueGraph s) (cliqueGraph t) ↔ (s ∩ t).Subsingleton := by
  constructor
  · intro hd x hx y hy
    by_contra hxy
    have hs : (cliqueGraph s).Adj x y := ⟨hxy, hx.1, hy.1⟩
    have ht : (cliqueGraph t).Adj x y := ⟨hxy, hx.2, hy.2⟩
    exact (SimpleGraph.disjoint_left.mp hd x y hs) ht
  · intro hst
    rw [SimpleGraph.disjoint_left]
    intro x y hs ht
    exact hs.1 (hst ⟨hs.2.1, ht.2.1⟩ ⟨hs.2.2, ht.2.2⟩)

/-- An indexed family of `n` copies of `K_n` on the finite ambient vertex type
`V`.  `edge_disjoint` says exactly that different copies share no graph edge,
and `covers` rules out ambient vertices that do not belong to the union. -/
structure Configuration (n : ℕ) (V : Type u) [Fintype V] where
  blocks : Fin n → Finset V
  card_blocks : ∀ i, (blocks i).card = n
  edge_disjoint : Pairwise fun i j ↦
    Disjoint (cliqueGraph (blocks i : Set V)) (cliqueGraph (blocks j : Set V))
  covers : ∀ v, ∃ i, v ∈ blocks i

namespace Configuration

variable {n : ℕ} {V : Type u} [Fintype V]

/-- The union of all the constituent copies of `K_n`. -/
def graph (C : Configuration n V) : SimpleGraph V :=
  ⨆ i, cliqueGraph (C.blocks i : Set V)

@[simp]
lemma graph_adj (C : Configuration n V) {x y : V} :
    C.graph.Adj x y ↔ x ≠ y ∧ ∃ i, x ∈ C.blocks i ∧ y ∈ C.blocks i := by
  simp only [graph, SimpleGraph.iSup_adj, cliqueGraph_adj]
  constructor
  · rintro ⟨i, hxy, hx, hy⟩
    exact ⟨hxy, i, hx, hy⟩
  · rintro ⟨hxy, i, hx, hy⟩
    exact ⟨i, hxy, hx, hy⟩

lemma cliqueGraph_le_graph (C : Configuration n V) (i : Fin n) :
    cliqueGraph (C.blocks i : Set V) ≤ C.graph :=
  le_iSup (fun j ↦ cliqueGraph (C.blocks j : Set V)) i

/-- The graph-theoretic edge-disjointness field is equivalent to the usual
linearity condition on the family of block vertex sets. -/
lemma linear_intersections (C : Configuration n V) :
    Pairwise fun i j ↦
      (((C.blocks i : Set V) ∩ (C.blocks j : Set V)).Subsingleton) := by
  intro i j hij
  exact disjoint_cliqueGraph_iff.mp (C.edge_disjoint hij)

/-- Each block really is a clique in the union graph. -/
lemma isClique_block (C : Configuration n V) (i : Fin n) :
    C.graph.IsClique (C.blocks i : Set V) := by
  intro x hx y hy hxy
  exact C.graph_adj.mpr ⟨hxy, i, hx, hy⟩

/-- Any proper coloring of a configuration uses at least `n` colors. -/
lemma card_le_of_colorable (C : Configuration n V) {k : ℕ}
    (hcolor : C.graph.Colorable k) (i : Fin n) : n ≤ k := by
  rw [← C.card_blocks i]
  exact (C.isClique_block i).card_le_of_colorable hcolor

/-- For positive `n`, the clique lower bound on the chromatic number. -/
lemma n_le_chromaticNumber (C : Configuration n V) (hn : 0 < n) :
    (n : ℕ∞) ≤ C.graph.chromaticNumber := by
  let i : Fin n := ⟨0, hn⟩
  rw [SimpleGraph.le_chromaticNumber_iff_colorable]
  intro k hk
  exact_mod_cast C.card_le_of_colorable hk i

/-- An `n`-coloring gives equality because a constituent `K_n` supplies the
matching lower bound. -/
lemma chromaticNumber_eq (C : Configuration n V) (hn : 0 < n)
    (hcolor : C.graph.Colorable n) : C.graph.chromaticNumber = n := by
  apply le_antisymm hcolor.chromaticNumber_le
  exact C.n_le_chromaticNumber hn

end Configuration

/-! ## Indexed hypergraphs and the duality reduction -/

/-- A hypergraph whose edges retain their labels.  Keeping the edge-label type
is important here: different graph vertices can have the same singleton
incidence set, but they must remain different dual hyperedges. -/
structure IndexedHypergraph (X : Type u) (E : Type*) where
  edge : E → Set X

namespace IndexedHypergraph

variable {X : Type u} {E : Type*}

/-- A linear indexed hypergraph has at most one common vertex in every pair of
different labeled edges. -/
def IsLinear (H : IndexedHypergraph X E) : Prop :=
  ∀ ⦃e f : E⦄, e ≠ f → (H.edge e ∩ H.edge f).Subsingleton

/-- A proper edge coloring of an indexed hypergraph. -/
structure EdgeColoring (H : IndexedHypergraph X E) (κ : Type*) where
  color : E → κ
  valid : ∀ ⦃e f : E⦄, e ≠ f → (H.edge e ∩ H.edge f).Nonempty → color e ≠ color f

instance {H : IndexedHypergraph X E} {κ : Type*} : CoeFun (H.EdgeColoring κ) fun _ ↦ E → κ :=
  ⟨EdgeColoring.color⟩

/-- Colorability with a palette of `k` colors. -/
def EdgeColorable (H : IndexedHypergraph X E) (k : ℕ) : Prop :=
  Nonempty (H.EdgeColoring (Fin k))

/-- Every hypergraph vertex is incident with at most `k` labeled edges.  This
extra field is what permits repeated singleton edges while retaining the usual
`k`-color conclusion. -/
def DegreeLE (H : IndexedHypergraph X E) (k : ℕ) : Prop :=
  ∀ x, {e | x ∈ H.edge e}.ncard ≤ k

/-- The labeled edges other than `e` which meet `e`. -/
def neighborSet (H : IndexedHypergraph X E) (e : E) : Set E :=
  {f | e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty}

/-- Conflicting edges which occur strictly earlier according to a numerical
rank.  An injective rank is an explicit finite ordering of the labeled
edges. -/
def earlierNeighborSet (H : IndexedHypergraph X E) (rank : E → ℕ) (e : E) : Set E :=
  {f | rank f < rank e ∧ (H.edge e ∩ H.edge f).Nonempty}

/-- Conflicting neighbors of `e` which lie in a prescribed subfamily. -/
def internalNeighborSet (H : IndexedHypergraph X E) (S : Set E) (e : E) : Set E :=
  {f | f ∈ S ∧ e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty}

/-- Finite greedy edge coloring: fewer than `k` conflicting neighbors at
every labeled edge suffice for a proper `k`-coloring.  This is the elementary
greedy endpoint used repeatedly after the large-edge ordering estimates in the
Kang--Kelly--Kühn--Methuku--Osthus proof. -/
theorem edgeColorable_of_neighbor_ncard_lt [Fintype E]
    (H : IndexedHypergraph X E) {k : ℕ} (hk : 0 < k)
    (hneighbors : ∀ e, (H.neighborSet e).ncard < k) : H.EdgeColorable k := by
  classical
  let fallback : Fin k := ⟨0, hk⟩
  have aux : ∀ S : Finset E, ∃ c : E → Fin k,
      ∀ ⦃e f : E⦄, e ∈ S → f ∈ S → e ≠ f →
        (H.edge e ∩ H.edge f).Nonempty → c e ≠ c f := by
    intro S
    induction S using Finset.induction with
    | empty =>
        exact ⟨fun _ ↦ fallback, by simp⟩
    | @insert e S he ih =>
        obtain ⟨c, hc⟩ := ih
        let adjacent : Finset E := S.filter fun f ↦ f ∈ H.neighborSet e
        let used : Finset (Fin k) := adjacent.image c
        have hused : used.card < k := by
          apply (show used.card ≤ (H.neighborSet e).ncard from ?_).trans_lt
            (hneighbors e)
          calc
            used.card ≤ adjacent.card := Finset.card_image_le
            _ = (adjacent : Set E).ncard := by simp
            _ ≤ (H.neighborSet e).ncard := Set.ncard_le_ncard (by
              intro f hf
              change f ∈ adjacent at hf
              exact (Finset.mem_filter.mp hf).2)
        obtain ⟨a, _, ha⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card
            (s := used) (t := Finset.univ) (by simpa using hused)
        let c' : E → Fin k := Function.update c e a
        refine ⟨c', ?_⟩
        intro x y hx hy hxy hinter
        simp only [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · have hyS : y ∈ S := by
            rcases hy with rfl | hy
            · exact (hxy rfl).elim
            · exact hy
          have hyadj : y ∈ adjacent := by
            exact Finset.mem_filter.mpr ⟨hyS, hxy, hinter⟩
          have hcy : c y ∈ used := by
            exact Finset.mem_image.mpr ⟨y, hyadj, rfl⟩
          have hay : a ≠ c y := fun hay ↦ ha (hay ▸ hcy)
          simpa [c', hxy, hxy.symm] using hay
        · rcases hy with rfl | hy
          · have hxadj : x ∈ adjacent := by
              have hinter' : (H.edge y ∩ H.edge x).Nonempty := by
                simpa [Set.inter_comm] using hinter
              exact Finset.mem_filter.mpr ⟨hx, hxy.symm, hinter'⟩
            have hcx : c x ∈ used := by
              exact Finset.mem_image.mpr ⟨x, hxadj, rfl⟩
            have hax : a ≠ c x := fun hax ↦ ha (hax ▸ hcx)
            simpa [c', hxy, hxy.symm] using hax.symm
          · have hxe : x ≠ e := fun h ↦ he (h ▸ hx)
            have hye : y ≠ e := fun h ↦ he (h ▸ hy)
            simpa [c', hxe, hye] using hc hx hy hxy hinter
  obtain ⟨c, hc⟩ := aux Finset.univ
  refine ⟨{ color := c, valid := ?_ }⟩
  intro e f hef hinter
  exact hc (by simp) (by simp) hef hinter

/-- Ordered greedy edge coloring.  It is enough that every edge have fewer
than `k` conflicting predecessors in one injective numerical ordering; later
neighbors do not constrain the color at the moment it is chosen. -/
theorem edgeColorable_of_earlierNeighbor_ncard_lt [Fintype E]
    (H : IndexedHypergraph X E) {k : ℕ} (hk : 0 < k)
    (rank : E → ℕ) (hrank : Function.Injective rank)
    (hearlier : ∀ e, (H.earlierNeighborSet rank e).ncard < k) :
    H.EdgeColorable k := by
  classical
  let fallback : Fin k := ⟨0, hk⟩
  have aux : ∀ m : ℕ, ∃ c : E → Fin k,
      ∀ ⦃e f : E⦄, rank e < m → rank f < m → e ≠ f →
        (H.edge e ∩ H.edge f).Nonempty → c e ≠ c f := by
    intro m
    induction m with
    | zero =>
        exact ⟨fun _ ↦ fallback, by omega⟩
    | succ m ih =>
        obtain ⟨c, hc⟩ := ih
        by_cases hex : ∃ e, rank e = m
        · obtain ⟨e, he⟩ := hex
          let adjacent : Finset E := Finset.univ.filter fun f ↦
            rank f < m ∧ (H.edge e ∩ H.edge f).Nonempty
          let used : Finset (Fin k) := adjacent.image c
          have hadjacent : (adjacent : Set E) ⊆ H.earlierNeighborSet rank e := by
            intro f hf
            have hf' := (Finset.mem_filter.mp hf).2
            exact ⟨by simpa [he] using hf'.1, hf'.2⟩
          have hused : used.card < k := by
            apply (show used.card ≤ (H.earlierNeighborSet rank e).ncard from ?_).trans_lt
              (hearlier e)
            calc
              used.card ≤ adjacent.card := Finset.card_image_le
              _ = (adjacent : Set E).ncard := by simp
              _ ≤ (H.earlierNeighborSet rank e).ncard :=
                Set.ncard_le_ncard hadjacent
          obtain ⟨a, _, ha⟩ :=
            Finset.exists_mem_notMem_of_card_lt_card
              (s := used) (t := Finset.univ) (by simpa using hused)
          let c' : E → Fin k := Function.update c e a
          refine ⟨c', ?_⟩
          intro x y hx hy hxy hinter
          have hxle : rank x ≤ m := Nat.lt_succ_iff.mp hx
          have hyle : rank y ≤ m := Nat.lt_succ_iff.mp hy
          rcases hxle.eq_or_lt with hxm | hxm
          · have hxe : x = e := hrank (hxm.trans he.symm)
            subst x
            have hym : rank y < m := by
              exact hyle.lt_of_ne (fun hym ↦ hxy (hrank (he.trans hym.symm)))
            have hyadj : y ∈ adjacent :=
              Finset.mem_filter.mpr ⟨by simp, hym, hinter⟩
            have hcy : c y ∈ used := Finset.mem_image.mpr ⟨y, hyadj, rfl⟩
            have hay : a ≠ c y := fun hay ↦ ha (hay ▸ hcy)
            simpa [c', hxy, hxy.symm] using hay
          · rcases hyle.eq_or_lt with hym | hym
            · have hye : y = e := hrank (hym.trans he.symm)
              subst y
              have hinter' : (H.edge e ∩ H.edge x).Nonempty := by
                simpa [Set.inter_comm] using hinter
              have hxadj : x ∈ adjacent :=
                Finset.mem_filter.mpr ⟨by simp, hxm, hinter'⟩
              have hcx : c x ∈ used := Finset.mem_image.mpr ⟨x, hxadj, rfl⟩
              have hax : a ≠ c x := fun hax ↦ ha (hax ▸ hcx)
              simpa [c', hxy, hxy.symm] using hax.symm
            · have hxe : x ≠ e := fun h ↦ by subst x; omega
              have hye : y ≠ e := fun h ↦ by subst y; omega
              simpa [c', hxe, hye] using hc hxm hym hxy hinter
        · refine ⟨c, ?_⟩
          intro e f he hf hef hinter
          have he' : rank e < m :=
            (Nat.lt_succ_iff.mp he).lt_of_ne fun hem ↦ hex ⟨e, hem⟩
          have hf' : rank f < m :=
            (Nat.lt_succ_iff.mp hf).lt_of_ne fun hfm ↦ hex ⟨f, hfm⟩
          exact hc he' hf' hef hinter
  let bound : ℕ := ∑ e : E, (rank e + 1)
  have hbelow (e : E) : rank e < bound := by
    have hterm : rank e + 1 ≤ bound := by
      simpa [bound] using
        (Finset.single_le_sum (f := fun f : E ↦ rank f + 1)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e))
    exact (Nat.lt_succ_self (rank e)).trans_le hterm
  obtain ⟨c, hc⟩ := aux bound
  refine ⟨{ color := c, valid := ?_ }⟩
  intro e f hef hinter
  exact hc (hbelow e) (hbelow f) hef hinter

/-- Finite peeling/degeneracy coloring.  If every nonempty edge subfamily has
an edge with fewer than `k` conflicts inside that subfamily, recursively remove
such an edge and color it last. -/
theorem edgeColorable_of_peelable [Fintype E]
    (H : IndexedHypergraph X E) {k : ℕ} (hk : 0 < k)
    (hpeel : ∀ S : Set E, S.Nonempty →
      ∃ e ∈ S, (H.internalNeighborSet S e).ncard < k) :
    H.EdgeColorable k := by
  classical
  let fallback : Fin k := ⟨0, hk⟩
  have aux (S : Finset E) : ∃ c : E → Fin k,
      ∀ ⦃e f : E⦄, e ∈ S → f ∈ S → e ≠ f →
        (H.edge e ∩ H.edge f).Nonempty → c e ≠ c f := by
    induction S using Finset.strongInductionOn
    rename_i S ih
    obtain rfl | hSnonempty := S.eq_empty_or_nonempty
    · exact ⟨fun _ ↦ fallback, by simp⟩
    · have hSetNonempty : (S : Set E).Nonempty := by
        simpa using hSnonempty
      obtain ⟨e, heS, hedegree⟩ := hpeel (S : Set E) hSetNonempty
      obtain ⟨c, hc⟩ := ih (S.erase e) (Finset.erase_ssubset heS)
      let adjacent : Finset E := (S.erase e).filter fun f ↦
        (H.edge e ∩ H.edge f).Nonempty
      let used : Finset (Fin k) := adjacent.image c
      have hadjacent : (adjacent : Set E) ⊆ H.internalNeighborSet (S : Set E) e := by
        intro f hf
        have hf' := Finset.mem_filter.mp hf
        exact ⟨Finset.mem_of_mem_erase hf'.1, (Finset.ne_of_mem_erase hf'.1).symm, hf'.2⟩
      have hused : used.card < k := by
        apply (show used.card ≤ (H.internalNeighborSet (S : Set E) e).ncard from ?_).trans_lt
          hedegree
        calc
          used.card ≤ adjacent.card := Finset.card_image_le
          _ = (adjacent : Set E).ncard := by simp
          _ ≤ (H.internalNeighborSet (S : Set E) e).ncard :=
            Set.ncard_le_ncard hadjacent
      obtain ⟨a, _, ha⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card
          (s := used) (t := Finset.univ) (by simpa using hused)
      let c' : E → Fin k := Function.update c e a
      refine ⟨c', ?_⟩
      intro x y hx hy hxy hinter
      by_cases hxe : x = e
      · subst x
        have hyerase : y ∈ S.erase e := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
        have hyadjacent : y ∈ adjacent := Finset.mem_filter.mpr ⟨hyerase, hinter⟩
        have hcy : c y ∈ used := Finset.mem_image.mpr ⟨y, hyadjacent, rfl⟩
        have hay : a ≠ c y := fun hay ↦ ha (hay ▸ hcy)
        simpa [c', hxy, hxy.symm] using hay
      · by_cases hye : y = e
        · subst y
          have hinter' : (H.edge e ∩ H.edge x).Nonempty := by
            simpa [Set.inter_comm] using hinter
          have hxerase : x ∈ S.erase e := Finset.mem_erase.mpr ⟨hxe, hx⟩
          have hxadjacent : x ∈ adjacent := Finset.mem_filter.mpr ⟨hxerase, hinter'⟩
          have hcx : c x ∈ used := Finset.mem_image.mpr ⟨x, hxadjacent, rfl⟩
          have hax : a ≠ c x := fun hax ↦ ha (hax ▸ hcx)
          simpa [c', hxy, hxy.symm] using hax.symm
        · have hxerase : x ∈ S.erase e := Finset.mem_erase.mpr ⟨hxe, hx⟩
          have hyerase : y ∈ S.erase e := Finset.mem_erase.mpr ⟨hye, hy⟩
          simpa [c', hxe, hye] using hc hxerase hyerase hxy hinter
  obtain ⟨c, hc⟩ := aux Finset.univ
  refine ⟨{ color := c, valid := ?_ }⟩
  intro e f hef hinter
  exact hc (by simp) (by simp) hef hinter

/-- The peeling dichotomy: either greedy peeling yields a `k`-edge-coloring,
or some nonempty subfamily has internal conflict degree at least `k` at every
edge.  KKKMO's reordering lemma refines the structure of this dense branch. -/
theorem edgeColorable_or_dense_subfamily [Fintype E]
    (H : IndexedHypergraph X E) {k : ℕ} (hk : 0 < k) :
    H.EdgeColorable k ∨
      ∃ S : Set E, S.Nonempty ∧
        ∀ e ∈ S, k ≤ (H.internalNeighborSet S e).ncard := by
  classical
  by_cases hpeel : ∀ S : Set E, S.Nonempty →
      ∃ e ∈ S, (H.internalNeighborSet S e).ncard < k
  · exact Or.inl (H.edgeColorable_of_peelable hk hpeel)
  · right
    push Not at hpeel
    obtain ⟨S, hS, hdegree⟩ := hpeel
    refine ⟨S, hS, ?_⟩
    intro e he
    exact hdegree e he

end IndexedHypergraph

/-! ## Set-valued hypergraphs (the published theorem's formulation) -/

/-- A hypergraph on `X` in the standard simple/set-valued sense: its edges
form a set of subsets of `X`. -/
abbrev SetHypergraph (X : Type u) := Set (Set X)

namespace SetHypergraph

variable {X : Type u}

/-- A hypergraph on a finite vertex type has only finitely many possible
set-valued edges. -/
noncomputable instance instFintypeEdges [Fintype X] (H : SetHypergraph X) : Fintype H :=
  Fintype.ofFinite H

/-- Proper edge colorings of a set-valued hypergraph. -/
structure EdgeColoring (H : SetHypergraph X) (κ : Type*) where
  color : H → κ
  valid : ∀ ⦃e f : H⦄, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f

instance {H : SetHypergraph X} {κ : Type*} : CoeFun (H.EdgeColoring κ) fun _ ↦ H → κ :=
  ⟨EdgeColoring.color⟩

/-- A set-valued hypergraph is linear when distinct edges meet in at most one
vertex. -/
def IsLinear (H : SetHypergraph X) : Prop :=
  H.Pairwise fun e f ↦ (e ∩ f).Subsingleton

/-- The edges of `H` incident with `x`, retained as elements of the edge
subtype `H`. -/
def incidentEdges (H : SetHypergraph X) (x : X) : Set H :=
  {e | x ∈ e.1}

noncomputable instance instFintypeIncidentEdges [Fintype X]
    (H : SetHypergraph X) (x : X) : Fintype (H.incidentEdges x) :=
  Fintype.ofFinite (H.incidentEdges x)

/-- In a finite simple linear hypergraph, every vertex has degree at most the
number of vertices.  Nonsingleton incident edges inject into the other
vertices by choosing one point besides `x`; linearity makes those choices
distinct, while a possible singleton edge is represented by `x` itself. -/
lemma incidentEdges_ncard_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (x : X) :
    (H.incidentEdges x).ncard ≤ Fintype.card X := by
  classical
  let _ : Fintype (H.incidentEdges x) := Fintype.ofFinite (H.incidentEdges x)
  let hasOther (e : H.incidentEdges x) : Prop :=
    ∃ y, y ∈ e.1.1 ∧ y ≠ x
  let representative (e : H.incidentEdges x) : X :=
    if he : hasOther e then Classical.choose he else x
  have representative_mem (e : H.incidentEdges x) : representative e ∈ e.1.1 := by
    simp only [representative]
    split
    next he => exact (Classical.choose_spec he).1
    next _ => exact e.2
  have representative_ne (e : H.incidentEdges x) (he : hasOther e) :
      representative e ≠ x := by
    simp only [representative, dif_pos he]
    exact (Classical.choose_spec he).2
  have edge_eq_singleton (e : H.incidentEdges x) (he : ¬hasOther e) :
      e.1.1 = {x} := by
    ext y
    constructor
    · intro hy
      have hyx : y = x := by
        by_contra hyx
        exact he ⟨y, hy, hyx⟩
      simpa [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact e.2
  have representative_injective : Function.Injective representative := by
    intro e f href
    apply Subtype.ext
    apply Subtype.ext
    by_cases he : hasOther e
    · by_cases hf : hasOther f
      · by_contra hef
        have hsub : (e.1.1 ∩ f.1.1).Subsingleton :=
          hlinear e.1.2 f.1.2 hef
        have hxmem : x ∈ e.1.1 ∩ f.1.1 := ⟨e.2, f.2⟩
        have hrmem : representative e ∈ e.1.1 ∩ f.1.1 := by
          refine ⟨representative_mem e, ?_⟩
          rw [href]
          exact representative_mem f
        exact (representative_ne e he) (hsub hrmem hxmem)
      · have hfx : representative f = x := by simp [representative, hf]
        exfalso
        exact (representative_ne e he) (href.trans hfx)
    · by_cases hf : hasOther f
      · have hex : representative e = x := by simp [representative, he]
        exfalso
        exact (representative_ne f hf) (href.symm.trans hex)
      · exact (edge_eq_singleton e he).trans (edge_eq_singleton f hf).symm
  let embedding : H.incidentEdges x ↪ X :=
    ⟨representative, representative_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  simpa only [Set.fintypeCard_eq_ncard] using hcard

/-- Incidence double counting for an edge family `S` and vertex family
`bad`.  This is the abstract form of (5.11). -/
lemma vertex_edge_incidence_bound [Fintype X] (H : SetHypergraph X)
    (S : Finset H) (bad : Finset X)
    [DecidableRel fun (e : H) (x : X) ↦ x ∈ e.1]
    (q k : ℕ)
    (hvertex : ∀ x ∈ bad, q ≤ (S.filter fun e ↦ x ∈ e.1).card)
    (hedge : ∀ e ∈ S, (bad.filter fun x ↦ x ∈ e.1).card ≤ k) :
    bad.card * q ≤ S.card * k := by
  classical
  exact finset_card_mul_le_of_bipartite_degrees S bad
    (fun e x ↦ x ∈ e.1) q k hvertex hedge

/-- The same incidence count with the two bipartition classes exchanged. -/
lemma edge_vertex_incidence_bound [Fintype X] (H : SetHypergraph X)
    (S : Finset H) (bad : Finset X)
    [DecidableRel fun (x : X) (e : H) ↦ x ∈ e.1]
    (q k : ℕ)
    (hedge : ∀ e ∈ S, q ≤ (bad.filter fun x ↦ x ∈ e.1).card)
    (hvertex : ∀ x ∈ bad, (S.filter fun e ↦ x ∈ e.1).card ≤ k) :
    S.card * q ≤ bad.card * k := by
  classical
  exact finset_card_mul_le_of_bipartite_degrees bad S
    (fun x e ↦ x ∈ e.1) q k hedge hvertex

/-- Weighted incidence budget at one vertex.  For a linear hypergraph, the
sets `e \ {x}` over all edges incident with `x` are pairwise disjoint subsets
of `X \ {x}`. -/
lemma sum_incident_ncard_sub_one_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (x : X) :
    (∑ e : H.incidentEdges x, (e.1.1.ncard - 1)) ≤ Fintype.card X - 1 := by
  classical
  let Fiber (e : H.incidentEdges x) := (e.1.1 \ {x} : Set X)
  let code (p : Σ e : H.incidentEdges x, Fiber e) : (Set.univ \ {x} : Set X) :=
    ⟨p.2.1, ⟨Set.mem_univ _, p.2.2.2⟩⟩
  have code_injective : Function.Injective code := by
    intro p q hcode
    have hpoint : p.2.1 = q.2.1 := congrArg Subtype.val hcode
    have hedge : p.1.1 = q.1.1 := by
      apply Subtype.ext
      by_contra hpq
      have hsub : (p.1.1.1 ∩ q.1.1.1).Subsingleton :=
        hlinear p.1.1.2 q.1.1.2 hpq
      have hxmem : x ∈ p.1.1.1 ∩ q.1.1.1 := ⟨p.1.2, q.1.2⟩
      have hypmem : p.2.1 ∈ p.1.1.1 ∩ q.1.1.1 := by
        refine ⟨p.2.2.1, ?_⟩
        rw [hpoint]
        exact q.2.2.1
      exact p.2.2.2 (hsub hypmem hxmem)
    have hindex : p.1 = q.1 := Subtype.ext hedge
    apply Sigma.ext hindex
    exact (Subtype.heq_iff_coe_eq (fun z ↦ by rw [hindex])).2 hpoint
  let embedding : (Σ e : H.incidentEdges x, Fiber e) ↪
      (Set.univ \ {x} : Set X) := ⟨code, code_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  have hdiff (e : H.incidentEdges x) :
      (e.1.1 \ {x}).ncard = e.1.1.ncard - 1 := by
    have hex : x ∈ e.1.1 := e.2
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hex)]
    simp
  calc
    (∑ e : H.incidentEdges x, (e.1.1.ncard - 1)) =
        ∑ e : H.incidentEdges x, Fintype.card (Fiber e) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Set.fintypeCard_eq_ncard, hdiff]
    _ = Fintype.card (Σ e : H.incidentEdges x, Fiber e) := by
      rw [Fintype.card_sigma]
    _ ≤ Fintype.card (Set.univ \ {x} : Set X) := hcard
    _ = (Set.univ \ {x} : Set X).ncard := Set.fintypeCard_eq_ncard _
    _ = Fintype.card X - 1 := by
      rw [Set.ncard_sdiff (show ({x} : Set X) ⊆ Set.univ by simp)]
      simp

/-- If all edges through `x` have size at least `r`, their number times
`r-1` is bounded by the off-`x` vertex budget. -/
lemma incidentEdges_ncard_mul_sub_one_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (x : X) (r : ℕ)
    (hsize : ∀ e ∈ H.incidentEdges x, r ≤ e.1.ncard) :
    (H.incidentEdges x).ncard * (r - 1) ≤ Fintype.card X - 1 := by
  classical
  calc
    (H.incidentEdges x).ncard * (r - 1) =
        ∑ _e ∈ (H.incidentEdges x).toFinset, (r - 1) := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    _ ≤ ∑ e ∈ (H.incidentEdges x).toFinset, (e.1.ncard - 1) := by
      apply Finset.sum_le_sum
      intro e he
      exact Nat.sub_le_sub_right (hsize e (Set.mem_toFinset.mp he)) 1
    _ = ∑ e : H.incidentEdges x, (e.1.1.ncard - 1) := by
      exact Finset.sum_subtype (H.incidentEdges x).toFinset
        (fun e ↦ Set.mem_toFinset) (fun e ↦ e.1.ncard - 1)
    _ ≤ Fintype.card X - 1 := H.sum_incident_ncard_sub_one_le hlinear x

/-- A subfamily version of the preceding incidence budget. -/
lemma incidentSubfamily_ncard_mul_sub_one_le [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (S : Set H) (x : X) (r : ℕ)
    (hincident : S ⊆ H.incidentEdges x)
    (hsize : ∀ e ∈ S, r ≤ e.1.ncard) :
    S.ncard * (r - 1) ≤ Fintype.card X - 1 := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  have hfin : S.toFinset ⊆ (H.incidentEdges x).toFinset := by
    intro e he
    exact Set.mem_toFinset.mpr (hincident (Set.mem_toFinset.mp he))
  calc
    S.ncard * (r - 1) = ∑ _e ∈ S.toFinset, (r - 1) := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    _ ≤ ∑ e ∈ S.toFinset, (e.1.ncard - 1) := by
      apply Finset.sum_le_sum
      intro e he
      exact Nat.sub_le_sub_right (hsize e (Set.mem_toFinset.mp he)) 1
    _ ≤ ∑ e ∈ (H.incidentEdges x).toFinset, (e.1.ncard - 1) :=
      Finset.sum_le_sum_of_subset hfin
    _ = ∑ e : H.incidentEdges x, (e.1.1.ncard - 1) := by
      exact Finset.sum_subtype (H.incidentEdges x).toFinset
        (fun e ↦ Set.mem_toFinset) (fun e ↦ e.1.ncard - 1)
    _ ≤ Fintype.card X - 1 := H.sum_incident_ncard_sub_one_le hlinear x

/-- Incident edges through `x` whose cardinality is strictly below `k`.
This is the family denoted `A_x` in Proposition 5.5. -/
def smallIncidentEdges (H : SetHypergraph X) (x : X) (k : ℕ) : Set H :=
  {e | x ∈ e.1 ∧ e.1.ncard < k}

lemma smallIncidentEdges_ncard_le_incidentEdges [Fintype X]
    (H : SetHypergraph X) (x : X) (k : ℕ) :
    (H.smallIncidentEdges x k).ncard ≤ (H.incidentEdges x).ncard := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  exact Set.ncard_le_ncard (fun _e he ↦ he.1) (Set.toFinite _)

/-- Equation (5.11) before the paper's asymptotic simplification.  Vertices
incident with at least `q` sub-scale edges are few because every such edge has
at most `k-1` vertices. -/
lemma badVertices_ncard_mul_le_subscaleEdges [Fintype X]
    (H : SetHypergraph X) (k q : ℕ) :
    ({x | q ≤ (H.smallIncidentEdges x k).ncard} : Set X).ncard * q ≤
      ({e : H | e.1.ncard < k} : Set H).ncard * (k - 1) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let S : Set H := {e | e.1.ncard < k}
  let bad : Set X := {x | q ≤ (H.smallIncidentEdges x k).ncard}
  letI : DecidableRel (fun (e : H) (x : X) ↦ x ∈ e.1) :=
    fun _ _ ↦ Classical.propDecidable _
  have hvertex : ∀ x ∈ bad.toFinset,
      q ≤ (S.toFinset.filter fun e ↦ x ∈ e.1).card := by
    intro x hx
    have hxq : q ≤ (H.smallIncidentEdges x k).ncard := by
      have hxbad : x ∈ bad := Set.mem_toFinset.mp hx
      change q ≤ (H.smallIncidentEdges x k).ncard at hxbad
      exact hxbad
    have hset :
        (↑(S.toFinset.filter fun e ↦ x ∈ e.1) : Set H) =
          H.smallIncidentEdges x k := by
      ext e
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset]
      change (e.1.ncard < k ∧ x ∈ e.1) ↔ x ∈ e.1 ∧ e.1.ncard < k
      tauto
    have hncard := congrArg Set.ncard hset
    calc
      q ≤ (H.smallIncidentEdges x k).ncard := hxq
      _ = (↑(S.toFinset.filter fun e ↦ x ∈ e.1) : Set H).ncard := hncard.symm
      _ = (S.toFinset.filter fun e ↦ x ∈ e.1).card :=
        Set.ncard_coe_finset _
  have hedge : ∀ e ∈ S.toFinset,
      (bad.toFinset.filter fun x ↦ x ∈ e.1).card ≤ k - 1 := by
    intro e he
    have hesmall : e.1.ncard < k := by
      have heS : e ∈ S := Set.mem_toFinset.mp he
      change e.1.ncard < k at heS
      exact heS
    calc
      (bad.toFinset.filter fun x ↦ x ∈ e.1).card ≤ e.1.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        have hxe := (Finset.mem_filter.mp hx).2
        exact Set.mem_toFinset.mpr hxe
      _ = e.1.ncard := (Set.ncard_eq_toFinset_card' e.1).symm
      _ ≤ k - 1 := by omega
  have hcount := H.vertex_edge_incidence_bound S.toFinset bad.toFinset
    q (k - 1) hvertex hedge
  have hcount' : bad.ncard * q ≤ S.ncard * (k - 1) := by
    calc
      bad.ncard * q = bad.toFinset.card * q := by
        rw [Set.ncard_eq_toFinset_card']
      _ ≤ S.toFinset.card * (k - 1) := hcount
      _ = S.ncard * (k - 1) := by rw [Set.ncard_eq_toFinset_card']
  simpa only [S, bad] using hcount'

/-- Equation (5.12) before asymptotic simplification.  Projective-scale edges
containing at least `s` bad vertices are bounded by the bad-vertex count times
the maximum possible projective-scale degree. -/
lemma heavyProjectiveEdges_ncard_mul_le_badVertices [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (k s : ℕ) (hk : 2 ≤ k)
    (bad : Set X) :
    ({e : H | e.1.ncard = k ∧ s ≤ (e.1 ∩ bad).ncard} : Set H).ncard * s ≤
      bad.ncard * ((Fintype.card X - 1) / (k - 1)) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let heavy : Set H := {e | e.1.ncard = k ∧ s ≤ (e.1 ∩ bad).ncard}
  letI : DecidableRel (fun (x : X) (e : H) ↦ x ∈ e.1) :=
    fun _ _ ↦ Classical.propDecidable _
  have hedge : ∀ e ∈ heavy.toFinset,
      s ≤ (bad.toFinset.filter fun x ↦ x ∈ e.1).card := by
    intro e he
    have heheavy : e ∈ heavy := Set.mem_toFinset.mp he
    have hes : s ≤ (e.1 ∩ bad).ncard := heheavy.2
    have hset :
        (↑(bad.toFinset.filter fun x ↦ x ∈ e.1) : Set X) = e.1 ∩ bad := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset,
        Set.mem_inter_iff]
      tauto
    have hncard := congrArg Set.ncard hset
    calc
      s ≤ (e.1 ∩ bad).ncard := hes
      _ = (↑(bad.toFinset.filter fun x ↦ x ∈ e.1) : Set X).ncard := hncard.symm
      _ = (bad.toFinset.filter fun x ↦ x ∈ e.1).card :=
        Set.ncard_coe_finset _
  have hvertex : ∀ x ∈ bad.toFinset,
      (heavy.toFinset.filter fun e ↦ x ∈ e.1).card ≤
        (Fintype.card X - 1) / (k - 1) := by
    intro x _hx
    let P : Set H := {e | e.1.ncard = k ∧ x ∈ e.1}
    have hsubset :
        heavy.toFinset.filter (fun e ↦ x ∈ e.1) ⊆ P.toFinset := by
      intro e he
      have he' := Finset.mem_filter.mp he
      have heheavy : e ∈ heavy := Set.mem_toFinset.mp he'.1
      exact Set.mem_toFinset.mpr ⟨heheavy.1, he'.2⟩
    have hPincident : P ⊆ H.incidentEdges x := by
      intro e he
      exact he.2
    have hPsize : ∀ e ∈ P, k ≤ e.1.ncard := by
      intro e he
      exact he.1.ge
    have hPbudget := H.incidentSubfamily_ncard_mul_sub_one_le hlinear
      P x k hPincident hPsize
    have hkpos : 0 < k - 1 := by omega
    have hPdiv : P.ncard ≤ (Fintype.card X - 1) / (k - 1) :=
      (Nat.le_div_iff_mul_le hkpos).2 hPbudget
    calc
      (heavy.toFinset.filter fun e ↦ x ∈ e.1).card ≤ P.toFinset.card :=
        Finset.card_le_card hsubset
      _ = P.ncard := (Set.ncard_eq_toFinset_card' P).symm
      _ ≤ (Fintype.card X - 1) / (k - 1) := hPdiv
  have hcount := H.edge_vertex_incidence_bound heavy.toFinset bad.toFinset
    s ((Fintype.card X - 1) / (k - 1)) hedge hvertex
  have hcount' : heavy.ncard * s ≤
      bad.ncard * ((Fintype.card X - 1) / (k - 1)) := by
    calc
      heavy.ncard * s = heavy.toFinset.card * s := by
        rw [Set.ncard_eq_toFinset_card']
      _ ≤ bad.toFinset.card * ((Fintype.card X - 1) / (k - 1)) := hcount
      _ = bad.ncard * ((Fintype.card X - 1) / (k - 1)) := by
        rw [Set.ncard_eq_toFinset_card']
  simpa only [heavy] using hcount'

/-- A projective-scale edge which is not heavy on `bad` retains many vertices
outside `bad`.  The hypothesis `q+s ≤ k+1` is the exact integral rounding of
`q ≤ k-(s-1)`. -/
lemma ncard_sdiff_ge_of_ncard_inter_lt [Fintype X]
    (e bad : Set X) (k s q : ℕ) (he : e.ncard = k)
    (hinter : (e ∩ bad).ncard < s) (hqs : q + s ≤ k + 1) :
    q ≤ (e \ bad).ncard := by
  have hsubset : e ∩ bad ⊆ e := Set.inter_subset_left
  have hdiff : (e \ bad).ncard = e.ncard - (e ∩ bad).ncard := by
    rw [show e \ bad = e \ (e ∩ bad) by
      ext x
      simp only [Set.mem_diff, Set.mem_inter_iff]
      tauto]
    exact Set.ncard_sdiff hsubset
  rw [hdiff, he]
  omega

/-- The two-tier incidence estimate underlying the second case of Proposition
5.5.  If every edge has size at least `r`, then the `m` incident edges smaller
than `k` contribute at least `m (r-1)` to the incidence-pair sum, while every
other incident edge contributes at least `k-1`. -/
lemma incident_two_tier_weight_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (x : X) (r k : ℕ)
    (hmin : ∀ e : H, r ≤ e.1.ncard) :
    ((H.incidentEdges x).ncard - (H.smallIncidentEdges x k).ncard) * (k - 1) +
        (H.smallIncidentEdges x k).ncard * (r - 1) ≤
      Fintype.card X - 1 := by
  classical
  let I := H.incidentEdges x
  let A := H.smallIncidentEdges x k
  have hAI : A ⊆ I := by
    intro e he
    exact he.1
  have hdiffcard : (I \ A).ncard = I.ncard - A.ncard :=
    Set.ncard_sdiff hAI
  have hsmall : A.ncard * (r - 1) ≤
      ∑ e ∈ A.toFinset, (e.1.ncard - 1) := by
    calc
      A.ncard * (r - 1) = ∑ _e ∈ A.toFinset, (r - 1) := by
        rw [Set.ncard_eq_toFinset_card']
        simp
      _ ≤ ∑ e ∈ A.toFinset, (e.1.ncard - 1) := by
        apply Finset.sum_le_sum
        intro e _
        exact Nat.sub_le_sub_right (hmin e) 1
  have hlarge : (I \ A).ncard * (k - 1) ≤
      ∑ e ∈ (I \ A).toFinset, (e.1.ncard - 1) := by
    calc
      (I \ A).ncard * (k - 1) =
          ∑ _e ∈ (I \ A).toFinset, (k - 1) := by
        rw [Set.ncard_eq_toFinset_card']
        simp
      _ ≤ ∑ e ∈ (I \ A).toFinset, (e.1.ncard - 1) := by
        apply Finset.sum_le_sum
        intro e he
        have heI : e ∈ I := (Set.mem_toFinset.mp he).1
        have heA : e ∉ A := (Set.mem_toFinset.mp he).2
        have hek : k ≤ e.1.ncard := by
          have hnlt : ¬ e.1.ncard < k := by
            intro hlt
            apply heA
            exact ⟨heI, hlt⟩
          omega
        exact Nat.sub_le_sub_right hek 1
  have hsum_split :
      (∑ e ∈ (I \ A).toFinset, (e.1.ncard - 1)) +
          ∑ e ∈ A.toFinset, (e.1.ncard - 1) =
        ∑ e ∈ I.toFinset, (e.1.ncard - 1) := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext e
        simp only [Set.mem_toFinset, Set.mem_sdiff, Finset.mem_union]
        tauto
      · intro e _
        rfl
    · rw [Finset.disjoint_left]
      intro e hediff heA
      exact (Set.mem_toFinset.mp hediff).2 (Set.mem_toFinset.mp heA)
  have htotal :
      ∑ e ∈ I.toFinset, (e.1.ncard - 1) ≤ Fintype.card X - 1 := by
    calc
      ∑ e ∈ I.toFinset, (e.1.ncard - 1) =
          ∑ e : H.incidentEdges x, (e.1.1.ncard - 1) := by
        exact Finset.sum_subtype I.toFinset
          (fun e ↦ Set.mem_toFinset) (fun e ↦ e.1.ncard - 1)
      _ ≤ Fintype.card X - 1 := H.sum_incident_ncard_sub_one_le hlinear x
  rw [← hdiffcard]
  exact (Nat.add_le_add hlarge hsmall).trans (hsum_split.le.trans htotal)

/-- The other edges of a set-valued hypergraph which meet `e`. -/
def neighborEdges (H : SetHypergraph X) (e : H) : Set H :=
  {f | e ≠ f ∧ (e.1 ∩ f.1).Nonempty}

noncomputable instance instFintypeNeighborEdges [Fintype X]
    (H : SetHypergraph X) (e : H) : Fintype (H.neighborEdges e) :=
  Fintype.ofFinite (H.neighborEdges e)

/-- A first counting consequence of linearity.  For each neighbor `f` of
`e`, choose their unique common point `x`; at this fixed `x`, incident edges
inject into the ambient vertex type.  Thus the neighbors inject into
`e × X`. -/
lemma neighborEdges_ncard_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) :
    (H.neighborEdges e).ncard ≤ e.1.ncard * Fintype.card X := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype (H.neighborEdges e) := Fintype.ofFinite (H.neighborEdges e)
  let _ (x : X) : Fintype (H.incidentEdges x) :=
    Fintype.ofFinite (H.incidentEdges x)
  let meetingPoint (f : H.neighborEdges e) : X := Classical.choose f.2.2
  have meetingPoint_mem_left (f : H.neighborEdges e) : meetingPoint f ∈ e.1 :=
    (Classical.choose_spec f.2.2).1
  have meetingPoint_mem_right (f : H.neighborEdges e) : meetingPoint f ∈ f.1.1 :=
    (Classical.choose_spec f.2.2).2
  let code (f : H.neighborEdges e) :
      Σ x : (e.1 : Set X), H.incidentEdges x.1 :=
    ⟨⟨meetingPoint f, meetingPoint_mem_left f⟩,
      ⟨f.1, meetingPoint_mem_right f⟩⟩
  have code_injective : Function.Injective code := by
    intro f g hcode
    apply Subtype.ext
    exact congrArg (fun p : Σ x : (e.1 : Set X), H.incidentEdges x.1 ↦ p.2.1) hcode
  let embedding : H.neighborEdges e ↪
      (Σ x : (e.1 : Set X), H.incidentEdges x.1) :=
    ⟨code, code_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  calc
    (H.neighborEdges e).ncard = Fintype.card (H.neighborEdges e) := by
      symm
      exact Set.fintypeCard_eq_ncard (H.neighborEdges e)
    _ ≤ Fintype.card (Σ x : (e.1 : Set X), H.incidentEdges x.1) := hcard
    _ = ∑ x : (e.1 : Set X), Fintype.card (H.incidentEdges x.1) :=
      Fintype.card_sigma
    _ ≤ ∑ _x : (e.1 : Set X), Fintype.card X := by
      apply Finset.sum_le_sum
      intro x _
      rw [Set.fintypeCard_eq_ncard]
      exact H.incidentEdges_ncard_le hlinear x.1
    _ = Fintype.card (e.1 : Set X) * Fintype.card X := by simp
    _ = e.1.ncard * Fintype.card X := by rw [Set.fintypeCard_eq_ncard]

/-- Edges other than `e` and `f` which intersect both of them. -/
def commonNeighborEdges (H : SetHypergraph X) (e f : H) : Set H :=
  H.neighborEdges e ∩ H.neighborEdges f

/-- The common-neighborhood estimate used at the start of Proposition 5.5.
If distinct linear-hypergraph edges `e` and `f` meet at `w`, then a common
neighbor through `w` is one of the other edges incident with `w`; a common
neighbor not through `w` injects into `(e \ {w}) × (f \ {w})` by its two
intersection points. -/
lemma commonNeighborEdges_ncard_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e f : H) (hef : e ≠ f)
    (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1) :
    (H.commonNeighborEdges e f).ncard ≤
      (e.1.ncard - 1) * (f.1.ncard - 1) +
        (H.incidentEdges w).ncard - 2 := by
  classical
  let _ : Fintype (H.commonNeighborEdges e f) :=
    Fintype.ofFinite (H.commonNeighborEdges e f)
  let meetE (g : H.commonNeighborEdges e f) : X :=
    Classical.choose g.2.1.2
  let meetF (g : H.commonNeighborEdges e f) : X :=
    Classical.choose g.2.2.2
  have meetE_mem_e (g : H.commonNeighborEdges e f) : meetE g ∈ e.1 :=
    (Classical.choose_spec g.2.1.2).1
  have meetE_mem_g (g : H.commonNeighborEdges e f) : meetE g ∈ g.1.1 :=
    (Classical.choose_spec g.2.1.2).2
  have meetF_mem_f (g : H.commonNeighborEdges e f) : meetF g ∈ f.1 :=
    (Classical.choose_spec g.2.2.2).1
  have meetF_mem_g (g : H.commonNeighborEdges e f) : meetF g ∈ g.1.1 :=
    (Classical.choose_spec g.2.2.2).2
  have meetE_ne_w (g : H.commonNeighborEdges e f) (hwg : w ∉ g.1.1) :
      meetE g ≠ w := fun h ↦ hwg (h ▸ meetE_mem_g g)
  have meetF_ne_w (g : H.commonNeighborEdges e f) (hwg : w ∉ g.1.1) :
      meetF g ≠ w := fun h ↦ hwg (h ▸ meetF_mem_g g)
  let A := (e.1 \ {w} : Set X) × (f.1 \ {w} : Set X)
  let B := (H.incidentEdges w \ ({e, f} : Set H) : Set H)
  let code (g : H.commonNeighborEdges e f) : A ⊕ B :=
    if hwg : w ∈ g.1.1 then
      Sum.inr ⟨g.1, ⟨hwg, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hge ↦ g.2.1.1 hge.symm,
          fun hgf ↦ g.2.2.1 hgf.symm⟩⟩⟩
    else
      Sum.inl
        (⟨meetE g, meetE_mem_e g, by simpa using meetE_ne_w g hwg⟩,
          ⟨meetF g, meetF_mem_f g, by simpa using meetF_ne_w g hwg⟩)
  have code_injective : Function.Injective code := by
    intro g h hcode
    by_cases hwg : w ∈ g.1.1
    · by_cases hwh : w ∈ h.1.1
      · have hright :
            (⟨g.1, by
              exact ⟨hwg, by
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                exact ⟨fun hge ↦ g.2.1.1 hge.symm,
                  fun hgf ↦ g.2.2.1 hgf.symm⟩⟩⟩ : B) =
              ⟨h.1, by
                exact ⟨hwh, by
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                  exact ⟨fun hhe ↦ h.2.1.1 hhe.symm,
                    fun hhf ↦ h.2.2.1 hhf.symm⟩⟩⟩ := by
          have hproject := congrArg
            (fun z : A ⊕ B ↦ match z with
              | Sum.inl _ => none
              | Sum.inr b => some b) hcode
          simpa [code, hwg, hwh] using hproject
        apply Subtype.ext
        exact congrArg (fun z : B ↦ z.1) hright
      · have hcontra :
            (Sum.inr ⟨g.1, by
              exact ⟨hwg, by
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                exact ⟨fun hge ↦ g.2.1.1 hge.symm,
                  fun hgf ↦ g.2.2.1 hgf.symm⟩⟩⟩ : A ⊕ B) =
              Sum.inl
                (⟨meetE h, meetE_mem_e h, by simpa using meetE_ne_w h hwh⟩,
                  ⟨meetF h, meetF_mem_f h, by simpa using meetF_ne_w h hwh⟩) := by
          simpa [code, hwg, hwh] using hcode
        exact (Sum.inr_ne_inl hcontra).elim
    · by_cases hwh : w ∈ h.1.1
      · have hcontra :
            (Sum.inl
              (⟨meetE g, meetE_mem_e g, by simpa using meetE_ne_w g hwg⟩,
                ⟨meetF g, meetF_mem_f g, by simpa using meetF_ne_w g hwg⟩) : A ⊕ B) =
              Sum.inr ⟨h.1, by
                exact ⟨hwh, by
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                  exact ⟨fun hhe ↦ h.2.1.1 hhe.symm,
                    fun hhf ↦ h.2.2.1 hhf.symm⟩⟩⟩ := by
          simpa [code, hwg, hwh] using hcode
        exact (Sum.inl_ne_inr hcontra).elim
      · have hleft :
            ((⟨meetE g, meetE_mem_e g, by simpa using meetE_ne_w g hwg⟩,
              ⟨meetF g, meetF_mem_f g, by simpa using meetF_ne_w g hwg⟩) : A) =
            (⟨meetE h, meetE_mem_e h, by simpa using meetE_ne_w h hwh⟩,
              ⟨meetF h, meetF_mem_f h, by simpa using meetF_ne_w h hwh⟩) := by
          have hproject := congrArg
            (fun z : A ⊕ B ↦ match z with
              | Sum.inl a => some a
              | Sum.inr _ => none) hcode
          simp only [code, dif_neg hwg, dif_neg hwh] at hproject
          exact Option.some.inj hproject
        have hx : meetE g = meetE h :=
          congrArg (fun p ↦ p.1.1) hleft
        have hy : meetF g = meetF h :=
          congrArg (fun p ↦ p.2.1) hleft
        apply Subtype.ext
        by_contra hgh
        have hsets : g.1.1 ≠ h.1.1 := fun h ↦ hgh (Subtype.ext h)
        have hsub : (g.1.1 ∩ h.1.1).Subsingleton :=
          hlinear g.1.2 h.1.2 hsets
        have hxmem : meetE g ∈ g.1.1 ∩ h.1.1 := by
          refine ⟨meetE_mem_g g, ?_⟩
          rw [hx]
          exact meetE_mem_g h
        have hymem : meetF g ∈ g.1.1 ∩ h.1.1 := by
          refine ⟨meetF_mem_g g, ?_⟩
          rw [hy]
          exact meetF_mem_g h
        have hxy : meetE g = meetF g := hsub hxmem hymem
        have hefsets : e.1 ≠ f.1 := fun h ↦ hef (Subtype.ext h)
        have hefsub : (e.1 ∩ f.1).Subsingleton := hlinear e.2 f.2 hefsets
        have hxinter : meetE g ∈ e.1 ∩ f.1 := by
          exact ⟨meetE_mem_e g, hxy ▸ meetF_mem_f g⟩
        have hwinter : w ∈ e.1 ∩ f.1 := ⟨hwe, hwf⟩
        exact hwg ((hefsub hxinter hwinter) ▸ meetE_mem_g g)
  let embedding : H.commonNeighborEdges e f ↪ A ⊕ B :=
    ⟨code, code_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  have hediff : (e.1 \ {w}).ncard = e.1.ncard - 1 := by
    rw [Set.ncard_sdiff (show ({w} : Set X) ⊆ e.1 by simpa using hwe)]
    simp
  have hfdiff : (f.1 \ {w}).ncard = f.1.ncard - 1 := by
    rw [Set.ncard_sdiff (show ({w} : Set X) ⊆ f.1 by simpa using hwf)]
    simp
  have hpairsubset : ({e, f} : Set H) ⊆ H.incidentEdges w := by
    intro g hg
    rcases hg with rfl | hg
    · exact hwe
    · have : g = f := by simpa using hg
      subst g
      exact hwf
  have hthrough :
      (H.incidentEdges w \ ({e, f} : Set H)).ncard =
        (H.incidentEdges w).ncard - 2 := by
    rw [Set.ncard_sdiff hpairsubset, Set.ncard_pair hef]
  calc
    (H.commonNeighborEdges e f).ncard =
        Fintype.card (H.commonNeighborEdges e f) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ ≤ Fintype.card
        (((e.1 \ {w} : Set X) × (f.1 \ {w} : Set X)) ⊕
          (H.incidentEdges w \ ({e, f} : Set H) : Set H)) := hcard
    _ = (e.1 \ {w}).ncard * (f.1 \ {w}).ncard +
        (H.incidentEdges w \ ({e, f} : Set H)).ncard := by
      rw [Fintype.card_sum, Fintype.card_prod,
        Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
        Set.fintypeCard_eq_ncard]
    _ = (e.1.ncard - 1) * (f.1.ncard - 1) +
        (H.incidentEdges w).ncard - 2 := by
      rw [hediff, hfdiff, hthrough]
      have hdeg : 2 ≤ (H.incidentEdges w).ncard := by
        rw [← Set.ncard_pair hef]
        exact Set.ncard_le_ncard hpairsubset
      omega

/-- The paper's notion of a useful pair (Section 5): two distinct intersecting
edges whose common line-graph neighborhood has at most `n - 2` vertices.  The
two-unit slack is the corrected threshold in the published proof. -/
def IsUseful (H : SetHypergraph X) (n : ℕ) (e f : H) : Prop :=
  e ≠ f ∧ (e.1 ∩ f.1).Nonempty ∧ (H.commonNeighborEdges e f).ncard ≤ n - 2

lemma IsUseful.symm {H : SetHypergraph X} {n : ℕ} {e f : H}
    (h : H.IsUseful n e f) : H.IsUseful n f e := by
  refine ⟨h.1.symm, ?_, ?_⟩
  · simpa [Set.inter_comm] using h.2.1
  · simpa [commonNeighborEdges, Set.inter_comm] using h.2.2

/-- The graph of useful pairs, used to package the iterative choice in Claim 1
of Lemma 5.1 as an ordinary matching problem. -/
def usefulPairGraph (H : SetHypergraph X) (n : ℕ) : SimpleGraph H where
  Adj e f := H.IsUseful n e f
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun e h ↦ h.1 rfl⟩

@[simp]
lemma usefulPairGraph_adj (H : SetHypergraph X) (n : ℕ) {e f : H} :
    (H.usefulPairGraph n).Adj e f ↔ H.IsUseful n e f :=
  Iff.rfl

/-- Restrict the useful-pair graph to a prescribed edge family. -/
def usefulPairGraphOn (H : SetHypergraph X) (n : ℕ) (S : Set H) :
    SimpleGraph S where
  Adj e f := H.IsUseful n e.1 f.1
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun e h ↦ h.1 (Subtype.ext rfl)⟩

/-- A residual-set condition produces `t` vertex-disjoint useful pairs.
This is the finite matching form of the iterative selection in Claim 1 of
Lemma 5.1. -/
lemma exists_useful_pairs_of_residual_condition [Fintype X]
    (H : SetHypergraph X) (n : ℕ) (S : Set H) (t : ℕ)
    (hresidual : ∀ T : Set S, S.ncard - 2 * (t - 1) ≤ T.ncard →
      ∃ e ∈ T, ∃ f ∈ T, e ≠ f ∧ H.IsUseful n e.1 f.1) :
    ∃ left right : Fin t → H,
      Function.Injective (Sum.elim left right) ∧
        (∀ i, H.IsUseful n (left i) (right i)) ∧
        (∀ i, left i ∈ S ∧ right i ∈ S) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    let empty : Fin 0 → H := fun i ↦ Fin.elim0 i
    refine ⟨empty, empty, ?_, ?_, ?_⟩
    · intro a
      exact a.elim (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    let G := H.usefulPairGraphOn n S
    obtain ⟨M, hM, hmax⟩ := exists_maximum_matching G
    have hMt : t ≤ M.edgeSet.ncard := by
      by_contra hnot
      have hlt : M.edgeSet.ncard < t := Nat.lt_of_not_ge hnot
      let U : Set S := M.vertsᶜ
      have hUcard : S.ncard - 2 * (t - 1) ≤ U.ncard := by
        have hcomp : U.ncard = Fintype.card S - M.verts.ncard := by
          dsimp only [U]
          rw [Set.ncard_compl, Nat.card_eq_fintype_card]
        have hS : Fintype.card S = S.ncard := Set.fintypeCard_eq_ncard S
        have hverts := matching_verts_ncard_generic M hM
        rw [hcomp, hS, hverts]
        omega
      obtain ⟨e, he, f, hf, hef, huseful⟩ := hresidual U hUcard
      have hnonadj := maximum_matching_unmatched_pairwise_not_adj M hM hmax
        he hf hef
      exact hnonadj huseful
    obtain ⟨leftS, rightS, hinjective, hadj⟩ :=
      exists_injective_endpoints_of_matching M hM hMt
    let left : Fin t → H := fun i ↦ (leftS i).1
    let right : Fin t → H := fun i ↦ (rightS i).1
    have elim_coe (a : Fin t ⊕ Fin t) :
        Sum.elim left right a = (Sum.elim leftS rightS a).1 := by
      rcases a with i | i <;> rfl
    have hinjective' : Function.Injective (Sum.elim left right) := by
      intro a b hab
      apply hinjective
      apply Subtype.ext
      rw [← elim_coe a, ← elim_coe b]
      exact hab
    refine ⟨left, right, hinjective', ?_, ?_⟩
    · intro i
      exact hadj i
    · intro i
      exact ⟨(leftS i).2, (rightS i).2⟩

/-- Arithmetic wrapper for the common-neighborhood injection. -/
lemma isUseful_of_commonNeighbor_bound [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (n : ℕ) (e f : H) (hef : e ≠ f)
    (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1)
    (hbound : (e.1.ncard - 1) * (f.1.ncard - 1) +
      (H.incidentEdges w).ncard - 2 ≤ n - 2) :
    H.IsUseful n e f := by
  refine ⟨hef, ⟨w, hwe, hwf⟩, ?_⟩
  exact (H.commonNeighborEdges_ncard_le hlinear e f hef w hwe hwf).trans hbound

/-- The first, purely integral branch of Proposition 5.5.  The displayed
arithmetic hypothesis is the final numerical estimate in the paper after
using `r ≈ √n` and `k ≈ √n`; all combinatorial steps, including the
degree quotient bound, are discharged here. -/
lemma isUseful_of_one_edge_small [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (n r k : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ g : H, r ≤ g.1.ncard)
    (e f : H) (hef : e ≠ f) (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1)
    (hek : e.1.ncard ≤ k) (hfk : f.1.ncard ≤ k)
    (hsmall : e.1.ncard ≤ k - 1 ∨ f.1.ncard ≤ k - 1)
    (harith : (k - 1) * (k - 2) +
      (Fintype.card X - 1) / (r - 1) - 2 ≤ n - 2) :
    H.IsUseful n e f := by
  have hdegmul := H.incidentEdges_ncard_mul_sub_one_le hlinear w r
    (fun g _ ↦ hmin g)
  have hrpos : 0 < r - 1 := by omega
  have hdeg : (H.incidentEdges w).ncard ≤
      (Fintype.card X - 1) / (r - 1) :=
    (Nat.le_div_iff_mul_le hrpos).2 hdegmul
  have hprod : (e.1.ncard - 1) * (f.1.ncard - 1) ≤
      (k - 1) * (k - 2) := by
    rcases hsmall with he | hf
    · have he' : e.1.ncard - 1 ≤ k - 2 := Nat.sub_le_sub_right he 1
      have hf' : f.1.ncard - 1 ≤ k - 1 := Nat.sub_le_sub_right hfk 1
      calc
        (e.1.ncard - 1) * (f.1.ncard - 1) ≤ (k - 2) * (k - 1) :=
          Nat.mul_le_mul he' hf'
        _ = (k - 1) * (k - 2) := Nat.mul_comm _ _
    · have he' : e.1.ncard - 1 ≤ k - 1 := Nat.sub_le_sub_right hek 1
      have hf' : f.1.ncard - 1 ≤ k - 2 := Nat.sub_le_sub_right hf 1
      exact Nat.mul_le_mul he' hf'
  apply H.isUseful_of_commonNeighbor_bound hlinear n e f hef w hwe hwf
  calc
    (e.1.ncard - 1) * (f.1.ncard - 1) +
          (H.incidentEdges w).ncard - 2 ≤
        (k - 1) * (k - 2) +
          (Fintype.card X - 1) / (r - 1) - 2 :=
      Nat.sub_le_sub_right (Nat.add_le_add hprod hdeg) 2
    _ ≤ n - 2 := harith

/-- Proposition 5.5(i) with the projective-plane scale chosen explicitly.
The sole edge-size approximation needed here is the integral inequality
`k+1 ≤ 2(r-1)`. -/
lemma isUseful_of_one_edge_below_projectiveScale [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n) (hr : 2 ≤ r)
    (hrscale : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ g : H, r ≤ g.1.ncard)
    (e f : H) (hef : e ≠ f) (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1)
    (hek : e.1.ncard ≤ projectiveScale n)
    (hfk : f.1.ncard ≤ projectiveScale n)
    (hsmall : e.1.ncard ≤ projectiveScale n - 1 ∨
      f.1.ncard ≤ projectiveScale n - 1) :
    H.IsUseful n e f := by
  apply H.isUseful_of_one_edge_small hlinear n r (projectiveScale n) hr hmin
    e f hef w hwe hwf hek hfk hsmall
  simpa [hvertices] using projectiveScale_case_one_arith hn hrscale

/-- The second combinatorial branch of Proposition 5.5.  Here both selected
edges have size `k`; the number `m` of smaller edges through their common point
is bounded, and `incident_two_tier_weight_le` supplies precisely the weighted
inequality used by the paper.  `harith` isolates the remaining elementary
parameter calculation. -/
lemma isUseful_of_few_small_incident [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (n r k q : ℕ)
    (hmin : ∀ g : H, r ≤ g.1.ncard)
    (e f : H) (hef : e ≠ f) (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1)
    (hek : e.1.ncard = k) (hfk : f.1.ncard = k)
    (hsmall : (H.smallIncidentEdges w k).ncard ≤ q)
    (harith : ∀ d m : ℕ, m ≤ d → m ≤ q →
      (d - m) * (k - 1) + m * (r - 1) ≤ Fintype.card X - 1 →
      (k - 1) * (k - 1) + d - 2 ≤ n - 2) :
    H.IsUseful n e f := by
  have htier := H.incident_two_tier_weight_le hlinear w r k hmin
  have hmle := H.smallIncidentEdges_ncard_le_incidentEdges w k
  have hnumeric := harith (H.incidentEdges w).ncard
    (H.smallIncidentEdges w k).ncard hmle hsmall htier
  apply H.isUseful_of_commonNeighbor_bound hlinear n e f hef w hwe hwf
  simpa [hek, hfk] using hnumeric

/-- Proposition 5.5(ii) with its arithmetic premise reduced to a single
explicit projective-scale slack inequality. -/
lemma isUseful_of_few_small_incident_below_projectiveScale [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r q : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ g : H, r ≤ g.1.ncard)
    (hdefect : q * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (e f : H) (hef : e ≠ f) (w : X) (hwe : w ∈ e.1) (hwf : w ∈ f.1)
    (hek : e.1.ncard = projectiveScale n)
    (hfk : f.1.ncard = projectiveScale n)
    (hsmall : (H.smallIncidentEdges w (projectiveScale n)).ncard ≤ q) :
    H.IsUseful n e f := by
  apply H.isUseful_of_few_small_incident hlinear n r (projectiveScale n) q hmin
    e f hef w hwe hwf hek hfk hsmall
  intro d m hmle hmq hbudget
  apply two_tier_degree_arith (two_le_projectiveScale hn) hr hrscale hmle hmq
    (by simpa [hvertices] using hbudget)
  · have hpred := projectiveScale_pred_sq_add_le (n := n) (by omega)
    omega
  · exact projectiveScale_case_two_slack hn hdefect

/-- Incidence pigeonhole outside a bad vertex set.  If every edge in `S`
contains at least `q` vertices outside `bad` and `|S|q > |X|`, two distinct
edges of `S` meet outside `bad`.  This is the double-counting step in Claim 1
of the proof of Lemma 5.1. -/
lemma exists_distinct_intersecting_outside [Fintype X] (H : SetHypergraph X)
    (S : Set H) (bad : Set X) (q : ℕ)
    (houtside : ∀ e ∈ S, q ≤ (e.1 \ bad).ncard)
    (hlarge : Fintype.card X < S.ncard * q) :
    ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧
      ∃ x, x ∉ bad ∧ x ∈ e.1 ∧ x ∈ f.1 := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let Outside (e : S) := (e.1.1 \ bad : Set X)
  let _ (e : S) : Fintype (Outside e) := Fintype.ofFinite (Outside e)
  let Incidence := Σ e : S, Outside e
  let code : Incidence → X := fun p ↦ p.2.1
  have hsource : S.ncard * q ≤ Fintype.card Incidence := by
    calc
      S.ncard * q = ∑ _e : S, q := by
        rw [show S.ncard = Fintype.card S from
          (Set.fintypeCard_eq_ncard S).symm]
        simp
      _ ≤ ∑ e : S, Fintype.card (Outside e) := by
        apply Finset.sum_le_sum
        intro e _
        rw [Set.fintypeCard_eq_ncard]
        exact houtside e.1 e.2
      _ = Fintype.card Incidence := by rw [Fintype.card_sigma]
  have hnotinjective : ¬ Function.Injective code := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective code hinjective
    omega
  obtain ⟨p, s, hcode, hps⟩ := Function.not_injective_iff.mp hnotinjective
  rcases p with ⟨e, x⟩
  rcases s with ⟨f, y⟩
  change x.1 = y.1 at hcode
  have hef : e.1 ≠ f.1 := by
    intro hef
    have hef' : e = f := Subtype.ext hef
    subst f
    have hxy : x = y := Subtype.ext hcode
    subst y
    exact hps rfl
  refine ⟨e.1, e.2, f.1, f.2, hef, x.1, x.2.2, x.2.1, ?_⟩
  rw [hcode]
  exact y.2.1

/-- A convenient useful-pair consequence of
`exists_distinct_intersecting_outside`. -/
lemma exists_useful_pair_of_many_outside [Fintype X] (H : SetHypergraph X)
    (n : ℕ) (S : Set H) (bad : Set X) (q : ℕ)
    (houtside : ∀ e ∈ S, q ≤ (e.1 \ bad).ncard)
    (hlarge : Fintype.card X < S.ncard * q)
    (hgood : ∀ (e f : H), e ∈ S → f ∈ S → e ≠ f →
      ∀ x, x ∉ bad → x ∈ e.1 → x ∈ f.1 → H.IsUseful n e f) :
    ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧ H.IsUseful n e f := by
  obtain ⟨e, he, f, hf, hef, x, hxbad, hxe, hxf⟩ :=
    H.exists_distinct_intersecting_outside S bad q houtside hlarge
  exact ⟨e, he, f, hf, hef, hgood e f he hf hef x hxbad hxe hxf⟩

/-- The pair-counting inequality at the start of Proposition 6.3 of
Kang--Kelly--Kühn--Methuku--Osthus.  Every pair consisting of the unique point
of `e ∩ f` and a point of `f \ e` is a distinct ordered pair in
`e × (X \ e)`. -/
lemma sum_neighbor_ncard_sub_one_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) :
    (∑ f : H.neighborEdges e, (f.1.1.ncard - 1)) ≤
      e.1.ncard * (Fintype.card X - e.1.ncard) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype (H.neighborEdges e) := Fintype.ofFinite (H.neighborEdges e)
  let _ (f : H.neighborEdges e) : Fintype ((f.1.1 \ e.1) : Set X) :=
    Fintype.ofFinite ((f.1.1 \ e.1) : Set X)
  let meetingPoint (f : H.neighborEdges e) : X := Classical.choose f.2.2
  have meetingPoint_mem_left (f : H.neighborEdges e) : meetingPoint f ∈ e.1 :=
    (Classical.choose_spec f.2.2).1
  have meetingPoint_mem_right (f : H.neighborEdges e) : meetingPoint f ∈ f.1.1 :=
    (Classical.choose_spec f.2.2).2
  let code (p : Σ f : H.neighborEdges e, ((f.1.1 \ e.1) : Set X)) :
      (e.1 : Set X) × (e.1ᶜ : Set X) :=
    (⟨meetingPoint p.1, meetingPoint_mem_left p.1⟩, ⟨p.2.1, p.2.2.2⟩)
  have code_injective : Function.Injective code := by
    intro p q hcode
    have hpoint : meetingPoint p.1 = meetingPoint q.1 :=
      congrArg (fun z : (e.1 : Set X) × (e.1ᶜ : Set X) ↦ z.1.1) hcode
    have houtside : p.2.1 = q.2.1 :=
      congrArg (fun z : (e.1 : Set X) × (e.1ᶜ : Set X) ↦ z.2.1) hcode
    have hedge : p.1.1 = q.1.1 := by
      apply Subtype.ext
      by_contra hpq
      have hsub : (p.1.1.1 ∩ q.1.1.1).Subsingleton :=
        hlinear p.1.1.2 q.1.1.2 hpq
      have hmeet : meetingPoint p.1 ∈ p.1.1.1 ∩ q.1.1.1 := by
        refine ⟨meetingPoint_mem_right p.1, ?_⟩
        rw [hpoint]
        exact meetingPoint_mem_right q.1
      have hout : p.2.1 ∈ p.1.1.1 ∩ q.1.1.1 := by
        refine ⟨p.2.2.1, ?_⟩
        rw [houtside]
        exact q.2.2.1
      have heq := hsub hmeet hout
      exact p.2.2.2 (heq ▸ meetingPoint_mem_left p.1)
    have hneighbor : p.1 = q.1 := Subtype.ext hedge
    apply Sigma.ext hneighbor
    exact (Subtype.heq_iff_coe_eq (fun x ↦ by rw [hneighbor])).2 houtside
  let embedding :
      (Σ f : H.neighborEdges e, ((f.1.1 \ e.1) : Set X)) ↪
        (e.1 : Set X) × (e.1ᶜ : Set X) :=
    ⟨code, code_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  have hdiff (f : H.neighborEdges e) :
      (f.1.1 \ e.1).ncard = f.1.1.ncard - 1 := by
    have hinter_nonempty : (f.1.1 ∩ e.1).Nonempty := by
      simpa [Set.inter_comm] using f.2.2
    have hinter_subsingleton : (f.1.1 ∩ e.1).Subsingleton :=
      hlinear f.1.2 e.2 (by
        intro hsets
        exact f.2.1.symm (Subtype.ext hsets))
    have hinter_card : (f.1.1 ∩ e.1).ncard = 1 := by
      have hpos : 0 < (f.1.1 ∩ e.1).ncard :=
        (Set.ncard_pos).2 hinter_nonempty
      have hle : (f.1.1 ∩ e.1).ncard ≤ 1 :=
        Set.ncard_le_one_iff_subsingleton.mpr hinter_subsingleton
      omega
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard f.1.1 e.1
    omega
  calc
    (∑ f : H.neighborEdges e, (f.1.1.ncard - 1)) =
        ∑ f : H.neighborEdges e, (f.1.1 \ e.1).ncard := by
      apply Finset.sum_congr rfl
      intro f _
      exact (hdiff f).symm
    _ = ∑ f : H.neighborEdges e,
        Fintype.card ((f.1.1 \ e.1) : Set X) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Set.fintypeCard_eq_ncard]
    _ = Fintype.card (Σ f : H.neighborEdges e, ((f.1.1 \ e.1) : Set X)) := by
      rw [Fintype.card_sigma]
    _ ≤ Fintype.card ((e.1 : Set X) × (e.1ᶜ : Set X)) := hcard
    _ = e.1.ncard * (Fintype.card X - e.1.ncard) := by
      rw [Fintype.card_prod, Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
        Set.ncard_compl]
      simp

/-- Any subfamily of the neighbors whose edges each contribute at least `q`
to the pair count has cardinality at most the total pair-count budget divided
implicitly by `q`.  The multiplicative form avoids division and is the one
used by the reordering estimates. -/
lemma ncard_mul_le_pairBudget [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (S : Set H)
    (hS : S ⊆ H.neighborEdges e) (q : ℕ)
    (hweight : ∀ f ∈ S, q ≤ f.1.ncard - 1) :
    S.ncard * q ≤ e.1.ncard * (Fintype.card X - e.1.ncard) := by
  classical
  have htotal := H.sum_neighbor_ncard_sub_one_le hlinear e
  calc
    S.ncard * q = ∑ _f ∈ S.toFinset, q := by
      rw [Set.ncard_eq_toFinset_card' S]
      simp
    _ ≤ ∑ f ∈ S.toFinset, (f.1.ncard - 1) := by
      apply Finset.sum_le_sum
      intro f hf
      exact hweight f (Set.mem_toFinset.mp hf)
    _ ≤ ∑ f ∈ (H.neighborEdges e).toFinset, (f.1.ncard - 1) := by
      exact Finset.sum_le_sum_of_subset (Set.toFinset_mono hS)
    _ = ∑ f : H.neighborEdges e, (f.1.1.ncard - 1) := by
      exact Finset.sum_subtype (H.neighborEdges e).toFinset
        (fun f ↦ Set.mem_toFinset) (fun f ↦ f.1.ncard - 1)
    _ ≤ e.1.ncard * (Fintype.card X - e.1.ncard) := htotal

/-- Two disjoint neighbor families may be charged at different minimum edge
weights against the same ordered-pair budget.  This is the integral core of
Proposition 6.3(i), before the paper divides by the size of the reference
edge and introduces real parameters. -/
lemma two_family_pairBudget [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (S T : Set H)
    (hS : S ⊆ H.neighborEdges e) (hT : T ⊆ H.neighborEdges e)
    (hST : Disjoint S T) (qS qT : ℕ)
    (hweightS : ∀ f ∈ S, qS ≤ f.1.ncard - 1)
    (hweightT : ∀ f ∈ T, qT ≤ f.1.ncard - 1) :
    S.ncard * qS + T.ncard * qT ≤
      e.1.ncard * (Fintype.card X - e.1.ncard) := by
  classical
  have htotal := H.sum_neighbor_ncard_sub_one_le hlinear e
  have hfinDisjoint : Disjoint S.toFinset T.toFinset := by
    rw [Finset.disjoint_left]
    intro f hfS hfT
    exact Set.disjoint_left.mp hST (Set.mem_toFinset.mp hfS)
      (Set.mem_toFinset.mp hfT)
  have hunion : S.toFinset ∪ T.toFinset ⊆
      (H.neighborEdges e).toFinset := by
    intro f hf
    rcases Finset.mem_union.mp hf with hfS | hfT
    · exact Set.mem_toFinset.mpr (hS (Set.mem_toFinset.mp hfS))
    · exact Set.mem_toFinset.mpr (hT (Set.mem_toFinset.mp hfT))
  calc
    S.ncard * qS + T.ncard * qT =
        (∑ _f ∈ S.toFinset, qS) + ∑ _f ∈ T.toFinset, qT := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      simp
    _ ≤ (∑ f ∈ S.toFinset, (f.1.ncard - 1)) +
        ∑ f ∈ T.toFinset, (f.1.ncard - 1) := by
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro f hf
        exact hweightS f (Set.mem_toFinset.mp hf)
      · apply Finset.sum_le_sum
        intro f hf
        exact hweightT f (Set.mem_toFinset.mp hf)
    _ = ∑ f ∈ S.toFinset ∪ T.toFinset, (f.1.ncard - 1) := by
      rw [Finset.sum_union hfinDisjoint]
    _ ≤ ∑ f ∈ (H.neighborEdges e).toFinset, (f.1.ncard - 1) :=
      Finset.sum_le_sum_of_subset hunion
    _ = ∑ f : H.neighborEdges e, (f.1.1.ncard - 1) := by
      exact Finset.sum_subtype (H.neighborEdges e).toFinset
        (fun f ↦ Set.mem_toFinset) (fun f ↦ f.1.ncard - 1)
    _ ≤ e.1.ncard * (Fintype.card X - e.1.ncard) := htotal

/-- Neighbors occurring earlier in a numerical edge ordering. -/
def earlierNeighborEdges (H : SetHypergraph X) (rank : H → ℕ) (e : H) : Set H :=
  {f | rank f < rank e ∧ (e.1 ∩ f.1).Nonempty}

/-- If an ordering puts no smaller edge before a larger edge, then an edge of
size at least two has at most `2|V|` earlier neighbors.  This is the integral,
division-free consequence of the bound
`|N⁻(e)| (|e|-1) ≤ |e| (|V|-|e|)` noted after Proposition 6.3. -/
lemma earlierNeighborEdges_ncard_le_two_mul [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (rank : H → ℕ)
    (horder : ∀ ⦃e f : H⦄, rank f < rank e → e.1.ncard ≤ f.1.ncard)
    (e : H) (he : 2 ≤ e.1.ncard) :
    (H.earlierNeighborEdges rank e).ncard ≤ 2 * Fintype.card X := by
  classical
  have hsubset : H.earlierNeighborEdges rank e ⊆ H.neighborEdges e := by
    intro f hf
    exact ⟨fun hef ↦ (ne_of_lt hf.1) (congrArg rank hef.symm), hf.2⟩
  have hweight : ∀ f ∈ H.earlierNeighborEdges rank e,
      e.1.ncard - 1 ≤ f.1.ncard - 1 := by
    intro f hf
    exact Nat.sub_le_sub_right (horder hf.1) 1
  have hpairs := H.ncard_mul_le_pairBudget hlinear e
    (H.earlierNeighborEdges rank e) hsubset (e.1.ncard - 1) hweight
  have hfactor : 0 < e.1.ncard - 1 := by omega
  have heratio : e.1.ncard ≤ 2 * (e.1.ncard - 1) := by omega
  have hmul :
      (H.earlierNeighborEdges rank e).ncard * (e.1.ncard - 1) ≤
        (2 * Fintype.card X) * (e.1.ncard - 1) := by
    calc
      (H.earlierNeighborEdges rank e).ncard * (e.1.ncard - 1) ≤
          e.1.ncard * (Fintype.card X - e.1.ncard) := hpairs
      _ ≤ e.1.ncard * Fintype.card X := by
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ (2 * (e.1.ncard - 1)) * Fintype.card X :=
        Nat.mul_le_mul_right _ heratio
      _ = (2 * Fintype.card X) * (e.1.ncard - 1) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul hfactor

/-- Quotient-sharp form of the same decreasing-size estimate.  If every edge
has size at least `r ≥ 2`, then a size-nonincreasing ordering gives each edge
at most `|X| + |X| / (r - 1)` earlier neighbors.  This is the integral version
of the observation following Proposition 6.3 that the greedy bound is
`(1 + 1/(r-1))|X| + 1`. -/
lemma earlierNeighborEdges_ncard_le_card_add_div [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (rank : H → ℕ)
    (horder : ∀ ⦃e f : H⦄, rank f < rank e → e.1.ncard ≤ f.1.ncard)
    (r : ℕ) (hr : 2 ≤ r) (hmin : ∀ e : H, r ≤ e.1.ncard)
    (e : H) :
    (H.earlierNeighborEdges rank e).ncard ≤
      Fintype.card X + Fintype.card X / (r - 1) := by
  classical
  let S := H.earlierNeighborEdges rank e
  let s := e.1.ncard
  have hs : r ≤ s := hmin e
  have hsubset : S ⊆ H.neighborEdges e := by
    intro f hf
    exact ⟨fun hef ↦ (ne_of_lt hf.1) (congrArg rank hef.symm), hf.2⟩
  have hweight : ∀ f ∈ S, s - 1 ≤ f.1.ncard - 1 := by
    intro f hf
    exact Nat.sub_le_sub_right (horder hf.1) 1
  have hpairs := H.ncard_mul_le_pairBudget hlinear e S hsubset (s - 1) hweight
  have hden : 0 < s - 1 := by omega
  have hmul : S.ncard * (s - 1) ≤ s * Fintype.card X := by
    exact hpairs.trans (Nat.mul_le_mul_left s (Nat.sub_le _ _))
  have hquot : S.ncard ≤ s * Fintype.card X / (s - 1) :=
    (Nat.le_div_iff_mul_le hden).2 hmul
  have hsSucc : s = (s - 1) + 1 := by omega
  have hidentity :
      s * Fintype.card X / (s - 1) =
        Fintype.card X + Fintype.card X / (s - 1) := by
    calc
      s * Fintype.card X / (s - 1) =
          ((s - 1) * Fintype.card X + Fintype.card X) / (s - 1) := by
        apply congrArg (fun z : ℕ ↦ z / (s - 1))
        calc
          s * Fintype.card X =
              ((s - 1) + 1) * Fintype.card X :=
            congrArg (fun z : ℕ ↦ z * Fintype.card X) hsSucc
          _ = (s - 1) * Fintype.card X + Fintype.card X := by
            rw [Nat.add_mul, one_mul]
      _ = (Fintype.card X + (s - 1) * Fintype.card X) / (s - 1) := by
        rw [Nat.add_comm]
      _ = Fintype.card X / (s - 1) + Fintype.card X :=
        Nat.add_mul_div_left _ _ hden
      _ = Fintype.card X + Fintype.card X / (s - 1) := Nat.add_comm _ _
  have hdenMono : Fintype.card X / (s - 1) ≤
      Fintype.card X / (r - 1) := by
    apply Nat.div_le_div_left
    · omega
    · omega
  rw [hidentity] at hquot
  exact hquot.trans (Nat.add_le_add_left hdenMono _)

/-- Every finite set-valued hypergraph admits an injective numerical ordering
which lists edges by nonincreasing cardinality.  The rank of an edge is the
number of strictly earlier edges in the lexicographic order on
`(dual cardinality, tie breaker)`. -/
lemma exists_rank_ordered_by_ncard [Fintype X] (H : SetHypergraph X) :
    ∃ rank : H → ℕ, Function.Injective rank ∧
      ∀ ⦃e f : H⦄, rank f < rank e → e.1.ncard ≤ f.1.ncard := by
  classical
  let tie : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let key : H → (OrderDual ℕ ×ₗ Fin (Fintype.card H)) := fun e ↦
    toLex ((e.1.ncard : OrderDual ℕ), tie e)
  have key_injective : Function.Injective key := by
    intro e f hef
    apply tie.injective
    exact congrArg (fun z : OrderDual ℕ ×ₗ Fin (Fintype.card H) ↦ (ofLex z).2) hef
  let predecessors (e : H) : Set H := {f | key f < key e}
  have predecessors_ssubset {e f : H} (hef : key e < key f) :
      predecessors e ⊂ predecessors f := by
    constructor
    · intro g hg
      exact hg.trans hef
    · intro hsubset
      have he_mem_f : e ∈ predecessors f := hef
      have he_mem_e := hsubset he_mem_f
      exact (lt_irrefl (key e)) he_mem_e
  let rank : H → ℕ := fun e ↦ (predecessors e).ncard
  have rank_injective : Function.Injective rank := by
    intro e f hef
    by_contra hne
    have hkeyne : key e ≠ key f := fun h ↦ hne (key_injective h)
    rcases lt_or_gt_of_ne hkeyne with hlt | hgt
    · have hc := Set.ncard_lt_ncard (predecessors_ssubset hlt)
      exact (Nat.ne_of_lt hc) hef
    · have hc := Set.ncard_lt_ncard (predecessors_ssubset hgt)
      exact (Nat.ne_of_lt hc) hef.symm
  refine ⟨rank, rank_injective, ?_⟩
  intro e f hrank
  have hfe : key f < key e := by
    rcases lt_trichotomy (key f) (key e) with hlt | heq | hgt
    · exact hlt
    · have hfeq : f = e := key_injective heq
      subst f
      exfalso
      exact (Nat.lt_irrefl _) hrank
    · have hc := Set.ncard_lt_ncard (predecessors_ssubset hgt)
      exfalso
      exact (Nat.not_lt_of_ge hc.le) hrank
  rcases Prod.Lex.lt_iff.mp hfe with hcard | htie
  · exact hcard.le
  · have hcardeq : f.1.ncard = e.1.ncard := htie.1
    exact hcardeq.symm.le

/-- Regard a set-valued hypergraph as an indexed hypergraph whose labels are
its edges. -/
def asIndexed (H : SetHypergraph X) : IndexedHypergraph X H where
  edge e := e.1

/-- Edge colorability with the palette `Fin k`. -/
def EdgeColorable (H : SetHypergraph X) (k : ℕ) : Prop :=
  Nonempty (H.EdgeColoring (Fin k))

/-- Increasing the palette preserves edge colorability. -/
lemma EdgeColorable.mono {H : SetHypergraph X} {k l : ℕ}
    (hcolor : H.EdgeColorable k) (hkl : k ≤ l) : H.EdgeColorable l := by
  obtain ⟨c⟩ := hcolor
  refine ⟨{ color := fun e ↦ Fin.castLE hkl (c e), valid := ?_ }⟩
  intro e f hef hinter hsame
  exact c.valid hef hinter (Fin.castLE_injective hkl hsame)

/-- A matching is a pairwise disjoint set of hyperedges. -/
def IsMatching (H : SetHypergraph X) (M : Set H) : Prop :=
  M.Pairwise fun (e f : H) ↦ Disjoint e.1 f.1

/-- The ambient vertices covered by a family of hyperedges. -/
def coveredVertices (H : SetHypergraph X) (M : Set H) : Set X :=
  ⋃ e ∈ M, e.1

/-- A finite part of a family of hyperedges, viewed again as a set of ambient
hyperedges. -/
def matchingPart (H : SetHypergraph X) (M : Set H) (p : Finset M) : Set H :=
  Subtype.val '' (↑p : Set M)

lemma matchingPart_subset (H : SetHypergraph X) (M : Set H) (p : Finset M) :
    H.matchingPart M p ⊆ M := by
  rintro e ⟨e', _he', rfl⟩
  exact e'.2

/-- Restricting a matching to one finite part preserves the matching
property. -/
lemma IsMatching.matchingPart {H : SetHypergraph X} {M : Set H}
    (hM : H.IsMatching M) (p : Finset M) :
    H.IsMatching (H.matchingPart M p) :=
  hM.mono (H.matchingPart_subset M p)

/-- The vertices covered by a finite hypergraph matching are counted without
overlap: their number is the sum of the sizes of the matching edges. -/
lemma IsMatching.coveredVertices_ncard_eq_sum [Fintype X]
    {H : SetHypergraph X} {M : Set H} (hM : H.IsMatching M) :
    (H.coveredVertices M).ncard = ∑ᶠ e ∈ M, e.1.ncard := by
  classical
  have hpairwise : M.PairwiseDisjoint (fun e : H ↦ e.1) := by
    intro e he f hf hef
    exact hM he hf hef
  calc
    (H.coveredVertices M).ncard = (⋃ e ∈ M, e.1).ncard := rfl
    _ = ∑ᶠ e ∈ M, e.1.ncard :=
      M.toFinite.ncard_biUnion (fun _ _ ↦ Set.toFinite _) hpairwise

/-- The coverage of a finite part of a matching is the sum of the sizes of
its edges. -/
lemma IsMatching.coveredVertices_matchingPart_ncard_eq_sum [Fintype X]
    {H : SetHypergraph X} {M : Set H} (hM : H.IsMatching M) (p : Finset M) :
    (H.coveredVertices (H.matchingPart M p)).ncard =
      ∑ e ∈ p, e.1.1.ncard := by
  classical
  have hpMatching := hM.matchingPart p
  have hcover := hpMatching.coveredVertices_ncard_eq_sum
  let Mp := H.matchingPart M p
  have hMpFinite : Mp.Finite := Mp.toFinite
  rw [finsum_mem_eq_finite_toFinset_sum
    (fun e : H ↦ e.1.ncard) hMpFinite] at hcover
  rw [hcover]
  let embed : M ↪ H := ⟨Subtype.val, Subtype.val_injective⟩
  have htoFinset : hMpFinite.toFinset = p.map embed := by
    ext e
    constructor
    · intro he
      have heMp : e ∈ Mp := hMpFinite.mem_toFinset.mp he
      obtain ⟨e', he'p, he'e⟩ := heMp
      exact Finset.mem_map.mpr ⟨e', he'p, he'e⟩
    · intro he
      obtain ⟨e', he'p, he'e⟩ := Finset.mem_map.mp he
      apply hMpFinite.mem_toFinset.mpr
      exact ⟨e', he'p, he'e⟩
  rw [htoFinset, Finset.sum_map]
  rfl

/-- Partition a matching into cover-bounded submatchings.  Every part is
either a singleton or covers at most `A` vertices, and the number of parts is
bounded by the total coverage divided (in multiplicative form) by
`A / 2 + 1`. -/
lemma IsMatching.exists_cover_bounded_partition [Fintype X]
    {H : SetHypergraph X} {M : Set H} [Fintype M]
    (hM : H.IsMatching M) (A : ℕ) :
    ∃ P : Finpartition (Finset.univ : Finset M),
      (∀ p ∈ P.parts,
        p.card ≤ 1 ∨ (H.coveredVertices (H.matchingPart M p)).ncard ≤ A) ∧
      (P.parts.card - 1) * (A / 2 + 1) ≤
        (H.coveredVertices M).ncard := by
  classical
  obtain ⟨P, hcapacity, hcard⟩ :=
    exists_capacity_partition_card_bound
      (fun e : M ↦ e.1.1.ncard) A
  have hcapacity' : ∀ p ∈ P.parts,
      p.card ≤ 1 ∨ (H.coveredVertices (H.matchingPart M p)).ncard ≤ A := by
    intro p hp
    rcases hcapacity p hp with hpSmall | hpWeight
    · exact Or.inl hpSmall
    · right
      rw [hM.coveredVertices_matchingPart_ncard_eq_sum]
      exact hpWeight
  have hcover := hM.coveredVertices_ncard_eq_sum
  rw [finsum_mem_eq_finite_toFinset_sum
    (fun e : H ↦ e.1.ncard) M.toFinite] at hcover
  have hfinEq : M.toFinite.toFinset = M.toFinset := by
    ext e
    simp
  rw [hfinEq] at hcover
  have htotal : (∑ e : M, e.1.1.ncard) = (H.coveredVertices M).ncard := by
    calc
      (∑ e : M, e.1.1.ncard) =
          ∑ e ∈ M.toFinset, e.1.ncard := by
        symm
        exact Finset.sum_subtype M.toFinset (fun e ↦ Set.mem_toFinset) 
          (fun e : H ↦ e.1.ncard)
      _ = (H.coveredVertices M).ncard := hcover.symm
  refine ⟨P, hcapacity', ?_⟩
  exact hcard.trans_eq htotal

/-- Refined cover-bounded partition: a matching which already covers at most
`A` vertices is kept in a single part, while the same quantitative bound is
retained in the other case. -/
lemma IsMatching.exists_cover_bounded_partition_refined [Fintype X]
    {H : SetHypergraph X} {M : Set H} [Fintype M]
    (hM : H.IsMatching M) (A : ℕ) :
    ∃ P : Finpartition (Finset.univ : Finset M),
      (∀ p ∈ P.parts,
        p.card ≤ 1 ∨ (H.coveredVertices (H.matchingPart M p)).ncard ≤ A) ∧
      ((H.coveredVertices M).ncard ≤ A → P.parts.card ≤ 1) ∧
      (P.parts.card - 1) * (A / 2 + 1) ≤
        (H.coveredVertices M).ncard := by
  classical
  by_cases hcover : (H.coveredVertices M).ncard ≤ A
  · by_cases hMnonempty : Nonempty M
    · have huniv : (Finset.univ : Finset M) ≠ ∅ :=
        Finset.univ_nonempty.ne_empty
      let P : Finpartition (Finset.univ : Finset M) :=
        Finpartition.indiscrete huniv
      have hparts : P.parts = {(Finset.univ : Finset M)} := rfl
      have hmatchingPart :
          H.matchingPart M (Finset.univ : Finset M) = M := by
        ext e
        constructor
        · intro he
          exact H.matchingPart_subset M Finset.univ he
        · intro he
          exact ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩
      refine ⟨P, ?_, ?_, ?_⟩
      · intro p hp
        right
        have hp' : p = (Finset.univ : Finset M) := by
          simpa only [hparts, Finset.mem_singleton] using hp
        subst p
        simpa only [hmatchingPart] using hcover
      · intro _
        simp [hparts]
      · simp [hparts]
    · letI : IsEmpty M := ⟨fun e ↦ hMnonempty ⟨e⟩⟩
      have hMcard : Fintype.card M = 0 := Fintype.card_eq_zero
      let P : Finpartition (Finset.univ : Finset M) := ⊥
      have hpartsCard : P.parts.card = 0 := by
        change ((⊥ : Finpartition (Finset.univ : Finset M)).parts).card = 0
        rw [Finpartition.card_bot]
        simpa using hMcard
      refine ⟨P, ?_, ?_, ?_⟩
      · intro p hp
        exfalso
        have hpos : 0 < P.parts.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      · intro _
        rw [hpartsCard]
        simp
      · rw [hpartsCard]
        simp
  · obtain ⟨P, hcapacity, hcard⟩ := hM.exists_cover_bounded_partition A
    exact ⟨P, hcapacity, fun h ↦ (hcover h).elim, hcard⟩

/-- If every edge of a matching has size at least `r+1`, its covered-vertex
count times `r` is at most the ordered-pair volume consumed by its edges. -/
lemma IsMatching.coveredVertices_ncard_mul_le_pairWeight [Fintype X]
    {H : SetHypergraph X} {M : Set H} (hM : H.IsMatching M) (r : ℕ)
    (hmin : ∀ e ∈ M, r + 1 ≤ e.1.ncard) :
    (H.coveredVertices M).ncard * r ≤
      ∑ᶠ e ∈ M, e.1.ncard * (e.1.ncard - 1) := by
  classical
  let hMfinite : M.Finite := M.toFinite
  have hcover := hM.coveredVertices_ncard_eq_sum
  rw [finsum_mem_eq_finite_toFinset_sum (fun e : H ↦ e.1.ncard) hMfinite]
    at hcover
  rw [finsum_mem_eq_finite_toFinset_sum
    (fun e : H ↦ e.1.ncard * (e.1.ncard - 1)) hMfinite]
  calc
    (H.coveredVertices M).ncard * r =
        (∑ e ∈ hMfinite.toFinset, e.1.ncard) * r := by rw [hcover]
    _ = ∑ e ∈ hMfinite.toFinset, e.1.ncard * r := by
      rw [Finset.sum_mul]
    _ ≤ ∑ e ∈ hMfinite.toFinset, e.1.ncard * (e.1.ncard - 1) := by
      apply Finset.sum_le_sum
      intro e he
      apply Nat.mul_le_mul_left
      have := hmin e (hMfinite.mem_toFinset.mp he)
      omega

/-- Properness is equivalent to every color class being a matching. -/
lemma edgeColoring_iff_colorClasses_matching {H : SetHypergraph X}
    {κ : Type*} (color : H → κ) :
    (∀ ⦃e f : H⦄, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f) ↔
      ∀ a : κ, H.IsMatching {e | color e = a} := by
  constructor
  · intro hvalid a e he f hf hef
    rw [Set.disjoint_left]
    intro x hxe hxf
    exact (hvalid hef ⟨x, hxe, hxf⟩) (he.trans hf.symm)
  · intro hmatching e f hef hinter hsame
    obtain ⟨x, hxe, hxf⟩ := hinter
    have hdisjoint := hmatching (color e) (show color e = color e from rfl)
      (show color f = color e from hsame.symm) hef
    exact (Set.disjoint_left.mp hdisjoint hxe) hxf

/-- A coloring is cover-bounded at scale `A` when every color class is either
a singleton or its matching covers at most `A` ambient vertices.  The
singleton exception is necessary because one hyperedge may itself have more
than `A` vertices. -/
def IsCoverBoundedColoring (H : SetHypergraph X) {K : Type*}
    (color : H → K) (A : ℕ) : Prop :=
  ∀ k : K,
    ({e : H | color e = k} : Set H).ncard ≤ 1 ∨
      (H.coveredVertices {e : H | color e = k}).ncard ≤ A

/-- The recoloring step in Proposition 6.8(ii).  Split every
color-class matching by the minimal-bin construction.  The dependent sum of
the resulting parts is a finite refined palette, and every refined class is
cover-bounded at scale `A`.  Only classes covering more than `A` vertices
need extra colors, and the displayed bound counts their extra parts. -/
lemma exists_cover_bounded_recoloring [Fintype X]
    (H : SetHypergraph X) {K : Type v} [Fintype K]
    (color : H.EdgeColoring K) (A : ℕ) :
    ∃ (L : Type (max u v)) (_ : Fintype L),
      ∃ recolor : H.EdgeColoring L,
        H.IsCoverBoundedColoring recolor A ∧
          Fintype.card L ≤ Fintype.card K +
            ({k : K |
              A < (H.coveredVertices {e : H | color e = k}).ncard} : Set K).ncard *
              (Fintype.card X / (A / 2 + 1)) := by
  classical
  have hmatching : ∀ k : K, H.IsMatching {e : H | color e = k} :=
    (H.edgeColoring_iff_colorClasses_matching color).mp color.valid
  have hexists (k : K) :=
    (hmatching k).exists_cover_bounded_partition_refined A
  choose P hcapacity hsmall hcard using hexists
  let recolor : H → (Σ k : K, (P k).parts) := fun e ↦
    ⟨color e,
      ⟨(P (color e)).part ⟨e, rfl⟩,
        (P (color e)).part_mem.mpr (Finset.mem_univ _)⟩⟩
  have hproper :
      ∀ ⦃e f : H⦄, e ≠ f → (e.1 ∩ f.1).Nonempty → recolor e ≠ recolor f := by
    intro e f hef hinter heq
    exact color.valid hef hinter (congrArg Sigma.fst heq)
  let refined : H.EdgeColoring (Σ k : K, (P k).parts) :=
    ⟨recolor, hproper⟩
  refine ⟨Σ k : K, (P k).parts, inferInstance, refined, ?_, ?_⟩
  · rintro ⟨k, p⟩
    have hclassSubset :
        ({e : H | refined e = ⟨k, p⟩} : Set H) ⊆
          H.matchingPart {e : H | color e = k} p.1 := by
      intro e he
      have hfirst : color e = k := congrArg Sigma.fst he
      subst k
      have hsecond :
          (⟨(P (color e)).part ⟨e, rfl⟩,
              (P (color e)).part_mem.mpr (Finset.mem_univ _)⟩ :
            (P (color e)).parts) = p := by
        exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
      have hePart : (⟨e, rfl⟩ : {f : H // color f = color e}) ∈ p.1 := by
        have hmem := (P (color e)).mem_part (Finset.mem_univ
          (⟨e, rfl⟩ : {f : H // color f = color e}))
        have hpart :
            (P (color e)).part ⟨e, rfl⟩ = p.1 :=
          congrArg Subtype.val hsecond
        rw [← hpart]
        exact hmem
      exact ⟨⟨e, rfl⟩, hePart, rfl⟩
    rcases hcapacity k p.1 p.2 with hp | hcover
    · left
      calc
        ({e : H | refined e = ⟨k, p⟩} : Set H).ncard ≤
            (H.matchingPart {e : H | color e = k} p.1).ncard :=
          Set.ncard_mono hclassSubset
        _ = p.1.card := by
          change (Subtype.val ''
            {e : {f : H // color f = k} | e ∈ p.1}).ncard =
            p.1.card
          rw [Set.ncard_image_of_injective _ Subtype.val_injective]
          simp
        _ ≤ 1 := hp
    · right
      apply (Set.ncard_mono ?_).trans hcover
      intro x hx
      simp only [coveredVertices, Set.mem_iUnion] at hx ⊢
      obtain ⟨e, heClass, hxe⟩ := hx
      exact ⟨e, hclassSubset heClass, hxe⟩
  · rw [Fintype.card_sigma]
    have hcoverAmbient (k : K) :
        (H.coveredVertices {e : H | color e = k}).ncard ≤
          Fintype.card X := by
      calc
        (H.coveredVertices {e : H | color e = k}).ncard ≤
            (Set.univ : Set X).ncard :=
          Set.ncard_mono (Set.subset_univ _)
        _ = Fintype.card X := by simp
    calc
      (∑ k : K, Fintype.card ↥(P k).parts) =
          ∑ k : K, (P k).parts.card := by
        simp only [Fintype.card_coe]
      _ ≤ ∑ k : K,
          (1 + if A < (H.coveredVertices {e : H | color e = k}).ncard then
            Fintype.card X / (A / 2 + 1) else 0) := by
        apply Finset.sum_le_sum
        intro k _
        split
        next hlarge =>
          have hquot : (P k).parts.card - 1 ≤
              Fintype.card X / (A / 2 + 1) := by
            apply (Nat.le_div_iff_mul_le (by omega)).2
            exact (hcard k).trans (hcoverAmbient k)
          omega
        next hnotlarge =>
          have hsmall' := hsmall k (Nat.le_of_not_gt hnotlarge)
          omega
      _ = Fintype.card K +
          ({k : K |
            A < (H.coveredVertices {e : H | color e = k}).ncard} : Set K).ncard *
            (Fintype.card X / (A / 2 + 1)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_one]
        congr 1
        let q := Fintype.card X / (A / 2 + 1)
        let bad : K → Prop := fun k ↦
          A < (H.coveredVertices {e : H | color e = k}).ncard
        change (∑ k : K, if bad k then q else 0) =
          ({k : K | bad k} : Set K).ncard * q
        calc
          (∑ k : K, if bad k then q else 0) =
              ∑ k : K, (if bad k then 1 else 0) * q := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : bad k <;> simp [hk]
          _ = (∑ k : K, if bad k then 1 else 0) * q := by
            rw [Finset.sum_mul]
          _ = ((Finset.univ.filter bad).card : ℕ) * q := by
            congr 1
            rw [← Finset.sum_filter]
            simp
          _ = ({k : K | bad k} : Set K).ncard * q := by
            congr 1
            calc
              (Finset.univ.filter bad).card = Fintype.card {k : K // bad k} :=
                (Fintype.card_subtype bad).symm
              _ = ({k : K | bad k} : Set K).ncard :=
                Set.fintypeCard_eq_ncard ({k : K | bad k} : Set K)

/-- Color two subhypergraphs independently with disjoint palettes and combine
the colorings on their union.  An edge in both subhypergraphs is assigned to
the left palette. -/
theorem edgeColorable_union (A B : SetHypergraph X) {k l : ℕ}
    (hA : A.EdgeColorable k) (hB : B.EdgeColorable l) :
    (A ∪ B).EdgeColorable (k + l) := by
  classical
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  let color (e : ↥(A ∪ B)) : Fin (k + l) :=
    if heA : e.1 ∈ A then
      finSumFinEquiv (Sum.inl (cA ⟨e.1, heA⟩))
    else
      finSumFinEquiv (Sum.inr (cB ⟨e.1, e.2.resolve_left heA⟩))
  refine ⟨{ color := color, valid := ?_ }⟩
  intro e f hef hinter hsame
  by_cases heA : e.1 ∈ A
  · by_cases hfA : f.1 ∈ A
    · have hsubne : (⟨e.1, heA⟩ : A) ≠ ⟨f.1, hfA⟩ := by
        intro h
        apply hef
        apply Subtype.ext
        exact congrArg (fun z : A ↦ z.1) h
      have hca := cA.valid hsubne hinter
      apply hca
      have hsum :
          (Sum.inl (cA ⟨e.1, heA⟩) : Fin k ⊕ Fin l) =
            Sum.inl (cA ⟨f.1, hfA⟩) :=
        finSumFinEquiv.injective (by simpa [color, heA, hfA] using hsame)
      exact Sum.inl_injective hsum
    · have hsum :
          (Sum.inl (cA ⟨e.1, heA⟩) : Fin k ⊕ Fin l) =
            Sum.inr (cB ⟨f.1, f.2.resolve_left hfA⟩) :=
        finSumFinEquiv.injective (by simpa [color, heA, hfA] using hsame)
      exact Sum.inl_ne_inr hsum
  · by_cases hfA : f.1 ∈ A
    · have hsum :
          (Sum.inr (cB ⟨e.1, e.2.resolve_left heA⟩) : Fin k ⊕ Fin l) =
            Sum.inl (cA ⟨f.1, hfA⟩) :=
        finSumFinEquiv.injective (by simpa [color, heA, hfA] using hsame)
      exact Sum.inr_ne_inl hsum
    · have hsubne :
          (⟨e.1, e.2.resolve_left heA⟩ : B) ≠
            ⟨f.1, f.2.resolve_left hfA⟩ := by
        intro h
        apply hef
        apply Subtype.ext
        exact congrArg (fun z : B ↦ z.1) h
      have hcb := cB.valid hsubne hinter
      apply hcb
      have hsum :
          (Sum.inr (cB ⟨e.1, e.2.resolve_left heA⟩) : Fin k ⊕ Fin l) =
            Sum.inr (cB ⟨f.1, f.2.resolve_left hfA⟩) :=
        finSumFinEquiv.injective (by simpa [color, heA, hfA] using hsame)
      exact Sum.inr_injective hsum

/-- A coloring compression principle.  If edges are mapped to at most `k`
labels and distinct edges with the same label are disjoint, embedding the label
type into `Fin k` gives a proper edge coloring.  Observation 5.2 constructs
such labels by pairing disjoint edges in a complement-line-graph matching. -/
theorem edgeColorable_of_compression (H : SetHypergraph X)
    {C : Type*} [Fintype C] {k : ℕ} (label : H → C)
    (hlabel : ∀ ⦃e f : H⦄, e ≠ f → label e = label f → Disjoint e.1 f.1)
    (hcard : Fintype.card C ≤ k) : H.EdgeColorable k := by
  classical
  have hcard' : Fintype.card C ≤ Fintype.card (Fin k) := by simpa using hcard
  obtain ⟨embedding : C ↪ Fin k⟩ :=
    Function.Embedding.nonempty_of_card_le hcard'
  refine ⟨{ color := fun e ↦ embedding (label e), valid := ?_ }⟩
  intro e f hef hinter hsame
  have hlabels : label e = label f := embedding.injective hsame
  have hdisjoint := hlabel hef hlabels
  obtain ⟨x, hxe, hxf⟩ := hinter
  exact (Set.disjoint_left.mp hdisjoint hxe) hxf

/-- Compress `t` disjoint pairs of hyperedges into `t` shared color labels.
The joint injectivity hypothesis says that all `2t` endpoints are distinct. -/
theorem edgeColorable_of_disjoint_pairs [Fintype X] (H : SetHypergraph X)
    {t k : ℕ} (left right : Fin t → H)
    (hendpoints : Function.Injective (Sum.elim left right))
    (hpairs : ∀ i, Disjoint (left i).1 (right i).1)
    (hcard : Fintype.card H ≤ k + t) :
    H.EdgeColorable k := by
  classical
  let endpoint : Fin t ⊕ Fin t → H := Sum.elim left right
  have endpoint_injective : Function.Injective endpoint := hendpoints
  let rangeEquiv : (Fin t ⊕ Fin t) ≃ Set.range endpoint :=
    Equiv.ofInjective endpoint endpoint_injective
  let pairIndex : Fin t ⊕ Fin t → Fin t := Sum.elim id id
  let Label := Fin t ⊕ {e : H // e ∉ Set.range endpoint}
  let label : H → Label := fun e ↦
    if he : e ∈ Set.range endpoint then
      Sum.inl (pairIndex (rangeEquiv.symm ⟨e, he⟩))
    else Sum.inr ⟨e, he⟩
  have hlabel : ∀ ⦃e f : H⦄, e ≠ f → label e = label f → Disjoint e.1 f.1 := by
    intro e f hef hsame
    by_cases he : e ∈ Set.range endpoint
    · by_cases hf : f ∈ Set.range endpoint
      · simp only [label, dif_pos he, dif_pos hf] at hsame
        have hindex :
            pairIndex (rangeEquiv.symm ⟨e, he⟩) =
              pairIndex (rangeEquiv.symm ⟨f, hf⟩) :=
          Sum.inl_injective hsame
        have heq : endpoint (rangeEquiv.symm ⟨e, he⟩) = e := by
          exact congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨e, he⟩)
        have hfeq : endpoint (rangeEquiv.symm ⟨f, hf⟩) = f := by
          exact congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨f, hf⟩)
        generalize hse : rangeEquiv.symm ⟨e, he⟩ = se at hindex heq
        generalize hsf : rangeEquiv.symm ⟨f, hf⟩ = sf at hindex hfeq
        rcases se with i | i <;> rcases sf with j | j
        · have hij : i = j := by simpa [pairIndex] using hindex
          exfalso
          apply hef
          rw [← heq, ← hfeq, hij]
        · have hij : i = j := by simpa [pairIndex] using hindex
          subst j
          rw [← heq, ← hfeq]
          exact hpairs i
        · have hij : i = j := by simpa [pairIndex] using hindex
          subst j
          rw [← heq, ← hfeq]
          exact (hpairs i).symm
        · have hij : i = j := by simpa [pairIndex] using hindex
          exfalso
          apply hef
          rw [← heq, ← hfeq, hij]
      · have hcontra :
            (Sum.inl (pairIndex (rangeEquiv.symm ⟨e, he⟩)) : Label) =
              Sum.inr ⟨f, hf⟩ := by
          dsimp only [label] at hsame
          rw [dif_pos he, dif_neg hf] at hsame
          exact hsame
        exact (Sum.inl_ne_inr hcontra).elim
    · by_cases hf : f ∈ Set.range endpoint
      · have hcontra :
            (Sum.inr ⟨e, he⟩ : Label) =
              Sum.inl (pairIndex (rangeEquiv.symm ⟨f, hf⟩)) := by
          dsimp only [label] at hsame
          rw [dif_neg he, dif_pos hf] at hsame
          exact hsame
        exact (Sum.inr_ne_inl hcontra).elim
      · have hunmatched :
            (⟨e, he⟩ : {e : H // e ∉ Set.range endpoint}) = ⟨f, hf⟩ := by
          simp only [label, dif_neg he, dif_neg hf] at hsame
          exact Sum.inr_injective hsame
        exact (hef (congrArg Subtype.val hunmatched)).elim
  have hrange : (Set.range endpoint).ncard = 2 * t := by
    calc
      (Set.range endpoint).ncard = Nat.card (Fin t ⊕ Fin t) :=
        Set.ncard_range_of_injective endpoint_injective
      _ = Fintype.card (Fin t ⊕ Fin t) := Nat.card_eq_fintype_card
      _ = Fintype.card (Fin t) + Fintype.card (Fin t) := Fintype.card_sum
      _ = 2 * t := by simp [two_mul]
  have hrange_le : 2 * t ≤ Fintype.card H := by
    rw [← hrange]
    calc
      (Set.range endpoint).ncard ≤ (Set.univ : Set H).ncard :=
        Set.ncard_le_ncard (Set.range endpoint).subset_univ
      _ = Fintype.card H := by simp
  have hLabel : Fintype.card Label = t + (Fintype.card H - 2 * t) := by
    calc
      Fintype.card Label = Fintype.card (Fin t) +
          Fintype.card {e : H // e ∉ Set.range endpoint} := Fintype.card_sum
      _ = t + ((Set.range endpoint)ᶜ : Set H).ncard := by
        rw [Fintype.card_fin]
        congr 1
        change Fintype.card ((Set.range endpoint)ᶜ : Set H) = _
        exact Set.fintypeCard_eq_ncard _
      _ = t + (Fintype.card H - (Set.range endpoint).ncard) := by
        rw [Set.ncard_compl, Nat.card_eq_fintype_card]
      _ = t + (Fintype.card H - 2 * t) := by rw [hrange]
  apply H.edgeColorable_of_compression label hlabel
  rw [hLabel]
  omega

/-- Proposition 5.3 of Kang--Kelly--Kühn--Methuku--Osthus, in its
hypergraph form.  Suppose `H` has `n + t` edges and `2t` distinguished,
pairwise-intersecting edges, arranged into `t` useful pairs.  For each useful
pair, Hall's theorem chooses a different edge outside its common neighborhood
and outside the pair itself.  That edge is disjoint from at least one endpoint
of the pair, so the resulting `t` disjoint pairs compress an `n + t` edge
family into `n` colors. -/
theorem edgeColorable_of_useful_pairs [Fintype X] (H : SetHypergraph X)
    {n t : ℕ} (hn : 2 ≤ n) (left right : Fin t → H)
    (hendpoints : Function.Injective (Sum.elim left right))
    (hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩ (Sum.elim left right b).1).Nonempty)
    (huseful : ∀ i, H.IsUseful n (left i) (right i))
    (hcard : Fintype.card H = n + t) :
    H.EdgeColorable n := by
  classical
  let endpoint : Fin t ⊕ Fin t → H := Sum.elim left right
  have endpoint_injective : Function.Injective endpoint := hendpoints
  let forbidden (i : Fin t) : Set H :=
    H.commonNeighborEdges (left i) (right i) ∪ ({left i, right i} : Set H)
  let candidate (i : Fin t) : Finset H := (forbidden i)ᶜ.toFinset
  have hforbidden (i : Fin t) : (forbidden i).ncard ≤ n := by
    calc
      (forbidden i).ncard ≤
          (H.commonNeighborEdges (left i) (right i)).ncard +
            ({left i, right i} : Set H).ncard := Set.ncard_union_le _ _
      _ = (H.commonNeighborEdges (left i) (right i)).ncard + 2 := by
        rw [Set.ncard_pair (huseful i).1]
      _ ≤ (n - 2) + 2 := Nat.add_le_add_right (huseful i).2.2 2
      _ = n := by omega
  have hcandidate (i : Fin t) : t ≤ (candidate i).card := by
    rw [← Set.ncard_eq_toFinset_card']
    change t ≤ (forbidden i)ᶜ.ncard
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, hcard]
    have hi := hforbidden i
    omega
  obtain ⟨z, z_injective, hz⟩ :=
    exists_injective_mem_of_card_le candidate (by simpa using hcandidate)
  have hz_not_forbidden (i : Fin t) : z i ∉ forbidden i := by
    simpa [candidate] using hz i
  have hz_ne_left (i : Fin t) : z i ≠ left i := by
    intro h
    apply hz_not_forbidden i
    exact Or.inr (by simp [h])
  have hz_ne_right (i : Fin t) : z i ≠ right i := by
    intro h
    apply hz_not_forbidden i
    exact Or.inr (by simp [h])
  have hz_ne_endpoint (i : Fin t) (a : Fin t ⊕ Fin t) : z i ≠ endpoint a := by
    intro hza
    by_cases hal : a = Sum.inl i
    · subst a
      exact hz_ne_left i (by simpa [endpoint] using hza)
    by_cases har : a = Sum.inr i
    · subst a
      exact hz_ne_right i (by simpa [endpoint] using hza)
    have hal' : a ≠ Sum.inl i := hal
    have har' : a ≠ Sum.inr i := har
    have hmeet_left : (endpoint a).1 ∩ (left i).1 |>.Nonempty := by
      simpa [endpoint] using hall_intersect a (Sum.inl i) hal'
    have hmeet_right : (endpoint a).1 ∩ (right i).1 |>.Nonempty := by
      simpa [endpoint] using hall_intersect a (Sum.inr i) har'
    have ha_ne_left : endpoint a ≠ left i := by
      intro ha
      apply hal'
      apply endpoint_injective
      simpa [endpoint] using ha
    have ha_ne_right : endpoint a ≠ right i := by
      intro ha
      apply har'
      apply endpoint_injective
      simpa [endpoint] using ha
    have ha_common : endpoint a ∈ H.commonNeighborEdges (left i) (right i) := by
      constructor
      · exact ⟨ha_ne_left.symm, by simpa [Set.inter_comm] using hmeet_left⟩
      · exact ⟨ha_ne_right.symm, by simpa [Set.inter_comm] using hmeet_right⟩
    apply hz_not_forbidden i
    left
    simpa [hza] using ha_common
  have hsome_disjoint (i : Fin t) :
      Disjoint (left i).1 (z i).1 ∨ Disjoint (right i).1 (z i).1 := by
    by_cases hl : Disjoint (left i).1 (z i).1
    · exact Or.inl hl
    right
    by_contra hr
    have hz_common : z i ∈ H.commonNeighborEdges (left i) (right i) := by
      constructor
      · exact ⟨(hz_ne_left i).symm,
          Set.not_disjoint_iff_nonempty_inter.mp hl⟩
      · exact ⟨(hz_ne_right i).symm,
          Set.not_disjoint_iff_nonempty_inter.mp hr⟩
    exact hz_not_forbidden i (Or.inl hz_common)
  let chooseLeft (i : Fin t) : Prop := Disjoint (left i).1 (z i).1
  let chosen (i : Fin t) : H := if chooseLeft i then left i else right i
  let side (i : Fin t) : Fin t ⊕ Fin t :=
    if chooseLeft i then Sum.inl i else Sum.inr i
  have chosen_eq_endpoint (i : Fin t) : chosen i = endpoint (side i) := by
    simp only [chosen, side, endpoint, chooseLeft]
    split <;> rfl
  let pairIndex : Fin t ⊕ Fin t → Fin t := Sum.elim id id
  have pairIndex_side (i : Fin t) : pairIndex (side i) = i := by
    simp only [pairIndex, side]
    split <;> rfl
  have side_injective : Function.Injective side := by
    intro i j hij
    simpa only [pairIndex_side] using congrArg pairIndex hij
  have chosen_injective : Function.Injective chosen := by
    intro i j hij
    apply side_injective
    apply endpoint_injective
    simpa only [← chosen_eq_endpoint] using hij
  have hchosen_disjoint (i : Fin t) : Disjoint (chosen i).1 (z i).1 := by
    by_cases hl : chooseLeft i
    · simpa [chosen, hl, chooseLeft] using hl
    · simpa [chosen, hl] using (hsome_disjoint i).resolve_left hl
  have hchosen_z_injective : Function.Injective (Sum.elim chosen z) := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact congrArg Sum.inl (chosen_injective hab)
    · exfalso
      exact hz_ne_endpoint j (side i) (by
        rw [← chosen_eq_endpoint]
        exact hab.symm)
    · exfalso
      exact hz_ne_endpoint i (side j) (by
        rw [← chosen_eq_endpoint]
        exact hab)
    · exact congrArg Sum.inr (z_injective hab)
  apply H.edgeColorable_of_disjoint_pairs chosen z hchosen_z_injective
    hchosen_disjoint
  omega

/-- A graph whose edges record disjoint pairs of hyperedges.  This is the
complement of the line graph (apart from loops), and is the graph used in
Observation 5.2 of Kang--Kelly--Kühn--Methuku--Osthus. -/
def disjointnessGraph (H : SetHypergraph X) : SimpleGraph H where
  Adj e f := e ≠ f ∧ Disjoint e.1 f.1
  symm := ⟨by
    rintro e f ⟨hef, hdisjoint⟩
    exact ⟨hef.symm, hdisjoint.symm⟩⟩
  loopless := ⟨by
    intro e he
    exact he.1 rfl⟩

@[simp]
lemma disjointnessGraph_adj (H : SetHypergraph X) {e f : H} :
    H.disjointnessGraph.Adj e f ↔ e ≠ f ∧ Disjoint e.1 f.1 :=
  Iff.rfl

/-- A finite disjointness graph has a matching with maximum edge cardinality. -/
lemma exists_maximum_disjointnessMatching [Fintype X] (H : SetHypergraph X) :
    ∃ M : H.disjointnessGraph.Subgraph, M.IsMatching ∧
      ∀ N : H.disjointnessGraph.Subgraph, N.IsMatching →
        N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  let matchings : Finset H.disjointnessGraph.Subgraph :=
    Finset.univ.filter SimpleGraph.Subgraph.IsMatching
  have hbottom : (⊥ : H.disjointnessGraph.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  have hnonempty : matchings.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [matchings, hbottom]
  obtain ⟨M, hMmem, hmax⟩ :=
    Finset.exists_max_image matchings
      (fun N ↦ N.edgeSet.ncard) hnonempty
  have hM : M.IsMatching := (Finset.mem_filter.mp hMmem).2
  refine ⟨M, hM, ?_⟩
  intro N hN
  exact hmax N (by simp [matchings, hN])

/-- The vertices left uncovered by a maximum matching in the hyperedge
disjointness graph are pairwise intersecting.  Otherwise their disjoint pair
could be added to the matching. -/
lemma maximum_disjointnessMatching_unmatched_pairwise_intersect [Fintype X]
    (H : SetHypergraph X) (M : H.disjointnessGraph.Subgraph)
    (hM : M.IsMatching)
    (hmax : ∀ N : H.disjointnessGraph.Subgraph, N.IsMatching →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.vertsᶜ.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty := by
  classical
  intro e he f hf hef
  by_contra hinter
  have hdisjoint : Disjoint e.1 f.1 := by
    by_contra hd
    exact hinter (Set.not_disjoint_iff_nonempty_inter.mp hd)
  have hadj : H.disjointnessGraph.Adj e f := ⟨hef, hdisjoint⟩
  let P := H.disjointnessGraph.subgraphOfAdj hadj
  have hP : P.IsMatching := SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hadj
  have hsupports : Disjoint M.support P.support := by
    rw [hM.support_eq_verts, show P.support = {e, f} by
      simpa [P] using SimpleGraph.Subgraph.support_subgraphOfAdj hadj]
    rw [Set.disjoint_left]
    intro x hxM hxpair
    rcases hxpair with (rfl | rfl)
    · exact he hxM
    · exact hf hxM
  let N := M ⊔ P
  have hN : N.IsMatching := hM.sup hP hsupports
  have hnew : s(e, f) ∉ M.edgeSet := by
    intro hedge
    have hMadj : M.Adj e f := SimpleGraph.Subgraph.mem_edgeSet.mp hedge
    exact he (M.edge_vert hMadj)
  have hNcard : N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    rw [show N.edgeSet = M.edgeSet ∪ P.edgeSet from
      SimpleGraph.Subgraph.edgeSet_sup]
    rw [show P.edgeSet = {s(e, f)} by
      simpa [P] using SimpleGraph.Subgraph.edgeSet_subgraphOfAdj hadj]
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hnew]
  have := hmax N hN
  omega

/-- A finite graph matching has exactly twice as many incident vertices as
edges.  We prove this by counting the two-element fibers of Mathlib's
`IsMatching.toEdge` map. -/
lemma matching_verts_ncard [Fintype X] (H : SetHypergraph X)
    (M : H.disjointnessGraph.Subgraph) (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  letI : Fintype M.verts := Fintype.ofFinite M.verts
  letI : Fintype M.edgeSet := Fintype.ofFinite M.edgeSet
  have hfiber (y : M.edgeSet) :
      ((Finset.univ : Finset M.verts).filter (fun x ↦ hM.toEdge x = y)).card = 2 := by
    rcases y with ⟨⟨u, v⟩, huv⟩
    have hadj : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp huv
    have hpre := hM.toEdge_preimage_singleton hadj
    have hfilter :
        (Finset.univ : Finset M.verts).filter
            (fun x ↦ hM.toEdge x = ⟨s(u, v), huv⟩) =
          {⟨u, hadj.fst_mem⟩, ⟨v, hadj.snd_mem⟩} := by
      ext w
      have hw := Set.ext_iff.mp hpre w
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_insert_iff] using hw
    rw [hfilter]
    simp [Subtype.ext_iff, hadj.ne]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset M.verts))
    (t := (Finset.univ : Finset M.edgeSet))
    (f := hM.toEdge) (fun _ _ ↦ Finset.mem_univ _)
  calc
    M.verts.ncard = Fintype.card M.verts := (Set.fintypeCard_eq_ncard _).symm
    _ = (Finset.univ : Finset M.verts).card := by simp
    _ = ∑ y ∈ (Finset.univ : Finset M.edgeSet),
        ((Finset.univ : Finset M.verts).filter (fun x ↦ hM.toEdge x = y)).card := hsum
    _ = ∑ _y ∈ (Finset.univ : Finset M.edgeSet), 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact hfiber y
    _ = 2 * Fintype.card M.edgeSet := by simp [Nat.mul_comm]
    _ = 2 * M.edgeSet.ncard := by rw [Set.fintypeCard_eq_ncard]

/-- Observation 5.2 of Kang--Kelly--Kühn--Methuku--Osthus.  A matching of
`m` disjoint pairs of hyperedges saves exactly `m` colors: give both endpoints
of every matched pair one label, and give each unmatched edge its own label.
Thus a matching of size at least `|H| - k` yields a proper `k`-edge-coloring. -/
theorem edgeColorable_of_disjointnessMatching [Fintype X]
    (H : SetHypergraph X) (M : H.disjointnessGraph.Subgraph)
    (hM : M.IsMatching) {k : ℕ}
    (hsize : Fintype.card H ≤ k + M.edgeSet.ncard) :
    H.EdgeColorable k := by
  classical
  let Label := M.edgeSet ⊕ {e : H // e ∉ M.verts}
  let label : H → Label := fun e ↦
    if he : e ∈ M.verts then Sum.inl (hM.toEdge ⟨e, he⟩)
    else Sum.inr ⟨e, he⟩
  have hlabel : ∀ ⦃e f : H⦄, e ≠ f → label e = label f → Disjoint e.1 f.1 := by
    intro e f hef hsame
    by_cases he : e ∈ M.verts
    · by_cases hf : f ∈ M.verts
      · have hedges : hM.toEdge ⟨e, he⟩ = hM.toEdge ⟨f, hf⟩ := by
          simp only [label, dif_pos he, dif_pos hf] at hsame
          exact Sum.inl_injective hsame
        let a : M.edgeSet := hM.toEdge ⟨e, he⟩
        have hea : e ∈ (a.1 : Sym2 H) := hM.mem_coe_toEdge he
        have hfa : f ∈ (a.1 : Sym2 H) := by
          change f ∈ ((hM.toEdge ⟨e, he⟩).1 : Sym2 H)
          rw [hedges]
          exact hM.mem_coe_toEdge hf
        have haeq : a.1 = s(e, f) :=
          (Sym2.mem_and_mem_iff hef).mp ⟨hea, hfa⟩
        have hadj : M.Adj e f := SimpleGraph.Subgraph.mem_edgeSet.mp (by
          rw [← haeq]
          exact a.2)
        exact (M.adj_sub hadj).2
      · have : False := by
          have hcontra : (Sum.inl (hM.toEdge ⟨e, he⟩) : Label) =
              Sum.inr ⟨f, hf⟩ := by simpa [label, he, hf] using hsame
          exact Sum.inl_ne_inr hcontra
        exact this.elim
    · by_cases hf : f ∈ M.verts
      · have : False := by
          have hcontra : (Sum.inr ⟨e, he⟩ : Label) =
              Sum.inl (hM.toEdge ⟨f, hf⟩) := by simpa [label, he, hf] using hsame
          exact Sum.inr_ne_inl hcontra
        exact this.elim
      · have hunmatched : (⟨e, he⟩ : {e : H // e ∉ M.verts}) = ⟨f, hf⟩ := by
          simp only [label, dif_neg he, dif_neg hf] at hsame
          exact Sum.inr_injective hsame
        exact (hef (congrArg Subtype.val hunmatched)).elim
  have hverts := H.matching_verts_ncard M hM
  have hverts_le : M.verts.ncard ≤ Fintype.card H := by
    letI : Fintype M.verts := Fintype.ofFinite M.verts
    simpa only [Set.fintypeCard_eq_ncard] using
      (Fintype.card_subtype_le (fun e : H ↦ e ∈ M.verts))
  have hedge_le : M.edgeSet.ncard ≤ Fintype.card H := by omega
  have hLabel : Fintype.card Label = Fintype.card H - M.edgeSet.ncard := by
    calc
      Fintype.card Label = Fintype.card M.edgeSet +
          Fintype.card {e : H // e ∉ M.verts} := Fintype.card_sum
      _ = M.edgeSet.ncard + (Fintype.card H - M.verts.ncard) := by
        rw [Fintype.card_subtype_compl (fun e : H ↦ e ∈ M.verts)]
        rw [show Fintype.card M.edgeSet = M.edgeSet.ncard from
          Set.fintypeCard_eq_ncard M.edgeSet]
        rw [show Fintype.card {e : H // e ∈ M.verts} = M.verts.ncard from
          Set.fintypeCard_eq_ncard M.verts]
      _ = Fintype.card H - M.edgeSet.ncard := by omega
  apply H.edgeColorable_of_compression label hlabel
  rw [hLabel]
  omega

/-- Proposition 5.4 of Kang--Kelly--Kühn--Methuku--Osthus.  If the edge set
is partitioned into `A` and `B`, the excess over `n` is at most one quarter of
`A`, and every intersecting pair in `A` is useful, then `H` is `n`-edge
colorable. -/
theorem edgeColorable_of_useful_partition [Fintype X]
    (H : SetHypergraph X) {n : ℕ} (hn : 2 ≤ n) (A B : Set H)
    (hdisjoint : Disjoint A B) (hpartition : A ∪ B = Set.univ)
    (hsurplus : A.ncard + B.ncard - n ≤ A.ncard / 4)
    (huseful : ∀ {e : H}, e ∈ A → ∀ {f : H}, f ∈ A →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f) :
    H.EdgeColorable n := by
  classical
  have hpartition_card : Fintype.card H = A.ncard + B.ncard := by
    calc
      Fintype.card H = (Set.univ : Set H).ncard := by simp
      _ = (A ∪ B).ncard := by rw [hpartition]
      _ = A.ncard + B.ncard := Set.ncard_union_eq hdisjoint
  by_cases hsmall : Fintype.card H ≤ n
  · apply H.edgeColorable_of_compression (fun e : H ↦ e)
    · intro e f hef heq
      exact (hef heq).elim
    · simpa using hsmall
  let t := A.ncard + B.ncard - n
  obtain ⟨M, hM, hmax⟩ := H.exists_maximum_disjointnessMatching
  by_cases hlargeMatching : t ≤ M.edgeSet.ncard
  · apply H.edgeColorable_of_disjointnessMatching M hM
    rw [hpartition_card]
    dsimp only [t] at hlargeMatching
    omega
  have hMt : M.edgeSet.ncard < t := Nat.lt_of_not_ge hlargeMatching
  have hA_four : 4 * t ≤ A.ncard := by
    dsimp only [t]
    omega
  let S : Set H := A \ M.verts
  have hS : 2 * t ≤ S.ncard := by
    have hdiff := Set.le_ncard_sdiff M.verts A
    change A.ncard - M.verts.ncard ≤ S.ncard at hdiff
    rw [H.matching_verts_ncard M hM] at hdiff
    omega
  have hindex_card :
      Fintype.card (Fin t ⊕ Fin t) ≤ Fintype.card S := by
    rw [Fintype.card_sum, Set.fintypeCard_eq_ncard]
    simpa [two_mul] using hS
  obtain ⟨select : (Fin t ⊕ Fin t) ↪ S⟩ :=
    Function.Embedding.nonempty_of_card_le hindex_card
  let selected : Fin t ⊕ Fin t → H := fun a ↦ (select a).1
  let left : Fin t → H := fun i ↦ selected (Sum.inl i)
  let right : Fin t → H := fun i ↦ selected (Sum.inr i)
  have elim_eq_selected (a : Fin t ⊕ Fin t) :
      Sum.elim left right a = selected a := by
    rcases a with i | i <;> rfl
  have hselected : Function.Injective (Sum.elim left right) := by
    intro a b hab
    apply select.injective
    apply Subtype.ext
    rw [elim_eq_selected a, elim_eq_selected b] at hab
    exact hab
  have selected_mem_A (a : Fin t ⊕ Fin t) : selected a ∈ A :=
    (select a).2.1
  have selected_not_mem_M (a : Fin t ⊕ Fin t) : selected a ∉ M.verts :=
    (select a).2.2
  have hunmatched_pairwise :=
    H.maximum_disjointnessMatching_unmatched_pairwise_intersect M hM hmax
  have hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩
        (Sum.elim left right b).1).Nonempty := by
    intro a b hab
    have hne : selected a ≠ selected b := by
      intro h
      apply hab
      exact select.injective (Subtype.ext h)
    have hinter := hunmatched_pairwise (selected_not_mem_M a)
      (selected_not_mem_M b) hne
    rw [elim_eq_selected a, elim_eq_selected b]
    exact hinter
  have hpairs_useful : ∀ i, H.IsUseful n (left i) (right i) := by
    intro i
    apply huseful (selected_mem_A (Sum.inl i))
      (selected_mem_A (Sum.inr i))
    · intro h
      exact Sum.inl_ne_inr (select.injective (Subtype.ext h))
    · exact hall_intersect (Sum.inl i) (Sum.inr i) Sum.inl_ne_inr
  apply H.edgeColorable_of_useful_pairs hn left right hselected
    hall_intersect hpairs_useful
  rw [hpartition_card]
  dsimp only [t]
  omega

/-- The quantitative incidence condition used in Claim 1 implies the residual
condition above.  The inequality says that even after deleting the endpoints
of `t-1` pairs, the surviving edges have more than one incidence on average
per ambient vertex outside `bad`. -/
lemma exists_useful_pairs_of_outside_density [Fintype X]
    (H : SetHypergraph X) (n : ℕ) (S : Set H) (t q : ℕ) (bad : Set X)
    (houtside : ∀ e ∈ S, q ≤ (e.1 \ bad).ncard)
    (hdensity : Fintype.card X < (S.ncard - 2 * (t - 1)) * q)
    (hgood : ∀ (e f : H), e ∈ S → f ∈ S → e ≠ f →
      ∀ x, x ∉ bad → x ∈ e.1 → x ∈ f.1 → H.IsUseful n e f) :
    ∃ left right : Fin t → H,
      Function.Injective (Sum.elim left right) ∧
        (∀ i, H.IsUseful n (left i) (right i)) ∧
        (∀ i, left i ∈ S ∧ right i ∈ S) := by
  apply H.exists_useful_pairs_of_residual_condition n S t
  intro T hT
  let R : Set H := Subtype.val '' T
  have hRcard : R.ncard = T.ncard := by
    exact Set.ncard_image_of_injective T Subtype.val_injective
  have hRsubset : R ⊆ S := by
    rintro e ⟨eS, -, rfl⟩
    exact eS.2
  have hRoutside : ∀ e ∈ R, q ≤ (e.1 \ bad).ncard := by
    intro e he
    exact houtside e (hRsubset he)
  have hRlarge : Fintype.card X < R.ncard * q := by
    rw [hRcard]
    exact hdensity.trans_le (Nat.mul_le_mul_right q hT)
  obtain ⟨e, heR, f, hfR, hef, huseful⟩ :=
    H.exists_useful_pair_of_many_outside n R bad q hRoutside hRlarge
      (fun e f he hf hne x hxbad hxe hxf ↦
        hgood e f (hRsubset he) (hRsubset hf) hne x hxbad hxe hxf)
  rcases heR with ⟨eS, heT, heval⟩
  rcases hfR with ⟨fS, hfT, hfval⟩
  have heSval : eS.1 = e := heval
  have hfSval : fS.1 = f := hfval
  have hefS : eS ≠ fS := by
    intro h
    apply hef
    rw [← heSval, ← hfSval, h]
  refine ⟨eS, heT, fS, hfT, hefS, ?_⟩
  simpa [heSval, hfSval] using huseful

/-- Claim 1 plus Proposition 5.3, abstracted from the particular numerical
parameter choices of Lemma 5.1. -/
theorem edgeColorable_of_pairwise_intersecting_outside_density [Fintype X]
    (H : SetHypergraph X) {n t q : ℕ} (hn : 2 ≤ n) (S : Set H)
    (bad : Set X) (hcard : Fintype.card H = n + t)
    (hpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty)
    (houtside : ∀ e ∈ S, q ≤ (e.1 \ bad).ncard)
    (hdensity : Fintype.card X < (S.ncard - 2 * (t - 1)) * q)
    (hgood : ∀ (e f : H), e ∈ S → f ∈ S → e ≠ f →
      ∀ x, x ∉ bad → x ∈ e.1 → x ∈ f.1 → H.IsUseful n e f) :
    H.EdgeColorable n := by
  obtain ⟨left, right, hinjective, huseful, hmem⟩ :=
    H.exists_useful_pairs_of_outside_density n S t q bad
      houtside hdensity hgood
  have endpoint_mem (a : Fin t ⊕ Fin t) : Sum.elim left right a ∈ S := by
    rcases a with i | i
    · exact (hmem i).1
    · exact (hmem i).2
  have hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩
        (Sum.elim left right b).1).Nonempty := by
    intro a b hab
    apply hpairwise (endpoint_mem a) (endpoint_mem b)
    intro heq
    exact hab (hinjective heq)
  exact H.edgeColorable_of_useful_pairs hn left right hinjective
    hall_intersect huseful hcard

/-- Claim 1 specialized to the projective-scale class.  The bad vertices are
exactly those incident with more than `qSmall` sub-scale edges, so every
intersection outside `bad` is useful by Proposition 5.5(ii). -/
theorem edgeColorable_of_projectiveScale_outside_density [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall t qOutside : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (S : Set H) (hcard : Fintype.card H = n + t)
    (hscale : ∀ e ∈ S, e.1.ncard = projectiveScale n)
    (hpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty)
    (houtside : ∀ e ∈ S, qOutside ≤
      (e.1 \ {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}).ncard)
    (hdensity : n < (S.ncard - 2 * (t - 1)) * qOutside) :
    H.EdgeColorable n := by
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  apply H.edgeColorable_of_pairwise_intersecting_outside_density (by omega) S bad
    hcard hpairwise
  · simpa only [bad] using houtside
  · simpa only [hvertices] using hdensity
  · intro e f he hf hef x hxbad hxe hxf
    have hsmallx :
        (H.smallIncidentEdges x (projectiveScale n)).ncard ≤ qSmall := by
      change ¬qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard at hxbad
      omega
    exact H.isUseful_of_few_small_incident_below_projectiveScale hlinear
      n r qSmall hn hvertices hr hrscale hmin hdefect e f hef x hxe hxf
      (hscale e he) (hscale f hf) hsmallx

/-- The difficult Claim 1 branch of Lemma 5.1, reduced to one exact density
inequality.  A maximum disjointness matching either already compresses enough
colors, or its unmatched edges are pairwise intersecting.  After deleting the
heavy projective edges, incidence averaging produces the required useful-pair
matching. -/
theorem edgeColorable_of_projectiveScale_claim [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside t : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hcard : Fintype.card H = n + t)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          ({e : H | e.1.ncard = projectiveScale n ∧
            s ≤ (e.1 ∩
              {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}).ncard} :
            Set H).ncard -
          4 * (t - 1)) * qOutside) :
    H.EdgeColorable n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  let Aplus : Set H := {e | e.1.ncard = projectiveScale n}
  let heavy : Set H :=
    {e | e.1.ncard = projectiveScale n ∧ s ≤ (e.1 ∩ bad).ncard}
  obtain ⟨M, hM, hmax⟩ := H.exists_maximum_disjointnessMatching
  by_cases hlarge : t ≤ M.edgeSet.ncard
  · apply H.edgeColorable_of_disjointnessMatching M hM
    rw [hcard]
    omega
  have hMlt : M.edgeSet.ncard < t := Nat.lt_of_not_ge hlarge
  have hMle : M.edgeSet.ncard ≤ t - 1 := by omega
  let S : Set H := Aplus \ (heavy ∪ M.verts)
  have hSscale : ∀ e ∈ S, e.1.ncard = projectiveScale n := by
    intro e he
    exact he.1
  have hSpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty := by
    intro e he f hf hef
    apply H.maximum_disjointnessMatching_unmatched_pairwise_intersect M hM hmax
    · intro heM
      exact he.2 (Or.inr heM)
    · intro hfM
      exact hf.2 (Or.inr hfM)
    · exact hef
  have hunion : (heavy ∪ M.verts).ncard ≤ heavy.ncard + M.verts.ncard :=
    Set.ncard_union_le _ _
  have hdiff := Set.le_ncard_sdiff (heavy ∪ M.verts) Aplus
  have hbase : Aplus.ncard - heavy.ncard - M.verts.ncard ≤ S.ncard := by
    calc
      Aplus.ncard - heavy.ncard - M.verts.ncard =
          Aplus.ncard - (heavy.ncard + M.verts.ncard) := Nat.sub_sub _ _ _
      _ ≤ Aplus.ncard - (heavy ∪ M.verts).ncard :=
        Nat.sub_le_sub_left hunion _
      _ ≤ S.ncard := hdiff
  have hverts := H.matching_verts_ncard M hM
  have hSbound :
      Aplus.ncard - heavy.ncard - 2 * (t - 1) ≤ S.ncard := by
    calc
      Aplus.ncard - heavy.ncard - 2 * (t - 1) ≤
          Aplus.ncard - heavy.ncard - M.verts.ncard := by
        rw [hverts]
        omega
      _ ≤ S.ncard := hbase
  have hSresidual :
      Aplus.ncard - heavy.ncard - 4 * (t - 1) ≤
        S.ncard - 2 * (t - 1) := by
    have h := Nat.sub_le_sub_right hSbound (2 * (t - 1))
    omega
  have hSdensity : n < (S.ncard - 2 * (t - 1)) * qOutside := by
    have hdensity' : n <
        (Aplus.ncard - heavy.ncard - 4 * (t - 1)) * qOutside := by
      simpa only [Aplus, heavy, bad] using hdensity
    exact hdensity'.trans_le (Nat.mul_le_mul_right qOutside hSresidual)
  have hSoutside : ∀ e ∈ S, qOutside ≤ (e.1 \ bad).ncard := by
    intro e he
    have heplus : e ∈ Aplus := he.1
    have henotheavy : e ∉ heavy := by
      intro heheavy
      exact he.2 (Or.inl heheavy)
    have hinter : (e.1 ∩ bad).ncard < s := by
      by_contra hnot
      apply henotheavy
      exact ⟨heplus, by omega⟩
    exact ncard_sdiff_ge_of_ncard_inter_lt e.1 bad (projectiveScale n)
      s qOutside heplus hinter houtside
  apply H.edgeColorable_of_projectiveScale_outside_density hlinear
    n r qSmall t qOutside hn hvertices hr hrscale hmin hdefect S hcard
    hSscale hSpairwise
  · simpa only [bad] using hSoutside
  · simpa only [hvertices] using hSdensity

/-- The incidence estimates (5.11)--(5.12) discharge the density premise of
`edgeColorable_of_projectiveScale_claim`.  Unlike the paper's displayed
asymptotic bounds, this statement keeps both integer divisions explicit:
`badBound` bounds vertices incident with more than `qSmall` sub-scale edges,
and `heavyBound` then bounds projective-scale edges containing at least `s`
such vertices. -/
theorem edgeColorable_of_projectiveScale_claim_of_floor_density [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside t : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hcard : Fintype.card H = n + t)
    (hs : 0 < s)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          ((({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
                (projectiveScale n - 1) / (qSmall + 1)) *
              ((n - 1) / (projectiveScale n - 1)) / s) -
          4 * (t - 1)) * qOutside) :
    H.EdgeColorable n := by
  classical
  let Aminus : Set H := {e | e.1.ncard < projectiveScale n}
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  let heavy : Set H :=
    {e | e.1.ncard = projectiveScale n ∧ s ≤ (e.1 ∩ bad).ncard}
  let badBound : ℕ := Aminus.ncard * (projectiveScale n - 1) / (qSmall + 1)
  let heavyBound : ℕ :=
    badBound * ((n - 1) / (projectiveScale n - 1)) / s
  have hbadmul : bad.ncard * (qSmall + 1) ≤
      Aminus.ncard * (projectiveScale n - 1) := by
    have h := H.badVertices_ncard_mul_le_subscaleEdges
      (projectiveScale n) (qSmall + 1)
    simpa only [Aminus, bad, Nat.lt_iff_add_one_le] using h
  have hbad : bad.ncard ≤ badBound := by
    dsimp only [badBound]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < qSmall + 1)).2 hbadmul
  have hk : 2 ≤ projectiveScale n := two_le_projectiveScale hn
  have hheavymul : heavy.ncard * s ≤
      bad.ncard * ((n - 1) / (projectiveScale n - 1)) := by
    have h := H.heavyProjectiveEdges_ncard_mul_le_badVertices hlinear
      (projectiveScale n) s hk bad
    simpa only [heavy, hvertices] using h
  have hheavymul' : heavy.ncard * s ≤
      badBound * ((n - 1) / (projectiveScale n - 1)) :=
    hheavymul.trans (Nat.mul_le_mul_right _ hbad)
  have hheavy : heavy.ncard ≤ heavyBound := by
    dsimp only [heavyBound]
    exact (Nat.le_div_iff_mul_le hs).2 hheavymul'
  apply H.edgeColorable_of_projectiveScale_claim hlinear
    n r qSmall s qOutside t hn hvertices hr hrscale hmin hdefect hcard
    houtside
  have hdensity' : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          heavyBound - 4 * (t - 1)) * qOutside := by
    simpa only [Aminus, badBound, heavyBound] using hdensity
  have hresidual :
      ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            heavyBound - 4 * (t - 1) ≤
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            heavy.ncard - 4 * (t - 1) := by
    exact Nat.sub_le_sub_right
      (Nat.sub_le_sub_left hheavy
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard)
      (4 * (t - 1))
  have := hdensity'.trans_le (Nat.mul_le_mul_right qOutside hresidual)
  simpa only [heavy, bad] using this

/-- The line graph of a hypergraph: its vertices are hyperedges, and distinct
vertices are adjacent exactly when the corresponding hyperedges intersect. -/
def lineGraph (H : SetHypergraph X) : SimpleGraph H where
  Adj e f := e ≠ f ∧ (e.1 ∩ f.1).Nonempty
  symm := ⟨by
    rintro e f ⟨hef, x, hxe, hxf⟩
    exact ⟨hef.symm, x, hxf, hxe⟩⟩
  loopless := ⟨by
    intro e he
    exact he.1 rfl⟩

@[simp]
lemma lineGraph_adj (H : SetHypergraph X) {e f : H} :
    H.lineGraph.Adj e f ↔ e ≠ f ∧ (e.1 ∩ f.1).Nonempty :=
  Iff.rfl

/-- Hypergraph edge colorings are definitionally the same data as vertex
colorings of the line graph. -/
lemma edgeColorable_iff_lineGraph_colorable (H : SetHypergraph X) (k : ℕ) :
    H.EdgeColorable k ↔ H.lineGraph.Colorable k := by
  constructor
  · rintro ⟨c⟩
    exact ⟨SimpleGraph.Coloring.mk c.color fun hef ↦ c.valid hef.1 hef.2⟩
  · rintro ⟨c⟩
    refine ⟨{ color := c, valid := ?_ }⟩
    intro e f hef hinter
    exact c.valid ⟨hef, hinter⟩

/-- The hypergraph neighbor family is exactly the graph-theoretic neighbor set
in the line graph. -/
lemma lineGraph_neighborSet (H : SetHypergraph X) (e : H) :
    H.lineGraph.neighborSet e = H.neighborEdges e :=
  rfl

/-! ### Exact local-sparsity bookkeeping for Section 6 -/

/-- If every edge through a vertex has at least `r` vertices, the incident
degree is at most the natural-number quotient `(n - 1) / (r - 1)`.  This is
the division form of `incidentEdges_ncard_mul_sub_one_le`. -/
lemma incidentEdges_ncard_le_div_of_min_size [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (x : X) (r : ℕ)
    (hr : 2 ≤ r) (hsize : ∀ e : H, r ≤ e.1.ncard) :
    (H.incidentEdges x).ncard ≤ (Fintype.card X - 1) / (r - 1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).2
  exact H.incidentEdges_ncard_mul_sub_one_le hlinear x r
    (fun e _he ↦ hsize e)

/-- Exact common-neighborhood estimate used in Corollaries 6.5 and 6.7.
When all hyperedges have sizes in `[r,R]`, common line-graph neighbors of an
intersecting pair split into those through the common point and those meeting
the two edges at two different points. -/
lemma commonNeighborEdges_ncard_le_of_size_range [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (r R : ℕ)
    (hr : 2 ≤ r) (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hmax : ∀ e : H, e.1.ncard ≤ R)
    (e f : H) (hef : e ≠ f) (hinter : (e.1 ∩ f.1).Nonempty) :
    (H.commonNeighborEdges e f).ncard ≤
      (R - 1) * (R - 1) + (Fintype.card X - 1) / (r - 1) := by
  obtain ⟨w, hwe, hwf⟩ := hinter
  have hraw := H.commonNeighborEdges_ncard_le hlinear e f hef w hwe hwf
  have hprod : (e.1.ncard - 1) * (f.1.ncard - 1) ≤
      (R - 1) * (R - 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_right (hmax e) 1)
      (Nat.sub_le_sub_right (hmax f) 1)
  have hdegree : (H.incidentEdges w).ncard ≤
      (Fintype.card X - 1) / (r - 1) :=
    H.incidentEdges_ncard_le_div_of_min_size hlinear w r hr hmin
  exact hraw.trans ((Nat.sub_le _ _).trans (Nat.add_le_add hprod hdegree))

/-- The exact handshaking bound for the graph induced by one line-graph
neighborhood.  Under a uniform edge-size window `[r,R]`, twice the number of
edges inside `N(e)` is at most `|N(e)|` times the common-neighborhood bound.
This is the finite combinatorial input immediately preceding the invocation
of the Molloy--Reed locally sparse coloring theorem in Corollary 6.5. -/
lemma two_mul_card_lineGraph_induce_neighborEdges_le [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (r R : ℕ)
    (hr : 2 ≤ r) (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hmax : ∀ e : H, e.1.ncard ≤ R) (e : H) :
    2 * (H.lineGraph.induce (H.neighborEdges e)).edgeSet.ncard ≤
      (H.neighborEdges e).ncard *
        ((R - 1) * (R - 1) + (Fintype.card X - 1) / (r - 1)) := by
  classical
  let K := H.lineGraph.induce (H.neighborEdges e)
  let q := (R - 1) * (R - 1) + (Fintype.card X - 1) / (r - 1)
  have hdegree (f : H.neighborEdges e) : K.degree f ≤ q := by
    let code (g : K.neighborSet f) : H.commonNeighborEdges e f.1 :=
      ⟨g.1.1, g.1.2, by
        change f.1 ≠ g.1.1 ∧ (f.1.1 ∩ g.1.1.1).Nonempty
        exact g.2⟩
    have hcode : Function.Injective code := by
      intro g h hgh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : H.commonNeighborEdges e f.1 ↦ z.1) hgh
    have hcard : K.degree f ≤ (H.commonNeighborEdges e f.1).ncard := by
      calc
        K.degree f = Fintype.card (K.neighborSet f) :=
          (K.card_neighborSet_eq_degree f).symm
        _ ≤ Fintype.card (H.commonNeighborEdges e f.1) :=
          Fintype.card_le_of_injective code hcode
        _ = (H.commonNeighborEdges e f.1).ncard :=
          Set.fintypeCard_eq_ncard _
    have hef : e ≠ f.1 := f.2.1
    have hinter : (e.1 ∩ f.1.1).Nonempty := f.2.2
    exact hcard.trans
      (H.commonNeighborEdges_ncard_le_of_size_range hlinear r R hr hmin hmax
        e f.1 hef hinter)
  have hedgecard : K.edgeSet.ncard = K.edgeFinset.card := by
    calc
      K.edgeSet.ncard = Fintype.card K.edgeSet :=
        (Set.fintypeCard_eq_ncard _).symm
      _ = K.edgeFinset.card := K.card_edgeSet
  change 2 * K.edgeSet.ncard ≤ (H.neighborEdges e).ncard * q
  calc
    2 * K.edgeSet.ncard = 2 * K.edgeFinset.card := by rw [hedgecard]
    _ = ∑ f : H.neighborEdges e, K.degree f :=
      K.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _f : H.neighborEdges e, q := by
      apply Finset.sum_le_sum
      intro f _
      exact hdegree f
    _ = (H.neighborEdges e).ncard * q := by
      simp [Set.fintypeCard_eq_ncard]
    _ = (H.neighborEdges e).ncard *
        ((R - 1) * (R - 1) + (Fintype.card X - 1) / (r - 1)) := rfl

/-- The subhypergraph consisting of edges of size at least two. -/
def nontrivialEdges (H : SetHypergraph X) : SetHypergraph X :=
  {e | e ∈ H ∧ 2 ≤ e.ncard}

/-- Original edges of size at least two which are incident with `x`. -/
def nontrivialIncidentEdges (H : SetHypergraph X) (x : X) : Set H :=
  {e | 2 ≤ e.1.ncard ∧ x ∈ e.1}

/-- If the singleton edge `{x}` is present, then the size-at-least-two edges
at `x` have strictly fewer than `|X|` members.  They form a proper subset of
all incident edges, whose cardinality is at most `|X|`. -/
lemma nontrivialIncidentEdges_ncard_lt [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (x : X)
    (hsingleton : ({x} : Set X) ∈ H) :
    (H.nontrivialIncidentEdges x).ncard < Fintype.card X := by
  classical
  let singletonEdge : H := ⟨{x}, hsingleton⟩
  have hproper : H.nontrivialIncidentEdges x ⊂ H.incidentEdges x := by
    constructor
    · intro e he
      exact he.2
    · intro hsubset
      have hmem : singletonEdge ∈ H.incidentEdges x := by simp [singletonEdge, incidentEdges]
      have hbad := hsubset hmem
      have : 2 ≤ ({x} : Set X).ncard := hbad.1
      simp at this
  exact (Set.ncard_lt_ncard hproper).trans_le (H.incidentEdges_ncard_le hlinear x)

/-- Ordered pairs of distinct points of a set, represented in the ambient
product type. -/
def OrderedPairsInSet (s : Set X) :=
  {p : X × X // p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2}

noncomputable instance instFintypeOrderedPairsInSet [Fintype X] (s : Set X) :
    Fintype (OrderedPairsInSet s) := by
  letI : Finite (OrderedPairsInSet s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (OrderedPairsInSet s)

/-- The number of ordered pairs of distinct points of a finite set. -/
lemma card_orderedPairsInSet [Fintype X] (s : Set X) :
    Fintype.card (OrderedPairsInSet s) =
      s.ncard * (s.ncard - 1) := by
  classical
  let pairEquiv :
      OrderedPairsInSet s ≃ Σ x : s, {y : s // y ≠ x} :=
    { toFun := fun p ↦
        ⟨⟨p.1.1, p.2.1⟩,
          ⟨⟨p.1.2, p.2.2.1⟩,
            fun h ↦ p.2.2.2 (congrArg Subtype.val h).symm⟩⟩
      invFun := fun p ↦
        ⟨(p.1.1, p.2.1.1), p.1.2, p.2.1.2,
          fun h ↦ p.2.2 (Subtype.ext h.symm)⟩
      left_inv := by
        intro p
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        apply Sigma.ext rfl
        exact heq_of_eq (Subtype.ext rfl) }
  calc
    Fintype.card (OrderedPairsInSet s) = Fintype.card (Σ x : s, {y : s // y ≠ x}) :=
      Fintype.card_congr pairEquiv
    _ = ∑ x : s, Fintype.card {y : s // y ≠ x} := Fintype.card_sigma
    _ = ∑ _x : s, (Fintype.card s - 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.card_subtype_compl (fun y : s ↦ y = x)]
      simp
    _ = Fintype.card s * (Fintype.card s - 1) := by simp
    _ = s.ncard * (s.ncard - 1) := by rw [Set.fintypeCard_eq_ncard]

/-- Global pair-volume inequality for a finite linear hypergraph.  Ordered
distinct vertex pairs belonging to labeled edges inject into the ordered
distinct pairs of the ambient vertex set. -/
lemma sum_ncard_mul_sub_one_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) :
    (∑ e : H, e.1.ncard * (e.1.ncard - 1)) ≤
      Fintype.card X * (Fintype.card X - 1) := by
  classical
  let Fiber (s : Set X) := OrderedPairsInSet s
  let code (p : Σ e : H, Fiber e.1) : Fiber (Set.univ : Set X) :=
    ⟨p.2.1, by simp only [Set.mem_univ, ne_eq, true_and]; exact p.2.2.2.2⟩
  have code_injective : Function.Injective code := by
    intro p q hcode
    have hpairs : p.2.1 = q.2.1 := congrArg Subtype.val hcode
    have hedge : p.1 = q.1 := by
      apply Subtype.ext
      by_contra hpq
      have hsub : (p.1.1 ∩ q.1.1).Subsingleton :=
        hlinear p.1.2 q.1.2 hpq
      have hfirst : p.2.1.1 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.1, ?_⟩
        have hq := q.2.2.1
        rw [← congrArg Prod.fst hpairs] at hq
        exact hq
      have hsecond : p.2.1.2 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.2.1, ?_⟩
        have hq := q.2.2.2.1
        rw [← congrArg Prod.snd hpairs] at hq
        exact hq
      exact p.2.2.2.2 (hsub hfirst hsecond)
    apply Sigma.ext hedge
    exact (Subtype.heq_iff_coe_eq (fun z ↦ by rw [hedge])).2 hpairs
  let embedding : (Σ e : H, Fiber e.1) ↪ Fiber (Set.univ : Set X) :=
    ⟨code, code_injective⟩
  have hcard := Fintype.card_le_of_embedding embedding
  calc
    (∑ e : H, e.1.ncard * (e.1.ncard - 1)) =
        ∑ e : H, Fintype.card (Fiber e.1) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (card_orderedPairsInSet e.1).symm
    _ = Fintype.card (Σ e : H, Fiber e.1) := by rw [Fintype.card_sigma]
    _ ≤ Fintype.card (Fiber (Set.univ : Set X)) := hcard
    _ = (Set.univ : Set X).ncard * ((Set.univ : Set X).ncard - 1) :=
      card_orderedPairsInSet Set.univ
    _ = Fintype.card X * (Fintype.card X - 1) := by simp

/-- A pairwise edge-disjoint family of matchings cannot simultaneously cover
too many vertices with large hyperedges.  If every matching covers at least
`a` vertices and all of its edges have size at least `r + 1`, then each
matching consumes at least `a * r` ordered vertex pairs.  Edge-disjointness
of the matchings lets us charge these contributions to the global pair budget
of a linear hypergraph.  This is the integral core of Proposition 6.8(i). -/
lemma matching_family_cover_mul_le_pairBudget [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    {I : Type*} [Fintype I] (M : I → Set H)
    (hmatching : ∀ i, H.IsMatching (M i))
    (hdisjoint : ∀ {i j : I}, i ≠ j → Disjoint (M i) (M j))
    (a r : ℕ)
    (hcover : ∀ i, a ≤ (H.coveredVertices (M i)).ncard)
    (hmin : ∀ i e, e ∈ M i → r + 1 ≤ e.1.ncard) :
    Fintype.card I * a * r ≤
      Fintype.card X * (Fintype.card X - 1) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let weight : H → ℕ := fun e ↦ e.1.ncard * (e.1.ncard - 1)
  have hone (i : I) :
      a * r ≤ ∑ e ∈ (M i).toFinset, weight e := by
    have hpair := (hmatching i).coveredVertices_ncard_mul_le_pairWeight r
      (hmin i)
    rw [finsum_mem_eq_finite_toFinset_sum weight (M i).toFinite] at hpair
    have hfinEq : (M i).toFinite.toFinset = (M i).toFinset := by
      ext e
      simp
    rw [hfinEq] at hpair
    exact (Nat.mul_le_mul_right r (hcover i)).trans hpair
  have hfinDisjoint :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset I))
        (fun i ↦ (M i).toFinset) := by
    intro i _hi j _hj hij
    change Disjoint (M i).toFinset (M j).toFinset
    rw [Finset.disjoint_left]
    intro e hei hej
    exact Set.disjoint_left.mp (hdisjoint hij)
      (Set.mem_toFinset.mp hei) (Set.mem_toFinset.mp hej)
  have hunionSubset :
      (Finset.univ.biUnion fun i : I ↦ (M i).toFinset) ⊆
        (Finset.univ : Finset H) :=
    Finset.subset_univ _
  have htotal := H.sum_ncard_mul_sub_one_le hlinear
  calc
    Fintype.card I * a * r = ∑ _i : I, a * r := by
      simp [Nat.mul_assoc]
    _ ≤ ∑ i : I, ∑ e ∈ (M i).toFinset, weight e := by
      apply Finset.sum_le_sum
      intro i _
      exact hone i
    _ = ∑ e ∈ (Finset.univ.biUnion fun i : I ↦ (M i).toFinset),
        weight e := by
      symm
      exact Finset.sum_biUnion hfinDisjoint
    _ ≤ ∑ e ∈ (Finset.univ : Finset H), weight e :=
      Finset.sum_le_sum_of_subset hunionSubset
    _ = ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
      simp [weight]
    _ ≤ Fintype.card X * (Fintype.card X - 1) := htotal

/-- The color-class form of Proposition 6.8(i).  In a proper coloring, color
classes are pairwise edge-disjoint matchings.  Consequently, if every edge
has size at least `r + 1`, then the number of colors whose classes cover more
than `A` vertices satisfies the displayed integral pair-budget bound. -/
lemma large_colorClasses_mul_le_pairBudget [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    {K : Type*} [Fintype K] (color : H → K)
    (hproper :
      ∀ {e f : H}, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f)
    (A r : ℕ) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard) :
    ({c : K | A < (H.coveredVertices {e | color e = c}).ncard} : Set K).ncard *
        (A + 1) * r ≤
      Fintype.card X * (Fintype.card X - 1) := by
  classical
  let C : Set K :=
    {c | A < (H.coveredVertices {e | color e = c}).ncard}
  let M : C → Set H := fun c ↦ {e | color e = c.1}
  have hproper' :
      ∀ ⦃e f : H⦄, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f := by
    intro e f
    exact hproper
  have hclasses : ∀ c : K, H.IsMatching {e | color e = c} :=
    (H.edgeColoring_iff_colorClasses_matching color).mp hproper'
  have hmatching : ∀ c, H.IsMatching (M c) := by
    intro c
    exact hclasses c.1
  have hdisjoint : ∀ {c d : C}, c ≠ d → Disjoint (M c) (M d) := by
    intro c d hcd
    rw [Set.disjoint_left]
    intro e hec hed
    apply hcd
    apply Subtype.ext
    exact hec.symm.trans hed
  have hcover : ∀ c, A + 1 ≤ (H.coveredVertices (M c)).ncard := by
    intro c
    exact Nat.add_one_le_iff.mpr c.2
  have hpair := H.matching_family_cover_mul_le_pairBudget hlinear M
    hmatching hdisjoint (A + 1) r hcover (fun _c e _he ↦ hmin e)
  simpa only [C, Set.fintypeCard_eq_ncard] using hpair

/-- Division form of `large_colorClasses_mul_le_pairBudget`. -/
lemma large_colorClasses_ncard_le_div [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    {K : Type*} [Fintype K] (color : H → K)
    (hproper :
      ∀ {e f : H}, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f)
    (A r : ℕ) (hr : 0 < r) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard) :
    ({c : K | A < (H.coveredVertices {e | color e = c}).ncard} : Set K).ncard ≤
      (Fintype.card X * (Fintype.card X - 1)) / ((A + 1) * r) := by
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.succ_pos A) hr)).2
  simpa [Nat.mul_assoc] using
    H.large_colorClasses_mul_le_pairBudget hlinear color hproper A r hmin

/-- Partial-coloring version of Proposition 6.8(i).  A coloring need only be
proper on the currently colored subfamily `S`; among those partial color
classes, the number covering at least `B` vertices is bounded by the same
global pair budget. -/
lemma partial_large_colorClasses_ncard_le_div [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    {K : Type*} [Fintype K] (S : Set H) (color : H → K)
    (hproper : ∀ {e f : H}, e ∈ S → f ∈ S → e ≠ f →
      (e.1 ∩ f.1).Nonempty → color e ≠ color f)
    (B r : ℕ) (hB : 0 < B) (hr : 0 < r)
    (hmin : ∀ e ∈ S, r + 1 ≤ e.1.ncard) :
    ({c : K | B ≤
      (H.coveredVertices {e : H | e ∈ S ∧ color e = c}).ncard} : Set K).ncard ≤
      (Fintype.card X * (Fintype.card X - 1)) / (B * r) := by
  classical
  let C : Set K := {c | B ≤
    (H.coveredVertices {e : H | e ∈ S ∧ color e = c}).ncard}
  let M : C → Set H := fun c ↦ {e | e ∈ S ∧ color e = c.1}
  have hmatching : ∀ c, H.IsMatching (M c) := by
    intro c e he f hf hef
    rw [Set.disjoint_left]
    intro x hxe hxf
    exact (hproper he.1 hf.1 hef ⟨x, hxe, hxf⟩) (he.2.trans hf.2.symm)
  have hdisjoint : ∀ {c d : C}, c ≠ d → Disjoint (M c) (M d) := by
    intro c d hcd
    rw [Set.disjoint_left]
    intro e hec hed
    apply hcd
    apply Subtype.ext
    exact hec.2.symm.trans hed.2
  have hcover : ∀ c, B ≤ (H.coveredVertices (M c)).ncard := fun c ↦ c.2
  have hpair := H.matching_family_cover_mul_le_pairBudget hlinear M
    hmatching hdisjoint B r hcover (fun _c e he ↦ hmin e he.1)
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hB hr)).2
  simpa only [C, Set.fintypeCard_eq_ncard, Nat.mul_assoc] using hpair

/-- Integral constant-palette form of Proposition 6.9.  Along an injective
edge ordering, suppose every edge has `margin` more available colors than
colored predecessors.  If the pair budget makes the number of color classes
already covering `A / 2 + 1` vertices smaller than `margin`, then the coloring
extends one edge at a time while every color class remains a singleton or
covers at most `A` vertices. -/
lemma exists_coverBounded_edgeColoring_of_earlierNeighbor_margin [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (rank : H → ℕ) (hrank : Function.Injective rank)
    (k margin r A : ℕ) (hk : 0 < k)
    (hearlier : ∀ e : H,
      (H.earlierNeighborEdges rank e).ncard + margin < k)
    (hr : 0 < r) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard)
    (hmax : ∀ e : H, e.1.ncard ≤ A - A / 2)
    (hmargin :
      (Fintype.card X * (Fintype.card X - 1)) /
          ((A / 2 + 1) * r) < margin) :
    ∃ color : H.EdgeColoring (Fin k), H.IsCoverBoundedColoring color A := by
  classical
  let fallback : Fin k := ⟨0, hk⟩
  let pref : ℕ → Set H := fun m ↦ {e | rank e < m}
  have aux : ∀ m : ℕ, ∃ c : H → Fin k,
      (∀ ⦃e f : H⦄, e ∈ pref m → f ∈ pref m → e ≠ f →
        (e.1 ∩ f.1).Nonempty → c e ≠ c f) ∧
      ∀ a : Fin k,
        ({e : H | e ∈ pref m ∧ c e = a} : Set H).ncard ≤ 1 ∨
          (H.coveredVertices {e : H | e ∈ pref m ∧ c e = a}).ncard ≤ A := by
    intro m
    induction m with
    | zero =>
        refine ⟨fun _ ↦ fallback, ?_, ?_⟩
        · intro e _f he
          exact (Nat.not_lt_zero _ he).elim
        · intro a
          left
          simp [pref]
    | succ m ih =>
        obtain ⟨c, hcproper, hcbounded⟩ := ih
        by_cases hex : ∃ e : H, rank e = m
        · obtain ⟨e, he⟩ := hex
          let oldClass (a : Fin k) : Set H :=
            {f | f ∈ pref m ∧ c f = a}
          let adjacent : Finset H := Finset.univ.filter fun f ↦
            rank f < m ∧ (e.1 ∩ f.1).Nonempty
          let used : Finset (Fin k) := adjacent.image c
          let heavy : Finset (Fin k) := Finset.univ.filter fun a ↦
            A / 2 + 1 ≤ (H.coveredVertices (oldClass a)).ncard
          let forbidden := used ∪ heavy
          have hadjacent : (adjacent : Set H) ⊆
              H.earlierNeighborEdges rank e := by
            intro f hf
            have hf' := (Finset.mem_filter.mp hf).2
            exact ⟨by simpa [he] using hf'.1, hf'.2⟩
          have hused : used.card ≤
              (H.earlierNeighborEdges rank e).ncard := by
            calc
              used.card ≤ adjacent.card := Finset.card_image_le
              _ = (adjacent : Set H).ncard := by simp
              _ ≤ (H.earlierNeighborEdges rank e).ncard :=
                Set.ncard_le_ncard hadjacent
          have hheavySet := H.partial_large_colorClasses_ncard_le_div hlinear
            (pref m) c
            (fun {_f _g} hf hg hfg hinter ↦ hcproper hf hg hfg hinter)
            (A / 2 + 1) r (by omega) hr
            (fun f _hf ↦ hmin f)
          have hheavy : heavy.card < margin := by
            have hheavyEq : heavy =
                ({a : Fin k | A / 2 + 1 ≤
                  (H.coveredVertices (oldClass a)).ncard} : Set (Fin k)).toFinset := by
              ext a
              simp [heavy]
            calc
              heavy.card =
                  ({a : Fin k | A / 2 + 1 ≤
                    (H.coveredVertices (oldClass a)).ncard} : Set (Fin k)).ncard := by
                rw [hheavyEq, Set.ncard_eq_toFinset_card']
              _ ≤ (Fintype.card X * (Fintype.card X - 1)) /
                  ((A / 2 + 1) * r) := by
                simpa only [oldClass] using hheavySet
              _ < margin := hmargin
          have hforbidden : forbidden.card < k := by
            have hunion : forbidden.card ≤ used.card + heavy.card := by
              simpa only [forbidden] using Finset.card_union_le used heavy
            have hearlier' := hearlier e
            omega
          obtain ⟨a, _haUniv, ha⟩ :=
            Finset.exists_mem_notMem_of_card_lt_card
              (s := forbidden) (t := Finset.univ) (by simpa using hforbidden)
          have haUsed : a ∉ used := fun h ↦ ha (Finset.mem_union_left _ h)
          have haHeavy : a ∉ heavy := fun h ↦ ha (Finset.mem_union_right _ h)
          have holdCover :
              (H.coveredVertices (oldClass a)).ncard ≤ A / 2 := by
            have := (Finset.mem_filter.not.mp haHeavy)
            simpa only [Finset.mem_univ, true_and, Nat.not_le, Nat.lt_add_one_iff,
              heavy] using this
          let c' : H → Fin k := Function.update c e a
          have hproper' :
              ∀ ⦃x y : H⦄, x ∈ pref (m + 1) → y ∈ pref (m + 1) →
                x ≠ y → (x.1 ∩ y.1).Nonempty → c' x ≠ c' y := by
            intro x y hx hy hxy hinter
            have hxle : rank x ≤ m := Nat.lt_succ_iff.mp hx
            have hyle : rank y ≤ m := Nat.lt_succ_iff.mp hy
            rcases hxle.eq_or_lt with hxm | hxm
            · have hxe : x = e := hrank (hxm.trans he.symm)
              subst x
              have hym : rank y < m :=
                hyle.lt_of_ne (fun hym ↦ hxy (hrank (he.trans hym.symm)))
              have hyadj : y ∈ adjacent :=
                Finset.mem_filter.mpr ⟨by simp, hym, hinter⟩
              have hcy : c y ∈ used := Finset.mem_image.mpr ⟨y, hyadj, rfl⟩
              have hay : a ≠ c y := fun hay ↦ haUsed (hay ▸ hcy)
              simpa [c', hxy, hxy.symm] using hay
            · rcases hyle.eq_or_lt with hym | hym
              · have hye : y = e := hrank (hym.trans he.symm)
                subst y
                have hinter' : (e.1 ∩ x.1).Nonempty := by
                  simpa [Set.inter_comm] using hinter
                have hxadj : x ∈ adjacent :=
                  Finset.mem_filter.mpr ⟨by simp, hxm, hinter'⟩
                have hcx : c x ∈ used := Finset.mem_image.mpr ⟨x, hxadj, rfl⟩
                have hax : a ≠ c x := fun hax ↦ haUsed (hax ▸ hcx)
                simpa [c', hxy, hxy.symm] using hax.symm
              · have hxe : x ≠ e := fun h ↦ by subst x; omega
                have hye : y ≠ e := fun h ↦ by subst y; omega
                exact (by simpa [pref, c', hxe, hye] using
                  hcproper hxm hym hxy hinter)
          refine ⟨c', hproper', ?_⟩
          intro z
          by_cases hza : z = a
          · subst z
            have hclass :
                ({f : H | f ∈ pref (m + 1) ∧ c' f = a} : Set H) =
                  insert e (oldClass a) := by
              ext f
              constructor
              · intro hf
                have hfle : rank f ≤ m := Nat.lt_succ_iff.mp hf.1
                rcases hfle.eq_or_lt with hfm | hfm
                · have hfe : f = e := hrank (hfm.trans he.symm)
                  exact Set.mem_insert_iff.mpr (Or.inl hfe)
                · by_cases hfe : f = e
                  · exact Set.mem_insert_iff.mpr (Or.inl hfe)
                  · apply Set.mem_insert_iff.mpr
                    right
                    exact ⟨hfm, by simpa [c', hfe] using hf.2⟩
              · intro hf
                rcases Set.mem_insert_iff.mp hf with rfl | hf
                · exact ⟨by simpa [pref, he], by simp [c']⟩
                · have hfe : f ≠ e := fun h ↦ by
                    subst f
                    exact (Nat.lt_irrefl m) (by simpa [oldClass, pref, he] using hf.1)
                  exact ⟨Nat.lt_succ_of_lt hf.1, by simpa [c', hfe] using hf.2⟩
            by_cases holdEmpty : oldClass a = ∅
            · left
              rw [hclass, holdEmpty]
              simp
            · right
              have hcoverEq :
                  H.coveredVertices (insert e (oldClass a)) =
                    e.1 ∪ H.coveredVertices (oldClass a) := by
                ext x
                simp [coveredVertices]
              rw [hclass, hcoverEq]
              calc
                (e.1 ∪ H.coveredVertices (oldClass a)).ncard ≤
                    e.1.ncard + (H.coveredVertices (oldClass a)).ncard :=
                  Set.ncard_union_le _ _
                _ ≤ (A - A / 2) + A / 2 :=
                  Nat.add_le_add (hmax e) holdCover
                _ = A := by omega
          · have hclass :
                ({f : H | f ∈ pref (m + 1) ∧ c' f = z} : Set H) =
                  oldClass z := by
              ext f
              constructor
              · intro hf
                have hfle : rank f ≤ m := Nat.lt_succ_iff.mp hf.1
                have hfm : rank f < m := by
                  exact hfle.lt_of_ne fun hfm ↦ by
                    have hfe : f = e := hrank (hfm.trans he.symm)
                    subst f
                    exact hza (by simpa [c'] using hf.2.symm)
                have hfe : f ≠ e := fun h ↦ by subst f; omega
                exact ⟨hfm, by simpa [c', hfe] using hf.2⟩
              · intro hf
                have hfe : f ≠ e := fun h ↦ by
                  subst f
                  exact (Nat.lt_irrefl m) (by simpa [oldClass, pref, he] using hf.1)
                exact ⟨Nat.lt_succ_of_lt hf.1, by simpa [c', hfe] using hf.2⟩
            simpa only [hclass] using hcbounded z
        · refine ⟨c, ?_, ?_⟩
          · intro e f he' hf' hef hinter
            have he'' : rank e < m :=
              (Nat.lt_succ_iff.mp he').lt_of_ne fun hem ↦ hex ⟨e, hem⟩
            have hf'' : rank f < m :=
              (Nat.lt_succ_iff.mp hf').lt_of_ne fun hfm ↦ hex ⟨f, hfm⟩
            exact hcproper he'' hf'' hef hinter
          · intro a
            have hclass :
                ({e : H | e ∈ pref (m + 1) ∧ c e = a} : Set H) =
                  {e : H | e ∈ pref m ∧ c e = a} := by
              ext e
              constructor
              · intro he'
                have hle : rank e ≤ m := Nat.lt_succ_iff.mp he'.1
                exact ⟨hle.lt_of_ne fun hem ↦ hex ⟨e, hem⟩, he'.2⟩
              · intro he'
                exact ⟨Nat.lt_succ_of_lt he'.1, he'.2⟩
            simpa only [hclass] using hcbounded a
  let bound : ℕ := ∑ e : H, (rank e + 1)
  have hbelow (e : H) : rank e < bound := by
    have hterm : rank e + 1 ≤ bound := by
      simpa [bound] using
        (Finset.single_le_sum (f := fun f : H ↦ rank f + 1)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e))
    exact (Nat.lt_succ_self (rank e)).trans_le hterm
  obtain ⟨c, hcproper, hcbounded⟩ := aux bound
  let color : H.EdgeColoring (Fin k) := ⟨c, fun e f hef hinter ↦
    hcproper (hbelow e) (hbelow f) hef hinter⟩
  refine ⟨color, ?_⟩
  intro a
  have hclass :
      ({e : H | color e = a} : Set H) =
        {e : H | e ∈ pref bound ∧ c e = a} := by
    ext e
    simp only [color, Set.mem_setOf_eq, true_and]
    exact ⟨fun h ↦ ⟨hbelow e, h⟩, fun h ↦ h.2⟩
  simpa only [hclass] using hcbounded a

/-- Integral finite form of Proposition 6.8(ii).  Starting with any proper
`K`-coloring of a linear hypergraph whose edges have size at least `r + 1`,
one may refine the palette so that every color class is a singleton or covers
at most `A` vertices.  Proposition 6.8(i) bounds the number of original heavy
classes, while the bin-packing lemma bounds the number of refined parts per
heavy class, giving the displayed product of two integer quotients. -/
lemma exists_cover_bounded_recoloring_card_le_pairBudget [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    {K : Type v} [Fintype K] (color : H.EdgeColoring K)
    (A r : ℕ) (hr : 0 < r) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard) :
    ∃ (L : Type (max u v)) (_ : Fintype L),
      ∃ recolor : H.EdgeColoring L,
        H.IsCoverBoundedColoring recolor A ∧
          Fintype.card L ≤ Fintype.card K +
            (Fintype.card X * (Fintype.card X - 1) / ((A + 1) * r)) *
              (Fintype.card X / (A / 2 + 1)) := by
  classical
  obtain ⟨L, hLfintype, recolor, hbounded, hpalette⟩ :=
    H.exists_cover_bounded_recoloring color A
  letI : Fintype L := hLfintype
  refine ⟨L, hLfintype, recolor, hbounded, hpalette.trans ?_⟩
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  have hproper :
      ∀ {e f : H}, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f := by
    intro e f hef hinter
    exact color.valid hef hinter
  exact H.large_colorClasses_ncard_le_div hlinear color hproper A r hr hmin

/-- Lower bounds for the pair-volume on the two parts of a partition may be
summed without losing any edge. -/
lemma partition_pairWeight_le [Fintype X] (H : SetHypergraph X)
    (A B : Set H) (hdisjoint : Disjoint A B)
    (hpartition : A ∪ B = Set.univ) (a b : ℕ)
    (hA : ∀ e ∈ A, a ≤ e.1.ncard * (e.1.ncard - 1))
    (hB : ∀ e ∈ B, b ≤ e.1.ncard * (e.1.ncard - 1)) :
    A.ncard * a + B.ncard * b ≤
      ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  have hfinDisjoint : Disjoint A.toFinset B.toFinset := by
    rw [Finset.disjoint_left]
    intro e heA heB
    exact Set.disjoint_left.mp hdisjoint (Set.mem_toFinset.mp heA)
      (Set.mem_toFinset.mp heB)
  have hunion : A.toFinset ∪ B.toFinset = Finset.univ := by
    ext e
    simp only [Set.mem_toFinset, Finset.mem_union, Finset.mem_univ, iff_true]
    have he : e ∈ A ∪ B := by rw [hpartition]; simp
    exact he
  calc
    A.ncard * a + B.ncard * b =
        (∑ _e ∈ A.toFinset, a) + ∑ _e ∈ B.toFinset, b := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      simp
    _ ≤ (∑ e ∈ A.toFinset, e.1.ncard * (e.1.ncard - 1)) +
        ∑ e ∈ B.toFinset, e.1.ncard * (e.1.ncard - 1) := by
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro e he
        exact hA e (Set.mem_toFinset.mp he)
      · apply Finset.sum_le_sum
        intro e he
        exact hB e (Set.mem_toFinset.mp he)
    _ = ∑ e ∈ A.toFinset ∪ B.toFinset,
        e.1.ncard * (e.1.ncard - 1) := by
      rw [Finset.sum_union hfinDisjoint]
    _ = ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by rw [hunion]

/-- Three-part version of `partition_pairWeight_le`, used to distinguish
sub-scale, projective-scale, and super-scale edges. -/
lemma triple_partition_pairWeight_le [Fintype X] (H : SetHypergraph X)
    (A B C : Set H) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hpartition : (A ∪ B) ∪ C = Set.univ)
    (a b c : ℕ)
    (hA : ∀ e ∈ A, a ≤ e.1.ncard * (e.1.ncard - 1))
    (hB : ∀ e ∈ B, b ≤ e.1.ncard * (e.1.ncard - 1))
    (hC : ∀ e ∈ C, c ≤ e.1.ncard * (e.1.ncard - 1)) :
    A.ncard * a + B.ncard * b + C.ncard * c ≤
      ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  have hABfin : Disjoint A.toFinset B.toFinset := by
    rw [Finset.disjoint_left]
    intro e heA heB
    exact Set.disjoint_left.mp hAB (Set.mem_toFinset.mp heA)
      (Set.mem_toFinset.mp heB)
  have hABCfin : Disjoint (A.toFinset ∪ B.toFinset) C.toFinset := by
    rw [Finset.disjoint_left]
    intro e heAB heC
    rcases Finset.mem_union.mp heAB with heA | heB
    · exact Set.disjoint_left.mp hAC (Set.mem_toFinset.mp heA)
        (Set.mem_toFinset.mp heC)
    · exact Set.disjoint_left.mp hBC (Set.mem_toFinset.mp heB)
        (Set.mem_toFinset.mp heC)
  have hunion : (A.toFinset ∪ B.toFinset) ∪ C.toFinset = Finset.univ := by
    ext e
    simp only [Set.mem_toFinset, Finset.mem_union, Finset.mem_univ, iff_true]
    have he : e ∈ (A ∪ B) ∪ C := by rw [hpartition]; simp
    rcases he with (heA | heB) | heC
    · exact Or.inl (Or.inl heA)
    · exact Or.inl (Or.inr heB)
    · exact Or.inr heC
  calc
    A.ncard * a + B.ncard * b + C.ncard * c =
        (∑ _e ∈ A.toFinset, a) + (∑ _e ∈ B.toFinset, b) +
          ∑ _e ∈ C.toFinset, c := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card',
        Set.ncard_eq_toFinset_card']
      simp
    _ ≤ (∑ e ∈ A.toFinset, e.1.ncard * (e.1.ncard - 1)) +
        (∑ e ∈ B.toFinset, e.1.ncard * (e.1.ncard - 1)) +
          ∑ e ∈ C.toFinset, e.1.ncard * (e.1.ncard - 1) := by
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · apply Finset.sum_le_sum
          intro e he
          exact hA e (Set.mem_toFinset.mp he)
        · apply Finset.sum_le_sum
          intro e he
          exact hB e (Set.mem_toFinset.mp he)
      · apply Finset.sum_le_sum
        intro e he
        exact hC e (Set.mem_toFinset.mp he)
    _ = ∑ e ∈ (A.toFinset ∪ B.toFinset) ∪ C.toFinset,
        e.1.ncard * (e.1.ncard - 1) := by
      rw [Finset.sum_union hABCfin, Finset.sum_union hABfin]
    _ = ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by rw [hunion]

/-- Integral volume form of (5.6): the low-volume part contributes at least
`R` per edge, the other part at least `n`, and the global pair budget then
forces the excess over `n` to be small. -/
lemma partition_surplus_le_quarter_of_pairWeights [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n R : ℕ)
    (hn : 0 < n) (hvertices : Fintype.card X = n)
    (A B : Set H) (hdisjoint : Disjoint A B)
    (hpartition : A ∪ B = Set.univ)
    (hR : R ≤ n) (hquarter : 4 * (n - R) ≤ n)
    (hA : ∀ e ∈ A, R ≤ e.1.ncard * (e.1.ncard - 1))
    (hB : ∀ e ∈ B, n ≤ e.1.ncard * (e.1.ncard - 1)) :
    A.ncard + B.ncard - n ≤ A.ncard / 4 := by
  have hweight : A.ncard * R + B.ncard * n ≤ n * (n - 1) := by
    calc
      A.ncard * R + B.ncard * n ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.partition_pairWeight_le A B hdisjoint hpartition R n hA hB
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  exact partition_surplus_le_quarter hn hR hquarter hweight

/-- The exact normalization used in (5.5)--(5.6): an edge in the high part
contributes at least `n-1` ordered-pair units, and the total budget is
`n(n-1)`. -/
lemma partition_surplus_le_quarter_of_pairWeights_pred [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n R : ℕ)
    (hn : 2 ≤ n) (hvertices : Fintype.card X = n)
    (A B : Set H) (hdisjoint : Disjoint A B)
    (hpartition : A ∪ B = Set.univ)
    (hR : R ≤ n - 1) (hquarter : 4 * (n - 1 - R) ≤ n - 1)
    (hA : ∀ e ∈ A, R ≤ e.1.ncard * (e.1.ncard - 1))
    (hB : ∀ e ∈ B, n - 1 ≤ e.1.ncard * (e.1.ncard - 1)) :
    A.ncard + B.ncard - n ≤ A.ncard / 4 := by
  have hweight : A.ncard * R + B.ncard * (n - 1) ≤ n * (n - 1) := by
    calc
      A.ncard * R + B.ncard * (n - 1) ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.partition_pairWeight_le A B hdisjoint hpartition R (n - 1) hA hB
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  exact weighted_partition_surplus_le_quarter (by omega) hR hquarter hweight

/-- Three edge-size classes, with the exact deficit-balance condition needed
to use the sub-scale class as the useful part in Proposition 5.4. -/
lemma triple_partition_surplus_le_quarter_of_pairWeights_pred [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n R K : ℕ)
    (hn : 2 ≤ n) (hvertices : Fintype.card X = n)
    (A B C : Set H) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hpartition : (A ∪ B) ∪ C = Set.univ)
    (hR : R ≤ n - 1) (hK : K ≤ n - 1)
    (hA : ∀ e ∈ A, R ≤ e.1.ncard * (e.1.ncard - 1))
    (hB : ∀ e ∈ B, K ≤ e.1.ncard * (e.1.ncard - 1))
    (hC : ∀ e ∈ C, n - 1 ≤ e.1.ncard * (e.1.ncard - 1))
    (hbalance : 4 * (A.ncard * (n - 1 - R) +
      B.ncard * (n - 1 - K)) ≤ (n - 1) * A.ncard) :
    A.ncard + B.ncard + C.ncard - n ≤ A.ncard / 4 := by
  have hweight : A.ncard * R + B.ncard * K + C.ncard * (n - 1) ≤
      n * (n - 1) := by
    calc
      A.ncard * R + B.ncard * K + C.ncard * (n - 1) ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.triple_partition_pairWeight_le A B C hAB hAC hBC hpartition
          R K (n - 1) hA hB hC
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  exact weighted_three_surplus_le_quarter (by omega) hR hK hweight hbalance

/-- The first complete branch of Lemma 5.1.  Edges are partitioned at the
projective-plane scale.  If the total number of sub-scale edges is small,
Proposition 5.5 makes every intersecting pair in the lower part useful, while
the pair-volume budget gives the one-quarter surplus condition required by
Proposition 5.4. -/
theorem edgeColorable_of_few_subscale_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r q : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : q * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hsmall : ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard ≤ q)
    (hR : r * (r - 1) ≤ n - 1)
    (hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1) :
    H.EdgeColorable n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let A : Set H := {e | e.1.ncard ≤ projectiveScale n}
  let B : Set H := Aᶜ
  have hdisjoint : Disjoint A B := by
    dsimp only [B]
    exact disjoint_compl_right
  have hpartition : A ∪ B = Set.univ := by simp [B]
  have hAweight : ∀ e ∈ A,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hBweight : ∀ e ∈ B,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e heB
    have hek : projectiveScale n + 1 ≤ e.1.ncard := by
      dsimp only [B, A] at heB
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at heB
      omega
    have hscale : n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := by
      have hupper := le_projectiveScale_sq_add n
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := hscale
      _ = (projectiveScale n + 1) * projectiveScale n := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hsurplus : A.ncard + B.ncard - n ≤ A.ncard / 4 :=
    H.partition_surplus_le_quarter_of_pairWeights_pred hlinear n
      (r * (r - 1)) (by omega) hvertices A B hdisjoint hpartition
      hR hquarter hAweight hBweight
  have huseful : ∀ {e : H}, e ∈ A → ∀ {f : H}, f ∈ A →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f := by
    intro e heA f hfA hef hinter
    have hek : e.1.ncard ≤ projectiveScale n := heA
    have hfk : f.1.ncard ≤ projectiveScale n := hfA
    obtain ⟨w, hwe, hwf⟩ := hinter
    by_cases heSmall : e.1.ncard ≤ projectiveScale n - 1
    · exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
        hvertices hr hrhalf hmin e f hef w hwe hwf hek hfk (Or.inl heSmall)
    by_cases hfSmall : f.1.ncard ≤ projectiveScale n - 1
    · exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
        hvertices hr hrhalf hmin e f hef w hwe hwf hek hfk (Or.inr hfSmall)
    have heeq : e.1.ncard = projectiveScale n := by omega
    have hfeq : f.1.ncard = projectiveScale n := by omega
    have hlocal :
        (H.smallIncidentEdges w (projectiveScale n)).ncard ≤ q := by
      apply (Set.ncard_le_ncard (t :=
        ({g : H | g.1.ncard < projectiveScale n} : Set H))
        (fun _g hg ↦ hg.2) (Set.toFinite _)).trans
      exact hsmall
    exact H.isUseful_of_few_small_incident_below_projectiveScale hlinear n r q
      hn hvertices (by omega) hrscale hmin hdefect e f hef w hwe hwf
      heeq hfeq hlocal
  exact H.edgeColorable_of_useful_partition (by omega) A B hdisjoint
    hpartition hsurplus huseful

/-- The second complete branch of Lemma 5.1.  Here the strictly sub-scale
class itself is used as the useful part of Proposition 5.4.  The displayed
balance hypothesis is the exact integral content of the paper's estimate
following (5.8). -/
theorem edgeColorable_of_subscale_volume_balance [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hR : r * (r - 1) ≤ n - 1)
    (hbalance : 4 *
      (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
          (n - 1 - r * (r - 1)) +
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
          (n - 1 - projectiveScale n * (projectiveScale n - 1))) ≤
      (n - 1) *
        ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard) :
    H.EdgeColorable n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let Aminus : Set H := {e | e.1.ncard < projectiveScale n}
  let Aplus : Set H := {e | e.1.ncard = projectiveScale n}
  let Bbig : Set H := {e | projectiveScale n < e.1.ncard}
  let Rest : Set H := Aplus ∪ Bbig
  have hmp : Disjoint Aminus Aplus := by
    rw [Set.disjoint_left]
    intro e heminus heplus
    change e.1.ncard < projectiveScale n at heminus
    change e.1.ncard = projectiveScale n at heplus
    omega
  have hmb : Disjoint Aminus Bbig := by
    rw [Set.disjoint_left]
    intro e heminus hebig
    change e.1.ncard < projectiveScale n at heminus
    change projectiveScale n < e.1.ncard at hebig
    omega
  have hpb : Disjoint Aplus Bbig := by
    rw [Set.disjoint_left]
    intro e heplus hebig
    change e.1.ncard = projectiveScale n at heplus
    change projectiveScale n < e.1.ncard at hebig
    omega
  have hthree : (Aminus ∪ Aplus) ∪ Bbig = Set.univ := by
    ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change (e.1.ncard < projectiveScale n ∨
      e.1.ncard = projectiveScale n) ∨ projectiveScale n < e.1.ncard
    omega
  have hAminusWeight : ∀ e ∈ Aminus,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hAplusWeight : ∀ e ∈ Aplus,
      projectiveScale n * (projectiveScale n - 1) ≤
        e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    change e.1.ncard = projectiveScale n at he
    rw [he]
  have hBbigWeight : ∀ e ∈ Bbig,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    have hek : projectiveScale n + 1 ≤ e.1.ncard := by
      change projectiveScale n < e.1.ncard at he
      omega
    have hscale : n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := by
      have hupper := le_projectiveScale_sq_add n
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := hscale
      _ = (projectiveScale n + 1) * projectiveScale n := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hK : projectiveScale n * (projectiveScale n - 1) ≤ n - 1 := by
    have hpred := projectiveScale_pred_sq_add_le (n := n) (by omega)
    have hk : 1 ≤ projectiveScale n := by
      have := two_le_projectiveScale hn
      omega
    have hid : projectiveScale n * (projectiveScale n - 1) =
        (projectiveScale n - 1) * (projectiveScale n - 1) +
          (projectiveScale n - 1) := by
      let j := projectiveScale n - 1
      have hkj : projectiveScale n = j + 1 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hsurplus :
      Aminus.ncard + Aplus.ncard + Bbig.ncard - n ≤ Aminus.ncard / 4 := by
    apply H.triple_partition_surplus_le_quarter_of_pairWeights_pred hlinear n
      (r * (r - 1)) (projectiveScale n * (projectiveScale n - 1))
      (by omega) hvertices Aminus Aplus Bbig hmp hmb hpb hthree hR hK
      hAminusWeight hAplusWeight hBbigWeight
    simpa only [Aminus, Aplus] using hbalance
  have hrestDisjoint : Disjoint Aminus Rest := by
    rw [Set.disjoint_left]
    intro e heminus herest
    rcases herest with heplus | hebig
    · exact Set.disjoint_left.mp hmp heminus heplus
    · exact Set.disjoint_left.mp hmb heminus hebig
  have hrestPartition : Aminus ∪ Rest = Set.univ := by
    dsimp only [Rest]
    rw [← Set.union_assoc]
    exact hthree
  have hRestCard : Rest.ncard = Aplus.ncard + Bbig.ncard := by
    dsimp only [Rest]
    exact Set.ncard_union_eq hpb
  have hsurplus' : Aminus.ncard + Rest.ncard - n ≤ Aminus.ncard / 4 := by
    rw [hRestCard]
    simpa only [Nat.add_assoc] using hsurplus
  have huseful : ∀ {e : H}, e ∈ Aminus → ∀ {f : H}, f ∈ Aminus →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f := by
    intro e he f hf hef hinter
    obtain ⟨w, hwe, hwf⟩ := hinter
    have heSmall : e.1.ncard ≤ projectiveScale n - 1 := by
      change e.1.ncard < projectiveScale n at he
      omega
    have hfSmall : f.1.ncard ≤ projectiveScale n - 1 := by
      change f.1.ncard < projectiveScale n at hf
      omega
    exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
      hvertices hr hrhalf hmin e f hef w hwe hwf
      (heSmall.trans (Nat.sub_le _ _)) (hfSmall.trans (Nat.sub_le _ _))
      (Or.inl heSmall)
  exact H.edgeColorable_of_useful_partition (by omega) Aminus Rest
    hrestDisjoint hrestPartition hsurplus' huseful

/-- The common three-way wrapper behind the integral versions of Lemma 5.1.
The last argument is a purely numerical certificate for the difficult branch;
all hypergraph incidence and matching work is discharged here. -/
theorem edgeColorable_of_projectiveScale_threeway [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hR : r * (r - 1) ≤ n - 1)
    (hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1)
    (hs : 0 < s)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : ∀ t,
      Fintype.card H = n + t →
      ¬({e : H | e.1.ncard < projectiveScale n} : Set H).ncard ≤ qSmall →
      ¬4 *
          (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - r * (r - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - projectiveScale n * (projectiveScale n - 1))) ≤
        (n - 1) *
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard →
      (n - 1) * t ≤
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - r * (r - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - projectiveScale n * (projectiveScale n - 1)) →
      n <
        (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            ((({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
                  (projectiveScale n - 1) / (qSmall + 1)) *
                ((n - 1) / (projectiveScale n - 1)) / s) -
            4 * (t - 1)) * qOutside) :
    H.EdgeColorable n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let k := projectiveScale n
  let Aminus : Set H := {e | e.1.ncard < k}
  let Aplus : Set H := {e | e.1.ncard = k}
  let Bbig : Set H := {e | k < e.1.ncard}
  by_cases hsmallCard : Fintype.card H ≤ n
  · exact H.edgeColorable_of_compression (fun e : H ↦ e)
      (fun {_e _f} hef heq ↦ (hef heq).elim) (by simpa using hsmallCard)
  by_cases hfew : Aminus.ncard ≤ qSmall
  · apply H.edgeColorable_of_few_subscale_edges hlinear n r qSmall hn
      hvertices hr hrscale hrhalf hmin hdefect
    · simpa only [Aminus, k] using hfew
    · exact hR
    · exact hquarter
  let lossR := n - 1 - r * (r - 1)
  let lossK := n - 1 - k * (k - 1)
  by_cases hbalance :
      4 * (Aminus.ncard * lossR + Aplus.ncard * lossK) ≤
        (n - 1) * Aminus.ncard
  · apply H.edgeColorable_of_subscale_volume_balance hlinear n r hn
      hvertices hr hrhalf hmin hR
    simpa only [Aminus, Aplus, lossR, lossK, k] using hbalance
  have hmp : Disjoint Aminus Aplus := by
    rw [Set.disjoint_left]
    intro e heminus heplus
    change e.1.ncard < k at heminus
    change e.1.ncard = k at heplus
    omega
  have hmb : Disjoint Aminus Bbig := by
    rw [Set.disjoint_left]
    intro e heminus hebig
    change e.1.ncard < k at heminus
    change k < e.1.ncard at hebig
    omega
  have hpb : Disjoint Aplus Bbig := by
    rw [Set.disjoint_left]
    intro e heplus hebig
    change e.1.ncard = k at heplus
    change k < e.1.ncard at hebig
    omega
  have hpartition : (Aminus ∪ Aplus) ∪ Bbig = Set.univ := by
    ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change (e.1.ncard < k ∨ e.1.ncard = k) ∨ k < e.1.ncard
    omega
  have hAweight : ∀ e ∈ Aminus,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hPweight : ∀ e ∈ Aplus,
      k * (k - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    change e.1.ncard = k at he
    rw [he]
  have hBweight : ∀ e ∈ Bbig,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    have hek : k + 1 ≤ e.1.ncard := by
      change k < e.1.ncard at he
      omega
    have hscale : n - 1 ≤ k * (k + 1) := by
      have hupper := le_projectiveScale_sq_add n
      dsimp only [k]
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ k * (k + 1) := hscale
      _ = (k + 1) * k := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hK : k * (k - 1) ≤ n - 1 := by
    have hpred := projectiveScale_pred_sq_add_le (n := n) (by omega)
    have hid : k * (k - 1) = (k - 1) * (k - 1) + (k - 1) := by
      have hkpos : 0 < k := by
        dsimp only [k]
        exact projectiveScale_pos (by omega)
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    simpa only [k] using (show
      (projectiveScale n - 1) * (projectiveScale n - 1) +
        (projectiveScale n - 1) ≤ n - 1 by omega)
  have hweight :
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤ n * (n - 1) := by
    calc
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.triple_partition_pairWeight_le Aminus Aplus Bbig hmp hmb hpb
          hpartition (r * (r - 1)) (k * (k - 1)) (n - 1)
          hAweight hPweight hBweight
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  have hpartsCard : Fintype.card H =
      Aminus.ncard + Aplus.ncard + Bbig.ncard := by
    have hab : (Aminus ∪ Aplus).ncard = Aminus.ncard + Aplus.ncard :=
      Set.ncard_union_eq hmp
    have habb : Disjoint (Aminus ∪ Aplus) Bbig := by
      rw [Set.disjoint_left]
      intro e heab heb
      rcases heab with hea | hep
      · exact Set.disjoint_left.mp hmb hea heb
      · exact Set.disjoint_left.mp hpb hep heb
    calc
      Fintype.card H = (Set.univ : Set H).ncard := by simp
      _ = ((Aminus ∪ Aplus) ∪ Bbig).ncard := by rw [hpartition]
      _ = (Aminus ∪ Aplus).ncard + Bbig.ncard := Set.ncard_union_eq habb
      _ = Aminus.ncard + Aplus.ncard + Bbig.ncard := by rw [hab]
  let t := Fintype.card H - n
  have hcard : Fintype.card H = n + t := by dsimp only [t]; omega
  have hsurplus : (n - 1) * t ≤
      Aminus.ncard * lossR + Aplus.ncard * lossK := by
    have h := weighted_three_surplus_mul_le hR hK hweight
    rw [← hpartsCard] at h
    simpa only [t, lossR, lossK] using h
  have hdensity' : n <
      (Aplus.ncard -
          ((Aminus.ncard * (k - 1) / (qSmall + 1)) *
              ((n - 1) / (k - 1)) / s) -
          4 * (t - 1)) * qOutside := by
    apply hdensity t hcard
    · simpa only [Aminus, k] using hfew
    · simpa only [Aminus, Aplus, lossR, lossK, k] using hbalance
    · simpa only [Aminus, Aplus, lossR, lossK, k] using hsurplus
  apply H.edgeColorable_of_projectiveScale_claim_of_floor_density hlinear
    n r qSmall s qOutside t hn hvertices (by omega) hrscale hmin hdefect
    hcard hs houtside
  simpa only [Aminus, Aplus, k] using hdensity'

/-- A complete integral version of Lemma 5.1 in the near-projective-scale
regime.  For `k = projectiveScale n`, every sufficiently large linear
`n`-vertex hypergraph whose edges all have size at least `k-1` is
`n`-edge-colorable.  The proof performs the paper's three-way split: few
sub-scale edges, the volume-balance branch, and the bad/heavy incidence
branch. -/
theorem edgeColorable_of_near_projectiveScale_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n : ℕ)
    (hvertices : Fintype.card X = n)
    (hk : 4096 ≤ projectiveScale n)
    (hmin : ∀ e : H, projectiveScale n - 1 ≤ e.1.ncard) :
    H.EdgeColorable n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let k := projectiveScale n
  let r := k - 1
  let qSmall := k - 2
  let s := k / 4
  let qOutside := k + 1 - s
  let Aminus : Set H := {e | e.1.ncard < k}
  let Aplus : Set H := {e | e.1.ncard = k}
  let Bbig : Set H := {e | k < e.1.ncard}
  have hn2 : 2 ≤ n := by
    by_contra hnnot
    have htest : n ≤ 1 * 1 + 1 + 1 := by omega
    have hscale_le : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) htest
    omega
  have hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n := by
    simpa only [k] using projectiveScale_pred_sq_add_le (n := n) hn2
  have hup : n ≤ k * k + k + 1 := by
    simpa only [k] using le_projectiveScale_sq_add n
  have hn : 4 ≤ n := by
    have hk' : 4096 ≤ k := by simpa only [k] using hk
    have : 2 ≤ k := by omega
    have hsq : 4 ≤ (k - 1) * (k - 1) + (k - 1) + 2 := by
      have hj : 1 ≤ k - 1 := by omega
      have hmul : 1 * 1 ≤ (k - 1) * (k - 1) := Nat.mul_le_mul hj hj
      norm_num at hmul
      omega
    exact hsq.trans hlow
  have hk' : 4096 ≤ k := by simpa only [k] using hk
  have hr : 2 ≤ r := by dsimp only [r]; omega
  have hrscale : r ≤ projectiveScale n := by dsimp only [r, k]; omega
  have hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1) := by
    dsimp only [r, k]
    omega
  have hmin' : ∀ e : H, r ≤ e.1.ncard := by
    intro e
    simpa only [r, k] using hmin e
  have hrpred : r - 1 = k - 2 := by
    dsimp only [r]
    omega
  have hqsucc : qSmall + 1 = k - 1 := by
    dsimp only [qSmall]
    omega
  have hdefect : qSmall * (projectiveScale n - r) ≤
      projectiveScale n - 2 := by
    dsimp only [qSmall, r, k]
    have hkpos : 0 < projectiveScale n := by omega
    have hdiff : projectiveScale n - (projectiveScale n - 1) = 1 := by omega
    rw [hdiff]
    simp
  have hR : r * (r - 1) ≤ n - 1 := by
    rw [hrpred]
    dsimp only [r]
    have hprod : (k - 1) * (k - 2) ≤ (k - 1) * (k - 1) :=
      Nat.mul_le_mul_left (k - 1) (by omega)
    omega
  have hlossR : n - 1 - r * (r - 1) ≤ 4 * k := by
    rw [hrpred]
    dsimp only [r]
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : (k - 1) * (k - 2) + (4 * k - 2) = k * k + k := by
      let j := k - 2
      have hkj : k = j + 2 := by dsimp only [j]; omega
      rw [hkj]
      have hj1 : j + 2 - 1 = j + 1 := by omega
      have hj2 : j + 2 - 2 = j := by omega
      have hsub : 4 * (j + 2) - 2 = 4 * j + 6 := by omega
      rw [hj1, hj2, hsub]
      ring
    omega
  have hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1 := by
    have h16k : 16 * k ≤ n - 1 := by
      have h16 : 16 ≤ k - 1 := by omega
      have hmul : 16 * k ≤ k * (k - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h16
      have hK : k * (k - 1) ≤ n - 1 := by
        have hid : k * (k - 1) =
            (k - 1) * (k - 1) + (k - 1) := by
          let j := k - 1
          have hkj : k = j + 1 := by dsimp only [j]; omega
          rw [hkj]
          have hj : j + 1 - 1 = j := by omega
          rw [hj]
          ring
        rw [hid]
        omega
      exact hmul.trans hK
    calc
      4 * (n - 1 - r * (r - 1)) ≤ 4 * (4 * k) :=
        Nat.mul_le_mul_left 4 hlossR
      _ = 16 * k := by ring
      _ ≤ n - 1 := h16k
  by_cases hsmallCard : Fintype.card H ≤ n
  · exact H.edgeColorable_of_compression (fun e : H ↦ e)
      (fun {_e _f} hef heq ↦ (hef heq).elim) (by simpa using hsmallCard)
  by_cases hfew : Aminus.ncard ≤ qSmall
  · apply H.edgeColorable_of_few_subscale_edges hlinear n r qSmall hn
      hvertices hr hrscale hrhalf hmin' hdefect
    · simpa only [Aminus, k] using hfew
    · exact hR
    · exact hquarter
  let lossR := n - 1 - r * (r - 1)
  let lossK := n - 1 - k * (k - 1)
  by_cases hbalance :
      4 * (Aminus.ncard * lossR + Aplus.ncard * lossK) ≤
        (n - 1) * Aminus.ncard
  · apply H.edgeColorable_of_subscale_volume_balance hlinear n r hn
      hvertices hr hrhalf hmin' hR
    simpa only [Aminus, Aplus, lossR, lossK, k] using hbalance
  have hmp : Disjoint Aminus Aplus := by
    rw [Set.disjoint_left]
    intro e heminus heplus
    change e.1.ncard < k at heminus
    change e.1.ncard = k at heplus
    omega
  have hmb : Disjoint Aminus Bbig := by
    rw [Set.disjoint_left]
    intro e heminus hebig
    change e.1.ncard < k at heminus
    change k < e.1.ncard at hebig
    omega
  have hpb : Disjoint Aplus Bbig := by
    rw [Set.disjoint_left]
    intro e heplus hebig
    change e.1.ncard = k at heplus
    change k < e.1.ncard at hebig
    omega
  have hpartition : (Aminus ∪ Aplus) ∪ Bbig = Set.univ := by
    ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change (e.1.ncard < k ∨ e.1.ncard = k) ∨ k < e.1.ncard
    omega
  have hAweight : ∀ e ∈ Aminus,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin' e) (Nat.sub_le_sub_right (hmin' e) 1)
  have hPweight : ∀ e ∈ Aplus,
      k * (k - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    change e.1.ncard = k at he
    rw [he]
  have hBweight : ∀ e ∈ Bbig,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    have hek : k + 1 ≤ e.1.ncard := by
      change k < e.1.ncard at he
      omega
    have hscale : n - 1 ≤ k * (k + 1) := by
      have hpoly : n - 1 ≤ k * k + k := by omega
      calc
        n - 1 ≤ k * k + k := hpoly
        _ = k * (k + 1) := by ring
    calc
      n - 1 ≤ k * (k + 1) := hscale
      _ = (k + 1) * k := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hK : k * (k - 1) ≤ n - 1 := by
    have hid : k * (k - 1) =
        (k - 1) * (k - 1) + (k - 1) := by
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hweight :
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤ n * (n - 1) := by
    calc
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.triple_partition_pairWeight_le Aminus Aplus Bbig hmp hmb hpb
          hpartition (r * (r - 1)) (k * (k - 1)) (n - 1)
          hAweight hPweight hBweight
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  have hpartsCard : Fintype.card H =
      Aminus.ncard + Aplus.ncard + Bbig.ncard := by
    have hab : (Aminus ∪ Aplus).ncard = Aminus.ncard + Aplus.ncard :=
      Set.ncard_union_eq hmp
    have habb : Disjoint (Aminus ∪ Aplus) Bbig := by
      rw [Set.disjoint_left]
      intro e heab heb
      rcases heab with hea | hep
      · exact Set.disjoint_left.mp hmb hea heb
      · exact Set.disjoint_left.mp hpb hep heb
    calc
      Fintype.card H = (Set.univ : Set H).ncard := by simp
      _ = ((Aminus ∪ Aplus) ∪ Bbig).ncard := by rw [hpartition]
      _ = (Aminus ∪ Aplus).ncard + Bbig.ncard := Set.ncard_union_eq habb
      _ = Aminus.ncard + Aplus.ncard + Bbig.ncard := by rw [hab]
  let t := Fintype.card H - n
  have hcard : Fintype.card H = n + t := by
    dsimp only [t]
    omega
  have hsurplus : (n - 1) * t ≤
      Aminus.ncard * lossR + Aplus.ncard * lossK := by
    have h := weighted_three_surplus_mul_le hR hK hweight
    rw [← hpartsCard] at h
    simpa only [t, lossR, lossK] using h
  have ha : k - 1 ≤ Aminus.ncard := by
    dsimp only [qSmall] at hfew
    omega
  have hnotBalance : (n - 1) * Aminus.ncard <
      4 * (Aminus.ncard * lossR + Aplus.ncard * lossK) := by
    omega
  have hdensity := near_projectiveScale_floor_density hk' hlow hup ha
    hnotBalance hsurplus
  apply H.edgeColorable_of_projectiveScale_claim_of_floor_density hlinear
    n r qSmall s qOutside t hn hvertices (by omega) hrscale hmin'
    hdefect hcard
  · dsimp only [s]
    omega
  · dsimp only [qOutside, s, k]
    omega
  · rw [hqsucc]
    simpa only [Aminus, Aplus, qOutside, s, r, k] using hdensity

/-- Lemma 5.1 with an explicit fixed relative gap.  The threshold
`k - k / 1024` is `(1-o(1))√n` only up to the harmless additive discrepancy
between `k` and `√n`, but unlike the preceding `k-1` version it has a genuine
constant fractional gap and is the form used by the later large-edge
decomposition. -/
theorem edgeColorable_of_fixedFraction_projectiveScale_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n : ℕ)
    (hvertices : Fintype.card X = n)
    (hk : 65536 ≤ projectiveScale n)
    (hmin : ∀ e : H,
      projectiveScale n - projectiveScale n / 1024 ≤ e.1.ncard) :
    H.EdgeColorable n := by
  let k := projectiveScale n
  let u := k / 1024
  let r := k - u
  let qSmall := 512
  let s := k / 8
  let qOutside := k + 1 - s
  have hk' : 65536 ≤ k := by simpa only [k] using hk
  have hn2 : 2 ≤ n := by
    by_contra hnnot
    have htest : n ≤ 1 * 1 + 1 + 1 := by omega
    have hscale_le : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) htest
    omega
  have hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n := by
    simpa only [k] using projectiveScale_pred_sq_add_le (n := n) hn2
  have hup : n ≤ k * k + k + 1 := by
    simpa only [k] using le_projectiveScale_sq_add n
  have hn : 4 ≤ n := by
    have hj : 1 ≤ k - 1 := by omega
    have hmul : 1 * 1 ≤ (k - 1) * (k - 1) := Nat.mul_le_mul hj hj
    norm_num at hmul
    omega
  have hu_mul : 1024 * u ≤ k := by
    dsimp only [u]
    exact Nat.mul_div_le k 1024
  have hu_le : u ≤ k := by
    have hu : u ≤ 1024 * u := by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left u (by norm_num : 1 ≤ 1024)
    exact hu.trans hu_mul
  have hku : k = r + u := by dsimp only [r]; omega
  have hr : 2 ≤ r := by
    have hu4 : 4 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 4 ≤ 1024)).trans hu_mul
    dsimp only [r]
    omega
  have hrscale : r ≤ projectiveScale n := by dsimp only [r, k]; omega
  have hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1) := by
    have hu4 : 4 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 4 ≤ 1024)).trans hu_mul
    dsimp only [r, k]
    omega
  have hmin' : ∀ e : H, r ≤ e.1.ncard := by
    intro e
    simpa only [r, u, k] using hmin e
  have hdiff : projectiveScale n - r = u := by
    dsimp only [r, k]
    omega
  have hdefect : qSmall * (projectiveScale n - r) ≤
      projectiveScale n - 2 := by
    rw [hdiff]
    have h512 : 512 * u ≤ k / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      calc
        512 * u * 2 = 1024 * u := by ring
        _ ≤ k := hu_mul
    dsimp only [qSmall, k]
    omega
  have hK : k * (k - 1) ≤ n - 1 := by
    have hid : k * (k - 1) =
        (k - 1) * (k - 1) + (k - 1) := by
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hR : r * (r - 1) ≤ n - 1 := by
    have hrk : r ≤ k := by dsimp only [r]; omega
    exact (Nat.mul_le_mul hrk (Nat.sub_le_sub_right hrk 1)).trans hK
  have hlossR : n - 1 - r * (r - 1) ≤ 2 * k * u + 2 * k := by
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * k + k + (u * u + u) =
        r * (r - 1) + (2 * k * u + 2 * k) := by
      let j := r - 1
      have hrj : r = j + 1 := by dsimp only [j]; omega
      have hkj : k = j + 1 + u := by omega
      rw [hrj, hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    have hsum : n - 1 ≤ r * (r - 1) + (2 * k * u + 2 * k) := by
      calc
        n - 1 ≤ k * k + k := hpoly
        _ ≤ k * k + k + (u * u + u) := Nat.le_add_right _ _
        _ = r * (r - 1) + (2 * k * u + 2 * k) := hid
    omega
  have hlossR32 : 32 * (n - 1 - r * (r - 1)) ≤ n - 1 := by
    have hu256 : 256 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 256 ≤ 1024)).trans hu_mul
    have h256ku : 256 * k * u ≤ k * k := by
      calc
        256 * k * u = k * (256 * u) := by ring
        _ ≤ k * k := Nat.mul_le_mul_left k hu256
    have h256k : 256 * k ≤ k * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : 256 ≤ k)
    have hfour : 4 * (64 * k * u + 64 * k) ≤ 2 * (k * k) := by
      calc
        4 * (64 * k * u + 64 * k) = 256 * k * u + 256 * k := by ring
        _ ≤ k * k + k * k := Nat.add_le_add h256ku h256k
        _ = 2 * (k * k) := by ring
    have htwo : 2 * (k * k) ≤ 4 * (k * (k - 1)) := by
      have h2k : 2 * k ≤ 4 * (k - 1) := by omega
      calc
        2 * (k * k) = k * (2 * k) := by ring
        _ ≤ k * (4 * (k - 1)) := Nat.mul_le_mul_left k h2k
        _ = 4 * (k * (k - 1)) := by ring
    have hbase : 64 * k * u + 64 * k ≤ k * (k - 1) :=
      Nat.le_of_mul_le_mul_left (hfour.trans htwo) (by norm_num : 0 < 4)
    calc
      32 * (n - 1 - r * (r - 1)) ≤ 32 * (2 * k * u + 2 * k) :=
        Nat.mul_le_mul_left 32 hlossR
      _ = 64 * k * u + 64 * k := by ring
      _ ≤ k * (k - 1) := hbase
      _ ≤ n - 1 := hK
  have hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1 := by
    have hfour32 :
        4 * (n - 1 - r * (r - 1)) ≤
          32 * (n - 1 - r * (r - 1)) := by omega
    exact hfour32.trans hlossR32
  have hs : 0 < s := by
    dsimp only [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2 (by omega)
  have houtside : qOutside + s ≤ projectiveScale n + 1 := by
    dsimp only [qOutside, s, k]
    omega
  apply H.edgeColorable_of_projectiveScale_threeway hlinear
    n r qSmall s qOutside hn hvertices hr hrscale hrhalf hmin' hdefect
    hR hquarter hs houtside
  intro t _hcard hfew hbalance hsurplus
  have ha : 513 ≤
      ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard := by
    dsimp only [qSmall] at hfew
    omega
  have hbalance' :
      (n - 1) *
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard <
        4 *
          (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - (k - k / 1024) * (k - k / 1024 - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - k * (k - 1))) := by
    simpa only [not_le, r, u, k] using hbalance
  have hdensity := fixedFraction_projectiveScale_floor_density hk' hlow hup
    ha hbalance' hsurplus
  have hq : qSmall + 1 = 513 := by rfl
  rw [hq]
  simpa only [r, u, k, s, qOutside] using hdensity

/-- A uniform lower bound `r` on the sizes of a subfamily converts the global
pair-volume estimate into a cardinality bound for that subfamily. -/
lemma ncard_mul_edgePairWeight_le [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Set H) (r : ℕ)
    (hsize : ∀ e ∈ S, r ≤ e.1.ncard) :
    S.ncard * (r * (r - 1)) ≤
      Fintype.card X * (Fintype.card X - 1) := by
  classical
  have htotal := H.sum_ncard_mul_sub_one_le hlinear
  calc
    S.ncard * (r * (r - 1)) = ∑ _e ∈ S.toFinset, r * (r - 1) := by
      rw [Set.ncard_eq_toFinset_card' S]
      simp
    _ ≤ ∑ e ∈ S.toFinset, e.1.ncard * (e.1.ncard - 1) := by
      apply Finset.sum_le_sum
      intro e he
      have her := hsize e (Set.mem_toFinset.mp he)
      exact Nat.mul_le_mul her (Nat.sub_le_sub_right her 1)
    _ ≤ ∑ e ∈ (Finset.univ : Finset H), e.1.ncard * (e.1.ncard - 1) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by simp
    _ ≤ Fintype.card X * (Fintype.card X - 1) := htotal

/-- Set-valued form of the finite peeling dichotomy. -/
theorem edgeColorable_or_dense_subfamily [Fintype X]
    (H : SetHypergraph X) {k : ℕ} (hk : 0 < k) :
    H.EdgeColorable k ∨
      ∃ W : Set H, W.Nonempty ∧
        ∀ e ∈ W, k ≤ (H.asIndexed.internalNeighborSet W e).ncard := by
  rcases H.asIndexed.edgeColorable_or_dense_subfamily hk with hcolor | hdense
  · left
    obtain ⟨c⟩ := hcolor
    exact ⟨{ color := c.color, valid := c.valid }⟩
  · exact Or.inr hdense

/-- Numerical constraint on the dense branch.  If every edge of `W` has size
at least `r` and every edge has at least `k` internal conflicts, then each
edge consumes enough of its pair budget to force
`k(r-1) ≤ |e|(|X|-|e|)`. -/
lemma dense_subfamily_pairBudget [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (W : Set H) (r k : ℕ)
    (hsize : ∀ e ∈ W, r ≤ e.1.ncard)
    (hdegree : ∀ e ∈ W,
      k ≤ (H.asIndexed.internalNeighborSet W e).ncard) :
    ∀ e ∈ W,
      k * (r - 1) ≤ e.1.ncard * (Fintype.card X - e.1.ncard) := by
  intro e he
  let S : Set H := H.asIndexed.internalNeighborSet W e
  have hsubset : S ⊆ H.neighborEdges e := by
    intro f hf
    exact ⟨hf.2.1, hf.2.2⟩
  have hweight : ∀ f ∈ S, r - 1 ≤ f.1.ncard - 1 := by
    intro f hf
    exact Nat.sub_le_sub_right (hsize f hf.1) 1
  have hpairs := H.ncard_mul_le_pairBudget hlinear e S hsubset (r - 1) hweight
  exact (Nat.mul_le_mul_right (r - 1) (hdegree e he)).trans hpairs

/-- If every edge is large enough that one edge consumes at least `|X|-1`
ordered-pair units, then the global pair budget permits at most `|X|` edges.
Giving every edge its own color proves the exact `|X|` bound in this large-edge
regime. -/
theorem edgeColorable_of_large_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (hn : 2 ≤ Fintype.card X) (r : ℕ)
    (hsize : ∀ e : H, r ≤ e.1.ncard)
    (hr : Fintype.card X - 1 ≤ r * (r - 1)) :
    H.EdgeColorable (Fintype.card X) := by
  classical
  have hpairs := H.ncard_mul_edgePairWeight_le hlinear (Set.univ : Set H) r
    (fun e _ ↦ hsize e)
  have hfactor : 0 < Fintype.card X - 1 := by omega
  have hmul :
      Fintype.card H * (Fintype.card X - 1) ≤
        Fintype.card X * (Fintype.card X - 1) := by
    calc
      Fintype.card H * (Fintype.card X - 1) ≤
          Fintype.card H * (r * (r - 1)) := Nat.mul_le_mul_left _ hr
      _ = (Set.univ : Set H).ncard * (r * (r - 1)) := by simp
      _ ≤ Fintype.card X * (Fintype.card X - 1) := hpairs
  have hcard : Fintype.card H ≤ Fintype.card (Fin (Fintype.card X)) := by
    rw [Fintype.card_fin]
    exact Nat.le_of_mul_le_mul_right hmul hfactor
  obtain ⟨embedding : H ↪ Fin (Fintype.card X)⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  refine ⟨{ color := embedding, valid := ?_ }⟩
  intro e f hef _ hsame
  exact hef (embedding.injective hsame)

/-- A coloring of the size-at-least-two core with `|X|` colors extends over
all singleton and empty edges.  A singleton `{x}` leaves a free color because
its presence makes the nontrivial incident family at `x` strictly smaller than
`|X|`; distinct singleton edges never conflict. -/
theorem edgeColorable_of_nontrivialEdges [Fintype X] [Nonempty X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (hcore : H.nontrivialEdges.EdgeColorable (Fintype.card X)) :
    H.EdgeColorable (Fintype.card X) := by
  classical
  obtain ⟨c⟩ := hcore
  let fallback : Fin (Fintype.card X) := ⟨0, Fintype.card_pos⟩
  let coreColor (e : H) : Fin (Fintype.card X) :=
    if he : 2 ≤ e.1.ncard then c ⟨e.1, e.2, he⟩ else fallback
  let used (x : X) : Finset (Fin (Fintype.card X)) :=
    (H.nontrivialIncidentEdges x).toFinset.image coreColor
  have used_card_lt (x : X) (hx : ({x} : Set X) ∈ H) :
      (used x).card < Fintype.card X := by
    calc
      (used x).card ≤ (H.nontrivialIncidentEdges x).toFinset.card :=
        Finset.card_image_le
      _ = (H.nontrivialIncidentEdges x).ncard := by
        rw [Set.ncard_eq_toFinset_card']
      _ < Fintype.card X := H.nontrivialIncidentEdges_ncard_lt hlinear x hx
  let singletonColor (x : X) : Fin (Fintype.card X) :=
    if hx : ({x} : Set X) ∈ H then
      Classical.choose (Finset.exists_mem_notMem_of_card_lt_card
        (s := used x) (t := Finset.univ) (by simpa using used_card_lt x hx))
    else fallback
  have singletonColor_not_used (x : X) (hx : ({x} : Set X) ∈ H) :
      singletonColor x ∉ used x := by
    simp only [singletonColor, dif_pos hx]
    exact (Classical.choose_spec (Finset.exists_mem_notMem_of_card_lt_card
      (s := used x) (t := Finset.univ) (by simpa using used_card_lt x hx))).2
  let finalColor (e : H) : Fin (Fintype.card X) :=
    if he : 2 ≤ e.1.ncard then coreColor e
    else if hne : e.1.Nonempty then singletonColor (Classical.choose hne)
    else fallback
  have finalColor_of_nontrivial (e : H) (he : 2 ≤ e.1.ncard) :
      finalColor e = c ⟨e.1, e.2, he⟩ := by
    simp [finalColor, coreColor, he]
  have subsingleton_of_not_nontrivial (e : H) (he : ¬2 ≤ e.1.ncard) :
      e.1.Subsingleton := by
    apply Set.ncard_le_one_iff_subsingleton.mp
    omega
  refine ⟨{ color := finalColor, valid := ?_ }⟩
  intro e f hef hinter
  obtain ⟨x, hxe, hxf⟩ := hinter
  by_cases he : 2 ≤ e.1.ncard
  · by_cases hf : 2 ≤ f.1.ncard
    · rw [finalColor_of_nontrivial e he, finalColor_of_nontrivial f hf]
      apply c.valid
      · intro hcoreeq
        apply hef
        apply Subtype.ext
        exact congrArg (fun z : H.nontrivialEdges ↦ z.1) hcoreeq
      · exact ⟨x, hxe, hxf⟩
    · have hfnonempty : f.1.Nonempty := ⟨x, hxf⟩
      have hfsub := subsingleton_of_not_nontrivial f hf
      have hchoice : Classical.choose hfnonempty = x :=
        hfsub (Classical.choose_spec hfnonempty) hxf
      have hfset : f.1 = {x} := by
        ext y
        constructor
        · intro hy
          have : y = x := hfsub hy hxf
          simpa [this]
        · intro hy
          have : y = x := by simpa using hy
          simpa [this] using hxf
      have hxsingleton : ({x} : Set X) ∈ H := by
        rw [← hfset]
        exact f.2
      have heIncident : e ∈ H.nontrivialIncidentEdges x := ⟨he, hxe⟩
      have heUsed : coreColor e ∈ used x := by
        exact Finset.mem_image.mpr ⟨e, Set.mem_toFinset.mpr heIncident, rfl⟩
      have hcolors : coreColor e ≠ singletonColor x := by
        intro hsame
        exact singletonColor_not_used x hxsingleton (hsame ▸ heUsed)
      rw [show finalColor e = coreColor e by simp [finalColor, he]]
      rw [show finalColor f = singletonColor x by
        simp [finalColor, hf, hfnonempty, hchoice]]
      exact hcolors
  · by_cases hf : 2 ≤ f.1.ncard
    · have henonempty : e.1.Nonempty := ⟨x, hxe⟩
      have hesum := subsingleton_of_not_nontrivial e he
      have hchoice : Classical.choose henonempty = x :=
        hesum (Classical.choose_spec henonempty) hxe
      have heset : e.1 = {x} := by
        ext y
        constructor
        · intro hy
          have : y = x := hesum hy hxe
          simpa [this]
        · intro hy
          have : y = x := by simpa using hy
          simpa [this] using hxe
      have hxsingleton : ({x} : Set X) ∈ H := by
        rw [← heset]
        exact e.2
      have hfIncident : f ∈ H.nontrivialIncidentEdges x := ⟨hf, hxf⟩
      have hfUsed : coreColor f ∈ used x := by
        exact Finset.mem_image.mpr ⟨f, Set.mem_toFinset.mpr hfIncident, rfl⟩
      have hcolors : singletonColor x ≠ coreColor f := by
        intro hsame
        exact singletonColor_not_used x hxsingleton (hsame.symm ▸ hfUsed)
      rw [show finalColor e = singletonColor x by
        simp [finalColor, he, henonempty, hchoice]]
      rw [show finalColor f = coreColor f by simp [finalColor, hf]]
      exact hcolors
    · have hesub := subsingleton_of_not_nontrivial e he
      have hfsub := subsingleton_of_not_nontrivial f hf
      exfalso
      apply hef
      apply Subtype.ext
      ext y
      constructor
      · intro hy
        have hyx : y = x := hesub hy hxe
        exact hyx ▸ hxf
      · intro hy
        have hyx : y = x := hfsub hy hxf
        exact hyx ▸ hxe

/-- The elementary `2|V|+1` bound mentioned after Proposition 6.3.  It is not
the final KKKMO theorem, but it kernel-checks the complete chain from pair
counting, through decreasing-size reordering, to ordered greedy coloring. -/
theorem edgeColorable_two_mul_card_add_one [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) :
    H.EdgeColorable (2 * Fintype.card X + 1) := by
  classical
  obtain ⟨rank, hrank, horder⟩ := H.exists_rank_ordered_by_ncard
  have hbound : ∀ e : H,
      (H.asIndexed.earlierNeighborSet rank e).ncard <
        2 * Fintype.card X + 1 := by
    intro e
    have hle := H.earlierNeighborEdges_ncard_le_two_mul hlinear rank horder e (hmin e)
    change (H.earlierNeighborEdges rank e).ncard < 2 * Fintype.card X + 1
    omega
  obtain ⟨c⟩ := H.asIndexed.edgeColorable_of_earlierNeighbor_ncard_lt
    (Nat.succ_pos _) rank hrank hbound
  exact ⟨{ color := c.color, valid := c.valid }⟩

/-- The quotient-sharp greedy corollary stated after Proposition 6.3.  When
all edges have size at least `r ≥ 2`, decreasing-size greedy coloring uses at
most `|X| + ⌊|X|/(r-1)⌋ + 1` colors. -/
theorem edgeColorable_card_add_div_add_one [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (r : ℕ) (hr : 2 ≤ r) (hmin : ∀ e : H, r ≤ e.1.ncard) :
    H.EdgeColorable
      (Fintype.card X + Fintype.card X / (r - 1) + 1) := by
  classical
  obtain ⟨rank, hrank, horder⟩ := H.exists_rank_ordered_by_ncard
  have hbound : ∀ e : H,
      (H.asIndexed.earlierNeighborSet rank e).ncard <
        Fintype.card X + Fintype.card X / (r - 1) + 1 := by
    intro e
    have hle := H.earlierNeighborEdges_ncard_le_card_add_div
      hlinear rank horder r hr hmin e
    change (H.earlierNeighborEdges rank e).ncard <
      Fintype.card X + Fintype.card X / (r - 1) + 1
    omega
  obtain ⟨c⟩ := H.asIndexed.edgeColorable_of_earlierNeighbor_ncard_lt
    (Nat.succ_pos _) rank hrank hbound
  exact ⟨{ color := c.color, valid := c.valid }⟩

/-- Every linear hypergraph whose edges have size at most two is edge-colorable
with `|X|` colors.  On the size-two core, encode vertices in `ZMod |X|` and
color an edge by the sum of its endpoints; cancellation at a common endpoint
proves properness.  The preceding extension theorem restores singleton and
empty edges. -/
theorem edgeColorable_of_edge_ncard_le_two [Fintype X] [Nonempty X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (hmax : ∀ e : H, e.1.ncard ≤ 2) :
    H.EdgeColorable (Fintype.card X) := by
  classical
  let n := Fintype.card X
  letI : NeZero n := ⟨Fintype.card_ne_zero⟩
  let encode : X ≃ Fin n := Fintype.equivFin X
  let weight : X → ZMod n := fun x ↦ ZMod.finEquiv n (encode x)
  let coreColor (e : H.nontrivialEdges) : Fin n :=
    (ZMod.finEquiv n).symm (∑ x ∈ e.1.toFinset, weight x)
  have hcore : H.nontrivialEdges.EdgeColorable n := by
    refine ⟨{ color := coreColor, valid := ?_ }⟩
    intro e f hef hinter hsame
    obtain ⟨x, hxe, hxf⟩ := hinter
    have hecard : e.1.ncard = 2 :=
      le_antisymm (hmax ⟨e.1, e.2.1⟩) e.2.2
    have hfcard : f.1.ncard = 2 :=
      le_antisymm (hmax ⟨f.1, f.2.1⟩) f.2.2
    have hxeft : x ∈ e.1.toFinset := Set.mem_toFinset.mpr hxe
    have hxfft : x ∈ f.1.toFinset := Set.mem_toFinset.mpr hxf
    have heerase : (e.1.toFinset.erase x).card = 1 := by
      rw [Finset.card_erase_of_mem hxeft]
      rw [← Set.ncard_eq_toFinset_card' e.1, hecard]
    have hferase : (f.1.toFinset.erase x).card = 1 := by
      rw [Finset.card_erase_of_mem hxfft]
      rw [← Set.ncard_eq_toFinset_card' f.1, hfcard]
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp heerase
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hferase
    have hsums : (∑ a ∈ e.1.toFinset, weight a) =
        ∑ a ∈ f.1.toFinset, weight a := by
      exact (ZMod.finEquiv n).symm.injective hsame
    have heraseSums : (∑ a ∈ e.1.toFinset.erase x, weight a) =
        ∑ a ∈ f.1.toFinset.erase x, weight a := by
      rw [← e.1.toFinset.sum_erase_add weight hxeft,
        ← f.1.toFinset.sum_erase_add weight hxfft] at hsums
      exact add_right_cancel hsums
    rw [hy, hz] at heraseSums
    simp only [Finset.sum_singleton] at heraseSums
    have hyz : y = z := by
      apply encode.injective
      apply (ZMod.finEquiv n).injective
      exact heraseSums
    apply hef
    apply Subtype.ext
    apply Set.toFinset_inj.mp
    calc
      e.1.toFinset = insert x (e.1.toFinset.erase x) :=
        (Finset.insert_erase hxeft).symm
      _ = insert x (f.1.toFinset.erase x) := by rw [hy, hz, hyz]
      _ = f.1.toFinset := Finset.insert_erase hxfft
  simpa [n] using H.edgeColorable_of_nontrivialEdges hlinear hcore

/-- The chromatic index is the least palette size admitting a proper edge
coloring. -/
noncomputable def chromaticIndex (H : SetHypergraph X) : ℕ :=
  sInf {k : ℕ | H.EdgeColorable k}

/-- A finite set-valued hypergraph can always color every edge with its own
color. -/
lemma edgeColorable_some [Fintype X] (H : SetHypergraph X) :
    ∃ k : ℕ, H.EdgeColorable k := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  refine ⟨Fintype.card H, ⟨{ color := Fintype.equivFin H, valid := ?_ }⟩⟩
  intro e f hef _ hsame
  exact hef ((Fintype.equivFin H).injective hsame)

/-- On a finite vertex type the minimum in `chromaticIndex` is attained, and
`chromaticIndex ≤ n` is equivalent to an explicit `Fin n` coloring. -/
lemma chromaticIndex_le_iff_edgeColorable [Fintype X] (H : SetHypergraph X) (n : ℕ) :
    H.chromaticIndex ≤ n ↔ H.EdgeColorable n := by
  classical
  obtain ⟨k, hk⟩ := H.edgeColorable_some
  have hnonempty : ({k : ℕ | H.EdgeColorable k} : Set ℕ).Nonempty := ⟨k, hk⟩
  constructor
  · intro hle
    have hmin : H.EdgeColorable H.chromaticIndex := by
      exact Nat.sInf_mem hnonempty
    obtain ⟨c⟩ := hmin
    refine ⟨{ color := fun e ↦ Fin.castLE hle (c e), valid := ?_ }⟩
    intro e f hef hinter hsame
    exact c.valid hef hinter (Fin.castLE_injective hle hsame)
  · intro hcolor
    exact Nat.sInf_le hcolor

end SetHypergraph

namespace IndexedHypergraph

variable {X : Type u} {E : Type*}

/-- Forget the labels on the edges of an indexed hypergraph. -/
def toSetHypergraph (H : IndexedHypergraph X E) : SetHypergraph X :=
  Set.range H.edge

/-- Forgetting edge labels preserves linearity. -/
lemma toSetHypergraph_isLinear {H : IndexedHypergraph X E} (hH : H.IsLinear) :
    H.toSetHypergraph.IsLinear := by
  rintro _ ⟨e, rfl⟩ _ ⟨f, rfl⟩ hef
  by_cases h : e = f
  · subst f
    exact (hef rfl).elim
  · exact hH h

/-- For a positive palette size, a coloring after forgetting edge labels can
be lifted back to the indexed hypergraph provided its labeled degrees are
bounded by the palette size.  Repeated nonsingleton edges are excluded by
linearity.  At each vertex, the colors of nonsingleton edges form a partial
injection; `exists_injective_extension` assigns the remaining colors to all
singleton copies.  Empty edges may all receive an arbitrary color because
they meet no edge. -/
theorem edgeColorable_of_toSetHypergraph_edgeColorable {n : ℕ} [Fintype E]
    (H : IndexedHypergraph (Fin n) E) (hn : 0 < n) (hlinear : H.IsLinear)
    (hdegree : H.DegreeLE n) (hset : H.toSetHypergraph.EdgeColorable n) :
    H.EdgeColorable n := by
  classical
  obtain ⟨c⟩ := hset
  let Incident (x : Fin n) := {e : E // x ∈ H.edge e}
  have hlocal : ∀ x : Fin n,
      ∃ g : Incident x → Fin n, Function.Injective g ∧
        ∀ a (ha : ¬(H.edge a.1).Subsingleton),
          g a = c ⟨H.edge a.1, ⟨a.1, rfl⟩⟩ := by
    intro x
    let p : Incident x → Prop := fun a ↦ ¬(H.edge a.1).Subsingleton
    let f : {a : Incident x // p a} → Fin n := fun a ↦
      c ⟨H.edge a.1.1, ⟨a.1.1, rfl⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hedge : H.edge a.1.1 = H.edge b.1.1 := by
        by_contra hne
        have hsubne :
            (⟨H.edge a.1.1, ⟨a.1.1, rfl⟩⟩ : H.toSetHypergraph) ≠
              ⟨H.edge b.1.1, ⟨b.1.1, rfl⟩⟩ := by
          intro heq
          exact hne (congrArg Subtype.val heq)
        exact (c.valid hsubne ⟨x, a.1.2, b.1.2⟩) hab
      have helabel : a.1.1 = b.1.1 := by
        by_contra hne
        have hs := hlinear hne
        rw [hedge, Set.inter_self] at hs
        exact b.2 hs
      exact Subtype.ext (Subtype.ext helabel)
    have hcard : Fintype.card (Incident x) ≤ Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      let s : Set E := {e | x ∈ H.edge e}
      change Fintype.card s ≤ n
      rw [Set.fintypeCard_eq_ncard]
      exact hdegree x
    obtain ⟨g, hg, hagree⟩ := exists_injective_extension p f hf hcard
    refine ⟨g, hg, ?_⟩
    intro a ha
    simpa [p, f] using hagree a ha
  choose localColor hlocal_injective hlocal_agree using hlocal
  let fallback : Fin n := ⟨0, hn⟩
  let color : E → Fin n := fun e ↦
    if he : (H.edge e).Nonempty then
      localColor (Classical.choose he) ⟨e, Classical.choose_spec he⟩
    else fallback
  have color_eq_local (e : E) (x : Fin n) (hx : x ∈ H.edge e) :
      color e = localColor x ⟨e, hx⟩ := by
    simp only [color]
    split
    next he =>
      by_cases hs : (H.edge e).Subsingleton
      · have hchoice : Classical.choose he = x :=
          hs (Classical.choose_spec he) hx
        subst x
        rfl
      · rw [hlocal_agree (Classical.choose he) ⟨e, Classical.choose_spec he⟩ hs,
            hlocal_agree x ⟨e, hx⟩ hs]
    next he => exact (he ⟨x, hx⟩).elim
  refine ⟨{ color := color, valid := ?_ }⟩
  intro e f hef hinter hsame
  obtain ⟨x, hxe, hxf⟩ := hinter
  apply hef
  have hincident : (⟨e, hxe⟩ : Incident x) = ⟨f, hxf⟩ :=
    hlocal_injective x (by
      rw [← color_eq_local e x hxe, ← color_eq_local f x hxf, hsame])
  exact congrArg Subtype.val hincident

end IndexedHypergraph

namespace Configuration

variable {n : ℕ} {V : Type u} [Fintype V]

/-- The dual indexed hypergraph.  Its vertices are the `n` constituent
cliques; the hyperedge labeled by a graph vertex records all cliques containing
that vertex. -/
def dual (C : Configuration n V) : IndexedHypergraph (Fin n) V where
  edge v := {i | v ∈ C.blocks i}

@[simp]
lemma mem_dual_edge (C : Configuration n V) (v : V) (i : Fin n) :
    i ∈ C.dual.edge v ↔ v ∈ C.blocks i :=
  Iff.rfl

/-- Edge-disjointness of the clique family makes the dual hypergraph linear. -/
lemma dual_isLinear (C : Configuration n V) : C.dual.IsLinear := by
  intro x y hxy i hi j hj
  by_contra hij
  have hdisj := C.edge_disjoint hij
  have hxi : (cliqueGraph (C.blocks i : Set V)).Adj x y :=
    ⟨hxy, hi.1, hi.2⟩
  have hxj : (cliqueGraph (C.blocks j : Set V)).Adj x y :=
    ⟨hxy, hj.1, hj.2⟩
  exact (SimpleGraph.disjoint_left.mp hdisj x y hxi) hxj

/-- The degree at the dual vertex `i` is exactly the size of the corresponding
clique, hence exactly `n`. -/
lemma dual_incident_ncard (C : Configuration n V) (i : Fin n) :
    {v | i ∈ C.dual.edge v}.ncard = n := by
  simpa [dual] using C.card_blocks i

lemma dual_degreeLE (C : Configuration n V) : C.dual.DegreeLE n := by
  intro i
  exact (C.dual_incident_ncard i).le

/-- A coloring of the dual hyperedges is exactly a vertex coloring of the
clique-union graph. -/
def coloringOfDualEdgeColoring {κ : Type*} (C : Configuration n V)
    (c : C.dual.EdgeColoring κ) : C.graph.Coloring κ :=
  SimpleGraph.Coloring.mk c.color fun {x y} hxy ↦ by
    obtain ⟨hne, i, hxi, hyi⟩ := C.graph_adj.mp hxy
    exact c.valid hne ⟨i, hxi, hyi⟩

/-- The converse direction of the coloring correspondence. -/
def dualEdgeColoringOfColoring {κ : Type*} (C : Configuration n V)
    (c : C.graph.Coloring κ) : C.dual.EdgeColoring κ where
  color := c
  valid := by
    intro x y hxy hinter
    obtain ⟨i, hxi, hyi⟩ := hinter
    exact c.valid (C.graph_adj.mpr ⟨hxy, i, hxi, hyi⟩)

/-- Formal graph--hypergraph coloring equivalence. -/
lemma dual_edgeColorable_iff_colorable (C : Configuration n V) (k : ℕ) :
    C.dual.EdgeColorable k ↔ C.graph.Colorable k := by
  constructor
  · rintro ⟨c⟩
    exact ⟨C.coloringOfDualEdgeColoring c⟩
  · rintro ⟨c⟩
    exact ⟨C.dualEdgeColoringOfColoring c⟩

end Configuration

/-- The exact upper-bound assertion of Erdős--Faber--Lovász at the parameter
`n`.  Together with `Configuration.n_le_chromaticNumber`, this says that the
chromatic number is exactly `n`. -/
def EFLAt (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V], ∀ C : Configuration n V, C.graph.Colorable n

/-- The universal Erdős--Faber--Lovász conjecture, including all finite
parameters. -/
def EFLConjecture : Prop := ∀ n : ℕ, EFLAt n

/-- The theorem established by Kang--Kelly--Kühn--Methuku--Osthus: the EFL
assertion holds for every sufficiently large parameter. -/
def EventuallyEFL : Prop := ∃ N : ℕ, ∀ n, N ≤ n → EFLAt n

/-- Direct-coloring formulation of Kang--Kelly--Kühn--Methuku--Osthus,
Theorem 1.1: every sufficiently large linear set-valued hypergraph on `n`
vertices has chromatic index at most `n`. -/
def EventuallySetLinearHypergraphColorable : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ H : SetHypergraph (Fin n), H.IsLinear → H.EdgeColorable n

/-- The customary loopless/nontrivial formulation: every edge has at least
two vertices.  Empty and singleton edges can be restored by
`edgeColorable_of_nontrivialEdges`. -/
def EventuallyNontrivialSetLinearHypergraphColorable : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) → H.EdgeColorable n

/-- The eventual theorem restricted to size-at-least-two edges implies the
version for all set-valued edges. -/
theorem eventuallySetLinearHypergraphColorable_of_nontrivial
    (h : EventuallyNontrivialSetLinearHypergraphColorable) :
    EventuallySetLinearHypergraphColorable := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max N 1, fun n hn H hlinear ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hn)
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hcorelinear : H.nontrivialEdges.IsLinear := by
    intro e he f hf hef
    exact hlinear he.1 hf.1 hef
  have hcoremin : ∀ e : H.nontrivialEdges, 2 ≤ e.1.ncard := fun e ↦ e.2.2
  have hcore : H.nontrivialEdges.EdgeColorable n :=
    hN n hnN H.nontrivialEdges hcorelinear hcoremin
  have hcore' :
      H.nontrivialEdges.EdgeColorable (Fintype.card (Fin n)) := by
    simpa using hcore
  simpa using H.edgeColorable_of_nontrivialEdges hlinear hcore'

/-- Literal chromatic-index formulation of Kang--Kelly--Kühn--Methuku--Osthus
Theorem 1.1. -/
def KKKMOTheorem : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ H : SetHypergraph (Fin n), H.IsLinear → H.chromaticIndex ≤ n

/-- The literal chromatic-index statement supplies the explicit colorings used
by the duality reduction. -/
theorem eventuallySetLinearHypergraphColorable_of_KKKMO
    (h : KKKMOTheorem) : EventuallySetLinearHypergraphColorable := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn H hlinear ↦ ?_⟩
  exact (H.chromaticIndex_le_iff_edgeColorable n).mp (hN n hn H hlinear)

/-- Indexed form of the sufficiently-large linear-hypergraph coloring theorem.
It is equivalent to the form needed for the EFL dual: repeated singleton edges
are retained as labels, and the degree hypothesis bounds their multiplicity. -/
def EventuallyLinearHypergraphColorable : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ (E : Type) [Fintype E], ∀ H : IndexedHypergraph (Fin n) E,
      H.IsLinear → H.DegreeLE n → H.EdgeColorable n

/-- The published set-valued theorem implies the indexed version needed by
the EFL dual.  The threshold is enlarged to `1` solely to provide a color for
empty labeled edges; singleton multiplicities are handled by
`edgeColorable_of_toSetHypergraph_edgeColorable`. -/
theorem eventuallyLinearHypergraphColorable_of_setVersion
    (h : EventuallySetLinearHypergraphColorable) :
    EventuallyLinearHypergraphColorable := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max N 1, fun n hn E _ H hlinear hdegree ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hn)
  exact H.edgeColorable_of_toSetHypergraph_edgeColorable hnpos hlinear hdegree
    (hN n hnN H.toSetHypergraph (H.toSetHypergraph_isLinear hlinear))

/-- The complete formal reduction from the sufficiently-large indexed
linear-hypergraph theorem to the sufficiently-large EFL upper bound. -/
theorem eventuallyEFL_of_eventuallyLinearHypergraphColorable
    (h : EventuallyLinearHypergraphColorable) : EventuallyEFL := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn V _ C ↦ ?_⟩
  rw [← C.dual_edgeColorable_iff_colorable]
  exact hN n hn V C.dual C.dual_isLinear C.dual_degreeLE

/-- The eventual chromatic-number equality which is the established resolution
of Erdős Problem 19. -/
def Erdos19Eventually : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ (V : Type) [Fintype V], ∀ C : Configuration n V,
      C.graph.chromaticNumber = n

/-- Once the sufficiently-large upper bound is available, the clique lower
bound turns it into the exact equality in the problem statement. -/
theorem erdos19Eventually_of_eventuallyEFL (h : EventuallyEFL) :
    Erdos19Eventually := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max N 1, fun n hn V _ C ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hn)
  exact C.chromaticNumber_eq hnpos (hN n hnN V C)

/-- End-to-end reduction from the published hypergraph statement to the exact
eventual conclusion. -/
theorem erdos19_of_eventuallyLinearHypergraphColorable
    (h : EventuallyLinearHypergraphColorable) : Erdos19Eventually :=
  erdos19Eventually_of_eventuallyEFL
    (eventuallyEFL_of_eventuallyLinearHypergraphColorable h)

/-- End-to-end, assumption-preserving reduction from the direct formulation of
Kang--Kelly--Kühn--Methuku--Osthus Theorem 1.1 to the established eventual
resolution of Erdős Problem 19. -/
theorem erdos19_of_KKKMO_setVersion
    (h : EventuallySetLinearHypergraphColorable) : Erdos19Eventually :=
  erdos19_of_eventuallyLinearHypergraphColorable
    (eventuallyLinearHypergraphColorable_of_setVersion h)

/-- End-to-end reduction from the customary size-at-least-two form of the
published sufficiently-large theorem. -/
theorem erdos19_of_KKKMO_nontrivialVersion
    (h : EventuallyNontrivialSetLinearHypergraphColorable) : Erdos19Eventually :=
  erdos19_of_KKKMO_setVersion
    (eventuallySetLinearHypergraphColorable_of_nontrivial h)

/-- Fully formal reduction from the literal published Theorem 1.1 statement to
the established eventual equality. -/
theorem erdos19_of_KKKMO (h : KKKMOTheorem) : Erdos19Eventually :=
  erdos19_of_KKKMO_setVersion
    (eventuallySetLinearHypergraphColorable_of_KKKMO h)

/-- Packaging lemma: the exact EFL upper bound implies the equality asked for
in Erdős Problem 19. -/
theorem erdos19_of_EFLAt {n : ℕ} (hn : 0 < n) (hEFL : EFLAt n)
    (V : Type) [Fintype V] (C : Configuration n V) :
    C.graph.chromaticNumber = n :=
  C.chromaticNumber_eq hn (hEFL V C)

#print axioms erdos19_of_KKKMO

end Erdos19
