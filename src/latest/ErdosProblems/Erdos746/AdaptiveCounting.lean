import ErdosProblems.Erdos746.Adaptive
import ErdosProblems.Erdos746.Model
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Exact counting interpretation of the adaptive lower-tail mass

The adaptive estimate in `Adaptive` is written as a finite probability
tree.  This file identifies that tree exactly with uniform counting of
ordered injective continuations.  In particular, it supplies the bridge
from an implication about every completed continuation to a bound on the
fraction of continuations having the event.
-/

open scoped BigOperators

namespace Erdos746

noncomputable section

variable {A : Type*} [DecidableEq A]

/-- An ordered injective continuation drawn from the elements which remain
after the history `h`. -/
abbrev FreshContinuation (ambient : Finset A) (h : List A) (steps : ℕ) :=
  Fin steps ↪ remaining ambient h

/-- The chronological list represented by a fresh continuation. -/
def freshContinuationHistory {ambient : Finset A} {h : List A} {steps : ℕ}
    (c : FreshContinuation ambient h steps) : List A :=
  List.ofFn fun i ↦ (c i : A)

@[simp]
theorem length_freshContinuationHistory {ambient : Finset A} {h : List A}
    {steps : ℕ} (c : FreshContinuation ambient h steps) :
    (freshContinuationHistory c).length = steps := by
  simp [freshContinuationHistory]

/-- The number of adaptive booster hits along a chronological continuation,
starting after the fixed history `h`. -/
def boosterHitCountFrom (boosters : List A → Finset A) :
    List A → List A → ℕ
  | _, [] => 0
  | h, a :: tail =>
      (if a ∈ boosters h then 1 else 0) +
        boosterHitCountFrom boosters (h ++ [a]) tail

@[simp]
theorem boosterHitCountFrom_nil (boosters : List A → Finset A) (h : List A) :
    boosterHitCountFrom boosters h [] = 0 := rfl

@[simp]
theorem boosterHitCountFrom_cons (boosters : List A → Finset A)
    (h : List A) (a : A) (tail : List A) :
    boosterHitCountFrom boosters h (a :: tail) =
      (if a ∈ boosters h then 1 else 0) +
        boosterHitCountFrom boosters (h ++ [a]) tail := rfl

/-- Exact number of fresh ordered continuations for which `event` holds. -/
def freshContinuationEventCount (ambient : Finset A) (h : List A)
    (steps : ℕ) (event : List A → Prop) : ℕ :=
  Nat.card
    {c : FreshContinuation ambient h steps // event (freshContinuationHistory c)}

abbrev CountingFixedFirstEmbedding (B : Type*) (b : B) (steps : ℕ) :=
  {f : Fin (steps + 1) ↪ B // f 0 = b}

def countingFixedFirstTail {B : Type*} {b : B} {steps : ℕ}
    (f : CountingFixedFirstEmbedding B b steps) :
    Fin steps ↪ {x : B // x ≠ b} where
  toFun i := ⟨f.1 i.succ, by
    intro hi
    have heq : f.1 i.succ = f.1 0 := hi.trans f.2.symm
    exact Fin.succ_ne_zero i (f.1.injective heq)⟩
  inj' i j hij := by
    apply Fin.succ_injective steps
    apply f.1.injective
    exact congrArg Subtype.val hij

def countingConsAvoiding {B : Type*} {b : B} {steps : ℕ}
    (g : Fin steps ↪ {x : B // x ≠ b}) :
    CountingFixedFirstEmbedding B b steps :=
  ⟨Fin.Embedding.cons
      (g.trans (Function.Embedding.subtype _))
      (by
        rintro ⟨i, hi⟩
        exact (g i).2 hi),
    by simp [Fin.Embedding.cons]⟩

def countingFixedFirstEmbeddingEquiv (B : Type*) (b : B) (steps : ℕ) :
    CountingFixedFirstEmbedding B b steps ≃
      (Fin steps ↪ {x : B // x ≠ b}) where
  toFun := countingFixedFirstTail
  invFun := countingConsAvoiding
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact f.2.symm
    · rfl
  right_inv g := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

theorem card_counting_avoiding_element (B : Type*) [Fintype B]
    [DecidableEq B] (b : B) :
    Fintype.card {x : B // x ≠ b} = Fintype.card B - 1 := by
  rw [Fintype.card_subtype_compl (fun x : B ↦ x = b)]
  simp

/-- Removing the chosen first entry from the remaining alphabet gives the
remaining alphabet after appending that entry to the history. -/
def remainingAfterEquiv (ambient : Finset A) (h : List A)
    (a : remaining ambient h) :
    {x : remaining ambient h // x ≠ a} ≃ remaining ambient (h ++ [a.1]) where
  toFun x := ⟨x.1.1, by
    rw [mem_remaining_iff]
    have hx := mem_remaining_iff.mp x.1.2
    refine ⟨hx.1, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    push Not
    refine ⟨hx.2, ?_⟩
    intro heq
    apply x.2
    apply Subtype.ext
    exact heq⟩
  invFun x := ⟨⟨x.1, by
    have hx := mem_remaining_iff.mp x.2
    rw [mem_remaining_iff]
    exact ⟨hx.1, fun hxmem ↦ hx.2 (by simp [hxmem])⟩⟩, by
      intro heq
      have hval := congrArg Subtype.val heq
      have hx := (mem_remaining_iff.mp x.2).2
      apply hx
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inr hval⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Split a nonempty ordered continuation into its first choice and its
fresh tail. -/
def freshContinuationConsEquiv (ambient : Finset A) (h : List A)
    (steps : ℕ) :
    FreshContinuation ambient h (steps + 1) ≃
      Σ a : remaining ambient h,
        FreshContinuation ambient (h ++ [a.1]) steps :=
  (Equiv.sigmaFiberEquiv
      (fun c : FreshContinuation ambient h (steps + 1) ↦ c 0)).symm.trans
    (Equiv.sigmaCongrRight fun a ↦
      (countingFixedFirstEmbeddingEquiv (remaining ambient h) a steps).trans
        (Equiv.embeddingCongr (Equiv.refl (Fin steps))
          (remainingAfterEquiv ambient h a)))

@[simp]
theorem freshContinuationConsEquiv_fst (ambient : Finset A) (h : List A)
    (steps : ℕ) (c : FreshContinuation ambient h (steps + 1)) :
    (freshContinuationConsEquiv ambient h steps c).1 = c 0 := rfl

@[simp]
theorem freshContinuationConsEquiv_snd_apply (ambient : Finset A) (h : List A)
    (steps : ℕ) (c : FreshContinuation ambient h (steps + 1)) (i : Fin steps) :
    ((freshContinuationConsEquiv ambient h steps c).2 i : A) = (c i.succ : A) := rfl

@[simp]
theorem freshContinuationHistory_consEquiv (ambient : Finset A) (h : List A)
    (steps : ℕ) (c : FreshContinuation ambient h (steps + 1)) :
    freshContinuationHistory c =
      ((freshContinuationConsEquiv ambient h steps c).1 : A) ::
        freshContinuationHistory (freshContinuationConsEquiv ambient h steps c).2 := by
  rw [freshContinuationHistory, List.ofFn_succ]
  congr 1

/-- Move a predicate on a dependent pair through the sigma/subtype
presentation. -/
def sigmaFreshContinuationEventEquiv (ambient : Finset A) (h : List A)
    (steps : ℕ) (event : List A → Prop) :
    {z : (Σ a : remaining ambient h,
        FreshContinuation ambient (h ++ [a.1]) steps) //
      event ((z.fst : A) :: freshContinuationHistory z.snd)} ≃
      Σ a : remaining ambient h,
        {c : FreshContinuation ambient (h ++ [a.1]) steps //
          event (a.1 :: freshContinuationHistory c)} where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Restricting the head-tail equivalence to continuations satisfying an
event. -/
def freshContinuationEventConsEquiv (ambient : Finset A) (h : List A)
    (steps : ℕ) (event : List A → Prop) :
    {c : FreshContinuation ambient h (steps + 1) //
        event (freshContinuationHistory c)} ≃
      Σ a : remaining ambient h,
        {c : FreshContinuation ambient (h ++ [a.1]) steps //
          event (a.1 :: freshContinuationHistory c)} :=
  ((freshContinuationConsEquiv ambient h steps).subtypeEquiv fun c ↦ by
      rw [freshContinuationHistory_consEquiv]).trans
    (sigmaFreshContinuationEventEquiv ambient h steps event)

/-- Head-tail recurrence for exact continuation counts. -/
theorem freshContinuationEventCount_succ (ambient : Finset A) (h : List A)
    (steps : ℕ) (event : List A → Prop) :
    freshContinuationEventCount ambient h (steps + 1) event =
      ∑ a : remaining ambient h,
        freshContinuationEventCount ambient (h ++ [a.1]) steps
          (fun tail ↦ event (a.1 :: tail)) := by
  unfold freshContinuationEventCount
  rw [Nat.card_congr (freshContinuationEventConsEquiv ambient h steps event),
    Nat.card_sigma]

theorem freshContinuationEventCount_zero_of (ambient : Finset A) (h : List A)
    (event : List A → Prop) (hevent : event []) :
    freshContinuationEventCount ambient h 0 event = 1 := by
  classical
  unfold freshContinuationEventCount freshContinuationHistory
  simp [hevent, Nat.card_eq_fintype_card]

theorem freshContinuationEventCount_zero_of_not (ambient : Finset A) (h : List A)
    (event : List A → Prop) (hevent : ¬ event []) :
    freshContinuationEventCount ambient h 0 event = 0 := by
  classical
  unfold freshContinuationEventCount freshContinuationHistory
  simp [hevent, Nat.card_eq_fintype_card]

theorem freshContinuationEventCount_congr (ambient : Finset A) (h : List A)
    (steps : ℕ) {p q : List A → Prop}
    (hpq : ∀ tail, p tail ↔ q tail) :
    freshContinuationEventCount ambient h steps p =
      freshContinuationEventCount ambient h steps q := by
  unfold freshContinuationEventCount
  apply Nat.card_congr
  exact
    { toFun := fun c ↦ ⟨c.1, (hpq _).mp c.2⟩
      invFun := fun c ↦ ⟨c.1, (hpq _).mpr c.2⟩
      left_inv := fun c ↦ by apply Subtype.ext; rfl
      right_inv := fun c ↦ by apply Subtype.ext; rfl }

theorem freshContinuationEventCount_mono (ambient : Finset A) (h : List A)
    (steps : ℕ) {p q : List A → Prop}
    (hpq : ∀ tail, p tail → q tail) :
    freshContinuationEventCount ambient h steps p ≤
      freshContinuationEventCount ambient h steps q := by
  unfold freshContinuationEventCount
  apply Nat.card_le_card_of_injective
    (fun c : {c : FreshContinuation ambient h steps //
        p (freshContinuationHistory c)} ↦
      (⟨c.1, hpq _ c.2⟩ : {c : FreshContinuation ambient h steps //
        q (freshContinuationHistory c)}))
  intro c d hcd
  apply Subtype.ext
  exact congrArg (fun x ↦ x.1) hcd

/-- A sum using the uniform remaining-element transition can be indexed by
the subtype of genuinely remaining choices. -/
theorem sum_uniformRemainingFactor_mul (ambient : Finset A) (h : List A)
    (f : A → ℝ) :
    (∑ a ∈ ambient, uniformRemainingFactor ambient h a * f a) =
      ((remaining ambient h).card : ℝ)⁻¹ *
        ∑ a : remaining ambient h, f a.1 := by
  classical
  calc
    (∑ a ∈ ambient, uniformRemainingFactor ambient h a * f a) =
        ∑ a ∈ ambient,
          if a ∈ remaining ambient h then
            ((remaining ambient h).card : ℝ)⁻¹ * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [uniformRemainingFactor]
      split_ifs <;> simp_all
    _ = ∑ a ∈ remaining ambient h,
          ((remaining ambient h).card : ℝ)⁻¹ * f a := by
      rw [← Finset.sum_filter]
      congr 1
      ext a
      simp [remaining]
    _ = ((remaining ambient h).card : ℝ)⁻¹ *
          ∑ a ∈ remaining ambient h, f a := by
      rw [Finset.mul_sum]
    _ = ((remaining ambient h).card : ℝ)⁻¹ *
          ∑ a : remaining ambient h, f a.1 := by
      rw [Finset.sum_coe_sort]

/-- Exactly one element disappears from the remaining alphabet after a
valid next choice. -/
theorem card_remaining_append_singleton (ambient : Finset A) (h : List A)
    (a : remaining ambient h) :
    (remaining ambient (h ++ [a.1])).card =
      (remaining ambient h).card - 1 := by
  calc
    (remaining ambient (h ++ [a.1])).card =
        Fintype.card (remaining ambient (h ++ [a.1])) := by simp
    _ = Fintype.card {x : remaining ambient h // x ≠ a} := by
      exact Fintype.card_congr (remainingAfterEquiv ambient h a).symm
    _ = Fintype.card (remaining ambient h) - 1 :=
      card_counting_avoiding_element (remaining ambient h) a
    _ = (remaining ambient h).card - 1 := by simp

/-- The full type of fresh continuations has falling-factorial cardinality. -/
theorem card_freshContinuation (ambient : Finset A) (h : List A) (steps : ℕ) :
    Fintype.card (FreshContinuation ambient h steps) =
      (remaining ambient h).card.descFactorial steps := by
  rw [Fintype.card_embedding_eq]
  simp

/-- The lower-tail predicate on chronological continuation lists. -/
def boosterLowerTailEvent (boosters : List A → Finset A)
    (h : List A) (budget : ℕ) (tail : List A) : Prop :=
  boosterHitCountFrom boosters h tail ≤ budget

/-- Probability mass of an arbitrary event on fresh ordered continuations,
expanded by chronological sampling without replacement. -/
noncomputable def uniformFreshEventMass (ambient : Finset A) :
    List A → ℕ → (List A → Prop) → ℝ
  | _, 0, event => @ite ℝ (event []) (Classical.propDecidable _) 1 0
  | h, steps + 1, event =>
      ∑ a ∈ ambient, uniformRemainingFactor ambient h a *
        uniformFreshEventMass ambient (h ++ [a]) steps
          (fun tail ↦ event (a :: tail))

theorem uniformFreshEventMass_zero_of (ambient : Finset A) (h : List A)
    (event : List A → Prop) (hevent : event []) :
    uniformFreshEventMass ambient h 0 event = 1 := by
  simp [uniformFreshEventMass, hevent]

theorem uniformFreshEventMass_zero_of_not (ambient : Finset A) (h : List A)
    (event : List A → Prop) (hevent : ¬ event []) :
    uniformFreshEventMass ambient h 0 event = 0 := by
  simp [uniformFreshEventMass, hevent]

@[simp]
theorem uniformFreshEventMass_succ (ambient : Finset A) (h : List A)
    (steps : ℕ) (event : List A → Prop) :
    uniformFreshEventMass ambient h (steps + 1) event =
      ∑ a ∈ ambient, uniformRemainingFactor ambient h a *
        uniformFreshEventMass ambient (h ++ [a]) steps
          (fun tail ↦ event (a :: tail)) := rfl

/-- Event mass depends only on the event predicate, not its presentation. -/
theorem uniformFreshEventMass_congr (ambient : Finset A) :
    ∀ (h : List A) (steps : ℕ) (p q : List A → Prop),
      (∀ tail, p tail ↔ q tail) →
      uniformFreshEventMass ambient h steps p =
        uniformFreshEventMass ambient h steps q := by
  intro h steps
  induction steps generalizing h with
  | zero =>
      intro p q hpq
      by_cases hp : p []
      · rw [uniformFreshEventMass_zero_of ambient h p hp,
          uniformFreshEventMass_zero_of ambient h q ((hpq []).mp hp)]
      · rw [uniformFreshEventMass_zero_of_not ambient h p hp,
          uniformFreshEventMass_zero_of_not ambient h q]
        exact fun hq ↦ hp ((hpq []).mpr hq)
  | succ steps ih =>
      intro p q hpq
      rw [uniformFreshEventMass_succ, uniformFreshEventMass_succ]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      apply ih
      intro tail
      exact hpq (a :: tail)

@[simp]
theorem uniformFreshEventMass_false (ambient : Finset A) (h : List A)
    (steps : ℕ) :
    uniformFreshEventMass ambient h steps (fun _ ↦ False) = 0 := by
  induction steps generalizing h with
  | zero => exact uniformFreshEventMass_zero_of_not ambient h _ (by simp)
  | succ steps ih =>
      rw [uniformFreshEventMass_succ]
      simp [ih]

/-- The recursively defined adaptive lower-tail mass is precisely the event
mass of the corresponding hit-count predicate on chronological lists. -/
theorem uniformBoosterLowerTailMass_eq_uniformFreshEventMass
    (ambient : Finset A) (boosters : List A → Finset A) :
    ∀ (h : List A) (steps budget : ℕ),
      uniformBoosterLowerTailMass ambient boosters h steps budget =
        uniformFreshEventMass ambient h steps
          (boosterLowerTailEvent boosters h budget) := by
  intro h steps
  induction steps generalizing h with
  | zero =>
      intro budget
      rw [uniformBoosterLowerTailMass, adaptiveLowerTailMass_zero]
      exact (uniformFreshEventMass_zero_of ambient h _
        (by simp [boosterLowerTailEvent])).symm
  | succ steps ih =>
      intro budget
      cases budget with
      | zero =>
          rw [uniformBoosterLowerTailMass, adaptiveLowerTailMass_succ_zero,
            uniformFreshEventMass_succ]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hhit : a ∈ boosters h
          · simp only [boosterHit, hhit, decide_true, if_true, mul_zero]
            rw [uniformFreshEventMass_congr ambient (h ++ [a]) steps
              (fun tail ↦ boosterLowerTailEvent boosters h 0 (a :: tail))
              (fun _ ↦ False)]
            · simp
            · intro tail
              simp [boosterLowerTailEvent, boosterHitCountFrom, hhit]
          · simp only [boosterHit, hhit, decide_false, if_false]
            congr 1
            change uniformBoosterLowerTailMass ambient boosters
              (h ++ [a]) steps 0 = _
            rw [ih (h ++ [a]) 0]
            apply uniformFreshEventMass_congr
            intro tail
            simp [boosterLowerTailEvent, boosterHitCountFrom, hhit]
      | succ budget =>
          rw [uniformBoosterLowerTailMass, adaptiveLowerTailMass_succ_succ,
            uniformFreshEventMass_succ]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hhit : a ∈ boosters h
          · simp only [boosterHit, hhit, decide_true, if_true]
            congr 1
            change uniformBoosterLowerTailMass ambient boosters
              (h ++ [a]) steps budget = _
            rw [ih (h ++ [a]) budget]
            apply uniformFreshEventMass_congr
            intro tail
            simp only [boosterLowerTailEvent, boosterHitCountFrom, hhit, if_pos]
            omega
          · simp only [boosterHit, hhit, decide_false, if_false]
            congr 1
            change uniformBoosterLowerTailMass ambient boosters
              (h ++ [a]) steps (budget + 1) = _
            rw [ih (h ++ [a]) (budget + 1)]
            apply uniformFreshEventMass_congr
            intro tail
            simp [boosterLowerTailEvent, boosterHitCountFrom, hhit]

/-- Under a valid sampling horizon, chronological uniform sampling without
replacement assigns the same mass to every fresh ordered continuation.
Consequently, the mass of an event is its exact continuation count divided
by the total falling-factorial count. -/
theorem uniformFreshEventMass_eq_eventCount_div
    (ambient : Finset A) {h : List A} {steps : ℕ}
    (hh : SamplingHorizon ambient h steps) (event : List A → Prop) :
    uniformFreshEventMass ambient h steps event =
      (freshContinuationEventCount ambient h steps event : ℝ) /
        ((remaining ambient h).card.descFactorial steps : ℝ) := by
  classical
  induction steps generalizing h event with
  | zero =>
      by_cases hevent : event []
      · rw [uniformFreshEventMass_zero_of ambient h event hevent,
          freshContinuationEventCount_zero_of ambient h event hevent]
        norm_num
      · rw [uniformFreshEventMass_zero_of_not ambient h event hevent,
          freshContinuationEventCount_zero_of_not ambient h event hevent]
        norm_num
  | succ steps ih =>
      have hremaining_ne : (remaining ambient h).card ≠ 0 :=
        remaining_card_ne_zero_of_samplingHorizon_succ ambient hh
      have hcapacity : steps + 1 ≤ (remaining ambient h).card := by
        rw [card_remaining_of_admissible ambient hh.1]
        apply Nat.le_sub_of_add_le
        simpa [Nat.add_comm] using hh.2
      have hsteps : steps ≤ (remaining ambient h).card - 1 := by
        omega
      have htail (a : remaining ambient h) :
          SamplingHorizon ambient (h ++ [a.1]) steps := by
        apply samplingHorizon_append_of_uniformRemainingFactor_ne_zero ambient hh
        simp [uniformRemainingFactor, a.2, hremaining_ne]
      have hmass (a : remaining ambient h) :
          uniformFreshEventMass ambient (h ++ [a.1]) steps
              (fun tail ↦ event (a.1 :: tail)) =
            (freshContinuationEventCount ambient (h ++ [a.1]) steps
                (fun tail ↦ event (a.1 :: tail)) : ℝ) /
              ((remaining ambient (h ++ [a.1])).card.descFactorial steps : ℝ) :=
        ih (h := h ++ [a.1]) (event := fun tail ↦ event (a.1 :: tail)) (htail a)
      rw [uniformFreshEventMass_succ,
        sum_uniformRemainingFactor_mul ambient h]
      simp_rw [hmass]
      simp_rw [card_remaining_append_singleton]
      rw [freshContinuationEventCount_succ]
      push_cast
      have hdesc :
          (remaining ambient h).card.descFactorial (steps + 1) =
            (remaining ambient h).card *
              ((remaining ambient h).card - 1).descFactorial steps := by
        calc
          (remaining ambient h).card.descFactorial (steps + 1) =
              (((remaining ambient h).card - 1) + 1).descFactorial
                (steps + 1) := by
                  congr 1
                  omega
          _ = (((remaining ambient h).card - 1) + 1) *
                ((remaining ambient h).card - 1).descFactorial steps :=
              Nat.succ_descFactorial_succ _ steps
          _ = (remaining ambient h).card *
                ((remaining ambient h).card - 1).descFactorial steps := by
              congr 1
              omega
      rw [hdesc]
      push_cast
      have htailDesc_ne :
          (((remaining ambient h).card - 1).descFactorial steps : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hsteps))
      have hremaining_cast_ne : ((remaining ambient h).card : ℝ) ≠ 0 := by
        exact_mod_cast hremaining_ne
      rw [← Finset.sum_div]
      field_simp [hremaining_cast_ne, htailDesc_ne]

/-- Exact counting form of the adaptive lower-tail mass. -/
theorem uniformBoosterLowerTailMass_eq_eventCount_div
    (ambient : Finset A) (boosters : List A → Finset A)
    {h : List A} {steps budget : ℕ}
    (hh : SamplingHorizon ambient h steps) :
    uniformBoosterLowerTailMass ambient boosters h steps budget =
      (freshContinuationEventCount ambient h steps
          (boosterLowerTailEvent boosters h budget) : ℝ) /
        ((remaining ambient h).card.descFactorial steps : ℝ) := by
  rw [uniformBoosterLowerTailMass_eq_uniformFreshEventMass]
  exact uniformFreshEventMass_eq_eventCount_div ambient hh _

/-- Any event which forces the adaptive lower-tail condition occupies at
most the lower-tail mass after normalization by all fresh continuations. -/
theorem freshContinuationEventCount_div_le_uniformBoosterLowerTailMass
    (ambient : Finset A) (boosters : List A → Finset A)
    {h : List A} {steps budget : ℕ}
    (hh : SamplingHorizon ambient h steps) (event : List A → Prop)
    (hevent : ∀ tail, event tail →
      boosterHitCountFrom boosters h tail ≤ budget) :
    (freshContinuationEventCount ambient h steps event : ℝ) /
        ((remaining ambient h).card.descFactorial steps : ℝ) ≤
      uniformBoosterLowerTailMass ambient boosters h steps budget := by
  rw [uniformBoosterLowerTailMass_eq_eventCount_div ambient boosters hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast freshContinuationEventCount_mono ambient h steps
    (fun tail htail ↦ hevent tail htail)

/-- The abstract uniform probability on fresh continuations agrees exactly
with the chronological sampling-without-replacement event mass. -/
theorem uniformProbability_freshContinuation_eq_uniformFreshEventMass
    (ambient : Finset A) {h : List A} {steps : ℕ}
    (hh : SamplingHorizon ambient h steps) (event : List A → Prop) :
    uniformProbability
        (fun c : FreshContinuation ambient h steps ↦
          event (freshContinuationHistory c)) =
      uniformFreshEventMass ambient h steps event := by
  classical
  rw [uniformFreshEventMass_eq_eventCount_div ambient hh]
  have hnum :
      (Finset.univ.filter (fun c : FreshContinuation ambient h steps ↦
        event (freshContinuationHistory c))).card =
        freshContinuationEventCount ambient h steps event := by
    unfold freshContinuationEventCount
    exact (Nat.subtype_card
      (Finset.univ.filter (fun c : FreshContinuation ambient h steps ↦
        event (freshContinuationHistory c))) (by simp)).symm
  unfold uniformProbability
  rw [hnum, card_freshContinuation]

/-- In particular, uniform continuation probability of the booster
lower-tail event is the adaptive lower-tail mass used by sprinkling. -/
theorem uniformProbability_boosterLowerTailEvent_eq_uniformBoosterLowerTailMass
    (ambient : Finset A) (boosters : List A → Finset A)
    {h : List A} {steps budget : ℕ}
    (hh : SamplingHorizon ambient h steps) :
    uniformProbability
        (fun c : FreshContinuation ambient h steps ↦
          boosterHitCountFrom boosters h (freshContinuationHistory c) ≤ budget) =
      uniformBoosterLowerTailMass ambient boosters h steps budget := by
  change uniformProbability
      (fun c : FreshContinuation ambient h steps ↦
        boosterLowerTailEvent boosters h budget (freshContinuationHistory c)) = _
  rw [uniformProbability_freshContinuation_eq_uniformFreshEventMass
    ambient hh (boosterLowerTailEvent boosters h budget)]
  exact
    (uniformBoosterLowerTailMass_eq_uniformFreshEventMass
      ambient boosters h steps budget).symm

end

end Erdos746
