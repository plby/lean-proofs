/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Finite counting for the random block construction

The probabilistic step in the Conlon--Fox--Pham construction only uses the
uniform distribution on a finite tuple space.  This file records the needed
facts as cardinality inequalities, so no measure-theoretic probability space
is involved.
-/

namespace Erdos54

open scoped BigOperators

namespace FiniteProbability

variable {X ι : Type*}

/-! ## Uniform finite tuples and elementary selection -/

theorem tuple_count [Fintype X] (n : ℕ) :
    Fintype.card (Fin n → X) = Fintype.card X ^ n := by
  simp

theorem tuple_univ_card [Fintype X] (n : ℕ) :
    (Finset.univ : Finset (Fin n → X)).card = Fintype.card X ^ n := by
  simp

theorem exists_not_of_filter_card_lt [Fintype X] [DecidableEq X]
    (n : ℕ) (bad : (Fin n → X) → Prop) [DecidablePred bad]
    (hbad : (Finset.univ.filter bad).card < Fintype.card X ^ n) :
    ∃ f : Fin n → X, ¬ bad f := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hall : Finset.univ.filter bad = (Finset.univ : Finset (Fin n → X)) := by
    exact Finset.filter_eq_self.mpr (fun f _ ↦ h f)
  rw [hall, tuple_univ_card] at hbad
  exact (Nat.lt_irrefl _ hbad)

theorem exists_good_of_bad_card_lt [Fintype X] [DecidableEq X]
    (n : ℕ) (good : (Fin n → X) → Prop) [DecidablePred good]
    (hbad : (Finset.univ.filter fun f ↦ ¬ good f).card < Fintype.card X ^ n) :
    ∃ f : Fin n → X, good f := by
  simpa only [not_not] using
    (exists_not_of_filter_card_lt n (fun f ↦ ¬ good f) hbad)

/-! ## Union bounds -/

theorem card_filter_exists_le_sum [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι] (n : ℕ)
    (event : ι → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)] :
    (Finset.univ.filter fun f ↦ ∃ i, event i f).card ≤
      ∑ i : ι, (Finset.univ.filter (event i)).card := by
  classical
  let family : ι → Finset (Fin n → X) :=
    fun i ↦ Finset.univ.filter (event i)
  have hsubset :
      Finset.univ.filter (fun f ↦ ∃ i, event i f) ⊆
        Finset.univ.biUnion family := by
    intro f hf
    obtain ⟨-, i, hi⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ f, hi⟩⟩
  exact (Finset.card_le_card hsubset).trans (Finset.card_biUnion_le)

theorem card_filter_exists_le_mul [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι] (n B : ℕ)
    (event : ι → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)]
    (hcard : ∀ i, (Finset.univ.filter (event i)).card ≤ B) :
    (Finset.univ.filter fun f ↦ ∃ i, event i f).card ≤ Fintype.card ι * B := by
  calc
    (Finset.univ.filter fun f ↦ ∃ i, event i f).card ≤
        ∑ i : ι, (Finset.univ.filter (event i)).card :=
      card_filter_exists_le_sum n event
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ ↦ hcard i
    _ = Fintype.card ι * B := by simp

/-! ## Pulling an event back along a coordinate embedding -/

/-- Restriction of a tuple to the coordinates selected by an embedding. -/
def projectTuple {q n : ℕ} (e : Fin q ↪ Fin n) (f : Fin n → X) : Fin q → X :=
  fun i ↦ f (e i)

/-- The fibre of `projectTuple` above a fixed short tuple. -/
def projectionFiber [Fintype X] [DecidableEq X] {q n : ℕ}
    (e : Fin q ↪ Fin n) (g : Fin q → X) : Finset (Fin n → X) :=
  Finset.univ.filter fun f ↦ projectTuple e f = g

@[simp] theorem mem_projectionFiber [Fintype X] [DecidableEq X] {q n : ℕ}
    {e : Fin q ↪ Fin n} {g : Fin q → X} {f : Fin n → X} :
    f ∈ projectionFiber e g ↔ projectTuple e f = g := by
  simp [projectionFiber]

/-- A fixed projection leaves at most `n-q` freely chosen coordinates. -/
theorem projectionFiber_card_le [Fintype X] [DecidableEq X] {q n : ℕ}
    (e : Fin q ↪ Fin n) (g : Fin q → X) :
    (projectionFiber e g).card ≤ Fintype.card X ^ (n - q) := by
  let selected : Finset (Fin n) := Finset.univ.image e
  let E := ↥(projectionFiber e g)
  let R := {j : Fin n // j ∉ selected} → X
  let restrict : E → R := fun f j ↦ f.1 j.1
  have hrestrict : Function.Injective restrict := by
    intro f h hfh
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ selected
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      have hf : projectTuple e f.1 = g := mem_projectionFiber.mp f.2
      have hh : projectTuple e h.1 = g := mem_projectionFiber.mp h.2
      exact (congrFun hf i).trans (congrFun hh i).symm
    · exact congrFun hfh ⟨j, hj⟩
  have hE : Fintype.card E = (projectionFiber e g).card := by
    exact Fintype.card_coe _
  have hselected : selected.card = q := by
    calc
      selected.card = (Finset.univ : Finset (Fin q)).card := by
        exact Finset.card_image_of_injective _ e.injective
      _ = q := by simp
  have hcomplement : Fintype.card {j : Fin n // j ∉ selected} = n - q := by
    calc
      Fintype.card {j : Fin n // j ∉ selected} =
          Fintype.card (Fin n) - Fintype.card {j : Fin n // j ∈ selected} :=
        Fintype.card_subtype_compl (fun j : Fin n ↦ j ∈ selected)
      _ = n - selected.card := by
        rw [Fintype.card_fin, Fintype.card_coe]
      _ = n - q := by rw [hselected]
  have hR : Fintype.card R = Fintype.card X ^ (n - q) := by
    simp [R, hcomplement]
  rw [← hE, ← hR]
  exact Fintype.card_le_of_injective restrict hrestrict

/-- Full tuples whose selected coordinates form a member of `bad`. -/
def pullbackTuples [Fintype X] [DecidableEq X] {q n : ℕ}
    (e : Fin q ↪ Fin n) (bad : Finset (Fin q → X)) : Finset (Fin n → X) :=
  Finset.univ.filter fun f ↦ projectTuple e f ∈ bad

@[simp] theorem mem_pullbackTuples [Fintype X] [DecidableEq X] {q n : ℕ}
    {e : Fin q ↪ Fin n} {bad : Finset (Fin q → X)} {f : Fin n → X} :
    f ∈ pullbackTuples e bad ↔ projectTuple e f ∈ bad := by
  simp [pullbackTuples]

/-- Pulling a set of bad `q`-tuples back to `n` coordinates costs at most
`|X|^(n-q)` extensions per bad tuple. -/
theorem pullbackTuples_card_le [Fintype X] [DecidableEq X] {q n : ℕ}
    (e : Fin q ↪ Fin n) (bad : Finset (Fin q → X)) :
    (pullbackTuples e bad).card ≤ bad.card * Fintype.card X ^ (n - q) := by
  have hsubset : pullbackTuples e bad ⊆ bad.biUnion (projectionFiber e) := by
    intro f hf
    have hproj : projectTuple e f ∈ bad := mem_pullbackTuples.mp hf
    exact Finset.mem_biUnion.mpr ⟨projectTuple e f, hproj,
      mem_projectionFiber.mpr rfl⟩
  calc
    (pullbackTuples e bad).card ≤ (bad.biUnion (projectionFiber e)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ g ∈ bad, (projectionFiber e g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ bad, Fintype.card X ^ (n - q) := by
      exact Finset.sum_le_sum fun g hg ↦ projectionFiber_card_le e g
    _ = bad.card * Fintype.card X ^ (n - q) := by simp

/-- Union bound for a family of bad short patterns placed in selected
coordinates of a full tuple. -/
theorem card_exists_badProjection_le
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι] {q n : ℕ}
    (embedding : ι → Fin q ↪ Fin n) (bad : ι → Finset (Fin q → X)) :
    (Finset.univ.filter fun f : Fin n → X ↦
        ∃ i, projectTuple (embedding i) f ∈ bad i).card ≤
      ∑ i : ι, (bad i).card * Fintype.card X ^ (n - q) := by
  calc
    _ ≤ ∑ i : ι,
        (Finset.univ.filter fun f : Fin n → X ↦
          projectTuple (embedding i) f ∈ bad i).card :=
      card_filter_exists_le_sum n
        (fun i f ↦ projectTuple (embedding i) f ∈ bad i)
    _ ≤ ∑ i : ι, (bad i).card * Fintype.card X ^ (n - q) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pullbackTuples] using
        pullbackTuples_card_le (embedding i) (bad i)

/-! ## Collision counting -/

def equalAt [Fintype X] [DecidableEq X] {n : ℕ} (i j : Fin n) :
    Finset (Fin n → X) :=
  Finset.univ.filter fun f ↦ f i = f j

@[simp] theorem mem_equalAt [Fintype X] [DecidableEq X] {n : ℕ}
    {i j : Fin n} {f : Fin n → X} :
    f ∈ equalAt i j ↔ f i = f j := by
  simp [equalAt]

theorem card_equalAt_le [Fintype X] [DecidableEq X] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    (equalAt (X := X) i j).card ≤ Fintype.card X ^ (n - 1) := by
  let E := ↥(equalAt (X := X) i j)
  let R := {k : Fin n // k ≠ j} → X
  let restrict : E → R := fun f k ↦ f.1 k.1
  have hrestrict : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext k
    by_cases hkj : k = j
    · subst k
      have hfij : f.1 i = f.1 j := mem_equalAt.mp f.2
      have hgif : g.1 i = g.1 j := mem_equalAt.mp g.2
      calc
        f.1 j = f.1 i := hfij.symm
        _ = g.1 i := congrFun hfg ⟨i, hij⟩
        _ = g.1 j := hgif
    · exact congrFun hfg ⟨k, hkj⟩
  have hE : Fintype.card E = (equalAt (X := X) i j).card := by
    exact Fintype.card_coe _
  have hR : Fintype.card R = Fintype.card X ^ (n - 1) := by
    simp [R, Fintype.card_subtype_compl]
  rw [← hE, ← hR]
  exact Fintype.card_le_of_injective restrict hrestrict

def collisionTuples [Fintype X] [DecidableEq X] (n : ℕ) :
    Finset (Fin n → X) :=
  Finset.univ.filter fun f ↦ ¬ Function.Injective f

@[simp] theorem mem_collisionTuples [Fintype X] [DecidableEq X] {n : ℕ}
    {f : Fin n → X} :
    f ∈ collisionTuples (X := X) n ↔ ¬ Function.Injective f := by
  simp [collisionTuples]

theorem collisionTuples_subset_biUnion [Fintype X] [DecidableEq X] (n : ℕ) :
    collisionTuples (X := X) n ⊆
      (Finset.univ : Finset (Fin n × Fin n)).biUnion
        (fun p ↦ if p.1 = p.2 then ∅ else equalAt (X := X) p.1 p.2) := by
  intro f hf
  rw [mem_collisionTuples] at hf
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hfij, hij⟩ := hf
  exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, by
    simp only [hij, if_false, mem_equalAt]
    exact hfij⟩

theorem collisionTuples_card_le [Fintype X] [DecidableEq X] (n : ℕ) :
    (collisionTuples (X := X) n).card ≤
      n * n * (Fintype.card X ^ (n - 1)) := by
  classical
  calc
    (collisionTuples (X := X) n).card ≤
        ((Finset.univ : Finset (Fin n × Fin n)).biUnion
          (fun p ↦ if p.1 = p.2 then ∅ else equalAt (X := X) p.1 p.2)).card :=
      Finset.card_le_card (collisionTuples_subset_biUnion n)
    _ ≤ ∑ p : Fin n × Fin n,
          (if p.1 = p.2 then ∅ else equalAt (X := X) p.1 p.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin n × Fin n, Fintype.card X ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.1 = p.2
      · simp [h]
      · simpa [h] using card_equalAt_le (X := X) p.1 p.2 h
    _ = n * n * (Fintype.card X ^ (n - 1)) := by simp [mul_assoc]

/-! ## Avoiding a family of bad events and all collisions -/

theorem exists_injective_avoiding_of_card_add_lt
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (n : ℕ) (event : ι → (Fin n → X) → Prop)
    [∀ i, DecidablePred (event i)]
    (hsmall :
      (Finset.univ.filter fun f ↦ ∃ i, event i f).card +
          (collisionTuples (X := X) n).card < Fintype.card X ^ n) :
    ∃ f : Fin n → X, Function.Injective f ∧ ∀ i, ¬ event i f := by
  classical
  let bad : Finset (Fin n → X) :=
    (Finset.univ.filter fun f ↦ ∃ i, event i f) ∪ collisionTuples (X := X) n
  have hbad : bad.card < Fintype.card X ^ n := by
    exact (Finset.card_union_le _ _).trans_lt hsmall
  have hfilter :
      (Finset.univ.filter fun f : Fin n → X ↦ f ∈ bad) = bad := by
    ext f
    simp
  have hfiltered :
      (Finset.univ.filter fun f : Fin n → X ↦ f ∈ bad).card <
        Fintype.card X ^ n := by
    rw [hfilter]
    exact hbad
  obtain ⟨f, hf⟩ := exists_not_of_filter_card_lt n (fun f ↦ f ∈ bad) hfiltered
  refine ⟨f, ?_, ?_⟩
  · by_contra hnot
    exact hf (Finset.mem_union_right _ (mem_collisionTuples.mpr hnot))
  · intro i hi
    exact hf (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ f, ⟨i, hi⟩⟩))

theorem exists_injective_avoiding_of_bounds
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (n B : ℕ) (event : ι → (Fin n → X) → Prop)
    [∀ i, DecidablePred (event i)]
    (hevent : ∀ i, (Finset.univ.filter (event i)).card ≤ B)
    (hsmall : Fintype.card ι * B +
        n * n * (Fintype.card X ^ (n - 1)) < Fintype.card X ^ n) :
    ∃ f : Fin n → X, Function.Injective f ∧ ∀ i, ¬ event i f := by
  apply exists_injective_avoiding_of_card_add_lt n event
  exact add_le_add (card_filter_exists_le_mul n B event hevent)
    (collisionTuples_card_le n) |>.trans_lt hsmall

/-- Version of the selection lemma with a separate cardinality budget for
each event. -/
theorem exists_injective_avoiding_of_sum_bounds
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (n : ℕ) (event : ι → (Fin n → X) → Prop)
    [∀ i, DecidablePred (event i)] (B : ι → ℕ)
    (hevent : ∀ i, (Finset.univ.filter (event i)).card ≤ B i)
    (hsmall : (∑ i : ι, B i) +
        n * n * (Fintype.card X ^ (n - 1)) < Fintype.card X ^ n) :
    ∃ f : Fin n → X, Function.Injective f ∧ ∀ i, ¬ event i f := by
  apply exists_injective_avoiding_of_card_add_lt n event
  have hunion :
      (Finset.univ.filter fun f : Fin n → X ↦ ∃ i, event i f).card ≤
        ∑ i : ι, B i := by
    exact (card_filter_exists_le_sum n event).trans
      (Finset.sum_le_sum fun i hi ↦ hevent i)
  exact (add_le_add hunion (collisionTuples_card_le n)).trans_lt hsmall

/-! ## Choice-set (binomial) union bound -/

/-- The tuples on which every event indexed by `s` occurs. -/
def allEvents [Fintype X] [DecidableEq X] {n : ℕ}
    (event : Fin n → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)]
    (s : Finset (Fin n)) : Finset (Fin n → X) :=
  Finset.univ.filter fun f ↦ ∀ i ∈ s, event i f

@[simp] theorem mem_allEvents [Fintype X] [DecidableEq X] {n : ℕ}
    (event : Fin n → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)]
    {s : Finset (Fin n)} {f : Fin n → X} :
    f ∈ allEvents event s ↔ ∀ i ∈ s, event i f := by
  simp [allEvents]

/-- If at least `t` stages are bad, some `t`-element choice of stages is bad.
This is the deterministic core of the binomial tail bound. -/
theorem atLeast_subset_choiceUnion [Fintype X] [DecidableEq X] {n t : ℕ}
    (event : Fin n → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)] :
    (Finset.univ.filter fun f ↦
        t ≤ (Finset.univ.filter fun i ↦ event i f).card) ⊆
      ((Finset.univ : Finset (Fin n)).powersetCard t).biUnion
        (allEvents event) := by
  intro f hf
  rw [Finset.mem_filter] at hf
  let bad := Finset.univ.filter fun i ↦ event i f
  obtain ⟨s, hsbad, hscard⟩ := Finset.exists_subset_card_eq hf.2
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_powersetCard.mpr ⟨?_, hscard⟩, ?_⟩
  · exact hsbad.trans (Finset.filter_subset _ _)
  · rw [mem_allEvents]
    intro i hi
    exact (Finset.mem_filter.mp (hsbad hi)).2

theorem card_atLeast_le_choice_sum [Fintype X] [DecidableEq X] {n t : ℕ}
    (event : Fin n → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)] :
    (Finset.univ.filter fun f ↦
        t ≤ (Finset.univ.filter fun i ↦ event i f).card).card ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
        (allEvents event s).card := by
  calc
    _ ≤ (((Finset.univ : Finset (Fin n)).powersetCard t).biUnion
        (allEvents event)).card :=
      Finset.card_le_card (atLeast_subset_choiceUnion event)
    _ ≤ _ := Finset.card_biUnion_le

theorem card_atLeast_le_choose_mul [Fintype X] [DecidableEq X] {n t C : ℕ}
    (event : Fin n → (Fin n → X) → Prop) [∀ i, DecidablePred (event i)]
    (hintersection : ∀ s ⊆ (Finset.univ : Finset (Fin n)), s.card = t →
      (allEvents event s).card ≤ C) :
    (Finset.univ.filter fun f ↦
        t ≤ (Finset.univ.filter fun i ↦ event i f).card).card ≤
      Nat.choose n t * C := by
  calc
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
        (allEvents event s).card := card_atLeast_le_choice_sum event
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin n)).powersetCard t, C := by
      apply Finset.sum_le_sum
      intro s hs
      exact hintersection s (Finset.mem_powersetCard.mp hs).1
        (Finset.mem_powersetCard.mp hs).2
    _ = Nat.choose n t * C := by simp

/-! ## Adaptive prefix-stage bounds -/

/-- The event that the choice at stage `i` is bad, where badness may depend
on the complete history strictly before `i`. -/
def prefixStageEvent {n : ℕ} (stepBad : List X → X → Prop)
    (i : Fin n) (f : Fin n → X) : Prop :=
  stepBad ((List.ofFn f).take i.val) (f i)

instance prefixStageEvent.decidable {n : ℕ} (stepBad : List X → X → Prop)
    [∀ history, DecidablePred (stepBad history)] (i : Fin n) :
    DecidablePred (prefixStageEvent stepBad i) :=
  fun f ↦ inferInstanceAs (Decidable
    (stepBad ((List.ofFn f).take i.val) (f i)))

private theorem ofFn_take_castSucc {n : ℕ} (f : Fin (n + 1) → X) (i : Fin n) :
    (List.ofFn f).take i.val =
      (List.ofFn fun j : Fin n ↦ f j.castSucc).take i.val := by
  rw [List.ofFn_succ_last]
  simp [Nat.le_of_lt i.isLt]

private theorem ofFn_take_last {n : ℕ} (f : Fin (n + 1) → X) :
    (List.ofFn f).take n = List.ofFn fun j : Fin n ↦ f j.castSucc := by
  rw [List.ofFn_succ_last]
  simp

private theorem castSucc_preimage_card {n : ℕ} (s : Finset (Fin (n + 1))) :
    let s₀ := (Finset.univ : Finset (Fin n)).filter fun i ↦ i.castSucc ∈ s
    s₀.card + (if Fin.last n ∈ s then 1 else 0) = s.card := by
  classical
  dsimp
  let e : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩
  have himage :
      ((Finset.univ : Finset (Fin n)).filter fun i ↦ i.castSucc ∈ s).map e =
        s.erase (Fin.last n) := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last i, (Finset.mem_filter.mp hi).2⟩
    · intro hj
      have hj' := Finset.mem_erase.mp hj
      let i : Fin n := j.castLT (Fin.val_lt_last hj'.1)
      apply Finset.mem_map.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, ?_⟩
      · simpa [i] using hj'.2
      · apply Fin.ext
        rfl
  have hcard₀ :
      ((Finset.univ : Finset (Fin n)).filter fun i ↦ i.castSucc ∈ s).card =
        (s.erase (Fin.last n)).card := by
    rw [← himage, Finset.card_map]
  rw [hcard₀]
  by_cases hlast : Fin.last n ∈ s
  · rw [if_pos hlast]
    exact Finset.card_erase_add_one hlast
  · rw [if_neg hlast, Finset.erase_eq_of_notMem hlast]
    simp

/-- Chain rule for a prescribed collection of adaptive bad stages.  At a
selected stage there are at most `B` possible bad next values; at every other
stage there are at most `|X|` values. -/
theorem all_prefixStageEvents_card_le [Fintype X] [DecidableEq X]
    (stepBad : List X → X → Prop) (B : ℕ)
    [∀ history, DecidablePred (stepBad history)]
    (hstep : ∀ history : List X,
      (Finset.univ.filter fun x : X ↦ stepBad history x).card ≤ B)
    {n : ℕ} (s : Finset (Fin n)) :
    (allEvents (prefixStageEvent stepBad) s).card ≤
      B ^ s.card * Fintype.card X ^ (n - s.card) := by
  classical
  induction n with
  | zero =>
      have hs : s = ∅ := by
        ext i
        exact Fin.elim0 i
      subst s
      simp [allEvents]
  | succ n ih =>
      let dropLast : (Fin (n + 1) → X) → (Fin n → X) :=
        fun f i ↦ f i.castSucc
      let s₀ : Finset (Fin n) :=
        Finset.univ.filter fun i ↦ i.castSucc ∈ s
      let S : Finset (Fin (n + 1) → X) :=
        allEvents (prefixStageEvent stepBad) s
      let T : Finset (Fin n → X) :=
        allEvents (prefixStageEvent stepBad) s₀
      have hmaps : ∀ f ∈ S, dropLast f ∈ T := by
        intro f hf
        rw [mem_allEvents] at hf ⊢
        intro i hi
        have his : i.castSucc ∈ s := (Finset.mem_filter.mp hi).2
        have hfi := hf i.castSucc his
        rw [prefixStageEvent] at hfi ⊢
        change stepBad
          ((List.ofFn fun j : Fin n ↦ f j.castSucc).take i.val) (f i.castSucc)
        rw [← ofFn_take_castSucc]
        exact hfi
      have hfiber_injective (p : Fin n → X) :
          Set.InjOn (fun f : Fin (n + 1) → X ↦ f (Fin.last n))
            ({f ∈ S | dropLast f = p} : Finset (Fin (n + 1) → X)) := by
        intro f hf g hg hlast
        have hdrop : dropLast f = dropLast g :=
          (Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm
        funext i
        refine Fin.lastCases hlast ?_ i
        intro j
        exact congrFun hdrop j
      by_cases hsLast : Fin.last n ∈ s
      · have hfiber : ∀ p ∈ T,
            ({f ∈ S | dropLast f = p} : Finset (Fin (n + 1) → X)).card ≤ B := by
          intro p hp
          let F : Finset (Fin (n + 1) → X) := {f ∈ S | dropLast f = p}
          have himage : F.image (fun f ↦ f (Fin.last n)) ⊆
              Finset.univ.filter (fun x : X ↦ stepBad (List.ofFn p) x) := by
            intro x hx
            obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hx
            have hfS : f ∈ S := (Finset.mem_filter.mp hf).1
            have hdrop : dropLast f = p := (Finset.mem_filter.mp hf).2
            change (fun j : Fin n ↦ f j.castSucc) = p at hdrop
            have hlastEvent : prefixStageEvent stepBad (Fin.last n) f :=
              (mem_allEvents (prefixStageEvent stepBad)).mp hfS
                (Fin.last n) hsLast
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [prefixStageEvent] at hlastEvent
            have hhistory : (List.ofFn f).take n = List.ofFn p := by
              rw [ofFn_take_last, hdrop]
            exact hhistory ▸ hlastEvent
          calc
            F.card = (F.image fun f ↦ f (Fin.last n)).card :=
              (Finset.card_image_iff.mpr (hfiber_injective p)).symm
            _ ≤ (Finset.univ.filter
                (fun x : X ↦ stepBad (List.ofFn p) x)).card :=
              Finset.card_le_card himage
            _ ≤ B := hstep (List.ofFn p)
        have hST : S.card ≤ B * T.card :=
          Finset.card_le_mul_card_image_of_maps_to hmaps B hfiber
        have hT := ih s₀
        have hcard := castSucc_preimage_card s
        simp only [hsLast, if_true] at hcard
        dsimp only [S, T] at hST
        calc
          (allEvents (prefixStageEvent stepBad) s).card ≤
              B * (allEvents (prefixStageEvent stepBad) s₀).card := hST
          _ ≤ B * (B ^ s₀.card * Fintype.card X ^ (n - s₀.card)) :=
            Nat.mul_le_mul_left B hT
          _ = B ^ s.card * Fintype.card X ^ (n + 1 - s.card) := by
            rw [← hcard]
            have hk : s₀.card ≤ n := by
              simpa using Finset.card_le_univ s₀
            have hsub : n + 1 - (s₀.card + 1) = n - s₀.card := by omega
            rw [hsub, pow_succ]
            ac_rfl
      · have hfiber : ∀ p ∈ T,
            ({f ∈ S | dropLast f = p} : Finset (Fin (n + 1) → X)).card ≤
              Fintype.card X := by
          intro p hp
          let F : Finset (Fin (n + 1) → X) := {f ∈ S | dropLast f = p}
          calc
            F.card = (F.image fun f ↦ f (Fin.last n)).card :=
              (Finset.card_image_iff.mpr (hfiber_injective p)).symm
            _ ≤ (Finset.univ : Finset X).card :=
              Finset.card_le_card (Finset.subset_univ _)
            _ = Fintype.card X := Finset.card_univ
        have hST : S.card ≤ Fintype.card X * T.card :=
          Finset.card_le_mul_card_image_of_maps_to hmaps (Fintype.card X) hfiber
        have hT := ih s₀
        have hcard := castSucc_preimage_card s
        simp only [hsLast, if_false, add_zero] at hcard
        dsimp only [S, T] at hST
        calc
          (allEvents (prefixStageEvent stepBad) s).card ≤
              Fintype.card X * (allEvents (prefixStageEvent stepBad) s₀).card := hST
          _ ≤ Fintype.card X *
              (B ^ s₀.card * Fintype.card X ^ (n - s₀.card)) :=
            Nat.mul_le_mul_left (Fintype.card X) hT
          _ = B ^ s.card * Fintype.card X ^ (n + 1 - s.card) := by
            rw [← hcard]
            have hk : s₀.card ≤ n := by
              simpa using Finset.card_le_univ s₀
            have hsub : n + 1 - s₀.card = (n - s₀.card) + 1 := by omega
            rw [hsub, pow_succ]
            ac_rfl

/-- Binomial/choice-set bound for adaptive bad stages. -/
theorem card_atLeast_prefixStageBad_le [Fintype X] [DecidableEq X]
    (stepBad : List X → X → Prop) (q b B : ℕ)
    [∀ history, DecidablePred (stepBad history)]
    (hstep : ∀ history : List X,
      (Finset.univ.filter fun x : X ↦ stepBad history x).card ≤ B) :
    (Finset.univ.filter fun f : Fin q → X ↦
        b ≤ (Finset.univ.filter fun i : Fin q ↦
          prefixStageEvent stepBad i f).card).card ≤
      Nat.choose q b * (B ^ b * Fintype.card X ^ (q - b)) := by
  apply card_atLeast_le_choose_mul (C := B ^ b * Fintype.card X ^ (q - b))
  intro s hs hscard
  simpa [hscard] using all_prefixStageEvents_card_le stepBad B hstep s

end FiniteProbability

end Erdos54
