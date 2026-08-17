/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos847.LineCounting

/-!
# Disjoint-block Hales--Jewett candidates

This file packages a useful amplification of the finite Hales--Jewett theorem.
The coordinate type `Fin t × J` is split into `t` disjoint copies of `J`.  A
candidate line moves inside one copy, is a prescribed Hales--Jewett line there,
and is fixed arbitrarily on all other copies.

The encoding is injective.  Consequently the candidate family has an exact
product count.  Every colouring makes many candidates monochromatic, while a
fixed cube point belongs to at most `t * 2 ^ card J` candidates.
-/

namespace Erdos847BlockCandidates

open Function Set
open Combinatorics
open Erdos847LineCounting

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w

variable {A : Type u} {J : Type v} {K : Type w}
variable [Fintype A] [Fintype J]

/-- The fixed coordinates outside the selected block. -/
abbrev OutsideIndex (t : ℕ) (j : Fin t) := {k : Fin t // k ≠ j}

/-- A fixed word on every block other than `j`. -/
abbrev OutsideWord (A : Type u) (J : Type v) (t : ℕ) (j : Fin t) :=
  OutsideIndex t j → J → A

/-- A frame consists of an active block and the fixed word outside it. -/
abbrev FrameCode (A : Type u) (J : Type v) (t : ℕ) :=
  Σ j : Fin t, OutsideWord A J t j

/-- Candidate-line codes relative to a prescribed finite internal line family `S`. -/
abbrev CandidateCode (A : Type u) (J : Type v) (t : ℕ)
    (S : Finset (Line A J)) :=
  Σ j : Fin t, OutsideWord A J t j × ↑S

/-- Fill the active block of a frame by a word on `J`. -/
def framePoint {t : ℕ} (f : FrameCode A J t) (x : J → A) : Fin t × J → A :=
  fun iq ↦ if h : iq.1 = f.1 then x iq.2 else f.2 ⟨iq.1, h⟩ iq.2

@[simp] lemma framePoint_active {t : ℕ} (f : FrameCode A J t) (x : J → A)
    (q : J) : framePoint f x (f.1, q) = x q := by
  simp [framePoint]

@[simp] lemma framePoint_outside {t : ℕ} (f : FrameCode A J t) (x : J → A)
    (k : Fin t) (q : J) (hk : k ≠ f.1) :
    framePoint f x (k, q) = f.2 ⟨k, hk⟩ q := by
  simp [framePoint, hk]

/-- Decode a candidate into an ambient combinatorial line. -/
def encodedLine {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) : Line A (Fin t × J) where
  idxFun iq := if h : iq.1 = c.1 then c.2.2.1.idxFun iq.2
    else some (c.2.1 ⟨iq.1, h⟩ iq.2)
  proper := by
    obtain ⟨q, hq⟩ := c.2.2.1.proper
    exact ⟨(c.1, q), by simp [hq]⟩

@[simp] lemma encodedLine_idxFun_active {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (q : J) :
    (encodedLine c).idxFun (c.1, q) = c.2.2.1.idxFun q := by
  simp [encodedLine]

@[simp] lemma encodedLine_idxFun_outside {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (k : Fin t) (q : J) (hk : k ≠ c.1) :
    (encodedLine c).idxFun (k, q) = some (c.2.1 ⟨k, hk⟩ q) := by
  simp [encodedLine, hk]

@[simp] lemma encodedLine_apply {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (a : A) :
    encodedLine c a = framePoint ⟨c.1, c.2.1⟩ (c.2.2.1 a) := by
  funext iq
  by_cases h : iq.1 = c.1
  · simp [Line.coe_apply, encodedLine, framePoint, h]
  · simp [Line.coe_apply, encodedLine, framePoint, h]

/-- The block/outside-word/internal-line encoding loses no information. -/
theorem encodedLine_injective {t : ℕ} {S : Finset (Line A J)} :
    Function.Injective (encodedLine : CandidateCode A J t S → Line A (Fin t × J)) := by
  rintro ⟨j, w, l⟩ ⟨k, v, m⟩ hline
  have hjk : j = k := by
    obtain ⟨q, hq⟩ := l.1.proper
    have hidx := congrArg (fun L : Line A (Fin t × J) ↦ L.idxFun (j, q)) hline
    by_contra hne
    simp [encodedLine, hq, hne] at hidx
  subst k
  have hlm : l = m := by
    apply Subtype.ext
    apply Line.ext
    funext q
    have hidx := congrArg (fun L : Line A (Fin t × J) ↦ L.idxFun (j, q)) hline
    simpa [encodedLine] using hidx
  subst m
  have hwv : w = v := by
    funext k' q
    have hidx := congrArg
      (fun L : Line A (Fin t × J) ↦ L.idxFun (k'.1, q)) hline
    have hsome : some (w k' q) = some (v k' q) := by
      simpa [encodedLine, k'.2] using hidx
    exact Option.some.inj hsome
  subst v
  rfl

/-- The finite family of all encoded candidates. -/
noncomputable def candidateLines (t : ℕ) (S : Finset (Line A J)) :
    Finset (Line A (Fin t × J)) :=
  Finset.univ.image (encodedLine (S := S))

@[simp] lemma mem_candidateLines {t : ℕ} {S : Finset (Line A J)}
    {l : Line A (Fin t × J)} :
    l ∈ candidateLines t S ↔ ∃ c : CandidateCode A J t S, encodedLine c = l := by
  simp [candidateLines]

/-- There are `t - 1` blocks outside a selected block. -/
lemma card_outsideIndex {t : ℕ} (j : Fin t) :
    Fintype.card (OutsideIndex t j) = t - 1 := by
  have h := Fintype.card_subtype_compl (fun k : Fin t ↦ k = j)
  simp only [Fintype.card_fin] at h
  have heq : Fintype.card {k : Fin t // k = j} = 1 := by simp
  rw [heq] at h
  simpa [OutsideIndex] using h

/-- Exact number of outside words. -/
lemma card_outsideWord {t : ℕ} (j : Fin t) :
    Fintype.card (OutsideWord A J t j) =
      Fintype.card A ^ (Fintype.card J * (t - 1)) := by
  simp only [OutsideWord, Fintype.card_fun, card_outsideIndex]
  rw [pow_mul]

/-- Exact number of frames. -/
lemma card_frameCode (t : ℕ) :
    Fintype.card (FrameCode A J t) =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) := by
  rw [Fintype.card_sigma]
  simp_rw [card_outsideWord]
  simp

/-- Exact number of candidate codes. -/
lemma card_candidateCode (t : ℕ) (S : Finset (Line A J)) :
    Fintype.card (CandidateCode A J t S) =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) * S.card := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_outsideWord, Fintype.card_coe]
  simp
  ring

/-- Exact candidate-family cardinality. -/
theorem card_candidateLines (t : ℕ) (S : Finset (Line A J)) :
    (candidateLines t S).card =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) * S.card := by
  rw [candidateLines, Finset.card_image_of_injective _ encodedLine_injective,
    Finset.card_univ, card_candidateCode]

/-- A finite internal family contains at most as many lines as raw `Option A` words. -/
lemma card_lineFamily_le (S : Finset (Line A J)) :
    S.card ≤ (Fintype.card A + 1) ^ Fintype.card J := by
  have hinj : Set.InjOn Line.idxFun (S : Set (Line A J)) := by
    intro l _ m _ h
    cases l
    cases m
    simp_all
  calc
    S.card = (S.image Line.idxFun).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (J → Option A)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card A + 1) ^ Fintype.card J := by simp [Fintype.card_fun]

/-- Nonempty internal families give the basic lower bound on candidates. -/
theorem candidateLines_card_lower {t : ℕ} {S : Finset (Line A J)}
    (hS : S.Nonempty) :
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) ≤
      (candidateLines t S).card := by
  rw [card_candidateLines]
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  simpa using Nat.mul_le_mul_left
    (t * Fintype.card A ^ (Fintype.card J * (t - 1))) hcard

/-- Crude raw-word upper bound on the candidate family. -/
theorem candidateLines_card_upper (t : ℕ) (S : Finset (Line A J)) :
    (candidateLines t S).card ≤
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) *
        (Fintype.card A + 1) ^ Fintype.card J := by
  rw [card_candidateLines]
  exact Nat.mul_le_mul_left _ (card_lineFamily_le S)

/-! ## Monochromatic candidates -/

/-- Candidates which are monochromatic for a given colouring. -/
noncomputable def monoCandidateLines {t : ℕ} (S : Finset (Line A J))
    (color : (Fin t × J → A) → K) : Finset (Line A (Fin t × J)) :=
  (candidateLines t S).filter fun l ↦ l.IsMono color

@[simp] lemma mem_monoCandidateLines {t : ℕ} {S : Finset (Line A J)}
    {color : (Fin t × J → A) → K} {l : Line A (Fin t × J)} :
    l ∈ monoCandidateLines S color ↔ l ∈ candidateLines t S ∧ l.IsMono color := by
  simp [monoCandidateLines]

/-- Choose a monochromatic internal line for the colouring induced by a frame. -/
noncomputable def chosenInternal {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) : ↑S :=
  ⟨Classical.choose (hHJ (fun x ↦ color (framePoint f x))),
    (Classical.choose_spec (hHJ (fun x ↦ color (framePoint f x)))).1⟩

lemma chosenInternal_mono {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    (chosenInternal hHJ color f).1.IsMono (fun x ↦ color (framePoint f x)) :=
  (Classical.choose_spec (hHJ (fun x ↦ color (framePoint f x)))).2

/-- Candidate selected from a frame by internal Hales--Jewett. -/
noncomputable def chosenCandidate {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    CandidateCode A J t S := ⟨f.1, f.2, chosenInternal hHJ color f⟩

lemma chosenCandidate_mono {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    (encodedLine (chosenCandidate hHJ color f)).IsMono color := by
  rcases chosenInternal_mono hHJ color f with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro a
  simpa [chosenCandidate, encodedLine_apply] using hk a

lemma chosenCandidate_injective {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) :
    Function.Injective (fun f : FrameCode A J t ↦
      encodedLine (chosenCandidate hHJ color f)) := by
  rintro ⟨j, w⟩ ⟨k, v⟩ h
  have hcode := encodedLine_injective h
  have hjk : j = k := congrArg Sigma.fst hcode
  subst k
  have hwv : w = v := by
    funext k' q
    have hidx := congrArg
      (fun L : Line A (Fin t × J) ↦ L.idxFun (k'.1, q)) h
    have hsome : some (w k' q) = some (v k' q) := by
      simpa [chosenCandidate, encodedLine, k'.2] using hidx
    exact Option.some.inj hsome
  subst v
  rfl

/-- Every colouring has at least one monochromatic candidate per frame. -/
theorem monoCandidateLines_card_lower {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) :
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) ≤
      (monoCandidateLines S color).card := by
  let f : FrameCode A J t → Line A (Fin t × J) :=
    fun frame ↦ encodedLine (chosenCandidate hHJ color frame)
  have himage : (Finset.univ : Finset (FrameCode A J t)).image f ⊆
      monoCandidateLines S color := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨frame, -, rfl⟩
    exact mem_monoCandidateLines.mpr ⟨mem_candidateLines.mpr
      ⟨chosenCandidate hHJ color frame, rfl⟩, chosenCandidate_mono hHJ color frame⟩
  calc
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) =
        (Finset.univ : Finset (FrameCode A J t)).card := by
          rw [Finset.card_univ, card_frameCode]
    _ = ((Finset.univ : Finset (FrameCode A J t)).image f).card :=
      (Finset.card_image_of_injective _ (chosenCandidate_injective hHJ color)).symm
    _ ≤ (monoCandidateLines S color).card := Finset.card_le_card himage

/-! ## Point degrees -/

/-- Candidate codes whose decoded line contains `x`. -/
noncomputable def incidentCandidateCodes {t : ℕ} (S : Finset (Line A J))
    (x : Fin t × J → A) : Finset (CandidateCode A J t S) :=
  Finset.univ.filter fun c ↦ ∃ a, encodedLine c a = x

/-- Number of candidates through a point. -/
noncomputable def candidateDegree {t : ℕ} (S : Finset (Line A J))
    (x : Fin t × J → A) : ℕ :=
  ((candidateLines t S).filter fun l ↦ ∃ a, l a = x).card

lemma candidateDegree_eq_incidentCodes_card {t : ℕ} (S : Finset (Line A J))
    (x : Fin t × J → A) :
    candidateDegree S x = (incidentCandidateCodes S x).card := by
  rw [candidateDegree, candidateLines, incidentCandidateCodes]
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ encodedLine_injective

/-- A line through a fixed point is determined by its moving-coordinate set. -/
lemma line_eq_of_movingSet_eq_of_point {I : Type*} [Fintype I]
    {l m : Line A I} {x : I → A}
    (hmove : movingSet l = movingSet m)
    (hl : ∃ a, l a = x) (hm : ∃ a, m a = x) : l = m := by
  rcases hl with ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  apply Line.ext
  funext i
  have hnone : l.idxFun i = none ↔ m.idxFun i = none := by
    rw [← mem_movingSet, ← mem_movingSet, hmove]
  cases hlopt : l.idxFun i with
  | none => exact (hnone.mp hlopt).symm
  | some c =>
      cases hmopt : m.idxFun i with
      | none => exact ((Option.some_ne_none c) (hlopt.symm.trans (hnone.mpr hmopt))).elim
      | some d =>
          have hc := congrFun ha i
          have hd := congrFun hb i
          simp only [Line.coe_apply, hlopt, hmopt, Option.getD_some] at hc hd
          exact congrArg some (hc.trans hd.symm)

/-- For incident candidates, the active block and internal moving set determine the code. -/
lemma blockSupport_injectiveOn_incident {t : ℕ} (S : Finset (Line A J))
    (x : Fin t × J → A) :
    Set.InjOn (fun c : CandidateCode A J t S ↦ (c.1, movingSet c.2.2.1))
      (incidentCandidateCodes S x : Set (CandidateCode A J t S)) := by
  intro c hc d hd heq
  have hblock : c.1 = d.1 := congrArg Prod.fst heq
  have hsupp : movingSet c.2.2.1 = movingSet d.2.2.1 := congrArg Prod.snd heq
  rcases Finset.mem_filter.mp hc with ⟨-, hcpoint⟩
  rcases Finset.mem_filter.mp hd with ⟨-, hdpoint⟩
  apply encodedLine_injective
  apply line_eq_of_movingSet_eq_of_point (x := x) _ hcpoint hdpoint
  ext iq
  simp only [mem_movingSet]
  by_cases hi : iq.1 = c.1
  · have hi' : iq.1 = d.1 := hi.trans hblock
    simpa [encodedLine, hi, hi', hblock] using
      congrArg (fun U : Finset J ↦ iq.2 ∈ U) hsupp
  · have hi' : iq.1 ≠ d.1 := fun h ↦ hi (h.trans hblock.symm)
    simp [encodedLine, hi, hi']

/-- Per-point degree bound for the amplified candidate family. -/
theorem candidateDegree_le (t : ℕ) (S : Finset (Line A J))
    (x : Fin t × J → A) :
    candidateDegree S x ≤ t * 2 ^ Fintype.card J := by
  rw [candidateDegree_eq_incidentCodes_card]
  let f : CandidateCode A J t S → Fin t × Finset J :=
    fun c ↦ (c.1, movingSet c.2.2.1)
  calc
    (incidentCandidateCodes S x).card =
        ((incidentCandidateCodes S x).image f).card :=
      (Finset.card_image_of_injOn (blockSupport_injectiveOn_incident S x)).symm
    _ ≤ (Finset.univ : Finset (Fin t × Finset J)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = t * 2 ^ Fintype.card J := by simp

end Erdos847BlockCandidates
