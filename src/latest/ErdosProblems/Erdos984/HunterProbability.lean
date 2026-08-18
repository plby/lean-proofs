/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Card

/-!
# Finite probability lemmas for Hunter's construction

The random radius labels in Hunter's proof live in a finite function space.
We formulate their independence by exact counting, avoiding any measurability
overhead.  Distinct queried coordinates contribute independent factors.
-/

open scoped BigOperators

namespace Erdos984

/-- Assignments which avoid one prescribed value at every coordinate in
`S`. -/
def AvoidingAssignments {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :=
  {f : ι → κ // ∀ i ∈ S, f i ≠ target i}

instance {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    Fintype (AvoidingAssignments S target) := by
  unfold AvoidingAssignments
  infer_instance

/-- Separate the constrained and unconstrained coordinates of an avoiding
assignment. -/
def avoidingAssignmentsEquiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    AvoidingAssignments S target ≃
      ((i : ↥S) → {x : κ // x ≠ target i}) ×
        ({i : ι // i ∉ S} → κ) where
  toFun f :=
    ⟨fun i => ⟨f.1 i, f.2 i i.2⟩, fun i => f.1 i⟩
  invFun g := by
    refine ⟨fun i => if hi : i ∈ S then (g.1 ⟨i, hi⟩).1 else g.2 ⟨i, hi⟩, ?_⟩
    intro i hi
    simp [hi, (g.1 ⟨i, hi⟩).2]
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  right_inv g := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simp [i.2]
    · funext i
      simp [i.2]

lemma card_subtype_ne {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ) :
    Fintype.card {x : κ // x ≠ a} = Fintype.card κ - 1 := by
  calc
    Fintype.card {x : κ // x ≠ a} =
        Fintype.card κ - Fintype.card {x : κ // x = a} :=
      Fintype.card_subtype_compl (fun x : κ => x = a)
    _ = Fintype.card κ - 1 := by simp

lemma card_subtype_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    Fintype.card {i : ι // i ∉ S} = Fintype.card ι - S.card := by
  calc
    Fintype.card {i : ι // i ∉ S} =
        Fintype.card ι - Fintype.card {i : ι // i ∈ S} :=
      Fintype.card_subtype_compl (fun i : ι => i ∈ S)
    _ = Fintype.card ι - S.card := by simp

/-- Exact count of assignments which miss prescribed labels at distinct
coordinates. -/
lemma card_avoidingAssignments {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    Fintype.card (AvoidingAssignments S target) =
      (Fintype.card κ - 1) ^ S.card *
        Fintype.card κ ^ (Fintype.card ι - S.card) := by
  rw [Fintype.card_congr (avoidingAssignmentsEquiv S target)]
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  simp_rw [card_subtype_ne]
  simp

def badLabelings {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    Finset (ι → κ) :=
  Finset.univ.filter fun f => ∀ i ∈ S, f i ≠ target i

def badLabelingsEquiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    ↥(badLabelings S target) ≃ AvoidingAssignments S target where
  toFun f := ⟨f.1, by simpa [badLabelings] using f.2⟩
  invFun f := ⟨f.1, by simpa [badLabelings] using f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_badLabelings {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (target : ι → κ) :
    (badLabelings S target).card =
      (Fintype.card κ - 1) ^ S.card *
        Fintype.card κ ^ (Fintype.card ι - S.card) := by
  rw [← Fintype.card_coe, Fintype.card_congr (badLabelingsEquiv S target)]
  exact card_avoidingAssignments S target

/-- The elementary exponential estimate used for the probability that all
`Y` independent radial opportunities miss. -/
lemma independent_miss_le_exp (K Y : ℕ) :
    (1 - 1 / ((K + 1 : ℕ) : ℝ)) ^ Y ≤
      Real.exp (-(Y : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
  have hden : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hone : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hden]
    norm_num
  calc
    (1 - 1 / ((K + 1 : ℕ) : ℝ)) ^ Y ≤
        (Real.exp (-(1 / ((K + 1 : ℕ) : ℝ)))) ^ Y :=
      pow_le_pow_left₀ (sub_nonneg.2 hone)
        (Real.one_sub_le_exp_neg _) Y
    _ = Real.exp ((Y : ℝ) * (-(1 / ((K + 1 : ℕ) : ℝ)))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(Y : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
      congr 1
      field_simp

/-- A finite union of bad subsets cannot cover the sample space if the sum
of their cardinalities is smaller than the sample-space cardinality. -/
lemma exists_avoiding_finite_union {Ω σ : Type*} [Fintype Ω] [Fintype σ]
    (bad : σ → Finset Ω)
    (hcard : ∑ s : σ, (bad s).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ s : σ, ω ∉ bad s := by
  classical
  let U : Finset Ω := Finset.univ.biUnion bad
  have hUcard : U.card < Fintype.card Ω := by
    apply lt_of_le_of_lt Finset.card_biUnion_le
    simpa [U] using hcard
  have hproper : U ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hUcard
    omega
  have hex : ∃ ω : Ω, ω ∉ U := by
    by_contra h
    simp only [not_exists, Decidable.not_not] at h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨ω, hωU⟩ := hex
  refine ⟨ω, ?_⟩
  intro s hωbad
  exact hωU (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hωbad⟩)

/-- Exact finite union-bound form of the independent-label argument.  Every
constraint queries `Y` distinct coordinates and prescribes one successful
label at each.  The displayed strict counting inequality guarantees one
labeling which succeeds for every constraint. -/
lemma exists_labeling_hits_all {ι κ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ]
    (S : σ → Finset ι) (target : σ → ι → κ) (Y : ℕ)
    (hS : ∀ s, (S s).card = Y)
    (hcount : Fintype.card σ *
        ((Fintype.card κ - 1) ^ Y *
          Fintype.card κ ^ (Fintype.card ι - Y)) <
        Fintype.card κ ^ Fintype.card ι) :
    ∃ f : ι → κ, ∀ s : σ, ∃ i ∈ S s, f i = target s i := by
  classical
  let bad : σ → Finset (ι → κ) := fun s => badLabelings (S s) (target s)
  have hbadcard : ∀ s, (bad s).card =
      (Fintype.card κ - 1) ^ Y *
        Fintype.card κ ^ (Fintype.card ι - Y) := by
    intro s
    dsimp [bad]
    rw [card_badLabelings, hS]
  have hsum : ∑ s : σ, (bad s).card < Fintype.card (ι → κ) := by
    simp_rw [hbadcard]
    simpa [Fintype.card_fun] using hcount
  obtain ⟨f, hf⟩ := exists_avoiding_finite_union bad hsum
  refine ⟨f, ?_⟩
  intro s
  have hnot := hf s
  simp only [bad, badLabelings, Finset.mem_filter, Finset.mem_univ, true_and,
    not_forall] at hnot
  obtain ⟨i, hi⟩ := hnot
  simp only [Decidable.not_not] at hi
  exact ⟨i, hi.1, hi.2⟩

end Erdos984
