/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 702.
https://www.erdosproblems.com/forum/thread/702

Informal authors:
- Péter Frankl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos702.md
-/
import Mathlib
import ErdosProblems.Erdos703.Iteration

/-!
# Erdős Problem 702: singleton intersections

The source-correct theorem is eventual in the ground-set size: for every
`k ≥ 4` there is a threshold after which a `k`-uniform family larger than a
two-star contains two members meeting in exactly one point.

The literal stronger all-`n` formulation is false; the named theorem
`not_erdos_702` records the concrete counterexample `n = 5`, `k = 4`.

The detailed mathematical proof and Leanization map are in `tex/702.tex`.
-/

namespace Erdos702

open Finset
open Asymptotics Filter
open scoped BigOperators

/-- A finite family of finite subsets of `Fin n` is `k`-uniform. -/
def IsUniform {n : ℕ} (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, A.card = k

/-- No ordered pair of members, including a member paired with itself, has
intersection of cardinality one. -/
def AvoidsSingleton {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, (A ∩ B).card ≠ 1

/-- The positive conclusion in Erdős Problem 702. -/
def HasSingletonIntersection {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

lemma avoidsSingleton_iff_not_hasSingletonIntersection {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) :
    AvoidsSingleton 𝓕 ↔ ¬ HasSingletonIntersection 𝓕 := by
  constructor
  · intro h ⟨A, hA, B, hB, hAB⟩
    exact h A hA B hB hAB
  · intro h A hA B hB hAB
    exact h ⟨A, hA, B, hB, hAB⟩

/-- The literal all-`n` strengthening that omits Frankl's threshold. -/
def AllNStatement : Prop :=
  ∀ (n k : ℕ) (𝓕 : Finset (Finset (Fin n))),
    4 ≤ k →
    IsUniform k 𝓕 →
    Nat.choose (n - 2) (k - 2) < 𝓕.card →
    HasSingletonIntersection 𝓕

/-- All four-subsets of a five-element set. -/
def allFourSubsetsOfFive : Finset (Finset (Fin 5)) :=
  Finset.univ.filter fun A => A.card = 4

lemma allFourSubsetsOfFive_card : allFourSubsetsOfFive.card = 5 := by
  decide

lemma allFourSubsetsOfFive_uniform : IsUniform 4 allFourSubsetsOfFive := by
  unfold IsUniform
  decide

lemma allFourSubsetsOfFive_large :
    Nat.choose (5 - 2) (4 - 2) < allFourSubsetsOfFive.card := by
  decide

lemma allFourSubsetsOfFive_avoids : AvoidsSingleton allFourSubsetsOfFive := by
  unfold AvoidsSingleton
  decide

/-- **Named main result (counterexample).**  The stronger formulation with no
lower bound on `n` is false already for all four-subsets of `Fin 5`. -/
theorem not_erdos_702 : ¬ (∀ (n k : ℕ) (𝓕 : Finset (Finset (Fin n))),
  4 ≤ k →
  Erdos702.IsUniform k 𝓕 →
  Nat.choose (n - 2) (k - 2) < 𝓕.card →
  Erdos702.HasSingletonIntersection 𝓕) := by
  intro h
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    h 5 4 allFourSubsetsOfFive (by decide) allFourSubsetsOfFive_uniform
      allFourSubsetsOfFive_large
  exact allFourSubsetsOfFive_avoids A hA B hB hAB

/-! ## The eventual theorem interface -/

/-- The sharp two-star bound appearing in Erdős Problem 702. -/
def twoStarBound (n k : ℕ) : ℕ := Nat.choose (n - 2) (k - 2)

/-- The source-correct eventual form of Erdős Problem 702. -/
def EventualStatement : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ 𝓕 : Finset (Finset (Fin n)),
      IsUniform k 𝓕 →
      twoStarBound n k < 𝓕.card →
      HasSingletonIntersection 𝓕

open Finset

def PairwiseDisjointFamily {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → Disjoint A B

def IsDeltaSystem {α : Type*} [DecidableEq α]
    (K : Finset α) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → A ∩ B = K

def sunflowerBound : ℕ → ℕ → ℕ
  | 0, _ => 1
  | r + 1, s => (r + 1) * (s - 1) * sunflowerBound r s

lemma empty_pairwiseDisjointFamily {α : Type*} [DecidableEq α] :
    PairwiseDisjointFamily (∅ : Finset (Finset α)) := by
  simp [PairwiseDisjointFamily]

lemma exists_max_pairwiseDisjoint_subfamily {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) :
    ∃ 𝓜 : Finset (Finset α),
      𝓜 ⊆ 𝓕 ∧ PairwiseDisjointFamily 𝓜 ∧
      ∀ 𝓝 : Finset (Finset α), 𝓝 ⊆ 𝓕 → PairwiseDisjointFamily 𝓝 →
        𝓝.card ≤ 𝓜.card := by
  classical
  let C := 𝓕.powerset.filter PairwiseDisjointFamily
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C, empty_pairwiseDisjointFamily]
  obtain ⟨𝓜, h𝓜C, hmax⟩ := C.exists_max_image Finset.card hC
  refine ⟨𝓜, ?_, ?_, ?_⟩
  · exact (mem_powerset.mp (mem_filter.mp h𝓜C).1)
  · exact (mem_filter.mp h𝓜C).2
  · intro 𝓝 h𝓝sub h𝓝pw
    exact hmax 𝓝 (mem_filter.mpr ⟨mem_powerset.mpr h𝓝sub, h𝓝pw⟩)

lemma mem_of_disjoint_from_maximal {α : Type*} [DecidableEq α]
    {𝓕 𝓜 : Finset (Finset α)}
    (hmax : ∀ 𝓝 : Finset (Finset α), 𝓝 ⊆ 𝓕 → PairwiseDisjointFamily 𝓝 →
      𝓝.card ≤ 𝓜.card)
    (h𝓜sub : 𝓜 ⊆ 𝓕) (h𝓜pw : PairwiseDisjointFamily 𝓜)
    {A : Finset α} (hA : A ∈ 𝓕)
    (hdisj : ∀ B ∈ 𝓜, Disjoint A B) : A ∈ 𝓜 := by
  by_contra hA𝓜
  have hinsSub : insert A 𝓜 ⊆ 𝓕 := by
    intro B hB
    rcases mem_insert.mp hB with rfl | hB
    · exact hA
    · exact h𝓜sub hB
  have hinsPW : PairwiseDisjointFamily (insert A 𝓜) := by
    intro B hB C hC hBC
    rcases mem_insert.mp hB with rfl | hB
    · rcases mem_insert.mp hC with rfl | hC
      · exact (hBC rfl).elim
      · exact hdisj C hC
    · rcases mem_insert.mp hC with rfl | hC
      · rcases mem_insert.mp hB with hEq | hBM
        · exact (hBC hEq).elim
        · exact (hdisj B hBM).symm
      · exact h𝓜pw B hB C hC hBC
  have hle := hmax (insert A 𝓜) hinsSub hinsPW
  simp [card_insert_of_notMem hA𝓜] at hle

def pointStar {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  𝓕.filter fun A => x ∈ A

lemma subset_biUnion_stars {α : Type*} [DecidableEq α]
    {𝓕 : Finset (Finset α)} {U : Finset α}
    (hmeet : ∀ A ∈ 𝓕, ∃ x ∈ U, x ∈ A) :
    𝓕 ⊆ U.biUnion (pointStar 𝓕) := by
  intro A hA
  obtain ⟨x, hxU, hxA⟩ := hmeet A hA
  exact mem_biUnion.mpr ⟨x, hxU, mem_filter.mpr ⟨hA, hxA⟩⟩

lemma card_le_card_mul_of_fibers_le {α : Type*} [DecidableEq α]
    {𝓕 : Finset (Finset α)} {U : Finset α} {b : ℕ}
    (hmeet : ∀ A ∈ 𝓕, ∃ x ∈ U, x ∈ A)
    (hstar : ∀ x ∈ U, (pointStar 𝓕 x).card ≤ b) :
    𝓕.card ≤ U.card * b := by
  calc
    𝓕.card ≤ (U.biUnion (pointStar 𝓕)).card := card_le_card (subset_biUnion_stars hmeet)
    _ ≤ U.card * b := card_biUnion_le_card_mul U (pointStar 𝓕) b hstar

lemma card_biUnion_id_of_pairwiseDisjoint_uniform {α : Type*} [DecidableEq α]
    {𝓜 : Finset (Finset α)} {r : ℕ}
    (hpw : PairwiseDisjointFamily 𝓜)
    (hcard : ∀ A ∈ 𝓜, A.card = r) :
    (𝓜.biUnion id).card = 𝓜.card * r := by
  have hpw' : (𝓜 : Set (Finset α)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    exact hpw A hA B hB hAB
  rw [card_biUnion hpw']
  calc
    ∑ A ∈ 𝓜, (id A).card = ∑ _A ∈ 𝓜, r := by
      apply sum_congr rfl
      intro A hA
      simpa using hcard A hA
    _ = 𝓜.card * r := by simp

lemma card_le_one_of_uniform_zero {α : Type*} [DecidableEq α]
    {𝓕 : Finset (Finset α)} (hcard : ∀ A ∈ 𝓕, A.card = 0) :
    𝓕.card ≤ 1 := by
  have hsub : 𝓕 ⊆ ({∅} : Finset (Finset α)) := by
    intro A hA
    have : A = ∅ := card_eq_zero.mp (hcard A hA)
    simp [this]
  exact (card_le_card hsub).trans_eq (by simp)

theorem exists_deltaSystem_of_card_gt_sunflowerBound {α : Type*} [DecidableEq α] :
    ∀ r s : ℕ, 2 ≤ s → ∀ 𝓕 : Finset (Finset α),
      (∀ A ∈ 𝓕, A.card = r) → sunflowerBound r s < 𝓕.card →
      ∃ 𝓢 : Finset (Finset α), 𝓢 ⊆ 𝓕 ∧ 𝓢.card = s ∧
        ∃ K : Finset α, IsDeltaSystem K 𝓢
  | 0, s, hs, 𝓕, hcard, hlarge => by
      have hle := card_le_one_of_uniform_zero hcard
      simp [sunflowerBound] at hlarge
      omega
  | r + 1, s, hs, 𝓕, hcard, hlarge => by
      classical
      obtain ⟨𝓜, h𝓜sub, h𝓜pw, hmax⟩ := exists_max_pairwiseDisjoint_subfamily 𝓕
      by_cases hMs : s ≤ 𝓜.card
      · obtain ⟨𝓢, h𝓢sub, h𝓢card⟩ := exists_subset_card_eq hMs
        refine ⟨𝓢, h𝓢sub.trans h𝓜sub, h𝓢card, ∅, ?_⟩
        intro A hA B hB hAB
        exact disjoint_iff_inter_eq_empty.mp
          (h𝓜pw A (h𝓢sub hA) B (h𝓢sub hB) hAB)
      · have hMsmall : 𝓜.card ≤ s - 1 := by omega
        let U : Finset α := 𝓜.biUnion id
        have hUcard : U.card ≤ (r + 1) * (s - 1) := by
          calc
            U.card = 𝓜.card * (r + 1) := by
              exact card_biUnion_id_of_pairwiseDisjoint_uniform h𝓜pw
                (fun A hA => hcard A (h𝓜sub hA))
            _ ≤ (s - 1) * (r + 1) := Nat.mul_le_mul_right _ hMsmall
            _ = (r + 1) * (s - 1) := by rw [Nat.mul_comm]
        have hmeet : ∀ A ∈ 𝓕, ∃ x ∈ U, x ∈ A := by
          intro A hA
          by_contra hnone
          push Not at hnone
          have hdisj : ∀ B ∈ 𝓜, Disjoint A B := by
            intro B hB
            rw [disjoint_left]
            intro x hxA hxB
            exact hnone x (mem_biUnion.mpr ⟨B, hB, hxB⟩) hxA
          have hAM := mem_of_disjoint_from_maximal hmax h𝓜sub h𝓜pw hA hdisj
          have hAA := hdisj A hAM
          rw [disjoint_self] at hAA
          have hAempty : A = ∅ := hAA
          have hAcard : A.card = r + 1 := hcard A hA
          rw [hAempty] at hAcard
          simp at hAcard
        have hex : ∃ x ∈ U, sunflowerBound r s < (pointStar 𝓕 x).card := by
          by_contra hnot
          push Not at hnot
          have hle := card_le_card_mul_of_fibers_le hmeet hnot
          have hbound : U.card * sunflowerBound r s ≤
              (r + 1) * (s - 1) * sunflowerBound r s :=
            Nat.mul_le_mul_right _ hUcard
          have := hle.trans hbound
          simp [sunflowerBound] at hlarge
          omega
        obtain ⟨x, hxU, hxlarge⟩ := hex
        let 𝓔 : Finset (Finset α) := (pointStar 𝓕 x).image fun A => A.erase x
        have herase_inj : Set.InjOn (fun A : Finset α => A.erase x) (pointStar 𝓕 x) := by
          intro A hA B hB hEq
          have hxA : x ∈ A := (mem_filter.mp hA).2
          have hxB : x ∈ B := (mem_filter.mp hB).2
          calc
            A = insert x (A.erase x) := (insert_erase hxA).symm
            _ = insert x (B.erase x) := congrArg (insert x) hEq
            _ = B := insert_erase hxB
        have hEcard : 𝓔.card = (pointStar 𝓕 x).card := by
          exact card_image_of_injOn herase_inj
        have hEuniform : ∀ A ∈ 𝓔, A.card = r := by
          intro A hA
          rw [mem_image] at hA
          obtain ⟨B, hB, rfl⟩ := hA
          have hxB : x ∈ B := (mem_filter.mp hB).2
          have hBcard : B.card = r + 1 := hcard B (mem_filter.mp hB).1
          have := card_erase_add_one hxB
          omega
        have hElarge : sunflowerBound r s < 𝓔.card := by
          simpa [hEcard] using hxlarge
        obtain ⟨𝓣, h𝓣sub, h𝓣card, K, h𝓣delta⟩ :=
          exists_deltaSystem_of_card_gt_sunflowerBound r s hs 𝓔 hEuniform hElarge
        let lift : Finset α → Finset α := fun A => insert x A
        let 𝓢 : Finset (Finset α) := 𝓣.image lift
        have hx_not_mem_of_mem_E : ∀ A ∈ 𝓔, x ∉ A := by
          intro A hA
          rw [mem_image] at hA
          obtain ⟨B, hB, rfl⟩ := hA
          simp
        have hlift_inj : Set.InjOn lift 𝓣 := by
          intro A hA B hB hEq
          have hxA : x ∉ A := hx_not_mem_of_mem_E A (h𝓣sub hA)
          have hxB : x ∉ B := hx_not_mem_of_mem_E B (h𝓣sub hB)
          simpa [lift, hxA, hxB] using congrArg (erase · x) hEq
        have h𝓢card : 𝓢.card = s := by
          change (𝓣.image lift).card = s
          rw [card_image_of_injOn hlift_inj, h𝓣card]
        have h𝓢sub : 𝓢 ⊆ 𝓕 := by
          intro A hA
          change A ∈ 𝓣.image lift at hA
          rw [mem_image] at hA
          obtain ⟨B, hB, rfl⟩ := hA
          have hBE : B ∈ 𝓔 := h𝓣sub hB
          change B ∈ (pointStar 𝓕 x).image (fun A => A.erase x) at hBE
          rw [mem_image] at hBE
          obtain ⟨C, hC, hCB⟩ := hBE
          have hxC : x ∈ C := (mem_filter.mp hC).2
          have : insert x B = C := by
            rw [← hCB, insert_erase hxC]
          change insert x B ∈ 𝓕
          rw [this]
          exact (mem_filter.mp hC).1
        refine ⟨𝓢, h𝓢sub, h𝓢card, insert x K, ?_⟩
        intro A hA B hB hAB
        change A ∈ 𝓣.image lift at hA
        change B ∈ 𝓣.image lift at hB
        rw [mem_image] at hA hB
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨B', hB', rfl⟩ := hB
        have hne : A' ≠ B' := by
          intro h
          exact hAB (by simp [lift, h])
        change insert x A' ∩ insert x B' = insert x K
        rw [← insert_inter_distrib]
        exact congrArg (insert x) (h𝓣delta A' hA' B' hB' hne)

lemma exists_deltaMember_disjoint_from_small {α : Type*} [DecidableEq α]
    {q : ℕ} {K D : Finset α} {𝓢 : Finset (Finset α)}
    (hdelta : IsDeltaSystem K 𝓢) (hcard : 𝓢.card = q)
    (hD : D.card < q) :
    ∃ A ∈ 𝓢, Disjoint (A \ K) D := by
  classical
  by_contra hnone
  push Not at hnone
  have hmeet : ∀ A ∈ 𝓢, ∃ d, d ∈ A \ K ∧ d ∈ D := by
    intro A hA
    exact not_disjoint_iff.mp (hnone A hA)
  let f : {A // A ∈ 𝓢} → α := fun A => Classical.choose (hmeet A.1 A.2)
  have hf_spec : ∀ A : {A // A ∈ 𝓢},
      f A ∈ A.1 \ K ∧ f A ∈ D := by
    intro A
    exact Classical.choose_spec (hmeet A.1 A.2)
  have hf_inj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    by_contra hne
    have hdeltaAB := hdelta A.1 A.2 B.1 B.2 hne
    have hdA : f A ∈ A.1 := (mem_sdiff.mp (hf_spec A).1).1
    have hdB : f A ∈ B.1 := by rw [hAB]; exact (mem_sdiff.mp (hf_spec B).1).1
    have hdK : f A ∈ K := by
      rw [← hdeltaAB]
      exact mem_inter.mpr ⟨hdA, hdB⟩
    exact (mem_sdiff.mp (hf_spec A).1).2 hdK
  have himage_sub : 𝓢.attach.image f ⊆ D := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨A, hA, rfl⟩ := hd
    exact (hf_spec A).2
  have himage_le : (𝓢.attach.image f).card ≤ D.card :=
    card_le_card himage_sub
  have himage_card : (𝓢.attach.image f).card = 𝓢.card := by
    rw [card_image_of_injective _ hf_inj, card_attach]
  rw [himage_card, hcard] at himage_le
  omega

/-! ## Links -/

/-- The link of a point: erase the point from every member that contains it. -/
def link {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (x : Fin n) :
    Finset (Finset (Fin n)) :=
  (𝓕.filter fun A => x ∈ A).image fun A => A.erase x

lemma mem_link_iff {n : ℕ} {𝓕 : Finset (Finset (Fin n))} {x : Fin n}
    {A : Finset (Fin n)} :
    A ∈ link 𝓕 x ↔ x ∉ A ∧ insert x A ∈ 𝓕 := by
  constructor
  · intro hA
    rw [link, mem_image] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    have hxB : x ∈ B := (mem_filter.mp hB).2
    refine ⟨by simp, ?_⟩
    rw [insert_erase hxB]
    exact (mem_filter.mp hB).1
  · rintro ⟨hxA, hA⟩
    rw [link, mem_image]
    refine ⟨insert x A, ?_, ?_⟩
    · exact mem_filter.mpr ⟨hA, by simp⟩
    · simp [hxA]

lemma card_link_eq_degree {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (x : Fin n) :
    (link 𝓕 x).card = (𝓕.filter fun A => x ∈ A).card := by
  classical
  unfold link
  apply card_image_of_injOn
  intro A hA B hB hEq
  have hxA : x ∈ A := (mem_filter.mp hA).2
  have hxB : x ∈ B := (mem_filter.mp hB).2
  calc
    A = insert x (A.erase x) := (insert_erase hxA).symm
    _ = insert x (B.erase x) := congrArg (insert x) hEq
    _ = B := insert_erase hxB

lemma link_uniform {n k : ℕ} {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (x : Fin n) :
    ∀ A ∈ link 𝓕 x, A.card = k - 1 := by
  intro A hA
  rw [mem_link_iff] at hA
  have hcard := huniform (insert x A) hA.2
  rw [card_insert_of_notMem hA.1] at hcard
  omega

/-- A finite family all of whose pairs have nonempty intersection. -/
def LinkIntersecting {n : ℕ} (𝓖 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓖, ∀ B ∈ 𝓖, ¬ Disjoint A B

lemma link_intersecting_of_avoidsSingleton {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (havoid : AvoidsSingleton 𝓕)
    (x : Fin n) : LinkIntersecting (link 𝓕 x) := by
  intro A hA B hB hdisj
  rw [mem_link_iff] at hA hB
  have hinter : insert x A ∩ insert x B = ({x} : Finset (Fin n)) := by
    rw [← insert_inter_distrib]
    rw [disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  have hbad := havoid (insert x A) hA.2 (insert x B) hB.2
  apply hbad
  rw [hinter]
  simp

/-! ## Generated kernels and delta-bases -/

/-- A nonempty set is generated by a family if it is already a member or is
the kernel of a q-member delta-system inside the family. -/
def IsGeneratedKernel {n : ℕ} (q : ℕ) (𝓖 : Finset (Finset (Fin n)))
    (E : Finset (Fin n)) : Prop :=
  E.Nonempty ∧
    (E ∈ 𝓖 ∨ ∃ 𝓢 : Finset (Finset (Fin n)),
      𝓢 ⊆ 𝓖 ∧ 𝓢.card = q ∧ IsDeltaSystem E 𝓢)

/-- The finite set of all generated kernels. -/
noncomputable def generatedKernels {n : ℕ} (q : ℕ) (𝓖 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  by
    classical
    exact (univ : Finset (Finset (Fin n))).filter (IsGeneratedKernel q 𝓖)

/-- The inclusion-minimal generated kernels. -/
noncomputable def deltaBase {n : ℕ} (q : ℕ) (𝓖 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  by
    classical
    exact (generatedKernels q 𝓖).filter fun B =>
      ∀ E ∈ generatedKernels q 𝓖, E ⊆ B → B ⊆ E

lemma mem_generatedKernels_iff {n q : ℕ} {𝓖 : Finset (Finset (Fin n))}
    {E : Finset (Fin n)} :
    E ∈ generatedKernels q 𝓖 ↔ IsGeneratedKernel q 𝓖 E := by
  simp [generatedKernels]

lemma mem_deltaBase_iff {n q : ℕ} {𝓖 : Finset (Finset (Fin n))}
    {B : Finset (Fin n)} :
    B ∈ deltaBase q 𝓖 ↔
      B ∈ generatedKernels q 𝓖 ∧
        ∀ E ∈ generatedKernels q 𝓖, E ⊆ B → B ⊆ E := by
  simp [deltaBase]

lemma mem_generatedKernels_of_mem {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∈ 𝓖) (hAne : A.Nonempty) :
    A ∈ generatedKernels q 𝓖 := by
  rw [mem_generatedKernels_iff]
  exact ⟨hAne, Or.inl hA⟩

lemma generatedKernel_nonempty {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (hE : E ∈ generatedKernels q 𝓖) : E.Nonempty :=
  (mem_generatedKernels_iff.mp hE).1

lemma exists_deltaBase_subset_of_mem {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∈ 𝓖) (hAne : A.Nonempty) :
    ∃ B ∈ deltaBase q 𝓖, B ⊆ A := by
  classical
  let C := (generatedKernels q 𝓖).filter fun E => E ⊆ A
  have hC : C.Nonempty := by
    refine ⟨A, ?_⟩
    exact mem_filter.mpr ⟨mem_generatedKernels_of_mem hA hAne, Subset.rfl⟩
  obtain ⟨B, hBC, hBmin⟩ := C.exists_min_image Finset.card hC
  have hBgen : B ∈ generatedKernels q 𝓖 := (mem_filter.mp hBC).1
  have hBsubA : B ⊆ A := (mem_filter.mp hBC).2
  refine ⟨B, ?_, hBsubA⟩
  rw [mem_deltaBase_iff]
  refine ⟨hBgen, ?_⟩
  intro E hEgen hEsubB
  have hEsubA : E ⊆ A := hEsubB.trans hBsubA
  have hEcard_ge : B.card ≤ E.card :=
    hBmin E (mem_filter.mpr ⟨hEgen, hEsubA⟩)
  have hEcard_le : E.card ≤ B.card := card_le_card hEsubB
  have hcard : E.card = B.card := by omega
  have hEq : E = B := eq_of_subset_of_card_le hEsubB (by omega)
  rw [hEq]

lemma deltaBase_covers_link {n k q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 1 < k) (x : Fin n) :
    ∀ A ∈ link 𝓕 x, ∃ B ∈ deltaBase q (link 𝓕 x), B ⊆ A := by
  intro A hA
  apply exists_deltaBase_subset_of_mem hA
  have hcard := link_uniform huniform x A hA
  have : 0 < A.card := by omega
  exact card_pos.mp this

lemma kernel_subset_of_mem_deltaSystem {α : Type*} [DecidableEq α]
    {K : Finset α} {𝓢 : Finset (Finset α)} {A : Finset α}
    (hdelta : IsDeltaSystem K 𝓢) (hcard : 2 ≤ 𝓢.card) (hA : A ∈ 𝓢) :
    K ⊆ A := by
  have hex : ∃ B ∈ 𝓢, B ≠ A := by
    by_contra hnone
    push Not at hnone
    have hsub : 𝓢 ⊆ ({A} : Finset (Finset α)) := by
      intro B hB
      simp [hnone B hB]
    have hle := card_le_card hsub
    simp at hle
    omega
  obtain ⟨B, hB, hBA⟩ := hex
  rw [← hdelta A hA B hB hBA.symm]
  exact inter_subset_left

lemma exists_member_superset_of_generatedKernel {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (hq : 2 ≤ q) (hE : E ∈ generatedKernels q 𝓖) :
    ∃ A ∈ 𝓖, E ⊆ A := by
  rw [mem_generatedKernels_iff] at hE
  rcases hE.2 with hmem | ⟨𝓢, h𝓢sub, h𝓢card, hdelta⟩
  · exact ⟨E, hmem, Subset.rfl⟩
  · have h𝓢two : 2 ≤ 𝓢.card := by omega
    have h𝓢pos : 0 < 𝓢.card := by omega
    obtain ⟨A, hA⟩ := card_pos.mp h𝓢pos
    exact ⟨A, h𝓢sub hA, kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA⟩

lemma generatedKernel_card_le_of_uniform {n k q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (huniform : IsUniform k 𝓕) (hq : 2 ≤ q)
    (hE : E ∈ generatedKernels q 𝓕) :
    E.card ≤ k := by
  obtain ⟨A, hA, hEA⟩ := exists_member_superset_of_generatedKernel hq hE
  calc
    E.card ≤ A.card := card_le_card hEA
    _ = k := huniform A hA

lemma exists_member_inter_eq_generatedKernel {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {K T : Finset (Fin n)}
    (_huniform : IsUniform k 𝓕) (hk : 2 ≤ k)
    (hK : K ∈ generatedKernels k 𝓕)
    (hTle : T.card ≤ k) (hKT : (K ∩ T).card = 1) :
    ∃ A ∈ 𝓕, A ∩ T = K ∩ T := by
  rw [mem_generatedKernels_iff] at hK
  rcases hK.2 with hmem | ⟨𝓢, h𝓢sub, h𝓢card, hdelta⟩
  · exact ⟨K, hmem, rfl⟩
  · let D := T \ K
    have hTinter : (T ∩ K).card = 1 := by simpa [inter_comm] using hKT
    have hDcard : D.card < k := by
      have hsum := card_sdiff_add_card_inter T K
      change (T \ K).card < k
      omega
    obtain ⟨A, hA, hdisj⟩ :=
      exists_deltaMember_disjoint_from_small hdelta h𝓢card hDcard
    have h𝓢two : 2 ≤ 𝓢.card := by omega
    have hKsubA : K ⊆ A :=
      kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA
    refine ⟨A, h𝓢sub hA, ?_⟩
    ext z
    constructor
    · intro hz
      have hzA : z ∈ A := (mem_inter.mp hz).1
      have hzT : z ∈ T := (mem_inter.mp hz).2
      by_cases hzK : z ∈ K
      · exact mem_inter.mpr ⟨hzK, hzT⟩
      · have hzPetal : z ∈ A \ K := mem_sdiff.mpr ⟨hzA, hzK⟩
        have hzD : z ∈ D := by
          change z ∈ T \ K
          exact mem_sdiff.mpr ⟨hzT, hzK⟩
        exact (disjoint_left.mp hdisj hzPetal hzD).elim
    · intro hz
      exact mem_inter.mpr ⟨hKsubA (mem_inter.mp hz).1, (mem_inter.mp hz).2⟩

lemma generatedKernels_compatible_of_avoidsSingleton {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {K L : Finset (Fin n)}
    (huniform : IsUniform k 𝓕) (hk : 2 ≤ k)
    (havoid : AvoidsSingleton 𝓕)
    (hK : K ∈ generatedKernels k 𝓕)
    (hL : L ∈ generatedKernels k 𝓕) :
    (K ∩ L).card ≠ 1 := by
  intro hKL
  have hLcard : L.card ≤ k :=
    generatedKernel_card_le_of_uniform huniform hk hL
  obtain ⟨A, hA, hAL⟩ :=
    exists_member_inter_eq_generatedKernel huniform hk hK hLcard hKL
  have hALcard : (A ∩ L).card = 1 := by rw [hAL, hKL]
  have hAcard : A.card ≤ k := by rw [huniform A hA]
  have hLA : (L ∩ A).card = 1 := by simpa [inter_comm] using hALcard
  obtain ⟨B, hB, hBA⟩ :=
    exists_member_inter_eq_generatedKernel huniform hk hL hAcard hLA
  apply havoid A hA B hB
  have hAB : A ∩ B = L ∩ A := by
    rw [inter_comm A B, hBA]
  rw [hAB, hLA]

lemma generatedKernel_insert_of_link {n q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x : Fin n} {E : Finset (Fin n)}
    (hE : E ∈ generatedKernels q (link 𝓕 x)) :
    insert x E ∈ generatedKernels q 𝓕 := by
  classical
  rw [mem_generatedKernels_iff] at hE ⊢
  refine ⟨by simp, ?_⟩
  rcases hE.2 with hmem | ⟨𝓢, h𝓢sub, h𝓢card, hdelta⟩
  · exact Or.inl (mem_link_iff.mp hmem).2
  · let lift : Finset (Fin n) → Finset (Fin n) := fun A => insert x A
    let 𝓣 : Finset (Finset (Fin n)) := 𝓢.image lift
    have hx_not_mem : ∀ A ∈ 𝓢, x ∉ A := by
      intro A hA
      exact (mem_link_iff.mp (h𝓢sub hA)).1
    have hlift_inj : Set.InjOn lift 𝓢 := by
      intro A hA B hB hAB
      have hxA := hx_not_mem A hA
      have hxB := hx_not_mem B hB
      simpa [lift, hxA, hxB] using congrArg (erase · x) hAB
    have h𝓣sub : 𝓣 ⊆ 𝓕 := by
      intro A hA
      change A ∈ 𝓢.image lift at hA
      rw [mem_image] at hA
      obtain ⟨B, hB, rfl⟩ := hA
      change insert x B ∈ 𝓕
      exact (mem_link_iff.mp (h𝓢sub hB)).2
    have h𝓣card : 𝓣.card = q := by
      change (𝓢.image lift).card = q
      rw [card_image_of_injOn hlift_inj, h𝓢card]
    refine Or.inr ⟨𝓣, h𝓣sub, h𝓣card, ?_⟩
    intro A hA B hB hAB
    change A ∈ 𝓢.image lift at hA
    change B ∈ 𝓢.image lift at hB
    rw [mem_image] at hA hB
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨B', hB', rfl⟩ := hB
    have hne : A' ≠ B' := by
      intro h
      exact hAB (by simp [lift, h])
    change insert x A' ∩ insert x B' = insert x E
    rw [← insert_inter_distrib]
    exact congrArg (insert x) (hdelta A' hA' B' hB' hne)

lemma link_deltaBases_compatible_of_avoidsSingleton {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y : Fin n} {B C : Finset (Fin n)}
    (hB : B ∈ deltaBase k (link 𝓕 x))
    (hC : C ∈ deltaBase k (link 𝓕 y)) :
    ((insert x B) ∩ (insert y C)).card ≠ 1 := by
  apply generatedKernels_compatible_of_avoidsSingleton huniform hk havoid
  · exact generatedKernel_insert_of_link (mem_deltaBase_iff.mp hB).1
  · exact generatedKernel_insert_of_link (mem_deltaBase_iff.mp hC).1

/-! ## Iterated kernel closure

The one-step delta-base above mirrors Frankl's notation.  For counting we use
its finite closure variant: adjoining a nonempty sunflower kernel is repeated
inductively.  This makes the no-large-sunflower property of minimal kernels a
direct consequence of minimality. -/

inductive KernelReachable {n : ℕ} (q : ℕ) (𝓖 : Finset (Finset (Fin n))) :
    Finset (Fin n) → Prop
  | member {E : Finset (Fin n)} :
      E ∈ 𝓖 → E.Nonempty → KernelReachable q 𝓖 E
  | delta {K : Finset (Fin n)} {𝓢 : Finset (Finset (Fin n))} :
      K.Nonempty →
      (∀ A ∈ 𝓢, KernelReachable q 𝓖 A) →
      𝓢.card = q →
      IsDeltaSystem K 𝓢 →
      KernelReachable q 𝓖 K

noncomputable def kernelClosure {n : ℕ} (q : ℕ)
    (𝓖 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  by
    classical
    exact (univ : Finset (Finset (Fin n))).filter (KernelReachable q 𝓖)

noncomputable def closedDeltaBase {n : ℕ} (q : ℕ)
    (𝓖 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  by
    classical
    exact (kernelClosure q 𝓖).filter fun B =>
      ∀ E ∈ kernelClosure q 𝓖, E ⊆ B → B ⊆ E

lemma mem_kernelClosure_iff {n q : ℕ} {𝓖 : Finset (Finset (Fin n))}
    {E : Finset (Fin n)} :
    E ∈ kernelClosure q 𝓖 ↔ KernelReachable q 𝓖 E := by
  simp [kernelClosure]

lemma mem_closedDeltaBase_iff {n q : ℕ} {𝓖 : Finset (Finset (Fin n))}
    {B : Finset (Fin n)} :
    B ∈ closedDeltaBase q 𝓖 ↔
      B ∈ kernelClosure q 𝓖 ∧
        ∀ E ∈ kernelClosure q 𝓖, E ⊆ B → B ⊆ E := by
  simp [closedDeltaBase]

lemma kernelReachable_nonempty {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (hE : KernelReachable q 𝓖 E) : E.Nonempty := by
  induction hE with
  | member _ hne => exact hne
  | delta hne _ _ _ _ => exact hne

lemma kernelReachable_card_le {n q r : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (h𝓖card : ∀ A ∈ 𝓖, A.card ≤ r) (hq : 2 ≤ q)
    (hE : KernelReachable q 𝓖 E) :
    E.card ≤ r := by
  induction hE with
  | member hmem _ =>
      exact h𝓖card _ hmem
  | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
      have h𝓢two : 2 ≤ 𝓢.card := by omega
      have h𝓢pos : 0 < 𝓢.card := by omega
      obtain ⟨A, hA⟩ := card_pos.mp h𝓢pos
      exact (card_le_card (kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA)).trans
        (ih A hA)

lemma exists_closedDeltaBase_subset_of_mem {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∈ 𝓖) (hAne : A.Nonempty) :
    ∃ B ∈ closedDeltaBase q 𝓖, B ⊆ A := by
  classical
  let C := (kernelClosure q 𝓖).filter fun E => E ⊆ A
  have hC : C.Nonempty := by
    refine ⟨A, ?_⟩
    exact mem_filter.mpr
      ⟨mem_kernelClosure_iff.mpr (KernelReachable.member hA hAne), Subset.rfl⟩
  obtain ⟨B, hBC, hBmin⟩ := C.exists_min_image Finset.card hC
  have hBcl : B ∈ kernelClosure q 𝓖 := (mem_filter.mp hBC).1
  have hBsubA : B ⊆ A := (mem_filter.mp hBC).2
  refine ⟨B, ?_, hBsubA⟩
  rw [mem_closedDeltaBase_iff]
  refine ⟨hBcl, ?_⟩
  intro E hEcl hEsubB
  have hEsubA : E ⊆ A := hEsubB.trans hBsubA
  have hEcard_ge : B.card ≤ E.card :=
    hBmin E (mem_filter.mpr ⟨hEcl, hEsubA⟩)
  have hEcard_le : E.card ≤ B.card := card_le_card hEsubB
  have hEq : E = B := eq_of_subset_of_card_le hEsubB (by omega)
  rw [hEq]

lemma exists_closedDeltaBase_subset_of_closure {n q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hAcl : A ∈ kernelClosure q 𝓖) :
    ∃ B ∈ closedDeltaBase q 𝓖, B ⊆ A := by
  classical
  let C := (kernelClosure q 𝓖).filter fun E => E ⊆ A
  have hC : C.Nonempty := by
    refine ⟨A, ?_⟩
    exact mem_filter.mpr ⟨hAcl, Subset.rfl⟩
  obtain ⟨B, hBC, hBmin⟩ := C.exists_min_image Finset.card hC
  have hBcl : B ∈ kernelClosure q 𝓖 := (mem_filter.mp hBC).1
  have hBsubA : B ⊆ A := (mem_filter.mp hBC).2
  refine ⟨B, ?_, hBsubA⟩
  rw [mem_closedDeltaBase_iff]
  refine ⟨hBcl, ?_⟩
  intro E hEcl hEsubB
  have hEsubA : E ⊆ A := hEsubB.trans hBsubA
  have hEcard_ge : B.card ≤ E.card :=
    hBmin E (mem_filter.mpr ⟨hEcl, hEsubA⟩)
  have hEcard_le : E.card ≤ B.card := card_le_card hEsubB
  have hEq : E = B := eq_of_subset_of_card_le hEsubB (by omega)
  rw [hEq]

lemma card_sdiff_lt_of_card_le_of_inter_card_one {α : Type*} [DecidableEq α]
    {q : ℕ} {K T : Finset α} (hTle : T.card ≤ q)
    (hKT : (K ∩ T).card = 1) :
    (T \ K).card < q := by
  have hTK : (T ∩ K).card = 1 := by simpa [inter_comm] using hKT
  have hsum := card_sdiff_add_card_inter T K
  omega

lemma inter_eq_kernel_inter_of_petal_disjoint {α : Type*} [DecidableEq α]
    {K A T : Finset α} (hKA : K ⊆ A)
    (hdisj : Disjoint (A \ K) (T \ K)) :
    A ∩ T = K ∩ T := by
  ext z
  constructor
  · intro hz
    have hzA : z ∈ A := (mem_inter.mp hz).1
    have hzT : z ∈ T := (mem_inter.mp hz).2
    by_cases hzK : z ∈ K
    · exact mem_inter.mpr ⟨hzK, hzT⟩
    · have hzPetal : z ∈ A \ K := mem_sdiff.mpr ⟨hzA, hzK⟩
      have hzTarget : z ∈ T \ K := mem_sdiff.mpr ⟨hzT, hzK⟩
      exact (disjoint_left.mp hdisj hzPetal hzTarget).elim
  · intro hz
    exact mem_inter.mpr ⟨hKA (mem_inter.mp hz).1, (mem_inter.mp hz).2⟩

lemma exists_deltaMember_inter_eq_kernel {α : Type*} [DecidableEq α]
    {q : ℕ} {K T : Finset α} {𝓢 : Finset (Finset α)}
    (hq : 2 ≤ q) (hdelta : IsDeltaSystem K 𝓢)
    (h𝓢card : 𝓢.card = q) (hTle : T.card ≤ q)
    (hKT : (K ∩ T).card = 1) :
    ∃ A ∈ 𝓢, A ∩ T = K ∩ T := by
  let D := T \ K
  have hDcard : D.card < q := by
    change (T \ K).card < q
    exact card_sdiff_lt_of_card_le_of_inter_card_one hTle hKT
  obtain ⟨A, hA, hdisj⟩ :=
    exists_deltaMember_disjoint_from_small hdelta h𝓢card hDcard
  have h𝓢two : 2 ≤ 𝓢.card := by omega
  refine ⟨A, hA, ?_⟩
  apply inter_eq_kernel_inter_of_petal_disjoint
  · exact kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA
  · exact hdisj

lemma kernelReachable_compatible {n q r : ℕ}
    {𝓖 : Finset (Finset (Fin n))}
    (hbase : ∀ A ∈ 𝓖, ∀ B ∈ 𝓖, (A ∩ B).card ≠ 1)
    (h𝓖card : ∀ A ∈ 𝓖, A.card ≤ r)
    (hq : 2 ≤ q) (hrq : r ≤ q)
    {E L : Finset (Fin n)}
    (hE : KernelReachable q 𝓖 E) (hL : KernelReachable q 𝓖 L) :
    (E ∩ L).card ≠ 1 := by
  revert L
  induction hE with
  | @member E₀ hEmem hEne =>
      intro L hL
      induction hL with
      | @member L₀ hLmem _ =>
          exact hbase E₀ hEmem L₀ hLmem
      | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
          intro hEK
          have hEcard : E₀.card ≤ q :=
            (kernelReachable_card_le h𝓖card hq
              (KernelReachable.member hEmem hEne)).trans hrq
          have hKE : (K ∩ E₀).card = 1 := by
            simpa [inter_comm] using hEK
          obtain ⟨A, hA, hAE⟩ :=
            exists_deltaMember_inter_eq_kernel hq hdelta h𝓢card hEcard hKE
          apply (ih A hA)
          rw [inter_comm E₀ A, hAE, hKE]
  | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
      intro L hL hKL
      have hLcard : L.card ≤ q :=
        (kernelReachable_card_le h𝓖card hq hL).trans hrq
      obtain ⟨A, hA, hAL⟩ :=
        exists_deltaMember_inter_eq_kernel hq hdelta h𝓢card hLcard hKL
      apply ih A hA hL
      rw [hAL, hKL]

lemma kernelReachable_not_mem_of_link {n q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x : Fin n} {E : Finset (Fin n)}
    (hq : 2 ≤ q)
    (hE : KernelReachable q (link 𝓕 x) E) :
    x ∉ E := by
  induction hE with
  | member hmem _ =>
      exact (mem_link_iff.mp hmem).1
  | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
      have h𝓢two : 2 ≤ 𝓢.card := by rw [h𝓢card]; exact hq
      have h𝓢pos : 0 < 𝓢.card := by omega
      obtain ⟨A, hA⟩ := card_pos.mp h𝓢pos
      have hKsubA := kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA
      intro hxK
      exact (ih A hA) (hKsubA hxK)

lemma kernelReachable_insert_of_link {n q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x : Fin n} {E : Finset (Fin n)}
    (hq : 2 ≤ q)
    (hE : KernelReachable q (link 𝓕 x) E) :
    KernelReachable q 𝓕 (insert x E) := by
  classical
  induction hE with
  | member hmem _ =>
      exact KernelReachable.member (mem_link_iff.mp hmem).2 (by simp)
  | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
      let lift : Finset (Fin n) → Finset (Fin n) := fun A => insert x A
      let 𝓣 : Finset (Finset (Fin n)) := 𝓢.image lift
      have hx_not_mem : ∀ A ∈ 𝓢, x ∉ A := by
        intro A hA
        exact kernelReachable_not_mem_of_link hq (hreach A hA)
      have hlift_inj : Set.InjOn lift 𝓢 := by
        intro A hA B hB hAB
        have hxA := hx_not_mem A hA
        have hxB := hx_not_mem B hB
        simpa [lift, hxA, hxB] using congrArg (erase · x) hAB
      have h𝓣card : 𝓣.card = q := by
        change (𝓢.image lift).card = q
        rw [card_image_of_injOn hlift_inj, h𝓢card]
      apply KernelReachable.delta (K := insert x K) (𝓢 := 𝓣) (by simp)
      · intro A hA
        change A ∈ 𝓢.image lift at hA
        rw [mem_image] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        exact ih B hB
      · exact h𝓣card
      · intro A hA B hB hAB
        change A ∈ 𝓢.image lift at hA
        change B ∈ 𝓢.image lift at hB
        rw [mem_image] at hA hB
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨B', hB', rfl⟩ := hB
        have hne : A' ≠ B' := by
          intro h
          exact hAB (by simp [lift, h])
        change insert x A' ∩ insert x B' = insert x K
        rw [← insert_inter_distrib]
        exact congrArg (insert x) (hdelta A' hA' B' hB' hne)

lemma kernelClosure_link_intersecting {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    (x : Fin n) {B C : Finset (Fin n)}
    (hB : B ∈ kernelClosure k (link 𝓕 x))
    (hC : C ∈ kernelClosure k (link 𝓕 x)) :
    ¬ Disjoint B C := by
  intro hdisj
  have hcompat := kernelReachable_compatible
    (q := k) (r := k) (𝓖 := 𝓕)
    havoid (fun A hA => by rw [huniform A hA]) hk (le_refl k)
    (kernelReachable_insert_of_link hk (mem_kernelClosure_iff.mp hB))
    (kernelReachable_insert_of_link hk (mem_kernelClosure_iff.mp hC))
  apply hcompat
  have hinter :
      insert x B ∩ insert x C = ({x} : Finset (Fin n)) := by
    rw [← insert_inter_distrib]
    rw [disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  rw [hinter]
  simp

noncomputable def closedBaseOfCard {n : ℕ} (q : ℕ)
    (𝓖 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Finset (Fin n)) :=
  (closedDeltaBase q 𝓖).filter fun B => B.card = t

lemma no_deltaSystem_in_closed_link_bases {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    (x : Fin n) {𝓢 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (h𝓢sub : 𝓢 ⊆ closedDeltaBase k (link 𝓕 x))
    (h𝓢card : 𝓢.card = k) (hdelta : IsDeltaSystem K 𝓢) :
    False := by
  have h𝓢two : 2 ≤ 𝓢.card := by omega
  have h𝓢pos : 0 < 𝓢.card := by omega
  obtain ⟨A, hA⟩ := card_pos.mp h𝓢pos
  have hexB : ∃ B ∈ 𝓢, B ≠ A := by
    by_contra hnone
    push Not at hnone
    have hsub : 𝓢 ⊆ ({A} : Finset (Finset (Fin n))) := by
      intro B hB
      simp [hnone B hB]
    have hle := card_le_card hsub
    simp at hle
    omega
  obtain ⟨B, hB, hBA⟩ := hexB
  have hABne : A ≠ B := hBA.symm
  have hKnonempty : K.Nonempty := by
    have hnotdisj : ¬ Disjoint A B :=
      kernelClosure_link_intersecting huniform hk havoid x
        (mem_closedDeltaBase_iff.mp (h𝓢sub hA)).1
        (mem_closedDeltaBase_iff.mp (h𝓢sub hB)).1
    rw [← hdelta A hA B hB hABne]
    exact not_disjoint_iff_nonempty_inter.mp hnotdisj
  have hKcl : K ∈ kernelClosure k (link 𝓕 x) := by
    rw [mem_kernelClosure_iff]
    apply KernelReachable.delta hKnonempty
    · intro D hD
      exact mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp (h𝓢sub hD)).1
    · exact h𝓢card
    · exact hdelta
  have hKsubA : K ⊆ A :=
    kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA
  have hAsubK : A ⊆ K :=
    (mem_closedDeltaBase_iff.mp (h𝓢sub hA)).2 K hKcl hKsubA
  have hKsubB : K ⊆ B :=
    kernel_subset_of_mem_deltaSystem hdelta h𝓢two hB
  have hBsubK : B ⊆ K :=
    (mem_closedDeltaBase_iff.mp (h𝓢sub hB)).2 K hKcl hKsubB
  have hAK : A = K := Subset.antisymm hAsubK hKsubA
  have hBK : B = K := Subset.antisymm hBsubK hKsubB
  exact hABne (hAK.trans hBK.symm)

lemma closed_link_bases_card_le_sunflowerBound {n k t : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    (x : Fin n) :
    (closedBaseOfCard k (link 𝓕 x) t).card ≤ sunflowerBound t k := by
  by_contra hnot
  push Not at hnot
  have hunif : ∀ B ∈ closedBaseOfCard k (link 𝓕 x) t, B.card = t := by
    intro B hB
    exact (mem_filter.mp hB).2
  obtain ⟨𝓢, h𝓢sub, h𝓢card, K, hdelta⟩ :=
    exists_deltaSystem_of_card_gt_sunflowerBound t k hk
      (closedBaseOfCard k (link 𝓕 x) t) hunif hnot
  apply no_deltaSystem_in_closed_link_bases huniform hk havoid x
    (𝓢 := 𝓢) (K := K)
  · exact h𝓢sub.trans (fun _ h => (mem_filter.mp h).1)
  · exact h𝓢card
  · exact hdelta

def supersetsInFamily {n : ℕ} (𝓖 : Finset (Finset (Fin n)))
    (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  𝓖.filter fun A => B ⊆ A

lemma card_supersetsInFamily_le_choose {n r t : ℕ}
    {𝓖 : Finset (Finset (Fin n))} (huniform : ∀ A ∈ 𝓖, A.card = r)
    {B : Finset (Fin n)} (hBcard : B.card = t) :
    (supersetsInFamily 𝓖 B).card ≤ Nat.choose n (r - t) := by
  classical
  let eraseB : Finset (Fin n) → Finset (Fin n) := fun A => A \ B
  have herase_inj : Set.InjOn eraseB (supersetsInFamily 𝓖 B) := by
    intro A hA C hC hEq
    have hBA : B ⊆ A := (mem_filter.mp hA).2
    have hBC : B ⊆ C := (mem_filter.mp hC).2
    calc
      A = (A \ B) ∪ B := (sdiff_union_of_subset hBA).symm
      _ = (C \ B) ∪ B := congrArg (fun D => D ∪ B) hEq
      _ = C := sdiff_union_of_subset hBC
  have himage_sub :
      (supersetsInFamily 𝓖 B).image eraseB ⊆
        (univ : Finset (Fin n)).powersetCard (r - t) := by
    intro D hD
    rw [mem_image] at hD
    obtain ⟨A, hA, rfl⟩ := hD
    have hAmem : A ∈ 𝓖 := (mem_filter.mp hA).1
    have hBA : B ⊆ A := (mem_filter.mp hA).2
    rw [mem_powersetCard]
    refine ⟨by simp, ?_⟩
    rw [card_sdiff_of_subset hBA, huniform A hAmem, hBcard]
  calc
    (supersetsInFamily 𝓖 B).card =
        ((supersetsInFamily 𝓖 B).image eraseB).card := by
          rw [card_image_of_injOn herase_inj]
    _ ≤ ((univ : Finset (Fin n)).powersetCard (r - t)).card :=
      card_le_card himage_sub
    _ = Nat.choose n (r - t) := by simp

lemma link_subset_biUnion_closed_bases {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 1 < k) (x : Fin n) :
    link 𝓕 x ⊆
      (closedDeltaBase k (link 𝓕 x)).biUnion
        (supersetsInFamily (link 𝓕 x)) := by
  intro A hA
  obtain ⟨B, hB, hBA⟩ :=
    exists_closedDeltaBase_subset_of_mem hA
      (by
        have hcard := link_uniform huniform x A hA
        exact card_pos.mp (by omega))
  exact mem_biUnion.mpr
    ⟨B, hB, mem_filter.mpr ⟨hA, hBA⟩⟩

lemma card_link_le_sum_closed_bases {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 1 < k) (x : Fin n) :
    (link 𝓕 x).card ≤
      ∑ B ∈ closedDeltaBase k (link 𝓕 x),
        Nat.choose n ((k - 1) - B.card) := by
  calc
    (link 𝓕 x).card ≤
        ((closedDeltaBase k (link 𝓕 x)).biUnion
          (supersetsInFamily (link 𝓕 x))).card :=
      card_le_card (link_subset_biUnion_closed_bases huniform hk x)
    _ ≤ ∑ B ∈ closedDeltaBase k (link 𝓕 x),
        (supersetsInFamily (link 𝓕 x) B).card := card_biUnion_le
    _ ≤ ∑ B ∈ closedDeltaBase k (link 𝓕 x),
        Nat.choose n ((k - 1) - B.card) := by
      apply sum_le_sum
      intro B hB
      apply card_supersetsInFamily_le_choose
      · exact link_uniform huniform x
      · rfl

def closedBaseCountBound (k r : ℕ) : ℕ :=
  ∑ t ∈ range (r + 1), sunflowerBound t k

lemma closed_link_deltaBase_card_le_bound {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk : 2 ≤ k)
    (havoid : AvoidsSingleton 𝓕) (x : Fin n) :
    (closedDeltaBase k (link 𝓕 x)).card ≤
      closedBaseCountBound k (k - 1) := by
  have hbasecard :
      ∀ B ∈ closedDeltaBase k (link 𝓕 x), B.card ≤ k - 1 := by
    intro B hB
    exact kernelReachable_card_le
      (fun A hA => by rw [link_uniform huniform x A hA]) hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hB).1)
  have hsub :
      closedDeltaBase k (link 𝓕 x) ⊆
        (range ((k - 1) + 1)).biUnion
          (fun t => closedBaseOfCard k (link 𝓕 x) t) := by
    intro B hB
    apply mem_biUnion.mpr
    refine ⟨B.card, ?_, ?_⟩
    · simp [hbasecard B hB]
    · exact mem_filter.mpr ⟨hB, rfl⟩
  calc
    (closedDeltaBase k (link 𝓕 x)).card ≤
        ((range ((k - 1) + 1)).biUnion
          (fun t => closedBaseOfCard k (link 𝓕 x) t)).card :=
      card_le_card hsub
    _ ≤ ∑ t ∈ range ((k - 1) + 1),
        (closedBaseOfCard k (link 𝓕 x) t).card :=
      card_biUnion_le
    _ ≤ ∑ t ∈ range ((k - 1) + 1), sunflowerBound t k := by
      apply sum_le_sum
      intro t ht
      exact closed_link_bases_card_le_sunflowerBound huniform hk havoid x

def HasSmallClosedLinkBase {n k : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n) : Prop :=
  ∃ B ∈ closedDeltaBase k (link 𝓕 x), B.card ≤ 2

lemma card_link_le_closedBaseCountBound_mul_pow_of_no_small_base
    {n k : ℕ} {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (havoid : AvoidsSingleton 𝓕) (hn : 1 ≤ n) (x : Fin n)
    (hnosmall : ¬ HasSmallClosedLinkBase (k := k) 𝓕 x) :
    (link 𝓕 x).card ≤
      closedBaseCountBound k (k - 1) * n ^ (k - 4) := by
  have hk : 2 ≤ k := by omega
  have hk1 : 1 < k := by omega
  have hbasebound :=
    closed_link_deltaBase_card_le_bound huniform hk havoid x
  have hterm :
      ∀ B ∈ closedDeltaBase k (link 𝓕 x),
        Nat.choose n ((k - 1) - B.card) ≤ n ^ (k - 4) := by
    intro B hB
    have hBlarge : 3 ≤ B.card := by
      by_contra hnot
      apply hnosmall
      exact ⟨B, hB, by omega⟩
    have hexp : (k - 1) - B.card ≤ k - 4 := by omega
    calc
      Nat.choose n ((k - 1) - B.card) ≤ n ^ ((k - 1) - B.card) :=
        Nat.choose_le_pow _ _
      _ ≤ n ^ (k - 4) := pow_le_pow_right' hn hexp
  calc
    (link 𝓕 x).card ≤
        ∑ B ∈ closedDeltaBase k (link 𝓕 x),
          Nat.choose n ((k - 1) - B.card) :=
      card_link_le_sum_closed_bases huniform hk1 x
    _ ≤ ∑ _B ∈ closedDeltaBase k (link 𝓕 x), n ^ (k - 4) := by
      apply sum_le_sum
      intro B hB
      exact hterm B hB
    _ = (closedDeltaBase k (link 𝓕 x)).card * n ^ (k - 4) := by simp
    _ ≤ closedBaseCountBound k (k - 1) * n ^ (k - 4) :=
      Nat.mul_le_mul_right _ hbasebound

/-! ## Eventual binomial comparisons -/

open scoped Topology

lemma tendsto_choose_add_div_pow_702 (r c : ℕ) :
    Filter.Tendsto
      (fun d : ℕ => ((Nat.choose (d + c) r : ℕ) : ℝ) / (d : ℝ) ^ r)
      Filter.atTop (𝓝 ((1 : ℝ) / r.factorial)) := by
  have hshift := (isEquivalent_choose r).comp_tendsto (tendsto_add_atTop_nat c)
  have hequiv := hshift.div
    (IsEquivalent.refl :
      (fun d : ℕ => ((d : ℝ) ^ r)) ~[Filter.atTop]
        (fun d : ℕ => ((d : ℝ) ^ r)))
  have hratio :
      Filter.Tendsto (fun d : ℕ =>
        (((d + c : ℕ) : ℝ) / (d : ℝ))) Filter.atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1
        (by norm_num : (1 : ℝ) ≠ 0))
  have href :
      Filter.Tendsto (fun d : ℕ =>
        (((((d + c : ℕ) : ℝ) / (d : ℝ)) ^ r) / (r.factorial : ℝ)))
        Filter.atTop (𝓝 ((1 : ℝ) / r.factorial)) := by
    simpa using (hratio.pow r).div_const (r.factorial : ℝ)
  apply (IsEquivalent.tendsto_nhds_iff hequiv).2
  refine href.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  dsimp
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

lemma eventually_const_mul_pow_lt_choose (C d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * n ^ d < Nat.choose n (d + 1) := by
  let r := d + 1
  have hlim := tendsto_choose_add_div_pow_702 r 0
  have hhalf :
      (0 : ℝ) < (1 : ℝ) / (2 * r.factorial) := by positivity
  have hhalf_lt :
      (1 : ℝ) / (2 * r.factorial) < (1 : ℝ) / r.factorial := by
    have hfac : (0 : ℝ) < r.factorial := by positivity
    rw [div_lt_div_iff₀ (by positivity) hfac]
    nlinarith
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      (1 : ℝ) / (2 * r.factorial) <
        ((Nat.choose (n + 0) r : ℕ) : ℝ) / (n : ℝ) ^ r :=
    hlim.eventually (lt_mem_nhds hhalf_lt)
  filter_upwards [hratio,
      Filter.eventually_gt_atTop (2 * C * r.factorial),
      Filter.eventually_gt_atTop 0] with n hnratio hnlarge hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnlargeR : (2 * C * r.factorial : ℝ) < n := by exact_mod_cast hnlarge
  have hpowd : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  have hpwr : (0 : ℝ) < (n : ℝ) ^ r := by positivity
  have hleft :
      (C : ℝ) * (n : ℝ) ^ d <
        (n : ℝ) ^ r / (2 * r.factorial) := by
    have hmul := mul_lt_mul_of_pos_right hnlargeR hpowd
    dsimp [r] at hmul ⊢
    rw [pow_succ]
    have hden : (0 : ℝ) < 2 * (d + 1).factorial := by positivity
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hright :
      (n : ℝ) ^ r / (2 * r.factorial) <
        (Nat.choose n r : ℝ) := by
    have hratio' : (1 : ℝ) / (2 * r.factorial) <
        (Nat.choose n r : ℝ) / (n : ℝ) ^ r := by
      simpa using hnratio
    have hmul := (lt_div_iff₀ hpwr).mp hratio'
    calc
      (n : ℝ) ^ r / (2 * r.factorial) =
          ((1 : ℝ) / (2 * r.factorial)) * (n : ℝ) ^ r := by ring
      _ < (Nat.choose n r : ℝ) := hmul
  have hreal : (C * n ^ d : ℕ) < Nat.choose n r := by
    exact_mod_cast (hleft.trans hright)
  simpa [r] using hreal

lemma eventually_const_mul_pow_lt_choose_sub (C d s : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * n ^ d < Nat.choose (n - s) (d + 1) := by
  have hbase :
      ∀ᶠ m : ℕ in Filter.atTop,
        (C * 2 ^ d) * m ^ d < Nat.choose m (d + 1) :=
    eventually_const_mul_pow_lt_choose (C * 2 ^ d) d
  have hshift :
      ∀ᶠ n : ℕ in Filter.atTop,
        (C * 2 ^ d) * (n - s) ^ d <
          Nat.choose (n - s) (d + 1) :=
    (tendsto_sub_atTop_nat s).eventually hbase
  filter_upwards [hshift, Filter.eventually_ge_atTop (2 * s)] with n hnbase hns
  have hnm : n ≤ 2 * (n - s) := by omega
  have hpow : n ^ d ≤ (2 * (n - s)) ^ d :=
    Nat.pow_le_pow_left hnm d
  calc
    C * n ^ d ≤ C * (2 * (n - s)) ^ d :=
      Nat.mul_le_mul_left _ hpow
    _ = (C * 2 ^ d) * (n - s) ^ d := by rw [mul_pow]; ring
    _ < Nat.choose (n - s) (d + 1) := hnbase

lemma exists_threshold_small_base_of_large_degree (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))) (x : Fin n),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card →
        HasSmallClosedLinkBase (k := k) 𝓕 x := by
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        closedBaseCountBound k (k - 1) * n ^ (k - 4) <
          Nat.choose (n - 3) ((k - 4) + 1) :=
    eventually_const_mul_pow_lt_choose_sub
      (closedBaseCountBound k (k - 1)) (k - 4) 3
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 1, ?_⟩
  intro n hn 𝓕 x huniform havoid hdeg
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  by_contra hsmall
  have hupper :=
    card_link_le_closedBaseCountBound_mul_pow_of_no_small_base
      huniform hk4 havoid hn1 x hsmall
  have hstrict := hN n hnN
  have hchoose :
      Nat.choose (n - 3) (k - 3) =
        Nat.choose (n - 3) ((k - 4) + 1) := by
    congr 1
    omega
  rw [card_link_eq_degree] at hupper
  rw [hchoose] at hdeg
  omega

/-! ## Singleton link bases -/

def twoStar {n : ℕ} (k : ℕ) (x y : Fin n) :
    Finset (Finset (Fin n)) :=
  (univ.powersetCard k).filter ({x, y} ⊆ ·)

lemma card_twoStar {n k : ℕ} {x y : Fin n}
    (hxy : x ≠ y) (hk : 2 ≤ k) :
    (twoStar k x y).card = Nat.choose (n - 2) (k - 2) := by
  have hpaircard : ({x, y} : Finset (Fin n)).card = 2 := by simp [hxy]
  unfold twoStar
  rw [card_filter_powersetCard_subset]
  · rw [card_univ, Fintype.card_fin, hpaircard]
  · simp
  · rw [hpaircard]
    exact hk

lemma mem_of_singleton_closedLinkBase {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)) :
    ∀ A ∈ link 𝓕 x, y ∈ A := by
  intro A hA
  obtain ⟨B, hB, hBA⟩ :=
    exists_closedDeltaBase_subset_of_mem hA
      (by
        have hcard := link_uniform huniform x A hA
        exact card_pos.mp (by omega))
  have hnotdisj : ¬ Disjoint ({y} : Finset (Fin n)) B :=
    kernelClosure_link_intersecting huniform hk havoid x
      (mem_closedDeltaBase_iff.mp hybase).1
      (mem_closedDeltaBase_iff.mp hB).1
  have hyB : y ∈ B := by
    by_contra hyB
    apply hnotdisj
    simp [hyB]
  exact hBA hyB

lemma mem_iff_of_singleton_closedLinkBase {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)) :
    x ≠ y ∧ ∀ A ∈ 𝓕, (x ∈ A ↔ y ∈ A) := by
  have hk : 2 ≤ k := by omega
  have hxy : x ≠ y := by
    intro hxy
    subst y
    have hxnot :=
      kernelReachable_not_mem_of_link hk
        (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hybase).1)
    simp at hxnot
  refine ⟨hxy, ?_⟩
  intro A hA
  constructor
  · intro hxA
    let E := A.erase x
    have hElink : E ∈ link 𝓕 x := by
      rw [mem_link_iff]
      refine ⟨by simp [E], ?_⟩
      simpa [E, insert_erase hxA] using hA
    have hyE := mem_of_singleton_closedLinkBase huniform hk havoid hybase E hElink
    exact (mem_erase.mp hyE).2
  · intro hyA
    by_contra hxA
    have hK :
        KernelReachable k 𝓕 (insert x ({y} : Finset (Fin n))) :=
      kernelReachable_insert_of_link hk
        (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hybase).1)
    have hAne : A.Nonempty := by
      have hAcard := huniform A hA
      exact card_pos.mp (by omega)
    have hcompat := kernelReachable_compatible
      (q := k) (r := k) (𝓖 := 𝓕)
      havoid (fun C hC => by rw [huniform C hC]) hk (le_refl k)
      hK (KernelReachable.member hA hAne)
    apply hcompat
    have hinter :
        insert x ({y} : Finset (Fin n)) ∩ A = ({y} : Finset (Fin n)) := by
      ext z
      simp [hxA, hyA]
    rw [hinter]
    simp

lemma two_closed_link_bases_card_le {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕) (x : Fin n) :
    (closedBaseOfCard k (link 𝓕 x) 2).card ≤ 2 * (k - 1) := by
  let 𝓔 := closedBaseOfCard k (link 𝓕 x) 2
  have hk : 2 ≤ k := by omega
  by_cases h𝓔empty : 𝓔 = ∅
  · simp [𝓔, h𝓔empty]
  have h𝓔ne : 𝓔.Nonempty := nonempty_iff_ne_empty.mpr h𝓔empty
  obtain ⟨A, hA⟩ := h𝓔ne
  have hAcard : A.card = 2 := (mem_filter.mp hA).2
  have hmeet : ∀ B ∈ 𝓔, ∃ z ∈ A, z ∈ B := by
    intro B hB
    have hnotdisj : ¬ Disjoint A B :=
      kernelClosure_link_intersecting huniform hk havoid x
        (mem_closedDeltaBase_iff.mp (mem_filter.mp hA).1).1
        (mem_closedDeltaBase_iff.mp (mem_filter.mp hB).1).1
    obtain ⟨z, hzA, hzB⟩ := not_disjoint_iff.mp hnotdisj
    exact ⟨z, hzA, hzB⟩
  have hstar : ∀ z ∈ A, (pointStar 𝓔 z).card ≤ k - 1 := by
    intro z hzA
    have hlt : (pointStar 𝓔 z).card < k := by
      by_contra hnot
      have hkcard : k ≤ (pointStar 𝓔 z).card := by omega
      obtain ⟨𝓢, h𝓢sub, h𝓢card⟩ :=
        exists_subset_card_eq hkcard
      have hdelta : IsDeltaSystem ({z} : Finset (Fin n)) 𝓢 := by
        intro B hB C hC hBC
        have hBstar : B ∈ pointStar 𝓔 z := h𝓢sub hB
        have hCstar : C ∈ pointStar 𝓔 z := h𝓢sub hC
        have hzB : z ∈ B := (mem_filter.mp hBstar).2
        have hzC : z ∈ C := (mem_filter.mp hCstar).2
        have hBcard : B.card = 2 :=
          (mem_filter.mp (mem_filter.mp hBstar).1).2
        have hCcard : C.card = 2 :=
          (mem_filter.mp (mem_filter.mp hCstar).1).2
        ext w
        constructor
        · intro hw
          have hwB : w ∈ B := (mem_inter.mp hw).1
          have hwC : w ∈ C := (mem_inter.mp hw).2
          by_cases hwz : w = z
          · simp [hwz]
          · have hpaircard : ({z, w} : Finset (Fin n)).card = 2 := by
              have hzw : z ≠ w := by
                intro h
                exact hwz h.symm
              simp [hzw]
            have hpairB : ({z, w} : Finset (Fin n)) ⊆ B := by
              intro u hu
              simp only [mem_insert, mem_singleton] at hu
              rcases hu with rfl | rfl
              · exact hzB
              · exact hwB
            have hpairC : ({z, w} : Finset (Fin n)) ⊆ C := by
              intro u hu
              simp only [mem_insert, mem_singleton] at hu
              rcases hu with rfl | rfl
              · exact hzC
              · exact hwC
            have hBeq : B = {z, w} :=
              (eq_of_subset_of_card_le hpairB (by rw [hpaircard, hBcard])).symm
            have hCeq : C = {z, w} :=
              (eq_of_subset_of_card_le hpairC (by rw [hpaircard, hCcard])).symm
            exact (hBC (hBeq.trans hCeq.symm)).elim
        · intro hw
          have hwz : w = z := by simpa using hw
          subst w
          exact mem_inter.mpr ⟨hzB, hzC⟩
      apply no_deltaSystem_in_closed_link_bases huniform hk havoid x
        (𝓢 := 𝓢) (K := ({z} : Finset (Fin n)))
      · intro B hB
        have hBE : B ∈ 𝓔 := (mem_filter.mp (h𝓢sub hB)).1
        change B ∈ closedDeltaBase k (link 𝓕 x)
        exact (mem_filter.mp (show B ∈ closedBaseOfCard k (link 𝓕 x) 2 by
          simpa [𝓔] using hBE)).1
      · exact h𝓢card
      · exact hdelta
    omega
  calc
    𝓔.card ≤ A.card * (k - 1) :=
      card_le_card_mul_of_fibers_le hmeet hstar
    _ = 2 * (k - 1) := by rw [hAcard]

/-! ## Matching bounds used by the structural argument -/

lemma card_pointStar_le_choose {n r : ℕ}
    {𝓖 : Finset (Finset (Fin n))}
    (huniform : ∀ A ∈ 𝓖, A.card = r) (x : Fin n) :
    (pointStar 𝓖 x).card ≤ Nat.choose n (r - 1) := by
  classical
  let eraseX : Finset (Fin n) → Finset (Fin n) := fun A => A.erase x
  have herase_inj : Set.InjOn eraseX (pointStar 𝓖 x) := by
    intro A hA B hB hEq
    have hxA : x ∈ A := (mem_filter.mp hA).2
    have hxB : x ∈ B := (mem_filter.mp hB).2
    calc
      A = insert x (A.erase x) := (insert_erase hxA).symm
      _ = insert x (B.erase x) := congrArg (insert x) hEq
      _ = B := insert_erase hxB
  have himage_sub :
      (pointStar 𝓖 x).image eraseX ⊆
        (univ : Finset (Fin n)).powersetCard (r - 1) := by
    intro D hD
    rw [mem_image] at hD
    obtain ⟨A, hA, rfl⟩ := hD
    have hAmem : A ∈ 𝓖 := (mem_filter.mp hA).1
    have hxA : x ∈ A := (mem_filter.mp hA).2
    rw [mem_powersetCard]
    refine ⟨by simp, ?_⟩
    have hcard := card_erase_add_one hxA
    rw [huniform A hAmem] at hcard
    have hrpos : 0 < r := by omega
    change (A.erase x).card = r - 1
    omega
  calc
    (pointStar 𝓖 x).card = ((pointStar 𝓖 x).image eraseX).card := by
      rw [card_image_of_injOn herase_inj]
    _ ≤ ((univ : Finset (Fin n)).powersetCard (r - 1)).card :=
      card_le_card himage_sub
    _ = Nat.choose n (r - 1) := by simp

lemma card_le_matchingBound_of_no_disjoint_subfamily {n r q : ℕ}
    {𝓖 : Finset (Finset (Fin n))}
    (hr : 0 < r) (huniform : ∀ A ∈ 𝓖, A.card = r)
    (hno : ∀ 𝓜 : Finset (Finset (Fin n)), 𝓜 ⊆ 𝓖 →
      PairwiseDisjointFamily 𝓜 → 𝓜.card < q) :
    𝓖.card ≤ r * (q - 1) * Nat.choose n (r - 1) := by
  obtain ⟨𝓜, h𝓜sub, h𝓜pw, hmax⟩ :=
    exists_max_pairwiseDisjoint_subfamily 𝓖
  have h𝓜small : 𝓜.card ≤ q - 1 := by
    have := hno 𝓜 h𝓜sub h𝓜pw
    omega
  let U : Finset (Fin n) := 𝓜.biUnion id
  have hUcard : U.card ≤ r * (q - 1) := by
    calc
      U.card = 𝓜.card * r := by
        exact card_biUnion_id_of_pairwiseDisjoint_uniform h𝓜pw
          (fun A hA => huniform A (h𝓜sub hA))
      _ ≤ (q - 1) * r := Nat.mul_le_mul_right _ h𝓜small
      _ = r * (q - 1) := by rw [Nat.mul_comm]
  have hmeet : ∀ A ∈ 𝓖, ∃ x ∈ U, x ∈ A := by
    intro A hA
    by_contra hnone
    push Not at hnone
    have hdisj : ∀ B ∈ 𝓜, Disjoint A B := by
      intro B hB
      rw [disjoint_left]
      intro x hxA hxB
      exact hnone x (mem_biUnion.mpr ⟨B, hB, hxB⟩) hxA
    have hAM := mem_of_disjoint_from_maximal hmax h𝓜sub h𝓜pw hA hdisj
    have hAA := hdisj A hAM
    rw [disjoint_self] at hAA
    have hAempty : A = ∅ := hAA
    have hAcard := huniform A hA
    rw [hAempty] at hAcard
    simp at hAcard
    omega
  have hstar : ∀ x ∈ U, (pointStar 𝓖 x).card ≤ Nat.choose n (r - 1) := by
    intro x hx
    exact card_pointStar_le_choose huniform x
  calc
    𝓖.card ≤ U.card * Nat.choose n (r - 1) :=
      card_le_card_mul_of_fibers_le hmeet hstar
    _ ≤ (r * (q - 1)) * Nat.choose n (r - 1) :=
      Nat.mul_le_mul_right _ hUcard
    _ = r * (q - 1) * Nat.choose n (r - 1) := rfl

/-! ## Dominant two-bases -/

def HasSingletonClosedLinkBase {n k : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n) : Prop :=
  ∃ y : Fin n, ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)

noncomputable def closedTwoBases {n : ℕ} (k : ℕ)
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n) :
    Finset (Finset (Fin n)) :=
  closedBaseOfCard k (link 𝓕 x) 2

noncomputable def closedLargeBases {n : ℕ} (k : ℕ)
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n) :
    Finset (Finset (Fin n)) :=
  (closedDeltaBase k (link 𝓕 x)).filter fun B => 3 ≤ B.card

def linkBranch {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (x : Fin n) (B : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  supersetsInFamily (link 𝓕 x) B

lemma link_subset_two_and_large_base_branches {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (x : Fin n)
    (hnosingle : ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x) :
    link 𝓕 x ⊆
      (closedTwoBases k 𝓕 x).biUnion (linkBranch 𝓕 x) ∪
        (closedLargeBases k 𝓕 x).biUnion (linkBranch 𝓕 x) := by
  intro A hA
  obtain ⟨B, hB, hBA⟩ :=
    exists_closedDeltaBase_subset_of_mem hA
      (by
        have hcard := link_uniform huniform x A hA
        exact card_pos.mp (by omega))
  have hBne : B.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hB).1)
  have hBcard_ne_one : B.card ≠ 1 := by
    intro hBone
    obtain ⟨y, rfl⟩ := card_eq_one.mp hBone
    exact hnosingle ⟨y, hB⟩
  have hBtwo_or_large : B.card = 2 ∨ 3 ≤ B.card := by
    have : 0 < B.card := card_pos.mpr hBne
    omega
  rcases hBtwo_or_large with hBtwo | hBlarge
  · apply mem_union_left
    apply mem_biUnion.mpr
    refine ⟨B, ?_, ?_⟩
    · exact mem_filter.mpr ⟨hB, hBtwo⟩
    · exact mem_filter.mpr ⟨hA, hBA⟩
  · apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨B, ?_, ?_⟩
    · exact mem_filter.mpr ⟨hB, hBlarge⟩
    · exact mem_filter.mpr ⟨hA, hBA⟩

lemma card_large_base_branches_le {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    (hn : 1 ≤ n) (x : Fin n) :
    ((closedLargeBases k 𝓕 x).biUnion (linkBranch 𝓕 x)).card ≤
      closedBaseCountBound k (k - 1) * n ^ (k - 4) := by
  have hk : 2 ≤ k := by omega
  have hbasebound :=
    closed_link_deltaBase_card_le_bound huniform hk havoid x
  have hbranch :
      ∀ B ∈ closedLargeBases k 𝓕 x,
        (linkBranch 𝓕 x B).card ≤ n ^ (k - 4) := by
    intro B hB
    have hBbase : B ∈ closedDeltaBase k (link 𝓕 x) :=
      (mem_filter.mp hB).1
    have hBlarge : 3 ≤ B.card := (mem_filter.mp hB).2
    have hexp : (k - 1) - B.card ≤ k - 4 := by omega
    calc
      (linkBranch 𝓕 x B).card ≤ Nat.choose n ((k - 1) - B.card) := by
        apply card_supersetsInFamily_le_choose
        · exact link_uniform huniform x
        · rfl
      _ ≤ n ^ ((k - 1) - B.card) := Nat.choose_le_pow _ _
      _ ≤ n ^ (k - 4) := pow_le_pow_right' hn hexp
  calc
    ((closedLargeBases k 𝓕 x).biUnion (linkBranch 𝓕 x)).card ≤
        ∑ B ∈ closedLargeBases k 𝓕 x, (linkBranch 𝓕 x B).card :=
      card_biUnion_le
    _ ≤ ∑ _B ∈ closedLargeBases k 𝓕 x, n ^ (k - 4) := by
      apply sum_le_sum
      intro B hB
      exact hbranch B hB
    _ = (closedLargeBases k 𝓕 x).card * n ^ (k - 4) := by simp
    _ ≤ (closedDeltaBase k (link 𝓕 x)).card * n ^ (k - 4) := by
      apply Nat.mul_le_mul_right
      exact card_le_card (filter_subset _ _)
    _ ≤ closedBaseCountBound k (k - 1) * n ^ (k - 4) :=
      Nat.mul_le_mul_right _ hbasebound

lemma exists_dominant_two_base_of_large_link {n k m : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    (hn : 1 ≤ n) (x : Fin n)
    (hnosingle : ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x)
    (hlarge :
      2 * (k - 1) * m +
          closedBaseCountBound k (k - 1) * n ^ (k - 4) <
        (link 𝓕 x).card) :
    ∃ B ∈ closedTwoBases k 𝓕 x, m < (linkBranch 𝓕 x B).card := by
  by_contra hnone
  push Not at hnone
  have htwo :
      ((closedTwoBases k 𝓕 x).biUnion (linkBranch 𝓕 x)).card ≤
        2 * (k - 1) * m := by
    calc
      ((closedTwoBases k 𝓕 x).biUnion (linkBranch 𝓕 x)).card ≤
          ∑ B ∈ closedTwoBases k 𝓕 x, (linkBranch 𝓕 x B).card :=
        card_biUnion_le
      _ ≤ ∑ _B ∈ closedTwoBases k 𝓕 x, m := by
        apply sum_le_sum
        intro B hB
        exact hnone B hB
      _ = (closedTwoBases k 𝓕 x).card * m := by simp
      _ ≤ (2 * (k - 1)) * m := by
        apply Nat.mul_le_mul_right
        exact two_closed_link_bases_card_le huniform hk4 havoid x
      _ = 2 * (k - 1) * m := rfl
  have hlargeBranches := card_large_base_branches_le huniform hk4 havoid hn x
  have hcover := link_subset_two_and_large_base_branches huniform hk4 x hnosingle
  have hcardcover := card_le_card hcover
  have hunion :=
    card_union_le
      ((closedTwoBases k 𝓕 x).biUnion (linkBranch 𝓕 x))
      ((closedLargeBases k 𝓕 x).biUnion (linkBranch 𝓕 x))
  omega

lemma exists_threshold_dominant_two_base (k M : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))) (x : Fin n),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card →
        ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x →
        ∃ B ∈ closedTwoBases k 𝓕 x,
          M * n ^ (k - 4) < (linkBranch 𝓕 x B).card := by
  let C := 2 * (k - 1) * M + closedBaseCountBound k (k - 1)
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        C * n ^ (k - 4) <
          Nat.choose (n - 3) ((k - 4) + 1) :=
    eventually_const_mul_pow_lt_choose_sub C (k - 4) 3
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 1, ?_⟩
  intro n hn 𝓕 x huniform havoid hdeg hnosingle
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hstrict := hN n hnN
  have hchoose :
      Nat.choose (n - 3) (k - 3) =
        Nat.choose (n - 3) ((k - 4) + 1) := by
    congr 1
    omega
  rw [← hchoose] at hstrict
  have hlinklower : Nat.choose (n - 3) (k - 3) ≤ (link 𝓕 x).card := by
    rw [card_link_eq_degree]
    exact hdeg
  have hlarge :
      2 * (k - 1) * (M * n ^ (k - 4)) +
          closedBaseCountBound k (k - 1) * n ^ (k - 4) <
        (link 𝓕 x).card := by
    dsimp [C] at hstrict
    have hcalc :
        2 * (k - 1) * (M * n ^ (k - 4)) +
            closedBaseCountBound k (k - 1) * n ^ (k - 4) =
          (2 * (k - 1) * M + closedBaseCountBound k (k - 1)) *
            n ^ (k - 4) := by ring
    rw [hcalc]
    exact hstrict.trans_le hlinklower
  exact exists_dominant_two_base_of_large_link
    huniform hk4 havoid hn1 x hnosingle hlarge

lemma card_family_meeting_le {n r : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    (huniform : ∀ A ∈ 𝓖, A.card = r)
    (hmeet : ∀ A ∈ 𝓖, ∃ z ∈ U, z ∈ A) :
    𝓖.card ≤ U.card * Nat.choose n (r - 1) := by
  apply card_le_card_mul_of_fibers_le hmeet
  intro z hz
  exact card_pointStar_le_choose huniform z

lemma exists_large_pointStar_of_card_gt {n : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {U : Finset (Fin n)} {m : ℕ}
    (hmeet : ∀ A ∈ 𝓖, ∃ z ∈ U, z ∈ A)
    (hlarge : U.card * m < 𝓖.card) :
    ∃ z ∈ U, m < (pointStar 𝓖 z).card := by
  by_contra hnone
  push Not at hnone
  have hle := card_le_card_mul_of_fibers_le hmeet hnone
  omega

lemma exists_deltaSystem_of_large_supersets {n r t q : ℕ}
    {𝓖 : Finset (Finset (Fin n))} {B : Finset (Fin n)}
    (huniform : ∀ A ∈ 𝓖, A.card = r) (hBcard : B.card = t)
    (hpos : 0 < r - t)
    (hlarge :
      (r - t) * (q - 1) * Nat.choose n ((r - t) - 1) <
        (supersetsInFamily 𝓖 B).card) :
    ∃ 𝓢 : Finset (Finset (Fin n)),
      𝓢 ⊆ supersetsInFamily 𝓖 B ∧ 𝓢.card = q ∧ IsDeltaSystem B 𝓢 := by
  classical
  let 𝓔 : Finset (Finset (Fin n)) :=
    (supersetsInFamily 𝓖 B).image fun A => A \ B
  have herase_inj :
      Set.InjOn (fun A : Finset (Fin n) => A \ B)
        (supersetsInFamily 𝓖 B) := by
    intro A hA C hC hEq
    have hBA : B ⊆ A := (mem_filter.mp hA).2
    have hBC : B ⊆ C := (mem_filter.mp hC).2
    calc
      A = (A \ B) ∪ B := (sdiff_union_of_subset hBA).symm
      _ = (C \ B) ∪ B := congrArg (fun D => D ∪ B) hEq
      _ = C := sdiff_union_of_subset hBC
  have h𝓔card : 𝓔.card = (supersetsInFamily 𝓖 B).card := by
    unfold 𝓔
    exact card_image_of_injOn herase_inj
  have h𝓔uniform : ∀ D ∈ 𝓔, D.card = r - t := by
    intro D hD
    unfold 𝓔 at hD
    rw [mem_image] at hD
    obtain ⟨A, hA, rfl⟩ := hD
    have hAmem : A ∈ 𝓖 := (mem_filter.mp hA).1
    have hBA : B ⊆ A := (mem_filter.mp hA).2
    rw [card_sdiff_of_subset hBA, huniform A hAmem, hBcard]
  have hexmatch :
      ∃ 𝓜 : Finset (Finset (Fin n)),
        𝓜 ⊆ 𝓔 ∧ PairwiseDisjointFamily 𝓜 ∧ q ≤ 𝓜.card := by
    by_contra hnone
    push Not at hnone
    have hno : ∀ 𝓜 : Finset (Finset (Fin n)), 𝓜 ⊆ 𝓔 →
        PairwiseDisjointFamily 𝓜 → 𝓜.card < q := by
      intro 𝓜 h𝓜sub h𝓜pw
      exact hnone 𝓜 h𝓜sub h𝓜pw
    have hupper :=
      card_le_matchingBound_of_no_disjoint_subfamily
        hpos h𝓔uniform hno
    rw [h𝓔card] at hupper
    omega
  obtain ⟨𝓜, h𝓜sub, h𝓜pw, hqM⟩ := hexmatch
  obtain ⟨𝓜q, h𝓜qsub, h𝓜qcard⟩ := exists_subset_card_eq hqM
  let lift : Finset (Fin n) → Finset (Fin n) := fun D => D ∪ B
  let 𝓢 : Finset (Finset (Fin n)) := 𝓜q.image lift
  have hdisjB : ∀ D ∈ 𝓜q, Disjoint D B := by
    intro D hD
    have hDE : D ∈ 𝓔 := h𝓜sub (h𝓜qsub hD)
    unfold 𝓔 at hDE
    rw [mem_image] at hDE
    obtain ⟨A, hA, rfl⟩ := hDE
    exact disjoint_sdiff_self_left
  have hlift_inj : Set.InjOn lift 𝓜q := by
    intro D hD E hE hEq
    ext z
    have hDB := hdisjB D hD
    have hEB := hdisjB E hE
    have hz : (z ∈ D ∨ z ∈ B) ↔ (z ∈ E ∨ z ∈ B) := by
      simpa [lift] using congrArg (fun A : Finset (Fin n) => z ∈ A) hEq
    constructor
    · intro hzD
      rcases hz.mp (Or.inl hzD) with hzE | hzB
      · exact hzE
      · exact (disjoint_left.mp hDB hzD hzB).elim
    · intro hzE
      rcases hz.mpr (Or.inl hzE) with hzD | hzB
      · exact hzD
      · exact (disjoint_left.mp hEB hzE hzB).elim
  have h𝓢card : 𝓢.card = q := by
    change (𝓜q.image lift).card = q
    rw [card_image_of_injOn hlift_inj, h𝓜qcard]
  have h𝓢sub : 𝓢 ⊆ supersetsInFamily 𝓖 B := by
    intro A hA
    change A ∈ 𝓜q.image lift at hA
    rw [mem_image] at hA
    obtain ⟨D, hD, rfl⟩ := hA
    have hDE : D ∈ 𝓔 := h𝓜sub (h𝓜qsub hD)
    unfold 𝓔 at hDE
    rw [mem_image] at hDE
    obtain ⟨C, hC, hCD⟩ := hDE
    have hBC : B ⊆ C := (mem_filter.mp hC).2
    have hEq : D ∪ B = C := by
      rw [← hCD]
      exact sdiff_union_of_subset hBC
    change D ∪ B ∈ supersetsInFamily 𝓖 B
    rw [hEq]
    exact hC
  refine ⟨𝓢, h𝓢sub, h𝓢card, ?_⟩
  intro A hA C hC hAC
  change A ∈ 𝓜q.image lift at hA
  change C ∈ 𝓜q.image lift at hC
  rw [mem_image] at hA hC
  obtain ⟨D, hD, rfl⟩ := hA
  obtain ⟨E, hE, rfl⟩ := hC
  have hDE : D ≠ E := by
    intro h
    exact hAC (by simp [lift, h])
  have hdisjDE : Disjoint D E :=
    h𝓜pw D (h𝓜qsub hD) E (h𝓜qsub hE) hDE
  have hDB := hdisjB D hD
  have hEB := hdisjB E hE
  ext z
  simp only [lift, mem_inter, mem_union]
  constructor
  · rintro ⟨hzD | hzB, hzE | hzB'⟩
    · exact (disjoint_left.mp hdisjDE hzD hzE).elim
    · exact hzB'
    · exact hzB
    · exact hzB
  · intro hzB
    exact ⟨Or.inr hzB, Or.inr hzB⟩

lemma exists_threshold_two_base_with_link_sunflower
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))) (x : Fin n),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card →
        ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x →
        ∃ B ∈ closedTwoBases k 𝓕 x,
          ∃ 𝓢 : Finset (Finset (Fin n)),
            𝓢 ⊆ linkBranch 𝓕 x B ∧ 𝓢.card = k ∧ IsDeltaSystem B 𝓢 := by
  let M := (k - 3) * (k - 1) + 1
  obtain ⟨N, hN⟩ := exists_threshold_dominant_two_base k M hk4
  refine ⟨N, ?_⟩
  intro n hn 𝓕 x huniform havoid hdeg hnosingle
  obtain ⟨B, hB, hbranch⟩ :=
    hN n hn 𝓕 x huniform havoid hdeg hnosingle
  have hBcard : B.card = 2 := (mem_filter.mp hB).2
  have hmatching :
      (k - 3) * (k - 1) * Nat.choose n ((k - 3) - 1) <
        (linkBranch 𝓕 x B).card := by
    have hchoose : Nat.choose n ((k - 3) - 1) ≤ n ^ (k - 4) := by
      have hexp : (k - 3) - 1 = k - 4 := by omega
      rw [hexp]
      exact Nat.choose_le_pow _ _
    have hcoeff :
        (k - 3) * (k - 1) * Nat.choose n ((k - 3) - 1) ≤
          (k - 3) * (k - 1) * n ^ (k - 4) :=
      Nat.mul_le_mul_left _ hchoose
    have hM :
        (k - 3) * (k - 1) * n ^ (k - 4) <
          M * n ^ (k - 4) := by
      dsimp [M]
      have hpowpos : 0 < n ^ (k - 4) := by
        have hnpos : 0 < n := by
          exact Nat.pos_of_ne_zero (by
            intro hn0
            subst n
            exact Fin.elim0 x)
        positivity
      nlinarith
    exact hcoeff.trans_lt (hM.trans hbranch)
  refine ⟨B, hB, ?_⟩
  apply exists_deltaSystem_of_large_supersets
    (r := k - 1) (t := 2) (q := k)
  · exact link_uniform huniform x
  · exact hBcard
  · omega
  · change
      (k - 1 - 2) * (k - 1) * Nat.choose n (k - 1 - 2 - 1) <
        (linkBranch 𝓕 x B).card
    have h1 : k - 1 - 2 = k - 3 := by omega
    rw [h1]
    exact hmatching

lemma inter_card_eq_one_of_not_subset_two_closedBase {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x : Fin n} {B A : Finset (Fin n)}
    (hB : B ∈ closedTwoBases k 𝓕 x) (hA : A ∈ link 𝓕 x)
    (hnot : ¬ B ⊆ A) :
    (A ∩ B).card = 1 := by
  have hBbase : B ∈ closedDeltaBase k (link 𝓕 x) := (mem_filter.mp hB).1
  have hBcard : B.card = 2 := (mem_filter.mp hB).2
  have hnotdisj : ¬ Disjoint A B :=
    kernelClosure_link_intersecting huniform hk havoid x
      (mem_kernelClosure_iff.mpr
        (KernelReachable.member hA
          (by
            have hcard := link_uniform huniform x A hA
            exact card_pos.mp (by omega))))
      (mem_closedDeltaBase_iff.mp hBbase).1
  have hpos : 0 < (A ∩ B).card := by
    exact card_pos.mpr (not_disjoint_iff_nonempty_inter.mp hnotdisj)
  have hle : (A ∩ B).card ≤ 2 := by
    calc
      (A ∩ B).card ≤ B.card := card_le_card inter_subset_right
      _ = 2 := hBcard
  have hne2 : (A ∩ B).card ≠ 2 := by
    intro hcard
    have hBA : B ⊆ A := by
      have heq : A ∩ B = B :=
        eq_of_subset_of_card_le inter_subset_right (by rw [hBcard, hcard])
      intro z hzB
      have hz : z ∈ A ∩ B := by rw [heq]; exact hzB
      exact (mem_inter.mp hz).1
    exact hnot hBA
  omega

def branchAvoiding {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (x : Fin n) (B H : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (linkBranch 𝓕 x B).filter fun A => Disjoint (A \ B) (H \ B)

lemma card_bad_branch_le {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    {x : Fin n} {B H : Finset (Fin n)} (hBcard : B.card = 2) :
    ((linkBranch 𝓕 x B).filter fun A => ¬ Disjoint (A \ B) (H \ B)).card ≤
      H.card * Nat.choose n (k - 4) := by
  let bad :=
    (linkBranch 𝓕 x B).filter fun A => ¬ Disjoint (A \ B) (H \ B)
  have hmeet : ∀ A ∈ bad, ∃ z ∈ H \ B, z ∈ A := by
    intro A hA
    have hnotdisj : ¬ Disjoint (A \ B) (H \ B) :=
      (mem_filter.mp hA).2
    obtain ⟨z, hzAB, hzHB⟩ := not_disjoint_iff.mp hnotdisj
    exact ⟨z, hzHB, (mem_sdiff.mp hzAB).1⟩
  have hstar :
      ∀ z ∈ H \ B, (pointStar bad z).card ≤ Nat.choose n (k - 4) := by
    intro z hz
    have hzB : z ∉ B := (mem_sdiff.mp hz).2
    have hpaircard : (insert z B).card = 3 := by
      rw [card_insert_of_notMem hzB, hBcard]
    have hsub :
        pointStar bad z ⊆ supersetsInFamily (link 𝓕 x) (insert z B) := by
      intro A hA
      have hAbad : A ∈ bad := (mem_filter.mp hA).1
      have hAbranch : A ∈ linkBranch 𝓕 x B := (mem_filter.mp hAbad).1
      have hBA : B ⊆ A := (mem_filter.mp hAbranch).2
      have hzA : z ∈ A := (mem_filter.mp hA).2
      exact mem_filter.mpr
        ⟨(mem_filter.mp hAbranch).1, insert_subset hzA hBA⟩
    calc
      (pointStar bad z).card ≤
          (supersetsInFamily (link 𝓕 x) (insert z B)).card :=
        card_le_card hsub
      _ ≤ Nat.choose n ((k - 1) - 3) := by
        apply card_supersetsInFamily_le_choose
        · exact link_uniform huniform x
        · exact hpaircard
      _ = Nat.choose n (k - 4) := by
        congr 1
  calc
    ((linkBranch 𝓕 x B).filter fun A =>
        ¬ Disjoint (A \ B) (H \ B)).card = bad.card := rfl
    _ ≤ (H \ B).card * Nat.choose n (k - 4) :=
      card_le_card_mul_of_fibers_le hmeet hstar
    _ ≤ H.card * Nat.choose n (k - 4) := by
      apply Nat.mul_le_mul_right
      exact card_le_card sdiff_subset

lemma card_branchAvoiding_gt_of_branch_gt {n k Q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    {x : Fin n} {B H : Finset (Fin n)} (hBcard : B.card = 2)
    (hlarge :
      (H.card + Q) * n ^ (k - 4) < (linkBranch 𝓕 x B).card) :
    Q * n ^ (k - 4) < (branchAvoiding 𝓕 x B H).card := by
  have hbad := card_bad_branch_le huniform hBcard (x := x) (H := H)
  have hbad' :
      ((linkBranch 𝓕 x B).filter fun A =>
        ¬ Disjoint (A \ B) (H \ B)).card ≤
        H.card * n ^ (k - 4) :=
    hbad.trans (Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _))
  have hsplit :=
    card_filter_add_card_filter_not
      (s := linkBranch 𝓕 x B)
      (p := fun A => Disjoint (A \ B) (H \ B))
  change
    (branchAvoiding 𝓕 x B H).card +
        ((linkBranch 𝓕 x B).filter fun A =>
          ¬ Disjoint (A \ B) (H \ B)).card =
      (linkBranch 𝓕 x B).card at hsplit
  have hsum :
      (H.card + Q) * n ^ (k - 4) =
        H.card * n ^ (k - 4) + Q * n ^ (k - 4) := by
    ring
  rw [hsum] at hlarge
  omega

lemma exists_outside_pointStar_of_good_branch_gt {n k Q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk5 : 5 ≤ k) {x : Fin n} {B H : Finset (Fin n)}
    (hBcard : B.card = 2)
    (hlarge :
      Q * n ^ (k - 4) < (branchAvoiding 𝓕 x B H).card) :
    ∃ z ∈ (univ : Finset (Fin n)) \ H,
      Q * n ^ (k - 5) <
        (pointStar (branchAvoiding 𝓕 x B H) z).card := by
  let U : Finset (Fin n) := (univ : Finset (Fin n)) \ H
  have hmeet :
      ∀ A ∈ branchAvoiding 𝓕 x B H, ∃ z ∈ U, z ∈ A := by
    intro A hA
    have hAbranch : A ∈ linkBranch 𝓕 x B := (mem_filter.mp hA).1
    have hBA : B ⊆ A := (mem_filter.mp hAbranch).2
    have hAlink : A ∈ link 𝓕 x := (mem_filter.mp hAbranch).1
    have hAcard : A.card = k - 1 := link_uniform huniform x A hAlink
    have hdiffcard : (A \ B).card = k - 3 := by
      rw [card_sdiff_of_subset hBA, hAcard, hBcard]
      omega
    have hdiffpos : 0 < (A \ B).card := by rw [hdiffcard]; omega
    obtain ⟨z, hzAB⟩ := card_pos.mp hdiffpos
    have hzA : z ∈ A := (mem_sdiff.mp hzAB).1
    have hzB : z ∉ B := (mem_sdiff.mp hzAB).2
    have hdisj : Disjoint (A \ B) (H \ B) := (mem_filter.mp hA).2
    have hzH : z ∉ H := by
      intro hzH
      exact disjoint_left.mp hdisj hzAB (mem_sdiff.mpr ⟨hzH, hzB⟩)
    exact ⟨z, by simp [U, hzH], hzA⟩
  have hUcard : U.card ≤ n := by
    calc
      U.card ≤ (univ : Finset (Fin n)).card := card_le_card sdiff_subset
      _ = n := by simp
  have hmul :
      U.card * (Q * n ^ (k - 5)) ≤ Q * n ^ (k - 4) := by
    calc
      U.card * (Q * n ^ (k - 5)) ≤ n * (Q * n ^ (k - 5)) :=
        Nat.mul_le_mul_right _ hUcard
      _ = Q * n ^ (k - 4) := by
        have hexp : k - 4 = (k - 5) + 1 := by omega
        rw [hexp, pow_succ]
        ring
  have hbig :
      U.card * (Q * n ^ (k - 5)) <
        (branchAvoiding 𝓕 x B H).card :=
    hmul.trans_lt hlarge
  exact exists_large_pointStar_of_card_gt hmeet hbig

lemma exists_deltaSystem_insert_of_large_good_pointStar {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk5 : 5 ≤ k) {x z : Fin n} {B H : Finset (Fin n)}
    (hBcard : B.card = 2) (hzB : z ∉ B)
    (hlarge :
      (k - 4) * (k - 1) * Nat.choose n ((k - 4) - 1) <
        (pointStar (branchAvoiding 𝓕 x B H) z).card) :
    ∃ 𝓢 : Finset (Finset (Fin n)),
      𝓢 ⊆ branchAvoiding 𝓕 x B H ∧ 𝓢.card = k ∧
        IsDeltaSystem (insert z B) 𝓢 := by
  have hpaircard : (insert z B).card = 3 := by
    rw [card_insert_of_notMem hzB, hBcard]
  have heq :
      supersetsInFamily (branchAvoiding 𝓕 x B H) (insert z B) =
        pointStar (branchAvoiding 𝓕 x B H) z := by
    ext A
    constructor
    · intro hA
      have hAmem : A ∈ branchAvoiding 𝓕 x B H := (mem_filter.mp hA).1
      have hzA : z ∈ A := (mem_filter.mp hA).2 (mem_insert_self _ _)
      exact mem_filter.mpr ⟨hAmem, hzA⟩
    · intro hA
      have hAgood : A ∈ branchAvoiding 𝓕 x B H := (mem_filter.mp hA).1
      have hzA : z ∈ A := (mem_filter.mp hA).2
      have hAbranch : A ∈ linkBranch 𝓕 x B := (mem_filter.mp hAgood).1
      have hBA : B ⊆ A := (mem_filter.mp hAbranch).2
      exact mem_filter.mpr ⟨hAgood, insert_subset hzA hBA⟩
  have hlarge' :
      (k - 1 - 3) * (k - 1) * Nat.choose n (k - 1 - 3 - 1) <
        (supersetsInFamily (branchAvoiding 𝓕 x B H) (insert z B)).card := by
    rw [heq]
    have h1 : k - 1 - 3 = k - 4 := by omega
    rw [h1]
    exact hlarge
  obtain ⟨𝓢, h𝓢sub, h𝓢card, hdelta⟩ :=
    exists_deltaSystem_of_large_supersets
      (𝓖 := branchAvoiding 𝓕 x B H) (B := insert z B)
      (r := k - 1) (t := 3) (q := k)
      (fun A hA =>
        link_uniform huniform x A
          ((mem_filter.mp (mem_filter.mp hA).1).1))
      hpaircard (by omega) hlarge'
  exact ⟨𝓢, h𝓢sub.trans (filter_subset _ _), h𝓢card, hdelta⟩

lemma kernelReachable_swap_link {n q : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x y : Fin n}
    (hxy : x ≠ y) (hq : 2 ≤ q)
    {K : Finset (Fin n)}
    (hK : KernelReachable q (link 𝓕 x) K) (hyK : y ∈ K) :
    KernelReachable q (link 𝓕 y) (insert x (K.erase y)) := by
  classical
  induction hK with
  | @member E hmem hne =>
      have hdata := mem_link_iff.mp hmem
      apply KernelReachable.member
      · rw [mem_link_iff]
        refine ⟨by simp [hxy.symm], ?_⟩
        have hEq : insert y (insert x (E.erase y)) = insert x E := by
          ext z
          by_cases hzy : z = y
          · subst z
            simp [hxy.symm, hyK]
          · by_cases hzx : z = x
            · subst z
              simp [hxy]
            · simp [hzy, hzx]
        rw [hEq]
        exact hdata.2
      · simp
  | @delta K 𝓢 hKne hreach h𝓢card hdelta ih =>
      have h𝓢two : 2 ≤ 𝓢.card := by rw [h𝓢card]; exact hq
      let swap : Finset (Fin n) → Finset (Fin n) :=
        fun A => insert x (A.erase y)
      let 𝓣 : Finset (Finset (Fin n)) := 𝓢.image swap
      have hy_mem : ∀ A ∈ 𝓢, y ∈ A := by
        intro A hA
        exact (kernel_subset_of_mem_deltaSystem hdelta h𝓢two hA) hyK
      have hx_not_mem : ∀ A ∈ 𝓢, x ∉ A := by
        intro A hA
        exact kernelReachable_not_mem_of_link hq (hreach A hA)
      have hswap_inj : Set.InjOn swap 𝓢 := by
        intro A hA C hC hEq
        have hxA := hx_not_mem A hA
        have hxC := hx_not_mem C hC
        have hyA := hy_mem A hA
        have hyC := hy_mem C hC
        have herase :
            A.erase y = C.erase y := by
          have := congrArg (erase · x) hEq
          simpa [swap, hxy, hxA, hxC] using this
        calc
          A = insert y (A.erase y) := (insert_erase hyA).symm
          _ = insert y (C.erase y) := congrArg (insert y) herase
          _ = C := insert_erase hyC
      have h𝓣card : 𝓣.card = q := by
        change (𝓢.image swap).card = q
        rw [card_image_of_injOn hswap_inj, h𝓢card]
      apply KernelReachable.delta (K := insert x (K.erase y)) (𝓢 := 𝓣) (by simp)
      · intro A hA
        change A ∈ 𝓢.image swap at hA
        rw [mem_image] at hA
        obtain ⟨C, hC, rfl⟩ := hA
        exact ih C hC (hy_mem C hC)
      · exact h𝓣card
      · intro A hA C hC hAC
        change A ∈ 𝓢.image swap at hA
        change C ∈ 𝓢.image swap at hC
        rw [mem_image] at hA hC
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨C', hC', rfl⟩ := hC
        have hne : A' ≠ C' := by
          intro h
          exact hAC (by simp [swap, h])
        change insert x (A'.erase y) ∩ insert x (C'.erase y) =
          insert x (K.erase y)
        rw [← insert_inter_distrib]
        have hErase :
            A'.erase y ∩ C'.erase y = (A' ∩ C').erase y := by
          ext z
          simp [and_left_comm, and_comm]
        rw [hErase, hdelta A' hA' C' hC' hne]

lemma twoBase_subset_of_transferred_kernel {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x z : Fin n} {B D K : Finset (Fin n)}
    (hBcl : B ∈ kernelClosure k (link 𝓕 x))
    (hKglobal : K = insert x B)
    (hKz : K ∈ kernelClosure k (link 𝓕 z))
    (hzK : z ∉ K)
    (hD : D ∈ closedTwoBases k 𝓕 z) :
    D ⊆ K := by
  have hDbase : D ∈ closedDeltaBase k (link 𝓕 z) := (mem_filter.mp hD).1
  have hDcard : D.card = 2 := (mem_filter.mp hD).2
  have hnotdisj : ¬ Disjoint D K :=
    kernelClosure_link_intersecting huniform hk havoid z
      (mem_closedDeltaBase_iff.mp hDbase).1 hKz
  have hpos : 0 < (D ∩ K).card :=
    card_pos.mpr (not_disjoint_iff_nonempty_inter.mp hnotdisj)
  have hDreach : KernelReachable k 𝓕 (insert z D) :=
    kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hKreach : KernelReachable k 𝓕 K := by
    rw [hKglobal]
    exact kernelReachable_insert_of_link hk (mem_kernelClosure_iff.mp hBcl)
  have hcompat := kernelReachable_compatible
    (q := k) (r := k) (𝓖 := 𝓕)
    havoid (fun A hA => by rw [huniform A hA]) hk (le_refl k)
    hDreach hKreach
  have hne1 : (D ∩ K).card ≠ 1 := by
    intro hDK
    apply hcompat
    have hinter : insert z D ∩ K = D ∩ K := by
      ext a
      simp [hzK]
    rw [hinter, hDK]
  have hle : (D ∩ K).card ≤ 2 := by
    calc
      (D ∩ K).card ≤ D.card := card_le_card inter_subset_left
      _ = 2 := hDcard
  have hcard : (D ∩ K).card = 2 := by omega
  have heq : D ∩ K = D :=
    eq_of_subset_of_card_le inter_subset_left (by rw [hDcard, hcard])
  intro a ha
  have : a ∈ D ∩ K := by rw [heq]; exact ha
  exact (mem_inter.mp this).2

lemma transferred_twoBase_contains_x {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x z : Fin n} {B D G : Finset (Fin n)}
    (hBcl : B ∈ kernelClosure k (link 𝓕 x))
    (hBcard : B.card = 2)
    (hD : D ∈ closedTwoBases k 𝓕 z)
    (hDsub : D ⊆ insert x B)
    (hG : G ∈ link 𝓕 x) (hBG : (B ∩ G).card = 1)
    (hzG : z ∉ insert x G) :
    x ∈ D := by
  have hDbase : D ∈ closedDeltaBase k (link 𝓕 z) := (mem_filter.mp hD).1
  have hDcard : D.card = 2 := (mem_filter.mp hD).2
  have hDB : D ≠ B := by
    intro hDB
    subst D
    have hBreach : KernelReachable k 𝓕 (insert z B) :=
      kernelReachable_insert_of_link hk
        (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
    have hGdata := mem_link_iff.mp hG
    have hGne : (insert x G).Nonempty := by simp
    have hcompat := kernelReachable_compatible
      (q := k) (r := k) (𝓖 := 𝓕)
      havoid (fun A hA => by rw [huniform A hA]) hk (le_refl k)
      hBreach (KernelReachable.member hGdata.2 hGne)
    apply hcompat
    have hxB : x ∉ B :=
      kernelReachable_not_mem_of_link hk (mem_kernelClosure_iff.mp hBcl)
    have hinter : insert z B ∩ insert x G = B ∩ G := by
      ext a
      simp [hzG, hxB]
    rw [hinter, hBG]
  by_contra hxD
  have hDBsub : D ⊆ B := by
    intro a ha
    have ha' := hDsub ha
    simp only [mem_insert] at ha'
    rcases ha' with rfl | haB
    · exact (hxD ha).elim
    · exact haB
  have hEq : D = B :=
    eq_of_subset_of_card_le hDBsub (by rw [hBcard, hDcard])
  exact hDB hEq

lemma exists_twoBase_containing_swapped_point {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (hk : 2 ≤ k)
    {x z : Fin n} (hxz : x ≠ z)
    {D : Finset (Fin n)}
    (hD : D ∈ closedTwoBases k 𝓕 z) (hxD : x ∈ D)
    (hnosingle : ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x) :
    ∃ E ∈ closedTwoBases k 𝓕 x, z ∈ E := by
  have hDbase : D ∈ closedDeltaBase k (link 𝓕 z) := (mem_filter.mp hD).1
  have hDcard : D.card = 2 := (mem_filter.mp hD).2
  have hDreach : KernelReachable k (link 𝓕 z) D :=
    mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1
  have hswap :
      KernelReachable k (link 𝓕 x) (insert z (D.erase x)) :=
    kernelReachable_swap_link hxz.symm hk hDreach hxD
  have hswapcl : insert z (D.erase x) ∈ kernelClosure k (link 𝓕 x) :=
    mem_kernelClosure_iff.mpr hswap
  obtain ⟨E, hEbase, hEsub⟩ :=
    exists_closedDeltaBase_subset_of_closure hswapcl
  have hEne : E.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hEbase).1)
  have hEcard_ne_one : E.card ≠ 1 := by
    intro hEone
    obtain ⟨y, rfl⟩ := card_eq_one.mp hEone
    exact hnosingle ⟨y, hEbase⟩
  have hzD : z ∉ D :=
    kernelReachable_not_mem_of_link hk hDreach
  have hDeraseCard : (D.erase x).card = 1 := by
    have hcard := card_erase_add_one hxD
    rw [hDcard] at hcard
    omega
  have htargetCard : (insert z (D.erase x)).card = 2 := by
    rw [card_insert_of_notMem]
    · rw [hDeraseCard]
    · exact fun hz => hzD (mem_erase.mp hz).2
  have hEcard_le : E.card ≤ 2 := by
    calc
      E.card ≤ (insert z (D.erase x)).card := card_le_card hEsub
      _ = 2 := htargetCard
  have hEcard : E.card = 2 := by
    have : 0 < E.card := card_pos.mpr hEne
    omega
  have hEq : E = insert z (D.erase x) :=
    eq_of_subset_of_card_le hEsub (by rw [htargetCard, hEcard])
  refine ⟨E, ?_, ?_⟩
  · exact mem_filter.mpr ⟨hEbase, hEcard⟩
  · rw [hEq]
    simp

lemma exists_threshold_unique_twoBase_link_structure
    (k : ℕ) (hk5 : 5 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x) →
        ∀ x : Fin n, ∃ B ∈ closedTwoBases k 𝓕 x,
          ∀ G ∈ link 𝓕 x, B ⊆ G := by
  let Q := (k - 4) * (k - 1) + 1
  let M := (5 * (k - 1) + 1) + Q
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_threshold_small_base_of_large_degree k (by omega)
  obtain ⟨Ndom, hNdom⟩ :=
    exists_threshold_dominant_two_base k M (by omega)
  refine ⟨max Nsmall Ndom, ?_⟩
  intro n hn 𝓕 huniform havoid hdegAll hnosingleAll x
  have hnsmall : Nsmall ≤ n := (le_max_left _ _).trans hn
  have hndom : Ndom ≤ n := (le_max_right _ _).trans hn
  obtain ⟨B, hBtwo, hBlarge⟩ :=
    hNdom n hndom 𝓕 x huniform havoid (hdegAll x) (hnosingleAll x)
  refine ⟨B, hBtwo, ?_⟩
  intro G hG
  by_contra hnotBG
  have hk : 2 ≤ k := by omega
  have hBcard : B.card = 2 := (mem_filter.mp hBtwo).2
  have hGB := inter_card_eq_one_of_not_subset_two_closedBase
    (x := x) (B := B) (A := G)
    huniform hk havoid hBtwo hG hnotBG
  have hBG : (B ∩ G).card = 1 := by
    simpa [inter_comm] using hGB
  let U := closedTwoBases k 𝓕 x
  let H : Finset (Fin n) := insert x (G ∪ U.biUnion id)
  have hUcard : U.card ≤ 2 * (k - 1) := by
    dsimp [U]
    exact two_closed_link_bases_card_le huniform (by omega) havoid x
  have hUeach : ∀ D ∈ U, (id D).card ≤ 2 := by
    intro D hD
    have : D.card = 2 := (mem_filter.mp hD).2
    simpa using this.le
  have hUunion : (U.biUnion id).card ≤ U.card * 2 :=
    card_biUnion_le_card_mul U id 2 hUeach
  have hUunion' : (U.biUnion id).card ≤ (2 * (k - 1)) * 2 :=
    hUunion.trans (Nat.mul_le_mul_right _ hUcard)
  have hGcard : G.card = k - 1 := link_uniform huniform x G hG
  have hHcard : H.card ≤ 5 * (k - 1) + 1 := by
    calc
      H.card ≤ (G ∪ U.biUnion id).card + 1 := card_insert_le _ _
      _ ≤ (G.card + (U.biUnion id).card) + 1 := by
        gcongr
        exact card_union_le _ _
      _ ≤ ((k - 1) + (2 * (k - 1)) * 2) + 1 := by
        rw [hGcard]
        gcongr
      _ = 5 * (k - 1) + 1 := by ring
  have hBU : B ∈ U := hBtwo
  have hBsubH : B ⊆ H := by
    intro b hb
    apply mem_insert_of_mem
    apply mem_union_right
    exact mem_biUnion.mpr ⟨B, hBU, hb⟩
  have hbranchHuge :
      (H.card + Q) * n ^ (k - 4) < (linkBranch 𝓕 x B).card := by
    have hcoef : H.card + Q ≤ M := by
      dsimp [M]
      omega
    exact (Nat.mul_le_mul_right _ hcoef).trans_lt hBlarge
  have hgood :=
    card_branchAvoiding_gt_of_branch_gt huniform hBcard hbranchHuge
  obtain ⟨z, hzoutside, hzstar⟩ :=
    exists_outside_pointStar_of_good_branch_gt huniform hk5 hBcard hgood
  have hzH : z ∉ H := (mem_sdiff.mp hzoutside).2
  have hzB : z ∉ B := fun hz => hzH (hBsubH hz)
  have hxH : x ∈ H := mem_insert_self _ _
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hzH hxH
  have hmatchStar :
      (k - 4) * (k - 1) * Nat.choose n ((k - 4) - 1) <
        (pointStar (branchAvoiding 𝓕 x B H) z).card := by
    have hchoose : Nat.choose n ((k - 4) - 1) ≤ n ^ (k - 5) := by
      have hexp : (k - 4) - 1 = k - 5 := by omega
      rw [hexp]
      exact Nat.choose_le_pow _ _
    have hcoeff :
        (k - 4) * (k - 1) * Nat.choose n ((k - 4) - 1) ≤
          (k - 4) * (k - 1) * n ^ (k - 5) :=
      Nat.mul_le_mul_left _ hchoose
    have hQ :
        (k - 4) * (k - 1) * n ^ (k - 5) <
          Q * n ^ (k - 5) := by
      dsimp [Q]
      have hpowpos : 0 < n ^ (k - 5) := by
        have hnpos : 0 < n := Nat.pos_of_ne_zero (by
          intro hn0
          subst n
          exact Fin.elim0 x)
        positivity
      nlinarith
    exact hcoeff.trans_lt (hQ.trans hzstar)
  obtain ⟨𝓢, h𝓢sub, h𝓢card, h𝓢delta⟩ :=
    exists_deltaSystem_insert_of_large_good_pointStar
      huniform hk5 hBcard hzB hmatchStar
  have hKx :
      KernelReachable k (link 𝓕 x) (insert z B) := by
    apply KernelReachable.delta (by simp)
    · intro A hA
      exact KernelReachable.member
        ((mem_filter.mp (mem_filter.mp (h𝓢sub hA)).1).1)
        (by
          have hAcard := link_uniform huniform x A
            ((mem_filter.mp (mem_filter.mp (h𝓢sub hA)).1).1)
          exact card_pos.mp (by omega))
    · exact h𝓢card
    · exact h𝓢delta
  have hKzReach :
      KernelReachable k (link 𝓕 z) (insert x B) := by
    have hswap :=
      kernelReachable_swap_link hxz hk hKx (by simp)
    simpa [hzB] using hswap
  have hKz : insert x B ∈ kernelClosure k (link 𝓕 z) :=
    mem_kernelClosure_iff.mpr hKzReach
  obtain ⟨D, hDbase, hDle⟩ :=
    hNsmall n hnsmall 𝓕 z huniform havoid (hdegAll z)
  have hDne : D.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hDcard_ne_one : D.card ≠ 1 := by
    intro hDone
    obtain ⟨d, rfl⟩ := card_eq_one.mp hDone
    exact hnosingleAll z ⟨d, hDbase⟩
  have hDcard : D.card = 2 := by
    have : 0 < D.card := card_pos.mpr hDne
    omega
  have hDtwo : D ∈ closedTwoBases k 𝓕 z :=
    mem_filter.mpr ⟨hDbase, hDcard⟩
  have hDsub : D ⊆ insert x B :=
    twoBase_subset_of_transferred_kernel huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      rfl hKz (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU, (mem_insert.mp hz).resolve_left hxz.symm⟩))
      hDtwo
  have hzG : z ∉ insert x G := by
    intro hz
    apply hzH
    rw [mem_insert] at hz
    rcases hz with rfl | hzG
    · exact hxH
    · exact mem_insert_of_mem (mem_union_left _ hzG)
  have hxD :=
    transferred_twoBase_contains_x huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      hBcard hDtwo hDsub hG hBG hzG
  obtain ⟨E, hEtwo, hzE⟩ :=
    exists_twoBase_containing_swapped_point hk hxz hDtwo hxD (hnosingleAll x)
  apply hzH
  apply mem_insert_of_mem
  apply mem_union_right
  exact mem_biUnion.mpr ⟨E, hEtwo, hzE⟩

/-- A one-point closed link base cannot coexist with a second closed link
kernel which is already reachable globally and avoids the link point.  This
is the local replacement for the stronger global no-singleton-base hypothesis
in Frankl's transferred-kernel argument. -/
lemma closedBase_card_ne_one_of_transferred_kernel {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 2 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {z : Fin n} {D K : Finset (Fin n)}
    (hDbase : D ∈ closedDeltaBase k (link 𝓕 z))
    (hKz : K ∈ kernelClosure k (link 𝓕 z))
    (hKreach : KernelReachable k 𝓕 K) (hzK : z ∉ K) :
    D.card ≠ 1 := by
  intro hDone
  have hDcl : D ∈ kernelClosure k (link 𝓕 z) :=
    (mem_closedDeltaBase_iff.mp hDbase).1
  have hnotdisj : ¬ Disjoint D K :=
    kernelClosure_link_intersecting huniform hk havoid z hDcl hKz
  have hpos : 0 < (D ∩ K).card :=
    card_pos.mpr (not_disjoint_iff_nonempty_inter.mp hnotdisj)
  have hle : (D ∩ K).card ≤ 1 := by
    calc
      (D ∩ K).card ≤ D.card := card_le_card inter_subset_left
      _ = 1 := hDone
  have hinterCard : (D ∩ K).card = 1 := by omega
  have hDreach : KernelReachable k 𝓕 (insert z D) :=
    kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp hDcl)
  have hcompat := kernelReachable_compatible
    (q := k) (r := k) (𝓖 := 𝓕)
    havoid (fun A hA => by rw [huniform A hA]) hk (le_refl k)
    hDreach hKreach
  apply hcompat
  have hinter : insert z D ∩ K = D ∩ K := by
    ext a
    simp [hzK]
  rw [hinter, hinterCard]

/-- The dominant two-base argument is pointwise: singleton bases at other
points are excluded automatically by the transferred kernel constructed in
the proof. -/
lemma exists_threshold_unique_twoBase_link_structure_local
    (k : ℕ) (hk5 : 5 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        ∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x →
          ∃ B ∈ closedTwoBases k 𝓕 x,
            ∀ G ∈ link 𝓕 x, B ⊆ G := by
  let Q := (k - 4) * (k - 1) + 1
  let M := (5 * (k - 1) + 1) + Q
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_threshold_small_base_of_large_degree k (by omega)
  obtain ⟨Ndom, hNdom⟩ :=
    exists_threshold_dominant_two_base k M (by omega)
  refine ⟨max Nsmall Ndom, ?_⟩
  intro n hn 𝓕 huniform havoid hdegAll x hnosingleX
  have hnsmall : Nsmall ≤ n := (le_max_left _ _).trans hn
  have hndom : Ndom ≤ n := (le_max_right _ _).trans hn
  obtain ⟨B, hBtwo, hBlarge⟩ :=
    hNdom n hndom 𝓕 x huniform havoid (hdegAll x) hnosingleX
  refine ⟨B, hBtwo, ?_⟩
  intro G hG
  by_contra hnotBG
  have hk : 2 ≤ k := by omega
  have hBcard : B.card = 2 := (mem_filter.mp hBtwo).2
  have hGB := inter_card_eq_one_of_not_subset_two_closedBase
    (x := x) (B := B) (A := G)
    huniform hk havoid hBtwo hG hnotBG
  have hBG : (B ∩ G).card = 1 := by
    simpa [inter_comm] using hGB
  let U := closedTwoBases k 𝓕 x
  let H : Finset (Fin n) := insert x (G ∪ U.biUnion id)
  have hUcard : U.card ≤ 2 * (k - 1) := by
    dsimp [U]
    exact two_closed_link_bases_card_le huniform (by omega) havoid x
  have hUeach : ∀ D ∈ U, (id D).card ≤ 2 := by
    intro D hD
    have : D.card = 2 := (mem_filter.mp hD).2
    simpa using this.le
  have hUunion : (U.biUnion id).card ≤ U.card * 2 :=
    card_biUnion_le_card_mul U id 2 hUeach
  have hUunion' : (U.biUnion id).card ≤ (2 * (k - 1)) * 2 :=
    hUunion.trans (Nat.mul_le_mul_right _ hUcard)
  have hGcard : G.card = k - 1 := link_uniform huniform x G hG
  have hHcard : H.card ≤ 5 * (k - 1) + 1 := by
    calc
      H.card ≤ (G ∪ U.biUnion id).card + 1 := card_insert_le _ _
      _ ≤ (G.card + (U.biUnion id).card) + 1 := by
        gcongr
        exact card_union_le _ _
      _ ≤ ((k - 1) + (2 * (k - 1)) * 2) + 1 := by
        rw [hGcard]
        gcongr
      _ = 5 * (k - 1) + 1 := by ring
  have hBU : B ∈ U := hBtwo
  have hBsubH : B ⊆ H := by
    intro b hb
    apply mem_insert_of_mem
    apply mem_union_right
    exact mem_biUnion.mpr ⟨B, hBU, hb⟩
  have hbranchHuge :
      (H.card + Q) * n ^ (k - 4) < (linkBranch 𝓕 x B).card := by
    have hcoef : H.card + Q ≤ M := by
      dsimp [M]
      omega
    exact (Nat.mul_le_mul_right _ hcoef).trans_lt hBlarge
  have hgood :=
    card_branchAvoiding_gt_of_branch_gt huniform hBcard hbranchHuge
  obtain ⟨z, hzoutside, hzstar⟩ :=
    exists_outside_pointStar_of_good_branch_gt huniform hk5 hBcard hgood
  have hzH : z ∉ H := (mem_sdiff.mp hzoutside).2
  have hzB : z ∉ B := fun hz => hzH (hBsubH hz)
  have hxH : x ∈ H := mem_insert_self _ _
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hzH hxH
  have hmatchStar :
      (k - 4) * (k - 1) * Nat.choose n ((k - 4) - 1) <
        (pointStar (branchAvoiding 𝓕 x B H) z).card := by
    have hchoose : Nat.choose n ((k - 4) - 1) ≤ n ^ (k - 5) := by
      have hexp : (k - 4) - 1 = k - 5 := by omega
      rw [hexp]
      exact Nat.choose_le_pow _ _
    have hcoeff :
        (k - 4) * (k - 1) * Nat.choose n ((k - 4) - 1) ≤
          (k - 4) * (k - 1) * n ^ (k - 5) :=
      Nat.mul_le_mul_left _ hchoose
    have hQ :
        (k - 4) * (k - 1) * n ^ (k - 5) <
          Q * n ^ (k - 5) := by
      dsimp [Q]
      have hpowpos : 0 < n ^ (k - 5) := by
        have hnpos : 0 < n := Nat.pos_of_ne_zero (by
          intro hn0
          subst n
          exact Fin.elim0 x)
        positivity
      nlinarith
    exact hcoeff.trans_lt (hQ.trans hzstar)
  obtain ⟨𝓢, h𝓢sub, h𝓢card, h𝓢delta⟩ :=
    exists_deltaSystem_insert_of_large_good_pointStar
      huniform hk5 hBcard hzB hmatchStar
  have hKx :
      KernelReachable k (link 𝓕 x) (insert z B) := by
    apply KernelReachable.delta (by simp)
    · intro A hA
      exact KernelReachable.member
        ((mem_filter.mp (mem_filter.mp (h𝓢sub hA)).1).1)
        (by
          have hAcard := link_uniform huniform x A
            ((mem_filter.mp (mem_filter.mp (h𝓢sub hA)).1).1)
          exact card_pos.mp (by omega))
    · exact h𝓢card
    · exact h𝓢delta
  have hKzReach :
      KernelReachable k (link 𝓕 z) (insert x B) := by
    have hswap :=
      kernelReachable_swap_link hxz hk hKx (by simp)
    simpa [hzB] using hswap
  have hKz : insert x B ∈ kernelClosure k (link 𝓕 z) :=
    mem_kernelClosure_iff.mpr hKzReach
  have hKglobal : KernelReachable k 𝓕 (insert x B) :=
    kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp
        (mem_filter.mp hBtwo).1).1)
  obtain ⟨D, hDbase, hDle⟩ :=
    hNsmall n hnsmall 𝓕 z huniform havoid (hdegAll z)
  have hDne : D.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hDcard_ne_one : D.card ≠ 1 :=
    closedBase_card_ne_one_of_transferred_kernel huniform hk havoid
      hDbase hKz hKglobal (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU,
            (mem_insert.mp hz).resolve_left hxz.symm⟩))
  have hDcard : D.card = 2 := by
    have : 0 < D.card := card_pos.mpr hDne
    omega
  have hDtwo : D ∈ closedTwoBases k 𝓕 z :=
    mem_filter.mpr ⟨hDbase, hDcard⟩
  have hDsub : D ⊆ insert x B :=
    twoBase_subset_of_transferred_kernel huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      rfl hKz (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU, (mem_insert.mp hz).resolve_left hxz.symm⟩))
      hDtwo
  have hzG : z ∉ insert x G := by
    intro hz
    apply hzH
    rw [mem_insert] at hz
    rcases hz with rfl | hzG
    · exact hxH
    · exact mem_insert_of_mem (mem_union_left _ hzG)
  have hxD :=
    transferred_twoBase_contains_x huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      hBcard hDtwo hDsub hG hBG hzG
  obtain ⟨E, hEtwo, hzE⟩ :=
    exists_twoBase_containing_swapped_point hk hxz hDtwo hxD hnosingleX
  apply hzH
  apply mem_insert_of_mem
  apply mem_union_right
  exact mem_biUnion.mpr ⟨E, hEtwo, hzE⟩

/-! ## The all-two-base regime is already below the two-star bound -/

def tripleStar {n : ℕ} (k : ℕ) (T : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.powersetCard k).filter (T ⊆ ·)

lemma card_tripleStar {n k : ℕ} {T : Finset (Fin n)}
    (hTcard : T.card = 3) (hk : 3 ≤ k) :
    (tripleStar k T).card = Nat.choose (n - 3) (k - 3) := by
  unfold tripleStar
  rw [card_filter_powersetCard_subset]
  · rw [card_univ, Fintype.card_fin, hTcard]
  · simp
  · rw [hTcard]
    exact hk

lemma degree_le_choose_of_link_pair_core {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk : 3 ≤ k) {x : Fin n} {B : Finset (Fin n)}
    (hB : B ∈ closedTwoBases k 𝓕 x)
    (hcore : ∀ G ∈ link 𝓕 x, B ⊆ G) :
    (𝓕.filter fun A => x ∈ A).card ≤ Nat.choose (n - 3) (k - 3) := by
  have hBbase : B ∈ closedDeltaBase k (link 𝓕 x) := (mem_filter.mp hB).1
  have hBcard : B.card = 2 := (mem_filter.mp hB).2
  have hxB : x ∉ B :=
    kernelReachable_not_mem_of_link (by omega)
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hBbase).1)
  have hTcard : (insert x B).card = 3 := by
    rw [card_insert_of_notMem hxB, hBcard]
  have hsub :
      𝓕.filter (fun A => x ∈ A) ⊆ tripleStar k (insert x B) := by
    intro A hA
    have hAF : A ∈ 𝓕 := (mem_filter.mp hA).1
    have hxA : x ∈ A := (mem_filter.mp hA).2
    have hlink : A.erase x ∈ link 𝓕 x := by
      rw [mem_link_iff]
      exact ⟨by simp, by simpa [insert_erase hxA] using hAF⟩
    have hBAerase := hcore (A.erase x) hlink
    have hTsub : insert x B ⊆ A := by
      apply insert_subset hxA
      intro b hb
      exact (mem_erase.mp (hBAerase hb)).2
    exact mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨by simp, huniform A hAF⟩, hTsub⟩
  calc
    (𝓕.filter fun A => x ∈ A).card ≤ (tripleStar k (insert x B)).card :=
      card_le_card hsub
    _ = Nat.choose (n - 3) (k - 3) := card_tripleStar hTcard hk

lemma sum_point_degrees_eq_card_mul {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕) :
    (∑ x : Fin n, (𝓕.filter fun A => x ∈ A).card) = 𝓕.card * k := by
  calc
    ∑ x : Fin n, (𝓕.filter fun A => x ∈ A).card =
        ∑ x : Fin n, ∑ A ∈ 𝓕, if x ∈ A then 1 else 0 := by
      apply sum_congr rfl
      intro x hx
      simp
    _ = ∑ A ∈ 𝓕, ∑ x : Fin n, if x ∈ A then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ A ∈ 𝓕, A.card := by
      apply sum_congr rfl
      intro A hA
      simp
    _ = ∑ _A ∈ 𝓕, k := by
      apply sum_congr rfl
      intro A hA
      rw [huniform A hA]
    _ = 𝓕.card * k := by simp

lemma choose_degree_gap {n k : ℕ} (hk : 3 ≤ k) (hnk : k < n) :
    n * Nat.choose (n - 3) (k - 3) <
      k * Nat.choose (n - 2) (k - 2) := by
  have hn3 : 3 ≤ n := by omega
  have hident :
      (n - 2) * Nat.choose (n - 3) (k - 3) =
        Nat.choose (n - 2) (k - 2) * (k - 2) := by
    have h := Nat.add_one_mul_choose_eq (n - 3) (k - 3)
    have hn : n - 3 + 1 = n - 2 := by omega
    have hk' : k - 3 + 1 = k - 2 := by omega
    simpa [hn, hk'] using h
  have hDpos : 0 < Nat.choose (n - 3) (k - 3) :=
    Nat.choose_pos (by omega)
  have hrealIdent :
      ((n - 2 : ℕ) : ℝ) * Nat.choose (n - 3) (k - 3) =
        Nat.choose (n - 2) (k - 2) * ((k - 2 : ℕ) : ℝ) := by
    exact_mod_cast hident
  norm_num [Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 2 ≤ k)] at hrealIdent
  have hnR : (k : ℝ) < n := by exact_mod_cast hnk
  have hkR : (2 : ℝ) < k := by exact_mod_cast hk
  have hDposR : (0 : ℝ) < Nat.choose (n - 3) (k - 3) := by
    exact_mod_cast hDpos
  have hgapR :
      (n : ℝ) * Nat.choose (n - 3) (k - 3) <
        k * Nat.choose (n - 2) (k - 2) := by
    nlinarith
  exact_mod_cast hgapR

lemma card_lt_twoStarBound_of_all_links_have_pair_core {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk3 : 3 ≤ k) (hnk : k < n)
    (hcore : ∀ x : Fin n, ∃ B ∈ closedTwoBases k 𝓕 x,
      ∀ G ∈ link 𝓕 x, B ⊆ G) :
    𝓕.card < Nat.choose (n - 2) (k - 2) := by
  have hdeg :
      ∀ x : Fin n,
        (𝓕.filter fun A => x ∈ A).card ≤ Nat.choose (n - 3) (k - 3) := by
    intro x
    obtain ⟨B, hB, hBcore⟩ := hcore x
    exact degree_le_choose_of_link_pair_core huniform (by omega) hB hBcore
  have hsumle :
      ∑ x : Fin n, (𝓕.filter fun A => x ∈ A).card ≤
        ∑ _x : Fin n, Nat.choose (n - 3) (k - 3) :=
    sum_le_sum fun x _ => hdeg x
  rw [sum_point_degrees_eq_card_mul huniform] at hsumle
  simp at hsumle
  have hgap := choose_degree_gap (n := n) (k := k) (by omega) hnk
  have hmul : 𝓕.card * k < Nat.choose (n - 2) (k - 2) * k := by
    have : 𝓕.card * k ≤ n * Nat.choose (n - 3) (k - 3) := by
      simpa [Nat.mul_comm] using hsumle
    have hgap' :
        n * Nat.choose (n - 3) (k - 3) <
          Nat.choose (n - 2) (k - 2) * k := by
      simpa [Nat.mul_comm] using hgap
    exact this.trans_lt hgap'
  exact (Nat.mul_lt_mul_right (by omega : 0 < k)).mp hmul

lemma exists_threshold_card_lt_of_high_degrees_without_singleton_bases
    (k : ℕ) (hk5 : 5 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x) →
        𝓕.card < Nat.choose (n - 2) (k - 2) := by
  obtain ⟨N, hN⟩ := exists_threshold_unique_twoBase_link_structure k hk5
  refine ⟨max N (k + 1), ?_⟩
  intro n hn 𝓕 huniform havoid hdeg hnosingle
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnk : k < n := by
    have : k + 1 ≤ n := (le_max_right _ _).trans hn
    omega
  apply card_lt_twoStarBound_of_all_links_have_pair_core huniform (by omega) hnk
  exact hN n hnN 𝓕 huniform havoid hdeg hnosingle

lemma exists_threshold_singleton_base_of_large_high_degree_family
    (k : ℕ) (hk5 : 5 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        Nat.choose (n - 2) (k - 2) ≤ 𝓕.card →
        ∃ x : Fin n, HasSingletonClosedLinkBase (k := k) 𝓕 x := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_card_lt_of_high_degrees_without_singleton_bases k hk5
  refine ⟨N, ?_⟩
  intro n hn 𝓕 huniform havoid hdeg hlarge
  by_contra hnone
  push Not at hnone
  have hsmall := hN n hn 𝓕 huniform havoid hdeg hnone
  omega

lemma exists_insert_eq_of_card_three_of_card_two_subset {α : Type*}
    [DecidableEq α] {B C : Finset α}
    (hBcard : B.card = 2) (hCcard : C.card = 3) (hBC : B ⊆ C) :
    ∃ z ∈ C \ B, C = insert z B := by
  have hdiffcard : (C \ B).card = 1 := by
    rw [card_sdiff_of_subset hBC, hCcard, hBcard]
  obtain ⟨z, hz⟩ := card_pos.mp (by rw [hdiffcard]; omega)
  refine ⟨z, hz, ?_⟩
  have hEq : (C \ B) ∪ B = C := sdiff_union_of_subset hBC
  have hsingleton : C \ B = {z} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hz, ?_⟩
    intro w hw
    have hcardle : ({z, w} : Finset α).card ≤ (C \ B).card := by
      apply card_le_card
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hz
      · exact hw
    rw [hdiffcard] at hcardle
    by_contra hzw
    have hne : z ≠ w := by
      intro h
      exact hzw h.symm
    have hpair : ({z, w} : Finset α).card = 2 := by simp [hne]
    rw [hpair] at hcardle
    omega
  rw [← hEq, hsingleton]
  simp [union_comm]

lemma exists_threshold_unique_twoBase_link_structure_four :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform 4 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) 1 ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := 4) 𝓕 x) →
        ∀ x : Fin n, ∃ B ∈ closedTwoBases 4 𝓕 x,
          ∀ G ∈ link 𝓕 x, B ⊆ G := by
  let M := 17
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_threshold_small_base_of_large_degree 4 (by decide)
  obtain ⟨Ndom, hNdom⟩ :=
    exists_threshold_dominant_two_base 4 M (by decide)
  refine ⟨max Nsmall Ndom, ?_⟩
  intro n hn 𝓕 huniform havoid hdegAll hnosingleAll x
  have hnsmall : Nsmall ≤ n := (le_max_left _ _).trans hn
  have hndom : Ndom ≤ n := (le_max_right _ _).trans hn
  obtain ⟨B, hBtwo, hBlarge⟩ :=
    hNdom n hndom 𝓕 x huniform havoid (by simpa using hdegAll x) (hnosingleAll x)
  refine ⟨B, hBtwo, ?_⟩
  intro G hG
  by_contra hnotBG
  have hk : 2 ≤ 4 := by decide
  have hBcard : B.card = 2 := (mem_filter.mp hBtwo).2
  have hGB := inter_card_eq_one_of_not_subset_two_closedBase
    (x := x) (B := B) (A := G)
    huniform hk havoid hBtwo hG hnotBG
  have hBG : (B ∩ G).card = 1 := by simpa [inter_comm] using hGB
  let U := closedTwoBases 4 𝓕 x
  let H : Finset (Fin n) := insert x (G ∪ U.biUnion id)
  have hUcard : U.card ≤ 6 := by
    simpa [U, closedTwoBases] using
      two_closed_link_bases_card_le huniform (by decide) havoid x
  have hUeach : ∀ D ∈ U, (id D).card ≤ 2 := by
    intro D hD
    exact (mem_filter.mp hD).2.le
  have hUunion : (U.biUnion id).card ≤ U.card * 2 :=
    card_biUnion_le_card_mul U id 2 hUeach
  have hUunion' : (U.biUnion id).card ≤ 6 * 2 :=
    hUunion.trans (Nat.mul_le_mul_right _ hUcard)
  have hGcard : G.card = 3 := by simpa using link_uniform huniform x G hG
  have hHcard : H.card ≤ 16 := by
    calc
      H.card ≤ (G ∪ U.biUnion id).card + 1 := card_insert_le _ _
      _ ≤ (G.card + (U.biUnion id).card) + 1 := by
        gcongr
        exact card_union_le _ _
      _ ≤ (3 + 6 * 2) + 1 := by
        rw [hGcard]
        gcongr
      _ = 16 := by norm_num
  have hBU : B ∈ U := hBtwo
  have hBsubH : B ⊆ H := by
    intro b hb
    exact mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr ⟨B, hBU, hb⟩))
  have hbranchHuge :
      (H.card + 1) * n ^ (4 - 4) < (linkBranch 𝓕 x B).card := by
    have hcoef : H.card + 1 ≤ M := by dsimp [M]; omega
    exact (Nat.mul_le_mul_right _ hcoef).trans_lt hBlarge
  have hgood :=
    card_branchAvoiding_gt_of_branch_gt huniform hBcard hbranchHuge
  have hgoodne : (branchAvoiding 𝓕 x B H).Nonempty := by
    apply card_pos.mp
    omega
  obtain ⟨C, hCgood⟩ := hgoodne
  have hCbranch : C ∈ linkBranch 𝓕 x B := (mem_filter.mp hCgood).1
  have hClink : C ∈ link 𝓕 x := (mem_filter.mp hCbranch).1
  have hBC : B ⊆ C := (mem_filter.mp hCbranch).2
  have hCcard : C.card = 3 := by simpa using link_uniform huniform x C hClink
  obtain ⟨z, hzCB, hCeq⟩ :=
    exists_insert_eq_of_card_three_of_card_two_subset hBcard hCcard hBC
  have hdisj : Disjoint (C \ B) (H \ B) := (mem_filter.mp hCgood).2
  have hzH : z ∉ H := by
    intro hzH
    exact disjoint_left.mp hdisj hzCB
      (mem_sdiff.mpr ⟨hzH, (mem_sdiff.mp hzCB).2⟩)
  have hzB : z ∉ B := (mem_sdiff.mp hzCB).2
  have hxH : x ∈ H := mem_insert_self _ _
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hzH hxH
  have hKz : insert x B ∈ kernelClosure 4 (link 𝓕 z) := by
    rw [mem_kernelClosure_iff]
    apply KernelReachable.member
    · rw [mem_link_iff]
      refine ⟨by simp [hxz.symm, hzB], ?_⟩
      have hCdata := mem_link_iff.mp hClink
      have hEq : insert z (insert x B) = insert x C := by
        rw [hCeq]
        ext a
        simp [or_left_comm]
      rw [hEq]
      exact hCdata.2
    · simp
  obtain ⟨D, hDbase, hDle⟩ :=
    hNsmall n hnsmall 𝓕 z huniform havoid (by simpa using hdegAll z)
  have hDne : D.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hDcard_ne_one : D.card ≠ 1 := by
    intro hDone
    obtain ⟨d, rfl⟩ := card_eq_one.mp hDone
    exact hnosingleAll z ⟨d, hDbase⟩
  have hDcard : D.card = 2 := by
    have : 0 < D.card := card_pos.mpr hDne
    omega
  have hDtwo : D ∈ closedTwoBases 4 𝓕 z :=
    mem_filter.mpr ⟨hDbase, hDcard⟩
  have hDsub : D ⊆ insert x B :=
    twoBase_subset_of_transferred_kernel huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      rfl hKz (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU, (mem_insert.mp hz).resolve_left hxz.symm⟩))
      hDtwo
  have hzG : z ∉ insert x G := by
    intro hz
    apply hzH
    rw [mem_insert] at hz
    rcases hz with rfl | hzG
    · exact hxH
    · exact mem_insert_of_mem (mem_union_left _ hzG)
  have hxD :=
    transferred_twoBase_contains_x huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      hBcard hDtwo hDsub hG hBG hzG
  obtain ⟨E, hEtwo, hzE⟩ :=
    exists_twoBase_containing_swapped_point hk hxz hDtwo hxD (hnosingleAll x)
  apply hzH
  exact mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr ⟨E, hEtwo, hzE⟩))

/-- The pointwise form of the preceding four-uniform link theorem. -/
lemma exists_threshold_unique_twoBase_link_structure_four_local :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform 4 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) 1 ≤
          (𝓕.filter fun A => x ∈ A).card) →
        ∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := 4) 𝓕 x →
          ∃ B ∈ closedTwoBases 4 𝓕 x,
            ∀ G ∈ link 𝓕 x, B ⊆ G := by
  let M := 17
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_threshold_small_base_of_large_degree 4 (by decide)
  obtain ⟨Ndom, hNdom⟩ :=
    exists_threshold_dominant_two_base 4 M (by decide)
  refine ⟨max Nsmall Ndom, ?_⟩
  intro n hn 𝓕 huniform havoid hdegAll x hnosingleX
  have hnsmall : Nsmall ≤ n := (le_max_left _ _).trans hn
  have hndom : Ndom ≤ n := (le_max_right _ _).trans hn
  obtain ⟨B, hBtwo, hBlarge⟩ :=
    hNdom n hndom 𝓕 x huniform havoid (by simpa using hdegAll x) hnosingleX
  refine ⟨B, hBtwo, ?_⟩
  intro G hG
  by_contra hnotBG
  have hk : 2 ≤ 4 := by decide
  have hBcard : B.card = 2 := (mem_filter.mp hBtwo).2
  have hGB := inter_card_eq_one_of_not_subset_two_closedBase
    (x := x) (B := B) (A := G)
    huniform hk havoid hBtwo hG hnotBG
  have hBG : (B ∩ G).card = 1 := by simpa [inter_comm] using hGB
  let U := closedTwoBases 4 𝓕 x
  let H : Finset (Fin n) := insert x (G ∪ U.biUnion id)
  have hUcard : U.card ≤ 6 := by
    simpa [U, closedTwoBases] using
      two_closed_link_bases_card_le huniform (by decide) havoid x
  have hUeach : ∀ D ∈ U, (id D).card ≤ 2 := by
    intro D hD
    exact (mem_filter.mp hD).2.le
  have hUunion : (U.biUnion id).card ≤ U.card * 2 :=
    card_biUnion_le_card_mul U id 2 hUeach
  have hUunion' : (U.biUnion id).card ≤ 6 * 2 :=
    hUunion.trans (Nat.mul_le_mul_right _ hUcard)
  have hGcard : G.card = 3 := by simpa using link_uniform huniform x G hG
  have hHcard : H.card ≤ 16 := by
    calc
      H.card ≤ (G ∪ U.biUnion id).card + 1 := card_insert_le _ _
      _ ≤ (G.card + (U.biUnion id).card) + 1 := by
        gcongr
        exact card_union_le _ _
      _ ≤ (3 + 6 * 2) + 1 := by
        rw [hGcard]
        gcongr
      _ = 16 := by norm_num
  have hBU : B ∈ U := hBtwo
  have hBsubH : B ⊆ H := by
    intro b hb
    exact mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr ⟨B, hBU, hb⟩))
  have hbranchHuge :
      (H.card + 1) * n ^ (4 - 4) < (linkBranch 𝓕 x B).card := by
    have hcoef : H.card + 1 ≤ M := by dsimp [M]; omega
    exact (Nat.mul_le_mul_right _ hcoef).trans_lt hBlarge
  have hgood :=
    card_branchAvoiding_gt_of_branch_gt huniform hBcard hbranchHuge
  have hgoodne : (branchAvoiding 𝓕 x B H).Nonempty := by
    apply card_pos.mp
    omega
  obtain ⟨C, hCgood⟩ := hgoodne
  have hCbranch : C ∈ linkBranch 𝓕 x B := (mem_filter.mp hCgood).1
  have hClink : C ∈ link 𝓕 x := (mem_filter.mp hCbranch).1
  have hBC : B ⊆ C := (mem_filter.mp hCbranch).2
  have hCcard : C.card = 3 := by simpa using link_uniform huniform x C hClink
  obtain ⟨z, hzCB, hCeq⟩ :=
    exists_insert_eq_of_card_three_of_card_two_subset hBcard hCcard hBC
  have hdisj : Disjoint (C \ B) (H \ B) := (mem_filter.mp hCgood).2
  have hzH : z ∉ H := by
    intro hzH
    exact disjoint_left.mp hdisj hzCB
      (mem_sdiff.mpr ⟨hzH, (mem_sdiff.mp hzCB).2⟩)
  have hzB : z ∉ B := (mem_sdiff.mp hzCB).2
  have hxH : x ∈ H := mem_insert_self _ _
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hzH hxH
  have hKz : insert x B ∈ kernelClosure 4 (link 𝓕 z) := by
    rw [mem_kernelClosure_iff]
    apply KernelReachable.member
    · rw [mem_link_iff]
      refine ⟨by simp [hxz.symm, hzB], ?_⟩
      have hCdata := mem_link_iff.mp hClink
      have hEq : insert z (insert x B) = insert x C := by
        rw [hCeq]
        ext a
        simp [or_left_comm]
      rw [hEq]
      exact hCdata.2
    · simp
  have hKglobal : KernelReachable 4 𝓕 (insert x B) :=
    kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp
        (mem_filter.mp hBtwo).1).1)
  obtain ⟨D, hDbase, hDle⟩ :=
    hNsmall n hnsmall 𝓕 z huniform havoid (by simpa using hdegAll z)
  have hDne : D.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hDcard_ne_one : D.card ≠ 1 :=
    closedBase_card_ne_one_of_transferred_kernel huniform hk havoid
      hDbase hKz hKglobal (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU,
            (mem_insert.mp hz).resolve_left hxz.symm⟩))
  have hDcard : D.card = 2 := by
    have : 0 < D.card := card_pos.mpr hDne
    omega
  have hDtwo : D ∈ closedTwoBases 4 𝓕 z :=
    mem_filter.mpr ⟨hDbase, hDcard⟩
  have hDsub : D ⊆ insert x B :=
    twoBase_subset_of_transferred_kernel huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      rfl hKz (by
        intro hz
        exact hzH (by
          apply mem_insert_of_mem
          apply mem_union_right
          exact mem_biUnion.mpr ⟨B, hBU, (mem_insert.mp hz).resolve_left hxz.symm⟩))
      hDtwo
  have hzG : z ∉ insert x G := by
    intro hz
    apply hzH
    rw [mem_insert] at hz
    rcases hz with rfl | hzG
    · exact hxH
    · exact mem_insert_of_mem (mem_union_left _ hzG)
  have hxD :=
    transferred_twoBase_contains_x huniform hk havoid
      (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1
      hBcard hDtwo hDsub hG hBG hzG
  obtain ⟨E, hEtwo, hzE⟩ :=
    exists_twoBase_containing_swapped_point hk hxz hDtwo hxD hnosingleX
  apply hzH
  exact mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr ⟨E, hEtwo, hzE⟩))

lemma exists_threshold_unique_twoBase_link_structure_local_all
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        ∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := k) 𝓕 x →
          ∃ B ∈ closedTwoBases k 𝓕 x,
            ∀ G ∈ link 𝓕 x, B ⊆ G := by
  by_cases hk : k = 4
  · subst k
    simpa using exists_threshold_unique_twoBase_link_structure_four_local
  · have hk5 : 5 ≤ k := by omega
    exact exists_threshold_unique_twoBase_link_structure_local k hk5

lemma exists_threshold_card_lt_of_high_degrees_without_singleton_bases_four :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform 4 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) 1 ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x : Fin n, ¬ HasSingletonClosedLinkBase (k := 4) 𝓕 x) →
        𝓕.card < Nat.choose (n - 2) 2 := by
  obtain ⟨N, hN⟩ := exists_threshold_unique_twoBase_link_structure_four
  refine ⟨max N 5, ?_⟩
  intro n hn 𝓕 huniform havoid hdeg hnosingle
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have h4n : 4 < n := by
    have : 5 ≤ n := (le_max_right _ _).trans hn
    omega
  apply card_lt_twoStarBound_of_all_links_have_pair_core
    huniform (by decide) h4n
  exact hN n hnN 𝓕 huniform havoid hdeg hnosingle

lemma exists_threshold_singleton_base_of_large_high_degree_family_all
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        Nat.choose (n - 2) (k - 2) ≤ 𝓕.card →
        ∃ x : Fin n, HasSingletonClosedLinkBase (k := k) 𝓕 x := by
  by_cases hk : k = 4
  · subst k
    obtain ⟨N, hN⟩ :=
      exists_threshold_card_lt_of_high_degrees_without_singleton_bases_four
    refine ⟨N, ?_⟩
    intro n hn 𝓕 huniform havoid hdeg hlarge
    by_contra hnone
    push Not at hnone
    have hsmall := hN n hn 𝓕 huniform havoid (by simpa using hdeg) hnone
    norm_num at hlarge
    omega
  · have hk5 : 5 ≤ k := by omega
    exact exists_threshold_singleton_base_of_large_high_degree_family k hk5

lemma exists_threshold_low_degree_or_singleton_base
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) ≤ 𝓕.card →
        (∃ x : Fin n,
            (𝓕.filter fun A => x ∈ A).card <
              Nat.choose (n - 3) (k - 3)) ∨
          ∃ x : Fin n, HasSingletonClosedLinkBase (k := k) 𝓕 x := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_singleton_base_of_large_high_degree_family_all k hk4
  refine ⟨N, ?_⟩
  intro n hn 𝓕 huniform havoid hlarge
  by_cases hlow : ∃ x : Fin n,
      (𝓕.filter fun A => x ∈ A).card <
        Nat.choose (n - 3) (k - 3)
  · exact Or.inl hlow
  · right
    apply hN n hn 𝓕 huniform havoid
    · intro x
      by_contra hx
      apply hlow
      exact ⟨x, by omega⟩
    · exact hlarge

def pairCoverage {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (x y : Fin n) : Finset (Finset (Fin n)) :=
  𝓕.filter fun A => x ∈ A ∨ y ∈ A

lemma pairCoverage_eq_pointDegree_of_mem_iff {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x y : Fin n}
    (hxy : ∀ A ∈ 𝓕, x ∈ A ↔ y ∈ A) :
    pairCoverage 𝓕 x y = 𝓕.filter fun A => x ∈ A := by
  ext A
  by_cases hA : A ∈ 𝓕
  · have hiff := hxy A hA
    simp [pairCoverage, hA, hiff]
  · simp [pairCoverage, hA]

lemma pairCoverage_eq_pointDegree_of_singleton_base {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)) :
    pairCoverage 𝓕 x y = 𝓕.filter fun A => x ∈ A := by
  apply pairCoverage_eq_pointDegree_of_mem_iff
  exact (mem_iff_of_singleton_closedLinkBase huniform hk4 havoid hybase).2

def IsReciprocalPair {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (x y : Fin n) : Prop :=
  x ≠ y ∧ ∀ A ∈ 𝓕, (x ∈ A ↔ y ∈ A)

lemma reciprocalPair_of_singleton_base {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)) :
    IsReciprocalPair 𝓕 x y :=
  mem_iff_of_singleton_closedLinkBase huniform hk4 havoid hybase

lemma singleton_pair_kernels_compatible {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y u v : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x))
    (hvbase : ({v} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 u)) :
    (({x, y} : Finset (Fin n)) ∩ {u, v}).card ≠ 1 := by
  have hk : 2 ≤ k := by omega
  have hcompat := kernelReachable_compatible
    (q := k) (r := k) (𝓖 := 𝓕)
    havoid (fun A hA => by rw [huniform A hA]) hk (le_refl k)
    (kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hybase).1))
    (kernelReachable_insert_of_link hk
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hvbase).1))
  simpa [insert_comm] using hcompat

lemma singleton_pairs_eq_or_disjoint {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    (hk4 : 4 ≤ k) (havoid : AvoidsSingleton 𝓕)
    {x y u v : Fin n}
    (hybase : ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x))
    (hvbase : ({v} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 u)) :
    ({x, y} : Finset (Fin n)) = {u, v} ∨
      Disjoint ({x, y} : Finset (Fin n)) {u, v} := by
  have hxy := (reciprocalPair_of_singleton_base huniform hk4 havoid hybase).1
  have huv := (reciprocalPair_of_singleton_base huniform hk4 havoid hvbase).1
  have hcard1 : ({x, y} : Finset (Fin n)).card = 2 := by simp [hxy]
  have hcard2 : ({u, v} : Finset (Fin n)).card = 2 := by simp [huv]
  have hcompat :=
    singleton_pair_kernels_compatible huniform hk4 havoid hybase hvbase
  by_cases hdisj : Disjoint ({x, y} : Finset (Fin n)) {u, v}
  · exact Or.inr hdisj
  left
  have hpos : 0 < (({x, y} : Finset (Fin n)) ∩ {u, v}).card :=
    card_pos.mpr (not_disjoint_iff_nonempty_inter.mp hdisj)
  have hle :
      (({x, y} : Finset (Fin n)) ∩ {u, v}).card ≤ 2 := by
    calc
      (({x, y} : Finset (Fin n)) ∩ {u, v}).card ≤ ({x, y} : Finset (Fin n)).card :=
        card_le_card inter_subset_left
      _ = 2 := hcard1
  have hcard :
      (({x, y} : Finset (Fin n)) ∩ {u, v}).card = 2 := by omega
  have hEqLeft :
      ({x, y} : Finset (Fin n)) ∩ {u, v} = {x, y} :=
    eq_of_subset_of_card_le inter_subset_left (by rw [hcard1, hcard])
  have hEqRight :
      ({x, y} : Finset (Fin n)) ∩ {u, v} = {u, v} :=
    eq_of_subset_of_card_le inter_subset_right (by rw [hcard2, hcard])
  exact hEqLeft.symm.trans hEqRight

/-! ## Reciprocal-pair blocks -/

def coreStar {n : ℕ} (k : ℕ) (T : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.powersetCard k).filter (T ⊆ ·)

lemma card_coreStar {n k t : ℕ} {T : Finset (Fin n)}
    (hTcard : T.card = t) (htk : t ≤ k) :
    (coreStar k T).card = Nat.choose (n - t) (k - t) := by
  unfold coreStar
  rw [card_filter_powersetCard_subset]
  · rw [card_univ, Fintype.card_fin, hTcard]
  · simp
  · rw [hTcard]
    exact htk

lemma degree_le_choose_of_fixed_core {n k t : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕)
    {x : Fin n} {T : Finset (Fin n)}
    (hTcard : T.card = t) (htk : t ≤ k)
    (hcore : ∀ A ∈ 𝓕, x ∈ A → T ⊆ A) :
    (𝓕.filter fun A => x ∈ A).card ≤ Nat.choose (n - t) (k - t) := by
  have hsub :
      𝓕.filter (fun A => x ∈ A) ⊆ coreStar k T := by
    intro A hA
    have hAF : A ∈ 𝓕 := (mem_filter.mp hA).1
    have hxA : x ∈ A := (mem_filter.mp hA).2
    exact mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨by simp, huniform A hAF⟩,
        hcore A hAF hxA⟩
  calc
    (𝓕.filter fun A => x ∈ A).card ≤ (coreStar k T).card :=
      card_le_card hsub
    _ = Nat.choose (n - t) (k - t) := card_coreStar hTcard htk

lemma choose_sub_four_lt_choose_sub_three {n k : ℕ}
    (hk4 : 4 ≤ k) (hkn : k + 1 ≤ n) :
    Nat.choose (n - 4) (k - 4) <
      Nat.choose (n - 3) (k - 3) := by
  have hn3 : 0 < n - 3 := by omega
  have hk3 : 0 < k - 3 := by omega
  have hpascal :=
    Nat.choose_eq_choose_pred_add (n := n - 3) (k := k - 3) hn3 hk3
  have hpos : 0 < Nat.choose (n - 4) (k - 3) :=
    Nat.choose_pos (by omega)
  have hn4 : n - 3 - 1 = n - 4 := by omega
  have hk4' : k - 3 - 1 = k - 4 := by omega
  rw [hn4, hk4'] at hpascal
  omega

lemma choose_degree_lt_pair_gap {n k : ℕ}
    (hk4 : 4 ≤ k) (hkn : k + 1 ≤ n) :
    Nat.choose (n - 3) (k - 3) <
      Nat.choose (n - 2) (k - 2) - Nat.choose (n - 4) (k - 2) := by
  have hn2 : 0 < n - 2 := by omega
  have hk2 : 0 < k - 2 := by omega
  have hn3 : 0 < n - 3 := by omega
  have hkp : 0 < k - 2 := by omega
  have hfirst :=
    Nat.choose_eq_choose_pred_add (n := n - 2) (k := k - 2) hn2 hk2
  have hsecond :=
    Nat.choose_eq_choose_pred_add (n := n - 3) (k := k - 2) hn3 hkp
  have hpos : 0 < Nat.choose (n - 4) (k - 3) :=
    Nat.choose_pos (by omega)
  have hn3a : n - 2 - 1 = n - 3 := by omega
  have hk3a : k - 2 - 1 = k - 3 := by omega
  rw [hn3a, hk3a] at hfirst
  have hn4 : n - 3 - 1 = n - 4 := by omega
  have hk3b : k - 2 - 1 = k - 3 := by omega
  rw [hn4, hk3b] at hsecond
  omega

def IsSingletonPairBlock {n k : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (B : Finset (Fin n)) : Prop :=
  ∃ x y : Fin n, x ≠ y ∧ B = {x, y} ∧
    ({y} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 x)

lemma singletonPairBlock_card {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {B : Finset (Fin n)}
    (hB : IsSingletonPairBlock (k := k) 𝓕 B) :
    B.card = 2 := by
  obtain ⟨x, y, hxy, rfl, hbase⟩ := hB
  simp [hxy]

lemma singletonPairBlock_eq_or_disjoint {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (havoid : AvoidsSingleton 𝓕)
    {B C : Finset (Fin n)}
    (hB : IsSingletonPairBlock (k := k) 𝓕 B)
    (hC : IsSingletonPairBlock (k := k) 𝓕 C) :
    B = C ∨ Disjoint B C := by
  obtain ⟨x, y, hxy, rfl, hybase⟩ := hB
  obtain ⟨u, v, huv, rfl, hvbase⟩ := hC
  exact singleton_pairs_eq_or_disjoint huniform hk4 havoid hybase hvbase

lemma singletonPairBlock_subset_of_member {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (havoid : AvoidsSingleton 𝓕)
    {B : Finset (Fin n)} (hB : IsSingletonPairBlock (k := k) 𝓕 B)
    {z : Fin n} (hzB : z ∈ B) :
    ∀ A ∈ 𝓕, z ∈ A → B ⊆ A := by
  obtain ⟨x, y, hxy, rfl, hybase⟩ := hB
  have hrecip :=
    reciprocalPair_of_singleton_base huniform hk4 havoid hybase
  intro A hA hzA
  have hxyA : x ∈ A ↔ y ∈ A := hrecip.2 A hA
  have hxA : x ∈ A := by
    simp only [mem_insert, mem_singleton] at hzB
    rcases hzB with rfl | rfl
    · exact hzA
    · exact hxyA.mpr hzA
  have hyA : y ∈ A := hxyA.mp hxA
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hxA
  · exact hyA

lemma singleton_closedLinkBase_symm {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (hk : 2 ≤ k)
    {x y : Fin n} (hxy : x ≠ y)
    (hybase : ({y} : Finset (Fin n)) ∈
      closedDeltaBase k (link 𝓕 x)) :
    ({x} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 y) := by
  have hyreach : KernelReachable k (link 𝓕 x) ({y} : Finset (Fin n)) :=
    mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hybase).1
  have hswap :
      KernelReachable k (link 𝓕 y)
        (insert x (({y} : Finset (Fin n)).erase y)) :=
    kernelReachable_swap_link hxy hk hyreach (by simp)
  have hxcl : ({x} : Finset (Fin n)) ∈ kernelClosure k (link 𝓕 y) := by
    rw [mem_kernelClosure_iff]
    simpa using hswap
  obtain ⟨D, hDbase, hDsub⟩ :=
    exists_closedDeltaBase_subset_of_closure hxcl
  have hDne : D.Nonempty :=
    kernelReachable_nonempty
      (mem_kernelClosure_iff.mp (mem_closedDeltaBase_iff.mp hDbase).1)
  have hDeq : D = ({x} : Finset (Fin n)) := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨d, hd⟩ := hDne
      have hd' := hDsub hd
      have hdx : d = x := by simpa using hd'
      subst d
      exact hd
    · intro d hd
      have hd' := hDsub hd
      simpa using hd'
  simpa [hDeq] using hDbase

lemma link_core_subset_of_member {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {x : Fin n}
    {B : Finset (Fin n)}
    (hcore : ∀ G ∈ link 𝓕 x, B ⊆ G) :
    ∀ A ∈ 𝓕, x ∈ A → insert x B ⊆ A := by
  intro A hA hxA
  have hlink : A.erase x ∈ link 𝓕 x := by
    rw [mem_link_iff]
    exact ⟨by simp, by simpa [insert_erase hxA] using hA⟩
  have hBAerase := hcore (A.erase x) hlink
  apply insert_subset hxA
  intro b hb
  exact (mem_erase.mp (hBAerase hb)).2

lemma not_low_pair_of_reciprocal_triple_core {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (hkn : k + 1 ≤ n)
    {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcore : ∀ A ∈ 𝓕, x ∈ A → ({x, y, z} : Finset (Fin n)) ⊆ A)
    (hiff : ∀ A ∈ 𝓕, x ∈ A ↔ y ∈ A)
    (hpair : Nat.choose (n - 2) (k - 2) -
        Nat.choose (n - 4) (k - 2) ≤
      (pairCoverage 𝓕 x y).card) :
    False := by
  have hxyzcard : ({x, y, z} : Finset (Fin n)).card = 3 := by
    simp [hxy, hxz, hyz]
  have hdeg :
      (𝓕.filter fun A => x ∈ A).card ≤
        Nat.choose (n - 3) (k - 3) :=
    degree_le_choose_of_fixed_core huniform hxyzcard (by omega) hcore
  have hcov :
      pairCoverage 𝓕 x y = 𝓕.filter fun A => x ∈ A :=
    pairCoverage_eq_pointDegree_of_mem_iff hiff
  rw [hcov] at hpair
  have hgap := choose_degree_lt_pair_gap hk4 hkn
  omega

lemma false_of_four_core_high_degree {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (hkn : k + 1 ≤ n)
    {x : Fin n} {T : Finset (Fin n)}
    (hTcard : T.card = 4)
    (hcore : ∀ A ∈ 𝓕, x ∈ A → T ⊆ A)
    (hdeg : Nat.choose (n - 3) (k - 3) ≤
      (𝓕.filter fun A => x ∈ A).card) :
    False := by
  have hdegUpper :
      (𝓕.filter fun A => x ∈ A).card ≤
        Nat.choose (n - 4) (k - 4) :=
    degree_le_choose_of_fixed_core huniform hTcard hk4 hcore
  have hstrict := choose_sub_four_lt_choose_sub_three hk4 hkn
  omega

lemma exists_threshold_singletonPairBlock_at_every_point
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x y : Fin n, x ≠ y →
          Nat.choose (n - 2) (k - 2) - Nat.choose (n - 4) (k - 2) ≤
            (pairCoverage 𝓕 x y).card) →
        ∀ x : Fin n, ∃ B : Finset (Fin n),
          IsSingletonPairBlock (k := k) 𝓕 B ∧
          ∀ A ∈ 𝓕, x ∈ A → B ⊆ A := by
  obtain ⟨Nlocal, hNlocal⟩ :=
    exists_threshold_unique_twoBase_link_structure_local_all k hk4
  refine ⟨max Nlocal (k + 1), ?_⟩
  intro n hn 𝓕 huniform havoid hdeg hpair x
  have hnlocal : Nlocal ≤ n := (le_max_left _ _).trans hn
  have hkn : k + 1 ≤ n := (le_max_right _ _).trans hn
  by_cases hxsingle : HasSingletonClosedLinkBase (k := k) 𝓕 x
  · obtain ⟨y, hybase⟩ := hxsingle
    have hrecip :=
      reciprocalPair_of_singleton_base huniform hk4 havoid hybase
    refine ⟨{x, y}, ⟨x, y, hrecip.1, rfl, hybase⟩, ?_⟩
    intro A hA hxA
    have hyA : y ∈ A := (hrecip.2 A hA).mp hxA
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hxA
    · exact hyA
  · obtain ⟨B, hBtwo, hBcore⟩ :=
      hNlocal n hnlocal 𝓕 huniform havoid hdeg x hxsingle
    have hBcard : B.card = 2 := (mem_filter.mp hBtwo).2
    have hxB : x ∉ B :=
      kernelReachable_not_mem_of_link (by omega)
        (mem_kernelClosure_iff.mp
          (mem_closedDeltaBase_iff.mp (mem_filter.mp hBtwo).1).1)
    obtain ⟨y, z, hyz, hBeq⟩ := Finset.card_eq_two.mp hBcard
    subst B
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hxB (by simp)
    have hxz : x ≠ z := by
      intro h
      subst z
      exact hxB (by simp)
    have hxyzcore :
        ∀ A ∈ 𝓕, x ∈ A → ({x, y, z} : Finset (Fin n)) ⊆ A := by
      intro A hA hxA
      simpa using
        (link_core_subset_of_member hBcore A hA hxA)
    have hyzbase :
        ({z} : Finset (Fin n)) ∈ closedDeltaBase k (link 𝓕 y) := by
      by_cases hysingle : HasSingletonClosedLinkBase (k := k) 𝓕 y
      · obtain ⟨w, hwbase⟩ := hysingle
        have hyw :=
          reciprocalPair_of_singleton_base huniform hk4 havoid hwbase
        by_cases hwz : w = z
        · simpa [hwz] using hwbase
        by_cases hwx : w = x
        · subst w
          exfalso
          exact not_low_pair_of_reciprocal_triple_core
            huniform hk4 hkn hxy hxz hyz hxyzcore
            (fun A hA => (hyw.2 A hA).symm) (hpair x y hxy)
        · exfalso
          have hwy : w ≠ y := hyw.1.symm
          have hxw : x ≠ w := by
            intro hxw
            exact hwx hxw.symm
          have hywne : y ≠ w := hyw.1
          have hzw : z ≠ w := by
            intro hzw
            exact hwz hzw.symm
          have hTcard : ({x, y, z, w} : Finset (Fin n)).card = 4 := by
            simp [hxy, hxz, hyz, hxw, hywne, hzw]
          exact false_of_four_core_high_degree huniform hk4 hkn hTcard
            (by
              intro A hA hxA
              have hxyz := hxyzcore A hA hxA
              have hyA : y ∈ A := hxyz (by simp)
              have hwA : w ∈ A := (hyw.2 A hA).mp hyA
              intro a ha
              simp only [mem_insert, mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl
              · exact hxA
              · exact hyA
              · exact hxyz (by simp)
              · exact hwA)
            (hdeg x)
      · exfalso
        obtain ⟨C, hCtwo, hCcore⟩ :=
          hNlocal n hnlocal 𝓕 huniform havoid hdeg y hysingle
        have hCcard : C.card = 2 := (mem_filter.mp hCtwo).2
        have hyC : y ∉ C :=
          kernelReachable_not_mem_of_link (by omega)
            (mem_kernelClosure_iff.mp
              (mem_closedDeltaBase_iff.mp (mem_filter.mp hCtwo).1).1)
        have hycore :
            ∀ A ∈ 𝓕, y ∈ A → insert y C ⊆ A :=
          link_core_subset_of_member hCcore
        by_cases hCeq : C = {x, z}
        · have hiff : ∀ A ∈ 𝓕, x ∈ A ↔ y ∈ A := by
            intro A hA
            constructor
            · intro hxA
              exact hxyzcore A hA hxA (by simp)
            · intro hyA
              have hsub := hycore A hA hyA
              exact hsub (by simp [hCeq])
          exact not_low_pair_of_reciprocal_triple_core
            huniform hk4 hkn hxy hxz hyz hxyzcore hiff (hpair x y hxy)
        · have hCnsub : ¬ C ⊆ ({x, y, z} : Finset (Fin n)) := by
            intro hCsub
            have hCsubxz : C ⊆ ({x, z} : Finset (Fin n)) := by
              intro c hc
              have hc' := hCsub hc
              simp only [mem_insert, mem_singleton] at hc'
              rcases hc' with rfl | rfl | rfl
              · simp
              · exact (hyC hc).elim
              · simp
            have hEq : C = {x, z} :=
              eq_of_subset_of_card_le hCsubxz (by
                rw [hCcard]
                simp [hxz])
            exact hCeq hEq
          obtain ⟨c, hcC, hcnot⟩ := not_subset.mp hCnsub
          have hTcard : ({c, x, y, z} : Finset (Fin n)).card = 4 := by
            have hcx : c ≠ x := by
              intro h
              subst c
              exact hcnot (by simp)
            have hcy : c ≠ y := by
              intro h
              subst c
              exact hcnot (by simp)
            have hcz : c ≠ z := by
              intro h
              subst c
              exact hcnot (by simp)
            simp [hxy, hxz, hyz, hcx, hcy, hcz]
          exact false_of_four_core_high_degree huniform hk4 hkn hTcard
            (by
              intro A hA hxA
              have hxyz := hxyzcore A hA hxA
              have hyA : y ∈ A := hxyz (by simp)
              have hCsubA := hycore A hA hyA
              have hcA : c ∈ A := hCsubA (by simp [hcC])
              intro a ha
              simp only [mem_insert, mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl
              · exact hcA
              · exact hxA
              · exact hyA
              · exact hxyz (by simp))
            (hdeg x)
    refine ⟨{y, z}, ⟨y, z, hyz, rfl, hyzbase⟩, ?_⟩
    intro A hA hxA
    have hsub := hxyzcore A hA hxA
    intro a ha
    apply hsub
    simp only [mem_insert, mem_singleton] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def blocksOf {n : ℕ} (b : Fin n → Finset (Fin n))
    (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  A.image b

def BlockAllowed {n : ℕ} (b : Fin n → Finset (Fin n))
    (A : Finset (Fin n)) : Prop :=
  ∀ x ∈ A, b x ⊆ A

def blockClosure {n : ℕ} (b : Fin n → Finset (Fin n))
    (A : Finset (Fin n)) : Finset (Fin n) :=
  A ∪ (blocksOf b A).biUnion id

def EncodesByBlocks {n : ℕ} (b : Fin n → Finset (Fin n))
    (p A E : Finset (Fin n)) : Prop :=
  (p ⊆ A ∧ E = A) ∨
    (¬ p ⊆ A ∧
      (((blocksOf b A).card = 1 ∧
          ∃ B ∈ blocksOf b A, E = (A \ B) ∪ p) ∨
        (2 ≤ (blocksOf b A).card ∧
          ∃ B ∈ blocksOf b A, ∃ C ∈ blocksOf b A, B ≠ C ∧
            ∃ u ∈ B, ∃ v ∈ C,
              E = ((A.erase u).erase v) ∪ p)))

lemma block_of_mem_blocksOf {n : ℕ} {b : Fin n → Finset (Fin n)}
    {A B : Finset (Fin n)} (hB : B ∈ blocksOf b A) :
    ∃ x ∈ A, b x = B := by
  simpa [blocksOf] using (mem_image.mp hB)

lemma blocksOf_nonempty_of_nonempty {n : ℕ}
    (b : Fin n → Finset (Fin n)) {A : Finset (Fin n)}
    (hA : A.Nonempty) :
    (blocksOf b A).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  exact ⟨b x, by
    exact mem_image.mpr ⟨x, hx, rfl⟩⟩

lemma block_subset_of_mem_blocksOf {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {b : Fin n → Finset (Fin n)}
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    {A B : Finset (Fin n)} (hA : A ∈ 𝓕)
    (hB : B ∈ blocksOf b A) :
    B ⊆ A := by
  obtain ⟨x, hxA, rfl⟩ := block_of_mem_blocksOf hB
  exact hcover A hA x hxA

lemma blockAllowed_of_mem {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))} {b : Fin n → Finset (Fin n)}
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    {A : Finset (Fin n)} (hA : A ∈ 𝓕) :
    BlockAllowed b A := by
  intro x hx
  exact hcover A hA x hx

lemma exists_encodesByBlocks {n : ℕ}
    (b : Fin n → Finset (Fin n))
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (p A : Finset (Fin n)) (hAne : A.Nonempty) :
    ∃ E : Finset (Fin n), EncodesByBlocks b p A E := by
  by_cases hpA : p ⊆ A
  · exact ⟨A, Or.inl ⟨hpA, rfl⟩⟩
  · have hSne : (blocksOf b A).Nonempty :=
      blocksOf_nonempty_of_nonempty b hAne
    by_cases hScard : (blocksOf b A).card = 1
    · obtain ⟨B, hB⟩ := hSne
      exact ⟨(A \ B) ∪ p,
        Or.inr ⟨hpA, Or.inl ⟨hScard, B, hB, rfl⟩⟩⟩
    · have hSge : 2 ≤ (blocksOf b A).card := by
        have hpos : 0 < (blocksOf b A).card := card_pos.mpr hSne
        omega
      obtain ⟨B, hB⟩ := hSne
      have hSerase : ((blocksOf b A).erase B).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem hB]
        omega
      obtain ⟨C, hCerase⟩ := hSerase
      have hC : C ∈ blocksOf b A := (mem_erase.mp hCerase).2
      have hBC : B ≠ C := by
        intro h
        subst C
        exact (mem_erase.mp hCerase).1 rfl
      obtain ⟨x, hxA, hBx⟩ := block_of_mem_blocksOf hB
      obtain ⟨y, hyA, hCy⟩ := block_of_mem_blocksOf hC
      have hBne : B.Nonempty := by
        apply card_pos.mp
        rw [← hBx, hblockCard]
        omega
      have hCne : C.Nonempty := by
        apply card_pos.mp
        rw [← hCy, hblockCard]
        omega
      obtain ⟨u, huB⟩ := hBne
      obtain ⟨v, hvC⟩ := hCne
      exact ⟨((A.erase u).erase v) ∪ p,
        Or.inr ⟨hpA, Or.inr
          ⟨hSge, B, hB, C, hC, hBC, u, huB, v, hvC, rfl⟩⟩⟩

lemma disjoint_of_not_subset_of_endpoint_block {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)} {p A : Finset (Fin n)}
    {x₀ : Fin n} (hp : p = b x₀)
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    (hA : A ∈ 𝓕) (hpA : ¬ p ⊆ A) :
    Disjoint p A := by
  apply disjoint_left.mpr
  intro z hzP hzA
  have hbz : b z = p := by
    rw [hp]
    exact hend x₀ z (by simpa [hp] using hzP)
  apply hpA
  rw [← hbz]
  exact hcover A hA z hzA

lemma block_disjoint_of_distinct_mem_blocksOf {n : ℕ}
    {b : Fin n → Finset (Fin n)} {A B C : Finset (Fin n)}
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hB : B ∈ blocksOf b A) (hC : C ∈ blocksOf b A)
    (hBC : B ≠ C) :
    Disjoint B C := by
  obtain ⟨x, hxA, rfl⟩ := block_of_mem_blocksOf hB
  obtain ⟨y, hyA, hCy⟩ := block_of_mem_blocksOf hC
  rcases hpair x y with hEq | hDisj
  · exfalso
    apply hBC
    rw [← hCy, hEq]
  · simpa [hCy] using hDisj

lemma encodesByBlocks_card_eq {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)} {p A E : Finset (Fin n)}
    {x₀ : Fin n} (hp : p = b x₀)
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    (hA : A ∈ 𝓕) (hAcard : A.card = k)
    (henc : EncodesByBlocks b p A E) :
    E.card = k := by
  rcases henc with ⟨hpA, rfl⟩ | ⟨hpA, hcase⟩
  · exact hAcard
  have hpDisjA := disjoint_of_not_subset_of_endpoint_block hp hend hcover hA hpA
  have hpCard : p.card = 2 := by rw [hp, hblockCard]
  rcases hcase with ⟨hScard, B, hB, rfl⟩ |
      ⟨hSge, B, hB, C, hC, hBC, u, huB, v, hvC, rfl⟩
  · have hBsub : B ⊆ A := block_subset_of_mem_blocksOf hcover hA hB
    obtain ⟨x, hxA, hBx⟩ := block_of_mem_blocksOf hB
    have hBcard : B.card = 2 := by rw [← hBx, hblockCard]
    have hdisj : Disjoint (A \ B) p :=
      Disjoint.mono (sdiff_subset : A \ B ⊆ A) Subset.rfl hpDisjA.symm
    have hk2 : 2 ≤ k := by
      have hcardLe := card_le_card hBsub
      rw [hAcard, hBcard] at hcardLe
      exact hcardLe
    rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hBsub,
      hAcard, hBcard, hpCard]
    omega
  · have hBsub : B ⊆ A := block_subset_of_mem_blocksOf hcover hA hB
    have hCsub : C ⊆ A := block_subset_of_mem_blocksOf hcover hA hC
    have huA : u ∈ A := hBsub huB
    have hvA : v ∈ A := hCsub hvC
    have hBCdisj := block_disjoint_of_distinct_mem_blocksOf hpair hB hC hBC
    have huv : u ≠ v := by
      intro huv
      subst v
      exact disjoint_left.mp hBCdisj huB hvC
    have hvErase : v ∈ A.erase u := mem_erase.mpr ⟨huv.symm, hvA⟩
    have hcardErase : ((A.erase u).erase v).card = A.card - 2 := by
      rw [card_erase_of_mem hvErase, card_erase_of_mem huA]
      omega
    have hdisj : Disjoint ((A.erase u).erase v) p :=
      Disjoint.mono (by
        exact (erase_subset _ _).trans (erase_subset _ _)) Subset.rfl hpDisjA.symm
    rw [card_union_of_disjoint hdisj, hcardErase, hAcard, hpCard]
    have hk2 : 2 ≤ k := by
      have hpairSub : ({u, v} : Finset (Fin n)) ⊆ A := by
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact huA
        · exact hvA
      have hcardLe := card_le_card hpairSub
      rw [hAcard] at hcardLe
      simpa [huv] using hcardLe
    omega

lemma blockClosure_subset_of {n : ℕ}
    {b : Fin n → Finset (Fin n)}
    {E U : Finset (Fin n)}
    (hE : E ⊆ U)
    (hblocks : ∀ x ∈ E, b x ⊆ U) :
    blockClosure b E ⊆ U := by
  intro a ha
  rw [blockClosure, mem_union] at ha
  rcases ha with haE | haU
  · exact hE haE
  · obtain ⟨B, hB, haB⟩ := mem_biUnion.mp haU
    obtain ⟨x, hxE, rfl⟩ := block_of_mem_blocksOf hB
    exact hblocks x hxE haB

lemma sdiff_eq_left_of_eq_union_of_disjoint {n : ℕ}
    {A p U : Finset (Fin n)}
    (hU : U = A ∪ p) (hdisj : Disjoint p A) :
    U \ p = A := by
  rw [hU]
  ext a
  by_cases haP : a ∈ p
  · have haA : a ∉ A := fun haA => disjoint_left.mp hdisj haP haA
    simp [haP, haA]
  · simp [haP]

lemma one_block_encode_not_allowed_and_recovers {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)} {p A B E : Finset (Fin n)}
    {x₀ : Fin n} (hp : p = b x₀)
    (hk4 : 4 ≤ k)
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    (hA : A ∈ 𝓕) (hAcard : A.card = k)
    (hpA : ¬ p ⊆ A)
    (hSone : (blocksOf b A).card = 1)
    (hB : B ∈ blocksOf b A)
    (hE : E = (A \ B) ∪ p) :
    ¬ BlockAllowed b E ∧ blockClosure b E \ p = A := by
  have hpDisjA := disjoint_of_not_subset_of_endpoint_block hp hend hcover hA hpA
  have hBsub : B ⊆ A := block_subset_of_mem_blocksOf hcover hA hB
  obtain ⟨x, hxA, hBx⟩ := block_of_mem_blocksOf hB
  have hBcard : B.card = 2 := by rw [← hBx, hblockCard]
  have hBne : B.Nonempty := card_pos.mp (by rw [hBcard]; omega)
  have hBnep : B ≠ p := by
    intro h
    apply hpA
    simpa [h] using hBsub
  have hBpdisj : Disjoint B p := by
    have hx0 : b x ≠ b x₀ := by
      intro hEq
      apply hBnep
      calc
        B = b x := hBx.symm
        _ = b x₀ := hEq
        _ = p := hp.symm
    rcases hpair x x₀ with hEq | hDisj
    · exact (hx0 hEq).elim
    · simpa [hBx, hp] using hDisj
  have hdiffCard : (A \ B).card = k - 2 := by
    rw [card_sdiff_of_subset hBsub, hAcard, hBcard]
  have hdiffNe : (A \ B).Nonempty := by
    apply card_pos.mp
    rw [hdiffCard]
    omega
  obtain ⟨t, htDiff⟩ := hdiffNe
  have htA : t ∈ A := (mem_sdiff.mp htDiff).1
  have htB : t ∉ B := (mem_sdiff.mp htDiff).2
  have hS_eq : blocksOf b A = {B} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hB, ?_⟩
    intro C hC
    have hsub : ({B, C} : Finset (Finset (Fin n))) ⊆ blocksOf b A := by
      intro D hD
      simp only [mem_insert, mem_singleton] at hD
      rcases hD with rfl | rfl
      · exact hB
      · exact hC
    have hle := card_le_card hsub
    rw [hSone] at hle
    by_contra hBC
    have : ({B, C} : Finset (Finset (Fin n))).card = 2 :=
      card_pair (by
        intro h
        exact hBC h.symm)
    rw [this] at hle
    omega
  have hbt : b t = B := by
    have : b t ∈ blocksOf b A := by
      exact mem_image.mpr ⟨t, htA, rfl⟩
    rw [hS_eq] at this
    simpa using this
  have htE : t ∈ E := by rw [hE]; exact mem_union_left _ htDiff
  have hBnotSubE : ¬ B ⊆ E := by
    obtain ⟨q, hqB⟩ := hBne
    intro hBsubE
    have hqE := hBsubE hqB
    rw [hE] at hqE
    rcases mem_union.mp hqE with hqDiff | hqP
    · exact (mem_sdiff.mp hqDiff).2 hqB
    · exact disjoint_left.mp hBpdisj hqB hqP
  have hnotAllowed : ¬ BlockAllowed b E := by
    intro hallowed
    exact hBnotSubE (by rw [← hbt]; exact hallowed t htE)
  refine ⟨hnotAllowed, ?_⟩
  apply sdiff_eq_left_of_eq_union_of_disjoint ?_ hpDisjA
  apply Subset.antisymm
  · apply blockClosure_subset_of (U := A ∪ p)
    · rw [hE]
      exact union_subset_union_left sdiff_subset
    · intro q hqE
      rw [hE] at hqE
      rcases mem_union.mp hqE with hqDiff | hqP
      · have hqA : q ∈ A := (mem_sdiff.mp hqDiff).1
        exact subset_trans (hcover A hA q hqA) (subset_union_left)
      · have hbq : b q = p := by
          rw [hp]
          exact hend x₀ q (by simpa [hp] using hqP)
        rw [hbq]
        exact subset_union_right
  · intro q hq
    rcases mem_union.mp hq with hqA | hqP
    · by_cases hqB : q ∈ B
      · rw [blockClosure]
        apply mem_union_right
        exact mem_biUnion.mpr ⟨B, by
          exact mem_image.mpr ⟨t, htE, hbt⟩, hqB⟩
      · rw [blockClosure]
        apply mem_union_left
        rw [hE]
        exact mem_union_left _ (mem_sdiff.mpr ⟨hqA, hqB⟩)
    · rw [blockClosure]
      apply mem_union_left
      rw [hE]
      exact mem_union_right _ hqP

lemma two_block_encode_not_allowed_and_recovers {n : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)}
    {p A B C E : Finset (Fin n)}
    {x₀ u v : Fin n} (hp : p = b x₀)
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    (hA : A ∈ 𝓕) (hpA : ¬ p ⊆ A)
    (hB : B ∈ blocksOf b A) (hC : C ∈ blocksOf b A)
    (hBC : B ≠ C) (huB : u ∈ B) (hvC : v ∈ C)
    (hE : E = ((A.erase u).erase v) ∪ p) :
    ¬ BlockAllowed b E ∧ blockClosure b E \ p = A := by
  have hpDisjA := disjoint_of_not_subset_of_endpoint_block hp hend hcover hA hpA
  have hBsub : B ⊆ A := block_subset_of_mem_blocksOf hcover hA hB
  have hCsub : C ⊆ A := block_subset_of_mem_blocksOf hcover hA hC
  obtain ⟨x, hxA, hBx⟩ := block_of_mem_blocksOf hB
  obtain ⟨y, hyA, hCy⟩ := block_of_mem_blocksOf hC
  have hBcard : B.card = 2 := by rw [← hBx, hblockCard]
  have hCcard : C.card = 2 := by rw [← hCy, hblockCard]
  have hBCdisj := block_disjoint_of_distinct_mem_blocksOf hpair hB hC hBC
  have huA : u ∈ A := hBsub huB
  have hvA : v ∈ A := hCsub hvC
  have huv : u ≠ v := by
    intro huv
    subst v
    exact disjoint_left.mp hBCdisj huB hvC
  have hBeraseNe : (B.erase u).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem huB, hBcard]
    omega
  have hCeraseNe : (C.erase v).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hvC, hCcard]
    omega
  obtain ⟨u', hu'⟩ := hBeraseNe
  obtain ⟨v', hv'⟩ := hCeraseNe
  have hu'B : u' ∈ B := (mem_erase.mp hu').2
  have hu'ne : u' ≠ u := (mem_erase.mp hu').1
  have hv'C : v' ∈ C := (mem_erase.mp hv').2
  have hv'ne : v' ≠ v := (mem_erase.mp hv').1
  have hu'v : u' ≠ v := by
    intro h
    subst v
    exact disjoint_left.mp hBCdisj hu'B hvC
  have hv'u : v' ≠ u := by
    intro h
    subst u
    exact disjoint_left.mp hBCdisj huB hv'C
  have hu'E : u' ∈ E := by
    rw [hE]
    apply mem_union_left
    exact mem_erase.mpr ⟨hu'v, mem_erase.mpr ⟨hu'ne, hBsub hu'B⟩⟩
  have hv'E : v' ∈ E := by
    rw [hE]
    apply mem_union_left
    exact mem_erase.mpr ⟨hv'ne, mem_erase.mpr ⟨hv'u, hCsub hv'C⟩⟩
  have hbu' : b u' = B := by
    rw [← hBx]
    exact hend x u' (by simpa [hBx] using hu'B)
  have hbv' : b v' = C := by
    rw [← hCy]
    exact hend y v' (by simpa [hCy] using hv'C)
  have huNotE : u ∉ E := by
    rw [hE]
    intro huE
    rcases mem_union.mp huE with huErase | huP
    · exact (mem_erase.mp (mem_erase.mp huErase).2).1 rfl
    · exact disjoint_left.mp hpDisjA huP huA
  have hBnotSubE : ¬ B ⊆ E := by
    intro hsub
    exact huNotE (hsub huB)
  have hnotAllowed : ¬ BlockAllowed b E := by
    intro hallowed
    exact hBnotSubE (by rw [← hbu']; exact hallowed u' hu'E)
  refine ⟨hnotAllowed, ?_⟩
  apply sdiff_eq_left_of_eq_union_of_disjoint ?_ hpDisjA
  apply Subset.antisymm
  · apply blockClosure_subset_of (U := A ∪ p)
    · rw [hE]
      exact union_subset_union_left
        ((erase_subset _ _).trans (erase_subset _ _))
    · intro q hqE
      rw [hE] at hqE
      rcases mem_union.mp hqE with hqErase | hqP
      · have hqA : q ∈ A :=
          (mem_erase.mp (mem_erase.mp hqErase).2).2
        exact subset_trans (hcover A hA q hqA) subset_union_left
      · have hbq : b q = p := by
          rw [hp]
          exact hend x₀ q (by simpa [hp] using hqP)
        rw [hbq]
        exact subset_union_right
  · intro q hq
    rcases mem_union.mp hq with hqA | hqP
    · by_cases hqu : q = u
      · subst q
        rw [blockClosure]
        apply mem_union_right
        exact mem_biUnion.mpr ⟨B,
          mem_image.mpr ⟨u', hu'E, hbu'⟩, huB⟩
      · by_cases hqv : q = v
        · subst q
          rw [blockClosure]
          apply mem_union_right
          exact mem_biUnion.mpr ⟨C,
            mem_image.mpr ⟨v', hv'E, hbv'⟩, hvC⟩
        · rw [blockClosure]
          apply mem_union_left
          rw [hE]
          apply mem_union_left
          exact mem_erase.mpr ⟨hqv, mem_erase.mpr ⟨hqu, hqA⟩⟩
    · rw [blockClosure]
      apply mem_union_left
      rw [hE]
      exact mem_union_right _ hqP

noncomputable def blockDecode {n : ℕ} (b : Fin n → Finset (Fin n))
    (p E : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact if BlockAllowed b E then E else blockClosure b E \ p

lemma blockDecode_of_encodesByBlocks {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)} {p A E : Finset (Fin n)}
    {x₀ : Fin n} (hp : p = b x₀)
    (hk4 : 4 ≤ k)
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A)
    (hA : A ∈ 𝓕) (hAcard : A.card = k)
    (henc : EncodesByBlocks b p A E) :
    blockDecode b p E = A := by
  rcases henc with ⟨hpA, rfl⟩ | ⟨hpA, hcase⟩
  · rw [blockDecode, if_pos]
    exact blockAllowed_of_mem hcover hA
  · rcases hcase with ⟨hSone, B, hB, hE⟩ |
        ⟨hSge, B, hB, C, hC, hBC, u, huB, v, hvC, hE⟩
    · have hrec :=
        one_block_encode_not_allowed_and_recovers hp hk4 hblockCard hpair
          hend hcover hA hAcard hpA hSone hB hE
      rw [blockDecode, if_neg hrec.1]
      exact hrec.2
    · have hrec :=
        two_block_encode_not_allowed_and_recovers hp hblockCard
          hpair hend hcover hA hpA hB hC hBC huB hvC hE
      rw [blockDecode, if_neg hrec.1]
      exact hrec.2

lemma p_subset_of_encodesByBlocks {n : ℕ}
    {b : Fin n → Finset (Fin n)} {p A E : Finset (Fin n)}
    (henc : EncodesByBlocks b p A E) :
    p ⊆ E := by
  rcases henc with ⟨hpA, rfl⟩ | ⟨hpA, hcase⟩
  · exact hpA
  · rcases hcase with ⟨hSone, B, hB, rfl⟩ |
        ⟨hSge, B, hB, C, hC, hBC, u, huB, v, hvC, rfl⟩
    · exact subset_union_right
    · exact subset_union_right

lemma card_le_choose_of_block_assignment {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {b : Fin n → Finset (Fin n)} {x₀ : Fin n}
    (huniform : IsUniform k 𝓕) (hk4 : 4 ≤ k)
    (hblockCard : ∀ x : Fin n, (b x).card = 2)
    (hpair : ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y))
    (hend : ∀ x z : Fin n, z ∈ b x → b z = b x)
    (hcover : ∀ A ∈ 𝓕, ∀ x ∈ A, b x ⊆ A) :
    𝓕.card ≤ Nat.choose (n - 2) (k - 2) := by
  classical
  let p : Finset (Fin n) := b x₀
  let f : Finset (Fin n) → Finset (Fin n) := fun A =>
    if hA : A ∈ 𝓕 then
      Classical.choose
        (exists_encodesByBlocks b hblockCard p A (by
          apply card_pos.mp
          rw [huniform A hA]
          omega))
    else A
  have hfenc : ∀ A ∈ 𝓕, EncodesByBlocks b p A (f A) := by
    intro A hA
    dsimp [f]
    rw [dif_pos hA]
    exact Classical.choose_spec
      (exists_encodesByBlocks b hblockCard p A (by
        apply card_pos.mp
        rw [huniform A hA]
        omega))
  have hmap : Set.MapsTo f (𝓕 : Set (Finset (Fin n))) (coreStar k p) := by
    intro A hA
    have henc := hfenc A hA
    have hpSub : p ⊆ f A := p_subset_of_encodesByBlocks henc
    have hcard : (f A).card = k :=
      encodesByBlocks_card_eq (p := p) (x₀ := x₀) rfl
        hblockCard hpair hend hcover hA (huniform A hA) henc
    exact mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨by simp, hcard⟩, hpSub⟩
  have hinj : (𝓕 : Set (Finset (Fin n))).InjOn f := by
    intro A hA C hC hEq
    have hdec := congrArg (blockDecode b p) hEq
    rw [blockDecode_of_encodesByBlocks (p := p) (x₀ := x₀) rfl hk4
      hblockCard hpair hend hcover hA (huniform A hA) (hfenc A hA)] at hdec
    rw [blockDecode_of_encodesByBlocks (p := p) (x₀ := x₀) rfl hk4
      hblockCard hpair hend hcover hC (huniform C hC) (hfenc C hC)] at hdec
    exact hdec
  calc
    𝓕.card ≤ (coreStar k p).card :=
      card_le_card_of_injOn f hmap hinj
    _ = Nat.choose (n - 2) (k - 2) := by
      apply card_coreStar
      · dsimp [p]
        exact hblockCard x₀
      · omega

lemma exists_threshold_card_le_of_high_degrees_and_high_pair_coverages
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (𝓕 : Finset (Finset (Fin n))),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        (∀ x : Fin n, Nat.choose (n - 3) (k - 3) ≤
          (𝓕.filter fun A => x ∈ A).card) →
        (∀ x y : Fin n, x ≠ y →
          Nat.choose (n - 2) (k - 2) - Nat.choose (n - 4) (k - 2) ≤
            (pairCoverage 𝓕 x y).card) →
        𝓕.card ≤ Nat.choose (n - 2) (k - 2) := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_singletonPairBlock_at_every_point k hk4
  refine ⟨max N (k + 1), ?_⟩
  intro n hn 𝓕 huniform havoid hdeg hpair
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hassign := hN n hnN 𝓕 huniform havoid hdeg hpair
  classical
  choose b hbblock hbcover using hassign
  have hblockCard : ∀ x : Fin n, (b x).card = 2 := by
    intro x
    exact singletonPairBlock_card (hbblock x)
  have hblockPair :
      ∀ x y : Fin n, b x = b y ∨ Disjoint (b x) (b y) := by
    intro x y
    exact singletonPairBlock_eq_or_disjoint huniform hk4 havoid
      (hbblock x) (hbblock y)
  have hkn : k + 1 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hend : ∀ x z : Fin n, z ∈ b x → b z = b x := by
    intro x z hz
    rcases hblockPair x z with hEq | hDisj
    · exact hEq.symm
    · exfalso
      have hTcard : (b x ∪ b z).card = 4 := by
        rw [card_union_of_disjoint hDisj, hblockCard, hblockCard]
      exact false_of_four_core_high_degree huniform hk4 hkn hTcard
        (by
          intro A hA hzA
          have hbxA :=
            singletonPairBlock_subset_of_member huniform hk4 havoid
              (hbblock x) hz A hA hzA
          have hbzA := hbcover z A hA hzA
          exact union_subset hbxA hbzA)
        (hdeg z)
  have hnpos : 0 < n := by omega
  let x₀ : Fin n := ⟨0, hnpos⟩
  exact card_le_choose_of_block_assignment (x₀ := x₀)
    huniform hk4 hblockCard hblockPair hend
      (fun A hA x hxA => hbcover x A hA hxA)

/-! ## Deletion and the final iteration -/

def relabelFamily {n : ℕ} (e : Fin n ≃ Fin n)
    (𝓕 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  e.finsetCongr.finsetCongr 𝓕

lemma card_relabelFamily {n : ℕ} (e : Fin n ≃ Fin n)
    (𝓕 : Finset (Finset (Fin n))) :
    (relabelFamily e 𝓕).card = 𝓕.card := by
  simp [relabelFamily]

lemma relabelFamily_uniform {n k : ℕ} {𝓕 : Finset (Finset (Fin n))}
    (e : Fin n ≃ Fin n) (huniform : IsUniform k 𝓕) :
    IsUniform k (relabelFamily e 𝓕) := by
  intro A hA
  rw [relabelFamily] at hA
  obtain ⟨B, hB, rfl⟩ := mem_map.mp hA
  simpa using huniform B hB

lemma relabelFamily_avoids {n : ℕ} {𝓕 : Finset (Finset (Fin n))}
    (e : Fin n ≃ Fin n) (havoid : AvoidsSingleton 𝓕) :
    AvoidsSingleton (relabelFamily e 𝓕) := by
  intro A hA B hB
  rw [relabelFamily] at hA hB
  obtain ⟨A', hA', rfl⟩ := mem_map.mp hA
  obtain ⟨B', hB', rfl⟩ := mem_map.mp hB
  have h := havoid A' hA' B' hB'
  change #(A'.map e.toEmbedding ∩ B'.map e.toEmbedding) ≠ 1
  rw [← Finset.map_inter]
  simpa using h

lemma sectionZero_uniform {m k : ℕ}
    {𝓕 : Finset (Finset (Fin (m + 1)))}
    (huniform : IsUniform k 𝓕) :
    IsUniform k (Erdos703Iteration.sectionZero 𝓕) := by
  intro A hA
  have hmem : Erdos703Iteration.liftZero A ∈ 𝓕 := by simpa using hA
  have hcard := huniform (Erdos703Iteration.liftZero A) hmem
  simpa using hcard

lemma sectionZero_avoids {m : ℕ}
    {𝓕 : Finset (Finset (Fin (m + 1)))}
    (havoid : AvoidsSingleton 𝓕) :
    AvoidsSingleton (Erdos703Iteration.sectionZero 𝓕) := by
  intro A hA B hB
  have hA' : Erdos703Iteration.liftZero A ∈ 𝓕 := by simpa using hA
  have hB' : Erdos703Iteration.liftZero B ∈ 𝓕 := by simpa using hB
  have h := havoid (Erdos703Iteration.liftZero A) hA'
    (Erdos703Iteration.liftZero B) hB'
  simpa using h

lemma card_sectionZero_relabel_eq_filter_not_mem {m : ℕ}
    (𝓕 : Finset (Finset (Fin (m + 1)))) (x : Fin (m + 1))
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (hex : e x = Fin.last m) :
    (Erdos703Iteration.sectionZero (relabelFamily e 𝓕)).card =
      (𝓕.filter fun A => x ∉ A).card := by
  rw [Erdos703Iteration.card_sectionZero]
  have hmap := Finset.map_filter
    (s := 𝓕) (f := e.finsetCongr) (p := fun A => x ∉ A)
  have hfilter :
      (relabelFamily e 𝓕).filter (fun A => Fin.last m ∉ A) =
        (relabelFamily e 𝓕).filter
          (fun A => x ∉ e.finsetCongr.symm A) := by
    ext A
    simp [Equiv.finsetCongr_apply, hex]
  rw [hfilter]
  have hEq :
      (𝓕.filter fun A => x ∉ A).map e.finsetCongr.toEmbedding =
        (relabelFamily e 𝓕).filter
          (fun A => x ∉ e.finsetCongr.symm A) := by
    simpa [relabelFamily, Function.comp_def] using hmap
  rw [← hEq]
  simp

lemma exists_point_deleted_family {n k : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n)
    (huniform : IsUniform k 𝓕) (havoid : AvoidsSingleton 𝓕) :
    ∃ 𝓖 : Finset (Finset (Fin (n - 1))),
      𝓖.card = (𝓕.filter fun A => x ∉ A).card ∧
      IsUniform k 𝓖 ∧ AvoidsSingleton 𝓖 := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ m =>
      let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap x (Fin.last m)
      let 𝓖 := Erdos703Iteration.sectionZero (relabelFamily e 𝓕)
      refine ⟨𝓖, ?_, ?_, ?_⟩
      · simpa [𝓖] using
          card_sectionZero_relabel_eq_filter_not_mem 𝓕 x e (by
            simp [e])
      · exact sectionZero_uniform (relabelFamily_uniform e huniform)
      · exact sectionZero_avoids (relabelFamily_avoids e havoid)

lemma card_sectionZero_filter_castSucc_not_mem {m : ℕ}
    (𝓕 : Finset (Finset (Fin (m + 1)))) (y : Fin m) :
    ((Erdos703Iteration.sectionZero 𝓕).filter fun A => y ∉ A).card =
      (𝓕.filter fun A => Fin.last m ∉ A ∧ y.castSucc ∉ A).card := by
  classical
  apply Finset.card_bij'
    (fun A _ => Erdos703Iteration.liftZero A)
    (fun S _ => Erdos703Iteration.dropLast S)
  · intro A hA
    simp only [mem_filter] at hA ⊢
    refine ⟨(by simpa using hA.1), ?_, ?_⟩
    · exact Erdos703Iteration.last_not_mem_liftZero A
    · simpa [Erdos703Iteration.liftZero] using hA.2
  · intro S hS
    simp only [mem_filter] at hS ⊢
    refine ⟨?_, ?_⟩
    · rw [Erdos703Iteration.mem_sectionZero,
        Erdos703Iteration.liftZero_dropLast_of_last_not_mem hS.2.1]
      exact hS.1
    · simpa [Erdos703Iteration.dropLast] using hS.2.2
  · intro A hA
    exact Erdos703Iteration.dropLast_liftZero A
  · intro S hS
    exact Erdos703Iteration.liftZero_dropLast_of_last_not_mem
      (mem_filter.mp hS).2.1

lemma card_relabel_filter_two_not_mem {m : ℕ}
    (𝓕 : Finset (Finset (Fin (m + 1)))) (x y : Fin (m + 1))
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (hex : e x = Fin.last m) :
    ((relabelFamily e 𝓕).filter
      fun A => Fin.last m ∉ A ∧ e y ∉ A).card =
      (𝓕.filter fun A => x ∉ A ∧ y ∉ A).card := by
  have hmap := Finset.map_filter
    (s := 𝓕) (f := e.finsetCongr)
    (p := fun A => x ∉ A ∧ y ∉ A)
  have hfilter :
      (relabelFamily e 𝓕).filter
          (fun A => Fin.last m ∉ A ∧ e y ∉ A) =
        (relabelFamily e 𝓕).filter
          (fun A => x ∉ e.finsetCongr.symm A ∧
            y ∉ e.finsetCongr.symm A) := by
    ext A
    simp [Equiv.finsetCongr_apply, hex]
  rw [hfilter]
  have hEq :
      (𝓕.filter fun A => x ∉ A ∧ y ∉ A).map e.finsetCongr.toEmbedding =
        (relabelFamily e 𝓕).filter
          (fun A => x ∉ e.finsetCongr.symm A ∧
            y ∉ e.finsetCongr.symm A) := by
    simpa [relabelFamily, Function.comp_def] using hmap
  rw [← hEq]
  simp

lemma exists_pair_deleted_family {n k : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x y : Fin n) (hxy : x ≠ y)
    (huniform : IsUniform k 𝓕) (havoid : AvoidsSingleton 𝓕) :
    ∃ 𝓖 : Finset (Finset (Fin (n - 2))),
      𝓖.card = (𝓕.filter fun A => x ∉ A ∧ y ∉ A).card ∧
      IsUniform k 𝓖 ∧ AvoidsSingleton 𝓖 := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ m =>
      let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap x (Fin.last m)
      have heyne : e y ≠ Fin.last m := by
        intro h
        have : e y = e x := by simpa [e] using h
        exact hxy (e.injective this).symm
      obtain ⟨y₀, hy₀⟩ := Fin.eq_castSucc_of_ne_last heyne
      let 𝓗 := Erdos703Iteration.sectionZero (relabelFamily e 𝓕)
      obtain ⟨𝓖, h𝓖card, h𝓖uniform, h𝓖avoid⟩ :=
        exists_point_deleted_family 𝓗 y₀
          (sectionZero_uniform (relabelFamily_uniform e huniform))
          (sectionZero_avoids (relabelFamily_avoids e havoid))
      refine ⟨𝓖, ?_, h𝓖uniform, h𝓖avoid⟩
      rw [h𝓖card]
      calc
        (𝓗.filter fun A => y₀ ∉ A).card =
            ((relabelFamily e 𝓕).filter fun A =>
              Fin.last m ∉ A ∧ y₀.castSucc ∉ A).card := by
                simpa [𝓗] using
                  card_sectionZero_filter_castSucc_not_mem
                    (relabelFamily e 𝓕) y₀
        _ = ((relabelFamily e 𝓕).filter fun A =>
              Fin.last m ∉ A ∧ e y ∉ A).card := by
                rw [← hy₀]
        _ = (𝓕.filter fun A => x ∉ A ∧ y ∉ A).card :=
          card_relabel_filter_two_not_mem 𝓕 x y e (by simp [e])

lemma exists_threshold_low_point_or_low_pair_of_large_family
    (k : ℕ) (hk4 : 4 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) < 𝓕.card →
        (∃ x : Fin n,
            (𝓕.filter fun A => x ∈ A).card <
              Nat.choose (n - 3) (k - 3)) ∨
          ∃ x y : Fin n, x ≠ y ∧
            (pairCoverage 𝓕 x y).card <
              Nat.choose (n - 2) (k - 2) -
                Nat.choose (n - 4) (k - 2) := by
  obtain ⟨N, hN⟩ :=
    exists_threshold_card_le_of_high_degrees_and_high_pair_coverages k hk4
  refine ⟨N, ?_⟩
  intro n hn 𝓕 huniform havoid hlarge
  by_cases hlow : ∃ x : Fin n,
      (𝓕.filter fun A => x ∈ A).card <
        Nat.choose (n - 3) (k - 3)
  · exact Or.inl hlow
  by_cases hpairlow : ∃ x y : Fin n, x ≠ y ∧
      (pairCoverage 𝓕 x y).card <
        Nat.choose (n - 2) (k - 2) - Nat.choose (n - 4) (k - 2)
  · exact Or.inr hpairlow
  exfalso
  have hdeg : ∀ x : Fin n,
      Nat.choose (n - 3) (k - 3) ≤
        (𝓕.filter fun A => x ∈ A).card := by
    intro x
    by_contra hx
    exact hlow ⟨x, by omega⟩
  have hpair : ∀ x y : Fin n, x ≠ y →
      Nat.choose (n - 2) (k - 2) - Nat.choose (n - 4) (k - 2) ≤
        (pairCoverage 𝓕 x y).card := by
    intro x y hxy
    by_contra hxyLow
    exact hpairlow ⟨x, y, hxy, by omega⟩
  have hbound := hN n hn 𝓕 huniform havoid hdeg hpair
  omega

lemma card_avoiding_point_add_degree {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x : Fin n) :
    (𝓕.filter fun A => x ∉ A).card +
        (𝓕.filter fun A => x ∈ A).card = 𝓕.card := by
  simpa [Nat.add_comm] using
    (card_filter_add_card_filter_not (s := 𝓕) (fun A => x ∈ A))

lemma card_avoiding_pair_add_coverage {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (x y : Fin n) :
    (𝓕.filter fun A => x ∉ A ∧ y ∉ A).card +
        (pairCoverage 𝓕 x y).card = 𝓕.card := by
  simpa [pairCoverage, Nat.add_comm, not_or] using
    (card_filter_add_card_filter_not (s := 𝓕)
      (fun A => x ∈ A ∨ y ∈ A))

lemma twoStarBound_point_gap {n k : ℕ}
    (hk4 : 4 ≤ k) (hkn : k + 1 ≤ n) :
    Nat.choose (n - 3) (k - 2) + Nat.choose (n - 3) (k - 3) =
      Nat.choose (n - 2) (k - 2) := by
  have hn2 : 0 < n - 2 := by omega
  have hk2 : 0 < k - 2 := by omega
  have h :=
    Nat.choose_eq_choose_pred_add (n := n - 2) (k := k - 2) hn2 hk2
  have hn3 : n - 2 - 1 = n - 3 := by omega
  have hk3 : k - 2 - 1 = k - 3 := by omega
  rw [hn3, hk3] at h
  omega

lemma twoStarBound_pair_gap {n k : ℕ} :
    Nat.choose (n - 4) (k - 2) +
        (Nat.choose (n - 2) (k - 2) -
          Nat.choose (n - 4) (k - 2)) =
      Nat.choose (n - 2) (k - 2) := by
  have hle : Nat.choose (n - 4) (k - 2) ≤
      Nat.choose (n - 2) (k - 2) :=
    Nat.choose_le_choose _ (by omega)
  omega

lemma card_uniform_le_choose {n k : ℕ}
    {𝓕 : Finset (Finset (Fin n))} (huniform : IsUniform k 𝓕) :
    𝓕.card ≤ Nat.choose n k := by
  have hsub : 𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k := by
    intro A hA
    exact mem_powersetCard.mpr ⟨by simp, huniform A hA⟩
  calc
    𝓕.card ≤ ((univ : Finset (Fin n)).powersetCard k).card :=
      card_le_card hsub
    _ = Nat.choose n k := by simp

lemma card_le_twoStar_add_constant_of_structural_deletion
    (k N : ℕ) (hk4 : 4 ≤ k) (hNk : k + 1 ≤ N)
    (hstruct : ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) < 𝓕.card →
        (∃ x : Fin n,
            (𝓕.filter fun A => x ∈ A).card <
              Nat.choose (n - 3) (k - 3)) ∨
          ∃ x y : Fin n, x ≠ y ∧
            (pairCoverage 𝓕 x y).card <
              Nat.choose (n - 2) (k - 2) -
                Nat.choose (n - 4) (k - 2)) :
    ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
      𝓕.card ≤ Nat.choose (n - 2) (k - 2) + Nat.choose N k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro 𝓕 huniform havoid
      by_cases hnN : N ≤ n
      · by_cases hsmall :
            𝓕.card ≤ Nat.choose (n - 2) (k - 2)
        · omega
        · have hlarge : Nat.choose (n - 2) (k - 2) < 𝓕.card := by omega
          have hkn : k + 1 ≤ n := hNk.trans hnN
          rcases hstruct n hnN 𝓕 huniform havoid hlarge with
            ⟨x, hxlow⟩ | ⟨x, y, hxy, hxylow⟩
          · obtain ⟨𝓖, h𝓖card, h𝓖uniform, h𝓖avoid⟩ :=
              exists_point_deleted_family 𝓕 x huniform havoid
            have hlt : n - 1 < n := by omega
            have hih := ih (n - 1) hlt 𝓖 h𝓖uniform h𝓖avoid
            have hsub : n - 1 - 2 = n - 3 := by omega
            rw [hsub] at hih
            have hpartition := card_avoiding_point_add_degree 𝓕 x
            rw [← h𝓖card] at hpartition
            have hgap := twoStarBound_point_gap hk4 hkn
            omega
          · obtain ⟨𝓖, h𝓖card, h𝓖uniform, h𝓖avoid⟩ :=
              exists_pair_deleted_family 𝓕 x y hxy huniform havoid
            have hlt : n - 2 < n := by omega
            have hih := ih (n - 2) hlt 𝓖 h𝓖uniform h𝓖avoid
            have hsub : n - 2 - 2 = n - 4 := by omega
            rw [hsub] at hih
            have hpartition := card_avoiding_pair_add_coverage 𝓕 x y
            rw [← h𝓖card] at hpartition
            have hgap := twoStarBound_pair_gap (n := n) (k := k)
            omega
      · have hnle : n ≤ N := by omega
        have hcard := card_uniform_le_choose huniform
        have hchoose : Nat.choose n k ≤ Nat.choose N k :=
          Nat.choose_le_choose _ hnle
        omega

lemma descend_excess_by_structural_deletion
    (k N q d : ℕ) (hk4 : 4 ≤ k) (hNk : k + 1 ≤ N)
    (hstruct : ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) < 𝓕.card →
        (∃ x : Fin n,
            (𝓕.filter fun A => x ∈ A).card <
              Nat.choose (n - 3) (k - 3)) ∨
          ∃ x y : Fin n, x ≠ y ∧
            (pairCoverage 𝓕 x y).card <
              Nat.choose (n - 2) (k - 2) -
                Nat.choose (n - 4) (k - 2)) :
    ∀ n : ℕ, N + 2 * q ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) + d < 𝓕.card →
        ∃ m : ℕ, ∃ 𝓖 : Finset (Finset (Fin m)),
          N ≤ m ∧ IsUniform k 𝓖 ∧ AvoidsSingleton 𝓖 ∧
          Nat.choose (m - 2) (k - 2) + (d + q) < 𝓖.card := by
  induction q generalizing d with
  | zero =>
      intro n hn 𝓕 huniform havoid hlarge
      exact ⟨n, 𝓕, by omega, huniform, havoid, by simpa using hlarge⟩
  | succ q ih =>
      intro n hn 𝓕 huniform havoid hlarge
      have hnN : N ≤ n := by omega
      have hkn : k + 1 ≤ n := hNk.trans hnN
      have hlarge0 : Nat.choose (n - 2) (k - 2) < 𝓕.card := by
        omega
      rcases hstruct n hnN 𝓕 huniform havoid hlarge0 with
        ⟨x, hxlow⟩ | ⟨x, y, hxy, hxylow⟩
      · obtain ⟨𝓗, h𝓗card, h𝓗uniform, h𝓗avoid⟩ :=
          exists_point_deleted_family 𝓕 x huniform havoid
        have hpartition := card_avoiding_point_add_degree 𝓕 x
        rw [← h𝓗card] at hpartition
        have hgap := twoStarBound_point_gap hk4 hkn
        have hHlarge :
            Nat.choose (n - 1 - 2) (k - 2) + (d + 1) < 𝓗.card := by
          have hsub : n - 1 - 2 = n - 3 := by omega
          rw [hsub]
          omega
        have hn' : N + 2 * q ≤ n - 1 := by omega
        obtain ⟨m, 𝓖, hmN, h𝓖uniform, h𝓖avoid, h𝓖large⟩ :=
          ih (d + 1) (n - 1) hn' 𝓗 h𝓗uniform h𝓗avoid hHlarge
        refine ⟨m, 𝓖, hmN, h𝓖uniform, h𝓖avoid, ?_⟩
        have hsum : d + 1 + q = d + (q + 1) := by omega
        simpa [hsum] using h𝓖large
      · obtain ⟨𝓗, h𝓗card, h𝓗uniform, h𝓗avoid⟩ :=
          exists_pair_deleted_family 𝓕 x y hxy huniform havoid
        have hpartition := card_avoiding_pair_add_coverage 𝓕 x y
        rw [← h𝓗card] at hpartition
        have hgap := twoStarBound_pair_gap (n := n) (k := k)
        have hHlarge :
            Nat.choose (n - 2 - 2) (k - 2) + (d + 1) < 𝓗.card := by
          have hsub : n - 2 - 2 = n - 4 := by omega
          rw [hsub]
          omega
        have hn' : N + 2 * q ≤ n - 2 := by omega
        obtain ⟨m, 𝓖, hmN, h𝓖uniform, h𝓖avoid, h𝓖large⟩ :=
          ih (d + 1) (n - 2) hn' 𝓗 h𝓗uniform h𝓗avoid hHlarge
        refine ⟨m, 𝓖, hmN, h𝓖uniform, h𝓖avoid, ?_⟩
        have hsum : d + 1 + q = d + (q + 1) := by omega
        simpa [hsum] using h𝓖large

/-- **Main result.**  Frankl's resolution of Erdős Problem 702 in its
source-correct eventual form. -/
theorem erdos_702_eventually : (∀ k : ℕ, 4 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
  ∀ 𝓕 : Finset (Finset (Fin n)),
    Erdos702.IsUniform k 𝓕 →
    Erdos702.twoStarBound n k < 𝓕.card →
    Erdos702.HasSingletonIntersection 𝓕) := by
  intro k hk4
  obtain ⟨N₀, hN₀⟩ :=
    exists_threshold_low_point_or_low_pair_of_large_family k hk4
  let N := max N₀ (k + 1)
  have hNk : k + 1 ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  have hstruct : ∀ n : ℕ, N ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        IsUniform k 𝓕 → AvoidsSingleton 𝓕 →
        Nat.choose (n - 2) (k - 2) < 𝓕.card →
        (∃ x : Fin n,
            (𝓕.filter fun A => x ∈ A).card <
              Nat.choose (n - 3) (k - 3)) ∨
          ∃ x y : Fin n, x ≠ y ∧
            (pairCoverage 𝓕 x y).card <
              Nat.choose (n - 2) (k - 2) -
                Nat.choose (n - 4) (k - 2) := by
    intro n hn 𝓕 huniform havoid hlarge
    apply hN₀ n
    · exact (le_max_left _ _).trans hn
    · exact huniform
    · exact havoid
    · exact hlarge
  let C := Nat.choose N k
  refine ⟨N + 2 * (C + 1), ?_⟩
  intro n hn 𝓕 huniform hlarge
  by_contra hnone
  have havoid : AvoidsSingleton 𝓕 :=
    (avoidsSingleton_iff_not_hasSingletonIntersection 𝓕).mpr hnone
  obtain ⟨m, 𝓖, hmN, h𝓖uniform, h𝓖avoid, h𝓖large⟩ :=
    descend_excess_by_structural_deletion k N (C + 1) 0 hk4 hNk
      hstruct n (by simpa [Nat.add_assoc] using hn) 𝓕 huniform havoid
      (by simpa [twoStarBound] using hlarge)
  have hbound :=
    card_le_twoStar_add_constant_of_structural_deletion
      k N hk4 hNk hstruct m 𝓖 h𝓖uniform h𝓖avoid
  dsimp [C] at h𝓖large hbound
  omega

end Erdos702

alias _root_.Erdos702.erdos_702_all_n_false := _root_.Erdos702.not_erdos_702
