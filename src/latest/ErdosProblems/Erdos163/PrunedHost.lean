/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.PreparedHost

/-!
# Deleting high-influence host vertices

For each target direction we mark vertices incident with too much old defect
weight.  Deleting the union of all marked sets gives bounded differences
simultaneously in every direction.  A separate common-neighbour lower bound
shows that this deletion loses less than half of every relevant common
neighbourhood.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace PrunedHost

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Simultaneous pruning in every tuple dimension -/

def badForLevel {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    (k : Fin (D + 1)) (j : Fin r) : Finset (Fin N) :=
  Pruning.badVertices (G := G) (ι := Fin k.1) θ s
    (HostDirections.unionExcept A j) (A j) (Λ k.1)

def allBadLevels {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) : Finset (Fin N) :=
  Finset.univ.biUnion fun k : Fin (D + 1) =>
    Finset.univ.biUnion fun j : Fin r =>
      badForLevel (D := D) (θ := θ) (s := s) G A Λ k j

def prunedLevels {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    (j : Fin r) : Finset (Fin N) :=
  A j \ allBadLevels (D := D) (θ := θ) (s := s) G A Λ

theorem prunedLevels_subset {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r) :
    prunedLevels (D := D) (θ := θ) (s := s) G A Λ j ⊆ A j :=
  Finset.sdiff_subset

theorem allBadLevels_card_le_sum
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) :
    (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤
      ∑ k : Fin (D + 1), ∑ j : Fin r,
        (badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card := by
  unfold allBadLevels
  exact (Finset.card_biUnion_le.trans <|
    Finset.sum_le_sum fun k _ => Finset.card_biUnion_le)

theorem allBadLevels_card_le_of_each
    {N r D θ s R₀ : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    (hbad : ∀ k : Fin (D + 1), ∀ j : Fin r,
      (badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card ≤ R₀) :
    (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤
      (D + 1) * r * R₀ := by
  calc
    (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤
        ∑ k : Fin (D + 1), ∑ j : Fin r,
          (badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card :=
      allBadLevels_card_le_sum G A Λ
    _ ≤ ∑ _k : Fin (D + 1), ∑ _j : Fin r, R₀ := by
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hbad k j
    _ = (D + 1) * r * R₀ := by simp [Nat.mul_assoc]

/-- A single numerical cutoff inequality at each tuple dimension bounds the
whole deleted set. -/
theorem allBadLevels_card_le
    {N r D θ s R₀ : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    (hU : ∀ j, (HostDirections.unionExcept A j).Nonempty)
    (hε : 0 ≤ ε) (hΛ : ∀ k, k ≤ D → 0 ≤ Λ k)
    (hmoment : ∀ j, FiniteDefect.moment G θ s
      (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε)
    (hcut : ∀ k, k ≤ D →
      (k : ℝ) * ((N : ℝ) ^ k * ε) < ((R₀ + 1 : ℕ) : ℝ) * Λ k) :
    (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤
      (D + 1) * r * R₀ := by
  apply allBadLevels_card_le_of_each G A Λ
  intro k j
  have hraw := PreparedHost.raw_const_le_card_pow_mul
    (ι := Fin k.1) G (HostDirections.unionExcept A j) (A j) (hU j)
      (by rw [Fintype.card_fin]; omega) hε (hmoment j)
  have hb := Pruning.badVertices_mul_le
    (G := G) (ι := Fin k.1) θ s (HostDirections.unionExcept A j) (A j)
      (Λ k.1) (hΛ k.1 (by omega))
  change ((badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card : ℝ) *
      Λ k.1 ≤ _ at hb
  have hbound : ((badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card : ℝ) *
      Λ k.1 ≤ (k.1 : ℝ) * ((N : ℝ) ^ k.1 * ε) := by
    exact hb.trans (by
      simpa using mul_le_mul_of_nonneg_left hraw (by positivity : (0 : ℝ) ≤ k.1))
  by_contra hnot
  have hsucc : R₀ + 1 ≤
      (badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card := by omega
  have hsuccR : (((R₀ + 1 : ℕ) : ℝ)) ≤
      ((badForLevel (D := D) (θ := θ) (s := s) G A Λ k j).card : ℝ) := by
    exact_mod_cast hsucc
  have hmul := mul_le_mul_of_nonneg_right hsuccR (hΛ k.1 (by omega))
  exact (not_lt_of_ge (hmul.trans hbound)) (hcut k.1 (by omega))

theorem prunedLevels_card_add_bad_ge
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r) :
    (A j).card ≤
      (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j).card +
        (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card := by
  exact Finset.card_le_card_sdiff_add_card

theorem incidentWeight_lt_of_mem_prunedLevels
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hdim : Fintype.card ι ≤ D) (j k : Fin r) {v : Fin N}
    (hv : v ∈ prunedLevels (D := D) (θ := θ) (s := s) G A Λ k) :
    Pruning.incidentWeight (G := G) (ι := ι) θ s
        (HostDirections.unionExcept A j) (A j) v < Λ (Fintype.card ι) := by
  let m : Fin (D + 1) := ⟨Fintype.card ι, by omega⟩
  have hnot : v ∉ badForLevel (D := D) (θ := θ) (s := s) G A Λ m j := by
    intro hvbad
    apply (Finset.mem_sdiff.mp hv).2
    simpa only [allBadLevels] using
      (Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ m,
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hvbad⟩⟩)
  simp only [badForLevel, Pruning.badVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, not_le] at hnot
  rw [Pruning.incidentWeight_eq_fin_card]
  exact hnot

theorem commonNeighbors_prunedLevels_eq_sdiff
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N) :
    FiniteDefect.commonNeighbors G g
        (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j) =
      FiniteDefect.commonNeighbors G g (A j) \
        allBadLevels (D := D) (θ := θ) (s := s) G A Λ := by
  ext v
  simp [FiniteDefect.commonNeighbors, Defect.commonNeighbors, prunedLevels,
    and_assoc, and_left_comm, and_comm]

theorem half_commonNeighbors_lt_prunedLevels
    {N r D θ s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hbad : (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    ((FiniteDefect.commonNeighbors G g (A j)).card : ℝ) / 2 <
      ((FiniteDefect.commonNeighbors G g
        (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j)).card : ℝ) := by
  let C := FiniteDefect.commonNeighbors G g (A j)
  let Z := allBadLevels (D := D) (θ := θ) (s := s) G A Λ
  have hlower : C.card - Z.card ≤ (C \ Z).card := Finset.le_card_sdiff Z C
  have hbad' : Z.card ≤ R := hbad
  have hlarge' : 2 * R < C.card := hlarge
  have htwice : C.card < 2 * (C \ Z).card := by omega
  rw [commonNeighbors_prunedLevels_eq_sdiff]
  have htwiceR : (C.card : ℝ) < 2 * ((C \ Z).card : ℝ) := by
    exact_mod_cast htwice
  nlinarith

theorem commonNeighbors_prunedLevels_pos
    {N r D θ s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hbad : (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    0 < (FiniteDefect.commonNeighbors G g
      (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j)).card := by
  have hhalf := half_commonNeighbors_lt_prunedLevels G A Λ j g hbad hlarge
  exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤
    ((FiniteDefect.commonNeighbors G g (A j)).card : ℝ) / 2) hhalf)

theorem defectPower_prunedLevels_le
    {N r D θ θ' s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hθ : (θ' : ℝ) ≤ (θ : ℝ) / 2)
    (hbad : (allBadLevels (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    FiniteDefect.defectPower G θ' g
        (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j) s ≤
      FiniteDefect.defectPower G θ g (A j) s := by
  exact HostPartition.defectPower_restrict_le_of_proportional G g
    (A j) (prunedLevels (D := D) (θ := θ) (s := s) G A Λ j) 1
    (by norm_num) (by omega) (by simpa using hθ)
    (by simpa using half_commonNeighbors_lt_prunedLevels G A Λ j g hbad hlarge)

def badFor {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r) : Finset (Fin N) :=
  Pruning.badVertices (G := G) (ι := Fin D) θ s
    (HostDirections.unionExcept A j) (A j) Λ

def allBad {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) : Finset (Fin N) :=
  Finset.univ.biUnion fun j => badFor (D := D) (θ := θ) (s := s) G A Λ j

def pruned {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r) : Finset (Fin N) :=
  A j \ allBad (D := D) (θ := θ) (s := s) G A Λ

theorem pruned_subset {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r) :
    pruned (D := D) (θ := θ) (s := s) G A Λ j ⊆ A j :=
  Finset.sdiff_subset

theorem not_mem_badFor_of_mem_pruned
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j k : Fin r) {v : Fin N}
    (hv : v ∈ pruned (D := D) (θ := θ) (s := s) G A Λ k) :
    v ∉ badFor (D := D) (θ := θ) (s := s) G A Λ j := by
  intro hvbad
  exact (Finset.mem_sdiff.mp hv).2 <|
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hvbad⟩

theorem incidentWeight_lt_of_mem_pruned
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j k : Fin r) {v : Fin N}
    (hv : v ∈ pruned (D := D) (θ := θ) (s := s) G A Λ k) :
    Pruning.incidentWeight (G := G) (ι := Fin D) θ s
        (HostDirections.unionExcept A j) (A j) v < Λ := by
  have hnot := not_mem_badFor_of_mem_pruned
    (D := D) (θ := θ) (s := s) G A Λ j k hv
  simp only [badFor, Pruning.badVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, not_le] at hnot
  exact hnot

theorem pruned_card_add_allBad_card_ge
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r) :
    (A j).card ≤
      (pruned (D := D) (θ := θ) (s := s) G A Λ j).card +
        (allBad (D := D) (θ := θ) (s := s) G A Λ).card := by
  exact Finset.card_le_card_sdiff_add_card

/-- The total number of deleted vertices is controlled by the sum of the
all-direction raw moments. -/
theorem allBad_card_mul_le
    {N r D θ s : ℕ} {ε Λ : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N))
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε)
    (hU : ∀ j, (HostDirections.unionExcept A j).Nonempty)
    (hmoment : ∀ j, FiniteDefect.moment G θ s
      (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε) :
    ((allBad (D := D) (θ := θ) (s := s) G A Λ).card : ℝ) * Λ ≤
      (r : ℝ) * ((D : ℝ) * ((N : ℝ) ^ D * ε)) := by
  have hcardNat : (allBad (D := D) (θ := θ) (s := s) G A Λ).card ≤
      ∑ j : Fin r, (badFor (D := D) (θ := θ) (s := s) G A Λ j).card := by
    unfold allBad
    exact Finset.card_biUnion_le
  have hcardReal : ((allBad (D := D) (θ := θ) (s := s) G A Λ).card : ℝ) ≤
      ∑ j : Fin r,
        ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ) := by
    exact_mod_cast hcardNat
  have hbad : ∀ j : Fin r,
      ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ) * Λ ≤
        (D : ℝ) * ((N : ℝ) ^ D * ε) := by
    intro j
    have hb := Pruning.badVertices_mul_le (G := G) (ι := Fin D) θ s
      (HostDirections.unionExcept A j) (A j) Λ hΛ
    change ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ) * Λ ≤ _ at hb
    calc
      ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ) * Λ ≤
          (D : ℝ) * HostTools.rawFamilyMoment G θ s
            (fun _ : Fin D => HostDirections.unionExcept A j) (A j) := by
        simpa using hb
      _ ≤ (D : ℝ) * ((N : ℝ) ^ D * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using PreparedHost.raw_const_le_card_pow_mul (ι := Fin D) G
          (HostDirections.unionExcept A j) (A j) (hU j) (by simp) hε (hmoment j)
  calc
    ((allBad (D := D) (θ := θ) (s := s) G A Λ).card : ℝ) * Λ ≤
        (∑ j : Fin r,
          ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ)) * Λ :=
      mul_le_mul_of_nonneg_right hcardReal hΛ
    _ = ∑ j : Fin r,
        ((badFor (D := D) (θ := θ) (s := s) G A Λ j).card : ℝ) * Λ := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _j : Fin r, (D : ℝ) * ((N : ℝ) ^ D * ε) :=
      Finset.sum_le_sum fun j hj => hbad j
    _ = (r : ℝ) * ((D : ℝ) * ((N : ℝ) ^ D * ε)) := by simp

theorem commonNeighbors_pruned_eq_sdiff
    {N r D θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N) :
    FiniteDefect.commonNeighbors G g
        (pruned (D := D) (θ := θ) (s := s) G A Λ j) =
      FiniteDefect.commonNeighbors G g (A j) \
        allBad (D := D) (θ := θ) (s := s) G A Λ := by
  ext v
  simp [FiniteDefect.commonNeighbors, Defect.commonNeighbors, pruned,
    and_assoc, and_left_comm, and_comm]

/-- If the deleted set has size at most `R` and the old common
neighbourhood has more than `2R` vertices, more than half survives. -/
theorem half_commonNeighbors_lt_pruned
    {N r D θ s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hbad : (allBad (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    ((FiniteDefect.commonNeighbors G g (A j)).card : ℝ) / 2 <
      ((FiniteDefect.commonNeighbors G g
        (pruned (D := D) (θ := θ) (s := s) G A Λ j)).card : ℝ) := by
  let C := FiniteDefect.commonNeighbors G g (A j)
  let Z := allBad (D := D) (θ := θ) (s := s) G A Λ
  have hlower : C.card - Z.card ≤ (C \ Z).card := Finset.le_card_sdiff Z C
  have hbad' : Z.card ≤ R := hbad
  have hlarge' : 2 * R < C.card := hlarge
  have htwice : C.card < 2 * (C \ Z).card := by omega
  rw [commonNeighbors_pruned_eq_sdiff]
  have htwiceR : (C.card : ℝ) < 2 * ((C \ Z).card : ℝ) := by
    exact_mod_cast htwice
  nlinarith

theorem commonNeighbors_pruned_pos
    {N r D θ s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hbad : (allBad (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    0 < (FiniteDefect.commonNeighbors G g
      (pruned (D := D) (θ := θ) (s := s) G A Λ j)).card := by
  have hhalf := half_commonNeighbors_lt_pruned G A Λ j g hbad hlarge
  exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤
    ((FiniteDefect.commonNeighbors G g (A j)).card : ℝ) / 2) hhalf)

/-- Halving both the threshold and every relevant common neighbourhood
makes the pruned defect no larger than the old defect. -/
theorem defectPower_pruned_le
    {N r D θ θ' s R : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : Fin r → Finset (Fin N)) (Λ : ℝ) (j : Fin r)
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (hθ : (θ' : ℝ) ≤ (θ : ℝ) / 2)
    (hbad : (allBad (D := D) (θ := θ) (s := s) G A Λ).card ≤ R)
    (hlarge : 2 * R < (FiniteDefect.commonNeighbors G g (A j)).card) :
    FiniteDefect.defectPower G θ' g
        (pruned (D := D) (θ := θ) (s := s) G A Λ j) s ≤
      FiniteDefect.defectPower G θ g (A j) s := by
  exact HostPartition.defectPower_restrict_le_of_proportional G g
    (A j) (pruned (D := D) (θ := θ) (s := s) G A Λ j) 1
    (by norm_num) (by omega) (by simpa using hθ)
    (by simpa using half_commonNeighbors_lt_pruned G A Λ j g hbad hlarge)

end
end PrunedHost
end Erdos163
