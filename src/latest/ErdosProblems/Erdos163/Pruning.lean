/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostPartition

/-!
# Weighted tuple pruning and diagonal estimates

These are the deterministic counting components of Lee's pruning lemma.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace Pruning

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def tupleUses {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → V) (v : V) : Prop := v ∈ Finset.univ.image g

def incidentWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) (v : V) : ℝ :=
  ∑ g ∈ (FiniteDefect.familyTuples (fun _ : ι => U)).filter
      (fun g => tupleUses g v),
    FiniteDefect.defectPower G θ g T s

theorem incidentWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) (v : V) :
    0 ≤ incidentWeight (G := G) ( ι := ι) θ s U T v := by
  unfold incidentWeight
  exact Finset.sum_nonneg fun g _ => FiniteDefect.defectPower_nonneg G θ g T s

/-- Summing incidences counts one tuple at most once for every coordinate. -/
theorem sum_incidentWeight_le_card_mul_raw
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) :
    ∑ v : V, incidentWeight (G := G) (ι := ι) θ s U T v ≤
      (Fintype.card ι : ℝ) * HostTools.rawFamilyMoment G θ s
        (fun _ : ι => U) T := by
  unfold incidentWeight HostTools.rawFamilyMoment
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g hg
  have hsumform : (∑ v : V,
      if tupleUses g v then FiniteDefect.defectPower G θ g T s else 0) =
      ∑ v : V, (if tupleUses g v then (1 : ℝ) else 0) *
        FiniteDefect.defectPower G θ g T s := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases huse : tupleUses g v <;> simp [huse]
  rw [hsumform]
  have hcount : (∑ v : V, if tupleUses g v then (1 : ℝ) else 0) ≤
      Fintype.card ι := by
    have hcard : (Finset.univ.image g).card ≤ Fintype.card ι := by
      simpa using (Finset.card_image_le :
        (Finset.univ.image g).card ≤ (Finset.univ : Finset ι).card)
    have heq : (∑ v : V, if tupleUses g v then (1 : ℝ) else 0) =
        ((Finset.univ.image g).card : ℝ) := by
      have hn : (∑ v : V, if tupleUses g v then 1 else 0 : ℕ) =
          (Finset.univ.image g).card := by
        simp [tupleUses]
      exact_mod_cast hn
    rw [heq]
    exact_mod_cast hcard
  calc
    ∑ v : V, (if tupleUses g v then 1 else 0) *
        FiniteDefect.defectPower G θ g T s =
      (∑ v : V, if tupleUses g v then (1 : ℝ) else 0) *
        FiniteDefect.defectPower G θ g T s := by rw [Finset.sum_mul]
    _ ≤ (Fintype.card ι : ℝ) *
        FiniteDefect.defectPower G θ g T s :=
      mul_le_mul_of_nonneg_right hcount
        (FiniteDefect.defectPower_nonneg G θ g T s)

def badVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) (B : ℝ) : Finset V :=
  Finset.univ.filter fun v => B ≤ incidentWeight (G := G) (ι := ι) θ s U T v

theorem badVertices_mul_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) (B : ℝ) (hB : 0 ≤ B) :
    ((badVertices (G := G) (ι := ι) θ s U T B).card : ℝ) * B ≤
      (Fintype.card ι : ℝ) * HostTools.rawFamilyMoment G θ s
        (fun _ : ι => U) T := by
  calc
    ((badVertices (G := G) (ι := ι) θ s U T B).card : ℝ) * B =
        ∑ _v ∈ badVertices (G := G) (ι := ι) θ s U T B, B := by simp
    _ ≤ ∑ v ∈ badVertices (G := G) (ι := ι) θ s U T B,
        incidentWeight (G := G) (ι := ι) θ s U T v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : V, incidentWeight (G := G) (ι := ι) θ s U T v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hv hnot
      exact incidentWeight_nonneg G θ s U T v
    _ ≤ _ := sum_incidentWeight_le_card_mul_raw G θ s U T

/-- Incident weights depend only on the cardinality of the coordinate type. -/
theorem incidentWeight_eq_fin_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (U T : Finset V) (v : V) :
    incidentWeight (G := G) (ι := ι) θ s U T v =
      incidentWeight (G := G) (ι := Fin (Fintype.card ι)) θ s U T v := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (ι → V) ≃ (Fin (Fintype.card ι) → V) :=
    { toFun := fun g i => g (e i)
      invFun := fun h i => h (e.symm i)
      left_inv := by intro g; funext i; simp
      right_inv := by intro h; funext i; simp }
  unfold incidentWeight
  apply Finset.sum_bij (fun g hg => E g)
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨?_, ?_⟩
    · rw [FiniteDefect.mem_familyTuples] at hg ⊢
      intro i
      exact hg.1 (e i)
    · simp only [tupleUses, Finset.mem_image, Finset.mem_univ, true_and] at hg ⊢
      obtain ⟨i, hi⟩ := hg.2
      exact ⟨e.symm i, by simpa [E] using hi⟩
  · intro a ha b hb hab
    exact E.injective hab
  · intro h hh
    refine ⟨E.symm h, ?_, E.apply_symm_apply h⟩
    rw [Finset.mem_filter] at hh ⊢
    refine ⟨?_, ?_⟩
    · rw [FiniteDefect.mem_familyTuples] at hh ⊢
      intro i
      simpa [E] using hh.1 (e.symm i)
    · simp only [tupleUses, Finset.mem_image, Finset.mem_univ, true_and] at hh ⊢
      obtain ⟨k, hk⟩ := hh.2
      exact ⟨e k, by simpa [E] using hk⟩
  · intro g hg
    have hc : FiniteDefect.commonNeighbors G g T =
        FiniteDefect.commonNeighbors G (E g) T := by
      ext z
      simp only [FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
      constructor
      · rintro ⟨hz, hall⟩
        exact ⟨hz, fun i => hall (e i)⟩
      · rintro ⟨hz, hall⟩
        exact ⟨hz, fun i => by simpa [E] using hall (e.symm i)⟩
    unfold FiniteDefect.defectPower FiniteDefect.defect
    simp only [hc]

/-! ## Diagonal deletion -/

abbrev eraseCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι) :=
  {i : ι // i ≠ b}

def restrictCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι)
    (g : ι → V) : eraseCoord b → V := fun i => g i.1

@[simp] theorem restrictCoord_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι)
    (g : ι → V) (i : eraseCoord b) : restrictCoord b g i = g i.1 := rfl

theorem restrictCoord_injective_on_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) :
    Set.InjOn (restrictCoord (V := V) b)
      {g : ι → V | g a = g b} := by
  intro g hg h hh heq
  funext i
  by_cases hib : i = b
  · subst i
    rw [← hg, ← hh]
    simpa using congrFun heq ⟨a, hab⟩
  · simpa using congrFun heq ⟨i, hib⟩

theorem commonNeighbors_restrictCoord_of_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (g : ι → V) (hgab : g a = g b)
    (T : Finset V) :
    FiniteDefect.commonNeighbors G g T =
      FiniteDefect.commonNeighbors G (restrictCoord b g) T := by
  ext v
  simp only [FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
  constructor
  · rintro ⟨hv, hall⟩
    exact ⟨hv, fun i => hall i⟩
  · rintro ⟨hv, hall⟩
    refine ⟨hv, fun i => ?_⟩
    by_cases hib : i = b
    · subst i
      rw [← hgab]
      exact hall ⟨a, hab⟩
    · exact hall ⟨i, hib⟩

theorem defectPower_restrictCoord_of_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (g : ι → V) (hgab : g a = g b)
    (θ s : ℕ) (T : Finset V) :
    FiniteDefect.defectPower G θ g T s =
      FiniteDefect.defectPower G θ (restrictCoord b g) T s := by
  have hc := commonNeighbors_restrictCoord_of_eq G hab g hgab T
  unfold FiniteDefect.defectPower FiniteDefect.defect
  simp only [hc]

/-- The raw weight of tuples with one specified repeated pair is controlled
by the moment in one fewer dimension. -/
theorem diagonalRaw_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (θ s : ℕ) (U T : Finset V) :
    ∑ g ∈ (FiniteDefect.familyTuples (fun _ : ι => U)).filter
        (fun g => g a = g b),
        FiniteDefect.defectPower G θ g T s ≤
      HostTools.rawFamilyMoment G θ s (fun _ : eraseCoord b => U) T := by
  let S := (FiniteDefect.familyTuples (fun _ : ι => U)).filter
    (fun g => g a = g b)
  let R := FiniteDefect.familyTuples (fun _ : eraseCoord b => U)
  let f : (ι → V) → (eraseCoord b → V) := restrictCoord b
  have hfmem : ∀ g ∈ S, f g ∈ R := by
    intro g hg
    dsimp [R, f]
    rw [FiniteDefect.mem_familyTuples]
    intro i
    have htuple := (Finset.mem_filter.mp hg).1
    rw [FiniteDefect.mem_familyTuples] at htuple
    exact htuple i
  have hfinj : (S : Set (ι → V)).InjOn f := by
    intro g hg h hh heq
    exact restrictCoord_injective_on_diagonal hab
      (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hh).2 heq
  calc
    ∑ g ∈ (FiniteDefect.familyTuples (fun _ : ι => U)).filter
          (fun g => g a = g b), FiniteDefect.defectPower G θ g T s =
        ∑ z ∈ S.image f, FiniteDefect.defectPower G θ z T s := by
      rw [Finset.sum_image hfinj]
      apply Finset.sum_congr rfl
      intro g hg
      exact defectPower_restrictCoord_of_eq G hab g
        (Finset.mem_filter.mp hg).2 θ s T
    _ ≤ ∑ z ∈ R, FiniteDefect.defectPower G θ z T s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨g, hg, rfl⟩ := hz
        exact hfmem g hg
      · intro z hz hnot
        exact FiniteDefect.defectPower_nonneg G θ z T s
    _ = HostTools.rawFamilyMoment G θ s (fun _ : eraseCoord b => U) T := rfl

end
end Pruning
end Erdos163
