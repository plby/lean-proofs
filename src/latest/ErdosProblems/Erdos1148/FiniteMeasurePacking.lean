import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Maximal finite disjoint packings controlled by measure -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Set Function

theorem exists_maximal_finite_disjoint_packing {X Y : Type*}
    (K : Set X) (B : X → Set Y) (hneB : ∀ x ∈ K, (B x).Nonempty) (N : ℕ)
    (hbound : ∀ F : Finset X, (↑F : Set X) ⊆ K →
      (↑F : Set X).Pairwise (Disjoint on B) → F.card ≤ N) :
    ∃ F : Finset X, (↑F : Set X) ⊆ K ∧ (↑F : Set X).Pairwise (Disjoint on B) ∧
      ∀ x ∈ K, ∃ y ∈ F, ¬ Disjoint (B x) (B y) := by
  classical
  let P : Set (Finset X) := {F | (↑F : Set X) ⊆ K ∧ (↑F : Set X).Pairwise (Disjoint on B)}
  have hfinite : (Finset.card '' P).Finite := by
    apply (Finset.finite_toSet (Finset.range (N + 1))).subset
    rintro n ⟨F, hF, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound F hF.1 hF.2))
  have hne : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨F, hF, hmax⟩ := Set.Finite.exists_maximalFor' Finset.card P hfinite hne
  refine ⟨F, hF.1, hF.2, ?_⟩
  intro x hx
  by_contra hnot
  have hd : ∀ y ∈ F, Disjoint (B x) (B y) := by
    simpa only [not_exists, not_and, not_not] using hnot
  have hxF : x ∉ F := by
    intro hxF
    exact (hneB x hx).ne_empty (disjoint_self.mp (hd x hxF))
  have hIns : insert x F ∈ P := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hF.1 hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | haF
      · subst a
        exact hd b ((Finset.mem_insert.mp hb).resolve_left (Ne.symm hab))
      · rcases Finset.mem_insert.mp hb with hbx | hbF
        · subst b
          exact (hd a haF).symm
        · exact hF.2 haF hbF hab
  have hcard := hmax hIns (Finset.card_le_card (Finset.subset_insert x F))
  rw [Finset.card_insert_of_notMem hxF] at hcard
  omega

theorem finite_disjoint_packing_mass_bound {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (K : Set X) (B : X → Set Y) (E : Set Y) (c : ℝ)
    (hmeas : ∀ x ∈ K, MeasurableSet (B x)) (hlower : ∀ x ∈ K, c ≤ μ.real (B x))
    (hcontain : ∀ x ∈ K, B x ⊆ E) (F : Finset X) (hF : (↑F : Set X) ⊆ K)
    (hdisj : (↑F : Set X).Pairwise (Disjoint on B)) : (F.card : ℝ) * c ≤ μ.real E := by
  classical
  have hd : Pairwise (Disjoint on fun x : F => B x) := by
    intro x y hxy
    exact hdisj x.property y.property (fun h => hxy (Subtype.ext h))
  have hsub : (⋃ x : F, B x) ⊆ E := Set.iUnion_subset fun x => hcontain x (hF x.property)
  calc
    (F.card : ℝ) * c = ∑ _x : F, c := by simp
    _ ≤ ∑ x : F, μ.real (B x) := Finset.sum_le_sum fun x _ => hlower x (hF x.property)
    _ = μ.real (⋃ x : F, B x) :=
      (measureReal_iUnion_fintype hd (fun x => hmeas x (hF x.property))).symm
    _ ≤ μ.real E := measureReal_mono hsub

theorem exists_finite_measure_packing {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (K : Set X) (B : X → Set Y) (E : Set Y)
    {c : ℝ} (hc : 0 < c) (hmeas : ∀ x ∈ K, MeasurableSet (B x))
    (hlower : ∀ x ∈ K, c ≤ μ.real (B x)) (hcontain : ∀ x ∈ K, B x ⊆ E) :
    ∃ F : Finset X, (↑F : Set X) ⊆ K ∧ (↑F : Set X).Pairwise (Disjoint on B) ∧
      (F.card : ℝ) * c ≤ μ.real E ∧ ∀ x ∈ K, ∃ y ∈ F, ¬ Disjoint (B x) (B y) := by
  have hneB : ∀ x ∈ K, (B x).Nonempty := by
    intro x hx
    by_contra hne
    have hp := hc.trans_le (hlower x hx)
    simp only [Set.not_nonempty_iff_eq_empty.mp hne, measureReal_empty, lt_self_iff_false] at hp
  have hbound : ∀ F : Finset X, (↑F : Set X) ⊆ K →
      (↑F : Set X).Pairwise (Disjoint on B) → F.card ≤ ⌈μ.real E / c⌉₊ := by
    intro F hF hd
    have h := finite_disjoint_packing_mass_bound μ K B E c hmeas hlower hcontain F hF hd
    have hreal : (F.card : ℝ) ≤ (⌈μ.real E / c⌉₊ : ℝ) :=
      ((le_div_iff₀ hc).mpr h).trans (Nat.le_ceil _)
    exact_mod_cast hreal
  obtain ⟨F, hF, hd, hcover⟩ := exists_maximal_finite_disjoint_packing K B hneB _ hbound
  exact ⟨F, hF, hd, finite_disjoint_packing_mass_bound μ K B E c hmeas hlower hcontain F hF hd,
    hcover⟩

end Erdos1148.DukeArithmetic
