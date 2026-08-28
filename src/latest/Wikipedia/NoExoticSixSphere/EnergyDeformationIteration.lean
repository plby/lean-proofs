import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Iterating a uniformly energy-decreasing homotopy

If a continuous step never increases energy and decreases it by a uniform
positive amount above a threshold, finitely many steps move every point of a
bounded-energy space below that threshold. Iterating the whole parameterized
family preserves continuity and its fixed set.
-/

open Set unitInterval

namespace NoExoticSixSphere.EnergyDeformationIteration

variable {X : Type*} [TopologicalSpace X]

def iterateFamily (H : C(I × X, X)) (N : ℕ) : C(I × X, X) where
  toFun p := (fun x ↦ H (p.1, x))^[N] p.2
  continuous_toFun := by
    induction N with
    | zero => exact continuous_snd
    | succ N ih =>
      simpa only [Function.iterate_succ_apply', Function.comp_def] using
        H.continuous.comp (continuous_fst.prodMk ih)

theorem iterateFamily_zero (H : C(I × X, X)) (p : I × X) : iterateFamily H 0 p = p.2 := rfl

theorem iterateFamily_succ (H : C(I × X, X)) (N : ℕ) (p : I × X) :
    iterateFamily H (N + 1) p = H (p.1, iterateFamily H N p) :=
  Function.iterate_succ_apply' _ _ _

theorem iterateFamily_at_zero (H : C(I × X, X)) (hzero : ∀ x, H (0, x) = x)
    (N : ℕ) (x : X) : iterateFamily H N (0, x) = x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iterateFamily_succ, ih, hzero]

theorem iterateFamily_fixed (H : C(I × X, X)) (S : Set X)
    (hfixed : ∀ s x, x ∈ S → H (s, x) = x) (N : ℕ) (s : I) {x : X} (hx : x ∈ S) :
    iterateFamily H N (s, x) = x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iterateFamily_succ, ih, hfixed s x hx]

theorem iterateFamily_energy_le (H : C(I × X, X)) (f : X → ℝ)
    (hle : ∀ s x, f (H (s, x)) ≤ f x) (N : ℕ) (s : I) (x : X) :
    f (iterateFamily H N (s, x)) ≤ f x := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    rw [iterateFamily_succ]
    exact (hle s _).trans ih

omit [TopologicalSpace X] in
theorem iterate_energy_dichotomy (g : X → X) (f : X → ℝ) (k δ : ℝ)
    (hle : ∀ x, f (g x) ≤ f x)
    (hdrop : ∀ x, k ≤ f x → f (g x) ≤ f x - δ) (N : ℕ) (x : X) :
    f (g^[N] x) ≤ k ∨ f (g^[N] x) ≤ f x - (N : ℝ) * δ := by
  induction N with
  | zero => exact Or.inr (by simp)
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    by_cases hk : f (g^[N] x) ≤ k
    · exact Or.inl ((hle _).trans hk)
    · have hprev := ih.resolve_left hk
      have hd := hdrop (g^[N] x) (lt_of_not_ge hk).le
      right
      rw [Nat.cast_add, Nat.cast_one]
      linarith

def endpoint (H : C(I × X, X)) (N : ℕ) : C(X, X) :=
  (iterateFamily H N).comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

def iteratedHomotopy (H : C(I × X, X)) (hzero : ∀ x, H (0, x) = x)
    (S : Set X) (hfixed : ∀ s x, x ∈ S → H (s, x) = x) (N : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X) (endpoint H N) S where
  toContinuousMap := iterateFamily H N
  map_zero_left := iterateFamily_at_zero H hzero N
  map_one_left _ := rfl
  prop' s _x hx := iterateFamily_fixed H S hfixed N s hx

/-- Finite iteration lowers a bounded-energy space, through a native relative
homotopy all of whose slices are energy nonincreasing. -/
theorem exists_lowering_homotopy (H : C(I × X, X)) (f : X → ℝ) (S : Set X)
    (k E δ : ℝ) (hδ : 0 < δ) (hbound : ∀ x, f x ≤ E)
    (hzero : ∀ x, H (0, x) = x) (hfixed : ∀ s x, x ∈ S → H (s, x) = x)
    (hle : ∀ s x, f (H (s, x)) ≤ f x)
    (hdrop : ∀ x, k ≤ f x → f (H (1, x)) ≤ f x - δ) :
    ∃ F : C(X, X), ∃ K : ContinuousMap.HomotopyRel (ContinuousMap.id X) F S,
      (∀ s x, f (K (s, x)) ≤ f x) ∧ ∀ x, f (F x) ≤ k := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((E - k) / δ)
  have hlarge : E - k < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
  refine ⟨endpoint H N, iteratedHomotopy H hzero S hfixed N,
    iterateFamily_energy_le H f hle N, ?_⟩
  intro x
  rcases iterate_energy_dichotomy (fun y ↦ H (1, y)) f k δ (hle 1) hdrop N x with hk | hk
  · exact hk
  · have hb := hbound x
    change f ((fun y ↦ H (1, y))^[N] x) ≤ k
    linarith

end NoExoticSixSphere.EnergyDeformationIteration
