module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Stream.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Tactic.Cases

/-!
## `Finset ℕ` machinery for use in sums and products
-/

open Filter (atTop)
open Stream' (cons)
open scoped Topology Stream

variable {G : Type} [NormedAddCommGroup G]
variable {H : Type} [CommMonoid H]

/-- Insert `0` into a `Finset ℕ`, adding `1` to existing elements -/
public def push (N : Finset ℕ) :=
  insert 0 (Finset.image (fun n ↦ n + 1) N)

/-- Subtract `1` from everything in a `Finset ℕ`, discarding `0`.
    This is the left inverse of push. -/
public def pop (N : Finset ℕ) :=
  Finset.image (fun n ↦ n - 1) (Finset.erase N 0)

/-- `push` almost cancels `pop` -/
public theorem push_pop {N : Finset ℕ} : push (pop N) = insert 0 N := by
  rw [push, pop]; apply Finset.ext; simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, ne_eq, exists_exists_and_eq_and]
  intro n; by_cases n0 : n = 0; · rw [n0]; simp
  simp_rw [or_iff_right n0]
  constructor
  · intro h; rcases h with ⟨x, ⟨x0, xN⟩, xn⟩
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr x0)] at xn
    rwa [←xn]
  · intro h; exists n; use ⟨n0,h⟩
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr n0)

/-- `push` is monotone -/
theorem push_le_push {A B : Finset ℕ} : push A ≤ push B ↔ A ≤ B := by
  rw [push, push]
  constructor
  · intro AB; rw [Finset.subset_iff] at AB ⊢; intro x xA
    have h : x + 1 ∈ insert 0 (Finset.image (fun n : ℕ ↦ n + 1) A) := by simpa
    specialize AB h; simp at AB; assumption
  · intro AB; apply Finset.insert_subset_insert; apply Finset.image_mono; assumption

/-- `push` and sums interact nicely, `Stream'.get` version to keep terms type-correct
    at low transparency -/
public theorem push_sum_get {X : Type} [AddCommGroup X] {a : X} {g : Stream' X} {N : Finset ℕ} :
    a + N.sum g.get = (push N).sum (cons a g).get := by
  rw [push, Finset.sum_insert (by simp), Finset.sum_image (fun x _ y _ h ↦ by omega)]
  rfl

/-- `push` and sums interact nicely -/
public theorem push_sum {X : Type} [AddCommGroup X] {a : X} {f : ℕ → X} {N : Finset ℕ} :
    a + N.sum f = (push N).sum (cons a f) :=
  push_sum_get

/-- `push` and products interact nicely, `Stream'.get` version to keep terms type-correct
    at low transparency -/
public theorem push_prod_get {a : H} {g : Stream' H} {N : Finset ℕ} :
    a * N.prod g.get = (push N).prod (cons a g).get := by
  rw [push, Finset.prod_insert (by simp), Finset.prod_image (fun x _ y _ h ↦ by omega)]
  rfl

/-- `push` and products interact nicely -/
public theorem push_prod {a : H} {f : ℕ → H} {N : Finset ℕ} :
    a * N.prod f = (push N).prod (cons a f) :=
  push_prod_get

/-- The range of `push` is `Finset`s containing 0 -/
theorem push_range : Set.range push = {N : Finset ℕ | 0 ∈ N} := by
  rw [Set.range]; apply Set.ext; simp only [Set.mem_ofPred_eq]; intro N; constructor
  · intro h; rcases h with ⟨M, H⟩; rw [push] at H; rw [← H]; exact Finset.mem_insert_self 0 _
  · intro N0; exists pop N; rw [push_pop]; exact Finset.insert_eq_of_mem N0

theorem push_comap_atTop : Filter.comap push atTop = atTop := by
  apply Filter.comap_embedding_atTop
  exact @push_le_push
  intro N; exists pop N; rw [push_pop]; simp

/-- `f ∘ push` converges `atTop` iff `f` does -/
public theorem tendsto_comp_push {A : Type} {f : Finset ℕ → A} {l : Filter A} :
    Filter.Tendsto (f ∘ push) atTop l ↔ Filter.Tendsto f atTop l := by
  nth_rw 1 [← push_comap_atTop]; apply Filter.tendsto_comap'_iff
  rw [push_range]
  have h : {N : Finset ℕ | 0 ∈ N} = {N : Finset ℕ | {0} ≤ N} := by simp
  rw [h]; exact Filter.mem_atTop _

/-- Triangle inequality for finset sums -/
public theorem finset_norm_sum_le (N : Finset ℕ) (f : ℕ → G) :
    ‖N.sum fun n ↦ f n‖ ≤ N.sum fun n ↦ ‖f n‖ := by
  induction' N using Finset.induction with n N Nn h; · simp
  · rw [Finset.sum_insert Nn]
    rw [Finset.sum_insert Nn]
    trans ‖f n‖ + ‖N.sum fun n ↦ f n‖
    · apply norm_add_le
    · apply add_le_add_right; assumption

public theorem subset_union_sdiff (A B : Finset ℕ) : B ⊆ A ∪ B \ A := by
  rw [Finset.subset_iff]; intro x Bx
  rw [Finset.mem_union, Finset.mem_sdiff]
  by_cases Ax : x ∈ A
  · left; exact Ax
  · right; exact ⟨Bx, Ax⟩
