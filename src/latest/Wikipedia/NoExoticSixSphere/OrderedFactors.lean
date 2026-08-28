import Wikipedia.NoExoticSixSphere.OrthogonalLieGroup
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered finite factors for broken-path realization

These products retain their order; no commutativity of the orthogonal
group is used. A completed prefix followed by a single active edge and
identity factors has the expected exact product.
-/

namespace NoExoticSixSphere.OrderedFactors

variable {G : Type*} [Monoid G] {N : ℕ}

theorem partialProd_congr (f g : Fin N → G) (k : Fin (N + 1))
    (h : ∀ j : Fin N, (j : ℕ) < (k : ℕ) → f j = g j) :
    Fin.partialProd f k = Fin.partialProd g k := by
  revert h
  induction k using Fin.inductionOn with
  | zero => intro _; simp
  | succ j ih =>
    intro h
    rw [Fin.partialProd_succ, Fin.partialProd_succ,
      ih (fun q hq ↦ h q (by
        change (q : ℕ) < (j : ℕ) at hq
        change (q : ℕ) < (j : ℕ) + 1
        omega)), h j (by change (j : ℕ) < (j : ℕ) + 1; omega)]

theorem partialProd_of_tail_one (f : Fin N → G) (i : Fin N)
    (h : ∀ j, i < j → f j = 1) (k : Fin (N + 1)) (hik : i.succ ≤ k) :
    Fin.partialProd f k = Fin.partialProd f i.succ := by
  revert hik
  induction k using Fin.inductionOn with
  | zero =>
    intro h
    change (i : ℕ) + 1 ≤ 0 at h
    omega
  | succ j ih =>
    intro hij
    by_cases he : j = i
    · subst j
      rfl
    · have hlt : i < j := by
        have hne : (i : ℕ) ≠ (j : ℕ) := fun hv ↦ he (Fin.ext hv.symm)
        change (i : ℕ) + 1 ≤ (j : ℕ) + 1 at hij
        change (i : ℕ) < (j : ℕ)
        omega
      rw [Fin.partialProd_succ, h j hlt, mul_one]
      apply ih
      change (i : ℕ) + 1 ≤ (j : ℕ)
      exact hlt

theorem partialProd_last_eq (f g : Fin N → G) (i : Fin N)
    (hbefore : ∀ j, j < i → f j = g j) (hafter : ∀ j, i < j → f j = 1) :
    Fin.partialProd f (Fin.last N) = Fin.partialProd g i.castSucc * f i := by
  rw [partialProd_of_tail_one f i hafter (Fin.last N) (Fin.le_last _), Fin.partialProd_succ]
  rw [partialProd_congr f g i.castSucc (fun j hj ↦ hbefore j hj)]

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace G] [ContinuousMul G]

theorem continuous_partialProd {f : X → Fin N → G} (hf : ∀ i, Continuous (fun x ↦ f x i))
    (k : Fin (N + 1)) : Continuous (fun x ↦ Fin.partialProd (f x) k) := by
  induction k using Fin.inductionOn with
  | zero =>
    simpa only [Fin.partialProd_zero] using
      (continuous_const : Continuous (fun _ : X ↦ (1 : G)))
  | succ j ih => simpa only [Fin.partialProd_succ] using! ih.mul (hf j)

end NoExoticSixSphere.OrderedFactors
