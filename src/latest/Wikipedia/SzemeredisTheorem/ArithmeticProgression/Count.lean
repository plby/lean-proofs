import Wikipedia.SzemeredisTheorem.Finite.Mean
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.ZMod.Basic

/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The `j`th term of a cyclic arithmetic progression. -/
def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

/-- The weight contributed by one cyclic `k`-term progression. -/
def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

/-- The normalized weighted count of cyclic `k`-term progressions. The
average includes the diagonal `d = 0`. -/
noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

theorem cyclicAPProduct_nonneg {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cyclicAPProduct k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (cyclicAPTerm a d j)

theorem cyclicAPCount_nonneg {k N : ℕ} [NeZero N]
    {f : ZMod N → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cyclicAPCount k N f := by
  apply mean_nonneg
  intro a
  apply mean_nonneg
  intro d
  exact cyclicAPProduct_nonneg hf a d

@[simp]
theorem cyclicAPProduct_const (k N : ℕ) (c : ℝ) (a d : ZMod N) :
    cyclicAPProduct k N (fun _ => c) a d = c ^ k := by
  simp [cyclicAPProduct]

theorem cyclicAPProduct_smul
    (k N : ℕ) (c : ℝ) (f : ZMod N → ℝ)
    (a d : ZMod N) :
    cyclicAPProduct k N (fun x => c * f x) a d =
      c ^ k * cyclicAPProduct k N f a d := by
  simp [cyclicAPProduct, Finset.prod_mul_distrib]

@[simp]
theorem cyclicAPCount_const (k N : ℕ) [NeZero N] (c : ℝ) :
    cyclicAPCount k N (fun _ => c) = c ^ k := by
  simp [cyclicAPCount, mean₂]

theorem cyclicAPCount_smul
    (k N : ℕ) [NeZero N] (c : ℝ) (f : ZMod N → ℝ) :
    cyclicAPCount k N (fun x => c * f x) =
      c ^ k * cyclicAPCount k N f := by
  simp_rw [cyclicAPCount, mean₂, cyclicAPProduct_smul, mean_smul]

theorem cyclicAPProduct_mono {k N : ℕ} {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (a d : ZMod N) :
    cyclicAPProduct k N f a d ≤ cyclicAPProduct k N g a d := by
  exact Finset.prod_le_prod
    (fun j _ => hf (cyclicAPTerm a d j))
    (fun j _ => hfg (cyclicAPTerm a d j))

theorem cyclicAPCount_mono {k N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    cyclicAPCount k N f ≤ cyclicAPCount k N g := by
  apply mean_mono
  intro a
  apply mean_mono
  intro d
  exact cyclicAPProduct_mono hf hfg a d

end Wikipedia.SzemeredisTheorem
