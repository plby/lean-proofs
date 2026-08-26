import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Set

namespace CofiniteDerivatives

variable {X : Type*} [TopologicalSpace X]

/-- The set of indices whose corresponding set meets `U`. -/
def goodOrders (Z : ℕ → Set X) (U : Set X) : Set ℕ :=
  {n | (Z n ∩ U).Nonempty}

/-- Every nonempty open set is met by all sufficiently large members of `Z`. -/
def CofinitelyHits (Z : ℕ → Set X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ N, ∀ n ≥ N, n ∈ goodOrders Z U

/-- Every strictly increasing subsequence of `Z` has dense union. -/
def EverySubsequenceDense (Z : ℕ → Set X) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → Dense (⋃ k, Z (s k))

/-- A strictly increasing sequence of natural numbers is eventually above every bound. -/
lemma strictMono_eventually_ge {s : ℕ → ℕ} (hs : StrictMono s) (N : ℕ) :
    ∃ k, N ≤ s k := by
  exact ⟨N, hs.id_le N⟩

/-- If the bad indices are infinite, they contain a strictly increasing subsequence. -/
lemma exists_strictMono_of_not_finite {P : ℕ → Prop}
    (hP : Set.Infinite {n | P n}) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k, P (s k) := by
  apply Nat.exists_strictMono_subsequence
  intro N
  obtain ⟨n, hn, hnrange⟩ := hP.exists_notMem_finset (Finset.range (N + 1))
  exact ⟨n, Nat.lt_of_not_ge (by simpa using! hnrange), hn⟩

/-- Cofinite hitting is equivalent to density along every increasing subsequence. -/
theorem cofiniteHits_iff_everySubsequenceDense (Z : ℕ → Set X) :
    CofinitelyHits Z ↔ EverySubsequenceDense Z := by
  constructor
  · intro hcof s hs
    rw [dense_iff_inter_open]
    intro U hU hUne
    obtain ⟨N, hN⟩ := hcof U hU hUne
    obtain ⟨k, hk⟩ := strictMono_eventually_ge hs N
    have hgood : s k ∈ goodOrders Z U := hN _ hk
    rcases hgood with ⟨z, hzZ, hzU⟩
    exact ⟨z, hzU, mem_iUnion.mpr ⟨k, hzZ⟩⟩
  · intro hsub U hU hUne
    by_contra heventual
    push Not at heventual
    have hinf : Set.Infinite ((goodOrders Z U)ᶜ) := by
      apply Set.infinite_of_forall_exists_gt
      intro N
      obtain ⟨n, hNn, hn⟩ := heventual (N + 1)
      exact ⟨n, hn, lt_of_lt_of_le (Nat.lt_succ_self N) hNn⟩
    obtain ⟨s, hs, hbad⟩ := exists_strictMono_of_not_finite hinf
    have hdense := hsub s hs
    obtain ⟨z, hzU, hzUnion⟩ := hdense.inter_open_nonempty U hU hUne
    rcases mem_iUnion.mp hzUnion with ⟨k, hzZ⟩
    exact hbad k ⟨z, hzZ, hzU⟩

end CofiniteDerivatives
