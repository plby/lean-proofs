import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.FinalReduction
import ErdosProblems.Erdos550.Reservoirs
import ErdosProblems.Erdos550.BlockerInequalities
import ErdosProblems.Erdos550.Compactness
import ErdosProblems.Erdos550.CompactnessGraph
import ErdosProblems.Erdos550.EFRS
import ErdosProblems.Erdos550.ProfileForest
import ErdosProblems.Erdos550.MainProof

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 550 — main theorem (statement)

For fixed `k ≥ 2` and `1 ≤ m₁ ≤ ⋯ ≤ m_k`, for every sufficiently large `n` and
every `n`-vertex tree `T`,
$$ R(T, K_{m_1,\ldots,m_k}) \le (k-1)\bigl(R(T,K_{m_1,m_2})-1\bigr) + m_1. $$

Here the two smallest classes `m₁, m₂` are `m 0, m 1` (using monotonicity), and
`K_{m_1,m_2}` is modelled as a two-part complete multipartite graph
`Kmult 2 (m ∘ Fin.castLE …)`.

The `k = 2` case is elementary (the right-hand side is `R(T,H) - 1 + m₁ ≥ R(T,H)`
and `K_{m_1,m_2} = K_{m_1,…,m_k}`).  The substantial content is the case
`k ≥ 3`, isolated as `erdos_550_large`, whose proof follows the paper's chain.

The off--Turán step follows from exact Szemerédi regularity, the red
multipartite blow-up lemma, a maximal reduced matching, whole-edge allocation,
and the stateful Hladký--Piguet parity embedding.
-/

open SimpleGraph

namespace Erdos550

/-- The substantial case `k ≥ 3` (equivalently `q = k-1 ≥ 2`) of Erdős 550. -/
theorem erdos_550_large (k : ℕ) (hk : 3 ≤ k) (m : Fin k → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m ⟨0, by omega⟩) :
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      ramsey T (Kmult k m) ≤
        (k - 1) * (ramsey T (Kmult 2 (fun j => m (Fin.castLE (by omega) j))) - 1)
          + m ⟨0, by omega⟩ := by
  set q := k - 1 with hqdef
  have hqk : q + 1 = k := by omega
  have hq : 2 ≤ q := by omega
  set m' : Fin (q + 1) → ℕ := fun j => m (Fin.cast hqk j) with hm'
  have hmono' : Monotone m' := fun i j hij => hmono hij
  have ec0 : Fin.cast hqk (0 : Fin (q+1)) = (⟨0, by omega⟩ : Fin k) := by ext; simp; try omega
  have ec1 : Fin.cast hqk (1 : Fin (q+1)) = (⟨1, by omega⟩ : Fin k) := by ext; simp; try omega
  have el0 : Fin.castLE (by omega : 2 ≤ k) (0 : Fin 2) = (⟨0, by omega⟩ : Fin k) := by ext; simp; try omega
  have el1 : Fin.castLE (by omega : 2 ≤ k) (1 : Fin 2) = (⟨1, by omega⟩ : Fin k) := by ext; simp; try omega
  have hm'0 : m' 0 = m ⟨0, by omega⟩ := by simp only [hm']; rw [ec0]
  have hm'1 : m' 1 = m ⟨1, by omega⟩ := by simp only [hm']; rw [ec1]
  have hpos' : 1 ≤ m' 0 := by rw [hm'0]; exact hpos
  obtain ⟨n0, H⟩ := erdos_550_large_core q hq m' hmono' hpos'
  refine ⟨n0, fun n hn V _ T hT hcard => ?_⟩
  have hreidx : ramsey T (Kmult k m) = ramsey T (Kmult (q+1) m') :=
    ramsey_Kmult_reindex T (finCongr hqk.symm) m m' (fun i => by simp only [hm']; congr 1)
  have hbip : ramsey T (Kmult 2 (fun j => m (Fin.castLE (by omega : 2 ≤ k) j)))
      = ramsey T (Kbip (m' 0) (m' 1)) := by
    rw [ramsey_Kmult2_Kbip T (fun j => m (Fin.castLE (by omega : 2 ≤ k) j)), hm'0, hm'1, el0, el1]
  rw [hreidx, hbip, hm'0]
  exact H n hn T hT hcard

/-- **Erdős Problem 550.**  Fix `k ≥ 2` and
`1 ≤ m 0 ≤ m 1 ≤ ⋯ ≤ m (k-1)`.  There is `n₀` such that
for every `n ≥ n₀` and every `n`-vertex tree `T`,
`R(T, K_{m 0,…,m (k-1)}) ≤ (k-1)(R(T, K_{m 0, m 1}) - 1) + m 0`.

Its off--Turán input is the unconditional theorem
`off_turan_embedding_direct`. -/
theorem erdos_550 (k : ℕ) (hk : 2 ≤ k) (m : Fin k → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m ⟨0, by omega⟩) :
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      ramsey T (Kmult k m) ≤
        (k - 1) * (ramsey T (Kmult 2 (fun j => m (Fin.castLE hk j))) - 1)
          + m ⟨0, by omega⟩ := by
  rcases lt_or_ge k 3 with hk2 | hk3
  · -- `k = 2`: here `K_{m_1,…,m_k} = K_{m_1,m_2}` and the RHS is `R - 1 + m 0 ≥ R`.
    obtain rfl : k = 2 := by omega
    refine ⟨0, fun n _ V _ T _ _ => ?_⟩
    -- the two graphs coincide and `m 0 ≥ 1`
    have hcast : (fun j => m (Fin.castLE hk j)) = m := by
      funext j; simp
    rw [ramsey_Kmult_congr T hcast]
    have h0 : 1 ≤ m ⟨0, by omega⟩ := hpos
    omega
  · -- `k ≥ 3`: the substantial case.
    exact erdos_550_large k hk3 m hmono hpos

end Erdos550
