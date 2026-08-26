import ErdosProblems.Erdos556.TwoColourResilience
import ErdosProblems.Erdos556.LongCycleReservoir
import ErdosProblems.Erdos556.ReservoirAsymptotic

/-!
# Order bounds for dense cores in a two-colouring

If neither colour has a sufficiently long cycle, a minimum-degree core
has order only slightly larger than the forbidden cycle length.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_uniform_two_colour_core_order_bound (D B : ℕ) (hD : 0 < D) (hB : 0 < B) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L b : ℕ),
      N₀ ≤ Fintype.card V → 2 ≤ L → Fintype.card V ≤ D * L →
      Fintype.card V ≤ B * b → (∀ v, L + b ≤ G.degree v) →
      ¬ cycleGraph (2 * L) ⊑ Gᶜ →
      (∀ (z : V) (c : G.Walk z z), c.IsCycle → c.length < 2 * L) →
      Fintype.card V < 2 * L + b := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  let q : ℝ := 1 / (2 * B)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * B)).mpr
    have hBR1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  obtain ⟨N₀, hN₀⟩ := exists_uniform_connecting_reservoir D B 0 hD hB q hq hq1
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ L b hN hL hscale hbudget hdegree hcomp hcycles
  classical
  have hc := connectedAfterDeleting_of_complement_cycle_free G L b hL hdegree hcomp
  obtain ⟨R, hRsize, hres⟩ := hN₀ G b L hN hc hdegree hscale hbudget
  have hR : R.card ≤ b := by
    have hbR : (Fintype.card V : ℝ) ≤ (B : ℝ) * b := by exact_mod_cast hbudget
    have hquot : (Fintype.card V : ℝ) / B ≤ b := (div_le_iff₀ hBR).mpr (by nlinarith only [hbR])
    have heq : 2 * q * Fintype.card V = (Fintype.card V : ℝ) / B := by
      dsimp [q]
      field_simp
    rw [heq] at hRsize
    exact_mod_cast hRsize.trans hquot
  have hres' (u v : V) : ShortConnection G (3 * D) u v R := by
    have h := hres u v ∅ (by simp)
    simpa only [sdiff_empty] using h
  by_contra hlarge
  have hdegR (v : V) : L + R.card ≤ G.degree v := by
    have h := hdegree v
    omega
  obtain ⟨z, c, hcyc, hclen⟩ := exists_long_cycle_of_reservoir G L b (3 * D) hL R hR hc
    hdegR (by omega) hres'
  exact (hcycles z c hcyc).not_ge hclen

#print axioms exists_uniform_two_colour_core_order_bound

end Erdos556
