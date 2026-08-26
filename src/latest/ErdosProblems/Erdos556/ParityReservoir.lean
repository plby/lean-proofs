import ErdosProblems.Erdos556.ParityConnections
import ErdosProblems.Erdos556.ResilientSampling
import ErdosProblems.Erdos556.SamplingAsymptotic

/-!
# Reservoirs supplying either parity

The finite sampling construction is applied to all ordered pairs of distinct
vertices. The final theorem absorbs the numerical failure bound into a
uniform sufficiently-large-order threshold.
-/

namespace Erdos556

open SimpleGraph Finset Filter

theorem exists_parity_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d D m a : ℕ)
    (hconn : ConnectedAfterDeleting G (b + 3 * D + 3))
    (hnonbip : NonbipartiteAfterDeleting G (b + 3 * D + 3))
    (hd : 0 < d) (hdeg : ∀ w, d + (b + 3 * D + 3) ≤ G.degree w)
    (hN : Fintype.card V ≤ D * d)
    (hbound : ((a + 1) * m) * (12 * D + 3) ≤ b)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hfail : (Fintype.card V : ℝ) ^ 2 * (a + 1) *
      (1 - q ^ (12 * D + 3)) ^ m < 1 / 2)
    (hV : 0 < Fintype.card V) :
    ∃ R : Finset V, (R.card : ℝ) ≤ 2 * q * Fintype.card V ∧
      ∀ u v, u ≠ v → ∀ S, S.card ≤ a →
        ParityConnection G (12 * D + 3) u v (R \ S) := by
  classical
  let I := {uv : V × V // uv.1 ≠ uv.2}
  let P : I → Finset V → Prop := fun uv => ParityConnection G (12 * D + 3) uv.val.1 uv.val.2
  have hav (uv : I) (S : Finset V) (hS : S.card ≤ b) :
      ∃ T : Finset V, P uv T ∧ T.card ≤ 12 * D + 3 ∧ Disjoint S T :=
    exists_short_parity_connection_avoiding G b d D hconn hnonbip hd hdeg hN
      uv.val.1 uv.val.2 uv.property S hS
  have hI : (Fintype.card I : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have h := Fintype.card_le_of_injective (fun uv : I => uv.val) Subtype.val_injective
    rw [Fintype.card_prod] at h
    rw [pow_two]
    exact_mod_cast h
  have hr : 0 ≤ 1 - q ^ (12 * D + 3) := sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hf : (Fintype.card I : ℝ) * (a + 1) * (1 - q ^ (12 * D + 3)) ^ m < 1 / 2 := by
    apply lt_of_le_of_lt _ hfail
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hI (by positivity)) (pow_nonneg hr _)
  obtain ⟨R, hR, hhit⟩ := exists_small_set_of_avoidance P q hq0 hq1 (12 * D + 3) b m a
    hbound hav hf hV
  refine ⟨R, hR, ?_⟩
  intro u v huv S hS
  obtain ⟨T, hTR, hP, _, hST⟩ := hhit ⟨(u, v), huv⟩ S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx, fun hxS => Finset.disjoint_left.mp hST hxS hx⟩

theorem exists_uniform_parity_reservoir (D B a : ℕ) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b d : ℕ),
      N₀ ≤ Fintype.card V → ConnectedAfterDeleting G (b + 3 * D + 3) →
      NonbipartiteAfterDeleting G (b + 3 * D + 3) →
      (∀ w, d + (b + 3 * D + 3) ≤ G.degree w) → Fintype.card V ≤ D * d →
      Fintype.card V ≤ B * b →
      ∃ R : Finset V, (R.card : ℝ) ≤ 2 * q * Fintype.card V ∧
        ∀ u v, u ≠ v → ∀ S, S.card ≤ a →
          ParityConnection G (12 * D + 3) u v (R \ S) := by
  let L := 12 * D + 3
  let K := B * ((a + 1) * L)
  have hL : 0 < L := by dsimp [L]; omega
  have hK : 0 < K := Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_reservoir_failure q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1, ?_⟩
  intro V _ _ G _ b d hN hc hnb hg hd hb
  have hV : 0 < Fintype.card V := by omega
  have hdpos : 0 < d := by nlinarith
  let m := Fintype.card V / K
  have hbudget : ((a + 1) * m) * L ≤ b := by
    have hmul : B * (((a + 1) * m) * L) ≤ B * b := by
      calc
        B * (((a + 1) * m) * L) = m * K := by dsimp [K]; ring
        _ ≤ Fintype.card V := Nat.div_mul_le_self _ _
        _ ≤ B * b := hb
    nlinarith
  exact exists_parity_reservoir G b d D m a hc hnb hdpos hg hd hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV

#print axioms exists_parity_reservoir
#print axioms exists_uniform_parity_reservoir

end Erdos556
