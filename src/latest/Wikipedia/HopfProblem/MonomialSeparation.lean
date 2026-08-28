import Wikipedia.HopfProblem.ToricCharts

/-!
# Closed graphs of separated monomial overlaps

Nonnegative integral characters on two charts give polynomial functions
whose product is one on the overlap. If the source character vanishes on
every excluded coordinate hyperplane, this prevents new identifications
from appearing in the closure of the overlap graph.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricCharts

def character (a : Fin 3 → ℤ) (z : CoordinateSpace 3) : ℂ := ∏ j, z j ^ a j

theorem character_contDiff (a : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (n : ℕ∞ω) :
    ContDiff ℂ n (character a) := by
  apply contDiff_prod
  intro j _
  have he : (fun z : CoordinateSpace 3 => z j ^ a j) =
      (fun z : CoordinateSpace 3 => z j ^ (a j).toNat) := by
    funext z
    conv_lhs => rw [← Int.toNat_of_nonneg (ha j), zpow_natCast]
  rw [he]
  exact (contDiff_apply ℂ ℂ j).pow _

theorem characters_mul_on_torus (A : Matrix (Fin 3) (Fin 3) ℤ)
    (a b : Fin 3 → ℤ) (h : ∀ j, a j + ∑ i, b i * A i j = 0)
    {z : CoordinateSpace 3} (hz : z ∈ torus) :
    character a z * character b (monomial A z) = 1 := by
  have he := congrFun (monomial_mul_on_torus (fun _ j : Fin 3 => b j) A hz) 0
  change character b (monomial A z) = ∏ j, z j ^ ∑ i, b i * A i j at he
  rw [he]
  unfold character
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ j, z j ^ a j * z j ^ ∑ i, b i * A i j) = ∏ _j : Fin 3, (1 : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_add₀ (hz j), h j, zpow_zero]
    _ = 1 := by simp

theorem characters_mul_on_domain (A : Matrix (Fin 3) (Fin 3) ℤ)
    (a b : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ j, a j + ∑ i, b i * A i j = 0) :
    EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1) (domain A) := by
  have he : EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1)
      (domain A ∩ torus) := fun _ hz => characters_mul_on_torus A a b h hz.2
  refine he.of_subset_closure ?_ continuousOn_const inter_subset_left
    (torus_dense.open_subset_closure_inter (domain_open A))
  exact (character_contDiff a ha 0).continuous.continuousOn.mul
    ((character_contDiff b hb 0).continuous.comp_continuousOn
      (monomial_contDiffOn A 0).continuousOn)

def overlapGraph (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Set (CoordinateSpace 3 × CoordinateSpace 3) :=
  {p | p.1 ∈ domain A ∧ monomial A p.1 = p.2}

theorem overlapGraph_closed (A : Matrix (Fin 3) (Fin 3) ℤ)
    (a b : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hcancel : ∀ j, a j + ∑ i, b i * A i j = 0)
    (hpos : ∀ i j, A i j < 0 → 0 < a j) : IsClosed (overlapGraph A) := by
  let P : CoordinateSpace 3 × CoordinateSpace 3 → ℂ :=
    fun p => character a p.1 * character b p.2
  have hP : Continuous P :=
    ((character_contDiff a ha 0).continuous.comp continuous_fst).mul
      ((character_contDiff b hb 0).continuous.comp continuous_snd)
  have hsubset : overlapGraph A ⊆ {p | P p = 1} := by
    intro p hp
    change character a p.1 * character b p.2 = 1
    rw [← hp.2]
    exact characters_mul_on_domain A a b ha hb hcancel hp.1
  apply isClosed_of_closure_subset
  intro p hp
  have hPeq : P p = 1 := closure_minimal hsubset (isClosed_eq hP continuous_const) hp
  have hD : p.1 ∈ domain A := by
    intro i j hij hz
    have hchar : character a p.1 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz, zero_zpow _ (ne_of_gt (hpos i j hij))]
    change character a p.1 * character b p.2 = 1 at hPeq
    simp [hchar] at hPeq
  refine ⟨hD, ?_⟩
  let : (𝓝[overlapGraph A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hf : ContinuousAt (fun q : CoordinateSpace 3 × CoordinateSpace 3 =>
      monomial A q.1) p :=
    ((monomial_contDiffOn A 0).continuousOn.continuousAt
      ((domain_open A).mem_nhds hD)).comp continuous_fst.continuousAt
  have he : (fun q : CoordinateSpace 3 × CoordinateSpace 3 => monomial A q.1)
      =ᶠ[𝓝[overlapGraph A] p] Prod.snd := by
    filter_upwards [self_mem_nhdsWithin (s := overlapGraph A) (a := p)] with q hq
    exact hq.2
  exact tendsto_nhds_unique hf.continuousWithinAt
    (continuous_snd.continuousAt.continuousWithinAt.congr' he.symm)

end Wikipedia.HopfProblem.ToricCharts
