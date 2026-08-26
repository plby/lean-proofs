import Mathlib
import ErdosProblems.Erdos550.OffTuranRegularityData
import ErdosProblems.Erdos550.OffTuranCleanedDegree
import ErdosProblems.Erdos550.RegularityRetention

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Regularity partition with normalized cleaned degree

This is the quantitative regularity output used by the reduced-graph steps.  The
cluster scale is the equipartition upper size `⌊N/ℓ⌋+1`; the rounding estimate
`ℓ·scale ≤ N+ℓ` lets the cleaned host average pass to the sum of normalized
cluster degrees.
-/

open Finset SimpleGraph Finpartition SzemerediRegularity

namespace Erdos550

open Classical

structure OffTuranReducedDegreeData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d base η : ℝ) (m₀ : ℕ) where
  P : Finpartition (Finset.univ : Finset V)
  equipartition : P.IsEquipartition
  lower_parts : ⌈4 / ε⌉₊ ≤ P.parts.card
  upper_parts :
    P.parts.card ≤ SzemerediRegularity.bound ε ⌈4 / ε⌉₊
  uniform : P.IsUniform G ε
  scale : ℕ
  scale_eq : scale = Fintype.card V / P.parts.card + 1
  scale_pos : 0 < scale
  part_nonempty : ∀ i : {C // C ∈ P.parts}, (i.1).Nonempty
  part_size_lower : ∀ i : {C // C ∈ P.parts}, m₀ ≤ i.1.card
  part_size_upper : ∀ i : {C // C ∈ P.parts}, i.1.card ≤ scale
  normalized_average :
    (base + 100 * η * Fintype.card V) * (P.parts.card : ℝ) ≤
      ∑ i, clusterNormalizedDegree
        (G.regularityReduced P ε d) P scale i

/-- Exact regularity plus the cleaned edge-average estimate produces
an equitable cluster system whose normalized degrees retain the full
`base+100ηN` margin. -/
theorem exists_offTuran_reduced_degree_data
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε d base η : ℝ) (m₀ : ℕ)
    (hε0 : 0 < ε)
    (hbase0 : 0 ≤ base)
    (hbaseN : base ≤ Fintype.card V)
    (hη0 : 0 < η) (hηsmall : η ≤ 1 / 100)
    (hregLarge :
      ⌈4 / ε⌉₊ ≤ Fintype.card V)
    (hboundEta :
      (SzemerediRegularity.bound ε ⌈4 / ε⌉₊ : ℝ) ≤
        η * Fintype.card V)
    (hboundMin :
      m₀ * SzemerediRegularity.bound ε ⌈4 / ε⌉₊ ≤
        Fintype.card V)
    (hclean : ∀ P : Finpartition (Finset.univ : Finset V),
      P.IsEquipartition → P.IsUniform G ε →
      ⌈4 / ε⌉₊ ≤ P.parts.card →
      P.parts.card ≤ SzemerediRegularity.bound ε ⌈4 / ε⌉₊ →
        (base + 150 * η * Fintype.card V) * Fintype.card V ≤
          2 * ((G.regularityReduced P ε d).edgeFinset.card : ℝ)) :
    Nonempty (OffTuranReducedDegreeData G ε d base η m₀) := by
  obtain ⟨P, hPeq, hPlo, hPhi, hPuni⟩ :=
    exists_offTuran_regular_partition G ε hε0 hregLarge
  let scale := Fintype.card V / P.parts.card + 1
  have hpartsPos : 0 < P.parts.card := by
    exact (Nat.ceil_pos.mpr (by positivity : 0 < 4 / ε)).trans_le hPlo
  have hscalePos : 0 < scale := by
    simpa [scale] using!
      Nat.succ_pos (Fintype.card V / P.parts.card)
  have hellEta :
      (P.parts.card : ℝ) ≤ η * Fintype.card V := by
    have hcast : (P.parts.card : ℝ) ≤
        SzemerediRegularity.bound ε ⌈4 / ε⌉₊ := by
      exact_mod_cast hPhi
    exact hcast.trans hboundEta
  have hmMul :
      m₀ * P.parts.card ≤ Fintype.card V :=
    (Nat.mul_le_mul_left m₀ hPhi).trans hboundMin
  have hmAvg :
      m₀ ≤ Fintype.card V / P.parts.card :=
    (Nat.le_div_iff_mul_le hpartsPos).2 hmMul
  have hellScaleNat :
      P.parts.card * scale ≤ Fintype.card V + P.parts.card := by
    dsimp [scale]
    calc
      P.parts.card * (Fintype.card V / P.parts.card + 1) =
          P.parts.card * (Fintype.card V / P.parts.card) +
            P.parts.card := by simp [Nat.mul_add]
      _ ≤ Fintype.card V + P.parts.card :=
        Nat.add_le_add_right
          (Nat.mul_div_le (Fintype.card V) P.parts.card)
          P.parts.card
  have hellScale :
      (P.parts.card : ℝ) * (scale : ℝ) ≤
        Fintype.card V + P.parts.card := by
    exact_mod_cast hellScaleNat
  have havg :=
    normalized_cluster_average_of_edges
      (G.regularityReduced P ε d) P scale base η
      hbase0 hbaseN hη0 hηsmall
      Fintype.card_pos hscalePos
      hellEta hellScale (hclean P hPeq hPuni hPlo hPhi)
  refine ⟨⟨P, hPeq, hPlo, hPhi, hPuni, scale, rfl,
    hscalePos, ?_, ?_, ?_, havg⟩⟩
  · intro i
    exact P.nonempty_of_mem_parts i.2
  · intro i
    exact hmAvg.trans (by
      have h := hPeq.average_le_card_part i.2
      simpa only [Finset.card_univ] using! h)
  · intro i
    have h := hPeq.card_part_le_average_add_one i.2
    simpa only [Finset.card_univ, scale] using! h

/-- The raw average-degree form.  Decoupled regularity cleaning at
density `η` costs less than the available `50ηN²` edge budget, so the
normalized reduced degree retains the `base+100ηN` margin. -/
theorem exists_offTuran_reduced_degree_data_of_raw
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε base η : ℝ) (m₀ : ℕ)
    (hε0 : 0 < ε) (hεη : ε ≤ η)
    (hbase0 : 0 ≤ base)
    (hbaseN : base ≤ Fintype.card V)
    (hη0 : 0 < η) (hηsmall : η ≤ 1 / 100)
    (hregLarge : ⌈4 / ε⌉₊ ≤ Fintype.card V)
    (hboundEta :
      (SzemerediRegularity.bound ε ⌈4 / ε⌉₊ : ℝ) ≤
        η * Fintype.card V)
    (hboundMin :
      m₀ * SzemerediRegularity.bound ε ⌈4 / ε⌉₊ ≤
        Fintype.card V)
    (hraw :
      (base + 200 * η * Fintype.card V) * Fintype.card V ≤
        2 * (G.edgeFinset.card : ℝ)) :
    Nonempty (OffTuranReducedDegreeData G ε η base η m₀) := by
  apply exists_offTuran_reduced_degree_data
    G ε η base η m₀ hε0 hbase0 hbaseN hη0 hηsmall
    hregLarge hboundEta hboundMin
  intro P hPeq hPuni hPlo hPhi
  have hN0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hell0 : (0 : ℝ) ≤ P.parts.card := by positivity
  have hellEta :
      (P.parts.card : ℝ) ≤ η * Fintype.card V := by
    have hcast :
        (P.parts.card : ℝ) ≤
          SzemerediRegularity.bound ε ⌈4 / ε⌉₊ := by
      exact_mod_cast hPhi
    exact hcast.trans hboundEta
  have hP' : 4 / ε ≤ (P.parts.card : ℝ) :=
    (Nat.le_ceil (4 / ε)).trans (by exact_mod_cast hPlo)
  have hret :=
    regularityReduced_edges_card_decoupled'
      hε0 hη0.le hε0 hPeq hPuni hP'
  have hloss :
      2 * ((G.edgeFinset.card : ℝ) -
          ((G.regularityReduced P ε η).edgeFinset.card : ℝ)) <
        50 * η * (Fintype.card V : ℝ) ^ 2 := by
    apply offTuran_cleaning_loss_lt_fifty
      ε η (Fintype.card V) P.parts.card
      (2 * ((G.edgeFinset.card : ℝ) -
        ((G.regularityReduced P ε η).edgeFinset.card : ℝ)))
      hε0.le hεη hη0 hηsmall hN0 hell0 hellEta
    simpa [mul_assoc] using! hret
  nlinarith [hraw]

end Erdos550
