import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Family
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Partition

/-! Consequences of the proved interval partition for actual sector germs. -/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

/-- For genuine local sector germs, equal widths force thirty degrees.
The width equality is discharged from actual congruences in the final theorem. -/
theorem width_eq_pi_div_six_of_equal_widths {P : Fin 3 → Set Plane}
    (g : ∀ i, AngularGerm (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : ∃ R > 0, ball (0 : Plane) R ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ ⋃ i, P i)
    (hwidth : ∀ i j, (g i).upper - (g i).lower = (g j).upper - (g j).lower)
    (i : Fin 3) : (g i).upper - (g i).lower = Real.pi / 6 := by
  have h := Partition.width_eq_third (div_pos Real.pi_pos (by norm_num))
    (fun i => ⟨(g i).lower_nonneg, (g i).lower_lt_upper, (g i).upper_le⟩)
    (intervals_pairwise_disjoint g hdis) (intervals_cover_of_local_cover g hcover) hwidth i
  linarith

/-- The rays really occur in the order `0, π/6, π/3, π/2`; neither boundary
coverage nor adjacency is an additional hypothesis. -/
theorem exists_ordering_of_equal_widths {P : Fin 3 → Set Plane}
    (g : ∀ i, AngularGerm (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : ∃ R > 0, ball (0 : Plane) R ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ ⋃ i, P i)
    (hwidth : ∀ i j, (g i).upper - (g i).lower = (g j).upper - (g j).lower) :
    ∃ σ : Equiv.Perm (Fin 3),
      (g (σ 0)).lower = 0 ∧ (g (σ 0)).upper = Real.pi / 6 ∧
      (g (σ 1)).lower = Real.pi / 6 ∧ (g (σ 1)).upper = Real.pi / 3 ∧
      (g (σ 2)).lower = Real.pi / 3 ∧ (g (σ 2)).upper = Real.pi / 2 := by
  obtain ⟨σ, h₀, h₁, h₂, h₃, h₄, h₅⟩ :=
    Partition.exists_thirds_permutation (div_pos Real.pi_pos (by norm_num))
      (fun i => ⟨(g i).lower_nonneg, (g i).lower_lt_upper, (g i).upper_le⟩)
      (intervals_pairwise_disjoint g hdis) (intervals_cover_of_local_cover g hcover) hwidth
  refine ⟨σ, h₀, ?_, ?_, ?_, ?_, h₅⟩ <;> linarith

end Puzzling139335.N6.TripleSectors.Angles
