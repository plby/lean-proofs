import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.IntrinsicCorners

/-!
# A common radius excluding nonincident pieces

There are only four physical square corners and four closed pieces. A
single positive radius therefore excludes every piece not incident at the
corner in question. The same exclusion holds for every smaller radius.
-/

open Set Metric

namespace Puzzling139335.SquareDissection

/-- Balls of this radius around the square corners meet only incident pieces. -/
def IsCornerRadius (d : SquareDissection) (r : ℝ) : Prop :=
  ∀ j i : Fin 4, corner j ∉ d.piece i → Disjoint (ball (corner j) r) (d.piece i)

theorem IsCornerRadius.mono {d : SquareDissection} {r ε : ℝ}
    (hε : d.IsCornerRadius ε) (hr : r ≤ ε) : d.IsCornerRadius r := by
  intro j i hji
  exact (hε j i hji).mono_left (ball_subset_ball hr)

theorem exists_corner_radius (d : SquareDissection) :
    ∃ ε : ℝ, 0 < ε ∧ d.IsCornerRadius ε := by
  classical
  have hlocal (j : Fin 4) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin 4, corner j ∉ d.piece i →
        Disjoint (ball (corner j) ε) (d.piece i) := by
    let U : Set Plane := ⋂ i : Fin 4,
      if corner j ∈ d.piece i then univ else (d.piece i)ᶜ
    have hU : IsOpen U := by
      apply isOpen_iInter_of_finite
      intro i
      split_ifs
      · exact isOpen_univ
      · exact (d.jordan i).isClosed.isOpen_compl
    have hjU : corner j ∈ U := by
      apply mem_iInter.mpr
      intro i
      split_ifs with hji
      · trivial
      · exact hji
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hjU)
    refine ⟨ε, hε, ?_⟩
    intro i hji
    apply disjoint_left.mpr
    intro x hx hxP
    have hxU : x ∈ U := hball hx
    have hxnot : x ∉ d.piece i := by
      change x ∈ (d.piece i)ᶜ
      simpa only [if_neg hji] using mem_iInter.mp hxU i
    exact hxnot hxP
  choose ρ hρpos hρsep using hlocal
  let ε : ℝ := min (min (ρ 0) (ρ 1)) (min (ρ 2) (ρ 3))
  have hεpos : 0 < ε := by
    simp only [ε, lt_min_iff]
    exact ⟨⟨hρpos 0, hρpos 1⟩, hρpos 2, hρpos 3⟩
  have hεle (j : Fin 4) : ε ≤ ρ j := by
    fin_cases j
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hεpos, ?_⟩
  intro j i hji
  exact (hρsep j i hji).mono_left (ball_subset_ball (hεle j))

end Puzzling139335.SquareDissection
