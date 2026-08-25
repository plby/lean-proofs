import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic
import Util.IncidenceGeometry.Basic

open Classical
open Filter
noncomputable section

lemma ThreeCoordinateSideEventNonconstantOfFinite
    (u v : Fin 3 → ℝ)
    (hfinite :
      ∀ i : Fin 3,
        Set.Finite
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * u i + t * v i = 0 ∧
              ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j}) :
    ∀ i : Fin 3,
      ({t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        (1 - t) * u i + t * v i = 0 ∧
          ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j} :
        Set ℝ).Nonempty →
        u i ≠ v i := by
  let L (u v : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
    (1 - t) * u i + t * v i

  let Side (u v : Fin 3 → ℝ) (i : Fin 3) : Set ℝ :=
    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
      L u v i t = 0 ∧ ∀ j : Fin 3, j ≠ i → 0 < L u v j t}

  have hfiniteSide : ∀ i : Fin 3, (Side u v i).Finite := by
    simpa [Side, L] using hfinite

  change ∀ i : Fin 3, (Side u v i).Nonempty → u i ≠ v i
  intro i hne huv
  rcases hne with ⟨r, hr⟩
  have hconst : ∀ t : ℝ, L u v i t = 0 := by
    have hui0 : u i = 0 := by
      dsimp [Side, L] at hr
      rw [huv] at hr
      linarith
    have hvi0 : v i = 0 := by
      simpa [huv] using hui0
    intro t
    dsimp [L]
    rw [hui0, hvi0]
    ring
  fin_cases i
  · dsimp [Side, L] at hr
    have hcont1 : Continuous fun t : ℝ => L u v 1 t := by
      dsimp [L]
      continuity
    have hcont2 : Continuous fun t : ℝ => L u v 2 t := by
      dsimp [L]
      continuity
    have hU :
        (Set.Ioo (0 : ℝ) 1 ∩ {t : ℝ | 0 < L u v 1 t} ∩
            {t : ℝ | 0 < L u v 2 t}) ∈ nhds r := by
      refine inter_mem (inter_mem (Ioo_mem_nhds hr.1.1 hr.1.2) ?_) ?_
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont1) (hr.2.2 1 (by decide))
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont2) (hr.2.2 2 (by decide))
    rcases mem_nhds_iff_exists_Ioo_subset.mp hU with ⟨a, b, hrab, hsub⟩
    have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite (lt_trans hrab.1 hrab.2)
    have hsubset : Set.Ioo a b ⊆ Side u v 0 := by
      intro s hs
      have hsU := hsub hs
      refine ⟨hsU.1.1, ?_, ?_⟩
      · simpa using hconst s
      · intro j hj
        fin_cases j
        · exact False.elim (hj rfl)
        · exact hsU.1.2
        · exact hsU.2
    exact hinf.not_finite ((hfiniteSide 0).subset hsubset)
  · dsimp [Side, L] at hr
    have hcont0 : Continuous fun t : ℝ => L u v 0 t := by
      dsimp [L]
      continuity
    have hcont2 : Continuous fun t : ℝ => L u v 2 t := by
      dsimp [L]
      continuity
    have hU :
        (Set.Ioo (0 : ℝ) 1 ∩ {t : ℝ | 0 < L u v 0 t} ∩
            {t : ℝ | 0 < L u v 2 t}) ∈ nhds r := by
      refine inter_mem (inter_mem (Ioo_mem_nhds hr.1.1 hr.1.2) ?_) ?_
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont0) (hr.2.2 0 (by decide))
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont2) (hr.2.2 2 (by decide))
    rcases mem_nhds_iff_exists_Ioo_subset.mp hU with ⟨a, b, hrab, hsub⟩
    have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite (lt_trans hrab.1 hrab.2)
    have hsubset : Set.Ioo a b ⊆ Side u v 1 := by
      intro s hs
      have hsU := hsub hs
      refine ⟨hsU.1.1, ?_, ?_⟩
      · simpa using hconst s
      · intro j hj
        fin_cases j
        · exact hsU.1.2
        · exact False.elim (hj rfl)
        · exact hsU.2
    exact hinf.not_finite ((hfiniteSide 1).subset hsubset)
  · dsimp [Side, L] at hr
    have hcont0 : Continuous fun t : ℝ => L u v 0 t := by
      dsimp [L]
      continuity
    have hcont1 : Continuous fun t : ℝ => L u v 1 t := by
      dsimp [L]
      continuity
    have hU :
        (Set.Ioo (0 : ℝ) 1 ∩ {t : ℝ | 0 < L u v 0 t} ∩
            {t : ℝ | 0 < L u v 1 t}) ∈ nhds r := by
      refine inter_mem (inter_mem (Ioo_mem_nhds hr.1.1 hr.1.2) ?_) ?_
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont0) (hr.2.2 0 (by decide))
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const hcont1) (hr.2.2 1 (by decide))
    rcases mem_nhds_iff_exists_Ioo_subset.mp hU with ⟨a, b, hrab, hsub⟩
    have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite (lt_trans hrab.1 hrab.2)
    have hsubset : Set.Ioo a b ⊆ Side u v 2 := by
      intro s hs
      have hsU := hsub hs
      refine ⟨hsU.1.1, ?_, ?_⟩
      · simpa using hconst s
      · intro j hj
        fin_cases j
        · exact hsU.1.2
        · exact hsU.2
        · exact False.elim (hj rfl)
    exact hinf.not_finite ((hfiniteSide 2).subset hsubset)
