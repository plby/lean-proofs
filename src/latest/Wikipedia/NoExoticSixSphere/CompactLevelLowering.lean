import Wikipedia.NoExoticSixSphere.CompactEnergyBand
import Wikipedia.NoExoticSixSphere.LoweringBudgets
import Wikipedia.NoExoticSixSphere.FiniteLoweringSequence

/-!
# Lowering across a whole compact energy level

Pointwise quantitative lowering data suffice to construct a relative homotopy
across a small band. Compactness supplies the finite cores, their movement
margins, the common energy window, and the band. Every finite-sequence input
is discharged here; no global lowering homotopy is assumed.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [CompactSpace M]
  [PseudoMetricSpace Y] [T2Space Y] [LocallyCompactSpace Y]

theorem exists_compact_level_lowering (energy : Y → ℝ) (admissible : Set Y)
    (henergy : ContinuousOn energy admissible) (S : Set Y) (hS : IsCompact S)
    (hSsub : S ⊆ admissible) (floor level cap : ℝ)
    (hfloor : floor < level) (hcap : level < cap)
    (hsublevel : ∀ y ∈ admissible, energy y ≤ cap → y ∈ S)
    (hlocal : ∀ y ∈ S, energy y = level →
      ∃ D : LocalLoweringData M energy admissible floor level cap, y ∈ D.domain) :
    ∃ a > 0, floor < level - a ∧ level + a < cap ∧
      ∀ p : C(M, Y), (∀ x, p x ∈ admissible) → (∀ x, energy (p x) ≤ level + a / 4) →
      ∃ q : C(M, Y), (∀ x, energy (q x) < level - a / 2) ∧
        ∃ G : ContinuousMap.HomotopyRel p q {x | energy (p x) ≤ floor},
          ∀ t x, G (t, x) ∈ admissible ∧ energy (G (t, x)) ≤ cap := by
  classical
  let K := S ∩ energy ⁻¹' {level}
  have hK : IsCompact K := hS.of_isClosed_subset
    ((henergy.mono hSsub).preimage_isClosed_of_isClosed hS.isClosed isClosed_singleton)
    inter_subset_left
  obtain ⟨n, D, F, hF, hcover⟩ := exists_finite_lowering_cover K hK
    (fun y hy ↦ hlocal y hy.1 hy.2)
  obtain ⟨ρ, hρ, ζ, hζ, hfit, hstep⟩ := exists_common_lowering_control n D F hF
  let U := ⋃ i, interior (F i)
  have hU : IsOpen U := isOpen_iUnion (fun _ ↦ isOpen_interior)
  obtain ⟨b, hb, hband⟩ := exists_energy_band_in_open energy S hS (henergy.mono hSsub)
    level U hU (fun y hy he ↦ hcover ⟨hy, he⟩)
  obtain ⟨a, ha, ξ, hξ, hafloor, hacap, hab, hξζ, hbudget, hgap, hthreshold⟩ :=
    exists_lowering_budgets n (fun i ↦ (D i).threshold) floor level cap ζ b
      hfloor hcap hζ hb (fun i ↦ (D i).threshold_lt_level)
  refine ⟨a, ha, hafloor, hacap, ?_⟩
  intro p hp hstart
  have hpcap (x) : energy (p x) ≤ cap := by have := hstart x; linarith
  let Fn : ℕ → Set Y := fun j ↦ if hj : j < n then F ⟨j, hj⟩ else ∅
  let Vn : ℕ → Set Y := fun j ↦ if hj : j < n then (D ⟨j, hj⟩).domain else ∅
  let kn : ℕ → ℝ := fun j ↦ if hj : j < n then (D ⟨j, hj⟩).threshold else 0
  have hFn (j : ℕ) (hj : j < n) : Fn j = F ⟨j, hj⟩ := dif_pos hj
  have hVn (j : ℕ) (hj : j < n) : Vn j = (D ⟨j, hj⟩).domain := dif_pos hj
  have hkn (j : ℕ) (hj : j < n) : kn j = (D ⟨j, hj⟩).threshold := dif_pos hj
  have hcompact : ∀ j < n, IsCompact (Fn j) := by
    intro j hj
    rw [hFn j hj]
    exact (hF ⟨j, hj⟩).1
  have hfitn : ∀ j < n, ∀ y ∈ Fn j, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ Vn j := by
    intro j hj
    rw [hFn j hj, hVn j hj]
    exact hfit ⟨j, hj⟩
  have hstepn : ∀ j < n, StepProperty (M := M) energy admissible (Vn j)
      floor (kn j) cap ξ ζ ρ := by
    intro j hj
    rw [hVn j hj, hkn j hj]
    exact hstep ξ hξ hξζ ⟨j, hj⟩
  have hthresholdn : ∀ j < n, kn j + (n : ℝ) * ξ ≤ level - a / 2 := by
    intro j hj
    rw [hkn j hj]
    exact hthreshold ⟨j, hj⟩
  have hcovern : ∀ x, level - a ≤ energy (p x) → ∃ j < n, p x ∈ Fn j := by
    intro x hx
    have hpx : p x ∈ U := hband (p x) (hsublevel (p x) (hp x) (hpcap x)) (by
      apply (abs_le.mpr ⟨?_, ?_⟩).trans hab
      · linarith
      · have := hstart x; linarith)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpx
    exact ⟨i.val, i.isLt, by rw [hFn i.val i.isLt]; exact interior_subset hi⟩
  obtain ⟨q, hq, G, hG⟩ := exists_finite_lowering energy admissible henergy p hp
    n Fn Vn kn floor (level - a) (level + a / 4) cap ξ ζ ρ (level - a / 2)
    hξ.le hρ.le hstart hbudget hcompact hfitn hstepn hgap hthresholdn hcovern
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, ?_⟩⟩
  exact (hG t x).2.trans (max_le (hpcap x) le_rfl)

end NoExoticSixSphere.FiniteControlledLowering
