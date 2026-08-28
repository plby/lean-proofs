import Wikipedia.NoExoticSixSphere.ChartFamilyCutoff
import Wikipedia.NoExoticSixSphere.CutoffHomotopyGluing
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Localizing a relative crossing to part of a parameter family

A crossing theorem for families entirely in one chart neighborhood extends to
arbitrary families: move only a selected compact parameter set and a surrounding
region whose original image lies in a smaller chart neighborhood. A cutoff
extension supplies the auxiliary family, and a supported time cutoff glues its
crossing homotopy back to the original family.
-/

open Set unitInterval
open scoped Topology

namespace NoExoticSixSphere

variable {M Y E : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_relational_localization_neighborhood
    (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (W : Set Y)
    (hW : IsOpen W) (hcenter : e.symm 0 ∈ W)
    :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ (energy : Y → ℝ) (admissible : Set Y) (l k cap : ℝ) (R : Y → Y → Prop),
        (∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q S,
                ∀ t x, H (t, x) ∈ admissible ∧ energy (H (t, x)) < cap ∧
                  R (p x) (H (t, x))) →
      ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
        ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x ∈ K, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, H (t, x) ∈ admissible ∧
                  energy (H (t, x)) ≤ max (energy (p x)) cap ∧
                    (H (t, x) = p x ∨ R (p x) (H (t, x))) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((e.open_target.inter (hW.preimage hinv)).mem_nhds ⟨hzero, hcenter⟩)
  let V := e.source ∩ e ⁻¹' Metric.ball 0 r
  have hV : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
  have hcenterV : e.symm 0 ∈ V := ⟨e.map_target hzero, by
    change e (e.symm 0) ∈ Metric.ball 0 r
    rw [e.right_inv hzero]
    exact Metric.mem_ball_self hr⟩
  have hVW : V ⊆ W := by
    intro y hy
    have hh := (hball hy.2).2
    change e.symm (e y) ∈ W at hh
    rwa [e.left_inv hy.1] at hh
  refine ⟨V, hV, hcenterV, hVW, ?_⟩
  intro energy admissible l k cap R hcross p hp K hK hKV S hS hLow
  let A := p ⁻¹' V
  have hA : IsOpen A := hV.preimage p.continuous
  obtain ⟨β, hβsupport, hβone, hβbound⟩ := exists_tsupport_one_of_isOpen_isClosed hA
    isClosed_closure.isCompact hK.isClosed hKV
  have hcoord : ContinuousOn (fun x ↦ e (p x)) A :=
    e.continuousOn.comp p.continuous.continuousOn (fun x hx ↦ hx.1)
  obtain ⟨u, huAgree, huBall⟩ := ChartFamilyCutoff.exists_extension (fun x ↦ e (p x))
    A hA hcoord (tsupport β) (isClosed_tsupport β) hβsupport r hr (fun x hx ↦ hx.2)
  let aux : C(M, Y) := ⟨fun x ↦ e.symm (u x), hinv.comp u.continuous⟩
  have hauxW (x) : aux x ∈ W := (hball (huBall x)).2
  have hAgree : EqOn aux p (tsupport β) := by
    intro x hx
    change e.symm (u x) = p x
    rw [huAgree hx]
    exact e.left_inv (hβsupport hx).1
  obtain ⟨qaux, hqaux, Haux, hHaux⟩ := hcross aux hauxW (S ∩ tsupport β)
    (hS.inter_right (isClosed_tsupport β)) (fun x hx ↦ by
      rw [hAgree hx.2]
      exact hLow x hx.1)
  have hFixed : ∀ t x, x ∈ (S ∪ Aᶜ) ∩ tsupport β → Haux (t, x) = aux x := by
    intro t x hx
    rcases hx.1 with hxS | hxA
    · exact Haux.eq_fst t ⟨hxS, hx.2⟩
    · exact (hxA (hβsupport hx.2)).elim
  let q := CutoffHomotopyGluing.endpoint Haux.toHomotopy p β hβbound hAgree
  let H := CutoffHomotopyGluing.homotopy Haux.toHomotopy p β hβbound hAgree hFixed
  refine ⟨q, fun x hx ↦ ?_, H, fun t x ↦ ?_⟩
  · change energy (CutoffHomotopyGluing.map Haux.toHomotopy p β hβbound hAgree (1, x)) < k
    rw [CutoffHomotopyGluing.map_one_of_one Haux.toHomotopy p β hβbound hAgree (hβone hx)]
    exact hqaux x
  · change CutoffHomotopyGluing.map Haux.toHomotopy p β hβbound hAgree (t, x) ∈ admissible ∧
      energy (CutoffHomotopyGluing.map Haux.toHomotopy p β hβbound hAgree (t, x)) ≤
        max (energy (p x)) cap ∧
      (CutoffHomotopyGluing.map Haux.toHomotopy p β hβbound hAgree (t, x) = p x ∨
        R (p x) (CutoffHomotopyGluing.map Haux.toHomotopy p β hβbound hAgree (t, x)))
    by_cases hx : x ∈ tsupport β
    · rw [CutoffHomotopyGluing.map_of_mem Haux.toHomotopy p β hβbound hAgree hx]
      refine ⟨(hHaux _ x).1, (hHaux _ x).2.1.le.trans (le_max_right _ _), Or.inr ?_⟩
      change R (p x) (Haux (CutoffHomotopyGluing.clock β hβbound (t, x), x))
      rw [← hAgree hx]
      exact (hHaux _ x).2.2
    · rw [CutoffHomotopyGluing.map_of_notMem Haux.toHomotopy p β hβbound hAgree hx]
      exact ⟨hp x, le_max_left _ _, Or.inl rfl⟩

theorem localize_crossing_controlled (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (energy : Y → ℝ) (admissible W control : Set Y)
    (hW : IsOpen W) (hcenter : e.symm 0 ∈ W)
    (l k cap : ℝ)
    (hcross : ∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
      ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
        ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
          ∃ H : ContinuousMap.HomotopyRel p q S,
            ∀ t x, H (t, x) ∈ admissible ∧ energy (H (t, x)) < cap ∧ H (t, x) ∈ control) :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
        ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x ∈ K, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, H (t, x) ∈ admissible ∧
                  energy (H (t, x)) ≤ max (energy (p x)) cap ∧
                    (H (t, x) = p x ∨ H (t, x) ∈ control) := by
  obtain ⟨V, hV, hcenterV, hVW, hlocal⟩ :=
    exists_relational_localization_neighborhood (M := M) e hinv hzero W hW hcenter
  exact ⟨V, hV, hcenterV, hVW, hlocal energy admissible l k cap (fun _ y ↦ y ∈ control) hcross⟩

theorem localize_crossing (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (energy : Y → ℝ) (admissible W : Set Y)
    (hW : IsOpen W) (hcenter : e.symm 0 ∈ W)
    (l k cap : ℝ)
    (hcross : ∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
      ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
        ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
          ∃ H : ContinuousMap.HomotopyRel p q S,
            ∀ t x, H (t, x) ∈ admissible ∧ energy (H (t, x)) < cap) :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
        ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x ∈ K, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, H (t, x) ∈ admissible ∧
                  energy (H (t, x)) ≤ max (energy (p x)) cap := by
  obtain ⟨V, hV, hcenterV, hVW, hlocal⟩ := localize_crossing_controlled e hinv hzero energy
    admissible W univ hW hcenter l k cap (fun p hp S hS hLow ↦ by
      obtain ⟨q, hq, H, hH⟩ := hcross p hp S hS hLow
      exact ⟨q, hq, H, fun t x ↦ ⟨(hH t x).1, (hH t x).2, mem_univ _⟩⟩)
  refine ⟨V, hV, hcenterV, hVW, ?_⟩
  intro p hp K hK hKV S hS hLow
  obtain ⟨q, hq, H, hH⟩ := hlocal p hp K hK hKV S hS hLow
  exact ⟨q, hq, H, fun t x ↦ ⟨(hH t x).1, (hH t x).2.1⟩⟩

end NoExoticSixSphere
