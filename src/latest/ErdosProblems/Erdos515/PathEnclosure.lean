/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.PlanarEnclosure
import ErdosProblems.Erdos515.SimplyConnectedSublevel
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Jordan enclosure and simple connectivity in the complex plane

This transports the planar square-chain enclosure theorem to complex-valued paths and closes
the simple-connectivity seam in the sublevel-component argument.
-/

open Set
open unitInterval

namespace Erdos515

/-- A complex path carried by an open set is enclosed by a planar Jordan curve whose transported
carrier remains in the open set. -/
theorem exists_complexJordan_enclosure_of_path
    {D : Set ℂ} (hD : IsOpen D) {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ D) :
    ∃ C : Set Schoenflies.Plane, Schoenflies.IsJordanCurve C ∧
      range p ⊆ complexJordanCarrier C ∪ complexJordanInside C ∧
      complexJordanCarrier C ⊆ D := by
  let pPlane : C(I, Schoenflies.Plane) :=
    ⟨fun t => complexPlaneEquiv (p t), complexPlaneEquiv.continuous.comp p.continuous⟩
  let α : ℝ → Schoenflies.Plane := ContinuousMap.IccExtendCM pPlane
  have hα : ContinuousOn α I :=
    (ContinuousMap.IccExtendCM pPlane).continuous.continuousOn
  have hα_apply (t : I) : α t = complexPlaneEquiv (p t) := by
    change ContinuousMap.IccExtendCM pPlane (t : ℝ) = complexPlaneEquiv (p t)
    rw [ContinuousMap.IccExtendCM_of_mem t.2]
    simp only [pPlane]
    apply congrArg complexPlaneEquiv
    apply congrArg p
    exact Subtype.ext (by rfl)
  let DPlane : Set Schoenflies.Plane := complexPlaneEquiv '' D
  have hDPlane : IsOpen DPlane := by
    exact complexPlaneEquiv.toHomeomorph.isOpen_image.2 hD
  have hαD : α '' I ⊆ DPlane := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨p ⟨t, ht⟩, hp ⟨t, ht⟩, (hα_apply ⟨t, ht⟩).symm⟩
  obtain ⟨C, hC, hαC, hCD⟩ :=
    Schoenflies.exists_jordan_enclosure_of_continuousOn hDPlane hα hαD
  refine ⟨C, hC, ?_, ?_⟩
  · rintro z ⟨t, rfl⟩
    change complexPlaneEquiv (p t) ∈ C ∪ Schoenflies.inside C
    apply hαC
    exact ⟨(t : ℝ), t.2, hα_apply t⟩
  · intro z hz
    have hzDPlane : complexPlaneEquiv z ∈ DPlane := hCD hz
    obtain ⟨w, hwD, hw⟩ := hzDPlane
    exact complexPlaneEquiv.injective hw ▸ hwD

/-- Strict sublevel components of continuous functions satisfying the bounded-open maximum
principle are simply connected. -/
theorem isSimplyConnected_sublevelComponent_of_maximumPrinciple
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} (ha : u a < c) :
    IsSimplyConnected (sublevelComponent u c a) := by
  apply isSimplyConnected_sublevelComponent_of_jordan_enclosure hu hmax ha
  intro x p hp
  exact exists_complexJordan_enclosure_of_path (isOpen_sublevelComponent hu c a) p hp

end Erdos515
