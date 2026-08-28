import Wikipedia.HopfProblem.OrbitPairHomotopyFiberTransportTimes
import Mathlib.Topology.CompactOpen

/-!
# Path-family transport with parameter-dependent terminal points

The same shrinking-prefix formula as the original homotopy-fiber
transport applies before fixing a terminal point. It retains the whole
original path at initial time and keeps each parameter's own terminal
value. This permits transport in the actual homotopy pullback.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.PathFamilyTransport

open Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (F : C(X, Y)) (p : C(Z, C(I, Y))) (H : C(I × Z, X))

def value (s t : I) (z : Z) : Y :=
  if 2 * (t : ℝ) ≤ (s : ℝ) then F (H (reverseTime s t, z))
  else p z (remainingTime s t)

theorem continuous_value (h0 : ∀ z, p z 0 = F (H (0, z))) :
    Continuous (fun z : I × (I × Z) ↦ value F p H z.2.1 z.1 z.2.2) := by
  have hs : Continuous (fun z : I × (I × Z) ↦ z.2.1) := continuous_fst.comp continuous_snd
  have ht : Continuous (fun z : I × (I × Z) ↦ z.1) := continuous_fst
  have hz : Continuous (fun z : I × (I × Z) ↦ z.2.2) := continuous_snd.comp continuous_snd
  have hleft : Continuous (fun z : I × (I × Z) ↦ F (H (reverseTime z.2.1 z.1, z.2.2))) :=
    F.continuous.comp (H.continuous.comp
      ((continuous_reverseTime.comp (hs.prodMk ht)).prodMk hz))
  have hright : Continuous (fun z : I × (I × Z) ↦ p z.2.2 (remainingTime z.2.1 z.1)) :=
    continuous_eval.comp ((p.continuous.comp hz).prodMk
      (continuous_remainingTime.comp (hs.prodMk ht)))
  apply Continuous.if_le hleft hright
    ((continuous_subtype_val.comp ht).const_mul 2) (continuous_subtype_val.comp hs)
  intro z h
  rw [reverseTime_join _ _ h, remainingTime_join _ _ h]
  exact (h0 z.2.2).symm

theorem value_source (s : I) (z : Z) : value F p H s 0 z = F (H (s, z)) := by
  rw [value, if_pos]
  · rw [reverseTime_zero]
  · simpa using s.property.1

theorem value_target (s : I) (z : Z) : value F p H s 1 z = p z 1 := by
  have hs : ¬ 2 * ((1 : I) : ℝ) ≤ (s : ℝ) := by
    have hs := s.property.2
    norm_num
    linarith
  rw [value, if_neg hs, remainingTime_one]

theorem value_initial (h0 : ∀ z, p z 0 = F (H (0, z))) (t : I) (z : Z) :
    value F p H 0 t z = p z t := by
  by_cases ht : t = 0
  · subst t
    exact (value_source F p H 0 z).trans (h0 z).symm
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun he ↦ ht (Subtype.ext he.symm))
    rw [value, if_neg (by simpa using (by linarith : ¬ 2 * (t : ℝ) ≤ 0)),
      remainingTime_zero]

def family (h0 : ∀ z, p z 0 = F (H (0, z))) : C(I × Z, C(I, Y)) :=
  ⟨fun q ↦ ⟨fun t ↦ value F p H q.1 t q.2,
    (continuous_value F p H h0).comp (continuous_id.prodMk continuous_const)⟩,
    ContinuousMap.continuous_of_continuous_uncurry _
      ((continuous_value F p H h0).comp continuous_swap)⟩

theorem family_source (h0 : ∀ z, p z 0 = F (H (0, z))) (s : I) (z : Z) :
    family F p H h0 (s, z) 0 = F (H (s, z)) := value_source F p H s z

theorem family_target (h0 : ∀ z, p z 0 = F (H (0, z))) (s : I) (z : Z) :
    family F p H h0 (s, z) 1 = p z 1 := value_target F p H s z

theorem family_initial (h0 : ∀ z, p z 0 = F (H (0, z))) (z : Z) :
    family F p H h0 (0, z) = p z :=
  ContinuousMap.ext (fun t ↦ value_initial F p H h0 t z)

end NoExoticSixSphere.PathFamilyTransport
