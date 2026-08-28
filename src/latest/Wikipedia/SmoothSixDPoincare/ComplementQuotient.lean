import Wikipedia.SmoothSixDPoincare.TransverseNormalLinearMap
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Quotient coordinates and germ-preserving corrections of complementary frames

An actual splitting `(G, C)` defines the quotient by `G` as the second
coordinate of its inverse. A prescribed frame `L` has coefficient `Q ∘ L`.
Replacing only that coefficient constructs a complementary frame while
retaining the entire original frame wherever the coefficient is unchanged.
-/

noncomputable section

open Function

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def complementQuotient (G : D →L[ℝ] F) (C : Z →L[ℝ] F) : F →L[ℝ] Z :=
  (ContinuousLinearMap.snd ℝ D Z).comp (G.coprod C).inverse

theorem complementQuotient_left (G : D →L[ℝ] F) (C : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) (u : D) : complementQuotient G C (G u) = 0 := by
  have hi := h.inverse_apply_self (u, 0)
  change (G.coprod C).inverse (G u + C 0) = (u, 0) at hi
  rw [map_zero, add_zero] at hi
  exact congrArg Prod.snd hi

theorem complementQuotient_right (G : D →L[ℝ] F) (C : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) (v : Z) : complementQuotient G C (C v) = v := by
  have hi := h.inverse_apply_self (0, v)
  change (G.coprod C).inverse (G 0 + C v) = (0, v) at hi
  rw [map_zero, zero_add] at hi
  exact congrArg Prod.snd hi

theorem surjective_complementQuotient (G : D →L[ℝ] F) (C : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) : Surjective (complementQuotient G C) :=
  fun v => ⟨C v, complementQuotient_right G C h v⟩

theorem ker_complementQuotient (G : D →L[ℝ] F) (C : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) : (complementQuotient G C).ker = G.range := by
  ext w
  constructor
  · intro hw
    let p := (G.coprod C).inverse w
    have hp : p.2 = 0 := hw
    have hi := h.self_apply_inverse w
    change G p.1 + C p.2 = w at hi
    rw [hp, map_zero, add_zero] at hi
    exact ⟨p.1, hi⟩
  · rintro ⟨u, rfl⟩
    exact complementQuotient_left G C h u

theorem bijective_coprod_of_quotient (G : D →L[ℝ] F) (C H : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible)
    (hH : Bijective ((complementQuotient G C).comp H)) : Bijective (G.coprod H) := by
  have hG : Injective G := by
    intro u v huv
    have hpair : (G.coprod C) (u, 0) = (G.coprod C) (v, 0) := by
      change G u + C 0 = G v + C 0
      rw [huv]
    exact congrArg Prod.fst (h.injective hpair)
  constructor
  · intro p q hpq
    have hq := congrArg (complementQuotient G C) hpq
    change complementQuotient G C (G p.1 + H p.2) =
      complementQuotient G C (G q.1 + H q.2) at hq
    rw [map_add, map_add, complementQuotient_left G C h,
      complementQuotient_left G C h, zero_add, zero_add] at hq
    have hp₂ : p.2 = q.2 := hH.1 hq
    have hp₁ : p.1 = q.1 := by
      change G p.1 + H p.2 = G q.1 + H q.2 at hpq
      rw [hp₂] at hpq
      exact hG (add_right_cancel hpq)
    exact Prod.ext hp₁ hp₂
  · intro w
    obtain ⟨v, hv⟩ := hH.2 (complementQuotient G C w)
    have hmem : w - H v ∈ G.range := by
      rw [← ker_complementQuotient G C h]
      change complementQuotient G C (w - H v) = 0
      rw [map_sub]
      change complementQuotient G C w - ((complementQuotient G C).comp H) v = 0
      rw [hv, sub_self]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(u, v), ?_⟩
    change G u + H v = w
    change G u = w - H v at hu
    rw [hu, sub_add_cancel]

def correctedComplement (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z) : Z →L[ℝ] F :=
  L + C.comp (K - (complementQuotient G C).comp L)

/-- The correction replaces exactly the quotient coefficient, with no approximation. -/
theorem quotient_correctedComplement (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).comp (correctedComplement G C L K) = K := by
  apply ContinuousLinearMap.ext
  intro v
  change complementQuotient G C (L v + C ((K - (complementQuotient G C).comp L) v)) = K v
  rw [map_add, complementQuotient_right G C h]
  change complementQuotient G C (L v) + (K v - complementQuotient G C (L v)) = K v
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem correctedComplement_self (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) :
    correctedComplement G C L ((complementQuotient G C).comp L) = L := by
  simp only [correctedComplement, sub_self, ContinuousLinearMap.comp_zero, add_zero]

theorem bijective_coprod_correctedComplement
    (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) (hK : Bijective K) :
    Bijective (G.coprod (correctedComplement G C L K)) := by
  apply bijective_coprod_of_quotient G C _ h
  rw [quotient_correctedComplement G C L K h]
  exact hK

variable [FiniteDimensional ℝ Z]

/-- Native corner complementarity gives an invertible quotient coefficient at that corner. -/
theorem bijective_complementCoefficient (G : D →L[ℝ] F) (C L : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) (hL : Surjective (G.coprod L)) :
    Bijective ((complementQuotient G C).comp L) := by
  apply TransverseCoordinates.bijective_normal_comp (complementQuotient G C) G L
    (surjective_complementQuotient G C h) hL _ rfl
  apply ContinuousLinearMap.ext
  intro u
  exact complementQuotient_left G C h u

end Wikipedia.SmoothSixDPoincare.FrameField
