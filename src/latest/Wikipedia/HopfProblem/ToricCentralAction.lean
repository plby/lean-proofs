import Wikipedia.HopfProblem.CuspComponentProjection
import Mathlib.Topology.LocallyFinite

/-!
# Local finiteness of the central components

Only the three vertex components meet a given affine toric chart. The ray
components therefore form a locally finite family. On the central fibre,
the twisted action agrees with a global homeomorphism obtained by freezing
its multiplier at zero. Images of subsets of `E₀` under these homeomorphisms
also form a locally finite family.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem rayDivisors_locallyFinite : LocallyFinite rayDivisor := by
  intro x
  let s := preferredTriangle x
  refine ⟨range (inclusion s), (inclusion_openEmbedding s).isOpen_range.mem_nhds
    (preferred_mem x), ?_⟩
  apply (Set.finite_range s.vertex).subset
  rintro v ⟨y, hy, ⟨z, rfl⟩⟩
  obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hy
  exact ⟨j, hj⟩

def centralTranslationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : Space ≃ₜ Space :=
  (translationHomeomorph (cuspVector v)).trans
    (torusHomeomorph (fibreMultiplier (exponentialMultiplier C v 0)))

@[simp] theorem centralTranslationHomeomorph_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    centralTranslationHomeomorph C v x =
      torusAction (fibreMultiplier (exponentialMultiplier C v 0))
        (translate (cuspVector v) x) := rfl

theorem centralTranslationHomeomorph_eq_twistedTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) (hx : time x = 0) :
    centralTranslationHomeomorph C v x = twistedTranslate C v x := by
  rw [centralTranslationHomeomorph_apply, twistedTranslate, variableMultiplier,
    time_translate, hx]

theorem branchVertices_centralTranslationHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (centralTranslationHomeomorph C v x) =
      (fun w => w + cuspVector v) '' branchVertices x := by
  rw [centralTranslationHomeomorph_apply, branchVertices_torusAction, branchVertices_translate]

theorem centralTranslation_image_subset_rayDivisor
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {K : Set Space}
    (hK : K ⊆ rayDivisor 0) :
    centralTranslationHomeomorph C v '' K ⊆ rayDivisor (cuspVector v) := by
  rintro _ ⟨x, hx, rfl⟩
  change cuspVector v ∈ branchVertices (centralTranslationHomeomorph C v x)
  rw [branchVertices_centralTranslationHomeomorph]
  exact ⟨0, hK hx, zero_add _⟩

theorem centralTranslation_images_locallyFinite
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {K : Set Space} (hK : K ⊆ rayDivisor 0) :
    LocallyFinite (fun v : Fin 2 → ℤ => centralTranslationHomeomorph C v '' K) :=
  (rayDivisors_locallyFinite.comp_injective cuspVector_injective).subset
    (fun v => centralTranslation_image_subset_rayDivisor C v hK)

theorem translate_zero_rayDivisor (v : Fin 2 → ℤ) :
    translate v '' rayDivisor 0 = rayDivisor v := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change v ∈ branchVertices (translate v y)
    rw [branchVertices_translate]
    exact ⟨0, hy, zero_add v⟩
  · intro hx
    refine ⟨translate (-v) x, ?_, ?_⟩
    · change 0 ∈ branchVertices (translate (-v) x)
      rw [branchVertices_translate]
      exact ⟨v, hx, add_neg_cancel v⟩
    · rw [translate_add]
      simp

end Wikipedia.HopfProblem.ToricSpace
