import Wikipedia.NoExoticSixSphere.JamesSpherePairingQuotient
import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration

/-!
# The original second James stage maps onto the smash sphere

The sphere pairing descends through the genuine finite-word presentation.
The descended map collapses exactly the first stage, is injective off that
stage, and factors the original James--Hopf map through the one-letter
inclusion of the target sphere. No relative homotopy comparison is inferred.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.SecondStage

abbrev Space (n : ℕ) := James.stage (spherePole n) 2

def arrayPairing (n : ℕ) : C((Fin 2 → Sphere n), Sphere (n + n)) :=
  ⟨fun v ↦ pairing n (v 0, v 1),
    (pairing n).continuous.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩

theorem arrayPairing_eq_pole_iff (n : ℕ) (v : Fin 2 → Sphere n) :
    arrayPairing n v = spherePole (n + n) ↔
      stagePresentation n 2 v ∈ StageAttachment.lower n 1 := by
  change pairing n (v 0, v 1) = _ ↔
    v ∈ stagePresentation n 2 ⁻¹' StageAttachment.lower n 1
  rw [StageAttachment.boundary_eq, pairing_eq_pole_iff]
  change v 0 = spherePole n ∨ v 1 = spherePole n ↔ ∃ i : Fin 2, v i = spherePole n
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

theorem respects_presentations (n : ℕ) (v w : Fin 2 → Sphere n)
    (h : stagePresentation n 2 v = stagePresentation n 2 w) :
    arrayPairing n v = arrayPairing n w := by
  rcases StageAttachment.fiber_condition n 1 v w h with hv | hvw
  · exact ((arrayPairing_eq_pole_iff n v).mpr hv).trans
      ((arrayPairing_eq_pole_iff n w).mpr (h ▸ hv)).symm
  · exact congrArg (arrayPairing n) hvw

def collapse (n : ℕ) : C(Space n, Sphere (n + n)) :=
  IsQuotientMap.lift (f := stagePresentation n 2) (isQuotientMap_stagePresentation n 2)
    (arrayPairing n) (respects_presentations n)

theorem collapse_presentation (n : ℕ) (v : Fin 2 → Sphere n) :
    collapse n (stagePresentation n 2 v) = arrayPairing n v :=
  ContinuousMap.congr_fun (IsQuotientMap.lift_comp
    (isQuotientMap_stagePresentation n 2) (arrayPairing n) (respects_presentations n)) v

theorem collapse_eq_pole_iff (n : ℕ) (w : Space n) :
    collapse n w = spherePole (n + n) ↔ w ∈ StageAttachment.lower n 1 := by
  obtain ⟨v, rfl⟩ := stagePresentation_surjective n 2 w
  rw [collapse_presentation, arrayPairing_eq_pole_iff]

theorem collapse_fiber_condition (n : ℕ) (w z : Space n)
    (h : collapse n w = collapse n z) : w ∈ StageAttachment.lower n 1 ∨ w = z := by
  obtain ⟨v, rfl⟩ := stagePresentation_surjective n 2 w
  obtain ⟨u, rfl⟩ := stagePresentation_surjective n 2 z
  rw [collapse_presentation, collapse_presentation] at h
  rcases pairing_fiber_condition n (v 0, v 1) (u 0, u 1) h with hv | hvu
  · exact Or.inl ((arrayPairing_eq_pole_iff n v).mp hv)
  · right
    apply congrArg (stagePresentation n 2)
    funext i
    fin_cases i
    · exact congrArg Prod.fst hvu
    · exact congrArg Prod.snd hvu

theorem collapse_surjective (n : ℕ) : Function.Surjective (collapse n) := by
  intro z
  obtain ⟨⟨x, y⟩, hxy⟩ := pairing_surjective n z
  refine ⟨stagePresentation n 2 ![x, y], ?_⟩
  rw [collapse_presentation]
  exact hxy

theorem isQuotientMap_collapse (n : ℕ) : IsQuotientMap (collapse n) :=
  IsQuotientMap.of_surjective_continuous (collapse_surjective n) (collapse n).continuous

theorem hopf_factor (n : ℕ) (w : Space n) :
    hopf n w.val = James.letter (spherePole (n + n)) (collapse n w) := by
  obtain ⟨v, rfl⟩ := stagePresentation_surjective n 2 w
  rw [collapse_presentation]
  change hopf n (James.word (spherePole n) (List.ofFn v)) = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
    James.word_cons, James.word_cons, James.word_nil, mul_one]
  exact hopf_two_letters n (v 0) (v 1)

end NoExoticSixSphere.JamesSphere.SecondStage
