/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Counting

set_option linter.mathlibStandardSet false

namespace Erdos180

section LineCoordinates

section Coordinates

variable (K : Type*) [Field K]

def symplecticHorizontalVector (x y : K) : SymplecticVector K :=
  ![x, 0, y, 0]

def symplecticAnnihilatorVector (x y : K) : SymplecticVector K :=
  ![0, -y, 0, x]

def symmetricGraphVector (a b c x y : K) : SymplecticVector K :=
  ![x, a * x + b * y, y, b * x + c * y]

lemma symmetricGraphVector_orthogonal
    (a b c x y x' y' : K) :
    standardSymplecticForm K
      (symmetricGraphVector K a b c x y)
      (symmetricGraphVector K a b c x' y') = 0 := by
  simp [standardSymplecticForm, symmetricGraphVector]
  ring

def coordinateCenterLinearMap (x y : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h :=
    h 0 • symplecticHorizontalVector K x y +
      h 1 • symplecticAnnihilatorVector K x y
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, smul_eq_mul] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

lemma coordinateCenterLinearMap_injective
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    Function.Injective (coordinateCenterLinearMap K x y) := by
  intro u v huv
  have hzero := congrFun huv 0
  have hone := congrFun huv 1
  have htwo := congrFun huv 2
  have hthree := congrFun huv 3
  simp [coordinateCenterLinearMap, symplecticHorizontalVector,
    symplecticAnnihilatorVector, smul_eq_mul]
    at hzero hone htwo hthree
  funext i
  fin_cases i
  · rcases hxy with hx | hy
    · exact hzero.resolve_right hx
    · exact htwo.resolve_right hy
  · rcases hxy with hx | hy
    · exact hthree.resolve_right hx
    · exact hone.resolve_right hy

def coordinateCenterLine (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) :
    SymplecticLine K :=
  ⟨LinearMap.range (coordinateCenterLinearMap K x y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (coordinateCenterLinearMap_injective K hxy)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [coordinateCenterLinearMap, standardSymplecticForm,
        symplecticHorizontalVector, symplecticAnnihilatorVector,
        smul_eq_mul]
      ring⟩

def symmetricGraphLinearMap (a b c : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h := symmetricGraphVector K a b c (h 0) (h 1)
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.add_apply] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.smul_apply, smul_eq_mul] <;> ring

lemma symmetricGraphLinearMap_injective
    (a b c : K) :
    Function.Injective (symmetricGraphLinearMap K a b c) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 0
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 2

def symmetricGraphLine (a b c : K) : SymplecticLine K :=
  ⟨LinearMap.range (symmetricGraphLinearMap K a b c), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symmetricGraphLinearMap_injective K a b c)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact symmetricGraphVector_orthogonal K a b c
        (u' 0) (u' 1) (v' 0) (v' 1)⟩

lemma symmetricGraphVector_mem_center_span_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ s t : K,
      symmetricGraphVector K a b c x y =
        s • symplecticHorizontalVector K x y +
          t • symplecticAnnihilatorVector K x y) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨s, t, hvector⟩
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hs : s = 1 := by
      rcases hxy with hx | hy
      · have hproduct : (s - 1) * x = 0 := by
          linear_combination -hzero
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hx)
      · have hproduct : (s - 1) * y = 0 := by
          linear_combination -htwo
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hy)
    subst s
    rw [symmetricQuadratic_eq_bilinear]
    linear_combination x * hone + y * hthree
  · intro hquadratic
    have hbilinear :
        x * (a * x + b * y) + y * (b * x + c * y) = 0 := by
      simpa [symmetricQuadratic_eq_bilinear] using hquadratic
    rcases hxy with hx | hy
    · refine ⟨1, (b * x + c * y) / x, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hx]
        linear_combination hbilinear
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hx]
    · refine ⟨1, -(a * x + b * y) / y, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hy]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hy]
        linear_combination hbilinear

lemma symmetricGraphLine_coordinateCenter_intersection_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ w : SymplecticVector K,
      w ≠ 0 ∧ w ∈ (symmetricGraphLine K a b c).1 ∧
        w ∈ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨w, hw, hgraph, hcenter⟩
    obtain ⟨u, hu⟩ := hgraph
    obtain ⟨d, hd⟩ := hcenter
    have hvector :
        symmetricGraphVector K a b c (u 0) (u 1) =
          d 0 • symplecticHorizontalVector K x y +
            d 1 • symplecticAnnihilatorVector K x y := by
      exact hu.trans hd.symm
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hdnonzero : d 0 ≠ 0 := by
      intro hd0
      have hu0 : u 0 = 0 := by
        simpa [hd0] using hzero
      have hu1 : u 1 = 0 := by
        simpa [hd0] using htwo
      apply hw
      rw [← hu]
      change symmetricGraphVector K a b c (u 0) (u 1) = 0
      funext i
      fin_cases i <;> simp [symmetricGraphVector, hu0, hu1]
    have hproduct : d 0 * symmetricQuadratic a b c x y = 0 := by
      rw [symmetricQuadratic_eq_bilinear]
      linear_combination x * hone + y * hthree -
        (a * x + b * y) * hzero -
        (b * x + c * y) * htwo
    exact (mul_eq_zero.mp hproduct).resolve_left hdnonzero
  · intro hquadratic
    obtain ⟨s, t, hvector⟩ :=
      (symmetricGraphVector_mem_center_span_iff K hxy).mpr hquadratic
    refine ⟨symmetricGraphVector K a b c x y, ?_, ?_, ?_⟩
    · intro hzero
      rcases hxy with hx | hy
      · apply hx
        simpa [symmetricGraphVector] using congrFun hzero 0
      · apply hy
        simpa [symmetricGraphVector] using congrFun hzero 2
    · refine ⟨![x, y], ?_⟩
      simp [symmetricGraphLinearMap, symmetricGraphVector]
    · refine ⟨![s, t], ?_⟩
      simpa [coordinateCenterLinearMap] using hvector.symm

lemma symmetricGraphLine_coordinateCenter_common_point_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  rw [← symmetricGraphLine_coordinateCenter_intersection_iff K hxy]
  constructor
  · rintro ⟨p, hpgraph, hpcenter⟩
    have hpbot : p.1 ≠ ⊥ := by
      intro hbot
      have hrank := p.2
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨w, hw, hwne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hpbot
    exact ⟨w, hwne, hpgraph hw, hpcenter hw⟩
  · rintro ⟨w, hwne, hwgraph, hwcenter⟩
    let p : SymplecticPoint K :=
      ⟨K ∙ w, finrank_span_singleton hwne⟩
    refine ⟨p, ?_, ?_⟩
    · exact (Submodule.span_le).mpr (by simpa using hwgraph)
    · exact (Submodule.span_le).mpr (by simpa using hwcenter)

lemma projectiveDirection_nonzero_left
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]

lemma projectiveDirection_nonzero_right
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]

lemma symmetricGraphLine_odd_no_three_actual_centers
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by
  apply symmetricQuadratic_no_three_roots_of_det_ne_zero
    htwo hdet h01 h02 h12
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K h01)).mp hcenter₀
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h01)).mp hcenter₁
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h02)).mp hcenter₂

lemma symmetricGraphLines_disjoint_of_difference_det
    {a b c a' b' c' : K}
    (hdet : symmetricDet (a - a') (b - b') (c - c') ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by
  apply Submodule.disjoint_def.mpr
  intro w hw hw'
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hw'
  have hvector :
      symmetricGraphVector K a b c (u 0) (u 1) =
        symmetricGraphVector K a' b' c' (v 0) (v 1) := by
    exact hu.trans hv.symm
  have hzero := congrFun hvector 0
  have htwo := congrFun hvector 2
  simp [symmetricGraphVector] at hzero htwo
  have huv : u = v := by
    funext i
    fin_cases i
    · exact hzero
    · exact htwo
  subst v
  have hone := congrFun hvector 1
  have hthree := congrFun hvector 3
  simp [symmetricGraphVector] at hone hthree
  have hdetx :
      symmetricDet (a - a') (b - b') (c - c') * u 0 = 0 := by
    unfold symmetricDet
    linear_combination (c - c') * hone - (b - b') * hthree
  have hdety :
      symmetricDet (a - a') (b - b') (c - c') * u 1 = 0 := by
    unfold symmetricDet
    linear_combination -(b - b') * hone + (a - a') * hthree
  have hx : u 0 = 0 :=
    (mul_eq_zero.mp hdetx).resolve_left hdet
  have hy : u 1 = 0 :=
    (mul_eq_zero.mp hdety).resolve_left hdet
  rw [← hu]
  change symmetricGraphVector K a b c (u 0) (u 1) = 0
  funext i
  fin_cases i <;> simp [symmetricGraphVector, hx, hy]

theorem symmetricGraphLine_zero_diagonal_disjoint
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by
  apply symmetricGraphLines_disjoint_of_difference_det K
  simpa using symmetricDet_zero_diagonal_sub_ne_zero h

section CharacteristicTwo

variable [CharP K 2] [Finite K]

lemma symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
    {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x y
            (projectiveDirection_nonzero_left K hind)).1)
    (hsecond : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x' y'
            (projectiveDirection_nonzero_right K hind)).1) :
    a = 0 ∧ c = 0 := by
  apply symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    hind
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K hind)).mp hfirst
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K hind)).mp hsecond

end CharacteristicTwo

end Coordinates

end LineCoordinates

section ArbitraryLineNormalization

open SimpleGraph

variable (K : Type*) [Field K]

abbrev SymplecticAutomorphism :=
  (standardSymplecticBilin K).IsometryEquiv
    (standardSymplecticBilin K)

lemma symplecticAutomorphism_form
    (e : SymplecticAutomorphism K)
    (u v : SymplecticVector K) :
    standardSymplecticForm K (e u) (e v) =
      standardSymplecticForm K u v := by
  change
    standardSymplecticBilin K (e u) (e v) =
      standardSymplecticBilin K u v
  exact e.map_app' u v

def symplecticAutomorphismPoint
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) : SymplecticPoint K :=
  ⟨p.1.map e.toLinearEquiv.toLinearMap,
    (e.toLinearEquiv.finrank_map_eq p.1).trans p.2⟩

def symplecticAutomorphismLine
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) : SymplecticLine K := by
  refine ⟨L.1.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · exact (e.toLinearEquiv.finrank_map_eq L.1).trans L.2.1
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_map.mp hu)
    obtain ⟨v', hv', rfl⟩ := (Submodule.mem_map.mp hv)
    change standardSymplecticForm K (e u') (e v') = 0
    exact (symplecticAutomorphism_form K e u' v').trans
      (L.2.2 u' hu' v' hv')

lemma symplecticAutomorphism_incidence_iff
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by
  change
    p.1.map e.toLinearEquiv.toLinearMap ≤
      L.1.map e.toLinearEquiv.toLinearMap ↔ p.1 ≤ L.1
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective)

lemma symplecticAutomorphism_isotropic_iff
    (e : SymplecticAutomorphism K)
    (S : Submodule K (SymplecticVector K)) :
    (∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
      ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
        standardSymplecticForm K u v = 0) ↔
      (∀ u ∈ S, ∀ v ∈ S,
        standardSymplecticForm K u v = 0) := by
  constructor
  · intro h u hu v hv
    have hmap := h (e u) (Submodule.mem_map_of_mem hu)
      (e v) (Submodule.mem_map_of_mem hv)
    exact (symplecticAutomorphism_form K e u v).symm.trans hmap
  · intro h u hu v hv
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    exact (symplecticAutomorphism_form K e u' v').trans
      (h u' hu' v' hv')

def symplecticAutomorphismLineEquiv
    (e : SymplecticAutomorphism K) :
    SymplecticLine K ≃ SymplecticLine K :=
  (Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv
    (fun S => by
      change
        (Module.finrank K S = 2 ∧
          ∀ u ∈ S, ∀ v ∈ S,
            standardSymplecticForm K u v = 0) ↔
        (Module.finrank K
            (S.map e.toLinearEquiv.toLinearMap) = 2 ∧
          ∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
            ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
              standardSymplecticForm K u v = 0)
      rw [e.toLinearEquiv.finrank_map_eq,
        symplecticAutomorphism_isotropic_iff K e S])

@[simp]
lemma symplecticAutomorphismLineEquiv_apply
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by
  apply Subtype.ext
  rfl

lemma symplecticLine_orthogonal_eq
    (L : SymplecticLine K) :
    (standardSymplecticBilin K).orthogonal L.1 = L.1 := by
  have hle :
      L.1 ≤ (standardSymplecticBilin K).orthogonal L.1 := by
    intro u hu
    change ∀ v ∈ L.1, standardSymplecticForm K v u = 0
    intro v hv
    exact L.2.2 v hv u hu
  have hdim :
      Module.finrank K
        ((standardSymplecticBilin K).orthogonal L.1) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal
      (standardSymplecticBilin_nondegenerate K), L.2.1]
    simp [SymplecticVector]
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (L.2.1.trans hdim.symm)).symm

lemma symplecticLine_isCompl_of_disjoint
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) : IsCompl L.1 M.1 := by
  apply (Submodule.isCompl_iff_disjoint L.1 M.1 ?_).mpr hLM
  simp [SymplecticVector, L.2.1, M.2.1]

def symplecticLinePairing
    (L M : SymplecticLine K) :
    M.1 →ₗ[K] Module.Dual K L.1 where
  toFun y :=
    { toFun := fun x =>
        standardSymplecticForm K
          (x : SymplecticVector K) (y : SymplecticVector K)
      map_add' := by
        intro x x'
        simpa using standardSymplecticForm_add_left K
          (x : SymplecticVector K)
          (x' : SymplecticVector K)
          (y : SymplecticVector K)
      map_smul' := by
        intro c x
        simpa [smul_eq_mul] using
          standardSymplecticForm_smul_left K c
            (x : SymplecticVector K)
            (y : SymplecticVector K) }
  map_add' := by
    intro y y'
    apply LinearMap.ext
    intro x
    simpa using standardSymplecticForm_add_right K
      (x : SymplecticVector K)
      (y : SymplecticVector K)
      (y' : SymplecticVector K)
  map_smul' := by
    intro c y
    apply LinearMap.ext
    intro x
    simpa [smul_eq_mul] using
      standardSymplecticForm_smul_right K c
        (x : SymplecticVector K)
        (y : SymplecticVector K)

lemma symplecticLinePairing_injective
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) :
    Function.Injective (symplecticLinePairing K L M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro y hy
    have hpair : symplecticLinePairing K L M y = 0 := by
      exact LinearMap.mem_ker.mp hy
    have hyorth :
        (y : SymplecticVector K) ∈
          (standardSymplecticBilin K).orthogonal L.1 := by
      change
        ∀ x ∈ L.1,
          standardSymplecticForm K x
            (y : SymplecticVector K) = 0
      intro x hx
      have hz := DFunLike.congr_fun hpair (⟨x, hx⟩ : L.1)
      simpa [symplecticLinePairing] using hz
    have hyL : (y : SymplecticVector K) ∈ L.1 := by
      rw [symplecticLine_orthogonal_eq K L] at hyorth
      exact hyorth
    have hyzero : (y : SymplecticVector K) = 0 := by
      have hbot :
          (y : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hLM.le_bot ⟨hyL, y.2⟩
      simpa using hbot
    have hyzero' : y = 0 := by
      apply Subtype.ext
      simpa using hyzero
    exact (Submodule.mem_bot K).2 hyzero'
  · exact bot_le

lemma symplecticLinePairing_finrank
    (L M : SymplecticLine K) :
    Module.finrank K M.1 =
      Module.finrank K (Module.Dual K L.1) := by
  rw [Subspace.dual_finrank_eq, L.2.1, M.2.1]

noncomputable def symplecticLinePairingEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] Module.Dual K L.1 :=
  (symplecticLinePairing K L M).linearEquivOfInjective
    (symplecticLinePairing_injective K hLM)
    (symplecticLinePairing_finrank K L M)

noncomputable def symplecticLineBasis
    (L : SymplecticLine K) : Module.Basis (Fin 2) K L.1 :=
  Module.finBasisOfFinrankEq K L.1 L.2.1

noncomputable def symplecticLineDualCoordinates
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] (Fin 2 → K) :=
  (symplecticLinePairingEquiv K L M hLM).trans
    (symplecticLineBasis K L).dualBasis.equivFun

@[simp]
lemma symplecticLineDualCoordinates_apply
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) (i : Fin 2) :
    symplecticLineDualCoordinates K L M hLM y i =
      standardSymplecticForm K
        ((symplecticLineBasis K L i : L.1) : SymplecticVector K)
        (y : SymplecticVector K) := by
  change
    (symplecticLineBasis K L).dualBasis.equivFun
        (symplecticLinePairingEquiv K L M hLM y) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  rfl

def symplecticCoordinateInterleave :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] SymplecticVector K where
  toFun x := ![x.1 0, x.2 0, x.1 1, x.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp [smul_eq_mul]

noncomputable def symplecticLineCoordinateEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticVector K ≃ₗ[K] SymplecticVector K :=
  ((L.1.prodEquivOfIsCompl M.1
      (symplecticLine_isCompl_of_disjoint K hLM)).symm.trans
      ((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))).trans
      (symplecticCoordinateInterleave K)

lemma symplecticLinePairing_coordinate_expansion
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
  let b := symplecticLineBasis K L
  have hsum :
      (∑ i : Fin 2, b.equivFun x i • b i) = x :=
    b.sum_equivFun x
  calc
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
        symplecticLinePairing K L M y x := rfl
    _ = symplecticLinePairing K L M y
          (∑ i : Fin 2, b.equivFun x i • b i) :=
      congrArg (symplecticLinePairing K L M y) hsum.symm
    _ = ∑ i : Fin 2,
          b.equivFun x i *
            standardSymplecticForm K
              ((b i : L.1) : SymplecticVector K)
              (y : SymplecticVector K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul, symplecticLinePairing]
    _ = (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
      simp [Fin.sum_univ_two, b,
        symplecticLineDualCoordinates_apply]

lemma symplecticLineCoordinateEquiv_apply_add
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    symplecticLineCoordinateEquiv K L M hLM
        ((x : SymplecticVector K) + (y : SymplecticVector K)) =
      ![(symplecticLineBasis K L).equivFun x 0,
        symplecticLineDualCoordinates K L M hLM y 0,
        (symplecticLineBasis K L).equivFun x 1,
        symplecticLineDualCoordinates K L M hLM y 1] := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  have hsplit :
      (L.1.prodEquivOfIsCompl M.1 hcompl).symm
        ((x : SymplecticVector K) +
          (y : SymplecticVector K)) = (x, y) := by
    apply (L.1.prodEquivOfIsCompl M.1 hcompl).symm_apply_eq.mpr
    rfl
  change
    symplecticCoordinateInterleave K
      (((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))
        ((L.1.prodEquivOfIsCompl M.1 hcompl).symm
          ((x : SymplecticVector K) +
            (y : SymplecticVector K)))) = _
  rw [hsplit]
  rfl

lemma symplecticLineCoordinateEquiv_form
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (u v : SymplecticVector K) :
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM u)
        (symplecticLineCoordinateEquiv K L M hLM v) =
      standardSymplecticForm K u v := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  obtain ⟨⟨x, y⟩, hu⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective u
  obtain ⟨⟨x', y'⟩, hv⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective v
  rw [← hu, ← hv]
  change
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K))
  calc
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y' 0 -
        symplecticLineDualCoordinates K L M hLM y 0 *
          (symplecticLineBasis K L).equivFun x' 0 +
        ((symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y' 1 -
        symplecticLineDualCoordinates K L M hLM y 1 *
          (symplecticLineBasis K L).equivFun x' 1) := by
        simp [symplecticLineCoordinateEquiv_apply_add,
          standardSymplecticForm]
    _ = standardSymplecticForm K
          (x : SymplecticVector K) (y' : SymplecticVector K) -
        standardSymplecticForm K
          (x' : SymplecticVector K) (y : SymplecticVector K) := by
        rw [symplecticLinePairing_coordinate_expansion K L M hLM x y',
          symplecticLinePairing_coordinate_expansion K L M hLM x' y]
        ring
    _ = standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K)) := by
        have hxx :
            standardSymplecticForm K
              (x : SymplecticVector K)
              (x' : SymplecticVector K) = 0 :=
          L.2.2 x x.2 x' x'.2
        have hyy :
            standardSymplecticForm K
              (y : SymplecticVector K)
              (y' : SymplecticVector K) = 0 :=
          M.2.2 y y.2 y' y'.2
        rw [standardSymplecticForm_add_left,
          standardSymplecticForm_add_right,
          standardSymplecticForm_add_right,
          hxx, hyy,
          standardSymplecticForm_swap K
            (y : SymplecticVector K)
            (x' : SymplecticVector K)]
        ring

noncomputable def symplecticLineNormalizer
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticAutomorphism K :=
  { symplecticLineCoordinateEquiv K L M hLM with
    map_app' := by
      intro u v
      change
        standardSymplecticForm K
            (symplecticLineCoordinateEquiv K L M hLM u)
            (symplecticLineCoordinateEquiv K L M hLM v) =
          standardSymplecticForm K u v
      exact symplecticLineCoordinateEquiv_form K L M hLM u v }

lemma symplecticLineNormalizer_apply_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) :
    symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    x (0 : M.1)
  simpa [standardSymplecticForm] using h

lemma symplecticLineNormalizer_apply_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) :
    symplecticLineNormalizer K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    (0 : L.1) y
  simpa using h

def symplecticVerticalLinearMap :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun y := ![0, y 0, 0, y 1]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticVerticalLinearMap_injective :
    Function.Injective (symplecticVerticalLinearMap K) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symplecticVerticalLinearMap] using congrFun huv 1
  · simpa [symplecticVerticalLinearMap] using congrFun huv 3

def symplecticVerticalLine : SymplecticLine K :=
  ⟨LinearMap.range (symplecticVerticalLinearMap K), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symplecticVerticalLinearMap_injective K)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [symplecticVerticalLinearMap,
        standardSymplecticForm]⟩

lemma symplecticLineNormalizer_map_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by
  apply Subtype.ext
  change
    L.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨(symplecticLineBasis K L).equivFun ⟨x, hx⟩, ?_⟩
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (symplecticLineNormalizer_apply_left K L M hLM
        (⟨x, hx⟩ : L.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let x : L.1 := (symplecticLineBasis K L).equivFun.symm z
    refine Submodule.mem_map.mpr
      ⟨(x : SymplecticVector K), x.2, ?_⟩
    simpa [x, symmetricGraphLinearMap, symmetricGraphVector] using
      symplecticLineNormalizer_apply_left K L M hLM x

lemma symplecticLineNormalizer_map_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) M =
      symplecticVerticalLine K := by
  apply Subtype.ext
  change
    M.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symplecticVerticalLinearMap K)
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨symplecticLineDualCoordinates K L M hLM ⟨y, hy⟩, ?_⟩
    simpa [symplecticVerticalLinearMap] using
      (symplecticLineNormalizer_apply_right K L M hLM
        (⟨y, hy⟩ : M.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let y : M.1 :=
      (symplecticLineDualCoordinates K L M hLM).symm z
    refine Submodule.mem_map.mpr
      ⟨(y : SymplecticVector K), y.2, ?_⟩
    change
      symplecticLineNormalizer K L M hLM
          (y : SymplecticVector K) =
        symplecticVerticalLinearMap K z
    rw [symplecticLineNormalizer_apply_right]
    change
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] =
        ![0, z 0, 0, z 1]
    have hy : symplecticLineDualCoordinates K L M hLM y = z :=
      (symplecticLineDualCoordinates K L M hLM).apply_symm_apply z
    rw [hy]

def symplecticHorizontalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 0, v 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticVerticalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, v 3]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticHorizontalProjection_ker :
    LinearMap.ker (symplecticHorizontalProjection K) =
      (symplecticVerticalLine K).1 := by
  apply le_antisymm
  · intro v hv
    have hzero := LinearMap.mem_ker.mp hv
    have hfirst := congrFun hzero 0
    have hthird := congrFun hzero 1
    simp [symplecticHorizontalProjection] at hfirst hthird
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K)
    refine ⟨![v 1, v 3], ?_⟩
    funext i
    fin_cases i <;>
      simp [symplecticVerticalLinearMap, hfirst, hthird]
  · intro v hv
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
    obtain ⟨y, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalProjection,
        symplecticVerticalLinearMap]

lemma symplecticLineHorizontalProjection_injective
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    Function.Injective
      ((symplecticHorizontalProjection K).comp L.1.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hproj := LinearMap.mem_ker.mp hx
    change
      symplecticHorizontalProjection K
          (x : SymplecticVector K) = 0 at hproj
    have hxvertical :
        (x : SymplecticVector K) ∈
          (symplecticVerticalLine K).1 := by
      rw [← symplecticHorizontalProjection_ker K]
      exact LinearMap.mem_ker.mpr hproj
    have hxzero : (x : SymplecticVector K) = 0 := by
      have hbot :
          (x : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hvertical.le_bot ⟨x.2, hxvertical⟩
      simpa using hbot
    have hxsub : x = 0 := by
      apply Subtype.ext
      simpa using hxzero
    exact (Submodule.mem_bot K).2 hxsub
  · exact bot_le

noncomputable def symplecticLineHorizontalProjectionEquiv
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    L.1 ≃ₗ[K] (Fin 2 → K) :=
  ((symplecticHorizontalProjection K).comp L.1.subtype).linearEquivOfInjective
      (symplecticLineHorizontalProjection_injective K L hvertical)
      (by simp [L.2.1])

noncomputable def symplecticLineGraphMap
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (symplecticVerticalProjection K).comp
    (L.1.subtype.comp
      (symplecticLineHorizontalProjectionEquiv K L hvertical).symm.toLinearMap)

lemma symplecticLineGraphMap_horizontal
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by
  change
    symplecticVerticalProjection K
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm
        (symplecticLineHorizontalProjectionEquiv K L hvertical x) :
          SymplecticVector K) = _
  rw [LinearEquiv.symm_apply_apply]

lemma symplecticLineGraphMap_symmetric
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    symplecticLineGraphMap K L hvertical ![1, 0] 1 =
      symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![1, 0]
  let v : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![0, 1]
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = ![1, 0] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u =
        ![1, 0]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![1, 0]
  have hv :
      symplecticHorizontalProjection K
        (v : SymplecticVector K) = ![0, 1] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical v =
        ![0, 1]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![0, 1]
  have hu0 : (u : SymplecticVector K) 0 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 0
  have hu2 : (u : SymplecticVector K) 2 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 1
  have hv0 : (v : SymplecticVector K) 0 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 0
  have hv2 : (v : SymplecticVector K) 2 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 1
  have hu3 :
      (u : SymplecticVector K) 3 =
        symplecticLineGraphMap K L hvertical ![1, 0] 1 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical u) 1
    rw [hu] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hv1 :
      (v : SymplecticVector K) 1 =
        symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical v) 0
    rw [hv] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hpair := L.2.2
    (u : SymplecticVector K) u.2
    (v : SymplecticVector K) v.2
  have hzero :
      symplecticLineGraphMap K L hvertical ![0, 1] 0 -
        symplecticLineGraphMap K L hvertical ![1, 0] 1 = 0 := by
    rw [sub_eq_add_neg]
    simpa [standardSymplecticForm, hu0, hu2, hv0, hv2,
      hu3, hv1] using hpair
  exact (sub_eq_zero.mp hzero).symm

lemma symplecticLineGraphMap_coordinate_expansion
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) (i : Fin 2) :
    symplecticLineGraphMap K L hvertical z i =
      symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext j
    fin_cases j <;> simp [smul_eq_mul]
  calc
    symplecticLineGraphMap K L hvertical z i =
        symplecticLineGraphMap K L hvertical
          (z 0 • ![1, 0] + z 1 • ![0, 1]) i := by
      rw [← hz]
    _ = symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
      rw [map_add, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

lemma symplecticLineGraphMap_graphVector
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) :
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm z :
        SymplecticVector K) := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = z := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u = z
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply z
  have hg :
      symplecticLineGraphMap K L hvertical z =
        symplecticVerticalProjection K
          (u : SymplecticVector K) := by
    rw [← hu]
    exact symplecticLineGraphMap_horizontal K L hvertical u
  change
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      (u : SymplecticVector K)
  funext i
  fin_cases i
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 0).symm
  · have hg0 := congrFun hg 0
    change
      symplecticLineGraphMap K L hvertical z 0 =
        (u : SymplecticVector K) 1 at hg0
    change
      symplecticLineGraphMap K L hvertical ![1, 0] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 1 =
        (u : SymplecticVector K) 1
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 0).symm.trans hg0
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 1).symm
  · have hg1 := congrFun hg 1
    change
      symplecticLineGraphMap K L hvertical z 1 =
        (u : SymplecticVector K) 3 at hg1
    change
      symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 1 * z 1 =
        (u : SymplecticVector K) 3
    rw [← symplecticLineGraphMap_symmetric K L hvertical]
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 1).symm.trans hg1

lemma symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    ∃ a b c : K, L = symmetricGraphLine K a b c := by
  let a := symplecticLineGraphMap K L hvertical ![1, 0] 0
  let b := symplecticLineGraphMap K L hvertical ![0, 1] 0
  let c := symplecticLineGraphMap K L hvertical ![0, 1] 1
  refine ⟨a, b, c, ?_⟩
  apply Subtype.ext
  change L.1 = LinearMap.range (symmetricGraphLinearMap K a b c)
  apply le_antisymm
  · intro w hw
    let x : L.1 := ⟨w, hw⟩
    let z := symplecticHorizontalProjection K
      (w : SymplecticVector K)
    refine ⟨z, ?_⟩
    change symmetricGraphVector K a b c (z 0) (z 1) = w
    have hgraph := symplecticLineGraphMap_graphVector
      K L hvertical z
    have hpreimage :
        (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z =
          x := by
      apply
        (symplecticLineHorizontalProjectionEquiv K L hvertical).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) = w
    rw [hgraph, hpreimage]
  · intro w hw
    obtain ⟨z, rfl⟩ := hw
    change
      symmetricGraphVector K a b c (z 0) (z 1) ∈ L.1
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) ∈ L.1
    rw [symplecticLineGraphMap_graphVector K L hvertical z]
    exact ((symplecticLineHorizontalProjectionEquiv
      K L hvertical).symm z).2

lemma symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
    (a b c : K)
    (hhorizontal :
      Disjoint (symmetricGraphLine K a b c).1
        (symmetricGraphLine K 0 0 0).1) :
    symmetricDet a b c ≠ 0 := by
  intro hdet
  have hkernel :
      ∃ x y : K,
        (x ≠ 0 ∨ y ≠ 0) ∧
          a * x + b * y = 0 ∧
          b * x + c * y = 0 := by
    by_cases ha : a = 0
    · have hb : b = 0 := by
        have hsq : b ^ 2 = 0 := by
          simpa [symmetricDet, ha] using hdet
        exact eq_zero_of_pow_eq_zero hsq
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha, hb],
        by simp [hb]⟩
    · refine ⟨b, -a, Or.inr (neg_ne_zero.mpr ha), ?_, ?_⟩
      · ring
      · unfold symmetricDet at hdet
        linear_combination -hdet
  obtain ⟨x, y, hnonzero, hfirst, hsecond⟩ := hkernel
  let w := symmetricGraphVector K a b c x y
  have hwgraph : w ∈ (symmetricGraphLine K a b c).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K a b c)
    exact ⟨![x, y], rfl⟩
  have hwhorizontal : w ∈ (symmetricGraphLine K 0 0 0).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    refine ⟨![x, y], ?_⟩
    funext i
    fin_cases i <;>
      simp [symmetricGraphLinearMap, symmetricGraphVector,
        w, hfirst, hsecond]
  have hwzero : w = (0 : SymplecticVector K) := by
    have hbot : w ∈ (⊥ : Submodule K (SymplecticVector K)) :=
      hhorizontal.le_bot ⟨hwgraph, hwhorizontal⟩
    simpa using hbot
  have hxzero : x = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 0
  have hyzero : y = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 2
  exact hnonzero.elim (fun h => h hxzero) (fun h => h hyzero)

lemma symplecticLine_eq_invertible_symmetricGraphLine
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (hhorizontal :
      Disjoint L.1 (symmetricGraphLine K 0 0 0).1) :
    ∃ a b c : K,
      L = symmetricGraphLine K a b c ∧
        symmetricDet a b c ≠ 0 := by
  obtain ⟨a, b, c, hL⟩ :=
    symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
      K L hvertical
  refine ⟨a, b, c, hL, ?_⟩
  apply symmetricGraphLine_det_ne_zero_of_disjoint_horizontal K a b c
  rw [← hL]
  exact hhorizontal

lemma symplecticCanonicalLines_disjoint :
    Disjoint (symmetricGraphLine K 0 0 0).1
      (symplecticVerticalLine K).1 := by
  apply Submodule.disjoint_def.mpr
  intro w hwH hwV
  change w ∈ LinearMap.range
    (symmetricGraphLinearMap K 0 0 0) at hwH
  change w ∈ LinearMap.range
    (symplecticVerticalLinearMap K) at hwV
  obtain ⟨z, hz⟩ := hwH
  obtain ⟨t, ht⟩ := hwV
  have heq := hz.trans ht.symm
  have hz0 : z 0 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 0
  have hz1 : z 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 2
  rw [← hz]
  funext i
  fin_cases i <;>
    simp [symmetricGraphLinearMap, symmetricGraphVector,
      hz0, hz1]

lemma symplecticVertical_mem_coordinateCenter_of_orthogonal
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0)
    {v : SymplecticVector K}
    (hv : v ∈ (symplecticVerticalLine K).1)
    (horth : standardSymplecticForm K
      (symplecticHorizontalVector K x y) v = 0) :
    v ∈ (coordinateCenterLine K x y hxy).1 := by
  change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
  obtain ⟨z, hz⟩ := hv
  have hv0 : v 0 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 0).symm
  have hv2 : v 2 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 2).symm
  have heq : x * v 1 + y * v 3 = 0 := by
    simpa [standardSymplecticForm,
      symplecticHorizontalVector] using horth
  change v ∈ LinearMap.range (coordinateCenterLinearMap K x y)
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with h | h
      · exact False.elim (h hx)
      · exact h
    refine ⟨![0, -(v 1 / y)], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hy]
    linear_combination -heq
  · refine ⟨![0, v 3 / x], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hx]
    linear_combination -heq

lemma symplecticLine_eq_coordinateCenterLine_of_common_points
    (C : SymplecticLine K)
    (p q : SymplecticPoint K)
    (hpH : p.1 ≤ (symmetricGraphLine K 0 0 0).1)
    (hpC : p.1 ≤ C.1)
    (hqV : q.1 ≤ (symplecticVerticalLine K).1)
    (hqC : q.1 ≤ C.1) :
    ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
      C = coordinateCenterLine K x y hxy := by
  have hpos : 0 < Module.finrank K p.1 := by
    rw [p.2]
    norm_num
  obtain ⟨u, hu⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have huhorizontal := hpH u.2
  change
    (u : SymplecticVector K) ∈
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    at huhorizontal
  obtain ⟨z, hz⟩ := huhorizontal
  have hu1 : (u : SymplecticVector K) 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 1).symm
  have hu3 : (u : SymplecticVector K) 3 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 3).symm
  let x : K := (u : SymplecticVector K) 0
  let y : K := (u : SymplecticVector K) 2
  have huvector :
      (u : SymplecticVector K) =
        symplecticHorizontalVector K x y := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, x, y, hu1, hu3]
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    have hx : x = 0 :=
      Classical.byContradiction (fun hx => h (Or.inl hx))
    have hy : y = 0 :=
      Classical.byContradiction (fun hy => h (Or.inr hy))
    have huzero : (u : SymplecticVector K) = 0 := by
      rw [huvector, hx, hy]
      simp [symplecticHorizontalVector]
    apply hu
    apply Subtype.ext
    simpa using huzero
  have hpq : p ≠ q := by
    intro heq
    subst q
    have hbot :
        (u : SymplecticVector K) ∈
          (⊥ : Submodule K (SymplecticVector K)) :=
      (symplecticCanonicalLines_disjoint K).le_bot
        ⟨hpH u.2, hqV u.2⟩
    apply hu
    apply Subtype.ext
    simpa using hbot
  have hucenter :
      (u : SymplecticVector K) ∈
        (coordinateCenterLine K x y hxy).1 := by
    change
      (u : SymplecticVector K) ∈
        LinearMap.range (coordinateCenterLinearMap K x y)
    refine ⟨![1, 0], ?_⟩
    rw [huvector]
    simp [coordinateCenterLinearMap,
      symplecticHorizontalVector,
      symplecticAnnihilatorVector, smul_eq_mul]
  have hpcenter :
      p.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hu (⟨v, hv⟩ : p.1)
    have hav : a • (u : SymplecticVector K) = v :=
      congrArg Subtype.val ha
    rw [← hav]
    exact (coordinateCenterLine K x y hxy).1.smul_mem a hucenter
  have hqcenter :
      q.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    apply symplecticVertical_mem_coordinateCenter_of_orthogonal
      K hxy (hqV hv)
    rw [← huvector]
    exact C.2.2 (u : SymplecticVector K)
      (hpC u.2) v (hqC hv)
  refine ⟨x, y, hxy, ?_⟩
  apply Subtype.ext
  have hspanC : p.1 ⊔ q.1 = C.1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpC hqC)
      ((symplecticPoint_sup_finrank K hpq).trans C.2.1.symm)
  have hspanCenter :
      p.1 ⊔ q.1 = (coordinateCenterLine K x y hxy).1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpcenter hqcenter)
      ((symplecticPoint_sup_finrank K hpq).trans
        (coordinateCenterLine K x y hxy).2.1.symm)
  exact hspanC.symm.trans hspanCenter

lemma coordinateCenterLine_direction_det_ne_zero_of_ne
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by
  intro hdet
  have hscale :
      ∃ t : K, t ≠ 0 ∧ x' = t * x ∧ y' = t * y := by
    rcases hxy with hx | hy
    · let t : K := x' / x
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hx]
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hx]
        linear_combination hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
    · let t : K := y' / y
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hy]
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hy]
        linear_combination -hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
  obtain ⟨t, ht, hfirst, hsecond⟩ := hscale
  apply hne
  apply Subtype.ext
  change
    LinearMap.range (coordinateCenterLinearMap K x y) =
      LinearMap.range (coordinateCenterLinearMap K x' y')
  have hmap (u : Fin 2 → K) :
      coordinateCenterLinearMap K x' y' u =
        t • coordinateCenterLinearMap K x y u := by
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hfirst, hsecond] <;>
      ring
  apply le_antisymm
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t⁻¹ • u, ?_⟩
    rw [hmap, map_smul]
    simp [ht]
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t • u, ?_⟩
    rw [map_smul, ← hmap]

lemma symplecticAutomorphism_disjoint_iff
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by
  change
    Disjoint (L.1.map e.toLinearEquiv.toLinearMap)
        (M.1.map e.toLinearEquiv.toLinearMap) ↔
      Disjoint L.1 M.1
  rw [disjoint_iff,
    ← Submodule.map_inf e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective,
    Submodule.map_eq_bot_iff,
    ← disjoint_iff]

lemma symplecticCanonical_line_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (X : SymplecticLine K)
    (hXH :
      Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV :
      Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  classical
  obtain ⟨a, b, c, hXgraph, hdet⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine
      K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 3) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hdir {i j : Fin 3} (hij : i ≠ j) :
      x i * y j - x j * y i ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy i) (hxy j)
    intro heq
    apply hij
    apply hcenters
    exact (hrepr i).trans (heq.trans (hrepr j).symm)
  have h01 : x 0 * y 1 - x 1 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 1)
  have h02 : x 0 * y 2 - x 2 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 2)
  have h12 : x 1 * y 2 - x 2 * y 1 ≠ 0 :=
    hdir (by decide : (1 : Fin 3) ≠ 2)
  apply symmetricGraphLine_odd_no_three_actual_centers K
    htwo hdet h01 h02 h12
  · obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 2
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 2]
      exact hpC

theorem symplecticLine_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (Y Z X : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hY : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (centers i).1)
    (hZ : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  have hleft :
      symplecticAutomorphismLine K e Y =
        symmetricGraphLine K 0 0 0 := by
    exact symplecticLineNormalizer_map_left K Y Z hYZ
  have hright :
      symplecticAutomorphismLine K e Z =
        symplecticVerticalLine K := by
    exact symplecticLineNormalizer_map_right K Y Z hYZ
  apply symplecticCanonical_line_no_three_common_centers K htwo
    (symplecticAutomorphismLine K e X)
    (centers := fun i =>
      symplecticAutomorphismLine K e (centers i))
  · rw [← hleft]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  · rw [← hright]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  · intro i j hij
    apply hcenters
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  · intro i
    obtain ⟨p, hpY, hpC⟩ := hY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hleft]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpZ, hpC⟩ := hZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hright]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpX, hpC⟩ := hX i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · exact (symplecticAutomorphism_incidence_iff K e p X).mpr hpX
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC

theorem symplecticQuadrangle_no_line_gamma_of_odd
    (htwo : (2 : K) ≠ 0)
    (copy : SimpleGraph.Copy gammaGraph
      (symplecticQuadrangle K))
    (C : SymplecticLine K)
    (hC : copy kSpecifiedCenter = .inr C) :
    False := by
  classical
  have hspecified :
      copy (.inl (.inr (0 : Fin 3))) = .inr C := by
    simpa [kSpecifiedCenter] using hC
  have hbase_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inl i)) = .inr L :=
    subdivisionLine_base_of_line_center K copy
      (base := i) (center := (0 : Fin 3)) hspecified
  choose bases hbase using hbase_exists
  have hcenter_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K copy
      (base := (0 : Fin 3)) (center := i) (hbase 0)
  choose centers hcenter using hcenter_exists
  apply symplecticLine_no_three_common_centers K htwo
    (bases 1) (bases 2) (bases 0)
    (centers := centers)
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (1 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 1) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_centers_injective K copy centers hcenter
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 1) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 2) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 0) (hcenter i)
    exact ⟨p, hpB, hpC⟩

theorem symplecticQuadrangle_no_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (quotientGraph kTemplate f).Free
      (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  let hom : kTemplate →g symplecticQuadrangle K :=
    copy.toHom.comp (kQuotientProjectionHom hf)
  have hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = i} := by
    intro i u hu v hv huv
    change
      copy (⟨f u, u, rfl⟩ : Set.range f) =
        copy (⟨f v, v, rfl⟩ : Set.range f)
      at huv
    apply hf.2 i hu hv
    exact congrArg Subtype.val (copy.injective huv)
  obtain ⟨i, L, hL⟩ :=
    symplecticQuadrangle_kTemplate_has_line_gamma
      K hom hcopies
  exact symplecticQuadrangle_no_line_gamma_of_odd K htwo
    (kGammaHomCopy hom hcopies i) L hL

theorem symplecticQuadrangle_encodeFiniteGraph_free_iff
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) :=
  (SimpleGraph.free_congr_left
    (SimpleGraph.Iso.map (Fintype.equivFin V) G)).symm

theorem symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  (symplecticQuadrangle_encodeFiniteGraph_free_iff K
    (quotientGraph kTemplate f)).mpr
    (symplecticQuadrangle_no_kQuotient_of_odd K htwo hf)

end ArbitraryLineNormalization

end Erdos180
