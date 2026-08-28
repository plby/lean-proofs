import Wikipedia.NoExoticSixSphere.JamesSphereTimeSeparation
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The reduced cone as the actual compact space of generator prefixes

The prefix with letter `x` and length `s` is the curve
`t ↦ loopEvaluation (x, s * t)`. Its only identifications collapse the
basepoint letter and zero length. Thus its compact Hausdorff range is
the actual reduced-cone quotient, with the original sphere embedded as
the full-length prefixes.
-/

noncomputable section

open Set Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.ReducedCone

def prefixCurve (n : ℕ) : C(Sphere n × I, C(I, Sphere (n + 1))) :=
  ((loopEvaluation n).comp
    ⟨fun p : (Sphere n × I) × I ↦ (p.1.1, p.1.2 * p.2),
      continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd)⟩).curry

theorem prefix_apply (n : ℕ) (x : Sphere n) (s t : I) :
    prefixCurve n (x, s) t = loopEvaluation n (x, s * t) := rfl

theorem prefix_zero (n : ℕ) (x : Sphere n) :
    prefixCurve n (x, 0) = ContinuousMap.const I (spherePole (n + 1)) := by
  apply ContinuousMap.ext
  intro t
  rw [prefix_apply, zero_mul, loopEvaluation_zero]
  rfl

theorem prefix_pole (n : ℕ) (s : I) :
    prefixCurve n (spherePole n, s) = ContinuousMap.const I (spherePole (n + 1)) := by
  apply ContinuousMap.ext
  intro t
  exact loopEvaluation_pole n (s * t)

def halfTime (s : I) : I := s * ⟨1 / 2, by constructor <;> norm_num⟩

theorem halfTime_pos (s : I) (hs : s ≠ 0) : 0 < (halfTime s : ℝ) := by
  have hp : 0 < (s : ℝ) := by
    apply lt_of_le_of_ne s.property.1
    intro he
    exact hs (Subtype.ext he.symm)
  change 0 < (s : ℝ) * (1 / 2)
  positivity

theorem halfTime_lt_one (s : I) : (halfTime s : ℝ) < 1 := by
  change (s : ℝ) * (1 / 2) < 1
  have hs := s.property.2
  linarith

theorem prefix_eq_constant_iff (n : ℕ) (x : Sphere n) (s : I) :
    prefixCurve n (x, s) = ContinuousMap.const I (spherePole (n + 1)) ↔
      x = spherePole n ∨ s = 0 := by
  constructor
  · intro h
    by_cases hx : x = spherePole n
    · exact Or.inl hx
    · right
      by_contra hs
      have he := ContinuousMap.congr_fun h (⟨1 / 2, by constructor <;> norm_num⟩ : I)
      exact loopEvaluation_ne_pole n hx (halfTime s) (halfTime_pos s hs)
        (halfTime_lt_one s) he
  · rintro (rfl | rfl)
    · exact prefix_pole n s
    · exact prefix_zero n x

theorem prefix_injective_off_base (n : ℕ) {x y : Sphere n} {s t : I}
    (hx : x ≠ spherePole n) (hs : s ≠ 0) (h : prefixCurve n (x, s) = prefixCurve n (y, t)) :
    x = y ∧ s = t := by
  have he := ContinuousMap.congr_fun h (⟨1 / 2, by constructor <;> norm_num⟩ : I)
  change loopEvaluation n (x, halfTime s) = loopEvaluation n (y, halfTime t) at he
  have ht : halfTime s = halfTime t :=
    loopEvaluation_time_eq n hx (halfTime_pos s hs) (halfTime_lt_one s) he
  have hst : s = t := by
    apply Subtype.ext
    have hv := congrArg Subtype.val ht
    change (s : ℝ) * (1 / 2) = (t : ℝ) * (1 / 2) at hv
    linarith
  refine ⟨?_, hst⟩
  have he' : loopEvaluation n (x, halfTime s) = loopEvaluation n (y, halfTime s) := by
    simpa only [hst] using he
  exact loopEvaluation_injective n (halfTime s)
    (clock_ne_infty _ (halfTime_pos s hs) (halfTime_lt_one s)) he'

theorem prefix_eq_iff (n : ℕ) (p q : Sphere n × I) :
    prefixCurve n p = prefixCurve n q ↔ p = q ∨
      ((p.1 = spherePole n ∨ p.2 = 0) ∧ (q.1 = spherePole n ∨ q.2 = 0)) := by
  constructor
  · intro h
    by_cases hp : p.1 = spherePole n ∨ p.2 = 0
    · exact Or.inr ⟨hp, (prefix_eq_constant_iff n q.1 q.2).mp
        (h.symm.trans ((prefix_eq_constant_iff n p.1 p.2).mpr hp))⟩
    · have hxy := prefix_injective_off_base n
        (fun hx ↦ hp (Or.inl hx)) (fun hs ↦ hp (Or.inr hs)) h
      exact Or.inl (Prod.ext hxy.1 hxy.2)
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · exact ((prefix_eq_constant_iff n p.1 p.2).mpr hp).trans
        ((prefix_eq_constant_iff n q.1 q.2).mpr hq).symm

def space (n : ℕ) : Set C(I, Sphere (n + 1)) := Set.range (prefixCurve n)

abbrev Space (n : ℕ) := ↥(space n)

instance (n : ℕ) : CompactSpace (Space n) :=
  isCompact_iff_compactSpace.mp (isCompact_range (prefixCurve n).continuous)

def presentation (n : ℕ) : C(Sphere n × I, Space n) :=
  ⟨fun p ↦ ⟨prefixCurve n p, Set.mem_range_self p⟩, (prefixCurve n).continuous.subtype_mk _⟩

theorem presentation_surjective (n : ℕ) : Function.Surjective (presentation n) := by
  rintro ⟨p, ⟨q, rfl⟩⟩
  exact ⟨q, rfl⟩

theorem presentation_isQuotientMap (n : ℕ) : IsQuotientMap (presentation n) :=
  IsQuotientMap.of_surjective_continuous (presentation_surjective n) (presentation n).continuous

def base (n : ℕ) : Space n := presentation n (spherePole n, 0)

theorem base_val (n : ℕ) : (base n).val = ContinuousMap.const I (spherePole (n + 1)) :=
  prefix_zero n (spherePole n)

theorem presentation_eq_base_iff (n : ℕ) (p : Sphere n × I) :
    presentation n p = base n ↔ p.1 = spherePole n ∨ p.2 = 0 := by
  rw [Subtype.ext_iff, base_val]
  exact prefix_eq_constant_iff n p.1 p.2

def boundary (n : ℕ) : C(Sphere n, Space n) :=
  (presentation n).comp ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩

theorem boundary_pole (n : ℕ) : boundary n (spherePole n) = base n :=
  (presentation_eq_base_iff n _).mpr (Or.inl rfl)

theorem boundary_injective (n : ℕ) : Function.Injective (boundary n) := by
  intro x y h
  have he : prefixCurve n (x, 1) = prefixCurve n (y, 1) := congrArg Subtype.val h
  rcases (prefix_eq_iff n (x, 1) (y, 1)).mp he with hxy | ⟨hx, hy⟩
  · exact congrArg Prod.fst hxy
  · have hx' : x = spherePole n := hx.resolve_right one_ne_zero
    have hy' : y = spherePole n := hy.resolve_right one_ne_zero
    exact hx'.trans hy'.symm

theorem boundary_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (boundary n) :=
  (boundary n).continuous.isClosedEmbedding (boundary_injective n)

end NoExoticSixSphere.JamesSphere.ReducedCone
