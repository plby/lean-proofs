import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Join
import Mathlib.Tactic

/-!
# Geometric tilings for Erdős problem 633

Triangles are nondegenerate Euclidean triangles in the complex plane. A tiling
covers the entire closed triangle, has pairwise disjoint interiors, and consists
of images of one tile under ambient Euclidean isometries. T-junctions are allowed.
-/

namespace Erdos633

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ
  nondegenerate : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0

def Triangle.carrier (T : Triangle) : Set ℂ := convexHull ℝ {T.a, T.b, T.c}

structure TriangleDissection (P : Triangle) (N : ℕ) where
  tile : Fin N → Triangle
  covers : (⋃ i, (tile i).carrier) = P.carrier
  disjoint : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

structure CongruentTiling (P R : Triangle) (N : ℕ) extends TriangleDissection P N where
  congruent : ∀ i, ∃ f : ℂ ≃ᵢ ℂ, f '' R.carrier = (tile i).carrier

def AdmitsNonsquareTiling (P : Triangle) : Prop :=
  ∃ (N : ℕ) (R : Triangle), ¬ IsSquare N ∧ Nonempty (CongruentTiling P R N)

def canonicalIsosceles (h : ℝ) (hh : h ≠ 0) : Triangle where
  a := ⟨0, h⟩
  b := -1
  c := 1
  nondegenerate := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, sub_zero, zero_sub, neg_zero]
    dsimp
    intro hz
    apply hh
    linarith

def leftHalf (h : ℝ) (hh : h ≠ 0) : Triangle where
  a := ⟨0, h⟩
  b := -1
  c := 0
  nondegenerate := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, sub_zero, zero_sub, neg_zero]
    dsimp
    intro hz
    apply hh
    linarith

def rightHalf (h : ℝ) (hh : h ≠ 0) : Triangle where
  a := ⟨0, h⟩
  b := 0
  c := 1
  nondegenerate := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero, zero_sub]
    dsimp
    intro hz
    apply hh
    linarith

/-- Reflection in the imaginary axis. -/
noncomputable def verticalReflection : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

theorem verticalReflection_apply (z : ℂ) : verticalReflection z = -star z := rfl

theorem real_segment_image (x y : ℝ) :
    Complex.ofReal '' segment ℝ x y = segment ℝ (x : ℂ) (y : ℂ) := by
  exact image_segment ℝ (Complex.ofRealLI.toLinearMap.toAffineMap) x y

theorem base_segment_split :
    segment ℝ (-1 : ℂ) 1 = segment ℝ (-1 : ℂ) 0 ∪ segment ℝ (0 : ℂ) 1 := by
  have hreal : segment ℝ (-1 : ℝ) 1 =
      segment ℝ (-1 : ℝ) 0 ∪ segment ℝ (0 : ℝ) 1 := by
    rw [segment_eq_Icc (by norm_num), segment_eq_Icc (by norm_num),
      segment_eq_Icc (by norm_num)]
    ext x
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · intro hx
      by_cases hx0 : x ≤ 0
      · exact Or.inl ⟨hx.1, hx0⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge hx0), hx.2⟩
    · rintro (hx | hx) <;> constructor <;> linarith [hx.1, hx.2]
  have hi := congrArg (fun s : Set ℝ => Complex.ofReal '' s) hreal
  simpa only [Set.image_union, real_segment_image, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_zero] using hi

theorem canonicalIsosceles_carrier_split (h : ℝ) (hh : h ≠ 0) :
    (canonicalIsosceles h hh).carrier =
      (leftHalf h hh).carrier ∪ (rightHalf h hh).carrier := by
  change convexHull ℝ {⟨0, h⟩, (-1 : ℂ), 1} =
    convexHull ℝ {⟨0, h⟩, (-1 : ℂ), 0} ∪ convexHull ℝ {⟨0, h⟩, (0 : ℂ), 1}
  simp_rw [← convexJoin_singleton_segment]
  rw [base_segment_split, convexJoin_union_right]

theorem verticalReflection_leftHalf (h : ℝ) (hh : h ≠ 0) :
    verticalReflection '' (leftHalf h hh).carrier = (rightHalf h hh).carrier := by
  change verticalReflection.toLinearMap '' convexHull ℝ {⟨0, h⟩, (-1 : ℂ), 0} =
    convexHull ℝ {⟨0, h⟩, (0 : ℂ), 1}
  rw [LinearMap.image_convexHull]
  have hapex : verticalReflection (⟨0, h⟩ : ℂ) = ⟨0, h⟩ := by
    rw [verticalReflection_apply]
    apply Complex.ext <;> simp
  have hm : verticalReflection (-1 : ℂ) = 1 := by rw [verticalReflection_apply]; simp
  have hz : verticalReflection (0 : ℂ) = 0 := by rw [verticalReflection_apply]; simp
  simp only [Set.image_insert_eq, Set.image_singleton]
  change convexHull ℝ {verticalReflection (⟨0, h⟩ : ℂ),
    verticalReflection (-1), verticalReflection 0} = _
  rw [hapex, hm, hz, Set.pair_comm (1 : ℂ) 0]

theorem leftHalf_re_nonpos (h : ℝ) (hh : h ≠ 0) :
    (leftHalf h hh).carrier ⊆ {z : ℂ | z.re ≤ 0} := by
  apply convexHull_min _ (convex_halfSpace_re_le 0)
  intro z hz
  simp only [leftHalf, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> simp

theorem rightHalf_re_nonneg (h : ℝ) (hh : h ≠ 0) :
    (rightHalf h hh).carrier ⊆ {z : ℂ | 0 ≤ z.re} := by
  apply convexHull_min _ (convex_halfSpace_re_ge 0)
  intro z hz
  simp only [rightHalf, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> simp

theorem half_interiors_disjoint (h : ℝ) (hh : h ≠ 0) :
    Disjoint (interior (leftHalf h hh).carrier) (interior (rightHalf h hh).carrier) := by
  apply Set.disjoint_left.mpr
  intro z hzL hzR
  have hL := interior_mono (leftHalf_re_nonpos h hh) hzL
  have hR := interior_mono (rightHalf_re_nonneg h hh) hzR
  rw [Complex.interior_setOfPred_re_le] at hL
  rw [Complex.interior_setOfPred_le_re] at hR
  change z.re < 0 at hL
  change 0 < z.re at hR
  exact (not_lt_of_gt hR) hL

/-- The altitude gives a genuine two-piece congruent tiling of every canonical
isosceles triangle. -/
noncomputable def canonicalIsoscelesTwoTiling (h : ℝ) (hh : h ≠ 0) :
    CongruentTiling (canonicalIsosceles h hh) (leftHalf h hh) 2 where
  tile := ![leftHalf h hh, rightHalf h hh]
  congruent := by
    intro i
    fin_cases i
    · refine ⟨IsometryEquiv.refl ℂ, ?_⟩
      change id '' (leftHalf h hh).carrier = (leftHalf h hh).carrier
      exact Set.image_id _
    · exact ⟨verticalReflection.toIsometryEquiv, verticalReflection_leftHalf h hh⟩
  covers := by
    rw [canonicalIsosceles_carrier_split]
    ext z
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hz | hz)
      · exact ⟨0, hz⟩
      · exact ⟨1, hz⟩
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact half_interiors_disjoint h hh
    · exact (half_interiors_disjoint h hh).symm
    · exact (hij rfl).elim

theorem canonicalIsosceles_admitsNonsquareTiling (h : ℝ) (hh : h ≠ 0) :
    AdmitsNonsquareTiling (canonicalIsosceles h hh) := by
  refine ⟨2, leftHalf h hh, ?_, ⟨canonicalIsoscelesTwoTiling h hh⟩⟩
  norm_num

end Erdos633
