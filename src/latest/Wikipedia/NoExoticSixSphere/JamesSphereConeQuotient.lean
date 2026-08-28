import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageCone
import Wikipedia.NoExoticSixSphere.ContractedQuotientEquivalence
import Mathlib.Analysis.Convex.Contractible

/-!
# The actual cone-collapse map is a homotopy equivalence

The collapse identifies precisely the embedded attached disk. The
original sphere inclusion has homotopy extension, hence so does the
attached disk inclusion. Extending a disk contraction gives a homotopy
preserving that disk and constant on it at the endpoint. The checked
quotient construction then supplies a homotopy inverse to the actual
collapse map, whose restriction remains the original James quotient.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric Topology
open scoped unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

theorem base_mem_cone_iff (n : ℕ) (w : SecondStage.Space n) :
    base n w ∈ Set.range (cone n) ↔ w ∈ StageAttachment.lower n 1 := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨s, hs, _⟩ := ClosedPushout.overlap_witness (isPushout n)
      PuncturedCellAttachment.boundary_injective w d hd.symm
    have hm : attaching n s ∈ StageAttachment.lower n 1 :=
      James.size_letter_le (spherePole n) s
    exact hs ▸ hm
  · intro hw
    let v : James.stage (spherePole n) 1 := ⟨w.val, hw⟩
    let s := (FirstStage.homeomorph n).symm v
    have hs : attaching n s = w :=
      Subtype.ext (congrArg (fun z : James.stage (spherePole n) 1 ↦ z.val)
        ((FirstStage.homeomorph n).apply_symm_apply v))
    exact ⟨PuncturedCellAttachment.boundary s, (cone_boundary n s).trans (congrArg (base n) hs)⟩

theorem quotient_eq_basepoint_iff (n : ℕ) (w : SecondStage.Space n) :
    SecondStage.quotientMap n w = quotientBasepoint n ↔ w ∈ StageAttachment.lower n 1 := by
  constructor
  · intro h
    rcases (SecondStage.quotientMap_eq_iff n w ⟨1, Nat.zero_le 2⟩).mp h with he | ⟨hw, _⟩
    · rw [he]
      exact Nat.zero_le 1
    · exact hw
  · intro hw
    exact (SecondStage.quotientMap_eq_iff n _ _).mpr (Or.inr ⟨hw, Nat.zero_le 1⟩)

theorem collapse_eq_basepoint_iff (n : ℕ) (z : Space n) :
    collapse n z = quotientBasepoint n ↔ z ∈ Set.range (cone n) := by
  rcases CompactCellAttachment.space_cases (attaching n) z with ⟨w, rfl⟩ | ⟨d, rfl⟩
  · change collapse n (base n w) = quotientBasepoint n ↔ base n w ∈ Set.range (cone n)
    rw [collapse_base, quotient_eq_basepoint_iff, base_mem_cone_iff]
  · exact iff_of_true (collapse_cone n d) (Set.mem_range_self d)

theorem collapse_eq_iff (n : ℕ) (x y : Space n) :
    collapse n x = collapse n y ↔ x = y ∨ x ∈ Set.range (cone n) ∧ y ∈ Set.range (cone n) := by
  constructor
  · intro h
    by_cases hx : x ∈ Set.range (cone n)
    · exact Or.inr ⟨hx, (collapse_eq_basepoint_iff n y).mp
        (h.symm.trans ((collapse_eq_basepoint_iff n x).mpr hx))⟩
    · have hy : y ∉ Set.range (cone n) := by
        intro hy
        exact hx ((collapse_eq_basepoint_iff n x).mp
          (h.trans ((collapse_eq_basepoint_iff n y).mpr hy)))
      obtain ⟨w, rfl⟩ := (CompactCellAttachment.space_cases (attaching n) x).resolve_right hx
      obtain ⟨z, rfl⟩ := (CompactCellAttachment.space_cases (attaching n) y).resolve_right hy
      change collapse n (base n w) = collapse n (base n z) at h
      rw [collapse_base, collapse_base] at h
      rcases (SecondStage.quotientMap_eq_iff n w z).mp h with he | ⟨hw, _⟩
      · exact Or.inl (congrArg (base n) he)
      · exact False.elim (hx ((base_mem_cone_iff n w).mpr hw))
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · exact ((collapse_eq_basepoint_iff n x).mpr hx).trans
        ((collapse_eq_basepoint_iff n y).mpr hy).symm

theorem collapse_surjective (n : ℕ) : Function.Surjective (collapse n) := by
  intro z
  refine Quotient.inductionOn z (fun w ↦ ?_)
  exact ⟨base n w, collapse_base n w⟩

theorem collapse_isQuotientMap (n : ℕ) : IsQuotientMap (collapse n) := by
  let : T2Space (SecondStage.QuotientSpace n) := (SecondStage.quotientHomeomorph n).symm.t2Space
  exact IsQuotientMap.of_surjective_continuous (collapse_surjective n) (collapse n).continuous

theorem attaching_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (TopCat.ofHom (attaching n)) := by
  have he : TopCat.ofHom (attaching n) =
      (TopCat.isoOfHomeo (FirstStage.homeomorph n)).hom ≫ StageAttachment.inclusion n 1 := rfl
  rw [he]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (StageAttachment.hasHomotopyExtension n 1)

theorem cone_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (TopCat.ofHom (cone n)) :=
  HomotopyExtension.of_pushout (isPushout n).flip (attaching_hasHomotopyExtension n)

theorem exists_extended_contraction (n : ℕ) :
    ∃ a : Space n, ∃ g : C(Space n, Space n), ∃ H : (ContinuousMap.id (Space n)).Homotopy g,
      (∀ x ∈ Set.range (cone n), g x = a) ∧
      ∀ t x, x ∈ Set.range (cone n) → H (t, x) ∈ Set.range (cone n) := by
  let D := CompactCellAttachment.Disk (ConeCoordinates n)
  let : ContractibleSpace D := (convex_closedBall (0 : ConeCoordinates n) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨a, ⟨K⟩⟩ := id_nullhomotopic D
  let G := (cone n).comp K.toContinuousMap
  have hG : ∀ d, G (0, d) = (ContinuousMap.id (Space n)) (cone n d) := by
    intro d
    change cone n (K (0, d)) = cone n d
    rw [K.apply_zero]
    rfl
  obtain ⟨L, hL0, hLC⟩ := cone_hasHomotopyExtension n (TopCat.of (Space n))
    (ContinuousMap.id (Space n)) G hG
  have hLC' : ∀ t d, L (t, cone n d) = G (t, d) := hLC
  let g : C(Space n, Space n) := ⟨fun x ↦ L (1, x),
    L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : (ContinuousMap.id (Space n)).Homotopy g :=
    ⟨L, hL0, fun _ ↦ rfl⟩
  refine ⟨cone n a, g, H, ?_, ?_⟩
  · rintro x ⟨d, rfl⟩
    change L (1, cone n d) = cone n a
    rw [hLC']
    change cone n (K (1, d)) = cone n a
    rw [K.apply_one]
    rfl
  · rintro t x ⟨d, rfl⟩
    change L (t, cone n d) ∈ Set.range (cone n)
    rw [hLC']
    exact Set.mem_range_self (K (t, d))

theorem collapse_homotopyEquivalence (n : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv (Space n) (SecondStage.QuotientSpace n),
      e.toFun = collapse n := by
  let : T2Space (SecondStage.QuotientSpace n) := (SecondStage.quotientHomeomorph n).symm.t2Space
  obtain ⟨a, g, H, hg, hH⟩ := exists_extended_contraction n
  exact ⟨ContractedQuotient.homotopyEquiv (collapse n) (collapse_isQuotientMap n)
    (Set.range (cone n)) (collapse_eq_iff n) a hg H hH, rfl⟩

end NoExoticSixSphere.JamesSphere.SecondStageCone
