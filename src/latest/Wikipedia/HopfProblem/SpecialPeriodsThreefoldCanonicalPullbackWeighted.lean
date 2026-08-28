import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Weighted product local biholomorphisms

The map `(x, c) ↦ (f x, a x * c)` is a local biholomorphism wherever `f`
is a local biholomorphism and the holomorphic weight `a` is nonzero.
The proof constructs an actual partial diffeomorphism for the original
product manifold atlases.  Its inverse is `(y, c) ↦ (g y, (a (g y))⁻¹ * c)`.
No converse to the inverse-function theorem or transported atlas is used.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M N : Type*}

/-- The natural product map whose fibre map is multiplication by the weight. -/
def weightedMap (f : M → N) (a : M → ℂ) (p : M × ℂ) : N × ℂ :=
  (f p.1, a p.1 * p.2)

@[simp] theorem weightedMap_fst (f : M → N) (a : M → ℂ) (p : M × ℂ) :
    (weightedMap f a p).1 = f p.1 := rfl

@[simp] theorem weightedMap_snd (f : M → N) (a : M → ℂ) (p : M × ℂ) :
    (weightedMap f a p).2 = a p.1 * p.2 := rfl

variable [TopologicalSpace M] [ChartedSpace Model M]
  [TopologicalSpace N] [ChartedSpace Model N]

/-- An explicit local biholomorphism above a base partial biholomorphism.
Both source and target use their ordinary product topologies and atlases. -/
def weightedPartialDiffeomorph
    (e : PartialDiffeomorph I I M N ω) (a : M → ℂ)
    (ha : ContMDiffOn I I₁ ω a e.source)
    (hne : ∀ x ∈ e.source, a x ≠ 0) :
    PartialDiffeomorph ((I).prod I₁) ((I).prod I₁) (M × ℂ) (N × ℂ) ω where
  toFun := weightedMap e a
  invFun p := (e.symm p.1, (a (e.symm p.1))⁻¹ * p.2)
  source := e.source ×ˢ univ
  target := e.target ×ˢ univ
  map_source' p hp := ⟨e.map_source hp.1, mem_univ _⟩
  map_target' p hp := ⟨e.map_target hp.1, mem_univ _⟩
  left_inv' p hp := by
    apply Prod.ext
    · exact e.left_inv hp.1
    · change (a (e.symm (e p.1)))⁻¹ * (a p.1 * p.2) = p.2
      have he : e.symm (e p.1) = p.1 := e.left_inv hp.1
      exact (congrArg (fun x : M => (a x)⁻¹ * (a p.1 * p.2)) he).trans
        (inv_mul_cancel_left₀ (hne p.1 hp.1) p.2)
  right_inv' p hp := by
    apply Prod.ext
    · exact e.right_inv hp.1
    · change a (e.symm p.1) * ((a (e.symm p.1))⁻¹ * p.2) = p.2
      exact mul_inv_cancel_left₀ (hne (e.symm p.1) (e.map_target hp.1)) p.2
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    have hf : ContMDiffOn ((I).prod I₁) I ω
        (fun p : M × ℂ => e p.1) (e.source ×ˢ univ) :=
      e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ hp => hp.1)
    have hw : ContMDiffOn ((I).prod I₁) I₁ ω
        (fun p : M × ℂ => a p.1) (e.source ×ˢ univ) :=
      ha.comp contMDiffOn_fst (fun _ hp => hp.1)
    exact hf.prodMk (hw.mul contMDiffOn_snd)
  contMDiffOn_invFun := by
    have hg : ContMDiffOn ((I).prod I₁) I ω
        (fun p : N × ℂ => e.symm p.1) (e.target ×ˢ univ) :=
      e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ hp => hp.1)
    have hw : ContMDiffOn ((I).prod I₁) I₁ ω
        (fun p : N × ℂ => a (e.symm p.1)) (e.target ×ˢ univ) :=
      ha.comp hg (fun _ hp => e.map_target hp.1)
    exact hg.prodMk ((hw.inv₀ (fun _ hp => hne _ (e.map_target hp.1))).mul
      contMDiffOn_snd)

@[simp] theorem weightedPartialDiffeomorph_source
    (e : PartialDiffeomorph I I M N ω) (a : M → ℂ)
    (ha : ContMDiffOn I I₁ ω a e.source) (hne : ∀ x ∈ e.source, a x ≠ 0) :
    (weightedPartialDiffeomorph e a ha hne).source = e.source ×ˢ univ := rfl

@[simp] theorem weightedPartialDiffeomorph_target
    (e : PartialDiffeomorph I I M N ω) (a : M → ℂ)
    (ha : ContMDiffOn I I₁ ω a e.source) (hne : ∀ x ∈ e.source, a x ≠ 0) :
    (weightedPartialDiffeomorph e a ha hne).target = e.target ×ˢ univ := rfl

@[simp] theorem weightedPartialDiffeomorph_apply
    (e : PartialDiffeomorph I I M N ω) (a : M → ℂ)
    (ha : ContMDiffOn I I₁ ω a e.source) (hne : ∀ x ∈ e.source, a x ≠ 0)
    (p : M × ℂ) :
    weightedPartialDiffeomorph e a ha hne p = (e p.1, a p.1 * p.2) := rfl

@[simp] theorem weightedPartialDiffeomorph_symm_apply
    (e : PartialDiffeomorph I I M N ω) (a : M → ℂ)
    (ha : ContMDiffOn I I₁ ω a e.source) (hne : ∀ x ∈ e.source, a x ≠ 0)
    (p : N × ℂ) :
    (weightedPartialDiffeomorph e a ha hne).symm p =
      (e.symm p.1, (a (e.symm p.1))⁻¹ * p.2) := rfl

private def restrictBase (e : PartialDiffeomorph I I M N ω)
    (s : Set M) (hs : IsOpen s) : PartialDiffeomorph I I M N ω where
  __ := e.toOpenPartialHomeomorph.restrOpen s hs
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono inter_subset_left

variable [IsManifold I ω M]

/-- Nonvanishing holomorphic weights preserve local biholomorphicity of
the base map, in the original product manifold structures. -/
theorem weightedMap_isLocalDiffeomorphAt {f : M → N} {a : M → ℂ} {p : M × ℂ}
    (hf : IsLocalDiffeomorphAt I I ω f p.1)
    (ha : ContMDiffAt I I₁ ω a p.1) (hne : a p.1 ≠ 0) :
    IsLocalDiffeomorphAt ((I).prod I₁) ((I).prod I₁) ω (weightedMap f a) p := by
  obtain ⟨u, hu, hau⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp ha
  have hz : ∀ᶠ x in 𝓝 p.1, a x ≠ 0 := ha.continuousAt.eventually_ne hne
  obtain ⟨s, hs, hso, hps⟩ := mem_nhds_iff.mp (inter_mem hu hz)
  let e := restrictBase hf.choose s hso
  have hase : ContMDiffOn I I₁ ω a e.source :=
    hau.mono (fun x hx => (hs hx.2).1)
  have hnse : ∀ x ∈ e.source, a x ≠ 0 := fun x hx => (hs hx.2).2
  refine ⟨weightedPartialDiffeomorph e a hase hnse,
    ⟨⟨hf.choose_spec.1, hps⟩, mem_univ _⟩, ?_⟩
  intro q hq
  apply Prod.ext
  · exact hf.choose_spec.2 hq.1.1
  · rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
