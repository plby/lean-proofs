import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Gluing actual holomorphic extensions from a dense open subset

Local extensions agree on their overlaps because they are continuous and
agree on the dense original domain. Their pointwise chosen values then
equal a fixed holomorphic map on a neighborhood of every point. This
constructs the global holomorphic extension in the original manifold
atlas and proves uniqueness. The local maps are genuine functions, not
an assumed sheaf or a supplied global extension.
-/

noncomputable section

open Function Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExtensionGluing

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- Agreement on a dense open subset forces equality on every overlap
where the two actual functions are continuous. -/
theorem overlap_eq_of_dense (U V W : Opens X) (hU : Dense (U : Set X))
    {f g : X → Y} (hf : ContinuousOn f V) (hg : ContinuousOn g W)
    (heq : ∀ x, x ∈ U → x ∈ V → x ∈ W → f x = g x)
    {x : X} (hxV : x ∈ V) (hxW : x ∈ W) : f x = g x := by
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ U := mem_closure_iff_frequently.mp (hU x)
  have hV : ∀ᶠ y in 𝓝 x, y ∈ V := V.isOpen.mem_nhds hxV
  have hW : ∀ᶠ y in 𝓝 x, y ∈ W := W.isOpen.mem_nhds hxW
  exact tendsto_nhds_unique_of_frequently_eq
    ((hf x hxV).continuousAt (V.isOpen.mem_nhds hxV))
    ((hg x hxW).continuousAt (W.isOpen.mem_nhds hxW))
    ((hfreq.and_eventually (hV.and hW)).mono fun y hy => heq y hy.1 hy.2.1 hy.2.2)

/-- Uniqueness only needs continuity and the proved density of the
original domain. -/
theorem continuous_extension_unique (U : Opens X) (f : U → Y)
    (hU : Dense (U : Set X)) {g h : X → Y} (hg : Continuous g) (hh : Continuous h)
    (hgf : ∀ x : U, g x = f x) (hhf : ∀ x : U, h x = f x) : g = h :=
  Continuous.ext_on hU hg hh fun x hx =>
    (hgf ⟨x, hx⟩).trans (hhf ⟨x, hx⟩).symm

end Topological

section Holomorphic

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local notation "IM" => modelWithCornersSelf ℂ E
local notation "IF" => modelWithCornersSelf ℂ F

/-- Extend a local function by zero outside its open domain. Only its
values on the original domain are used in the gluing construction. -/
def extendLocal (V : Opens M) (h : V → F) : M → F :=
  (Subtype.val : V → M).extend h 0

omit [NormedSpace ℂ F] in
@[simp] theorem extendLocal_apply (V : Opens M) (h : V → F) (x : V) :
    extendLocal V h x = h x :=
  Subtype.val_injective.extend_apply h 0 x

/-- The ambient extension is holomorphic at every point of the original
open domain, for the unchanged inherited subtype atlas. -/
theorem extendLocal_contMDiffAt (V : Opens M) (h : V → F)
    (hh : ContMDiff IM IF ω h) (x : V) :
    ContMDiffAt IM IF ω (extendLocal V h) (x : M) := by
  apply (contMDiffAt_subtype_iff (I := IM) (I' := IF) (x := x)).mp
  simpa only [extendLocal_apply] using hh x

theorem extendLocal_contMDiffOn (V : Opens M) (h : V → F)
    (hh : ContMDiff IM IF ω h) : ContMDiffOn IM IF ω (extendLocal V h) V := by
  intro x hx
  exact (extendLocal_contMDiffAt V h hh ⟨x, hx⟩).contMDiffWithinAt

/-- Restrict an ambient holomorphic map on an open set to that literal
open submanifold. -/
theorem restrict_contMDiff (V : Opens M) (h : M → F)
    (hh : ContMDiffOn IM IF ω h V) : ContMDiff IM IF ω (fun x : V => h x) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr (hh.contMDiffAt (V.isOpen.mem_nhds x.property))

/-- Genuine compatible local extensions on neighborhoods of every point
construct one global holomorphic function. Compatibility on full overlaps
is proved from density; it is not an additional input. -/
theorem exists_holomorphic_extension_of_local (U : Opens M) (f : U → F)
    (hU : Dense (U : Set M))
    (hlocal : ∀ x : M, ∃ V : Opens M, x ∈ V ∧ ∃ h : V → F,
      ContMDiff IM IF ω h ∧ ∀ y : V, ∀ hy : (y : M) ∈ U, h y = f ⟨y, hy⟩) :
    ∃ g : M → F, ContMDiff IM IF ω g ∧ ∀ x : U, g x = f x := by
  classical
  choose V hV h hh hagree using hlocal
  let H (x : M) : M → F := extendLocal (V x) (h x)
  have hH : ∀ x : M, ContMDiffOn IM IF ω (H x) (V x) :=
    fun x => extendLocal_contMDiffOn (V x) (h x) (hh x)
  have hHagree : ∀ x y : M, y ∈ V x → ∀ hy : y ∈ U, H x y = f ⟨y, hy⟩ := by
    intro x y hyV hyU
    exact (extendLocal_apply (V x) (h x) ⟨y, hyV⟩).trans (hagree x ⟨y, hyV⟩ hyU)
  have hcompat : ∀ x x' y : M, y ∈ V x → y ∈ V x' → H x y = H x' y := by
    intro x x' y hy hy'
    exact overlap_eq_of_dense U (V x) (V x') hU
      (hH x).continuousOn (hH x').continuousOn
      (fun z hzU hzV hzW => (hHagree x z hzV hzU).trans (hHagree x' z hzW hzU).symm)
      hy hy'
  let g : M → F := fun x => H x x
  have hgLocal : ∀ x y : M, y ∈ V x → g y = H x y :=
    fun x y hy => hcompat y x y (hV y) hy
  refine ⟨g, ?_, ?_⟩
  · intro x
    apply ((hH x).contMDiffAt ((V x).isOpen.mem_nhds (hV x))).congr_of_eventuallyEq
    filter_upwards [(V x).isOpen.mem_nhds (hV x)] with y hy
    exact hgLocal x y hy
  · intro x
    exact hHagree x x (hV x) x.property

/-- It suffices to construct local extensions at points outside the
original domain; its given holomorphic function supplies the other patches. -/
theorem exists_holomorphic_extension_of_local_outside (U : Opens M) (f : U → F)
    (hf : ContMDiff IM IF ω f) (hU : Dense (U : Set M))
    (hlocal : ∀ x : M, x ∉ U → ∃ V : Opens M, x ∈ V ∧ ∃ h : V → F,
      ContMDiff IM IF ω h ∧ ∀ y : V, ∀ hy : (y : M) ∈ U, h y = f ⟨y, hy⟩) :
    ∃ g : M → F, ContMDiff IM IF ω g ∧ ∀ x : U, g x = f x := by
  classical
  apply exists_holomorphic_extension_of_local U f hU
  intro x
  by_cases hx : x ∈ U
  · exact ⟨U, hx, f, hf, fun _ _ => rfl⟩
  · exact hlocal x hx

/-- The equivalent ambient-function interface uses holomorphicity on
the actual open neighborhood and pointwise agreement on its overlap with U. -/
theorem exists_holomorphic_extension_of_ambient_local (U : Opens M) (f : U → F)
    (hU : Dense (U : Set M))
    (hlocal : ∀ x : M, ∃ V : Opens M, x ∈ V ∧ ∃ h : M → F,
      ContMDiffOn IM IF ω h V ∧ ∀ y : M, y ∈ V → ∀ hy : y ∈ U, h y = f ⟨y, hy⟩) :
    ∃ g : M → F, ContMDiff IM IF ω g ∧ ∀ x : U, g x = f x := by
  apply exists_holomorphic_extension_of_local U f hU
  intro x
  obtain ⟨V, hx, h, hh, hagree⟩ := hlocal x
  exact ⟨V, hx, (fun y : V => h y), restrict_contMDiff V h hh,
    fun y hy => hagree y y.property hy⟩

/-- Ambient local extensions are only needed at the missing points. -/
theorem exists_holomorphic_extension_of_ambient_local_outside (U : Opens M) (f : U → F)
    (hf : ContMDiff IM IF ω f) (hU : Dense (U : Set M))
    (hlocal : ∀ x : M, x ∉ U → ∃ V : Opens M, x ∈ V ∧ ∃ h : M → F,
      ContMDiffOn IM IF ω h V ∧ ∀ y : M, y ∈ V → ∀ hy : y ∈ U, h y = f ⟨y, hy⟩) :
    ∃ g : M → F, ContMDiff IM IF ω g ∧ ∀ x : U, g x = f x := by
  apply exists_holomorphic_extension_of_local_outside U f hf hU
  intro x hxU
  obtain ⟨V, hx, h, hh, hagree⟩ := hlocal x hxU
  exact ⟨V, hx, (fun y : V => h y), restrict_contMDiff V h hh,
    fun y hy => hagree y y.property hy⟩

/-- Any two genuine global holomorphic extensions are the same function. -/
theorem holomorphic_extension_unique (U : Opens M) (f : U → F)
    (hU : Dense (U : Set M)) {g h : M → F}
    (hg : ContMDiff IM IF ω g) (hh : ContMDiff IM IF ω h)
    (hgf : ∀ x : U, g x = f x) (hhf : ∀ x : U, h x = f x) : g = h :=
  continuous_extension_unique U f hU hg.continuous hh.continuous hgf hhf

/-- Local extensions at all missing points give a unique global
holomorphic extension, without a separately supplied global map. -/
theorem existsUnique_holomorphic_extension_of_local_outside (U : Opens M) (f : U → F)
    (hf : ContMDiff IM IF ω f) (hU : Dense (U : Set M))
    (hlocal : ∀ x : M, x ∉ U → ∃ V : Opens M, x ∈ V ∧ ∃ h : V → F,
      ContMDiff IM IF ω h ∧ ∀ y : V, ∀ hy : (y : M) ∈ U, h y = f ⟨y, hy⟩) :
    ∃! g : M → F, ContMDiff IM IF ω g ∧ ∀ x : U, g x = f x := by
  obtain ⟨g, hg, hgf⟩ := exists_holomorphic_extension_of_local_outside U f hf hU hlocal
  exact ⟨g, ⟨hg, hgf⟩, fun h hh => holomorphic_extension_unique U f hU hh.1 hg hh.2 hgf⟩

end Holomorphic

end Wikipedia.HopfProblem.HolomorphicExtensionGluing
