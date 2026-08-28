import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual Euclidean coordinates and closed cores of an open cell

An open cell is specified by its genuine homeomorphism from a Euclidean
space. Closed coordinate balls have compact closed images. Tietze extension
extends the original coordinates of a map on the preimage of such a core;
it does not alter the original target map or assert any smoothing result.
-/

noncomputable section

open Set Metric TopologicalSpace

namespace NoExoticSixSphere.CellChart

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
  (n : ℕ) (U : Opens X) (e : (Fin n → ℝ) ≃ₜ U)

def encode : C((Fin n → ℝ), X) :=
  ⟨fun v ↦ (e v).val, continuous_subtype_val.comp e.continuous⟩

theorem encode_injective : Function.Injective (encode n U e) :=
  fun v w h ↦ e.injective (Subtype.ext h)

theorem encode_mem (v : Fin n → ℝ) : encode n U e v ∈ U := (e v).property

theorem encode_inverse (x : U) : encode n U e (e.symm x) = x.val :=
  congrArg Subtype.val (e.apply_symm_apply x)

def core (r : ℝ) : Set X := encode n U e '' closedBall 0 r

def openCore (r : ℝ) : Set X := encode n U e '' ball 0 r

theorem core_subset (r : ℝ) : core n U e r ⊆ U := by
  rintro _ ⟨v, _, rfl⟩
  exact encode_mem n U e v

theorem openCore_subset (r : ℝ) : openCore n U e r ⊆ U := by
  rintro _ ⟨v, _, rfl⟩
  exact encode_mem n U e v

theorem isCompact_core (r : ℝ) : IsCompact (core n U e r) :=
  (isCompact_closedBall (0 : Fin n → ℝ) r).image (encode n U e).continuous

theorem isClosed_core [T2Space X] (r : ℝ) : IsClosed (core n U e r) :=
  (isCompact_core n U e r).isClosed

theorem isOpen_openCore (r : ℝ) : IsOpen (openCore n U e r) :=
  (U.isOpen.isOpenMap_subtype_val.comp e.isOpenMap) _ isOpen_ball

theorem core_subset_openCore {r s : ℝ} (hrs : r < s) : core n U e r ⊆ openCore n U e s :=
  image_mono (closedBall_subset_ball hrs)

theorem openCore_subset_core (r : ℝ) : openCore n U e r ⊆ core n U e r :=
  image_mono ball_subset_closedBall

theorem encode_mem_core_iff (r : ℝ) (v : Fin n → ℝ) :
    encode n U e v ∈ core n U e r ↔ ‖v‖ ≤ r := by
  rw [core, (encode_injective n U e).mem_set_image]
  exact mem_closedBall_zero_iff

theorem encode_mem_openCore_iff (r : ℝ) (v : Fin n → ℝ) :
    encode n U e v ∈ openCore n U e r ↔ ‖v‖ < r := by
  rw [openCore, (encode_injective n U e).mem_set_image]
  exact mem_ball_zero_iff

def coordinates (f : C(D, X)) : C(f ⁻¹' (U : Set X), (Fin n → ℝ)) :=
  ⟨fun z ↦ e.symm ⟨f z.val, z.property⟩,
    e.symm.continuous.comp ((f.continuous.comp continuous_subtype_val).subtype_mk _)⟩

theorem encode_coordinates (f : C(D, X)) (z : f ⁻¹' (U : Set X)) :
    encode n U e (coordinates n U e f z) = f z.val :=
  encode_inverse n U e ⟨f z.val, z.property⟩

theorem exists_coordinate_extension [T2Space X] [NormalSpace D]
    (f : C(D, X)) (r : ℝ) : ∃ g : C(D, (Fin n → ℝ)),
      ∀ z, f z ∈ core n U e r → encode n U e (g z) = f z := by
  let K : Set D := f ⁻¹' core n U e r
  let c : C(K, (Fin n → ℝ)) :=
    ⟨fun z ↦ e.symm ⟨f z.val, core_subset n U e r z.property⟩,
      e.symm.continuous.comp ((f.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  obtain ⟨g, hg⟩ := c.exists_restrict_eq ((isClosed_core n U e r).preimage f.continuous)
  refine ⟨g, ?_⟩
  intro z hz
  have he : g z = c ⟨z, hz⟩ := congrArg (fun h : C(K, (Fin n → ℝ)) ↦ h ⟨z, hz⟩) hg
  rw [he]
  exact encode_inverse n U e ⟨f z, core_subset n U e r hz⟩

end NoExoticSixSphere.CellChart
