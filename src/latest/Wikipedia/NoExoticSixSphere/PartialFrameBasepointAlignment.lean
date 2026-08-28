import Wikipedia.NoExoticSixSphere.PartialFramePathTransport
import Wikipedia.NoExoticSixSphere.RectangularDeformationHomotopy

/-!
# Moving a frame-map basepoint through an actual ambient homotopy

Apply the constructed ambient transport to every frame in the original map,
then normalize. At the chosen point, the transported columns are exactly
the prescribed path of frames, so normalization retains its endpoint value.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Stiefel.FramePath

open GLOrthonormalization

theorem exists_homotopic_with_value {X : Type*} [TopologicalSpace X] {N n d : ℕ}
    (hN : n + d = N) (f : C(X, Space N n)) (p : X) (b : Space N n) (γ : Path (f p) b) :
    ∃ g : C(X, Space N n), f.Homotopic g ∧ g p = b := by
  let Γ : C(I, Space N n) := γ.toContinuousMap
  let U := transport Γ hN
  have hU : Continuous (fun t ↦ (U t).toContinuousLinearMap) := continuous_transport Γ hN
  let A : C(I × X, Monomorphism.Space N n) :=
    ⟨fun z ↦ ⟨(U z.1).toContinuousLinearMap.comp (f z.2).val,
      (U z.1).injective.comp (Stiefel.injective _)⟩,
      ((hU.comp continuous_fst).clm_comp
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd))).subtype_mk _⟩
  have hA0 (x : X) : A (0, x) = Monomorphism.inclusion N n (f x) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change transport Γ hN 0 ((f x).val v) = (f x).val v
    rw [transport_zero]
    rfl
  have hA1 : A (1, p) = Monomorphism.inclusion N n b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change transport Γ hN 1 ((f p).val v) = b.val v
    have he := transport_column Γ hN 1 v
    change transport Γ hN 1 ((γ 0).val v) = (γ 1).val v at he
    simpa only [Path.source, Path.target] using he
  let F := (Monomorphism.normalize N n).comp A
  let g : C(X, Space N n) :=
    ⟨fun x ↦ F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, ⟨{
    toContinuousMap := F
    map_zero_left := ?_
    map_one_left := fun _ ↦ rfl }⟩, ?_⟩
  · intro x
    change Monomorphism.normalize N n (A (0, x)) = f x
    rw [hA0, Monomorphism.normalize_inclusion]
  · change Monomorphism.normalize N n (A (1, p)) = b
    rw [hA1, Monomorphism.normalize_inclusion]

end NoExoticSixSphere.Stiefel.FramePath
