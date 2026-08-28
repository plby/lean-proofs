import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplementEquality
import Wikipedia.NoExoticSixSphere.SpanningDiskRadialComplement
import Wikipedia.NoExoticSixSphere.TransverseRadialExtension
import Wikipedia.NoExoticSixSphere.FramedProductCollarReplacement

/-!
# Radializing the actual spanning-disk product without changing boundary columns

The prescribed disk collar and partial normal frame put the radial extension
of the original transverse boundary columns in the actual combined-operator
complement. Relative frame replacement then constructs a new framed embedded
product, with the same disk and partial frame, whose transverse columns are
exactly radial on a whole collar. The actual boundary columns are unchanged.
All transverse dimensions are allowed.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

variable {N k q : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
  (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 N) f s))
  (a : Sphere 3 → Space N k)
  (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
  {T : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6)}
  (A : DiskThickening.FramedProduct D.toFun T q)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (a s).val)

include hf hd ha hTb in
theorem range_transverseExtension_le_complement
    {V : Set (Vector 4)} (hV : IsOpen V) (hDV : EqOn D.toFun (collar b f) V)
    {x : Vector 4} (hxV : x ∈ V) (hx : (1 / 2 : ℝ) < ‖x‖)
    (hTx : T x = boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val) :
    (A.transverseExtension b x).range ≤
      (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ := by
  let s := SphereRadialRetraction.retract b x
  have hC : (A.transverse s.val).range =
      ((a s).val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ).map
        (appendZeroMap N 6).toLinearMap := by
    rw [A.range_transverse s.val (sphere_subset_closedBall s.property), hTb s]
    exact (D.map_normal_eq_combined_orthogonal hf s (hd s) (a s) (ha s)).symm
  rw [A.transverseExtension_eq_radial b hx]
  change (A.transverse s.val).range ≤ _
  rw [hC, hTx]
  exact map_normal_le_combined_orthogonal_radial b f hf hV hDV hxV hx (a s).val

include hf hd ha hTb in
theorem exists_framedProduct_radialCollar (r₀ : ℝ) (hr₀ : r₀ < 1)
    (hTc : ∀ x ∈ closedBall (0 : Vector 4) 1, r₀ ≤ ‖x‖ →
      T x = boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val)
    (hN : (k + 5) + 4 + q = N + 6) :
    ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧ r₀ ≤ r ∧
      ∃ A' : DiskThickening.FramedProduct D.toFun T q,
        (∀ s : Sphere 3, A'.transverse s.val = A.transverse s.val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
          D.toFun x = collar b f x ∧
          T x = boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val ∧
          A'.transverse x = A'.transverse (SphereRadialRetraction.retract b x).val := by
  obtain ⟨V, hV, hSV, hDV⟩ := D.collar_eq
  let U := V ∩ ({x : Vector 4 | (1 / 2 : ℝ) < ‖x‖} ∩ {x : Vector 4 | r₀ < ‖x‖})
  have hU : IsOpen U := hV.inter
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_const continuous_norm))
  have hSU : sphere (0 : Vector 4) 1 ⊆ U := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    refine ⟨hSV hx, ?_, ?_⟩
    · change (1 / 2 : ℝ) < ‖x‖
      rw [hn]
      norm_num
    · change r₀ < ‖x‖
      rwa [hn]
  have hFn (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U)
      (w : Vector q) : ‖A.transverseExtension b x w‖ = ‖w‖ :=
    A.norm_transverseExtension b hx.2.2.1 w
  have hFr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U) :
      (A.transverseExtension b x).range ≤
        (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ :=
    D.range_transverseExtension_le_complement hf hd a ha A hTb hV hDV
      hx.2.1 hx.2.2.1 (hTc x hx.1 hx.2.2.2.le)
  have hinj : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    have he' : (⟨x, hx⟩ : closedBall (0 : Vector 4) 1) = ⟨y, hy⟩ :=
      D.embedded.injective he
    exact congrArg Subtype.val he'
  obtain ⟨r, hr, hr1, hrU, A', hAb, hAF⟩ := A.exists_framedProduct_collar
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (A.transverseExtension b)
    (A.contDiff_transverseExtension b) (A.transverseExtension_coe b)
    hU hSU hFn hFr hinj hN
  let ρ : ℝ := max r (max r₀ (3 / 4))
  have hρr : r ≤ ρ := le_max_left _ _
  have hρr₀ : r₀ ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
  have hρhalf : (1 / 2 : ℝ) < ρ :=
    lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      ((le_max_right _ _).trans (le_max_right _ _))
  have hρ1 : ρ < 1 := max_lt hr1 (max_lt hr₀ (by norm_num))
  refine ⟨ρ, hρhalf, hρ1, hρr₀, A', hAb, ?_⟩
  intro x hx hρx
  have hxr : r ≤ ‖x‖ := hρr.trans hρx
  have hxU := hrU ⟨hx, hxr⟩
  refine ⟨hDV hxU.1, hTc x hx (hρr₀.trans hρx), ?_⟩
  exact (hAF x hx hxr).trans
    ((A.transverseExtension_eq_radial b (hρhalf.trans_le hρx)).trans
      (hAb (SphereRadialRetraction.retract b x)).symm)

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
