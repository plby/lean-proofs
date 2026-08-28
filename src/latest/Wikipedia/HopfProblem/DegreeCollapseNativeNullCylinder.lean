import Wikipedia.NoExoticSixSphere.RelativeRegularCylinder
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!

# A nullhomotopy constructs the cylinder with the exact original native endpoint

Move the terminal constant off the specified regular value, then apply
the actual endpoint-preserving relative regular-cylinder construction.
The initial map remains literally equal to the supplied smooth map.
Consequently its specified native regular-fiber atlas and any original
endpoint diffeomorphism survive, with every ambient point unchanged.
Nullhomotopy and the filling's low connectivity are not inferred here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere

theorem exists_regular_filling_cylinder_of_nullhomotopic {m n : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (hn : 0 < n) (hnull : f.Nullhomotopic) :
    ∃ d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1,
      d.leftMap = f ∧ ∀ x, d.rightMap x ≠ b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨c, ⟨H⟩⟩ := hnull
  obtain ⟨c', hc'⟩ := exists_ne b
  let p := PathConnectedSpace.somePath c c'
  have hconst : ContMDiff (𝓡 m) (𝓡 (n + 1)) ∞
      (ContinuousMap.const (Sphere m) c') := contMDiff_const
  have hregconst : ∀ x, (ContinuousMap.const (Sphere m) c') x = b →
      Surjective (mfderiv (𝓡 m) (𝓡 (n + 1)) (ContinuousMap.const (Sphere m) c') x) := by
    intro x hx
    exact (hc' hx).elim
  obtain ⟨d, hleft, hright, _⟩ := exists_regularCollaredCylinder hf hconst
    (H.trans p.toHomotopyConst) b hreg hregconst
  refine ⟨d, hleft, ?_⟩
  intro x
  simpa only [hright, ContinuousMap.const_apply] using hc'

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem exists_native_filling_cylinder_retaining_endpoint {m n k : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (hdim : m = n + k) (hn : 0 < n) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hdim)
    ∀ D : X ≃ₘ⟮I, 𝓡 k⟯ {x : Sphere m // f x = b},
      f.Nullhomotopic →
      ∃ d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1,
        d.leftMap = f ∧ (∀ x, d.rightMap x ≠ b) ∧
        letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k
          (by simpa using hdim)
        ∃ D' : X ≃ₘ⟮I, 𝓡 k⟯ {x : Sphere m // d.leftMap x = b},
          ∀ x, (D' x).val = (D x).val := by
  let _ := regularFiberAtlas f hf b hreg k (by simpa using hdim)
  intro D hnull
  obtain ⟨d, hleft, hmiss⟩ := exists_regular_filling_cylinder_of_nullhomotopic f hf b hreg hn hnull
  refine ⟨d, hleft, hmiss, ?_⟩
  subst f
  let _ := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hdim)
  exact ⟨D, fun _ => rfl⟩

/-- Finite stabilization retains the supplied native endpoint and its exact ambient map. -/
theorem exists_native_filling_cylinder_of_nullhomotopic_iterate {m n k : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
    (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (hdim : m = n + k) (r : ℕ) (hn : 0 < n + r) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hdim)
    ∀ D : X ≃ₘ⟮I, 𝓡 k⟯ {x : Sphere m // f x = b},
      (SphereMapSuspension.iterate f r).Nullhomotopic →
      ∃ d : RegularCollaredCylinder (M := Sphere (m + r))
          (𝓡 (m + r)) (𝓡 (n + r)) (SphereMapSuspension.equators n r b) 0 1,
        (SphereMapSuspension.iterate f r).Homotopic d.leftMap ∧
        (∀ x, d.rightMap x ≠ SphereMapSuspension.equators n r b) ∧
        letI := regularFiberAtlas d.leftMap d.smooth_left
          (SphereMapSuspension.equators n r b) d.regular_left k
          (by simp only [finrank_euclideanSpace_fin]; omega)
        ∃ D' : X ≃ₘ⟮I, 𝓡 k⟯
            {x : Sphere (m + r) // d.leftMap x = SphereMapSuspension.equators n r b},
          ∀ x, (D' x).val = SphereMapSuspension.equators m r (D x).val := by
  let _ := regularFiberAtlas f hf b hreg k (by simpa using hdim)
  intro D hnull
  obtain ⟨g, hg, hgreg, H, F, hF⟩ :=
    SphereMapSuspension.exists_smooth_iterate_with_fiber f hf b hreg k hdim r
  have hgn : g.Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnull
    exact ⟨c, H.symm.trans hc⟩
  have hdr : m + r = (n + r) + k := by omega
  let _ := regularFiberAtlas g hg (SphereMapSuspension.equators n r b) hgreg k
    (by simpa using hdr)
  obtain ⟨d, hleft, hmiss, D', hD'⟩ :=
    exists_native_filling_cylinder_retaining_endpoint g hg
      (SphereMapSuspension.equators n r b) hgreg hdr hn (D.trans F) hgn
  refine ⟨d, by simpa only [hleft] using H, hmiss, ?_⟩
  let _ := regularFiberAtlas d.leftMap d.smooth_left
    (SphereMapSuspension.equators n r b) d.regular_left k (by simpa using hdr)
  refine ⟨D', ?_⟩
  intro x
  rw [hD']
  exact hF (D x)

end Wikipedia.HopfProblem.DegreeCollapse
