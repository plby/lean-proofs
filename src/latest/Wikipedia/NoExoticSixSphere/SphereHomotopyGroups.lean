import Wikipedia.NoExoticSixSphere.SphereGenLoopConnectivity
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Native homotopy groups below the dimension of a sphere

The positive-dimensional case follows from the relative cube contraction.
The zeroth case uses path connectedness. A homeomorphism transfers the result
to the candidate's underlying space, without changing or making assumptions
about its smooth atlas.

These are statements about mathlib's actual `HomotopyGroup`. No Hurewicz or
singular-homology comparison is assumed here.
-/

namespace NoExoticSixSphere

theorem subsingleton_sphereHomotopyGroup {m n : ℕ} (hmn : m < n) (b : Sphere n) :
    Subsingleton (HomotopyGroup (Fin m) (Sphere n) b) := by
  cases m with
  | zero =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmn)
      let e : HomotopyGroup (Fin 0) (Sphere (n + 1)) b ≃ ZerothHomotopy (Sphere (n + 1)) :=
        HomotopyGroup.pi0EquivZerothHomotopy
      exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩
  | succ m => exact subsingleton_sphereHomotopyGroup_of_pos (Nat.succ_pos m) hmn b

variable {M : Type*} [TopologicalSpace M]

theorem subsingleton_homotopyGroup_of_homeomorph_sphere {m n : ℕ} (hmn : m < n)
    (h : M ≃ₜ Sphere n) (b : M) : Subsingleton (HomotopyGroup (Fin m) M b) := by
  let i : C(M, Sphere n) := ⟨h, h.continuous_toFun⟩
  let j : C(Sphere n, M) := ⟨h.symm, h.symm.continuous_toFun⟩
  have hi : Function.Injective (HigherHomotopy.map (N := Fin m) (y := b) i rfl) := by
    apply HigherHomotopy.map_injective
    intro f g S hfg
    obtain ⟨H⟩ := hfg
    have hf : j.comp (i.comp f) = f := by
      ext x
      exact h.symm_apply_apply (f x)
    have hg : j.comp (i.comp g) = g := by
      ext x
      exact h.symm_apply_apply (g x)
    exact ⟨(H.compContinuousMap j).cast hf hg⟩
  let : Subsingleton (HomotopyGroup (Fin m) (Sphere n) (i b)) :=
    subsingleton_sphereHomotopyGroup hmn (i b)
  exact ⟨fun x y ↦ hi (Subsingleton.elim _ _)⟩

theorem genLoop_homotopic_const_of_homeomorph_sphere {m n : ℕ} (hmn : m < n)
    (h : M ≃ₜ Sphere n) (b : M) (p : GenLoop (Fin m) M b) :
    GenLoop.Homotopic p GenLoop.const := by
  have he : (Quotient.mk' p : HomotopyGroup (Fin m) M b) = Quotient.mk' GenLoop.const :=
    @Subsingleton.elim _ (subsingleton_homotopyGroup_of_homeomorph_sphere hmn h b) _ _
  exact Quotient.exact he

theorem sixSphere_thirdHomotopyGroup_subsingleton (h : M ≃ₜ Sphere 6) (b : M) :
    Subsingleton (HomotopyGroup (Fin 3) M b) :=
  subsingleton_homotopyGroup_of_homeomorph_sphere (by decide : 3 < 6) h b

end NoExoticSixSphere
