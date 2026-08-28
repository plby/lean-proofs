import Wikipedia.NoExoticSixSphere.CubicalSuspensionSurjectivity

/-!
# The constructed stable sixth-stem group is a genuine finite-stage group

The actual cubical transitions are surjective from stage five and injective
from stage six. Their directed limit is consequently isomorphic to each
native group from stage six onward. In particular, the constructed stable
group is isomorphic to the actual native π₁₄(S⁸), not to a group declared
in advance to have a chosen cardinality.
-/

noncomputable section

namespace NoExoticSixSphere.CubicalStableSix

open StableSixSphereMaps

theorem ofNative_transition {k l : ℕ} (h : k ≤ l) (x : NativeStage k) :
    ofNative (transition k l h x) = ofNative x :=
  (DirectLimit.eq_of_le (f := transition) ⟨k, x⟩ l h).symm

theorem ofNative_stepHom (k : ℕ) (x : NativeStage k) :
    ofNative (stepHom k x) = ofNative x := by
  have h := ofNative_transition (Nat.le_succ k) x
  rw [transition_succ (le_refl k), transition_self] at h
  exact h

theorem transition_surjective {k l : ℕ} (hk : 5 ≤ k) (h : k ≤ l) :
    Function.Surjective (transition k l h) := by
  induction l, h using Nat.le_induction with
  | base =>
    rw [transition_self]
    exact Function.surjective_id
  | succ l h ih =>
    rw [transition_succ h]
    exact (stepHom_surjective (hk.trans h)).comp ih

theorem ofNative_surjective {k : ℕ} (hk : 5 ≤ k) :
    Function.Surjective (ofNative (k := k)) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨j, x⟩
    let l := max k j
    have hkl : k ≤ l := Nat.le_max_left _ _
    have hjl : j ≤ l := Nat.le_max_right _ _
    obtain ⟨y, hy⟩ := transition_surjective hk hkl (transition j l hjl x)
    refine ⟨y, ?_⟩
    change ofNative y = ofNative x
    calc
      ofNative y = ofNative (transition k l hkl y) := (ofNative_transition hkl y).symm
      _ = ofNative (transition j l hjl x) := congrArg ofNative hy
      _ = ofNative x := ofNative_transition hjl x

theorem stepHom_injective {k : ℕ} (hk : 6 ≤ k) : Function.Injective (stepHom k) := by
  intro x y hxy
  apply ofNative_injective hk
  rw [← ofNative_stepHom k x, ← ofNative_stepHom k y, hxy]

def stepMulEquiv (k : ℕ) (hk : 6 ≤ k) : NativeStage k ≃* NativeStage (k + 1) :=
  MulEquiv.ofBijective (stepHom k)
    ⟨stepHom_injective hk, stepHom_surjective (by omega)⟩

theorem stepMulEquiv_apply (k : ℕ) (hk : 6 ≤ k) (x : NativeStage k) :
    stepMulEquiv k hk x = stepHom k x := rfl

def stableMulEquiv (k : ℕ) (hk : 6 ≤ k) : NativeStage k ≃* Group :=
  MulEquiv.ofBijective (ofNativeHom k)
    ⟨ofNative_injective hk, ofNative_surjective (by omega)⟩

theorem stableMulEquiv_apply (k : ℕ) (hk : 6 ≤ k) (x : NativeStage k) :
    stableMulEquiv k hk x = ofNative x := rfl

def piFourteenSphereEightMulEquiv :
    HomotopyGroup (Fin 14) (Sphere 8) (spherePole 8) ≃* Group :=
  stableMulEquiv 6 (by decide)

end NoExoticSixSphere.CubicalStableSix
