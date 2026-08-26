import ErdosProblems.Erdos73.ProjectiveAcrossFacePair

/-! The concrete projective-grid vertex rotation and its quadrangular identity. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

theorem projectiveAcrossFace_injective {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Function.Injective (projectiveAcrossFace hn hnEven) := by
  intro d e he
  apply projectiveAlphaPair_injective hn hnEven
  rw [← projectiveAcrossFace_pair hn hnEven d, ← projectiveAcrossFace_pair hn hnEven e, he]

def projectiveAcrossPermutation {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Perm (ProjectivePort n) :=
  Equiv.ofBijective (projectiveAcrossFace hn hnEven)
    ⟨projectiveAcrossFace_injective hn hnEven,
      Finite.injective_iff_surjective.mp (projectiveAcrossFace_injective hn hnEven)⟩

def projectiveRotation {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) : Perm (ProjectivePort n) :=
  (projectiveAcrossPermutation hn hnEven)⁻¹

theorem projectiveRotation_pair {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) (d : ProjectivePort n) :
    orientedPortPair (projectivePortLabel hn) (projectivePortPair n)
      (projectiveRotation hn hnEven d) =
        orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n) d := by
  have hh := projectiveAcrossFace_pair hn hnEven (projectiveRotation hn hnEven d)
  change orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
    (projectiveAcrossPermutation hn hnEven ((projectiveAcrossPermutation hn hnEven).symm d)) = _ at hh
  rw [(projectiveAcrossPermutation hn hnEven).apply_symm_apply] at hh
  exact hh.symm

theorem projectiveRotation_label {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) (d : ProjectivePort n) :
    projectivePortLabel hn (projectiveRotation hn hnEven d) = projectivePortLabel hn d :=
  congrArg Prod.fst (projectiveRotation_pair hn hnEven d)

theorem projectiveAcrossFace_label {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) (d : ProjectivePort n) :
    projectivePortLabel hn (projectiveAcrossFace hn hnEven d) = projectivePortLabel hn d :=
  congrArg Prod.fst (projectiveAcrossFace_pair hn hnEven d)

theorem projectiveRotation_face_identity {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    (projectiveRotation hn hnEven)⁻¹ * projectivePortPair n * projectiveRotation hn hnEven *
      projectivePortPair n = projectivePortOpposite n := by
  let α := projectivePortPair n
  let τ := projectivePortOpposite n
  let σ := projectiveRotation hn hnEven
  have hβ : Function.Involutive (τ * α) := by
    intro d
    change τ (α (τ (α d))) = d
    rw [projectivePortPair_commute n, projectivePortPair_involutive n d,
      projectivePortOpposite_involutive n d]
  have hh := rotation_intertwines_of_pair_eq (projectivePortLabel hn) α (τ * α) σ
    (projectivePortPair_involutive n) hβ (projectiveAlphaPair_injective hn hnEven)
    (projectiveRotation_pair hn hnEven)
  have hαα : α * α = 1 := by
    apply Equiv.ext
    intro d
    exact projectivePortPair_involutive n d
  change σ⁻¹ * α * σ * α = τ
  calc
    σ⁻¹ * α * σ * α = σ⁻¹ * (α * σ) * α := by group
    _ = σ⁻¹ * (σ * (τ * α)) * α := by rw [hh]
    _ = τ * (α * α) := by group
    _ = τ := by rw [hαα, mul_one]

theorem projectivePair_commutes_contour {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Commute (projectivePortPair n) (projectiveRotation hn hnEven * projectivePortSwitch n) := by
  exact faceSwitch_commutes_with_edge_pairing (projectivePortPair n) (projectiveRotation hn hnEven)
    (projectivePortOpposite n) projectivePortSelected (projectivePortPair_involutive n)
    (projectivePortOpposite_involutive n) (projectivePortPair_commute n)
    projectivePortSelected_opposite projectivePortSelected_pair (projectiveRotation_face_identity hn hnEven)

end
end Erdos73
