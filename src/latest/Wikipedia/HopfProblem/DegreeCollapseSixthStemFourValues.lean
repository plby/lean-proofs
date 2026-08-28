import Wikipedia.HopfProblem.DegreeCollapseFirstStemGroup
import Wikipedia.HopfProblem.DegreeCollapseFourSphereDesuspension
import Wikipedia.HopfProblem.DegreeCollapseSixSphereDesuspension

/-!
# At most four actual classes in the stable sixth stem

The original middle James--Hopf map takes values in the now computed
first stable stem of order two. Its kernel consists of actual suspensions
from S5, whose stable images are already proved to be one or the specified
square. Thus at most one additional coset remains. The whole stable
sixth stem is finite of cardinality at most four and exponent dividing four.
This does not eliminate the additional coset or prove Arf detection.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthStemFourValues

open NoExoticSixSphere JamesSphere CubicalStableSix
open StableThirdComposition

def hopf : π_ 12 (Sphere 6) (spherePole 6) →* π_ 12 (Sphere 11) (spherePole 11) :=
  SuspensionComparison.orderedHopfHom 5 (by decide) 11

theorem kernel_stable (x : π_ 12 (Sphere 6) (spherePole 6)) (hx : hopf x = 1) :
    ofNative (k := 4) x = 1 ∨ ofNative (k := 4) x = stableSquare := by
  obtain ⟨a, rfl⟩ := (EHP.hopf_eq_one_iff_metastable 5 10 (by decide) (by decide) x).mp hx
  have he := ofNative_stepHom 3 a
  rcases FourSphereDesuspension.stable_eq_one_or_square a with h | h
  · exact Or.inl (he.trans h)
  · exact Or.inr (he.trans h)

theorem square_stable (x : π_ 12 (Sphere 6) (spherePole 6)) :
    ofNative (k := 4) x ^ 2 = 1 ∨ ofNative (k := 4) x ^ 2 = stableSquare := by
  have hh : hopf (x ^ 2) = 1 := by
    rw [map_pow]
    exact FirstStemGroup.pow_two 8 _
  have h := kernel_stable (x ^ 2) hh
  change ofNativeHom 4 (x ^ 2) = 1 ∨ ofNativeHom 4 (x ^ 2) = stableSquare at h
  change ofNativeHom 4 x ^ 2 = 1 ∨ ofNativeHom 4 x ^ 2 = stableSquare
  simpa only [map_pow] using h

theorem stable_square_eq_one_or_square (z : CubicalStableSix.Group) :
    z ^ 2 = 1 ∨ z ^ 2 = stableSquare := by
  obtain ⟨x, rfl⟩ := SixSphereDesuspension.stable_surjective z
  exact square_stable x

theorem stable_pow_four (z : CubicalStableSix.Group) : z ^ 4 = 1 := by
  have he : z ^ 4 = (z ^ 2) ^ 2 := (pow_mul z 2 2)
  rw [he]
  rcases stable_square_eq_one_or_square z with h | h
  · rw [h, one_pow]
  · rw [h, stableSquare_pow_two]

/-- A representative is chosen only if the actual Hopf image is nontrivial. -/
def extraRepresentative : π_ 12 (Sphere 6) (spherePole 6) := by
  classical
  exact if h : ∃ x, hopf x ≠ 1 then h.choose else 1

def extraClass : CubicalStableSix.Group := ofNative (k := 4) extraRepresentative

theorem hopf_eq_one_or_extra (x : π_ 12 (Sphere 6) (spherePole 6)) :
    hopf x = 1 ∨ hopf x = hopf extraRepresentative := by
  by_cases hx : hopf x = 1
  · exact Or.inl hx
  · right
    have hex : ∃ y, hopf y ≠ 1 := ⟨x, hx⟩
    have hr : hopf extraRepresentative ≠ 1 := by
      simpa only [extraRepresentative, dif_pos hex] using hex.choose_spec
    exact ((FirstStemGroup.eq_one_or_generator 8 (hopf x)).resolve_left hx).trans
      ((FirstStemGroup.eq_one_or_generator 8 (hopf extraRepresentative)).resolve_left hr).symm

theorem stable_four_values (z : CubicalStableSix.Group) :
    z = 1 ∨ z = stableSquare ∨ z = extraClass ∨ z = stableSquare * extraClass := by
  obtain ⟨x, rfl⟩ := SixSphereDesuspension.stable_surjective z
  rcases hopf_eq_one_or_extra x with hx | hx
  · rcases kernel_stable x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hh : hopf (x / extraRepresentative) = 1 := by
      rw [map_div]
      exact div_eq_one.mpr hx
    have h := kernel_stable (x / extraRepresentative) hh
    change ofNativeHom 4 (x / extraRepresentative) = 1 ∨
      ofNativeHom 4 (x / extraRepresentative) = stableSquare at h
    rw [map_div] at h
    change ofNative (k := 4) x / extraClass = 1 ∨
      ofNative (k := 4) x / extraClass = stableSquare at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl (div_eq_one.mp h)))
    · have he := congrArg (fun z ↦ z * extraClass) h
      rw [div_mul_cancel] at he
      exact Or.inr (Or.inr (Or.inr he))

def fourValues (i : Fin 4) : CubicalStableSix.Group :=
  if i = 0 then 1 else if i = 1 then stableSquare else
    if i = 2 then extraClass else stableSquare * extraClass

theorem fourValues_surjective : Function.Surjective fourValues := by
  intro z
  rcases stable_four_values z with h | h | h | h
  · exact ⟨0, by simpa [fourValues] using h.symm⟩
  · exact ⟨1, by simpa [fourValues] using h.symm⟩
  · exact ⟨2, by simpa [fourValues] using h.symm⟩
  · exact ⟨3, by simpa [fourValues] using h.symm⟩

theorem finite : Finite CubicalStableSix.Group :=
  Finite.of_surjective fourValues fourValues_surjective

theorem card_le_four : Nat.card CubicalStableSix.Group ≤ 4 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Nat.card_le_card_of_surjective fourValues fourValues_surjective

theorem native_card_le_four (k : ℕ) (hk : 6 ≤ k) :
    Nat.card (StableSixSphereMaps.NativeStage k) ≤ 4 :=
  (Nat.card_congr (stableMulEquiv k hk).toEquiv).trans_le card_le_four

theorem native_pow_four (k : ℕ) (hk : 6 ≤ k) (c : StableSixSphereMaps.NativeStage k) :
    c ^ 4 = 1 := by
  apply (stableMulEquiv k hk).injective
  rw [map_pow, map_one]
  exact stable_pow_four _

end Wikipedia.HopfProblem.DegreeCollapse.SixthStemFourValues
