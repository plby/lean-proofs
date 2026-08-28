import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Transporting actual Mayer–Vietoris naturality through small chains

A commuting map of actual small-chain sequences gives the naturality square
on ordinary singular homology. The small-chain comparisons are the proved
open-cover isomorphisms, not additional hypotheses. This file supplies the
transport step; the next file constructs the sequence map from a continuous
map carrying the two cover sets into the corresponding target sets.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)

/-- A commuting actual small-chain inclusion square induces its literal homology square. -/
theorem smallHomologyComparison_naturality_of_comm
    (g : smallComplex U V ⟶ smallComplex U' V')
    (hg : g ≫ smallInclusion U' V' = smallInclusion U V ≫ singularChainMap f)
    (n : ℕ) (a : SmallHomology U V n) :
    smallHomologyComparison U' V' n (homologyLinearMap g n a) =
      singularHomologyMap f n (smallHomologyComparison U V n a) := by
  have h := congrArg (fun q => homologyLinearMap q n) hg
  rw [homologyLinearMap_comp, homologyLinearMap_comp] at h
  exact LinearMap.congr_fun h a

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)

/-- The connecting square for an actual sequence map, transported through the
proved small-chain isomorphisms of the two open covers. -/
theorem connectingHomomorphism_naturality_of_sequenceMap
    (φ : chainSequence U V ⟶ chainSequence U' V')
    (hφ : φ.τ₃ ≫ smallInclusion U' V' = smallInclusion U V ≫ singularChainMap f)
    (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp
        (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp
        (singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hcover (n + 1)).surjective a
  have hb' : smallHomologyComparison U V (n + 1) b = a := hb
  change homologyLinearMap φ.τ₁ n (connectingHomomorphism U V hU hV hcover n a) =
    connectingHomomorphism U' V' hU' hV' hcover' n (singularHomologyMap f (n + 1) a)
  rw [← hb', connectingHomomorphism_comparison]
  have hδ : homologyLinearMap φ.τ₁ n (smallConnectingMap U V n b) =
      smallConnectingMap U' V' n (homologyLinearMap φ.τ₃ (n + 1) b) :=
    LinearMap.congr_fun
      (connectingMap_naturality (chainSequence_shortExact U V) φ
        (chainSequence_shortExact U' V') n) b
  have hc := (connectingHomomorphism_comparison U' V' hU' hV' hcover' n
    (homologyLinearMap φ.τ₃ (n + 1) b)).symm
  have hn := congrArg (connectingHomomorphism U' V' hU' hV' hcover' n)
    (smallHomologyComparison_naturality_of_comm f U V U' V' φ.τ₃ hφ (n + 1) b)
  exact hδ.trans (hc.trans hn)

end Wikipedia.HopfProblem.SingularMayerVietoris
