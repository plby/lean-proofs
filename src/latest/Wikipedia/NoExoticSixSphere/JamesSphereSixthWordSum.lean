import Wikipedia.NoExoticSixSphere.ProductSixthHomology
import Wikipedia.NoExoticSixSphere.SphereProductConnectivity
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.NoExoticSixSphere.JamesSphereHopf
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedTopology

/-!
# Sixth homology of finite words of actual six-sphere letters

The original finite-word presentation has, in sixth homology, the sum
of its one-letter coordinate maps. The proof splits actual Cartesian
products and uses the proved five-connectivity of their sphere factors.
No continuity of multiplication on the full James space is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.SixthWordSum

abbrev Letters (k : ℕ) := Fin k → Sphere 6

def point (k : ℕ) : Letters k := fun _ ↦ spherePole 6

instance lettersSimplyConnected (k : ℕ) : SimplyConnectedSpace (Letters k) :=
  SphereProductConnectivity.simplyConnected_pi

instance lettersPiTwo (k : ℕ) : Subsingleton (π_ 2 (Letters k) (point k)) :=
  SphereProductConnectivity.pi_subsingleton (by decide) (by decide) _

instance lettersPiThree (k : ℕ) : Subsingleton (π_ 3 (Letters k) (point k)) :=
  SphereProductConnectivity.pi_subsingleton (by decide) (by decide) _

instance lettersPiFour (k : ℕ) : Subsingleton (π_ 4 (Letters k) (point k)) :=
  SphereProductConnectivity.pi_subsingleton (by decide) (by decide) _

instance lettersPiFive (k : ℕ) : Subsingleton (π_ 5 (Letters k) (point k)) :=
  SphereProductConnectivity.pi_subsingleton (by decide) (by decide) _

local instance spherePiTwo : Subsingleton (π_ 2 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance spherePiThree : Subsingleton (π_ 3 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance spherePiFour : Subsingleton (π_ 4 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

local instance spherePiFive : Subsingleton (π_ 5 (Sphere 6) (spherePole 6)) :=
  subsingleton_sphereHomotopyGroup (by decide) _

def split (k : ℕ) : Letters (k + 1) ≃ₜ Sphere 6 × Letters k where
  toFun v := (v 0, Fin.tail v)
  invFun p := Fin.cons p.1 p.2
  left_inv := Fin.cons_self_tail
  right_inv := fun _ ↦ rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i ↦ continuous_apply i.succ))
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd

def wordMap (k : ℕ) : C(Letters k, James.Space (Sphere 6) (spherePole 6)) :=
  ⟨fun v ↦ James.word (spherePole 6) (List.ofFn v),
    James.continuous_word_array (spherePole 6) k⟩

def coordinate (k : ℕ) (i : Fin k) : C(Letters k, Sphere 6) := ContinuousMap.eval i

def tail (k : ℕ) : C(Letters (k + 1), Letters k) :=
  ⟨Fin.tail, continuous_pi (fun i ↦ continuous_apply i.succ)⟩

theorem wordMap_point (k : ℕ) : wordMap k (point k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change James.word (spherePole 6) (List.ofFn (point (k + 1))) = _
      rw [List.ofFn_succ, James.word_cons]
      change James.letter (spherePole 6) (spherePole 6) * wordMap k (point k) = _
      rw [James.letter_basepoint, ih, one_mul]

theorem wordMap_split_left (k : ℕ) :
    ((wordMap (k + 1)).comp (split k).symm).comp
      (ProductSixthHomology.leftSection (point k)) = inclusion 6 := by
  apply ContinuousMap.ext
  intro x
  change James.word (spherePole 6) (List.ofFn (Fin.cons x (point k))) = _
  rw [List.ofFn_succ, James.word_cons]
  change inclusion 6 x * wordMap k (point k) = inclusion 6 x
  rw [wordMap_point, mul_one]

theorem wordMap_split_right (k : ℕ) :
    ((wordMap (k + 1)).comp (split k).symm).comp
      (ProductSixthHomology.rightSection (spherePole 6)) = wordMap k := by
  apply ContinuousMap.ext
  intro v
  change James.word (spherePole 6) (List.ofFn (Fin.cons (spherePole 6) v)) = _
  rw [List.ofFn_succ, James.word_cons]
  change James.letter (spherePole 6) (spherePole 6) * wordMap k v = wordMap k v
  rw [James.letter_basepoint, one_mul]

theorem wordMap_homology_step (k : ℕ) (a : SingularHomology (Letters (k + 1)) 6) :
    singularHomologyMap (wordMap (k + 1)) 6 a =
      singularHomologyMap (inclusion 6) 6
        (singularHomologyMap (coordinate (k + 1) 0) 6 a) +
      singularHomologyMap (wordMap k) 6
        (singularHomologyMap (tail k) 6 a) := by
  have h := ProductSixthHomology.map_product (spherePole 6) (point k)
    ((wordMap (k + 1)).comp (split k).symm)
    (singularHomologyMap (split k : C(Letters (k + 1), Sphere 6 × Letters k)) 6 a)
  rw [wordMap_split_left, wordMap_split_right] at h
  have he : ((wordMap (k + 1)).comp (split k).symm).comp
      (split k : C(Letters (k + 1), Sphere 6 × Letters k)) =
      wordMap (k + 1) := by
    apply ContinuousMap.ext
    intro v
    exact congrArg (wordMap (k + 1)) ((split k).symm_apply_apply v)
  simp only [← LinearMap.comp_apply, ← singularHomologyMap_comp] at h
  rw [he] at h
  change singularHomologyMap (wordMap (k + 1)) 6 a =
    singularHomologyMap ((inclusion 6).comp (coordinate (k + 1) 0)) 6 a +
      singularHomologyMap ((wordMap k).comp (tail k)) 6 a at h
  simpa only [singularHomologyMap_comp, LinearMap.comp_apply] using h

theorem wordMap_homology (k : ℕ) (a : SingularHomology (Letters k) 6) :
    singularHomologyMap (wordMap k) 6 a =
      ∑ i : Fin k, singularHomologyMap (inclusion 6) 6
        (singularHomologyMap (coordinate k i) 6 a) := by
  induction k with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact ProductSixthHomology.constant_map_zero (point 0) 1 a
  | succ k ih =>
      rw [wordMap_homology_step, ih, Fin.sum_univ_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
      rfl

end NoExoticSixSphere.JamesSphere.SixthWordSum
