import Wikipedia.NoExoticSixSphere.EndingPathSpace

/-!
# An explicit contraction of loops in the ending-path space

Path shortening fixes the constant ending path. Applying it pointwise
therefore contracts the actual compact-open loop space while retaining
both loop endpoints. The resulting contraction is jointly continuous.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.EndingPath

variable {X : Type} [TopologicalSpace X] (x : X)

abbrev Loops := Path (constant x) (constant x)

def shortenLoop (s : I) (p : Loops x) : Loops x where
  toFun t := shorten s (p t)
  continuous_toFun := continuous_shorten.comp (continuous_const.prodMk p.continuous)
  source' := (congrArg (shorten s) p.source).trans (shorten_constant s)
  target' := (congrArg (shorten s) p.target).trans (shorten_constant s)

theorem continuous_shortenLoop : Continuous (fun u : I × Loops x ↦ shortenLoop x u.1 u.2) := by
  apply continuous_induced_rng.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (I × Loops x) × I ↦ shorten p.1.1 (p.1.2 p.2))
  exact continuous_shorten.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

theorem shortenLoop_zero (p : Loops x) : shortenLoop x 0 p = p := by
  apply Path.ext
  funext t
  exact shorten_zero (p t)

theorem shortenLoop_one (p : Loops x) : shortenLoop x 1 p = Path.refl (constant x) := by
  apply Path.ext
  funext t
  exact shorten_one (p t)

def loopContraction : (ContinuousMap.id (Loops x)).Homotopy
    (ContinuousMap.const (Loops x) (Path.refl (constant x))) where
  toFun p := shortenLoop x p.1 p.2
  continuous_toFun := continuous_shortenLoop x
  map_zero_left := shortenLoop_zero x
  map_one_left := shortenLoop_one x

theorem loops_contractible : ContractibleSpace (Loops x) :=
  (contractible_iff_id_nullhomotopic (Loops x)).mpr
    ⟨Path.refl (constant x), ⟨loopContraction x⟩⟩

end NoExoticSixSphere.EndingPath
