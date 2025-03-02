import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.Topology.Algebra.UniformRing

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  isUniformInducing_of_comp h |>.uniformContinuous

end WithAbs

namespace AbsoluteValue.Completion

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

noncomputable abbrev semiAlgHomOfComp (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    v.Completion →ₛₐ[algebraMap (WithAbs v) (WithAbs w)] w.Completion :=
  UniformSpace.Completion.mapSemialgHom _
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous

theorem semiAlgHomOfComp_coe (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x)
    (x : WithAbs v) :
    semiAlgHomOfComp h x = algebraMap (WithAbs v) (WithAbs w) x :=
  UniformSpace.Completion.mapSemialgHom_coe
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous x

theorem semiAlgHomOfComp_dist_eq (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x)
    (x y : v.Completion) :
    dist (semiAlgHomOfComp h x) (semiAlgHomOfComp h y) = dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · rw [semiAlgHomOfComp_coe, semiAlgHomOfComp_coe, UniformSpace.Completion.dist_eq]
    exact UniformSpace.Completion.dist_eq x y ▸
      (WithAbs.isometry_of_comp (L := WithAbs w) h).dist_eq x y

theorem isometry_semiAlgHomOfComp (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    Isometry (semiAlgHomOfComp h) :=
  Isometry.of_dist_eq <| semiAlgHomOfComp_dist_eq h

end AbsoluteValue.Completion
