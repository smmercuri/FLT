import Mathlib
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.NumberField.Embeddings

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

theorem algebraMap_eq_coe :
    (algebraMap K v.Completion).toFun = ((↑) : K → v.Completion) := rfl

noncomputable instance : Algebra K (w.Completion) where
  toFun k := algebraMap L w.Completion (algebraMap K L k)
  map_one' := by simp only [map_one]
  map_mul' k₁ k₂ := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' k₁ k₂ := by simp only [map_add]
  commutes' k lhat := mul_comm _ _
  smul_def' k lhat := by
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.smul_def,
    ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq,
    UniformSpace.Completion.map_smul_eq_mul_coe, UniformSpace.Completion.algebraMap_def]

instance {wv : v.ExtensionPlace L} : Algebra v.Completion wv.1.Completion :=
  (mapOfComp wv.abs_comp_eq).toAlgebra

open UniformSpace.Completion in
def extensionPlaceContinuousAlgHom (wv : v.ExtensionPlace L) :
    v.Completion →A[v.Completion] wv.1.Completion where
  __ := mapOfComp wv.abs_comp_eq
  commutes' (r : _) := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, mapRingHom_apply, algebraMap_eq_coe, map_coe
      <| WithAbs.uniformContinuous_algebraMap wv.abs_comp_eq]; rfl
  cont := continuous_map

end NumberField.InfinitePlace.Completion
