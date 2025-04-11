import Mathlib.NumberTheory.NumberField.Completion
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.MetricSpace.Pseudo.Matrix
import FLT.NumberField.Embeddings
import FLT.NumberField.WeakApproximation

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion SemialgHom

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
  {wv : v.ExtensionPlace L}

instance {v : InfinitePlace K} : NontriviallyNormedField (v.Completion) where
  toNormedField := InfinitePlace.Completion.instNormedField v
  non_trivial :=
    let ⟨x, hx⟩ := v.isNontrivial.exists_abv_gt_one
    ⟨x, by rw [UniformSpace.Completion.norm_coe]; exact hx⟩

instance : Algebra v.Completion wv.1.Completion :=
  semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.toAlgebra
variable (n : ℕ)
#synth NormedSpace ℝ (Fin n → ℝ)
/-theorem algebraMap_isOpenMap : IsOpenMap (algebraMap v.Completion wv.1.Completion) := by
  apply (isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2)).isUniformInducing.isInducing.isOpenMap
  change IsOpen (Set.range (algebraMap v.Completion wv.1.Completion))
  rw [Metric.isOpen_iff]
  rw [TopologicalGroup.isOpenMap_iff_nhds_zero]
  intro U hU
  simp at hU
  rw [Metric.mem_nhds_iff] at hU
  let ⟨ε, hε, h⟩ := hU
  use closure (algebraMap v.Completion wv.1.Completion '' (Metric.ball 0 ε))
  use algebraMap v.Completion wv.1.Completion '' (Metric.ball 0 ε)

  have := isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.mapsTo_ball 0 ε
  simp [Set.MapsTo] at this
  have := isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.preimage_ball 0 ε
  simp at this
  refine ⟨ε, hε, fun y hy => ?_⟩
  simp at hy
  rw [← this] at h
  -/


instance : NormedSpace v.Completion wv.1.Completion where
  norm_smul_le x y := by
    rw [Algebra.smul_def, norm_mul, SemialgHom.algebraMap_apply,
      ← isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.norm_map_of_map_zero (map_zero _)]

noncomputable instance : FiniteDimensional v.Completion wv.1.Completion :=
  FiniteDimensional.of_locallyCompactSpace v.Completion

/-- The map from `v.Completion` to `w.Completion` whenever the infinite place `w` of `L` lies
above the infinite place `v` of `K`. -/
def comapHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap (WithAbs v.1) (WithAbs w.1)] w.Completion :=
  mapSemialgHom _ <| (WithAbs.uniformContinuous_algebraMap (v.comp_of_comap_eq h)).continuous

theorem comapHom_cont (h : w.comap (algebraMap K L) = v) : Continuous (comapHom h) := continuous_map

variable (L v)

/-- The map from `v.Completion` to the product of all completions of `L` lying above `v`. -/
def piExtensionPlace :
    v.Completion →ₛₐ[algebraMap K L] (wv : v.ExtensionPlace L) → wv.1.Completion :=
  Pi.semialgHom _ _ fun wv => comapHom wv.2

@[simp]
theorem piExtensionPlace_apply (x : v.Completion) :
    piExtensionPlace L v x = fun wv : v.ExtensionPlace L => comapHom wv.2 x := rfl

local instance : Algebra v.Completion (L ⊗[K] v.Completion) := Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := ⟨rfl⟩

/-- The `L`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L` lying
above `v`, induced by `piExtensionPlace`. -/
abbrev baseChange :
    L ⊗[K] v.Completion →ₐ[L] (wv : v.ExtensionPlace L) → wv.1.Completion :=
  baseChange_of_algebraMap (piExtensionPlace L v)

theorem continuous_baseChange_tmul_right : Continuous fun x => baseChange L v (1 ⊗ₜ x) := by
  simpa [baseChange_of_algebraMap_tmul_right] using continuous_pi fun _ => comapHom_cont _

/- The motivation for changing the scalars of `baseChange L v` to `v.Completion` is that
both sides are _finite-dimensional_ `v.Completion`-modules, which have the same dimension.
This fact is used to show that `baseChangeRight` (and therefore `baseChange`) is surjective. -/
/-- The `v.Completion`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L`
lying above `v`, induced by `piExtensionPlace`. -/
abbrev baseChangeRight :
    L ⊗[K] v.Completion →ₐ[v.Completion] ((wv : v.ExtensionPlace L) → wv.1.Completion) :=
  baseChangeRightOfAlgebraMap (piExtensionPlace L v)

variable [NumberField L]

-- upstreaming this to mathlib instead
theorem finrank_pi_eq_finrank_tensorProduct :
    Module.finrank v.Completion ((w : v.ExtensionPlace L) → w.1.Completion) =
      Module.finrank v.Completion (L ⊗[K] v.Completion) := by
  sorry

open scoped Classical in
theorem baseChange_surjective : Function.Surjective (baseChange L v) := by
  -- Let `d` be the `K_v` dimension of `L ⊗[K] K_v`.
  -- Then `Π v | w, L_w` also has dimension d over `K_v`.
  -- Let `Bw` be a basis of `Π v | w, L_w` size `d`.
  let Bw := Module.finBasisOfFinrankEq v.Completion
    ((w : v.ExtensionPlace L) → w.1.Completion) (finrank_pi_eq_finrank_tensorProduct L v)
  -- `L` is dense inside Π v | w, L_w
  have := denseRange_algebraMap_subtype_pi _ fun w : InfinitePlace L => w.comap (algebraMap K L) = v
  -- So there exists a vector `α ∈ L^d` whose matrix wrt `Bw` gets close to `1` (has non-zero det)
  let ⟨α, h⟩ := (DenseRange.piMap fun _ => this).exists_matrix_det_ne_zero
    (Basis.toMatrix_continuous Bw) Bw.toMatrix_self
  -- Therefore `α` is a basis under the image of `piExtensionPlace L v`, hence it's surjective
  rw [← isUnit_iff_ne_zero, ← Bw.det_apply, ← is_basis_iff_det Bw] at h
  rw [← baseChangeRightOfAlgebraMap_coe, ← LinearMap.range_eq_top, ← top_le_iff, ← h.2,
    Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact ⟨α i ⊗ₜ 1, by simp⟩

variable [NumberField K]

open scoped Classical in
theorem baseChange_injective :
    Function.Injective (baseChange L v) := by
  rw [← baseChangeRightOfAlgebraMap_coe, ← AlgHom.coe_toLinearMap,
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_pi_eq_finrank_tensorProduct L v).symm]
  simp [baseChange_surjective L v]

instance : IsModuleTopology v.Completion wv.1.Completion :=
  IsModuleTopology.iso (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (Module.finrank_fin_fun v.Completion)).some

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsTopologicalSemiring (L ⊗[K] v.Completion) :=
  IsModuleTopology.topologicalSemiring v.Completion _

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The `L`-algebra homeomorphism between `L ⊗[K] v.Completion` and the product of all completions
of `L` lying above `v`. -/
def baseChangeEquiv :
    L ⊗[K] v.Completion ≃A[L] (wv : v.ExtensionPlace L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  IsModuleTopology.continuousAlgEquiv K v.Completion e (continuous_baseChange_tmul_right L v)
    (baseChange_of_algebraMap_tmul_right _)

@[simp]
theorem baseChangeEquiv_tmul (l : L) (x : v.Completion) :
    baseChangeEquiv L v (l ⊗ₜ[K] x) = fun wv : v.ExtensionPlace L => l * comapHom wv.2 x := by
  simp [baseChangeEquiv, baseChange, SemialgHom.baseChange_of_algebraMap_tmul]
  rfl

def baseChangeEquivRight :
    L ⊗[K] v.Completion ≃A[v.Completion] (wv : v.ExtensionPlace L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  IsModuleTopology.continuousAlgEquiv' (e.changeScalars K v.Completion (baseChange_of_algebraMap_tmul_right _))

open TensorProduct.AlgebraTensorModule in
def piEquiv :
    (Fin (Module.finrank K L) → v.Completion) ≃L[v.Completion]
      (wv : v.ExtensionPlace L) → wv.1.Completion := by
  let comm := (Algebra.TensorProduct.comm K v.Completion L).extendScalars v.Completion |>.toLinearEquiv
  let π := finiteEquivPi K L v.Completion
  let π := IsModuleTopology.continuousLinearEquiv (comm.symm.trans π) |>.symm
  let BC := baseChangeEquivRight L v |>.toContinuousLinearEquiv
  exact π.trans BC

theorem piEquiv_smul (x : v.Completion) (y : Fin (Module.finrank K L) → v.Completion)
    (wv : v.ExtensionPlace L) :
    piEquiv L v (x • y) wv = comapHom wv.2 x * piEquiv L v y wv := by
  have := (piEquiv L v).map_smul x y
  rw [this, Pi.smul_def]
  dsimp
  rw [RingHom.smul_toAlgebra]
  rfl


end NumberField.InfinitePlace.Completion
