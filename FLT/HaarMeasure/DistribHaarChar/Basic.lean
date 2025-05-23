/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The distributive character of Haar measures

Given a group `G` acting on an measurable additive commutative group `A`, and an element `g : G`,
one can pull back the Haar measure `μ` of `A` along the map `(g • ·) : A → A` to get another Haar
measure `μ'` on `A`. By unicity of Haar measures, there exists some nonnegative real number `r` such
that `μ' = r • μ`. We can thus define a map `distribHaarChar : G → ℝ≥0` sending `g` to its
associated real number `r`. Furthermore, this number doesn't depend on the Haar measure `μ` we
started with, and `distribHaarChar` is a group homomorphism.

## See also

[Zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/canonical.20norm.20coming.20from.20Haar.20measure/near/480050592)
-/

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

section group

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [MeasurableSpace A]
  -- We only need `MeasurableConstSMul G A` but we don't have this class. So we erroneously must
  -- assume `MeasurableSpace G` + `MeasurableSMul G A`
  [MeasurableSpace G] [MeasurableSMul G A] [TopologicalSpace A] [BorelSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A] {μ ν : Measure A}
  {g : G} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

variable (μ A) in
/-- `distribHaarChar A : G →* ℝ≥0` is the factor by which the action
of `G` on the locally compact additive abelian group `A` scales
Haar measure. -/
@[simps -isSimp]
noncomputable def distribHaarChar : G →* ℝ≥0 where
  toFun g := addHaarScalarFactor (DomMulAct.mk g • addHaar) (addHaar (G := A))
  map_one' := by simp
  map_mul' g g' := by
    simp_rw [DomMulAct.mk_mul]
    rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g' • addHaar (G := A))]
    congr 1
    simp_rw [mul_smul]
    rw [addHaarScalarFactor_domSMul]

variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = distribHaarChar A g :=
  addHaarScalarFactor_smul_congr' ..

variable (μ) in
lemma addHaarScalarFactor_smul_inv_eq_distribHaarChar (g : G) :
    addHaarScalarFactor μ ((DomMulAct.mk g)⁻¹ • μ) = distribHaarChar A g := by
  rw [← addHaarScalarFactor_domSMul _ _ (DomMulAct.mk g)]
  simp_rw [← mul_smul, mul_inv_cancel, one_smul]
  exact addHaarScalarFactor_smul_eq_distribHaarChar ..

variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) :
    addHaarScalarFactor μ (DomMulAct.mk g • μ) = (distribHaarChar A g)⁻¹ := by
  rw [← map_inv, ← addHaarScalarFactor_smul_inv_eq_distribHaarChar μ, DomMulAct.mk_inv, inv_inv]

lemma distribHaarChar_pos : 0 < distribHaarChar A g :=
  pos_iff_ne_zero.mpr ((Group.isUnit g).map (distribHaarChar A)).ne_zero

variable [Regular μ] {s : Set A}

variable (μ) in
lemma distribHaarChar_mul (g : G) (s : Set A) : distribHaarChar A g * μ s = μ (g • s) := by
  have : (DomMulAct.mk g • μ) s = μ (g • s) := by simp [dmaSMul_apply]
  rw [eq_comm, ← nnreal_smul_coe_apply, ← addHaarScalarFactor_smul_eq_distribHaarChar μ,
    ← this, ← smul_apply, ← isAddLeftInvariant_eq_smul_of_regular]

lemma distribHaarChar_eq_div (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (g : G) :
    distribHaarChar A g = μ (g • s) / μ s := by
  rw [← distribHaarChar_mul, ENNReal.mul_div_cancel_right] <;> simp [*]

lemma distribHaarChar_eq_of_measure_smul_eq_mul (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) {r : ℝ≥0}
    (hμgs : μ (g • s) = r * μ s) : distribHaarChar A g = r := by
  refine ENNReal.coe_injective ?_
  rw [distribHaarChar_eq_div hs₀ hs, hμgs, ENNReal.mul_div_cancel_right] <;> simp [*]

end group

section ring

variable (R : Type*) [Ring R] [MeasurableSpace R] [TopologicalSpace R] [BorelSpace R]
  [IsTopologicalAddGroup R] [LocallyCompactSpace R]

/-- The σ-algebra on Rˣ coming from pulling back the σ-algebra on R × R along the usual
embedding g ↦ (g,g⁻¹). -/
local instance : MeasurableSpace Rˣ := MeasurableSpace.comap (Units.embedProduct R) inferInstance

local instance : MeasurableSMul Rˣ R := sorry -- TODO need advice from measure theorists

local instance : ContinuousConstSMul Rˣ R := sorry -- TODO need advice from measure theorists

noncomputable example : Rˣ → ℝ≥0 := distribHaarChar R

/-- The subgroup R^(1) of the units Rˣ of a locally compact topological ring R
consisting of the elements such that multiplication by them doesn't scale Haar measure.
-/
noncomputable def distribHaarChar.ker := MonoidHom.ker (distribHaarChar R : Rˣ →* ℝ≥0)

end ring

end MeasureTheory.Measure
