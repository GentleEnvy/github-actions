import NavierStokesAB.Relations

/-!
# Beltrami fields give global smooth solutions

Let `U` be smooth and divergence free, an eigenfunction of the vector Laplacian
(`Δ U = -μ U`), and let its convective term be a gradient in the Beltrami sense:
`(U · ∇) U = ∇ (|U|² / 2)`, which we state weakly as
`⟪DU(x) (U x), w⟫ = ⟪U x, DU(x) w⟫` for all `w`.
Then
```
  v(x, t) = e^{-ν μ t} U(x),       p(x, t) = -(e^{-ν μ t})² |U(x)|² / 2
```
is a global smooth solution of the unforced Navier–Stokes equations with initial datum `U`,
in any dimension and for every viscosity. If `U` is `1`-periodic, it is a solution in the
periodic class of Clay alternative (B).

This is the classical mechanism behind the Arnold–Beltrami–Childress flows (`NavierStokesAB.ABC`).
-/

open NavierStokes.Comparator InnerProductSpace Laplacian Set
open scoped ContDiff RealInnerProductSpace

namespace NavierStokesAB

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The hypotheses on the profile `U`. -/
structure IsBeltrami (μ : ℝ) (U : ℝ^n → ℝ^n) : Prop where
  smooth : ContDiff ℝ ∞ U
  div_free : ∀ x, divergence U x = 0
  laplacian_eq : ∀ x, Δ U x = -μ • U x
  lamb : ∀ x w, ⟪fderiv ℝ U x (U x), w⟫ = ⟪U x, fderiv ℝ U x w⟫

/-- Velocity of the Beltrami solution. -/
noncomputable def beltramiVelocity (nu μ : ℝ) (U : ℝ^n → ℝ^n) (x : ℝ^n) (t : ℝ) : ℝ^n :=
  Real.exp (-(nu * μ) * t) • U x

/-- Pressure of the Beltrami solution. -/
noncomputable def beltramiPressure (nu μ : ℝ) (U : ℝ^n → ℝ^n) (x : ℝ^n) (t : ℝ) : ℝ :=
  -(Real.exp (-(nu * μ) * t) ^ 2 / 2) * ‖U x‖ ^ 2

theorem inner_gradient_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x w : E) : ⟪gradient f x, w⟫ = fderiv ℝ f x w := by
  rw [gradient, toDual_symm_apply]

namespace IsBeltrami

variable {μ : ℝ} {U : ℝ^n → ℝ^n}

theorem differentiable (hU : IsBeltrami μ U) : Differentiable ℝ U :=
  hU.smooth.differentiable (by simp)

theorem contDiffAt_two (hU : IsBeltrami μ U) (x : ℝ^n) : ContDiffAt ℝ 2 U x :=
  hU.smooth.contDiffAt.of_le (by simp)

theorem initialVelocityCondition (hU : IsBeltrami μ U) : InitialVelocityCondition U :=
  ⟨hU.div_free, hU.smooth⟩

theorem initialVelocityConditionPeriodic (hU : IsBeltrami μ U) (hper : IsOnePeriodic U) :
    InitialVelocityConditionPeriodic U :=
  ⟨hU.initialVelocityCondition, hper⟩

/-- The Beltrami ansatz solves the unforced Navier–Stokes equations for all `t ≥ 0`. -/
theorem solution (nu : ℝ) (hU : IsBeltrami μ U) :
    NavierStokesExistenceAndSmoothness nu U 0 (beltramiVelocity nu μ U)
      (beltramiPressure nu μ U) where
  navier_stokes x t ht := by
    simp only [beltramiVelocity, beltramiPressure, Pi.zero_apply, add_zero]
    have hUx : DifferentiableAt ℝ U x := hU.differentiable x
    -- time derivative
    have hc : HasDerivAt (fun s : ℝ => -(nu * μ) * s) (-(nu * μ)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(nu * μ))
    have hdt : derivWithin (fun s => Real.exp (-(nu * μ) * s) • U x) (Ici 0) t =
        (Real.exp (-(nu * μ) * t) * -(nu * μ)) • U x :=
      (hc.exp.smul_const (U x)).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
    set a := Real.exp (-(nu * μ) * t) with ha
    -- convective term
    have hconv : fderiv ℝ (fun y => a • U y) x = a • fderiv ℝ U x :=
      fderiv_fun_const_smul hUx a
    -- viscous term
    have hlap : Δ (fun y => a • U y) x = a • Δ U x := by
      have : (fun y => a • U y) = a • U := rfl
      rw [this, laplacian_smul a (hU.contDiffAt_two x)]
    -- pressure term
    have hp : HasFDerivAt (fun y => -(a ^ 2 / 2) * ‖U y‖ ^ 2)
        ((-(a ^ 2 / 2)) • (2 • (innerSL ℝ (U x)).comp (fderiv ℝ U x))) x :=
      hUx.hasFDerivAt.norm_sq.const_mul (-(a ^ 2 / 2))
    apply ext_inner_right ℝ
    intro w
    rw [hdt, hconv, hlap, inner_add_left, inner_sub_left, inner_gradient_left, hp.fderiv,
      hU.laplacian_eq x]
    simp only [ContinuousLinearMap.smul_apply, map_smul, real_inner_smul_left,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul, two_smul,
      ContinuousLinearMap.add_apply]
    rw [hU.lamb x w]
    ring
  div_free x t _ := by
    show divergence (fun y => Real.exp (-(nu * μ) * t) • U y) x = 0
    rw [divergence_smul _ (hU.differentiable x), hU.div_free, mul_zero]
  initial_condition x := by simp [beltramiVelocity]
  velocity_smooth := by
    have : ContDiff ℝ ∞ (fun q : ℝ^n × ℝ => Real.exp (-(nu * μ) * q.2) • U q.1) :=
      (contDiff_const.mul contDiff_snd).exp.smul (hU.smooth.comp contDiff_fst)
    exact this.contDiffOn
  pressure_smooth := by
    have : ContDiff ℝ ∞
        (fun q : ℝ^n × ℝ => -(Real.exp (-(nu * μ) * q.2) ^ 2 / 2) * ‖U q.1‖ ^ 2) :=
      ((((contDiff_const.mul contDiff_snd).exp.pow 2).div_const 2).neg).mul
        (ContDiff.norm_sq ℝ (hU.smooth.comp contDiff_fst))
    exact this.contDiffOn

/-- For a `1`-periodic Beltrami profile the solution is in the class of Clay (B). -/
theorem periodicSolution (nu : ℝ) (hU : IsBeltrami μ U) (hper : IsOnePeriodic U) :
    NavierStokesExistenceAndSmoothnessPeriodic nu U 0 (beltramiVelocity nu μ U)
      (beltramiPressure nu μ U) where
  toNavierStokesExistenceAndSmoothness := hU.solution nu
  isOnePeriodic_velocity t _ x i := by
    show beltramiVelocity nu μ U _ t = beltramiVelocity nu μ U x t
    simp only [beltramiVelocity, hper x i]
  isOnePeriodic_pressure t _ x i := by
    show beltramiPressure nu μ U _ t = beltramiPressure nu μ U x t
    simp only [beltramiPressure, hper x i]

end IsBeltrami

end NavierStokesAB
