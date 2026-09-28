import NavierStokes.ComparatorSolution

/-!
# The four Clay alternatives, one viscosity at a time

All objects below are built from the definitions that OpenAI's Comparator submission
checks against the Formal Conjectures reference
(`NavierStokes.Comparator.*`, imported through `NavierStokes.ComparatorSolution`).
Nothing is redefined: `ExistenceR3 nu` is literally the body of the Formal Conjectures
statement `navier_stokes_existence_and_smoothness_R3` at a fixed viscosity, and so on.

* `ClayA`  – (A) unforced existence and smoothness on `ℝ³`             (**open**)
* `ClayB`  – (B) unforced existence and smoothness on `ℝ³/ℤ³`          (**open**)
* `ClayC`  – (C) forced breakdown on `ℝ³`        (proved by OpenAI, re-exported below)
* `ClayD`  – (D) forced breakdown on `ℝ³/ℤ³`     (proved by OpenAI, re-exported below)
-/

open NavierStokes.Comparator

namespace NavierStokesAB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- (A) at a fixed viscosity: every admissible datum on `ℝ³` has a global smooth
finite-energy solution of the **unforced** equations. -/
def ExistenceR3 (nu : ℝ) : Prop :=
  ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ (f := 0) v p

/-- (B) at a fixed viscosity: every admissible periodic datum has a global smooth
periodic solution of the **unforced** equations. -/
def ExistencePeriodic (nu : ℝ) : Prop :=
  ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (f := 0) v p

/-- The version of (A) in which an admissible force is allowed as well. -/
def ForcedExistenceR3 (nu : ℝ) : Prop :=
  ∀ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³), InitialVelocityConditionDecay u₀ →
    ForceConditionDecay f → ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p

/-- The version of (B) in which an admissible periodic force is allowed as well. -/
def ForcedExistencePeriodic (nu : ℝ) : Prop :=
  ∀ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³), InitialVelocityConditionPeriodic u₀ →
    ForceConditionPeriodic f → ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p

/-- Breakdown on `ℝ³` **without** a force: the negation of `ExistenceR3`. -/
def UnforcedBreakdownR3 (nu : ℝ) : Prop :=
  ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ ∧
    ¬ ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ (f := 0) v p

/-- Breakdown on `ℝ³/ℤ³` **without** a force: the negation of `ExistencePeriodic`. -/
def UnforcedBreakdownPeriodic (nu : ℝ) : Prop :=
  ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic u₀ ∧
    ¬ ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (f := 0) v p

/-- Clay alternative (A). -/
def ClayA : Prop := ∀ nu > 0, ExistenceR3 nu

/-- Clay alternative (B). -/
def ClayB : Prop := ∀ nu > 0, ExistencePeriodic nu

/-- Clay alternative (C), with the exact body of `navier_stokes_breakdown_R3`. -/
def ClayC : Prop := ∀ nu > 0,
  ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)

/-- Clay alternative (D), with the exact body of `navier_stokes_breakdown_periodic`. -/
def ClayD : Prop := ∀ nu > 0,
  ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p)

/-- OpenAI's theorem (C), used as a black box. -/
theorem clayC : ClayC := navier_stokes_breakdown_R3

/-- OpenAI's theorem (D), used as a black box. -/
theorem clayD : ClayD := navier_stokes_breakdown_periodic

end NavierStokesAB
