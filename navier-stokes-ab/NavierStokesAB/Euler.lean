import NavierStokesAB.Relations
import Euler.Solution

/-!
# The inviscid endpoint: (A) fails at `nu = 0`

OpenAI's Euler theorem `Euler.euler_breakdown_R3` is stated with its own copy of the
definitions (`Euler.*`). At zero viscosity and zero force, the Navier–Stokes solution class
of the Clay/Formal Conjectures formalization is literally the Euler solution class, so the
Euler theorem says that the statement `ExistenceR3` fails at `nu = 0`.

Together with `NavierStokesAB.not_forcedExistenceR3` this pins down the gap:

| viscosity | force      | global existence on `ℝ³`                  |
|-----------|------------|-------------------------------------------|
| `nu = 0`  | `f = 0`    | false (`not_existenceR3_zero`, Euler)     |
| `nu > 0`  | admissible | false (`not_forcedExistenceR3`, (C))      |
| `nu > 0`  | `f = 0`    | **open**: this is Clay (A)                |
-/

open NavierStokes.Comparator

namespace NavierStokesAB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem euler_initialVelocityConditionDecay_iff (u₀ : ℝ³ → ℝ³) :
    Euler.InitialVelocityConditionDecay u₀ ↔ InitialVelocityConditionDecay u₀ :=
  ⟨fun h => ⟨⟨h.div_free, h.smooth⟩, h.decay⟩, fun h => ⟨⟨h.div_free, h.smooth⟩, h.decay⟩⟩

/-- Unforced Euler on `ℝ³` is the `nu = 0`, `f = 0` case of the Clay solution class. -/
theorem euler_iff_navierStokes_zero (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) :
    Euler.EulerExistenceAndSmoothnessR3 u₀ v p ↔
      NavierStokesExistenceAndSmoothnessRn 0 u₀ 0 v p := by
  have heq : ∀ x t, (derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      -gradient (p · t) x) ↔
      (derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
        (0 : ℝ) • InnerProductSpace.laplacian (v · t) x - gradient (p · t) x +
          (0 : ℝ³ → ℝ → ℝ³) x t) := by
    intro x t
    simp
  constructor
  · intro h
    exact
      { navier_stokes := fun x t ht => (heq x t).1 (h.euler x t ht)
        div_free := h.div_free
        initial_condition := h.initial_condition
        velocity_smooth := h.velocity_smooth
        pressure_smooth := h.pressure_smooth
        integrable := h.integrable
        globally_bounded_energy := h.globally_bounded_energy }
  · intro h
    exact
      { euler := fun x t ht => (heq x t).2 (h.navier_stokes x t ht)
        div_free := h.div_free
        initial_condition := h.initial_condition
        velocity_smooth := h.velocity_smooth
        pressure_smooth := h.pressure_smooth
        integrable := h.integrable
        globally_bounded_energy := h.globally_bounded_energy }

/-- From OpenAI's unforced Euler blowup: the statement (A) is false at zero viscosity. -/
theorem not_existenceR3_zero : ¬ ExistenceR3 0 := by
  intro h
  obtain ⟨u₀, hu₀, hno⟩ := Euler.euler_breakdown_R3
  obtain ⟨v, p, hvp⟩ := h u₀ ((euler_initialVelocityConditionDecay_iff u₀).1 hu₀)
  exact hno ⟨v, p, (euler_iff_navierStokes_zero u₀ v p).2 hvp⟩

/-- Equivalently: an unforced breakdown on `ℝ³` exists at `nu = 0`. -/
theorem unforcedBreakdownR3_zero : UnforcedBreakdownR3 0 := by
  by_contra h
  exact not_existenceR3_zero ((existenceR3_iff_not_unforcedBreakdownR3 0).2 h)

end NavierStokesAB
