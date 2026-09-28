import NavierStokesAB.Beltrami

/-!
# Elementary data for which (A) and (B) hold

* (A) and (B) hold for the zero datum (any dimension, any viscosity).
* (B) holds for every constant datum: constants are Beltrami fields with `μ = 0`.

These are sanity checks that the formal solution classes are inhabited. The nontrivial
explicit family for (B) is in `NavierStokesAB.ABC`.
-/

open NavierStokes.Comparator InnerProductSpace Laplacian MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace NavierStokesAB

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- Constant fields are Beltrami fields with eigenvalue `0`. -/
theorem isBeltrami_const (c : ℝ^n) : IsBeltrami 0 (fun _ : ℝ^n => c) where
  smooth := contDiff_const
  div_free x := divergence_const c x
  laplacian_eq x := by simp
  lamb x w := by simp

theorem isOnePeriodic_const (c : ℝ^n) : IsOnePeriodic (fun _ : ℝ^n => c) :=
  fun _ _ => rfl

/-- (B) holds for constant data. -/
theorem existencePeriodic_const (nu : ℝ) (c : ℝ^n) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu (fun _ => c) (f := 0) v p :=
  ⟨_, _, (isBeltrami_const c).periodicSolution nu (isOnePeriodic_const c)⟩

/-- The rest state solves the unforced equations on `ℝⁿ` with zero (hence bounded) energy. -/
theorem zero_solution_Rn (nu : ℝ) :
    NavierStokesExistenceAndSmoothnessRn nu (0 : ℝ^n → ℝ^n) 0 (beltramiVelocity nu 0 0)
      (beltramiPressure nu 0 0) where
  toNavierStokesExistenceAndSmoothness := (isBeltrami_const (0 : ℝ^n)).solution nu
  integrable t _ := by simp [beltramiVelocity]
  globally_bounded_energy := ⟨1, fun t _ => by simp [beltramiVelocity]⟩

/-- (A) holds for the zero datum. -/
theorem existenceR3_zero_datum (nu : ℝ) :
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu (0 : ℝ^3 → ℝ^3) (f := 0) v p :=
  ⟨_, _, zero_solution_Rn nu⟩

/-- (B) holds for the zero datum. -/
theorem existencePeriodic_zero_datum (nu : ℝ) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu (0 : ℝ^3 → ℝ^3) (f := 0) v p :=
  existencePeriodic_const nu 0

end NavierStokesAB
