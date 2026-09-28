import NavierStokesAB.Statements

/-!
# What (C) and (D) do and do not say about (A) and (B)

The Clay text states (A)/(B) with `f ≡ 0`, while (C)/(D) allow an admissible force.
The zero force is admissible, so the implications run only one way:

```
  UnforcedBreakdownR3 nu  ─────►  (C) at nu        (breakdown without force is the stronger claim)
  ForcedExistenceR3   nu  ─────►  ExistenceR3 nu   (existence with force is the stronger claim)
  ExistenceR3 nu          ◄────►  ¬ UnforcedBreakdownR3 nu
  (C) at nu               ◄────►  ¬ ForcedExistenceR3 nu
```

OpenAI proved (C) and (D) for every `nu > 0`. By the lemmas below this refutes the
*forced* existence statements, and nothing more. Whether (A) and (B) hold is exactly
the question whether an unforced breakdown exists, which is not settled by these results.
-/

open NavierStokes.Comparator

namespace NavierStokesAB

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ### The zero force is admissible -/

theorem uncurry_zero : (↿(0 : ℝ^n → ℝ → ℝ^n)) = fun _ => 0 := rfl

theorem forceCondition_zero : ForceCondition (0 : ℝ^n → ℝ → ℝ^n) :=
  ⟨by rw [uncurry_zero]; exact contDiffOn_const⟩

theorem forceConditionDecay_zero : ForceConditionDecay (0 : ℝ^n → ℝ → ℝ^n) where
  toForceCondition := forceCondition_zero
  decay m K := ⟨0, fun x t _ => by
    rw [uncurry_zero, iteratedFDerivWithin_zero_fun, norm_zero, zero_div]⟩

theorem forceConditionPeriodic_zero : ForceConditionPeriodic (0 : ℝ^n → ℝ → ℝ^n) where
  toForceCondition := forceCondition_zero
  isOnePeriodic _ _ _ _ := rfl
  decay m K := ⟨0, fun x t _ => by
    rw [uncurry_zero, iteratedFDerivWithin_zero_fun, norm_zero, zero_div]⟩

/-! ### Existence ↔ no breakdown -/

theorem existenceR3_iff_not_unforcedBreakdownR3 (nu : ℝ) :
    ExistenceR3 nu ↔ ¬ UnforcedBreakdownR3 nu := by
  constructor
  · rintro h ⟨u₀, hu₀, hno⟩
    exact hno (h u₀ hu₀)
  · intro h u₀ hu₀
    by_contra hno
    exact h ⟨u₀, hu₀, hno⟩

theorem existencePeriodic_iff_not_unforcedBreakdownPeriodic (nu : ℝ) :
    ExistencePeriodic nu ↔ ¬ UnforcedBreakdownPeriodic nu := by
  constructor
  · rintro h ⟨u₀, hu₀, hno⟩
    exact hno (h u₀ hu₀)
  · intro h u₀ hu₀
    by_contra hno
    exact h ⟨u₀, hu₀, hno⟩

/-- (C) at a fixed viscosity is precisely the failure of forced existence. -/
theorem breakdownR3_iff_not_forcedExistenceR3 (nu : ℝ) :
    (∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)) ↔
    ¬ ForcedExistenceR3 nu := by
  constructor
  · rintro ⟨u₀, f, hu₀, hf, hno⟩ h
    exact hno (h u₀ f hu₀ hf)
  · intro h
    by_contra hno
    refine h fun u₀ f hu₀ hf => ?_
    by_contra hsol
    exact hno ⟨u₀, f, hu₀, hf, hsol⟩

/-- (D) at a fixed viscosity is precisely the failure of forced periodic existence. -/
theorem breakdownPeriodic_iff_not_forcedExistencePeriodic (nu : ℝ) :
    (∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p)) ↔
    ¬ ForcedExistencePeriodic nu := by
  constructor
  · rintro ⟨u₀, f, hu₀, hf, hno⟩ h
    exact hno (h u₀ f hu₀ hf)
  · intro h
    by_contra hno
    refine h fun u₀ f hu₀ hf => ?_
    by_contra hsol
    exact hno ⟨u₀, f, hu₀, hf, hsol⟩

/-! ### The one-way implications -/

theorem existenceR3_of_forcedExistenceR3 {nu : ℝ} (h : ForcedExistenceR3 nu) :
    ExistenceR3 nu :=
  fun u₀ hu₀ => h u₀ 0 hu₀ forceConditionDecay_zero

theorem existencePeriodic_of_forcedExistencePeriodic {nu : ℝ}
    (h : ForcedExistencePeriodic nu) : ExistencePeriodic nu :=
  fun u₀ hu₀ => h u₀ 0 hu₀ forceConditionPeriodic_zero

/-- An unforced breakdown would give (C); the converse is not available. -/
theorem clayC_of_unforcedBreakdownR3 (h : ∀ nu > 0, UnforcedBreakdownR3 nu) : ClayC := by
  intro nu hnu
  obtain ⟨u₀, hu₀, hno⟩ := h nu hnu
  exact ⟨u₀, 0, hu₀, forceConditionDecay_zero, hno⟩

/-- An unforced periodic breakdown would give (D); the converse is not available. -/
theorem clayD_of_unforcedBreakdownPeriodic (h : ∀ nu > 0, UnforcedBreakdownPeriodic nu) :
    ClayD := by
  intro nu hnu
  obtain ⟨u₀, hu₀, hno⟩ := h nu hnu
  exact ⟨u₀, 0, hu₀, forceConditionPeriodic_zero, hno⟩

/-! ### Consequences of OpenAI's theorems -/

/-- From OpenAI's (C): allowing a force, global existence on `ℝ³` fails for every `nu > 0`. -/
theorem not_forcedExistenceR3 {nu : ℝ} (hnu : 0 < nu) : ¬ ForcedExistenceR3 nu :=
  (breakdownR3_iff_not_forcedExistenceR3 nu).1 (clayC nu hnu)

/-- From OpenAI's (D): allowing a force, periodic global existence fails for every `nu > 0`. -/
theorem not_forcedExistencePeriodic {nu : ℝ} (hnu : 0 < nu) : ¬ ForcedExistencePeriodic nu :=
  (breakdownPeriodic_iff_not_forcedExistencePeriodic nu).1 (clayD nu hnu)

/-- (A) is equivalent to the absence of unforced breakdown, (C) notwithstanding. -/
theorem clayA_iff : ClayA ↔ ∀ nu > 0, ¬ UnforcedBreakdownR3 nu :=
  forall₂_congr fun nu _ => existenceR3_iff_not_unforcedBreakdownR3 nu

/-- (B) is equivalent to the absence of unforced periodic breakdown, (D) notwithstanding. -/
theorem clayB_iff : ClayB ↔ ∀ nu > 0, ¬ UnforcedBreakdownPeriodic nu :=
  forall₂_congr fun nu _ => existencePeriodic_iff_not_unforcedBreakdownPeriodic nu

/-- The shape of the statements alone does not let one pass from a forced breakdown to an
unforced one: here is a toy "solution predicate" with a forced failure and no unforced one.
So any derivation of `¬ ClayA` from `ClayC` has to use actual analysis of the equations. -/
theorem forced_breakdown_does_not_formally_give_unforced :
    ∃ (Sol : Bool → Bool → Prop), (∃ u f, ¬ Sol u f) ∧ ∀ u, Sol u false :=
  ⟨fun _ f => f = false, ⟨false, true, by decide⟩, fun _ => rfl⟩

end NavierStokesAB
