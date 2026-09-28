import NavierStokesAB.Beltrami

/-!
# (A) and (B) do not depend on the viscosity

If `(v, p)` solves the unforced equations with viscosity `ν` and datum `u₀`, then for `a > 0`
```
  w(x, t) = a v(x, a t),        q(x, t) = a² p(x, a t)
```
solves them with viscosity `a ν` and datum `a u₀`. Smoothness, divergence, finite and
uniformly bounded energy, and periodicity are all preserved, and so are the admissible data
classes. Hence `ExistenceR3 ν ↔ ExistenceR3 ν'` for all `ν, ν' > 0`, and likewise on the torus:
Clay (A) is equivalent to `ExistenceR3 1`, and (B) to `ExistencePeriodic 1`.

Together with `NavierStokesAB.not_existenceR3_zero` this shows that the only viscosity at which
the truth value of (A) is currently known is the degenerate one, `ν = 0`, where it is false.
-/

open NavierStokes.Comparator InnerProductSpace Laplacian Set MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace NavierStokesAB

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-- The rescaled velocity `a v(x, a t)`. -/
def rescaleVelocity (a : ℝ) (v : ℝ^n → ℝ → ℝ^n) (x : ℝ^n) (t : ℝ) : ℝ^n := a • v x (a * t)

/-- The rescaled pressure `a² p(x, a t)`. -/
def rescalePressure (a : ℝ) (p : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) : ℝ := a ^ 2 * p x (a * t)

section Slices

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ^n → ℝ → F}

theorem contDiff_space_slice (hg : ContDiffOn ℝ ∞ (↿g) (univ ×ˢ Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (g · t) :=
  contDiffOn_univ.1 <| hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    fun _ _ => ⟨mem_univ _, ht⟩

theorem contDiffOn_time_slice (hg : ContDiffOn ℝ ∞ (↿g) (univ ×ˢ Ici 0)) (x : ℝ^n) :
    ContDiffOn ℝ ∞ (g x ·) (Ici 0) :=
  hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hτ => ⟨mem_univ _, hτ⟩

theorem contDiffOn_rescale (hg : ContDiffOn ℝ ∞ (↿g) (univ ×ˢ Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    ContDiffOn ℝ ∞ (fun q : ℝ^n × ℝ => g q.1 (a * q.2)) (univ ×ˢ Ici 0) :=
  hg.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)).contDiffOn
    fun _ hq => ⟨mem_univ _, mul_nonneg ha hq.2⟩

end Slices

variable {nu a : ℝ} {u₀ : ℝ^n → ℝ^n} {v : ℝ^n → ℝ → ℝ^n} {p : ℝ^n → ℝ → ℝ}

theorem _root_.NavierStokes.Comparator.NavierStokesExistenceAndSmoothness.rescale (ha : 0 < a)
    (h : NavierStokesExistenceAndSmoothness nu u₀ 0 v p) :
    NavierStokesExistenceAndSmoothness (a * nu) (a • u₀) 0 (rescaleVelocity a v)
      (rescalePressure a p) where
  navier_stokes x t ht := by
    have hs : 0 ≤ a * t := mul_nonneg ha.le ht
    have hsp := contDiff_space_slice h.velocity_smooth hs
    have hps := contDiff_space_slice h.pressure_smooth hs
    have hvd : DifferentiableAt ℝ (v · (a * t)) x := hsp.differentiable (by simp) x
    have hpd : DifferentiableAt ℝ (p · (a * t)) x := hps.differentiable (by simp) x
    -- time derivative, by the chain rule within `[0, ∞)`
    have htime : HasDerivWithinAt (v x ·) (derivWithin (v x ·) (Ici 0) (a * t)) (Ici 0) (a * t) :=
      ((contDiffOn_time_slice h.velocity_smooth x).differentiableOn (by simp) _
        hs).hasDerivWithinAt
    have hlin : HasDerivWithinAt (fun τ : ℝ => a * τ) a (Ici 0) t := by
      simpa using ((hasDerivAt_id t).const_mul a).hasDerivWithinAt
    have hdt : derivWithin (fun τ => rescaleVelocity a v x τ) (Ici 0) t =
        a • a • derivWithin (v x ·) (Ici 0) (a * t) :=
      ((htime.scomp t hlin fun _ hτ => mul_nonneg ha.le hτ).const_smul a).derivWithin
        (uniqueDiffOn_Ici 0 t ht)
    -- spatial terms
    have hconv : fderiv ℝ (fun y => rescaleVelocity a v y t) x = a • fderiv ℝ (v · (a * t)) x :=
      fderiv_fun_const_smul hvd a
    have hlap : Δ (fun y => rescaleVelocity a v y t) x = a • Δ (v · (a * t)) x := by
      have : (fun y => rescaleVelocity a v y t) = a • (v · (a * t)) := rfl
      rw [this, laplacian_smul a (hsp.contDiffAt.of_le (by simp))]
    have hp : fderiv ℝ (fun y => rescalePressure a p y t) x = a ^ 2 • fderiv ℝ (p · (a * t)) x :=
      fderiv_const_mul hpd (a ^ 2)
    -- the equation at `(x, a t)`, tested against `w`
    have hns := h.navier_stokes x (a * t) hs
    simp only [Pi.zero_apply, add_zero] at hns ⊢
    apply ext_inner_right ℝ
    intro w
    have hw := congrArg (fun z => ⟪z, w⟫) hns
    simp only [inner_add_left, inner_sub_left, inner_gradient_left, real_inner_smul_left] at hw
    rw [hdt, hconv, hlap, inner_add_left, inner_sub_left, inner_gradient_left, hp]
    simp only [rescaleVelocity, ContinuousLinearMap.smul_apply, map_smul, real_inner_smul_left,
      smul_eq_mul]
    linear_combination a ^ 2 * hw
  div_free x t ht := by
    have hs : 0 ≤ a * t := mul_nonneg ha.le ht
    show divergence (fun y => a • v y (a * t)) x = 0
    rw [divergence_smul _ ((contDiff_space_slice h.velocity_smooth hs).differentiable (by simp) x),
      h.div_free x _ hs, mul_zero]
  initial_condition x := by
    show a • v x (a * 0) = a • u₀ x
    rw [mul_zero, h.initial_condition]
  velocity_smooth := (contDiffOn_rescale h.velocity_smooth ha.le).const_smul a
  pressure_smooth := contDiffOn_const.mul (contDiffOn_rescale h.pressure_smooth ha.le)

theorem _root_.NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn.rescale (ha : 0 < a)
    (h : NavierStokesExistenceAndSmoothnessRn nu u₀ 0 v p) :
    NavierStokesExistenceAndSmoothnessRn (a * nu) (a • u₀) 0 (rescaleVelocity a v)
      (rescalePressure a p) where
  toNavierStokesExistenceAndSmoothness := h.toNavierStokesExistenceAndSmoothness.rescale ha
  integrable t ht := by
    have := (h.integrable (a * t) (mul_nonneg ha.le ht)).const_mul |a|
    simpa [rescaleVelocity, norm_smul] using this
  globally_bounded_energy := by
    obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨a ^ 2 * E, fun t ht => ?_⟩
    have h1 : (∫ x, ‖rescaleVelocity a v x t‖ ^ 2) = a ^ 2 * ∫ x, ‖v x (a * t)‖ ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext x
      simp [rescaleVelocity, norm_smul, mul_pow]
    rw [h1]
    exact mul_lt_mul_of_pos_left (hE _ (mul_nonneg ha.le ht)) (by positivity)

theorem _root_.NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic.rescale (ha : 0 < a)
    (h : NavierStokesExistenceAndSmoothnessPeriodic nu u₀ 0 v p) :
    NavierStokesExistenceAndSmoothnessPeriodic (a * nu) (a • u₀) 0 (rescaleVelocity a v)
      (rescalePressure a p) where
  toNavierStokesExistenceAndSmoothness := h.toNavierStokesExistenceAndSmoothness.rescale ha
  isOnePeriodic_velocity t ht x i :=
    congrArg (a • ·) (h.isOnePeriodic_velocity (a * t) (mul_nonneg ha.le ht) x i)
  isOnePeriodic_pressure t ht x i :=
    congrArg (a ^ 2 * ·) (h.isOnePeriodic_pressure (a * t) (mul_nonneg ha.le ht) x i)

/-! ### The data classes are invariant under scaling -/

theorem _root_.NavierStokes.Comparator.InitialVelocityCondition.smul (c : ℝ) (h : InitialVelocityCondition u₀) :
    InitialVelocityCondition (c • u₀) where
  div_free x := by
    show divergence (fun y => c • u₀ y) x = 0
    rw [divergence_smul c (h.smooth.differentiable (by simp) x), h.div_free, mul_zero]
  smooth := h.smooth.const_smul c

theorem _root_.NavierStokes.Comparator.InitialVelocityConditionDecay.smul (c : ℝ) (h : InitialVelocityConditionDecay u₀) :
    InitialVelocityConditionDecay (c • u₀) where
  toInitialVelocityCondition := h.toInitialVelocityCondition.smul c
  decay m K := by
    obtain ⟨C, hC⟩ := h.decay m K
    refine ⟨|c| * C, fun x => ?_⟩
    rw [iteratedFDeriv_const_smul_apply (h.smooth.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

theorem _root_.NavierStokes.Comparator.InitialVelocityConditionPeriodic.smul (c : ℝ) (h : InitialVelocityConditionPeriodic u₀) :
    InitialVelocityConditionPeriodic (c • u₀) where
  toInitialVelocityCondition := h.toInitialVelocityCondition.smul c
  isOnePeriodic x i := congrArg (c • ·) (h.isOnePeriodic x i)

/-! ### Viscosity independence of (A) and (B) -/

theorem existenceR3_mul (ha : 0 < a) (h : ExistenceR3 nu) : ExistenceR3 (a * nu) := by
  intro u₀ hu₀
  obtain ⟨v, p, hvp⟩ := h (a⁻¹ • u₀) (hu₀.smul a⁻¹)
  have hu : a • a⁻¹ • u₀ = u₀ := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  refine ⟨rescaleVelocity a v, rescalePressure a p, ?_⟩
  rw [← hu]
  exact hvp.rescale ha

theorem existencePeriodic_mul (ha : 0 < a) (h : ExistencePeriodic nu) :
    ExistencePeriodic (a * nu) := by
  intro u₀ hu₀
  obtain ⟨v, p, hvp⟩ := h (a⁻¹ • u₀) (hu₀.smul a⁻¹)
  have hu : a • a⁻¹ • u₀ = u₀ := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  refine ⟨rescaleVelocity a v, rescalePressure a p, ?_⟩
  rw [← hu]
  exact hvp.rescale ha

/-- (A) at one positive viscosity is equivalent to (A) at any other. -/
theorem existenceR3_iff {nu nu' : ℝ} (h : 0 < nu) (h' : 0 < nu') :
    ExistenceR3 nu ↔ ExistenceR3 nu' := by
  constructor
  · intro H
    simpa [div_mul_cancel₀ _ h.ne'] using existenceR3_mul (div_pos h' h) H
  · intro H
    simpa [div_mul_cancel₀ _ h'.ne'] using existenceR3_mul (div_pos h h') H

/-- (B) at one positive viscosity is equivalent to (B) at any other. -/
theorem existencePeriodic_iff {nu nu' : ℝ} (h : 0 < nu) (h' : 0 < nu') :
    ExistencePeriodic nu ↔ ExistencePeriodic nu' := by
  constructor
  · intro H
    simpa [div_mul_cancel₀ _ h.ne'] using existencePeriodic_mul (div_pos h' h) H
  · intro H
    simpa [div_mul_cancel₀ _ h'.ne'] using existencePeriodic_mul (div_pos h h') H

/-- Clay (A) is exactly the statement at viscosity `1`. -/
theorem clayA_iff_existenceR3_one : ClayA ↔ ExistenceR3 1 :=
  ⟨fun h => h 1 one_pos, fun h _ hnu => (existenceR3_iff one_pos hnu).1 h⟩

/-- Clay (B) is exactly the statement at viscosity `1`. -/
theorem clayB_iff_existencePeriodic_one : ClayB ↔ ExistencePeriodic 1 :=
  ⟨fun h => h 1 one_pos, fun h _ hnu => (existencePeriodic_iff one_pos hnu).1 h⟩

end NavierStokesAB
