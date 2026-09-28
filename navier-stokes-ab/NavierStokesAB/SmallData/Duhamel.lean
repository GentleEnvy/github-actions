import NavierStokesAB.SmallData.Conv

/-!
# Heat factors, Duhamel integrals and pointwise bilinear maps on `ℝ≥0 →ᵇ E`

For `μ > 0`:
* `heat μ a = (t ↦ e^{-μ t} a)`, of norm `≤ ‖a‖`;
* `duh μ f = (t ↦ ∫₀ᵗ e^{-μ (t - s)} f(s) ds)`, a continuous linear map of norm `≤ 1 / μ`.

`lift m` applies a bounded bilinear map `m : E →L E →L E` pointwise in time.
-/

open Real MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace NavierStokesAB.SmallData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A bounded continuous function on `ℝ≥0`, read on `ℝ` through `Real.toNNReal`. -/
def ext (f : ℝ≥0 →ᵇ E) (s : ℝ) : E := f (Real.toNNReal s)

theorem continuous_ext (f : ℝ≥0 →ᵇ E) : Continuous (ext f) :=
  f.continuous.comp continuous_real_toNNReal

theorem norm_ext_le (f : ℝ≥0 →ᵇ E) (s : ℝ) : ‖ext f s‖ ≤ ‖f‖ := f.norm_coe_le_norm _

@[simp] theorem ext_coe (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) : ext f t = f t := by
  simp [ext]

theorem integral_exp_decay {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, exp (-μ * (t - s)) = (1 - exp (-μ * t)) / μ := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => exp (-μ * (t - s)) / μ) (exp (-μ * (t - s))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -μ * (t - s)) μ s := by
      simpa using ((hasDerivAt_id s).const_sub t).const_mul (-μ)
    have h2 := (h1.exp).div_const μ
    rwa [mul_div_assoc, div_self hμ.ne', mul_one] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  ring

/-! ### Heat factors -/

theorem exp_neg_mul_le_one {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ≥0) : exp (-μ * t) ≤ 1 := by
  rw [exp_le_one_iff]
  have : 0 ≤ μ * (t : ℝ) := mul_nonneg hμ t.2
  linarith

/-- `t ↦ e^{-μ t} a`. -/
noncomputable def heat (μ : ℝ) (hμ : 0 ≤ μ) (a : E) : ℝ≥0 →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t : ℝ≥0 => (exp (-μ * t) : ℂ) • a)
    (by fun_prop) ‖a‖ fun t => by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_of_le_one_left (norm_nonneg _) (exp_neg_mul_le_one hμ t)

@[simp] theorem heat_apply (μ : ℝ) (hμ : 0 ≤ μ) (a : E) (t : ℝ≥0) :
    heat μ hμ a t = (exp (-μ * t) : ℂ) • a := rfl

theorem norm_heat_le (μ : ℝ) (hμ : 0 ≤ μ) (a : E) : ‖heat μ hμ a‖ ≤ ‖a‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

/-! ### Duhamel integrals -/

/-- The Duhamel integral `t ↦ ∫₀ᵗ e^{-μ(t-s)} f(s) ds`. -/
noncomputable def duhFun (μ : ℝ) (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) : E :=
  ∫ s in (0 : ℝ)..(t : ℝ), (exp (-μ * ((t : ℝ) - s)) : ℂ) • ext f s

theorem intervalIntegrable_duh (μ t : ℝ) (f : ℝ≥0 →ᵇ E) (a b : ℝ) :
    IntervalIntegrable (fun s => (exp (-μ * (t - s)) : ℂ) • ext f s) volume a b :=
  (Continuous.smul (by fun_prop) (continuous_ext f)).intervalIntegrable a b

theorem duhFun_eq (μ : ℝ) (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    duhFun μ f t =
      (exp (-μ * t) : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), (exp (μ * s) : ℂ) • ext f s := by
  unfold duhFun
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext s
  rw [smul_smul, ← Complex.ofReal_mul, ← exp_add]
  ring_nf

theorem continuous_duhFun (μ : ℝ) (f : ℝ≥0 →ᵇ E) : Continuous (duhFun μ f) := by
  have hprim : Continuous fun b : ℝ => ∫ s in (0 : ℝ)..b, (exp (μ * s) : ℂ) • ext f s :=
    intervalIntegral.continuous_primitive
      (fun a b => (Continuous.smul (by fun_prop) (continuous_ext f)).intervalIntegrable a b) 0
  have : duhFun μ f = fun t : ℝ≥0 =>
      (exp (-μ * t) : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), (exp (μ * s) : ℂ) • ext f s :=
    funext (duhFun_eq μ f)
  rw [this]
  exact (by fun_prop : Continuous fun t : ℝ≥0 => (exp (-μ * t) : ℂ)).smul
    (hprim.comp NNReal.continuous_coe)

theorem norm_duhFun_le {μ : ℝ} (hμ : 0 < μ) (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    ‖duhFun μ f t‖ ≤ ‖f‖ / μ := by
  unfold duhFun
  have hle : ∀ s, ‖(exp (-μ * ((t : ℝ) - s)) : ℂ) • ext f s‖ ≤
      exp (-μ * ((t : ℝ) - s)) * ‖f‖ := by
    intro s
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (norm_ext_le f s) (exp_pos _).le
  calc ‖∫ s in (0 : ℝ)..(t : ℝ), (exp (-μ * ((t : ℝ) - s)) : ℂ) • ext f s‖
      ≤ ∫ s in (0 : ℝ)..(t : ℝ), exp (-μ * ((t : ℝ) - s)) * ‖f‖ :=
        intervalIntegral.norm_integral_le_of_norm_le t.2 (Filter.Eventually.of_forall
          fun s _ => hle s) (by apply Continuous.intervalIntegrable; fun_prop)
    _ = (1 - exp (-μ * t)) / μ * ‖f‖ := by
        rw [intervalIntegral.integral_mul_const, integral_exp_decay hμ]
    _ ≤ ‖f‖ / μ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hμ]
        have : 0 ≤ exp (-μ * t) := (exp_pos _).le
        nlinarith [norm_nonneg f]

/-- The Duhamel integral as a bounded function. -/
noncomputable def duhBCF (μ : ℝ) (hμ : 0 < μ) (f : ℝ≥0 →ᵇ E) : ℝ≥0 →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (duhFun μ f) (continuous_duhFun μ f) (‖f‖ / μ)
    (norm_duhFun_le hμ f)

theorem duhFun_add (μ : ℝ) (f g : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    duhFun μ (f + g) t = duhFun μ f t + duhFun μ g t := by
  unfold duhFun
  rw [← intervalIntegral.integral_add (intervalIntegrable_duh μ t f 0 t)
    (intervalIntegrable_duh μ t g 0 t)]
  congr 1
  funext s
  simp [ext, smul_add]

theorem duhFun_smul (μ : ℝ) (c : ℂ) (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    duhFun μ (c • f) t = c • duhFun μ f t := by
  unfold duhFun
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp only [ext, BoundedContinuousFunction.coe_smul]
  exact smul_comm _ _ _

/-- The Duhamel operator, of norm at most `1 / μ`. -/
noncomputable def duh (μ : ℝ) (hμ : 0 < μ) : (ℝ≥0 →ᵇ E) →L[ℂ] (ℝ≥0 →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := duhBCF μ hμ
      map_add' := fun f g => by ext t; exact duhFun_add μ f g t
      map_smul' := fun c f => by ext t; exact duhFun_smul μ c f t }
    (1 / μ) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [one_div_mul_eq_div]
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
        (div_nonneg (norm_nonneg _) hμ.le) _

@[simp] theorem duh_apply (μ : ℝ) (hμ : 0 < μ) (f : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    duh μ hμ f t = duhFun μ f t := rfl

theorem norm_duh_le (μ : ℝ) (hμ : 0 < μ) : ‖(duh μ hμ : (ℝ≥0 →ᵇ E) →L[ℂ] (ℝ≥0 →ᵇ E))‖ ≤ 1 / μ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-! ### Pointwise bilinear maps -/

/-- Apply `m` pointwise in time. -/
noncomputable def liftBCF (m : E →L[ℂ] E →L[ℂ] E) (f g : ℝ≥0 →ᵇ E) : ℝ≥0 →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => m (f t) (g t))
    (m.continuous₂.comp (f.continuous.prodMk g.continuous)) (‖m‖ * ‖f‖ * ‖g‖) fun t => by
      calc ‖m (f t) (g t)‖ ≤ ‖m‖ * ‖f t‖ * ‖g t‖ := m.le_opNorm₂ _ _
        _ ≤ ‖m‖ * ‖f‖ * ‖g‖ := by
          gcongr
          · exact f.norm_coe_le_norm t
          · exact g.norm_coe_le_norm t

theorem liftBCF_apply (m : E →L[ℂ] E →L[ℂ] E) (f g : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    liftBCF m f g t = m (f t) (g t) := rfl

theorem norm_liftBCF_le (m : E →L[ℂ] E →L[ℂ] E) (f g : ℝ≥0 →ᵇ E) :
    ‖liftBCF m f g‖ ≤ ‖m‖ * ‖f‖ * ‖g‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_
  rw [liftBCF_apply]
  calc ‖m (f t) (g t)‖ ≤ ‖m‖ * ‖f t‖ * ‖g t‖ := m.le_opNorm₂ _ _
    _ ≤ ‖m‖ * ‖f‖ * ‖g‖ := by
      gcongr
      · exact f.norm_coe_le_norm t
      · exact g.norm_coe_le_norm t

/-- Pointwise-in-time bilinear map. -/
noncomputable def lift (m : E →L[ℂ] E →L[ℂ] E) :
    (ℝ≥0 →ᵇ E) →L[ℂ] (ℝ≥0 →ᵇ E) →L[ℂ] (ℝ≥0 →ᵇ E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (liftBCF m)
      (fun f₁ f₂ g => by
        ext t; simp only [liftBCF_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add,
          ContinuousLinearMap.add_apply])
      (fun c f g => by
        ext t; simp only [liftBCF_apply, BoundedContinuousFunction.coe_smul,
          map_smul, ContinuousLinearMap.smul_apply])
      (fun f g₁ g₂ => by
        ext t; simp only [liftBCF_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add])
      (fun c f g => by
        ext t; simp only [liftBCF_apply, BoundedContinuousFunction.coe_smul, map_smul]))
    ‖m‖ fun f g => by rw [LinearMap.mk₂_apply]; exact norm_liftBCF_le m f g

theorem lift_eq (m : E →L[ℂ] E →L[ℂ] E) (f g : ℝ≥0 →ᵇ E) : lift m f g = liftBCF m f g := by
  rw [lift, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]

theorem lift_apply (m : E →L[ℂ] E →L[ℂ] E) (f g : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    lift m f g t = m (f t) (g t) := by
  rw [lift_eq, liftBCF_apply]

theorem norm_lift_le (m : E →L[ℂ] E →L[ℂ] E) : ‖lift m‖ ≤ ‖m‖ := by
  unfold lift
  exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg m) _

end NavierStokesAB.SmallData
