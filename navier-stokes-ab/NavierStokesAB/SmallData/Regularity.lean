import NavierStokesAB.SmallData.Weighted

/-!
# Time regularity of the mild solution

For a fixed point `b = Φ a b` (weight `σ₀`):

* every mode satisfies `∂ₜ b_k = -ν λ_k b_k + F_k` on `[0, ∞)` (`hasDerivWithinAt_mode`), where
  `F_k(t) = Σⱼ r_{k,j} nl_k (b j t) (b (k - j) t)`;
* read at any weight `s < σ₀`, the solution `t ↦ w_s(t) ∈ D` is differentiable on `[0,∞)` with
  derivative given by bounded operators applied to `w_{s''}` for `s < s'' ≤ σ₀`;
* hence `w_s` is `C^∞` on `[0, ∞)` (`contDiffOn_slice`), by induction on the order, losing a bit
  of weight at each step.
-/

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ContDiff

-- Instance search over operator spaces on these concrete spaces is slow.
set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

/-- The forcing of mode `k` at time `t`: `Σⱼ r_{k,j} nl_k (b j t) (b (k - j) t)`. -/
noncomputable def forcing (σ₀ : ℝ) (b : X) (k : Λ) (t : ℝ≥0) : V :=
  ∑' j, ((ratio σ₀ k j : ℝ) : ℂ) • nl k (b j t) (b (k - j) t)

/-- The forcing of mode `k` as a bounded function of time. -/
noncomputable def forcingG (σ₀ : ℝ) (b : X) (k : Λ) : G :=
  ∑' j, ((ratio σ₀ k j : ℝ) : ℂ) • lift (nl k) (b j) (b (k - j))

theorem norm_forcingG_summand_le {σ₀ : ℝ} (hσ : 0 ≤ σ₀) (b : X) (k j : Λ) :
    ‖((ratio σ₀ k j : ℝ) : ℂ) • lift (nl k) (b j) (b (k - j))‖ ≤
      ‖nl k‖ * (‖b j‖ * ‖b (k - j)‖) := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (ratio_pos σ₀ k j).le]
  calc ratio σ₀ k j * ‖lift (nl k) (b j) (b (k - j))‖
      ≤ 1 * (‖nl k‖ * ‖b j‖ * ‖b (k - j)‖) := by
        gcongr
        · exact ratio_le_one hσ k j
        · calc ‖lift (nl k) (b j) (b (k - j))‖ ≤ ‖lift (nl k)‖ * ‖b j‖ * ‖b (k - j)‖ :=
                ContinuousLinearMap.le_opNorm₂ _ _ _
            _ ≤ ‖nl k‖ * ‖b j‖ * ‖b (k - j)‖ := by gcongr; exact norm_lift_le _
    _ = ‖nl k‖ * (‖b j‖ * ‖b (k - j)‖) := by ring

theorem forcingG_summable {σ₀ : ℝ} (hσ : 0 ≤ σ₀) (b : X) (k : Λ) :
    Summable fun j => ((ratio σ₀ k j : ℝ) : ℂ) • lift (nl k) (b j) (b (k - j)) :=
  Summable.of_norm_bounded (((conv_bound_summable b b).1 k).mul_left ‖nl k‖)
    (norm_forcingG_summand_le hσ b k)

theorem forcingG_apply {σ₀ : ℝ} (hσ : 0 ≤ σ₀) (b : X) (k : Λ) (t : ℝ≥0) :
    forcingG σ₀ b k t = forcing σ₀ b k t := by
  have h := (BoundedContinuousFunction.evalCLM ℂ t).map_tsum (forcingG_summable hσ b k)
  simp only [BoundedContinuousFunction.evalCLM_apply] at h
  rw [forcingG, h, forcing]
  congr 1

@[simp] theorem forcing_zero_freq (σ₀ : ℝ) (b : X) (t : ℝ≥0) : forcing σ₀ b 0 t = 0 := by
  simp [forcing]

/-! ### The mode equations -/

variable {ν σ₀ : ℝ} {hν : 0 < ν} {hσ : 0 ≤ σ₀} {a : D} {b : X}

theorem mode_eq (hfix : Φ hν hσ a b = b) (k : Λ) :
    b k = heat (ν * lam k) (mul_nonneg hν.le (lam_nonneg k)) (a k) +
      (convCLM (nlSymbol hν hσ) b b) k := by
  conv_lhs => rw [← hfix]
  rfl

theorem conv_mode_eq (k : Λ) (hk : k ≠ 0) :
    (convCLM (nlSymbol hν hσ) b b) k = duh (ν * lam k) (rate_pos hν hk) (forcingG σ₀ b k) := by
  rw [convCLM_apply, conv_apply, forcingG, (duh (ν * lam k) (rate_pos hν hk)).map_tsum
    (forcingG_summable hσ b k)]
  congr 1
  funext j
  show nlK ν σ₀ hν k j (b j) (b (k - j)) = _
  rw [nlK_apply hν hk, map_smul]

theorem conv_mode_zero : (convCLM (nlSymbol hν hσ) b b) 0 = 0 := by
  rw [convCLM_apply, conv_apply]
  simp [nlSymbol, nlK_zero]

theorem hasDerivAt_exp_neg_mul (μ s : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (-μ * s) : ℂ)) ((Real.exp (-μ * s) * (-μ) : ℝ) : ℂ) s := by
  have h0 : HasDerivAt (fun s => Real.exp (-μ * s)) (Real.exp (-μ * s) * (-μ)) s := by
    simpa using ((hasDerivAt_id' s).const_mul (-μ)).exp
  exact h0.ofReal_comp

/-- The primitive used to differentiate Duhamel integrals. -/
theorem hasDerivAt_duhFormula (μ : ℝ) (f : G) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (-μ * s) : ℂ) •
        ∫ τ in (0 : ℝ)..s, (Real.exp (μ * τ) : ℂ) • ext f τ)
      (-((μ : ℝ) : ℂ) • ((Real.exp (-μ * s) : ℂ) •
          ∫ τ in (0 : ℝ)..s, (Real.exp (μ * τ) : ℂ) • ext f τ) + ext f s) s := by
  have hcont : Continuous fun τ : ℝ => (Real.exp (μ * τ) : ℂ) • ext f τ :=
    (by fun_prop : Continuous fun τ : ℝ => (Real.exp (μ * τ) : ℂ)).smul (continuous_ext f)
  have hP : HasDerivAt (fun s : ℝ => ∫ τ in (0 : ℝ)..s, (Real.exp (μ * τ) : ℂ) • ext f τ)
      ((Real.exp (μ * s) : ℂ) • ext f s) s :=
    (intervalIntegral.integral_hasStrictDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).hasDerivAt
  refine ((hasDerivAt_exp_neg_mul μ s).smul hP).congr_deriv ?_
  have h1 : (Real.exp (-μ * s) : ℂ) * (Real.exp (μ * s) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  rw [smul_smul, h1, one_smul, add_comm, smul_smul, Complex.ofReal_mul, Complex.ofReal_neg,
    mul_comm]

theorem duhFun_eq_formula (μ : ℝ) (f : G) {s : ℝ} (hs : 0 ≤ s) :
    duhFun μ f (Real.toNNReal s) = (Real.exp (-μ * s) : ℂ) •
        ∫ τ in (0 : ℝ)..s, (Real.exp (μ * τ) : ℂ) • ext f τ := by
  rw [duhFun_eq, Real.coe_toNNReal _ hs]

/-- **The mode equation** `∂ₜ b_k = -ν λ_k b_k + F_k` on `[0, ∞)`. -/
theorem hasDerivWithinAt_mode (hfix : Φ hν hσ a b = b) (k : Λ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => b k (Real.toNNReal s))
      (-(((ν * lam k : ℝ)) : ℂ) • b k (Real.toNNReal t) + forcing σ₀ b k (Real.toNNReal t))
      (Ici 0) t := by
  by_cases hk : k = 0
  · subst hk
    have hconst : ∀ s : ℝ, b 0 (Real.toNNReal s) = a 0 := by
      intro s
      rw [mode_eq hfix 0, conv_mode_zero]
      simp [lam]
    simp only [hconst, forcing_zero_freq, add_zero]
    simp only [lam, kn_zero]
    simpa using (hasDerivWithinAt_const t (Ici (0 : ℝ)) (a 0))
  set μ := ν * lam k with hμdef
  have hμ : 0 < μ := rate_pos hν hk
  set F := forcingG σ₀ b k
  -- the smooth formula for `b k` on `[0, ∞)`
  set g : ℝ → V := fun s => (Real.exp (-μ * s) : ℂ) • a k +
    (Real.exp (-μ * s) : ℂ) • ∫ τ in (0 : ℝ)..s, (Real.exp (μ * τ) : ℂ) • ext F τ with hg
  have heq : EqOn (fun s : ℝ => b k (Real.toNNReal s)) g (Ici 0) := by
    intro s hs
    simp only [hg]
    rw [mode_eq hfix k, conv_mode_eq k hk]
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, heat_apply, duh_apply]
    rw [duhFun_eq_formula μ F hs, Real.coe_toNNReal _ hs]
  have ha : HasDerivAt (fun s : ℝ => (Real.exp (-μ * s) : ℂ) • a k)
      (((Real.exp (-μ * t) * (-μ) : ℝ) : ℂ) • a k) t :=
    (hasDerivAt_exp_neg_mul μ t).smul_const (a k)
  have hg' := ha.add (hasDerivAt_duhFormula μ F t)
  refine (hg'.hasDerivWithinAt.congr_of_mem (fun s hs => heq hs) (mem_Ici.2 ht)).congr_deriv ?_
  -- identify the derivative
  have hbt : b k (Real.toNNReal t) = g t := heq (mem_Ici.2 ht)
  rw [hbt, ← forcingG_apply hσ b k]
  show _ = -((μ : ℝ) : ℂ) • g t + ext F t
  simp only [hg, smul_add]
  rw [Complex.ofReal_mul, Complex.ofReal_neg, mul_comm, ← smul_smul]
  abel

/-! ### The solution as a curve in the weighted spaces -/

theorem ratio_eq_wt (σ₀ : ℝ) (k j : Λ) :
    ((ratio σ₀ k j : ℝ) : ℂ) = wt σ₀ k * wt (-σ₀) j * wt (-σ₀) (k - j) := by
  simp only [ratio, wt, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2; ring

/-- The solution at time `t : ℝ` (clamped at `0`), read at weight `s ≤ σ₀`. -/
noncomputable def curve (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t : ℝ) : D :=
  sliceFun σ₀ s hs b (Real.toNNReal t)

theorem curve_apply (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t : ℝ) (k : Λ) :
    curve σ₀ s hs b t k = wt (s - σ₀) k • b k (Real.toNNReal t) := rfl

theorem continuous_curve (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) : Continuous (curve σ₀ s hs b) :=
  (continuous_sliceFun σ₀ s hs b).comp continuous_real_toNNReal

/-- The candidate derivative, built from bounded operators applied at a larger weight `s''`. -/
noncomputable def curveDeriv (ν σ₀ s s'' : ℝ) (hν : 0 ≤ ν) (h : s < s'') (hs'' : s'' ≤ σ₀)
    (hs0 : 0 ≤ s'') (b : X) (t : ℝ) : D :=
  lapOp ν s'' s hν h (curve σ₀ s'' hs'' b t) +
    nlOp s'' s hs0 h (curve σ₀ s'' hs'' b t) (curve σ₀ s'' hs'' b t)

theorem continuous_curveDeriv (ν σ₀ s s'' : ℝ) (hν : 0 ≤ ν) (h : s < s'') (hs'' : s'' ≤ σ₀)
    (hs0 : 0 ≤ s'') (b : X) : Continuous (curveDeriv ν σ₀ s s'' hν h hs'' hs0 b) := by
  have hc := continuous_curve σ₀ s'' hs'' b
  have h1 : Continuous fun t => lapOp ν s'' s hν h (curve σ₀ s'' hs'' b t) :=
    (lapOp ν s'' s hν h).continuous.comp hc
  have h2 : Continuous fun t =>
      nlOp s'' s hs0 h (curve σ₀ s'' hs'' b t) (curve σ₀ s'' hs'' b t) :=
    ((nlOp s'' s hs0 h).continuous.comp hc).clm_apply hc
  exact h1.add h2

theorem curveDeriv_apply (hfix : Φ hν hσ a b = b) {s s'' : ℝ} (h : s < s'') (hs'' : s'' ≤ σ₀)
    (hs0 : 0 ≤ s'') (t : ℝ) (k : Λ) :
    curveDeriv ν σ₀ s s'' hν.le h hs'' hs0 b t k = wt (s - σ₀) k •
      (-(((ν * lam k : ℝ)) : ℂ) • b k (Real.toNNReal t) + forcing σ₀ b k (Real.toNNReal t)) := by
  unfold curveDeriv
  rw [lp.coeFn_add, Pi.add_apply, lapOp_apply, nlOp_apply, curve_apply, smul_add, forcing,
    ← tsum_const_smul'']
  congr 1
  · rw [smul_smul, smul_smul, Complex.ofReal_neg, neg_mul, neg_mul, mul_comm (wt (s - σ₀) k),
      mul_assoc, wt_mul]
    congr 3; ring_nf
  · congr 1
    funext j
    simp only [curve_apply, map_smul, ContinuousLinearMap.smul_apply, smul_smul, ratio_eq_wt]
    congr 1
    simp only [wt, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2; ring

theorem hasDerivWithinAt_curve (hfix : Φ hν hσ a b = b) {s s'' : ℝ} (h : s < s'')
    (hs'' : s'' ≤ σ₀) (hs0 : 0 ≤ s'') {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (curve σ₀ s (h.le.trans hs'') b)
      (curveDeriv ν σ₀ s s'' hν.le h hs'' hs0 b t) (Ici 0) t := by
  set W := curveDeriv ν σ₀ s s'' hν.le h hs'' hs0 b
  have hW : Continuous W := continuous_curveDeriv ν σ₀ s s'' hν.le h hs'' hs0 b
  set I : ℝ → D := fun u => curve σ₀ s (h.le.trans hs'') b 0 + ∫ τ in (0 : ℝ)..u, W τ
  have hI : HasDerivAt I (W t) t :=
    ((intervalIntegral.integral_hasStrictDerivAt_right (hW.intervalIntegrable _ _)
      (hW.stronglyMeasurableAtFilter volume (𝓝 t)) hW.continuousAt).hasDerivAt).const_add _
  have hEq : EqOn (curve σ₀ s (h.le.trans hs'') b) I (Ici 0) := by
    intro u hu
    have hu' : (0 : ℝ) ≤ u := hu
    refine lp.ext (funext fun k => ?_)
    have hcomm := (lp.evalCLM ℂ (fun _ : Λ => V) 1 k).intervalIntegral_comp_comm
      (hW.intervalIntegrable (μ := volume) 0 u)
    simp only [I, lp.coeFn_add, Pi.add_apply]
    change curve σ₀ s _ b u k = curve σ₀ s _ b 0 k + (lp.evalCLM ℂ (fun _ : Λ => V) 1 k)
      (∫ τ in (0 : ℝ)..u, W τ)
    rw [← hcomm]
    -- the fundamental theorem of calculus for the mode `k`
    have hbk : Continuous fun τ : ℝ => wt (s - σ₀) k • b k (Real.toNNReal τ) :=
      ((b k).continuous.comp continuous_real_toNNReal).const_smul (wt (s - σ₀) k)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hu'
      (f := fun τ => wt (s - σ₀) k • b k (Real.toNNReal τ))
      (f' := fun τ => (lp.evalCLM ℂ (fun _ : Λ => V) 1 k) (W τ))
      hbk.continuousOn
      (fun x hx => by
        have hx0 : 0 ≤ x := hx.1.le
        have hm := ((hasDerivWithinAt_mode hfix k hx0).mono
          (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hx0))).const_smul (wt (s - σ₀) k)
        refine hm.congr_deriv ?_
        show _ = W x k
        rw [curveDeriv_apply hfix h hs'' hs0 x k])
      (((lp.evalCLM ℂ (fun _ : Λ => V) 1 k).continuous.comp hW).intervalIntegrable (μ := volume) 0 u)
    rw [hftc, curve_apply, curve_apply]
    simp only [Real.toNNReal_zero]
    abel
  exact hI.hasDerivWithinAt.congr_of_mem hEq (mem_Ici.2 ht)

/-- **Smoothness in time.** For every weight `s < σ₀`, the solution is `C^∞` on `[0, ∞)`. -/
theorem contDiffOn_curve_nat (hfix : Φ hν hσ a b = b) (n : ℕ) :
    ∀ (s : ℝ) (hs0 : 0 ≤ s) (hs : s < σ₀), ContDiffOn ℝ n (curve σ₀ s hs.le b) (Ici 0) := by
  induction n with
  | zero =>
    intro s _ hs
    exact contDiffOn_zero.2 (continuous_curve σ₀ s hs.le b).continuousOn
  | succ n ih =>
    intro s hs0 hs
    set s'' := (s + σ₀) / 2
    have h : s < s'' := by simp only [s'']; linarith
    have hs'' : s'' < σ₀ := by simp only [s'']; linarith
    have hs''0 : 0 ≤ s'' := by linarith
    have ih'' := ih s'' hs''0 hs''
    have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (curve σ₀ s hs.le b)
        (curveDeriv ν σ₀ s s'' hν.le h hs''.le hs''0 b t) (Ici 0) t :=
      fun t ht => hasDerivWithinAt_curve hfix h hs''.le hs''0 ht
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hd t ht).differentiableWithinAt, by simp, ?_⟩
    have hW : ContDiffOn ℝ n (curveDeriv ν σ₀ s s'' hν.le h hs''.le hs''0 b) (Ici 0) := by
      unfold curveDeriv
      refine ContDiffOn.add ?_ ?_
      · exact ((lapOp ν s'' s hν.le h).restrictScalars ℝ).contDiff.comp_contDiffOn ih''
      · have h1 : ContDiffOn ℝ n (fun t => ((nlOp s'' s hs''0 h).bilinearRestrictScalars ℝ)
            (curve σ₀ s'' hs''.le b t)) (Ici 0) :=
          ((nlOp s'' s hs''0 h).bilinearRestrictScalars ℝ).contDiff.comp_contDiffOn ih''
        exact h1.clm_apply ih''
    exact hW.congr fun t ht => (hd t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem contDiffOn_curve (hfix : Φ hν hσ a b = b) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < σ₀) :
    ContDiffOn ℝ ∞ (curve σ₀ s hs.le b) (Ici 0) :=
  contDiffOn_infty.2 fun n => contDiffOn_curve_nat hfix n s hs0 hs

end NavierStokesAB.SmallData
