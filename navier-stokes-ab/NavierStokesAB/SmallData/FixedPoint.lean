import NavierStokesAB.SmallData.Symbols

/-!
# The mild formulation and the contraction

Unknown: `b ∈ X = ℓ¹(Λ, ℝ≥0 →ᵇ ℂ³)`, weighted by `e^{σ|k|}`: the physical Fourier coefficient
of the velocity at frequency `k` and time `t` is `e^{-σ|k|} b k t`.

The mild (Duhamel) form of the unforced Navier–Stokes equations reads `b = Φ b` with
```
  (Φ b) k = heat(ν λ_k) (a k) + Σⱼ r_{k,j} · duh(ν λ_k) (nl_k (b j, b (k - j)))
```
where `r_{k,j} = e^{σ(|k| - |j| - |k-j|)} ≤ 1`. The bilinear part has norm `≤ 1 / (2πν)`, so `Φ`
maps the ball of radius `πν/2` into itself and is a `1/2`-contraction there when `‖a‖ ≤ πν/4`.
-/

open Real Complex Metric Set
open scoped NNReal BoundedContinuousFunction InnerProductSpace

namespace NavierStokesAB.SmallData

/-- Time-dependent Fourier coefficients. -/
noncomputable abbrev G := ℝ≥0 →ᵇ V

/-- The unknown: weighted `ℓ¹` sequences of time-dependent coefficients. -/
noncomputable abbrev X := lp (fun _ : Λ => G) 1

/-- The data: weighted `ℓ¹` sequences of coefficients. -/
noncomputable abbrev D := lp (fun _ : Λ => V) 1

/-! Instance search does not find the operator norm on bilinear maps over these concrete
spaces unaided; we register the (canonical) instances explicitly. -/
noncomputable instance : NormedAddCommGroup (G →L[ℂ] G) := inferInstance
noncomputable instance : NormedSpace ℂ (G →L[ℂ] G) := inferInstance
noncomputable instance : NormedAddCommGroup (X →L[ℂ] X) := inferInstance
noncomputable instance : NormedSpace ℂ (X →L[ℂ] X) := inferInstance

/-- The weight ratio `e^{σ(|k| - |j| - |k-j|)}`. -/
noncomputable def ratio (σ : ℝ) (k j : Λ) : ℝ := exp (σ * (kn k - kn j - kn (k - j)))

theorem ratio_pos (σ : ℝ) (k j : Λ) : 0 < ratio σ k j := exp_pos _

theorem ratio_le_one {σ : ℝ} (hσ : 0 ≤ σ) (k j : Λ) : ratio σ k j ≤ 1 := by
  unfold ratio
  rw [exp_le_one_iff]
  have := kn_le_add_sub k j
  nlinarith

variable {ν σ : ℝ}

/-- The Duhamel rate `μ_k = ν λ_k > 0` for `k ≠ 0`. -/
theorem rate_pos (hν : 0 < ν) {k : Λ} (hk : k ≠ 0) : 0 < ν * lam k := mul_pos hν (lam_pos hk)

/-- The weighted Duhamel–nonlinear symbol. -/
noncomputable def nlK (ν σ : ℝ) (hν : 0 < ν) (k j : Λ) : G →L[ℂ] G →L[ℂ] G :=
  if hk : k = 0 then 0 else
    ((ratio σ k j : ℝ) : ℂ) •
      (ContinuousLinearMap.compL ℂ G G G (duh (ν * lam k) (rate_pos hν hk))).comp (lift (nl k))

theorem nlK_apply (hν : 0 < ν) {k : Λ} (hk : k ≠ 0) (j : Λ) (f g : G) :
    nlK ν σ hν k j f g = ((ratio σ k j : ℝ) : ℂ) • duh (ν * lam k) (rate_pos hν hk) (lift (nl k) f g) := by
  rw [nlK, dif_neg hk]
  rfl

theorem nlK_zero (hν : 0 < ν) (j : Λ) : nlK ν σ hν 0 j = 0 := by simp [nlK]

theorem norm_nlK_apply_le (hν : 0 < ν) (hσ : 0 ≤ σ) (k j : Λ) (f g : G) :
    ‖nlK ν σ hν k j f g‖ ≤ 1 / (2 * π * ν) * ‖f‖ * ‖g‖ := by
  by_cases hk : k = 0
  · subst hk; simp [nlK_zero]; positivity
  rw [nlK_apply hν hk, norm_smul, Complex.norm_real, Real.norm_of_nonneg (ratio_pos σ k j).le]
  have hμ := rate_pos hν hk
  have hkn := one_le_kn hk
  have h1 : ‖duh (ν * lam k) hμ (lift (nl k) f g)‖ ≤ 1 / (ν * lam k) * (2 * π * kn k * ‖f‖ * ‖g‖) := by
    calc ‖duh (ν * lam k) hμ (lift (nl k) f g)‖
        ≤ ‖(duh (ν * lam k) hμ : G →L[ℂ] G)‖ * ‖lift (nl k) f g‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (ν * lam k) * (‖lift (nl k)‖ * ‖f‖ * ‖g‖) := by
          gcongr
          · exact norm_duh_le _ hμ
          · exact ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ 1 / (ν * lam k) * (2 * π * kn k * ‖f‖ * ‖g‖) := by
          gcongr
          exact (norm_lift_le _).trans (norm_nl_le k)
  have h2 : 1 / (ν * lam k) * (2 * π * kn k) ≤ 1 / (2 * π * ν) := by
    unfold lam
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk2 : kn k ≤ kn k ^ 2 := by nlinarith
    have h4 : 0 ≤ 4 * π ^ 2 * ν := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hk2 h4]
  calc ratio σ k j * ‖duh (ν * lam k) hμ (lift (nl k) f g)‖
      ≤ 1 * (1 / (ν * lam k) * (2 * π * kn k * ‖f‖ * ‖g‖)) := by
        gcongr
        · exact ratio_le_one hσ k j
    _ = (1 / (ν * lam k) * (2 * π * kn k)) * ‖f‖ * ‖g‖ := by ring
    _ ≤ 1 / (2 * π * ν) * ‖f‖ * ‖g‖ := by gcongr

theorem norm_nlK_le (hν : 0 < ν) (hσ : 0 ≤ σ) (k j : Λ) : ‖nlK ν σ hν k j‖ ≤ 1 / (2 * π * ν) :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) (norm_nlK_apply_le hν hσ k j)

/-- The nonlinear symbol, packaged for `convCLM`. -/
noncomputable def nlSymbol (hν : 0 < ν) (hσ : 0 ≤ σ) : Symbol G where
  K := nlK ν σ hν
  C := 1 / (2 * π * ν)
  C_nonneg := by positivity
  bound := norm_nlK_le hν hσ

/-! ### The heat part -/

/-- `k ↦ heat(ν λ_k) (a k)`. -/
noncomputable def heatX (ν : ℝ) (hν : 0 ≤ ν) (a : D) : X :=
  ⟨fun k => heat (ν * lam k) (mul_nonneg hν (lam_nonneg k)) (a k),
    memℓp_one_of_summable ((l1_summable a).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun k => norm_heat_le (ν * lam k) (mul_nonneg hν (lam_nonneg k)) (a k))⟩

@[simp] theorem heatX_apply (hν : 0 ≤ ν) (a : D) (k : Λ) (t : ℝ≥0) :
    heatX ν hν a k t = (Real.exp (-(ν * lam k) * t) : ℂ) • a k := rfl

theorem norm_heatX_le (hν : 0 ≤ ν) (a : D) : ‖heatX ν hν a‖ ≤ ‖a‖ := by
  rw [l1_norm_eq, l1_norm_eq]
  exact Summable.tsum_le_tsum (fun k => norm_heat_le (ν * lam k) (mul_nonneg hν (lam_nonneg k)) (a k))
    (l1_summable _) (l1_summable a)

/-! ### The fixed-point map -/

/-- The mild Navier–Stokes map. -/
noncomputable def Φ (hν : 0 < ν) (hσ : 0 ≤ σ) (a : D) (b : X) : X :=
  heatX ν hν.le a + convCLM (nlSymbol hν hσ) b b

theorem norm_Φ_le (hν : 0 < ν) (hσ : 0 ≤ σ) (a : D) (b : X) :
    ‖Φ hν hσ a b‖ ≤ ‖a‖ + 1 / (2 * π * ν) * (‖b‖ * ‖b‖) := by
  unfold Φ
  refine (norm_add_le _ _).trans (add_le_add (norm_heatX_le _ a) ?_)
  rw [convCLM_apply]
  exact norm_conv_le _ b b

theorem dist_Φ_le (hν : 0 < ν) (hσ : 0 ≤ σ) (a : D) (b b' : X) :
    dist (Φ hν hσ a b) (Φ hν hσ a b') ≤ 1 / (2 * π * ν) * (‖b‖ + ‖b'‖) * dist b b' := by
  set B := convCLM (nlSymbol hν hσ)
  have hdiff : Φ hν hσ a b - Φ hν hσ a b' = B (b - b') b + B b' (b - b') := by
    simp only [Φ, B, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [dist_eq_norm, hdiff, dist_eq_norm]
  have hC : ‖B‖ ≤ 1 / (2 * π * ν) := norm_convCLM_le _
  calc ‖B (b - b') b + B b' (b - b')‖ ≤ ‖B (b - b') b‖ + ‖B b' (b - b')‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖b - b'‖ * ‖b‖ + ‖B‖ * ‖b'‖ * ‖b - b'‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = ‖B‖ * (‖b‖ + ‖b'‖) * ‖b - b'‖ := by ring
    _ ≤ 1 / (2 * π * ν) * (‖b‖ + ‖b'‖) * ‖b - b'‖ := by gcongr

/-- **Global existence in the mild formulation for small data.** -/
theorem exists_fixedPoint_Φ (hν : 0 < ν) (hσ : 0 ≤ σ) (a : D) (ha : ‖a‖ ≤ π * ν / 4) :
    ∃ b : X, ‖b‖ ≤ π * ν / 2 ∧ Φ hν hσ a b = b := by
  set R := π * ν / 2 with hR
  have hRpos : 0 < R := by positivity
  have hmaps : MapsTo (Φ hν hσ a) (closedBall 0 R) (closedBall 0 R) := by
    intro b hb
    rw [mem_closedBall, dist_zero_right] at hb ⊢
    refine (norm_Φ_le hν hσ a b).trans ?_
    have hbb : ‖b‖ * ‖b‖ ≤ R * R := mul_self_le_mul_self (norm_nonneg _) hb
    have : 1 / (2 * π * ν) * (R * R) = π * ν / 8 := by
      rw [hR]; field_simp; ring
    calc ‖a‖ + 1 / (2 * π * ν) * (‖b‖ * ‖b‖) ≤ π * ν / 4 + 1 / (2 * π * ν) * (R * R) := by
          gcongr
      _ = π * ν / 4 + π * ν / 8 := by rw [this]
      _ ≤ R := by rw [hR]; nlinarith [pi_pos]
  have hcontr : ContractingWith (1 / 2) (hmaps.restrict (Φ hν hσ a) _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx : ‖(x : X)‖ ≤ R := by
      have := x.2; rwa [mem_closedBall, dist_zero_right] at this
    have hy : ‖(y : X)‖ ≤ R := by
      have := y.2; rwa [mem_closedBall, dist_zero_right] at this
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [MapsTo.val_restrict_apply]
    refine (dist_Φ_le hν hσ a x y).trans ?_
    have : 1 / (2 * π * ν) * (‖(x : X)‖ + ‖(y : X)‖) ≤ 1 / 2 := by
      calc 1 / (2 * π * ν) * (‖(x : X)‖ + ‖(y : X)‖) ≤ 1 / (2 * π * ν) * (R + R) := by gcongr
        _ = 1 / 2 := by rw [hR]; field_simp; ring
    push_cast
    exact mul_le_mul_of_nonneg_right this dist_nonneg
  obtain ⟨b, hb, hfix, -, -⟩ := hcontr.exists_fixedPoint' (isClosed_closedBall.isComplete) hmaps
    (mem_closedBall_self hRpos.le) (edist_ne_top _ _)
  exact ⟨b, by simpa using hb, hfix⟩

/-- Uniqueness of the fixed point in the ball. -/
theorem fixedPoint_Φ_unique (hν : 0 < ν) (hσ : 0 ≤ σ) (a : D) {b b' : X}
    (hb : ‖b‖ ≤ π * ν / 2) (hb' : ‖b'‖ ≤ π * ν / 2) (hfb : Φ hν hσ a b = b)
    (hfb' : Φ hν hσ a b' = b') : b = b' := by
  have h := dist_Φ_le hν hσ a b b'
  rw [hfb, hfb'] at h
  have hc : 1 / (2 * π * ν) * (‖b‖ + ‖b'‖) ≤ 1 / 2 := by
    calc 1 / (2 * π * ν) * (‖b‖ + ‖b'‖) ≤ 1 / (2 * π * ν) * (π * ν / 2 + π * ν / 2) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  have : dist b b' ≤ 1 / 2 * dist b b' := h.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)
  have h0 : dist b b' = 0 := by linarith [dist_nonneg (x := b) (y := b')]
  exact dist_eq_zero.1 h0

end NavierStokesAB.SmallData
