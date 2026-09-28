import NavierStokesAB.SmallData.Regularity

/-!
# Divergence-free and real solutions

For the fixed point `b = Φ a b`:

* if `⟪k, a_k⟫ = 0` for all `k`, then `⟪k, b_k(t)⟫ = 0` for all `k, t` (`inner_kC_mode`);
* if `a_{-k} = conj a_k` for all `k`, then `b_{-k}(t) = conj b_k(t)` (`mode_neg`), so that the
  velocity field is real. This follows from uniqueness of the fixed point: the reflection
  `τ b = (k ↦ conj ∘ b_{-k})` is an isometry of `X` commuting with `Φ`.
-/

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

/-! ### Divergence -/

theorem inner_kC_forcing (σ₀ : ℝ) (hσ : 0 ≤ σ₀) (b : X) (k : Λ) (t : ℝ≥0) :
    ⟪kC k, forcing σ₀ b k t⟫_ℂ = 0 := by
  have hs : Summable fun j => ((ratio σ₀ k j : ℝ) : ℂ) • nl k (b j t) (b (k - j) t) := by
    have := (BoundedContinuousFunction.evalCLM ℂ t).summable (forcingG_summable hσ b k)
    simpa [BoundedContinuousFunction.evalCLM_apply, lift_apply] using this
  rw [forcing, ← innerSL_apply_apply, (innerSL ℂ (kC k)).map_tsum hs]
  simp [inner_smul_right, inner_kC_nl]

variable {ν σ₀ : ℝ} {hν : 0 < ν} {hσ : 0 ≤ σ₀} {a : D} {b : X}

theorem inner_kC_mode (hfix : Φ hν hσ a b = b) (hdiv : ∀ k, ⟪kC k, a k⟫_ℂ = 0) (k : Λ)
    (t : ℝ≥0) : ⟪kC k, b k t⟫_ℂ = 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  rw [mode_eq hfix k, conv_mode_eq k hk]
  simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, heat_apply, duh_apply,
    inner_add_right, inner_smul_right, hdiv k, mul_zero, zero_add]
  rw [duhFun, ← innerSL_apply_apply,
    ← (innerSL ℂ (kC k)).intervalIntegral_comp_comm (intervalIntegrable_duh _ _ _ _ _)]
  have hzero : (fun s : ℝ => innerSL ℂ (kC k)
      ((Real.exp (-(ν * lam k) * ((t : ℝ) - s)) : ℂ) • ext (forcingG σ₀ b k) s)) = fun _ => 0 := by
    funext s
    rw [innerSL_apply_apply, inner_smul_right, ext, forcingG_apply hσ, inner_kC_forcing σ₀ hσ,
      mul_zero]
  rw [hzero, intervalIntegral.integral_zero]

/-! ### Complex conjugation on `ℂ³` -/

/-- Componentwise complex conjugation on `ℂ³`. -/
noncomputable def vconj (z : V) : V := WithLp.toLp 2 fun i => conj (z i)

@[simp] theorem vconj_apply (z : V) (i : Fin 3) : vconj z i = conj (z i) := rfl

@[simp] theorem vconj_vconj (z : V) : vconj (vconj z) = z := by ext i; simp

theorem vconj_add (z w : V) : vconj (z + w) = vconj z + vconj w := by ext i; simp

theorem vconj_smul (c : ℂ) (z : V) : vconj (c • z) = conj c • vconj z := by ext i; simp

@[simp] theorem vconj_zero : vconj 0 = 0 := by ext i; simp

theorem vconj_sub (z w : V) : vconj (z - w) = vconj z - vconj w := by ext i; simp

theorem vconj_ofReal_smul (r : ℝ) (z : V) : vconj ((r : ℂ) • z) = (r : ℂ) • vconj z := by
  rw [vconj_smul, Complex.conj_ofReal]

theorem norm_vconj (z : V) : ‖vconj z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

/-- Conjugation as a real-linear map. -/
noncomputable def vconjL : V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := vconj
      map_add' := vconj_add
      map_smul' := fun r z => by
        rw [RingHom.id_apply, ← Complex.coe_smul, vconj_ofReal_smul, Complex.coe_smul] }
    1 fun z => by simp [norm_vconj]

theorem vconjL_apply (z : V) : vconjL z = vconj z := rfl

@[simp] theorem vconj_kC (k : Λ) : vconj (kC k) = kC k := by ext i; simp

theorem inner_kC_vconj (k : Λ) (z : V) : ⟪kC k, vconj z⟫_ℂ = conj ⟪kC k, z⟫_ℂ := by
  rw [inner_kC, inner_kC, map_sum]
  simp

theorem leray_vconj (k : Λ) (z : V) : leray k (vconj z) = vconj (leray k z) := by
  rw [leray_apply, leray_apply, inner_kC_vconj, vconj_sub, vconj_smul, vconj_kC, map_div₀,
    Complex.conj_ofReal]

theorem nl_vconj (k : Λ) (x y : V) : vconj (nl k x y) = nl (-k) (vconj x) (vconj y) := by
  rw [nl_apply, nl_apply, vconj_smul, ← leray_vconj, vconj_smul, leray_neg, kC_neg, inner_neg_left,
    inner_kC_vconj]
  have h : conj (-(2 * (π : ℂ) * I)) = 2 * π * I := by
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h, neg_smul (starRingEnd ℂ ⟪kC k, x⟫_ℂ) (vconj y), map_neg (leray k), smul_neg,
    neg_smul (2 * (π : ℂ) * I), neg_neg]

/-! ### The reflection `τ` -/

/-- `t ↦ conj (f t)`. -/
noncomputable def gconj (f : G) : G :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => vconj (f t))
    (vconjL.continuous.comp f.continuous) ‖f‖ fun t => by
      rw [norm_vconj]; exact f.norm_coe_le_norm t

theorem gconj_apply (f : G) (t : ℝ≥0) : gconj f t = vconj (f t) := rfl

theorem norm_gconj_le (f : G) : ‖gconj f‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

/-- The reflection `τ b = (k ↦ conj ∘ b_{-k})`. -/
noncomputable def τ (b : X) : X :=
  ⟨fun k => gconj (b (-k)), memℓp_one_of_summable
    (((Equiv.neg Λ).summable_iff.2 (l1_summable b)).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun k => norm_gconj_le _)⟩

theorem τ_apply (b : X) (k : Λ) (t : ℝ≥0) : τ b k t = vconj (b (-k) t) := rfl

theorem norm_τ_le (b : X) : ‖τ b‖ ≤ ‖b‖ := by
  rw [l1_norm_eq, l1_norm_eq, ← (Equiv.neg Λ).tsum_eq (fun k => ‖b k‖)]
  exact Summable.tsum_le_tsum (fun k => norm_gconj_le _) (l1_summable (τ b))
    ((Equiv.neg Λ).summable_iff.2 (l1_summable b))

theorem ratio_neg (σ₀ : ℝ) (k j : Λ) : ratio σ₀ (-k) (-j) = ratio σ₀ k j := by
  unfold ratio
  rw [show -k - -j = -(k - j) by abel, kn_neg, kn_neg, kn_neg]

/-! ### `Φ` commutes with `τ` -/

/-- The value at time `t` of the `j`-th term of the nonlinearity in mode `k`. -/
noncomputable def nlTerm (ν σ₀ : ℝ) (b : X) (k j : Λ) (t : ℝ≥0) : V :=
  ((ratio σ₀ k j : ℝ) : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ),
    (Real.exp (-(ν * lam k) * ((t : ℝ) - s)) : ℂ) • nl k (ext (b j) s) (ext (b (k - j)) s)

theorem nlK_apply_apply (hν : 0 < ν) {k : Λ} (hk : k ≠ 0) (j : Λ) (b : X) (t : ℝ≥0) :
    nlK ν σ₀ hν k j (b j) (b (k - j)) t = nlTerm ν σ₀ b k j t := by
  rw [nlK_apply hν hk, BoundedContinuousFunction.smul_apply, duh_apply, nlTerm, duhFun]
  congr 2

theorem conv_apply_time (hν : 0 < ν) (hσ : 0 ≤ σ₀) (b : X) {k : Λ} (hk : k ≠ 0) (t : ℝ≥0) :
    (convCLM (nlSymbol hν hσ) b b) k t = ∑' j, nlTerm ν σ₀ b k j t ∧
      Summable fun j => nlTerm ν σ₀ b k j t := by
  have hs := (BoundedContinuousFunction.evalCLM ℂ t).summable
    (summable_convSummand (nlSymbol hν hσ) b b k)
  have he := (BoundedContinuousFunction.evalCLM ℂ t).map_tsum
    (summable_convSummand (nlSymbol hν hσ) b b k)
  simp only [BoundedContinuousFunction.evalCLM_apply] at hs he
  have hK : ∀ j, (nlSymbol hν hσ).K k j (b j) (b (k - j)) t = nlTerm ν σ₀ b k j t :=
    fun j => nlK_apply_apply hν hk j b t
  simp only [hK] at hs he
  exact ⟨by rw [convCLM_apply, conv_apply, he], hs⟩

theorem Φ_apply_time (hν : 0 < ν) (hσ : 0 ≤ σ₀) (a : D) (b : X) {k : Λ} (hk : k ≠ 0)
    (t : ℝ≥0) :
    Φ hν hσ a b k t = (Real.exp (-(ν * lam k) * t) : ℂ) • a k + ∑' j, nlTerm ν σ₀ b k j t := by
  show (heatX ν hν.le a k + (convCLM (nlSymbol hν hσ) b b) k) t = _
  rw [BoundedContinuousFunction.coe_add, Pi.add_apply, heatX_apply,
    (conv_apply_time hν hσ b hk t).1]

theorem Φ_apply_zero_freq (hν : 0 < ν) (hσ : 0 ≤ σ₀) (a : D) (b : X) (t : ℝ≥0) :
    Φ hν hσ a b 0 t = a 0 := by
  show (heatX ν hν.le a 0 + (convCLM (nlSymbol hν hσ) b b) 0) t = _
  rw [conv_mode_zero]
  simp [lam]

theorem ext_τ (b : X) (j : Λ) (s : ℝ) : ext (τ b j) s = vconj (ext (b (-j)) s) := rfl

theorem vconj_nlTerm (b : X) (k j : Λ) (t : ℝ≥0) :
    vconj (nlTerm ν σ₀ b (-k) j t) = nlTerm ν σ₀ (τ b) k (-j) t := by
  unfold nlTerm
  rw [vconj_ofReal_smul, ← vconjL_apply, ← vconjL.intervalIntegral_comp_comm]
  · have hr : ratio σ₀ (-k) j = ratio σ₀ k (-j) := by
      rw [← ratio_neg σ₀ k (-j), neg_neg]
    rw [hr, lam_neg]
    congr 2
    funext s
    rw [vconjL_apply, vconj_ofReal_smul, nl_vconj, neg_neg, ext_τ, ext_τ, neg_neg,
      show -(k - -j) = -k - j by abel]
  · apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun s : ℝ =>
      (Real.exp (-(ν * lam (-k)) * ((t : ℝ) - s)) : ℂ)).smul
      (((nl (-k)).continuous.comp (continuous_ext _)).clm_apply (continuous_ext _))

/-- `Φ` commutes with the reflection for Hermitian data. -/
theorem Φ_τ (hν : 0 < ν) (hσ : 0 ≤ σ₀) (a : D) (ha : ∀ k, a (-k) = vconj (a k)) (b : X) :
    Φ hν hσ a (τ b) = τ (Φ hν hσ a b) := by
  refine lp.ext (funext fun k => ?_)
  ext1 t
  rw [τ_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Φ_apply_zero_freq, neg_zero, Φ_apply_zero_freq]
    have := ha 0
    rw [neg_zero] at this
    rw [← this]
  have hk' : -k ≠ 0 := neg_ne_zero.2 hk
  rw [Φ_apply_time hν hσ a _ hk, Φ_apply_time hν hσ a _ hk', vconj_add, vconj_ofReal_smul,
    ha k, vconj_vconj, lam_neg]
  congr 1
  obtain ⟨-, hs⟩ := conv_apply_time hν hσ b hk' t
  rw [← vconjL_apply, vconjL.map_tsum hs]
  simp only [vconjL_apply, vconj_nlTerm]
  exact ((Equiv.neg Λ).tsum_eq fun j => nlTerm ν σ₀ (τ b) k j t).symm

/-- **Hermitian symmetry of the solution.** -/
theorem τ_fixedPoint (hν : 0 < ν) (hσ : 0 ≤ σ₀) (a : D) (ha : ∀ k, a (-k) = vconj (a k))
    {b : X} (hb : ‖b‖ ≤ π * ν / 2) (hfix : Φ hν hσ a b = b) : τ b = b :=
  fixedPoint_Φ_unique hν hσ a ((norm_τ_le b).trans hb) hb
    (by rw [Φ_τ hν hσ a ha, hfix]) hfix

theorem mode_neg (hν : 0 < ν) (hσ : 0 ≤ σ₀) (a : D) (ha : ∀ k, a (-k) = vconj (a k))
    {b : X} (hb : ‖b‖ ≤ π * ν / 2) (hfix : Φ hν hσ a b = b) (k : Λ) (t : ℝ≥0) :
    b (-k) t = vconj (b k t) := by
  have h := congrArg (fun b : X => b k t) (τ_fixedPoint hν hσ a ha hb hfix)
  simp only [τ_apply] at h
  rw [← h, vconj_vconj]

end NavierStokesAB.SmallData
