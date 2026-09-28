import NavierStokesAB.SmallData.Symmetry
import NavierStokesAB.SmallData.Fourier

/-!
# Pressure coefficients and evaluation of Fourier series on weighted sequences

* `pm n x y = -⟪n, x⟫⟪n, y⟫ / |n|²`: the Fourier symbol of the pressure,
  `p̂_n = Σⱼ pm_n(ĉⱼ, ĉ_{n-j})`, i.e. `-Δp = ∂ᵢ∂ⱼ(uᵢuⱼ)`; `presOp` is the corresponding bounded
  bilinear map between weighted sequence spaces.
* `evV s x w = Σₖ e_k(x) e^{-s|k|} w_k`: evaluation at `x` of the Fourier series whose coefficients
  are `w` read at weight `s`; it is a `C^∞` function of `x` with values in `D →L[ℝ] ℂ³`.
  `evS` is the scalar version.
-/

open Real Complex Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate ContDiff

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Scalar coefficient sequences. -/
noncomputable abbrev Dsc := lp (fun _ : Λ => ℂ) 1

/-! ### The pressure symbol -/

noncomputable instance : NormedAddCommGroup (V →L[ℂ] ℂ) := inferInstance
noncomputable instance : NormedSpace ℂ (V →L[ℂ] ℂ) := inferInstance

/-- `(x, y) ↦ -⟪n, x⟫⟪n, y⟫ / |n|²`. -/
noncomputable def pm (n : Λ) : V →L[ℂ] V →L[ℂ] ℂ :=
  (-(((kn n ^ 2 : ℝ) : ℂ)⁻¹)) • (innerSL ℂ (kC n)).smulRight (innerSL ℂ (kC n))

theorem pm_apply (n : Λ) (x y : V) :
    pm n x y = -(((kn n ^ 2 : ℝ) : ℂ)⁻¹) * (⟪kC n, x⟫_ℂ * ⟪kC n, y⟫_ℂ) := by
  simp [pm]

theorem norm_pm_apply_le (n : Λ) (x y : V) : ‖pm n x y‖ ≤ ‖x‖ * ‖y‖ := by
  by_cases hn : n = 0
  · subst hn; simp [pm_apply]; positivity
  have hk : 0 < kn n := lt_of_lt_of_le one_pos (one_le_kn hn)
  rw [pm_apply, norm_mul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), norm_mul]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (kC n) x
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (kC n) y
  rw [norm_kC] at h1 h2
  rw [inv_mul_le_iff₀ (by positivity)]
  calc ‖⟪kC n, x⟫_ℂ‖ * ‖⟪kC n, y⟫_ℂ‖ ≤ (kn n * ‖x‖) * (kn n * ‖y‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = kn n ^ 2 * (‖x‖ * ‖y‖) := by ring

theorem norm_pm_le (n : Λ) : ‖pm n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun x y => by
    simpa using norm_pm_apply_le n x y

theorem weight_le_one {s s' : ℝ} (hs : 0 ≤ s) (h : s' ≤ s) (n j : Λ) :
    ‖wt s' n * wt (-s) j * wt (-s) (n - j)‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_wt, norm_wt, norm_wt, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_one_iff]
  have := kn_le_add_sub n j
  have := kn_nonneg n
  nlinarith

/-- The pressure bilinear map, from weight `s` to weight `s' ≤ s`. -/
noncomputable def presSymbol (s s' : ℝ) (hs : 0 ≤ s) (h : s' ≤ s) : Symbol V ℂ where
  K n j := (wt s' n * wt (-s) j * wt (-s) (n - j)) • pm n
  C := 1
  C_nonneg := zero_le_one
  bound n j := by
    rw [norm_smul]
    calc ‖wt s' n * wt (-s) j * wt (-s) (n - j)‖ * ‖pm n‖ ≤ 1 * 1 :=
          mul_le_mul (weight_le_one hs h n j) (norm_pm_le n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The pressure coefficients as a bounded bilinear map `D × D → Dsc`. -/
noncomputable def presOp (s s' : ℝ) (hs : 0 ≤ s) (h : s' ≤ s) : D →L[ℂ] D →L[ℂ] Dsc :=
  convCLM (presSymbol s s' hs h)

theorem presOp_apply (s s' : ℝ) (hs : 0 ≤ s) (h : s' ≤ s) (w w' : D) (n : Λ) :
    presOp s s' hs h w w' n =
      ∑' j, (wt s' n * wt (-s) j * wt (-s) (n - j)) • pm n (w j) (w' (n - j)) := by
  simp [presOp, presSymbol]

/-! ### Evaluating Fourier series of weighted sequences -/

section Eval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_evalCLM_le (k : Λ) : ‖lp.evalCLM ℝ (fun _ : Λ => E) 1 k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact lp.norm_apply_le_norm one_ne_zero w k

/-- The coefficients of the evaluation map at weight `s`. -/
noncomputable def evCoef (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s : ℝ) (k : Λ) : lp (fun _ : Λ => E) 1 →L[ℝ] E :=
  wt (-s) k • lp.evalCLM ℝ (fun _ : Λ => E) 1 k

theorem rapidDecay_evCoef {s : ℝ} (hs : 0 < s) : RapidDecay (evCoef E s) := fun m => by
  refine (summable_pow_mul_exp_neg_kn m hs).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (kn_nonneg k) m)
  rw [evCoef, norm_smul, norm_wt, neg_mul]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_evalCLM_le k)

/-- Evaluation at `x` of the Fourier series of a sequence read at weight `s`. -/
noncomputable def ev (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s : ℝ) (x : ℝ³) : lp (fun _ : Λ => E) 1 →L[ℝ] E :=
  four (evCoef E s) x

theorem ev_apply {s : ℝ} (hs : 0 < s) (x : ℝ³) (w : lp (fun _ : Λ => E) 1) :
    ev E s x w = four (fun k => wt (-s) k • w k) x := by
  rw [ev, four_apply_clm (rapidDecay_evCoef hs)]
  rfl

theorem contDiff_ev {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (ev E s) :=
  contDiff_four (rapidDecay_evCoef hs)

theorem ev_add_single (s : ℝ) (x : ℝ³) (i : Fin 3) :
    ev E s (x + EuclideanSpace.single i 1) = ev E s x :=
  four_add_single _ x i

theorem rapidDecay_of_weighted {s : ℝ} (hs : 0 < s) (w : lp (fun _ : Λ => E) 1) :
    RapidDecay fun k => wt (-s) k • w k := fun m => by
  have hb : ∀ k, ‖w k‖ ≤ ‖w‖ := fun k => lp.norm_apply_le_norm one_ne_zero w k
  refine ((summable_pow_mul_exp_neg_kn m hs).mul_right ‖w‖).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => ?_
  rw [norm_smul, norm_wt, neg_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb k) (Real.exp_pos _).le)
    (pow_nonneg (kn_nonneg k) m)

end Eval

end NavierStokesAB.SmallData
